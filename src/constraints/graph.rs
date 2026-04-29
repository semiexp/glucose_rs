use crate::constraint::{Constraint, ConstraintIdx};
use crate::solver::Solver;
use crate::types::{LBool, Lit, Var};

/// `ActiveVerticesConnected(lits, edges)`:
/// Among the vertices whose literals are TRUE, the induced subgraph must be connected
/// (or empty).
///
/// `lits[i]` is TRUE iff vertex `i` is active.
/// `edges` lists undirected edges as `(u, v)` pairs.
///
/// Ports the C++ `ActiveVerticesConnected` class from `constraints/Graph.{h,cc}`.
pub struct ActiveVerticesConnected {
    lits: Vec<Lit>,
    /// `var_to_idx[k] = (var, vertex_index)` sorted by var, for quick lookup.
    var_to_idx: Vec<(Var, usize)>,
    adj: Vec<Vec<usize>>,
    state: Vec<NodeState>,
    /// Order in which vertices were decided (for calcReason).
    decision_order: Vec<usize>,
    rank: Vec<i32>,
    lowlink: Vec<i32>,
    subtree_active_count: Vec<i32>,
    cluster_id: Vec<i32>,
    parent: Vec<i32>,
    next_rank: i32,
    conflict_cause_lit: Lit,
    conflict_cause_pos: i32,
    n_active_vertices: i32,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum NodeState {
    Undecided,
    Active,
    Inactive,
}

const K_UNVISITED: i32 = -1;

impl ActiveVerticesConnected {
    pub fn new(lits: Vec<Lit>, edges: &[(usize, usize)]) -> Self {
        let n = lits.len();
        let mut adj = vec![Vec::new(); n];
        for &(u, v) in edges {
            adj[u].push(v);
            adj[v].push(u);
        }
        let mut var_to_idx: Vec<(Var, usize)> =
            lits.iter().enumerate().map(|(i, l)| (l.var(), i)).collect();
        var_to_idx.sort();

        ActiveVerticesConnected {
            lits,
            var_to_idx,
            adj,
            state: vec![NodeState::Undecided; n],
            decision_order: Vec::new(),
            rank: vec![K_UNVISITED; n],
            lowlink: vec![0; n],
            subtree_active_count: vec![0; n],
            cluster_id: vec![0; n],
            parent: vec![-1; n],
            next_rank: 0,
            conflict_cause_lit: Lit::UNDEF,
            conflict_cause_pos: -2,
            n_active_vertices: 0,
        }
    }

    fn vertex_indices_for_var(&self, v: Var) -> impl Iterator<Item = usize> + '_ {
        let lo = self.var_to_idx.partition_point(|&(x, _)| x < v);
        let hi = self.var_to_idx.partition_point(|&(x, _)| x <= v);
        self.var_to_idx[lo..hi].iter().map(|&(_, i)| i)
    }

    /// Tarjan-style DFS that builds `rank`, `lowlink`, `subtree_active_count`, `cluster_id`,
    /// `parent`.  Returns the lowlink of `v`.
    fn build_tree(&mut self, v: usize, parent: i32, cluster_id: usize) -> i32 {
        self.rank[v] = self.next_rank;
        self.next_rank += 1;
        self.cluster_id[v] = cluster_id as i32;
        self.parent[v] = parent;

        let mut lowlink = self.rank[v];
        let mut subtree_active = if self.state[v] == NodeState::Active {
            1
        } else {
            0
        };

        let adj = self.adj[v].clone();
        for w in adj {
            if w as i32 == parent || self.state[w] == NodeState::Inactive {
                continue;
            }
            if self.rank[w] == K_UNVISITED {
                let child_low = self.build_tree(w, v as i32, cluster_id);
                lowlink = lowlink.min(child_low);
                subtree_active += self.subtree_active_count[w];
            } else {
                lowlink = lowlink.min(self.rank[w]);
            }
        }

        self.subtree_active_count[v] = subtree_active;
        self.lowlink[v] = lowlink;
        lowlink
    }

    /// Run the full propagation check.  Returns `Ok(())` on no conflict or
    /// `Err(())` if a conflict was found (conflict metadata stored in fields).
    fn run_propagation(&mut self, solver: &mut Solver, ci: ConstraintIdx) -> bool {
        let n = self.lits.len();
        if self.n_active_vertices == 0 {
            return true;
        }

        self.rank.iter_mut().for_each(|x| *x = K_UNVISITED);
        self.lowlink.iter_mut().for_each(|x| *x = 0);
        self.subtree_active_count.iter_mut().for_each(|x| *x = 0);
        self.cluster_id.iter_mut().for_each(|x| *x = 0);
        self.parent.iter_mut().for_each(|x| *x = -1);
        self.next_rank = 0;

        let mut nonempty_cluster: i32 = -1;
        let mut n_all_clusters = 0;

        for i in 0..n {
            if self.state[i] != NodeState::Inactive && self.rank[i] == K_UNVISITED {
                self.build_tree(i, -1, i);
                let sz = self.subtree_active_count[i];
                if sz >= 1 {
                    if nonempty_cluster != -1 {
                        // Already two non-empty clusters – disconnected
                        self.conflict_cause_pos = -1;
                        return false;
                    }
                    nonempty_cluster = i as i32;
                } else {
                    n_all_clusters += 1;
                }
            }
        }

        if self.n_active_vertices <= 1 && n_all_clusters == 0 {
            return true;
        }

        if nonempty_cluster != -1 {
            let nc = nonempty_cluster as usize;
            for v in 0..n {
                if self.state[v] != NodeState::Undecided {
                    continue;
                }

                if self.cluster_id[v] as usize != nc {
                    // Vertex outside the nonempty cluster must be inactive
                    if !solver.constraint_enqueue(!self.lits[v], ci) {
                        self.conflict_cause_pos = v as i32;
                        self.conflict_cause_lit = self.lits[v];
                        return false;
                    }
                } else {
                    if self.n_active_vertices <= 1 {
                        continue;
                    }
                    // Check if v is an articulation point
                    let mut parent_side_count =
                        self.subtree_active_count[nc] - self.subtree_active_count[v];
                    let mut n_nonempty_subgraph = 0;

                    let adj_len = self.adj[v].len();
                    for k in 0..adj_len {
                        let w = self.adj[v][k];
                        if self.rank[v] < self.rank[w] && self.parent[w] == v as i32 {
                            // w is a child of v
                            if self.lowlink[w] < self.rank[v] {
                                // w is not separated from v's parent after v's removal
                                parent_side_count += self.subtree_active_count[w];
                            } else if self.subtree_active_count[w] > 0 {
                                n_nonempty_subgraph += 1;
                            }
                        }
                    }
                    if parent_side_count > 0 {
                        n_nonempty_subgraph += 1;
                    }
                    if n_nonempty_subgraph >= 2 {
                        // v is an articulation point – must be active
                        if !solver.constraint_enqueue(self.lits[v], ci) {
                            self.conflict_cause_pos = v as i32;
                            self.conflict_cause_lit = !self.lits[v];
                            return false;
                        }
                    }
                }
            }
        }
        true
    }
}

// ──────────────────────────────────────────────────────────────────────────────────
// Union-Find with undo support (used in calcReason)
// ──────────────────────────────────────────────────────────────────────────────────
struct UnionFind {
    parent: Vec<i32>,
    n_active: Vec<i32>,
    redo: Vec<(i32, i32)>,
    n_active_clusters: i32,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        UnionFind {
            parent: vec![-1; n],
            n_active: vec![0; n],
            redo: Vec::new(),
            n_active_clusters: 0,
        }
    }
    fn root(&self, mut p: usize) -> usize {
        while self.parent[p] >= 0 {
            p = self.parent[p] as usize;
        }
        p
    }
    fn num_active_clusters(&self) -> i32 {
        self.n_active_clusters
    }
    fn merge(&mut self, p: usize, q: usize) {
        let mut p = self.root(p);
        let mut q = self.root(q);
        if p == q {
            return;
        }
        if self.parent[p] > self.parent[q] {
            std::mem::swap(&mut p, &mut q);
        }
        let nac_updated = self.n_active_clusters
            - (if self.n_active[p] > 0 { 1 } else { 0 })
            - (if self.n_active[q] > 0 { 1 } else { 0 })
            + (if self.n_active[p] + self.n_active[q] > 0 {
                1
            } else {
                0
            });
        self.update_parent(p, self.parent[p] + self.parent[q]);
        self.update_parent(q, p as i32);
        self.update_n_active(p, self.n_active[p] + self.n_active[q]);
        self.update_n_active(q, 0);
        self.update_n_active_clusters(nac_updated);
    }
    fn add_active_count(&mut self, p: usize, d: i32) {
        let nac_before = if self.n_active[self.root(p)] > 0 {
            1
        } else {
            0
        };
        let r = self.root(p);
        self.update_n_active(r, self.n_active[r] + d);
        let nac_after = if self.n_active[r] > 0 { 1 } else { 0 };
        let nac_updated = self.n_active_clusters - nac_before + nac_after;
        self.update_n_active_clusters(nac_updated);
    }
    fn commit(&mut self) {
        self.redo.clear();
    }
    fn redo_changes(&mut self) {
        while let Some((loc, val)) = self.redo.pop() {
            if loc == -1 {
                self.n_active_clusters = val;
            } else if loc % 2 == 0 {
                self.parent[(loc / 2) as usize] = val;
            } else {
                self.n_active[(loc / 2) as usize] = val;
            }
        }
    }
    fn update_parent(&mut self, p: usize, v: i32) {
        if self.parent[p] != v {
            self.redo.push((p as i32 * 2, self.parent[p]));
            self.parent[p] = v;
        }
    }
    fn update_n_active(&mut self, p: usize, v: i32) {
        if self.n_active[p] != v {
            self.redo.push((p as i32 * 2 + 1, self.n_active[p]));
            self.n_active[p] = v;
        }
    }
    fn update_n_active_clusters(&mut self, v: i32) {
        if self.n_active_clusters != v {
            self.redo.push((-1, self.n_active_clusters));
            self.n_active_clusters = v;
        }
    }
}

impl Constraint for ActiveVerticesConnected {
    fn initialize(&mut self, solver: &mut Solver, ci: ConstraintIdx) -> bool {
        // Note initial states
        for i in 0..self.lits.len() {
            let val = solver.value_of(self.lits[i]);
            if val != LBool::Undef {
                self.decision_order.push(i);
            }
            if val == LBool::True {
                self.state[i] = NodeState::Active;
            } else if val == LBool::False {
                self.state[i] = NodeState::Inactive;
            }
        }

        // Watch both literals for each vertex
        let mut watch_lits: Vec<Lit> = self.lits.iter().flat_map(|&l| [l, !l]).collect();
        watch_lits.sort();
        watch_lits.dedup();
        for l in watch_lits {
            solver.add_watch(l, ci);
        }

        // Propagate already-decided vertices
        let mut to_propagate: Vec<Lit> = Vec::new();
        for i in 0..self.lits.len() {
            if self.state[i] == NodeState::Active {
                to_propagate.push(self.lits[i]);
            } else if self.state[i] == NodeState::Inactive {
                to_propagate.push(!self.lits[i]);
            }
        }
        // Deduplicate (same lit may appear for multiple vertices sharing a var)
        to_propagate.sort();
        to_propagate.dedup();
        for l in to_propagate {
            if !self.propagate(solver, l, ci) {
                return false;
            }
        }
        true
    }

    fn propagate(&mut self, solver: &mut Solver, p: Lit, ci: ConstraintIdx) -> bool {
        solver.register_undo(p.var(), ci);

        // Update state for all vertices mapped to var(p)
        let indices: Vec<usize> = self.vertex_indices_for_var(p.var()).collect();
        for i in indices {
            let val = solver.value_of(self.lits[i]);
            let s = match val {
                LBool::True => NodeState::Active,
                LBool::False => NodeState::Inactive,
                LBool::Undef => panic!("propagate called on undef literal"),
            };
            if s == NodeState::Active {
                self.n_active_vertices += 1;
            }
            self.state[i] = s;
            self.decision_order.push(i);
        }

        if solver.num_pending(ci) > 0 {
            // Lazy propagation: skip expensive check
            return true;
        }

        self.run_propagation(solver, ci)
    }

    fn calc_reason(
        &mut self,
        _solver: &mut Solver,
        p: Option<Lit>,
        extra: Option<Lit>,
        out_reason: &mut Vec<Lit>,
    ) {
        let n = self.lits.len();

        // When conflict is a forced FALSE (p == None, conflict_cause_pos != -1), the conflicting
        // vertex's state needs to be temporarily set for the reasoning.
        let temp_push = p.is_none() && self.conflict_cause_pos != -1;
        if temp_push {
            debug_assert_eq!(extra, Some(self.conflict_cause_lit));
            let pos = self.conflict_cause_pos as usize;
            self.decision_order.push(pos);
            if self.conflict_cause_lit == self.lits[pos] {
                self.state[pos] = NodeState::Active;
            } else {
                self.state[pos] = NodeState::Inactive;
            }
        }

        let mut uf = UnionFind::new(n);
        let mut activated = vec![false; n];

        for i in 0..n {
            if self.state[i] == NodeState::Active {
                uf.add_active_count(i, 1);
            }
            if self.state[i] != NodeState::Inactive {
                let exclude = p.map_or(false, |lit| lit == self.lits[i]);
                if !exclude {
                    activated[i] = true;
                }
            }
        }
        for v in 0..n {
            for &w in &self.adj[v] {
                if activated[v] && activated[w] {
                    uf.merge(v, w);
                }
            }
        }
        // Add all vertices corresponding to ~p (if p exists).
        if let Some(pl) = p {
            for i in 0..n {
                if self.lits[i] == !pl {
                    uf.add_active_count(i, 1);
                }
            }
        }
        uf.commit();

        // Walk decision_order backwards; include or exclude each vertex
        for idx in (0..self.decision_order.len()).rev() {
            let v = self.decision_order[idx];
            if let Some(pl) = p {
                if pl.var() == self.lits[v].var() {
                    panic!("calc_reason: p is in decision_order");
                }
            }

            if self.state[v] == NodeState::Active {
                uf.add_active_count(v, -1);
            }
            let adj_len = self.adj[v].len();
            for k in 0..adj_len {
                let w = self.adj[v][k];
                if activated[w] {
                    uf.merge(v, w);
                }
            }

            if uf.num_active_clusters() >= 2 {
                uf.commit();
                activated[v] = true;
            } else {
                uf.redo_changes();
                // This vertex is in the reason
                match self.state[v] {
                    NodeState::Active => out_reason.push(self.lits[v]),
                    NodeState::Inactive => out_reason.push(!self.lits[v]),
                    NodeState::Undecided => {}
                }
            }
        }

        if temp_push {
            self.decision_order.pop();
            self.state[self.conflict_cause_pos as usize] = NodeState::Undecided;
        }
    }

    fn undo(&mut self, _solver: &mut Solver, p: Lit) {
        let indices: Vec<usize> = self.vertex_indices_for_var(p.var()).collect();
        for i in indices {
            if self.state[i] == NodeState::Active {
                self.n_active_vertices -= 1;
            }
            self.state[i] = NodeState::Undecided;
            self.decision_order.pop();
        }
    }
}
