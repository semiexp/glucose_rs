use std::collections::{HashMap, VecDeque};

use crate::constraint::{Constraint, ConstraintIdx};
use crate::solver::Solver;
use crate::types::{LBool, Lit};

/// Order-encoding of an integer variable, or absent (unconstrained).
///
/// When present: `lits.len() == values.len() - 1` and `lits[i] <=> (value >= values[i+1])`.
/// When absent: `values.is_empty()`.
#[derive(Clone)]
pub struct OptionalOrderEncoding {
    pub lits: Vec<Lit>,
    pub values: Vec<i32>,
}

impl OptionalOrderEncoding {
    pub fn is_absent(&self) -> bool {
        self.values.is_empty()
    }

    /// Return the literal that is TRUE iff `value >= x`, or `None` if x <= min (always true),
    /// or `Some(Lit::UNDEF)` if x > max (always false).
    pub fn at_least(&self, x: i32) -> Option<Lit> {
        assert!(!self.is_absent());
        if x <= self.values[0] {
            return None;
        }
        if x > *self.values.last().unwrap() {
            return Some(Lit::UNDEF);
        }
        let idx = self.values.partition_point(|&v| v < x);
        Some(self.lits[idx - 1])
    }

    /// Return the literal that is TRUE iff `value <= x` (i.e. `!(value >= x+1)`),
    /// or `None` if x >= max (always true), or `Some(Lit::UNDEF)` if x < min (always false).
    pub fn at_most(&self, x: i32) -> Option<Lit> {
        assert!(!self.is_absent());
        if x >= *self.values.last().unwrap() {
            return None;
        }
        if x < self.values[0] {
            return Some(Lit::UNDEF);
        }
        let idx = self.values.partition_point(|&v| v <= x);
        Some(!self.lits[idx - 1])
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum EdgeState {
    Undecided,
    Connected,
    Disconnected,
}

/// GraphDivision constraint.
///
/// Given a graph with vertices and edges, and each vertex optionally having an integer
/// size variable (order-encoded), enforce:
/// - Vertices in the same connected region (connected edges) must have the same size.
/// - The size of each region matches the number of vertices it contains.
///
/// Ports the C++ `GraphDivision` class from `constraints/GraphDivision.{h,cc}`.
pub struct GraphDivision {
    vertices: Vec<OptionalOrderEncoding>,
    /// adjacency list: adj[v] = Vec<(neighbor, edge_id)>
    adj: Vec<Vec<(usize, usize)>>,
    edge_lits: Vec<Lit>,
    edge_state: Vec<EdgeState>,
    size_lb: Vec<i32>,
    size_ub: Vec<i32>,
    size_lb_reason: Vec<Option<Lit>>,
    size_ub_reason: Vec<Option<Lit>>,
    /// Per-propagation conflict/reason info stored in a stack (one entry per registerUndo call).
    reasons: Vec<Vec<Lit>>,
    /// Reasons for individual propagated literals.
    reasons_prop: HashMap<Lit, Vec<Lit>>,
    decided_regions: Vec<Vec<usize>>,
    decided_region_id: Vec<usize>,
    potential_regions: Vec<Vec<usize>>,
    potential_region_id: Vec<usize>,
}

impl GraphDivision {
    pub fn new(
        vertices: Vec<OptionalOrderEncoding>,
        edges: &[(usize, usize)],
        edge_lits: Vec<Lit>,
    ) -> Self {
        let n = vertices.len();
        let m = edge_lits.len();
        let mut adj = vec![Vec::new(); n];
        for (i, &(s, t)) in edges.iter().enumerate() {
            assert_ne!(s, t);
            adj[s].push((t, i));
            adj[t].push((s, i));
        }
        GraphDivision {
            vertices,
            adj,
            edge_lits,
            edge_state: vec![EdgeState::Undecided; m],
            size_lb: vec![-1; n],
            size_ub: vec![-1; n],
            size_lb_reason: vec![None; n],
            size_ub_reason: vec![None; n],
            reasons: Vec::new(),
            reasons_prop: HashMap::new(),
            decided_regions: vec![Vec::new(); n],
            decided_region_id: vec![0; n],
            potential_regions: vec![Vec::new(); n],
            potential_region_id: vec![0; n],
        }
    }

    // ── Region computation ──────────────────────────────────────────────

    fn compute_regions_dfs(
        &self,
        p: usize,
        id: usize,
        region: &mut Vec<usize>,
        region_id: &mut Vec<i32>,
        is_potential: bool,
    ) {
        if region_id[p] >= 0 {
            return;
        }
        region.push(p);
        region_id[p] = id as i32;
        let adj = self.adj[p].clone();
        for (q, e) in adj {
            let state = self.edge_state[e];
            if state == EdgeState::Connected || (is_potential && state == EdgeState::Undecided) {
                self.compute_regions_dfs(q, id, region, region_id, is_potential);
            }
        }
    }

    fn compute_regions(
        &self,
        regions: &mut Vec<Vec<usize>>,
        region_id: &mut Vec<i32>,
        is_potential: bool,
    ) -> usize {
        let n = self.vertices.len();
        let mut n_regions = 0;
        region_id.iter_mut().for_each(|x| *x = -1);
        for i in 0..n {
            if region_id[i] >= 0 {
                continue;
            }
            regions[n_regions].clear();
            self.compute_regions_dfs(
                i,
                n_regions,
                &mut regions[n_regions],
                region_id,
                is_potential,
            );
            n_regions += 1;
        }
        n_regions
    }

    // ── Reason helpers ──────────────────────────────────────────────────

    fn reason_decided_connecting_path(&self, src: usize, dest: usize) -> Vec<Lit> {
        if src == dest {
            return Vec::new();
        }
        let n = self.vertices.len();
        let mut origin: Vec<Option<(usize, usize)>> = vec![None; n]; // (prev_vertex, edge_id)
        let mut found = vec![false; n];
        found[src] = true;
        origin[src] = Some((usize::MAX, usize::MAX)); // sentinel
        let mut queue = VecDeque::new();
        queue.push_back(src);
        'bfs: while let Some(u) = queue.pop_front() {
            for &(v, e) in &self.adj[u] {
                if self.edge_state[e] != EdgeState::Connected {
                    continue;
                }
                if found[v] {
                    continue;
                }
                found[v] = true;
                origin[v] = Some((u, e));
                if v == dest {
                    break 'bfs;
                }
                queue.push_back(v);
            }
        }
        assert!(found[dest]);
        let mut ret = Vec::new();
        let mut p = dest;
        while p != src {
            let (prev, e) = origin[p].unwrap();
            ret.push(!self.edge_lits[e]);
            p = prev;
        }
        ret
    }

    fn reason_decided_region(&self, id: usize) -> Vec<Lit> {
        let mut ret = Vec::new();
        for &p in &self.decided_regions[id] {
            for &(q, e) in &self.adj[p] {
                if self.edge_state[e] == EdgeState::Connected {
                    // decided_region_id[q] should == id
                    if p < q {
                        ret.push(!self.edge_lits[e]);
                    }
                }
            }
        }
        ret
    }

    fn reason_potential_region(&self, id: usize) -> Vec<Lit> {
        let mut ret = Vec::new();
        for &p in &self.potential_regions[id] {
            for &(q, e) in &self.adj[p] {
                if self.potential_region_id[q] as usize != id {
                    assert_eq!(self.edge_state[e], EdgeState::Disconnected);
                    ret.push(self.edge_lits[e]);
                }
            }
        }
        ret
    }

    // ── Main check ──────────────────────────────────────────────────────

    fn run_check(&mut self, solver: &mut Solver, ci: ConstraintIdx) -> Option<Vec<Lit>> {
        let n = self.vertices.len();
        let m = self.edge_lits.len();

        // Update edge states
        for i in 0..m {
            match solver.value_of(self.edge_lits[i]) {
                LBool::True => self.edge_state[i] = EdgeState::Disconnected,
                LBool::False => self.edge_state[i] = EdgeState::Connected,
                LBool::Undef => self.edge_state[i] = EdgeState::Undecided,
            }
        }

        // Update size bounds for vertices
        for i in 0..n {
            if self.vertices[i].is_absent() {
                continue;
            }
            // Lower bound: largest index where lits[idx] is TRUE
            {
                let mut left = 0usize;
                let mut right = self.vertices[i].values.len() - 1;
                while left < right {
                    let mid = (left + right + 1) / 2;
                    if solver.value_of(self.vertices[i].lits[mid - 1]) == LBool::True {
                        left = mid;
                    } else {
                        right = mid - 1;
                    }
                }
                self.size_lb[i] = self.vertices[i].values[left];
                self.size_lb_reason[i] = if left == 0 {
                    None
                } else {
                    Some(self.vertices[i].lits[left - 1])
                };
            }
            // Upper bound: smallest index where lits[idx] is FALSE
            {
                let mut left = 0usize;
                let mut right = self.vertices[i].values.len() - 1;
                while left < right {
                    let mid = (left + right) / 2;
                    if solver.value_of(self.vertices[i].lits[mid]) == LBool::False {
                        right = mid;
                    } else {
                        left = mid + 1;
                    }
                }
                self.size_ub[i] = self.vertices[i].values[left];
                self.size_ub_reason[i] = if left == self.vertices[i].values.len() - 1 {
                    None
                } else {
                    Some(!self.vertices[i].lits[left])
                };
            }
        }

        // Compute regions
        let mut decided_region_id: Vec<i32> = vec![-1; n];
        let mut potential_region_id: Vec<i32> = vec![-1; n];
        let n_decided = {
            let mut r = self.decided_regions.clone();
            let cnt = self.compute_regions(&mut r, &mut decided_region_id, false);
            self.decided_regions = r;
            cnt
        };
        let n_potential = {
            let mut r = self.potential_regions.clone();
            let cnt = self.compute_regions(&mut r, &mut potential_region_id, true);
            self.potential_regions = r;
            cnt
        };
        for i in 0..n {
            self.decided_region_id[i] = decided_region_id[i].max(0) as usize;
            self.potential_region_id[i] = potential_region_id[i].max(0) as usize;
        }

        // ── Check 1: No borders within a decided region ─────────────────
        for u in 0..n {
            let adj_u = self.adj[u].clone();
            for (v, e) in adj_u {
                if decided_region_id[u] == decided_region_id[v] {
                    if self.edge_state[e] == EdgeState::Disconnected {
                        let mut ret = self.reason_decided_connecting_path(u, v);
                        ret.push(self.edge_lits[e]);
                        return Some(ret);
                    } else if self.edge_state[e] == EdgeState::Undecided {
                        let ret = self.reason_decided_connecting_path(u, v);
                        self.reasons_prop.insert(!self.edge_lits[e], ret);
                        // Enqueue ~edge_lits[e] (force connected)
                        assert!(solver.constraint_enqueue(!self.edge_lits[e], ci));
                    }
                }
            }
        }

        // ── Check 2: Decided regions – size constraints ─────────────────
        for r in 0..n_decided {
            let r_size = self.decided_regions[r].len() as i32;
            let mut least_ub = n as i32;
            let mut least_ub_pos: i32 = -1;

            let region = self.decided_regions[r].clone();
            for &p in &region {
                if self.vertices[p].is_absent() {
                    continue;
                }
                if least_ub > self.size_ub[p] {
                    least_ub = self.size_ub[p];
                    least_ub_pos = p as i32;
                }
                if self.size_ub[p] < r_size {
                    let mut ret = self.reason_decided_region(r);
                    if let Some(x) = self.vertices[p].at_most(r_size - 1) {
                        assert_ne!(x, Lit::UNDEF);
                        assert_eq!(solver.value_of(x), LBool::True);
                        ret.push(x);
                    }
                    return Some(ret);
                }
                if self.size_lb[p] < r_size {
                    if let Some(x) = self.vertices[p].at_least(r_size) {
                        assert_ne!(x, Lit::UNDEF);
                        if solver.value_of(x) == LBool::Undef {
                            let reason = self.reason_decided_region(r);
                            self.reasons_prop.insert(x, reason);
                            assert!(solver.constraint_enqueue(x, ci));
                        }
                    }
                }
            }

            for &p in &region {
                if self.vertices[p].is_absent() {
                    continue;
                }
                if least_ub < self.size_lb[p] {
                    assert!(least_ub_pos >= 0);
                    let lup = least_ub_pos as usize;
                    let mut ret = self.reason_decided_connecting_path(lup, p);
                    if let Some(r_lit) = self.size_ub_reason[lup] {
                        ret.push(r_lit);
                    }
                    if let Some(x) = self.vertices[p].at_least(least_ub + 1) {
                        assert_ne!(x, Lit::UNDEF);
                        assert_eq!(solver.value_of(x), LBool::True);
                        ret.push(x);
                    }
                    return Some(ret);
                }
            }
        }

        // ── Check 3: Potential regions – upper size bounds ──────────────
        for r in 0..n_potential {
            let r_size = self.potential_regions[r].len() as i32;
            let region = self.potential_regions[r].clone();
            let mut cached_reason: Option<Vec<Lit>> = None;

            for &p in &region {
                if self.vertices[p].is_absent() {
                    continue;
                }
                if self.size_lb[p] > r_size {
                    let reason_r =
                        cached_reason.get_or_insert_with(|| self.reason_potential_region(r));
                    let mut ret = reason_r.clone();
                    if let Some(x) = self.vertices[p].at_least(r_size + 1) {
                        assert_ne!(x, Lit::UNDEF);
                        assert_eq!(solver.value_of(x), LBool::True);
                        ret.push(x);
                    }
                    return Some(ret);
                }
                if self.size_ub[p] > r_size {
                    if let Some(x) = self.vertices[p].at_most(r_size) {
                        assert_ne!(x, Lit::UNDEF);
                        if solver.value_of(x) == LBool::Undef {
                            let reason_r = cached_reason
                                .get_or_insert_with(|| self.reason_potential_region(r))
                                .clone();
                            self.reasons_prop.insert(x, reason_r);
                            assert!(solver.constraint_enqueue(x, ci));
                        }
                    }
                }
            }
        }

        // ── Check 3a: Non-overlapping bounds sum ────────────────────────
        for r in 0..n_potential {
            let region = &self.potential_regions[r];
            // Build (ub, lb, cell_id) tuples, sort by ub
            let mut cells: Vec<(i32, i32, usize)> = region
                .iter()
                .map(|&p| (self.size_ub[p], self.size_lb[p], p))
                .collect();
            cells.sort();

            let mut cur = 0i32;
            let mut min_required = 0i32;
            let mut non_overlapping: Vec<usize> = Vec::new();

            for (ub, lb, p) in &cells {
                if cur < *lb {
                    min_required += lb;
                    cur = *ub;
                    non_overlapping.push(*p);
                }
            }

            if min_required > region.len() as i32 {
                let mut ret = self.reason_potential_region(r);
                for p in non_overlapping {
                    if let Some(r_lit) = self.size_lb_reason[p] {
                        ret.push(r_lit);
                    }
                    if let Some(r_lit) = self.size_ub_reason[p] {
                        ret.push(r_lit);
                    }
                }
                return Some(ret);
            }
        }

        None
    }
}

impl Constraint for GraphDivision {
    fn initialize(&mut self, solver: &mut Solver, ci: ConstraintIdx) -> bool {
        let mut lits_unique: Vec<Lit> = Vec::new();
        for v in &self.vertices {
            for &l in &v.lits {
                lits_unique.push(l);
                lits_unique.push(!l);
            }
        }
        for &l in &self.edge_lits {
            lits_unique.push(l);
            lits_unique.push(!l);
        }
        lits_unique.sort();
        lits_unique.dedup();
        for l in lits_unique {
            solver.add_watch(l, ci);
        }

        // Validate initial domain bounds
        for v in &self.vertices {
            if v.is_absent() {
                continue;
            }
            if v.values[0] > self.vertices.len() as i32 {
                return false;
            }
        }

        if self.run_check(solver, ci).is_some() {
            return false;
        }
        true
    }

    fn propagate(&mut self, solver: &mut Solver, p: Lit, ci: ConstraintIdx) -> bool {
        solver.register_undo(p.var(), ci);

        if solver.num_pending(ci) > 0 {
            // Lazy propagation
            self.reasons.push(Vec::new());
            return true;
        }

        let result = self.run_check(solver, ci);

        if let Some(mut conflict_lits) = result {
            conflict_lits.sort();
            conflict_lits.dedup();
            self.reasons.push(conflict_lits);
            false
        } else {
            self.reasons.push(Vec::new());
            true
        }
    }

    fn calc_reason(
        &mut self,
        _solver: &mut Solver,
        p: Option<Lit>,
        extra: Option<Lit>,
        out_reason: &mut Vec<Lit>,
    ) {
        if p.is_none() {
            // Conflict
            if let Some(last) = self.reasons.last() {
                for &l in last {
                    out_reason.push(l);
                }
            }
        } else if let Some(pl) = p {
            if let Some(reason_lits) = self.reasons_prop.get(&pl) {
                for &l in reason_lits.clone().iter() {
                    out_reason.push(l);
                }
            }
        }
        if let Some(extra_lit) = extra {
            out_reason.push(extra_lit);
        }
    }

    fn undo(&mut self, _solver: &mut Solver, _p: Lit) {
        self.reasons.pop();
    }
}
