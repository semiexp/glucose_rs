use std::collections::VecDeque;

use crate::clause::{ClauseDb, ClauseIdx, CLAUSE_UNDEF};
use crate::constraint::{Constraint, ConstraintIdx};
use crate::types::{LBool, Lit, Var, VAR_UNDEF};
use crate::watch::{WatchList, Watcher};

const RATIO_REMOVE_CLAUSES: usize = 2;

// ──────────────────────────────────────────────
// ConflictReason
// ──────────────────────────────────────────────
/// Describes the source of a BCP conflict: either a clause or a non-clause constraint.
#[derive(Clone, Copy, Debug)]
pub enum ConflictReason {
    Clause(ClauseIdx),
    Constraint(ConstraintIdx),
}

// ──────────────────────────────────────────────
// BoundedQueue: sliding-window average
// ──────────────────────────────────────────────
/// A fixed-capacity sliding-window queue that tracks a running sum for fast average computation.
///
/// Used by the Glucose restart heuristic to maintain moving averages of:
/// - LBD (Literal Block Distance) values of recently learned clauses (`lbd_queue`)
/// - trail sizes at each restart opportunity (`trail_queue`)
///
/// Corresponds to `BoundedQueue` in C++ Glucose (`core/BoundedQueue.h`).
struct BoundedQueue {
    elems: VecDeque<u32>,
    max_size: usize,
    sum: u64,
}

impl BoundedQueue {
    fn new(max_size: usize) -> Self {
        BoundedQueue {
            elems: VecDeque::new(),
            max_size,
            sum: 0,
        }
    }

    fn push(&mut self, val: u32) {
        if self.elems.len() == self.max_size {
            self.sum -= self.elems.pop_front().unwrap() as u64;
        }
        self.elems.push_back(val);
        self.sum += val as u64;
    }

    fn is_valid(&self) -> bool {
        self.elems.len() == self.max_size
    }

    /// Returns the sliding-window average. Panics if the queue is empty.
    /// Always check `is_valid()` or `!is_empty()` before calling.
    fn avg(&self) -> f64 {
        debug_assert!(!self.elems.is_empty(), "avg() called on empty BoundedQueue");
        if self.elems.is_empty() {
            return 0.0;
        }
        self.sum as f64 / self.elems.len() as f64
    }

    fn clear(&mut self) {
        self.elems.clear();
        self.sum = 0;
    }
}

// ──────────────────────────────────────────────
// OrderHeap: indexed binary max-heap by activity
// ──────────────────────────────────────────────
/// An indexed binary max-heap that orders variables by their VSIDS activity score.
///
/// Supports O(log n) insert/remove-max and O(log n) increase-key (used when a
/// variable's activity is bumped during conflict analysis).
///
/// Corresponds to the `Heap<VarOrderLt>` field (`order_heap`) in C++ Glucose `Solver.h`.
const HEAP_NONE: usize = usize::MAX;

struct OrderHeap {
    heap: Vec<Var>,
    pos: Vec<usize>,
}

#[allow(dead_code)]
impl OrderHeap {
    fn new(n: usize) -> Self {
        OrderHeap {
            heap: Vec::new(),
            pos: vec![HEAP_NONE; n],
        }
    }

    fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    fn contains(&self, v: Var) -> bool {
        (v as usize) < self.pos.len() && self.pos[v as usize] != HEAP_NONE
    }

    fn insert(&mut self, v: Var, activity: &[f64]) {
        if self.contains(v) {
            return;
        }
        let idx = self.heap.len();
        self.pos[v as usize] = idx;
        self.heap.push(v);
        self.sift_up(idx, activity);
    }

    fn remove_max(&mut self, activity: &[f64]) -> Option<Var> {
        if self.heap.is_empty() {
            return None;
        }
        let top = self.heap[0];
        self.pos[top as usize] = HEAP_NONE;
        let n = self.heap.len();
        if n > 1 {
            let last = self.heap[n - 1];
            self.heap[0] = last;
            self.pos[last as usize] = 0;
            self.heap.pop();
            self.sift_down(0, activity);
        } else {
            self.heap.pop();
        }
        Some(top)
    }

    fn increase(&mut self, v: Var, activity: &[f64]) {
        let idx = self.pos[v as usize];
        if idx != HEAP_NONE {
            self.sift_up(idx, activity);
        }
    }

    fn sift_up(&mut self, mut i: usize, activity: &[f64]) {
        let v = self.heap[i];
        while i > 0 {
            let parent = (i - 1) / 2;
            if activity[self.heap[parent] as usize] < activity[v as usize] {
                self.heap[i] = self.heap[parent];
                self.pos[self.heap[i] as usize] = i;
                i = parent;
            } else {
                break;
            }
        }
        self.heap[i] = v;
        self.pos[v as usize] = i;
    }

    fn sift_down(&mut self, mut i: usize, activity: &[f64]) {
        let v = self.heap[i];
        let n = self.heap.len();
        loop {
            let left = 2 * i + 1;
            let right = 2 * i + 2;
            let mut largest = i;
            if left < n
                && activity[self.heap[left] as usize] > activity[self.heap[largest] as usize]
            {
                largest = left;
            }
            if right < n
                && activity[self.heap[right] as usize] > activity[self.heap[largest] as usize]
            {
                largest = right;
            }
            if largest == i {
                break;
            }
            self.heap[i] = self.heap[largest];
            self.pos[self.heap[i] as usize] = i;
            i = largest;
        }
        self.heap[i] = v;
        self.pos[v as usize] = i;
    }
}

// ──────────────────────────────────────────────
// Solver
// ──────────────────────────────────────────────
pub struct Solver {
    // Problem
    num_vars: usize,

    // Assignments
    assigns: Vec<LBool>,
    polarity: Vec<bool>,
    decision: Vec<bool>,

    // Trail
    trail: Vec<Lit>,
    trail_lim: Vec<usize>,
    qhead: usize,

    // Clause database
    db: ClauseDb,
    clauses: Vec<ClauseIdx>,
    learnts: Vec<ClauseIdx>,

    // Watch lists
    watches: WatchList,
    watches_bin: WatchList,

    // Propagation metadata
    reason: Vec<ClauseIdx>,
    level: Vec<u32>,

    // VSIDS
    activity: Vec<f64>,
    var_inc: f64,
    var_decay: f64,
    max_var_decay: f64,

    // Clause activity
    cla_inc: f64,
    clause_decay: f64,

    // Order heap
    order_heap: OrderHeap,

    // Glucose restart heuristics
    lbd_queue: BoundedQueue,
    trail_queue: BoundedQueue,
    k_factor: f64,
    r_factor: f64,
    sum_lbd: f64,

    // Clause DB reduction
    next_reduce_db: u64,
    #[allow(dead_code)]
    first_reduce_db: u64,
    inc_reduce_db: u64,
    special_inc_reduce_db: u64,
    lb_lbd_frozen_clause: u32,
    lb_size_minimizing_clause: usize,
    lb_lbd_minimizing_clause: u32,

    // Statistics
    conflicts: u64,
    conflicts_restarts: u64,
    decisions: u64,
    propagations: u64,
    pub restarts: u64,

    // Model (set when SAT)
    pub model: Vec<LBool>,

    // Solver status
    ok: bool,

    // Seen array for conflict analysis (reused across calls)
    seen: Vec<u8>,

    // perm_diff for LBD computation
    perm_diff: Vec<u64>,
    perm_diff_timer: u64,

    // ── Non-clause constraint framework ──────────────────────────────────
    /// Registered constraints.  Stored as `Option` to allow the "take" pattern during
    /// callbacks (temporarily remove so we can pass `&mut Solver` at the same time).
    pub constraints: Vec<Option<Box<dyn Constraint>>>,
    /// Per-literal watch lists for constraints: `constr_watches[lit.0]` contains the
    /// indices of constraints that want to be notified when that literal becomes TRUE.
    pub constr_watches: Vec<Vec<ConstraintIdx>>,
    /// Per-variable undo lists: `undo_lists[var]` contains constraint indices that
    /// registered for undo notification on this variable.
    pub undo_lists: Vec<Vec<ConstraintIdx>>,
    /// Per-variable constraint reason: `Some(ci)` when constraint `ci` propagated this var.
    pub nc_reason: Vec<Option<ConstraintIdx>>,
    /// Per-constraint pending propagation count (number of watched literals currently in
    /// the propagation queue that have not yet been delivered to the constraint).
    pub constr_pending: Vec<i32>,
    /// The TRUE literal that caused the most recent failed `constraint_enqueue` call.
    /// Set to `Lit::UNDEF` when not applicable.
    pub enqueue_failure: Lit,
}

#[allow(dead_code)]
impl Solver {
    pub fn new() -> Self {
        Solver {
            num_vars: 0,
            assigns: Vec::new(),
            polarity: Vec::new(),
            decision: Vec::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            qhead: 0,
            db: ClauseDb::new(),
            clauses: Vec::new(),
            learnts: Vec::new(),
            watches: WatchList::new(0),
            watches_bin: WatchList::new(0),
            reason: Vec::new(),
            level: Vec::new(),
            activity: Vec::new(),
            var_inc: 1.0,
            var_decay: 0.8,
            max_var_decay: 0.95,
            cla_inc: 1.0,
            clause_decay: 0.999,
            order_heap: OrderHeap::new(0),
            lbd_queue: BoundedQueue::new(50),
            trail_queue: BoundedQueue::new(5000),
            k_factor: 0.8,
            r_factor: 1.4,
            sum_lbd: 0.0,
            next_reduce_db: 2000,
            first_reduce_db: 2000,
            inc_reduce_db: 300,
            special_inc_reduce_db: 1000,
            lb_lbd_frozen_clause: 30,
            lb_size_minimizing_clause: 30,
            lb_lbd_minimizing_clause: 6,
            conflicts: 0,
            conflicts_restarts: 0,
            decisions: 0,
            propagations: 0,
            restarts: 0,
            model: Vec::new(),
            ok: true,
            seen: Vec::new(),
            perm_diff: Vec::new(),
            perm_diff_timer: 0,
            constraints: Vec::new(),
            constr_watches: Vec::new(),
            undo_lists: Vec::new(),
            nc_reason: Vec::new(),
            constr_pending: Vec::new(),
            enqueue_failure: Lit::UNDEF,
        }
    }

    pub fn new_var(&mut self) -> Var {
        let v = self.num_vars as Var;
        self.num_vars += 1;

        self.assigns.push(LBool::Undef);
        self.polarity.push(false);
        self.decision.push(true);
        self.reason.push(CLAUSE_UNDEF);
        self.level.push(0);
        self.activity.push(0.0);
        self.seen.push(0);
        self.perm_diff.push(0);

        let new_lits = self.num_vars * 2;
        self.watches.grow(new_lits);
        self.watches_bin.grow(new_lits);
        self.order_heap.pos.push(HEAP_NONE);

        // Grow constraint watch lists: two entries per variable (pos and neg literal)
        self.constr_watches.push(Vec::new()); // Lit(2*v)   = positive lit
        self.constr_watches.push(Vec::new()); // Lit(2*v+1) = negative lit
        self.undo_lists.push(Vec::new());
        self.nc_reason.push(None);

        self.order_heap.insert(v, &self.activity);

        v
    }

    fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    fn value_lit(&self, lit: Lit) -> LBool {
        self.assigns[lit.var() as usize].xor(lit.is_neg())
    }

    fn value_var(&self, v: Var) -> LBool {
        self.assigns[v as usize]
    }

    // ── Public constraint API ──────────────────────────────────────────

    /// Value of a literal; convenience wrapper for constraint implementations.
    pub fn value_of(&self, lit: Lit) -> LBool {
        self.value_lit(lit)
    }

    /// Value of a variable; convenience wrapper for constraint implementations.
    pub fn value_of_var(&self, v: Var) -> LBool {
        self.value_var(v)
    }

    /// Current decision level; convenience wrapper for constraint implementations.
    pub fn current_level(&self) -> usize {
        self.decision_level()
    }

    /// Number of pending (not-yet-delivered) watched literals for constraint `ci`.
    /// Constraints can use this for lazy propagation: skip expensive checks when > 0.
    pub fn num_pending(&self, ci: ConstraintIdx) -> i32 {
        self.constr_pending[ci]
    }

    /// Register `ci` to be notified (via `propagate`) when `lit` becomes TRUE.
    pub fn add_watch(&mut self, lit: Lit, ci: ConstraintIdx) {
        self.constr_watches[lit.0 as usize].push(ci);
    }

    /// Register `ci` to have `undo` called when `var` is backtracked.
    pub fn register_undo(&mut self, var: Var, ci: ConstraintIdx) {
        self.undo_lists[var as usize].push(ci);
    }

    /// Enqueue `lit` as TRUE on behalf of constraint `ci`.
    /// Returns `false` if `lit` is already FALSE (conflict); in that case
    /// `self.enqueue_failure` is set to the TRUE literal that conflicted (`!lit`).
    pub fn constraint_enqueue(&mut self, lit: Lit, ci: ConstraintIdx) -> bool {
        match self.value_lit(lit) {
            LBool::True => true,
            LBool::False => {
                // !lit is the TRUE literal that conflicts with our attempt to set lit=TRUE
                self.enqueue_failure = !lit;
                false
            }
            LBool::Undef => {
                let v = lit.var() as usize;
                self.assigns[v] = if lit.is_neg() {
                    LBool::False
                } else {
                    LBool::True
                };
                self.level[v] = self.decision_level() as u32;
                self.reason[v] = CLAUSE_UNDEF;
                self.nc_reason[v] = Some(ci);
                self.trail.push(lit);
                // Increment pending counts for constraints watching this literal
                Self::add_num_pending_static(
                    &self.constr_watches,
                    &mut self.constr_pending,
                    lit,
                    1,
                );
                true
            }
        }
    }

    /// Add a non-clause constraint to the solver.  Must be called at decision level 0.
    /// Calls `initialize` on the constraint and runs BCP; returns `false` if UNSAT.
    pub fn add_constraint(&mut self, constraint: Box<dyn Constraint>) -> bool {
        if !self.ok {
            return false;
        }
        debug_assert_eq!(self.decision_level(), 0);

        let ci = self.constraints.len();
        self.constraints.push(Some(constraint));
        self.constr_pending.push(0);

        // initialize: uses "take" pattern so we can pass &mut self simultaneously
        let mut c = self.constraints[ci].take().unwrap();
        let ok = c.initialize(self, ci);
        self.constraints[ci] = Some(c);

        if !ok {
            self.ok = false;
            return false;
        }

        if self.propagate().is_some() {
            self.ok = false;
            return false;
        }

        true
    }

    // ── Internal helpers ───────────────────────────────────────────────

    /// Increment or decrement pending counts for all constraints watching `lit`.
    fn add_num_pending_static(
        constr_watches: &[Vec<ConstraintIdx>],
        constr_pending: &mut [i32],
        lit: Lit,
        delta: i32,
    ) {
        if constr_watches.is_empty() {
            return;
        }
        let idx = lit.0 as usize;
        if idx >= constr_watches.len() {
            return;
        }
        for &ci in &constr_watches[idx] {
            constr_pending[ci] += delta;
        }
    }

    /// Drain pending counts for `p`'s constraint watches, then drain the rest of the queue.
    /// Called when a clause conflict is detected (constraint loop is skipped for `p`).
    fn drain_pending_for_clause_conflict(&mut self, p: Lit) {
        // p's constraint watches were not processed (clause conflict found first)
        let n = if (p.0 as usize) < self.constr_watches.len() {
            self.constr_watches[p.0 as usize].len()
        } else {
            0
        };
        for k in 0..n {
            let ci = self.constr_watches[p.0 as usize][k];
            self.constr_pending[ci] -= 1;
        }
        // Drain remaining queue
        while self.qhead < self.trail.len() {
            let q = self.trail[self.qhead];
            self.qhead += 1;
            let m = if (q.0 as usize) < self.constr_watches.len() {
                self.constr_watches[q.0 as usize].len()
            } else {
                0
            };
            for k in 0..m {
                let ci = self.constr_watches[q.0 as usize][k];
                self.constr_pending[ci] -= 1;
            }
        }
    }

    /// Drain pending counts for the rest of the queue (after a constraint conflict).
    fn drain_pending_queue(&mut self) {
        while self.qhead < self.trail.len() {
            let q = self.trail[self.qhead];
            self.qhead += 1;
            let m = if (q.0 as usize) < self.constr_watches.len() {
                self.constr_watches[q.0 as usize].len()
            } else {
                0
            };
            for k in 0..m {
                let ci = self.constr_watches[q.0 as usize][k];
                self.constr_pending[ci] -= 1;
            }
        }
    }

    fn unchecked_enqueue(&mut self, lit: Lit, reason: ClauseIdx) {
        let v = lit.var() as usize;
        debug_assert!(self.assigns[v] == LBool::Undef);
        self.assigns[v] = if lit.is_neg() {
            LBool::False
        } else {
            LBool::True
        };
        self.level[v] = self.decision_level() as u32;
        self.reason[v] = reason;
        self.nc_reason[v] = None;
        self.trail.push(lit);
        // Increment pending counts for constraints watching this literal
        Self::add_num_pending_static(&self.constr_watches, &mut self.constr_pending, lit, 1);
    }

    fn attach_clause(&mut self, cref: ClauseIdx) {
        let len = self.db.clauses[cref as usize].lits.len();
        debug_assert!(len >= 2);
        let lit0 = self.db.clauses[cref as usize].lits[0];
        let lit1 = self.db.clauses[cref as usize].lits[1];
        // Convention: watcher stored at `lit` is triggered when `lit` becomes FALSE.
        // In propagate we read watches[false_lit] where false_lit = !p.
        if len == 2 {
            self.watches_bin.add(
                lit0,
                Watcher {
                    cref,
                    blocker: lit1,
                },
            );
            self.watches_bin.add(
                lit1,
                Watcher {
                    cref,
                    blocker: lit0,
                },
            );
        } else {
            self.watches.add(
                lit0,
                Watcher {
                    cref,
                    blocker: lit1,
                },
            );
            self.watches.add(
                lit1,
                Watcher {
                    cref,
                    blocker: lit0,
                },
            );
        }
    }

    fn detach_clause(&mut self, cref: ClauseIdx) {
        let len = self.db.clauses[cref as usize].lits.len();
        let lit0 = self.db.clauses[cref as usize].lits[0];
        let lit1 = self.db.clauses[cref as usize].lits[1];
        if len == 2 {
            self.watches_bin.get_mut(lit0).retain(|w| w.cref != cref);
            self.watches_bin.get_mut(lit1).retain(|w| w.cref != cref);
        } else {
            self.watches.get_mut(lit0).retain(|w| w.cref != cref);
            self.watches.get_mut(lit1).retain(|w| w.cref != cref);
        }
    }

    fn is_locked(&self, cref: ClauseIdx) -> bool {
        let lit0 = self.db.clauses[cref as usize].lits[0];
        let v = lit0.var() as usize;
        self.value_lit(lit0) == LBool::True && self.nc_reason[v].is_none() && self.reason[v] == cref
    }

    fn ensure_binary_clause_first_lit_true(&mut self, cref: ClauseIdx) {
        if self.db.clauses[cref as usize].lits.len() != 2 {
            return;
        }
        let lit0 = self.db.clauses[cref as usize].lits[0];
        if self.value_lit(lit0) == LBool::False {
            self.db.clauses[cref as usize].lits.swap(0, 1);
        }
    }

    // ── BCP ────────────────────────────────────
    fn propagate(&mut self) -> Option<ConflictReason> {
        let mut bin_ws = vec![];
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            self.propagations += 1;
            let false_lit = !p;

            // ── Binary clause watches ──────────────
            std::mem::swap(&mut bin_ws, self.watches_bin.get_mut(false_lit));
            for &w in &bin_ws {
                match self.value_lit(w.blocker) {
                    LBool::True => {}
                    LBool::False => {
                        std::mem::swap(&mut bin_ws, self.watches_bin.get_mut(false_lit));
                        self.drain_pending_for_clause_conflict(p);
                        return Some(ConflictReason::Clause(w.cref));
                    }
                    LBool::Undef => {
                        self.unchecked_enqueue(w.blocker, w.cref);
                    }
                }
            }
            std::mem::swap(&mut bin_ws, self.watches_bin.get_mut(false_lit));

            // ── Long clause watches ────────────────
            let mut ws = std::mem::take(self.watches.get_mut(false_lit));
            let mut i = 0usize;
            let mut j = 0usize;
            let mut clause_conflict: Option<ClauseIdx> = None;

            'outer: while i < ws.len() {
                let blocker = ws[i].blocker;
                let cref = ws[i].cref;

                if self.db.clauses[cref as usize].header.deleted {
                    i += 1;
                    continue;
                }

                if self.value_lit(blocker) == LBool::True {
                    ws[j] = ws[i];
                    j += 1;
                    i += 1;
                    continue;
                }

                if self.db.clauses[cref as usize].lits[0] == false_lit {
                    self.db.clauses[cref as usize].lits.swap(0, 1);
                }

                let first = self.db.clauses[cref as usize].lits[0];

                if self.value_lit(first) == LBool::True {
                    ws[j] = Watcher {
                        cref,
                        blocker: first,
                    };
                    j += 1;
                    i += 1;
                    continue;
                }

                let cl_len = self.db.clauses[cref as usize].lits.len();
                let mut new_watch: Option<usize> = None;
                for k in 2..cl_len {
                    if self.value_lit(self.db.clauses[cref as usize].lits[k]) != LBool::False {
                        new_watch = Some(k);
                        break;
                    }
                }

                if let Some(k) = new_watch {
                    self.db.clauses[cref as usize].lits.swap(1, k);
                    let new_lit = self.db.clauses[cref as usize].lits[1];
                    self.watches.add(
                        new_lit,
                        Watcher {
                            cref,
                            blocker: first,
                        },
                    );
                    i += 1;
                    continue 'outer;
                }

                ws[j] = ws[i];
                j += 1;
                i += 1;

                if self.value_lit(first) == LBool::False {
                    clause_conflict = Some(cref);
                    while i < ws.len() {
                        ws[j] = ws[i];
                        j += 1;
                        i += 1;
                    }
                    break;
                } else {
                    self.unchecked_enqueue(first, cref);
                }
            }

            ws.truncate(j);
            *self.watches.get_mut(false_lit) = ws;

            if let Some(cref) = clause_conflict {
                self.drain_pending_for_clause_conflict(p);
                return Some(ConflictReason::Clause(cref));
            }

            // ── Constraint watches ─────────────────
            let n_cw = if (p.0 as usize) < self.constr_watches.len() {
                self.constr_watches[p.0 as usize].len()
            } else {
                0
            };
            for k in 0..n_cw {
                let ci = self.constr_watches[p.0 as usize][k];
                self.constr_pending[ci] -= 1;
                self.enqueue_failure = Lit::UNDEF;

                let mut c = self.constraints[ci].take().unwrap();
                let ok = c.propagate(self, p, ci);
                self.constraints[ci] = Some(c);

                if !ok {
                    // Decrement remaining constraint watches for p
                    for l in (k + 1)..n_cw {
                        let cl = self.constr_watches[p.0 as usize][l];
                        self.constr_pending[cl] -= 1;
                    }
                    self.drain_pending_queue();
                    return Some(ConflictReason::Constraint(ci));
                }
            }
        }

        None
    }

    // ── LBD computation ────────────────────────
    fn compute_lbd(&mut self, lits: &[Lit]) -> u32 {
        self.perm_diff_timer += 1;
        let timer = self.perm_diff_timer;
        let mut lbd = 0u32;
        for &lit in lits {
            let lvl = self.level[lit.var() as usize] as usize;
            if lvl > 0 {
                if self.perm_diff.len() <= lvl {
                    self.perm_diff.resize(lvl + 1, 0);
                }
                if self.perm_diff[lvl] != timer {
                    self.perm_diff[lvl] = timer;
                    lbd += 1;
                }
            }
        }
        lbd
    }

    fn abstract_level(level: u32) -> u32 {
        1u32 << (level & 31)
    }

    /// Glucose's binary-resolution based conflict-clause minimization.
    fn minimisation_with_binary_resolution(&mut self, out_learnt: &mut Vec<Lit>) {
        if out_learnt.len() <= 1 {
            return;
        }

        let lbd = self.compute_lbd(out_learnt);
        if lbd > self.lb_lbd_minimizing_clause {
            return;
        }

        self.perm_diff_timer += 1;
        let marker = self.perm_diff_timer;
        let p = !out_learnt[0];
        let bin_watch_key = !p;

        for &lit in out_learnt.iter().skip(1) {
            self.perm_diff[lit.var() as usize] = marker;
        }

        for &w in self.watches_bin.get(bin_watch_key) {
            let imp = w.blocker;
            let v = imp.var() as usize;
            if self.perm_diff[v] == marker && self.value_lit(imp) == LBool::True {
                self.perm_diff[v] = marker - 1;
            }
        }

        let mut minimized: Vec<Lit> = Vec::with_capacity(out_learnt.len());
        minimized.push(out_learnt[0]);
        for &lit in out_learnt.iter().skip(1) {
            if self.perm_diff[lit.var() as usize] == marker {
                minimized.push(lit);
            }
        }
        *out_learnt = minimized;
    }

    // Recursively check if `p` is redundant given the current learned clause
    fn lit_redundant(&mut self, p: Lit, abs_levels: u32, to_clear: &mut Vec<Var>) -> bool {
        // Cannot minimize through constraint-propagated literals
        if self.nc_reason[p.var() as usize].is_some() {
            return false;
        }
        let mut stack: Vec<Lit> = vec![p];
        let top = to_clear.len();

        while let Some(lit) = stack.pop() {
            let v = lit.var() as usize;
            // Cannot minimize through constraint-propagated literals
            if self.nc_reason[v].is_some() {
                for i in top..to_clear.len() {
                    self.seen[to_clear[i] as usize] = 0;
                }
                to_clear.truncate(top);
                return false;
            }
            let r = self.reason[v];
            if r == CLAUSE_UNDEF {
                // Decision variable – cannot remove
                for i in top..to_clear.len() {
                    self.seen[to_clear[i] as usize] = 0;
                }
                to_clear.truncate(top);
                return false;
            }
            self.ensure_binary_clause_first_lit_true(r);
            let cl_len = self.db.clauses[r as usize].lits.len();
            for j in 1..cl_len {
                let q = self.db.clauses[r as usize].lits[j];
                let qv = q.var() as usize;
                let lvl = self.level[qv];
                if self.seen[qv] == 0 && lvl > 0 {
                    let qr = self.reason[qv];
                    if self.nc_reason[qv].is_none()
                        && qr != CLAUSE_UNDEF
                        && (Self::abstract_level(lvl) & abs_levels) != 0
                    {
                        self.seen[qv] = 3;
                        to_clear.push(q.var());
                        stack.push(q);
                    } else {
                        for i in top..to_clear.len() {
                            self.seen[to_clear[i] as usize] = 0;
                        }
                        to_clear.truncate(top);
                        return false;
                    }
                }
            }
        }
        true
    }

    // ── Conflict analysis (1-UIP) ──────────────
    /// Analyse a conflict and produce a learnt clause plus a backtrack level.
    ///
    /// `initial_conflict` is either a clause or a non-clause constraint that detected
    /// the conflict.  When constraints are involved, undo is called on constraint state
    /// for every trail position that is "walked over" during the backward scan, mirroring
    /// the C++ behaviour that maintains consistent constraint state for `calc_reason`.
    fn analyze(&mut self, initial_conflict: ConflictReason) -> (Vec<Lit>, u32) {
        let current_level = self.decision_level() as u32;
        let mut learnt: Vec<Lit> = vec![Lit::UNDEF];
        let mut btlevel: u32 = 0;
        let mut path_c: i32 = 0;
        let mut p = Lit::UNDEF;
        // C++ uses post-decrement: after loop, trail[index+1] is the found literal.
        let mut index = self.trail.len() as i32 - 1;
        let mut to_clear: Vec<Var> = Vec::new();

        // Grab enqueue_failure once; clear it so it is not re-used.
        let mut extra: Option<Lit> = if self.enqueue_failure == Lit::UNDEF {
            None
        } else {
            Some(self.enqueue_failure)
        };
        self.enqueue_failure = Lit::UNDEF;

        let mut confl = initial_conflict;

        'analyze_loop: loop {
            match confl {
                ConflictReason::Clause(cref) => {
                    // Defensive guard: decisions have no clause reason (`CLAUSE_UNDEF`).
                    // When this appears here, treat it as an empty reason instead of
                    // indexing into the clause arena with a sentinel value.
                    if cref == CLAUSE_UNDEF {
                        break 'analyze_loop;
                    }
                    let start_j: usize = if p == Lit::UNDEF { 0 } else { 1 };

                    // For binary clauses used as reason: ensure p is at lits[0]
                    if p != Lit::UNDEF {
                        self.ensure_binary_clause_first_lit_true(cref);
                    }

                    if self.db.clauses[cref as usize].header.learnt {
                        self.cla_bump_activity(cref);
                        let old_lbd = self.db.clauses[cref as usize].header.lbd;
                        if old_lbd > 2 {
                            let lits = self.db.clauses[cref as usize].lits.clone();
                            let nblevels = self.compute_lbd(&lits);
                            if nblevels + 1 < old_lbd {
                                if old_lbd <= self.lb_lbd_frozen_clause {
                                    self.db.clauses[cref as usize].header.can_be_del = false;
                                }
                                self.db.clauses[cref as usize].header.lbd = nblevels;
                            }
                        }
                    }

                    let cl_len = self.db.clauses[cref as usize].lits.len();
                    for j in start_j..cl_len {
                        // Clause lits[j] are FALSE literals (antecedents); push directly.
                        let q = self.db.clauses[cref as usize].lits[j];
                        let qv = q.var() as usize;
                        let lvl = self.level[qv];
                        if self.seen[qv] == 0 && lvl > 0 {
                            self.var_bump_activity(q.var());
                            self.seen[qv] = 1;
                            to_clear.push(q.var());
                            if lvl >= current_level {
                                path_c += 1;
                            } else {
                                learnt.push(q);
                                if lvl > btlevel {
                                    btlevel = lvl;
                                }
                            }
                        }
                    }
                }
                ConflictReason::Constraint(ci) => {
                    let p_opt = if p == Lit::UNDEF { None } else { Some(p) };
                    let cur_extra = extra.take();

                    let mut reason_lits: Vec<Lit> = Vec::new();
                    let mut c = self.constraints[ci].take().unwrap();
                    c.calc_reason(self, p_opt, cur_extra, &mut reason_lits);
                    self.constraints[ci] = Some(c);

                    // calc_reason returns TRUE literals; negate them for the learnt clause.
                    for q in reason_lits {
                        let qv = q.var() as usize;
                        let lvl = self.level[qv];
                        if self.seen[qv] == 0 && lvl > 0 {
                            self.var_bump_activity(q.var());
                            self.seen[qv] = 1;
                            to_clear.push(q.var());
                            if lvl >= current_level {
                                path_c += 1;
                            } else {
                                learnt.push(!q); // negate: q is TRUE, !q is the FALSE antecedent
                                if lvl > btlevel {
                                    btlevel = lvl;
                                }
                            }
                        }
                    }
                }
            }

            // ── Scan backward for next seen literal; undo constraints along the way ──
            // Mirrors C++: while (!seen[var(trail[index--])]);
            // After the loop, trail[index+1] is the found literal.
            let index_pre = index;
            loop {
                debug_assert!(index >= 0, "analyze: ran off the start of the trail");
                let idx = index as usize;
                let seen_val = self.seen[self.trail[idx].var() as usize];
                index -= 1;
                if seen_val != 0 {
                    break;
                }
            }
            // index+1 is the found position.  Undo constraints for all positions
            // from index_pre down to index+1 (inclusive) — mirrors C++ undo loop.
            // This includes the found literal itself, so calc_reason in the next
            // iteration sees the constraint state *before* that literal was assigned.
            for i in ((index + 1) as usize..=index_pre as usize).rev() {
                let undo_lit = self.trail[i];
                let undo_var = undo_lit.var() as usize;
                // Drain the undo list (popping matches C++ `while undoLists[x].size() > 0`)
                while let Some(undo_ci) = self.undo_lists[undo_var].pop() {
                    let mut c = self.constraints[undo_ci].take().unwrap();
                    c.undo(self, undo_lit);
                    self.constraints[undo_ci] = Some(c);
                }
            }

            p = self.trail[(index + 1) as usize];
            self.seen[p.var() as usize] = 0;
            path_c -= 1;

            if path_c <= 0 {
                break;
            }

            // Get the reason for the next p
            confl = if let Some(ci) = self.nc_reason[p.var() as usize] {
                ConflictReason::Constraint(ci)
            } else {
                ConflictReason::Clause(self.reason[p.var() as usize])
            };
        }

        learnt[0] = !p;

        // Deep minimization (ccmin_mode = 2)
        let mut abs_levels: u32 = 0;
        for &lit in &learnt[1..] {
            abs_levels |= Self::abstract_level(self.level[lit.var() as usize]);
        }

        let mut j = 1usize;
        for i in 1..learnt.len() {
            let lit = learnt[i];
            let v = lit.var() as usize;
            if self.nc_reason[v].is_some()
                || self.reason[v] == CLAUSE_UNDEF
                || !self.lit_redundant(lit, abs_levels, &mut to_clear)
            {
                learnt[j] = lit;
                j += 1;
            }
        }
        learnt.truncate(j);

        if self.constraints.is_empty() && learnt.len() <= self.lb_size_minimizing_clause {
            self.minimisation_with_binary_resolution(&mut learnt);
        }

        // Clear seen for all variables we touched
        for &v in &to_clear {
            self.seen[v as usize] = 0;
        }

        (learnt, btlevel)
    }

    // ── Variable activity ──────────────────────
    fn var_bump_activity(&mut self, v: Var) {
        self.activity[v as usize] += self.var_inc;
        if self.activity[v as usize] > 1e100 {
            for a in &mut self.activity {
                *a /= 1e100;
            }
            self.var_inc /= 1e100;
        }
        self.order_heap.increase(v, &self.activity);
    }

    fn var_decay_activity(&mut self) {
        self.var_inc /= self.var_decay;
    }

    // ── Clause activity ────────────────────────
    fn cla_bump_activity(&mut self, cref: ClauseIdx) {
        self.db.clauses[cref as usize].activity += self.cla_inc as f32;
        if self.db.clauses[cref as usize].activity > 1e20_f32 {
            for c in &mut self.db.clauses {
                if c.header.learnt {
                    c.activity /= 1e20_f32;
                }
            }
            self.cla_inc /= 1e20;
        }
    }

    fn clause_decay_activity(&mut self) {
        self.cla_inc /= self.clause_decay;
    }

    // ── Backtracking ───────────────────────────
    fn backtrack(&mut self, level: usize) {
        if self.decision_level() <= level {
            return;
        }
        let trail_start = self.trail_lim[level];
        for i in (trail_start..self.trail.len()).rev() {
            let lit = self.trail[i];
            let v = lit.var();
            self.polarity[v as usize] = lit.is_neg();
            self.assigns[v as usize] = LBool::Undef;
            self.reason[v as usize] = CLAUSE_UNDEF;
            self.nc_reason[v as usize] = None;
            if !self.order_heap.contains(v) {
                self.order_heap.insert(v, &self.activity);
            }
            // Notify constraints via undo (drain the list – each entry is called exactly once)
            while let Some(ci) = self.undo_lists[v as usize].pop() {
                let mut c = self.constraints[ci].take().unwrap();
                c.undo(self, lit);
                self.constraints[ci] = Some(c);
            }
        }
        self.trail.truncate(trail_start);
        self.qhead = trail_start;
        self.trail_lim.truncate(level);
    }

    // ── Branch literal selection (VSIDS) ───────
    fn pick_branch_lit(&mut self) -> Option<Lit> {
        let mut next = VAR_UNDEF;
        loop {
            match self.order_heap.remove_max(&self.activity) {
                None => break,
                Some(v) => {
                    if self.assigns[v as usize] == LBool::Undef && self.decision[v as usize] {
                        next = v;
                        break;
                    }
                }
            }
        }
        if next == VAR_UNDEF {
            return None;
        }
        let sign = self.polarity[next as usize];
        Some(Lit::new(next, sign))
    }

    // ── Reduce learned clause DB ───────────────
    fn reduce_db(&mut self) {
        // Collect locked clause indices
        let mut locked_set: std::collections::HashSet<ClauseIdx> = std::collections::HashSet::new();
        for &r in &self.reason {
            if r != CLAUSE_UNDEF {
                locked_set.insert(r);
            }
        }

        // Sort learnts: worst first (high LBD, low activity)
        {
            let clauses = &self.db.clauses;
            self.learnts.sort_by(|&a, &b| {
                let ca = &clauses[a as usize];
                let cb = &clauses[b as usize];
                // Higher LBD is worse; among equal LBD, lower activity is worse
                match cb.header.lbd.cmp(&ca.header.lbd) {
                    std::cmp::Ordering::Equal => ca
                        .activity
                        .partial_cmp(&cb.activity)
                        .unwrap_or(std::cmp::Ordering::Equal),
                    other => other,
                }
            });
        }

        if !self.learnts.is_empty() {
            let idx = self.learnts.len() / RATIO_REMOVE_CLAUSES;
            if self.db.clauses[self.learnts[idx] as usize].header.lbd <= 3 {
                self.next_reduce_db += self.special_inc_reduce_db;
            }
            if self.db.clauses[*self.learnts.last().unwrap() as usize].header.lbd <= 5 {
                self.next_reduce_db += self.special_inc_reduce_db;
            }
        }

        let mut limit = self.learnts.len() / 2;
        let mut removed = 0usize;
        let mut new_learnts: Vec<ClauseIdx> = Vec::with_capacity(self.learnts.len());

        let old_learnts = std::mem::take(&mut self.learnts);
        for cref in old_learnts {
            let lbd = self.db.clauses[cref as usize].header.lbd;
            let len = self.db.clauses[cref as usize].lits.len();
            let del = self.db.clauses[cref as usize].header.deleted;
            let can_be_del = self.db.clauses[cref as usize].header.can_be_del;

            if del
                || (lbd > 2
                    && len > 2
                    && can_be_del
                    && !locked_set.contains(&cref)
                    && removed < limit)
            {
                if !del {
                    removed += 1;
                    // Detach from the correct watch lists (binary / long).
                    self.detach_clause(cref);
                    self.db.clauses[cref as usize].header.deleted = true;
                }
            } else {
                if !can_be_del {
                    limit += 1;
                }
                self.db.clauses[cref as usize].header.can_be_del = true;
                new_learnts.push(cref);
            }
        }
        self.learnts = new_learnts;
    }

    // ── Public: add clause ─────────────────────
    pub fn add_clause(&mut self, lits: &[Lit]) -> bool {
        if !self.ok {
            return false;
        }
        debug_assert!(self.decision_level() == 0);

        // Deduplicate and check tautology
        let mut v: Vec<Lit> = lits.to_vec();
        v.sort();
        v.dedup();

        // Check tautology
        for i in 1..v.len() {
            if v[i - 1].var() == v[i].var() {
                return true;
            }
        }

        // Remove false lits at level 0, check for satisfied
        let mut simplified: Vec<Lit> = Vec::new();
        for &lit in &v {
            match self.value_lit(lit) {
                LBool::True => return true,
                LBool::False => {}
                LBool::Undef => simplified.push(lit),
            }
        }

        match simplified.len() {
            0 => {
                self.ok = false;
                false
            }
            1 => {
                self.unchecked_enqueue(simplified[0], CLAUSE_UNDEF);
                if self.propagate().is_some() {
                    self.ok = false;
                    false
                } else {
                    true
                }
            }
            _ => {
                let cref = self.db.alloc(simplified, false);
                self.clauses.push(cref);
                self.attach_clause(cref);
                true
            }
        }
    }

    // ── Main CDCL loop ─────────────────────────
    pub fn solve(&mut self) -> LBool {
        if !self.ok {
            return LBool::False;
        }

        loop {
            let confl = self.propagate();

            if let Some(conflict_reason) = confl {
                // ── Conflict ──
                if self.decision_level() == 0 {
                    self.ok = false;
                    return LBool::False;
                }

                self.conflicts += 1;
                self.conflicts_restarts += 1;
                if self.conflicts % 5000 == 0 && self.var_decay < self.max_var_decay {
                    self.var_decay = (self.var_decay + 0.01).min(self.max_var_decay);
                }

                let (learnt_lits, btlevel) = self.analyze(conflict_reason);
                let lbd = self.compute_lbd(&learnt_lits);

                self.backtrack(btlevel as usize);

                if learnt_lits.len() == 1 {
                    self.unchecked_enqueue(learnt_lits[0], CLAUSE_UNDEF);
                } else {
                    let cref = self.db.alloc(learnt_lits.clone(), true);
                    self.db.clauses[cref as usize].header.lbd = lbd;
                    self.learnts.push(cref);
                    self.attach_clause(cref);
                    self.unchecked_enqueue(learnt_lits[0], cref);
                    self.cla_bump_activity(cref);
                }

                self.var_decay_activity();
                self.clause_decay_activity();

                // Update restart queues
                self.sum_lbd += lbd as f64;
                self.lbd_queue.push(lbd);
                self.trail_queue.push(self.trail.len() as u32);

                // Clause DB reduction
                if self.conflicts >= self.next_reduce_db {
                    self.next_reduce_db = self.conflicts + self.inc_reduce_db;
                    self.reduce_db();
                }
            } else {
                // ── No conflict ──

                // Check Glucose restart condition
                let should_restart = self.lbd_queue.is_valid()
                    && self.conflicts > 0
                    && (self.lbd_queue.avg() * self.k_factor
                        > self.sum_lbd / self.conflicts as f64);

                if should_restart {
                    let should_block = self.trail_queue.is_valid()
                        && self.trail_queue.avg() * self.r_factor > self.trail.len() as f64;
                    if !should_block {
                        self.restarts += 1;
                        self.backtrack(0);
                        self.lbd_queue.clear();
                        self.conflicts_restarts = 0;
                        continue;
                    }
                }

                // Pick decision
                match self.pick_branch_lit() {
                    None => {
                        // All variables assigned – SAT.
                        // Save the model and backtrack to level 0 so that
                        // callers can add new clauses (e.g. blocking clauses
                        // for solution enumeration) without violating the
                        // "add_clause requires decision level 0" invariant.
                        self.model = self.assigns.clone();
                        self.backtrack(0);
                        return LBool::True;
                    }
                    Some(lit) => {
                        self.decisions += 1;
                        self.trail_lim.push(self.trail.len());
                        self.unchecked_enqueue(lit, CLAUSE_UNDEF);
                    }
                }
            }
        }
    }
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}
