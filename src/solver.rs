use std::collections::VecDeque;

use crate::clause::{ClauseDb, ClauseIdx, CLAUSE_UNDEF};
use crate::types::{LBool, Lit, Var, VAR_UNDEF};
use crate::watch::{WatchList, Watcher};

// ──────────────────────────────────────────────
// BoundedQueue: sliding-window average
// ──────────────────────────────────────────────
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

    fn avg(&self) -> f64 {
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
const HEAP_NONE: usize = usize::MAX;

struct OrderHeap {
    heap: Vec<Var>,
    pos: Vec<usize>,
}

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
    first_reduce_db: u64,
    inc_reduce_db: u64,

    // Statistics
    conflicts: u64,
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
}

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
            conflicts: 0,
            decisions: 0,
            propagations: 0,
            restarts: 0,
            model: Vec::new(),
            ok: true,
            seen: Vec::new(),
            perm_diff: Vec::new(),
            perm_diff_timer: 0,
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

    fn unchecked_enqueue(&mut self, lit: Lit, reason: ClauseIdx) {
        let v = lit.var() as usize;
        debug_assert!(self.assigns[v] == LBool::Undef);
        self.assigns[v] = if lit.is_neg() { LBool::False } else { LBool::True };
        self.level[v] = self.decision_level() as u32;
        self.reason[v] = reason;
        self.trail.push(lit);
    }

    fn attach_clause(&mut self, cref: ClauseIdx) {
        let len = self.db.clauses[cref as usize].lits.len();
        debug_assert!(len >= 2);
        let lit0 = self.db.clauses[cref as usize].lits[0];
        let lit1 = self.db.clauses[cref as usize].lits[1];
        // Convention: watcher stored at `lit` is triggered when `lit` becomes FALSE.
        // In propagate we read watches[false_lit] where false_lit = !p.
        if len == 2 {
            self.watches_bin
                .add(lit0, Watcher { cref, blocker: lit1 });
            self.watches_bin
                .add(lit1, Watcher { cref, blocker: lit0 });
        } else {
            self.watches.add(lit0, Watcher { cref, blocker: lit1 });
            self.watches.add(lit1, Watcher { cref, blocker: lit0 });
        }
    }

    fn detach_clause(&mut self, cref: ClauseIdx) {
        let len = self.db.clauses[cref as usize].lits.len();
        let lit0 = self.db.clauses[cref as usize].lits[0];
        let lit1 = self.db.clauses[cref as usize].lits[1];
        if len == 2 {
            self.watches_bin
                .get_mut(lit0)
                .retain(|w| w.cref != cref);
            self.watches_bin
                .get_mut(lit1)
                .retain(|w| w.cref != cref);
        } else {
            self.watches.get_mut(lit0).retain(|w| w.cref != cref);
            self.watches.get_mut(lit1).retain(|w| w.cref != cref);
        }
    }

    fn is_locked(&self, cref: ClauseIdx) -> bool {
        let lit0 = self.db.clauses[cref as usize].lits[0];
        let v = lit0.var() as usize;
        self.value_lit(lit0) == LBool::True
            && self.reason[v] == cref
    }

    // ── BCP ────────────────────────────────────
    fn propagate(&mut self) -> Option<ClauseIdx> {
        let mut conflict: Option<ClauseIdx> = None;

        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            self.propagations += 1;
            let false_lit = !p;

            // Binary watches – clone to avoid borrow issues
            let bin_ws: Vec<Watcher> = self.watches_bin.get(false_lit).to_vec();
            for w in bin_ws {
                match self.value_lit(w.blocker) {
                    LBool::True => {}
                    LBool::False => {
                        return Some(w.cref);
                    }
                    LBool::Undef => {
                        self.unchecked_enqueue(w.blocker, w.cref);
                    }
                }
            }

            // Long clause watches – take the list to avoid aliasing
            let mut ws = std::mem::take(self.watches.get_mut(false_lit));
            let mut i = 0usize;
            let mut j = 0usize;

            'outer: while i < ws.len() {
                let blocker = ws[i].blocker;
                let cref = ws[i].cref;

                // Skip deleted clauses
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

                // Ensure false_lit is at position 1
                if self.db.clauses[cref as usize].lits[0] == false_lit {
                    self.db.clauses[cref as usize].lits.swap(0, 1);
                }

                let first = self.db.clauses[cref as usize].lits[0];

                // If clause[0] is true, update blocker and keep
                if self.value_lit(first) == LBool::True {
                    ws[j] = Watcher {
                        cref,
                        blocker: first,
                    };
                    j += 1;
                    i += 1;
                    continue;
                }

                // Search for new watch in clause[2..]
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
                    let new_blocker = first;
                    self.watches
                        .add(new_lit, Watcher { cref, blocker: new_blocker });
                    // Don't keep old watcher
                    i += 1;
                    continue 'outer;
                }

                // No new watch – unit or conflict
                ws[j] = ws[i];
                j += 1;
                i += 1;

                if self.value_lit(first) == LBool::False {
                    // Conflict
                    conflict = Some(cref);
                    self.qhead = self.trail.len();
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

            if conflict.is_some() {
                break;
            }
        }

        conflict
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

    // Recursively check if `p` is redundant given the current learned clause
    fn lit_redundant(
        &mut self,
        p: Lit,
        abs_levels: u32,
        to_clear: &mut Vec<Var>,
    ) -> bool {
        let mut stack: Vec<Lit> = vec![p];
        let top = to_clear.len();

        while let Some(lit) = stack.pop() {
            let v = lit.var() as usize;
            let r = self.reason[v];
            if r == CLAUSE_UNDEF {
                // Decision variable – cannot remove
                for i in top..to_clear.len() {
                    self.seen[to_clear[i] as usize] = 0;
                }
                to_clear.truncate(top);
                return false;
            }
            let cl_len = self.db.clauses[r as usize].lits.len();
            for j in 1..cl_len {
                let q = self.db.clauses[r as usize].lits[j];
                let qv = q.var() as usize;
                let lvl = self.level[qv];
                if self.seen[qv] == 0 && lvl > 0 {
                    let qr = self.reason[qv];
                    if qr != CLAUSE_UNDEF
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
    fn analyze(&mut self, mut conflict: ClauseIdx) -> (Vec<Lit>, u32) {
        let current_level = self.decision_level() as u32;
        let mut learnt: Vec<Lit> = vec![Lit::UNDEF];
        let mut btlevel: u32 = 0;
        let mut path_c: i32 = 0;
        let mut p = Lit::UNDEF;
        let mut index = self.trail.len() as i32 - 1;
        let mut to_clear: Vec<Var> = Vec::new();

        loop {
            let start_j: usize = if p == Lit::UNDEF { 0 } else { 1 };

            // For binary clauses used as reason: ensure p is at lits[0]
            if p != Lit::UNDEF {
                let cl_len = self.db.clauses[conflict as usize].lits.len();
                if cl_len == 2 && self.db.clauses[conflict as usize].lits[0] != p {
                    self.db.clauses[conflict as usize].lits.swap(0, 1);
                }
            }

            if self.db.clauses[conflict as usize].header.learnt {
                self.cla_bump_activity(conflict);
            }

            let cl_len = self.db.clauses[conflict as usize].lits.len();
            for j in start_j..cl_len {
                let q = self.db.clauses[conflict as usize].lits[j];
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

            // Find next seen literal on trail (walking backwards)
            while index >= 0
                && self.seen[self.trail[index as usize].var() as usize] == 0
            {
                index -= 1;
            }
            if index < 0 {
                break;
            }
            p = self.trail[index as usize];
            self.seen[p.var() as usize] = 0;
            path_c -= 1;
            index -= 1;

            if path_c <= 0 {
                break;
            }

            conflict = self.reason[p.var() as usize];
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
            if self.reason[v] == CLAUSE_UNDEF
                || !self.lit_redundant(lit, abs_levels, &mut to_clear)
            {
                learnt[j] = lit;
                j += 1;
            }
        }
        learnt.truncate(j);

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
            if !self.order_heap.contains(v) {
                self.order_heap.insert(v, &self.activity);
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
                    if self.assigns[v as usize] == LBool::Undef
                        && self.decision[v as usize]
                    {
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
        let mut locked_set: std::collections::HashSet<ClauseIdx> =
            std::collections::HashSet::new();
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

        let limit = self.learnts.len() / 2;
        let mut removed = 0usize;
        let mut new_learnts: Vec<ClauseIdx> = Vec::with_capacity(self.learnts.len());

        let old_learnts = std::mem::take(&mut self.learnts);
        for cref in old_learnts {
            let lbd = self.db.clauses[cref as usize].header.lbd;
            let len = self.db.clauses[cref as usize].lits.len();
            let del = self.db.clauses[cref as usize].header.deleted;

            if del
                || (lbd > 2
                    && len > 2
                    && !locked_set.contains(&cref)
                    && removed < limit)
            {
                if !del {
                    removed += 1;
                    // Detach
                    let lit0 = self.db.clauses[cref as usize].lits[0];
                    let lit1 = self.db.clauses[cref as usize].lits[1];
                    self.watches.get_mut(lit0).retain(|w| w.cref != cref);
                    self.watches.get_mut(lit1).retain(|w| w.cref != cref);
                    self.db.clauses[cref as usize].header.deleted = true;
                }
            } else {
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

            if let Some(conflict_cref) = confl {
                // ── Conflict ──
                if self.decision_level() == 0 {
                    self.ok = false;
                    return LBool::False;
                }

                self.conflicts += 1;

                let (learnt_lits, btlevel) = self.analyze(conflict_cref);
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
                        && self.trail_queue.avg() * self.r_factor
                            > self.trail.len() as f64;
                    if !should_block {
                        self.restarts += 1;
                        self.backtrack(0);
                        self.lbd_queue.clear();
                        continue;
                    }
                }

                // Pick decision
                match self.pick_branch_lit() {
                    None => {
                        // All variables assigned – SAT
                        self.model = self.assigns.clone();
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
