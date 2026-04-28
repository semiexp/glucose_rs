use crate::constraint::{Constraint, ConstraintIdx};
use crate::solver::Solver;
use crate::types::{LBool, Lit};

/// A single term in an order-encoding linear constraint.
///
/// Represents the variable `x` with coefficient `coef`, domain `domain`, and order-encoding
/// literals `lits` where `lits[i] <=> (x >= domain[i+1])`.
///
/// `domain.len() == lits.len() + 1`.
pub struct LinearTerm {
    pub lits: Vec<Lit>,
    pub domain: Vec<i32>,
    pub coef: i32,
}

impl LinearTerm {
    /// Normalize so that `coef == 1` by possibly reversing lits/domain and scaling domain.
    fn normalize(&mut self) {
        if self.coef < 0 {
            self.lits.reverse();
            for l in &mut self.lits {
                *l = !*l;
            }
            self.domain.reverse();
        }
        for d in &mut self.domain {
            *d *= self.coef;
        }
        self.coef = 1;
    }
}

/// Order-encoding linear constraint: `sum(terms) + constant >= 0`.
///
/// Ports the C++ `OrderEncodingLinear` class from `constraints/OrderEncodingLinear.{h,cc}`.
pub struct OrderEncodingLinear {
    terms: Vec<LinearTerm>,
    /// Sorted list of (literal, term_index, lit_index_within_term).
    lits: Vec<(Lit, usize, usize)>,
    /// For term `i`: upper-bound index into `terms[i].domain`.  
    /// ub_index[i] == k  means  domain[k] is the current upper bound value.
    ub_index: Vec<usize>,
    /// Undo stack entries: (term_index, previous_ub_index).  (-1,-1) is a sentinel.
    undo_list: Vec<(i32, i32)>,
    /// Active literals pushed so far (one per call to `propagate`).
    active_lits: Vec<Lit>,
    #[allow(dead_code)]
    constant: i32,
    /// Running total_ub = constant + sum of terms[i].domain[ub_index[i]].
    total_ub: i32,
}

impl OrderEncodingLinear {
    /// Create the constraint.  `terms` have arbitrary non-zero coefficients;
    /// they are normalized internally to coef==1.
    pub fn new(mut terms: Vec<LinearTerm>, constant: i32) -> Self {
        for t in &mut terms {
            assert_ne!(t.coef, 0);
            if t.coef != 1 {
                t.normalize();
            }
        }

        let mut total_ub = constant;
        let mut ub_index = Vec::with_capacity(terms.len());
        let mut lits: Vec<(Lit, usize, usize)> = Vec::new();

        for (i, term) in terms.iter().enumerate() {
            ub_index.push(term.lits.len());
            total_ub += *term.domain.last().unwrap();
            for (j, &l) in term.lits.iter().enumerate() {
                lits.push((l, i, j));
            }
        }
        lits.sort();

        OrderEncodingLinear {
            terms,
            lits,
            ub_index,
            undo_list: Vec::new(),
            active_lits: Vec::new(),
            constant,
            total_ub,
        }
    }

    /// Binary search for entries in `self.lits` matching `target_lit`.
    fn lits_range_for(&self, target: Lit) -> std::ops::Range<usize> {
        let start = self.lits.partition_point(|&(l, _, _)| l < target);
        let end = self.lits.partition_point(|&(l, _, _)| l <= target);
        start..end
    }
}

impl Constraint for OrderEncodingLinear {
    fn initialize(&mut self, solver: &mut Solver, ci: ConstraintIdx) -> bool {
        // Collect unique watch literals (negations of constraint lits)
        let mut watchers: Vec<Lit> = self.lits.iter().map(|&(l, _, _)| !l).collect();
        watchers.sort();
        watchers.dedup();

        for &w in &watchers {
            solver.add_watch(w, ci);
        }

        // Propagate already-true watchers
        let watchers_copy = watchers.clone();
        for w in watchers_copy {
            if solver.value_of(w) == LBool::True {
                if !self.propagate(solver, w, ci) {
                    return false;
                }
            }
        }

        if self.total_ub < 0 {
            return false;
        }
        true
    }

    /// `p` is a TRUE literal that is a negation of one of the constraint's order-encoding lits.
    /// When `lits[i] == ~p` is FALSE, the upper bound for term `i` is reduced.
    fn propagate(&mut self, solver: &mut Solver, p: Lit, ci: ConstraintIdx) -> bool {
        solver.register_undo(p.var(), ci);

        self.active_lits.push(p);
        self.undo_list.push((-1, -1)); // sentinel

        // Find all constraint lits l such that ~l == p  (i.e. l == ~p)
        let neg_p = !p;
        let range = self.lits_range_for(neg_p);
        for k in range {
            let (_, i, j) = self.lits[k];
            if self.ub_index[i] <= j {
                continue;
            }
            // Save old ub_index[i] for undo
            self.undo_list.push((i as i32, self.ub_index[i] as i32));
            let old_ub = self.terms[i].domain[self.ub_index[i]];
            let new_ub = self.terms[i].domain[j];
            self.total_ub -= old_ub - new_ub;
            self.ub_index[i] = j;

            if self.total_ub < 0 {
                return false;
            }
        }

        // Propagate consequences
        for i in 0..self.terms.len() {
            let ubi = self.ub_index[i];
            if ubi == 0 {
                continue;
            }
            // If total_ub - (domain[ubi] - domain[0]) < 0, we need to raise the lower bound
            let slack = self.total_ub - (self.terms[i].domain[ubi] - self.terms[i].domain[0]);
            if slack >= 0 {
                continue;
            }
            // Find largest j s.t. domain[j] < domain[ubi] - total_ub
            let threshold = self.terms[i].domain[ubi] - self.total_ub;
            let left = self.terms[i].domain.partition_point(|&d| d < threshold) as i32 - 1;
            let left = left as usize;
            // Enqueue lits[left] (force domain >= domain[left+1])
            if !solver.constraint_enqueue(self.terms[i].lits[left], ci) {
                return false;
            }
        }

        true
    }

    fn calc_reason(
        &mut self,
        _solver: &mut Solver,
        _p: Option<Lit>,
        extra: Option<Lit>,
        out_reason: &mut Vec<Lit>,
    ) {
        // For each term, if the upper-bound index is less than lits.len(),
        // the corresponding negated lit is a reason (it's FALSE = its negation is TRUE).
        for i in 0..self.terms.len() {
            if self.ub_index[i] < self.terms[i].lits.len() {
                out_reason.push(!self.terms[i].lits[self.ub_index[i]]);
            }
        }
        if let Some(extra_lit) = extra {
            out_reason.push(extra_lit);
        }
    }

    fn undo(&mut self, _solver: &mut Solver, _p: Lit) {
        loop {
            let (i, j) = self.undo_list.pop().unwrap();
            if i < 0 {
                break; // sentinel
            }
            let i = i as usize;
            let j = j as usize;
            self.total_ub += self.terms[i].domain[j] - self.terms[i].domain[self.ub_index[i]];
            self.ub_index[i] = j;
        }
        self.active_lits.pop();
    }
}
