use crate::constraint::{Constraint, ConstraintIdx};
use crate::solver::Solver;
use crate::types::{LBool, Lit};

/// AtMost(lits, threshold): at most `threshold` of the literals in `lits` can be TRUE.
///
/// Ports the C++ `AtMost` class from `constraints/AtMost.{h,cc}`.
pub struct AtMost {
    lits: Vec<Lit>,
    threshold: i32,
    n_true: i32,
}

impl AtMost {
    pub fn new(mut lits: Vec<Lit>, threshold: i32) -> Self {
        lits.sort();
        lits.dedup();
        AtMost {
            lits,
            threshold,
            n_true: 0,
        }
    }
}

impl Constraint for AtMost {
    fn initialize(&mut self, solver: &mut Solver, ci: ConstraintIdx) -> bool {
        for &lit in &self.lits {
            solver.add_watch(lit, ci);
        }
        let lits = self.lits.clone();
        for &lit in &lits {
            if solver.value_of(lit) == LBool::True {
                if !self.propagate(solver, lit, ci) {
                    return false;
                }
            }
        }
        if self.n_true > self.threshold {
            return false;
        }
        if self.n_true == self.threshold {
            for &lit in &self.lits {
                if solver.value_of(lit) == LBool::Undef && !solver.constraint_enqueue(!lit, ci) {
                    return false;
                }
            }
        }
        true
    }

    fn propagate(&mut self, solver: &mut Solver, p: Lit, ci: ConstraintIdx) -> bool {
        self.n_true += 1;
        solver.register_undo(p.var(), ci);

        if self.n_true > self.threshold {
            return false;
        }
        if self.n_true == self.threshold {
            for &lit in &self.lits {
                if solver.value_of(lit) == LBool::Undef && !solver.constraint_enqueue(!lit, ci) {
                    return false;
                }
            }
        }
        true
    }

    fn calc_reason(
        &mut self,
        solver: &mut Solver,
        p: Option<Lit>,
        extra: Option<Lit>,
        out_reason: &mut Vec<Lit>,
    ) {
        if let Some(extra_lit) = extra {
            out_reason.push(extra_lit);
        }
        for &lit in &self.lits {
            if solver.value_of(lit) == LBool::True && Some(lit) != p {
                out_reason.push(lit);
            }
        }
    }

    fn undo(&mut self, _solver: &mut Solver, _p: Lit) {
        self.n_true -= 1;
    }
}
