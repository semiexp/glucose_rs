use std::collections::BTreeSet;

use crate::constraint::{Constraint, ConstraintIdx};
use crate::solver::Solver;
use crate::types::{LBool, Lit, Var};

/// Xor(lits, parity): XOR of the variables (positive = 1, negative = 0) equals `parity`.
///
/// Ports the C++ `Xor` class from `constraints/Xor.{h,cc}`.
pub struct Xor {
    /// Sorted, deduplicated variable list (after absorbing signs into `parity`).
    vars: Vec<Var>,
    /// Current assigned value per variable: -1 = undef, 0 = false, 1 = true.
    value: Vec<i32>,
    /// Running XOR of assigned values XOR'd with the target parity.
    /// Starts as `target_parity`.  When all variables are assigned, `parity == 0` iff satisfied.
    parity: i32,
    n_undecided: i32,
}

impl Xor {
    /// Create an XOR constraint.  `lits` may contain negative literals and duplicates;
    /// negative literals flip `parity`, duplicates cancel out.
    pub fn new(lits: &[Lit], mut parity: i32) -> Self {
        let mut vars_set: BTreeSet<Var> = BTreeSet::new();
        for &l in lits {
            if l.is_neg() {
                parity ^= 1;
            }
            let v = l.var();
            if vars_set.contains(&v) {
                vars_set.remove(&v);
            } else {
                vars_set.insert(v);
            }
        }
        let vars: Vec<Var> = vars_set.into_iter().collect();
        let n = vars.len() as i32;
        let value = vec![-1; vars.len()];
        Xor {
            vars,
            value,
            parity,
            n_undecided: n,
        }
    }

    fn var_index(&self, v: Var) -> usize {
        self.vars.partition_point(|&x| x < v)
    }
}

impl Constraint for Xor {
    fn initialize(&mut self, solver: &mut Solver, ci: ConstraintIdx) -> bool {
        for &v in &self.vars {
            solver.add_watch(Lit::new(v, false), ci); // positive lit
            solver.add_watch(Lit::new(v, true), ci); // negative lit
        }
        let vars = self.vars.clone();
        for &v in &vars {
            match solver.value_of_var(v) {
                LBool::True => {
                    if !self.propagate(solver, Lit::new(v, false), ci) {
                        return false;
                    }
                }
                LBool::False => {
                    if !self.propagate(solver, Lit::new(v, true), ci) {
                        return false;
                    }
                }
                LBool::Undef => {}
            }
        }
        if self.vars.is_empty() && self.parity != 0 {
            return false;
        }
        true
    }

    fn propagate(&mut self, solver: &mut Solver, p: Lit, ci: ConstraintIdx) -> bool {
        // s = 0 if negative lit (var=false), 1 if positive lit (var=true)
        let s = if p.is_neg() { 0 } else { 1 };
        let v = p.var();
        solver.register_undo(v, ci);

        let idx = self.var_index(v);
        debug_assert_eq!(self.value[idx], -1);
        self.value[idx] = s;
        self.parity ^= s;
        self.n_undecided -= 1;

        debug_assert!(self.n_undecided >= 0);

        if self.n_undecided == 0 {
            if self.parity != 0 {
                return false;
            }
        } else if self.n_undecided == 1 {
            // Force the last undecided variable
            for i in 0..self.vars.len() {
                if self.value[i] == -1 {
                    // Need last_val = parity (so parity ^ last_val = 0)
                    // sign=true means negative lit (var=false), sign=false means positive (var=true)
                    let forced = Lit::new(self.vars[i], self.parity == 0);
                    if !solver.constraint_enqueue(forced, ci) {
                        return false;
                    }
                    break;
                }
            }
        }

        true
    }

    fn calc_reason(
        &mut self,
        _solver: &mut Solver,
        p: Option<Lit>,
        extra: Option<Lit>,
        out_reason: &mut Vec<Lit>,
    ) {
        for i in 0..self.vars.len() {
            if self.value[i] != -1 {
                // Push the TRUE literal for this variable
                // value[i]==0 means var is FALSE → TRUE lit is negative → Lit(var, neg=true)
                // value[i]==1 means var is TRUE  → TRUE lit is positive → Lit(var, neg=false)
                out_reason.push(Lit::new(self.vars[i], self.value[i] == 0));
            } else if p.is_none() {
                // Conflict case with an undef var: only relevant when extra is set
                if let Some(_extra_lit) = extra {
                    out_reason.push(Lit::new(self.vars[i], self.parity == 1));
                }
            }
        }
    }

    fn undo(&mut self, _solver: &mut Solver, p: Lit) {
        let v = p.var();
        let idx = self.var_index(v);
        let s = if p.is_neg() { 0 } else { 1 };
        debug_assert_eq!(self.value[idx], s);
        self.parity ^= self.value[idx];
        self.value[idx] = -1;
        self.n_undecided += 1;
    }
}
