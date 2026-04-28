use crate::constraint::{Constraint, ConstraintIdx};
use crate::solver::Solver;
use crate::types::{LBool, Lit};

/// DirectEncodingExtensionSupports constraint.
///
/// Variables are encoded as groups of literals: `vars[i][j]` is TRUE iff variable `i`
/// has value `j`.  `supports` is the list of allowed tuples; `supports[k][i] == j` means
/// variable `i` has value `j` in the `k`-th support, and `-1` means "any value".
///
/// Ports the C++ `DirectEncodingExtensionSupports` class.
pub struct DirectEncodingExtensionSupports {
    /// `vars[i][j]` = literal for "variable i has value j".
    vars: Vec<Vec<Lit>>,
    /// Allowed tuples; `supports[k][i]` is the value for variable `i` (-1 = wildcard).
    supports: Vec<Vec<i32>>,
    /// Sorted list of (literal, var_index, value_index).
    lits: Vec<(Lit, usize, usize)>,
    /// For variable `i`: the currently assigned value index (-1 = unassigned).
    known_values: Vec<i32>,
    /// Undo stack: variable index (-1 = sentinel).
    undo_list: Vec<i32>,
    /// Active literals (one per propagate call).
    active_lits: Vec<Lit>,
}

impl DirectEncodingExtensionSupports {
    pub fn new(vars: Vec<Vec<Lit>>, supports: Vec<Vec<i32>>) -> Self {
        let known_values = vec![-1; vars.len()];
        let mut lits: Vec<(Lit, usize, usize)> = Vec::new();
        for (i, row) in vars.iter().enumerate() {
            for (j, &l) in row.iter().enumerate() {
                lits.push((l, i, j));
            }
        }
        lits.sort();
        DirectEncodingExtensionSupports {
            vars,
            supports,
            lits,
            known_values,
            undo_list: Vec::new(),
            active_lits: Vec::new(),
        }
    }

    fn lits_range_for(&self, target: Lit) -> std::ops::Range<usize> {
        let start = self.lits.partition_point(|&(l, _, _)| l < target);
        let end = self.lits.partition_point(|&(l, _, _)| l <= target);
        start..end
    }
}

impl Constraint for DirectEncodingExtensionSupports {
    fn initialize(&mut self, solver: &mut Solver, ci: ConstraintIdx) -> bool {
        // Watch every literal (when one becomes true, variable is assigned to that value)
        let mut watchers: Vec<Lit> = self.lits.iter().map(|&(l, _, _)| l).collect();
        watchers.sort();
        watchers.dedup();

        for &w in &watchers {
            solver.add_watch(w, ci);
        }

        let watchers_copy = watchers.clone();
        for w in watchers_copy {
            if solver.value_of(w) == LBool::True {
                if !self.propagate(solver, w, ci) {
                    return false;
                }
            }
        }

        // Empty supports with non-empty vars means unsatisfiable
        if self.supports.is_empty() && !self.vars.is_empty() {
            return false;
        }
        true
    }

    fn propagate(&mut self, solver: &mut Solver, p: Lit, ci: ConstraintIdx) -> bool {
        solver.register_undo(p.var(), ci);

        self.active_lits.push(p);
        self.undo_list.push(-1); // sentinel

        // Record which variable was assigned
        let range = self.lits_range_for(p);
        for k in range {
            let (_, i, j) = self.lits[k];
            if self.known_values[i] != -1 {
                // Already assigned: conflict if different value
                if self.known_values[i] == j as i32 {
                    continue;
                } else {
                    return false;
                }
            }
            self.undo_list.push(i as i32);
            self.known_values[i] = j as i32;
        }

        // Count matching supports and track which values are still possible
        let n_vars = self.vars.len();
        // occurrence[i][j+1] == true means value j for variable i appears in some valid support
        // occurrence[i][0] == true means wildcard (-1) for variable i appears in some valid support
        let mut occurrence: Vec<Vec<bool>> = self
            .vars
            .iter()
            .map(|row| vec![false; row.len() + 1])
            .collect();
        let mut n_match = 0;

        'supports: for support in &self.supports {
            for (var_idx, &support_val) in support.iter().enumerate() {
                let known = self.known_values[var_idx];
                if support_val != -1 && known != -1 && support_val != known {
                    continue 'supports;
                }
            }
            // This support is compatible
            n_match += 1;
            for (var_idx, &support_val) in support.iter().enumerate() {
                let col = (support_val + 1) as usize;
                occurrence[var_idx][col] = true;
            }
        }

        if n_match == 0 {
            return false;
        }

        // For each variable with no wildcard support, eliminate impossible values
        for i in 0..n_vars {
            if occurrence[i][0] {
                continue; // wildcard present – no inference possible
            }
            for j in 0..self.vars[i].len() {
                if !occurrence[i][j + 1] {
                    // Value j is not supported – force it to FALSE
                    if !solver.constraint_enqueue(!self.vars[i][j], ci) {
                        return false;
                    }
                }
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
        // All previously propagated literals are the reason
        for &l in &self.active_lits {
            out_reason.push(l);
        }
        if let Some(extra_lit) = extra {
            out_reason.push(extra_lit);
        }
    }

    fn undo(&mut self, _solver: &mut Solver, _p: Lit) {
        loop {
            let i = self.undo_list.pop().unwrap();
            if i < 0 {
                break; // sentinel
            }
            self.known_values[i as usize] = -1;
        }
        self.active_lits.pop();
    }
}
