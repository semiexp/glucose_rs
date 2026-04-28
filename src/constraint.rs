use crate::solver::Solver;
use crate::types::Lit;

/// Index into `Solver::constraints`.
pub type ConstraintIdx = usize;

/// Trait for non-clause constraints that can participate in CDCL propagation,
/// conflict analysis, and backtracking.
///
/// Mirrors the C++ `Constraint` abstract base class in `core/Constraint.h`.
pub trait Constraint {
    /// Called once after the constraint is registered with the solver (at decision level 0).
    /// The implementation should call `solver.add_watch(lit, ci)` for every literal it
    /// wants to be notified about, and may call `solver.constraint_enqueue(lit, ci)` to
    /// propagate initial consequences.  Returns `false` if the constraint is immediately
    /// unsatisfiable.
    fn initialize(&mut self, solver: &mut Solver, ci: ConstraintIdx) -> bool;

    /// Called when a watched literal `p` becomes TRUE.
    /// The constraint may call `solver.constraint_enqueue` to force more literals.
    /// Returns `false` on conflict.
    fn propagate(&mut self, solver: &mut Solver, p: Lit, ci: ConstraintIdx) -> bool;

    /// Fill `out_reason` with the TRUE literals that caused `p` to be forced (or caused the
    /// conflict when `p` is `None`).  `extra` is the enqueue-failure literal that triggered
    /// the conflict, if any.
    ///
    /// **Important**: `out_reason` must contain TRUE literals.  Conflict analysis will negate
    /// them when constructing the learnt clause.
    fn calc_reason(
        &mut self,
        solver: &mut Solver,
        p: Option<Lit>,
        extra: Option<Lit>,
        out_reason: &mut Vec<Lit>,
    );

    /// Called during backtracking (and during conflict analysis) when `p` is being unassigned.
    /// The constraint should undo any internal state that was set when `p` was assigned.
    fn undo(&mut self, solver: &mut Solver, p: Lit);
}
