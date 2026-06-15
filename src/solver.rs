//! Port of `core/Solver.h` / `core/Solver.cc` (Glucose 4.1 based), excluding the
//! parallel-solving related features.
//!
//! The corresponding C++ method names are kept (in snake_case).  Methods that are inline in
//! `Solver.h` are implemented in the "inline methods" section near the end of the `impl` block,
//! mirroring the structure of the original headers.

use std::io::Write;

use crate::bounded_queue::BoundedQueue;
use crate::constants::{LOWER_BOUND_FOR_BLOCKING_RESTART, RATIO_REMOVE_CLAUSES};
use crate::constraint::{Constraint, ConstraintIdx};
use crate::heap::Heap;
use crate::types::{CRef, ClauseAllocator, LBool, Lit, OccLists, Var, CREF_UNDEF};

//=================================================================================================
// Statistics
//=================================================================================================

// Core stats
#[derive(Clone, Copy)]
#[allow(dead_code)]
pub enum CoreStats {
    SumResSeen,
    SumRes,
    SumTrail,
    NbPromoted,
    OriginalClausesSeen,
    SumDecisionLevels,
    NbPermanentLearnts,
    NbRemovedClauses,
    NbRemovedUnaryWatchedClauses,
    NbReducedClauses,
    NbDL2,
    NbBin,
    NbUn,
    NbReduceDB,
    RndDecisions,
    NbStopsRestarts,
    NbStopsRestartsSame,
    LastBlockAtRestart,
    DecVars,
    ClausesLiterals,
    LearntsLiterals,
    MaxLiterals,
    TotLiterals,
    NoDecisionConflict,
}

pub const CORE_STATS_SIZE: usize = 24;

//=================================================================================================
// Options:
//
// The C++ implementation reads these from the command-line option framework (`utils/Options.h`);
// the Rust port uses the default values as constants.

const OPT_K: f64 = 0.8;
const OPT_R: f64 = 1.4;
const OPT_SIZE_LBD_QUEUE: i32 = 50;
const OPT_SIZE_TRAIL_QUEUE: i32 = 5000;

const OPT_FIRST_REDUCE_DB: i32 = 2000;
const OPT_INC_REDUCE_DB: i32 = 300;
const OPT_SPEC_INC_REDUCE_DB: i32 = 1000;
const OPT_LB_LBD_FROZEN_CLAUSE: u32 = 30;
const OPT_CHANSEOK_HACK: bool = false;
const OPT_CHANSEOK_LIMIT: i32 = 5;

const OPT_LB_SIZE_MINIMZING_CLAUSE: usize = 30;
const OPT_LB_LBD_MINIMZING_CLAUSE: u32 = 6;

const OPT_VAR_DECAY: f64 = 0.8;
const OPT_MAX_VAR_DECAY: f64 = 0.95;
const OPT_CLAUSE_DECAY: f64 = 0.999;
const OPT_RANDOM_VAR_FREQ: f64 = 0.0;
const OPT_RANDOM_SEED: f64 = 91648253.0;
const OPT_CCMIN_MODE: i32 = 2;
const OPT_PHASE_SAVING: i32 = 2;
const OPT_RND_INIT_ACT: bool = false;
const OPT_GARBAGE_FRAC: f64 = 0.20;
const OPT_GLU_REDUCTION: bool = true;
const OPT_LUBY_RESTART: bool = false;
const OPT_RESTART_INC: f64 = 2.0;
const OPT_LUBY_RESTART_FACTOR: i32 = 100;

const OPT_RANDOMIZE_PHASE_ON_RESTARTS: i32 = 0;
const OPT_FIXED_RANDOMIZE_PHASE_ON_RESTARTS: bool = false;

const OPT_ADAPT: bool = true;

const OPT_FORCEUNSAT: bool = true;

//=================================================================================================
// Solver -- the main class:

// Helper structures:
//
#[derive(Clone, Copy)]
struct VarData {
    reason: CRef,
    nc_reason: Option<ConstraintIdx>,
    level: i32,
}

fn mk_var_data(cr: CRef, l: i32) -> VarData {
    VarData {
        reason: cr,
        nc_reason: None,
        level: l,
    }
}

fn mk_var_data_constr(cs: ConstraintIdx, l: i32) -> VarData {
    VarData {
        reason: CREF_UNDEF,
        nc_reason: Some(cs),
        level: l,
    }
}

#[derive(Clone, Copy)]
struct Watcher {
    cref: CRef,
    blocker: Lit,
}

// (`WatcherDeleted` and `VarOrderLt` are expressed as closures at the call sites in this port.)

pub struct Solver {
    // Extra results: (read-only member variable)
    //
    /// If problem is satisfiable, this vector contains the model (if any).
    pub model: Vec<LBool>,
    /// If problem is unsatisfiable (possibly under assumptions),
    /// this vector represent the final conflict clause expressed in the assumptions.
    pub conflict: Vec<Lit>,

    // Mode of operation:
    //
    pub verbosity: i32,
    pub verb_every_conflicts: i32,
    pub show_model: i32,

    // Constants For restarts
    pub k: f64,
    pub r: f64,
    pub size_lbd_queue: f64,
    pub size_trail_queue: f64,

    // Constants for reduce DB
    pub first_reduce_db: i32,
    pub inc_reduce_db: i32,
    pub special_inc_reduce_db: i32,
    pub lb_lbd_frozen_clause: u32,
    pub chanseok_strategy: bool,
    /// Keep all learnts with lbd<=coLBDBound
    pub co_lbd_bound: i32,
    // Constant for reducing clause
    pub lb_size_minimizing_clause: usize,
    pub lb_lbd_minimizing_clause: u32,

    // Constant for heuristic
    pub var_decay: f64,
    pub max_var_decay: f64,
    pub clause_decay: f64,
    pub random_var_freq: f64,
    pub random_seed: f64,
    /// Controls conflict clause minimization (0=none, 1=basic, 2=deep).
    pub ccmin_mode: i32,
    /// Controls the level of phase saving (0=none, 1=limited, 2=full).
    pub phase_saving: i32,
    /// Use random polarities for branching heuristics.
    pub rnd_pol: bool,
    /// Initialize variable activities with a small random value.
    pub rnd_init_act: bool,
    /// the first decisions (until first conflict) are made randomly.
    pub randomize_first_descent: bool,

    // Constant for Memory managment
    /// The fraction of wasted memory allowed before a garbage collection is triggered.
    pub garbage_frac: f64,

    // Certified UNSAT (Thanks to Marijn Heule)
    // New in 2016 : proof in DRAT format, possibility to use binary output
    pub certified_output: Option<Box<dyn Write>>,
    pub certified_unsat: bool,
    pub vbyte: bool,

    pub dump_analysis_info: bool,

    // Panic mode.
    // Save memory
    pub panic_mode_last_removed: u32,
    pub panic_mode_last_removed_shared: u32,

    /// Enable unary watched literals
    pub use_unary_watched: bool,
    /// One watched clauses are promotted to two watched clauses if found empty
    pub promote_one_watched_clause: bool,

    // Statistics
    pub stats: Vec<u64>,

    // Important stats completely related to search. Keep here
    pub solves: u64,
    pub starts: u64,
    pub decisions: u64,
    pub propagations: u64,
    pub conflicts: u64,
    pub conflicts_restarts: u64,

    // -- protected members --
    cur_restart: i64,

    // Alpha variables
    glureduce: bool,
    restart_inc: u32,
    luby_restart: bool,
    adapt_strategies: bool,
    luby_restart_factor: i32,
    randomize_on_restarts: bool,
    fixed_randomize_on_restarts: bool,
    new_descent: bool,
    random_descent_assignments: u32,
    force_unsat_on_new_descent: bool,

    // Solver state:
    //
    /// If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    ok: bool,
    /// Amount to bump next clause with.
    cla_inc: f64,
    /// A heuristic measurement of the activity of a variable.
    activity: Vec<f64>,
    /// Amount to bump next variable with.
    var_inc: f64,
    /// 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    watches: OccLists<Watcher>,
    watches_bin: OccLists<Watcher>,
    /// Unary watch scheme (clauses are seen when they become empty)
    unary_watches: OccLists<Watcher>,
    /// List of problem clauses.
    clauses: Vec<CRef>,
    /// List of learnt clauses.
    learnts: Vec<CRef>,
    /// The list of learnts clauses kept permanently
    permanent_learnts: Vec<CRef>,
    /// List of imported clauses (after the purgatory)
    unary_watched_clauses: Vec<CRef>,

    /// 'constr_watches[lit]' is a list of non-clause constraints watching 'lit'
    constr_watches: Vec<Vec<ConstraintIdx>>,
    /// 'undo_lists[var]' is a list of non-clause constraints to which undo of 'var' must be notified
    undo_lists: Vec<Vec<ConstraintIdx>>,
    /// List of non-clause constraints.  The `Option` is used to temporarily move a constraint out
    /// while it is given a `&mut Solver` (the C++ code can call methods on the constraint and the
    /// solver simultaneously).
    constraints: Vec<Option<Box<dyn Constraint>>>,
    /// `num_pending_propagation_` of each constraint.  In C++ this counter lives in the
    /// `Constraint` base class; here the solver keeps it, indexed by `ConstraintIdx`.
    num_pending_propagation: Vec<i32>,
    /// The last Lit which was enqueued by a Constraint and failed.
    enqueue_failure: Option<Lit>,

    /// The current assignments.
    assigns: Vec<LBool>,
    /// The preferred polarity of each variable.
    polarity: Vec<bool>,
    force_unsat: Vec<i8>,

    /// Declares if a variable is eligible for selection in the decision heuristic.
    decision: Vec<bool>,
    /// Assignment stack; stores all assigments made in the order they were made.
    trail: Vec<Lit>,
    /// Separator indices for different decision levels in 'trail'.
    trail_lim: Vec<i32>,
    /// Stores reason and level for each variable.
    vardata: Vec<VarData>,
    /// Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
    qhead: i32,
    /// Number of top-level assignments since last execution of 'simplify()'.
    simp_db_assigns: i32,
    /// Remaining number of propagations that must be made before next execution of 'simplify()'.
    simp_db_props: i64,
    /// Current set of assumptions provided to solve by the user.
    assumptions: Vec<Lit>,
    /// A priority queue of variables ordered with respect to the variable activity.
    order_heap: Heap,
    /// Set by 'search()'.
    progress_estimate: f64,
    /// Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.
    remove_satisfied: bool,
    /// permDiff[var] contains the current conflict number... Used to count the number of LBD
    perm_diff: Vec<u32>,

    /// names of variables
    var_names: Vec<String>,

    // UPDATEVARACTIVITY trick (see competition'09 companion paper)
    last_decision_level: Vec<Lit>,

    ca: ClauseAllocator,

    /// To know when it is time to reduce clause database
    nbclausesbeforereduce: i32,

    // Used for restart strategies
    /// Bounded queues for restarts.
    trail_queue: BoundedQueue,
    lbd_queue: BoundedQueue,
    /// used to compute the global average of LBD. Restarts...
    sum_lbd: f32,
    last_learnt_clause: CRef,

    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in
    // which it is used, exept 'seen' wich is used in several places.
    //
    seen: Vec<bool>,
    analyze_stack: Vec<Lit>,
    analyze_toclear: Vec<Lit>,
    add_tmp: Vec<Lit>,
    myflag: u32,

    // Resource contraints:
    //
    /// -1 means no budget.
    conflict_budget: i64,
    /// -1 means no budget.
    propagation_budget: i64,
    asynch_interrupt: bool,

    // Variables added for incremental mode
    /// Use incremental SAT Solver
    incremental: bool,
    /// nb VAR in formula without assumptions (incremental SAT)
    nb_vars_initial_formula: i32,
    total_time_4_sat: f64,
    total_time_4_unsat: f64,
    nb_sat_calls: i32,
    nb_unsat_calls: i32,
}

/// Counterpart of `Solver::hasConflict`.
fn has_conflict(p: &(CRef, Option<ConstraintIdx>)) -> bool {
    p.0 != CREF_UNDEF || p.1.is_some()
}

impl Solver {
    //=============================================================================================
    // Constructor:

    pub fn new() -> Solver {
        let mut solver = Solver {
            // Parameters (user settable):
            //
            verbosity: 0,
            // NOTE: not initialized by the C++ constructor (it is set by the frontend);
            // initialized here to the frontend's default to avoid division by zero.
            verb_every_conflicts: 10000,
            show_model: 0,
            k: OPT_K,
            r: OPT_R,
            size_lbd_queue: OPT_SIZE_LBD_QUEUE as f64,
            size_trail_queue: OPT_SIZE_TRAIL_QUEUE as f64,
            first_reduce_db: OPT_FIRST_REDUCE_DB,
            inc_reduce_db: if OPT_CHANSEOK_HACK {
                0
            } else {
                OPT_INC_REDUCE_DB
            },
            special_inc_reduce_db: if OPT_CHANSEOK_HACK {
                0
            } else {
                OPT_SPEC_INC_REDUCE_DB
            },
            lb_lbd_frozen_clause: OPT_LB_LBD_FROZEN_CLAUSE,
            chanseok_strategy: OPT_CHANSEOK_HACK,
            co_lbd_bound: OPT_CHANSEOK_LIMIT,
            lb_size_minimizing_clause: OPT_LB_SIZE_MINIMZING_CLAUSE,
            lb_lbd_minimizing_clause: OPT_LB_LBD_MINIMZING_CLAUSE,
            var_decay: OPT_VAR_DECAY,
            max_var_decay: OPT_MAX_VAR_DECAY,
            clause_decay: OPT_CLAUSE_DECAY,
            random_var_freq: OPT_RANDOM_VAR_FREQ,
            random_seed: OPT_RANDOM_SEED,
            ccmin_mode: OPT_CCMIN_MODE,
            phase_saving: OPT_PHASE_SAVING,
            rnd_pol: false,
            rnd_init_act: OPT_RND_INIT_ACT,
            randomize_first_descent: false,
            garbage_frac: OPT_GARBAGE_FRAC,
            certified_output: None,
            certified_unsat: false,
            vbyte: false,
            dump_analysis_info: false,
            panic_mode_last_removed: 0,
            panic_mode_last_removed_shared: 0,
            use_unary_watched: false,
            promote_one_watched_clause: true,
            solves: 0,
            starts: 0,
            decisions: 0,
            propagations: 0,
            conflicts: 0,
            conflicts_restarts: 0,
            cur_restart: 1,
            glureduce: OPT_GLU_REDUCTION,
            restart_inc: OPT_RESTART_INC as u32,
            luby_restart: OPT_LUBY_RESTART,
            adapt_strategies: OPT_ADAPT,
            luby_restart_factor: OPT_LUBY_RESTART_FACTOR,
            randomize_on_restarts: OPT_RANDOMIZE_PHASE_ON_RESTARTS != 0,
            fixed_randomize_on_restarts: OPT_FIXED_RANDOMIZE_PHASE_ON_RESTARTS,
            new_descent: false,
            random_descent_assignments: 0,
            force_unsat_on_new_descent: OPT_FORCEUNSAT,

            ok: true,
            cla_inc: 1.0,
            activity: Vec::new(),
            var_inc: 1.0,
            watches: OccLists::new(),
            watches_bin: OccLists::new(),
            unary_watches: OccLists::new(),
            clauses: Vec::new(),
            learnts: Vec::new(),
            permanent_learnts: Vec::new(),
            unary_watched_clauses: Vec::new(),
            constr_watches: Vec::new(),
            undo_lists: Vec::new(),
            constraints: Vec::new(),
            num_pending_propagation: Vec::new(),
            enqueue_failure: None,
            assigns: Vec::new(),
            polarity: Vec::new(),
            force_unsat: Vec::new(),
            decision: Vec::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            vardata: Vec::new(),
            qhead: 0,
            simp_db_assigns: -1,
            simp_db_props: 0,
            assumptions: Vec::new(),
            order_heap: Heap::new(),
            progress_estimate: 0.0,
            remove_satisfied: true,
            perm_diff: Vec::new(),
            var_names: Vec::new(),
            last_decision_level: Vec::new(),
            ca: ClauseAllocator::new(),
            nbclausesbeforereduce: 0,
            trail_queue: BoundedQueue::new(),
            lbd_queue: BoundedQueue::new(),
            sum_lbd: 0.0,
            last_learnt_clause: CREF_UNDEF,
            seen: Vec::new(),
            analyze_stack: Vec::new(),
            analyze_toclear: Vec::new(),
            add_tmp: Vec::new(),
            myflag: 0,
            // Resource constraints:
            //
            conflict_budget: -1,
            propagation_budget: -1,
            asynch_interrupt: false,
            incremental: false,
            nb_vars_initial_formula: i32::MAX,
            total_time_4_sat: 0.0,
            total_time_4_unsat: 0.0,
            nb_sat_calls: 0,
            nb_unsat_calls: 0,
            model: Vec::new(),
            conflict: Vec::new(),
            stats: Vec::new(),
        };
        solver.myflag = 0;
        // Initialize only first time. Useful for incremental solving (not in // version), useless otherwise
        // Kept here for simplicity
        solver.lbd_queue.init_size(solver.size_lbd_queue as usize);
        solver
            .trail_queue
            .init_size(solver.size_trail_queue as usize);
        solver.sum_lbd = 0.0;
        solver.nbclausesbeforereduce = solver.first_reduce_db;
        solver.stats.resize(CORE_STATS_SIZE, 0);
        solver
    }

    /****************************************************************
     Certified UNSAT proof in binary format
    ****************************************************************/

    fn write_char(&mut self, ch: u8) {
        if self
            .certified_output
            .as_mut()
            .unwrap()
            .write_all(&[ch])
            .is_err()
        {
            std::process::exit(1);
        }
    }

    fn write_lit(&mut self, mut n: i32) {
        while n > 127 {
            self.write_char((128 | (n & 127)) as u8);
            n >>= 7;
        }
        self.write_char(n as u8);
    }

    /****************************************************************
     Set the incremental mode
    ****************************************************************/

    // This function set the incremental mode to true.
    // You can add special code for this mode here.

    pub fn set_incremental_mode(&mut self) {
        // (this build does not enable INCREMENTAL, like the C++ build used by cspuz_core)
        eprintln!("c Trying to set incremental mode, but not compiled properly for this.");
        std::process::exit(1);
    }

    /// Number of variables without selectors
    pub fn init_nb_initial_vars(&mut self, nb: i32) {
        self.nb_vars_initial_formula = nb;
    }

    pub fn is_incremental(&self) -> bool {
        self.incremental
    }

    //=============================================================================================
    // Minor methods:

    /// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
    /// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
    ///
    /// Counterpart of `newVar(bool polarity = true, bool dvar = true)`; the default-argument
    /// version is `new_var()`.
    pub fn new_var_(&mut self, sign: bool, dvar: bool) -> Var {
        let v = self.n_vars() as Var;
        self.watches.init(Lit::new(v, false));
        self.watches.init(Lit::new(v, true));
        self.watches_bin.init(Lit::new(v, false));
        self.watches_bin.init(Lit::new(v, true));
        self.unary_watches.init(Lit::new(v, false));
        self.unary_watches.init(Lit::new(v, true));
        self.assigns.push(LBool::Undef);
        self.vardata.push(mk_var_data(CREF_UNDEF, 0));
        let act = if self.rnd_init_act {
            Self::drand(&mut self.random_seed) * 0.00001
        } else {
            0.0
        };
        self.activity.push(act);
        self.seen.push(false);
        self.perm_diff.push(0);
        // `perm_diff` is pushed one-per-variable (as in C++), but `computeLBD` indexes it by
        // decision level, which can be as deep as `nVars` in the all-decisions case.  Keep one
        // extra slot so that the level-`nVars` access is in bounds; the C++ `vec` instead relies
        // on its over-allocated capacity for this.
        self.perm_diff.resize(self.assigns.len() + 1, 0);
        self.polarity.push(sign);
        self.force_unsat.push(0);
        self.decision.push(false);
        self.constr_watches.push(Vec::new());
        self.constr_watches.push(Vec::new());
        self.undo_lists.push(Vec::new());
        self.set_decision_var(v, dvar);
        v
    }

    pub fn new_var(&mut self) -> Var {
        self.new_var_(true, true)
    }

    pub fn new_named_var(&mut self, name: &str) -> Var {
        let v = self.n_vars();
        while self.var_names.len() < v {
            self.var_names.push(String::new());
        }
        self.var_names.push(name.to_owned());
        self.new_var()
    }

    /// Add a clause to the solver without making superflous internal copy. Will change the passed
    /// vector 'ps'.
    pub fn add_clause_(&mut self, ps: &mut Vec<Lit>) -> bool {
        debug_assert!(self.decision_level() == 0);
        if !self.ok {
            return false;
        }

        // Check if clause is satisfied and remove false/duplicate literals:
        ps.sort();

        let mut oc: Vec<Lit> = Vec::new();

        let mut flag = false;
        if self.certified_unsat {
            let p = Lit::UNDEF;
            for i in 0..ps.len() {
                oc.push(ps[i]);
                if self.value_of(ps[i]) == LBool::True
                    || ps[i] == !p
                    || self.value_of(ps[i]) == LBool::False
                {
                    flag = true;
                }
            }
        }

        let mut j = 0;
        let mut p = Lit::UNDEF;
        for i in 0..ps.len() {
            if self.value_of(ps[i]) == LBool::True || ps[i] == !p {
                return true;
            } else if self.value_of(ps[i]) != LBool::False && ps[i] != p {
                p = ps[i];
                ps[j] = p;
                j += 1;
            }
        }
        ps.truncate(j);

        if flag && self.certified_unsat {
            if self.vbyte {
                self.write_char(b'a');
                for i in 0..ps.len() {
                    self.write_lit(2 * (ps[i].var() as i32 + 1) + ps[i].is_neg() as i32);
                }
                self.write_lit(0);

                self.write_char(b'd');
                for i in 0..oc.len() {
                    self.write_lit(2 * (oc[i].var() as i32 + 1) + oc[i].is_neg() as i32);
                }
                self.write_lit(0);
            } else {
                let out = self.certified_output.as_mut().unwrap();
                for i in 0..ps.len() {
                    write!(
                        out,
                        "{} ",
                        (ps[i].var() as i32 + 1) * (-2 * ps[i].is_neg() as i32 + 1)
                    )
                    .unwrap();
                }
                writeln!(out, "0").unwrap();

                write!(out, "d ").unwrap();
                for i in 0..oc.len() {
                    write!(
                        out,
                        "{} ",
                        (oc[i].var() as i32 + 1) * (-2 * oc[i].is_neg() as i32 + 1)
                    )
                    .unwrap();
                }
                writeln!(out, "0").unwrap();
            }
        }

        if ps.is_empty() {
            self.ok = false;
            false
        } else if ps.len() == 1 {
            self.unchecked_enqueue(ps[0], CREF_UNDEF);
            let confl = self.propagate();
            self.ok = !has_conflict(&confl);
            self.ok
        } else {
            let cr = self.ca.alloc(ps, false);
            self.clauses.push(cr);
            self.attach_clause(cr);
            true
        }
    }

    /// Add a non-clause constraint to the solver.
    pub fn add_constraint(&mut self, constr: Box<dyn Constraint>) -> bool {
        debug_assert!(self.decision_level() == 0);
        if !self.ok {
            return false;
        }

        let ci = self.constraints.len();
        self.constraints.push(Some(constr));
        self.num_pending_propagation.push(0);

        let mut constr_i = self.constraints[ci].take().unwrap();
        let initialized = constr_i.initialize(self, ci);
        self.constraints[ci] = Some(constr_i);
        if !initialized {
            self.ok = false;
            return false;
        }
        let confl = self.propagate();
        if has_conflict(&confl) {
            self.ok = false;
            return false;
        }
        true
    }

    /// Register constraint `ci` as a watcher of literal 'p'
    pub fn add_watch(&mut self, p: Lit, ci: ConstraintIdx) {
        self.constr_watches[p.0 as usize].push(ci);
    }

    fn attach_clause(&mut self, cr: CRef) {
        let size = self.ca.clause_size(cr);
        debug_assert!(size > 1);
        let c0 = self.ca.lit(cr, 0);
        let c1 = self.ca.lit(cr, 1);
        if size == 2 {
            self.watches_bin.occ_mut(!c0).push(Watcher {
                cref: cr,
                blocker: c1,
            });
            self.watches_bin.occ_mut(!c1).push(Watcher {
                cref: cr,
                blocker: c0,
            });
        } else {
            self.watches.occ_mut(!c0).push(Watcher {
                cref: cr,
                blocker: c1,
            });
            self.watches.occ_mut(!c1).push(Watcher {
                cref: cr,
                blocker: c0,
            });
        }
        if self.ca.learnt(cr) {
            self.stats[CoreStats::LearntsLiterals as usize] += size as u64;
        } else {
            self.stats[CoreStats::ClausesLiterals as usize] += size as u64;
        }
    }

    #[allow(dead_code)]
    fn attach_clause_purgatory(&mut self, _cr: CRef) {
        // this is used only by parallel solver, so currently not supported
        panic!("attach_clause_purgatory is not supported");
    }

    fn detach_clause(&mut self, cr: CRef, strict: bool) {
        let size = self.ca.clause_size(cr);
        debug_assert!(size > 1);
        let c0 = self.ca.lit(cr, 0);
        let c1 = self.ca.lit(cr, 1);
        if size == 2 {
            if strict {
                Self::remove_watcher(self.watches_bin.occ_mut(!c0), cr);
                Self::remove_watcher(self.watches_bin.occ_mut(!c1), cr);
            } else {
                // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
                self.watches_bin.smudge(!c0);
                self.watches_bin.smudge(!c1);
            }
        } else {
            if strict {
                Self::remove_watcher(self.watches.occ_mut(!c0), cr);
                Self::remove_watcher(self.watches.occ_mut(!c1), cr);
            } else {
                // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
                self.watches.smudge(!c0);
                self.watches.smudge(!c1);
            }
        }
        if self.ca.learnt(cr) {
            self.stats[CoreStats::LearntsLiterals as usize] -= size as u64;
        } else {
            self.stats[CoreStats::ClausesLiterals as usize] -= size as u64;
        }
    }

    /// Counterpart of `Glucose::remove` in `mtl/Alg.h` (specialized to watcher lists; watchers
    /// compare equal iff their `cref`s are equal).
    fn remove_watcher(ws: &mut Vec<Watcher>, cr: CRef) {
        let j = ws.iter().position(|w| w.cref == cr).unwrap();
        ws.remove(j);
    }

    // The purgatory is the 1-Watched scheme for imported clauses

    #[allow(dead_code)]
    fn detach_clause_purgatory(&mut self, _cr: CRef, _strict: bool) {
        // this is used only by parallel solver, so currently not supported
        panic!("detach_clause_purgatory is not supported");
    }

    fn remove_clause(&mut self, cr: CRef, in_purgatory: bool) {
        if self.certified_unsat {
            let size = self.ca.clause_size(cr);
            if self.vbyte {
                self.write_char(b'd');
                for i in 0..size {
                    let l = self.ca.lit(cr, i);
                    self.write_lit(2 * (l.var() as i32 + 1) + l.is_neg() as i32);
                }
                self.write_lit(0);
            } else {
                let mut buf = String::new();
                buf.push_str("d ");
                for i in 0..size {
                    let l = self.ca.lit(cr, i);
                    buf.push_str(&format!(
                        "{} ",
                        (l.var() as i32 + 1) * (-2 * l.is_neg() as i32 + 1)
                    ));
                }
                let out = self.certified_output.as_mut().unwrap();
                write!(out, "{}", buf).unwrap();
                writeln!(out, "0").unwrap();
            }
        }

        if in_purgatory {
            self.detach_clause_purgatory(cr, false);
        } else {
            self.detach_clause(cr, false);
        }
        // Don't leave pointers to free'd memory!
        if self.locked(cr) {
            self.vardata[self.ca.lit(cr, 0).var() as usize].reason = CREF_UNDEF;
        }
        self.ca.set_mark(cr, 1);
        self.ca.free(cr);
    }

    fn satisfied(&self, cr: CRef) -> bool {
        // Default mode
        for i in 0..self.ca.clause_size(cr) {
            if self.value_of(self.ca.lit(cr, i)) == LBool::True {
                return true;
            }
        }
        false
    }

    /************************************************************
     * Compute LBD functions
     *************************************************************/

    // (the C++ `computeLBD` is a template over the literal container; here it is split into
    // a slice version and a clause version)

    fn compute_lbd(&mut self, lits: &[Lit]) -> u32 {
        let mut nblevels = 0;
        self.myflag += 1;
        for i in 0..lits.len() {
            let l = self.level(lits[i].var());
            if self.perm_diff[l as usize] != self.myflag {
                self.perm_diff[l as usize] = self.myflag;
                nblevels += 1;
            }
        }
        nblevels
    }

    fn compute_lbd_clause(&mut self, cr: CRef) -> u32 {
        let mut nblevels = 0;
        self.myflag += 1;
        for i in 0..self.ca.clause_size(cr) {
            let l = self.level(self.ca.lit(cr, i).var());
            if self.perm_diff[l as usize] != self.myflag {
                self.perm_diff[l as usize] = self.myflag;
                nblevels += 1;
            }
        }
        nblevels
    }

    /******************************************************************
     * Minimisation with binary reolution
     ******************************************************************/
    fn minimisation_with_binary_resolution(&mut self, out_learnt: &mut Vec<Lit>) {
        // Find the LBD measure
        let lbd = self.compute_lbd(out_learnt);
        let p = !out_learnt[0];

        if lbd <= self.lb_lbd_minimizing_clause {
            self.myflag += 1;

            for i in 1..out_learnt.len() {
                self.perm_diff[out_learnt[i].var() as usize] = self.myflag;
            }

            let wbin_len = self.watches_bin.occ(p).len();
            let mut nb = 0;
            for k in 0..wbin_len {
                let imp = self.watches_bin.occ(p)[k].blocker;
                if self.perm_diff[imp.var() as usize] == self.myflag
                    && self.value_of(imp) == LBool::True
                {
                    nb += 1;
                    self.perm_diff[imp.var() as usize] = self.myflag - 1;
                }
            }
            let mut l = out_learnt.len() - 1;
            if nb > 0 {
                self.stats[CoreStats::NbReducedClauses as usize] += 1;
                let mut i = 1;
                while i < out_learnt.len() - nb {
                    if self.perm_diff[out_learnt[i].var() as usize] != self.myflag {
                        out_learnt.swap(l, i);
                        l -= 1;
                    } else {
                        i += 1;
                    }
                }

                out_learnt.truncate(out_learnt.len() - nb);
            }
        }
    }

    /// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
    fn cancel_until(&mut self, level: i32) {
        if self.decision_level() > level {
            for c in (self.trail_lim[level as usize]..self.trail.len() as i32).rev() {
                let p = self.trail[c as usize];
                let x = p.var();
                self.assigns[x as usize] = LBool::Undef;
                if self.phase_saving > 1
                    || (self.phase_saving == 1 && c > *self.trail_lim.last().unwrap())
                {
                    self.polarity[x as usize] = p.is_neg();
                }
                self.insert_var_order(x);
                while !self.undo_lists[x as usize].is_empty() {
                    let ci = *self.undo_lists[x as usize].last().unwrap();
                    let mut constr = self.constraints[ci].take().unwrap();
                    constr.undo(self, p);
                    self.constraints[ci] = Some(constr);
                    self.undo_lists[x as usize].pop();
                }
            }
            self.qhead = self.trail_lim[level as usize];
            self.trail.truncate(self.trail_lim[level as usize] as usize);
            self.trail_lim.truncate(level as usize);
        }
    }

    //=============================================================================================
    // Major methods:

    fn pick_branch_lit(&mut self) -> Option<Lit> {
        let mut next: Option<Var> = None;

        // Random decision:
        if ((self.randomize_first_descent && self.conflicts == 0)
            || Self::drand(&mut self.random_seed) < self.random_var_freq)
            && !self.order_heap.is_empty()
        {
            let i = Self::irand(&mut self.random_seed, self.order_heap.size() as i32);
            let v = self.order_heap[i as usize];
            next = Some(v);
            if self.value_of_var(v) == LBool::Undef && self.decision[v as usize] {
                self.stats[CoreStats::RndDecisions as usize] += 1;
            }
        }

        // Activity based decision:
        while next.is_none()
            || self.value_of_var(next.unwrap()) != LBool::Undef
            || !self.decision[next.unwrap() as usize]
        {
            if self.order_heap.is_empty() {
                next = None;
                break;
            } else {
                let activity = &self.activity;
                next = Some(
                    self.order_heap
                        .remove_min(|x, y| activity[x as usize] > activity[y as usize]),
                );
            }
        }

        // NOTE: in the C++ code the `next == var_Undef` check comes after the two randomized
        // branches below (`mkLit(var_Undef, ...)` would yield an invalid literal there); the Rust
        // port checks it first.
        let next = match next {
            None => return None,
            Some(v) => v,
        };

        if self.randomize_on_restarts
            && !self.fixed_randomize_on_restarts
            && self.new_descent
            && (self.decision_level() % 2 == 0)
        {
            return Some(Lit::new(
                next,
                (self.random_descent_assignments >> (self.decision_level() % 32)) & 1 != 0,
            ));
        }

        if self.fixed_randomize_on_restarts && self.decision_level() < 7 {
            return Some(Lit::new(
                next,
                (self.random_descent_assignments >> (self.decision_level() % 32)) & 1 != 0,
            ));
        }

        if self.force_unsat_on_new_descent && self.new_descent {
            if self.force_unsat[next as usize] != 0 {
                return Some(Lit::new(next, self.force_unsat[next as usize] < 0));
            }
            return Some(Lit::new(next, self.polarity[next as usize]));
        }

        Some(Lit::new(
            next,
            if self.rnd_pol {
                Self::drand(&mut self.random_seed) < 0.5
            } else {
                self.polarity[next as usize]
            },
        ))
    }

    /*_________________________________________________________________________________________________
    |
    |  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
    |
    |  Description:
    |    Analyze conflict and produce a reason clause.
    |
    |    Pre-conditions:
    |      * 'out_learnt' is assumed to be cleared.
    |      * Current decision level must be greater than root level.
    |
    |    Post-conditions:
    |      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
    |      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the
    |        rest of literals. There may be others from the same level though.
    |
    |________________________________________________________________________________________________@*/
    #[allow(clippy::too_many_arguments)]
    fn analyze(
        &mut self,
        mut confl: CRef,
        mut constr: Option<ConstraintIdx>,
        out_learnt: &mut Vec<Lit>,
        selectors: &mut Vec<Lit>,
        out_btlevel: &mut i32,
        lbd: &mut u32,
        sz_without_selectors: &mut u32,
    ) {
        let mut path_c = 0;
        let mut p: Option<Lit> = None;
        let mut p_reason: Vec<Lit> = Vec::new();

        let mut extra = self.enqueue_failure;

        // Generate conflict clause:
        //
        out_learnt.push(Lit::UNDEF); // (leave room for the asserting literal)
        let mut index = self.trail.len() as i32 - 1;
        loop {
            debug_assert!(confl != CREF_UNDEF || constr.is_some()); // (otherwise should be UIP)

            if let Some(ci) = constr {
                // TODO: add optimizations for custom constraints, too
                p_reason.clear();
                let mut c = self.constraints[ci].take().unwrap();
                c.calc_reason(self, p, extra, &mut p_reason);
                self.constraints[ci] = Some(c);
                extra = None;

                if self.dump_analysis_info {
                    print!("propagate reason:");
                    if let Some(p) = p {
                        print!(
                            "{{p: {}{}}}",
                            if p.is_neg() { "!" } else { "" },
                            self.var_name(p.var())
                        );
                    }
                    for j in 0..p_reason.len() {
                        let q = p_reason[j];
                        print!(
                            " {}{}",
                            if q.is_neg() { "!" } else { "" },
                            self.var_name(q.var())
                        );
                    }
                    println!();
                }

                for j in 0..p_reason.len() {
                    let q = p_reason[j];
                    if !self.seen[q.var() as usize] && self.level(q.var()) > 0 {
                        self.var_bump_activity(q.var());
                        self.seen[q.var() as usize] = true;
                        if self.level(q.var()) >= self.decision_level() {
                            path_c += 1;
                        } else {
                            out_learnt.push(!q);
                        }
                    }
                }
            } else {
                extra = None;

                // Special case for binary clauses
                // The first one has to be SAT
                if p.is_some()
                    && self.ca.clause_size(confl) == 2
                    && self.value_of(self.ca.lit(confl, 0)) == LBool::False
                {
                    debug_assert!(self.value_of(self.ca.lit(confl, 1)) == LBool::True);
                    let tmp = self.ca.lit(confl, 0);
                    self.ca.set_lit(confl, 0, self.ca.lit(confl, 1));
                    self.ca.set_lit(confl, 1, tmp);
                }

                if self.ca.learnt(confl) {
                    self.parallel_import_clause_during_conflict_analysis(confl);
                    self.cla_bump_activity(confl);
                } else {
                    // original clause
                    if !self.ca.get_seen(confl) {
                        self.stats[CoreStats::OriginalClausesSeen as usize] += 1;
                        self.ca.set_seen(confl, true);
                    }
                }

                // DYNAMIC NBLEVEL trick (see competition'09 companion paper)
                if self.ca.learnt(confl) && self.ca.lbd(confl) > 2 {
                    let nblevels = self.compute_lbd_clause(confl);
                    if nblevels + 1 < self.ca.lbd(confl) {
                        // improve the LBD
                        if self.ca.lbd(confl) <= self.lb_lbd_frozen_clause {
                            // seems to be interesting : keep it for the next round
                            self.ca.set_can_be_del(confl, false);
                        }
                        if self.chanseok_strategy && nblevels <= self.co_lbd_bound as u32 {
                            self.ca.nolearnt(confl);
                            let pos = self.learnts.iter().position(|&cr| cr == confl).unwrap();
                            self.learnts.remove(pos);
                            self.permanent_learnts.push(confl);
                            self.stats[CoreStats::NbPermanentLearnts as usize] += 1;
                        } else {
                            self.ca.set_lbd(confl, nblevels); // Update it
                        }
                    }
                }

                if self.dump_analysis_info {
                    print!("propagate along:");
                    for j in 0..self.ca.clause_size(confl) {
                        let q = self.ca.lit(confl, j);
                        print!(
                            " {}{}",
                            if q.is_neg() { "!" } else { "" },
                            self.var_name(q.var())
                        );
                    }
                    println!();
                }

                let start = if p.is_none() { 0 } else { 1 };
                for j in start..self.ca.clause_size(confl) {
                    let q = self.ca.lit(confl, j);

                    if !self.seen[q.var() as usize] {
                        if self.level(q.var()) == 0 {
                        } else {
                            // Here, the old case
                            if !self.is_selector(q.var()) {
                                self.var_bump_activity(q.var());
                            }

                            // This variable was responsible for a conflict,
                            // consider it as a UNSAT assignation for this literal
                            self.bump_force_unsat(!q); // Negation because q is false here

                            self.seen[q.var() as usize] = true;
                            if self.level(q.var()) >= self.decision_level() {
                                path_c += 1;
                                // UPDATEVARACTIVITY trick (see competition'09 companion paper)
                                if !self.is_selector(q.var())
                                    && self.reason(q.var()) != CREF_UNDEF
                                    && self.ca.learnt(self.reason(q.var()))
                                {
                                    self.last_decision_level.push(q);
                                }
                            } else if self.is_selector(q.var()) {
                                debug_assert!(self.value_of(q) == LBool::False);
                                selectors.push(q);
                            } else {
                                out_learnt.push(q);
                            }
                        }
                    }
                }
            }

            // Select next clause to look at:
            let index_pre = index;
            loop {
                let seen_here = self.seen[self.trail[index as usize].var() as usize];
                index -= 1;
                if seen_here {
                    break;
                }
            }
            for i in ((index + 1)..=index_pre).rev() {
                let p = self.trail[i as usize];
                let x = p.var();
                while !self.undo_lists[x as usize].is_empty() {
                    let ci = *self.undo_lists[x as usize].last().unwrap();
                    let mut constr = self.constraints[ci].take().unwrap();
                    constr.undo(self, p);
                    self.constraints[ci] = Some(constr);
                    self.undo_lists[x as usize].pop();
                }
            }
            let p_lit = self.trail[(index + 1) as usize];
            p = Some(p_lit);
            confl = self.reason(p_lit.var());
            constr = self.nc_reason(p_lit.var());
            self.seen[p_lit.var() as usize] = false;
            path_c -= 1;

            if path_c <= 0 {
                break;
            }
        }
        out_learnt[0] = !p.unwrap();

        // Simplify conflict clause:
        //
        for i in 0..selectors.len() {
            out_learnt.push(selectors[i]);
        }

        self.analyze_toclear.clear();
        self.analyze_toclear.extend_from_slice(out_learnt);
        if self.ccmin_mode == 2 {
            let mut abstract_level: u32 = 0;
            for i in 1..out_learnt.len() {
                // (maintain an abstraction of levels involved in conflict)
                abstract_level |= self.abstract_level(out_learnt[i].var());
            }

            let mut j = 1;
            for i in 1..out_learnt.len() {
                if self.reason(out_learnt[i].var()) == CREF_UNDEF
                    || !self.lit_redundant(out_learnt[i], abstract_level)
                {
                    out_learnt[j] = out_learnt[i];
                    j += 1;
                }
            }
            out_learnt.truncate(j);
        } else if self.ccmin_mode == 1 {
            let mut j = 1;
            for i in 1..out_learnt.len() {
                let x = out_learnt[i].var();

                if self.reason(x) == CREF_UNDEF {
                    out_learnt[j] = out_learnt[i];
                    j += 1;
                } else {
                    let cr = self.reason(out_learnt[i].var());
                    // Thanks to Siert Wieringa for this bug fix!
                    let start = if self.ca.clause_size(cr) == 2 { 0 } else { 1 };
                    for k in start..self.ca.clause_size(cr) {
                        let l = self.ca.lit(cr, k);
                        if !self.seen[l.var() as usize] && self.level(l.var()) > 0 {
                            out_learnt[j] = out_learnt[i];
                            j += 1;
                            break;
                        }
                    }
                }
            }
            out_learnt.truncate(j);
        }

        /* ***************************************
         Minimisation with binary clauses of the asserting clause
         First of all : we look for small clauses
         Then, we reduce clauses with small LBD.
         Otherwise, this can be useless
        */
        if !self.incremental && out_learnt.len() <= self.lb_size_minimizing_clause {
            self.minimisation_with_binary_resolution(out_learnt);
        }
        // Find correct backtrack level:
        //
        if out_learnt.len() == 1 {
            *out_btlevel = 0;
        } else {
            let mut max_i = 1;
            // Find the first literal assigned at the next-highest level:
            for i in 2..out_learnt.len() {
                if self.level(out_learnt[i].var()) > self.level(out_learnt[max_i].var()) {
                    max_i = i;
                }
            }
            // Swap-in this literal at index 1:
            let p = out_learnt[max_i];
            out_learnt[max_i] = out_learnt[1];
            out_learnt[1] = p;
            *out_btlevel = self.level(p.var());
        }

        *sz_without_selectors = out_learnt.len() as u32;

        if self.dump_analysis_info {
            print!("learnt clause:");
            for i in 0..out_learnt.len() {
                print!(
                    " {}{}",
                    if out_learnt[i].is_neg() { "!" } else { "" },
                    self.var_name(out_learnt[i].var())
                );
            }
            println!();
        }

        // Compute LBD
        *lbd = self.compute_lbd(&out_learnt[..out_learnt.len() - selectors.len()]);

        // UPDATEVARACTIVITY trick (see competition'09 companion paper)
        if !self.last_decision_level.is_empty() {
            for i in 0..self.last_decision_level.len() {
                let q = self.last_decision_level[i];
                if self.ca.lbd(self.reason(q.var())) < *lbd {
                    self.var_bump_activity(q.var());
                }
            }
            self.last_decision_level.clear();
        }

        for j in 0..self.analyze_toclear.len() {
            self.seen[self.analyze_toclear[j].var() as usize] = false; // ('seen[]' is now cleared)
        }
        for j in 0..selectors.len() {
            self.seen[selectors[j].var() as usize] = false;
        }
    }

    /// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
    /// visiting literals at levels that cannot be removed later.
    fn lit_redundant(&mut self, p: Lit, abstract_levels: u32) -> bool {
        if self.nc_reason(p.var()).is_some() {
            return false; // TODO: verify if this is okay
        }

        self.analyze_stack.clear();
        self.analyze_stack.push(p);
        let top = self.analyze_toclear.len();
        while !self.analyze_stack.is_empty() {
            debug_assert!(self.reason(self.analyze_stack.last().unwrap().var()) != CREF_UNDEF);
            let cr = self.reason(self.analyze_stack.last().unwrap().var());
            self.analyze_stack.pop();
            if self.ca.clause_size(cr) == 2 && self.value_of(self.ca.lit(cr, 0)) == LBool::False {
                debug_assert!(self.value_of(self.ca.lit(cr, 1)) == LBool::True);
                let tmp = self.ca.lit(cr, 0);
                self.ca.set_lit(cr, 0, self.ca.lit(cr, 1));
                self.ca.set_lit(cr, 1, tmp);
            }

            for i in 1..self.ca.clause_size(cr) {
                let p = self.ca.lit(cr, i);
                if !self.seen[p.var() as usize] && self.level(p.var()) > 0 {
                    if self.reason(p.var()) != CREF_UNDEF
                        && (self.abstract_level(p.var()) & abstract_levels) != 0
                    {
                        self.seen[p.var() as usize] = true;
                        self.analyze_stack.push(p);
                        self.analyze_toclear.push(p);
                    } else {
                        for j in top..self.analyze_toclear.len() {
                            self.seen[self.analyze_toclear[j].var() as usize] = false;
                        }
                        self.analyze_toclear.truncate(top);
                        return false;
                    }
                }
            }
        }

        true
    }

    /*_________________________________________________________________________________________________
    |
    |  analyzeFinal : (p : Lit)  ->  [void]
    |
    |  Description:
    |    Specialized analysis procedure to express the final conflict in terms of assumptions.
    |    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
    |    stores the result in 'out_conflict'.
    |________________________________________________________________________________________________@*/
    fn analyze_final(&mut self, p: Lit, out_conflict: &mut Vec<Lit>) {
        out_conflict.clear();
        out_conflict.push(p);

        if self.decision_level() == 0 {
            return;
        }

        self.seen[p.var() as usize] = true;

        for i in (self.trail_lim[0]..self.trail.len() as i32).rev() {
            let x = self.trail[i as usize].var();
            if self.seen[x as usize] {
                if self.reason(x) == CREF_UNDEF {
                    debug_assert!(self.level(x) > 0);
                    out_conflict.push(!self.trail[i as usize]);
                } else {
                    let cr = self.reason(x);
                    // Bug in case of assumptions due to special data structures for Binary.
                    // Many thanks to Sam Bayless (sbayless@cs.ubc.ca) for discover this bug.
                    let start = if self.ca.clause_size(cr) == 2 { 0 } else { 1 };
                    for j in start..self.ca.clause_size(cr) {
                        let v = self.ca.lit(cr, j).var();
                        if self.level(v) > 0 {
                            self.seen[v as usize] = true;
                        }
                    }
                }

                self.seen[x as usize] = false;
            }
        }

        self.seen[p.var() as usize] = false;
    }

    /// Counterpart of `enqueue(Lit p, Constraint* from)`.
    pub fn constraint_enqueue(&mut self, p: Lit, from: ConstraintIdx) -> bool {
        if self.value_of(p) != LBool::Undef {
            if self.value_of(p) == LBool::False {
                self.enqueue_failure = Some(!p);
                return false;
            }
            return true;
        }
        self.assigns[p.var() as usize] = LBool::from_bool(!p.is_neg());
        self.vardata[p.var() as usize] = mk_var_data_constr(from, self.decision_level());
        self.trail.push(p);

        self.add_num_pending_propagation(p, 1);
        true
    }

    fn unchecked_enqueue(&mut self, p: Lit, from: CRef) {
        debug_assert!(self.value_of(p) == LBool::Undef);
        self.assigns[p.var() as usize] = LBool::from_bool(!p.is_neg());
        self.vardata[p.var() as usize] = mk_var_data(from, self.decision_level());
        self.trail.push(p);

        self.add_num_pending_propagation(p, 1);
    }

    /// Handles the forces
    fn bump_force_unsat(&mut self, q: Lit) {
        self.force_unsat[q.var() as usize] = if q.is_neg() { -1 } else { 1 };
    }

    /*_________________________________________________________________________________________________
    |
    |  propagate : [void]  ->  [Clause*]
    |
    |  Description:
    |    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
    |    otherwise CRef_Undef.
    |
    |    Post-conditions:
    |      * the propagation queue is empty, even if there was a conflict.
    |________________________________________________________________________________________________@*/
    fn propagate(&mut self) -> (CRef, Option<ConstraintIdx>) {
        let mut confl = CREF_UNDEF;
        let mut constr: Option<ConstraintIdx> = None;
        let mut num_props: u64 = 0;
        {
            let ca = &self.ca;
            self.watches.clean_all(|w| ca.mark(w.cref) == 1);
            self.watches_bin.clean_all(|w| ca.mark(w.cref) == 1);
            self.unary_watches.clean_all(|w| ca.mark(w.cref) == 1);
        }
        while self.qhead < self.trail.len() as i32 {
            let p = self.trail[self.qhead as usize]; // 'p' is enqueued fact to propagate.
            self.qhead += 1;
            let mut skip_constr = false;
            num_props += 1;

            // First, Propagate binary clauses
            let wbin_len = self.watches_bin.occ(p).len();
            for k in 0..wbin_len {
                let w = self.watches_bin.occ(p)[k];
                let imp = w.blocker;

                if self.value_of(imp) == LBool::False {
                    self.add_num_pending_propagation(p, -1);
                    while self.qhead < self.trail.len() as i32 {
                        let q = self.trail[self.qhead as usize];
                        self.qhead += 1;
                        self.add_num_pending_propagation(q, -1);
                    }
                    // (the C++ code returns here without adding num_props to `propagations`)
                    return (w.cref, None);
                }

                if self.value_of(imp) == LBool::Undef {
                    self.unchecked_enqueue(imp, w.cref);
                }
            }

            // Now propagate other 2-watched clauses
            // (the C++ code keeps a reference to `watches[p]` while pushing to other watch lists;
            // in Rust the list is temporarily moved out instead)
            let mut ws = self.watches.take(p);
            let end = ws.len();
            let mut i = 0;
            let mut j = 0;
            'next_clause: while i != end {
                // Try to avoid inspecting the clause:
                let blocker = ws[i].blocker;
                if self.value_of(blocker) == LBool::True {
                    ws[j] = ws[i];
                    j += 1;
                    i += 1;
                    continue;
                }

                // Make sure the false literal is data[1]:
                let cr = ws[i].cref;
                debug_assert!(!self.ca.get_one_watched(cr));
                let false_lit = !p;
                if self.ca.lit(cr, 0) == false_lit {
                    let tmp = self.ca.lit(cr, 1);
                    self.ca.set_lit(cr, 0, tmp);
                    self.ca.set_lit(cr, 1, false_lit);
                }
                debug_assert!(self.ca.lit(cr, 1) == false_lit);
                i += 1;

                // If 0th watch is true, then clause is already satisfied.
                let first = self.ca.lit(cr, 0);
                let w = Watcher {
                    cref: cr,
                    blocker: first,
                };
                if first != blocker && self.value_of(first) == LBool::True {
                    ws[j] = w;
                    j += 1;
                    continue;
                }

                for k in 2..self.ca.clause_size(cr) {
                    if self.value_of(self.ca.lit(cr, k)) != LBool::False {
                        let tmp = self.ca.lit(cr, k);
                        self.ca.set_lit(cr, 1, tmp);
                        self.ca.set_lit(cr, k, false_lit);
                        self.watches.occ_mut(!self.ca.lit(cr, 1)).push(w);
                        continue 'next_clause;
                    }
                }

                // Did not find watch -- clause is unit under assignment:
                ws[j] = w;
                j += 1;
                if self.value_of(first) == LBool::False {
                    confl = cr;
                    self.add_num_pending_propagation(p, -1);
                    while self.qhead < self.trail.len() as i32 {
                        let q = self.trail[self.qhead as usize];
                        self.qhead += 1;
                        self.add_num_pending_propagation(q, -1);
                    }
                    skip_constr = true;
                    // Copy the remaining watches:
                    while i < end {
                        ws[j] = ws[i];
                        j += 1;
                        i += 1;
                    }
                } else {
                    self.unchecked_enqueue(first, cr);
                }
            }
            ws.truncate(j);
            self.watches.put(p, ws);

            if skip_constr {
                break;
            }
            let ncws_len = self.constr_watches[p.0 as usize].len();
            for k in 0..ncws_len {
                let ci = self.constr_watches[p.0 as usize][k];
                self.enqueue_failure = None;
                self.num_pending_propagation[ci] -= 1;
                let mut c = self.constraints[ci].take().unwrap();
                let no_conflict = c.propagate(self, p, ci);
                self.constraints[ci] = Some(c);
                if !no_conflict {
                    for l in (k + 1)..ncws_len {
                        let ci2 = self.constr_watches[p.0 as usize][l];
                        self.num_pending_propagation[ci2] -= 1;
                    }
                    constr = Some(ci);
                    while self.qhead < self.trail.len() as i32 {
                        let q = self.trail[self.qhead as usize];
                        self.qhead += 1;
                        self.add_num_pending_propagation(q, -1);
                    }
                    break;
                }
            }
            // unaryWatches "propagation"
            if self.use_unary_watched {
                panic!("unary watches are not supported");
            }
        }

        self.propagations += num_props;
        self.simp_db_props -= num_props as i64;

        (confl, constr)
    }

    fn add_num_pending_propagation(&mut self, p: Lit, inc: i32) {
        let ncws = &self.constr_watches[p.0 as usize];
        for i in 0..ncws.len() {
            self.num_pending_propagation[ncws[i]] += inc;
        }
    }

    /*_________________________________________________________________________________________________
    |
    |  propagateUnaryWatches : [Lit]  ->  [Clause*]
    |
    |  Description:
    |    Propagates unary watches of Lit p, return a conflict
    |    otherwise CRef_Undef
    |
    |________________________________________________________________________________________________@*/
    #[allow(dead_code)]
    fn propagate_unary_watches(&mut self, _p: Lit) -> CRef {
        // Unary watches are used only for clauses imported from other threads (parallel solver),
        // which is not supported; `propagate` panics before this can ever be reached
        // (the C++ code aborts likewise).
        panic!("propagate_unary_watches is not supported");
    }

    /*_________________________________________________________________________________________________
    |
    |  reduceDB : ()  ->  [void]
    |
    |  Description:
    |    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
    |    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
    |________________________________________________________________________________________________@*/
    fn reduce_db(&mut self) {
        self.stats[CoreStats::NbReduceDB as usize] += 1;
        let mut learnts = std::mem::take(&mut self.learnts);
        if self.chanseok_strategy {
            let ca = &self.ca;
            learnts.sort_by(|&x, &y| {
                if Self::reduce_db_act_lt(ca, x, y) {
                    std::cmp::Ordering::Less
                } else if Self::reduce_db_act_lt(ca, y, x) {
                    std::cmp::Ordering::Greater
                } else {
                    std::cmp::Ordering::Equal
                }
            });
        } else {
            let ca = &self.ca;
            learnts.sort_by(|&x, &y| {
                if Self::reduce_db_lt(ca, x, y) {
                    std::cmp::Ordering::Less
                } else if Self::reduce_db_lt(ca, y, x) {
                    std::cmp::Ordering::Greater
                } else {
                    std::cmp::Ordering::Equal
                }
            });

            // We have a lot of "good" clauses, it is difficult to compare them. Keep more !
            if self.ca.lbd(learnts[learnts.len() / RATIO_REMOVE_CLAUSES]) <= 3 {
                self.nbclausesbeforereduce += self.special_inc_reduce_db;
            }
            // Useless :-)
            if self.ca.lbd(*learnts.last().unwrap()) <= 5 {
                self.nbclausesbeforereduce += self.special_inc_reduce_db;
            }
        }
        // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
        // Keep clauses which seem to be usefull (their lbd was reduce during this sequence)

        let mut limit = (learnts.len() / 2) as i32;

        let mut j = 0;
        for i in 0..learnts.len() {
            let cr = learnts[i];
            if self.ca.lbd(cr) > 2
                && self.ca.clause_size(cr) > 2
                && self.ca.can_be_del(cr)
                && !self.locked(cr)
                && (i as i32) < limit
            {
                self.remove_clause(cr, false);
                self.stats[CoreStats::NbRemovedClauses as usize] += 1;
            } else {
                if !self.ca.can_be_del(cr) {
                    limit += 1; // we keep c, so we can delete an other clause
                }
                self.ca.set_can_be_del(cr, true); // At the next step, c can be delete
                learnts[j] = cr;
                j += 1;
            }
        }
        learnts.truncate(j);
        self.learnts = learnts;
        self.check_garbage();
    }

    fn remove_satisfied(&mut self, cs: &mut Vec<CRef>) {
        let mut j = 0;
        for i in 0..cs.len() {
            let cr = cs[i];
            if self.satisfied(cr) {
                if self.ca.get_one_watched(cr) {
                    self.remove_clause(cr, true);
                } else {
                    self.remove_clause(cr, false);
                }
            } else {
                cs[j] = cs[i];
                j += 1;
            }
        }
        cs.truncate(j);
    }

    fn rebuild_order_heap(&mut self) {
        let mut vs: Vec<Var> = Vec::new();
        for v in 0..self.n_vars() {
            if self.decision[v] && self.value_of_var(v as Var) == LBool::Undef {
                vs.push(v as Var);
            }
        }
        let activity = &self.activity;
        self.order_heap
            .build(&vs, |x, y| activity[x as usize] > activity[y as usize]);
    }

    /*_________________________________________________________________________________________________
    |
    |  simplify : [void]  ->  [bool]
    |
    |  Description:
    |    Simplify the clause database according to the current top-level assigment. Currently, the only
    |    thing done here is the removal of satisfied clauses, but more things can be put here.
    |________________________________________________________________________________________________@*/
    pub fn simplify(&mut self) -> bool {
        debug_assert!(self.decision_level() == 0);

        if !self.ok {
            self.ok = false;
            return false;
        } else {
            let confl = self.propagate();
            if has_conflict(&confl) {
                self.ok = false;
                return false;
            }
        }

        if self.n_assigns() as i32 == self.simp_db_assigns || self.simp_db_props > 0 {
            return true;
        }

        // Remove satisfied clauses:
        let mut learnts = std::mem::take(&mut self.learnts);
        self.remove_satisfied(&mut learnts);
        self.learnts = learnts;
        let mut permanent_learnts = std::mem::take(&mut self.permanent_learnts);
        self.remove_satisfied(&mut permanent_learnts);
        self.permanent_learnts = permanent_learnts;
        let mut unary_watched_clauses = std::mem::take(&mut self.unary_watched_clauses);
        self.remove_satisfied(&mut unary_watched_clauses);
        self.unary_watched_clauses = unary_watched_clauses;
        if self.remove_satisfied {
            // Can be turned off.
            let mut clauses = std::mem::take(&mut self.clauses);
            self.remove_satisfied(&mut clauses);
            self.clauses = clauses;
        }
        self.check_garbage();
        self.rebuild_order_heap();

        self.simp_db_assigns = self.n_assigns() as i32;
        // (shouldn't depend on stats really, but it will do for now)
        self.simp_db_props = (self.stats[CoreStats::ClausesLiterals as usize]
            + self.stats[CoreStats::LearntsLiterals as usize]) as i64;

        true
    }

    /// Adapt solver strategies
    fn adapt_solver(&mut self) {
        let mut adjusted = false;
        let mut reinit = false;
        let decpc = self.decisions as f32 / self.conflicts as f32;
        if decpc <= 1.2 {
            self.chanseok_strategy = true;
            self.co_lbd_bound = 4;
            self.glureduce = true;
            adjusted = true;
            reinit = true;
            self.first_reduce_db = 2000;
            self.nbclausesbeforereduce = self.first_reduce_db;
            self.cur_restart = (self.conflicts / self.nbclausesbeforereduce as u64) as i64 + 1;
            self.inc_reduce_db = 0;
        }
        if self.stats[CoreStats::NoDecisionConflict as usize] < 30000 {
            self.luby_restart = true;
            self.luby_restart_factor = 100;

            self.var_decay = 0.999;
            self.max_var_decay = 0.999;
            adjusted = true;
        }
        if self.stats[CoreStats::NoDecisionConflict as usize] > 54400 {
            self.chanseok_strategy = true;
            self.glureduce = true;
            self.co_lbd_bound = 3;
            self.first_reduce_db = 30000;
            self.var_decay = 0.99;
            self.max_var_decay = 0.99;
            self.randomize_on_restarts = true;
            adjusted = true;
        }
        // (unsigned arithmetic, like the C++ code)
        if self.stats[CoreStats::NbDL2 as usize].wrapping_sub(self.stats[CoreStats::NbBin as usize])
            > 20000
        {
            self.var_decay = 0.91;
            self.max_var_decay = 0.91;
            adjusted = true;
        }
        if adjusted {
            // Let's reinitialize the glucose restart strategy counters
            self.lbd_queue.fast_clear();
            self.sum_lbd = 0.0;
            self.conflicts_restarts = 0;
        }

        if self.chanseok_strategy && adjusted {
            let mut j = 0;
            let learnts = std::mem::take(&mut self.learnts);
            let mut learnts = learnts;
            for i in 0..learnts.len() {
                let cr = learnts[i];
                if self.ca.lbd(cr) <= self.co_lbd_bound as u32 {
                    self.permanent_learnts.push(cr);
                } else {
                    learnts[j] = cr;
                    j += 1;
                }
            }
            learnts.truncate(j);
            self.learnts = learnts;
        }

        if reinit {
            debug_assert!(self.decision_level() == 0);
            let learnts = std::mem::take(&mut self.learnts);
            for i in 0..learnts.len() {
                self.remove_clause(learnts[i], false);
            }
            self.learnts = Vec::new();
            self.check_garbage();
        }
    }

    /*_________________________________________________________________________________________________
    |
    |  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
    |
    |  Description:
    |    Search for a model the specified number of conflicts.
    |    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
    |
    |  Output:
    |    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
    |    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
    |    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
    |________________________________________________________________________________________________@*/
    fn search(&mut self, nof_conflicts: i32) -> LBool {
        debug_assert!(self.ok);
        let mut backtrack_level: i32 = 0;
        let mut conflict_c = 0;
        let mut learnt_clause: Vec<Lit> = Vec::new();
        let mut selectors: Vec<Lit> = Vec::new();
        let mut nblevels: u32 = 0;
        let mut sz_without_selectors: u32 = 0;
        let mut blocked = false;
        let mut a_decision_was_made = false;

        self.starts += 1;
        loop {
            if self.decision_level() == 0 {
                // We import clauses FIXME: ensure that we will import clauses enventually (restart after some point)
                self.parallel_import_unary_clauses();

                if self.parallel_import_clauses() {
                    return LBool::False;
                }
            }
            let confl_pair = self.propagate();

            if has_conflict(&confl_pair) {
                self.new_descent = false;
                if self.parallel_job_is_finished() {
                    return LBool::Undef;
                }

                if !a_decision_was_made {
                    self.stats[CoreStats::NoDecisionConflict as usize] += 1;
                }
                a_decision_was_made = false;

                self.stats[CoreStats::SumDecisionLevels as usize] += self.decision_level() as u64;
                self.stats[CoreStats::SumTrail as usize] += self.trail.len() as u64;
                // CONFLICT
                self.conflicts += 1;
                conflict_c += 1;
                self.conflicts_restarts += 1;
                if self.conflicts % 5000 == 0 && self.var_decay < self.max_var_decay {
                    self.var_decay += 0.01;
                }

                if self.verbosity >= 1
                    && self.starts > 0
                    && self.conflicts % self.verb_every_conflicts as u64 == 0
                {
                    println!(
                        "c | {:8}   {:7}    {:5} | {:7} {:8} {:8} | {:5} {:8}   {:6} {:8} | {:6.3} % |",
                        self.starts,
                        self.stats[CoreStats::NbStopsRestarts as usize],
                        self.conflicts / self.starts,
                        self.stats[CoreStats::DecVars as usize] as i64
                            - (if self.trail_lim.is_empty() {
                                self.trail.len() as i64
                            } else {
                                self.trail_lim[0] as i64
                            }),
                        self.n_clauses(),
                        self.stats[CoreStats::ClausesLiterals as usize],
                        self.stats[CoreStats::NbReduceDB as usize],
                        self.n_learnts(),
                        self.stats[CoreStats::NbDL2 as usize],
                        self.stats[CoreStats::NbRemovedClauses as usize],
                        self.progress_estimate() * 100.0
                    );
                }
                if self.decision_level() == 0 {
                    return LBool::False;
                }
                if self.adapt_strategies && self.conflicts == 100000 {
                    self.cancel_until(0);
                    self.adapt_solver();
                    self.adapt_strategies = false;
                    return LBool::Undef;
                }

                self.trail_queue.push(self.trail.len() as u32);
                // BLOCK RESTART (CP 2012 paper)
                if self.conflicts_restarts > LOWER_BOUND_FOR_BLOCKING_RESTART
                    && self.lbd_queue.is_valid()
                    && self.trail.len() as f64 > self.r * self.trail_queue.get_avg() as f64
                {
                    self.lbd_queue.fast_clear();
                    self.stats[CoreStats::NbStopsRestarts as usize] += 1;
                    if !blocked {
                        self.stats[CoreStats::LastBlockAtRestart as usize] = self.starts;
                        self.stats[CoreStats::NbStopsRestartsSame as usize] += 1;
                        blocked = true;
                    }
                }

                learnt_clause.clear();
                selectors.clear();

                self.analyze(
                    confl_pair.0,
                    confl_pair.1,
                    &mut learnt_clause,
                    &mut selectors,
                    &mut backtrack_level,
                    &mut nblevels,
                    &mut sz_without_selectors,
                );

                self.lbd_queue.push(nblevels);
                self.sum_lbd += nblevels as f32;

                self.cancel_until(backtrack_level);

                if self.certified_unsat {
                    if self.vbyte {
                        self.write_char(b'a');
                        for i in 0..learnt_clause.len() {
                            self.write_lit(
                                2 * (learnt_clause[i].var() as i32 + 1)
                                    + learnt_clause[i].is_neg() as i32,
                            );
                        }
                        self.write_lit(0);
                    } else {
                        let out = self.certified_output.as_mut().unwrap();
                        for i in 0..learnt_clause.len() {
                            write!(
                                out,
                                "{} ",
                                (learnt_clause[i].var() as i32 + 1)
                                    * (-2 * learnt_clause[i].is_neg() as i32 + 1)
                            )
                            .unwrap();
                        }
                        writeln!(out, "0").unwrap();
                    }
                }

                if learnt_clause.len() == 1 {
                    self.unchecked_enqueue(learnt_clause[0], CREF_UNDEF);
                    self.stats[CoreStats::NbUn as usize] += 1;
                    self.parallel_export_unary_clause(learnt_clause[0]);
                } else {
                    let cr;
                    if self.chanseok_strategy && nblevels <= self.co_lbd_bound as u32 {
                        cr = self.ca.alloc(&learnt_clause, false);
                        self.permanent_learnts.push(cr);
                        self.stats[CoreStats::NbPermanentLearnts as usize] += 1;
                    } else {
                        cr = self.ca.alloc(&learnt_clause, true);
                        self.ca.set_lbd(cr, nblevels);
                        self.ca.set_one_watched(cr, false);
                        self.learnts.push(cr);
                        self.cla_bump_activity(cr);
                    }
                    if nblevels <= 2 {
                        self.stats[CoreStats::NbDL2 as usize] += 1; // stats
                    }
                    if self.ca.clause_size(cr) == 2 {
                        self.stats[CoreStats::NbBin as usize] += 1; // stats
                    }
                    self.attach_clause(cr);
                    self.last_learnt_clause = cr; // Use in multithread (to hard to put inside ParallelSolver)
                    self.parallel_export_clause_during_search(cr);
                    self.unchecked_enqueue(learnt_clause[0], cr);
                }
                self.var_decay_activity();
                self.cla_decay_activity();
            } else {
                // Our dynamic restart, see the SAT09 competition compagnion paper
                if (self.luby_restart && nof_conflicts <= conflict_c)
                    || (!self.luby_restart
                        && self.lbd_queue.is_valid()
                        && self.lbd_queue.get_avg() as f64 * self.k
                            > (self.sum_lbd / self.conflicts_restarts as f32) as f64)
                {
                    self.lbd_queue.fast_clear();
                    self.progress_estimate = self.progress_estimate();
                    let bt = 0;
                    self.new_descent = true;

                    if self.randomize_on_restarts || self.fixed_randomize_on_restarts {
                        self.random_descent_assignments = Self::drand(&mut self.random_seed) as u32;
                    }

                    self.cancel_until(bt);
                    return LBool::Undef;
                }

                // Simplify the set of problem clauses:
                if self.decision_level() == 0 && !self.simplify() {
                    return LBool::False;
                }
                // Perform clause database reduction !
                if (self.chanseok_strategy
                    && !self.glureduce
                    && self.learnts.len() as i32 > self.first_reduce_db)
                    || (self.glureduce
                        && self.conflicts
                            >= (self.cur_restart as u32)
                                .wrapping_mul(self.nbclausesbeforereduce as u32)
                                as u64)
                {
                    if !self.learnts.is_empty() {
                        self.cur_restart =
                            (self.conflicts / self.nbclausesbeforereduce as u64) as i64 + 1;
                        self.reduce_db();
                        if !self.panic_mode_is_enabled() {
                            self.nbclausesbeforereduce += self.inc_reduce_db;
                        }
                    }
                }

                self.last_learnt_clause = CREF_UNDEF;
                let mut next: Option<Lit> = None;
                while self.decision_level() < self.assumptions.len() as i32 {
                    // Perform user provided assumption:
                    let p = self.assumptions[self.decision_level() as usize];
                    if self.value_of(p) == LBool::True {
                        // Dummy decision level:
                        self.new_decision_level();
                    } else if self.value_of(p) == LBool::False {
                        let mut conflict = std::mem::take(&mut self.conflict);
                        self.analyze_final(!p, &mut conflict);
                        self.conflict = conflict;
                        return LBool::False;
                    } else {
                        next = Some(p);
                        break;
                    }
                }

                if next.is_none() {
                    // New variable decision:
                    self.decisions += 1;
                    next = self.pick_branch_lit();
                    if next.is_none() {
                        // Model found:
                        for ci in 0..self.constraints.len() {
                            debug_assert!(self.num_pending_propagation[ci] == 0);
                        }
                        return LBool::True;
                    }
                }

                // Increase decision level and enqueue 'next'
                a_decision_was_made = true;
                self.new_decision_level();
                self.unchecked_enqueue(next.unwrap(), CREF_UNDEF);
            }
        }
    }

    /// Counterpart of `progressEstimate()`.  (Note: the C++ class also has a field of the same
    /// name; Rust allows a method and a field to share the name.)
    fn progress_estimate(&self) -> f64 {
        let mut progress = 0.0;
        let f = 1.0 / self.n_vars() as f64;

        for i in 0..=self.decision_level() {
            let beg = if i == 0 {
                0
            } else {
                self.trail_lim[(i - 1) as usize]
            };
            let end = if i == self.decision_level() {
                self.trail.len() as i32
            } else {
                self.trail_lim[i as usize]
            };
            progress += f.powi(i) * (end - beg) as f64;
        }

        progress / self.n_vars() as f64
    }

    pub fn print_incremental_stats(&self) {
        println!("c---------- Glucose Stats -------------------------");
        println!("c restarts              : {}", self.starts);
        println!(
            "c nb ReduceDB           : {}",
            self.stats[CoreStats::NbReduceDB as usize]
        );
        println!(
            "c nb removed Clauses    : {}",
            self.stats[CoreStats::NbRemovedClauses as usize]
        );
        println!(
            "c nb learnts DL2        : {}",
            self.stats[CoreStats::NbDL2 as usize]
        );
        println!(
            "c nb learnts size 2     : {}",
            self.stats[CoreStats::NbBin as usize]
        );
        println!(
            "c nb learnts size 1     : {}",
            self.stats[CoreStats::NbUn as usize]
        );
        println!("c conflicts             : {}", self.conflicts);
        println!("c decisions             : {}", self.decisions);
        println!("c propagations          : {}", self.propagations);
        println!(
            "\nc SAT Calls             : {} in {} seconds",
            self.nb_sat_calls, self.total_time_4_sat
        );
        println!(
            "c UNSAT Calls           : {} in {} seconds",
            self.nb_unsat_calls, self.total_time_4_unsat
        );
        println!("c--------------------------------------------------");
    }

    pub fn luby(&self, y: f64, mut x: i32) -> f64 {
        // Find the finite subsequence that contains index 'x', and the
        // size of that subsequence:
        let mut size = 1;
        let mut seq = 0;
        while size < x + 1 {
            seq += 1;
            size = 2 * size + 1;
        }

        while size - 1 != x {
            size = (size - 1) >> 1;
            seq -= 1;
            x %= size;
        }

        y.powi(seq)
    }

    // NOTE: assumptions passed in member-variable 'assumptions'.

    fn solve_(&mut self) -> LBool {
        self.model.clear();
        self.conflict.clear();
        if !self.ok {
            return LBool::False;
        }
        let cur_time = std::time::Instant::now();

        self.solves += 1;

        let mut status = LBool::Undef;
        if !self.incremental && self.verbosity >= 1 {
            println!("c ========================================[ MAGIC CONSTANTS ]==============================================");
            println!("c | Constants are supposed to work well together :-)                                                      |");
            println!("c | however, if you find better choices, please let us known...                                           |");
            println!("c |-------------------------------------------------------------------------------------------------------|");
            if self.adapt_strategies {
                println!("c | Adapt dynamically the solver after 100000 conflicts (restarts, reduction strategies...)               |");
                println!("c |-------------------------------------------------------------------------------------------------------|");
            }
            println!("c |                                |                                |                                     |");
            println!("c | - Restarts:                    | - Reduce Clause DB:            | - Minimize Asserting:               |");
            if self.chanseok_strategy {
                println!(
                    "c |   * LBD Queue    : {:6}      |     chanseok Strategy          |    * size < {:3}                     |",
                    self.lbd_queue.max_size(),
                    self.lb_size_minimizing_clause
                );
                println!(
                    "c |   * Trail  Queue : {:6}      |   * learnts size     : {:6}  |    * lbd  < {:3}                     |",
                    self.trail_queue.max_size(),
                    self.first_reduce_db,
                    self.lb_lbd_minimizing_clause
                );
                println!(
                    "c |   * K            : {:6.2}      |   * Bound LBD   : {:6}       |                                     |",
                    self.k, self.co_lbd_bound
                );
                println!(
                    "c |   * R            : {:6.2}      |   * Protected :  (lbd)< {:2}     |                                     |",
                    self.r, self.lb_lbd_frozen_clause
                );
            } else {
                println!(
                    "c |   * LBD Queue    : {:6}      |   * First     : {:6}         |    * size < {:3}                     |",
                    self.lbd_queue.max_size(),
                    self.nbclausesbeforereduce,
                    self.lb_size_minimizing_clause
                );
                println!(
                    "c |   * Trail  Queue : {:6}      |   * Inc       : {:6}         |    * lbd  < {:3}                     |",
                    self.trail_queue.max_size(),
                    self.inc_reduce_db,
                    self.lb_lbd_minimizing_clause
                );
                println!(
                    "c |   * K            : {:6.2}      |   * Special   : {:6}         |                                     |",
                    self.k, self.special_inc_reduce_db
                );
                println!(
                    "c |   * R            : {:6.2}      |   * Protected :  (lbd)< {:2}     |                                     |",
                    self.r, self.lb_lbd_frozen_clause
                );
            }
            println!("c |                                |                                |                                     |");
            println!("c ==================================[ Search Statistics (every {:6} conflicts) ]=========================", self.verb_every_conflicts);
            println!("c |                                                                                                       |");
            println!("c |          RESTARTS           |          ORIGINAL         |              LEARNT              | Progress |");
            println!("c |       NB   Blocked  Avg Cfc |    Vars  Clauses Literals |   Red   Learnts    LBD2  Removed |          |");
            println!("c =========================================================================================================");
        }

        // Search:
        let mut curr_restarts = 0;
        while status == LBool::Undef {
            status = self.search(if self.luby_restart {
                // the parameter is useless in glucose, kept to allow modifications
                (self.luby(self.restart_inc as f64, curr_restarts)
                    * self.luby_restart_factor as f64) as i32
            } else {
                0
            });

            if !self.within_budget() {
                break;
            }
            curr_restarts += 1;
        }

        if !self.incremental && self.verbosity >= 1 {
            println!("c =========================================================================================================");
        }

        if self.certified_unsat {
            // Want certified output
            if status == LBool::False {
                if self.vbyte {
                    self.write_char(b'a');
                    self.write_lit(0);
                } else {
                    writeln!(self.certified_output.as_mut().unwrap(), "0").unwrap();
                }
            }
            self.certified_output = None; // fclose(certifiedOutput)
        }

        if status == LBool::True {
            // Extend & copy model:
            self.model.resize(self.n_vars(), LBool::Undef);
            for i in 0..self.n_vars() {
                self.model[i] = self.value_of_var(i as Var);
            }
        } else if status == LBool::False && self.conflict.is_empty() {
            self.ok = false;
        }

        self.cancel_until(0);

        let elapsed = cur_time.elapsed().as_secs_f64();
        if status == LBool::True {
            self.nb_sat_calls += 1;
            self.total_time_4_sat += elapsed;
        }
        if status == LBool::False {
            self.nb_unsat_calls += 1;
            self.total_time_4_unsat += elapsed;
        }

        status
    }

    //=============================================================================================
    // Writing CNF to DIMACS:
    //
    // FIXME: this needs to be rewritten completely.

    fn map_var(x: Var, map: &mut Vec<i32>, max: &mut i32) -> i32 {
        if map.len() <= x as usize || map[x as usize] == -1 {
            map.resize((x as usize + 1).max(map.len()), -1);
            map[x as usize] = *max;
            *max += 1;
        }
        map[x as usize]
    }

    fn to_dimacs_clause(
        &self,
        f: &mut impl Write,
        cr: CRef,
        map: &mut Vec<i32>,
        max: &mut i32,
    ) -> std::io::Result<()> {
        if self.satisfied(cr) {
            return Ok(());
        }

        for i in 0..self.ca.clause_size(cr) {
            let l = self.ca.lit(cr, i);
            if self.value_of(l) != LBool::False {
                write!(
                    f,
                    "{}{} ",
                    if l.is_neg() { "-" } else { "" },
                    Self::map_var(l.var(), map, max) + 1
                )?;
            }
        }
        writeln!(f, "0")?;
        Ok(())
    }

    pub fn to_dimacs(&mut self, file: &str, assumps: &[Lit]) -> std::io::Result<()> {
        let mut f = std::fs::File::create(file)?;
        self.to_dimacs_write(&mut f, assumps)
    }

    /// NOTE: like the C++ code, this uses the member `assumptions` (not the `_assumps` argument)
    /// for the unit clauses.
    fn to_dimacs_write(&mut self, f: &mut impl Write, _assumps: &[Lit]) -> std::io::Result<()> {
        // Handle case when solver is in contradictory state:
        if !self.ok {
            writeln!(f, "p cnf 1 2\n1 0\n-1 0")?;
            return Ok(());
        }

        let mut map: Vec<i32> = Vec::new();
        let mut max: i32 = 0;

        // Cannot use removeClauses here because it is not safe
        // to deallocate them at this point. Could be improved.
        let mut cnt = 0;
        for i in 0..self.clauses.len() {
            if !self.satisfied(self.clauses[i]) {
                cnt += 1;
            }
        }

        for i in 0..self.clauses.len() {
            if !self.satisfied(self.clauses[i]) {
                let cr = self.clauses[i];
                for j in 0..self.ca.clause_size(cr) {
                    let l = self.ca.lit(cr, j);
                    if self.value_of(l) != LBool::False {
                        Self::map_var(l.var(), &mut map, &mut max);
                    }
                }
            }
        }

        // Assumptions are added as unit clauses:
        cnt += self.assumptions.len();

        writeln!(f, "p cnf {} {}", max, cnt)?;

        for i in 0..self.assumptions.len() {
            debug_assert!(self.value_of(self.assumptions[i]) != LBool::False);
            writeln!(
                f,
                "{}{} 0",
                if self.assumptions[i].is_neg() {
                    "-"
                } else {
                    ""
                },
                Self::map_var(self.assumptions[i].var(), &mut map, &mut max) + 1
            )?;
        }

        for i in 0..self.clauses.len() {
            self.to_dimacs_clause(f, self.clauses[i], &mut map, &mut max)?;
        }

        if self.verbosity > 0 {
            println!("Wrote {} clauses with {} variables.", cnt, max);
        }
        Ok(())
    }

    //=============================================================================================
    // Garbage Collection methods:

    fn reloc_all(&mut self, to: &mut ClauseAllocator) {
        // All watchers:
        {
            let ca = &self.ca;
            self.watches.clean_all(|w| ca.mark(w.cref) == 1);
            self.watches_bin.clean_all(|w| ca.mark(w.cref) == 1);
            self.unary_watches.clean_all(|w| ca.mark(w.cref) == 1);
        }
        for v in 0..self.n_vars() {
            for s in 0..2 {
                let p = Lit::new(v as Var, s != 0);
                for j in 0..self.watches.occ(p).len() {
                    let mut cr = self.watches.occ(p)[j].cref;
                    self.ca.reloc(&mut cr, to);
                    self.watches.occ_mut(p)[j].cref = cr;
                }
                for j in 0..self.watches_bin.occ(p).len() {
                    let mut cr = self.watches_bin.occ(p)[j].cref;
                    self.ca.reloc(&mut cr, to);
                    self.watches_bin.occ_mut(p)[j].cref = cr;
                }
                for j in 0..self.unary_watches.occ(p).len() {
                    let mut cr = self.unary_watches.occ(p)[j].cref;
                    self.ca.reloc(&mut cr, to);
                    self.unary_watches.occ_mut(p)[j].cref = cr;
                }
            }
        }

        // All reasons:
        //
        for i in 0..self.trail.len() {
            let v = self.trail[i].var();

            if self.reason(v) != CREF_UNDEF
                && (self.ca.reloced(self.reason(v)) || self.locked(self.reason(v)))
            {
                let mut cr = self.vardata[v as usize].reason;
                self.ca.reloc(&mut cr, to);
                self.vardata[v as usize].reason = cr;
            }
        }

        // All learnt:
        //
        for i in 0..self.learnts.len() {
            let mut cr = self.learnts[i];
            self.ca.reloc(&mut cr, to);
            self.learnts[i] = cr;
        }

        for i in 0..self.permanent_learnts.len() {
            let mut cr = self.permanent_learnts[i];
            self.ca.reloc(&mut cr, to);
            self.permanent_learnts[i] = cr;
        }

        // All original:
        //
        for i in 0..self.clauses.len() {
            let mut cr = self.clauses[i];
            self.ca.reloc(&mut cr, to);
            self.clauses[i] = cr;
        }

        for i in 0..self.unary_watched_clauses.len() {
            let mut cr = self.unary_watched_clauses[i];
            self.ca.reloc(&mut cr, to);
            self.unary_watched_clauses[i] = cr;
        }
    }

    fn garbage_collect(&mut self) {
        // Initialize the next region to a size corresponding to the estimated utilization degree. This
        // is not precise but should avoid some unnecessary reallocations for the new region:
        let mut to = ClauseAllocator::with_capacity(self.ca.size() - self.ca.wasted());
        self.reloc_all(&mut to);
        if self.verbosity >= 2 {
            println!(
                "|  Garbage collection:   {:12} bytes => {:12} bytes             |",
                self.ca.size() * 4,
                to.size() * 4
            );
        }
        self.ca = to;
    }

    //---------------------------------------------------------------
    // Functions related to MultiThread.
    // Useless in case of single core solver (aka original glucose)
    // Keep them empty if you just use core solver
    //---------------------------------------------------------------

    fn panic_mode_is_enabled(&self) -> bool {
        false
    }

    fn parallel_import_unary_clauses(&mut self) {}

    fn parallel_import_clauses(&mut self) -> bool {
        false
    }

    fn parallel_export_unary_clause(&mut self, _p: Lit) {}

    fn parallel_export_clause_during_search(&mut self, _cr: CRef) {}

    fn parallel_job_is_finished(&self) -> bool {
        // Parallel: another job has finished let's quit
        false
    }

    fn parallel_import_clause_during_conflict_analysis(&mut self, _cr: CRef) {}

    //=============================================================================================
    // Implementation of inline methods (from Solver.h):

    fn reason(&self, x: Var) -> CRef {
        self.vardata[x as usize].reason
    }

    fn nc_reason(&self, x: Var) -> Option<ConstraintIdx> {
        self.vardata[x as usize].nc_reason
    }

    fn level(&self, x: Var) -> i32 {
        self.vardata[x as usize].level
    }

    /// Insert a variable in the decision order priority queue.
    fn insert_var_order(&mut self, x: Var) {
        if !self.order_heap.in_heap(x) && self.decision[x as usize] {
            let activity = &self.activity;
            self.order_heap
                .insert(x, |a, b| activity[a as usize] > activity[b as usize]);
        }
    }

    /// Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
    fn var_decay_activity(&mut self) {
        self.var_inc *= 1.0 / self.var_decay;
    }

    /// Increase a variable with the current 'bump' value.
    fn var_bump_activity(&mut self, v: Var) {
        self.var_bump_activity_(v, self.var_inc);
    }

    fn var_bump_activity_(&mut self, v: Var, inc: f64) {
        self.activity[v as usize] += inc;
        if self.activity[v as usize] > 1e100 {
            // Rescale:
            for i in 0..self.n_vars() {
                self.activity[i] *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }

        // Update order_heap with respect to new activity:
        if self.order_heap.in_heap(v) {
            let activity = &self.activity;
            self.order_heap
                .decrease(v, |a, b| activity[a as usize] > activity[b as usize]);
        }
    }

    /// Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.
    fn cla_decay_activity(&mut self) {
        self.cla_inc *= 1.0 / self.clause_decay;
    }

    /// Increase a clause with the current 'bump' value.
    fn cla_bump_activity(&mut self, cr: CRef) {
        let act = (self.ca.activity(cr) as f64 + self.cla_inc) as f32;
        self.ca.set_activity(cr, act);
        if act as f64 > 1e20 {
            // Rescale:
            for i in 0..self.learnts.len() {
                let l = self.learnts[i];
                let a = self.ca.activity(l) * 1e-20;
                self.ca.set_activity(l, a);
            }
            self.cla_inc *= 1e-20;
        }
    }

    fn check_garbage(&mut self) {
        self.check_garbage_frac(self.garbage_frac);
    }

    fn check_garbage_frac(&mut self, gf: f64) {
        if self.ca.wasted() as f64 > self.ca.size() as f64 * gf {
            self.garbage_collect();
        }
    }

    // NOTE: enqueue does not set the ok flag! (only public methods do)
    /// Test if fact 'p' contradicts current state, enqueue otherwise.
    #[allow(dead_code)]
    fn enqueue(&mut self, p: Lit, from: CRef) -> bool {
        if self.value_of(p) != LBool::Undef {
            self.value_of(p) != LBool::False
        } else {
            self.unchecked_enqueue(p, from);
            true
        }
    }

    /// Add a clause to the solver.
    pub fn add_clause(&mut self, ps: &[Lit]) -> bool {
        self.add_tmp.clear();
        self.add_tmp.extend_from_slice(ps);
        let mut add_tmp = std::mem::take(&mut self.add_tmp);
        let result = self.add_clause_(&mut add_tmp);
        self.add_tmp = add_tmp;
        result
    }

    /// Add the empty clause, making the solver contradictory.
    pub fn add_empty_clause(&mut self) -> bool {
        self.add_clause(&[])
    }

    /// Returns TRUE if a clause is a reason for some implication in the current state.
    fn locked(&self, cr: CRef) -> bool {
        let c0 = self.ca.lit(cr, 0);
        if self.ca.clause_size(cr) > 2 {
            return self.value_of(c0) == LBool::True
                && self.reason(c0.var()) != CREF_UNDEF
                && self.reason(c0.var()) == cr;
        }
        let c1 = self.ca.lit(cr, 1);
        (self.value_of(c0) == LBool::True
            && self.reason(c0.var()) != CREF_UNDEF
            && self.reason(c0.var()) == cr)
            || (self.value_of(c1) == LBool::True
                && self.reason(c1.var()) != CREF_UNDEF
                && self.reason(c1.var()) == cr)
    }

    /// Begins a new decision level.
    fn new_decision_level(&mut self) {
        self.trail_lim.push(self.trail.len() as i32);
    }

    /// Gives the current decisionlevel.
    pub fn decision_level(&self) -> i32 {
        self.trail_lim.len() as i32
    }

    /// Gives the current decision level as `usize` (used by the cspuz_core backend).
    pub fn current_level(&self) -> usize {
        self.trail_lim.len()
    }

    /// Returns true if the literal `p` was assigned at the current decision level.
    pub fn is_current_level(&self, p: Lit) -> bool {
        self.decision_level() == self.level(p.var())
    }

    /// Used to represent an abstraction of sets of decision levels.
    fn abstract_level(&self, x: Var) -> u32 {
        1u32 << (self.level(x) & 31)
    }

    /// The current value of a variable.  Counterpart of `value(Var)`.
    pub fn value_of_var(&self, x: Var) -> LBool {
        self.assigns[x as usize]
    }

    /// The current value of a literal.  Counterpart of `value(Lit)`.
    pub fn value_of(&self, p: Lit) -> LBool {
        self.assigns[p.var() as usize].xor(p.is_neg())
    }

    /// The value of a variable in the last model. The last call to solve must have been satisfiable.
    pub fn model_value_var(&self, x: Var) -> LBool {
        self.model[x as usize]
    }

    /// The value of a literal in the last model. The last call to solve must have been satisfiable.
    pub fn model_value(&self, p: Lit) -> LBool {
        self.model[p.var() as usize].xor(p.is_neg())
    }

    /// The current number of assigned literals.
    pub fn n_assigns(&self) -> usize {
        self.trail.len()
    }

    /// The current number of original clauses.
    pub fn n_clauses(&self) -> usize {
        self.clauses.len()
    }

    /// The current number of learnt clauses.
    pub fn n_learnts(&self) -> usize {
        self.learnts.len()
    }

    /// The current number of variables.
    pub fn n_vars(&self) -> usize {
        self.vardata.len()
    }

    pub fn n_free_vars(&self) -> i32 {
        let a = self.stats[CoreStats::DecVars as usize];
        a as i32
            - (if self.trail_lim.is_empty() {
                self.trail.len() as i32
            } else {
                self.trail_lim[0]
            })
    }

    pub fn var_name(&self, x: Var) -> String {
        if (x as usize) < self.var_names.len() && !self.var_names[x as usize].is_empty() {
            self.var_names[x as usize].clone()
        } else {
            format!("<{}>", x)
        }
    }

    /// Declare which polarity the decision heuristic should use for a variable. Requires mode 'polarity_user'.
    pub fn set_polarity(&mut self, v: Var, b: bool) {
        self.polarity[v as usize] = b;
    }

    /// Declare if a variable should be eligible for selection in the decision heuristic.
    pub fn set_decision_var(&mut self, v: Var, b: bool) {
        if b && !self.decision[v as usize] {
            self.stats[CoreStats::DecVars as usize] += 1;
        } else if !b && self.decision[v as usize] {
            self.stats[CoreStats::DecVars as usize] -= 1;
        }

        self.decision[v as usize] = b;
        self.insert_var_order(v);
    }

    pub fn set_conf_budget(&mut self, x: i64) {
        self.conflict_budget = self.conflicts as i64 + x;
    }

    pub fn set_prop_budget(&mut self, x: i64) {
        self.propagation_budget = self.propagations as i64 + x;
    }

    /// Trigger a (potentially asynchronous) interruption of the solver.
    pub fn interrupt(&mut self) {
        self.asynch_interrupt = true;
    }

    /// Clear interrupt indicator flag.
    pub fn clear_interrupt(&mut self) {
        self.asynch_interrupt = false;
    }

    pub fn budget_off(&mut self) {
        self.conflict_budget = -1;
        self.propagation_budget = -1;
    }

    fn within_budget(&self) -> bool {
        !self.asynch_interrupt
            && (self.conflict_budget < 0 || self.conflicts < self.conflict_budget as u64)
            && (self.propagation_budget < 0 || self.propagations < self.propagation_budget as u64)
    }

    /// Search without assumptions.
    ///
    /// NOTE: the C++ `solve()` returns `bool` and `solveLimited` returns `lbool`; the Rust port
    /// returns `LBool` here because the existing callers expect it.
    pub fn solve(&mut self) -> LBool {
        self.budget_off();
        self.assumptions.clear();
        self.solve_()
    }

    /// Search for a model that respects a given set of assumptions (With resource constraints).
    pub fn solve_limited(&mut self, assumps: &[Lit]) -> LBool {
        self.assumptions.clear();
        self.assumptions.extend_from_slice(assumps);
        self.solve_()
    }

    /// FALSE means solver is in a conflicting state
    pub fn okay(&self) -> bool {
        self.ok
    }

    pub fn register_undo(&mut self, v: Var, constr: ConstraintIdx) {
        self.undo_lists[v as usize].push(constr);
    }

    /// Counterpart of `Constraint::num_pending_propagation()` (the counter is maintained by the
    /// solver in this port; see `num_pending_propagation`).
    pub fn num_pending(&self, ci: ConstraintIdx) -> i32 {
        debug_assert!(self.num_pending_propagation[ci] >= 0);
        self.num_pending_propagation[ci]
    }

    // Statistics accessors (used by the cspuz_core backend):

    pub fn num_decisions(&self) -> u64 {
        self.decisions
    }

    pub fn num_propagations(&self) -> u64 {
        self.propagations
    }

    pub fn num_conflicts(&self) -> u64 {
        self.conflicts
    }

    //=============================================================================================
    // Debug etc:

    pub fn print_lit(&self, l: Lit) {
        print!(
            "{}{}:{}",
            if l.is_neg() { "-" } else { "" },
            l.var() + 1,
            match self.value_of(l) {
                LBool::True => '1',
                LBool::False => '0',
                LBool::Undef => 'X',
            }
        );
    }

    pub fn print_clause(&self, cr: CRef) {
        for i in 0..self.ca.clause_size(cr) {
            self.print_lit(self.ca.lit(cr, i));
            print!(" ");
        }
    }

    fn is_selector(&self, v: Var) -> bool {
        self.incremental && (v as i32) > self.nb_vars_initial_formula
    }

    //=============================================================================================
    // Static helpers:

    /// Returns a random float 0 <= x < 1. Seed must never be 0.
    fn drand(seed: &mut f64) -> f64 {
        *seed *= 1389796.0;
        let q = (*seed / 2147483647.0) as i32;
        *seed -= q as f64 * 2147483647.0;
        *seed / 2147483647.0
    }

    /// Returns a random integer 0 <= x < size. Seed must never be 0.
    fn irand(seed: &mut f64, size: i32) -> i32 {
        (Self::drand(seed) * size as f64) as i32
    }

    //=============================================================================================
    // reduceDB comparators (`reduceDBAct_lt` / `reduceDB_lt` in Solver.h):

    fn reduce_db_act_lt(ca: &ClauseAllocator, x: CRef, y: CRef) -> bool {
        // Main criteria... Like in MiniSat we keep all binary clauses
        if ca.clause_size(x) > 2 && ca.clause_size(y) == 2 {
            return true;
        }

        if ca.clause_size(y) > 2 && ca.clause_size(x) == 2 {
            return false;
        }
        if ca.clause_size(x) == 2 && ca.clause_size(y) == 2 {
            return false;
        }

        ca.activity(x) < ca.activity(y)
    }

    fn reduce_db_lt(ca: &ClauseAllocator, x: CRef, y: CRef) -> bool {
        // Main criteria... Like in MiniSat we keep all binary clauses
        if ca.clause_size(x) > 2 && ca.clause_size(y) == 2 {
            return true;
        }

        if ca.clause_size(y) > 2 && ca.clause_size(x) == 2 {
            return false;
        }
        if ca.clause_size(x) == 2 && ca.clause_size(y) == 2 {
            return false;
        }

        // Second one  based on literal block distance
        if ca.lbd(x) > ca.lbd(y) {
            return true;
        }
        if ca.lbd(x) < ca.lbd(y) {
            return false;
        }

        // Finally we can use old activity or size, we choose the last one
        ca.activity(x) < ca.activity(y)
    }
}

impl Default for Solver {
    fn default() -> Self {
        Solver::new()
    }
}
