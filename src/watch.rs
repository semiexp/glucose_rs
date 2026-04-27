use crate::types::Lit;
use crate::clause::ClauseIdx;

#[derive(Clone, Copy, Debug)]
pub struct Watcher {
    pub cref: ClauseIdx,
    /// A "blocker" literal from the same clause used to short-circuit the watch check:
    /// if `blocker` is already TRUE we can skip inspecting the clause entirely.
    pub blocker: Lit,
}

/// Per-literal watch lists for the two-watched-literals BCP scheme.
///
/// `watches[lit]` contains all clauses that are watching `lit`.  A clause with
/// watches `w0` and `w1` is stored in both `watches[w0]` and `watches[w1]`.  When
/// `lit` is assigned FALSE the propagation loop visits `watches[lit]` to find unit
/// consequences or conflicts.
///
/// Corresponds to `OccLists<Lit, vec<Watcher>, WatcherDeleted>` in C++ Glucose
/// (`core/Solver.h`).
pub struct WatchList {
    watches: Vec<Vec<Watcher>>,
}

impl WatchList {
    pub fn new(num_lits: usize) -> Self {
        WatchList {
            watches: vec![Vec::new(); num_lits],
        }
    }

    pub fn add(&mut self, lit: Lit, w: Watcher) {
        self.watches[lit.0 as usize].push(w);
    }

    pub fn get(&self, lit: Lit) -> &[Watcher] {
        &self.watches[lit.0 as usize]
    }

    pub fn get_mut(&mut self, lit: Lit) -> &mut Vec<Watcher> {
        &mut self.watches[lit.0 as usize]
    }

    pub fn grow(&mut self, num_lits: usize) {
        while self.watches.len() < num_lits {
            self.watches.push(Vec::new());
        }
    }
}
