use crate::types::Lit;
use crate::clause::ClauseIdx;

#[derive(Clone, Copy, Debug)]
pub struct Watcher {
    pub cref: ClauseIdx,
    pub blocker: Lit,
}

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
