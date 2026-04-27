use crate::types::Lit;

pub type ClauseIdx = u32;
pub const CLAUSE_UNDEF: ClauseIdx = u32::MAX;

#[derive(Clone, Debug)]
pub struct ClauseHeader {
    pub lbd: u32,
    pub learnt: bool,
    pub mark: u8,
    pub deleted: bool,
}

#[derive(Clone, Debug)]
pub struct Clause {
    pub header: ClauseHeader,
    pub lits: Vec<Lit>,
    pub activity: f32,
}

impl Clause {
    pub fn new(lits: Vec<Lit>, learnt: bool) -> Self {
        Clause {
            header: ClauseHeader {
                lbd: 0,
                learnt,
                mark: 0,
                deleted: false,
            },
            lits,
            activity: 0.0,
        }
    }
}

pub struct ClauseDb {
    pub clauses: Vec<Clause>,
}

impl ClauseDb {
    pub fn new() -> Self {
        ClauseDb { clauses: Vec::new() }
    }

    pub fn alloc(&mut self, lits: Vec<Lit>, learnt: bool) -> ClauseIdx {
        let idx = self.clauses.len() as ClauseIdx;
        self.clauses.push(Clause::new(lits, learnt));
        idx
    }

    pub fn get(&self, idx: ClauseIdx) -> &Clause {
        &self.clauses[idx as usize]
    }

    pub fn get_mut(&mut self, idx: ClauseIdx) -> &mut Clause {
        &mut self.clauses[idx as usize]
    }
}

impl Default for ClauseDb {
    fn default() -> Self {
        Self::new()
    }
}
