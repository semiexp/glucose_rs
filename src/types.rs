//! Port of `core/SolverTypes.h`: variables, literals, lifted booleans, clauses,
//! the clause allocator and occurrence lists.

//=================================================================================================
// Variables, literals, lifted booleans, clauses:

// NOTE! Variables are just integers. No abstraction here. They should be chosen from 0..N,
// so that they can be used as array indices.

pub type Var = u32;

/// A literal. The internal representation is `var + var + sign` (like the C++ `Lit`),
/// where `sign == true` means the negative literal.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Lit(pub u32);

impl Lit {
    /// Counterpart of `lit_Undef` (`{-2}` in C++; the same bit pattern as `u32`).
    pub const UNDEF: Lit = Lit(u32::MAX - 1);
    /// Counterpart of `lit_Error` (`{-1}` in C++).
    pub const ERROR: Lit = Lit(u32::MAX);

    /// Counterpart of `mkLit(var, sign)`.
    pub fn new(var: Var, sign: bool) -> Lit {
        Lit(var + var + sign as u32)
    }

    /// Counterpart of `var(p)`.
    pub fn var(self) -> Var {
        self.0 >> 1
    }

    /// Counterpart of `sign(p)`. `true` for the negative literal.
    pub fn is_neg(self) -> bool {
        (self.0 & 1) != 0
    }
}

impl std::ops::Not for Lit {
    type Output = Lit;

    fn not(self) -> Lit {
        Lit(self.0 ^ 1)
    }
}

//=================================================================================================
// Lifted booleans:

/// Counterpart of `lbool` (`l_True` / `l_False` / `l_Undef`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LBool {
    True,
    False,
    Undef,
}

impl LBool {
    /// Counterpart of `lbool(bool)`.
    pub fn from_bool(x: bool) -> LBool {
        if x {
            LBool::True
        } else {
            LBool::False
        }
    }

    /// Counterpart of `lbool operator ^ (bool)`.
    pub fn xor(self, b: bool) -> LBool {
        match (self, b) {
            (LBool::True, true) => LBool::False,
            (LBool::False, true) => LBool::True,
            (x, _) => x,
        }
    }
}

//=================================================================================================
// Clause -- a simple class for representing a clause:
//
// In the C++ implementation, a clause is laid out in a `RegionAllocator<uint32_t>` as a packed
// header followed by the literals and optional extra fields, and is accessed through `CRef`
// (an index into the region).  The Rust port keeps exactly the same layout, but the accessors
// (`Clause` methods in C++) are provided as methods of `ClauseAllocator` taking a `CRef`, to
// avoid holding long-lived references into the region.
//
// Layout of a clause at `cr`:
//   memory[cr]     : header (bitfields; see below)
//   memory[cr + 1] : size
//   memory[cr + 2 .. cr + 2 + size] : literals
//   memory[cr + 2 + size .. ]       : extra fields (activity / abstraction, importedFrom)

pub type CRef = u32;
pub const CREF_UNDEF: CRef = u32::MAX;

pub const BITS_LBD: u32 = 20;

// Header bitfields (same fields as the C++ `Clause::header`):
//   mark       : 2 bits  (bits 0-1)
//   learnt     : 1 bit   (bit 2)
//   canbedel   : 1 bit   (bit 3)
//   extra_size : 2 bits  (bits 4-5)
//   seen       : 1 bit   (bit 6)
//   reloced    : 1 bit   (bit 7)
//   exported   : 2 bits  (bits 8-9)
//   oneWatched : 1 bit   (bit 10)
//   lbd        : 20 bits (bits 11-30)
const SHIFT_MARK: u32 = 0;
const SHIFT_LEARNT: u32 = 2;
const SHIFT_CANBEDEL: u32 = 3;
const SHIFT_EXTRA_SIZE: u32 = 4;
const SHIFT_SEEN: u32 = 6;
const SHIFT_RELOCED: u32 = 7;
const SHIFT_EXPORTED: u32 = 8;
const SHIFT_ONE_WATCHED: u32 = 10;
const SHIFT_LBD: u32 = 11;

pub struct ClauseAllocator {
    memory: Vec<u32>,
    wasted: usize,
    pub extra_clause_field: bool,
}

impl ClauseAllocator {
    fn clause_word32_size(size: usize, extra_size: usize) -> usize {
        2 + size + extra_size
    }

    pub fn with_capacity(start_cap: usize) -> ClauseAllocator {
        ClauseAllocator {
            memory: Vec::with_capacity(start_cap),
            wasted: 0,
            extra_clause_field: false,
        }
    }

    pub fn new() -> ClauseAllocator {
        ClauseAllocator {
            memory: Vec::new(),
            wasted: 0,
            extra_clause_field: false,
        }
    }

    /// Size of the allocated region (in 32-bit words). Counterpart of `RegionAllocator::size()`.
    pub fn size(&self) -> usize {
        self.memory.len()
    }

    /// Counterpart of `RegionAllocator::wasted()`.
    pub fn wasted(&self) -> usize {
        self.wasted
    }

    /// Counterpart of `ClauseAllocator::alloc` (with `imported = false`).
    pub fn alloc(&mut self, ps: &[Lit], learnt: bool) -> CRef {
        self.alloc_(ps, learnt, false)
    }

    fn alloc_(&mut self, ps: &[Lit], learnt: bool, imported: bool) -> CRef {
        let use_extra = learnt | self.extra_clause_field;
        let extra_size = if imported {
            3
        } else if use_extra {
            1
        } else {
            0
        };
        let cid = self.memory.len() as CRef;
        self.memory
            .resize(self.memory.len() + Self::clause_word32_size(ps.len(), extra_size), 0);

        // Header: mark = 0, learnt, extra_size, reloced = 0, lbd = 0, canbedel = 1,
        // exported = 0, oneWatched = 0, seen = 0.
        self.memory[cid as usize] = ((learnt as u32) << SHIFT_LEARNT)
            | ((extra_size as u32) << SHIFT_EXTRA_SIZE)
            | (1 << SHIFT_CANBEDEL);
        self.memory[cid as usize + 1] = ps.len() as u32;
        for (i, &p) in ps.iter().enumerate() {
            self.memory[cid as usize + 2 + i] = p.0;
        }

        if extra_size > 0 {
            if learnt {
                self.memory[cid as usize + 2 + ps.len()] = 0f32.to_bits();
            } else {
                self.calc_abstraction(cid);
            }
            if extra_size > 1 {
                self.memory[cid as usize + 2 + ps.len() + 1] = 0; // learntFrom
            }
        }

        cid
    }

    /// Counterpart of `ClauseAllocator::free`.
    pub fn free(&mut self, cr: CRef) {
        let size = self.clause_size(cr);
        let extra = self.has_extra(cr) as usize;
        self.wasted += Self::clause_word32_size(size, extra);
    }

    /// Counterpart of `ClauseAllocator::reloc`.
    pub fn reloc(&mut self, cr: &mut CRef, to: &mut ClauseAllocator) {
        if self.reloced(*cr) {
            *cr = self.relocation(*cr);
            return;
        }

        let lits: Vec<Lit> = (0..self.clause_size(*cr)).map(|i| self.lit(*cr, i)).collect();
        let new_cr = to.alloc_(&lits, self.learnt(*cr), self.was_imported(*cr));

        // Copy extra data-fields:
        to.set_mark(new_cr, self.mark(*cr));
        if to.learnt(new_cr) {
            to.set_activity(new_cr, self.activity(*cr));
            to.set_lbd(new_cr, self.lbd(*cr));
            to.set_exported(new_cr, self.get_exported(*cr));
            to.set_one_watched(new_cr, self.get_one_watched(*cr));
            to.set_can_be_del(new_cr, self.can_be_del(*cr));
        } else {
            to.set_seen(new_cr, self.get_seen(*cr));
            if to.has_extra(new_cr) {
                to.calc_abstraction(new_cr);
            }
        }

        self.relocate(*cr, new_cr);
        *cr = new_cr;
    }

    // ---- Clause accessors (counterparts of `Clause` methods) ----

    fn header(&self, cr: CRef) -> u32 {
        self.memory[cr as usize]
    }

    fn set_header_bits(&mut self, cr: CRef, shift: u32, width: u32, value: u32) {
        let mask = ((1u32 << width) - 1) << shift;
        let h = self.memory[cr as usize];
        self.memory[cr as usize] = (h & !mask) | ((value << shift) & mask);
    }

    pub fn clause_size(&self, cr: CRef) -> usize {
        self.memory[cr as usize + 1] as usize
    }

    pub fn lit(&self, cr: CRef, i: usize) -> Lit {
        Lit(self.memory[cr as usize + 2 + i])
    }

    pub fn set_lit(&mut self, cr: CRef, i: usize, p: Lit) {
        self.memory[cr as usize + 2 + i] = p.0;
    }

    pub fn learnt(&self, cr: CRef) -> bool {
        (self.header(cr) >> SHIFT_LEARNT) & 1 != 0
    }

    pub fn nolearnt(&mut self, cr: CRef) {
        self.set_header_bits(cr, SHIFT_LEARNT, 1, 0);
    }

    pub fn has_extra(&self, cr: CRef) -> bool {
        (self.header(cr) >> SHIFT_EXTRA_SIZE) & 3 > 0
    }

    pub fn mark(&self, cr: CRef) -> u32 {
        (self.header(cr) >> SHIFT_MARK) & 3
    }

    pub fn set_mark(&mut self, cr: CRef, m: u32) {
        self.set_header_bits(cr, SHIFT_MARK, 2, m);
    }

    pub fn reloced(&self, cr: CRef) -> bool {
        (self.header(cr) >> SHIFT_RELOCED) & 1 != 0
    }

    pub fn relocation(&self, cr: CRef) -> CRef {
        self.memory[cr as usize + 2]
    }

    pub fn relocate(&mut self, cr: CRef, c: CRef) {
        self.set_header_bits(cr, SHIFT_RELOCED, 1, 1);
        self.memory[cr as usize + 2] = c;
    }

    pub fn activity(&self, cr: CRef) -> f32 {
        debug_assert!(self.has_extra(cr));
        let size = self.clause_size(cr);
        f32::from_bits(self.memory[cr as usize + 2 + size])
    }

    pub fn set_activity(&mut self, cr: CRef, act: f32) {
        debug_assert!(self.has_extra(cr));
        let size = self.clause_size(cr);
        self.memory[cr as usize + 2 + size] = act.to_bits();
    }

    pub fn abstraction(&self, cr: CRef) -> u32 {
        debug_assert!(self.has_extra(cr));
        let size = self.clause_size(cr);
        self.memory[cr as usize + 2 + size]
    }

    pub fn calc_abstraction(&mut self, cr: CRef) {
        debug_assert!(self.has_extra(cr));
        let size = self.clause_size(cr);
        let mut abstraction: u32 = 0;
        for i in 0..size {
            abstraction |= 1 << (self.lit(cr, i).var() & 31);
        }
        self.memory[cr as usize + 2 + size] = abstraction;
    }

    pub fn was_imported(&self, cr: CRef) -> bool {
        (self.header(cr) >> SHIFT_EXTRA_SIZE) & 3 > 1
    }

    pub fn set_lbd(&mut self, cr: CRef, i: u32) {
        self.set_header_bits(cr, SHIFT_LBD, BITS_LBD, i);
    }

    pub fn lbd(&self, cr: CRef) -> u32 {
        (self.header(cr) >> SHIFT_LBD) & ((1 << BITS_LBD) - 1)
    }

    pub fn set_can_be_del(&mut self, cr: CRef, b: bool) {
        self.set_header_bits(cr, SHIFT_CANBEDEL, 1, b as u32);
    }

    pub fn can_be_del(&self, cr: CRef) -> bool {
        (self.header(cr) >> SHIFT_CANBEDEL) & 1 != 0
    }

    pub fn set_seen(&mut self, cr: CRef, b: bool) {
        self.set_header_bits(cr, SHIFT_SEEN, 1, b as u32);
    }

    pub fn get_seen(&self, cr: CRef) -> bool {
        (self.header(cr) >> SHIFT_SEEN) & 1 != 0
    }

    pub fn set_exported(&mut self, cr: CRef, b: u32) {
        self.set_header_bits(cr, SHIFT_EXPORTED, 2, b);
    }

    pub fn get_exported(&self, cr: CRef) -> u32 {
        (self.header(cr) >> SHIFT_EXPORTED) & 3
    }

    pub fn set_one_watched(&mut self, cr: CRef, b: bool) {
        self.set_header_bits(cr, SHIFT_ONE_WATCHED, 1, b as u32);
    }

    pub fn get_one_watched(&self, cr: CRef) -> bool {
        (self.header(cr) >> SHIFT_ONE_WATCHED) & 1 != 0
    }
}

//=================================================================================================
// OccLists -- a class for maintaining occurence lists with lazy deletion:
//
// The C++ version is parameterized by a `Deleted` predicate object; the Rust port takes the
// predicate as a closure argument of `clean_all` / `clean` instead.

pub struct OccLists<T> {
    occs: Vec<Vec<T>>,
    dirty: Vec<bool>,
    dirties: Vec<Lit>,
}

impl<T> OccLists<T> {
    pub fn new() -> OccLists<T> {
        OccLists {
            occs: Vec::new(),
            dirty: Vec::new(),
            dirties: Vec::new(),
        }
    }

    pub fn init(&mut self, idx: Lit) {
        while self.occs.len() < idx.0 as usize + 1 {
            self.occs.push(Vec::new());
        }
        while self.dirty.len() < idx.0 as usize + 1 {
            self.dirty.push(false);
        }
    }

    /// Counterpart of `operator[]` (shared access).
    pub fn occ(&self, idx: Lit) -> &Vec<T> {
        &self.occs[idx.0 as usize]
    }

    /// Counterpart of `operator[]` (mutable access).
    pub fn occ_mut(&mut self, idx: Lit) -> &mut Vec<T> {
        &mut self.occs[idx.0 as usize]
    }

    /// Takes out the occurrence list of `idx`, leaving an empty one.  This is a helper for the
    /// Rust port: the C++ code holds a reference to `watches[p]` while pushing to other lists,
    /// which is expressed in Rust by temporarily moving the list out.
    pub fn take(&mut self, idx: Lit) -> Vec<T> {
        std::mem::take(&mut self.occs[idx.0 as usize])
    }

    /// Puts back the list taken by `take`.
    pub fn put(&mut self, idx: Lit, v: Vec<T>) {
        self.occs[idx.0 as usize] = v;
    }

    pub fn clean_all(&mut self, deleted: impl Fn(&T) -> bool) {
        for i in 0..self.dirties.len() {
            // Dirties may contain duplicates so check here if a variable is already cleaned:
            let idx = self.dirties[i];
            if self.dirty[idx.0 as usize] {
                self.clean(idx, &deleted);
            }
        }
        self.dirties.clear();
    }

    pub fn clean(&mut self, idx: Lit, deleted: &impl Fn(&T) -> bool) {
        let vec = &mut self.occs[idx.0 as usize];
        vec.retain(|x| !deleted(x));
        self.dirty[idx.0 as usize] = false;
    }

    pub fn smudge(&mut self, idx: Lit) {
        if !self.dirty[idx.0 as usize] {
            self.dirty[idx.0 as usize] = true;
            self.dirties.push(idx);
        }
    }

    pub fn clear(&mut self) {
        self.occs.clear();
        self.dirty.clear();
        self.dirties.clear();
    }
}
