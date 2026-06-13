//! Port of `mtl/Heap.h`: a heap implementation with support for decrease/increase key.
//!
//! The C++ version stores the comparator (`Comp`) as a member; since the comparator used by the
//! solver (`VarOrderLt`) borrows the activity array, the Rust port takes the comparator as a
//! closure argument of each operation instead.

use crate::types::Var;

pub struct Heap {
    heap: Vec<Var>,    // Heap of variables
    indices: Vec<i32>, // Each variable's position (index) in the Heap
}

impl Heap {
    // Index "traversal" functions
    fn left(i: usize) -> usize {
        i * 2 + 1
    }
    fn right(i: usize) -> usize {
        (i + 1) * 2
    }
    fn parent(i: usize) -> usize {
        (i - 1) >> 1
    }

    fn percolate_up(&mut self, mut i: usize, lt: &impl Fn(Var, Var) -> bool) {
        let x = self.heap[i];

        while i != 0 && lt(x, self.heap[Self::parent(i)]) {
            let p = Self::parent(i);
            self.heap[i] = self.heap[p];
            self.indices[self.heap[p] as usize] = i as i32;
            i = p;
        }
        self.heap[i] = x;
        self.indices[x as usize] = i as i32;
    }

    fn percolate_down(&mut self, mut i: usize, lt: &impl Fn(Var, Var) -> bool) {
        let x = self.heap[i];
        while Self::left(i) < self.heap.len() {
            let child = if Self::right(i) < self.heap.len()
                && lt(self.heap[Self::right(i)], self.heap[Self::left(i)])
            {
                Self::right(i)
            } else {
                Self::left(i)
            };
            if !lt(self.heap[child], x) {
                break;
            }
            self.heap[i] = self.heap[child];
            self.indices[self.heap[i] as usize] = i as i32;
            i = child;
        }
        self.heap[i] = x;
        self.indices[x as usize] = i as i32;
    }

    pub fn new() -> Heap {
        Heap {
            heap: Vec::new(),
            indices: Vec::new(),
        }
    }

    pub fn size(&self) -> usize {
        self.heap.len()
    }

    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    pub fn in_heap(&self, n: Var) -> bool {
        (n as usize) < self.indices.len() && self.indices[n as usize] >= 0
    }

    pub fn decrease(&mut self, n: Var, lt: impl Fn(Var, Var) -> bool) {
        debug_assert!(self.in_heap(n));
        self.percolate_up(self.indices[n as usize] as usize, &lt);
    }

    pub fn increase(&mut self, n: Var, lt: impl Fn(Var, Var) -> bool) {
        debug_assert!(self.in_heap(n));
        self.percolate_down(self.indices[n as usize] as usize, &lt);
    }

    // Safe variant of insert/decrease/increase:
    pub fn update(&mut self, n: Var, lt: impl Fn(Var, Var) -> bool) {
        if !self.in_heap(n) {
            self.insert(n, lt);
        } else {
            self.percolate_up(self.indices[n as usize] as usize, &lt);
            self.percolate_down(self.indices[n as usize] as usize, &lt);
        }
    }

    pub fn insert(&mut self, n: Var, lt: impl Fn(Var, Var) -> bool) {
        while self.indices.len() < n as usize + 1 {
            self.indices.push(-1);
        }
        debug_assert!(!self.in_heap(n));

        self.indices[n as usize] = self.heap.len() as i32;
        self.heap.push(n);
        self.percolate_up(self.indices[n as usize] as usize, &lt);
    }

    pub fn remove_min(&mut self, lt: impl Fn(Var, Var) -> bool) -> Var {
        let x = self.heap[0];
        let last = *self.heap.last().unwrap();
        self.heap[0] = last;
        self.indices[last as usize] = 0;
        self.indices[x as usize] = -1;
        self.heap.pop();
        if self.heap.len() > 1 {
            self.percolate_down(0, &lt);
        }
        x
    }

    // Rebuild the heap from scratch, using the elements in 'ns':
    pub fn build(&mut self, ns: &[Var], lt: impl Fn(Var, Var) -> bool) {
        for i in 0..self.heap.len() {
            self.indices[self.heap[i] as usize] = -1;
        }
        self.heap.clear();

        for (i, &n) in ns.iter().enumerate() {
            while self.indices.len() < n as usize + 1 {
                self.indices.push(-1);
            }
            self.indices[n as usize] = i as i32;
            self.heap.push(n);
        }

        for i in (0..self.heap.len() / 2).rev() {
            self.percolate_down(i, &lt);
        }
    }

    pub fn clear(&mut self) {
        for i in 0..self.heap.len() {
            self.indices[self.heap[i] as usize] = -1;
        }
        self.heap.clear();
    }
}

impl std::ops::Index<usize> for Heap {
    type Output = Var;

    fn index(&self, index: usize) -> &Var {
        debug_assert!(index < self.heap.len());
        &self.heap[index]
    }
}
