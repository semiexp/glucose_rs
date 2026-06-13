//! Port of `core/BoundedQueue.h`.
//!
//! The C++ `bqueue<T>` is only instantiated with `unsigned int` in the core solver, so the Rust
//! port uses `u32` elements (with a `u64` running sum) instead of being generic.

pub struct BoundedQueue {
    elems: Vec<u32>,
    first: usize,
    last: usize,
    sumofqueue: u64,
    maxsize: usize,
    queuesize: usize, // Number of current elements (must be < maxsize !)
    exp_computed: bool,
    exp: f64,
    value: f64,
}

impl BoundedQueue {
    pub fn new() -> BoundedQueue {
        BoundedQueue {
            elems: Vec::new(),
            first: 0,
            last: 0,
            sumofqueue: 0,
            maxsize: 0,
            queuesize: 0,
            exp_computed: false,
            exp: 0.0,
            value: 0.0,
        }
    }

    /// Init size of bounded size queue
    pub fn init_size(&mut self, size: usize) {
        self.grow_to(size);
        self.exp = 2.0 / (size + 1) as f64;
    }

    pub fn push(&mut self, x: u32) {
        self.exp_computed = false;
        if self.queuesize == self.maxsize {
            // The queue is full, next value to enter will replace oldest one
            debug_assert!(self.last == self.first);
            self.sumofqueue -= self.elems[self.last] as u64;
            self.last += 1;
            if self.last == self.maxsize {
                self.last = 0;
            }
        } else {
            self.queuesize += 1;
        }
        self.sumofqueue += x as u64;
        self.elems[self.first] = x;
        self.first += 1;
        if self.first == self.maxsize {
            self.first = 0;
            self.last = 0;
        }
    }

    pub fn peek(&self) -> u32 {
        debug_assert!(self.queuesize > 0);
        self.elems[self.last]
    }

    pub fn pop(&mut self) {
        self.sumofqueue -= self.elems[self.last] as u64;
        self.queuesize -= 1;
        self.last += 1;
        if self.last == self.maxsize {
            self.last = 0;
        }
    }

    pub fn get_sum(&self) -> u64 {
        self.sumofqueue
    }

    pub fn get_avg(&self) -> u32 {
        (self.sumofqueue / self.queuesize as u64) as u32
    }

    pub fn max_size(&self) -> usize {
        self.maxsize
    }

    pub fn get_avg_double(&self) -> f64 {
        let mut tmp = 0.0;
        for &e in &self.elems {
            tmp += e as f64;
        }
        tmp / self.elems.len() as f64
    }

    pub fn is_valid(&self) -> bool {
        self.queuesize == self.maxsize
    }

    pub fn grow_to(&mut self, size: usize) {
        self.elems.resize(size, 0);
        self.first = 0;
        self.maxsize = size;
        self.queuesize = 0;
        self.last = 0;
        for e in self.elems.iter_mut() {
            *e = 0;
        }
    }

    pub fn get_avg_exp(&mut self) -> f64 {
        if self.exp_computed {
            return self.value;
        }
        let mut a = self.exp;
        self.value = self.elems[self.first] as f64;
        for i in self.first..self.maxsize {
            self.value += a * self.elems[i] as f64;
            a *= self.exp;
        }
        for i in 0..self.last {
            self.value += a * self.elems[i] as f64;
            a *= self.exp;
        }
        self.value = self.value * (1.0 - self.exp) / (1.0 - a);
        self.exp_computed = true;
        self.value
    }

    /// to be called after restarts... Discard the queue
    pub fn fast_clear(&mut self) {
        self.first = 0;
        self.last = 0;
        self.queuesize = 0;
        self.sumofqueue = 0;
    }

    pub fn size(&self) -> usize {
        self.queuesize
    }

    pub fn clear(&mut self) {
        self.elems.clear();
        self.first = 0;
        self.maxsize = 0;
        self.queuesize = 0;
        self.sumofqueue = 0;
    }
}
