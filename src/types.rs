use std::ops::Not;

pub type Var = u32;
pub const VAR_UNDEF: Var = u32::MAX;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Lit(pub u32);

impl Lit {
    pub fn new(var: Var, neg: bool) -> Lit {
        Lit(var * 2 + neg as u32)
    }

    pub fn var(self) -> Var {
        self.0 >> 1
    }

    pub fn is_neg(self) -> bool {
        (self.0 & 1) != 0
    }

    pub const UNDEF: Lit = Lit(u32::MAX);
}

impl Not for Lit {
    type Output = Lit;
    fn not(self) -> Lit {
        Lit(self.0 ^ 1)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LBool {
    True,
    False,
    Undef,
}

impl From<bool> for LBool {
    fn from(b: bool) -> LBool {
        if b {
            LBool::True
        } else {
            LBool::False
        }
    }
}

impl LBool {
    pub fn xor(self, b: bool) -> LBool {
        if b {
            match self {
                LBool::True => LBool::False,
                LBool::False => LBool::True,
                LBool::Undef => LBool::Undef,
            }
        } else {
            self
        }
    }
}
