extern crate sat;

use std::cell::RefCell;
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};

use sat::{Instance, Literal, Assignment};
use sat::solver::Solver;

pub fn init() {
    NdMachine::with_opt(|machine| {
        *machine = Some(NdMachine::new());
    });
}

pub fn solve_by<T: Solver>(solver: &T) -> bool {
    NdMachine::with(|machine| {
        let assignment = solver.solve(&machine.instance);
        machine.assignment = assignment;
        machine.assignment.is_some()
    })
}

pub fn ndassert(b: ndbool) {
    NdMachine::with(|machine| {
        machine.instance.assert_any(&[b.0]);
    })
}

pub fn ndassert_eq<T: NdEq<U>, U>(lhs: T, rhs: U) {
    ndassert(lhs.ndeq(&rhs));
}

pub fn ndassert_ne<T: NdEq<U>, U>(lhs: T, rhs: U) {
    ndassert(lhs.ndne(&rhs));
}


pub struct NdMachine {
    instance: Instance,
    assignment: Option<Assignment>,
}

impl NdMachine {
    fn new() -> Self {
        NdMachine {
            instance: Instance::new(),
            assignment: None,
        }
    }
    fn with_opt<R, F: FnOnce(&mut Option<Self>) -> R>(f: F) -> R {
        thread_local! {
            static MACHINE : RefCell<Option<NdMachine>> = RefCell::new(None);
        }
        MACHINE.with(|machine| {
            f(&mut machine.borrow_mut())
        })
    }
    fn with<R, F: FnOnce(&mut Self) -> R>(f: F) -> R {
        Self::with_opt(|this_opt| {
            if let Some(ref mut this) = *this_opt {
                f(this)
            } else {
                panic!("ndmachine::init() should be called first")
            }
        })
    }
}

#[allow(non_camel_case_types)]
#[derive(Copy, Clone)]
pub struct ndbool(Literal);

impl ndbool {
    pub fn t() -> Self {
        NdMachine::with(|machine| {
            let l = machine.instance.fresh_var();
            machine.instance.assert_any(&[l]);
            machine.assignment = None;
            ndbool(l)
        })
    }
    pub fn f() -> Self {
        NdMachine::with(|machine| {
            let l = machine.instance.fresh_var();
            machine.instance.assert_any(&[!l]);
            machine.assignment = None;
            ndbool(l)
        })
    }
    pub fn fresh() -> Self {
        NdMachine::with(|machine| {
            ndbool(machine.instance.fresh_var())
        })
    }
    pub fn value(self) -> bool {
        NdMachine::with(|machine| {
            let assignment = machine.assignment.as_ref().expect("No solution!");
            assignment.get(self.0)
        })
    }
}

impl Not for ndbool {
    type Output = ndbool;
    fn not(self) -> ndbool {
        ndbool(!self.0)
    }
}

impl BitAnd for ndbool {
    type Output = ndbool;
    fn bitand(self, other: ndbool) -> ndbool {
        NdMachine::with(|machine| {
            let l = machine.instance.fresh_var();
            machine.instance.assert_any(&[!self.0, !other.0, l]);
            machine.instance.assert_any(&[self.0, !l]);
            machine.instance.assert_any(&[other.0, !l]);
            machine.assignment = None;
            ndbool(l)
        })
    }
}

impl BitAndAssign for ndbool {
    fn bitand_assign(&mut self, rhs: ndbool) {
        *self = *self & rhs;
    }
}

impl BitOr for ndbool {
    type Output = ndbool;
    fn bitor(self, other: ndbool) -> ndbool {
        NdMachine::with(|machine| {
            let l = machine.instance.fresh_var();
            machine.instance.assert_any(&[self.0, other.0, !l]);
            machine.instance.assert_any(&[!self.0, l]);
            machine.instance.assert_any(&[!other.0, l]);
            machine.assignment = None;
            ndbool(l)
        })
    }
}

impl BitOrAssign for ndbool {
    fn bitor_assign(&mut self, rhs: ndbool) {
        *self = *self | rhs;
    }
}

impl BitXor for ndbool {
    type Output = ndbool;
    fn bitxor(self, other: ndbool) -> ndbool {
        (self | other) & !(self & other)
    }
}

impl BitXorAssign for ndbool {
    fn bitxor_assign(&mut self, rhs: ndbool) {
        *self = *self ^ rhs;
    }
}

impl NdEq for ndbool {
    fn ndeq(&self, rhs: &ndbool) -> ndbool {
        (*self | !*rhs) & (!*self | *rhs)
    }
}


pub trait NdEq<Rhs : ?Sized = Self> {
    fn ndeq(&self, rhs: &Rhs) -> ndbool;
    fn ndne(&self, rhs: &Rhs) -> ndbool {
        !self.ndeq(rhs)
    }
}


#[cfg(test)]
mod tests {
    use std::process::Command;

    use super::*;

    fn solve() -> bool {
        solve_by(&sat::solver::Dimacs::new(|| Command::new("minisat")))
    }

    #[test]
    fn test_solve_no_constraint() {
        init();
        assert!(solve());
    }

    #[test]
    fn test_and() {
        init();
        let b0 = ndbool::fresh();
        let b1 = ndbool::fresh();
        ndassert(b0 & b1);
        assert!(solve());
        assert!(b0.value() && b1.value());
    }

    #[test]
    fn test_or() {
        init();
        let b0 = ndbool::fresh();
        let b1 = ndbool::fresh();
        ndassert(b0 | b1);
        assert!(solve());
        assert!(b0.value() || b1.value());
    }

    #[test]
    fn test_xor() {
        init();
        let b0 = ndbool::fresh();
        let b1 = ndbool::fresh();
        ndassert(b0 ^ b1);
        assert!(solve());
        assert!(b0.value() ^ b1.value());
    }

    #[test]
    fn test_and_comm() {
        init();
        let b0 = ndbool::fresh();
        let b1 = ndbool::fresh();
        ndassert_ne(b0 & b1, b1 & b0);
        assert!(!solve());
    }

    #[test]
    fn test_and_assoc() {
        init();
        let b0 = ndbool::fresh();
        let b1 = ndbool::fresh();
        let b2 = ndbool::fresh();
        ndassert_ne((b0 & b1) & b2, b0 & (b1 & b2));
        assert!(!solve());
    }

    #[test]
    fn test_or_comm() {
        init();
        let b0 = ndbool::fresh();
        let b1 = ndbool::fresh();
        ndassert_ne(b0 | b1, b1 | b0);
        assert!(!solve());
    }

    #[test]
    fn test_or_assoc() {
        init();
        let b0 = ndbool::fresh();
        let b1 = ndbool::fresh();
        let b2 = ndbool::fresh();
        ndassert_ne((b0 | b1) | b2, b0 | (b1 | b2));
        assert!(!solve());
    }
}
