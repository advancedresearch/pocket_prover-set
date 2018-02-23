#![deny(missing_docs)]

//! # pocket_prover-set
//! A base logical system for PocketProver to reason about set properties
//!
//! ```rust
//! extern crate pocket_prover;
//! extern crate pocket_prover_set;
//!
//! use pocket_prover::*;
//! use pocket_prover_set::*;
//!
//! fn main() {
//!     println!("Result {}", Set::imply(
//!         |s| s.fin_many,
//!         |s| not(s.inf_many)
//!     ));
//! }
//! ```
//!
//! There are 4 bits of information, used to derive all other properties:
//!
//! - `any` - All types, including those not defined
//! - `uniq` - A unique value
//! - `fin_many` - Many but finite number of values
//! - `inf_many` - Many but infinite number of values
//!
//! A set is empty (`.none()`) when all bits are set to 0.
//!
//! A set is non-empty (`.some()`) when at least bit is set to 1.
//!
//! A set is undefined when it is `any` but neither unique, finite or infinite.
//!
//! Here is an example of a proof of 8 sets:
//!
//! ```rust
//! extern crate pocket_prover;
//! extern crate pocket_prover_set;
//!
//! use pocket_prover::*;
//! use pocket_prover_set::*;
//!
//! fn main() {
//!     println!("Result {}", Set8::imply(
//!         |sets| and(sets.uniqs(|xs| xorn(xs)), sets.a.uniq),
//!         |sets| not(sets.h.uniq)
//!     ));
//! }
//! ```
//! 

extern crate pocket_prover;

use pocket_prover::*;

/// Conditions that holds for a set in general.
#[derive(Copy, Clone)]
pub struct Set {
    /// All types, including those who are not defined.
    pub any: u64,
    /// A unique value.
    pub uniq: u64,
    /// Many but finite number of values.
    pub fin_many: u64,
    /// Many but infinite number of values.
    pub inf_many: u64,
}

impl Set {
    /// Rules for sets.
    pub fn rules(&self) -> u64 {
        and(
            imply(or3(self.uniq, self.fin_many, self.inf_many), and(self.some(), not(self.any))),
            imply(self.some(), xor4(self.uniq, self.fin_many, self.inf_many, self.any))
        )
    }

    /// Returns whether the set is empty.
    pub fn none(&self) -> u64 {
        not(or4(self.any, self.uniq, self.fin_many, self.inf_many))
    }

    /// Returns whether the set is non-empty.
    pub fn some(&self) -> u64 {
        or4(self.any, self.uniq, self.fin_many, self.inf_many)
    }

    /// Returns whether the set is undefined.
    /// This can be a set of higher cardinality.
    pub fn undefined(&self) -> u64 {
        and4(self.any, not(self.uniq), not(self.fin_many), not(self.inf_many))
    }

    /// Returns whether the set contains more than one.
    /// The set must be well defined.
    pub fn multiple(&self) -> u64 {
        or(self.fin_many, self.inf_many)
    }

    /// Counts the number of true cases.
    pub fn count<F: Fn(Set) -> u64>(f: F) -> u32 {
        count4(&mut |any, uniq, fin_many, inf_many| {
            f(Set {any, uniq, fin_many, inf_many})
        })
    }
}

impl Prove for Set {
    fn prove<F: Fn(Set) -> u64>(f: F) -> bool {
        Set::count(|x| imply(x.rules(), f(x))) == 1 << 4
    }
}

/// Contains 2 sets.
#[derive(Copy, Clone)]
pub struct Set2 {
    /// 1st set.
    pub a: Set,
    /// 2nd set.
    pub b: Set
}

impl Set2 {
    /// Do something with the `any` bits.
    pub fn anys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.a.any, self.b.any])
    }

    /// Do something with the `uniq` bits.
    pub fn uniqs<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.a.uniq, self.b.uniq])
    }

    /// Do something with the `fin_many` bits.
    pub fn fin_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.a.fin_many, self.b.fin_many])
    }

    /// Do something with the `inf_many` bits.
    pub fn inf_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.a.inf_many, self.b.inf_many])
    }
}

impl Prove for Set2 {
    fn prove<F: Fn(Set2) -> u64>(f: F) -> bool {
        prove8(&mut |
            x_any, x_uniq, x_fin_many, x_inf_many,
            y_any, y_uniq, y_fin_many, y_inf_many
        | {
            let sets = Set2 {
                a: Set {any: x_any, uniq: x_uniq, fin_many: x_fin_many, inf_many: x_inf_many},
                b: Set {any: y_any, uniq: y_uniq, fin_many: y_fin_many, inf_many: y_inf_many},
            };
            imply(
                and(
                    sets.a.rules(),
                    sets.b.rules(),
                ),
                f(sets)
            )
        })
    }
}

/// Contains 3 sets.
#[derive(Copy, Clone)]
pub struct Set3 {
    /// 1st set.
    pub a: Set,
    /// 2nd set.
    pub b: Set,
    /// 3rd set.
    pub c: Set
}

impl Set3 {
    /// Do something with the `any` bits.
    pub fn anys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.a.any, self.b.any, self.c.any])
    }

    /// Do something with the `uniq` bits.
    pub fn uniqs<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.a.uniq, self.b.uniq, self.c.uniq])
    }

    /// Do something with the `fin_many` bits.
    pub fn fin_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.a.fin_many, self.b.fin_many, self.c.fin_many])
    }

    /// Do something with the `inf_many` bits.
    pub fn inf_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.a.inf_many, self.b.inf_many, self.c.inf_many])
    }
}

impl Prove for Set3 {
    fn prove<F: Fn(Set3) -> u64>(f: F) -> bool {
        proven(12, &mut |vs| {
            let sets = Set3 {
                a: Set {any: vs[0], uniq: vs[1], fin_many: vs[2], inf_many: vs[3]},
                b: Set {any: vs[4], uniq: vs[5], fin_many: vs[6], inf_many: vs[7]},
                c: Set {any: vs[8], uniq: vs[9], fin_many: vs[10], inf_many: vs[11]}
            };
            imply(
                and3(
                    sets.a.rules(),
                    sets.b.rules(),
                    sets.c.rules(),
                ),
                f(sets)
            )
        })
    }
}

/// Contains 4 sets.
#[derive(Copy, Clone)]
pub struct Set4 {
    /// 1st set.
    pub a: Set,
    /// 2nd set.
    pub b: Set,
    /// 3rd set.
    pub c: Set,
    /// 4th set.
    pub d: Set
}

impl Set4 {
    /// Do something with the `any` bits.
    pub fn anys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.a.any, self.b.any, self.c.any, self.d.any])
    }

    /// Do something with the `uniq` bits.
    pub fn uniqs<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.a.uniq, self.b.uniq, self.c.uniq, self.d.uniq])
    }

    /// Do something with the `fin_many` bits.
    pub fn fin_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.a.fin_many, self.b.fin_many, self.c.fin_many, self.d.fin_many])
    }

    /// Do something with the `inf_many` bits.
    pub fn inf_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.a.inf_many, self.b.inf_many, self.c.inf_many, self.d.inf_many])
    }
}

impl Prove for Set4 {
    fn prove<F: Fn(Set4) -> u64>(f: F) -> bool {
        proven(16, &mut |vs| {
            let sets = Set4 {
                a: Set {any: vs[0], uniq: vs[1], fin_many: vs[2], inf_many: vs[3]},
                b: Set {any: vs[4], uniq: vs[5], fin_many: vs[6], inf_many: vs[7]},
                c: Set {any: vs[8], uniq: vs[9], fin_many: vs[10], inf_many: vs[11]},
                d: Set {any: vs[12], uniq: vs[13], fin_many: vs[14], inf_many: vs[15]},
            };
            imply(
                and4(
                    sets.a.rules(),
                    sets.b.rules(),
                    sets.c.rules(),
                    sets.d.rules(),
                ),
                f(sets)
            )
        })
    }
}

/// Contains 5 sets.
#[derive(Copy, Clone)]
pub struct Set5 {
    /// 1st set.
    pub a: Set,
    /// 2nd set.
    pub b: Set,
    /// 3rd set.
    pub c: Set,
    /// 4th set.
    pub d: Set,
    /// 5th set.
    pub e: Set
}

impl Set5 {
    /// Do something with the `any` bits.
    pub fn anys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.a.any, self.b.any, self.c.any, self.d.any, self.e.any])
    }

    /// Do something with the `uniq` bits.
    pub fn uniqs<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.a.uniq, self.b.uniq, self.c.uniq, self.d.uniq, self.e.uniq])
    }

    /// Do something with the `fin_many` bits.
    pub fn fin_many<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.a.fin_many, self.b.fin_many, self.c.fin_many, self.d.fin_many, self.e.fin_many])
    }

    /// Do something with the `inf_many` bits.
    pub fn inf_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.a.inf_many, self.b.inf_many, self.c.inf_many, self.d.inf_many, self.e.inf_many])
    }
}

impl Prove for Set5 {
    fn prove<F: Fn(Set5) -> u64>(f: F) -> bool {
        proven(20, &mut |vs| {
            let sets = Set5 {
                a: Set {any: vs[0], uniq: vs[1], fin_many: vs[2], inf_many: vs[3]},
                b: Set {any: vs[4], uniq: vs[5], fin_many: vs[6], inf_many: vs[7]},
                c: Set {any: vs[8], uniq: vs[9], fin_many: vs[10], inf_many: vs[11]},
                d: Set {any: vs[12], uniq: vs[13], fin_many: vs[14], inf_many: vs[15]},
                e: Set {any: vs[16], uniq: vs[17], fin_many: vs[18], inf_many: vs[19]}
            };
            imply(
                and5(
                    sets.a.rules(),
                    sets.b.rules(),
                    sets.c.rules(),
                    sets.d.rules(),
                    sets.e.rules(),
                ),
                f(sets)
            )
        })
    }
}

/// Contains 6 sets.
#[derive(Copy, Clone)]
pub struct Set6 {
    /// 1st set.
    pub a: Set,
    /// 2nd set.
    pub b: Set,
    /// 3rd set.
    pub c: Set,
    /// 4th set.
    pub d: Set,
    /// 5th set.
    pub e: Set,
    /// 6th set.
    pub f: Set
}

impl Set6 {
    /// Do something with the `any` bits.
    pub fn anys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.a.any, self.b.any, self.c.any, self.d.any, self.e.any, self.f.any])
    }

    /// Do something with the `uniq` bits.
    pub fn uniqs<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.a.uniq, self.b.uniq, self.c.uniq, self.d.uniq, self.e.uniq, self.f.uniq])
    }

    /// Do something with the `fin_many` bits.
    pub fn fin_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.a.fin_many, self.b.fin_many, self.c.fin_many, self.d.fin_many,
            self.e.fin_many, self.f.fin_many])
    }

    /// Do something with the `inf_many` bits.
    pub fn inf_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.a.inf_many, self.b.inf_many, self.c.inf_many, self.d.inf_many,
             self.e.inf_many, self.f.inf_many])
    }
}

impl Prove for Set6 {
    fn prove<F: Fn(Set6) -> u64>(f: F) -> bool {
        proven(24, &mut |vs| {
            let sets = Set6 {
                a: Set {any: vs[0], uniq: vs[1], fin_many: vs[2], inf_many: vs[3]},
                b: Set {any: vs[4], uniq: vs[5], fin_many: vs[6], inf_many: vs[7]},
                c: Set {any: vs[8], uniq: vs[9], fin_many: vs[10], inf_many: vs[11]},
                d: Set {any: vs[12], uniq: vs[13], fin_many: vs[14], inf_many: vs[15]},
                e: Set {any: vs[16], uniq: vs[17], fin_many: vs[18], inf_many: vs[19]},
                f: Set {any: vs[20], uniq: vs[21], fin_many: vs[22], inf_many: vs[23]},
            };
            imply(
                and6(
                    sets.a.rules(),
                    sets.b.rules(),
                    sets.c.rules(),
                    sets.d.rules(),
                    sets.e.rules(),
                    sets.f.rules(),
                ),
                f(sets)
            )
        })
    }
}

/// Contains 7 sets.
#[derive(Copy, Clone)]
pub struct Set7 {
    /// 1st set.
    pub a: Set,
    /// 2nd set.
    pub b: Set,
    /// 3rd set.
    pub c: Set,
    /// 4th set.
    pub d: Set,
    /// 5th set.
    pub e: Set,
    /// 6th set.
    pub f: Set,
    /// 7th set.
    pub g: Set
}

impl Set7 {
    /// Do something with the `any` bits.
    pub fn anys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[
            self.a.any, self.b.any, self.c.any, self.d.any,
            self.e.any, self.f.any, self.g.any
        ])
    }

    /// Do something with the `uniq` bits.
    pub fn uniqs<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[
            self.a.uniq, self.b.uniq, self.c.uniq, self.d.uniq,
            self.e.uniq, self.f.uniq, self.g.uniq
        ])
    }

    /// Do something with the `fin_many` bits.
    pub fn fin_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[
            self.a.fin_many, self.b.fin_many, self.c.fin_many, self.d.fin_many,
            self.e.fin_many, self.f.fin_many, self.g.fin_many
        ])
    }

    /// Do something with the `inf_many` bits.
    pub fn inf_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[
            self.a.inf_many, self.b.inf_many, self.c.inf_many, self.d.inf_many,
            self.e.inf_many, self.f.inf_many, self.g.inf_many
        ])
    }
}

impl Prove for Set7 {
    fn prove<F: Fn(Set7) -> u64>(f: F) -> bool {
        proven(28, &mut |vs| {
            let sets = Set7 {
                a: Set {any: vs[0], uniq: vs[1], fin_many: vs[2], inf_many: vs[3]},
                b: Set {any: vs[4], uniq: vs[5], fin_many: vs[6], inf_many: vs[7]},
                c: Set {any: vs[8], uniq: vs[9], fin_many: vs[10], inf_many: vs[11]},
                d: Set {any: vs[12], uniq: vs[13], fin_many: vs[14], inf_many: vs[15]},
                e: Set {any: vs[16], uniq: vs[17], fin_many: vs[18], inf_many: vs[19]},
                f: Set {any: vs[20], uniq: vs[21], fin_many: vs[22], inf_many: vs[23]},
                g: Set {any: vs[24], uniq: vs[25], fin_many: vs[26], inf_many: vs[27]},
            };
            imply(
                and7(
                    sets.a.rules(),
                    sets.b.rules(),
                    sets.c.rules(),
                    sets.d.rules(),
                    sets.e.rules(),
                    sets.f.rules(),
                    sets.g.rules(),
                ),
                f(sets)
            )
        })
    }
}

/// Contains 8 sets.
#[derive(Copy, Clone)]
pub struct Set8 {
    /// 1st set.
    pub a: Set,
    /// 2nd set.
    pub b: Set,
    /// 3rd set.
    pub c: Set,
    /// 4th set.
    pub d: Set,
    /// 5th set.
    pub e: Set,
    /// 6th set.
    pub f: Set,
    /// 7th set.
    pub g: Set,
    /// 8th set.
    pub h: Set,
}

impl Set8 {
    /// Do something with the `any` bits.
    pub fn anys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[
            self.a.any, self.b.any, self.c.any, self.d.any,
            self.e.any, self.f.any, self.g.any, self.h.any
        ])
    }

    /// Do something with the `uniq` bits.
    pub fn uniqs<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[
            self.a.uniq, self.b.uniq, self.c.uniq, self.d.uniq,
            self.e.uniq, self.f.uniq, self.g.uniq, self.h.uniq
        ])
    }

    /// Do something with the `fin_many` bits.
    pub fn fin_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[
            self.a.fin_many, self.b.fin_many, self.c.fin_many, self.d.fin_many,
            self.e.fin_many, self.f.fin_many, self.g.fin_many, self.h.fin_many
        ])
    }

    /// Do something with the `inf_many` bits.
    pub fn inf_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[
            self.a.inf_many, self.b.inf_many, self.c.inf_many, self.d.inf_many,
            self.e.inf_many, self.f.inf_many, self.g.inf_many, self.h.inf_many
        ])
    }
}

impl Prove for Set8 {
    fn prove<F: Fn(Set8) -> u64>(f: F) -> bool {
        proven(32, &mut |vs| {
            let sets = Set8 {
                a: Set {any: vs[0], uniq: vs[1], fin_many: vs[2], inf_many: vs[3]},
                b: Set {any: vs[4], uniq: vs[5], fin_many: vs[6], inf_many: vs[7]},
                c: Set {any: vs[8], uniq: vs[9], fin_many: vs[10], inf_many: vs[11]},
                d: Set {any: vs[12], uniq: vs[13], fin_many: vs[14], inf_many: vs[15]},
                e: Set {any: vs[16], uniq: vs[17], fin_many: vs[18], inf_many: vs[19]},
                f: Set {any: vs[20], uniq: vs[21], fin_many: vs[22], inf_many: vs[23]},
                g: Set {any: vs[24], uniq: vs[25], fin_many: vs[26], inf_many: vs[27]},
                h: Set {any: vs[28], uniq: vs[29], fin_many: vs[30], inf_many: vs[31]},
            };
            imply(
                and8(
                    sets.a.rules(),
                    sets.b.rules(),
                    sets.c.rules(),
                    sets.d.rules(),
                    sets.e.rules(),
                    sets.f.rules(),
                    sets.g.rules(),
                    sets.h.rules(),
                ),
                f(sets)
            )
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn both_none_and_some_means_uniq_is_nonsense() {
        assert!(!Set::means(
            |s| and(s.none(), s.some()),
            |s| not(s.uniq)
        ));
    }

    #[test]
    fn multiple_is_exclusive_from_undefined() {
        assert!(Set::exc(
            |s| s.multiple(),
            |s| s.undefined()
        ));
    }

    #[test]
    fn some_includes_undefined() {
        assert!(!Set::exc(
            |s| s.some(),
            |s| s.undefined()
        ));
    }

    #[test]
    fn none_is_not_some() {
        assert!(Set::imply(|s| s.none(), |s| not(s.some())));
    }

    #[test]
    fn some_is_not_none() {
        assert!(Set::imply(|s| s.some(), |s| not(s.none())));
    }

    #[test]
    fn some_is_eq_not_none() {
        assert!(Set::eq(|s| s.some(), |s| not(s.none())));
    }

    #[test]
    fn uniq_is_some() {
        assert!(Set::imply(|s| s.uniq, |s| s.some()));
    }

    #[test]
    fn uniq_is_not_fin_many() {
        assert!(Set::imply(|s| s.uniq, |s| not(s.fin_many)))
    }

    #[test]
    fn any_is_some() {
        assert!(Set::imply(|s| s.any, |s| s.some()));
    }

    #[test]
    fn fin_many_is_some() {
        assert!(Set::imply(|s| s.fin_many, |s| s.some()));
    }

    #[test]
    fn inf_many_is_some() {
        assert!(Set::imply(|s| s.inf_many, |s| s.some()));
    }

    #[test]
    fn some_does_not_mean_any() {
        assert!(Set::does_not_mean(|s| s.some(), |s| s.any));
    }

    #[test]
    fn not_uniq_and_not_none_is_either_fin_many_inf_many_or_any() {
        assert!(Set::imply(
            |s| and(not(s.uniq), not(s.none())),
            |s| or3(s.fin_many, s.inf_many, s.any)
        ));
    }

    #[test]
    fn fin_many_is_not_inf_many() {
        assert!(Set::imply(|s| s.fin_many, |s| not(s.inf_many)));
    }

    #[test]
    fn not_fin_many_does_not_mean_inf_many() {
        assert!(Set::does_not_mean(|s| not(s.fin_many), |s| s.inf_many));
    }

    #[test]
    fn none_is_equal_to_neither_uniq_fin_many_inf_many_or_any() {
        assert!(Set::eq(
            |s| s.none(),
            |s| not(or4(s.uniq, s.fin_many, s.inf_many, s.any))
        ));
    }

    #[test]
    fn undefined_is_some() {
        assert!(Set::imply(
            |s| s.undefined(),
            |s| s.some()
        ));
    }
}
