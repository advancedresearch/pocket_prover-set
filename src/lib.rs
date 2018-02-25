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
//!     println!("Result {}", <(Set, Set, Set, Set, Set, Set, Set, Set)>::imply(
//!         |sets| and(sets.uniqs(|xs| xorn(xs)), sets.0.uniq),
//!         |sets| not(sets.7.uniq)
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

impl Construct for Set {
    fn construct(vs: &[u64]) -> Self {
        Set {
            any: vs[0],
            uniq: vs[1],
            fin_many: vs[2],
            inf_many: vs[3],
        }
    }
}

impl CoreRules for Set {
    fn core_rules(&self) -> u64 {self.rules()}
}

impl ExtendRules for Set {
    type Inner = ();
    fn inner(&self) -> &() {&()}
    fn extend_rules(&self, _: &Self::Inner) -> u64 {T}
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

/// Implemented on tuples of sets to access arrays of same kind of bits.
pub trait MSet {
    /// Do something with the `any` bits.
    fn anys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64;
    /// Do something with the `uniq` bits.
    fn uniqs<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64;
    /// Do something with the `fin_many` bits.
    fn fin_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64;
    /// Do something with the `inf_many` bits.
    fn inf_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64;
}

impl MSet for (Set, Set) {
    fn anys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.0.any, self.1.any])
    }
    fn uniqs<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.0.uniq, self.1.uniq])
    }
    fn fin_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.0.fin_many, self.1.fin_many])
    }
    fn inf_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.0.inf_many, self.1.inf_many])
    }
}

impl MSet for (Set, Set, Set) {
    fn anys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.0.any, self.1.any, self.2.any])
    }
    fn uniqs<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.0.uniq, self.1.uniq, self.2.uniq])
    }
    fn fin_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.0.fin_many, self.1.fin_many, self.2.fin_many])
    }
    fn inf_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.0.inf_many, self.1.inf_many, self.2.inf_many])
    }
}

impl MSet for (Set, Set, Set, Set) {
    fn anys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.0.any, self.1.any, self.2.any, self.3.any])
    }
    fn uniqs<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.0.uniq, self.1.uniq, self.2.uniq, self.3.uniq])
    }
    fn fin_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.0.fin_many, self.1.fin_many, self.2.fin_many, self.3.fin_many])
    }
    fn inf_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.0.inf_many, self.1.inf_many, self.2.inf_many, self.3.inf_many])
    }
}

impl MSet for (Set, Set, Set, Set, Set) {
    fn anys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.0.any, self.1.any, self.2.any, self.3.any, self.4.any])
    }
    fn uniqs<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.0.uniq, self.1.uniq, self.2.uniq, self.3.uniq, self.4.uniq])
    }
    fn fin_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.0.fin_many, self.1.fin_many, self.2.fin_many, self.3.fin_many, self.4.fin_many])
    }
    fn inf_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.0.inf_many, self.1.inf_many, self.2.inf_many, self.3.inf_many, self.4.inf_many])
    }
}

impl MSet for (Set, Set, Set, Set, Set, Set) {
    fn anys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.0.any, self.1.any, self.2.any, self.3.any, self.4.any, self.5.any])
    }
    fn uniqs<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.0.uniq, self.1.uniq, self.2.uniq, self.3.uniq, self.4.uniq, self.5.uniq])
    }
    fn fin_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.0.fin_many, self.1.fin_many, self.2.fin_many, self.3.fin_many,
            self.4.fin_many, self.5.fin_many])
    }
    fn inf_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[self.0.inf_many, self.1.inf_many, self.2.inf_many, self.3.inf_many,
            self.4.inf_many, self.5.inf_many])
    }
}

impl MSet for (Set, Set, Set, Set, Set, Set, Set) {
    fn anys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[
            self.0.any, self.1.any, self.2.any, self.3.any,
            self.4.any, self.5.any, self.6.any
        ])
    }
    fn uniqs<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[
            self.0.uniq, self.1.uniq, self.2.uniq, self.3.uniq,
            self.4.uniq, self.5.uniq, self.6.uniq
        ])
    }
    fn fin_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[
            self.0.fin_many, self.1.fin_many, self.2.fin_many, self.3.fin_many,
            self.4.fin_many, self.5.fin_many, self.6.fin_many
        ])
    }
    fn inf_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[
            self.0.inf_many, self.1.inf_many, self.2.inf_many, self.3.inf_many,
            self.4.inf_many, self.5.inf_many, self.6.inf_many
        ])
    }
}

impl MSet for (Set, Set, Set, Set, Set, Set, Set, Set) {
    fn anys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[
            self.0.any, self.1.any, self.2.any, self.3.any,
            self.4.any, self.5.any, self.6.any, self.7.any
        ])
    }
    fn uniqs<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[
            self.0.uniq, self.1.uniq, self.2.uniq, self.3.uniq,
            self.4.uniq, self.5.uniq, self.6.uniq, self.7.uniq
        ])
    }
    fn fin_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[
            self.0.fin_many, self.1.fin_many, self.2.fin_many, self.3.fin_many,
            self.4.fin_many, self.5.fin_many, self.6.fin_many, self.7.fin_many
        ])
    }
    fn inf_manys<F: Fn(&[u64]) -> u64>(&self, f: F) -> u64 {
        f(&[
            self.0.inf_many, self.1.inf_many, self.2.inf_many, self.3.inf_many,
            self.4.inf_many, self.5.inf_many, self.6.inf_many, self.7.inf_many
        ])
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
