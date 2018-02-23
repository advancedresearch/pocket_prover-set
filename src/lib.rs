extern crate pocket_prover;

use pocket_prover::*;

/// Conditions that holds for a set in general.
#[derive(Copy, Clone)]
pub struct Set {
    /// All types, including those who are not defined.
    pub any: u64,
    /// A unique value.
    pub uniq: u64,
    // Many but finite number of values.
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
        not(self.none())
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
