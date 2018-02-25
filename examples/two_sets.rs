extern crate pocket_prover;
extern crate pocket_prover_set;

use pocket_prover::*;
use pocket_prover_set::*;

fn main() {
    println!("Result {}", <(Set, Set)>::imply(
        |sets| and(imply(sets.0.uniq, sets.1.uniq), sets.0.uniq),
        |sets| sets.1.uniq
    ));
}
