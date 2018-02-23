extern crate pocket_prover;
extern crate pocket_prover_set;

use pocket_prover::*;
use pocket_prover_set::*;

fn main() {
    println!("Result {}", Set2::imply(
        |sets| and(imply(sets.a.uniq, sets.b.uniq), sets.a.uniq),
        |sets| sets.b.uniq
    ));
}
