extern crate pocket_prover;
extern crate pocket_prover_set;

use pocket_prover::*;
use pocket_prover_set::*;

fn main() {
    println!("Result {}", <(Set, Set, Set, Set, Set, Set, Set, Set)>::imply(
        |sets| and(sets.uniqs(|xs| xorn(xs)), sets.0.uniq),
        |sets| not(sets.7.uniq)
    ));
}
