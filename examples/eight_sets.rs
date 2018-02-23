extern crate pocket_prover;
extern crate pocket_prover_set;

use pocket_prover::*;
use pocket_prover_set::*;

fn main() {
    println!("Result {}", Set8::imply(
        |sets| and(sets.uniqs(|xs| xorn(xs)), sets.a.uniq),
        |sets| not(sets.h.uniq)
    ));
}
