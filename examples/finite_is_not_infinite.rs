extern crate pocket_prover;
extern crate pocket_prover_set;

use pocket_prover::*;
use pocket_prover_set::*;

fn main() {
    println!("Result {}", Set::imply(
        |s| s.fin_many,
        |s| not(s.inf_many)
    ));
}
