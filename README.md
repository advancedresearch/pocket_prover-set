# pocket_prover-set
A base logical system for PocketProver to reason about set properties

```rust
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
```

There are 4 bits of information, used to derive all other properties:

- `any` - All types, including those not defined
- `uniq` - A unique value
- `fin_many` - Many but finite number of values
- `inf_many` - Many but infinite number of values

A set is empty (`.none()`) when all bits are set to 0.

A set is non-empty (`.some()`) when at least bit is set to 1.

A set is undefined when it is `any` but neither unique, finite or infinite.

Here is an example of a proof of 8 sets:

```rust
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
```
