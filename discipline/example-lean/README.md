# example-lean: the Lean referee on five theorems

`Example/Doubling.lean` holds five theorems whose status is obvious, one for each kind the
referee separates. `expected/` holds every output the suite printed on them, so the
behaviour can be read without running anything.

| theorem | what it is | computed class | manifest claim | status |
|---|---|---|---|---|
| `double_eq` | holds by unfolding `double` | DEF | DEF | PASS |
| `double_eq_two_mul` | uses a library lemma | A? | B (known as: the distributive law) | REVIEW: a person checks the known-as line |
| `eq_of_double_eq` | a person's theorem whose name begins with `eq_` | A? | A? | REVIEW: novelty is a person's call |
| `prime_above_ten` | holds under a `PrimeSource` nothing on file builds | C | A? | FAIL: the claim is stronger than the class |
| `two_pow_ten` | left on `sorry` | D | A? | FAIL: L0 |

The census (`expected/census/`) finds every accepted user theorem classed, so
`accepted-not-classed.tsv` is empty. `eq_of_double_eq` is listed in `name-shapes.tsv` as a
person's `eq_` name and is classed, not skipped.

## Run it

Build the module first (the referee reads compiled declarations):

    lake build Example
    python3 ../lean/referee_lean.py --project=. --modules=Example.Doubling      > expected/referee-modules.out
    python3 ../lean/referee_lean.py --project=. --manifest=headlines.tsv       > expected/referee-manifest.out
    python3 ../lean/census/census.py --project=. --modules=Example.Doubling --out=expected/census \
            --referee-log=expected/referee-modules.out                           > expected/census.out

The two referee runs exit 1 (a FAIL is present); the census exits 0 (nothing accepted was
left unread). The outputs here were produced on Lean 4.33.1 with the Mathlib revision
pinned in `lakefile.toml`.
