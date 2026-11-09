# The behaviour step (design and registration)

Status: registered;  built 31 Oct 2026 to this registration (`Behaviour.lean`, `behaviour_run.py`, `behaviour_report.py`,
`controls/behaviour-rows.tsv`;  the readings of its words in `METHOD-LOG.md` entry 16);  registered run 1 (1 Nov 2026, `runs/behaviour-run1/`, entry 17):  controls 1, 2, 5 FAIL, 3, 4, 7 PASS.  Adopted by the author 30 Oct 2026 21:45 UTC, on the combined test the author
proposed at 21:22 UTC (family classification, probe objects from several families with an expected range of
results, the sequence of constants instead of the object).  It replaces the search of the decode step
(`DECODE-DESIGN.md`), which failed run 1 because two constructions of one object share few constants.  The library
lines, the unpacking and the report format of the decode step are kept.

## Why

A bridge proves that the framework's object is the mathematical object, whatever it is built from.  So the search for
a candidate must compare what an object does, not how it is written.  Values (the object on small inputs) and rules
(the laws it satisfies) are one test here:  a candidate `N` is tested by its own laws, taken from the library, with the
project definition `D` put in its place and checked on probes.

## What the step does

1. **Shape (the sequence of constants).**  The type of `D` after unpacking, and of every outside definition, is read
   as the ordered sequence of its carriers, each mapped to a carrier class:

   | class | outside carriers | project carriers (after unpacking) |
   |---|---|---|
   | N | `Nat`, `Int`, `Fin n`, `ZMod n` | `Nat`, `Int`, `Fin n` |
   | W | `List`, `FreeMonoid` | `List` |
   | M | `Multiset` | `Quot`/`Quotient` of `List` by a permutation relation |
   | S | `Finset`, `Set` over a finite type | `List` with a no-repeat condition, predicates on `Fin n` |
   | P | `Polynomial`, `MvPolynomial` | `Quot`/`Quotient` of coefficient lists |
   | R | `Real` | `Real` |
   | C | `Complex` | `Complex` |
   | F | functions `N → _` (sequences) | functions `Nat → _` |
   | Prop | `Prop` | `Prop` |

   The shape is the arrow sequence, for example `N → N → N` or `(F R) → R → Prop`.  The candidates of `D` are the
   outside definitions, structures and classes of the same shape.  The table is fixed by this file.
2. **Probes.**  Each class has a fixed probe set, written once as literals:  N: 0 to 6;  W: the words over
   {0, 1, 2} of length at most 3;  M: the multisets of those words;  S: the subsets of {0, 1, 2};  P: polynomials of
   degree at most 3 over `ZMod 2` and `ZMod 3`;  F: the sequences `n ↦ c`, `n ↦ n`, `n ↦ 1/(n+1)`.  R and C have no
   probes (see step 4).  Each side builds a probe from its literal with its own constructors (`Multiset.ofList` on
   the outside, the project's own quotient map inside).  No bridge is used.
3. **Laws.**  The laws of `N` are the outside theorems with an `=` or `↔` conclusion whose constants include `N` and
   whose other constants lie in the shared vocabulary:  the core (`Init`) constants and the probe builders of the
   classes in the shape.  At most the 50 shortest laws per candidate are kept.
4. **Transport and check.**  In each law `N` is replaced by `D` and the outside probe builders by the project's.
   - For computable shapes (no R or C), the law is checked by `decide` on every probe tuple that fits its binders,
     with a 2 s limit per law.  A law holds if every probe passes.
   - For shapes with R or C, the law is checked by one fixed tactic script, `intros; simp only [D's unfolding];
     first | rfl | (constructor <;> intro h <;> exact h) | aesop`, with a 10 s limit.  A law holds if the script
     proves it.
   - When `N` itself computes on the probes, the two sides' values are also compared (value agreement).
5. **Score and report.**  `S(D, N)` = the share of the tested laws that hold, with at least 3 laws tested;  value
   agreement must hold where it was checked.  `N` is a candidate when `S ≥ 0.8`.  Candidates are ranked by `S`,
   then by the number of laws tested, then by name length;  the top 10 are reported in `behaviour.tsv` with the
   laws that failed.  A candidate is a lead, not a status:  only a proved bridge gives one.

## Controls and pass criteria

The step passes only if all seven hold.  Controls 1, 2, 3, 5 and 6 are those of the decode step, unchanged, so the two
runs compare.

| # | control | passes when |
|---|---|---|
| 1 | known answers (the 20 rows of `controls/decode-controls.tsv`) | at least 14 of 20 in the top 10 |
| 2 | held out (the 12 rows) | at least 8 of 12 in the top 10 |
| 3 | planted absence (`tritonicHyperbracket`, `tritonicTwist`) | 0 candidates |
| 4 | cross-family swap:  each known and held-out `D` scored against the expected `N` of a row of another shape class, 1,000 random pairings, seed 20261030 | fewer than 5 % of pairings reach `S ≥ 0.8` |
| 5 | planted pair (`addOut`) | `Nat.add` in the top 10 |
| 6 | mutation:  the self-test with the step switched off | the self-test fails |
| 7 | other family:  for every known row, the `D` of each other known row of the same shape is scored on that row's `N` | no more than 2 of these reach `S ≥ 0.8` |

The rows `inversion` and `unique_factor` are theorems and `Swaps` an inductive:  the step decodes definitions, so
`Swaps` is read as the relation it defines (shape `W → W → Prop`) and the two theorems count as misses.

If any control fails, the step is reported as failed with its numbers and the unfold pass stays as it is.

## Limits

- The R and C laws are checked by a fixed proof script, not by evaluation;  a law it cannot prove counts as failing,
  so analytic rows can only be missed this way, never found falsely.
- The shape table decides the candidate pool;  a definition whose carriers are outside the table gets no candidates.
- The pass reads compiled environments only:  run it on a built package.
