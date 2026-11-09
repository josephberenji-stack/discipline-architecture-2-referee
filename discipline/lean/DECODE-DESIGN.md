# The decode step (design and registration)

Status: built and run once, 30 Oct 2026;  **failed** controls 1, 2 and 5 (results below).  The unfold pass is unchanged.  Approved by the author 30 Oct 2026 17:02 UTC.  This file fixes the step, its controls and
its pass criteria before any code is written or run.  It extends the unfold pass (`UNFOLD-DESIGN.md`).

## Why

The unfold pass says what carries a theorem (R1k).  For UNFOLD rows (the theorem holds by unfolding definitions and
logic alone) the author's build plan marks the row "circular by the vocabulary" and stops.  That leaves open the
question the person must answer for each such definition:  is it an object the outside library already has?  If so,
a proved bridge lets the definition be read as that object, and the theorems about it as the object's facts.

A word search over names and docstrings answers this badly.  In the author's library's Mathlib comparison (runs 3 and
4, `docs/mathlib-comparison/` in that repository) the two declarations that its bridges needed most,
`finFunctionFinEquiv` and `Nat.Partition.hasProd_genFun`, were missed:  one states the count in its type and never
says "card", the other has no docstring and writes its product as `HasProd` over `R⟦X⟧`.  The counterparts report has
the same limit:  it matches field names, and a renamed copy shares none.  The elaborated environment has neither
problem:  a declaration's type lists the constants it is built from, whatever words or notation were used.

## What the step does

1. **Library lines.**  `#referee_unfold_library` also prints, for every declaration of the outside library:
   `MDECL  name  kind  module  head  lhs  rhs  consts`.  `head` is the head constant of the conclusion after the
   binders (`Iff`, `Eq`, `Equiv`, `HasProd`, …, or the type's head for a definition).  For an `Iff` or `Eq`
   conclusion, `lhs` and `rhs` are the constant sets of the two sides;  otherwise they are empty.  `consts` is the
   constant set of the type, and for a definition also of its value.
2. **Unpack.**  For each project definition that an UNFOLD theorem uses (its `EDGE` lines), project constants are
   delta-expanded until only outside constants remain (at most 20 rounds;  a definition still holding project
   constants after that, or whose expansion hits a project inductive or structure, is reported as stopping there,
   with the project constants that remain).  The result is the definition's unpacked constant set `U(D)`.
3. **Ignored constants.**  The logic core (`Eq`, `Iff`, `And`, `Or`, `Not`, `Exists`, `True`, `False`, `ite`, `dite`,
   `Decidable`), instances (kind `instance`), `OfNat.ofNat` and the numerals, and auxiliary names Lean generates are
   dropped from every set before scoring.  The list is in this file and changes only by a new registration.
4. **Two routes to a candidate.**
   - **Twin:**  an outside definition `N` with `J(U(D), consts(N)) ≥ 1/2` and at least two shared constants.
   - **Characterisation:**  an outside theorem `T` whose conclusion is an `Iff` or `Eq` with one side `S` such that
     `J(U(D), S) ≥ 1/2` with at least two shared constants, and whose other side has an outside head `N`.  The
     candidate is `N`, with `T` as its evidence (for example `Metric.tendsto_atTop` for a definition written as
     ε–N convergence).
   `J` is the Jaccard index.  Candidates are ranked by `J`, then twins before characterisations, then by name length.
   The top 10 per definition are reported.
5. **Report, not verdict.**  `unfold_report.py` writes `decode.tsv`:  definition, its UNFOLD theorems, `U(D)` or the
   stop, and the ranked candidates with route and evidence.  No status is given and no verdict changes.  A candidate
   becomes a bridge only when a Lean file proves the definition equal or equivalent to the outside object;  that
   theorem is also the check that the definition does not drift when unpacked.

## Controls and pass criteria

Every count below is fixed now.  The step passes only if all six hold.

| # | control | set | passes when |
|---|---|---|---|
| 1 | known answers (design set) | the 20 single-declaration bridges of the author's library comparison (`Bridges/Mathlib/`, 30 Oct; the composite neck-prim row is left out):  `numeralEquiv`→`Nat`, `wordsEquiv`→`FreeMonoid`, `ffinEquivMultiset`→`Multiset`, `setsEquivFinset`→`Finset`, `toF`→`Multiset.toFinsupp`, `swaps`→`List.Perm`, `sub`→`Multiset.le`, `deloop`→`CategoryTheory.SingleObj`, `Poly`→`MvPolynomial`, `mc`→`Nat.multichoose`, `pref`→`PiNat.res`, `mu`→`ArithmeticFunction.moebius`, inversion→`ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`, `lexle`→`List.Lex`, `rot`→`List.rotate`, `reading`→`finFunctionFinEquiv`, `Pol`→`Polynomial`, `unique_factor`→`UniqueFactorizationMonoid.factors_unique`, `Gc` series→`Nat.Partition.hasProd_genFun`, `eval`→`MvPolynomial.aeval` | at least 14 of 20 in the top 10 |
| 2 | held out | the 12 bridges of waves 1–2 (`Bridges/R1Hyp1.lean`, `R1Hyp2.lean`, built 29 Oct):  `ConvergesTo`, `ConvergesToC`→`Filter.Tendsto`;  `SumsTo`→`Filter.Tendsto` of partial sums;  `Cont`, `CCont`→`Continuous`;  `ContOnR`→`ContinuousOn`;  `IsChainS`→`IsChain`;  `Adj`→`SimpleGraph.fromEdgeSet`;  `Per`→`Function.Periodic`;  `bndN`→`Set.Finite`;  `IsChar`→`AddChar`;  `CastRel`→`Eq` on `Sigma` | at least 8 of 12 in the top 10 |
| 3 | planted absence | a control module with an inductive and two definitions found only in the project | 0 candidates |
| 4 | shuffle | the constants of all `U(D)` in scope pooled and dealt back at random, each definition keeping its number of constants and no constant twice in one set, 1,000 times, seed 20261030 | the real candidate rate is above the 95th percentile |
| 5 | planted pair | `controls/RefereeControls.lean`:  one definition whose value is `Nat.add` written out (must fire, `Nat.add` in the top 10) and one built on the planted inductive (must not fire) | both as stated |
| 6 | mutation | the self-test with the decode step switched off | the self-test fails |

If any of 1–6 fails, the step is reported as failed with its numbers, and the unfold pass stays as it is.  If all
pass, `decode.tsv` is produced with the next round on the build VM, for the UNFOLD rows first.

**Amendment, 30 Oct 2026, before any code ran.**  Control 4 first read "the `U(D)` sets permuted across the
definitions in scope".  A whole set moved to another definition is scored exactly as before, so that shuffle leaves
the candidate rate unchanged and the control could never pass.  It now deals the pooled constants back at random,
which keeps each set's size and breaks which constants occur together.  Nothing else changed.

**Amendment 2, 30 Oct 2026, before any scoring run.**  The first project-side dump (not scored) showed two kinds of
noise.  Values built through quotients carry proof terms, so lemma names (`Eq.trans`, `Int.add_one_le_of_lt`, …)
and casts entered the sets;  and a `match` on a project inductive unfolds through its `casesOn` and `ctorIdx` into bit
operations (`Nat.land`, `Nat.shiftRight`).  So the ignored constants now also leave out, on both sides, every theorem, every
constructor of a proposition (`Eq.refl`, `Iff.intro`, …), the casts `Eq.mpr`, `Eq.mp`, `Eq.rec`, `Eq.ndrec`, `cast`,
`id`, `Decidable.decide`, and the tactic framework's own constants (`Lean.*`, such as `Lean.Omega`);  a matcher counts
by its type only;  and a constant that belongs to a project
inductive (its constructors, recursors, `casesOn`, `ctorIdx`) is a stop at that inductive, as step 2 already says.
The controls and pass criteria are unchanged.

## Afterwards, other mechanisms

The same library lines and unpacking serve other checks, each added later as its own check with a planted control
that must fire and a clean one that must not:  FIELD (a record matched to an outside structure or class by its
fields' types), HYP (a project proposition matched to an outside predicate), IND (an inductive matched by its
constructors), CARRIER (an assumed proposition the outside library proves), counterparts (the ranking in place of
shared field names), and DUP/COPY (the same comparison inside the project finds renamed twins).

## Limits

- Constant sets ignore structure:  two statements with the same constants can say different things.  That is why a
  candidate is a lead and only a proved bridge counts.
- Delta-expansion can stop on project inductives and structures;  those definitions are decoded by IND and FIELD,
  not here.
- The pass reads compiled environments only:  run it on a built package.

## Results, run 1 (30 Oct 2026)

Library:  362,657 MDECL lines (`import Mathlib`, Mathlib 0df444a3, Lean 4.33.1;  md5 67966f2f…).  Project:  628 DDECL
lines from the 15 generation modules, `F1C3.PROOF_F1_C3_spheres`, `WordsDigits`, the 10 held-out modules and the planted
controls (md5 da50dd78…).  Outputs:  `decode.tsv` (md5 bf30d1a4…), `decode-controls.json` (md5 519d6c04…).

| # | control | criterion | result | |
|---|---|---|---|---|
| 1 | known answers | ≥ 14 of 20 | 1 of 20 (`bag` → `Multiset`, rank 1) | FAIL |
| 2 | held out | ≥ 8 of 12 | 2 of 12 (`ConvergesTo` rank 5, `Adj` rank 2) | FAIL |
| 3 | planted absence | 0 candidates | 0 and 0 | PASS |
| 4 | shuffle | real rate above p95 | real 0.539, null mean 0.168, p95 0.185, max 0.198 | PASS |
| 5 | planted pair | `Nat.add` in the top 10 | not there | FAIL |
| 6 | mutation | self-test fails without the step | not run (the step failed first) | — |

The step fails as registered.  What the numbers show:

- The candidate rate is far above chance (control 4), so constant sets do carry signal;  but the signal is not the
  object.  A project definition is unpacked to the constants of its construction (lists, `Quot`, `List.Perm`,
  arithmetic), and Mathlib's object of the same name is built from other constants (`Multiset` from `Quot` on
  `List.Perm`'s setoid, `Nat.add` from `Nat.rec`).  Two constructions of one object share few constants:  `addOut`
  unpacks to {Nat, Nat.succ}, and 12 of the 17 decoded known definitions unpack to sets of 1 to 9 constants that many
  unrelated declarations share.
- Three known rows are not definitions (`Swaps` is an inductive, `inversion` and `unique_factor` theorems) and were
  never decoded.
- The top candidates include logic and tactic names (`And`, `Not`, `Membership.mem`, `Lean.Meta.Grind.*`,
  `Mathlib.Tactic.*`) as the head of a characterisation's other side:  the ignored list was applied to the sets, not
  to candidate heads.

Any change to the step is a new registration before a new run.
