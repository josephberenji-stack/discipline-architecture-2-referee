# Design: referee checks for proofs built from supplied inputs (28 Oct 2026)

Status: **built 28 Oct 2026** (R1i, DUP, SHADOW in RefereeCore.lean; INST and VEND per module in referee_lean.py; self-test 61/61, each check needed).  Each check below gets controls
(planted cases that must fire, and clean cases that must not) before it is built, as L1u did (`L1U-DESIGN.md`).

## The pattern these checks are for

A long proof is often staged: each stage is stated with named hypotheses ("…Input", "KnownResults…"), and a separate
file supplies each hypothesis as a proved theorem, so the final theorem carries none. The pattern is sound when every
supplied proof is a real proof of the stated input. It can go wrong in ten ways; six are already covered (hidden
values: L1/L1u; escape hatches: L0/L1; unused inputs: census; weakened targets: R1 on the headline plus the
statement-origin pass; weakened claims: a person reading against the source, by design). Four are not:

| id | gap | what fires it | output |
|---|---|---|---|
| **R1i** | an input supplied trivially: the "hard step" moved into a definition, so the supplying theorem holds by `rfl`, `trivial`, `⟨⟩` or unfolding | R1 (holds by unfolding) run on **every theorem whose type is a named input of another theorem** (a hypothesis type of a theorem the headline reaches), not only on headline theorems | one row per supplying theorem: REVIEW if it holds by unfolding |
| **DUP** | two copies of one object: the same body under two names, the statement using one and the proof the other, joined by a bridge | every pair of definitions in the closure with identical `ConstantInfo` values (types and bodies, up to the names of the constants themselves); for each pair, the theorem the proof uses to move between them, which must be a proved equivalence (`↔`, `≃`, `=`) | one row per pair: the two names, the bridge or NONE |
| **INST** | swapped instances: `attribute [-instance]` or local instances change what notation means between statement and proof | the instances in each statement's closure (by name and by the structure they provide), listed beside the instances the proof's closure uses for the same classes | one row per class with a differing instance |
| **SHADOW** | shadowed or vendored modules: two modules declare the same names and types, and import order decides which is used; vendored copies of library modules | constants with the same name declared in more than one module of the environment, and modules whose source is a copy of a library module under another root | one row per duplicate name / vendored module |

R1i and DUP serve our own build too: DUP is a mechanical check of "one home per object", and R1i applies to every
staged argument in a project.

## Controls (to be written before any check is built)

- R1i: a staged theorem whose input is `True` (supplied by `trivial`) must fire; one whose input is a real lemma must not.
- DUP: two definitions with the same body under different names, used across a statement/proof split, with and without a
  proved bridge: fires NONE without, names the bridge with.
- INST: a statement elaborated with a local instance removed: fires; the same statement with matching instances: silent.
- SHADOW: two modules declaring `Foo.bar` with the same type: fires; distinct names: silent.

## Effect on the case study

The case study's claims (K, M, F, G, H) were registered against the referee as it stands. Results from these new checks
on the OpenAI library are **exploratory** unless a dated pre-registration entry for them is written before they run.
