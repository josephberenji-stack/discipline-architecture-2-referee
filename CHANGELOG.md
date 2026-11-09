# Changelog

## 9 Nov 2026: the circle gate and source pinning of targets

`RefereeCore.lean` and `referee_lean.py` add the circle gate's questions as checks.
- CIRCLE1 (Q1): a construction takes in a registered problem object.
- CIRCLE2 (Q2): true for every input, either through a hypothesis about the problem object that the proof never uses, or because the kernel still accepts the proof with the object replaced by a variable.
- KNOWN (Q5): a label for registered known results.
- CIRCLE: one row per theorem over Q1–Q4, giving the new class CIRCLE.

E1 adds PIN: a registered target's pinned source must be unchanged, or come with an equivalence to the pinned version. The registry gains the kinds `data`, `known` and `pin`. New controls; self-test 114 of 114. The self-test fails with any one of the 34 checks switched off.

## 1–3 Nov 2026: fixes carried from Discipline-Architecture-2 main

- IFFSET rows for set equations; CARRY rows for a conclusion carried in by hand.
- A project instance is plumbing for R1, like an outside one.
- Generated names (`@[ext]`, `ofNat_ctorIdx`) are skipped.
- SRC FAIL when a module's source is missing under a srcDir.
- A finite step limit for the referee's own commands (`REFEREE_HEARTBEATS`).
- The module manifest tracks sections and blanks block comments.
- `Set`, `Set.ofPred` and `setOf` are named without being resolved.

## 30 Oct 2026: the decode step, run 1 (failed), and the behaviour step, registered

`lean/DECODE-DESIGN.md` § Results:  run 1 over 362,657 library declarations failed controls 1 (1 of 20), 2 (2 of 12)
and 5;  controls 3 and 4 passed.  The unfold pass is unchanged.  `#referee_decode_library` writes to the file named by
`REFEREE_DECODE_FILE` (Lean held a command's whole output until it ended).  `lean/BEHAVIOUR-DESIGN.md`:  the behaviour
step (shape by carrier sequence, probes per carrier class, the candidate's own laws checked on the project definition),
its seven controls and pass criteria, fixed before any code is written.  Not built.

## 30 Oct 2026: the decode step, registered

`lean/DECODE-DESIGN.md`:  the decode step for UNFOLD rows (match a definition, unpacked to outside constants, to an
outside declaration by its type's constants), its six controls and their pass criteria, fixed before any code is
written.  Not built.

## 29 Oct 2026: the unfold pass

`RefereeCore.lean`:  `#referee_unfold` prints a machine account of every declaration of a module (kinds, the constants
each uses, what carries each theorem, structure fields, instances;  `lean/UNFOLD-DESIGN.md`), and `#referee_unfold_library`
the outside library's structures.  New check R1k:  what carries a theorem (CONTENT, FIELD, HYP, IND, UNFOLD), printed as
the row's status, changing no verdict.  `referee_lean.py`:  `--unfold-out=DIR` writes each run's lines,
`--unfold-library=FILE` the library's structures, and `package_checks` computes UNFOLD (the pass accounted for every
theorem), BRIDGED (a law of an object that already carries an outside-library instance, proved by unfolding) and
CARRIER (a project proposition assumed and never established).  `unfold_report.py`:  summary, inventory, R1k, carriers
with downstream counts, counterpart candidates, package checks, and changes since an earlier report.  New controls for
each;  self-test 75/75, and every one of the 25 checks is needed (the self-test fails with any one switched off).

## 28 Oct 2026: generated declarations are not twins

`RefereeCore.lean`: the skip filter also skips matchers with several numeric suffixes (`match_1_1`), auxiliary recursors (`brecOn` and the like) and `noConfusion`; DUP no longer compares generated declarations, so two definitions with the same `match` shape are not reported as twins. New controls: `good_match_twins` (DUP PASS), `match_1_1` and `Nat.brecOn` (LS INFO), `match_up` (LS PASS). Self-test 65/65; every check is needed.

## 28 Oct 2026: a crashed Lean run is a failure

`referee_lean.py`: a Lean process that dies without printing an error (out of memory, a crash) now reports `BUILD FAIL` with its exit code and last line. Before, such a run produced no rows and passed. Self-test 61/61.

## 2.0.0 (unreleased)

### Python suite
- `referee`: the literal-verdict check now reads a call spread over several lines at module level (it started one
  line late and let a literal verdict print HOLDS).
- `primitive`: a class copied between files counts as a primitive;  `--rebuild-names A,B` regenerates only the named
  register sections.
- `reprleak` (new, file-level, opt-in):  a typed value is read only through a named translation, never through its
  storage.  The policy ships empty (`registers/reprleak.json`).
- `example/regenerate-walkthrough.sh` regenerates `walkthrough.out` from a scratch copy.

### Lean (new, `lean/`)
- The Lean referee (`RefereeCore.lean`, `referee_lean.py`):  checks L0–L7, L1u, LS and R1–R7, a computed class per
  theorem, exit codes 0 / 1 / 2.  L7 ships off.
- L1:  an `opaque` with a value is REVIEW, one without a value is FAIL.
- L1u:  where an `opaque` with a value is reached, from the statement (REVIEW) or the proof only (PASS).
- LS:  the generated-name skip filter decides on the last name component only;  a planted `eq_of_x` must be checked.
- R1i, DUP, SHADOW (Lean) and INST, VEND (per module):  checks for proofs built from supplied inputs
  (`lean/INPUTS-DESIGN.md`), each with a planted control that must fire and a clean one that must stay silent;
  self-test 61 of 61, and every check is needed (the self-test fails with any one switched off).
- `registry.tsv`:  the project's roots, registered targets, claim words, carriers and patterns, all shipped empty.
- `statics.py`:  P1–P8 on Python runs, without executing them.
- `census/census.py`:  stated vs accepted vs classed, with the accepted theorems no check read.
- Self-test:  49 planted expectations;  switching off any one of the 16 checks makes it fail.
- `example-lean/`:  five theorems, one per class, with the referee's and the census's outputs.

### Project
- Apache License 2.0 (`LICENSE`, `NOTICE`), citation metadata completed, `.gitignore`.
