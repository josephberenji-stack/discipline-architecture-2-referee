# The unfold pass (design)

Status: built (`#referee_unfold` and R1k in `RefereeCore.lean`;  `package_checks` and `--unfold-out` in `referee_lean.py`;
`unfold_report.py`), with planted controls for R1k, BRIDGED, CARRIER and UNFOLD.

## Why

R1 says one thing about a theorem:  whether its proof reaches a theorem outside the project.  A project that builds
its own objects can fail R1 on thousands of theorems, and R1 does not say why each one fails, so it cannot say what
to do about each one.  The reasons are different in kind:

- a law read off a record that stores it as a field (the record's instances supply the weight, or nothing does);
- a conclusion carried by a hypothesis that is a project proposition (the definition supplies the weight);
- a fact that holds by recursion on a type the project built (the weight is in the construction);
- a fact that holds by unfolding definitions alone (an accessor, a restatement).

And the objects behind them differ too:  some already carry an outside-library structure (an instance), some match an
outside-library structure field for field, some are new.  The unfold pass records all of this once, for every
declaration, so a person plans the work from the record instead of from reading thousands of proofs.

## What it prints

`#referee_unfold M` prints machine lines `UNFOLD <record> …` for every declaration of module `M` (in the check file:
of namespace `M`).  Schema 1:

| record | fields |
|---|---|
| `SCHEMA` | version, scope |
| `DECL` | name, kind, module, flags, type (pretty-printed, cut at 300 characters) |
| `EDGE` | from, to, part (`type` or `value`), the target's kind, the target's origin |
| `THM` | name, R1k, first content, stored axioms read, hypothesis heads, recursors, decide, rfl, project theorems reached, outside theorems reached, conclusion head, project types in the statement |
| `FIELD` | structure, field, is a proposition, type |
| `INSTOF` | instance, class, the class's origin, project types in the instance |
| `END` | scope, number of declarations |
| `ERROR` | a declaration the pass could not account for, and why |

Kinds:  theorem, def, propdef (a `def … : Prop` or a family of them), abbrev, instance (first:  an instance of a class
of propositions is stored as a theorem), structure, class, inductive, ctor, rec, opaque, axiom.  Origins:  project,
mathlib, core (`Init`, `Std`, `Lean`), lib (the other outside libraries).  Names Lean generates (matchers, auxiliary
proofs, equation lemmas) are opened, and their constants credited to the declaration that made them.

`#referee_unfold_library` prints `MSTRUCT` lines for every structure and class of the outside library (its fields by
name), for the counterparts report.

## The checks built on it

| check | where | catches | status |
|---|---|---|---|
| R1k | Lean, per theorem | what carries it:  CONTENT, FIELD, HYP, IND, UNFOLD | the kind itself, as with CLASS;  no verdict changes |
| UNFOLD | Python, per scope | the pass ran to its end, raised no error, and gave every theorem a THM line | PASS / FAIL |
| BRIDGED | Python, package | a theorem without content about a project type that already carries an outside-library instance:  the law is proved by unfolding, not through the bridge | REVIEW |
| CARRIER | Python, package | a project proposition that theorems assume and no theorem establishes (concluding `P n` from `P m` does not establish `P`) | REVIEW |

Each has a planted control that must fire and a clean one that must not (`controls/RefereeControls.lean`,
`controls.tsv`), and the mutation test switches each off in turn:  the self-test must then fail.

BRIDGED and CARRIER read the whole package, so they are computed by `unfold_report.py` over all the modules' lines,
not per module:  a module run sees only what it imports, and an instance or an establishing theorem may live
downstream.  In the self-test the check file is the whole package.

## What is a report and not a check

Counterparts.  A project structure whose field names match an outside-library structure is a candidate for a
proved equivalence, nothing more:  a field name is not a morphism, two structures with the same names can mean
different things, and a renamed copy has no names in common.  So `counterparts.tsv` lists candidates (shared field
names and their Jaccard index, at least two shared and at least one half) beside the outside instances the structure
already has, and no status is given.  The decision is a person's, and the evidence is a proved equivalence.

## The reports (`unfold_report.py`)

`summary.md`, `inventory.tsv`, `decls.tsv`, `r1k.tsv`, `carriers.tsv` (each carrier with its direct theorems and every
theorem downstream of them through the proof graph, and whether it is established), `counterparts.tsv`, `checks.tsv`,
and with `--compare` the theorems whose R1k changed since an earlier report:  the record of what a round of work moved.

## Limits

- R1k inherits R1's notion of content:  an outside theorem in the logic core does not count, and a project that
  rebuilds everything without imports has no content by this measure even where its proofs are long.  R1k says what
  carries such a proof;  it does not say the proof is shallow.
- Pretty-printed types are cut at 300 characters;  the edges are complete.
- The pass reads compiled environments only:  run it on a built package.
