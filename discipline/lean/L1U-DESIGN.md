# L1u: unpacking an opaque constant (design)

Status: steps 1 and 2 are built (check `L1u` in `RefereeCore.lean`, with controls); step 3, the providers, is designed
and not built. L1 already separates the two kinds of `opaque`. An `opaque` with no value is a stand-in
and FAILs. An `opaque` given an explicit value is REVIEW: the kernel checked the value, but no theorem can see it.
L1u is the step that turns that REVIEW into a recorded outcome, so that a person reads the outcome instead of the
raw constant.

## Why

A proof can be correct and still hide its content. When `opaque c : T := v` is used, every theorem about `c` is a
theorem about an unknown inhabitant of `T`. That is fine when the hiding is cosmetic, and wrong when the hidden value
is what makes the proof go through. Which case applies is decidable for each constant, but only by looking at `v`.

## A correction to the first draft

The first draft had a `hidden-proof` outcome: "the theorem fails once `c` is made transparent". That outcome cannot
occur. Making an `opaque` transparent only adds definitional equalities. Every typing judgement the kernel accepted
with `c` opaque still holds with `c` unfolded, so a proof never depends on not seeing `v`. Replaying proofs therefore
tests nothing, and the draft's control (a planted `opaque` whose hiding carries a proof) cannot be built. What can
differ is where `c` appears, and what `v` is.

## The steps, per opaque constant `c : T := v` that a checked theorem reaches

1. **Read.** Take `T` and `v` from the compiled environment (`ConstantInfo.opaqueInfo`). Its axioms are already in L0:
   the axiom walk follows an `opaque`'s value.
2. **Locate.** For each theorem `t` that reaches `c`, decide whether `c` is reached from `t`'s statement (its type,
   through every project definition it unfolds to) or only from its proof.
   - **Proof-only:** the statement means the same whatever `v` is. The hiding is cosmetic for `t`, and the kernel
     checked `v` anyway.
   - **Statement-level:** the statement is about `c`, so what `t` says depends on `v`. A person has to read `v`.
3. **Name.** For a statement-level `c`, ask the reference providers (below) for a known object equal to `v`. A
   candidate is accepted only with a proved equality `c' = r` for the transparent twin `def c' : T := v`, checked by the
   kernel in a scratch file. A provider proposes; the kernel decides.

## Outcomes, one row per (theorem, constant)

| outcome | meaning | status |
|---|---|---|
| `proof-only` | `c` is reached only from the proof | PASS, with the record |
| `statement:match:<provider>:<name>` | the statement reaches `c`, and `v` is provably equal to the named object | PASS, with the record |
| `statement:unnamed` | the statement reaches `c`, and no provider has a match | REVIEW: a person reads `v` |

## Reference providers

A provider is any program with one call:

    candidates(T, v, context) -> list of (name, Lean term r, Lean proof of v = r or a tactic to try)

- The public suite ships one provider, the **outside library**. It searches the imported library (`exact?`-style
  term search, `#find` on the type, `decide` on a finite type) for a constant of type `T` equal to `v`.
- A project may register its own provider (a file named in `registry.tsv` as kind `provider`, once L1u is built).
  It can propose objects from the project's own library. Its candidates pass through the same kernel check, so a
  project provider can add matches but cannot weaken the check.

## Limits

- L1u does not decide whether a match is the intended meaning. A proved equality to a library object is a fact. That
  the author meant that object is a reading.
- A statement-level `c` is not a defect. A challenge statement may define its objects with `opaque` on purpose. The
  outcome says only that the statement's meaning runs through `v`.
- An `opaque` reached only through another `opaque` is unpacked in dependency order. A cycle is reported, not
  resolved.

## Pre-registration

Every L1u run over an outside corpus states its claims before the run: the constants in scope (by a static pass), the
outcomes expected and what would count against them, and a negative control. The control is a planted theorem whose
statement mentions an `opaque`, and it must come out `statement:*`.
