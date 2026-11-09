# Construction drift: one object built several ways, and the readings that join them (registered, not run)

Registered 30 Oct 2026, before any run.  Changes after this commit are new registrations, logged in `METHOD-LOG.md`.

## 1. Question

The behaviour step (`BEHAVIOUR-DESIGN.md`), with the project's own definitions admitted as candidates, found five
constructions of one function (prototype 2, `METHOD-LOG.md` entry 9;  joined by proof in the project's
`MobiusRoutes`).  The owner's question:  can this be a test that finds every such drift in the project and ties each
back to the project's label library?  His hypothesis, in his words:  *"these may be the example of things that have
the same label or are extensions of a labels ennumerations if it doubled itself or divided itself by 2"*.

## 2. Stage 1:  groups (drift by construction)

Candidates for a definition `D` are the project's own definitions of the same shape, with the matching rules of the
behaviour step (type parameters set to `ℕ`, instances filled, a Bool relation read as a Prop one).  Laws are each
candidate's own `=`/`↔` theorems, untestable laws skipped before the cap of 50 is counted.  Two definitions are **one
object** when S = 1 on at least 10 laws in both directions and their values agree on every probe.  A **group** is a
connected set of such pairs.

## 3. Stage 2:  the readings that join a pair

For every pair of definitions `f, g : ℕ → R` of the same shape (inside a group or not), on the probes `n = 1 … 64`:

| reading | test |
|---|---|
| same | `f n = g n` for all probes |
| doubled | `f n = g (2 n)` for all probes |
| halved | `f (2 n) = g n` for all probes |
| tripled (comparison) | `f n = g (3 n)` |
| third (comparison) | `f (3 n) = g n` |

A pair is **joined** by a reading when the test holds on every probe and the reading is not forced by both functions
being constant.  The label reading:  each member of a joined pair is looked up in the label library (`Labels/`
modules, by the constants its definition reaches).  The record is whether both reach the same label entry.

## 4. Controls (fixed thresholds)

| # | control | passes when |
|---|---|---|
| D1 | the five Möbius routes | form one group under "same" |
| D2 | planted pair `μ` and `n ↦ μ (2 n)` | joined by "doubled", not by "same" |
| D3 | planted pair `μ` and `n ↦ μ (n / 2)` restricted to even `n` | joined by "halved" |
| D4 | shuffled pairs:  1,000 pairs of the same shape drawn at random | joined by doubled or halved in at most 1 % |
| D5 | comparison:  doubled + halved against tripled + third, over all pairs | both counts reported;  no threshold |

The run is reported only if D1–D4 pass.  A failed control is reported with its numbers and nothing else is read.

## 5. What is decided and what is not

- Stage 1 decides groups.  Each group is a candidate for one home, which is the owner's decision.
- Stage 2 reports which readings join which pairs.  The hypothesis is supported to the extent that "doubled" and
  "halved" join pairs well above D4's rate, and above the tripled / third comparison of D5.  The run proves nothing:
  each join it reports becomes a proved link (a theorem in the project, as `MobiusRoutes`) before it counts.
- Carriers without probes (sets, multisets, polynomials, series) are out of this run, as in the behaviour step.

## 6. Outputs

`runs/drift-1/`:  `groups.tsv` (group, member, laws, S), `pairs.tsv` (f, g, reading, probes held), `labels.tsv`
(member, label entries reached), `controls.json`, `MD5.txt`, and a `METHOD-LOG.md` entry.
