# The Protocol

**A referee-gated method for computational claims built with a language model, and the
protocols that keep the record honest.**

This document is the rulebook the `discipline` suite enforces. Part I states the method:
who does what, in what order, and what each party may not do. Part II names the
instruments. Part III states the standing protocols, each as a rule with the failure it
exists to prevent. `README.md` describes the software; `LOG-PROTOCOL.md` describes the
human's flag for putting their own words into the record.

Throughout, *the builder* is the party that writes computation files (in practice a
language model working from a human's prose), *the referee* is the runtime module
`discipline/referee.py` together with the checks that run over a file, *the human* is the
person supplying the ideas, and *the outside check* is a separate reader given the files
and nothing else.

---

## Part I — The method

### 1. Separation of roles

A file that both computes a result and announces whether the result came out is a file in
which the announcing party had an interest in the answer. The method assigns the jobs to
different parties and makes the referee's lines un-writable by the builder.

- **The builder** finds the formulation under which an idea would work, writes the
  declaration, writes the file, and, after the referee has spoken, writes the next
  formulation or the parking note. The builder is not a judge of the idea.
- **The referee** decides. It owns the structure of every test, and that structure is fixed
  before anything runs.
- **The human** supplies the ideas and the pushes, sets the budget, argues for a new
  question when a budget runs out, signs parking notes, and calls the reassessment points.
- **The outside check** is a separate session, opened at reassessment points, given the
  files and nothing else, and held to the same rule as everyone: quote the row.

The working sentence for the builder is: *I may not believe what you are saying, but if it
were to work it would require X, Y, Z* — followed by the declaration, the prediction, and
the referee.

### 2. The cycle

1. **Receive.** The human states the idea. The builder restates it, in one sentence, using
   only words from the registry (`registers/NAMES.md`). No evaluation. If the idea cannot
   be restated in registered words, that is the first finding — a word is missing from the
   registry — and it is logged, not argued.
2. **Require.** The builder writes the requires-list: *if this were to work, it would
   require …*, each item cited from `RESULTS-INDEX.md` as **`file:line ITEM`**, found by
   search, never from recollection.
3. **Declare.** In the module docstring, before any code: the human's sentence verbatim,
   then what the run *predicts*, what would *kill* it, what it *requires*, the negative
   *control* that must fail, and the *budget* (which formulation this is, of how many). The
   setup is fixed here.
4. **Run.** `declare()`, then `verdict()` with a computed argument, `rows()` behind every
   count, a `control()` that must fail and states its vacuity, and `close()`. Then
   `sh check.sh FILE.py`.
5. **Read.** The builder reports what the `.out` file says, quoting its lines. Any
   interpretation is one sentence, tagged `[OPEN]`.
6. **Continue or park.** A FAILS is a fact about the formulation, not about the idea. The
   next move is the next formulation, or a parking note the human signs.

### 3. What the builder may not do

1. **Write a verdict.** A literal verdict argument is refused at runtime and reported by the
   static checks. The printed word is chosen by the value, never typed.
2. **Change the setup after the run.** A different setup is a new formulation and spends
   the budget.
3. **Interpret past the rows.** No sentence in conversation promotes a claim past `[OPEN]`.
4. **Skip the requires step.** A file with no requires-list, cited by line, is a violation.
5. **Re-litigate a FAILS in prose.** The answer to a FAILS is the next formulation or the
   parking note.
6. **Evaluate the idea.** The register for a promising surprise is *"positive coincidence —
   hold it loosely until the referee speaks."*
7. **Summarise from memory.** A number that is not in a named `.out` file does not appear
   anywhere.
8. **Declare a forced quantity as a measurement.** Before declaring, the builder names the
   theorem that would force the answer whatever the object is — or states that it looked
   and none applies. A quantity determined by the construction is not a measurement.

Two corollaries. *A word is not a morphism until the map is exhibited*: a structural term
(functor, kernel, morphism, invariant) is used only where the object it names has been
built in the file, or the file names the construction that is missing. *Corrections are
logged where the error happened*: numbered, in the docstring of the file, naming the finder
(human, machinery, model, or outside check) — never narrated in conversation.

### 4. What the human may rely on

- Every idea gets its formulations, honestly built, before anyone says no — and the "no" is
  a FAILS row, not a sentence.
- Every idea is linked, before it is tested, to everything on file it depends on, by line.
- Nothing the human said is lost: their sentence enters the docstring verbatim, a correction
  they found is a numbered ledger entry naming them as finder, and their own notes enter the
  project log verbatim (`LOG-PROTOCOL.md`).
- What stood is reported at the same weight as what fell, every cycle.

### 5. Budget and scope

- **Three formulations per idea**, written into the declaration as `budget="k of 3"`.
- **A fourth attempt is a new idea** and requires the human's written argument for it.
- **Fenced readings.** No complexity reading — P, NP, hardness, cost as a function of input
  size — until a computed rate against an input size exists in the project and is cited
  `file:line`. The same fence applies to any reading whose evidence is not yet on file:
  a physical claim, a claim about a system the file does not model. A file that points at
  such a claim either makes it, under the same rules, or stops pointing.

### 6. Reassessment points

The human calls them. At a reassessment point, in this order:

1. `sh reindex.sh` — rebuild `RESULTS-INDEX.md` and confirm every citation resolves.
2. `python3 -m discipline.baseline --write` — regenerate the standing rows (§9), **after**
   any backlog work, never before.
3. `python3 -m discipline.ledger --floor=… .` — confirm the correction numbering has no gap.
4. `python3 -m discipline.rollover` — confirm no working document is over the cap (§11).
5. `python3 -m discipline.log triggers` — surface held log entries that have accumulated.
6. The case sheet is reconciled against the `.out` files, not against the conversation.
7. The outside check is given the folder and asked what does not hold.

### 7. What the method is not

It is not an agreement regime, and it is not a scepticism regime. The safeguard against
building the human's belief instead of the mathematics is not the builder's attitude; it is
that the referee's structure is declared before execution, the verdict is computed, the
control must fail, and the record is the transcript.

---

## Part II — The instruments

| instrument | where | when |
|---|---|---|
| the results index | `sh reindex.sh` → `RESULTS-INDEX.md` | before every requires-list; at reassessment |
| the runtime referee | `discipline/referee.py` | imported by every computation file |
| the suite | `sh check.sh FILE.py` → `discipline/run.py` | over every file before its result counts |
| the ten file-level checks | `predeclare`, `rowsplit`, `guard`, `withdraw`, `noliteral`, `names`, `forced`, `cited`, `ground`, `primitive` | every file |
| the two corpus-level checks | `ledger`, `rollover` | every `check.sh` run |
| the baseline | `discipline/baseline.py` → `registers/BASELINE.md` | loaded every run; regenerated by hand at reassessment |
| the registry | `registers/NAMES.md` | every restatement; `names.py` at reassessment |
| the primitive register | `discipline/primitive.py` → `registers/PRIMITIVES-REGISTER.md` | every file that carries a copied construction |
| the correction ledger | `discipline/ledger.py`, numbered `#N` entries in docstrings | every correction, where it happened, naming the finder |
| the frozen register | `registers/FROZEN.md` | every rollover |
| the project log | `discipline/log.py` → `registers/PROJECT-LOG.md` | every `[[LOG]]` block |
| the storage manifests | `discipline/storage.py` → `registers/*-MANIFEST.tsv` | after every full reindex; `sh quickcheck.sh` between |
| the case sheet | a working document of the project | every cycle end |

Every check prints rows, not counts, and exits on the count of rows it cannot hold. Every
register is plain text, so it diffs, greps, and is cited like anything else.

---

## Part III — The protocols

### 8. The declaration

A computation file carries, in its module docstring and before any code:

- the human's sentence, verbatim, marked as theirs;
- `DECLARED IN ADVANCE`: what the run predicts and what result would count as its failure
  (the kill condition);
- `THE OBJECTS`: every object the file constructs, defined in the terms of the registry;
- `WHAT IS FORCED`: the theorem that would force the answer whatever the objects are, or the
  statement that none was found;
- `MIRRORS`: what the file's own construction reproduces from elsewhere, as a comment that
  carries no weight — delete every MIRRORS line and the file computes the same numbers;
- the negative control: a case that must fail, and how many of its rows agree with the
  claim by construction (its vacuity).

The declaration is what `predeclare` looks for, what `forced` compares literals against,
what `ground` requires the MIRRORS block from, and what `referee.declare()` records at
runtime. A change to it after a run is a new formulation.

### 9. The baseline — a check with a backlog is blind

**The failure.** A suite of checks run over a project that has grown under weaker rules
returns rows from the first run onward. For a check with a standing backlog, a row returned
tomorrow cannot be told from the rows returned today; the check reports, and nothing in the
report is a signal.

**The rule.**

- `registers/BASELINE.md` records the **standing rows** as identities:
  `check | kind | file | line`.
- Every `check.sh` run splits each file-level check into **HELD** and **NEW**, prints the
  new rows by name, and **exits on the NEW count**. A held row is still printed under its
  check; it is not cleared and not forgotten.
- **Regeneration is an act, never automatic:** `python3 -m discipline.baseline --write`, by
  hand, at a reassessment point, after the backlog work of that reassessment and never
  before. A silent refresh would restore exactly the condition the baseline exists to
  remove.
- The identity is deliberately tight: a row that moves to another line is NEW, because a
  file whose lines moved is a file somebody just touched, and its rows are worth reading
  again.

**What the baseline does not do.** It does not clear anything. The backlog is worked down
by fixing files, and the record shrinks when it is regenerated after that.

### 10. The citation address — the name is the address; the line is advisory

**The failure.** A citation resolved by its line alone accepts any line in a window below
it, and a citation resolved by its label alone accepts any line in the file. Neither set
contains the other, and a citation that resolves under one rule and not the other is an
address nobody can check.

**The rule.**

- A citation is written `path/FILE:LINE ITEM`. When `ITEM` is an item name, **the name is
  authoritative and the line is advisory.**
- The cited file must **anchor** the item: in a `.py`, a `declare("X"`, a `verdict("X"`, or
  a printed head `print("X.`; in a `.md`, a bolded section header `**X — …` or a table row
  whose first cell is `**X**`; in an `.out`, a `[X]` marker or a printed head `X.`. A citation
  with no anchor is `item-not-anchored`: it has no address.
- The line must be the item's **own material**: in a `.py`, the smallest enclosing statement
  of the syntax tree that names the item; in a `.md` or `.out`, the territory from the
  item's anchor to the next anchor. A drifted line is `line-stale` and the row **carries its
  repair target**, so it can be repaired without a human opening the cited file.
- When the label is prose rather than an item name, the block rule applies: the label must
  appear in the block at the cited line. No anchor convention is defined for prose.
- **Where to point:** at the item's printed section head; where it has none, at its
  verdict; where it has neither, at its declaration.
- A citation that nothing in the citing file reads — no import, no runtime read, no copied
  construction — is `not-load-bearing`: deleting it cannot break the file. A citation of a
  `.md` or `.out` can never be load-bearing by this test; the row says so and a human
  applies the rule.

### 11. The rollover — a working document is frozen at the cap

**The failure.** Nothing watches the size of the documents a project appends to every
cycle until the day one of them can no longer be read whole, or the store holding it refuses
the next write. By then the document is cited by line from everywhere, and renaming or
trimming it breaks every citation into it.

**The rule** (`discipline/rollover.py`).

- A **working document** is one the builder appends to every cycle: the case sheet, the
  state document, the transcript, any running register of results.
- **The cap is 120 KB**, about thirty thousand tokens. It is a constraint, not a
  measurement, and the reason is stated rather than tuned: a document of that size costs
  more to read than one turn should spend to find one row. Moving the cap means editing the
  docstring of `rollover.py`, where the move is visible.
- At the cap a document is **frozen**: its **name** and its **line count** are kept exactly
  as they are, because citations resolve into it by line. Nothing is appended to it, nothing
  is deleted from it, it is never renamed.
- The freeze is recorded in `registers/FROZEN.md` — a **sidecar**, never a marker inside the
  document, because a line added at the top of a cited file moves every line every citation
  names.
- A **successor** opens, naming its predecessor and its line count in its first lines.
- `rollover.py` rows on a live document over the cap, and on a frozen document whose line
  count has moved.

**A run is never split.**

- A **run** is one cycle's build: every file it produced, every row those files earned in
  the case sheet, and the one section it earned in the state document and the transcript.
  A run that produced two files is one run and two rows.
- **The freeze point is a run boundary, not a byte.** A document is frozen at the last
  complete run at or before the cap. It is never cut inside a run.
- **A run that cannot fit whole does not start.** If appending the next run's rows would
  carry the document past the cap, the document is frozen below the cap, at whatever size
  the last complete run left it, and the new run opens the successor with its first row.
  Freezing under the cap is correct and is not a row: the cap is a ceiling, not a target.
- **If a run has already started and its remaining rows will not fit, the rows already
  written move** to the successor, and the predecessor is frozen at the line count it has
  once they are gone. This is the only case in which a line is removed from a document
  about to be frozen; it is permitted because the document is not yet frozen when the move
  happens, and no citation resolves into it before then.
- **A citation is never left hanging.** Before a freeze, `sh reindex.sh` must resolve every
  citation; a `.out` cited from one document and a row cited from another must land in the
  same document if they belong to the same run.

### 12. One copy of record

**The failure.** A copy of a check, a register, or a run output that sits on a retrieval
surface is still *read*, and a reader routed to it first answers from it as if it were the
rule. A stale copy does not sit harmlessly.

**The rule.**

- **One space is canonical.** Every computation file, every `.out`, every register and every
  working document lives there, and nowhere else is authoritative. `registers/storage.cfg`
  names it (as the space itself, or as named parts).
- **Every run happens there.** The one standing exception is a file whose runtime exceeds
  the shell's per-call limit; it may be run elsewhere only against byte-identical
  `referee.py` and source, with the hashes recorded in the transcript entry for that run,
  and the `.out` written straight back.
- **Every other copy is a mirror**, kept exact by `sh mirror.sh` and proved exact by
  `sh quickcheck.sh`. A mirror is never cited and never indexed.
- **A retrieval surface carries source documents and the transcript** — the axioms or
  definitions, the registry, this protocol, the live case sheet, state document and
  transcript. It never carries the computation files, never the machinery, and never a run
  output. `RESULTS-INDEX.md` is generated by `sh reindex.sh` and is rebuilt, not carried.

### 13. The transcript — the dialogue is the record of how the computing was caused

The `.out` files are the record of what was computed. The transcript is the record of
*how the computing was caused*: which push produced which formulation, which objection
killed which rule, where the human's plain-language hunch turned into a declaration. That
is the data on the method itself, and it exists nowhere else: a `.out` cannot show it, and
a case row shows only the verdict at the end of it.

**What an entry must contain**, in this order:

1. **The human's prose, verbatim and in their own words** — not paraphrased and not tidied —
   including mid-turn pushes, corrections, hedges, redirections, and questions asked back.
   A hedge is part of the record; so is a redirection, because what it redirected is the
   finding.
2. **What the builder did with it** — the restatement in registered words, the formulation,
   and the declaration it became.
3. **What the referee said** — HOLDS, FAILS, or a run that does not count, with the `.out`
   named.
4. **What changed because of it** — the correction number, the rule that moved, the
   protocol that was written. A push that changed nothing is recorded as a push that
   changed nothing.

**What an entry may not do.** It may not replace the human's words with the builder's
summary of them; it may not drop a push because the push turned out to be wrong; and it
may not read as a report when what happened was an exchange. The builder's own reasoning
belongs in the docstrings and the `.out`; the transcript is the two voices and the referee
between them.

The transcript is a working document and rolls over under §11 with every predecessor kept
whole.

### 14. A positive coincidence is a debt, not a result

**The rule.** A surprise is written *"positive coincidence — hold it loosely until the
referee speaks"* — and that phrasing is not a place to stop. It is an entry in the debt
column. A coincidence recorded in one file is a declaration owed in a later one, whose job
is to either exhibit the arithmetic that makes the coincidence forced, or measure the family
that breaks it. Both discharge the debt; the verdict decides which.

**What discharging means, exactly.** A coincidence is discharged when one of these is on
the page: (a) a theorem is named that forces the observed agreement for any object of that
kind, so the coincidence was never one; (b) a member of the family is exhibited where the
agreement fails, with the condition separating the two sides counted on both; or (c) the
agreement is shown to be a consequence of the construction, in which case it is a defect of
the construction and the ledger takes it. What does not discharge it is a second run on a
larger family that agrees again: a coincidence surviving more draws is a bigger coincidence,
not an explanation.

**Where the debt is carried.** The `[OPEN]` cell of the case-sheet row that recorded it,
and the file's line in the open-lines register, which names it as a coincidence owed rather
than a limitation noted. A reassessment sweep reads both for anything undischarged.

### 15. Ask how much, not whether

**The rule.** A declaration does not carry a predicate. Where a reading can be written as
"this object has the property", it is written instead as the exact integer whose being
above nothing *is* that property, and the integer is what is declared, censused and
compared.

**Why.** A predicate is the coarsest possible reading of a quantity. It cannot separate two
objects that both have the property, and on a family drawn freely it very often comes back
constant — which looks like a result and is not one. A reading that asks whether some closed
path carries anything other than the identity is true on almost every free draw; the same
reading taken as an amount — how far the object's set of possibilities shrinks — separates
the objects immediately.

**What it requires on the page.** The degree named in the docstring's objects section
before it is used; its census reported; and, where the file is correcting an earlier
predicate, the measurement that the degree separates objects the predicate cannot: pairs
agreeing on the predicate and differing on the degree, counted.

### 16. A constant reading is structure; the invariant is where the functor fails to invert

**The rule.** When a reading comes back constant across a family, that is not a measurement
and is not reported as one: it is a structural necessity of how the family was built, and
the file says so. What is then built is a functor to another family, and what is measured
is exactly where that functor fails to invert — its image and its fibres, both as exact
integers, and whether the two failures are independent.

**Why.** Constancy inside a family carries no information about any member of it. It can
still carry information about the family, and the place that information becomes visible
is in a map to a different family, because only there is there something for the reading to
fail to preserve. One integer is not enough: a map of finite sets can fail to be onto while
staying injective, and fail to be injective while staying onto, and those are different
facts.

**What it requires on the page.** The constancy checked rather than assumed, and the labels
where it fails counted. The functor exhibited, not named. The forced part — that the
induced map exists at all — gated and not claimed. Then the image count, the fibre census,
and the count of cases failing each direction alone.

### 17. Walk the distance — a word without its object is not a reading

**The rule.** If a question can be asked of an object, it is walked until the arithmetic
stops, not until the prose runs out. *"What X means beyond that is unread"* is not an
allowed ending. Either the entirety of X's existence is defined and computed, or the file
names the construction that would have to be built first and logs that as the open line —
with the name of the thing missing, not with a shrug.

**Why.** A reading that stops early usually stops because a word is being used without its
object. A file that calls the fibres of a map of finite sets a *kernel* is honest about
using the word loosely, and that honesty is the tell: no group has been exhibited, so no
kernel in the real sense can be. Once the group is built, readings that were unreadable
become forced arithmetic in one step — the section set becomes a kernel, the restriction
acquires a cokernel, the blocks of a hom-set become cosets, the block count becomes an
index. Nothing is discovered by asking harder. The object is supplied and the questions
answer themselves.

**The corollary that costs.** Walking the distance can show that the *question* was wrong
rather than the object. A shortfall defined as a difference of two counts is additive; a
shortfall defined as a difference of two group orders is multiplicative, and an additive
question asked of it returns a fact about the formulation, not the object. A formulation
spent this way is spent — it goes on the budget and into the ledger at the place it
happened — and the next formulation asks the *same* question of the invariant whose
arithmetic the object actually has.

**What it requires on the page.** Every word that names a structure has its structure
exhibited in the same file, or the file says which construction is missing and where. No
reading ends at "unread". A formulation that failed because the invariant was wrong is
logged in the docstring at the declaration it failed at, numbered, naming the finder, with
the invariant that replaced it.

### 18. Push to the arithmetic boundary, then name its categorical components

**The rule, in two halves.** A claim is computed until the arithmetic stops, not until the
prose runs out (§17). What this section adds is what happens *at* the stop. A boundary is
not a result and it is not an excuse: it is an object, and the file must say what it is
made of. The components of a boundary are categorical — properties of the index, the
category or the functor, not of the numbers — and each one must be named, gated as forced,
and shown to be the thing doing the stopping. A boundary with its components named is a map
of where to push next, because dropping a component moves the boundary.

**An illustration.** A cohomology computation over a free category returns nothing above
degree one, at every diagram. That is the boundary. Its components are three, each gated
and none declared: freeness (a free category's classifying space is its own graph, which is
one-dimensional); a terminal object (an index with one has nothing above degree zero); and
a constant diagram (for which the cohomology is that of the order complex with those
coefficients). Naming them says exactly which index to build next: one that is not free,
carries no top, and is given a diagram that is not constant. The boundary was not a wall;
it was a list of conditions, and each one was a door.

**Three attempts, and no check-in.** A formulation that FAILS because the claim ran into a
boundary is a failure like any other, and the three-formulation budget applies to it. The
run is not stopped for one: the builder has the authority to reformulate mid-run, up to
three times, without asking, and reports the state of the findings and the failures
afterwards.

**Phrases that must be pushed before results are committed.** If a printed line, a scope
statement or a report carries the sentiment of any of these, the run does not end there:

- *does not exist in the project* — build it, or name the construction that must come first;
- *the map has not been established* — exhibit the map, or say what it would have to be a
  map of;
- *named but not exhibited* — a word is not a morphism until the map is shown;
- *a physical claim is not made* — if the file is pointing at a physical system, the physical
  claim is the thing being asked for; make it under the same rules, or stop pointing, and
  say which in the fence.

**What it requires on the page.** The boundary stated as an object, not as an absence. Its
components enumerated, each forced, each gated, each a property of the category rather than
of the coefficients. A statement of which component was dropped to get past it, and what
was found there. A ledger entry for every formulation the boundary cost.

### 19. A held claim is not finished until a proof engine has verified it

**The rule.** Nothing in §1–§18 is amended. A computational run still has to HOLD before
anything else happens. This section adds a stage *after* the referee: a declaration that
held is not a finished object; it is a claim that has survived computation and now owes a
proof.

**When it fires.** Not per file and not per declaration. It fires when a line of
investigation is finalized all the way through — every sub-investigation has been put to
the kill check and the ones that were going to hold have held. At that point the attempts
that held, and only those, are carried into a proof engine.

**Which engine, by content.** The choice between proof assistants is made by what the claim
is about, not by preference; it is recorded in the file's own header, with the reason, and
is not revisited once the file exists.

**The failure direction is backwards.** A claim that holds computationally and does not
hold in the proof engine is not a defect of the engine and not a translation problem. It is
a fact about the computational formulation, and it is answered the way every FAILS is
answered: another formulation, under the same budget, with the failure logged in the
docstring where it happened.

**Rigour is the same rigour.** A functor in a proof file is built the way a functor is built
anywhere under this protocol: the map exhibited, its action on objects and arrows given,
its laws proved, not asserted. A proof engine is stricter about that than the suite is, not
looser.

**Self-standing files.** A proof file may name its references in comments — which
investigation, which declaration, which `.out`, which line — but it is built from the
ground up and stands alone, importing nothing from the project. The comment is provenance;
the file is the proof.

**Documentation is unchanged.** Proof files live in the canonical space beside the runs.
Their contents, holds and fails are recorded briefly in the working documents — a row where
a run's row would go, under the same freeze and rollover rules.

### 20. Proof files form a chain; each starts where the last one stopped

**The rule.** A proof file still imports nothing — not from the project and not from
another proof file. The chain is a chain of *content*, not of imports.

**What it means on the page.** Every proof file ends with a numbered list of the things it
did not close, and that list is its **seam**. The next proof file's first declaration must
be one of the items on the previous file's seam, named as such in its header, with the file
and the item number. A proof file that opens on something no earlier seam names is out of
order, whatever else is true of it.

**The join is exhibited, not asserted.** Because nothing is imported, the successor cannot
point at the predecessor's theorem; it must rebuild the object at the join and re-prove the
endpoint in its own engine before going past it. That rebuild is the seam made visible, and
it is also a check: if the predecessor's endpoint does not come out again in the
successor's engine, §19's failure direction has fired and the matter goes back to
computation.

**The seam register.** The proof register carries a SEAM column: what the file closed off
its predecessor's list, and what it left on its own. A seam item is closed only by a file
that names it.

**Where a chain may branch.** A file's seam may carry more than one item, and a later file
may pick up any of them; the register records which. What is not allowed is starting a file
at an item no seam carries, and what is not allowed is a seam that says nothing, because a
file with no seam ends the chain.

---

## Appendix — The vocabulary

| term | meaning |
|---|---|
| **claim** | a sentence the referee can decide: a prediction with a kill condition |
| **formulation** | one construction under which the claim is put to the referee; three per idea |
| **declaration** | the docstring block fixing prediction, kill, requires, control and budget before any code runs |
| **verdict** | the referee's printed word, HOLDS or FAILS, chosen by a computed value |
| **control** | a case that must fail; a control that passes is a failure of the file |
| **vacuity** | the number of a control's rows that agree with the claim by construction, and are therefore silent rather than failing |
| **row** | one violating instance, printed; every count is backed by its rows |
| **forced** | determined by the construction; a forced quantity is gated, never declared as a measurement |
| **`[OPEN]`** | the only tag an interpretation in prose may carry |
| **ledger entry** | a numbered correction `#N`, in the docstring where the error happened, naming the finder |
| **finder** | who found a correction: the human, the machinery, the model, or the outside check |
| **register** | a plain-text record the suite reads: the registry, the baseline, the frozen list, the primitives, the independents, the log |
| **working document** | a document appended to every cycle; frozen at the cap under §11 |
| **run** | one cycle's build, named by its cycle; never split across two documents |
| **reassessment point** | a point the human calls, at which §6 is executed in order |
| **seam** | the numbered list of open items a proof file ends with, from which the next file must start |
