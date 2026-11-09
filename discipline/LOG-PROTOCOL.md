# The project log — protocol, flag and template

The project log is the human's way of putting their own words into the record, connected
to what they bear on, at the moment they have them — between two exchanges or after ten —
without the model deciding whether the words deserve it. The log is append-only and
verbatim, and every entry names what it connects to. It is the human's half of the
protocol's requires-step (`PROTOCOL.md` §2): the builder links ideas to results by
search; the human links results to ideas by flag. The load is shared.

Why it exists. The human's side of the work is the part most easily lost: a decision
adopted in a document the model never saw; a question asked three times in different words
that the record says nobody asked; a connection the human made by hand because the model's
memory of the record failed. Every one of those is a contribution that was never in a file,
so it could not be retrieved, so it was re-derived or lost. The log puts it in a file.

## 1. The flag

A line that is exactly `[[LOG]]` opens a block. Everything from that line to a line that is
exactly `[[/LOG]]` — or to the end of the message if there is no closing line — is committed
to the project log. The flag can carry a disposition:

| flag | meaning |
|---|---|
| `[[LOG]]` or `[[LOG hold]]` | log it and hold it; it stays in the log until something makes it relevant |
| `[[LOG connect]]` | log it and distil it into the project content now — a note under the theorem, a line in the docstring, a row in the census |
| `[[LOG draft: <target>]]` | log it and treat it as enough to trigger a new iterative draft of `<target>` |

Anything outside the block is ordinary conversation. A message can contain more than one
block. The brackets do not render as anything in Markdown and do not occur in normal prose,
so the model can match them mechanically and so can `discipline/log.py`.

## 2. The template

Inside the block. Only `what` and `connects` are required; the rest is there when wanted.
Plain language throughout — the model's job is to resolve the human's names against the
registry and the index, not to make the human write in them.

```
[[LOG]]
what:      the text to be logged, in your words, as you would say it
connects:  SQ1; perfect square; example.py         <- the things this relates to, separated
                                                      by semicolons: item names, registered
                                                      words, files or sections, ledger
                                                      numbers, earlier log entries (L-0012)
how:       SQ1 -- instance of
how:       perfect square -- extends (gives it a unit)   <- one line per connection you want to
                                                      characterise; the relation words:
                                                      depends on / extends / contradicts /
                                                      same as / instance of / renames /
                                                      question about / answers
because:   why you think it connects, if the connection is not obvious from the text
do:        hold | connect | draft: <target>       <- overrides the flag's disposition
[[/LOG]]
```

Three fields cover most entries: `what`, `connects`, and one or two `how` lines. If the
human does not know what an entry connects to, `connects: ?` is itself a valid entry, and
the model's first job with it is to search rather than to guess.

## 3. What the model does when it sees the flag

In this order, before anything else in its reply, and without evaluating the content:

1. **Append.** The block becomes an entry in `registers/PROJECT-LOG.md` with an id
   (`L-0001`, …), a UTC timestamp, and the disposition. The `what` field is copied verbatim
   under the author's label (`DISCIPLINE_AUTHOR`, default "Author"). Nothing in the entry
   is paraphrased. The log is append-only; a later change of status is a new line, never an
   edit.
2. **Resolve.** Each item in `connects` is looked up in `RESULTS-INDEX.md` and
   `registers/NAMES.md` and written into the entry with its `file:line` (or its registered
   definition). An item that resolves nowhere is written as **UNRESOLVED** — a finding about
   the registry or the index, not a correction of the human. The model does not substitute
   what it thinks was meant. With the tool, `python3 -m discipline.log add MESSAGE.txt`
   (or `add -` with the message on standard input) does steps 1 and 2 and prints the rows.
3. **Restate.** One sentence, in registered words, marked as the model's, filled into the
   entry's "restated" line. If the restatement is not obviously the same claim as `what`,
   the model asks one clarifying question in the reply. It does not argue.
4. **Confirm.** One line in the reply: the id, the disposition, how many connections
   resolved and which are unresolved, and — for `connect` — where the distillation went;
   for `draft` — that a draft of the target is queued for the human's go-ahead.
5. **Act on the disposition.**
   - `hold`: nothing further now. The entry is indexed from then on, so the builder's
     requires-step surfaces it whenever its targets come up.
   - `connect`: the model adds a citation line to each resolved target's own home — a note
     under the theorem in the definitions document, a line in the file's docstring, a row in
     the census — reading `see PROJECT-LOG L-0007`, and appends `status: connected -> …` to
     the entry (`python3 -m discipline.log resolve L-0007 --status "connected -> …"`). The
     distillation cites the log; it does not replace it.
   - `draft`: the model proposes a new iterative draft of the target, citing every log entry
     that bears on it, and waits for the human's go-ahead before writing it.

## 4. When held entries become a draft

Held entries accumulate. Two things turn them into a draft:

- **The human says so** — `[[LOG draft: <target>]]` on any later entry, or the word "draft"
  at a reassessment point.
- **A threshold** — `python3 -m discipline.log triggers --threshold 3` lists every target
  with three or more held entries. At a reassessment point the model runs it and
  *proposes* a draft for each; it never writes one unprompted. The threshold is the
  human's to set; three is the default.

Between those, `python3 -m discipline.log pending` shows what is held, by target, so
nothing sits unseen.

## 5. Where the log lives and how it feeds everything else

- `registers/PROJECT-LOG.md` lives with the other registers, one per project, and is
  committed with everything else. It is a document in the canonical space, so every check
  sees it and the outside check reads it.
- `discipline/index.py` indexes it: every entry is a row (`L-0012 | log (hold) | …`), so
  the builder's `grep -i <term> RESULTS-INDEX.md` returns the human's words next to the
  theorems. That is the mechanism that makes "nobody has asked" a claim the index can
  refute.
- Ledger entries stay in docstrings (`PROTOCOL.md` §3); a log entry that turns out to be a
  correction gets a ledger number *and* keeps its log id, with each citing the other.
- For a methodology write-up, the log is the human-side record: the "found by" column with
  the finding in the human's words, dated, before the file that used it.

## 6. Two examples

A single-exchange entry, held:

```
[[LOG]]
what: I think adding up odd numbers always gives you a square.
connects: SQ1; example.py
how: SQ1 -- instance of
[[/LOG]]
```

An entry after several exchanges, that should change a definition's text:

```
[[LOG draft: DEFINITIONS.md D3]]
what: the objects that refuse to overstate are the ones with an empty section set, not the
      ones with a single free choice; every filter so far has thrown them away first
connects: section set; free choice; filter.py; D3
how: D3 -- contradicts (D3 says the degree grades every object; it grades the ones the
     filter kept)
because: the census in filter.out counts the objects it never graded
[[/LOG]]
```

The example project under `example/` runs the first of these: `example/message.txt` is the
message, and `example/walkthrough.out` shows the entry it produced and both connections
resolving against the index.
