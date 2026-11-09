"""
rollover.py -- a working document that grows without bound eventually cannot be carried.

WHY THIS EXISTS.  Nothing watches the size of the documents a project appends to every
cycle -- the case sheet, the state document, the transcript -- until the day one of them
can no longer be read whole, or the store that holds it refuses the next write.  By then
the document is cited by line from everywhere, and renaming or trimming it would break
every citation into it.

THE RULE.  A WORKING DOCUMENT is one that is appended to every cycle.  When it passes the
CAP it is FROZEN -- its name and its line count are kept exactly as they are, because
citations resolve into it by line -- and a successor opens, naming its predecessor in its
first lines.

THE CAP is 120 KB, about 30,000 tokens.  It is a constraint and not a measurement, and the
reason is stated rather than tuned: a document of that size costs about thirty thousand
tokens to read, which is more than any one turn should spend to find one row.  A cap that
is moved must be moved in this docstring, where the move is visible.

WHAT IT CHECKS.  Every `.md` in THE SPACE (config.space(): the directory holding the
`.discipline` marker, or the one given by DISCIPLINE_SPACE) and its immediate subfolders,
that is not itself frozen.  It does not walk the wider project: a source document nobody
appends to is not a working document, and freezing it would say nothing.  A frozen
document is one named in registers/FROZEN.md, which records its line count and byte count
at the moment it was frozen and the successor that opened.  The register is a SIDECAR and
not a marker inside the document, because citations resolve into these files by line: a
line added at the top of a frozen document to say it is closed would move every line every
citation names.  A row is a live document over the cap, or a frozen document whose line
count has moved.

WHAT IT DOES NOT CHECK.  Whether a successor was actually opened -- that is the author's
next move, and the row is what tells them to make it.

Rows, not counts.
"""
import sys, os
from pathlib import Path
import sys as _s, os as _o; _s.path.insert(0, _o.path.dirname(_o.path.abspath(__file__)))
import config

CAP = 120 * 1024
HEAD = 40
SKIP = {"RESULTS-INDEX.md", "discipline-report.md", "BASELINE.md", "PRIMITIVES-REGISTER.md"}


def register_path(start=None):
    return config.registers(start) / "FROZEN.md"


def frozen_names(start=None):
    """the documents the register says are frozen, with the line count each was frozen at."""
    out = {}
    reg = register_path(start)
    if not reg.is_file():
        return out
    for line in reg.read_text(errors="replace").split("\n"):
        line = line.strip()
        if not line or line.startswith("#") or line.startswith("|-"):
            continue
        parts = [x.strip() for x in line.strip("|").split("|")]
        if len(parts) >= 2 and parts[0].endswith(".md"):
            try:
                out[parts[0]] = int(parts[1])
            except ValueError:
                out[parts[0]] = None
    return out


def is_frozen(p, reg):
    return p.name in reg


def check(paths):
    start = paths[0] if paths else None
    roots = [config.space(start)]
    reg = frozen_names(start)
    seen, rows, moved = set(), [], []
    for root in roots or [Path(".")]:
        for p in sorted(root.glob("*.md")) + sorted(root.glob("*/*.md")):
            if p.name in SKIP or p in seen or config.skipped(p):
                continue
            seen.add(p)
            n = p.stat().st_size
            lines = len(p.read_text(errors="replace").split("\n"))
            if is_frozen(p, reg):
                was = reg.get(p.name)
                if was is not None and was != lines:
                    moved.append((p.name, was, lines))
                continue
            if n > CAP:
                rows.append((p.name, n, lines))
    for (name, n, lines) in rows:
        print("  over-cap           %-34s %8d bytes, %5d lines" % (name, n, lines))
        print("  %-18s   freeze it with its name and line count and open a successor"
              % "")
    for (name, was, now) in moved:
        print("  frozen-file-moved  %-34s frozen at %d lines, now %d" % (name, was, now))
        print("  %-18s   a citation into it by line no longer resolves where it did" % "")
    print("\n  rollover: %d live documents over the %d KB cap, %d frozen documents whose "
          "line count moved (%d .md examined, %d on the register)"
          % (len(rows), CAP // 1024, len(moved), len(seen), len(reg)))
    return rows + moved


if __name__ == "__main__":
    sys.exit(1 if check(sys.argv[1:] or ["."]) else 0)
