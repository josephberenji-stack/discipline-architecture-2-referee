"""
rowsplit.py -- a kill-check reports the rows that violate, and a witness.

WHY THIS EXISTS.  A count is believable in a way that the rows behind it are not.  A test
can pass on zero examinations because the keys it compares never collide; a filter can hide
the handful of rows that were the whole of the evidence; a check can compare a set with
itself and report no violations.  In every such case a count is printed and the count is
believable, and nothing on the page says what it was a count of.

TWO HALVES.

  1. An API for scripts.  killcheck(name, rows, violates, key=...) prints the violating
     rows (up to `show`), the first witness, the number examined, and REFUSES to report
     "0 violations" when 0 rows were examined -- it prints VACUOUS instead of PASS.

  2. A linter.  For each print() whose text matches "N of M" / "0 of" / "violations" /
     "failures" with no neighbouring print of a row or a witness within `window` lines, a
     row is reported: a count with nothing beside it.  This is a heuristic; it produces
     rows for a human, not a verdict.

Rows, not counts.
"""
import re, sys
from pathlib import Path

def killcheck(name, rows, violates, key=lambda r: r, show=5):
    examined = 0; bad = []
    for r in rows:
        examined += 1
        if violates(r):
            bad.append(r)
    if examined == 0:
        print(f"  {name}: VACUOUS -- 0 rows examined; a test that examines nothing cannot pass")
        return {"name": name, "examined": 0, "violations": None, "witness": None}
    print(f"  {name}: examined {examined}, violations {len(bad)}")
    for r in bad[:show]:
        print(f"      row  {key(r)}")
    if len(bad) > show:
        print(f"      ... {len(bad) - show} more")
    return {"name": name, "examined": examined, "violations": len(bad),
            "witness": key(bad[0]) if bad else None}

COUNT = re.compile(r"\b\d+\s+of\s+\d+\b|\bviolations?\b|\bfailures?\b|\b0 of\b", re.I)
ROWISH = re.compile(r"\bwitness\b|\brow\b|\bfor [a-z_]+ in\b|\bexample\b|\bpair\b", re.I)

def lint(paths, window=6):
    rows = []
    for p in paths:
        p = Path(p)
        files = [p] if p.is_file() else sorted(p.rglob("*.py"))
        for f in files:
            lines = f.read_text(errors="replace").splitlines()
            for i, line in enumerate(lines):
                if "print(" in line and COUNT.search(line):
                    ctx = "\n".join(lines[max(0, i - window): i + window])
                    if not ROWISH.search(ctx):
                        rows.append((str(f), i + 1, line.strip()[:100]))
    for f, i, line in rows:
        print(f"  count-without-rows  {f}:{i}  {line}")
    print(f"\n  rowsplit: {len(rows)} counts printed with no row or witness within {window} lines")
    return rows

if __name__ == "__main__":
    sys.exit(1 if lint(sys.argv[1:]) else 0)
