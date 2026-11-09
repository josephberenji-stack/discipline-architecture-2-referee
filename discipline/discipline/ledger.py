"""
ledger.py -- regenerate the consolidated correction ledger from the files.

WHY THIS EXISTS.  Corrections are numbered and recorded in place -- in the docstring of the
file where the error happened, naming the finder.  A consolidated table of them kept by
hand falls behind the in-place record and nobody notices, because the primary record
(the correction where it happened) survives while the secondary one (the table) does not.
The rule: the consolidated ledger is regenerated from the files, by search, not from
memory, and a number that no file carries is a gap.

SCOPE.  This check is CORPUS-LEVEL.  Run over a single file it finds that file's highest
number and calls every number below it a gap -- a finding about the invocation, not about
the file.  run.py routes it correctly and never hands it a bare file; if you invoke it by
hand, give it the roots where the numbering actually lives.

    --floor=N     ignore gaps below N (numbers spent before this project)
    --baseline=2,3,4,5,6,7
                  known-absent numbers, held so a NEW gap is visible
    --max=N       ignore numbers above N

Exit is non-zero only for gaps that are neither below the floor nor in the baseline.
Rows, not counts.
"""
import re, sys
from pathlib import Path

PAT = re.compile(r"(?:[Cc]orrection\s+#|#)(\d{1,3})\b")


def scan(paths, maxn=None):
    hits = {}
    for p in paths:
        p = Path(p)
        files = [p] if p.is_file() else sorted(f for f in p.rglob("*")
                                               if f.suffix in (".py", ".md", ".out", ".lean", ".v"))
        for f in files:
            try:
                text = f.read_text(errors="replace")
            except Exception:
                continue
            for i, line in enumerate(text.splitlines(), 1):
                for m in PAT.finditer(line):
                    n = int(m.group(1))
                    if n == 0 or (maxn and n > maxn):
                        continue
                    if line.lstrip().startswith("#") and "orrection" not in line and not re.search(r"#\d+", line):
                        continue
                    hits.setdefault(n, []).append((str(f), i, line.strip()[:110]))
    return hits


def main(argv):
    maxn = floor = None
    baseline = set()
    rest = []
    for a in argv:
        if a.startswith("--max="):
            maxn = int(a[6:])
        elif a.startswith("--floor="):
            floor = int(a[8:])
        elif a.startswith("--baseline="):
            baseline = {int(x) for x in re.findall(r"\d+", a)}
        else:
            rest.append(a)

    if len(rest) == 1 and Path(rest[0]).is_file():
        print("  ledger: SKIPPED -- corpus-level check handed a single file.")
        print("          give it the roots where the numbering lives, or use run.py --corpus.")
        return []

    hits = scan(rest, maxn)
    top = max(hits) if hits else 0
    lo = floor or 1
    print(f"  {'#':>4}  {'files':>5}  first occurrence")
    gaps, held = [], []
    for n in range(lo, (maxn or top) + 1):
        if n in hits:
            files = sorted({h[0].split('/')[-1] for h in hits[n]})
            first = hits[n][0]
            print(f"  {n:>4}  {len(files):>5}  {first[0].split('/')[-1]}:{first[1]}  {first[2]}")
        elif n in baseline:
            held.append(n)
        else:
            gaps.append(n)
            print(f"  {n:>4}  {'-':>5}  MISSING -- no file carries this number")
    tail = f"; {len(held)} held as baseline {held}" if held else ""
    print(f"\n  ledger: {len(hits)} numbers found, {len(gaps)} new gaps {gaps}{tail}")
    return gaps


if __name__ == "__main__":
    sys.exit(1 if main(sys.argv[1:]) else 0)
