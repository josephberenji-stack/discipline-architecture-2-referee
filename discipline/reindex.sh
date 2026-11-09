#!/bin/sh
# reindex.sh -- regenerate RESULTS-INDEX.md, then CHECK that every citation in it resolves
# to a real file and a real line.  One command, so the index is never hand-edited, never
# stale for an unrecorded reason, and never silently dangling.
#
# WHY THE CHECK EXISTS.  An index generated once and carried forward cites paths that have
# since moved, and nothing says so.  A requires-list is only as good as the citation
# resolving, so the resolution is checked by the same command that generates the index,
# and it prints the ROWS that fail, not a count of them.
#
# THE PARTS.  The space (the directory holding this script, or DISCIPLINE_SPACE) is always
# indexed.  Further roots come from DISCIPLINE_ROOTS (colon-separated).  Each row of the
# index is written relative to the part that holds it, under the part's name (the
# directory's basename), so a citation reads the same wherever this is run.
#
# EXCLUSIONS.  The index does not index itself, the report the runner writes, the baseline
# register, or anything under a directory the suite skips (discipline/config.py SKIP).
set -e
DIR="$(cd "$(dirname "$0")" && pwd)"
SPACE="${DISCIPLINE_SPACE:-$DIR}"
export DISCIPLINE_SPACE="$SPACE"

PARTS="$SPACE"
if [ -n "$DISCIPLINE_ROOTS" ]; then
  OLDIFS="$IFS"; IFS=':'
  for r in $DISCIPLINE_ROOTS; do PARTS="$PARTS $r"; done
  IFS="$OLDIFS"
fi

cd "$SPACE"
python3 -m discipline.index $PARTS > "$SPACE/RESULTS-INDEX.raw" 2>/dev/null

PARTS="$PARTS" SPACE="$SPACE" python3 - <<'PY'
import os, re, sys
parts = [p for p in os.environ["PARTS"].split() if p]
space = os.environ["SPACE"]
names = {}
for p in parts:
    p = os.path.abspath(p)
    names[p] = os.path.basename(p)
out = []
raw = open(os.path.join(space, "RESULTS-INDEX.raw"), errors="replace").read().splitlines()
head, body = raw[:3], raw[3:]
skip_names = ("RESULTS-INDEX.md", "RESULTS-INDEX.raw", "discipline-report.md", "BASELINE.md")
for l in body:
    if not l or l.startswith("#"):
        continue
    for p, name in sorted(names.items(), key=lambda kv: -len(kv[0])):
        if l.startswith(p + "/"):
            l = name + "/" + l[len(p) + 1:]
            break
    fn = l.split(":", 1)[0]
    if os.path.basename(fn) in skip_names:
        continue
    out.append(l)
open(os.path.join(space, "RESULTS-INDEX.md"), "w").write("\n".join(head + out) + "\n")
os.remove(os.path.join(space, "RESULTS-INDEX.raw"))

# resolution check
nl, bad = {}, []
for l in out:
    m = re.match(r"^(.*?):(\d+) \| ", l)
    if not m:
        bad.append("UNPARSED   " + l); continue
    cited, n = m.group(1), int(m.group(2))
    real = None
    for p, name in names.items():
        if cited.startswith(name + "/"):
            real = os.path.join(p, cited[len(name) + 1:]); break
    if real is None:            bad.append("UNMAPPED   " + l); continue
    if not os.path.isfile(real): bad.append("NO FILE    " + l); continue
    if real not in nl: nl[real] = sum(1 for _ in open(real, errors="replace"))
    if not 1 <= n <= nl[real]:  bad.append(f"PAST EOF ({nl[real]} lines)  " + l)
print(f"reindex: {len(out)} rows -> RESULTS-INDEX.md")
if bad:
    print("reindex: CITATIONS THAT DO NOT RESOLVE --")
    for l in bad: print("   " + l[:170])
    sys.exit(1)
print("reindex: every citation resolves to a real file and a real line.")
PY

python3 -m discipline.storage snapshot
