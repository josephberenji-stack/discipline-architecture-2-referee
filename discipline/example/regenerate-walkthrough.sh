#!/bin/sh
# Regenerate walkthrough.out:  run the whole suite on this example in a scratch copy and record every output.
#   sh regenerate-walkthrough.sh > walkthrough.out
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
W=$(mktemp -d)
cp -r "$HERE"/. "$W/example"
cd "$W/example"
rm -f walkthrough.out regenerate-walkthrough.sh
cp -r "$HERE/../discipline" "$HERE"/../*.sh "$HERE/../registers" . && touch .discipline
echo "# walkthrough.out -- the portable discipline suite run end to end on this example project."
echo "# Reproduce: sh regenerate-walkthrough.sh > walkthrough.out  (it runs the commands below in a scratch copy)."
run() { echo "== $* =="; "$@" 2>&1; echo "   exit $?"; }
echo "== self-tests =="
for m in forced ground primitive cited reprleak; do echo "-- python3 -m discipline.$m --self"; out=$(python3 -m discipline.$m --self 2>&1); rc=$?; echo "$out" | tail -2; echo "   exit $rc"; done
run python3 example.py
run python3 broken.py
run sh check.sh example.py
run sh check.sh broken.py
echo "== discipline-report.md (the rows behind the two counts) =="; grep -E "^  (forced|ground|corpus|third|runtime|no-mirrors)" discipline-report.md
run sh reindex.sh
echo "== RESULTS-INDEX.md =="; cat RESULTS-INDEX.md
run python3 -m discipline.baseline --write
echo "-- registers/BASELINE.md"; cat registers/BASELINE.md
echo "== python3 -m discipline.run broken.py (rows split against the baseline) =="; python3 -m discipline.run broken.py 2>&1; echo "   exit $?"
run python3 -m discipline.log add message.txt
echo "-- registers/PROJECT-LOG.md"; cat registers/PROJECT-LOG.md
echo "== sh quickcheck.sh (files changed since the last full reindex) =="; sh quickcheck.sh 2>&1; echo "   exit $?"
run sh reindex.sh
run sh quickcheck.sh
echo "== sh mirror.sh (no mirror configured in registers/storage.cfg) =="; sh mirror.sh 2>&1; echo "   exit $?"
rm -rf "$W"
