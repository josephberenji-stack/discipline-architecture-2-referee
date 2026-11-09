#!/bin/sh
# check.sh -- the whole of the author's obligation to the machinery.
#   sh check.sh FILE.py [FILE.py ...]
#
# Runs the ten file-level checks on the file(s) given and the two corpus-level checks
# (ledger, rollover) over the space, with any standing rows held by the baseline so that
# a NEW row is visible.  Exit status is the count of new rows (or of all rows when no
# baseline is on record).  The full report is written to discipline-report.md.
#
# THE SPACE is the directory holding this script (or DISCIPLINE_SPACE if set).  Roots a
# citation may resolve into are the space plus DISCIPLINE_ROOTS (colon-separated), if set.
# The registers live in $SPACE/registers unless DISCIPLINE_REGISTERS says otherwise.
# Known-absent correction numbers are held with LEDGER_BASELINE, e.g.
#   LEDGER_BASELINE=--baseline=2,3 sh check.sh FILE.py
set -e
DIR="$(cd "$(dirname "$0")" && pwd)"
SPACE="${DISCIPLINE_SPACE:-$DIR}"
[ $# -ge 1 ] || { echo "usage: sh check.sh <file.py> [...]" >&2; exit 2; }

export DISCIPLINE_SPACE="$SPACE"
REG="${DISCIPLINE_REGISTERS:-$SPACE/registers}"
NAMES=""
[ -f "$REG/NAMES.md" ] && NAMES="--names $REG/NAMES.md"

CORPUS="--corpus $SPACE"
if [ -n "$DISCIPLINE_ROOTS" ]; then
  OLDIFS="$IFS"; IFS=':'
  for r in $DISCIPLINE_ROOTS; do CORPUS="$CORPUS --corpus $r"; done
  IFS="$OLDIFS"
fi

cd "$SPACE"
python3 -m discipline.run "$@" $NAMES $CORPUS ${LEDGER_BASELINE:-}
