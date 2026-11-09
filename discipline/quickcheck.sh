#!/bin/sh
# quickcheck.sh -- between full reindexes: has anything the index reads changed since the
# last full reindex, and is the mirror (if one is configured) an exact copy of the
# canonical files?  Exit 0: both current; 2: run sh reindex.sh; 3: run
# python3 -m discipline.storage mirror.  See discipline/storage.py.
DIR="$(cd "$(dirname "$0")" && pwd)"
export DISCIPLINE_SPACE="${DISCIPLINE_SPACE:-$DIR}"
cd "$DISCIPLINE_SPACE"
exec python3 -m discipline.storage quick
