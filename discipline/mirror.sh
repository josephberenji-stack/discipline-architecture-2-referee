#!/bin/sh
# mirror.sh -- copy every final file named by registers/storage.cfg (canonical = GLOB) into
# the configured mirror directory where the copy is missing or differs.  Never deletes.
DIR="$(cd "$(dirname "$0")" && pwd)"
export DISCIPLINE_SPACE="${DISCIPLINE_SPACE:-$DIR}"
cd "$DISCIPLINE_SPACE"
exec python3 -m discipline.storage mirror
