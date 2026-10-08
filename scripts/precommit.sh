#!/bin/sh
# Check exactly what would be committed: export the git index (staged
# contents) to a persistent shadow directory, rebuild every tracked theory
# there, refresh the manifest from it, and run the HOL-reference checks
# including the kernel check.  Work in progress in the working tree (for
# example other agents' edits) cannot affect the result.
# Usage: git add <files>; scripts/precommit.sh && git commit ...
set -e
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SHADOW="${GALETTE_SHADOW:-$ROOT/../.galette-index-build}"
FLAPJACK="${FLAPJACK:-$ROOT/../flapjack}"
NEW="$SHADOW.new"
rm -rf "$NEW"; mkdir -p "$NEW" "$SHADOW"
cd "$ROOT"
git checkout-index -a --prefix="$NEW/"
rsync -a --delete --checksum --exclude=_build "$NEW/" "$SHADOW/"
rm -rf "$NEW"
cd "$SHADOW"
LOG="$SHADOW/.precommit-build.log"
if ! find theories -name '*.v' | sed 's/\.v$/.vo/' | xargs dune build --root . >"$LOG" 2>&1; then
  # Errors, but also actions killed by a signal (e.g. a runaway proof
  # search), which print no "Error" line.
  grep -E '^Error|signal' -B3 "$LOG"
  echo "precommit: build failed (full log: $LOG)"
  exit 1
fi
FLAPJACK="$FLAPJACK" python3 scripts/check-hol-refs.py --update-manifest >/dev/null
cp docs/HOL-THEOREM-MAP.json "$ROOT/docs/HOL-THEOREM-MAP.json"
cd "$ROOT"; git add docs/HOL-THEOREM-MAP.json
cd "$SHADOW"
FLAPJACK="$FLAPJACK" python3 scripts/check-hol-refs.py --kernel
