#!/bin/sh
# Rebuild every git-tracked theory (staged contents are what the checker
# reads), refresh the manifest, and run the HOL-reference checks including
# the kernel check.  Exit status 0 means the staged tree is consistent.
# Usage: git add <files>; scripts/precommit.sh && git commit ...
set -e
cd "$(dirname "$0")/.."
git ls-files 'theories/*.v' | sed 's/\.v$/.vo/' | xargs dune build 2>&1 \
  | grep -E '^Error' -B3 && exit 1
python3 scripts/check-hol-refs.py --tracked --update-manifest >/dev/null
git add docs/HOL-THEOREM-MAP.json
python3 scripts/check-hol-refs.py --tracked --kernel
