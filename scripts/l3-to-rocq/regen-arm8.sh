#!/bin/bash
# Regenerate theories/HOL/examples/l3_machine_code/arm8/model/arm8.v from
# HOL's arm8Theory.  Needs a HOL4 build in which
# examples/l3-machine-code/arm8/model has been built (Holmake), at the
# revision pinned by ../flapjack/HOL:
#
#   HOLDIR=/path/to/HOL scripts/l3-to-rocq/regen-arm8.sh
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
ref=${FLAPJACK:-$root/../flapjack}
: "${HOLDIR:?set HOLDIR to a HOL4 build}"
export L3GEN=$here
export L3OUT=$(mktemp -d)
script=$ref/HOL/examples/l3-machine-code/arm8/model/arm8Script.sml
python3 "$here/l3-names.py" types "$script" > "$L3OUT/types.txt"
python3 "$here/l3-names.py" defs "$script" > "$L3OUT/defs.txt"
(cd "$HOLDIR/examples/l3-machine-code/arm8/model" && "$HOLDIR/bin/hol" < "$here/arm8.sml" > "$L3OUT/hol.log" 2>&1)
out=$root/theories/HOL/examples/l3_machine_code/arm8/model/arm8.v
cat "$here/arm8-head.v" "$L3OUT/arm8.v.body" > "$out"
python3 "$here/arm8-patch.py" "$out"
if grep -q 'FAILED' "$out"; then grep 'FAILED' "$out"; exit 1; fi
echo "wrote $out"
