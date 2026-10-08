#!/usr/bin/env python3
"""Byte-parity check of Galette's extracted compiler against the original.

Runs a compiler (by default Galette's extracted executable) as
`<compiler> --pancake --target=riscv < source.pnk` on every fixture of
Flapjack's small corpus (`../flapjack/scripts/parity-small-corpus.json`) and
compares the sha256 of stdout with the digest recorded from the original
CakeML executable (`cake`, sha256 recorded in
`../flapjack/scripts/guest-parity.json`).

  scripts/parity.py                      # all fixtures
  scripts/parity.py -k ffi               # fixtures whose path contains "ffi"
  scripts/parity.py --compiler ~/pancake-lean/cakeml/developers/bin/cake
                                         # sanity-check the oracle itself
  scripts/parity.py --diff FIXTURE --cake PATH
                                         # show a diff against the oracle
  scripts/parity.py --vs-cake prog.pnk ...
                                         # compare stdout and stderr with a
                                         # live run of the oracle (e.g. the
                                         # stateless-pancaketh guest programs)
"""
from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REFERENCE = Path(os.environ.get("FLAPJACK", ROOT.parent / "flapjack")).resolve()
MANIFEST = REFERENCE / "scripts" / "parity-small-corpus.json"
DEFAULT_COMPILER = ROOT / "_build" / "default" / "extraction" / "galette.exe"
DEFAULT_CAKE = Path.home() / "pancake-lean" / "cakeml" / "developers" / "bin" / "cake"


def compile_with(compiler: Path, source: Path, timeout: int) -> subprocess.CompletedProcess:
    with source.open("rb") as f:
        return subprocess.run([str(compiler), "--pancake", "--target=riscv"], stdin=f,
                              capture_output=True, timeout=timeout)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--compiler", type=Path, default=DEFAULT_COMPILER)
    ap.add_argument("-k", dest="filter", default="")
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--diff", metavar="FIXTURE", help="diff one fixture against --cake output")
    ap.add_argument("--cake", type=Path, default=DEFAULT_CAKE)
    ap.add_argument("--vs-cake", nargs="+", type=Path, metavar="PNK")
    args = ap.parse_args()

    if args.vs_cake:
        bad = 0
        for src in args.vs_cake:
            ours = compile_with(args.compiler, src, args.timeout)
            theirs = compile_with(args.cake, src, args.timeout)
            same = ours.stdout == theirs.stdout and ours.stderr == theirs.stderr
            bad += not same
            print(f"{'ok' if same else 'MISMATCH':10} {hashlib.sha256(ours.stdout).hexdigest()[:16]} "
                  f"{len(ours.stdout)} bytes  {src}")
        return 1 if bad else 0

    fixtures = json.loads(MANIFEST.read_text())["fixtures"]
    if args.diff:
        f = next(x for x in fixtures if args.diff in x["path"])
        src = REFERENCE / f["path"]
        ours = compile_with(args.compiler, src, args.timeout).stdout.decode(errors="replace")
        theirs = compile_with(args.cake, src, args.timeout).stdout.decode(errors="replace")
        sys.stdout.writelines(difflib.unified_diff(theirs.splitlines(True), ours.splitlines(True),
                                                   "cake", "galette", n=2))
        return 0

    ok = bad = 0
    for f in fixtures:
        if args.filter not in f["path"]:
            continue
        src = REFERENCE / f["path"]
        try:
            r = compile_with(args.compiler, src, args.timeout)
            digest = hashlib.sha256(r.stdout).hexdigest()
            status = "ok" if digest == f["cake_sha256"] else f"MISMATCH (exit {r.returncode})"
        except subprocess.TimeoutExpired:
            status = "TIMEOUT"
        if status == "ok":
            ok += 1
        else:
            bad += 1
        print(f"{status:24} {f['path']}")
    print(f"{ok} identical, {bad} different")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
