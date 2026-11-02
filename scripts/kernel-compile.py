#!/usr/bin/env python3
"""Run the Pancake compiler inside the Rocq kernel.

Writes a Rocq file that applies `compiler.compiler_main` (the definition the
extracted executable runs) to the given command-line arguments and Pancake
source, evaluates it with `vm_compute`, and prints the stdout and stderr
texts that the kernel computed. No extracted code is involved.

  scripts/kernel-compile.py --target=riscv prog.pnk > prog.S
  scripts/kernel-compile.py --target=arm8 prog.pnk
  scripts/kernel-compile.py --keep prog.v --target=riscv prog.pnk
                              # also keep the generated Rocq file

`--pancake` is added to the arguments. Requires a built `_build/default/theories`
(`dune build`). The exit code is 1 when the stderr text is an error message,
as for the executable.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
THEORIES = ROOT / "_build" / "default" / "theories"

TEMPLATE = """\
From Galette Require Import Base.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.compiler Require compiler.

Definition args : list mlstring := [{args}].

Definition src : string := "{src}"%hstring.

(** What the executable prints: the stdout chunks (concatenated) and the
    stderr text. *)
Definition result : mlstring * mlstring :=
  let '(out, err) := compiler.compiler_main args src in
  (concat (append out), err).

Eval vm_compute in result.
"""


def rocq_string(s: str) -> str:
    return s.replace('"', '""')


def parse_output(text: str) -> tuple[str, str]:
    """Extract the two strings of `= (strlit "...", strlit "...")`."""
    lits = []
    for m in re.finditer(r'strlit\s+(EMPTYSTRING|"((?:[^"]|"")*)")', text):
        lits.append("" if m.group(1) == "EMPTYSTRING" else m.group(2).replace('""', '"'))
    if len(lits) != 2:
        sys.exit(f"unexpected Rocq output:\n{text[:2000]}")
    return lits[0], lits[1]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--keep", type=Path, help="write the generated Rocq file here")
    ap.add_argument("source", type=Path, help="Pancake source file")
    args, compiler_args = ap.parse_known_args()

    src = args.source.read_bytes().decode("ascii")
    cl = ["--pancake"] + compiler_args
    v = TEMPLATE.format(args="; ".join(f'strlit "{rocq_string(a)}"%hstring' for a in cl),
                        src=rocq_string(src))
    with tempfile.TemporaryDirectory() as d:
        vfile = Path(d) / "KernelCompile.v"
        vfile.write_text(v)
        if args.keep:
            args.keep.write_text(v)
        r = subprocess.run(["rocq", "c", "-R", str(THEORIES), "Galette", str(vfile)],
                           capture_output=True, text=True)
    if r.returncode != 0:
        sys.stderr.write(r.stdout + r.stderr)
        return 2
    out, err = parse_output(r.stdout)
    sys.stdout.write(out)
    sys.stderr.write(err)
    if err.startswith("###"):
        sys.stderr.write("Program exited with nonzero exit code.\n")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
