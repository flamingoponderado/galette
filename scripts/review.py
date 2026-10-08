#!/usr/bin/env python3
"""Side-by-side review of HOL tags, and recording review verdicts.

  scripts/review.py show FILE.v [NAME]   # HOL declaration next to the Rocq one
  scripts/review.py mark FILE.v NAME... --status reviewed_exact --note "..."
  scripts/review.py todo [PREFIX]        # count pending_review rows per file

`mark` updates docs/HOL-THEOREM-MAP.json rows (matched by Rocq file and Rocq
declaration name).  A reviewed_exact verdict means: definitions, quantified
variables, hypotheses, side conditions, conclusions and carrier types were
compared with the HOL source (see AGENTS.md).
"""
from __future__ import annotations

import argparse
import collections
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "docs" / "HOL-THEOREM-MAP.json"
sys.path.insert(0, str(ROOT / "scripts"))
import importlib.util  # noqa: E402

_spec = importlib.util.spec_from_file_location("chk", ROOT / "scripts" / "check-hol-refs.py")
chk = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(chk)

END_HOL = re.compile(r"^(End|QED|Proof)\b")


def hol_block(path: Path, name: str, line: int | None) -> str:
    lines = path.read_text(errors="replace").splitlines()
    decl = chk.hol_declarations(path, {}).get(name, [])
    if not decl:
        return "(not found)"
    start = (line or decl[0]) - 1
    out = []
    for i in range(start, min(start + 60, len(lines))):
        if i > start and (END_HOL.match(lines[i]) or (lines[i].strip() == "" and len(out) > 3)):
            break
        out.append(lines[i])
    return "\n".join(out)


def rocq_block(path: Path, name: str) -> str:
    text = path.read_text()
    m = re.search(r"^[ \t]*(?:#\[[^\]]*\]\s*)*(?:Definition|Fixpoint|Inductive|Record|Theorem|Lemma|"
                  r"Abbreviation|Notation|Class|Instance)\s+" + re.escape(name) + r"\b", text, re.M)
    if not m:
        return "(not found)"
    rest = text[m.start():]
    end = re.search(r"\n(Proof\.|Qed\.|\(\*! HOL|\n\n)", rest)
    return rest[: end.start() if end else 1500]


def main() -> int:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("show"); s.add_argument("file"); s.add_argument("name", nargs="?")
    m = sub.add_parser("mark"); m.add_argument("file"); m.add_argument("names", nargs="+")
    m.add_argument("--status", required=True, choices=sorted(chk.STATUSES))
    m.add_argument("--note", required=True)
    t = sub.add_parser("todo"); t.add_argument("prefix", nargs="?", default="")
    args = ap.parse_args()
    rows = json.loads(MANIFEST.read_text())
    if args.cmd == "todo":
        c = collections.Counter(r.get("rocq_path") for r in rows
                                if r["status"] == "pending_review"
                                and (r.get("rocq_path") or "").startswith(args.prefix))
        for k, v in sorted(c.items(), key=lambda x: -x[1]):
            print(f"{v:5} {k}")
        return 0
    rel = str(Path(args.file).resolve().relative_to(ROOT))
    if args.cmd == "show":
        for r in rows:
            if r.get("rocq_path") != rel or (args.name and r.get("rocq_name") != args.name):
                continue
            print("=" * 78)
            print(f"{r['hol_name']}  [{r['status']}]  ->  {r['rocq_name']}")
            print("-- HOL " + "-" * 71)
            print(hol_block(chk.REFERENCE / r["hol_path"], r["hol_name"], r.get("hol_line")))
            print("-- Rocq " + "-" * 70)
            print(rocq_block(ROOT / rel, r["rocq_name"]))
        return 0
    n = 0
    for r in rows:
        if r.get("rocq_path") == rel and r.get("rocq_name") in args.names:
            r["status"], r["note"] = args.status, args.note
            n += 1
    MANIFEST.write_text(json.dumps(rows, indent=1) + "\n")
    print(f"marked {n} rows")
    return 0 if n == len(set(args.names)) else 1


if __name__ == "__main__":
    sys.exit(main())
