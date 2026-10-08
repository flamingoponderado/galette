#!/usr/bin/env python3
"""Check Galette's HOL cross-references.

Every Rocq declaration that ports a HOL4/CakeML declaration is immediately
preceded by a tag comment

    (*! HOL "cakeml/pancake/panLangScript.sml" "shape" *)

optionally followed by a source line (for a name declared twice in one
script) and/or a case name (for a theorem split along HOL's own case
structure):

    (*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "compile_correct" case "Skip" *)

Paths are relative to the reference checkout (default ../flapjack, override
with $FLAPJACK); `HOL/...` and `cakeml/...` are its two submodules.

Checks:
  1. the tag is followed by a Rocq declaration (its name is recorded);
  2. the HOL file exists and declares the cited name (at the cited line);
  3. the tag sits in the HOL script's counterpart file, or a file in the
     counterpart's directory (`theories/<dir>/<name>.v` or
     `theories/<dir>/<name>/*.v`);
  4. uniqueness: one HOL declaration has at most one main translation; case
     pieces are unique per case and require the main translation;
  5. docs/HOL-THEOREM-MAP.json has exactly one row per tag
     (`--update-manifest` adds missing rows as `pending_review` and drops
     stale ones);
  6. `--kernel` additionally compiles a file that `Check`s every tagged
     Rocq name, so a tag cannot refer to a declaration that does not exist.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
THEORIES = ROOT / "theories"
MANIFEST = ROOT / "docs" / "HOL-THEOREM-MAP.json"
REFERENCE = Path(os.environ.get("FLAPJACK", ROOT.parent / "flapjack")).resolve()

TAG_RE = re.compile(
    r'\(\*!\s*HOL\s+"([^"]+)"\s+"([^"]+)"(?:\s+(\d+))?(?:\s+case\s+"([^"]+)")?\s*\*\)')
ROCQ_DECL_RE = re.compile(
    r"^\s*(?:#\[[^\]]*\]\s*)*(?:(?:Local|Global|Program|Polymorphic|Monomorphic|Private)\s+)*"
    r"(Definition|Fixpoint|CoFixpoint|Function|Inductive|CoInductive|Variant|Record|"
    r"Structure|Class|Instance|Theorem|Lemma|Corollary|Proposition|Fact|Remark|"
    r"Example|Notation|Abbreviation|Axiom|Parameter|Equations)\s+([A-Za-z_][A-Za-z0-9_']*)")
STATUSES = {"pending_review", "reviewed_exact", "documented_mismatch"}

HOL_HEADER = re.compile(
    r"^(?:Theorem|Triviality|Definition|Datatype|Inductive|CoInductive|Overload|"
    r"Type|Quote)\s*:?\s*([A-Za-z0-9_']+)")
SML_VAL = re.compile(r"^val\s+(?:\(\s*)?([A-Za-z0-9_']+)\s*(?:,|=)")
DATATYPE_OPEN = re.compile(r"^Datatype\s*:?\s*$")
DATATYPE_INLINE = re.compile(r"^Datatype\s*:\s*([A-Za-z0-9_']+)\s*=")
DATATYPE_NAME = re.compile(r"^\s*([A-Za-z0-9_']+)\s*(=|$)")
END = re.compile(r"^End\b")
INDUCTIVE = re.compile(r"^(?:Co)?Inductive\s+([A-Za-z0-9_']+)\s*:")


def strip_sml_comments(text: str) -> str:
    """Blank out (nested) SML comments, keeping line breaks, so declarations
    that HOL has commented out are not counted."""
    out, depth, i, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("(*", i) and not text.startswith("(*)", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def hol_declarations(path: Path, cache: dict) -> dict[str, list[int]]:
    """Names declared by a HOL script, with their source lines."""
    if path in cache:
        return cache[path]
    names: dict[str, list[int]] = {}

    def add(name: str, line: int) -> None:
        names.setdefault(name, []).append(line)

    in_datatype = False
    expect_name = False
    for number, line in enumerate(strip_sml_comments(path.read_text(errors="replace")).splitlines(), 1):
        if in_datatype:
            if END.match(line):
                in_datatype = False
                continue
            # A datatype block declares one type per top-level `name = ...`
            # (or a bare `name` line followed by `= ...`).
            if expect_name or re.match(r"^\s*;", line) or re.match(r"^\s{0,4}[A-Za-z]", line):
                m = DATATYPE_NAME.match(line.lstrip(";").rstrip())
                if m and not re.match(r"^\s*\|", line):
                    add(m.group(1), number)
                    expect_name = False
            continue
        if DATATYPE_OPEN.match(line):
            in_datatype, expect_name = True, True
            continue
        m = DATATYPE_INLINE.match(line)
        if m:
            add(m.group(1), number)
            in_datatype, expect_name = True, False
            continue
        m = INDUCTIVE.match(line)
        if m:
            base = m.group(1)
            for suffix in ("", "_rules", "_ind", "_cases", "_strongind", "_def"):
                add(base + suffix, number)
            continue
        m = HOL_HEADER.match(line) or SML_VAL.match(line)
        if m:
            add(m.group(1), number)
            # `Definition foo_def:` also yields `foo` (the constant) and the
            # induction theorem `foo_ind` for recursive definitions.
            if line.startswith("Definition") and m.group(1).endswith("_def"):
                add(m.group(1)[:-4], number)
                add(m.group(1)[:-4] + "_ind", number)
    cache[path] = names
    return names


def counterpart(hol_path: str) -> Path:
    """`cakeml/pancake/panLangScript.sml` -> theories/cakeml/pancake/panLang.v."""
    p = Path(hol_path)
    stem = p.name
    for suffix in ("Script.sml", ".sml"):
        if stem.endswith(suffix):
            stem = stem[: -len(suffix)]
            break
    parts = [re.sub(r"[^A-Za-z0-9_]", "_", d) for d in p.parent.parts]
    return THEORIES.joinpath(*parts, stem + ".v")


def strip_comments(text: str) -> str:
    """Blank out ordinary comments (keeping `(*!` tags) so declarations after
    a tag are found even when a docstring sits in between."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i) and not (depth == 0 and text.startswith("(*!", i)):
            depth += 1
            out.append("  ")
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def module_of(v: Path) -> str:
    rel = v.relative_to(THEORIES).with_suffix("")
    return ".".join(("Galette",) + rel.parts)


def tracked_files() -> set[Path]:
    out = subprocess.run(["git", "-C", str(ROOT), "ls-files", "theories"],
                         capture_output=True, text=True, check=True).stdout
    return {ROOT / line for line in out.splitlines()}


def scan(exclude: str | None = None, tracked: bool = False) -> tuple[list[dict], list[str]]:
    tags, errors = [], []
    only = tracked_files() if tracked else None
    for v in sorted(THEORIES.rglob("*.v")):
        if only is not None and v not in only:
            continue
        if exclude and re.search(exclude, str(v.relative_to(ROOT))):
            continue
        # In --tracked mode read the staged (index) contents, so concurrent
        # uncommitted edits by others do not leak into the manifest.
        text = (subprocess.run(["git", "-C", str(ROOT), "show", ":" + str(v.relative_to(ROOT))],
                               capture_output=True, text=True, check=True).stdout
                if only is not None else v.read_text())
        clean = strip_comments(text)
        for m in TAG_RE.finditer(text):
            rest = clean[m.end():]
            # The declaration is the first non-blank line after the tag.
            decl = None
            for line in rest.splitlines():
                if not line.strip():
                    continue
                if TAG_RE.search(line):
                    break
                decl = ROCQ_DECL_RE.match(line)
                break
            lineno = text.count("\n", 0, m.start()) + 1
            where = f"{v.relative_to(ROOT)}:{lineno}"
            if not decl:
                errors.append(f"{where}: HOL tag is not followed by a Rocq declaration")
                continue
            tags.append({
                "hol_path": m.group(1), "hol_name": m.group(2),
                "hol_line": int(m.group(3)) if m.group(3) else None,
                "case": m.group(4), "rocq_path": str(v.relative_to(ROOT)),
                "rocq_module": module_of(v), "rocq_name": decl.group(2),
                "rocq_kind": decl.group(1), "where": where,
            })
    return tags, errors


def check(tags: list[dict]) -> list[str]:
    errors, cache = [], {}
    seen_main: dict[tuple, str] = {}
    seen_case: dict[tuple, str] = {}
    for t in tags:
        where, hp, hn, hl = t["where"], t["hol_path"], t["hol_name"], t["hol_line"]
        src = REFERENCE / hp
        if not (hp.startswith("HOL/") or hp.startswith("cakeml/")):
            errors.append(f"{where}: HOL path must start with HOL/ or cakeml/: {hp}")
            continue
        if not src.is_file():
            errors.append(f"{where}: no such HOL file {hp} under {REFERENCE}")
            continue
        lines = hol_declarations(src, cache).get(hn)
        if not lines:
            errors.append(f"{where}: {hp} does not declare `{hn}`")
            continue
        if hl is None and len(lines) > 1:
            errors.append(f"{where}: `{hn}` is declared {len(lines)} times in {hp} "
                          f"(lines {lines}); add the source line to the tag")
        if hl is not None and hl not in lines:
            errors.append(f"{where}: `{hn}` is not declared at {hp}:{hl} (lines {lines})")
        cp = counterpart(hp)
        here = ROOT / t["rocq_path"]
        if here != cp and here.parent != cp.with_suffix(""):
            errors.append(f"{where}: tag for {hp} must be in {cp.relative_to(ROOT)} "
                          f"or {cp.with_suffix('').relative_to(ROOT)}/")
        key = (hp, hn, hl)
        if t["case"] is None:
            if key in seen_main:
                errors.append(f"{where}: `{hn}` ({hp}) is already translated at "
                              f"{seen_main[key]}; one HOL declaration has one translation")
            seen_main[key] = where
        else:
            ckey = key + (t["case"],)
            if ckey in seen_case:
                errors.append(f"{where}: case `{t['case']}` of `{hn}` already at {seen_case[ckey]}")
            seen_case[ckey] = where
    for t in tags:
        if t["case"] is not None and (t["hol_path"], t["hol_name"], t["hol_line"]) not in seen_main:
            errors.append(f"{t['where']}: case piece of `{t['hol_name']}` has no assembling "
                          "main translation (untagged-case tag)")
    # Rocq names must be unique per module for the kernel check to be meaningful.
    by_name: dict[tuple, str] = {}
    for t in tags:
        k = (t["rocq_module"], t["rocq_name"])
        if k in by_name:
            errors.append(f"{t['where']}: Rocq declaration {t['rocq_name']} tagged twice "
                          f"(also {by_name[k]})")
        by_name[k] = t["where"]
    return errors


def row_key(r: dict) -> tuple:
    return (r["hol_path"], r["hol_name"], r.get("hol_line"), r.get("case"))


def check_manifest(tags: list[dict], update: bool) -> list[str]:
    rows = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else []
    by_key = {row_key(r): r for r in rows}
    errors, new_rows = [], []
    for t in tags:
        k = row_key(t)
        r = by_key.pop(k, None)
        if r is None:
            if not update:
                errors.append(f"{t['where']}: no manifest row for {k} "
                              "(run with --update-manifest)")
                continue
            r = {"hol_path": t["hol_path"], "hol_name": t["hol_name"],
                 "hol_line": t["hol_line"], "case": t["case"],
                 "status": "pending_review", "note": ""}
        if update:
            r["rocq_path"], r["rocq_name"] = t["rocq_path"], t["rocq_name"]
        elif (r.get("rocq_path"), r.get("rocq_name")) != (t["rocq_path"], t["rocq_name"]):
            errors.append(f"{t['where']}: manifest row for `{t['hol_name']}` names "
                          f"{r.get('rocq_path')}:{r.get('rocq_name')}")
        if r.get("status") not in STATUSES:
            errors.append(f"{t['where']}: manifest status {r.get('status')!r} not in {sorted(STATUSES)}")
        if r.get("status") == "reviewed_exact" and not r.get("note"):
            errors.append(f"{t['where']}: reviewed_exact row needs a reviewer note")
        new_rows.append(r)
    if by_key and not update:
        for k in by_key:
            errors.append(f"manifest row {k} has no tagged declaration")
    if update:
        new_rows.sort(key=lambda r: (r["hol_path"], r["hol_name"], r.get("hol_line") or 0,
                                     r.get("case") or ""))
        MANIFEST.write_text(json.dumps(new_rows, indent=1) + "\n")
    return errors


def kernel_check(tags: list[dict]) -> list[str]:
    out = ROOT / "_build" / "holref"
    out.mkdir(parents=True, exist_ok=True)
    mods = sorted({t["rocq_module"] for t in tags})
    body = [f"Require {m}." for m in mods]
    body += [f"Check @{t['rocq_module']}.{t['rocq_name']}." for t in tags
             if t["rocq_kind"] not in ("Notation", "Abbreviation")]
    f = out / "HolRefCheck.v"
    f.write_text("\n".join(body) + "\n")
    r = subprocess.run(["rocq", "c", "-Q", str(ROOT / "_build/default/theories"), "Galette",
                        str(f)], capture_output=True, text=True)
    return [] if r.returncode == 0 else ["kernel check failed:\n" + r.stdout + r.stderr]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--update-manifest", action="store_true")
    ap.add_argument("--kernel", action="store_true", help="also Check every tagged name")
    ap.add_argument("--mapping", action="store_true", help="print HOL -> Rocq mapping")
    ap.add_argument("--no-manifest", action="store_true",
                    help="skip the manifest check (for work in progress)")
    ap.add_argument("--tracked", action="store_true",
                    help="only git-tracked files (what a commit contains)")
    ap.add_argument("--exclude", metavar="REGEX",
                    help="ignore Rocq files whose path matches (work in progress)")
    ap.add_argument("--only", metavar="PREFIX",
                    help="report only errors for Rocq files under this path prefix")
    args = ap.parse_args()
    if not REFERENCE.is_dir():
        print(f"reference checkout not found: {REFERENCE}", file=sys.stderr)
        return 2
    tags, errors = scan(args.exclude, args.tracked)
    errors += check(tags)
    if not args.no_manifest:
        errors += check_manifest(tags, args.update_manifest)
    if args.only:
        errors = [e for e in errors if e.startswith(args.only)]
    if args.kernel and not errors:
        errors += kernel_check(tags)
    if args.mapping:
        for t in tags:
            case = f" [{t['case']}]" if t["case"] else ""
            print(f"{t['hol_path']}:{t['hol_name']}{case} -> {t['rocq_module']}.{t['rocq_name']}")
    for e in errors:
        print(e, file=sys.stderr)
    print(f"{len(tags)} HOL tags, {len(errors)} errors", file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
