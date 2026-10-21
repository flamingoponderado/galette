# Galette

Galette is a Rocq port of the formally verified
[Pancake](https://cakeml.org) compiler (part of CakeML) and its correctness
theorems, for the RISC-V backend only. It is derived from CakeML and HOL4;
see `LICENSE` (CakeML's BSD-3-Clause license).

The reference is the HOL4 development, read from a checkout of
[Flapjack](https://github.com/flamingoponderado/flapjack) at `../flapjack`
(its `cakeml` and `HOL` submodules pin the exact CakeML and HOL4 revisions).
Flapjack's Lean port serves as a second opinion; HOL is authoritative.

Two properties are the point of the port:

1. **Same-looking statements and definitions**: every ported declaration is
   tagged with the HOL declaration it translates, and one HOL declaration
   has at most one translation (`scripts/check-hol-refs.py`).
2. **Same bytes**: the extracted compiler reproduces the output of
   `cake --pancake --target=riscv` byte for byte (the oracle digests are those
   recorded in Flapjack's parity fixtures).

Contributor conventions are in [AGENTS.md](AGENTS.md).

## Building

Requires dune 3.24 or later and Rocq 9.3.0 or later.
From the repository root:

    opam install . --deps-only
    opam install zarith        # for the extracted compiler
    dune build
    python3 scripts/check-hol-refs.py --kernel

The reference checkout at `../flapjack` is needed for the HOL-reference
checks and parity tests. The parity script also accepts its location through
`FLAPJACK`.

Galette is a public dune/opam package named `galette`. Install it locally
with `opam install .`; downstream dune projects can then depend on the
`Galette` theory via `(theories Galette)` in their `rocq.theory` stanza.

## Dependencies

Only the Rocq standard library (`rocq-stdlib`) and, for extraction, OCaml
`zarith`. Carriers mirror HOL4's (see AGENTS.md), so HOL-shaped `words`,
`finite_map` and `sptree` theories are ported rather than taken from
bit-vector or finite-map libraries.

## Status

**Correctness: the top-level theorem is proved.**
[`pan_to_target_compile_semantics`](theories/cakeml/pancake/proofs/pan_to_targetProof.v)
composes the Pancake and backend pass proofs through to target-machine
semantics. Its statement matches HOL clause for clause; under HOL's
well-formedness, configuration and initial-state hypotheses, it relates
compiled machine behavior to Pancake semantics, allowing the specified
resource-limit behavior. Its assumptions are only the classical logic,
choice and extensionality axioms in `theories/Base.v`.

The semantics and proofs needed by that theorem are ported, including
Pancake, crep, loop, word, stack, lab, assembly and target semantics, and the
needed L3 RISC-V model definitions. This does not mean every declaration in
every upstream library has been ported; see [the progress inventory](docs/PROGRESS.md)
for the remaining omissions.

**Compiler: complete and byte-identical on the parity corpus.** The
extracted executable (`dune build ./extraction/galette.exe`) reproduces the
original `cake --pancake --target=riscv` stdout byte for byte on all 166
fixtures of Flapjack's parity corpus:

    python3 scripts/parity.py          # 166 identical, 0 different

It is also byte-identical (stdout and stderr) on both builds of the
stateless-pancaketh guest program (about 5 MB of assembly each), checked
against a live run of the original executable:

    python3 scripts/parity.py --vs-cake Guest/guest.pp.pnk Guest/guest-software.pp.pnk

Run time on those is about 3-9x that of `cake` (44 s and 75 s against 5 s and
25 s). HOL's monadic arrays (lists in the logic) are extracted to persistent
arrays (`ml_monadBase.marray`, `extraction/galette_parray.ml`); without that
the register allocator is quadratic.

Every compiler definition on the `compile_pancake_64` path is ported from
HOL (parser, static checker, Pancake passes, word/stack/lab backend,
register allocation, assembler, RISC-V encoder, exporter) and tagged.

**Review: complete for all tagged declarations.** All 8,255 tags in
[`docs/HOL-THEOREM-MAP.json`](docs/HOL-THEOREM-MAP.json) have been compared
line by line with HOL: 8,030 are `reviewed_exact`, 225 are
`documented_mismatch`, and none are `pending_review`. Documented differences
are recorded in the manifest and the corresponding file headers.

Remaining work includes unported library declarations and a faithful port
of HOL's floating-point theories (`machine_ieee`/`binary_ieee`). The current
floating-point operations are `ARB` stand-ins shared by word, stack and
assembly semantics; Pancake never emits floating-point instructions.
