# Galette

Galette is an in-progress Rocq port of the formally verified
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

    opam install rocq-prover   # Rocq 9.3
    dune build
    python3 scripts/check-hol-refs.py --kernel

## Dependencies

Only the Rocq standard library (`rocq-stdlib`) and, for extraction, OCaml
`zarith`. Carriers mirror HOL4's (see AGENTS.md), so HOL-shaped `words`,
`finite_map` and `sptree` theories are ported rather than taken from
bit-vector or finite-map libraries.

Libraries that may be added later: `coq-itree`/`coq-paco` for the
interaction-tree semantics, and `rocq-equations` (needs rocq-core 9.2) for
HOL-style well-founded definitions.

## Status

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
register allocation, assembler, RISC-V encoder, exporter) and tagged; see
`docs/HOL-THEOREM-MAP.json` for the per-declaration inventory and review
status (`pending_review` rows have not yet been compared line by line).

Plan, in order:

1. Semantics: Pancake (panSem), crep, loop, word, stack, lab, asm and
   target semantics, and the L3 RISC-V step function.
2. Correctness proofs, pass by pass, up to `pan_to_target_compile_semantics`.
3. Review: compare `pending_review` declarations with HOL and mark them
   `reviewed_exact`.
