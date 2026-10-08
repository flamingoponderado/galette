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

Ported so far (see `docs/HOL-THEOREM-MAP.json` for the per-declaration
inventory and review status):

- HOL foundations: `arithmetic`, `bit`, `sum_num`, `words` (n2w compute
  theorems), `list`, `option`, `pair`, `combin`.

Plan, in order:

1. HOL/CakeML foundations used by the compiler (finite maps, sptree,
   mlstring, misc, alignment, byte, integer_word, sorting, balanced_map,
   peg/pegexec, monadic state).
2. Compiler definitions along the pipeline of `compile_pancake_64`
   (parser, static checker, Pancake passes, word/stack/lab backend, RISC-V
   encoder and exporter), extracted to OCaml and checked for byte parity.
3. Semantics (Pancake to target, the L3 RISC-V model).
4. Correctness proofs, up to `pan_to_target_compile_semantics`.
