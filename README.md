# Galette

Galette is a Rocq port of the formally verified
[Pancake](https://cakeml.org) compiler (part of CakeML) and its correctness
theorems, for the RISC-V and ARMv8 (AArch64) backends. It is derived from
CakeML and HOL4, both under BSD-3-Clause licenses. `theories/cakeml/LICENSE`
is CakeML's license and covers the ports of CakeML theories under
`theories/cakeml`; `theories/HOL/LICENSE` is HOL4's (its `COPYRIGHT` file)
and covers the ports of HOL4 theories under `theories/HOL`. The rest of the
repository is under `LICENSE` (CakeML's license).

The reference is the HOL4 development, read from a checkout of
[Flapjack](https://github.com/flamingoponderado/flapjack) at `../flapjack`
(its `cakeml` and `HOL` submodules pin the exact CakeML and HOL4 revisions).
Flapjack's Lean port serves as a second opinion; HOL is authoritative.

Two properties are the point of the port:

1. **Same-looking statements and definitions**: every ported declaration is
   tagged with the HOL declaration it translates, and one HOL declaration
   has at most one translation (`scripts/check-hol-refs.py`).
2. **Same bytes**: the extracted compiler reproduces the output of
   `cake --pancake --target=riscv` and `cake --pancake --target=arm8` byte for
   byte (for RISC-V, the oracle digests are those recorded in Flapjack's
   parity fixtures; for ARMv8, a live run of `cake` and Flapjack's ARMv8
   goldens).

Contributor conventions are in [AGENTS.md](AGENTS.md). What the proofs and
tests do and do not establish is in [docs/SOUNDNESS.md](docs/SOUNDNESS.md).

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

Galette is a public dune/opam package named `rocq-galette`. Install it locally
with `opam install .`; downstream dune projects can then depend on the
`Galette` theory via `(theories Galette)` in their `rocq.theory` stanza.

## Usage

### Running the compiler from the command line

The compiler is extracted to OCaml and built as a standalone executable that
takes the same arguments as CakeML's `cake` and reads the Pancake source on
stdin:

    dune build ./extraction/galette.exe
    ./_build/default/extraction/galette.exe --pancake --target=riscv < prog.pnk > prog.S
    ./_build/default/extraction/galette.exe --pancake --target=arm8  < prog.pnk > prog.S

For example:

    printf 'fun 1 main() { return 7; }' \
      | ./_build/default/extraction/galette.exe --pancake --target=riscv > ret7.S

`--target=riscv` (RV64) or `--target=arm8` (AArch64) is required; x64 and
mips are rejected. Other `cake` options (`--help`, `--version`,
`--explore`, `--main_return=`, `--no_warn`, ...) behave as in `cake`.
Warnings go to stderr. On an error, the message (starting `###`) goes to
stderr and the exit code is 1.

The output is the same GNU assembler file `cake` writes (run through the C
preprocessor: a `.S` file). It defines `cml_main`, `cml_heap`, `cml_stack`
and the code buffer. As with `cake`'s output, it is linked with C code that
provides `main`, sets up the heap and stack and implements the program's FFI
functions (`ffi<name>`); CakeML's `basis/basis_ffi.c` shows the expected
interface.

### Running the compiler in the Rocq kernel

The compiler is a Rocq function, so it also runs inside Rocq itself, with
no extracted code involved. `compiler.compiler_main` is the definition that
the executable runs: it takes the command-line arguments and the source text
and returns the stdout chunks and the stderr text.

    From Galette Require Import Base.
    From Galette.HOL.src.string Require Import string.
    From Galette.cakeml.misc Require Import misc.
    From Galette.cakeml.basis.pure Require Import mlstring.
    From Galette.cakeml.compiler Require compiler.

    Definition src : string := "fun 1 main() { return 7; }"%hstring.

    Definition result : mlstring * mlstring :=
      let '(out, err) :=
        compiler.compiler_main [strlit "--pancake"; strlit "--target=riscv"] src in
      (concat (append out), err).

    Eval vm_compute in result.   (* (assembly text, stderr text) *)

Compile it against the built theories with
`rocq c -R _build/default/theories Galette File.v`, or put it in a dune
`rocq.theory` that depends on `Galette`. `scripts/kernel-compile.py` does
this for a source file and prints the result like the executable:

    python3 scripts/kernel-compile.py --target=riscv prog.pnk > prog.S

The kernel's output was byte-identical to the executable's on every program
tried (19 programs of up to 755 bytes of source, both targets). Each took
4-40 s, mostly Rocq start-up and loading the library. Use `vm_compute`
(or `native_compute`); `compute`/`cbv` are much slower. Larger programs
are slow: in the logic HOL's monadic arrays are lists, so the register
allocator is quadratic. A 17 KB program
(`secp256k1_recover.pnk`) did not finish in 15 minutes, and the
stateless-pancaketh guests are out of reach. The same evaluation can be used
in proofs, e.g. `vm_compute; reflexivity` to show that a given program
compiles to given bytes.

### Where the correctness theorem is

The top-level compiler correctness theorem is
[`pan_to_target_compile_semantics`](theories/cakeml/pancake/proofs/pan_to_targetProof.v)
(`Galette.cakeml.pancake.proofs.pan_to_targetProof`), the port of HOL's theorem
of the same name in `cakeml/pancake/proofs/pan_to_targetProofScript.sml`.
For any machine configuration `mc` and backend configuration `c`, if
`compile_prog_max c mc pan_code` returns `bytes` and the hypotheses hold
(well-formed source, a configuration satisfying `backend_config_ok` and
`mc_conf_ok`, and an initial machine state `ms` with `bytes` installed), then
every behaviour of the machine (`machine_sem mc ffi0 ms`) is a behaviour of
the source program (`panSem.semantics_decls`), possibly cut short by running
out of resources. It cannot be summarised fully; read the statement and the
definitions it uses. To check its axioms:

    From Galette.cakeml.pancake.proofs Require Import pan_to_targetProof.
    Print Assumptions pan_to_target_compile_semantics.

The encoder theorems that discharge its target-specific part are
`riscv_encoder_correct`
([`riscv_targetProof.v`](theories/cakeml/compiler/encoders/riscv/proofs/riscv_targetProof.v))
and `arm8_encoder_correct`
([`arm8_targetProof.v`](theories/cakeml/compiler/encoders/arm8/proofs/arm8_targetProof.v)).
As in HOL, the theorem is stated for `compile_prog_max` (defined in the same
file). It runs the Pancake-to-bytes passes and also returns the static stack
bound. It is not literally the function `compiler_main` calls
(`pan_to_target.compile_prog`, which also moves `main` first and records
function names for the output), and the parser, the assembly printer and the
command-line driver are outside it. [docs/SOUNDNESS.md](docs/SOUNDNESS.md)
lists this and the other limitations, e.g. that the theorem is not yet
instantiated with the concrete RISC-V or ARMv8 configuration.

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

Run time on those is about 2-3x that of `cake` (16 s and 43 s against 5 s
and 22 s). HOL's monadic arrays (lists in the logic) are extracted to
persistent arrays (`ml_monadBase.marray`, `extraction/galette_parray.ml`),
and `List.rev` (HOL's `REVERSE`) to OCaml's linear `List.rev`; without
these the register allocator is quadratic.

**ARMv8 compiler: byte-identical to `cake --pancake --target=arm8`.** The
ARMv8 backend (L3 `arm8` model generated from HOL's `arm8Theory` by
`scripts/l3-to-rocq`, `arm8_target` encoder, `arm8_config`, `export_arm8`)
matches a live run of `cake` (stdout, stderr and exit code) on all 166 corpus
programs and Flapjack's 15 ARMv8 goldens, and both guest builds:

    CAKE=PATH/cake python3 scripts/parity.py --target=arm8     # 181 identical
    python3 scripts/parity.py --target=arm8 --vs-cake Guest/guest.pp.pnk Guest/guest-software.pp.pnk

Run time on the guests is about 2-2.5x that of `cake` (92 s and 122 s
against 38 s and 62 s; ARMv8 uses the IRC allocator without spill-cost
heuristics, `reg_alg = 2`, which is slower than RISC-V's in both). The
encoder's correctness theorem `arm8_encoder_correct`
([`arm8_targetProof.v`](theories/cakeml/compiler/encoders/arm8/proofs/arm8_targetProof.v))
is proved with HOL's statement. As for RISC-V, `pan_to_target_compile_semantics`
is not instantiated for the concrete configuration (HOL's `arm8_configProof`
is not ported).

Every compiler definition on the `compile_pancake_64` path is ported from
HOL (parser, static checker, Pancake passes, word/stack/lab backend,
register allocation, assembler, RISC-V and ARMv8 encoders, exporters) and
tagged.

**Review: complete for all tagged declarations.** All 8,455 tags in
[`docs/HOL-THEOREM-MAP.json`](docs/HOL-THEOREM-MAP.json) have been compared
line by line with HOL: 8,228 are `reviewed_exact`, 227 are
`documented_mismatch`, and none are `pending_review`. Documented differences
are recorded in the manifest and the corresponding file headers.

Remaining work includes unported library declarations and a faithful port
of HOL's floating-point theories (`machine_ieee`/`binary_ieee`). The current
floating-point operations are `ARB` stand-ins shared by word, stack and
assembly semantics; Pancake never emits floating-point instructions.
