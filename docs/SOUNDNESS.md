# Soundness status

This document records what Galette establishes and what it does not. It is
deliberately conservative: a theorem that the Rocq kernel accepts and a
compiler that reproduces `cake`'s output on a corpus are not, by themselves,
evidence that the port is equivalent to the HOL development or that compiled
programs behave correctly on real hardware.

The list is not exhaustive. Items are added as they are noticed, not as the
result of a complete audit.

## Scope

Galette ports the CakeML Pancake compiler and its correctness theorems from
HOL4 to Rocq, for two backends: RISC-V (RV64, `--target=riscv`) and ARMv8
(AArch64, `--target=arm8`). The reference is the HOL4 source pinned by the
Flapjack checkout (`../flapjack/cakeml`, `../flapjack/HOL`). Other CakeML
backends (x64, mips, ag32, and the ASL-based `arm8_asl` target) and the
CakeML source-language compiler are out of scope.

The two backends are not on the same footing. The top-level theorem is
generic in the target, and for both targets the encoder theorem is proved.
For neither target is the theorem instantiated with the concrete
configuration (limitation 2), and both machine models are L3 models rather
than the vendors' specifications (limitation 4).

## What is checked

- **Kernel.** Rocq checks every definition and proof in `theories/`
  (`dune build`). There is no `Admitted` in the tree.
- **Top-level theorem.** `pan_to_target_compile_semantics`
  (`theories/cakeml/pancake/proofs/pan_to_targetProof.v`) is proved. Its
  statement was compared clause by clause with HOL's. `Print Assumptions`
  lists only the axioms imported by `theories/Base.v`: excluded middle,
  constructive indefinite description (choice), functional and
  propositional extensionality, and proof irrelevance. These correspond to
  HOL's classical logic with choice and extensionality.
- **Encoders.** `riscv_encoder_correct`
  (`theories/cakeml/compiler/encoders/riscv/proofs/riscv_targetProof.v`) is
  proved against the ported L3 RISC-V model, and `arm8_encoder_correct`
  (`theories/cakeml/compiler/encoders/arm8/proofs/arm8_targetProof.v`)
  against the ported L3 ARMv8 model. Both have HOL's statements and use only
  the `Base.v` axioms. Both proofs are new Rocq proofs; they follow HOL's
  structure but are not line-by-line translations of HOL's tactics.
- **Bookkeeping.** `scripts/check-hol-refs.py --kernel` checks that every
  `(*! HOL ... *)` tag cites an existing HOL declaration, that no HOL
  declaration has two translations, that every tag has a manifest row, and
  that every tagged Rocq name exists in the compiled library.
- **Review.** Every one of the 8,455 tagged declarations in
  `docs/HOL-THEOREM-MAP.json` has been compared with its HOL original:
  8,228 are `reviewed_exact` and 227 are `documented_mismatch`.
- **Parity.** The extracted compiler reproduces the stdout of
  `cake --pancake --target=riscv` byte for byte on the 166 programs of
  Flapjack's parity corpus (`scripts/parity.py`, against recorded digests),
  and stdout and stderr on both builds of the stateless-pancaketh guest
  program (`scripts/parity.py --vs-cake`). For `--target=arm8` there are no
  recorded digests: the same 166 programs and both guest builds are
  compared with a live run of `cake` (stdout, stderr and exit code;
  `scripts/parity.py --target=arm8`), and the output on Flapjack's 15 ARMv8
  programs (`scripts/arm8/parity`) is compared with Flapjack's recorded
  `cake` output.

## HOL-to-Rocq trust boundary

A tag is a reviewed claim that a Rocq declaration is the HOL one; it is not
a proof. No theorem relates HOL terms to Rocq terms, and HOL's assurance
does not transfer to Galette automatically. Rocq proofs establish results
about the Rocq definitions in their statements, and those definitions must
be judged on their own.

The review itself was carried out by the authors of the port (largely AI
agents) and has not been repeated independently. A `reviewed_exact` row
means a reviewer compared the two texts and recorded a note; it does not
mean a second party checked that note.

HOL types are represented by fixed Rocq carriers (AGENTS.md): `num` as `N`,
`'a word` as an `N`-backed record, `'a set` as predicates, finite maps and
`spt` as ported HOL theories, `string` as `list ascii`. These carriers are
the standard reading of the HOL types, but their agreement with HOL is a
reviewed assumption, not a theorem.

The 227 `documented_mismatch` rows each carry a note in the manifest and in
the file header. The main groups are:

- **Floating point.** HOL's `machine_ieee`/`binary_ieee` are not ported. The
  floating-point operations of word, stack and assembly semantics, and the
  floating-point instructions of the L3 RISC-V model (`dfn'FADD_D` and
  others), use `ARB` stand-ins for the IEEE-754 operations. Pancake never
  emits floating-point instructions, so the compiler and the top-level
  theorem do not depend on their values.
- **Unspecified HOL values.** Where HOL leaves a value unspecified
  (`word_sdiv`/`word_smod` with a zero divisor, `riscv_bop_i Sub`,
  `riscv_sh Ror`, `arm8`'s `bop_enc Add`/`bop_enc Sub`, the unset
  `get_fp_reg` field of `riscv_target` and `arm8_target`), Rocq fixes a
  value or uses `ARB`. Galette's `word_sdiv`/`word_smod` take `i / 0 = 0` and
  `i mod 0 = i`.
- **Restricted or reshaped statements.** `backend_passes`' `any_prog` has
  only the `Word`, `Stack` and `Lab` constructors. Most `word_cseProof`
  lemmas depend on Galette's own invariant over the CSE map entries.
  Several `lab_to_targetProof` rows are case fragments of `compile_correct`
  whose hypotheses are normalised differently. Some `stack_allocProof` and
  `reg_allocProof` statements drop unused binders, some `wordConvs`
  predicates are `Prop`-valued instead of `bool`-valued, and HOL's local
  `word_cse` tests are proved at width 64 only.
- **Tuple nesting.** `riscv_proj` returns a left-nested tuple where HOL's is
  right-nested. (`arm8_proj` and the L3 ARMv8 model keep HOL's
  right-nested tuples.)

The L3 ARMv8 model (`theories/HOL/examples/l3_machine_code/arm8/model/arm8.v`,
about 1,600 lines) is not hand-translated: `scripts/l3-to-rocq` prints it
from the HOL terms of the built `arm8Theory`, and its output is checked in.
The printer is not verified; its output was reviewed definition by
definition against HOL's printed defining theorems, like any other tagged
file. Three recursive definitions are written by hand and only their
equations are tagged: `ByteList`, `Poly32Mod2_loop` (by recursion on a step
count) and `CountTrailing` (with `dimindex + 1` steps of fuel, which is
proved sufficient). HOL's `boolify32` (generated on demand by HOL's
`bitstringLib`) is an untagged helper.

## Explicit limitations

1. **The theorem is about `compile_prog_max`, not the executable.**
   `pan_to_target_compile_semantics` is stated for any machine
   configuration `mc` and backend configuration `c` satisfying its
   hypotheses, and concerns the bytes returned by `compile_prog_max`. As in
   HOL, it says nothing directly about:
   - the parser and `compiler_main`/`compile_pancake_64`, which produce the
     `pan_code` the theorem quantifies over;
   - `riscv_export` and `arm8_export`, which render the bytes as assembly
     text, together with their startup code and FFI stubs;
   - the assembler and linker that turn that text into a binary, and the
     loader that establishes the `pan_installed` premise.

   These are trusted.

2. **The target instantiations are not ported.** HOL's
   `riscv_configProofScript.sml` (`riscv_backend_config_ok`,
   `riscv_machine_config_ok`, `riscv_init_ok`) and
   `arm8_configProofScript.sml` (the ARMv8 counterparts) have no Galette
   counterpart. Galette therefore has no proof that the hypotheses of the
   top-level theorem can be met with `riscv_backend_config` or
   `arm8_backend_config` and a matching machine configuration; only the
   encoder halves (`riscv_encoder_correct`, `arm8_encoder_correct`) are
   proved. Until the instantiations exist, vacuity of the hypotheses is not
   excluded by a proof.

3. **Premises are not checked by the compiler.** The theorem requires,
   among others, `pancake_good_code`, distinct parameters and function
   names, a `main` function, and a source program that does not `Fail`.
   The compiler does not check all of these; for a program that violates
   them, the theorem says nothing.

4. **Machine semantics are L3 models, not the vendors' specifications.**
   Both theorems are stated against Galette's ports of HOL4's L3 models
   (`riscv_step`/`NextRISCV`, `arm8_step`/`NextStateARM8`), following
   CakeML. L3 models are hand-written specifications in Anthony Fox's L3
   language; they are not the architecture specifications the vendors or
   standards bodies maintain, and agreement with real hardware is not
   established by any theorem in Galette.

   - **RISC-V.** The authoritative formal model is the Sail RISC-V model
     (the RISC-V International golden model). L3 and Sail are known to
     differ (Flapjack's `docs/SOUNDNESS.md` lists the differences on the
     instructions the encoder emits: hint encodings, misaligned accesses,
     total vs. partial memory, CSR and privilege state). The separate
     project
     [galette-sail-riscv](https://github.com/flamingoponderado/galette-sail-riscv)
     is building an L3-to-Sail simulation in Rocq; it is work in progress,
     and the correctness theorem has not been transferred to Sail.
   - **ARMv8.** Arm's authoritative specification is its machine-readable
     ASL (Architecture Specification Language) description of the
     architecture. The L3 ARMv8 model covers part of A64: integer data
     processing, loads and stores, branches, CRC, and a few system, hint
     and barrier instructions. It has no SIMD or floating-point
     instructions, no address translation (memory is a total
     `word64 -> word8` map), no exception entry (a fault sets the
     `exception` field and `NextStateARM8` stops) and no interrupts. Like
     RISC-V's L3 model, it is total where hardware can fault or behave in
     implementation-defined ways.

     HOL goes further than Galette here. `HOL/examples/l3-machine-code/arm8/asl-equiv`
     proves, for each instruction form CakeML's encoder emits, that L3
     agrees with a Sail model generated from Arm's Armv8.6 ASL
     (`l3_models_asl`). The agreement is proved under restrictions on the
     ASL state: AArch64 only, no virtualisation host extension, memory
     tags all zero, identity address translation, and no L3 exception.
     CakeML's `arm8_asl` target uses that result to prove
     `arm8_asl_encoder_correct` against the ASL-derived model directly.
     None of this is ported: it needs the HOL snapshot of the Armv8.6 ASL
     model, which is not in Flapjack's checkout. Galette's ARMv8 theorem is
     therefore only as good as the L3 model, and the ASL agreement is HOL
     evidence about HOL's L3 model, not a Galette theorem.
   - **x86-64.** Galette has no x64 backend (`--target=x64` is rejected),
     so nothing in Galette depends on HOL's L3 x64 model. Were one added,
     the same caveat would apply in a stronger form: the L3 x64 model is a
     hand-written subset of x86-64 (it models undefined flags as unknown
     `option` values and memory as a total map), and there is no
     vendor-maintained formal specification of x86-64 to check it against;
     independent models such as ACL2's `x86isa` exist, but CakeML does not
     relate its L3 x64 model to any of them.

5. **The extracted executable has its own trusted base.** The compiler runs
   as OCaml extracted from Rocq. Trusted are: Rocq's extraction mechanism;
   the realisations in `extraction/Extract.v` (HOL `num`/`int` as Zarith
   integers, each claimed to agree with the Rocq definition on all
   arguments; HOL monadic arrays as persistent arrays,
   `extraction/galette_parray.ml`; `List.rev` as OCaml's `List.rev`); the driver `extraction/galette.ml`;
   Zarith; and the OCaml compiler and runtime. `ARB` and `select` are
   extracted to a run-time failure, so reaching them aborts the compiler
   instead of producing output.

6. **Compiler-level deviations.** In `theories/cakeml/compiler/compiler.v`,
   `parse_target_64` accepts only `--target=riscv` and `--target=arm8`
   (HOL's defaults to x64 and also selects mips); `full_compile_64` is replaced by
   `compiler_main`, which returns the stdout and stderr texts instead of
   operating on the basis library's file-system model; and
   `current_build_info_str` is Galette's own. These are untagged and
   documented in the file.

7. **Parity is tested, not proved.** Byte parity with `cake` is checked on a
   fixed corpus for each target (166 programs and two guest builds, plus
   15 ARMv8 programs). The ARMv8 comparison runs against a local build of
   `cake`; it is only as reliable as that build's agreement with HOL's
   compiler. This does not
   establish equal output for arbitrary Pancake programs. There is also no
   theorem relating the extracted compiler to the HOL compiler.

8. **Partial libraries.** Many HOL library theories are only partly ported
   (see `docs/PROGRESS.md`); some helper lemmas are proved but untagged. The
   ported parts are sufficient for the top-level theorem, but a HOL
   declaration that is not tagged has no Galette counterpart, even if a
   similar-looking Rocq lemma exists.

## Stack bounds and liveness

Compiler correctness does not unconditionally preserve source liveness on a
finite-memory machine. HOL's `pan_to_target_compile_semantics`, and
Galette's port of it, gives the exact source behaviour only when the
statically computed `stack_max` is known and strictly below the available
stack limit (`option_lt stack_max (SOME ...)`). `compile_prog_max` computes
the bound from frame sizes and the call graph; an unknown bound (`NONE`)
does not satisfy the condition.

Otherwise the conclusion is `extend_with_resource_limit'`: the machine may
stop with a resource-limit outcome after a prefix of the source's I/O
trace, even when the source program would continue or terminate normally.
Recursive programs whose stack use cannot be bounded statically may
therefore exhaust the stack. Galette keeps this condition as in HOL and does
not strengthen the theorem to exclude it.

## The correctness theorem cannot be summarized faithfully

The top-level theorem names every definition it depends on: the Pancake
semantics, every compiler pass, the backend configuration, the target
record, the L3 machine semantics and the memory-layout, FFI and resource
hypotheses. Reading the statement means following all of those
definitions.

No natural-language summary of it is accurate, including the ones in this
file, the README and commit messages. Each omits or simplifies something
that the kernel checks. Treat such summaries as pointers to the theorem, not
as the theorem. To know what Galette proves, read the Rocq statement, check
it with `Print Assumptions`, and follow the definitions it uses.

## Evidence needed for a stronger claim

- an independent review of the HOL-to-Rocq correspondence of the theorem
  statements and of the definitions they depend on;
- ports of `riscv_configProofScript.sml` and `arm8_configProofScript.sml`,
  showing that the theorem's hypotheses are satisfiable for the
  configurations the compiler uses;
- a port of the floating-point theories in place of the `ARB` stand-ins;
- transfer of the correctness theorem from L3 to the Sail RISC-V model, and
  a port of HOL's L3-to-ASL ARMv8 agreement (`asl-equiv`, `arm8_asl`);
- differential testing against `cake` on a substantially larger and more
  representative corpus; and
- a verified or independently validated account of the parts outside the
  theorem: parser, assembly export (`riscv_export`, `arm8_export`), startup code,
  assembler and loader.
