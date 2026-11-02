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
HOL4 to Rocq, for the RISC-V (RV64) backend only. The reference is the HOL4
source pinned by the Flapjack checkout (`../flapjack/cakeml`,
`../flapjack/HOL`). Other CakeML backends (x64, arm8, mips, ag32) and the
CakeML source-language compiler are out of scope.

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
- **Encoder.** `riscv_encoder_correct`
  (`theories/cakeml/compiler/encoders/riscv/proofs/riscv_targetProof.v`) is
  proved against the ported L3 RISC-V model.
- **Bookkeeping.** `scripts/check-hol-refs.py --kernel` checks that every
  `(*! HOL ... *)` tag cites an existing HOL declaration, that no HOL
  declaration has two translations, that every tag has a manifest row, and
  that every tagged Rocq name exists in the compiled library.
- **Review.** Every one of the 8,255 tagged declarations in
  `docs/HOL-THEOREM-MAP.json` has been compared with its HOL original:
  8,030 are `reviewed_exact` and 225 are `documented_mismatch`.
- **Parity.** The extracted compiler reproduces the stdout of
  `cake --pancake --target=riscv` byte for byte on the 166 programs of
  Flapjack's parity corpus (`scripts/parity.py`), and stdout and stderr on
  both builds of the stateless-pancaketh guest program
  (`scripts/parity.py --vs-cake`).

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

The 225 `documented_mismatch` rows each carry a note in the manifest and in
the file header. The main groups are:

- **Floating point.** HOL's `machine_ieee`/`binary_ieee` are not ported. The
  floating-point operations of word, stack and assembly semantics, and the
  floating-point instructions of the L3 RISC-V model (`dfn'FADD_D` and
  others), use `ARB` stand-ins for the IEEE-754 operations. Pancake never
  emits floating-point instructions, so the compiler and the top-level
  theorem do not depend on their values.
- **Unspecified HOL values.** Where HOL leaves a value unspecified
  (`word_sdiv`/`word_smod` with a zero divisor, `riscv_bop_i Sub`,
  `riscv_sh Ror`, the unset `get_fp_reg` field of `riscv_target`), Rocq
  fixes a value. Galette's `word_sdiv`/`word_smod` take `i / 0 = 0` and
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
  right-nested.

## Explicit limitations

1. **The theorem is about `compile_prog_max`, not the executable.**
   `pan_to_target_compile_semantics` is stated for any machine
   configuration `mc` and backend configuration `c` satisfying its
   hypotheses, and concerns the bytes returned by `compile_prog_max`. As in
   HOL, it says nothing directly about:
   - the parser and `compiler_main`/`compile_pancake_64`, which produce the
     `pan_code` the theorem quantifies over;
   - `riscv_export`, which renders the bytes as assembly text, together with
     its startup code and FFI stubs;
   - the assembler and linker that turn that text into a binary, and the
     loader that establishes the `pan_installed` premise.

   These are trusted.

2. **The RISC-V instantiation is not ported.** HOL's
   `riscv_configProofScript.sml` (`riscv_backend_config_ok`,
   `riscv_machine_config_ok`, `riscv_init_ok`) has no Galette counterpart.
   Galette therefore has no proof that the hypotheses of the top-level
   theorem can be met with `riscv_backend_config` and a RISC-V machine
   configuration; only the encoder half (`riscv_encoder_correct`) is
   proved. Until the instantiation exists, vacuity of the hypotheses is not
   excluded by a proof.

3. **Premises are not checked by the compiler.** The theorem requires,
   among others, `pancake_good_code`, distinct parameters and function
   names, a `main` function, and a source program that does not `Fail`.
   The compiler does not check all of these; for a program that violates
   them, the theorem says nothing.

4. **RISC-V semantics is the L3 model, not Sail.** The theorem is stated
   against Galette's port of the HOL4 L3 RISC-V model (`riscv_step`,
   `NextRISCV`), following CakeML. L3 and the authoritative Sail RISC-V model
   are known to differ (Flapjack's `docs/SOUNDNESS.md` lists the
   differences on the instructions the encoder emits: hint encodings,
   misaligned accesses, total vs. partial memory, CSR and privilege state).
   The separate project
   [galette-sail-riscv](https://github.com/flamingoponderado/galette-sail-riscv)
   is building an L3-to-Sail simulation in Rocq; it is work in progress, and
   the correctness theorem has not been transferred to Sail.

5. **The extracted executable has its own trusted base.** The compiler runs
   as OCaml extracted from Rocq. Trusted are: Rocq's extraction mechanism;
   the realisations in `extraction/Extract.v` (HOL `num`/`int` as Zarith
   integers, each claimed to agree with the Rocq definition on all
   arguments; HOL monadic arrays as persistent arrays,
   `extraction/galette_parray.ml`); the driver `extraction/galette.ml`;
   Zarith; and the OCaml compiler and runtime. `ARB` and `select` are
   extracted to a run-time failure, so reaching them aborts the compiler
   instead of producing output.

6. **Compiler-level deviations.** In `theories/cakeml/compiler/compiler.v`,
   `parse_target_64` accepts only `--target=riscv` (HOL's defaults to x64
   and also selects arm8 and mips); `full_compile_64` is replaced by
   `compiler_main`, which returns the stdout and stderr texts instead of
   operating on the basis library's file-system model; and
   `current_build_info_str` is Galette's own. These are untagged and
   documented in the file.

7. **Parity is tested, not proved.** Byte parity with `cake` is checked on a
   fixed corpus (166 programs and two guest builds). This does not
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
- a port of `riscv_configProofScript.sml`, showing that the theorem's
  hypotheses are satisfiable for the RISC-V configuration the compiler uses;
- a port of the floating-point theories in place of the `ARB` stand-ins;
- transfer of the correctness theorem from L3 to the Sail RISC-V model;
- differential testing against `cake` on a substantially larger and more
  representative corpus; and
- a verified or independently validated account of the parts outside the
  theorem: parser, assembly export, startup code, assembler and loader.
