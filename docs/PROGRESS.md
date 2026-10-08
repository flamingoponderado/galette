# Progress towards `pan_to_target_compile_semantics`

The goal is the Rocq port of the Pancake compiler (RISC-V) together with its
top-level correctness theorem `pan_to_target_compile_semantics`
(`cakeml/pancake/proofs/pan_to_targetProofScript.sml`). This file tracks the
HOL scripts on that theorem's dependency path. Per-declaration status is in
`docs/HOL-THEOREM-MAP.json`.

Legend: **done** (all declarations needed by the chain ported), **partial**,
**wip** (in progress), **todo**.

## Compiler (definitions)

All definitions on the `compile_pancake_64` path: **done**, byte-identical to
`cake` on the 166-file corpus and on both stateless-pancaketh guest builds.

## Semantics

| HOL script | Status |
| --- | --- |
| semantics/ffi/ffiScript | done |
| HOL llist, lprefix_lub | done for what the proofs cite (LAPPEND, LPREFIX, lprefix_lub, build_lprefix_lub_thm, ...) |
| pancake/semantics/panSemScript | done |
| pancake/semantics/crepSemScript, loopSemScript | done (crep `eval_def` untagged: needs bitstring `v2w`) |
| compiler/backend/semantics/wordSemScript | done |
| compiler/backend/semantics/wordConvsScript | definitions done; theorems wip |
| compiler/backend/semantics/stackSemScript, labSemScript | wip |
| compiler/encoders/asm/asmSemScript, backend/semantics/targetSemScript | wip |
| HOL L3 riscv model (Next, step) | wip |

## Properties libraries

| HOL script | Status |
| --- | --- |
| pancake/semantics/panPropsScript, pan_commonPropsScript | wip |
| pancake/semantics/crepPropsScript, loopPropsScript | wip |
| backend/semantics/backendPropsScript | done |
| backend/semantics/wordPropsScript | wip |
| backend/semantics/stackPropsScript, labPropsScript, targetPropsScript | todo |
| encoders/asm/asmPropsScript | todo |

## Pass proofs

| HOL script | Status |
| --- | --- |
| pancake/proofs/pan_simpProof, pan_structsProof, pan_globalsProof | wip |
| pancake/proofs/crep_arithProof, crep_inlineProof, loop_callProof, loop_liveProof | wip |
| pancake/proofs/pan_to_crepProof | todo |
| pancake/proofs/crep_to_loopProof | todo |
| pancake/proofs/loop_to_wordProof, pan_to_wordProof | todo |
| backend/reg_alloc/proofs (reg_alloc, linear_scan, parmove) | wip |
| backend/proofs word_simp, word_inst, word_cse, word_copy, word_remove, word_unreach, word_depth, word_alloc, word_to_word | todo |
| backend/proofs word_to_stack, stack_alloc, stack_remove, stack_names, stack_rawcall, stack_to_lab | todo |
| backend/proofs lab_filter, lab_to_target | todo |
| encoders/riscv/proofs/riscv_targetProof | todo |
| backend/proofs/backendProof (Pancake-relevant part), wordConvsProof | todo |
| pancake/proofs/pan_to_targetProof | todo |

Axiom audit: the theorems checked so far depend only on the axioms declared
in `theories/Base.v` (excluded middle, choice, functional extensionality,
proof irrelevance), i.e. HOL's logic.

Known gap: floating-point operations (`machine_ieee`/`binary_ieee`) are
Galette stand-ins (`ARB`) shared by wordSem/stackSem/asmSem; Pancake never
emits FP instructions, but a faithful port of those HOL theories is still to
do.
