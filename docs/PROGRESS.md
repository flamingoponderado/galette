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
| HOL llist, lprefix_lub (subset) | partial (definitions used by semantics) |
| pancake/semantics/panSemScript | done except `mem_load_32_alt`, `mem_store_32_alt` |
| pancake/semantics/crepSemScript, loopSemScript | wip |
| compiler/backend/semantics/wordSemScript (+ wordConvs) | wip |
| compiler/backend/semantics/stackSemScript, labSemScript | wip |
| compiler/encoders/asm/asmSemScript, backend/semantics/targetSemScript | wip |
| HOL L3 riscv model (Next, step) | wip |

## Properties libraries

| HOL script | Status |
| --- | --- |
| pancake/semantics/panPropsScript, pan_commonPropsScript | wip |
| pancake/semantics/crepPropsScript, loopPropsScript | todo |
| backend/semantics/wordPropsScript, stackPropsScript, labPropsScript, targetPropsScript, backendPropsScript | todo |
| encoders/asm/asmPropsScript | todo |

## Pass proofs

| HOL script | Status |
| --- | --- |
| pancake/proofs/pan_simpProof, pan_structsProof, pan_globalsProof | wip |
| pancake/proofs/pan_to_crepProof, crep_arithProof, crep_inlineProof | todo |
| pancake/proofs/crep_to_loopProof, loop_callProof, loop_liveProof | todo |
| pancake/proofs/loop_to_wordProof, pan_to_wordProof | todo |
| backend/reg_alloc/proofs (reg_alloc, linear_scan, parmove) | wip |
| backend/proofs word_simp, word_inst, word_cse, word_copy, word_remove, word_unreach, word_depth, word_alloc, word_to_word | todo |
| backend/proofs word_to_stack, stack_alloc, stack_remove, stack_names, stack_rawcall, stack_to_lab | todo |
| backend/proofs lab_filter, lab_to_target | todo |
| encoders/riscv/proofs/riscv_targetProof | todo |
| backend/proofs/backendProof (Pancake-relevant part), wordConvsProof | todo |
| pancake/proofs/pan_to_targetProof | todo |
