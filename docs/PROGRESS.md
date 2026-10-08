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
| compiler/backend/semantics/wordConvsScript | definitions done; theorems partial |
| compiler/backend/semantics/stackSemScript, labSemScript | done (stackSem `evaluate_ind` not ported) |
| compiler/encoders/asm/asmSemScript, backend/semantics/targetSemScript | done |
| HOL L3 riscv model (Next, step) | done for what is ported (model, step) |

## Properties libraries

| HOL script | Status |
| --- | --- |
| pancake/semantics/panPropsScript, pan_commonPropsScript | partial |
| pancake/semantics/crepPropsScript, loopPropsScript | partial |
| backend/semantics/backendPropsScript | done |
| backend/semantics/wordPropsScript | partial (constant-field lemmas, wordProps/consts.v) |
| backend/semantics/stackPropsScript, labPropsScript | partial |
| backend/semantics/targetPropsScript | todo |
| encoders/asm/asmPropsScript | partial |

## Pass proofs

| HOL script | Status |
| --- | --- |
| pancake/proofs/pan_simpProof | partial |
| pancake/proofs/pan_structsProof, pan_globalsProof | todo |
| pancake/proofs/crep_arithProof, crep_inlineProof | partial |
| pancake/proofs/loop_callProof, loop_liveProof | todo |
| pancake/proofs/pan_to_crepProof | todo |
| pancake/proofs/crep_to_loopProof | todo |
| pancake/proofs/loop_to_wordProof, pan_to_wordProof | todo |
| backend/reg_alloc/parmoveScript theorems | done |
| backend/reg_alloc/proofs/reg_allocProof | done (`reg_alloc_correct`) |
| backend/reg_alloc/proofs/linear_scanProof | partial (intervals, allocator) |
| backend/proofs word_simp, word_inst, word_cse, word_copy, word_remove, word_unreach, word_depth, word_alloc, word_to_word | todo |
| backend/proofs stack_names (helpers; comp_correct todo), stack_rawcall | partial |
| backend/proofs word_to_stack, stack_alloc, stack_remove, stack_to_lab | todo |
| backend/proofs lab_filter (helpers; filter_correct todo) | partial |
| backend/proofs lab_to_target | todo |
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
