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
| backend/semantics/wordPropsScript | mostly done (stack_max section complete; see module headers for omissions) |
| backend/semantics/stackPropsScript, labPropsScript | done |
| backend/semantics/targetPropsScript | done except encoder_correct_(RTC_)asm_step_target_state_rel |
| encoders/asm/asmPropsScript | partial |

## Pass proofs

| HOL script | Status |
| --- | --- |
| pancake/proofs/pan_simpProof | done (compile_eval_correct_none is commented out in HOL) |
| pancake/proofs/pan_structsProof | done |
| pancake/proofs/pan_globalsProof | done |
| pancake/proofs/crep_arithProof | partial |
| pancake/proofs/crep_inlineProof | done (except `unreach_elim_prog_size`, stated with HOL `prog_size`) |
| pancake/proofs/loop_callProof, loop_liveProof | done |
| pancake/proofs/pan_to_crepProof | done |
| pancake/proofs/crep_to_loopProof | done (`state_rel_imp_semantics`) |
| pancake/proofs/loop_to_wordProof | done |
| pancake/proofs/pan_to_wordProof | done (`state_rel_imp_semantics`, syntactic lemmas for pan_to_target) |
| backend/reg_alloc/parmoveScript theorems | done |
| backend/reg_alloc/proofs/reg_allocProof | done (`reg_alloc_correct`) |
| backend/reg_alloc/proofs/linear_scanProof | partial (intervals, allocator) |
| backend/proofs word_simp, word_inst, word_remove, word_unreach | done (agent-reported; see file headers) |
| backend/proofs word_copy, wordConvsProof | done |
| backend/proofs word_cse | done except balanced_map invariant lemmas (wf_data / sem_inv over map entries; see header) |
| backend/proofs word_elim | skipped (not on the Pancake path; definitions unported) |
| backend/proofs word_depth | done |
| backend/proofs word_alloc | done (`word_alloc_correct`) |
| backend/proofs word_to_word | done (`word_to_word_compile_semantics`, `compile_to_word_conventions`) |
| backend/proofs stack_names, stack_rawcall | done |
| backend/proofs stack_remove | done (`compile_semantics`, `make_init_semantics`, asm_name) |
| backend/proofs stack_alloc | done (`compile_semantics`, `make_init_semantics`, GC code theorems) |
| backend/proofs stack_to_lab | partial (up to `flatten_semantics`; HOL line 3027 onward todo) |
| backend/proofs word_to_stack | todo |
| backend/proofs lab_filter | done |
| backend/proofs lab_to_target | todo |
| encoders/riscv/proofs/riscv_targetProof | done (`riscv_encoder_correct`; lem11/lem12 are ML-generated, see header) |
| backend/proofs/backendProof (Pancake-relevant part), wordConvsProof | todo |
| pancake/proofs/pan_to_targetProof | todo |

Axiom audit: the theorems checked so far depend only on the axioms declared
in `theories/Base.v` (excluded middle, choice, functional extensionality,
proof irrelevance), i.e. HOL's logic.

Known gap: floating-point operations (`machine_ieee`/`binary_ieee`) are
Galette stand-ins (`ARB`) shared by wordSem/stackSem/asmSem; Pancake never
emits FP instructions, but a faithful port of those HOL theories is still to
do.
