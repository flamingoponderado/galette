(** * CakeML [word_to_stackProof]: correctness of [word_to_stack]

    A port of [compiler/backend/proofs/word_to_stackProofScript.sml], split
    along the script's own sections:
    - [word_to_stackProof/basic.v]: the [perf = F] instances of the stub
      and handler code and the list lemmas (HOL lines 1-700);
    - [word_to_stackProof/state_rel.v]: [abs_stack], [stack_rel],
      [state_rel] and the bitmap and sorting lemmas (HOL lines 700-1340);
    - [word_to_stackProof/gc.v]: [evaluate_wLive], the stack encodings
      and the simulation of [gc] and [alloc] (HOL lines 1339-2433);
    - [word_to_stackProof/stack_rel.v]: [push_locals], prefixes of the
      abstract stack and [stack_rel_raise] (HOL lines 2433-2796);
    - [word_to_stackProof/moves.v]: reading and writing variables through
      [state_rel], [wMoveSingle]/[wMoveAux], the parallel-move lemmas and
      [call_dest_lemma] (HOL lines 2856-3720);
    - [word_to_stackProof/inst.v]: [wRegWrite1]/[wRegWrite2], operand
      loads and result stores, [evaluate_wInst], [stack_move] and the
      handler push/pop lemmas (HOL lines 3720-5594);
    - [word_to_stackProof/comp_lemmas.v]: the lemmas stated between the
      cases of [comp_correct]: constant stores, shared memory, copying of
      results (HOL lines 5855-7767);
    - [word_to_stackProof/compile_props.v]: how [comp], [compile_prog] and
      [compile_word_to_stack] thread the bitmaps and code names (HOL lines
      2797-2856 and 5594-5717);
    - [word_to_stackProof/syntax.v]: the syntactic properties of the
      output used by [backendProof] and [pan_to_targetProof]: label
      preservation, the asm naming conventions, [alloc_arg], [reg_bound],
      [call_args], code and handler labels, [no_install], [no_shmemop]
      (HOL lines 10760-12411).

    Statement conventions: HOL [s with f := v] is [set_f v s]; HOL's tuples
    are right-nested pairs; HOL [EVERY] over [Prop] predicates uses [⌜P⌝]
    ([Classical.v]); HOL's [compile] result [(bytes, c, fs, p)] is
    [(bytes, (c, (fs, p)))]. *)

From Galette.cakeml.compiler.backend.proofs.word_to_stackProof Require Export
  basic compile_props state_rel gc stack_rel moves inst comp_lemmas syntax.
