(** * CakeML [word_allocProof]: correctness of register allocation

    A port of [compiler/backend/proofs/word_allocProofScript.sml].  The
    script is split along its own sections into
    - [word_allocProof/colouring.v]: [colouring_ok], [word_state_eq_rel],
      [strong_locals_rel], the cutting and stack-frame lemmas and
      [evaluate_apply_colour] (HOL lines 1-2270);
    - [word_allocProof/clash.v]: the clash-tree lemmas
      ([clash_tree_colouring_ok], [get_forced] lemmas) and the
      allocator-agnostic part of [word_alloc_correct] (HOL lines
      2270-3479);
    - [word_allocProof/remove_dead.v]: [evaluate_remove_dead] (HOL lines
      3479-4506);
    - [word_allocProof/ssa_props.v], [ssa_loop.v], [ssa.v], [ssa_call.v],
      [ssa_full.v]: [ssa_locals_rel], the SSA renaming lemmas,
      [ssa_cc_trans_correct] and [full_ssa_cc_trans_correct] (HOL lines
      4506-10377);
    - [word_allocProof/conv.v]: the syntactic conventions (HOL lines
      10377-11484).

    Not ported:
    - the HOL code commented out in the script ([get_clash_sets] and its
      lemmas [colouring_ok_alt_def], [get_clash_sets_hd],
      [get_clash_sets_tl], [colouring_ok_alt_thm],
      [every_var_in_get_clash_set]; [stack_size_map_excp_const];
      [lookup_undir_g_insert_existing]);
    - [LET_FORALL_ELIM'] (a rewrite on HOL's [LET] constant, proof
      automation);
    - [list_rearrange_perm] is stated with Rocq's [Permutation] and is
      untagged (HOL's [sorting$PERM] is not ported).

    Pending: [select_reg_alloc_correct], [word_alloc_correct],
    [pre_post_conventions_word_alloc] and [word_alloc_full_inst_ok_less]
    need [linear_scanProof]'s [linear_scan_reg_alloc_correct], which is
    not ported yet; they are proved as the untagged
    [select_reg_alloc_correct_from], [word_alloc_correct_from] (in
    [clash.v]), [pre_post_conventions_word_alloc_from] and
    [word_alloc_full_inst_ok_less_from] (in [conv.v]), with that theorem's
    statement ([linear_scan_reg_alloc_correct_stmt]) as a hypothesis.

    Statement conventions: HOL [s with f := v] is [set_f v s]; HOL
    [let (a,b,c) = e in P] is [let '(a, (b, c)) := e in P]; HOL [EVERY]
    and [every_var] over [Prop] predicates use [⌜P⌝] ([Classical.v]) or
    the boolean comparisons [x <? n]; proofs are by structural induction
    on programs where HOL uses complete induction on [prog_size]. *)

From Galette.cakeml.compiler.backend.proofs.word_allocProof Require Export
  colouring clash remove_dead ssa_props ssa_loop ssa ssa_call ssa_full conv.
