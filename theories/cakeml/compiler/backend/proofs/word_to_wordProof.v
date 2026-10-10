(** * CakeML [word_to_wordProof]: correctness of the wordLang pass pipeline

    A port of [cakeml/compiler/backend/proofs/word_to_wordProofScript.sml].

    Pending dependency: [word_allocProof]'s [word_alloc_correct],
    [pre_post_conventions_word_alloc] and [word_alloc_full_inst_ok_less]
    rest on [linear_scanProof]'s [linear_scan_reg_alloc_correct], which is
    not ported yet.  The theorems of this file that depend on them are
    proved as [_from] versions taking that theorem's statement
    ([linear_scan_reg_alloc_correct_stmt], [word_allocProof]) as a
    hypothesis, and are not tagged:
    [compile_single_lem_from], [compile_single_correct_from],
    [compile_word_to_word_thm_from], [compile_to_word_conventions_from],
    [no_install_no_alloc_compile_single_correct_from],
    [panLang_compile_word_to_word_thm_from] and
    [word_to_word_compile_semantics_from].  Apart from that hypothesis
    their statements are HOL's.  Nothing here depends on [word_elim]
    ([word_elimProof] is only an ancestor of the HOL theory); nothing is
    skipped.

    Statement conventions: HOL [s with <|f1 := v1; ...|>] is
    [set_f1 v1 (...)] (innermost update first); HOL [f ## g] and [f o g]
    are [f ## g] and [f ∘ g]; HOL [EVERY2] is [LIST_REL]; HOL [EVERY] over a
    [Prop] predicate uses [⌜P⌝]; HOL tuples nest to the right; HOL's free
    variables ([tt kk aa co] of [compile_single_correct], [start], ...) are
    quantified explicitly (or are section variables).  [word_to_word$compile]
    is [word_to_word.compile] and [Fail] is [ffi.Fail] (other modules use
    the same names).  [rm_perm] etc. keep HOL's names although they are
    [local] in HOL; [code_rel_P], [code_rel_no_alloc] and
    [code_rel_no_install] are HOL's derived local theorems, stated
    explicitly.  [cond16bit_inst_select_exp] (an ML [val]) is not separate.

    Proof method: [compile_single_correct] and
    [no_install_no_alloc_compile_single_correct] are proved by well-founded
    induction on [eval_lt] (HOL: complete induction on termdep, clock and
    [prog_size]) through the Galette-only [cs_main] and [ni_main], whose
    target state is [tgo cc l o s] (HOL's
    [s with <|code := l; compile_oracle := o; compile := cc|>]) and whose
    final-state relations are [srel] / [nrel] (HOL's conclusion).
    [word_to_word_compile_semantics] is proved by showing that for every
    clock the two runs have the same result and FFI state, instead of
    HOL's case analysis on [semantics]. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words byte.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.misc.misc Require Import fromList2.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang wordLang word_alloc
  word_simp word_inst word_cse word_copy word_unreach word_remove word_to_word.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem wordConvs.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import
  consts consts_with clock dec_clock code permute_swap stack_swap.
From Galette.cakeml.compiler.backend.proofs Require Import word_simpProof word_instProof word_cseProof
  word_copyProof word_unreachProof word_removeProof wordConvsProof word_allocProof.
Open Scope N_scope.

Section Single.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "FST_compile_single" *)
Theorem FST_compile_single : forall t k alg (c0 : asm_config a) (e : (N * (N * prog a)) * option (num_map N)),
  FST (compile_single t k alg c0 e) = FST (FST e).
Proof. intros t k alg c0 [[n [m p]] co]; reflexivity. Qed.

Lemma domain_fromList2_even {A} (l : list A) : domain (fromList2 l) = set (even_list (LENGTH l)).
Proof.
  unfold fromList2.
  assert (G : forall l0 i (t : num_map A),
    domain (snd (FOLDL (fun '(i, t) a0 => (i + 2, insert i a0 t)) (i, t) l0)) =
    (fun x => domain t x \/ exists k, k < LENGTH l0 /\ x = i + 2 * k)).
  { induction l0 as [|y l0 IH]; intros i t; cbn [FOLDL].
    - apply set_ext; intros x; cbn [snd LENGTH]. split; [auto|intros [H|(k & Hk & _)]; [exact H|lia]].
    - rewrite IH, domain_insert. apply set_ext; intros x. cbn [LENGTH]. split.
      + intros [[->|H]|(k & Hk & ->)].
        * right. exists 0. lia.
        * left. exact H.
        * right. exists (k + 1). lia.
      + intros [H|(k & Hk & ->)]; [left; right; exact H|].
        destruct (N.eq_dec k 0) as [->|Hk0]; [left; left; lia|].
        right. exists (k - 1). lia. }
  rewrite G. apply set_ext; intros x. unfold even_list. cbn. split.
  - intros [H|(k & Hk & ->)]; [contradiction|]. apply IN_set, In_GENLIST_iff. exists k; split; [exact Hk|lia].
  - intros H. apply IN_set, In_GENLIST_iff in H. destruct H as (k & Hk & ->). right. exists k. split; [exact Hk|lia].
Qed.

(** HOL's [compile_single_lem], with [linear_scanProof]'s
    [linear_scan_reg_alloc_correct] as a hypothesis (see the header). *)
Theorem compile_single_lem_from : linear_scan_reg_alloc_correct_stmt ->
  forall t k alg (c0 : asm_config a) name col (prog : prog a) n (st : state),
  domain (locals st) = set (even_list n) /\ gc_fun_const_ok (gc_fun st) ->
  exists perm',
    let '(res, rst) := evaluate (prog, set_permute perm' st) in
    let '(_, (_, cprog)) := compile_single t k alg c0 ((name, (n, prog)), col) in
    if bool_decide (res = SOME Error) then True else
    let '(res', rcst) := evaluate (cprog, st) in
    res = res' /\ word_state_eq_rel rst rcst /\
    match res with
    | NONE => True
    | SOME (Break _) => True
    | SOME (Continue _) => True
    | SOME _ => locals rst = locals rcst
    end.
Proof.
  intros Hlsc t k alg c0 name col prog n st [Hdom Hgc]. unfold compile_single. cbv zeta.
  set (p0 := word_simp.compile_exp prog).
  set (p1 := inst_select c0 (max_var p0 + 1) p0).
  set (p2 := full_ssa_cc_trans n p1).
  set (p3 := remove_dead_prog p2).
  set (p4 := copy_prop (word_common_subexp_elim p3)).
  set (p5 := three_to_two_reg_prog t p4).
  set (p6 := remove_unreach p5).
  set (p7 := remove_dead_prog p6).
  assert (Hfe2 : flat_exp_conventions p2)
    by (apply full_ssa_cc_trans_flat_exp_conventions, inst_select_flat_exp_conventions).
  assert (Hfe3 : flat_exp_conventions p3) by (apply (remove_dead_prog_conventions (fun _ => true) p2 c0 0), Hfe2).
  assert (Hfe6 : flat_exp_conventions p6).
  { apply flat_exp_conventions_remove_unreach, three_to_two_reg_prog_flat_exp_conventions,
      flat_exp_conventions_copy_prop, flat_exp_conventions_word_common_subexp_elim, Hfe3. }
  assert (Hdt4 : every_inst distinct_tar_reg p4).
  { apply every_inst_distinct_tar_reg_copy_prop, every_inst_distinct_tar_reg_word_common_subexp_elim.
    apply (remove_dead_prog_conventions distinct_tar_reg p2 c0 0), full_ssa_cc_trans_distinct_tar_reg. }
  assert (Hwc7 : wf_cutsets p7).
  { apply (remove_dead_prog_conventions (fun _ => true) p6 c0 0).
    apply wf_cutsets_remove_unreach, three_to_two_reg_prog_wf_cutsets, wf_cutsets_copy_prop,
      wf_cutsets_word_common_subexp_elim.
    apply (remove_dead_prog_conventions (fun _ => true) p2 c0 0), full_ssa_cc_trans_wf_cutsets. }
  assert (Hev : even_starting_locals (locals st)).
  { intros x Hx. rewrite Hdom in Hx. apply IN_set in Hx. apply (proj2 (even_list_props n)), Hx. }
  destruct (word_alloc_correct_from Hlsc name c0 alg p7 k col st (conj Hev Hwc7)) as [perm1 H7].
  destruct (full_ssa_cc_trans_correct p1 (set_permute perm1 st) n Hdom) as [perm2 H2].
  exists perm2.
  destruct (evaluate (prog, set_permute perm2 st)) as [res rst] eqn:E.
  destruct (bool_decide (res = SOME Error)) eqn:Eb; [trivial|].
  assert (Eerr : res <> SOME Error) by (intros H; apply (bool_decide_spec (res = SOME Error)) in H; congruence).
  pose proof (compile_exp_thm prog (set_permute perm2 st) res rst (conj E (conj Eerr Hgc))) as E0. fold p0 in E0.
  destruct (inst_select_thm c0 (max_var p0 + 1) p0 (set_permute perm2 st) res rst (locals st)) as [loc' [E1 Hl1]].
  { split; [exact E0|split; [|split; [exact Eerr|intros x _; reflexivity]]].
    apply (every_var_mono (fun x => x <=? max_var p0)). split; [|apply max_var_max].
    intros x Hx. unfold is_true in *. apply N.leb_le in Hx. apply N.ltb_lt. lia. }
  fold p1 in E1. change (set_locals (locals st) (set_permute perm2 st)) with (set_permute perm2 st) in E1.
  rewrite set_permute_set_permute, E1, Eb in H2. fold p2 in H2.
  set (sp1 := set_permute perm1 st) in *.
  destruct (evaluate (p2, sp1)) as [r2 s2] eqn:E2. destruct H2 as (<- & Hr2 & Hl2).
  destruct (evaluate_remove_dead_prog p2 sp1 s2 res (conj Hfe2 (conj E2 Eerr))) as [t3 [E3 Hl3]]. fold p3 in E3.
  pose proof (word_common_subexp_elim_correct p3 sp1 res _ (conj E3 (conj Hfe3 Eerr))) as E3'.
  assert (E4 : evaluate (p4, sp1) = (res, set_locals t3 s2)).
  { unfold p4. rewrite evaluate_copy_prop; [exact E3'|]. rewrite E3'. exact Eerr. }
  pose proof (evaluate_three_to_two_reg_prog p4 sp1 res _ t (conj E4 (conj Eerr Hdt4))) as E5. fold p5 in E5.
  pose proof (evaluate_remove_unreach p5 sp1 res _ (conj E5 Eerr)) as E6. fold p6 in E6.
  destruct (evaluate_remove_dead_prog p6 sp1 _ res (conj Hfe6 (conj E6 Eerr))) as [t7 [E7 Hl7]]. fold p7 in E7.
  rewrite E7, Eb in H7.
  destruct (evaluate (word_alloc name c0 alg k p7 col, st)) as [r8 s8] eqn:E8. destruct H7 as (<- & Hr8 & Hl8).
  split; [reflexivity|split].
  - apply (word_state_eq_rel_trans _ (set_locals loc' rst)); [unfold word_state_eq_rel; cbn; repeat split|].
    apply (word_state_eq_rel_trans _ s2); [exact Hr2|].
    apply (word_state_eq_rel_trans _ (set_locals t7 (set_locals t3 s2))); [unfold word_state_eq_rel; cbn; repeat split|exact Hr8].
  - destruct res as [[]|]; cbn in Hl1, Hl2, Hl3, Hl7, Hl8 |- *; auto; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "rm_perm" *)
Theorem rm_perm : forall (s : state), set_permute (permute s) s = s.
Proof. intros s; destruct s; reflexivity. Qed.

Lemma LENGTH_FRONT_succ {A} (l : list A) : l <> [] -> LENGTH (FRONT l) + 1 = LENGTH l.
Proof.
  induction l as [|x l IH]; [congruence|]. intros _. destruct l as [|y l]; [reflexivity|].
  cbn [FRONT LENGTH] in *. specialize (IH ltac:(discriminate)). cbn [LENGTH] in IH. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "find_code_thm" *)
Theorem find_code_thm : forall (st : state) (l : num_map (N * prog a)) o1 o' x args prog locsize,
  (forall n v, lookup n (code st) = SOME v ->
     exists t k alg (c0 : asm_config a) col,
       lookup n l = SOME (SND (compile_single t k alg c0 ((n, v), col)))) /\
  find_code o1 (add_ret_loc o' x) (code st) (state_stack_size st) = SOME (args, (prog, locsize)) ->
  exists t k alg (c0 : asm_config a) col n prog',
    SND (compile_single t k alg c0 ((n, (LENGTH args, prog)), col)) = (LENGTH args, prog') /\
    find_code o1 (add_ret_loc o' x) l (state_stack_size st) = SOME (args, (prog', locsize)).
Proof.
  intros st l o1 o' x args prog locsize [Hc Hf]. destruct o1 as [p|]; unfold find_code in *.
  - destruct (lookup p (code st)) as [[ar e]|] eqn:E; [|discriminate].
    destruct (LENGTH (add_ret_loc o' x) =? ar) eqn:El; [|discriminate]. injection Hf as <- <- <-.
    destruct (Hc _ _ E) as (t & k & alg & c0 & col & Hl). apply N.eqb_eq in El.
    exists t, k, alg, c0, col, p; eexists.
    rewrite <- El. split; [reflexivity|]. rewrite Hl. cbn. rewrite El, N.eqb_refl. reflexivity.
  - destruct (bool_decide (add_ret_loc o' x = [])) eqn:Eb; [discriminate|].
    destruct (LAST (add_ret_loc o' x)) as [w|loc n] eqn:Ela; [discriminate|].
    destruct (n =? 0); [|discriminate].
    destruct (lookup loc (code st)) as [[ar e]|] eqn:E; [|discriminate].
    destruct (LENGTH (add_ret_loc o' x) =? ar + 1) eqn:El; [|discriminate]. injection Hf as <- <- <-.
    destruct (Hc _ _ E) as (t & k & alg & c0 & col & Hl). apply N.eqb_eq in El.
    assert (Hne : add_ret_loc o' x <> []) by (intros H; assert (Hb : bool_decide (add_ret_loc o' x = []) = true) by (apply bool_decide_spec, H); congruence).
    assert (Hfl : LENGTH (FRONT (add_ret_loc o' x)) = ar) by (pose proof (LENGTH_FRONT_succ _ Hne); lia).
    exists t, k, alg, c0, col, loc; eexists.
    rewrite <- Hfl. split; [reflexivity|]. rewrite Hl. cbn. rewrite El, N.eqb_refl, Hfl. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "pop_env_termdep" *)
Theorem pop_env_termdep : forall (rst x : state), pop_env rst = SOME x -> termdep x = termdep rst.
Proof. intros rst x H. apply (pop_env_const _ _ H). Qed.

(** HOL: the [t k a c] parameters are existentially quantified per entry. *)
(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "code_rel_def" *)
Definition code_rel (stc ttc : num_map (N * prog a)) : Prop :=
  forall n v, lookup n stc = SOME v ->
    exists col t k alg (c0 : asm_config a),
      lookup n ttc = SOME (SND (compile_single t k alg c0 ((n, v), col))).

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_eta" *)
Theorem compile_single_eta : forall t k alg (c0 : asm_config a) p (x : N * prog a) y,
  compile_single t k alg c0 ((p, x), y) = (p, SND (compile_single t k alg c0 ((p, x), y))).
Proof. intros t k alg c0 p [m q] y; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "code_rel_union_fromAList" *)
Theorem code_rel_union_fromAList : forall t k alg (c0 : asm_config a) s l ls,
  code_rel s l /\ domain s = domain l ->
  code_rel (union s (fromAList ls))
    (union l (fromAList (MAP (fun p => compile_single t k alg c0 (p, NONE)) ls))).
Proof.
  intros t k alg c0 s l ls [Hc Hd] n v. rewrite !lookup_union, !lookup_fromAList.
  destruct (lookup n s) as [v'|] eqn:Es.
  - intros [= <-]. destruct (Hc _ _ Es) as (col & t' & k' & alg' & c' & Hl). rewrite Hl. eauto 6.
  - intros Ha. assert (Hln : lookup n l = NONE).
    { destruct (lookup n l) eqn:El; [|reflexivity].
      assert (Hdn : domain l n) by (apply domain_lookup; eauto). rewrite <- Hd in Hdn.
      apply domain_lookup in Hdn as [? Hx]. congruence. }
    rewrite Hln. exists NONE, t, k, alg, c0.
    replace (MAP (fun p => compile_single t k alg c0 (p, NONE)) ls)
      with (MAP (fun '(x, y) => (x, SND (compile_single t k alg c0 ((x, y), NONE)))) ls)
      by (apply map_ext; intros [x [y z]]; reflexivity).
    rewrite ALOOKUP_MAP_2, Ha. reflexivity.
Qed.

(** Galette-only corollaries for [compile_single_correct]. *)
Lemma find_code_rel (st : state) l o1 o' x args prog locsize :
  code_rel (code st) l ->
  find_code o1 (add_ret_loc o' x) (code st) (state_stack_size st) = SOME (args, (prog, locsize)) ->
  exists t k alg (c0 : asm_config a) col n prog',
    SND (compile_single t k alg c0 ((n, (LENGTH args, prog)), col)) = (LENGTH args, prog') /\
    find_code o1 (add_ret_loc o' x) l (state_stack_size st) = SOME (args, (prog', locsize)).
Proof.
  intros Hc Hf. apply (find_code_thm st l o1 o' x args prog locsize). split; [|exact Hf].
  intros n v E. destruct (Hc n v E) as (col & t & k & alg & c0 & H). exists t, k, alg, c0, col. exact H.
Qed.

Lemma wser_locals_perm (s t : state) :
  word_state_eq_rel s t -> locals s = locals t -> set_permute (permute t) s = t.
Proof.
  intros H Hl. apply word_state_eq_rel_iff in H.
  transitivity (set_permute (permute t) (set_locals (locals t) s)); [|symmetry; exact H].
  rewrite <- Hl. destruct s; reflexivity.
Qed.

End Single.

(** ** More on syntactic form restrictions *)
Section Syntax.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "code_rel_not_created_subprogs" *)
Theorem code_rel_not_created_subprogs : forall (P : prog a -> Prop) op (args : list (word_loc a)) c1 c2 sz v v',
  find_code op args c1 sz = SOME v /\ code_rel c1 c2 /\
  not_created_subprogs P (FST (SND v)) /\ find_code op args c2 sz = SOME v' ->
  not_created_subprogs P (FST (SND v')).
Proof.
  intros P op args c1 c2 sz v v' (H1 & Hc & Hp & H2).
  assert (G : forall p, lookup p c1 <> NONE -> forall ar e, lookup p c1 = SOME (ar, e) ->
            forall ar' e', lookup p c2 = SOME (ar', e') -> not_created_subprogs P e -> not_created_subprogs P e').
  { intros p _ ar e E1 ar' e' E2 Hn. destruct (Hc _ _ E1) as (col & t & k & alg & c0 & E3). rewrite E2 in E3.
    pose proof (compile_single_not_created_subprogs P t k alg c0 ((p, (ar, e)), col) Hn) as Hn'.
    injection E3 as -> ->. exact Hn'. }
  destruct op as [p|]; unfold find_code in H1, H2.
  - destruct (lookup p c1) as [[ar e]|] eqn:E1; [|discriminate].
    destruct (lookup p c2) as [[ar' e']|] eqn:E2; [|discriminate].
    destruct (_ =? ar); [|discriminate]. destruct (_ =? ar'); [|discriminate].
    injection H1 as <-. injection H2 as <-. cbn [FST SND] in *. apply (G p ltac:(congruence) ar e E1 ar' e' E2 Hp).
  - destruct (bool_decide (args = [])); [discriminate|].
    destruct (LAST args) as [|loc n]; [discriminate|]. destruct (n =? 0); [|discriminate].
    destruct (lookup loc c1) as [[ar e]|] eqn:E1; [|discriminate].
    destruct (lookup loc c2) as [[ar' e']|] eqn:E2; [|discriminate].
    destruct (_ =? ar + 1); [|discriminate]. destruct (_ =? ar' + 1); [|discriminate].
    injection H1 as <-. injection H2 as <-. cbn [FST SND] in *. apply (G loc ltac:(congruence) ar e E1 ar' e' E2 Hp).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "code_rel_P" *)
Theorem code_rel_P : forall (P : prog a -> Prop) op (args : list (word_loc a)) c1 c2 sz v v',
  find_code op args c1 sz = SOME v /\ code_rel c1 c2 /\
  not_created_subprogs P (FST (SND v)) /\ find_code op args c2 sz = SOME v' ->
  not_created_subprogs P (FST (SND v')).
Proof. exact code_rel_not_created_subprogs. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "code_rel_no_alloc" *)
Theorem code_rel_no_alloc : forall op (args : list (word_loc a)) c1 c2 sz v v',
  find_code op args c1 sz = SOME v /\ code_rel c1 c2 /\
  no_alloc (FST (SND v)) /\ find_code op args c2 sz = SOME v' ->
  no_alloc (FST (SND v')).
Proof. intros. eapply code_rel_not_created_subprogs; eauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "code_rel_no_install" *)
Theorem code_rel_no_install : forall op (args : list (word_loc a)) c1 c2 sz v v',
  find_code op args c1 sz = SOME v /\ code_rel c1 c2 /\
  no_install (FST (SND v)) /\ find_code op args c2 sz = SOME v' ->
  no_install (FST (SND v')).
Proof. intros. eapply code_rel_not_created_subprogs; eauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "code_rel_no_share_inst" *)
Theorem code_rel_no_share_inst : forall op (args : list (word_loc a)) c1 c2 sz v v',
  find_code op args c1 sz = SOME v /\ code_rel c1 c2 /\
  no_share_inst (FST (SND v)) /\ find_code op args c2 sz = SOME v' ->
  no_share_inst (FST (SND v')).
Proof. intros. eapply code_rel_not_created_subprogs; eauto. Qed.

End Syntax.

(** ** More on [no_mt]; [code_rel_ext] *)
Section NoMT.
Context {a : N}.

Lemma LENGTH_next_n_oracle n (col : list (option (num_map N))) : LENGTH (fst (next_n_oracle n col)) = n.
Proof.
  unfold next_n_oracle. destruct (n <=? LENGTH col) eqn:E; cbn [fst].
  - apply N.leb_le in E. apply LENGTH_TAKE_le, E.
  - apply LENGTH_REPLICATE.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "no_mt_remove_must_terminate_const" *)
Theorem no_mt_remove_must_terminate_const : forall (prog : prog a),
  no_mt prog -> remove_must_terminate prog = prog.
Proof.
  unfold no_mt. intros p; induction p using prog_nested_ind; intros Hp;
    cbn [remove_must_terminate not_created_subprogs] in *; try reflexivity.
  - destruct Hp as [Hp _]. exfalso; apply Hp; reflexivity.
  - destruct ret as [[r1 [r2 [r3 [r4 r5]]]]|], h as [[h1 [h2 [h3 h4]]]|]; cbn [not_created_subprogs] in *;
      destr_conj; repeat match goal with H : _ -> _ |- _ => specialize (H ltac:(assumption)) end; congruence.
  - destruct Hp as [H1 H2]. rewrite IHp1, IHp2 by assumption. reflexivity.
  - destruct Hp as [H1 H2]. rewrite IHp1, IHp2 by assumption. reflexivity.
  - rewrite IHp by assumption. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "no_mt_full_compile_single" *)
Theorem no_mt_full_compile_single : forall tt kk aa (c : asm_config a) (x : (N * (N * prog a)) * option (num_map N)),
  no_mt (SND (SND (FST x))) ->
  full_compile_single tt kk aa c x = compile_single tt kk aa c x.
Proof.
  intros tt kk aa c [[n [m p]] col] H.
  pose proof (compile_single_not_created_subprogs _ tt kk aa c ((n, (m, p)), col) H) as H1.
  unfold full_compile_single. destruct (compile_single tt kk aa c ((n, (m, p)), col)) as [n' [m' p']].
  cbn [SND] in H1. rewrite no_mt_remove_must_terminate_const by exact H1. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "no_mt_code_full_compile_single" *)
Theorem no_mt_code_full_compile_single : forall tt kk aa (co : asm_config a) (progs : list (N * (N * prog a))) x,
  no_mt_code (fromAList progs) /\ ALL_DISTINCT (MAP FST progs) /\ LENGTH x = LENGTH progs ->
  MAP (full_compile_single tt kk aa co) (ZIP (progs, x)) =
  MAP (compile_single tt kk aa co) (ZIP (progs, x)).
Proof.
  intros tt kk aa co progs; induction progs as [|[n [m p]] progs IH]; intros x (Hm & Hd & Hl).
  - reflexivity.
  - destruct x as [|col x]; [cbn in Hl; lia|]. rewrite (proj2 (proj2 ZIP_eqns)). cbn [MAP].
    cbn [MAP FST ALL_DISTINCT] in Hd. apply andb_prop in Hd as [Hn Hd].
    f_equal.
    + apply no_mt_full_compile_single. cbn [FST SND].
      apply (Hm n m p). rewrite lookup_fromAList. cbn [ALOOKUP]. destruct (decide (n = n)); [reflexivity|congruence].
    + apply IH. split; [|split; [exact Hd|cbn [LENGTH] in Hl; lia]].
      intros k m' p' E. apply (Hm k m' p'). rewrite lookup_fromAList in *. cbn [ALOOKUP].
      destruct (decide (n = k)) as [->|]; [|exact E].
      exfalso. assert (Hin : In k (MAP fst progs)).
      { clear -E. induction progs as [|[k' v'] progs IH]; cbn in E; [discriminate|].
        destruct (decide (k' = k)) as [->|]; [left; reflexivity|right; apply IH, E]. }
      rewrite <- MEM_In in Hin. unfold is_true in *. rewrite Hin in Hn. discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "code_rel_ext_def" 2144 *)
Definition code_rel_ext (code l : num_map (N * prog a)) : Prop :=
  forall n p_1 p_2, SOME (p_1, p_2) = lookup n code ->
    exists t' k' a' (c' : asm_config a) col,
      SOME (SND (full_compile_single t' k' a' c' ((n, (p_1, p_2)), col))) = lookup n l.

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "code_rel_ext_word_to_word" *)
Theorem code_rel_ext_word_to_word : forall (code : list (N * (N * prog a))) c1 (c2 : asm_config a) col code',
  word_to_word.compile c1 c2 code = (col, code') ->
  code_rel_ext (fromAList code) (fromAList code').
Proof.
  intros code c1 c2 col code' H. unfold word_to_word.compile in H. cbv zeta in H.
  pose proof (LENGTH_next_n_oracle (LENGTH code) (col_oracle c1)) as Hl.
  destruct (next_n_oracle (LENGTH code) (col_oracle c1)) as [orc col0]. cbn [fst] in Hl.
  injection H as _ <-.
  set (f := full_compile_single (two_reg_arith c2) (reg_count c2 - (5 + LENGTH (avoid_regs c2))) (reg_alg c1) c2).
  assert (G : forall code0 orc0, LENGTH orc0 = LENGTH code0 -> forall n p1 p2, ALOOKUP code0 n = SOME (p1, p2) ->
            exists colx, ALOOKUP (MAP f (ZIP (code0, orc0))) n = SOME (SND (f ((n, (p1, p2)), colx)))).
  { induction code0 as [|[n0 [m0 q0]] code0 IH]; intros orc0 Hl0 n p1 p2 E; [discriminate|].
    destruct orc0 as [|c0 orc0]; [cbn in Hl0; lia|]. rewrite (proj2 (proj2 ZIP_eqns)). cbn [MAP].
    cbn [ALOOKUP] in E. unfold f at 1. unfold full_compile_single at 1, compile_single at 1. cbv zeta. cbn [ALOOKUP].
    destruct (decide (n0 = n)) as [->|Hne].
    - injection E as <- <-. exists c0. reflexivity.
    - apply (IH orc0 ltac:(cbn [LENGTH] in Hl0; lia) n p1 p2 E). }
  intros n p1 p2 E. rewrite lookup_fromAList in E. symmetry in E.
  destruct (G code orc Hl n p1 p2 E) as [colx Hx]. exists (two_reg_arith c2), (reg_count c2 - (5 + LENGTH (avoid_regs c2))),
    (reg_alg c1), c2, colx. unfold f in Hx. rewrite lookup_fromAList. symmetry. exact Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "no_mt_code_rel_ext" *)
Theorem no_mt_code_rel_ext : forall (cd1 cd2 : num_map (N * prog a)),
  no_mt_code cd1 /\ code_rel_ext cd1 cd2 -> code_rel cd1 cd2.
Proof.
  intros cd1 cd2 [Hm He] n [q r] E. destruct (He n q r (eq_sym E)) as (t' & k' & a' & c' & col & H).
  exists col, t', k', a', c'. rewrite <- H. f_equal.
  rewrite no_mt_full_compile_single; [reflexivity|]. cbn [FST SND]. exact (Hm n q r E).
Qed.

End NoMT.

(** ** Galette-only: the target state of [compile_single_correct]

    [tgo cc l o s] is HOL's [s with <|code := l; compile_oracle := o;
    compile := cc|>]; the lemmas below push it through the semantic
    primitives. *)
Section Tgt.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).
Implicit Types s : state.
Local Abbreviation compile_fun :=
  (c -> list (N * (N * prog a)) -> option (list word8 * (list (word a) * c))).

Definition tgo (cc : compile_fun) (l : num_map (N * prog a)) (o : N -> c * list (N * (N * prog a))) s : state :=
  set_compile cc (set_compile_oracle o (set_code l s)).

Context (cc : compile_fun) (l : num_map (N * prog a)) (o : N -> c * list (N * (N * prog a))).

Lemma tgo_get_var x s : get_var x (tgo cc l o s) = get_var x s. Proof. reflexivity. Qed.
Lemma tgo_get_fp_var x s : get_fp_var x (tgo cc l o s) = get_fp_var x s. Proof. reflexivity. Qed.
Lemma tgo_get_vars xs s : get_vars xs (tgo cc l o s) = get_vars xs s.
Proof. induction xs as [|x xs IH]; cbn; [reflexivity|]. rewrite IH; reflexivity. Qed.
Lemma tgo_get_var_imm x s : get_var_imm x (tgo cc l o s) = get_var_imm x s. Proof. destruct x; reflexivity. Qed.
Lemma tgo_get_store x s : get_store x (tgo cc l o s) = get_store x s. Proof. reflexivity. Qed.
Lemma tgo_word_exp s e : word_exp (tgo cc l o s) e = word_exp s e.
Proof. apply word_exp_state_cong; reflexivity. Qed.
Lemma tgo_set_var x v s : set_var x v (tgo cc l o s) = tgo cc l o (set_var x v s). Proof. reflexivity. Qed.
Lemma tgo_set_vars x v s : set_vars x v (tgo cc l o s) = tgo cc l o (set_vars x v s). Proof. reflexivity. Qed.
Lemma tgo_unset_var x s : unset_var x (tgo cc l o s) = tgo cc l o (unset_var x s). Proof. reflexivity. Qed.
Lemma tgo_set_fp_var x v s : set_fp_var x v (tgo cc l o s) = tgo cc l o (set_fp_var x v s). Proof. reflexivity. Qed.
Lemma tgo_set_store x v s : set_store x v (tgo cc l o s) = tgo cc l o (set_store x v s). Proof. reflexivity. Qed.
Lemma tgo_set_memory v s : set_memory v (tgo cc l o s) = tgo cc l o (set_memory v s). Proof. reflexivity. Qed.
Lemma tgo_set_locals v s : set_locals v (tgo cc l o s) = tgo cc l o (set_locals v s). Proof. reflexivity. Qed.
Lemma tgo_set_fp_regs v s : set_fp_regs v (tgo cc l o s) = tgo cc l o (set_fp_regs v s). Proof. reflexivity. Qed.
Lemma tgo_set_ffi v s : set_ffi v (tgo cc l o s) = tgo cc l o (set_ffi v s). Proof. reflexivity. Qed.
Lemma tgo_set_code_buffer v s : set_code_buffer v (tgo cc l o s) = tgo cc l o (set_code_buffer v s). Proof. reflexivity. Qed.
Lemma tgo_set_data_buffer v s : set_data_buffer v (tgo cc l o s) = tgo cc l o (set_data_buffer v s). Proof. reflexivity. Qed.
Lemma tgo_set_termdep v s : set_termdep v (tgo cc l o s) = tgo cc l o (set_termdep v s). Proof. reflexivity. Qed.
Lemma tgo_set_clock v s : set_clock v (tgo cc l o s) = tgo cc l o (set_clock v s). Proof. reflexivity. Qed.
Lemma tgo_set_permute v s : set_permute v (tgo cc l o s) = tgo cc l o (set_permute v s). Proof. reflexivity. Qed.
Lemma tgo_flush_state b s : flush_state b (tgo cc l o s) = tgo cc l o (flush_state b s). Proof. destruct b; reflexivity. Qed.
Lemma tgo_dec_clock s : dec_clock (tgo cc l o s) = tgo cc l o (dec_clock s). Proof. reflexivity. Qed.
Lemma tgo_code s : code (tgo cc l o s) = l. Proof. reflexivity. Qed.
Lemma tgo_stack_max s : stack_max (tgo cc l o s) = stack_max s. Proof. reflexivity. Qed.
Lemma tgo_set_stack_max v s : set_stack_max v (tgo cc l o s) = tgo cc l o (set_stack_max v s). Proof. reflexivity. Qed.
Lemma tgo_set_stack v s : set_stack v (tgo cc l o s) = tgo cc l o (set_stack v s). Proof. reflexivity. Qed.
Lemma tgo_clock s : clock (tgo cc l o s) = clock s. Proof. reflexivity. Qed.
Lemma tgo_termdep s : termdep (tgo cc l o s) = termdep s. Proof. reflexivity. Qed.
Lemma tgo_locals s : locals (tgo cc l o s) = locals s. Proof. reflexivity. Qed.
Lemma tgo_mdomain s : mdomain (tgo cc l o s) = mdomain s. Proof. reflexivity. Qed.
Lemma tgo_memory s : memory (tgo cc l o s) = memory s. Proof. reflexivity. Qed.
Lemma tgo_be s : be (tgo cc l o s) = be s. Proof. reflexivity. Qed.
Lemma tgo_ffi s : ffi (tgo cc l o s) = ffi s. Proof. reflexivity. Qed.
Lemma tgo_code_buffer s : code_buffer (tgo cc l o s) = code_buffer s. Proof. reflexivity. Qed.
Lemma tgo_data_buffer s : data_buffer (tgo cc l o s) = data_buffer s. Proof. reflexivity. Qed.
Lemma tgo_state_stack_size s : state_stack_size (tgo cc l o s) = state_stack_size s. Proof. reflexivity. Qed.
Lemma tgo_inst i s : inst i (tgo cc l o s) = OPTION_MAP (tgo cc l o) (inst i s).
Proof.
  unfold tgo.
  destruct (@inst_with_const a c ffi_t i (set_compile_oracle o (set_code l s)) 0 l cc o (permute s) [])
    as (_ & _ & H1 & _). rewrite H1.
  destruct (@inst_with_const a c ffi_t i (set_code l s) 0 l cc o (permute s) []) as (_ & _ & _ & H2 & _). rewrite H2.
  destruct (@inst_with_const a c ffi_t i s 0 l cc o (permute s) []) as (_ & H3 & _). rewrite H3.
  destruct (inst i s); reflexivity.
Qed.
Lemma tgo_mem_store x w s : mem_store x w (tgo cc l o s) = OPTION_MAP (tgo cc l o) (mem_store x w s).
Proof. unfold mem_store. cbn [mdomain tgo set_compile set_compile_oracle set_code]. destruct (classical_dec _); reflexivity. Qed.
Lemma tgo_jump_exc s :
  jump_exc (tgo cc l o s) = OPTION_MAP (fun '(t, ll) => (tgo cc l o t, ll)) (jump_exc s).
Proof.
  unfold jump_exc. cbn [handler stack tgo set_compile set_compile_oracle set_code].
  destruct (_ <? _); [|reflexivity]. destruct (LASTN _ _) as [|[m e0 e [[n [l1 l2]]|]] xs]; reflexivity.
Qed.
Lemma tgo_cut_state x s : cut_state x (tgo cc l o s) = OPTION_MAP (tgo cc l o) (cut_state x s).
Proof. unfold cut_state. cbn [locals tgo set_compile set_compile_oracle set_code]. destruct (cut_env _ _); reflexivity. Qed.
Lemma tgo_push_env x y s : push_env x y (tgo cc l o s) = tgo cc l o (push_env x y s).
Proof. destruct y as [[? [? [? ?]]]|]; unfold push_env; cbn [permute tgo set_compile set_compile_oracle set_code]; destruct (env_to_list _ _); reflexivity. Qed.
Lemma tgo_pop_env s : pop_env (tgo cc l o s) = OPTION_MAP (tgo cc l o) (pop_env s).
Proof. unfold pop_env. cbn [stack tgo set_compile set_compile_oracle set_code]. destruct (stack s) as [|[m e0 e [[? ?]|]] xs]; reflexivity. Qed.
Lemma tgo_call_env x y s : call_env x y (tgo cc l o s) = tgo cc l o (call_env x y s). Proof. reflexivity. Qed.
Lemma tgo_gc s : gc (tgo cc l o s) = OPTION_MAP (tgo cc l o) (gc s).
Proof.
  unfold gc. cbn [stack memory mdomain store gc_fun tgo set_compile set_compile_oracle set_code].
  destruct (gc_fun s _) as [[wl [m st]]|]; [|reflexivity]. destruct (dec_stack _ _); reflexivity.
Qed.
Lemma tgo_has_space w s : has_space w (tgo cc l o s) = has_space w s. Proof. reflexivity. Qed.
Lemma tgo_alloc w names s : alloc w names (tgo cc l o s) = PAIR_MAP I (tgo cc l o) (alloc w names s).
Proof.
  unfold alloc. cbn [locals tgo set_compile set_compile_oracle set_code].
  destruct (cut_envs _ _) as [envs|]; [|reflexivity].
  rewrite tgo_set_store, tgo_push_env, tgo_gc. destruct (gc _) as [g|]; [|reflexivity]. cbn [OPTION_MAP].
  rewrite tgo_pop_env. destruct (pop_env g) as [q|]; [|reflexivity]. cbn [OPTION_MAP].
  rewrite tgo_get_store. destruct (get_store _ q) as [w'|]; [|reflexivity].
  rewrite tgo_has_space. destruct (has_space w' q) as [[]|]; reflexivity.
Qed.
Lemma tgo_share_inst op v ad s : share_inst op v ad (tgo cc l o s) = PAIR_MAP I (tgo cc l o) (share_inst op v ad s).
Proof.
  destruct op; cbn [share_inst];
    unfold sh_mem_set_var, sh_mem_load, sh_mem_load_byte, sh_mem_load16, sh_mem_load32,
      sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32;
    cbn [sh_mdomain ffi tgo set_compile set_compile_oracle set_code]; unfold get_var;
    cbn [locals tgo set_compile set_compile_oracle set_code];
    repeat match goal with |- context [match ?x with _ => _ end] =>
      lazymatch x with context [tgo] => fail | _ => destruct x end end; reflexivity.
Qed.

End Tgt.

Create Rewrite HintDb tgo_db.
Global Hint Rewrite @tgo_code @tgo_stack_max @tgo_set_stack_max @tgo_set_stack @tgo_get_var @tgo_get_fp_var @tgo_get_vars @tgo_get_var_imm @tgo_get_store @tgo_word_exp
  @tgo_set_var @tgo_set_vars @tgo_unset_var @tgo_set_fp_var @tgo_set_store @tgo_set_memory @tgo_set_locals
  @tgo_set_fp_regs @tgo_set_ffi @tgo_set_code_buffer @tgo_set_data_buffer @tgo_set_termdep @tgo_set_clock
  @tgo_set_permute @tgo_flush_state @tgo_dec_clock @tgo_clock @tgo_termdep @tgo_locals @tgo_mdomain @tgo_memory
  @tgo_be @tgo_ffi @tgo_code_buffer @tgo_data_buffer @tgo_state_stack_size @tgo_inst @tgo_mem_store
  @tgo_jump_exc @tgo_cut_state @tgo_push_env @tgo_pop_env @tgo_call_env @tgo_alloc @tgo_share_inst : tgo_db.

(** ** [compile_single_correct] *)
Section Correct.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).
Local Abbreviation compile_fun :=
  (c -> list (N * (N * prog a)) -> option (list word8 * (list (word a) * c))).
Context (Hlsc : linear_scan_reg_alloc_correct_stmt) (tt : bool) (kk aa : N) (co : asm_config a).

Local Definition fs (p : N * (N * prog a)) : N * (N * prog a) := compile_single tt kk aa co (p, NONE).
Local Definition ORC (o : N -> c * list (N * (N * prog a))) : N -> c * list (N * (N * prog a)) :=
  (I ## MAP fs) ∘ o.

Local Definition srel (cc : compile_fun) (rst rst1 : state) : Prop :=
  code_rel (code rst) (code rst1) /\ domain (code rst) = domain (code rst1) /\
  rst1 = tgo cc (code rst1) (ORC (compile_oracle rst)) rst.

Lemma MAP_fst_fs (P : list (N * (N * prog a))) : MAP fst (MAP fs P) = MAP fst P.
Proof. induction P as [|[k [n p]] P IH]; [reflexivity|]. cbn [MAP]. rewrite IH. reflexivity. Qed.

Lemma srel_intro cc l (st s' : state) :
  code s' = code st -> compile_oracle s' = compile_oracle st ->
  code_rel (code st) l -> domain (code st) = domain l ->
  srel cc s' (tgo cc l (ORC (compile_oracle st)) s').
Proof.
  intros Hc Ho Hr Hd. unfold srel. cbn [code tgo set_compile set_compile_oracle set_code].
  rewrite Hc, Ho. auto.
Qed.

Lemma bdt (P : Prop) `{Decision P} : P -> bool_decide P = true.
Proof. apply bool_decide_spec. Qed.

Lemma srel_tc cc (s1 s2 : state) t k :
  srel cc s1 s2 -> srel cc (set_termdep t (set_clock k s1)) (set_termdep t (set_clock k s2)).
Proof. intros (H1 & H2 & H3). split; [exact H1|split; [exact H2|]]. rewrite H3 at 1. reflexivity. Qed.

Lemma srel_code cc (s1 s2 : state) : srel cc s1 s2 -> s2 = tgo cc (code s2) (ORC (compile_oracle s1)) s1.
Proof. intros (_ & _ & H). exact H. Qed.

Lemma srel_f cc (s1 s2 : state) (f : state -> state) :
  (forall s, code (f s) = code s) -> (forall s, compile_oracle (f s) = compile_oracle s) ->
  (forall l' o' s, f (tgo cc l' o' s) = tgo cc l' o' (f s)) ->
  srel cc s1 s2 -> srel cc (f s1) (f s2).
Proof.
  intros Hc Ho Ht (H1 & H2 & H3). set (L := code s2) in *. rewrite H3, Ht. unfold srel.
  cbn [code tgo set_compile set_compile_oracle set_code]. rewrite Hc, Ho. auto.
Qed.

Lemma srel_flush cc b (s1 s2 : state) : srel cc s1 s2 -> srel cc (flush_state b s1) (flush_state b s2).
Proof. apply srel_f; [destruct b; reflexivity..|intros; apply tgo_flush_state]. Qed.
Lemma srel_set_locals cc e (s1 s2 : state) : srel cc s1 s2 -> srel cc (set_locals e s1) (set_locals e s2).
Proof. apply srel_f; [reflexivity..|intros; apply tgo_set_locals]. Qed.
Lemma srel_dec_clock cc (s1 s2 : state) : srel cc s1 s2 -> srel cc (dec_clock s1) (dec_clock s2).
Proof. apply srel_f; [reflexivity..|intros; apply tgo_dec_clock]. Qed.

Lemma sp_get_var x p (s : state) : get_var x (set_permute p s) = get_var x s. Proof. reflexivity. Qed.
Lemma sp_get_var_imm x p (s : state) : get_var_imm x (set_permute p s) = get_var_imm x s. Proof. destruct x; reflexivity. Qed.
Lemma sp_cut_state x p (s : state) : cut_state x (set_permute p s) = OPTION_MAP (set_permute p) (cut_state x s).
Proof. unfold cut_state. cbn [locals set_permute]. destruct (cut_env _ _); reflexivity. Qed.

Local Definition cs_goal (x : prog a * state) : Prop :=
  forall l cc,
  code_rel (code (snd x)) l -> domain (code (snd x)) = domain l ->
  compile (snd x) = (fun conf progs => cc conf (MAP fs progs)) ->
  gc_fun_const_ok (gc_fun (snd x)) ->
  exists perm',
    let '(res, rst) := evaluate (fst x, set_permute perm' (snd x)) in
    if bool_decide (res = SOME Error) then True else
    let '(res1, rst1) := evaluate (fst x, tgo cc l (ORC (compile_oracle (snd x))) (snd x)) in
    res1 = res /\ srel cc rst rst1.

Ltac cs_const :=
  unfold set_var, set_vars, unset_var, set_store, flush_state, dec_clock, set_fp_var in *;
  cbn [code compile_oracle set_locals set_store_field set_memory set_fp_regs set_ffi set_code_buffer
       set_data_buffer set_clock set_termdep set_stack set_locals_size set_permute set_handler set_stack_max];
  first [ reflexivity
        | match goal with
          | E : inst _ _ = SOME _ |- _ => pose proof (inst_const_full _ _ _ E)
          | E : mem_store _ _ _ = SOME _ |- _ => pose proof (mem_store_const _ _ _ _ E)
          | E : jump_exc _ = SOME _ |- _ => pose proof (jump_exc_const _ _ _ E)
          | E : alloc _ _ _ = _ |- _ => pose proof (alloc_code_gc_fun_const _ _ _ _ _ E)
          | E : share_inst _ _ _ _ = _ |- _ => pose proof (share_inst_const _ _ _ _ _ _ E)
          end; tauto ].

Ltac bd_simp :=
  repeat match goal with
         | |- context [@bool_decide (?u = ?v) ?d] =>
             first [ replace (@bool_decide (u = v) d) with false
                       by (symmetry; apply Bool.not_true_iff_false; intros Hbd; apply bool_decide_spec in Hbd; discriminate)
                   | replace (@bool_decide (u = v) d) with true by (symmetry; apply bool_decide_spec; reflexivity) ]
         end.

Ltac cs_fin :=
  cbn beta iota zeta; bd_simp; cbn beta iota zeta;
  first [ exact Logic.I
        | match goal with |- (if ?b then True else _) => destruct b; [exact Logic.I|] end;
          split; [reflexivity|]; apply srel_intro; [cs_const|cs_const|assumption|assumption]
        | split; [reflexivity|]; apply srel_intro; [cs_const|cs_const|assumption|assumption] ].

Ltac cs_simple st :=
  exists (permute st); rewrite rm_perm;
  rewrite (evaluate_eqn _ st), (evaluate_eqn _ (tgo _ _ _ st)); cbn [evaluate_body];
  autorewrite with tgo_db;
  repeat match goal with
         | |- context [match ?x with _ => _ end] =>
             lazymatch x with
             | context [tgo] => fail
             | context [match _ with _ => _ end] => fail
             | _ => let E := fresh "E" in destruct x eqn:E;
                    cbn [PAIR_MAP OPTION_MAP I] in *; autorewrite with tgo_db
             end
         end;
  cbn [PAIR_MAP OPTION_MAP I];
  first [ exact Logic.I
        | split; [reflexivity|]; apply srel_intro; [cs_const|cs_const|assumption|assumption] ].

Lemma csl_cor t k alg (c0 : asm_config a) n col (prog : prog a) len prog' (st : state) :
  SND (compile_single t k alg c0 ((n, (len, prog)), col)) = (len, prog') ->
  domain (locals st) = set (even_list len) -> gc_fun_const_ok (gc_fun st) ->
  exists perm',
    let '(res, rst) := evaluate (prog, set_permute perm' st) in
    if bool_decide (res = SOME Error) then True else
    let '(res', rcst) := evaluate (prog', st) in
    res = res' /\ word_state_eq_rel rst rcst /\
    match res with
    | NONE => True
    | SOME (Break _) => True
    | SOME (Continue _) => True
    | SOME _ => locals rst = locals rcst
    end.
Proof.
  intros E Hd Hg. destruct (compile_single_lem_from Hlsc t k alg c0 n col prog len st (conj Hd Hg)) as [perm H].
  exists perm. rewrite compile_single_eta, E in H. exact H.
Qed.

Lemma ce_facts args1 ss envs (h : option (N * (prog a * (N * N)))) (s : state) :
  code (call_env args1 ss (push_env envs h s)) = code s /\
  compile (call_env args1 ss (push_env envs h s)) = compile s /\
  compile_oracle (call_env args1 ss (push_env envs h s)) = compile_oracle s /\
  gc_fun (call_env args1 ss (push_env envs h s)) = gc_fun s /\
  clock (call_env args1 ss (push_env envs h s)) = clock s /\
  termdep (call_env args1 ss (push_env envs h s)) = termdep s /\
  locals (call_env args1 ss (push_env envs h s)) = fromList2 args1.
Proof.
  destruct h as [[? [? [? ?]]]|]; unfold call_env, push_env; destruct (env_to_list _ _); cbn; repeat split.
Qed.

Ltac cs_loop :=
  repeat first
   [ progress bd_simp; cbn beta iota zeta
   | match goal with
         | |- context [match ?x with _ => _ end] =>
             lazymatch x with
             | context [tgo] => fail
             | context [evaluate] => fail
             | context [match _ with _ => _ end] => fail
             | _ => let E := fresh "E" in destruct x eqn:E;
                    cbn [PAIR_MAP OPTION_MAP I] in *; autorewrite with tgo_db wdp
             end
         end ].

Ltac cs_cases :=
  repeat match goal with
         | E : ?X = ?v |- _ =>
             lazymatch v with
             | true => idtac | false => idtac | SOME _ => idtac | NONE => idtac
             end;
             lazymatch goal with |- context [X] => idtac end;
             rewrite E; cbn beta iota zeta
         end.

Ltac cs_err st :=
  exists (permute st); rewrite rm_perm, (evaluate_eqn _ st), (evaluate_eqn _ (tgo _ _ _ st)); cbn [evaluate_body];
  autorewrite with tgo_db; bd_simp; cs_cases; autorewrite with tgo_db; cs_fin.

Theorem cs_main : forall x, cs_goal x.
Proof.
  intros x; induction x as [[p st] IH] using (well_founded_induction eval_lt_wf).
  unfold cs_goal. intros l cc Hcr Hdom Hcomp Hgc. cbn [fst snd] in *.
  destruct p.
  all: try (cs_simple st; fail).
  (* MustTerminate *)
  - destruct (termdep st =? 0) eqn:Et.
    { exists (permute st). rewrite rm_perm, (evaluate_eqn _ st), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
      rewrite Et. cbn. exact Logic.I. }
    set (st' := set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) st)).
    assert (Hlt : eval_lt (p, st') (MustTerminate p, st))
      by (unfold eval_lt, st'; cbn; apply N.eqb_neq in Et; left; lia).
    destruct (IH _ Hlt l cc Hcr Hdom Hcomp Hgc) as [perm H]. cbn [fst snd] in H.
    exists perm. rewrite (evaluate_eqn _ (set_permute perm st)), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
    autorewrite with tgo_db. cbn [termdep set_permute]. rewrite Et.
    change (set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) (set_permute perm st)))
      with (set_permute perm st').
    change (tgo cc l (ORC (compile_oracle st)) (set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) st)))
      with (tgo cc l (ORC (compile_oracle st')) st').
    destruct (evaluate (p, set_permute perm st')) as [r1 s1] eqn:E1.
    destruct (bool_decide (r1 = SOME Error)) eqn:Eb.
    { destruct (bool_decide (r1 = SOME TimeOut)); cbn beta iota zeta; [exact Logic.I|]. rewrite Eb. exact Logic.I. }
    destruct (evaluate (p, tgo cc l (ORC (compile_oracle st')) st')) as [r2 s2] eqn:E2. destruct H as [-> Hs].
    destruct (bool_decide (r1 = SOME TimeOut)); cbn beta iota zeta; [exact Logic.I|]. rewrite Eb.
    split; [reflexivity|]. apply srel_tc, Hs.
  (* Call *)
  - rename o into ret, o0 into dest, l0 into args, o1 into hdl.
    destruct (get_vars args st) as [xs|] eqn:Egv; [|cs_err st].
    destruct (bad_dest_args dest args) eqn:Ebd; [cs_err st|].
    destruct (find_code dest (add_ret_loc ret xs) (code st) (state_stack_size st)) as [[args1 [prog ss]]|] eqn:Efc;
      [|cs_err st].
    destruct (find_code_rel st l _ _ _ _ _ _ Hcr Efc) as (t & k & alg & c0 & col & n & prog' & Hsnd & Efc').
    destruct ret as [[rn [names [rh [l1 l2]]]]|].
    2: {
    destruct hdl as [hh|]; [cs_err st|].
    destruct (clock st =? 0) eqn:Ec0; [cs_err st|].
    set (stt := call_env args1 ss (dec_clock st)).
    assert (Hlt : eval_lt (prog', stt) (Call NONE dest args NONE, st))
      by (unfold eval_lt, stt, call_env, dec_clock; cbn; apply N.eqb_neq in Ec0; right; split; [reflexivity|left; lia]).
    destruct (IH _ Hlt l cc Hcr Hdom Hcomp Hgc) as [perm1 H1]. cbn [fst snd] in H1.
    change (compile_oracle stt) with (compile_oracle st) in H1.
    destruct (csl_cor t k alg c0 n col prog (LENGTH args1) prog' (set_permute perm1 stt) Hsnd
               ltac:(apply domain_fromList2_even) Hgc) as [perm2 H2].
    rewrite set_permute_set_permute in H2.
    destruct (evaluate (prog, set_permute perm2 stt)) as [r0 s1] eqn:E2.
    destruct (bool_decide (r0 = SOME Error)) eqn:Eb0.
    { exists perm2. rewrite (evaluate_eqn _ (set_permute perm2 st)). cbn [evaluate_body]. autorewrite with wdp.
      rewrite Egv, Ebd, Efc. bd_simp. rewrite Ec0.
      change (call_env args1 ss (set_permute perm2 (dec_clock st))) with (set_permute perm2 stt). rewrite E2.
      apply bool_decide_spec in Eb0. subst r0. cbn. exact Logic.I. }
    destruct (evaluate (prog', set_permute perm1 stt)) as [r c1] eqn:E1.
    destruct H2 as (<- & Hw & Hloc).
    rewrite Eb0 in H1.
    destruct (evaluate (prog', tgo cc l (ORC (compile_oracle st)) stt)) as [r1 t1] eqn:F1. destruct H1 as [-> Hs].
    destruct (bad_fun_return r0) eqn:Ebf.
    { exists perm2. rewrite (evaluate_eqn _ (set_permute perm2 st)). cbn [evaluate_body]. autorewrite with wdp.
      rewrite Egv, Ebd, Efc. bd_simp. rewrite Ec0.
      change (call_env args1 ss (set_permute perm2 (dec_clock st))) with (set_permute perm2 stt). rewrite E2, Ebf.
      cbn beta iota zeta. rewrite (bdt (SOME (@Error a) = SOME Error) eq_refl). exact Logic.I. }
    assert (Hl1 : locals s1 = locals c1) by (destruct r0 as [[]|]; cbn in Ebf; try discriminate; exact Hloc).
    pose proof (permute_swap_lemma prog (set_permute perm2 stt) (permute c1)) as Hsw. rewrite E2 in Hsw.
    destruct (Hsw ltac:(intros E; rewrite E in Eb0; rewrite (bdt (SOME (@Error a) = SOME Error) eq_refl) in Eb0; discriminate))
      as [perm3 E3]. rewrite set_permute_set_permute, (wser_locals_perm _ _ Hw Hl1) in E3.
    exists perm3. rewrite (evaluate_eqn _ (set_permute perm3 st)), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
    autorewrite with wdp tgo_db.
    rewrite Egv, Ebd, Efc, Efc'. bd_simp. rewrite Ec0.
    change (call_env args1 ss (set_permute perm3 (dec_clock st))) with (set_permute perm3 stt). rewrite E3.
    change (call_env args1 ss (tgo cc l (ORC (compile_oracle st)) (dec_clock st))) with (tgo cc l (ORC (compile_oracle st)) stt).
    rewrite F1, Ebf. cbn beta iota zeta. rewrite Eb0. split; [reflexivity|exact Hs]. }
    (* returning call *)
    pose proof (evaluate_eqn (Call (SOME (rn, (names, (rh, (l1, l2))))) dest args hdl) st) as EE.
    cbn [evaluate_body] in EE. rewrite Egv, Ebd, Efc in EE. cbn beta iota zeta in EE.
    match type of EE with _ = (if ?b then _ else _) => destruct b eqn:Ech end; [cs_err st|]. clear EE.
    destruct (cut_envs names (locals st)) as [envs|] eqn:Ecut; [|cs_err st].
    destruct (clock st =? 0) eqn:Ec0; [cs_err st|].
    set (stt := call_env args1 ss (push_env envs hdl (dec_clock st))).
    destruct (ce_facts args1 ss envs hdl (dec_clock st)) as (Hc_code & Hc_comp & Hc_or & Hc_gc & Hc_clk & Hc_td & Hc_loc).
    fold stt in Hc_code, Hc_comp, Hc_or, Hc_gc, Hc_clk, Hc_td, Hc_loc.
    cbn [code compile compile_oracle gc_fun clock termdep dec_clock set_clock] in Hc_code, Hc_comp, Hc_or, Hc_gc, Hc_clk, Hc_td.
    assert (Hlt : eval_lt (prog', stt) (Call (SOME (rn, (names, (rh, (l1, l2))))) dest args hdl, st))
      by (unfold eval_lt; cbn [fst snd]; rewrite Hc_clk, Hc_td; apply N.eqb_neq in Ec0; right; split; [reflexivity|left; lia]).
    destruct (IH _ Hlt l cc ltac:(cbn [snd]; rewrite Hc_code; exact Hcr) ltac:(cbn [snd]; rewrite Hc_code; exact Hdom)
               ltac:(cbn [snd]; rewrite Hc_comp; exact Hcomp) ltac:(cbn [snd]; rewrite Hc_gc; exact Hgc)) as [perm1 H1].
    cbn [fst snd] in H1. rewrite Hc_or in H1.
    destruct (csl_cor t k alg c0 n col prog (LENGTH args1) prog' (set_permute perm1 stt) Hsnd
               ltac:(cbn [locals set_permute]; rewrite Hc_loc; apply domain_fromList2_even)
               ltac:(cbn [gc_fun set_permute]; rewrite Hc_gc; exact Hgc)) as [perm2 H2].
    rewrite set_permute_set_permute in H2.
    assert (Hsrc : forall P, call_env args1 ss (push_env envs hdl (set_permute (perm_cons (permute st 0) P) (dec_clock st)))
                             = set_permute P stt)
      by (intros P; rewrite (push_env_perm_cons' envs hdl (dec_clock st) P (permute st 0) eq_refl),
            call_env_set_permute; reflexivity).
    Ltac cs_go st stt Hsrc E1 F1 :=
      rewrite (evaluate_eqn _ (set_permute _ st)), (evaluate_eqn _ (tgo _ _ _ st)); cbn [evaluate_body];
      autorewrite with tgo_db wdp; cs_cases; autorewrite with tgo_db wdp;
      rewrite !fix_clock_evaluate, Hsrc; fold stt; rewrite E1, ?F1;
      autorewrite with tgo_db wdp; cs_cases; cbn beta iota zeta.
    destruct (evaluate (prog, set_permute perm2 stt)) as [r0 s1] eqn:E2.
    destruct (bool_decide (r0 = SOME Error)) eqn:Eb0.
    { apply bool_decide_spec in Eb0. subst r0. exists (perm_cons (permute st 0) perm2).
      cs_go st stt Hsrc E2 E2. cs_fin. }
    destruct (evaluate (prog', set_permute perm1 stt)) as [r c1] eqn:E1.
    destruct H2 as (<- & Hw & Hloc).
    rewrite Eb0 in H1.
    destruct (evaluate (prog', tgo cc l (ORC (compile_oracle st)) stt)) as [r1 t1] eqn:F1. destruct H1 as [-> Hs].
    assert (Hr0 : r0 <> SOME Error)
      by (intros E; rewrite E in Eb0; apply Bool.not_true_iff_false in Eb0; apply Eb0, bool_decide_spec; reflexivity).
    assert (Hsw : forall pp, locals s1 = locals c1 ->
                  exists perm4, evaluate (prog, set_permute perm4 stt) = (r0, set_permute pp c1)).
    { intros pp Hl. pose proof (permute_swap_lemma prog (set_permute perm2 stt) pp) as Hp. rewrite E2 in Hp.
      destruct (Hp Hr0) as [perm4 E4]. exists perm4. rewrite set_permute_set_permute in E4. rewrite E4.
      rewrite <- (wser_locals_perm _ _ Hw Hl). reflexivity. }
    destruct (evaluate_clock _ _ _ _ E1) as [Hck1 Htd1]. cbn [clock termdep set_permute] in Hck1, Htd1.
    destruct (evaluate_consts _ _ _ _ E1) as (Hg1 & _ & _ & _ & Hcp1 & _). cbn [gc_fun compile set_permute] in Hg1, Hcp1.
    destruct r0 as [[x ys|x y|kk0|kk0| | |ff|]|].
    + (* Result *)
      destruct (pop_env c1) as [q|] eqn:Ep.
      2: { destruct (Hsw (permute c1) Hloc) as [perm4 E4]. rewrite rm_perm in E4.
           exists (perm_cons (permute st 0) perm4). cs_go st stt Hsrc E4 F1. cs_loop; cs_fin. }
      assert (Hq : clock q = clock c1 /\ termdep q = termdep c1 /\ code q = code c1 /\ gc_fun q = gc_fun c1 /\
                   compile_oracle q = compile_oracle c1)
        by (pose proof (pop_env_const _ _ Ep); pose proof (pop_env_code_gc_fun_clock _ _ Ep); tauto).
      destruct Hq as (Hqc & Hqt & Hqcd & Hqg & Hqo).
      assert (Hcq : compile q = compile c1) by (unfold pop_env in Ep; destruct (stack c1) as [|[? ? ? [[? ?]|]] ?]; try discriminate; injection Ep as <-; reflexivity).
      assert (Hlt3 : eval_lt (rh, set_vars rn ys q) (Call (SOME (rn, (names, (rh, (l1, l2))))) dest args hdl, st)).
      { unfold eval_lt, set_vars; cbn [fst snd clock termdep set_locals]. rewrite Hqc, Hqt, Htd1, Hc_td.
        rewrite Hc_clk in Hck1. apply N.eqb_neq in Ec0. right; split; [reflexivity|left; lia]. }
      destruct Hs as (Hr1 & Hd1 & Ht1).
      destruct (IH _ Hlt3 (code t1) cc ltac:(cbn [snd code set_vars set_locals]; rewrite Hqcd; exact Hr1)
                 ltac:(cbn [snd code set_vars set_locals]; rewrite Hqcd; exact Hd1)
                 ltac:(cbn [snd compile set_vars set_locals]; rewrite Hcq, <- Hcp1, Hc_comp; exact Hcomp)
                 ltac:(cbn [snd gc_fun set_vars set_locals]; rewrite Hqg, <- Hg1, Hc_gc; exact Hgc)) as [perm3 H3].
      cbn [fst snd] in H3. change (compile_oracle (set_vars rn ys q)) with (compile_oracle q) in H3. rewrite Hqo in H3.
      destruct (Hsw perm3 Hloc) as [perm4 E4].
      exists (perm_cons (permute st 0) perm4). cs_go st stt Hsrc E4 F1.
      rewrite Ht1. autorewrite with tgo_db wdp. cs_cases. cs_loop. all: try (cs_fin; fail).
      all: exact H3.
    + (* Exception *)
      destruct hdl as [[n0 [h [l3 l4]]]|].
      2: { destruct (Hsw (permute c1) Hloc) as [perm4 E4]. rewrite rm_perm in E4.
           exists (perm_cons (permute st 0) perm4). cs_go st stt Hsrc E4 F1. bd_simp. cbn beta iota zeta.
           split; [reflexivity|exact Hs]. }
      assert (Hlt3 : eval_lt (h, set_var n0 y c1) (Call (SOME (rn, (names, (rh, (l1, l2))))) dest args (SOME (n0, (h, (l3, l4)))), st)).
      { unfold eval_lt, set_var; cbn [fst snd clock termdep set_locals]. rewrite Htd1, Hc_td.
        rewrite Hc_clk in Hck1. apply N.eqb_neq in Ec0. right; split; [reflexivity|left; lia]. }
      destruct Hs as (Hr1 & Hd1 & Ht1).
      destruct (IH _ Hlt3 (code t1) cc ltac:(cbn [snd code set_var set_locals]; exact Hr1)
                 ltac:(cbn [snd code set_var set_locals]; exact Hd1)
                 ltac:(cbn [snd compile set_var set_locals]; rewrite <- Hcp1, Hc_comp; exact Hcomp)
                 ltac:(cbn [snd gc_fun set_var set_locals]; rewrite <- Hg1, Hc_gc; exact Hgc)) as [perm3 H3].
      cbn [fst snd] in H3. change (compile_oracle (set_var n0 y c1)) with (compile_oracle c1) in H3.
      destruct (Hsw perm3 Hloc) as [perm4 E4].
      exists (perm_cons (permute st 0) perm4). cs_go st stt Hsrc E4 F1.
      rewrite Ht1. autorewrite with tgo_db wdp. cs_cases. cs_loop. all: try (cs_fin; fail).
      all: exact H3.
    + (* Break *)
      exists (perm_cons (permute st 0) perm2). cs_go st stt Hsrc E2 F1. cs_fin.
    + (* Continue *)
      exists (perm_cons (permute st 0) perm2). cs_go st stt Hsrc E2 F1. cs_fin.
    + (* TimeOut *)
      destruct (Hsw (permute c1) Hloc) as [perm4 E4]. rewrite rm_perm in E4.
      exists (perm_cons (permute st 0) perm4). cs_go st stt Hsrc E4 F1. bd_simp. cbn beta iota zeta.
      split; [reflexivity|exact Hs].
    + (* NotEnoughSpace *)
      destruct (Hsw (permute c1) Hloc) as [perm4 E4]. rewrite rm_perm in E4.
      exists (perm_cons (permute st 0) perm4). cs_go st stt Hsrc E4 F1. bd_simp. cbn beta iota zeta.
      split; [reflexivity|exact Hs].
    + (* FinalFFI *)
      destruct (Hsw (permute c1) Hloc) as [perm4 E4]. rewrite rm_perm in E4.
      exists (perm_cons (permute st 0) perm4). cs_go st stt Hsrc E4 F1. bd_simp. cbn beta iota zeta.
      split; [reflexivity|exact Hs].
    + (* Error *)
      exfalso; apply Hr0; reflexivity.
    + (* NONE *)
      exists (perm_cons (permute st 0) perm2). cs_go st stt Hsrc E2 F1. cs_fin.
  (* Seq *)
  - destruct (IH (p1, st) ltac:(unfold eval_lt; cbn; lia) l cc Hcr Hdom Hcomp Hgc) as [perm1 H1]. cbn [fst snd] in H1.
    destruct (evaluate (p1, set_permute perm1 st)) as [r1 s1] eqn:E1.
    destruct (bool_decide (r1 = SOME Error)) eqn:Eb1.
    { exists perm1. rewrite (evaluate_eqn _ (set_permute perm1 st)). cbn [evaluate_body]. rewrite fix_clock_evaluate, E1.
      apply bool_decide_spec in Eb1. subst r1. cbn. exact Logic.I. }
    destruct (evaluate (p1, tgo cc l (ORC (compile_oracle st)) st)) as [r1' t1] eqn:F1. destruct H1 as [-> Hs1].
    destruct (bool_decide (r1 = NONE)) eqn:En.
    + apply bool_decide_spec in En. subst r1.
      destruct (evaluate_clock _ _ _ _ E1) as [Hck Htd]. cbn [clock termdep set_permute] in Hck, Htd.
      destruct (evaluate_consts _ _ _ _ E1) as (Hg1 & _ & _ & _ & Hc1 & _). cbn [gc_fun compile set_permute] in Hg1, Hc1.
      assert (Hlt : eval_lt (p2, s1) (Seq p1 p2, st)).
      { unfold eval_lt; cbn [fst snd psize]. right. split; [exact Htd|].
        destruct (N.lt_ge_cases (clock s1) (clock st)); [left; exact H|right; split; lia]. }
      destruct Hs1 as (Hr1 & Hd1 & Ht1).
      destruct (IH _ Hlt (code t1) cc Hr1 Hd1 ltac:(cbn [snd]; rewrite <- Hc1; exact Hcomp) ltac:(cbn [snd]; rewrite <- Hg1; exact Hgc))
        as [perm2 H2]. cbn [fst snd] in H2.
      pose proof (permute_swap_lemma p1 (set_permute perm1 st) perm2) as Hsw. rewrite E1 in Hsw.
      destruct (Hsw ltac:(discriminate)) as [perm3 E3]. rewrite set_permute_set_permute in E3.
      exists perm3. rewrite (evaluate_eqn _ (set_permute perm3 st)), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
      rewrite !fix_clock_evaluate, E3, F1. rewrite (bdt (@NONE (result a) = NONE) eq_refl).
      rewrite <- Ht1 in H2. exact H2.
    + exists perm1. rewrite (evaluate_eqn _ (set_permute perm1 st)), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
      rewrite !fix_clock_evaluate, E1, F1, En. rewrite Eb1. split; [reflexivity|exact Hs1].
  (* If *)
  - destruct (get_var n st) as [x|] eqn:Ex;
      [|exists (permute st); rewrite rm_perm, (evaluate_eqn _ st), (evaluate_eqn _ (tgo _ _ _ st));
        cbn [evaluate_body]; rewrite tgo_get_var, Ex; cs_fin].
    destruct (get_var_imm r st) as [y|] eqn:Ey;
      [|exists (permute st); rewrite rm_perm, (evaluate_eqn _ st), (evaluate_eqn _ (tgo _ _ _ st));
        cbn [evaluate_body]; rewrite tgo_get_var, tgo_get_var_imm, Ex, Ey; cs_fin].
    destruct (word_cmp c0 x y) as [[]|] eqn:Ew;
      [| |exists (permute st); rewrite rm_perm, (evaluate_eqn _ st), (evaluate_eqn _ (tgo _ _ _ st));
          cbn [evaluate_body]; rewrite tgo_get_var, tgo_get_var_imm, Ex, Ey, Ew; cs_fin].
    + destruct (IH (p1, st) ltac:(unfold eval_lt; cbn; lia) l cc Hcr Hdom Hcomp Hgc) as [perm H]. cbn [fst snd] in H.
      exists perm. rewrite (evaluate_eqn _ (set_permute perm st)), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
      rewrite tgo_get_var, tgo_get_var_imm, sp_get_var, sp_get_var_imm, Ex, Ey, Ew. exact H.
    + destruct (IH (p2, st) ltac:(unfold eval_lt; cbn; lia) l cc Hcr Hdom Hcomp Hgc) as [perm H]. cbn [fst snd] in H.
      exists perm. rewrite (evaluate_eqn _ (set_permute perm st)), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
      rewrite tgo_get_var, tgo_get_var_imm, sp_get_var, sp_get_var_imm, Ex, Ey, Ew. exact H.
  (* Loop *)
  - destruct (cut_state (s, LN) st) as [stt|] eqn:Ecs;
      [|exists (permute st); rewrite rm_perm, (evaluate_eqn _ st), (evaluate_eqn _ (tgo _ _ _ st));
        cbn [evaluate_body]; rewrite tgo_cut_state, Ecs; cs_fin].
    destruct (cut_state_const _ _ _ Ecs) as [env ->].
    assert (Hlt1 : eval_lt (p, set_locals env st) (Loop s p s0, st)) by (unfold eval_lt; cbn; lia).
    destruct (IH _ Hlt1 l cc Hcr Hdom Hcomp Hgc) as [perm1 H1]. cbn [fst snd] in H1.
    change (compile_oracle (set_locals env st)) with (compile_oracle st) in H1.
    destruct (evaluate (p, set_permute perm1 (set_locals env st))) as [r1 s1] eqn:E1.
    assert (Hrun : forall perm, cut_state (s, LN) (set_permute perm st) = SOME (set_permute perm (set_locals env st)))
      by (intros perm; rewrite sp_cut_state, Ecs; reflexivity).
    destruct (bool_decide (r1 = SOME Error)) eqn:Eb1.
    { apply bool_decide_spec in Eb1. subst r1. exists perm1.
      rewrite (evaluate_eqn _ (set_permute perm1 st)). cbn [evaluate_body]. rewrite Hrun, fix_clock_evaluate, E1.
      cbn [cont_loop]. destruct (bool_decide (SOME Error = SOME (Break 0))) eqn:Ebb; cbn beta iota zeta.
      - apply bool_decide_spec in Ebb. discriminate.
      - cbn [exit_loop]. rewrite (bdt (@SOME (result a) Error = SOME Error) eq_refl). exact Logic.I. }
    destruct (evaluate (p, tgo cc l (ORC (compile_oracle st)) (set_locals env st))) as [r1' t1] eqn:F1.
    destruct H1 as [-> Hs1].
    assert (Htrun : cut_state (s, LN) (tgo cc l (ORC (compile_oracle st)) st) =
                    SOME (tgo cc l (ORC (compile_oracle st)) (set_locals env st)))
      by (rewrite tgo_cut_state, Ecs; reflexivity).
    destruct (cont_loop r1) eqn:Ecl.
    + destruct (clock s1 =? 0) eqn:Ec0.
      * exists perm1. rewrite (evaluate_eqn _ (set_permute perm1 st)), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
        rewrite Hrun, Htrun, !fix_clock_evaluate, E1, F1, Ecl.
        assert (Hck : clock t1 = clock s1) by (rewrite (srel_code _ _ _ Hs1); reflexivity).
        rewrite Hck, Ec0. cbn beta iota zeta.
        destruct (bool_decide (SOME TimeOut = SOME Error)); [exact Logic.I|].
        split; [reflexivity|]. apply srel_flush, Hs1.
      * destruct (evaluate_clock _ _ _ _ E1) as [Hck Htd]. cbn [clock termdep set_permute set_locals] in Hck, Htd.
        destruct (evaluate_consts _ _ _ _ E1) as (Hg1 & _ & _ & _ & Hc1 & _).
        cbn [gc_fun compile set_permute set_locals] in Hg1, Hc1.
        assert (Hlt2 : eval_lt (Loop s p s0, dec_clock s1) (Loop s p s0, st)).
        { unfold eval_lt, dec_clock; cbn [fst snd clock termdep set_clock]. apply N.eqb_neq in Ec0. right; split; [exact Htd|left; lia]. }
        destruct Hs1 as (Hr1 & Hd1 & Ht1).
        destruct (IH _ Hlt2 (code t1) cc Hr1 Hd1 ltac:(cbn [snd dec_clock compile set_clock]; rewrite <- Hc1; exact Hcomp)
                   ltac:(cbn [snd dec_clock gc_fun set_clock]; rewrite <- Hg1; exact Hgc)) as [perm2 H2].
        cbn [fst snd] in H2.
        pose proof (permute_swap_lemma p (set_permute perm1 (set_locals env st)) perm2) as Hsw. rewrite E1 in Hsw.
        destruct (Hsw ltac:(intros ->; discriminate)) as [perm3 E3]. rewrite set_permute_set_permute in E3.
        exists perm3. rewrite (evaluate_eqn _ (set_permute perm3 st)), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
        rewrite Hrun, Htrun, !fix_clock_evaluate, E3, F1, Ecl.
        assert (Hck1 : clock t1 = clock s1) by (rewrite Ht1; reflexivity).
        change (clock (set_permute perm2 s1)) with (clock s1). rewrite Hck1, Ec0. unfold STOP.
        change (dec_clock (set_permute perm2 s1)) with (set_permute perm2 (dec_clock s1)).
        rewrite Ht1, tgo_dec_clock. exact H2.
    + destruct (bool_decide (r1 = SOME (Break 0))) eqn:Ebr.
      * exists perm1. rewrite (evaluate_eqn _ (set_permute perm1 st)), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
        rewrite Hrun, Htrun, !fix_clock_evaluate, E1, F1, Ecl, Ebr.
        rewrite (srel_code _ _ _ Hs1). rewrite tgo_cut_state.
        destruct (cut_state (s0, LN) s1) as [s2|] eqn:Ecs2; cbn [OPTION_MAP].
        -- destruct (cut_state_const _ _ _ Ecs2) as [env2 ->]. cbn beta iota zeta.
           destruct (bool_decide (@NONE (result a) = SOME Error)); [exact Logic.I|].
           split; [reflexivity|]. rewrite <- tgo_set_locals, <- (srel_code _ _ _ Hs1). apply srel_set_locals, Hs1.
        -- cbn beta iota zeta. destruct (bool_decide (SOME (@Error a) = SOME Error)); [exact Logic.I|].
           split; [reflexivity|]. rewrite <- (srel_code _ _ _ Hs1). exact Hs1.
      * exists perm1. rewrite (evaluate_eqn _ (set_permute perm1 st)), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
        rewrite Hrun, Htrun, !fix_clock_evaluate, E1, F1, Ecl, Ebr. cbn beta iota zeta.
        destruct (bool_decide (exit_loop r1 = SOME Error)); [exact Logic.I|]. split; [reflexivity|exact Hs1].
  (* LocValue *)
  - exists (permute st). rewrite rm_perm, (evaluate_eqn _ st), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
    cbn [code tgo set_compile set_compile_oracle set_code]. rewrite <- Hdom, tgo_set_var.
    destruct (classical_dec _); cs_fin.
  (* Install *)
  - exists (permute st). rewrite rm_perm, (evaluate_eqn _ st), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
    autorewrite with tgo_db. cbn [compile_oracle compile code_buffer data_buffer tgo set_compile set_compile_oracle set_code].
    rewrite Hcomp.
    assert (Eo : ORC (compile_oracle st) 0 = (I ## MAP fs) (compile_oracle st 0)) by reflexivity. rewrite Eo.
    assert (Eo1 : FST (shift_seq 1 (ORC (compile_oracle st)) 0) = FST (shift_seq 1 (compile_oracle st) 0))
      by (unfold shift_seq, ORC; destruct (compile_oracle st (0 + 1)); reflexivity).
    rewrite Eo1.
    destruct (compile_oracle st 0) as [cfg progs] eqn:Ec0. cbn [PAIR_MAP FST SND fst snd combin.I].
    destruct (cut_env p (locals st)) as [env|]; [|cs_fin].
    destruct (get_var n st) as [[w1|? ?]|]; [|cs_fin|cs_fin].
    destruct (get_var n0 st) as [[w2|? ?]|]; [|cs_fin|cs_fin].
    destruct (get_var n1 st) as [[w3|? ?]|]; [|cs_fin|cs_fin].
    destruct (get_var n2 st) as [[w4|? ?]|]; [|cs_fin|cs_fin].
    cbn beta iota zeta.
    destruct (buffer_flush (code_buffer st) w1 w2) as [[bytes cb]|]; [|cs_fin].
    destruct (buffer_flush (data_buffer st) w3 w4) as [[data db]|]; [|cs_fin].
    destruct (cc cfg (MAP fs progs)) as [[bytes' [data' cfg']]|]; [|cs_fin].
    destruct progs as [|[k [n3 p3]] rest]; [cs_fin|].
    cbn [MAP fs compile_single].
    destruct (_ && _ && _); [|cs_fin]. cbn beta iota zeta.
    destruct (bool_decide (@NONE (result a) = SOME Error)); [exact Logic.I|].
    split; [reflexivity|]. unfold srel.
    cbn [code compile_oracle set_stack_size set_stack_max set_compile_oracle set_fp_regs set_locals set_code
         set_data_buffer set_code_buffer tgo set_compile].
    split; [|split].
    + pose proof (code_rel_union_fromAList tt kk aa co (code st) l ((k, (n3, p3)) :: rest) (conj Hcr Hdom)) as H.
      exact H.
    + rewrite !domain_union, !domain_fromAList. cbn [MAP fst FST]. rewrite MAP_fst_fs, Hdom. reflexivity.
    + reflexivity.
Qed.

(** HOL's [compile_single_correct], with [linear_scanProof]'s
    [linear_scan_reg_alloc_correct] as a hypothesis (the section variable
    [Hlsc]); HOL's free [tt kk aa co] are section variables. *)
Theorem compile_single_correct_from : forall (prog : prog a) (st : state) l coracle cc,
  code_rel (code st) l /\ domain (code st) = domain l /\
  compile st = (fun conf progs => cc conf (MAP (fun p => compile_single tt kk aa co (p, NONE)) progs)) /\
  coracle = (I ## MAP (fun p => compile_single tt kk aa co (p, NONE))) ∘ compile_oracle st /\
  gc_fun_const_ok (gc_fun st) ->
  exists perm',
    let '(res, rst) := evaluate (prog, set_permute perm' st) in
    if bool_decide (res = SOME Error) then True else
    let '(res1, rst1) := evaluate (prog, set_compile cc (set_compile_oracle coracle (set_code l st))) in
    res1 = res /\ code_rel (code rst) (code rst1) /\ domain (code rst) = domain (code rst1) /\
    rst1 = set_compile cc (set_compile_oracle
             ((I ## MAP (fun p => compile_single tt kk aa co (p, NONE))) ∘ compile_oracle rst)
             (set_code (code rst1) rst)).
Proof. intros prog st l coracle cc (H1 & H2 & H3 & -> & H5). exact (cs_main (prog, st) l cc H1 H2 H3 H5). Qed.

Lemma map_full_compile_single (ps : list (N * (N * prog a))) :
  MAP (I ## (I ## remove_must_terminate)) (MAP (fun p => compile_single tt kk aa co (p, NONE)) ps) =
  MAP (fun p => full_compile_single tt kk aa co (p, NONE)) ps.
Proof. induction ps as [|[k0 [n0 p0]] ps IH]; [reflexivity|]. cbn [MAP]. rewrite IH. reflexivity. Qed.

(** HOL's [compile_word_to_word_thm], with [linear_scanProof]'s
    [linear_scan_reg_alloc_correct] as a hypothesis (the section variable
    [Hlsc]). *)
Theorem compile_word_to_word_thm_from : forall (st : state) l cc coracle start,
  code_rel (code st) l /\ domain (code st) = domain l /\
  compile st = (fun conf progs => cc conf (MAP (fun p => full_compile_single tt kk aa co (p, NONE)) progs)) /\
  coracle = (I ## MAP (fun p => full_compile_single tt kk aa co (p, NONE))) ∘ compile_oracle st /\
  gc_fun_const_ok (gc_fun st) ->
  exists perm' clk,
    let prog := Call NONE (SOME start) [0] NONE in
    let '(res, rst) := evaluate (prog, set_permute perm' st) in
    if bool_decide (res = SOME Error) then True else
    let '(res1, rst1) := evaluate (prog,
      set_compile_oracle coracle (set_compile cc (set_termdep 0 (set_clock (clock st + clk)
        (set_code (map (I ## remove_must_terminate) l) st))))) in
    res1 = res /\ clock rst1 = clock rst /\ ffi rst1 = ffi rst /\ stack_max rst1 = stack_max rst.
Proof.
  intros st l cc coracle start (Hcr & Hd & Hc & -> & Hg).
  set (cc' := fun conf => cc conf ∘ MAP (I ## (I ## remove_must_terminate))).
  set (O := (I ## MAP (fun p => compile_single tt kk aa co (p, NONE))) ∘ compile_oracle st).
  assert (Hc' : compile st = (fun conf progs => cc' conf (MAP (fun p => compile_single tt kk aa co (p, NONE)) progs))).
  { rewrite Hc. unfold cc'. apply functional_extensionality; intros conf. apply functional_extensionality; intros ps.
    cbv beta. rewrite map_full_compile_single. reflexivity. }
  destruct (compile_single_correct_from (Call NONE (SOME start) [0] NONE) st l O cc'
              (conj Hcr (conj Hd (conj Hc' (conj eq_refl Hg))))) as [perm H].
  exists perm. cbv zeta.
  destruct (evaluate (Call NONE (SOME start) [0] NONE, set_permute perm st)) as [res rst] eqn:E.
  destruct (bool_decide (res = SOME Error)) eqn:Eb; [exists 0; exact Logic.I|].
  assert (Hr : res <> SOME Error) by (intros Er; rewrite Er in Eb; apply Bool.not_true_iff_false in Eb; apply Eb, bool_decide_spec; reflexivity).
  destruct (evaluate (Call NONE (SOME start) [0] NONE, set_compile cc' (set_compile_oracle O (set_code l st))))
    as [res1 rst1] eqn:E1.
  destruct H as (-> & _ & _ & Hrst1).
  destruct (word_remove_correct cc (Call NONE (SOME start) [0] NONE) _ res rst1 (conj E1 (conj eq_refl Hr))) as [clk Hk].
  exists clk.
  replace (set_compile_oracle ((I ## MAP (fun p => full_compile_single tt kk aa co (p, NONE))) ∘ compile_oracle st)
             (set_compile cc (set_termdep 0 (set_clock (clock st + clk) (set_code (map (I ## remove_must_terminate) l) st)))))
    with (compile_state clk cc (set_compile cc' (set_compile_oracle O (set_code l st)))).
  - cbn [remove_must_terminate] in Hk. rewrite Hk. rewrite Hrst1.
    split; [reflexivity|]. cbn. split; [lia|split; reflexivity].
  - unfold compile_state. cbn [compile_oracle code clock set_compile set_compile_oracle set_code].
    assert (Ho : (I ## MAP (I ## (I ## remove_must_terminate))) ∘ O =
                 (I ## MAP (fun p => full_compile_single tt kk aa co (p, NONE))) ∘ compile_oracle st).
    { apply functional_extensionality; intros x. unfold O. destruct (compile_oracle st x) as [cf ps].
      rewrite !PAIR_MAP_THM. unfold combin.I. rewrite map_full_compile_single. reflexivity. }
    rewrite Ho. reflexivity.
Qed.


(** ** [no_install_no_alloc_compile_single_correct]: the same simulation with
    the code replaced only (Galette-only infrastructure as above). *)
Local Definition nrel (cc : compile_fun) (rst rst1 : state) : Prop :=
  code_rel (code rst) (code rst1) /\ domain (code rst) = domain (code rst1) /\
  rst1 = tgo cc (code rst1) (compile_oracle rst) rst.

Lemma nrel_intro cc l (st s' : state) :
  code s' = code st -> compile_oracle s' = compile_oracle st ->
  code_rel (code st) l -> domain (code st) = domain l ->
  nrel cc s' (tgo cc l (compile_oracle st) s').
Proof.
  intros Hc Ho Hr Hd. unfold nrel. cbn [code tgo set_compile set_compile_oracle set_code].
  rewrite Hc, Ho. auto.
Qed.

Lemma nrel_tc cc (s1 s2 : state) t k :
  nrel cc s1 s2 -> nrel cc (set_termdep t (set_clock k s1)) (set_termdep t (set_clock k s2)).
Proof. intros (H1 & H2 & H3). split; [exact H1|split; [exact H2|]]. rewrite H3 at 1. reflexivity. Qed.

Lemma nrel_code cc (s1 s2 : state) : nrel cc s1 s2 -> s2 = tgo cc (code s2) (compile_oracle s1) s1.
Proof. intros (_ & _ & H). exact H. Qed.

Lemma nrel_f cc (s1 s2 : state) (f : state -> state) :
  (forall s, code (f s) = code s) -> (forall s, compile_oracle (f s) = compile_oracle s) ->
  (forall l' o' s, f (tgo cc l' o' s) = tgo cc l' o' (f s)) ->
  nrel cc s1 s2 -> nrel cc (f s1) (f s2).
Proof.
  intros Hc Ho Ht (H1 & H2 & H3). set (L := code s2) in *. rewrite H3, Ht. unfold nrel.
  cbn [code tgo set_compile set_compile_oracle set_code]. rewrite Hc, Ho. auto.
Qed.

Lemma nrel_flush cc b (s1 s2 : state) : nrel cc s1 s2 -> nrel cc (flush_state b s1) (flush_state b s2).
Proof. apply nrel_f; [destruct b; reflexivity..|intros; apply tgo_flush_state]. Qed.
Lemma nrel_set_locals cc e (s1 s2 : state) : nrel cc s1 s2 -> nrel cc (set_locals e s1) (set_locals e s2).
Proof. apply nrel_f; [reflexivity..|intros; apply tgo_set_locals]. Qed.
Lemma nrel_dec_clock cc (s1 s2 : state) : nrel cc s1 s2 -> nrel cc (dec_clock s1) (dec_clock s2).
Proof. apply nrel_f; [reflexivity..|intros; apply tgo_dec_clock]. Qed.

Local Definition NI (st : state) (p : prog a) : Prop :=
  no_install p /\ no_alloc p /\ no_install_code (code st) /\ no_alloc_code (code st).

Local Definition ni_goal (x : prog a * state) : Prop :=
  forall l cc,
  code_rel (code (snd x)) l -> domain (code (snd x)) = domain l ->
  compile (snd x) = cc -> gc_fun_const_ok (gc_fun (snd x)) -> NI (snd x) (fst x) ->
  exists perm',
    let '(res, rst) := evaluate (fst x, set_permute perm' (snd x)) in
    if bool_decide (res = SOME Error) then True else
    let '(res1, rst1) := evaluate (fst x, tgo cc l (compile_oracle (snd x)) (snd x)) in
    res1 = res /\ nrel cc rst rst1.

Ltac ni_fin :=
  cbn beta iota zeta; bd_simp; cbn beta iota zeta;
  first [ exact Logic.I
        | match goal with |- (if ?b then True else _) => destruct b; [exact Logic.I|] end;
          split; [reflexivity|]; apply nrel_intro; [cs_const|cs_const|assumption|assumption]
        | split; [reflexivity|]; apply nrel_intro; [cs_const|cs_const|assumption|assumption] ].

Ltac ni_simple st :=
  exists (permute st); rewrite rm_perm;
  rewrite (evaluate_eqn _ st), (evaluate_eqn _ (tgo _ _ _ st)); cbn [evaluate_body];
  autorewrite with tgo_db;
  repeat match goal with
         | |- context [match ?x with _ => _ end] =>
             lazymatch x with
             | context [tgo] => fail
             | context [match _ with _ => _ end] => fail
             | _ => let E := fresh "E" in destruct x eqn:E;
                    cbn [PAIR_MAP OPTION_MAP I] in *; autorewrite with tgo_db
             end
         end;
  cbn [PAIR_MAP OPTION_MAP I];
  first [ exact Logic.I
        | split; [reflexivity|]; apply nrel_intro; [cs_const|cs_const|assumption|assumption] ].

Ltac ni_err st :=
  exists (permute st); rewrite rm_perm, (evaluate_eqn _ st), (evaluate_eqn _ (tgo _ _ _ st)); cbn [evaluate_body];
  autorewrite with tgo_db; bd_simp; cs_cases; autorewrite with tgo_db; ni_fin.

Ltac ni_prog :=
  first [ assumption
        | match goal with H : no_install ?p /\ no_alloc ?p |- _ => first [exact (proj1 H) | exact (proj2 H)] end
        | match goal with H : NI _ _ |- _ =>
            let Hi := fresh in let Ha := fresh in destruct H as (Hi & Ha & _);
            unfold no_install, no_alloc in *; cbn [not_created_subprogs] in Hi, Ha; tauto end ].

Ltac ni_code :=
  cbn [code set_var set_vars set_locals set_permute set_termdep set_clock dec_clock call_env set_stack_max
       set_locals_size];
  repeat (match goal with H : code ?X = code ?Y |- context [code ?X] => progress rewrite H end);
  match goal with H : NI _ _ |- _ => first [ exact (proj1 (proj2 (proj2 H))) | exact (proj2 (proj2 (proj2 H))) ] end.

Ltac ni_tac :=
  cbn [fst snd]; unfold NI; split; [ni_prog|split; [ni_prog|split; ni_code]].

Theorem ni_main : forall x, ni_goal x.
Proof.
  intros x; induction x as [[p st] IH] using (well_founded_induction eval_lt_wf).
  unfold ni_goal. intros l cc Hcr Hdom Hcomp Hgc Hni. cbn [fst snd] in *.
  destruct p.
  all: try (ni_simple st; fail).
  (* MustTerminate *)
  - destruct (termdep st =? 0) eqn:Et.
    { exists (permute st). rewrite rm_perm, (evaluate_eqn _ st), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
      rewrite Et. cbn. exact Logic.I. }
    set (st' := set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) st)).
    assert (Hlt : eval_lt (p, st') (MustTerminate p, st))
      by (unfold eval_lt, st'; cbn; apply N.eqb_neq in Et; left; lia).
    destruct (IH _ Hlt l cc Hcr Hdom Hcomp Hgc ltac:(ni_tac)) as [perm H]. cbn [fst snd] in H.
    exists perm. rewrite (evaluate_eqn _ (set_permute perm st)), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
    autorewrite with tgo_db. cbn [termdep set_permute]. rewrite Et.
    change (set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) (set_permute perm st)))
      with (set_permute perm st').
    change (tgo cc l ((compile_oracle st)) (set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) st)))
      with (tgo cc l ((compile_oracle st')) st').
    destruct (evaluate (p, set_permute perm st')) as [r1 s1] eqn:E1.
    destruct (bool_decide (r1 = SOME Error)) eqn:Eb.
    { destruct (bool_decide (r1 = SOME TimeOut)); cbn beta iota zeta; [exact Logic.I|]. rewrite Eb. exact Logic.I. }
    destruct (evaluate (p, tgo cc l ((compile_oracle st')) st')) as [r2 s2] eqn:E2. destruct H as [-> Hs].
    destruct (bool_decide (r1 = SOME TimeOut)); cbn beta iota zeta; [exact Logic.I|]. rewrite Eb.
    split; [reflexivity|]. apply nrel_tc, Hs.
  (* Call *)
  - rename o into ret, o0 into dest, l0 into args, o1 into hdl.
    destruct (get_vars args st) as [xs|] eqn:Egv; [|ni_err st].
    destruct (bad_dest_args dest args) eqn:Ebd; [ni_err st|].
    destruct (find_code dest (add_ret_loc ret xs) (code st) (state_stack_size st)) as [[args1 [prog ss]]|] eqn:Efc;
      [|ni_err st].
    destruct (find_code_rel st l _ _ _ _ _ _ Hcr Efc) as (t & k & alg & c0 & col & n & prog' & Hsnd & Efc').
    assert (Hnp : no_install prog' /\ no_alloc prog').
    { destruct Hni as (_ & _ & Hc1' & Hc2'). split.
      - apply (code_rel_no_install _ _ _ _ _ _ _ (conj Efc (conj Hcr (conj (no_install_find_code _ _ _ _ _ _ _ (conj Hc1' Efc)) Efc')))).
      - apply (code_rel_no_alloc _ _ _ _ _ _ _ (conj Efc (conj Hcr (conj (no_alloc_find_code _ _ _ _ _ _ _ (conj Efc Hc2')) Efc')))). }
    destruct ret as [[rn [names [rh [l1 l2]]]]|].
    2: {
    destruct hdl as [hh|]; [ni_err st|].
    destruct (clock st =? 0) eqn:Ec0; [ni_err st|].
    set (stt := call_env args1 ss (dec_clock st)).
    assert (Hlt : eval_lt (prog', stt) (Call NONE dest args NONE, st))
      by (unfold eval_lt, stt, call_env, dec_clock; cbn; apply N.eqb_neq in Ec0; right; split; [reflexivity|left; lia]).
    destruct (IH _ Hlt l cc Hcr Hdom Hcomp Hgc ltac:(ni_tac)) as [perm1 H1]. cbn [fst snd] in H1.
    change (compile_oracle stt) with (compile_oracle st) in H1.
    destruct (csl_cor t k alg c0 n col prog (LENGTH args1) prog' (set_permute perm1 stt) Hsnd
               ltac:(apply domain_fromList2_even) Hgc) as [perm2 H2].
    rewrite set_permute_set_permute in H2.
    destruct (evaluate (prog, set_permute perm2 stt)) as [r0 s1] eqn:E2.
    destruct (bool_decide (r0 = SOME Error)) eqn:Eb0.
    { exists perm2. rewrite (evaluate_eqn _ (set_permute perm2 st)). cbn [evaluate_body]. autorewrite with wdp.
      rewrite Egv, Ebd, Efc. bd_simp. rewrite Ec0.
      change (call_env args1 ss (set_permute perm2 (dec_clock st))) with (set_permute perm2 stt). rewrite E2.
      apply bool_decide_spec in Eb0. subst r0. cbn. exact Logic.I. }
    destruct (evaluate (prog', set_permute perm1 stt)) as [r c1] eqn:E1.
    destruct H2 as (<- & Hw & Hloc).
    rewrite Eb0 in H1.
    destruct (evaluate (prog', tgo cc l ((compile_oracle st)) stt)) as [r1 t1] eqn:F1. destruct H1 as [-> Hs].
    destruct (bad_fun_return r0) eqn:Ebf.
    { exists perm2. rewrite (evaluate_eqn _ (set_permute perm2 st)). cbn [evaluate_body]. autorewrite with wdp.
      rewrite Egv, Ebd, Efc. bd_simp. rewrite Ec0.
      change (call_env args1 ss (set_permute perm2 (dec_clock st))) with (set_permute perm2 stt). rewrite E2, Ebf.
      cbn beta iota zeta. rewrite (bdt (SOME (@Error a) = SOME Error) eq_refl). exact Logic.I. }
    assert (Hl1 : locals s1 = locals c1) by (destruct r0 as [[]|]; cbn in Ebf; try discriminate; exact Hloc).
    pose proof (permute_swap_lemma prog (set_permute perm2 stt) (permute c1)) as Hsw. rewrite E2 in Hsw.
    destruct (Hsw ltac:(intros E; rewrite E in Eb0; rewrite (bdt (SOME (@Error a) = SOME Error) eq_refl) in Eb0; discriminate))
      as [perm3 E3]. rewrite set_permute_set_permute, (wser_locals_perm _ _ Hw Hl1) in E3.
    exists perm3. rewrite (evaluate_eqn _ (set_permute perm3 st)), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
    autorewrite with wdp tgo_db.
    rewrite Egv, Ebd, Efc, Efc'. bd_simp. rewrite Ec0.
    change (call_env args1 ss (set_permute perm3 (dec_clock st))) with (set_permute perm3 stt). rewrite E3.
    change (call_env args1 ss (tgo cc l ((compile_oracle st)) (dec_clock st))) with (tgo cc l ((compile_oracle st)) stt).
    rewrite F1, Ebf. cbn beta iota zeta. rewrite Eb0. split; [reflexivity|exact Hs]. }
    (* returning call *)
    pose proof (evaluate_eqn (Call (SOME (rn, (names, (rh, (l1, l2))))) dest args hdl) st) as EE.
    cbn [evaluate_body] in EE. rewrite Egv, Ebd, Efc in EE. cbn beta iota zeta in EE.
    match type of EE with _ = (if ?b then _ else _) => destruct b eqn:Ech end; [ni_err st|]. clear EE.
    destruct (cut_envs names (locals st)) as [envs|] eqn:Ecut; [|ni_err st].
    destruct (clock st =? 0) eqn:Ec0; [ni_err st|].
    set (stt := call_env args1 ss (push_env envs hdl (dec_clock st))).
    destruct (ce_facts args1 ss envs hdl (dec_clock st)) as (Hc_code & Hc_comp & Hc_or & Hc_gc & Hc_clk & Hc_td & Hc_loc).
    fold stt in Hc_code, Hc_comp, Hc_or, Hc_gc, Hc_clk, Hc_td, Hc_loc.
    cbn [code compile compile_oracle gc_fun clock termdep dec_clock set_clock] in Hc_code, Hc_comp, Hc_or, Hc_gc, Hc_clk, Hc_td.
    assert (Hlt : eval_lt (prog', stt) (Call (SOME (rn, (names, (rh, (l1, l2))))) dest args hdl, st))
      by (unfold eval_lt; cbn [fst snd]; rewrite Hc_clk, Hc_td; apply N.eqb_neq in Ec0; right; split; [reflexivity|left; lia]).
    destruct (IH _ Hlt l cc ltac:(cbn [snd]; rewrite Hc_code; exact Hcr) ltac:(cbn [snd]; rewrite Hc_code; exact Hdom)
               ltac:(cbn [snd]; rewrite Hc_comp; exact Hcomp) ltac:(cbn [snd]; rewrite Hc_gc; exact Hgc) ltac:(ni_tac)) as [perm1 H1].
    cbn [fst snd] in H1. rewrite Hc_or in H1.
    destruct (csl_cor t k alg c0 n col prog (LENGTH args1) prog' (set_permute perm1 stt) Hsnd
               ltac:(cbn [locals set_permute]; rewrite Hc_loc; apply domain_fromList2_even)
               ltac:(cbn [gc_fun set_permute]; rewrite Hc_gc; exact Hgc)) as [perm2 H2].
    rewrite set_permute_set_permute in H2.
    assert (Hsrc : forall P, call_env args1 ss (push_env envs hdl (set_permute (perm_cons (permute st 0) P) (dec_clock st)))
                             = set_permute P stt)
      by (intros P; rewrite (push_env_perm_cons' envs hdl (dec_clock st) P (permute st 0) eq_refl),
            call_env_set_permute; reflexivity).
    destruct (evaluate (prog, set_permute perm2 stt)) as [r0 s1] eqn:E2.
    destruct (bool_decide (r0 = SOME Error)) eqn:Eb0.
    { apply bool_decide_spec in Eb0. subst r0. exists (perm_cons (permute st 0) perm2).
      cs_go st stt Hsrc E2 E2. ni_fin. }
    destruct (evaluate (prog', set_permute perm1 stt)) as [r c1] eqn:E1.
    destruct H2 as (<- & Hw & Hloc).
    rewrite Eb0 in H1.
    destruct (evaluate (prog', tgo cc l ((compile_oracle st)) stt)) as [r1 t1] eqn:F1. destruct H1 as [-> Hs].
    assert (Hr0 : r0 <> SOME Error)
      by (intros E; rewrite E in Eb0; apply Bool.not_true_iff_false in Eb0; apply Eb0, bool_decide_spec; reflexivity).
    assert (Hsw : forall pp, locals s1 = locals c1 ->
                  exists perm4, evaluate (prog, set_permute perm4 stt) = (r0, set_permute pp c1)).
    { intros pp Hl. pose proof (permute_swap_lemma prog (set_permute perm2 stt) pp) as Hp. rewrite E2 in Hp.
      destruct (Hp Hr0) as [perm4 E4]. exists perm4. rewrite set_permute_set_permute in E4. rewrite E4.
      rewrite <- (wser_locals_perm _ _ Hw Hl). reflexivity. }
    destruct (evaluate_clock _ _ _ _ E1) as [Hck1 Htd1]. cbn [clock termdep set_permute] in Hck1, Htd1.
    destruct (evaluate_consts _ _ _ _ E1) as (Hg1 & _ & _ & _ & Hcp1 & _). cbn [gc_fun compile set_permute] in Hg1, Hcp1.
    assert (HcC1 : code c1 = code st).
    { rewrite <- Hc_code. symmetry. eapply (no_install_evaluate_const_code prog' (set_permute perm1 stt) _ c1).
      split; [exact E1|split; [exact (proj1 Hnp)|]]. cbn [code set_permute]. rewrite Hc_code. exact (proj1 (proj2 (proj2 Hni))). }
    destruct r0 as [[x ys|x y|kk0|kk0| | |ff|]|].
    + (* Result *)
      destruct (pop_env c1) as [q|] eqn:Ep.
      2: { destruct (Hsw (permute c1) Hloc) as [perm4 E4]. rewrite rm_perm in E4.
           exists (perm_cons (permute st 0) perm4). cs_go st stt Hsrc E4 F1. cs_loop; ni_fin. }
      assert (Hq : clock q = clock c1 /\ termdep q = termdep c1 /\ code q = code c1 /\ gc_fun q = gc_fun c1 /\
                   compile_oracle q = compile_oracle c1)
        by (pose proof (pop_env_const _ _ Ep); pose proof (pop_env_code_gc_fun_clock _ _ Ep); tauto).
      destruct Hq as (Hqc & Hqt & Hqcd & Hqg & Hqo).
      assert (Hcq : compile q = compile c1) by (unfold pop_env in Ep; destruct (stack c1) as [|[? ? ? [[? ?]|]] ?]; try discriminate; injection Ep as <-; reflexivity).
      assert (Hlt3 : eval_lt (rh, set_vars rn ys q) (Call (SOME (rn, (names, (rh, (l1, l2))))) dest args hdl, st)).
      { unfold eval_lt, set_vars; cbn [fst snd clock termdep set_locals]. rewrite Hqc, Hqt, Htd1, Hc_td.
        rewrite Hc_clk in Hck1. apply N.eqb_neq in Ec0. right; split; [reflexivity|left; lia]. }
      destruct Hs as (Hr1 & Hd1 & Ht1).
      destruct (IH _ Hlt3 (code t1) cc ltac:(cbn [snd code set_vars set_locals]; rewrite Hqcd; exact Hr1)
                 ltac:(cbn [snd code set_vars set_locals]; rewrite Hqcd; exact Hd1)
                 ltac:(cbn [snd compile set_vars set_locals]; rewrite Hcq, <- Hcp1, Hc_comp; exact Hcomp)
                 ltac:(cbn [snd gc_fun set_vars set_locals]; rewrite Hqg, <- Hg1, Hc_gc; exact Hgc) ltac:(ni_tac)) as [perm3 H3].
      cbn [fst snd] in H3. change (compile_oracle (set_vars rn ys q)) with (compile_oracle q) in H3. rewrite Hqo in H3.
      destruct (Hsw perm3 Hloc) as [perm4 E4].
      exists (perm_cons (permute st 0) perm4). cs_go st stt Hsrc E4 F1.
      rewrite Ht1. autorewrite with tgo_db wdp. cs_cases. cs_loop. all: try (ni_fin; fail).
      all: exact H3.
    + (* Exception *)
      destruct hdl as [[n0 [h [l3 l4]]]|].
      2: { destruct (Hsw (permute c1) Hloc) as [perm4 E4]. rewrite rm_perm in E4.
           exists (perm_cons (permute st 0) perm4). cs_go st stt Hsrc E4 F1. bd_simp. cbn beta iota zeta.
           split; [reflexivity|exact Hs]. }
      assert (Hlt3 : eval_lt (h, set_var n0 y c1) (Call (SOME (rn, (names, (rh, (l1, l2))))) dest args (SOME (n0, (h, (l3, l4)))), st)).
      { unfold eval_lt, set_var; cbn [fst snd clock termdep set_locals]. rewrite Htd1, Hc_td.
        rewrite Hc_clk in Hck1. apply N.eqb_neq in Ec0. right; split; [reflexivity|left; lia]. }
      destruct Hs as (Hr1 & Hd1 & Ht1).
      destruct (IH _ Hlt3 (code t1) cc ltac:(cbn [snd code set_var set_locals]; exact Hr1)
                 ltac:(cbn [snd code set_var set_locals]; exact Hd1)
                 ltac:(cbn [snd compile set_var set_locals]; rewrite <- Hcp1, Hc_comp; exact Hcomp)
                 ltac:(cbn [snd gc_fun set_var set_locals]; rewrite <- Hg1, Hc_gc; exact Hgc) ltac:(ni_tac)) as [perm3 H3].
      cbn [fst snd] in H3. change (compile_oracle (set_var n0 y c1)) with (compile_oracle c1) in H3.
      destruct (Hsw perm3 Hloc) as [perm4 E4].
      exists (perm_cons (permute st 0) perm4). cs_go st stt Hsrc E4 F1.
      rewrite Ht1. autorewrite with tgo_db wdp. cs_cases. cs_loop. all: try (ni_fin; fail).
      all: exact H3.
    + (* Break *)
      exists (perm_cons (permute st 0) perm2). cs_go st stt Hsrc E2 F1. ni_fin.
    + (* Continue *)
      exists (perm_cons (permute st 0) perm2). cs_go st stt Hsrc E2 F1. ni_fin.
    + (* TimeOut *)
      destruct (Hsw (permute c1) Hloc) as [perm4 E4]. rewrite rm_perm in E4.
      exists (perm_cons (permute st 0) perm4). cs_go st stt Hsrc E4 F1. bd_simp. cbn beta iota zeta.
      split; [reflexivity|exact Hs].
    + (* NotEnoughSpace *)
      destruct (Hsw (permute c1) Hloc) as [perm4 E4]. rewrite rm_perm in E4.
      exists (perm_cons (permute st 0) perm4). cs_go st stt Hsrc E4 F1. bd_simp. cbn beta iota zeta.
      split; [reflexivity|exact Hs].
    + (* FinalFFI *)
      destruct (Hsw (permute c1) Hloc) as [perm4 E4]. rewrite rm_perm in E4.
      exists (perm_cons (permute st 0) perm4). cs_go st stt Hsrc E4 F1. bd_simp. cbn beta iota zeta.
      split; [reflexivity|exact Hs].
    + (* Error *)
      exfalso; apply Hr0; reflexivity.
    + (* NONE *)
      exists (perm_cons (permute st 0) perm2). cs_go st stt Hsrc E2 F1. ni_fin.
  (* Seq *)
  - destruct (IH (p1, st) ltac:(unfold eval_lt; cbn; lia) l cc Hcr Hdom Hcomp Hgc ltac:(ni_tac)) as [perm1 H1]. cbn [fst snd] in H1.
    destruct (evaluate (p1, set_permute perm1 st)) as [r1 s1] eqn:E1.
    destruct (bool_decide (r1 = SOME Error)) eqn:Eb1.
    { exists perm1. rewrite (evaluate_eqn _ (set_permute perm1 st)). cbn [evaluate_body]. rewrite fix_clock_evaluate, E1.
      apply bool_decide_spec in Eb1. subst r1. cbn. exact Logic.I. }
    destruct (evaluate (p1, tgo cc l ((compile_oracle st)) st)) as [r1' t1] eqn:F1. destruct H1 as [-> Hs1].
    destruct (bool_decide (r1 = NONE)) eqn:En.
    + apply bool_decide_spec in En. subst r1.
      destruct (evaluate_clock _ _ _ _ E1) as [Hck Htd]. cbn [clock termdep set_permute] in Hck, Htd.
      destruct (evaluate_consts _ _ _ _ E1) as (Hg1 & _ & _ & _ & Hc1 & _). cbn [gc_fun compile set_permute] in Hg1, Hc1.
      assert (HcS1 : code s1 = code st).
      { symmetry. apply (no_install_evaluate_const_code p1 (set_permute perm1 st) NONE s1).
        split; [exact E1|split; [|exact (proj1 (proj2 (proj2 Hni)))]].
        destruct Hni as (Hi & _). unfold no_install in *. cbn [not_created_subprogs] in Hi. tauto. }
      assert (Hlt : eval_lt (p2, s1) (Seq p1 p2, st)).
      { unfold eval_lt; cbn [fst snd psize]. right. split; [exact Htd|].
        destruct (N.lt_ge_cases (clock s1) (clock st)); [left; exact H|right; split; lia]. }
      destruct Hs1 as (Hr1 & Hd1 & Ht1).
      destruct (IH _ Hlt (code t1) cc Hr1 Hd1 ltac:(cbn [snd]; rewrite <- Hc1; exact Hcomp) ltac:(cbn [snd]; rewrite <- Hg1; exact Hgc) ltac:(ni_tac))
        as [perm2 H2]. cbn [fst snd] in H2.
      pose proof (permute_swap_lemma p1 (set_permute perm1 st) perm2) as Hsw. rewrite E1 in Hsw.
      destruct (Hsw ltac:(discriminate)) as [perm3 E3]. rewrite set_permute_set_permute in E3.
      exists perm3. rewrite (evaluate_eqn _ (set_permute perm3 st)), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
      rewrite !fix_clock_evaluate, E3, F1. rewrite (bdt (@NONE (result a) = NONE) eq_refl).
      rewrite <- Ht1 in H2. exact H2.
    + exists perm1. rewrite (evaluate_eqn _ (set_permute perm1 st)), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
      rewrite !fix_clock_evaluate, E1, F1, En. rewrite Eb1. split; [reflexivity|exact Hs1].
  (* If *)
  - destruct (get_var n st) as [x|] eqn:Ex;
      [|exists (permute st); rewrite rm_perm, (evaluate_eqn _ st), (evaluate_eqn _ (tgo _ _ _ st));
        cbn [evaluate_body]; rewrite tgo_get_var, Ex; ni_fin].
    destruct (get_var_imm r st) as [y|] eqn:Ey;
      [|exists (permute st); rewrite rm_perm, (evaluate_eqn _ st), (evaluate_eqn _ (tgo _ _ _ st));
        cbn [evaluate_body]; rewrite tgo_get_var, tgo_get_var_imm, Ex, Ey; ni_fin].
    destruct (word_cmp c0 x y) as [[]|] eqn:Ew;
      [| |exists (permute st); rewrite rm_perm, (evaluate_eqn _ st), (evaluate_eqn _ (tgo _ _ _ st));
          cbn [evaluate_body]; rewrite tgo_get_var, tgo_get_var_imm, Ex, Ey, Ew; ni_fin].
    + destruct (IH (p1, st) ltac:(unfold eval_lt; cbn; lia) l cc Hcr Hdom Hcomp Hgc ltac:(ni_tac)) as [perm H]. cbn [fst snd] in H.
      exists perm. rewrite (evaluate_eqn _ (set_permute perm st)), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
      rewrite tgo_get_var, tgo_get_var_imm, sp_get_var, sp_get_var_imm, Ex, Ey, Ew. exact H.
    + destruct (IH (p2, st) ltac:(unfold eval_lt; cbn; lia) l cc Hcr Hdom Hcomp Hgc ltac:(ni_tac)) as [perm H]. cbn [fst snd] in H.
      exists perm. rewrite (evaluate_eqn _ (set_permute perm st)), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
      rewrite tgo_get_var, tgo_get_var_imm, sp_get_var, sp_get_var_imm, Ex, Ey, Ew. exact H.
  (* Loop *)
  - destruct (cut_state (s, LN) st) as [stt|] eqn:Ecs;
      [|exists (permute st); rewrite rm_perm, (evaluate_eqn _ st), (evaluate_eqn _ (tgo _ _ _ st));
        cbn [evaluate_body]; rewrite tgo_cut_state, Ecs; ni_fin].
    destruct (cut_state_const _ _ _ Ecs) as [env ->].
    assert (Hlt1 : eval_lt (p, set_locals env st) (Loop s p s0, st)) by (unfold eval_lt; cbn; lia).
    destruct (IH _ Hlt1 l cc Hcr Hdom Hcomp Hgc ltac:(ni_tac)) as [perm1 H1]. cbn [fst snd] in H1.
    change (compile_oracle (set_locals env st)) with (compile_oracle st) in H1.
    destruct (evaluate (p, set_permute perm1 (set_locals env st))) as [r1 s1] eqn:E1.
    assert (Hrun : forall perm, cut_state (s, LN) (set_permute perm st) = SOME (set_permute perm (set_locals env st)))
      by (intros perm; rewrite sp_cut_state, Ecs; reflexivity).
    destruct (bool_decide (r1 = SOME Error)) eqn:Eb1.
    { apply bool_decide_spec in Eb1. subst r1. exists perm1.
      rewrite (evaluate_eqn _ (set_permute perm1 st)). cbn [evaluate_body]. rewrite Hrun, fix_clock_evaluate, E1.
      cbn [cont_loop]. destruct (bool_decide (SOME Error = SOME (Break 0))) eqn:Ebb; cbn beta iota zeta.
      - apply bool_decide_spec in Ebb. discriminate.
      - cbn [exit_loop]. rewrite (bdt (@SOME (result a) Error = SOME Error) eq_refl). exact Logic.I. }
    destruct (evaluate (p, tgo cc l ((compile_oracle st)) (set_locals env st))) as [r1' t1] eqn:F1.
    destruct H1 as [-> Hs1].
    assert (Htrun : cut_state (s, LN) (tgo cc l ((compile_oracle st)) st) =
                    SOME (tgo cc l ((compile_oracle st)) (set_locals env st)))
      by (rewrite tgo_cut_state, Ecs; reflexivity).
    destruct (cont_loop r1) eqn:Ecl.
    + destruct (clock s1 =? 0) eqn:Ec0.
      * exists perm1. rewrite (evaluate_eqn _ (set_permute perm1 st)), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
        rewrite Hrun, Htrun, !fix_clock_evaluate, E1, F1, Ecl.
        assert (Hck : clock t1 = clock s1) by (rewrite (nrel_code _ _ _ Hs1); reflexivity).
        rewrite Hck, Ec0. cbn beta iota zeta.
        destruct (bool_decide (SOME TimeOut = SOME Error)); [exact Logic.I|].
        split; [reflexivity|]. apply nrel_flush, Hs1.
      * destruct (evaluate_clock _ _ _ _ E1) as [Hck Htd]. cbn [clock termdep set_permute set_locals] in Hck, Htd.
        destruct (evaluate_consts _ _ _ _ E1) as (Hg1 & _ & _ & _ & Hc1 & _).
        cbn [gc_fun compile set_permute set_locals] in Hg1, Hc1.
        assert (HcS1 : code s1 = code st).
        { symmetry. apply (no_install_evaluate_const_code p (set_permute perm1 (set_locals env st)) r1 s1).
          split; [exact E1|split; [|exact (proj1 (proj2 (proj2 Hni)))]].
          destruct Hni as (Hi & _). unfold no_install in *. cbn [not_created_subprogs] in Hi. tauto. }
        assert (Hlt2 : eval_lt (Loop s p s0, dec_clock s1) (Loop s p s0, st)).
        { unfold eval_lt, dec_clock; cbn [fst snd clock termdep set_clock]. apply N.eqb_neq in Ec0. right; split; [exact Htd|left; lia]. }
        destruct Hs1 as (Hr1 & Hd1 & Ht1).
        destruct (IH _ Hlt2 (code t1) cc Hr1 Hd1 ltac:(cbn [snd dec_clock compile set_clock]; rewrite <- Hc1; exact Hcomp)
                   ltac:(cbn [snd dec_clock gc_fun set_clock]; rewrite <- Hg1; exact Hgc) ltac:(ni_tac)) as [perm2 H2].
        cbn [fst snd] in H2.
        pose proof (permute_swap_lemma p (set_permute perm1 (set_locals env st)) perm2) as Hsw. rewrite E1 in Hsw.
        destruct (Hsw ltac:(intros ->; discriminate)) as [perm3 E3]. rewrite set_permute_set_permute in E3.
        exists perm3. rewrite (evaluate_eqn _ (set_permute perm3 st)), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
        rewrite Hrun, Htrun, !fix_clock_evaluate, E3, F1, Ecl.
        assert (Hck1 : clock t1 = clock s1) by (rewrite Ht1; reflexivity).
        change (clock (set_permute perm2 s1)) with (clock s1). rewrite Hck1, Ec0. unfold STOP.
        change (dec_clock (set_permute perm2 s1)) with (set_permute perm2 (dec_clock s1)).
        rewrite Ht1, tgo_dec_clock. exact H2.
    + destruct (bool_decide (r1 = SOME (Break 0))) eqn:Ebr.
      * exists perm1. rewrite (evaluate_eqn _ (set_permute perm1 st)), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
        rewrite Hrun, Htrun, !fix_clock_evaluate, E1, F1, Ecl, Ebr.
        rewrite (nrel_code _ _ _ Hs1). rewrite tgo_cut_state.
        destruct (cut_state (s0, LN) s1) as [s2|] eqn:Ecs2; cbn [OPTION_MAP].
        -- destruct (cut_state_const _ _ _ Ecs2) as [env2 ->]. cbn beta iota zeta.
           destruct (bool_decide (@NONE (result a) = SOME Error)); [exact Logic.I|].
           split; [reflexivity|]. rewrite <- tgo_set_locals, <- (nrel_code _ _ _ Hs1). apply nrel_set_locals, Hs1.
        -- cbn beta iota zeta. destruct (bool_decide (SOME (@Error a) = SOME Error)); [exact Logic.I|].
           split; [reflexivity|]. rewrite <- (nrel_code _ _ _ Hs1). exact Hs1.
      * exists perm1. rewrite (evaluate_eqn _ (set_permute perm1 st)), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
        rewrite Hrun, Htrun, !fix_clock_evaluate, E1, F1, Ecl, Ebr. cbn beta iota zeta.
        destruct (bool_decide (exit_loop r1 = SOME Error)); [exact Logic.I|]. split; [reflexivity|exact Hs1].
  (* LocValue *)
  - exists (permute st). rewrite rm_perm, (evaluate_eqn _ st), (evaluate_eqn _ (tgo _ _ _ st)). cbn [evaluate_body].
    cbn [code tgo set_compile set_compile_oracle set_code]. rewrite <- Hdom, tgo_set_var.
    destruct (classical_dec _); ni_fin.
  (* Install *)
  - exfalso. destruct Hni as (Hi & _). unfold no_install in Hi. cbn [not_created_subprogs] in Hi. exact (Hi eq_refl).
Qed.

Lemma tgo_self l (s : state) : tgo (compile s) l (compile_oracle s) s = set_code l s.
Proof. destruct s; reflexivity. Qed.

(** HOL's [no_install_no_alloc_compile_single_correct], with
    [linear_scanProof]'s [linear_scan_reg_alloc_correct] as a hypothesis
    (the section variable [Hlsc]). *)
Theorem no_install_no_alloc_compile_single_correct_from : forall (prog : prog a) (st : state) l,
  code_rel (code st) l /\ no_install prog /\ no_alloc prog /\
  no_install_code (code st) /\ no_alloc_code (code st) /\
  domain (code st) = domain l /\ gc_fun_const_ok (gc_fun st) ->
  exists perm',
    let '(res, rst) := evaluate (prog, set_permute perm' st) in
    if bool_decide (res = SOME Error) then True else
    let '(res1, rst1) := evaluate (prog, set_code l st) in
    res1 = res /\ code_rel (code rst) (code rst1) /\ domain (code rst) = domain (code rst1) /\
    rst1 = set_code (code rst1) rst.
Proof.
  intros prog st l (Hcr & Hi & Ha & Hic & Hac & Hd & Hg).
  destruct (ni_main (prog, st) l (compile st) Hcr Hd eq_refl Hg (conj Hi (conj Ha (conj Hic Hac)))) as [perm H].
  exists perm. cbn [fst snd] in H. rewrite tgo_self in H.
  destruct (evaluate (prog, set_permute perm st)) as [res rst] eqn:E.
  destruct (bool_decide (res = SOME Error)); [exact Logic.I|].
  destruct (evaluate (prog, set_code l st)) as [res1 rst1]. destruct H as (-> & H1 & H2 & H3).
  split; [reflexivity|split; [exact H1|split; [exact H2|]]].
  destruct (evaluate_consts _ _ _ _ E) as (_ & _ & _ & _ & Hc & _). cbn [compile set_permute] in Hc.
  rewrite Hc, tgo_self in H3. exact H3.
Qed.

(** HOL's [panLang_compile_word_to_word_thm], with [linear_scanProof]'s
    [linear_scan_reg_alloc_correct] as a hypothesis (the section variable
    [Hlsc]). *)
Theorem panLang_compile_word_to_word_thm_from : forall (st : state) l start,
  code_rel (code st) l /\ no_install_code (code st) /\ no_alloc_code (code st) /\ no_mt_code (code st) /\
  domain (code st) = domain l /\ gc_fun_const_ok (gc_fun st) ->
  exists perm' (clk : N),
    let prog := Call NONE (SOME start) [0] NONE in
    let '(res, rst) := evaluate (prog, set_permute perm' st) in
    if bool_decide (res = SOME Error) then True else
    let '(res1, rst1) := evaluate (prog, set_code l st) in
    res1 = res /\ clock rst1 = clock rst /\ ffi rst1 = ffi rst /\ stack_max rst1 = stack_max rst.
Proof.
  intros st l start (Hcr & Hic & Hac & _ & Hd & Hg).
  assert (Hi : no_install (@Call a NONE (SOME start) [0] NONE))
    by (unfold no_install; cbn [not_created_subprogs]; repeat split; discriminate).
  assert (Ha : no_alloc (@Call a NONE (SOME start) [0] NONE))
    by (unfold no_alloc; cbn [not_created_subprogs]; repeat split; discriminate).
  destruct (no_install_no_alloc_compile_single_correct_from (Call NONE (SOME start) [0] NONE) st l
              (conj Hcr (conj Hi (conj Ha (conj Hic (conj Hac (conj Hd Hg))))))) as [perm H].
  exists perm, 0. cbv zeta.
  destruct (evaluate (Call NONE (SOME start) [0] NONE, set_permute perm st)) as [res rst].
  destruct (bool_decide (res = SOME Error)); [exact Logic.I|].
  destruct (evaluate (Call NONE (SOME start) [0] NONE, set_code l st)) as [res1 rst1].
  destruct H as (-> & _ & _ & H3). rewrite H3. split; [reflexivity|]. repeat split.
Qed.

Lemma MAP_fst_compile_ZIP tt' kk' aa' (co' : asm_config a) (w : list (N * (N * prog a))) orc :
  LENGTH orc = LENGTH w ->
  MAP fst (MAP (full_compile_single tt' kk' aa' co') (ZIP (w, orc))) = MAP fst w.
Proof.
  revert orc; induction w as [|[n [m p]] w IH]; intros [|o orc] Hl; cbn in Hl; try lia; [reflexivity|].
  rewrite (proj2 (proj2 ZIP_eqns)). cbn [MAP]. rewrite IH by lia. reflexivity.
Qed.

(** HOL's [word_to_word_compile_semantics], with [linear_scanProof]'s
    [linear_scan_reg_alloc_correct] as a hypothesis (the section variable
    [Hlsc]).  Proof: for every clock the two runs have the same result and
    the same FFI state ([panLang_compile_word_to_word_thm] and
    [permute_swap_lemma3]), so the two [semantics] coincide. *)
Theorem word_to_word_compile_semantics_from : forall wconf (acomf : asm_config a) wprog0 col wprog (s t : state) start,
  word_to_word.compile wconf acomf wprog0 = (col, wprog) /\
  gc_fun_const_ok (gc_fun s) /\
  no_install_code (fromAList wprog0) /\ no_alloc_code (fromAList wprog0) /\
  no_install_code (code s) /\ no_alloc_code (code s) /\
  no_mt_code (fromAList wprog0) /\
  ALL_DISTINCT (MAP FST wprog0) /\ stack s = [] /\
  code t = fromAList wprog /\ lookup 0 (locals t) = SOME (Loc 1 0) /\
  t = set_code (code t) s /\
  code s = fromAList wprog0 /\
  semantics s start <> ffi.Fail ->
  semantics s start = semantics t start.
Proof.
  intros wconf acomf wprog0 col wprog s t start
    (Hc & Hg & Hi0 & Ha0 & Hi & Ha & Hm0 & Hdst & Hst & Htc & _ & Ht & Hsc & Hsem).
  pose proof (no_mt_code_rel_ext _ _ (conj Hm0 (code_rel_ext_word_to_word _ _ _ _ _ Hc))) as Hcr.
  assert (Hdom : domain (fromAList wprog0) = domain (fromAList wprog)).
  { unfold word_to_word.compile in Hc.
    pose proof (LENGTH_next_n_oracle (LENGTH wprog0) (col_oracle wconf)) as Hl.
    destruct (next_n_oracle (LENGTH wprog0) (col_oracle wconf)) as [orc col0]. cbn [fst] in Hl.
    assert (Hw : wprog = MAP (full_compile_single (two_reg_arith acomf) (reg_count acomf - (5 + LENGTH (avoid_regs acomf)))
                                (reg_alg wconf) acomf) (ZIP (wprog0, orc)))
      by (change (pair col0 (MAP (full_compile_single (two_reg_arith acomf) (reg_count acomf - (5 + LENGTH (avoid_regs acomf)))
                                (reg_alg wconf) acomf) (ZIP (wprog0, orc))) = (col, wprog)) in Hc; congruence).
    rewrite Hw, !domain_fromAList. apply functional_extensionality; intros x.
    rewrite MAP_fst_compile_ZIP by exact Hl. reflexivity. }
  set (prog := @Call a NONE (SOME start) [0] NONE).
  assert (Hk : forall k, fst (evaluate (prog, set_clock k s)) <> SOME Error ->
            fst (evaluate (prog, set_clock k t)) = fst (evaluate (prog, set_clock k s)) /\
            ffi (snd (evaluate (prog, set_clock k t))) = ffi (snd (evaluate (prog, set_clock k s)))).
  { intros k Hne.
    destruct (panLang_compile_word_to_word_thm_from (set_clock k s) (fromAList wprog) start) as (perm & _ & H).
    { cbn [code set_clock gc_fun]. rewrite Hsc. repeat split; try assumption; rewrite <- Hsc; assumption. }
    cbv zeta in H. fold prog in H.
    pose proof (permute_swap_lemma3 prog (set_clock k s) perm) as H3.
    destruct (evaluate (prog, set_clock k s)) as [r s1] eqn:E. cbn [fst] in Hne.
    destruct (H3 ltac:(split; [exact Hne|]; cbn [code set_clock wordSem.stack]; rewrite Hst;
                       repeat split; try assumption; unfold prog, no_alloc, no_install; cbn [not_created_subprogs];
                       repeat split; discriminate)) as (perm' & stack' & E3 & _).
    rewrite E3 in H. destruct (bool_decide (r = SOME Error)) eqn:Eb.
    { exfalso. apply bool_decide_spec in Eb. contradiction. }
    replace (set_clock k t) with (set_code (fromAList wprog) (set_clock k s)) by (rewrite Ht; rewrite Htc; reflexivity).
    destruct (evaluate (prog, set_code (fromAList wprog) (set_clock k s))) as [r1 t1].
    destruct H as (-> & _ & Hf & _). split; [reflexivity|]. exact Hf. }
  assert (Hnf : forall k, fst (evaluate (prog, set_clock k s)) <> SOME Error).
  { intros k E. apply Hsem. unfold semantics. fold prog. destruct (classical_dec _) as [_|Hn]; [reflexivity|].
    exfalso. apply Hn. exists k. rewrite E. exact Logic.I. }
  assert (Hf1 : forall k, fst (evaluate (prog, set_clock k t)) = fst (evaluate (prog, set_clock k s)))
    by (intros k; exact (proj1 (Hk k (Hnf k)))).
  assert (Hf2 : forall k, ffi (snd (evaluate (prog, set_clock k t))) = ffi (snd (evaluate (prog, set_clock k s))))
    by (intros k; exact (proj2 (Hk k (Hnf k)))).
  unfold semantics. fold prog.
  assert (Hc1 : (exists k, match fst (evaluate (prog, set_clock k s)) with
                           | SOME (Exception _ _) => True | SOME (Result ret _) => ret <> Loc 1 0
                           | SOME Error => True | NONE => True | _ => False end) =
                (exists k, match fst (evaluate (prog, set_clock k t)) with
                           | SOME (Exception _ _) => True | SOME (Result ret _) => ret <> Loc 1 0
                           | SOME Error => True | NONE => True | _ => False end)).
  { apply propositional_extensionality. split; intros [k Hk']; exists k; [rewrite Hf1|rewrite <- Hf1]; exact Hk'. }
  rewrite <- Hc1. destruct (classical_dec _) as [_|_]; [reflexivity|].
  assert (Hp : (fun res => exists k t0 r outcome, evaluate (prog, set_clock k s) = (r, t0) /\
                  match r with
                  | SOME (FinalFFI e) => outcome = FFI_outcome e
                  | SOME (Result _ _) => outcome = Success
                  | SOME NotEnoughSpace => outcome = Resource_limit_hit
                  | _ => False
                  end /\ res = Terminate outcome (io_events (ffi t0))) =
               (fun res => exists k t0 r outcome, evaluate (prog, set_clock k t) = (r, t0) /\
                  match r with
                  | SOME (FinalFFI e) => outcome = FFI_outcome e
                  | SOME (Result _ _) => outcome = Success
                  | SOME NotEnoughSpace => outcome = Resource_limit_hit
                  | _ => False
                  end /\ res = Terminate outcome (io_events (ffi t0)))).
  { apply functional_extensionality; intros res. apply propositional_extensionality.
    split; intros (k & t0 & r & o & E & Hm & ->); exists k.
    - exists (snd (evaluate (prog, set_clock k t))), r, o. split.
      + rewrite (surjective_pairing (evaluate (prog, set_clock k t))), Hf1, E. reflexivity.
      + split; [exact Hm|]. rewrite Hf2, E. reflexivity.
    - exists (snd (evaluate (prog, set_clock k s))), r, o. split.
      + rewrite (surjective_pairing (evaluate (prog, set_clock k s))), <- Hf1, E. reflexivity.
      + split; [exact Hm|]. rewrite <- Hf2, E. reflexivity. }
  rewrite <- Hp. destruct (some _); [reflexivity|]. f_equal. f_equal.
  match goal with |- IMAGE ?f _ = IMAGE ?g _ =>
    replace g with f; [reflexivity|apply functional_extensionality; intros k; rewrite Hf2; reflexivity] end.
Qed.

End Correct.

(** ** Syntactic conventions *)
Section Conv.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "cond16bit_inst_select_exp'" *)
Theorem cond16bit_inst_select_exp' : forall x (c : asm_config a) t1 t2 exp,
  x = inst_select_exp c t1 t2 exp -> no_share_inst x \/ ISA c <> Ag32.
Proof. intros x c t1 t2 exp ->. left. apply inst_select_exp_not_created_subprogs. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "cond16bit_inst_select" *)
Theorem cond16bit_inst_select : forall x (c : asm_config a) n (p : prog a),
  x = inst_select c n p /\ (no_share_inst p \/ ISA c <> Ag32) -> no_share_inst x \/ ISA c <> Ag32.
Proof.
  intros x c n p [-> [H|H]]; [left|right; exact H]. apply inst_select_not_created_subprogs, H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "remove_must_terminate_no_share_inst" *)
Theorem remove_must_terminate_no_share_inst : forall (p : prog a),
  no_share_inst p -> no_share_inst (remove_must_terminate p).
Proof.
  unfold no_share_inst. intros p; induction p using prog_nested_ind; intros Hp;
    cbn [remove_must_terminate not_created_subprogs] in *; try tauto.
  destruct ret as [[r1 [r2 [r3 [r4 r5]]]]|], h as [[h1 [h2 [h3 h4]]]|]; cbn [not_created_subprogs] in *; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "full_compile_single_no_share_inst" *)
Theorem full_compile_single_no_share_inst : forall two_reg_arith reg_count alg (c : asm_config a)
    (prog_info : (N * (N * prog a)) * option (num_map N)),
  no_share_inst (SND (SND (FST prog_info))) ->
  no_share_inst (SND (SND (full_compile_single two_reg_arith reg_count alg c prog_info))).
Proof.
  intros t rc alg c [[n [m p]] o] H. pose proof (compile_single_not_created_subprogs _ t rc alg c ((n, (m, p)), o) H) as H1.
  unfold full_compile_single. destruct (compile_single t rc alg c ((n, (m, p)), o)) as [n' [m' p']] eqn:E.
  cbn [SND] in *. apply remove_must_terminate_no_share_inst, H1.
Qed.

Section ConvAlloc.
Context (Hlsc : linear_scan_reg_alloc_correct_stmt).

Lemma fcs_props (wc : config) (ac : asm_config a) n m (prog : prog a) col :
  (no_share_inst prog \/ ISA ac <> Ag32) ->
  let '(n', (m', prog')) :=
    full_compile_single (two_reg_arith ac) (reg_count ac - (5 + LENGTH (avoid_regs ac))) (reg_alg wc) ac
      ((n, (m, prog)), col) in
  n' = n /\ m' = m /\ labels_rel (extract_labels prog) (extract_labels prog') /\
  flat_exp_conventions prog' /\
  post_alloc_conventions (reg_count ac - (5 + LENGTH (avoid_regs ac))) prog' /\
  (every_inst (inst_ok_less ac) prog /\ addr_offset_ok ac (n2w 0) /\ hw_offset_ok ac (n2w 0) /\
   byte_offset_ok ac (n2w 0) -> full_inst_ok_less ac prog') /\
  (two_reg_arith ac -> every_inst two_reg_inst prog') /\
  (no_share_inst prog' \/ ISA ac <> Ag32).
Proof.
  intros Hns.
  pose proof (full_compile_single_no_share_inst (two_reg_arith ac) (reg_count ac - (5 + LENGTH (avoid_regs ac)))
                (reg_alg wc) ac ((n, (m, prog)), col)) as Hns'.
  unfold full_compile_single, compile_single in *. cbv zeta in *. cbn [SND FST] in Hns'.
  set (k := reg_count ac - (5 + LENGTH (avoid_regs ac))) in *.
  set (p0 := word_simp.compile_exp prog) in *.
  set (p1 := inst_select ac (max_var p0 + 1) p0) in *.
  set (p2 := full_ssa_cc_trans m p1) in *.
  set (p3 := remove_dead_prog p2) in *.
  set (p4 := copy_prop (word_common_subexp_elim p3)) in *.
  set (p5 := three_to_two_reg_prog (two_reg_arith ac) p4) in *.
  set (p6 := remove_unreach p5) in *.
  set (p7 := remove_dead_prog p6) in *.
  set (p8 := word_alloc n ac (reg_alg wc) k p7 col) in *.
  split; [reflexivity|split; [reflexivity|]].
  split.
  { rewrite <- (proj2 (proj2 (proj2 (proj2 (remove_must_terminate_conventions (fun _ => true) p8 ac k))))).
    unfold p8. rewrite <- word_alloc_lab_pres. unfold p7.
    rewrite <- (proj2 (proj2 (proj2 (proj2 (proj2 (remove_dead_prog_conventions (fun _ => true) p6 ac k)))))).
    apply (labels_rel_TRANS _ (extract_labels p0)). split; [apply extract_labels_compile_exp|].
    unfold p6. replace (extract_labels p0) with (extract_labels p5); [apply labels_rel_remove_unreach|].
    unfold p5, p4, p3, p2, p1.
    rewrite <- three_to_two_reg_prog_lab_pres, extract_labels_copy_prop, extract_labels_word_common_subexp_elim,
      <- (proj2 (proj2 (proj2 (proj2 (proj2 (remove_dead_prog_conventions (fun _ => true) _ ac k)))))),
      <- full_ssa_cc_trans_lab_pres, <- inst_select_lab_pres. reflexivity. }
  split.
  { apply (proj1 (remove_must_terminate_conventions (fun _ => true) p8 ac k)).
    apply word_alloc_flat_exp_conventions.
    apply (proj1 (remove_dead_prog_conventions (fun _ => true) p6 ac k)).
    apply flat_exp_conventions_remove_unreach, three_to_two_reg_prog_flat_exp_conventions,
      flat_exp_conventions_copy_prop, flat_exp_conventions_word_common_subexp_elim.
    apply (proj1 (remove_dead_prog_conventions (fun _ => true) p2 ac k)).
    apply full_ssa_cc_trans_flat_exp_conventions, inst_select_flat_exp_conventions. }
  split.
  { apply (proj1 (proj2 (proj2 (remove_must_terminate_conventions (fun _ => true) p8 ac k)))).
    apply pre_post_conventions_word_alloc_from; [exact Hlsc|].
    apply (proj1 (proj2 (proj2 (remove_dead_prog_conventions (fun _ => true) p6 ac k)))).
    apply pre_alloc_conventions_remove_unreach, three_to_two_reg_prog_pre_alloc_conventions,
      pre_alloc_conventions_copy_prop, pre_alloc_conventions_word_common_subexp_elim.
    apply (proj1 (proj2 (proj2 (remove_dead_prog_conventions (fun _ => true) p2 ac k)))).
    apply full_ssa_cc_trans_pre_alloc_conventions. }
  split.
  { intros (Hi & Ha & Hh & Hb).
    apply (proj1 (proj2 (remove_must_terminate_conventions (fun _ => true) p8 ac k))).
    apply word_alloc_full_inst_ok_less_from; [exact Hlsc|].
    apply (proj1 (proj2 (remove_dead_prog_conventions (fun _ => true) p6 ac k))).
    apply full_inst_ok_less_remove_unreach, three_to_two_reg_prog_full_inst_ok_less,
      full_inst_ok_less_copy_prop, full_inst_ok_less_word_common_subexp_elim.
    apply (proj1 (proj2 (remove_dead_prog_conventions (fun _ => true) p2 ac k))).
    apply full_ssa_cc_trans_full_inst_ok_less, inst_select_full_inst_ok_less.
    repeat split; auto. apply compile_exp_no_inst, Hi. }
  split.
  { intros Ht.
    apply (proj1 (proj2 (proj2 (proj2 (remove_must_terminate_conventions two_reg_inst p8 ac k))))).
    apply word_alloc_two_reg_inst.
    apply (proj1 (proj2 (proj2 (proj2 (remove_dead_prog_conventions two_reg_inst p6 ac k))))).
    apply every_inst_remove_unreach, three_to_two_reg_prog_two_reg_inst, Ht. }
  destruct Hns as [Hns|Hns]; [left; apply Hns', Hns|right; exact Hns].
Qed.



Local Definition ctwc_elem (ac : asm_config a) (P0 : list (N * (N * prog a))) (x : N * (N * prog a)) : Prop :=
  let '(n, (m, prog)) := x in
  flat_exp_conventions prog /\
  post_alloc_conventions (reg_count ac - (5 + LENGTH (avoid_regs ac))) prog /\
  (EVERY (fun '(n, (m, prog)) => every_inst (inst_ok_less ac) prog) P0 /\
   addr_offset_ok ac (n2w 0) /\ hw_offset_ok ac (n2w 0) /\ byte_offset_ok ac (n2w 0) ->
   full_inst_ok_less ac prog) /\
  (two_reg_arith ac -> every_inst two_reg_inst prog) /\
  (no_share_inst prog \/ ISA ac <> Ag32).

Lemma ctwc_ind (wc : config) (ac : asm_config a) (P0 : list (N * (N * prog a))) : forall q orc,
  LENGTH orc = LENGTH q -> (forall y, In y q -> In y P0) ->
  EVERY (fun '(_, (_, prg)) => ⌜no_share_inst prg \/ ISA ac <> Ag32⌝) q ->
  let progs := MAP (full_compile_single (two_reg_arith ac) (reg_count ac - (5 + LENGTH (avoid_regs ac))) (reg_alg wc) ac)
                 (ZIP (q, orc)) in
  MAP FST progs = MAP FST q /\
  LIST_REL labels_rel (MAP (extract_labels ∘ SND ∘ SND) q) (MAP (extract_labels ∘ SND ∘ SND) progs) /\
  Forall (ctwc_elem ac P0) progs.
Proof.
  induction q as [|[n [m prog]] q IH]; intros orc Hl Hin Hq; cbv zeta.
  - rewrite (proj1 ZIP_eqns). cbn. split; [reflexivity|split; constructor].
  - destruct orc as [|col orc]; [cbn in Hl; lia|]. rewrite (proj2 (proj2 ZIP_eqns)).
    cbn [EVERY] in Hq. apply andb_prop in Hq as [Hq1 Hq2]. apply bool_decide_spec in Hq1.
    assert (Hl' : LENGTH orc = LENGTH q) by (cbn [LENGTH] in Hl; lia).
    destruct (IH orc Hl' (fun y Hy => Hin y (or_intror Hy)) Hq2) as (H1 & H2 & H3).
    pose proof (fcs_props wc ac n m prog col Hq1) as Hp.
    cbn [MAP]. destruct (full_compile_single _ _ _ _ _) as [n' [m' prog']] eqn:E.
    destruct Hp as (-> & -> & Hlab & Hf & Hpa & Hfi & Htr & Hns).
    split; [cbn [FST]; f_equal; exact H1|]. split.
    + constructor; [exact Hlab|exact H2].
    + constructor; [|exact H3]. unfold ctwc_elem. repeat split; auto.
      intros (He & Ha & Hh & Hb). apply Hfi. repeat split; auto.
      unfold is_true in He. rewrite EVERY_Forall, Forall_forall in He.
      exact (He (n, (m, prog)) (Hin _ (or_introl eq_refl))).
Qed.

(** HOL's [compile_to_word_conventions], with [linear_scanProof]'s
    [linear_scan_reg_alloc_correct] as a hypothesis (the section variable
    [Hlsc]); HOL's [EVERY2] is [LIST_REL]. *)
Theorem compile_to_word_conventions_from : forall (wc : config) (ac : asm_config a) (p : list (N * (N * prog a))),
  EVERY (fun '(_, (_, prg)) => ⌜no_share_inst prg \/ ISA ac <> Ag32⌝) p ->
  let '(_, progs) := word_to_word.compile wc ac p in
  MAP FST progs = MAP FST p /\
  LIST_REL labels_rel (MAP (extract_labels ∘ SND ∘ SND) p) (MAP (extract_labels ∘ SND ∘ SND) progs) /\
  EVERY (fun '(n, (m, prog)) =>
    ⌜flat_exp_conventions prog /\
     post_alloc_conventions (reg_count ac - (5 + LENGTH (avoid_regs ac))) prog /\
     (EVERY (fun '(n, (m, prog)) => every_inst (inst_ok_less ac) prog) p /\
      addr_offset_ok ac (n2w 0) /\ hw_offset_ok ac (n2w 0) /\ byte_offset_ok ac (n2w 0) ->
      full_inst_ok_less ac prog) /\
     (two_reg_arith ac -> every_inst two_reg_inst prog) /\
     (no_share_inst prog \/ ISA ac <> Ag32)⌝) progs.
Proof.
  intros wc ac p Hp. unfold word_to_word.compile. cbv zeta.
  pose proof (LENGTH_next_n_oracle (LENGTH p) (col_oracle wc)) as Hl.
  destruct (next_n_oracle (LENGTH p) (col_oracle wc)) as [orc col]. cbn [fst] in Hl.
  destruct (ctwc_ind wc ac p p orc Hl (fun y Hy => Hy) Hp) as (H1 & H2 & H3).
  split; [exact H1|split; [exact H2|]].
  unfold is_true. rewrite EVERY_Forall, Forall_forall. rewrite Forall_forall in H3.
  intros [n [m prog]] Hx. apply bool_decide_spec. exact (H3 _ Hx).
Qed.

End ConvAlloc.
End Conv.
