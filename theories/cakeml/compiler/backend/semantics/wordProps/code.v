(** * CakeML [wordProps]: environments and the code table

    Port of the part of [cakeml/compiler/backend/semantics/wordPropsScript.sml]
    after [evaluate_NONE_stack_size_const]: [env_to_list] lemmas, the code
    table predicates [no_alloc_code], [no_install_code], [no_mt_code] with
    their [find_code] lemmas, the constancy of the code table under
    [no_install] ([no_install_evaluate_const_code]), [get_code_labels] as
    [not_created_subprogs], [evaluate_code_only_grows] (stated earlier in
    HOL, but grouped here with the other code-table lemmas) and
    [word_cmp_Word_Word].

    Carrier notes:
    - HOL's [sorting$PERM] is not ported: [PERM_fromAList], [stack_size_perm]
      and [env_to_list_PERM] are stated with Rocq's [Permutation] and are
      untagged (as [PERM_list_rearrange] in [wordProps.consts]); HOL's
      overload [PERM_STACK] is the Galette-only [PERM_STACK] below.
    - [subspt] on code tables needs decidable equality on
      [wordLang$prog]; a classical instance ([wprog_eq_dec_classical],
      Galette-only) is provided, as in [stackProps].
    - Proofs about [evaluate] are by well-founded induction on [eval_lt]
      with [evaluate_eqn] (HOL: [recInduct evaluate_ind]). *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.cakeml.misc Require Import misc.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.basis.pure Require Import mllist.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common wordLang.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem wordConvs.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import consts clock consts_with.
From Stdlib Require Import Permutation.
Open Scope N_scope.

(** Decidable equality on wordLang programs, classically (HOL equality);
    used by [subspt] on code tables (Galette-only). *)
#[global] Instance wprog_eq_dec_classical {a : N} : EqDecision (wordLang.prog a) :=
  fun x y => classical_dec (x = y).

(** ** [env_to_list] *)

Section Env.
Context {a : N}.

Local Lemma env_to_list_perm (y : num_map (word_loc a)) f :
  Permutation (toAList y) (FST (env_to_list y f)) /\ NoDup (MAP FST (FST (env_to_list y f))).
Proof.
  unfold env_to_list; cbn [FST fst].
  pose proof (ALL_DISTINCT_MAP_FST_toAList y) as Hd.
  unfold is_true in Hd; rewrite ALL_DISTINCT_NoDup in Hd.
  assert (Hs : Permutation (toAList y) (sort key_val_compare (toAList y))) by apply sort_Permutation.
  assert (Hd2 : ALL_DISTINCT (sort key_val_compare (toAList y))).
  { unfold is_true; rewrite ALL_DISTINCT_NoDup.
    eapply Permutation_NoDup; [exact Hs|]. eapply NoDup_map_inv; exact Hd. }
  pose proof (PERM_list_rearrange (f 0) _ Hd2) as Hr.
  assert (HP : Permutation (toAList y) (list_rearrange (f 0) (sort key_val_compare (toAList y))))
    by (eapply Permutation_trans; eassumption).
  split; [exact HP|]. eapply Permutation_NoDup; [apply Permutation_map, HP|exact Hd].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "env_to_list_lookup_equiv" *)
Theorem env_to_list_lookup_equiv : forall (y : num_map (word_loc a)) f q r,
  env_to_list y f = (q, r) ->
  (forall n, ALOOKUP q n = lookup n y) /\
  (forall x1 x2, MEM (x1, x2) q -> lookup x1 y = SOME x2).
Proof.
  intros y f q r H.
  destruct (env_to_list_perm y f) as [HP Hd]; rewrite H in HP, Hd; cbn [FST fst] in HP, Hd.
  assert (Hm : forall x1 x2, MEM (x1, x2) q <-> lookup x1 y = SOME x2).
  { intros x1 x2; rewrite <- MEM_toAList; unfold is_true; rewrite !MEM_In.
    split; apply Permutation_in; [symmetry|]; exact HP. }
  split; [|intros x1 x2; apply Hm].
  intros n; destruct (lookup n y) as [v|] eqn:E.
  - apply ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME; split; [unfold is_true; rewrite ALL_DISTINCT_NoDup; exact Hd|].
    apply Hm, E.
  - apply ALOOKUP_NONE. intros Hn; unfold is_true in Hn; rewrite MEM_In in Hn.
    apply in_map_iff in Hn as [[k v] [Hk Hin]]; cbn in Hk; subst k.
    assert (Hv : MEM (n, v) q) by (unfold is_true; rewrite MEM_In; exact Hin).
    apply Hm in Hv; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "env_to_list_ALL_DISTINCT" *)
Theorem env_to_list_ALL_DISTINCT : forall (y : num_map (word_loc a)) perm vs other,
  env_to_list y perm = (vs, other) -> ALL_DISTINCT (MAP FST vs).
Proof.
  intros y perm vs other H; destruct (env_to_list_perm y perm) as [_ Hd]; rewrite H in Hd.
  unfold is_true; rewrite ALL_DISTINCT_NoDup; exact Hd.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "env_to_list_ALL_DISTINCT_FST" *)
Theorem env_to_list_ALL_DISTINCT_FST : forall (y : num_map (word_loc a)) perm,
  ALL_DISTINCT (MAP FST (FST (env_to_list y perm))).
Proof.
  intros y perm; destruct (env_to_list_perm y perm) as [_ Hd].
  unfold is_true; rewrite ALL_DISTINCT_NoDup; exact Hd.
Qed.

End Env.

(** ** Code table predicates *)

Section CodeTable.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "no_alloc_code_def" *)
Definition no_alloc_code (code : num_map (N * prog a)) : Prop :=
  forall k n p, lookup k code = SOME (n, p) -> no_alloc p.

Local Lemma find_code_lookup (dest : option N) (args : list (word_loc a)) code lsize args1 expr ps :
  find_code dest args code lsize = SOME (args1, (expr, ps)) ->
  exists k n, lookup k code = SOME (n, expr).
Proof.
  unfold find_code; intros H; split_H H; try discriminate H;
    injection H as <- <- <-; eexists _, _; eassumption.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "no_alloc_find_code" *)
Theorem no_alloc_find_code : forall code dest (args : list (word_loc a)) lsize args1 expr ps,
  find_code dest args code lsize = SOME (args1, (expr, ps)) /\ no_alloc_code code ->
  no_alloc expr.
Proof.
  intros code dest args lsize args1 expr ps [H Hc].
  destruct (find_code_lookup _ _ _ _ _ _ _ H) as [k [n Hk]]; exact (Hc _ _ _ Hk).
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "no_install_code_def" *)
Definition no_install_code (code : num_map (N * prog a)) : Prop :=
  forall k n p, lookup k code = SOME (n, p) -> no_install p.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "no_install_find_code" *)
Theorem no_install_find_code : forall code dest (args : list (word_loc a)) lsize args1 expr ps,
  no_install_code code /\ find_code dest args code lsize = SOME (args1, (expr, ps)) ->
  no_install expr.
Proof.
  intros code dest args lsize args1 expr ps [Hc H].
  destruct (find_code_lookup _ _ _ _ _ _ _ H) as [k [n Hk]]; exact (Hc _ _ _ Hk).
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "no_mt_code_def" *)
Definition no_mt_code (code : num_map (N * prog a)) : Prop :=
  forall k n p, lookup k code = SOME (n, p) -> no_mt p.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "no_mt_find_code" *)
Theorem no_mt_find_code : forall code dest (args : list (word_loc a)) lsize args1 expr ps,
  find_code dest args code lsize = SOME (args1, (expr, ps)) /\ no_mt_code code ->
  no_mt expr.
Proof.
  intros code dest args lsize args1 expr ps [H Hc].
  destruct (find_code_lookup _ _ _ _ _ _ _ H) as [k [n Hk]]; exact (Hc _ _ _ Hk).
Qed.


(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "get_code_labels_not_created" *)
Theorem get_code_labels_not_created : forall (p : prog a) x,
  x IN get_code_labels p <->
  ~ not_created_subprogs (fun sp => sp <> Call NONE (SOME x) [] NONE /\ sp <> LocValue 0 x) p.
Proof.
  intros p x.
  induction p as [| | | | | | |p IHp|ret dest args h Hr Hh|p1 p2 IHp1 IHp2|c r ri p1 p2 IHp1 IHp2
                 |n1 p n2 IHp| | | | | | | | |r l| | | | |] using prog_nested_ind;
    cbn [get_code_labels not_created_subprogs]; unfold pred_set.UNION, pred_set.INSERT, pred_set.EMPTY in *; unfold pred_set.IN in *;
    try (split; [intros []|intros Hn; apply Hn; exact Logic.I]);
    try (split; [intros []|intros Hn; apply Hn; split; discriminate]).
  - rewrite IHp; split; [intros Hn [_ H]; exact (Hn H)|intros Hn H; apply Hn; split; [split; discriminate|exact H]].
  - destruct dest as [d|]; destruct ret as [[v [cs [rp [l1 l2]]]]|];
      destruct h as [[hv [hp [hl1 hl2]]]|]; cbn beta iota in Hr, Hh |- *;
      unfold pred_set.IN in Hr, Hh; rewrite ?Hr, ?Hh;
      repeat match goal with |- context [not_created_subprogs ?P ?q] =>
        lazymatch goal with
        | _ : {not_created_subprogs P q} + {~ not_created_subprogs P q} |- _ => fail
        | _ => pose proof (classical_dec (not_created_subprogs P q))
        end
      end; repeat match goal with H : {_} + {_} |- _ => destruct H end;
      try (destruct (classical_dec (d = x)) as [->|?]);
      firstorder congruence.
  - rewrite IHp1, IHp2;
    match goal with |- context [not_created_subprogs ?P p1] =>
      destruct (classical_dec (not_created_subprogs P p1)),
        (classical_dec (not_created_subprogs P p2)); tauto end.
  - rewrite IHp1, IHp2;
    match goal with |- context [not_created_subprogs ?P p1] =>
      destruct (classical_dec (not_created_subprogs P p1)),
        (classical_dec (not_created_subprogs P p2)); tauto end.
  - exact IHp.
  - split; [intros [->|[]] [_ H]; exact (H eq_refl)|].
    intros Hn; destruct (classical_dec (x = l)) as [->|Hl]; [left; reflexivity|].
    exfalso; apply Hn; split; [discriminate|intros E; injection E as ->; exact (Hl eq_refl)].
Qed.

End CodeTable.

(** ** The code table during evaluation *)

(** Facts on the [code] field of the primitives in the context. *)
Local Ltac code_facts :=
  repeat match goal with
         | E : alloc _ _ _ = (_, _) |- _ => apply alloc_const in E
         | E : inst _ _ = SOME _ |- _ => apply inst_const_full in E
         | E : mem_store _ _ _ = SOME _ |- _ => apply mem_store_const in E
         | E : jump_exc _ = SOME (_, _) |- _ => apply jump_exc_const in E
         | E : share_inst _ _ _ _ = (_, _) |- _ => apply share_inst_const in E
         | E : pop_env _ = SOME _ |- _ => apply pop_env_const in E
         | E : cut_state _ _ = SOME _ |- _ =>
             let l := fresh "l" in apply cut_state_const in E; destruct E as [l ->]
         end;
  repeat match goal with
         | |- context [push_env ?x ?y ?z] =>
             lazymatch goal with
             | _ : clock (push_env x y z) = _ |- _ => fail
             | _ => pose proof (push_env_const x y z); destr_conj
             end
         | H : context [push_env ?x ?y ?z] |- _ =>
             lazymatch goal with
             | _ : clock (push_env x y z) = _ |- _ => fail
             | _ => pose proof (push_env_const x y z); destr_conj
             end
         end;
  destr_conj;
  unfold flush_state, dec_clock, call_env, set_var, set_vars, unset_var, set_store in *;
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  cbn [fst snd] in *; unfold_sets.

Local Ltac sub_chain :=
  first [ apply subspt_refl | eassumption | apply subspt_union
        | eapply subspt_trans; split; [eassumption|sub_chain] ].

Section EvalCode.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "no_install_evaluate_const_code" *)
Theorem no_install_evaluate_const_code : forall (prog : prog a) (s : state) result s1,
  evaluate (prog, s) = (result, s1) /\ no_install prog /\ no_install_code (code s) ->
  code s = code s1.
Proof.
  enough (G : forall x : wordLang.prog a * state, forall r t, evaluate x = (r, t) ->
            no_install (fst x) -> no_install_code (code (snd x)) -> code (snd x) = code t)
    by (intros p s r t (H & H1 & H2); exact (G (p, s) r t H H1 H2)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r t H Hn Hc; cbn [fst snd] in *.
  rewrite evaluate_eqn in H; destruct p; cbn [evaluate_body] in H; io_step IH H;
  repeat match goal with E : (_, _) = (_, _) |- _ => injection E as <- <- end;
  repeat match goal with E : ?v = (_, _) |- _ => is_var v; subst v end;
  try (exfalso; unfold no_install in Hn; cbn [not_created_subprogs] in Hn; apply Hn; reflexivity);
  repeat match goal with
         | Hi : ?A -> no_install_code ?cs -> code ?x = code ?y |- _ =>
             let H1 := fresh "Hn" in let H2 := fresh "Hc" in
             assert (H1 : A) by
               (first [ eapply no_install_find_code; split; eassumption
                      | unfold no_install in *; cbn [not_created_subprogs STOP] in *; destr_conj;
                        assumption ]);
             assert (H2 : no_install_code cs) by
               (code_facts; repeat match goal with E : code ?x = code ?y |- _ => rewrite E in * end;
                assumption);
             specialize (Hi H1 H2)
         end;
  code_facts; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_code_only_grows" *)
Theorem evaluate_code_only_grows : forall (p : prog a) (s : state) r t,
  evaluate (p, s) = (r, t) -> subspt (code s) (code t).
Proof.
  enough (G : forall x : prog a * state, forall r t, evaluate x = (r, t) -> subspt (code (snd x)) (code t))
    by (intros p s r t H; exact (G (p, s) r t H)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r t H; cbn [snd].
  rewrite evaluate_eqn in H; destruct p; cbn [evaluate_body] in H; io_step IH H;
  repeat match goal with E : (_, _) = (_, _) |- _ => injection E as <- <- end;
  code_facts;
  repeat match goal with H : code ?x = code ?y |- _ => rewrite H in * end;
  try sub_chain.

Qed.

End EvalCode.

(** ** Permuted stacks *)

Section PermStack.
Context {a : N}.

(** HOL's overload [PERM_STACK] (Galette-only definition), with Rocq's
    [Permutation] for HOL's [PERM]. *)
Definition PERM_STACK (s1 s2 : stack_frame a) : Prop :=
  match s1, s2 with
  | StackFrame ss l env h, StackFrame ss' l' env' h' =>
      ss = ss' /\ h = h' /\ l = l' /\ Permutation env env' /\ ALL_DISTINCT (MAP FST env)
  end.

(** HOL's [PERM_fromAList], with [Permutation] for [PERM]. *)
Theorem PERM_fromAList : forall (l1 l2 : list (N * word_loc a)),
  Permutation l1 l2 /\ ALL_DISTINCT (MAP FST l1) ->
  fromAList l1 = fromAList l2.
Proof.
  intros l1 l2 [HP Hd]. apply spt_eq_thm; [split; apply wf_fromAList|].
  intros n; rewrite !lookup_fromAList.
  assert (Hd2 : ALL_DISTINCT (MAP FST l2)).
  { unfold is_true in *; rewrite ALL_DISTINCT_NoDup in *.
    eapply Permutation_NoDup; [apply Permutation_map, HP|exact Hd]. }
  destruct (ALOOKUP l2 n) as [v|] eqn:E.
  - apply ALOOKUP_MEM in E. apply ALOOKUP_ALL_DISTINCT_MEM; split; [exact Hd|].
    unfold is_true in *; rewrite MEM_In in *. apply (Permutation_in _ (Permutation_sym HP)), E.
  - apply ALOOKUP_NONE; apply ALOOKUP_NONE in E. intros Hm; apply E.
    unfold is_true in *; rewrite MEM_In in *. apply (Permutation_in _ (Permutation_map _ HP)), Hm.
Qed.

(** HOL's [stack_size_perm], with [Permutation] for [PERM]. *)
Theorem stack_size_perm : forall (l1 l2 : list (stack_frame a)),
  LIST_REL PERM_STACK l1 l2 -> stack_size l1 = stack_size l2.
Proof.
  intros l1 l2 H; induction H as [|[ss l env h] [ss' l' env' h'] l1 l2 Hp _ IH]; [reflexivity|].
  destruct Hp as (-> & -> & _).
  change (OPTION_MAP2 N.add (stack_size_frame (StackFrame ss' l env h')) (stack_size l1) =
          OPTION_MAP2 N.add (stack_size_frame (StackFrame ss' l' env' h')) (stack_size l2)).
  rewrite IH; reflexivity.
Qed.

(** HOL's [env_to_list_PERM], with [Permutation] for [PERM]. *)
Theorem env_to_list_PERM : forall (env : num_map (word_loc a)) perm perm',
  Permutation (FST (env_to_list env perm)) (FST (env_to_list env perm')).
Proof.
  intros env perm perm'.
  destruct (env_to_list_perm env perm) as [H1 _], (env_to_list_perm env perm') as [H2 _].
  eapply Permutation_trans; [symmetry; exact H1|exact H2].
Qed.

End PermStack.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "word_cmp_Word_Word" *)
Theorem word_cmp_Word_Word : forall {a} cmp (c0 c' : word a),
  wordSem.word_cmp cmp (Word c0) (Word c') = SOME (asm.word_cmp cmp c0 c').
Proof. intros a cmp c0 c'; destruct cmp; reflexivity. Qed.
