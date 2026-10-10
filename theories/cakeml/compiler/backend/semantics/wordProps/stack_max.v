(** * CakeML [wordProps]: stack bounds

    Port of the part of [cakeml/compiler/backend/semantics/wordPropsScript.sml]
    between [locals_rel_evaluate_thm] and [evaluate_code_only_grows]:
    [gc_fun_ok], the lemmas on [stack_max] and [stack_size]
    ([evaluate_option_le_stack_max_preserved], [evaluate_stack_max_le],
    [evaluate_stack_max_only_grows], ...), [stack_limit], and [inc_clock].

    Carrier notes:
    - HOL's [$+] on [num option]s is [N.add] under [OPTION_MAP2]; HOL's
      [x >= y] is [y <= x] and [x > y] is [y < x].
    - HOL [s with f := v] is [set_f v s]; [s.stack_size] is
      [state_stack_size s].
    - Proofs about [evaluate] are by well-founded induction on [eval_lt]
      with [evaluate_eqn] (HOL: [recInduct evaluate_ind]). *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
From Galette.cakeml.misc Require Import misc.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang wordLang.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem wordConvs backendProps.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import
  consts clock consts_with dec_clock code stack_swap.
Open Scope N_scope.

Section GcFun.
Context {a : N}.
Local Open Scope fmap_scope.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "gc_fun_ok_def" *)
Definition gc_fun_ok (f : gc_fun_type a) : Prop :=
  forall wl m d s wl1 m1 s1,
    Handler IN FDOM s /\ f (wl, (m, (d, s \\ Handler))) = SOME (wl1, (m1, s1)) ->
    LENGTH wl = LENGTH wl1 /\ ~ (Handler IN FDOM s1) /\
    f (wl, (m, (d, s))) = SOME (wl1, (m1, s1 |+ (Handler, s ' Handler))).

End GcFun.

Section StackSize.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(** The invariant of [evaluate_option_le_stack_max_preserved]
    (Galette-only abbreviation). *)
Local Abbreviation stk_ok s :=
  (option_le (OPTION_MAP2 N.add (stack_size (stack s)) (locals_size s)) (stack_max s)).

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "push_env_dec_clock_stack" *)
Theorem push_env_dec_clock_stack : forall y (opt : option (N * (prog a * (N * N)))) (t : state),
  stack_max (push_env y opt (dec_clock t)) = stack_max (push_env y opt t) /\
  stack (push_env y opt (dec_clock t)) = stack (push_env y opt t).
Proof.
  intros y [[? [? [? ?]]]|] t; unfold push_env; destruct (env_to_list _ _); split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "set_store_stack_max_greater_bound" *)
Theorem set_store_stack_max_greater_bound : forall v x (s t : state),
  set_store v x s = t /\ stk_ok s -> stk_ok t.
Proof. intros v x s t [<- H]; exact H. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "stack_size_some_at_least_one" *)
Theorem stack_size_some_at_least_one : forall (stk : list (stack_frame a)) sz,
  stack_size stk = SOME sz -> 1 <= sz.
Proof.
  induction stk as [|f stk IH]; intros sz H; [injection H as <-; lia|].
  change (OPTION_MAP2 N.add (stack_size_frame f) (stack_size stk) = SOME sz) in H.
  unfold OPTION_MAP2 in H. destruct (stack_size_frame f), (stack_size stk) eqn:E; cbn in H; try discriminate.
  injection H as <-. specialize (IH _ eq_refl); lia.
Qed.

Local Lemma stack_size_cons (f : stack_frame a) stk :
  stack_size (f :: stk) = OPTION_MAP2 N.add (stack_size_frame f) (stack_size stk).
Proof. reflexivity. Qed.

Local Ltac ole := unfold is_true, OPTION_MAP2, option_le in *;
  cbn [IS_SOME THE andb option_map] in *;
  repeat rewrite N.leb_le in *; rewrite ?MAX_max in *;
  intuition (try discriminate; try lia).

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "push_call_option_le_stack_max_preserved" *)
Theorem push_call_option_le_stack_max_preserved : forall args sz env handler (s : state),
  option_le
    (OPTION_MAP2 N.add (stack_size (stack (call_env args sz (push_env env handler s))))
                       (locals_size (call_env args sz (push_env env handler s))))
    (stack_max (call_env args sz (push_env env handler s))).
Proof.
  intros args sz env handler s.
  remember (push_env env handler s) as t.
  unfold call_env; cbn [stack set_stack_max set_locals_size set_locals locals_size stack_max].
  destruct (stack_size (stack t)) as [x|], sz as [y|], (stack_max t) as [z|]; ole.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "pop_env_option_le_stack_max_preserved" *)
Theorem pop_env_option_le_stack_max_preserved : forall (s t : state),
  stk_ok s /\ pop_env s = SOME t -> stk_ok t.
Proof.
  intros s t [H Hp]; unfold pop_env in Hp.
  destruct (stack s) as [|[m e0 e h] xs] eqn:E; [discriminate|].
  rewrite stack_size_cons in H.
  destruct h as [[n x]|]; injection Hp as <-; cbn [stack locals_size set_handler set_locals_size set_stack
    set_locals stack_max stack_size_frame] in *; unfold OPTION_MAP in *;
    destruct m as [m|], (stack_size xs) as [k|], (locals_size s) as [l|], (stack_max s) as [z|]; ole.
Qed.

Local Lemma dec_stack_stack_size (xs : list (word_loc a)) stk stk' :
  dec_stack xs stk = SOME stk' -> stack_size stk' = stack_size stk.
Proof.
  revert xs stk'; induction stk as [|[n l0 l h] stk IH]; intros xs stk' H; cbn in H.
  - destruct xs; [injection H as <-; reflexivity|discriminate].
  - destruct (_ <? _); [discriminate|].
    destruct (dec_stack _ stk) as [s|] eqn:E; [|discriminate]. injection H as <-.
    rewrite !stack_size_cons, (IH _ _ E). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "dec_stack_stack_size_some_not_none" *)
Theorem dec_stack_stack_size_some_not_none : forall (xs : list (word_loc a)) stk stk' x,
  dec_stack xs stk = SOME stk' /\ stack_size stk = SOME x -> stack_size stk' <> NONE.
Proof. intros xs stk stk' x [H1 H2]; rewrite (dec_stack_stack_size _ _ _ H1), H2; discriminate. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "dec_stack_stack_size_not_none_not_none" *)
Theorem dec_stack_stack_size_not_none_not_none : forall (xs : list (word_loc a)) stk stk',
  dec_stack xs stk = SOME stk' /\ stack_size stk <> NONE -> stack_size stk' <> NONE.
Proof. intros xs stk stk' [H1 H2]; rewrite (dec_stack_stack_size _ _ _ H1); exact H2. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "dec_stack_stack_size_some_leq" *)
Theorem dec_stack_stack_size_some_leq : forall (xs : list (word_loc a)) stk stk' x y,
  dec_stack xs stk = SOME stk' /\ stack_size stk = SOME x /\ stack_size stk' = SOME y -> y <= x.
Proof.
  intros xs stk stk' x y (H1 & H2 & H3); rewrite (dec_stack_stack_size _ _ _ H1), H2 in H3.
  injection H3 as ->; lia.
Qed.

(** HOL's [let t = flush_state p s in ...] is unfolded. *)
(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "flush_state_option_le_stack_max_preserved" *)
Theorem flush_state_option_le_stack_max_preserved : forall (s : state) p,
  stk_ok s -> stk_ok (flush_state p s).
Proof.
  intros s [] H; cbn [flush_state stack locals_size stack_max set_locals_size set_store_field set_stack
    set_locals] in *;
    destruct (stack_size (stack s)) as [k|] eqn:Ek, (locals_size s) as [l|], (stack_max s) as [z|];
    cbn [stack_size FOLDR] in *; try (pose proof (stack_size_some_at_least_one _ _ Ek)); ole.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "LASTN_stack_size_SOME" *)
Theorem LASTN_stack_size_SOME : forall n (stack : list (stack_frame a)) stack' x,
  LASTN n stack = stack' /\ stack_size stack = SOME x /\ n <= LENGTH stack ->
  exists y, stack_size stack' = SOME y /\ y <= x.
Proof.
  intros n stack; induction stack as [|f stack IH]; intros stack' x (H1 & H2 & H3).
  - subst stack'; exists x; split; [exact H2|lia].
  - rewrite stack_size_cons in H2. unfold OPTION_MAP2 in H2.
    destruct (stack_size_frame f) as [fs|] eqn:Ef, (stack_size stack) as [k|] eqn:Ek; cbn in H2; try discriminate.
    injection H2 as <-.
    destruct (N.eq_dec n (LENGTH (f :: stack))) as [Hn|Hn].
    + rewrite LASTN_LENGTH_cond in H1 by exact Hn. subst stack'. exists (fs + k).
      rewrite stack_size_cons, Ef, Ek; split; [reflexivity|lia].
    + assert (Hle : n <= LENGTH stack) by (rewrite !LENGTH_length in *; cbn [length] in *; lia).
      rewrite LASTN_cons_le in H1 by exact Hle.
      destruct (IH stack' k (conj H1 (conj eq_refl Hle))) as (y & Hy & Hyk).
      exists y; split; [exact Hy|lia].
Qed.

(** I'm pretty sure this is defined somewhere else too. *)
(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "OPTION_MAP2_ADD_0" *)
Theorem OPTION_MAP2_ADD_0 : forall m,
  OPTION_MAP2 N.add m (SOME 0) = m /\ OPTION_MAP2 N.add (SOME 0) m = m.
Proof. intros [m|]; unfold OPTION_MAP2; cbn; split; try reflexivity; f_equal; lia. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "option_le_stack_size_nil" *)
Theorem option_le_stack_size_nil : forall (xs : list (stack_frame a)) opt,
  option_le (stack_size (@nil (stack_frame a))) (OPTION_MAP2 N.add (stack_size xs) opt).
Proof.
  intros xs opt. destruct (stack_size xs) as [k|] eqn:Ek, opt as [o|]; cbn; try reflexivity.
  pose proof (stack_size_some_at_least_one _ _ Ek); ole.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "push_env_stack_max_eq" *)
Theorem push_env_stack_max_eq : forall env (handler : option (N * (prog a * (N * N)))) (s : state),
  stack_max (push_env env handler s) =
  OPTION_MAP2 MAX (stack_max s) (stack_size (stack (push_env env handler s))).
Proof.
  intros env [[? [? [? ?]]]|] s; unfold push_env; destruct (env_to_list _ _); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "call_env_option_le_stack_max" *)
Theorem call_env_option_le_stack_max : forall (s : state) args1 ss,
  option_le (stack_max s) (stack_max (call_env args1 ss s)).
Proof. intros s args1 ss; unfold call_env; cbn [stack_max set_stack_max]; apply option_le_max_right; left; apply option_le_refl. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "call_push_env_option_le_stack_max" *)
Theorem call_push_env_option_le_stack_max : forall (s : state) args1 ss envs handler,
  option_le (stack_max s) (stack_max (call_env args1 ss (push_env envs handler s))).
Proof.
  intros s args1 ss envs handler. eapply option_le_trans; split; [|apply call_env_option_le_stack_max].
  rewrite push_env_stack_max_eq; apply option_le_max_right; left; apply option_le_refl.
Qed.

End StackSize.
