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
      with [evaluate_eqn] (HOL: [recInduct evaluate_ind]).
    - [evaluate_option_le_stack_max_preserved] needs [push_env_stack_max_eq],
      so it is stated after it (HOL states it before).
    - HOL [t with clock := k] is [set_clock k t]; [inc_clock_inc_clock]
      quantifies HOL's free [n] and [m]; in [evaluate_stack_max] HOL's
      bound variable [stack_max] is renamed [sm] (it would shadow the
      field projection). *)

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

(** Galette-only helpers for [evaluate_option_le_stack_max_preserved]. *)
Lemma option_le_NONE_r x : option_le x NONE.
Proof. destruct x; reflexivity. Qed.

Local Lemma call_env_stk_ok args ss (s : state) : stk_ok (call_env args ss s).
Proof.
  unfold call_env; unfold_sets.
  destruct (stack_size (stack s)), ss, (stack_max s); ole.
Qed.

Local Lemma flush_true_stk_ok (s t : state) :
  stk_ok s -> option_le (stack_max s) (stack_max t) -> stk_ok (flush_state true t).
Proof.
  intros Hs Ht; cbn [flush_state]; unfold_sets; cbn [stack_size FOLDR].
  destruct (stack_size (stack s)) as [k|] eqn:Ek, (locals_size s), (stack_max s), (stack_max t);
    try (pose proof (stack_size_some_at_least_one _ _ Ek)); ole.
Qed.

Local Lemma alloc_stk_ok w names (s t : state) r :
  alloc w names s = (r, t) -> stk_ok s -> stk_ok t.
Proof.
  intros H Hs; unfold alloc in H.
  destruct (cut_envs names (locals s)) as [envs|];
    [|injection H as <- <-; exact (flush_state_option_le_stack_max_preserved s true Hs)].
  destruct (gc _) as [s1|] eqn:Eg; [|injection H as <- <-; exact (flush_state_option_le_stack_max_preserved s true Hs)].
  destruct (pop_env s1) as [s2|] eqn:Ep.
  2:{ injection H as <- <-; apply (flush_true_stk_ok s); [exact Hs|].
      apply gc_const in Eg; destr_conj. match goal with E : stack_max s1 = _ |- _ => rewrite E end.
      rewrite push_env_stack_max_eq; apply option_le_max_right; left; apply option_le_refl. }
  assert (H2 : stk_ok s2).
  { unfold gc in Eg; unfold push_env, env_to_list in Eg; cbn zeta in Eg.
    unfold set_store in Eg; unfold_sets.
    cbn [dec_stack] in Eg.
    destruct (gc_fun s _) as [[wl [m st]]|]; [|discriminate].
    destruct (_ <? _); [discriminate|].
    destruct (dec_stack _ (stack s)) as [stk'|] eqn:Ed; [|discriminate].
    injection Eg as <-. unfold pop_env in Ep; unfold_sets. injection Ep as <-. unfold_sets.
    rewrite (dec_stack_stack_size _ _ _ Ed), stack_size_cons. cbn [stack_size_frame].
    destruct (stack_size (stack s)), (locals_size s), (stack_max s); ole. }
  destruct (get_store _ s2); [|injection H as <- <-; exact H2].
  destruct (has_space _ s2) as [[]|]; injection H as <- <-;
    first [exact H2 | exact (flush_state_option_le_stack_max_preserved s2 true H2)].
Qed.

Local Lemma jump_exc_stk_ok (s t : state) l :
  jump_exc s = SOME (t, l) -> stk_ok s -> stk_ok t.
Proof.
  intros H Hs; unfold jump_exc in H.
  destruct (handler s <? LENGTH (stack s)) eqn:Eh; [|discriminate].
  destruct (LASTN (handler s + 1) (stack s)) as [|[m e0 e [[n [l1 l2]]|]] xs] eqn:El; try discriminate.
  injection H as <- _. unfold_sets.
  destruct (stack_size (stack s)) as [k|] eqn:Ek.
  2:{ destruct (stack_max s); [|apply option_le_NONE_r]. destruct (locals_size s); discriminate. }
  assert (Hle : handler s + 1 <= LENGTH (stack s)) by (apply N.ltb_lt in Eh; lia).
  destruct (LASTN_stack_size_SOME _ _ _ _ (conj El (conj Ek Hle))) as (y & Hy & Hyk).
  rewrite stack_size_cons in Hy.
  destruct m as [m|]; [|discriminate Hy].
  change (stack_size_frame _) with (SOME (N.add 3 m)) in Hy.
  destruct (stack_size xs) as [z|]; [|discriminate Hy].
  assert (Hy' : y = 3 + m + z) by (symmetry; exact (f_equal THE Hy)).
  subst y. assert (Hzm : z + m <= k) by lia; clear Hyk Hy.
  destruct (locals_size s), (stack_max s); ole.
Qed.

Local Lemma share_inst_stk_ok op v ad (s t : state) r :
  share_inst op v ad s = (r, t) -> stk_ok s -> stk_ok t.
Proof.
  intros H Hs; destruct op; cbn [share_inst] in H;
    unfold sh_mem_set_var, sh_mem_load, sh_mem_load_byte, sh_mem_load16, sh_mem_load32,
      sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32 in H;
    split_H H; leaf H;
    first [ exact Hs | exact (flush_state_option_le_stack_max_preserved s true Hs) ].
Qed.

Local Ltac sm_le :=
  first [ apply option_le_refl | assumption | apply option_le_NONE_r
        | apply option_le_max_right; left; sm_le
        | rewrite push_env_stack_max_eq; sm_le ].

Local Ltac ok_base :=
  first [ assumption
        | apply option_le_NONE_r
        | apply push_call_option_le_stack_max_preserved
        | apply call_env_stk_ok
        | apply flush_state_option_le_stack_max_preserved; ok_base
        | refine (flush_state_option_le_stack_max_preserved _ true _); ok_base
        | refine (flush_state_option_le_stack_max_preserved _ false _); ok_base
        | refine (flush_true_stk_ok _ _ _ _); [eassumption|sm_le]
        | progress (unfold dec_clock, set_var, set_vars, unset_var, set_store;
            cbn [set_locals set_locals_size set_fp_regs set_store_field set_stack
              set_stack_limit set_stack_max set_stack_size set_memory set_mdomain set_sh_mdomain
              set_permute set_compile set_compile_oracle set_code_buffer set_data_buffer
              set_gc_fun set_handler set_clock set_termdep set_code set_be set_ffi
              stack locals_size stack_max]); ok_base ].

Local Ltac ok_facts :=
  repeat match goal with
         | E : alloc _ _ _ = (_, _) |- _ => let H := fresh "Ha" in pose proof (alloc_stk_ok _ _ _ _ _ E) as H; clear E
         | E : share_inst _ _ _ _ = (_, _) |- _ => let H := fresh "Ha" in pose proof (share_inst_stk_ok _ _ _ _ _ _ E) as H; clear E
         | E : jump_exc _ = SOME (_, _) |- _ => let H := fresh "Ha" in pose proof (jump_exc_stk_ok _ _ _ E) as H; clear E
         | E : pop_env ?x = SOME ?y |- _ =>
             let H := fresh "Hp" in
             assert (H : stk_ok x -> stk_ok y)
               by (intros Hx; exact (pop_env_option_le_stack_max_preserved x y (conj Hx E)));
             clear E
         | E : inst _ _ = SOME _ |- _ => apply inst_const_full in E; destr_conj
         | E : mem_store _ _ _ = SOME _ |- _ => apply mem_store_const in E; destr_conj
         | E : cut_state _ _ = SOME _ |- _ =>
             let l := fresh "l" in apply cut_state_const in E; destruct E as [l ->]
         end;
  repeat match goal with H : ?x = ?y |- _ =>
           lazymatch x with
           | stack _ => rewrite H in * | locals_size _ => rewrite H in * | stack_max _ => rewrite H in *
           end; clear H end;
  repeat match goal with Hi : is_true (option_le _ _) -> _ |- _ =>
           specialize (Hi ltac:(ok_base)) end.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_option_le_stack_max_preserved" *)
Theorem evaluate_option_le_stack_max_preserved : forall (p : prog a) (s : state) r t,
  evaluate (p, s) = (r, t) /\ stk_ok s -> stk_ok t.
Proof.
  enough (G : forall x : prog a * state, forall r t, evaluate x = (r, t) -> stk_ok (snd x) -> stk_ok t)
    by (intros p s r t [H Hs]; exact (G (p, s) r t H Hs)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r t H Hs; cbn [snd] in *.
  rewrite evaluate_eqn in H; destruct p; cbn [evaluate_body] in H; io_step IH H;
  repeat match goal with E : (_, _) = (_, _) |- _ => injection E as <- <- end;
  cbn [snd] in *.
  all: ok_facts; ok_base.
Qed.

(** Galette-only helpers for [evaluate_stack_max_le]. *)
Local Lemma alloc_stack_max_le w names (s t : state) r :
  alloc w names s = (r, t) -> option_le (stack_max s) (stack_max t).
Proof.
  intros H; unfold alloc in H; split_H H; leaf H; try apply option_le_refl;
    repeat match goal with
           | E : gc _ = SOME _ |- _ => pose proof (gc_const _ _ E); destr_conj; clear E
           | E : pop_env _ = SOME _ |- _ => pose proof (pop_env_const _ _ E); destr_conj; clear E
           end;
    unfold flush_state; repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn [stack_max set_locals_size set_store_field set_stack set_locals];
    repeat match goal with H : stack_max _ = stack_max _ |- _ => rewrite H; clear H end;
    rewrite push_env_stack_max_eq; apply option_le_max_right; left; apply option_le_refl.
Qed.

Local Ltac sm_facts :=
  repeat match goal with
         | E : alloc _ _ _ = (_, _) |- _ => apply alloc_stack_max_le in E
         | E : inst _ _ = SOME _ |- _ => apply inst_const_full in E; destr_conj
         | E : mem_store _ _ _ = SOME _ |- _ => apply mem_store_const in E; destr_conj
         | E : jump_exc _ = SOME (_, _) |- _ => apply jump_exc_const in E; destr_conj
         | E : share_inst _ _ _ _ = (_, _) |- _ => apply share_inst_const in E; destr_conj
         | E : pop_env _ = SOME _ |- _ => apply pop_env_const in E; destr_conj
         | E : cut_state _ _ = SOME _ |- _ =>
             let l := fresh "l" in apply cut_state_const in E; destruct E as [l ->]
         end;
  repeat match goal with
         | |- context [call_env ?x ?y (push_env ?e ?h ?z)] =>
             lazymatch goal with
             | _ : is_true (option_le (stack_max z) (stack_max (call_env x y (push_env e h z)))) |- _ => fail
             | _ => pose proof (call_push_env_option_le_stack_max z x y e h)
             end
         | H : context [call_env ?x ?y (push_env ?e ?h ?z)] |- _ =>
             lazymatch goal with
             | _ : is_true (option_le (stack_max z) (stack_max (call_env x y (push_env e h z)))) |- _ => fail
             | _ => pose proof (call_push_env_option_le_stack_max z x y e h)
             end
         | H : context [call_env ?x ?y ?z] |- _ =>
             lazymatch z with push_env _ _ _ => fail | _ => idtac end;
             lazymatch goal with
             | _ : is_true (option_le (stack_max z) (stack_max (call_env x y z))) |- _ => fail
             | _ => pose proof (call_env_option_le_stack_max z x y)
             end
         end;
  unfold flush_state, dec_clock, set_var, set_vars, unset_var, set_store in *;
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  cbn [fst snd] in *; unfold_sets.


Local Ltac ole_chain :=
  first [ apply option_le_refl | assumption | apply option_le_NONE_r
        | eapply option_le_trans; split; [eassumption|ole_chain]
        | apply option_le_max_right; left; ole_chain
        | rewrite push_env_stack_max_eq; ole_chain ].

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_stack_max_le" *)
Theorem evaluate_stack_max_le : forall (c0 : prog a) (s1 : state) res s2,
  evaluate (c0, s1) = (res, s2) -> option_le (stack_max s1) (stack_max s2).
Proof.
  enough (G : forall x : prog a * state, forall r t, evaluate x = (r, t) -> option_le (stack_max (snd x)) (stack_max t))
    by (intros c0 s1 res s2 H; exact (G (c0, s1) res s2 H)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r t H; cbn [snd].
  rewrite evaluate_eqn in H; destruct p; cbn [evaluate_body] in H; io_step IH H;
  repeat match goal with E : (_, _) = (_, _) |- _ => injection E as <- <- end;
  sm_facts;
  repeat match goal with H : stack_max ?x = stack_max ?y |- _ => rewrite H in *; clear H end;
  try ole_chain.
Qed.

(** HOL's bound variable [stack_max] (which would shadow the field) is [sm]. *)
(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_stack_max" *)
Theorem evaluate_stack_max : forall (c0 : prog a) (s1 : state) res s2,
  evaluate (c0, s1) = (res, s2) ->
  match stack_max s1 with
  | NONE => stack_max s2 = NONE
  | SOME sm => the sm (stack_max s2) >= sm
  end.
Proof.
  intros c0 s1 res s2 H; apply evaluate_stack_max_le in H.
  destruct (stack_max s1) as [x|], (stack_max s2) as [y|]; cbn in *; try discriminate; try reflexivity;
    unfold is_true in H; rewrite ?N.leb_le in H; unfold the; lia.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_stack_max_IS_SOME" *)
Theorem evaluate_stack_max_IS_SOME : forall (c0 : prog a) (s1 : state) res s2,
  evaluate (c0, s1) = (res, s2) /\ IS_SOME (stack_max s2) -> IS_SOME (stack_max s1).
Proof.
  intros c0 s1 res s2 [H Hs]; apply evaluate_stack_max in H.
  destruct (stack_max s1); [reflexivity|]. rewrite H in Hs; exact Hs.
Qed.

(** Facts on [stack_limit] (Galette-only). *)
Local Ltac sl_facts :=
  repeat match goal with
         | E : alloc _ _ _ = (_, _) |- _ => apply alloc_const in E; destr_conj
         | E : inst _ _ = SOME _ |- _ => apply inst_const_full in E; destr_conj
         | E : mem_store _ _ _ = SOME _ |- _ => apply mem_store_const in E; destr_conj
         | E : jump_exc _ = SOME (_, _) |- _ => apply jump_exc_const in E; destr_conj
         | E : share_inst _ _ _ _ = (_, _) |- _ => apply share_inst_const in E; destr_conj
         | E : pop_env _ = SOME _ |- _ => apply pop_env_const in E; destr_conj
         | E : cut_state _ _ = SOME _ |- _ =>
             let l := fresh "l" in apply cut_state_const in E; destruct E as [l ->]
         end;
  repeat match goal with
         | |- context [push_env ?x ?y ?z] =>
             lazymatch goal with
             | _ : stack_limit (push_env x y z) = _ |- _ => fail
             | _ => pose proof (push_env_const x y z); destr_conj
             end
         | H : context [push_env ?x ?y ?z] |- _ =>
             lazymatch goal with
             | _ : stack_limit (push_env x y z) = _ |- _ => fail
             | _ => pose proof (push_env_const x y z); destr_conj
             end
         end;
  destr_conj;
  unfold flush_state, dec_clock, call_env, set_var, set_vars, unset_var, set_store in *;
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  cbn [fst snd] in *; unfold_sets.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_stack_limit" *)
Theorem evaluate_stack_limit : forall (c0 : prog a) (s1 : state) res s2,
  evaluate (c0, s1) = (res, s2) -> stack_limit s2 = stack_limit s1.
Proof.
  enough (G : forall x : prog a * state, forall r t, evaluate x = (r, t) -> stack_limit t = stack_limit (snd x))
    by (intros c0 s1 res s2 H; exact (G (c0, s1) res s2 H)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r t H; cbn [snd].
  rewrite evaluate_eqn in H; destruct p; cbn [evaluate_body] in H; io_step IH H;
  repeat match goal with E : (_, _) = (_, _) |- _ => injection E as <- <- end;
  sl_facts; cbn [snd] in *; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_stack_limit_stack_max_eq" *)
Theorem evaluate_stack_limit_stack_max_eq : forall (c0 : prog a) (s1 : state) res s2,
  evaluate (c0, s1) = (res, s2) /\ the (stack_limit s1) (stack_max s1) >= stack_limit s1 ->
  the (stack_limit s2) (stack_max s2) >= stack_limit s2.
Proof.
  intros c0 s1 res s2 [H Hl].
  pose proof (evaluate_stack_max _ _ _ _ H) as Hm; apply evaluate_stack_limit in H.
  rewrite H; unfold the in *.
  destruct (stack_max s1), (stack_max s2); try discriminate; lia.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_stack_limit_stack_max" *)
Theorem evaluate_stack_limit_stack_max : forall (c0 : prog a) (s1 : state) res s2,
  evaluate (c0, s1) = (res, s2) /\ the (stack_limit s1 + 1) (stack_max s1) > stack_limit s1 ->
  the (stack_limit s2 + 1) (stack_max s2) > stack_limit s2.
Proof.
  intros c0 s1 res s2 [H Hl].
  pose proof (evaluate_stack_max _ _ _ _ H) as Hm; apply evaluate_stack_limit in H.
  rewrite H; unfold the in *.
  destruct (stack_max s1), (stack_max s2); try discriminate; lia.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "inc_clock_def" *)
Definition inc_clock (n : N) (t : state) : state := set_clock (clock t + n) t.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "inc_clock_0" *)
Theorem inc_clock_0 : forall t, inc_clock 0 t = t.
Proof.
  intros t; unfold inc_clock; apply state_component_equality; unfold_sets.
  repeat split; try reflexivity; lia.
Qed.

(** HOL's free variables [n] and [m] are quantified first. *)
(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "inc_clock_inc_clock" *)
Theorem inc_clock_inc_clock : forall n m t, inc_clock n (inc_clock m t) = inc_clock (n + m) t.
Proof.
  intros n m t; unfold inc_clock; apply state_component_equality; unfold_sets.
  repeat split; try reflexivity; lia.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_call_push_dec_option_le_stack_max" *)
Theorem evaluate_call_push_dec_option_le_stack_max :
  forall (p : prog a) args sz env handler (s : state) res t ck,
  evaluate (p, call_env args sz (push_env env handler (dec_clock (set_clock ck s)))) = (res, t) ->
  option_le (stack_max (call_env args sz (push_env env handler s))) (stack_max t).
Proof.
  intros p args sz env handler s res t ck H; apply evaluate_stack_max_le in H.
  unfold call_env in *; unfold_sets.
  rewrite (proj1 (push_env_dec_clock_stack _ _ _)), (proj2 (push_env_dec_clock_stack _ _ _)) in H.
  rewrite (proj1 (push_env_with_const env handler s ck (compile s) (compile_oracle s) (code s) (termdep s) (locals s))) in H.
  unfold_sets; exact H.
Qed.

(** As [io_loop] in [wordProps.clock], for [stack_max] (Galette-only). *)
Local Ltac sm_loop IH extra H :=
  repeat first
    [ bd_contra
    | progress (rewrite ?fix_clock_evaluate in H)
    | progress (rewrite ?fix_clock_evaluate)
    | match goal with
      | E : (?x =? 0)%N = false |- context [(?x + extra =? 0)%N] =>
          let E' := fresh "E" in
          assert (E' : (x + extra =? 0)%N = false) by (apply N.eqb_neq; apply N.eqb_neq in E; lia);
          rewrite E'; clear E'; cbn beta iota zeta
      end
    | match goal with
      | E : evaluate (?p', ?s'') = (?r', ?t) |- _ =>
          let Hc := fresh "Hc" in
          pose proof (evaluate_clock p' s'' r' t E) as Hc;
          let Heq := fresh "Heq" in let Hn := fresh "Hn" in
          destruct (classical_dec (r' = SOME TimeOut)) as [Heq | Hn];
          [ first
              [ discriminate Heq
              | try subst r';
                let Hp := fresh "Hp" in
                pose proof (IH (p', s'') ltac:(wd_eval_lt) _ _ E) as Hp;
                pose proof (evaluate_stack_max_le _ _ _ _ E); clear E;
                cbn [fst snd] in Hp;
                match goal with
                | |- context [evaluate (p', ?X)] =>
                    replace X with (set_clock (clock s'' + extra) s'') by wd_eq;
                    let r2 := fresh "r" in let t2 := fresh "t" in let E2 := fresh "E" in
                    destruct (evaluate (p', set_clock (clock s'' + extra) s'')) as [r2 t2] eqn:E2;
                    pose proof (evaluate_stack_max_le _ _ _ _ E2); clear E2; cbn [snd] in Hp
                end;
                try ac_simpl H ]
          | let Hi := fresh "Hi" in
            pose proof (evaluate_stack_max_le _ _ _ _ E);
            pose proof (evaluate_add_clock extra p' s'' r' t (conj E Hn)) as Hi; clear E;
            match goal with
            | |- context [evaluate (p', ?X)] =>
                replace X with (set_clock (clock s'' + extra) s'') by wd_eq; rewrite Hi; clear Hi
            end ]
      end
    | match type of H with
      | context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; ac_simpl H
      end ].

Local Ltac sm_goal_split :=
  repeat first
    [ match goal with
      | |- context [evaluate (?q, ?Y)] =>
          let r3 := fresh "r" in let t3 := fresh "t" in let E3 := fresh "E" in
          destruct (evaluate (q, Y)) as [r3 t3] eqn:E3;
          pose proof (evaluate_stack_max_le _ _ _ _ E3); clear E3; cbn beta iota zeta
      end
    | match goal with
      | |- context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
      end ].

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_stack_max_only_grows" *)
Theorem evaluate_stack_max_only_grows : forall (p : prog a) (s : state) r t ck r' t',
  evaluate (p, s) = (r, t) /\ evaluate (p, inc_clock ck s) = (r', t') ->
  option_le (stack_max t) (stack_max t').
Proof.
  enough (G : forall extra (x : prog a * state) r s1, evaluate x = (r, s1) ->
    option_le (stack_max s1)
      (stack_max (snd (evaluate (fst x, set_clock (clock (snd x) + extra) (snd x))))))
    by (intros p s r t ck r' t' [H1 H2]; pose proof (G ck (p, s) r t H1) as G';
        cbn [fst snd] in G'; unfold inc_clock in H2; rewrite H2 in G'; exact G').
  intros extra x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s1 H; cbn [fst snd].
  destruct (classical_dec (r = SOME TimeOut)) as [->|Hr].
  2:{ rewrite (evaluate_add_clock extra p s r s1 (conj H Hr)); apply option_le_refl. }
  rewrite evaluate_eqn in H |- *.
  destruct p; cbn [evaluate_body] in H |- *; ac_simpl H; sm_loop IH extra H;
  try discriminate H; try (injection H; intros; subst); try rewrite H;
  repeat match goal with
         | E : alloc _ _ _ = _ |- context [alloc _ _ _] => rewrite E
         | E : share_inst _ _ _ _ = _ |- context [share_inst _ _ _ _] => rewrite E
         end;
  cbn [PAIR_MAP snd fst]; rw_cases;
  sm_goal_split;
  autorewrite with wdc in *;
  sm_facts;
  repeat match goal with H : stack_max ?x = stack_max ?y |- _ => rewrite H in *; clear H end;
  try ole_chain.
Qed.

End StackSize.
