(** * CakeML [word_to_stackProof]: variables and parallel moves

    Part of the port of
    [cakeml/compiler/backend/proofs/word_to_stackProofScript.sml] (HOL lines
    2856-3720): reading and writing variables through [state_rel],
    [wMoveSingle] and [wMoveAux], the parallel-move lemmas and
    [call_dest_lemma].

    Notes: as in [state_rel.v].  HOL's [wMoveSingle] arguments [INL]/[INR]
    are [inl]/[inr]. *)

From Galette Require Import Base Classical.
From Stdlib Require FinFun Finite.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.misc.misc Require Import fromList2.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend.reg_alloc Require Import parmove.
From Galette.cakeml.compiler.backend.reg_alloc.parmove Require proofs.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend Require Import word_to_stack.
From Galette.cakeml.compiler.backend.semantics Require wordSem.
From Galette.cakeml.compiler.backend.semantics Require Import stackSem stackProps.
From Galette.cakeml.compiler.backend.proofs.word_to_stackProof Require Import basic compile_props state_rel gc stack_rel syntax.
Import wordLang (word_loc, Word, Loc).
Import wordSem (stack_frame, StackFrame).
Open Scope N_scope.

(** ** Galette-only helpers *)

Lemma decide_True {P : Prop} {d : Decision P} {X} (x y : X) : P -> (if decide P then x else y) = x.
Proof. intros H. destruct (decide P); [reflexivity|contradiction]. Qed.

Lemma decide_False {P : Prop} {d : Decision P} {X} (x y : X) : ~ P -> (if decide P then x else y) = y.
Proof. intros H. destruct (decide P); [contradiction|reflexivity]. Qed.

Lemma even_div2 n : EVEN n -> n = 2 * (n DIV 2).
Proof. intros H. apply N.even_spec in H as [p ->]. rewrite (N.mul_comm 2 p), N.div_mul by lia. lia. Qed.

Lemma mul2_div2 x : (2 * x) DIV 2 = x.
Proof. rewrite N.mul_comm, N.div_mul by lia. reflexivity. Qed.

Lemma oEL_DROP {A} m j (l : list A) : oEL j (DROP m l) = oEL (m + j) l.
Proof. rewrite !oEL_nth_error, DROP_skipn, nth_error_skipn. f_equal. lia. Qed.

Lemma oEL_LUPDATE_eq {A} (x : A) i l : i < LENGTH l -> oEL i (LUPDATE x i l) = SOME x.
Proof.
  revert i; induction l as [|y l IH]; intros i H; [cbn in H; lia|].
  rewrite LUPDATE_cons_eq, LENGTH_cons' in *. destruct (N.eqb_spec i 0) as [->|Hi]; [reflexivity|].
  cbn [oEL]. replace (i =? 0) with false by (symmetry; apply N.eqb_neq; exact Hi). apply IH. lia.
Qed.

Lemma oEL_TAKE_ge {A} n m (l : list A) : m <= n -> oEL n (TAKE m l) = NONE.
Proof.
  intros H. rewrite oEL_nth_error. apply nth_error_None. rewrite TAKE_firstn, length_firstn. lia.
Qed.

Lemma oEL_SOME_EL {A} {HA : Inhabited A} n (l : list A) v : oEL n l = SOME v -> EL n l = v.
Proof.
  intros H. pose proof (oEL_SOME_lt _ _ _ H) as Hl. rewrite oEL_EL in H by exact Hl. injection H as <-. reflexivity.
Qed.

Lemma DROP_LUPDATE_lt {A} (x : A) i n l : i < n -> DROP n (LUPDATE x i l) = DROP n l.
Proof.
  revert i n; induction l as [|y l IH]; intros i n H; [rewrite LUPDATE_nil; reflexivity|].
  rewrite LUPDATE_cons_eq. rewrite !DROP_skipn. replace (N.to_nat n) with (Datatypes.S (N.to_nat (n - 1))) by lia.
  cbn [skipn]. destruct (N.eqb_spec i 0); [reflexivity|].
  pose proof (IH (i - 1) (n - 1) ltac:(lia)) as IH'. rewrite !DROP_skipn in IH'. exact IH'.
Qed.

Lemma set_regs_set_var_regs {a c ffi_t} (t : stackSem.state a c ffi_t) r v :
  set_regs (regs t) (stackSem.set_var r v t) = t.
Proof. destruct t; reflexivity. Qed.

Lemma inst_mov {a c ffi_t} r1 r2 (t : stackSem.state a c ffi_t) :
  inst (Arith (Binop asm.Or r1 r2 (Reg r2))) t =
  match FLOOKUP (regs t) r2 with NONE => NONE | SOME w => SOME (stackSem.set_var r1 w t) end.
Proof. unfold inst. rewrite !bd_true' by reflexivity. reflexivity. Qed.

Section Moves.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wMoveAux_thm" *)
Theorem wMoveAux_thm : forall kf x xs t,
  evaluate (wMoveAux [] kf, t) = (NONE, t) /\
  evaluate (wMoveAux (x :: xs) kf, t) = evaluate (Seq (wMoveSingle x kf) (wMoveAux xs kf), t).
Proof.
  intros kf x xs t. split; [apply ev_skip|].
  destruct xs as [|y ys]; [|reflexivity]. cbn [wMoveAux]. rewrite ev_seq.
  destruct (evaluate (wMoveSingle x kf, t)) as [[r|] t1]; [reflexivity|]. rewrite ev_skip. reflexivity.
Qed.

(** [state_rel] does not look at the registers from [k] on (Galette-only). *)
Lemma state_rel_set_regs ac k f f' s t lens extra R :
  state_rel ac k f f' s t lens extra ->
  (forall r, r < k -> FLOOKUP R r = FLOOKUP (regs t) r) ->
  state_rel ac k f f' s (set_regs R t) lens extra.
Proof.
  intros H HR. sr_destr H. sr_split; stk_fields; try assumption.
  intros n v Hn. destruct (Hloc n v Hn) as [He Hr]. split; [exact He|].
  destruct (n DIV 2 <? k) eqn:Ek; [|exact Hr]. rewrite HR by (apply N.ltb_lt; exact Ek). exact Hr.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_get_var_imp" *)
Theorem state_rel_get_var_imp : forall ac k f f' s t lens extra x v,
  state_rel ac k f f' s t lens extra /\
  wordSem.get_var (2 * x) s = SOME v /\
  x < k ->
  FLOOKUP (regs t) x = SOME v.
Proof.
  intros ac k f f' s t lens extra x v (H & Hv & Hx). sr_destr H. unfold wordSem.get_var in Hv.
  destruct (Hloc _ _ Hv) as [_ Hr]. rewrite mul2_div2 in Hr.
  replace (x <? k) with true in Hr by (symmetry; apply N.ltb_lt; exact Hx). exact Hr.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_get_var_imp'" *)
Theorem state_rel_get_var_imp' : forall ac k f f' s t lens extra n v,
  state_rel ac k f f' s t lens extra /\
  wordSem.get_var n s = SOME v /\
  EVEN n /\
  n DIV 2 < k ->
  stackSem.get_var (n DIV 2) t = SOME v.
Proof.
  intros ac k f f' s t lens extra n v (H & Hv & He & Hn). unfold stackSem.get_var.
  rewrite (even_div2 n He) in Hv. eapply state_rel_get_var_imp. eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_get_var_imp2" *)
Theorem state_rel_get_var_imp2 : forall ac k f f' s t lens x v,
  state_rel ac k f f' s t lens 0 /\
  wordSem.get_var (2 * x) s = SOME v /\
  ~ (x < k) ->
  EL (stack_space t + (f + k - (x + 1))) (stackSem.stack t) = v.
Proof.
  intros ac k f f' s t lens x v (H & Hv & Hx). sr_destr H. unfold wordSem.get_var in Hv.
  destruct (Hloc _ _ Hv) as [_ Hr]. rewrite mul2_div2 in Hr.
  replace (x <? k) with false in Hr by (symmetry; apply N.ltb_ge; lia). destruct Hr as [Hr Hxk].
  assert (Hf : f = f' + 1) by (destruct (f' =? 0) eqn:E; [apply N.eqb_eq in E; lia|lia]).
  rewrite N.add_0_r in Hr. rewrite oEL_TAKE_lt in Hr by lia. rewrite oEL_DROP in Hr.
  apply oEL_SOME_EL in Hr. rewrite <- Hr. f_equal. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_set_var_k" *)
Theorem state_rel_set_var_k : forall ac k f f' s t lens extra v,
  (state_rel ac k f f' s (stackSem.set_var (k + 1) v t) lens extra <->
   state_rel ac k f f' s t lens extra) /\
  (state_rel ac k f f' s (stackSem.set_var k v t) lens extra <->
   state_rel ac k f f' s t lens extra).
Proof.
  intros ac k f f' s t lens extra v. split; split; intros H.
  - rewrite <- (set_regs_set_var_regs t (k + 1) v). apply state_rel_set_regs; [exact H|].
    intros r Hr. stk_fields. rewrite FLOOKUP_UPDATE. destruct (decide (k + 1 = r)); [lia|reflexivity].
  - apply state_rel_set_regs; [exact H|]. intros r Hr. rewrite FLOOKUP_UPDATE.
    destruct (decide (k + 1 = r)); [lia|reflexivity].
  - rewrite <- (set_regs_set_var_regs t k v). apply state_rel_set_regs; [exact H|].
    intros r Hr. stk_fields. rewrite FLOOKUP_UPDATE. destruct (decide (k = r)); [lia|reflexivity].
  - apply state_rel_set_regs; [exact H|]. intros r Hr. rewrite FLOOKUP_UPDATE.
    destruct (decide (k = r)); [lia|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_set_var" *)
Theorem state_rel_set_var : forall ac k f f' s t lens extra x v,
  state_rel ac k f f' s t lens extra /\
  x < k ->
  state_rel ac k f f' (wordSem.set_var (2 * x) v s) (stackSem.set_var x v t) lens extra.
Proof.
  intros ac k f f' s t lens extra x v (H & Hx). sr_destr H. unfold wordSem.set_var, stackSem.set_var.
  sr_split; ws_fields; stk_fields; try assumption.
  - apply wf_insert, Hwf.
  - intros n w Hn. rewrite lookup_insert in Hn. destruct (decide (n = 2 * x)) as [->|Hne].
    + injection Hn as <-. rewrite mul2_div2. split; [apply N.even_spec; exists x; lia|].
      replace (x <? k) with true by (symmetry; apply N.ltb_lt; exact Hx).
      rewrite FLOOKUP_UPDATE. destruct (decide (x = x)); [reflexivity|congruence].
    + destruct (Hloc n w Hn) as [He Hr]. split; [exact He|].
      destruct (n DIV 2 <? k); [|exact Hr]. rewrite FLOOKUP_UPDATE.
      destruct (decide (x = n DIV 2)) as [E|]; [|exact Hr].
      exfalso. apply Hne. rewrite (even_div2 n He), <- E. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_set_var'" *)
Theorem state_rel_set_var' : forall ac k f f' s t lens extra x y v,
  state_rel ac k f f' s t lens extra /\
  x < k /\ y = x * 2 ->
  state_rel ac k f f' (wordSem.set_var y v s) (stackSem.set_var x v t) lens extra.
Proof.
  intros ac k f f' s t lens extra x y v (H & Hx & ->). rewrite N.mul_comm. apply state_rel_set_var. auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_set_var2" *)
Theorem state_rel_set_var2 : forall ac k f f' s t lens x v st sp,
  state_rel ac k f f' s t lens 0 /\
  ~ (x < k) /\ x < f' + k /\ st = stackSem.stack t /\ sp = stack_space t ->
  state_rel ac k f f' (wordSem.set_var (2 * x) v s)
    (set_stack (LUPDATE v (sp + (f + k - (x + 1))) st) t) lens 0.
Proof.
  intros ac k f f' s t lens x v st sp (H & Hx & Hx' & -> & ->). sr_destr H.
  assert (Hf : f = f' + 1) by (destruct (f' =? 0) eqn:E; [apply N.eqb_eq in E; lia|lia]).
  rewrite N.add_0_r in *.
  set (i := stack_space t + (f + k - (x + 1))) in *.
  assert (Hi : i < stack_space t + f) by (unfold i; lia).
  assert (ED : DROP f (DROP (stack_space t) (LUPDATE v i (stackSem.stack t))) =
               DROP f (DROP (stack_space t) (stackSem.stack t))).
  { rewrite !DROP_DROP_EQ. apply DROP_LUPDATE_lt. lia. }
  unfold wordSem.set_var. sr_split; ws_fields; stk_fields; rewrite ?N.add_0_r, ?ED, ?LENGTH_LUPDATE'; try assumption.
  - apply wf_insert, Hwf.
  - unfold stack_size_rel in *. rewrite LENGTH_LUPDATE'. exact Hssr.
  - intros n w Hn. rewrite lookup_insert in Hn. destruct (decide (n = 2 * x)) as [->|Hne].
    + injection Hn as <-. rewrite mul2_div2. split; [apply N.even_spec; exists x; lia|].
      replace (x <? k) with false by (symmetry; apply N.ltb_ge; lia). split; [|lia].
      rewrite oEL_TAKE_lt by lia. rewrite oEL_DROP. replace (stack_space t + (f - 1 - (x - k))) with i by (unfold i; lia).
      apply oEL_LUPDATE_eq. lia.
    + destruct (Hloc n w Hn) as [He Hr]. split; [exact He|].
      destruct (n DIV 2 <? k) eqn:Ek; [exact Hr|]. apply N.ltb_ge in Ek. destruct Hr as [Hr Hr2]. split; [|exact Hr2].
      assert (Hnx : n DIV 2 <> x) by (intros E; apply Hne; rewrite (even_div2 n He), E; reflexivity).
      rewrite oEL_TAKE_lt in Hr |- * by lia. rewrite oEL_DROP in Hr |- *.
      rewrite oEL_LUPDATE_neq by (unfold i; lia). exact Hr.
Qed.

(** Galette-only: the three kinds of instructions of [wMoveSingle]. *)
Lemma ev_mov r1 r2 t v :
  FLOOKUP (regs t) r2 = SOME v ->
  evaluate (Inst (Arith (Binop asm.Or r1 r2 (Reg r2))), t) = (NONE, stackSem.set_var r1 v t).
Proof. intros H. rewrite ev_inst, inst_mov, H. reflexivity. Qed.

Lemma ev_load_slot ac k f f' s t lens x v r :
  state_rel ac k f f' s t lens 0 -> wordSem.get_var (2 * x) s = SOME v -> ~ (x < k) ->
  evaluate (StackLoad r (f - 1 - (x - k)), t) = (NONE, stackSem.set_var r v t).
Proof.
  intros H Hv Hx. pose proof (state_rel_get_var_imp2 ac k f f' s t lens x v (conj H (conj Hv Hx))) as HE.
  sr_destr H. unfold wordSem.get_var in Hv. destruct (Hloc _ _ Hv) as [_ Hr]. rewrite mul2_div2 in Hr.
  replace (x <? k) with false in Hr by (symmetry; apply N.ltb_ge; lia). destruct Hr as [_ Hxk].
  assert (Hf : f = f' + 1) by (destruct (f' =? 0) eqn:E; [apply N.eqb_eq in E; lia|lia]).
  rewrite ev_stackload. unfold is_true in Hus. rewrite Hus. cbn [negb].
  replace (stack_space t + (f - 1 - (x - k)) <? LENGTH (stackSem.stack t)) with true
    by (symmetry; apply N.ltb_lt; lia).
  replace (f - 1 - (x - k)) with (f + k - (x + 1)) by lia. rewrite HE. reflexivity.
Qed.

Lemma ev_store_slot ac k f f' s t lens y v r :
  state_rel ac k f f' s t lens 0 -> ~ (y < k) -> y < f' + k -> stackSem.get_var r t = SOME v ->
  evaluate (StackStore r (f - 1 - (y - k)), t) =
    (NONE, set_stack (LUPDATE v (stack_space t + (f + k - (y + 1))) (stackSem.stack t)) t).
Proof.
  intros H Hy Hy' Hv. sr_destr H.
  assert (Hf : f = f' + 1) by (destruct (f' =? 0) eqn:E; [apply N.eqb_eq in E; lia|lia]).
  rewrite ev_stackstore. unfold is_true in Hus. rewrite Hus. cbn [negb].
  replace (LENGTH (stackSem.stack t) <=? stack_space t + (f - 1 - (y - k))) with false
    by (symmetry; apply N.leb_gt; lia).
  rewrite Hv. replace (f - 1 - (y - k)) with (f + k - (y + 1)) by lia. reflexivity.
Qed.

Lemma state_rel_var_bound ac k f f' s t lens extra x v :
  state_rel ac k f f' s t lens extra -> wordSem.get_var (2 * x) s = SOME v -> ~ (x < k) ->
  x < f' + k /\ f = f' + 1.
Proof.
  intros H Hv Hx. sr_destr H. unfold wordSem.get_var in Hv. destruct (Hloc _ _ Hv) as [_ Hr].
  rewrite mul2_div2 in Hr. replace (x <? k) with false in Hr by (symmetry; apply N.ltb_ge; lia).
  destruct Hr as [_ Hxk]. destruct (f' =? 0) eqn:E; [apply N.eqb_eq in E; lia|lia].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wMoveSingle_thm" *)
Theorem wMoveSingle_thm : forall ac k f f' s t lens x y v,
  state_rel ac k f f' s t lens 0 /\
  match x with NONE => stackSem.get_var (k + 1) t = SOME v
  | SOME x => wordSem.get_var (x * 2) s = SOME v end /\
  match y with SOME x => x < f' + k | _ => True end ->
  exists t',
    evaluate (wMoveSingle (format_var k y, format_var k x) (k, (f, f')), t) = (NONE, t') /\
    state_rel ac k f f' match y with NONE => s | SOME y => wordSem.set_var (y * 2) v s end t' lens 0 /\
    (y = NONE -> stackSem.get_var (k + 1) t' = SOME v) /\
    (y <> NONE -> stackSem.get_var (k + 1) t' = stackSem.get_var (k + 1) t) /\
    LENGTH (stackSem.stack t') = LENGTH (stackSem.stack t) /\ stack_space t' = stack_space t.
Proof.
  intros ac k f f' s t lens x y v (H & Hx & Hy).
  assert (Hk : 4 < k) by (sr_destr H; exact Hk).
  assert (Hgk : forall r w t0, r <> k + 1 ->
            stackSem.get_var (k + 1) (stackSem.set_var r w t0) = stackSem.get_var (k + 1) t0).
  { intros r w t0 Hr. unfold stackSem.get_var, stackSem.set_var. stk_fields. rewrite FLOOKUP_UPDATE.
    destruct (decide (r = k + 1)); [lia|reflexivity]. }
  assert (Hgs : forall r w t0, stackSem.get_var r (stackSem.set_var r w t0) = SOME w).
  { intros r w t0. unfold stackSem.get_var, stackSem.set_var. stk_fields. rewrite FLOOKUP_UPDATE.
    destruct (decide (r = r)); [reflexivity|congruence]. }
  unfold format_var.
  destruct y as [y0|], x as [x0|].
  - rewrite N.mul_comm in Hx |- *. destruct (y0 <? k) eqn:Ey, (x0 <? k) eqn:Ex; to_prop.
    + (* reg <- reg *)
      cbn [wMoveSingle]. rewrite (ev_mov _ _ _ v) by (eapply state_rel_get_var_imp; eauto).
      eexists; split; [reflexivity|]. split; [apply state_rel_set_var; auto|].
      split; [discriminate|]. split; [intros _; apply Hgk; lia|]. split; reflexivity.
    + (* reg <- slot *)
      cbn [wMoveSingle]. rewrite (ev_load_slot ac k f f' s t lens x0 v) by (auto; lia).
      eexists; split; [reflexivity|]. split; [apply state_rel_set_var; auto|].
      split; [discriminate|]. split; [intros _; apply Hgk; lia|]. split; reflexivity.
    + (* slot <- reg *)
      cbn [wMoveSingle].
      rewrite (ev_store_slot ac k f f' s t lens y0 v x0) by (auto; try lia; eapply state_rel_get_var_imp; eauto).
      eexists; split; [reflexivity|]. split; [apply state_rel_set_var2; split; [exact H|]; split; [lia|]; split; [lia|]; split; reflexivity|].
      split; [discriminate|]. split; [intros _; reflexivity|].
      stk_fields. rewrite LENGTH_LUPDATE'. split; reflexivity.
    + (* slot <- slot *)
      cbn [wMoveSingle]. rewrite ev_seq.
      rewrite (ev_load_slot ac k f f' s t lens x0 v) by (auto; lia).
      assert (H1 : state_rel ac k f f' s (stackSem.set_var k v t) lens 0) by (apply state_rel_set_var_k; exact H).
      rewrite (ev_store_slot ac k f f' s _ lens y0 v k H1) by (auto; lia).
      eexists; split; [reflexivity|].
      split; [apply state_rel_set_var2; split; [exact H1|]; split; [lia|]; split; [lia|]; split; reflexivity|].
      split; [discriminate|].
      split; [intros _; unfold stackSem.get_var; stk_fields; rewrite FLOOKUP_UPDATE;
              destruct (decide (k = k + 1)); [lia|reflexivity]|].
      stk_fields. rewrite LENGTH_LUPDATE'. split; reflexivity.
  - destruct (y0 <? k) eqn:Ey; to_prop.
    + cbn [wMoveSingle]. rewrite (ev_mov _ _ _ v) by exact Hx.
      eexists; split; [reflexivity|]. split; [rewrite N.mul_comm; apply state_rel_set_var; auto|].
      split; [discriminate|]. split; [intros _; apply Hgk; lia|]. split; reflexivity.
    + cbn [wMoveSingle]. rewrite (ev_store_slot ac k f f' s t lens y0 v (k + 1)) by (auto; lia).
      eexists; split; [reflexivity|]. split; [rewrite N.mul_comm; apply state_rel_set_var2; split; [exact H|]; split; [lia|]; split; [lia|]; split; reflexivity|].
      split; [discriminate|]. split; [intros _; reflexivity|].
      stk_fields. rewrite LENGTH_LUPDATE'. split; reflexivity.
  - rewrite N.mul_comm in Hx. destruct (x0 <? k) eqn:Ex; to_prop.
    + cbn [wMoveSingle]. rewrite (ev_mov _ _ _ v) by (eapply state_rel_get_var_imp; eauto).
      eexists; split; [reflexivity|]. split; [apply state_rel_set_var_k; exact H|].
      split; [intros _; apply Hgs|]. split; [congruence|]. split; reflexivity.
    + cbn [wMoveSingle]. rewrite (ev_load_slot ac k f f' s t lens x0 v) by (auto; lia).
      eexists; split; [reflexivity|]. split; [apply state_rel_set_var_k; exact H|].
      split; [intros _; apply Hgs|]. split; [congruence|]. split; reflexivity.
  - cbn [wMoveSingle]. rewrite (ev_mov _ _ _ v) by exact Hx.
    eexists; split; [reflexivity|]. split; [apply state_rel_set_var_k; exact H|].
    split; [intros _; apply Hgs|]. split; [congruence|]. split; reflexivity.
Qed.

End Moves.

Section GetVars.
Context {a : N} {C F : Type}.
Implicit Types (s : wordSem.state a C F).

Lemma get_var_set_var' x k (v : word_loc a) s :
  wordSem.get_var x (wordSem.set_var k v s) = if decide (x = k) then SOME v else wordSem.get_var x s.
Proof. unfold wordSem.get_var, wordSem.set_var. ws_fields. apply lookup_insert. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "IS_SOME_get_vars_set_var" *)
Theorem IS_SOME_get_vars_set_var : forall k (v : word_loc a) ls s,
  IS_SOME (wordSem.get_vars ls s) -> IS_SOME (wordSem.get_vars ls (wordSem.set_var k v s)).
Proof.
  intros k v ls s. induction ls as [|x ls IH]; [reflexivity|]. cbn [wordSem.get_vars].
  rewrite get_var_set_var'.
  destruct (wordSem.get_var x s) as [w|] eqn:Ex; [|discriminate].
  destruct (wordSem.get_vars ls s) as [ws|]; [|discriminate]. intros _.
  specialize (IH eq_refl). destruct (wordSem.get_vars ls (wordSem.set_var k v s)) as [ws'|]; [|discriminate].
  destruct (decide (x = k)); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "IS_SOME_get_vars_EVERY" *)
Theorem IS_SOME_get_vars_EVERY : forall xs s,
  IS_SOME (wordSem.get_vars xs s) = EVERY (fun x => IS_SOME (wordSem.get_var x s)) xs.
Proof.
  intros xs s. induction xs as [|x xs IH]; [reflexivity|]. cbn [wordSem.get_vars EVERY].
  destruct (wordSem.get_var x s); [|reflexivity]. cbn [IS_SOME andb]. rewrite <- IH.
  destruct (wordSem.get_vars xs s); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "with_same_locals" *)
Theorem with_same_locals : forall s, wordSem.set_locals (wordSem.locals s) s = s.
Proof. intros []; reflexivity. Qed.

End GetVars.

Lemma set_locals_set_locals {a C F} (s : wordSem.state a C F) l1 l2 :
  wordSem.set_locals l1 (wordSem.set_locals l2 s) = wordSem.set_locals l1 s.
Proof. destruct s; reflexivity. Qed.

Lemma find_index_shift' {X} `{EqDecision X} (y : X) l : forall n,
  find_index y l (n + 1) = option_map (fun i => i + 1) (find_index y l n).
Proof.
  induction l as [|x l IH]; intros n; cbn [find_index]; [reflexivity|].
  destruct (decide (x = y)); [reflexivity|apply IH].
Qed.

Section MoveAux.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wMoveAux_seqsem" *)
Theorem evaluate_wMoveAux_seqsem : forall ac k f f' lens (ms : list (option N * option N)) s t
    (r : option N -> option (word_loc a)),
  state_rel ac k f f' s t lens 0 /\
  (forall i v, r (SOME i) = SOME v <-> wordSem.get_var (2 * i) s = SOME v) /\
  (forall v, r NONE = SOME v -> stackSem.get_var (k + 1) t = SOME v) /\
  IS_SOME (wordSem.get_vars (MAP (fun x => 2 * THE x) (FILTER IS_SOME (MAP SND ms))) s) /\
  match find_index NONE (MAP SND ms) 0 with
  | NONE => True
  | SOME i =>
      match find_index NONE (MAP FST ms) 0 with
      | NONE => IS_SOME (r NONE)
      | SOME j => i <= j -> IS_SOME (r NONE)
      end
  end /\
  EVERY (fun '(x, y) => ⌜forall a0, x = SOME a0 \/ y = SOME a0 -> a0 < f' + k⌝) ms /\
  ALL_DISTINCT (FILTER IS_SOME (MAP FST ms)) ->
  exists t',
    evaluate (wMoveAux (MAP (format_var k ## format_var k) ms) (k, (f, f')), t) = (NONE, t') /\
    state_rel ac k f f'
      (wordSem.set_vars
        (MAP (fun x => 2 * THE x) (FILTER IS_SOME (MAP FST (REVERSE ms))))
        (MAP THE (MAP (seqsem ms r) (FILTER IS_SOME (MAP FST (REVERSE ms)))))
        s) t' lens 0 /\
    LENGTH (stackSem.stack t') = LENGTH (stackSem.stack t) /\ stack_space t' = stack_space t.
Proof.
  intros ac k f f' lens ms. induction ms as [|[y x] ms IH]; intros s t r (Hs & Hr & Hrn & Hgv & Hfi & Hev & Had).
  - exists t. cbn [MAP map]. split; [apply (proj1 (wMoveAux_thm _ (inl 0, inl 0) [] t))|].
    cbn. unfold wordSem.set_vars. cbn [alist_insert]. rewrite with_same_locals. auto.
  - cbn [MAP map PAIR_MAP]. rewrite (proj2 (wMoveAux_thm _ _ _ _)), ev_seq.
    change ((format_var k ## format_var k) (y, x)) with (format_var k y, format_var k x).
    cbn [MAP map FST SND fst snd] in Hgv, Hfi, Had.
    cbn [EVERY] in Hev. apply andb_prop in Hev as [Hh Hev]. apply bool_decide_spec in Hh.
    assert (Hv : exists v, r x = SOME v /\
      match x with NONE => stackSem.get_var (k + 1) t = SOME v
      | SOME x0 => wordSem.get_var (x0 * 2) s = SOME v end).
    { destruct x as [x0|].
      - cbn [FILTER filter IS_SOME MAP map THE] in Hgv. cbn [wordSem.get_vars] in Hgv.
        destruct (wordSem.get_var (2 * x0) s) as [v|] eqn:Ev; [|discriminate].
        exists v. split; [apply Hr, Ev|]. rewrite N.mul_comm. exact Ev.
      - assert (Hr0 : IS_SOME (r NONE)).
        { revert Hfi. cbn [find_index]. rewrite (decide_True (P := NONE = NONE)) by reflexivity.
          destruct (decide (y = NONE)); [intros H; apply H; lia|].
          match goal with |- context [match ?m with _ => _ end] => destruct m end;
            intros H; [apply H; lia|exact H]. }
        destruct (r NONE) as [v|] eqn:Ev; [|discriminate]. exists v. split; [reflexivity|]. apply Hrn; reflexivity. }
    destruct Hv as (v & Hrx & Hv).
    assert (Hy : match y with SOME y0 => y0 < f' + k | NONE => True end).
    { destruct y as [y0|]; [|exact Logic.I]. apply Hh. left; reflexivity. }
    destruct (wMoveSingle_thm ac k f f' s t lens x y v (conj Hs (conj Hv Hy))) as (t1 & E1 & Hs1 & Hn1 & Hn2 & Hl1 & Hsp1).
    rewrite E1.
    set (s1 := match y with NONE => s | SOME y0 => wordSem.set_var (y0 * 2) v s end) in Hs1.
    set (rr := UPDATE y (r x) r).
    assert (Hdist : ALL_DISTINCT (FILTER IS_SOME (MAP FST ms)) /\
                    (forall y0, y = SOME y0 -> ~ In (SOME y0) (MAP FST ms))).
    { cbn [FILTER filter] in Had. destruct y as [y0|]; cbn [IS_SOME] in Had.
      - cbn [ALL_DISTINCT] in Had. apply andb_prop in Had as [Hn Hd]. split; [exact Hd|].
        intros ? [= <-] Hin. apply negb_true_iff in Hn. rewrite <- not_true_iff_false in Hn. apply Hn.
        apply MEM_In. apply filter_In. split; [exact Hin|reflexivity].
      - split; [exact Had|discriminate]. }
    destruct Hdist as [Had' Hnin].
    destruct (IH s1 t1 rr) as (t2 & E2 & Hs2 & Hl2 & Hsp2).
    { split; [exact Hs1|]. split.
      { intros i w. unfold rr, UPDATE, s1. destruct y as [y0|].
        - unfold wordSem.get_var, wordSem.set_var. ws_fields. rewrite lookup_insert.
          destruct (decide (SOME y0 = SOME i)) as [E|E].
          + injection E as <-. rewrite decide_True by lia. rewrite Hrx. reflexivity.
          + rewrite decide_False by (intros C; apply E; f_equal; lia). apply Hr.
        - destruct (decide (NONE = SOME i)); [discriminate|]. apply Hr. }
      split.
      { intros w. unfold rr, UPDATE. destruct y as [y0|].
        - rewrite decide_False by discriminate. intros Hw. rewrite Hn2 by discriminate. apply Hrn, Hw.
        - rewrite decide_True by reflexivity. rewrite Hrx. intros [= <-]. apply Hn1. reflexivity. }
      split.
      { assert (Hgv' : IS_SOME (wordSem.get_vars (MAP (fun x => 2 * THE x) (FILTER IS_SOME (MAP SND ms))) s)).
        { destruct x as [x0|]; [|exact Hgv]. cbn [FILTER filter IS_SOME MAP map] in Hgv.
          cbn [wordSem.get_vars] in Hgv. destruct (wordSem.get_var _ s); [|discriminate].
          destruct (wordSem.get_vars _ s); [reflexivity|discriminate]. }
        unfold s1. destruct y as [y0|]; [apply IS_SOME_get_vars_set_var|]; exact Hgv'. }
      split.
      { destruct (find_index NONE (MAP SND ms) 0) as [i|] eqn:Ei; [|exact Logic.I].
        unfold rr, UPDATE. destruct y as [y0|].
        - rewrite decide_False by discriminate.
          cbn [find_index] in Hfi. rewrite (decide_False (P := SOME y0 = NONE)) in Hfi by discriminate.
          rewrite !find_index_shift' in Hfi.
          destruct x as [x0|].
          + rewrite (decide_False (P := SOME x0 = NONE)) in Hfi by discriminate.
            rewrite Ei in Hfi. cbn [option_map] in Hfi.
            destruct (find_index NONE (MAP FST ms) 0) as [j|]; cbn [option_map] in Hfi; [|exact Hfi].
            intros Hij. apply Hfi. lia.
          + rewrite decide_True in Hfi by reflexivity.
            assert (Hr0 : IS_SOME (r NONE))
              by (destruct (find_index NONE (MAP FST ms) 0); cbn [option_map] in Hfi; [apply Hfi; lia|exact Hfi]).
            destruct (find_index NONE (MAP FST ms) 0); intros; exact Hr0.
        - rewrite decide_True by reflexivity. rewrite Hrx.
          destruct (find_index NONE (MAP FST ms) 0); [intros _|]; reflexivity. }
      split; [exact Hev|exact Had']. }
    exists t2. rewrite E2. split; [reflexivity|]. split; [|split; congruence].
    replace (seqsem ((y, x) :: ms) r) with (seqsem ms rr) by reflexivity.
    cbn [REVERSE rev]. rewrite !map_app, !filter_app, !map_app. cbn [List.map List.filter FST fst].
    unfold s1 in Hs2. destruct y as [y0|]; cbn [IS_SOME List.filter List.map].
    + rewrite ?app_nil_r in *. unfold wordSem.set_vars in *.
      rewrite alist_insert_append by (rewrite !LENGTH_length, !length_map; reflexivity).
      cbn [alist_insert THE]. rewrite proofs.seqsem_move_unchanged.
      2:{ unfold is_true. rewrite MEM_In. apply Hnin. reflexivity. }
      assert (Hrr : rr (SOME y0) = SOME v) by (unfold rr, UPDATE; rewrite decide_True by reflexivity; exact Hrx).
      rewrite Hrr. cbn [THE].
      unfold wordSem.set_var in Hs2. rewrite set_locals_set_locals in Hs2. ws_fields.
      rewrite (N.mul_comm y0 2) in Hs2. exact Hs2.
    + rewrite !app_nil_r. exact Hs2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_SeqStackFree" 3286 *)
Theorem evaluate_SeqStackFree : forall n (p : prog a) t,
  use_stack t /\ stack_space t <= LENGTH (stackSem.stack t) ->
  evaluate (SeqStackFree n p, t) = evaluate (Seq (StackFree n) p, t).
Proof. intros n p t H. apply evaluate_SeqStackFree_local, H. Qed.

End MoveAux.

Section CallDest.
Context {a : N} {C F : Type}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "get_vars_eq" *)
Theorem get_vars_eq : forall (st : wordSem.state a C F) ls z,
  wordSem.get_vars ls st = SOME z ->
  let lookups := MAP (fun x => lookup x (wordSem.locals st)) ls in
  EVERY IS_SOME lookups /\ z = MAP THE lookups.
Proof.
  intros st ls; induction ls as [|x ls IH]; intros z H; cbn [wordSem.get_vars] in H.
  - injection H as <-. split; reflexivity.
  - unfold wordSem.get_var in H. cbv zeta. cbn [List.map EVERY].
    destruct (lookup x (wordSem.locals st)) as [v|]; [|discriminate].
    destruct (wordSem.get_vars ls st) as [zs|]; [|discriminate]. injection H as <-.
    destruct (IH zs eq_refl) as [H1 H2]. split; [exact H1|]. cbn [THE]. f_equal. exact H2.
Qed.

Lemma get_vars_LAST (st : wordSem.state a C F) : forall ls z,
  wordSem.get_vars ls st = SOME z -> ls <> [] ->
  lookup (LAST ls) (wordSem.locals st) = SOME (LAST z) /\ z <> [].
Proof.
  induction ls as [|x ls IH]; intros z H Hne; [congruence|]. cbn [wordSem.get_vars] in H.
  unfold wordSem.get_var in H. destruct (lookup x (wordSem.locals st)) as [v|] eqn:Ex; [|discriminate].
  destruct (wordSem.get_vars ls st) as [zs|] eqn:Ezs; [|discriminate]. injection H as <-.
  destruct ls as [|y ls'].
  - cbn in Ezs. injection Ezs as <-. split; [exact Ex|discriminate].
  - destruct (IH zs eq_refl ltac:(discriminate)) as [H1 H2]. destruct zs as [|z1 zs]; [congruence|].
    split; [exact H1|discriminate].
Qed.

End CallDest.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LAST_add_ret_loc" *)
Theorem LAST_add_ret_loc : forall {a} (args' : list (word_loc a)) ret,
  args' <> [] -> LAST (wordSem.add_ret_loc ret args') = LAST args'.
Proof.
  intros a args' ret H. destruct ret as [[n [names [rh [l1 l2]]]]|]; [|reflexivity].
  cbn [wordSem.add_ret_loc LAST]. destruct args'; [congruence|reflexivity].
Qed.

Lemma LENGTH_FRONT_cons' {A} (x : A) l : LENGTH (FRONT (x :: l)) = LENGTH l.
Proof.
  revert x; induction l as [|y l IH]; intros x; [reflexivity|].
  change (FRONT (x :: y :: l)) with (x :: FRONT (y :: l)). rewrite LENGTH_cons', IH, LENGTH_cons'. reflexivity.
Qed.

Section CallDest2.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "call_dest_lemma" *)
Theorem call_dest_lemma : forall ac k f f' (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t)
    lens dest args q0 dest' args' (ret : option (list N * (wordLang.cutsets * (wordLang.prog a * (N * N))))),
  ~ is_true (wordSem.bad_dest_args dest args) /\
  state_rel ac k f f' s t lens 0 /\
  call_dest dest args (k, (f, f')) = (q0, dest') /\
  wordSem.get_vars args s = SOME args' ->
  exists t4 : stackSem.state a c ffi_t,
    evaluate (q0, t) = (NONE, t4) /\
    state_rel ac k f f' s t4 lens 0 /\
    LENGTH (stackSem.stack t4) = LENGTH (stackSem.stack t) /\
    stack_space t4 = stack_space t /\
    forall real_args prog ssize,
      wordSem.find_code dest (wordSem.add_ret_loc ret args') (wordSem.code s) (wordSem.state_stack_size s) =
        SOME (real_args, (prog, ssize)) ->
      exists bs i bs2 i2 fs stack_prog,
        compile_prog ac false prog (LENGTH real_args) k (bs, i) = (stack_prog, (fs, (bs2, i2))) /\
        LENGTH (append bs) <= i /\ i - LENGTH (append bs) <= LENGTH (bitmaps t) /\
        isPREFIX (append bs2) (DROP (i - LENGTH (append bs)) (bitmaps t)) /\
        the fs ssize = fs /\
        find_code dest' (regs t4) (code t4) = SOME stack_prog.
Proof.
  intros ac k f f' s t lens dest args q0 dest' args' ret (Hbad & H & Hcd & Hgv).
  pose proof H as H0. sr_destr H0.
  destruct dest as [pos|].
  - cbn [call_dest] in Hcd. injection Hcd as <- <-.
    exists t. split; [apply ev_skip|]. split; [exact H|]. split; [reflexivity|]. split; [reflexivity|].
    intros real_args prog ssize Hfc. cbn [wordSem.find_code] in Hfc.
    destruct (lookup pos (wordSem.code s)) as [[arity exp]|] eqn:El; [|discriminate].
    destruct (LENGTH _ =? arity) eqn:Ea; [|discriminate]. injection Hfc as <- <- <-. apply N.eqb_eq in Ea.
    destruct (Hcode _ _ _ El) as (_ & _ & bs & i & bs2 & i2 & fs & sp & Hc & H1 & H2 & H3 & H4 & H5).
    exists bs, i, bs2, i2, fs, sp. rewrite Ea. repeat split; auto.
  - assert (Hne : args <> []).
    { intros ->. apply Hbad. unfold wordSem.bad_dest_args. rewrite !bd_true' by reflexivity. reflexivity. }
    destruct (get_vars_LAST s args args' Hgv Hne) as [Hlast Hne'].
    destruct (Hloc _ _ Hlast) as [Hev Hr].
    assert (Hfind : forall t4 : stackSem.state a c ffi_t, code t4 = code t ->
              FLOOKUP (regs t4) (match dest' with inl p => p | inr r => r end) = SOME (LAST args') ->
              (exists r, dest' = inr r) ->
              forall real_args prog ssize,
                wordSem.find_code NONE (wordSem.add_ret_loc ret args') (wordSem.code s) (wordSem.state_stack_size s) =
                  SOME (real_args, (prog, ssize)) ->
                exists bs i bs2 i2 fs stack_prog,
                  compile_prog ac false prog (LENGTH real_args) k (bs, i) = (stack_prog, (fs, (bs2, i2))) /\
                  LENGTH (append bs) <= i /\ i - LENGTH (append bs) <= LENGTH (bitmaps t) /\
                  isPREFIX (append bs2) (DROP (i - LENGTH (append bs)) (bitmaps t)) /\
                  the fs ssize = fs /\
                  find_code dest' (regs t4) (code t4) = SOME stack_prog).
    { intros t4 Ec Hreg [r ->] real_args prog ssize Hfc. cbn [wordSem.find_code] in Hfc.
      assert (Hne2 : wordSem.add_ret_loc ret args' <> []).
      { destruct ret as [[? [? [? [? ?]]]]|]; cbn [wordSem.add_ret_loc]; [discriminate|exact Hne']. }
      rewrite bd_false' in Hfc by exact Hne2. rewrite LAST_add_ret_loc in Hfc by exact Hne'.
      destruct (LAST args') as [w|loc n] eqn:EL; [discriminate|].
      destruct (n =? 0) eqn:En; [|discriminate].
      destruct (lookup loc (wordSem.code s)) as [[arity exp]|] eqn:El; [|discriminate].
      destruct (LENGTH _ =? arity + 1) eqn:Ea; [|discriminate]. injection Hfc as <- <- <-. apply N.eqb_eq in Ea.
      destruct (Hcode _ _ _ El) as (_ & _ & bs & i & bs2 & i2 & fs & sp & Hc & H1 & H2 & H3 & H4 & H5).
      exists bs, i, bs2, i2, fs, sp.
      replace (LENGTH (FRONT (wordSem.add_ret_loc ret args'))) with arity.
      2:{ destruct (wordSem.add_ret_loc ret args') as [|z zs]; [congruence|].
          rewrite LENGTH_FRONT_cons'. rewrite LENGTH_cons' in Ea. lia. }
      repeat split; auto. cbn [stackSem.find_code]. rewrite Hreg, En, Ec. exact H4. }
    cbn [call_dest] in Hcd.
    assert (HL : (LENGTH args =? 0) = false) by (destruct args; [congruence|apply N.eqb_neq; rewrite LENGTH_cons'; lia]).
    rewrite HL in Hcd. unfold wReg2 in Hcd.
    destruct (LAST args DIV 2 <? k) eqn:Ek.
    + injection Hcd as <- <-. cbn [wStackLoad].
      exists t. split; [apply ev_skip|]. split; [exact H|]. split; [reflexivity|]. split; [reflexivity|].
      apply Hfind; [reflexivity|exact Hr|eexists; reflexivity].
    + injection Hcd as <- <-. cbn [wStackLoad]. rewrite ev_seq.
      apply N.ltb_ge in Ek.
      rewrite (ev_load_slot ac k f f' s t lens (LAST args DIV 2) (LAST args') (k + 1) H)
        by first [lia | (unfold wordSem.get_var; rewrite <- (even_div2 _ Hev); exact Hlast)].
      rewrite ev_skip. eexists; split; [reflexivity|].
      split; [apply state_rel_set_var_k; exact H|]. split; [reflexivity|]. split; [reflexivity|].
      apply Hfind; [reflexivity| |eexists; reflexivity].
      unfold stackSem.set_var. stk_fields. rewrite FLOOKUP_UPDATE. rewrite decide_True by reflexivity. reflexivity.
Qed.

End CallDest2.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "compile_result_NOT_2" *)
Theorem compile_result_NOT_2 : forall {a} (x : wordSem.result a),
  good_dimindex a -> compile_result x <> Halt (Word (n2w 2)).
Proof.
  intros a x Hg. destruct x; cbn [compile_result]; try discriminate.
  intros E. injection E as E.
  assert (H : 2 < dimword a).
  { unfold dimword. destruct Hg as [Hg|Hg]; rewrite Hg; reflexivity. }
  rewrite !N.mod_small in E by lia. discriminate.
Qed.

(** ** Parallel moves *)

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAP_o_THE_FILTER_IS_SOME" *)
Theorem MAP_o_THE_FILTER_IS_SOME : forall {A B} `{Inhabited A} `{Inhabited B} (f : A -> B) (ls : list (option A)),
  MAP (f ∘ THE) (FILTER IS_SOME ls) = MAP (THE ∘ OPTION_MAP f) (FILTER IS_SOME ls).
Proof.
  intros A B HA HB f ls. induction ls as [|[x|] ls IH]; cbn [List.filter IS_SOME]; [reflexivity| |exact IH].
  cbn [List.map]. rewrite IH. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAP_OPTION_MAP_FILTER_IS_SOME" *)
Theorem MAP_OPTION_MAP_FILTER_IS_SOME : forall {A} (f : A -> A) (ls : list (option A)),
  MAP (OPTION_MAP f) (FILTER IS_SOME ls) = FILTER IS_SOME (MAP (OPTION_MAP f) ls).
Proof.
  intros A f ls. induction ls as [|[x|] ls IH]; cbn [List.filter List.map IS_SOME option_map]; [reflexivity| |exact IH].
  cbn [List.map]. rewrite IH. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAP_FILTER_IS_SOME" *)
Theorem MAP_FILTER_IS_SOME : forall {A B} `{Inhabited A} (f : option A -> B) (ls : list (option A)),
  MAP f (FILTER IS_SOME ls) = MAP (f ∘ SOME ∘ THE) (FILTER IS_SOME ls).
Proof.
  intros A B HA f ls. induction ls as [|[x|] ls IH]; cbn [List.filter IS_SOME]; [reflexivity| |exact IH].
  cbn [List.map]. rewrite IH. reflexivity.
Qed.

Lemma EVERY_In {A} (P : A -> bool) l x : is_true (EVERY P l) -> In x l -> is_true (P x).
Proof. unfold is_true. rewrite EVERY_Forall, Forall_forall. intros H; apply H. Qed.

Lemma map_FST_PAIR_MAP {A B C D} (f : A -> C) (g : B -> D) l :
  MAP FST (MAP (f ## g) l) = MAP f (MAP FST l).
Proof. rewrite !map_map. reflexivity. Qed.

Lemma filter_map_div2 (L : list (option N)) :
  (forall x, In (SOME x) L -> EVEN x) ->
  MAP (fun x => 2 * THE x) (FILTER IS_SOME (MAP (OPTION_MAP (fun n => n DIV 2)) L)) = MAP THE (FILTER IS_SOME L).
Proof.
  induction L as [|[x|] L IH]; intros H; cbn [List.map List.filter option_map IS_SOME]; [reflexivity| |].
  - cbn [List.map THE]. rewrite IH by (intros y Hy; apply H; right; exact Hy).
    f_equal. symmetry. apply even_div2, H. left; reflexivity.
  - apply IH. intros y Hy; apply H; right; exact Hy.
Qed.

Lemma div2_inj_even (moves : list (N * N)) :
  is_true (EVERY EVEN (MAP FST moves)) -> is_true (EVERY EVEN (MAP SND moves)) ->
  let ls1 := MAP FST moves ++ MAP SND moves in
  forall x y, MEM x ls1 /\ MEM y ls1 /\ x DIV 2 = y DIV 2 -> x = y.
Proof.
  intros H1 H2 ls1 x y (Hx & Hy & E). apply EVEN_DIV2_INJ. unfold ls1, is_true in *.
  rewrite MEM_In in Hx, Hy. apply in_app_or in Hx, Hy.
  split; [destruct Hx as [Hx|Hx]; [apply (EVERY_In _ _ _ H1 Hx)|apply (EVERY_In _ _ _ H2 Hx)]|].
  split; [destruct Hy as [Hy|Hy]; [apply (EVERY_In _ _ _ H1 Hy)|apply (EVERY_In _ _ _ H2 Hy)]|exact E].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "TIMES2_DIV2_lemma" *)
Theorem TIMES2_DIV2_lemma : forall (moves : list (N * N)),
  windmill moves /\ EVERY EVEN (MAP FST moves) /\ EVERY EVEN (MAP SND moves) ->
  MAP (fun x => 2 * THE x)
    (FILTER IS_SOME (MAP FST (parmove (MAP ((fun n => n DIV 2) ## (fun n => n DIV 2)) moves)))) =
  MAP THE (FILTER IS_SOME (MAP FST (parmove moves))).
Proof.
  intros moves (Hw & H1 & H2).
  rewrite (proofs.parmove_MAP_INJ (fun n => n DIV 2) moves) by (split; [apply div2_inj_even; assumption|exact Hw]).
  rewrite map_FST_PAIR_MAP. apply filter_map_div2.
  intros x Hx. assert (Hm : is_true (MEM (SOME x) (MAP FST (parmove moves)))) by (unfold is_true; rewrite MEM_In; exact Hx).
  apply proofs.MEM_MAP_FST_parmove in Hm. unfold is_true in Hm. rewrite MEM_In in Hm. apply (EVERY_In _ _ _ H1 Hm).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "PAIR_MAP_SOME_SWAP" *)
Theorem PAIR_MAP_SOME_SWAP : forall {A B C D} (f : A -> C) (g : B -> D),
  (SOME ## SOME) ∘ (f ## g) = (OPTION_MAP f ## OPTION_MAP g) ∘ (SOME ## SOME).
Proof. intros A B C D f g. apply functional_extensionality. intros [x y]. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "IS_SOME_o_OPTION_MAP" *)
Theorem IS_SOME_o_OPTION_MAP : forall {A B} (f : A -> B), IS_SOME ∘ OPTION_MAP f = IS_SOME.
Proof. intros A B f. apply functional_extensionality. intros [x|]; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "parsem_parmove_DIV2_lemma" *)
Theorem parsem_parmove_DIV2_lemma : forall {B} (moves : list (N * N)) (r : option N -> B),
  windmill moves /\ EVERY EVEN (MAP FST moves) /\ EVERY EVEN (MAP SND moves) ->
  MAP (parsem (MAP (SOME ## SOME) (MAP ((fun n => n DIV 2) ## (fun n => n DIV 2)) moves)) r)
    (FILTER IS_SOME (MAP FST (parmove (MAP ((fun n => n DIV 2) ## (fun n => n DIV 2)) moves)))) =
  MAP (parsem (MAP (SOME ## SOME) moves) (r ∘ OPTION_MAP (fun n => n DIV 2)))
    (FILTER IS_SOME (MAP FST (parmove moves))).
Proof.
  intros B moves r (Hw & H1 & H2).
  set (g := OPTION_MAP (fun n : N => n DIV 2)).
  rewrite (proofs.parmove_MAP_INJ (fun n => n DIV 2) moves) by (split; [apply div2_inj_even; assumption|exact Hw]).
  rewrite map_FST_PAIR_MAP, <- MAP_OPTION_MAP_FILTER_IS_SOME, map_map.
  set (mvs := MAP (SOME ## SOME) moves).
  assert (Emv : MAP (SOME ## SOME) (MAP ((fun n => n DIV 2) ## (fun n => n DIV 2)) moves) = MAP (g ## g) mvs).
  { unfold mvs. rewrite !map_map. apply map_ext. intros [x y]. reflexivity. }
  rewrite Emv. apply map_ext_in. intros z Hz.
  apply filter_In in Hz as [Hz Hs]. destruct z as [x|]; [|discriminate].
  assert (Hx : is_true (MEM x (MAP FST moves))).
  { apply proofs.MEM_MAP_FST_parmove. unfold is_true; rewrite MEM_In; exact Hz. }
  assert (Hwm : windmill mvs).
  { unfold windmill, mvs. rewrite map_FST_PAIR_MAP. unfold windmill in Hw. apply ALL_DISTINCT_iff.
    apply ALL_DISTINCT_iff in Hw. apply Finite.Injective_map_NoDup; [|exact Hw].
    intros p q E; injection E; auto. }
  rewrite (proofs.parsem_MAP_INJ g r mvs).
  - reflexivity.
  - split; [exact Hwm|]. split; [intros; exact Logic.I|].
    intros p q [Hp Hq] E. unfold mvs in Hp, Hq. rewrite map_FST_PAIR_MAP in Hp, Hq.
    replace (MAP SND (MAP (SOME ## SOME) moves)) with (MAP SOME (MAP SND moves)) in Hp, Hq
      by (rewrite !map_map; reflexivity).
    rewrite <- map_app in Hp, Hq. apply IN_set in Hp, Hq. apply in_map_iff in Hp as [p' [<- Hp']].
    apply in_map_iff in Hq as [q' [<- Hq']]. unfold g in E. cbn [option_map] in E. injection E as E.
    f_equal. apply EVEN_DIV2_INJ. apply in_app_or in Hp', Hq'.
    split; [destruct Hp' as [Hp'|Hp']; [apply (EVERY_In _ _ _ H1 Hp')|apply (EVERY_In _ _ _ H2 Hp')]|].
    split; [destruct Hq' as [Hq'|Hq']; [apply (EVERY_In _ _ _ H1 Hq')|apply (EVERY_In _ _ _ H2 Hq')]|exact E].
  - unfold mvs. rewrite map_FST_PAIR_MAP. apply MEM_iff. apply MEM_iff in Hx. apply in_map, Hx.
Qed.

(** ** Association lists and [alist_insert] *)

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "ALOOKUP_MAP_any" *)
Theorem ALOOKUP_MAP_any : forall {A B C D} `{EqDecision A} `{EqDecision B} `{EqDecision C}
    (f : A * B -> C * D) (k : A -> C) (h : C -> B -> D) (ls : list (A * B)) a0 x,
  INJ k (a0 INSERT set (MAP FST ls)) UNIV /\
  (forall x y, MEM (x, y) ls -> f (x, y) = (k x, h (k x) y)) /\ k a0 = x ->
  ALOOKUP (MAP f ls) x = OPTION_MAP (h x) (ALOOKUP ls a0).
Proof.
  intros A B C D HA HB HC f k h ls a0 x. induction ls as [|[x0 y0] ls IH]; intros (Hi & Hf & Hk); [reflexivity|].
  cbn [List.map ALOOKUP]. rewrite Hf by (unfold is_true; rewrite MEM_In; left; reflexivity).
  cbn [ALOOKUP]. destruct Hi as [_ Hi].
  destruct (decide (k x0 = x)) as [E|E].
  - assert (x0 = a0).
    { apply Hi; [split; apply IN_INSERT; [right; apply IN_set; left; reflexivity|left; reflexivity]|congruence]. }
    subst x0. rewrite decide_True by reflexivity. cbn [option_map]. rewrite E. reflexivity.
  - rewrite decide_False by (intros <-; contradiction).
    apply IH. split; [split; [intros; exact Logic.I|]|split; [|exact Hk]].
    + intros p q [Hp Hq]. apply Hi. split; apply IN_INSERT; apply IN_INSERT in Hp, Hq;
        [destruct Hp as [Hp|Hp]; [left; exact Hp|right; apply IN_set; right; apply IN_set, Hp]|
         destruct Hq as [Hq|Hq]; [left; exact Hq|right; apply IN_set; right; apply IN_set, Hq]].
    + intros p q Hm. apply Hf. unfold is_true in *. rewrite MEM_In in *. right; exact Hm.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wf_alist_insert" *)
Theorem wf_alist_insert : forall {A} xs (ys : list A) (z : num_map A), sptree.wf z -> sptree.wf (alist_insert xs ys z).
Proof.
  intros A xs; induction xs as [|x xs IH]; intros [|y ys] z H; cbn [alist_insert]; try exact H.
  apply wf_insert, IH, H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "ALOOKUP_MAP_INJ_FST" *)
Theorem ALOOKUP_MAP_INJ_FST : forall {A K V} `{EqDecision A} `{EqDecision K} (ls : list A) (f : A -> K * V) x k,
  INJ (FST ∘ f) (x INSERT set ls) UNIV /\ FST (f x) = k ->
  ALOOKUP (MAP f ls) k = ALOOKUP (MAP (fun x => (x, SND (f x))) ls) x.
Proof.
  intros A K V HA HK ls f x k. induction ls as [|h ls IH]; intros [Hi Hk]; [reflexivity|].
  cbn [List.map]. destruct (f h) as [k1 v1] eqn:Eh. cbn [ALOOKUP]. destruct Hi as [_ Hi].
  destruct (decide (k1 = k)) as [E|E].
  - assert (h = x).
    { apply Hi; [split; apply IN_INSERT; [right; apply IN_set; left; reflexivity|left; reflexivity]|].
      cbv beta. rewrite Eh, Hk. exact E. }
    subst h. rewrite !decide_True by (reflexivity || exact E). reflexivity.
  - rewrite decide_False by (intros <-; apply E; rewrite <- Hk, Eh; reflexivity).
    apply IH. split; [split; [intros; exact Logic.I|]|exact Hk].
    intros p q [Hp Hq]. apply Hi. split; apply IN_INSERT; apply IN_INSERT in Hp, Hq;
      [destruct Hp as [Hp|Hp]; [left; exact Hp|right; apply IN_set; right; apply IN_set, Hp]|
       destruct Hq as [Hq|Hq]; [left; exact Hq|right; apply IN_set; right; apply IN_set, Hq]].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "ALOOKUP_ID_TABULATE" *)
Theorem ALOOKUP_ID_TABULATE : forall {A} `{EqDecision A} (ls : list A) x,
  ALOOKUP (MAP (fun x => (x, x)) ls) x = if MEM x ls then SOME x else NONE.
Proof.
  intros A HA ls x. induction ls as [|y ls IH]; [reflexivity|]. cbn [List.map ALOOKUP MEM].
  destruct (decide (y = x)) as [->|E].
  - rewrite bd_true' by reflexivity. reflexivity.
  - rewrite bd_false' by congruence. exact IH.
Qed.

Lemma ZIP_cons' {A B} (x : A) (y : B) l1 l2 : ZIP (x :: l1, y :: l2) = (x, y) :: ZIP (l1, l2).
Proof. reflexivity. Qed.

Lemma ZIP_MAP_MAP {A B C} (f : A -> B) (g : A -> C) l : ZIP (MAP f l, MAP g l) = MAP (fun p => (f p, g p)) l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [List.map]. rewrite ZIP_cons', IH. reflexivity. Qed.

Lemma ALOOKUP_MAP_FILTER_THE {A B} `{EqDecision A} `{Inhabited A} (g : option A -> B) (ls : list (option A)) z :
  ALOOKUP (MAP (fun o => (THE o, g o)) (FILTER IS_SOME ls)) z = if MEM (SOME z) ls then SOME (g (SOME z)) else NONE.
Proof.
  induction ls as [|[y|] ls IH]; [reflexivity| |].
  - cbn [List.filter IS_SOME List.map ALOOKUP THE MEM]. destruct (decide (y = z)) as [->|E].
    + rewrite bd_true' by reflexivity. reflexivity.
    + rewrite bd_false' by congruence. exact IH.
  - cbn [List.filter IS_SOME MEM]. rewrite bd_false' by discriminate. exact IH.
Qed.

Lemma ALOOKUP_MAP_FST_pair {A B C} `{EqDecision A} (h : A * B -> C) (l : list (A * B)) z :
  ALOOKUP (MAP (fun p => (FST p, h p)) l) z = option_map (fun v => h (z, v)) (ALOOKUP l z).
Proof.
  induction l as [|[x y] l IH]; [reflexivity|]. cbn [List.map ALOOKUP FST fst].
  destruct (decide (x = z)) as [->|]; [reflexivity|exact IH].
Qed.

Lemma ALOOKUP_MEM_FST {A B} `{EqDecision A} (l : list (A * B)) z :
  In z (MAP FST l) -> exists b, ALOOKUP l z = SOME b.
Proof.
  induction l as [|[x y] l IH]; intros Hz; [destruct Hz|]. cbn [ALOOKUP].
  destruct (decide (x = z)) as [->|E]; [eexists; reflexivity|]. apply IH.
  destruct Hz as [Hz|Hz]; [cbn in Hz; congruence|exact Hz].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "alist_insert_get_vars" *)
Theorem alist_insert_get_vars : forall {a C F} (moves : list (N * N)) (s : wordSem.state a C F) x (ls : list (option N)),
  ALL_DISTINCT (MAP FST moves) /\
  wordSem.get_vars (MAP SND moves) s = SOME x /\
  ALL_DISTINCT (FILTER IS_SOME ls) /\
  sptree.wf (wordSem.locals s) /\
  (forall x, MEM (SOME x) ls -> MEM x (MAP FST moves)) /\
  (forall x y, MEM (x, y) moves /\ x <> y -> MEM (SOME x) ls) ->
  alist_insert
    (MAP THE (FILTER IS_SOME ls))
    (MAP (fun x => THE (wordSem.get_var (THE (ALOOKUP moves (THE x))) s)) (FILTER IS_SOME ls)) (wordSem.locals s) =
  alist_insert (MAP FST moves) x (wordSem.locals s).
Proof.
  intros a C F moves s x ls (Hd & Hg & Hd2 & Hwf & H1 & H2).
  destruct (get_vars_eq s _ _ Hg) as [Hsome Ex]. cbv zeta in Hsome, Ex.
  rewrite !map_map in Hsome. rewrite !map_map in Ex. subst x.
  apply spt_eq_thm; [split; apply wf_alist_insert, Hwf|]. intros z.
  rewrite !lookup_alist_insert by (rewrite !LENGTH_length, !length_map; reflexivity).
  rewrite !ZIP_MAP_MAP, ALOOKUP_MAP_FILTER_THE.
  rewrite (ALOOKUP_MAP_FST_pair (fun p => THE (lookup (SND p) (wordSem.locals s)))).
  assert (Hs : forall b, In b (MAP SND moves) -> exists w, lookup b (wordSem.locals s) = SOME w).
  { intros b Hb. apply in_map_iff in Hb as [p [<- Hp]].
    pose proof (EVERY_In _ _ _ Hsome (in_map _ _ _ Hp)) as Hi. cbv beta in Hi.
    destruct (lookup (SND p) (wordSem.locals s)) as [w|]; [exists w; reflexivity|discriminate]. }
  destruct (MEM (SOME z) ls) eqn:Em.
  - specialize (H1 z Em). unfold is_true in H1. rewrite MEM_In in H1.
    destruct (ALOOKUP_MEM_FST _ _ H1) as [b Eb]. cbn [THE]. rewrite Eb. reflexivity.
  - destruct (ALOOKUP moves z) as [b|] eqn:Eb; [|reflexivity]. cbn [option_map].
    apply ALOOKUP_In in Eb.
    destruct (decide (z = b)) as [<-|Ne].
    + destruct (Hs z) as [w Hw]; [apply (in_map SND _ _ Eb)|]. cbn [SND snd]. rewrite Hw. reflexivity.
    + exfalso. assert (Hm : is_true (MEM (SOME z) ls)).
      { apply (H2 z b). split; [unfold is_true; rewrite MEM_In; exact Eb|exact Ne]. }
      unfold is_true in Hm. congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wf_fromList2" *)
Theorem wf_fromList2 : forall {A} (ls : list A), sptree.wf (fromList2 ls).
Proof.
  intros A ls. unfold fromList2.
  assert (G : forall l i (t : num_map A), sptree.wf t ->
            sptree.wf (snd (FOLDL (fun '(i, t) a0 => (i + 2, insert i a0 t)) (i, t) l))).
  { induction l as [|y l IH]; intros i t Ht; [exact Ht|]. cbn [FOLDL]. apply IH, wf_insert, Ht. }
  apply G. apply wf_LN. 
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wStackLoad_append" *)
Theorem wStackLoad_append : forall {a} l1 l2, @wStackLoad a (l1 ++ l2) = wStackLoad l1 ∘ wStackLoad l2.
Proof.
  intros a l1 l2. apply functional_extensionality. intros p. induction l1 as [|[r i] l1 IH]; [reflexivity|].
  cbn [app wStackLoad]. rewrite IH. reflexivity.
Qed.
