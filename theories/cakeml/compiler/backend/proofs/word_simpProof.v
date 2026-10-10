(** * CakeML [word_simpProof]: correctness of [word_simp]

    Port of [cakeml/compiler/backend/proofs/word_simpProofScript.sml].

    Notes:
    - HOL's free variables are quantified explicitly (first, when the HOL
      statement quantifies only some of them).  HOL's bound variables
      [c], [c'] (programs) of [evaluate_Loop_body_cong(_gc)] are [p], [p']
      ([c] is the configuration type of the states); [handler] is [h]
      where it would shadow the state field.
    - HOL [s with f := v] is [set_f v s]; [s.stack_size] is
      [state_stack_size s]; [EVERY2] is [LIST_REL]; HOL's [if x = y] is
      [if decide (x = y)].
    - Renamed bound variables: [a], [b], [c] of [sf_gc_consts_trans] are
      [x], [y], [z]; [handler] of [LIST_REL_call_Result] and
      [push_env_pop_env_locals_thm] is [h].  The unconstrained free
      variable [R] of [EVERY2_trans_LASTN_sf_gc_consts] (unused in HOL's
      statement) is a [Prop].
    - [get_above_handler_def]: HOL's [EL] beyond the end of a list and the
      missing [NONE] case of its [case] are unspecified ([ARB]); Galette's
      [EL] needs an [Inhabited] instance for stack frames (a local
      instance).
    - Not ported (they mention HOL's [sorting$PERM], which Galette does not
      port; see [wordProps.code]): [ALL_DISTINCT_PERM_FST],
      [ALOOKUP_ALL_DISTINCT_FST_PERM], [ALOOKUP_ALL_DISTINCT_FST_PERM_SOME]
      (only used in the proof of [push_env_pop_env_locals_thm], proved here
      directly).
    - Proofs are by induction on the program ([prog_nested_ind]) or by
      well-founded induction on [eval_lt] with [evaluate_eqn] instead of
      HOL's recursion-induction principles ([Seq_assoc_ind],
      [const_fp_loop_ind], [evaluate_ind], ...).  The Galette-only helpers
      (the [evaluate] equations used for rewriting, the congruence lemmas
      [eq_eval_*]) have no HOL original. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common wordLang word_simp.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem wordConvs.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import
  consts consts_with clock dec_clock.
From Galette.cakeml.compiler.backend.semantics.wordProps Require code.
Open Scope N_scope.

(** ** Galette-only helpers *)

Lemma bd_true (P : Prop) `{Decision P} : P -> bool_decide P = true.
Proof. apply bool_decide_spec. Qed.
Lemma bd_false (P : Prop) `{Decision P} : ~ P -> bool_decide P = false.
Proof. intros HP; destruct (bool_decide P) eqn:E; [|reflexivity]. apply bool_decide_spec in E; tauto. Qed.

Section Eqns.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

Lemma evaluate_Skip_eq s : evaluate (Skip, s) = (NONE, s).
Proof. rewrite (evaluate_eqn Skip s); reflexivity. Qed.

Lemma evaluate_Seq_eq (p1 p2 : prog a) s :
  evaluate (Seq p1 p2, s) =
  let '(res, s1) := evaluate (p1, s) in
  if bool_decide (res = NONE) then evaluate (p2, s1) else (res, s1).
Proof. rewrite (evaluate_eqn (Seq p1 p2) s); cbn [evaluate_body]. rewrite fix_clock_evaluate. reflexivity. Qed.

Lemma evaluate_Loop_eq names (p : prog a) exit_names s s' :
  cut_state (names, LN) s = SOME s' ->
  evaluate (Loop names p exit_names, s) =
  let '(res, s1) := evaluate (p, s') in
  if cont_loop res then
    (if clock s1 =? 0 then (SOME TimeOut, flush_state true s1)
     else evaluate (STOP (Loop names p exit_names), dec_clock s1))
  else if bool_decide (res = SOME (Break 0)) then
    match cut_state (exit_names, LN) s1 with
    | NONE => (SOME Error, s1)
    | SOME s2 => (NONE, s2)
    end
  else (exit_loop res, s1).
Proof.
  intros E. rewrite (evaluate_eqn (Loop names p exit_names) s); cbn [evaluate_body].
  rewrite E. rewrite fix_clock_evaluate. reflexivity.
Qed.

Lemma evaluate_Loop_None names (p : prog a) exit_names s :
  cut_state (names, LN) s = NONE ->
  evaluate (Loop names p exit_names, s) = (SOME Error, s).
Proof. intros E. rewrite (evaluate_eqn (Loop names p exit_names) s); cbn [evaluate_body]. rewrite E. reflexivity. Qed.

End Eqns.

(** ** Verification of [Seq_assoc] *)

Section SeqAssoc.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_SmartSeq" *)
Theorem evaluate_SmartSeq : forall (p1 p2 : prog a) s,
  evaluate (SmartSeq p1 p2, s) = evaluate (Seq p1 p2, s).
Proof.
  intros p1 p2 s; destruct p1; try reflexivity. cbn [SmartSeq].
  rewrite evaluate_Seq_eq, evaluate_Skip_eq, bd_true by reflexivity. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_Seq_Skip" *)
Theorem evaluate_Seq_Skip : forall (p1 : prog a) s,
  evaluate (Seq p1 Skip, s) = evaluate (p1, s).
Proof.
  intros; rewrite evaluate_Seq_eq. destruct (evaluate (p1, s)) as [r t].
  destruct (bool_decide (r = NONE)) eqn:E; [|reflexivity].
  apply bool_decide_spec in E; subst r. apply evaluate_Skip_eq.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_Skip_Seq" *)
Theorem evaluate_Skip_Seq : forall (p : prog a) s,
  evaluate (Seq Skip p, s) = evaluate (p, s).
Proof. intros; rewrite evaluate_Seq_eq, evaluate_Skip_eq, bd_true by reflexivity; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_Loop_body_cong" *)
Theorem evaluate_Loop_body_cong : forall s names (p p' : prog a) exit_names,
  (forall v : state a c ffi_t, evaluate (p', v) = evaluate (p, v)) ->
  evaluate (Loop names p' exit_names, s) = evaluate (Loop names p exit_names, s).
Proof.
  intros s names p p' exit_names Hs.
  remember (N.to_nat (clock s)) as n eqn:Hn. revert s Hn.
  induction n as [n IHn] using (well_founded_induction lt_wf). intros s Hn.
  destruct (cut_state (names, LN) s) as [s'|] eqn:Ec.
  2:{ rewrite !evaluate_Loop_None by exact Ec. reflexivity. }
  rewrite (evaluate_Loop_eq _ p' _ _ _ Ec), (evaluate_Loop_eq _ p _ _ _ Ec), Hs.
  destruct (evaluate (p, s')) as [r t] eqn:E1.
  destruct (cont_loop r); [|reflexivity].
  destruct (clock t =? 0) eqn:Ez; [reflexivity|].
  apply N.eqb_neq in Ez. unfold STOP.
  pose proof (evaluate_clock _ _ _ _ E1) as [Hc _].
  pose proof (cut_state_clock _ _ _ Ec) as [Hc' _].
  eapply (IHn (N.to_nat (clock (dec_clock t)))); [|reflexivity].
  unfold dec_clock; cbn [clock set_clock]. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_Loop_body_cong_gc" *)
Theorem evaluate_Loop_body_cong_gc : forall (R : gc_fun_type a -> Prop) s names (p p' : prog a) exit_names,
  (forall v : state a c ffi_t, R (gc_fun v) -> evaluate (p', v) = evaluate (p, v)) ->
  R (gc_fun s) ->
  evaluate (Loop names p' exit_names, s) = evaluate (Loop names p exit_names, s).
Proof.
  intros R s names p p' exit_names Hs.
  remember (N.to_nat (clock s)) as n eqn:Hn. revert s Hn.
  induction n as [n IHn] using (well_founded_induction lt_wf). intros s Hn HR.
  destruct (cut_state (names, LN) s) as [s'|] eqn:Ec.
  2:{ rewrite !evaluate_Loop_None by exact Ec. reflexivity. }
  assert (HR' : R (gc_fun s')).
  { apply cut_state_const in Ec as Ec'. destruct Ec' as [l ->]. exact HR. }
  rewrite (evaluate_Loop_eq _ p' _ _ _ Ec), (evaluate_Loop_eq _ p _ _ _ Ec), (Hs _ HR').
  destruct (evaluate (p, s')) as [r t] eqn:E1.
  destruct (cont_loop r); [|reflexivity].
  destruct (clock t =? 0) eqn:Ez; [reflexivity|].
  apply N.eqb_neq in Ez. unfold STOP.
  pose proof (evaluate_clock _ _ _ _ E1) as [Hc _].
  pose proof (cut_state_clock _ _ _ Ec) as [Hc' _].
  pose proof (evaluate_consts _ _ _ _ E1) as [Hg _].
  eapply (IHn (N.to_nat (clock (dec_clock t)))); [|reflexivity|].
  - unfold dec_clock; cbn [clock set_clock]. lia.
  - change (gc_fun (dec_clock t)) with (gc_fun t). rewrite <- Hg. exact HR'.
Qed.

(** Galette-only: two programs with the same semantics. *)
Definition eq_eval (p q : prog a) : Prop :=
  forall s : state a c ffi_t, evaluate (p, s) = evaluate (q, s).

(** Split the [match]es of an equation between two [evaluate_body]
    unfoldings, rewriting with the given equations at the leaves. *)
Ltac cong_split :=
  repeat first
    [ progress (rewrite ?fix_clock_evaluate)
    | match goal with
      | H : eq_eval ?p ?q |- context [evaluate (?p, ?s)] => rewrite (H s)
      end
    | match goal with
      | |- context [@bool_decide (SOME ?x = NONE) ?d] =>
          let F := fresh "F" in
          assert (F : @bool_decide (SOME x = NONE) d = false) by (apply bd_false; discriminate);
          rewrite F; clear F
      end
    | match goal with
      | |- context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
      end ];
  try reflexivity.

Lemma eq_eval_refl p : eq_eval p p.
Proof. intros s; reflexivity. Qed.

Lemma eq_eval_Seq p1 q1 p2 q2 :
  eq_eval p1 q1 -> eq_eval p2 q2 -> eq_eval (Seq p1 p2) (Seq q1 q2).
Proof.
  intros H1 H2 s. rewrite !evaluate_Seq_eq, H1. destruct (evaluate (q1, s)) as [r t].
  destruct (bool_decide _); [apply H2|reflexivity].
Qed.

Lemma eq_eval_If cmp r ri p1 q1 p2 q2 :
  eq_eval p1 q1 -> eq_eval p2 q2 -> eq_eval (If cmp r ri p1 p2) (If cmp r ri q1 q2).
Proof.
  intros H1 H2 s. rewrite !(evaluate_eqn (If _ _ _ _ _) s); cbn [evaluate_body]. cong_split.
Qed.

Lemma eq_eval_MustTerminate p q : eq_eval p q -> eq_eval (MustTerminate p) (MustTerminate q).
Proof.
  intros H s. rewrite !(evaluate_eqn (MustTerminate _) s); cbn [evaluate_body]. rewrite H.
  reflexivity.
Qed.

Lemma eq_eval_Loop names p q exit_names :
  eq_eval p q -> eq_eval (Loop names p exit_names) (Loop names q exit_names).
Proof. intros H s. symmetry. apply evaluate_Loop_body_cong. intros v; symmetry; apply H. Qed.

Lemma eq_eval_Call (f : prog a -> prog a) ret dest args h :
  match ret with Some (_, (_, (q, _))) => eq_eval (f q) q | None => True end ->
  match h with Some (_, (q, _)) => eq_eval (f q) q | None => True end ->
  eq_eval
    (Call (match ret with
           | None => None
           | Some (x1, (x2, (q1, (x3, x4)))) => Some (x1, (x2, (f q1, (x3, x4))))
           end) dest args
          (match h with
           | None => None
           | Some (y1, (q2, (y2, y3))) => Some (y1, (f q2, (y2, y3)))
           end))
    (Call ret dest args h).
Proof.
  intros H1 H2 s.
  destruct ret as [[x1 [x2 [q1 [x3 x4]]]]|], h as [[y1 [q2 [y2 y3]]]|];
    cbn iota in H1, H2;
    rewrite !(evaluate_eqn (Call _ _ _ _) s); cbn [evaluate_body add_ret_loc];
    unfold push_env; cong_split.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_Seq_assoc_lemma" *)
Theorem evaluate_Seq_assoc_lemma : forall (p1 p2 : prog a) s,
  evaluate (Seq_assoc p1 p2, s) = evaluate (Seq p1 p2, s).
Proof.
  intros p1 p2; revert p1.
  induction p2 as [ | | | | | | |q IHq|ret dest args h IHret IHh|q1 q2 IH1 IH2
                   |cmp r ri q1 q2 IH1 IH2|n1 q n2 IHq | | | | | | | | | | | | | |]
    using prog_nested_ind; intros p1 st; cbn [Seq_assoc];
    rewrite ?evaluate_SmartSeq; try reflexivity.
  - (* Skip *) rewrite evaluate_Seq_Skip. reflexivity.
  - (* MustTerminate *)
    apply eq_eval_Seq; [apply eq_eval_refl|]. apply eq_eval_MustTerminate.
    intros v. rewrite IHq, evaluate_Skip_Seq. reflexivity.
  - (* Call *)
    apply eq_eval_Seq; [apply eq_eval_refl|].
    apply (eq_eval_Call (fun q => Seq_assoc Skip q)).
    + destruct ret as [[? [? [q1 ?]]]|]; [|exact Logic.I].
      intros v; rewrite IHret, evaluate_Skip_Seq; reflexivity.
    + destruct h as [[? [q2 ?]]|]; [|exact Logic.I].
      intros v; rewrite IHh, evaluate_Skip_Seq; reflexivity.
  - (* Seq *)
    rewrite IH2. rewrite !evaluate_Seq_eq, IH1, evaluate_Seq_eq.
    destruct (evaluate (p1, st)) as [r t].
    destruct (bool_decide (r = NONE)) eqn:E; [|rewrite E; reflexivity].
    rewrite evaluate_Seq_eq. reflexivity.
  - (* If *)
    apply eq_eval_Seq; [apply eq_eval_refl|]. apply eq_eval_If; intros v;
      rewrite ?IH1, ?IH2, evaluate_Skip_Seq; reflexivity.
  - (* Loop *)
    apply eq_eval_Seq; [apply eq_eval_refl|]. apply eq_eval_Loop.
    intros v; rewrite IHq, evaluate_Skip_Seq; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_Seq_assoc" *)
Theorem evaluate_Seq_assoc : forall (p : prog a) s,
  evaluate (Seq_assoc Skip p, s) = evaluate (p, s).
Proof. intros; rewrite evaluate_Seq_assoc_lemma, evaluate_Skip_Seq; reflexivity. Qed.

End SeqAssoc.

Section Dest.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "dest_If_Eq_Imm_thm" *)
Theorem dest_If_Eq_Imm_thm : forall (x2 : prog a) n w p1 p2,
  dest_If_Eq_Imm x2 = SOME (n, (w, (p1, p2))) <-> x2 = If Equal n (Imm w) p1 p2.
Proof.
  intros x2 n w p1 p2; destruct x2; unfold dest_If_Eq_Imm, dest_If;
    try (split; intros H; discriminate H).
  match goal with |- context [If ?cc _ ?rr _ _] => destruct cc, rr end;
    split; intros H; try discriminate H; injection H; intros; subst; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "dest_If_thm" *)
Theorem dest_If_thm : forall (x2 : prog a) g1 g2 g3 g4 g5,
  dest_If x2 = SOME (g1, (g2, (g3, (g4, g5)))) <-> x2 = If g1 g2 g3 g4 g5.
Proof.
  intros x2 g1 g2 g3 g4 g5; destruct x2; unfold dest_If;
    split; intros H; try discriminate H; injection H; intros; subst; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "dest_Seq_IMP" *)
Theorem dest_Seq_IMP : forall (p1 x1 x2 : prog a) s,
  dest_Seq p1 = (x1, x2) -> evaluate (p1, s) = evaluate (Seq x1 x2, s).
Proof.
  intros p1 x1 x2 s H; destruct p1; unfold dest_Seq in H; injection H as <- <-;
    try (rewrite evaluate_Skip_Seq; reflexivity); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "dest_Seq_Assign_Const_IMP" *)
Theorem dest_Seq_Assign_Const_IMP : forall v (p q : prog a) w s,
  dest_Seq_Assign_Const v p = SOME (q, w) ->
  evaluate (p, s) = evaluate (Seq q (Assign v (Const w)), s).
Proof.
  intros v p q w s H; unfold dest_Seq_Assign_Const in H.
  destruct (dest_Seq p) as [p1 p2] eqn:E.
  destruct p2; try discriminate H. destruct e; try discriminate H.
  destruct (decide (n = v)) as [->|]; [|discriminate H]. injection H as <- <-.
  apply dest_Seq_IMP, E.
Qed.

End Dest.

(** ** Verification of [const_fp] *)

Section GcConsts.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "is_gc_word_const_def" *)
Definition is_gc_word_const (x : word_loc a) : bool :=
  match x with
  | Loc _ _ => true
  | Word w => is_gc_const w
  end.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "gc_fun_const_ok_def" *)
Definition gc_fun_const_ok (f : gc_fun_type a) : Prop :=
  forall x y, f x = SOME y ->
    LIST_REL (fun a0 b => is_gc_word_const a0 -> b = a0) (FST x) (FST y).

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "sf_gc_consts_def" *)
Definition sf_gc_consts (x y : stack_frame a) : Prop :=
  match x, y with
  | StackFrame _ l0 sv h, StackFrame _ l0' sw h' =>
      LIST_REL (fun '(ak, av) '(bk, bv) => ak = bk /\ (is_gc_word_const av -> bv = av)) sv sw /\
      l0 = l0' /\ h = h'
  end.

Lemma LIST_REL_refl {A} (R : A -> A -> Prop) l : (forall x, R x x) -> LIST_REL R l l.
Proof. intros HR; induction l; constructor; auto. Qed.

Lemma LIST_REL_trans {A} (R : A -> A -> Prop) l1 l2 l3 :
  (forall x y z, R x y -> R y z -> R x z) ->
  LIST_REL R l1 l2 -> LIST_REL R l2 l3 -> LIST_REL R l1 l3.
Proof.
  intros HR H1; revert l3; induction H1; intros l3 H2; inversion H2; subst; constructor; eauto.
Qed.

Lemma LIST_REL_length {A B} (R : A -> B -> Prop) l1 l2 : LIST_REL R l1 l2 -> length l1 = length l2.
Proof. induction 1; cbn; congruence. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "sf_gc_consts_refl" *)
Theorem sf_gc_consts_refl : forall x, sf_gc_consts x x.
Proof.
  intros [m l0 sv h]; cbn; split; [|split; reflexivity].
  apply LIST_REL_refl. intros [k v]; split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "sf_gc_consts_trans" *)
Theorem sf_gc_consts_trans : forall x y z,
  sf_gc_consts x y /\ sf_gc_consts y z -> sf_gc_consts x z.
Proof.
  intros [m1 l1 s1 h1] [m2 l2 s2 h2] [m3 l3 s3 h3] [[R1 [-> ->]] [R2 [-> ->]]]; cbn.
  split; [|split; reflexivity].
  eapply LIST_REL_trans; [|exact R1|exact R2].
  intros [k1 v1] [k2 v2] [k3 v3] [-> A1] [-> A2]; split; [reflexivity|].
  intros G. rewrite A2 by (rewrite A1 by exact G; exact G). apply A1, G.
Qed.

End GcConsts.

Section ConstFpExp.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "strip_const_thm" *)
Theorem strip_const_thm : forall (xs : list (exp a)) x s,
  strip_const xs = SOME x -> MAP (fun a0 => word_exp s a0) xs = MAP (SOME ∘ Word) x.
Proof.
  induction xs as [|e xs IH]; intros x s H; cbn in H.
  - injection H as <-. reflexivity.
  - destruct e; try discriminate H. destruct (strip_const xs) as [ws|] eqn:E; [|discriminate H].
    injection H as <-. cbn. rewrite (IH ws s eq_refl). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "the_words_thm" *)
Theorem the_words_thm : forall x : list (word a), the_words (MAP (SOME ∘ Word) x) = SOME x.
Proof. induction x as [|w x IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma MAP_word_exp_const_fp (args : list (exp a)) cs s :
  Forall (fun e => word_exp s (const_fp_exp e cs) = word_exp s e) args ->
  MAP (fun a0 => word_exp s a0) (MAP (fun a0 => const_fp_exp a0 cs) args) =
  MAP (fun a0 => word_exp s a0) args.
Proof. induction 1; cbn; congruence. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "const_fp_exp_word_exp" *)
Theorem const_fp_exp_word_exp : forall (e : exp a) cs s,
  (forall v w, lookup v cs = SOME w -> get_var v s = SOME (Word w)) ->
  word_exp s (const_fp_exp e cs) = word_exp s e.
Proof.
  intros e cs s Hcs.
  induction e as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using exp_nested_ind; cbn [const_fp_exp].
  - reflexivity.
  - destruct (lookup n cs) as [w|] eqn:E; [|reflexivity]. cbn. rewrite (Hcs _ _ E). reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn zeta. pose proof (MAP_word_exp_const_fp es cs s IH) as HM.
    destruct (strip_const (MAP (fun a0 => const_fp_exp a0 cs) es)) as [ws|] eqn:Es.
    + pose proof (strip_const_thm _ _ s Es) as HS. cbn [word_exp].
      change (List.map (word_exp s) es) with (MAP (fun a0 => word_exp s a0) es).
      rewrite <- HM, HS, the_words_thm.
      destruct (word_op op ws) as [w|] eqn:Ew; cbn [word_exp OPTION_MAP option_map].
      * reflexivity.
      * rewrite List.map_map. change (fun x => word_exp s (Const x)) with (SOME ∘ (@Word a)).
        rewrite the_words_thm, Ew. reflexivity.
    + cbn [word_exp].
      change (List.map (word_exp s) ?l) with (MAP (fun a0 => word_exp s a0) l). rewrite HM.
      reflexivity.
  - cbn zeta.
    destruct (const_fp_exp e1 cs) eqn:E1; cbn [word_exp]; rewrite <- ?IH1, <- ?IH2;
      try reflexivity;
      destruct (const_fp_exp e2 cs) eqn:E2; cbn [word_exp]; rewrite <- ?IH2; try reflexivity.
    destruct (word_sh sh w (w2n w0)) eqn:Es; cbn [word_exp OPTION_MAP option_map];
      rewrite ?Es; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "const_fp_exp_word_exp_const" *)
Theorem const_fp_exp_word_exp_const : forall (e : exp a) cs s c0,
  (forall v w, lookup v cs = SOME w -> get_var v s = SOME (Word w)) /\
  const_fp_exp e cs = Const c0 ->
  word_exp s e = SOME (Word c0).
Proof.
  intros e cs s c0 [Hcs H]. rewrite <- (const_fp_exp_word_exp e cs s Hcs), H. reflexivity.
Qed.

End ConstFpExp.

Section Moves.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "set_vars_move_NONE" *)
Theorem set_vars_move_NONE : forall (moves : list (N * N)) x s s' v,
  set_vars (MAP FST moves) x s = s' /\ ALOOKUP moves v = NONE ->
  get_var v s' = get_var v s.
Proof.
  induction moves as [|[q r] moves IH]; intros x s s' v [<- Hv]; [reflexivity|].
  cbn [ALOOKUP] in Hv. destruct (decide (q = v)) as [->|Hne]; [discriminate|].
  destruct x as [|y x]; [reflexivity|].
  unfold set_vars, get_var; cbn [List.map fst alist_insert locals set_locals].
  rewrite lookup_insert. destruct (decide (v = q)) as [->|]; [congruence|].
  exact (IH x s _ v (conj eq_refl Hv)).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "set_vars_move_SOME" *)
Theorem set_vars_move_SOME : forall (moves : list (N * N)) x v w s s',
  set_vars (MAP FST moves) x s = s' /\ get_vars (MAP SND moves) s = SOME x /\
  ALOOKUP moves v = SOME w ->
  get_var v s' = get_var w s.
Proof.
  induction moves as [|[q r] moves IH]; intros x v w s s' [<- [Hg Hv]]; [discriminate|].
  cbn [List.map fst snd get_vars] in Hg.
  destruct (get_var r s) as [y|] eqn:Er; [|discriminate].
  destruct (get_vars (MAP SND moves) s) as [ys|] eqn:Es; [|discriminate].
  injection Hg as <-. cbn [ALOOKUP] in Hv.
  unfold set_vars, get_var; cbn [List.map fst alist_insert locals set_locals].
  rewrite lookup_insert. destruct (decide (q = v)) as [->|Hne].
  - injection Hv as <-. destruct (decide (v = v)); [|congruence]. symmetry; exact Er.
  - destruct (decide (v = q)) as [->|]; [congruence|].
    exact (IH ys v w s _ (conj eq_refl (conj Es Hv))).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "get_var_move_thm" *)
Theorem get_var_move_thm : forall s s' (moves : list (N * N)) x v,
  get_vars (MAP SND moves) s = SOME x /\ set_vars (MAP FST moves) x s = s' ->
  get_var v s' = match ALOOKUP moves v with
                 | SOME w => get_var w s
                 | NONE => get_var v s
                 end.
Proof.
  intros s s' moves x v [Hg Hs]. destruct (ALOOKUP moves v) as [w|] eqn:E.
  - eapply set_vars_move_SOME; eauto.
  - eapply set_vars_move_NONE; eauto.
Qed.

End Moves.

Section MoveCs.
Context {a : N}.
Implicit Types cs : num_map (word a).

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "lookup_const_fp_move_cs_NONE" *)
Theorem lookup_const_fp_move_cs_NONE : forall (moves : list (N * N)) v cs cs',
  ALOOKUP moves v = NONE /\ lookup v cs = lookup v cs' ->
  lookup v (const_fp_move_cs moves cs cs') = lookup v cs'.
Proof.
  induction moves as [|[q r] moves IH]; intros v cs cs' [Hv Hl]; [reflexivity|].
  cbn [ALOOKUP] in Hv. destruct (decide (q = v)) as [->|Hne]; [discriminate|].
  cbn [const_fp_move_cs FST SND fst snd].
  destruct (lookup r cs) as [c0|].
  - rewrite IH; [rewrite lookup_insert; destruct (decide (v = q)); [congruence|reflexivity]|].
    split; [exact Hv|]. rewrite lookup_insert; destruct (decide (v = q)); [congruence|exact Hl].
  - rewrite IH; [rewrite lookup_delete; destruct (decide (v = q)); [congruence|reflexivity]|].
    split; [exact Hv|]. rewrite lookup_delete; destruct (decide (v = q)); [congruence|exact Hl].
Qed.

Lemma not_MEM_In {A} `{EqDecision A} (x : A) l : ~ MEM x l <-> ~ In x l.
Proof. unfold is_true; rewrite MEM_In; tauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "lookup_const_fp_move_cs_SOME_part" *)
Theorem lookup_const_fp_move_cs_SOME_part : forall (moves : list (N * N)) q cs cs' x,
  ~ MEM q (MAP FST moves) /\ lookup q cs' = x ->
  lookup q (const_fp_move_cs moves cs cs') = x.
Proof.
  induction moves as [|[q' r] moves IH]; intros q cs cs' x [Hm Hl]; [exact Hl|].
  apply not_MEM_In in Hm. cbn [List.map fst] in Hm.
  cbn [const_fp_move_cs FST SND fst snd]. apply IH.
  split; [apply not_MEM_In; intros H; apply Hm; right; exact H|].
  destruct (decide (q = q')) as [->|Hne]; [exfalso; apply Hm; left; reflexivity|].
  destruct (lookup r cs); rewrite ?lookup_insert, ?lookup_delete;
    (destruct (decide (q = q')); [congruence|exact Hl]).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "lookup_const_fp_move_cs_SOME" *)
Theorem lookup_const_fp_move_cs_SOME : forall (moves : list (N * N)) v w cs cs',
  ALOOKUP moves v = SOME w /\ ALL_DISTINCT (MAP FST moves) /\ lookup v cs = lookup v cs' ->
  lookup v (const_fp_move_cs moves cs cs') = lookup w cs.
Proof.
  induction moves as [|[q r] moves IH]; intros v w cs cs' [Hv [Hd Hl]]; [discriminate|].
  cbn [ALOOKUP] in Hv. cbn [List.map fst ALL_DISTINCT] in Hd. unfold is_true in Hd.
  apply andb_prop in Hd as [Hn Hd]. apply Bool.negb_true_iff in Hn.
  cbn [const_fp_move_cs FST SND fst snd].
  destruct (decide (q = v)) as [->|Hne].
  - injection Hv as <-. apply lookup_const_fp_move_cs_SOME_part. split.
    + intros H; unfold is_true in H; rewrite H in Hn; discriminate.
    + destruct (lookup r cs); rewrite ?lookup_insert, ?lookup_delete;
        (destruct (decide (v = v)); [reflexivity|congruence]).
  - apply IH. split; [exact Hv|]. split; [exact Hd|].
    destruct (lookup r cs); rewrite ?lookup_insert, ?lookup_delete;
      (destruct (decide (v = q)); [congruence|exact Hl]).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "lookup_const_fp_move_cs" *)
Theorem lookup_const_fp_move_cs : forall v (moves : list (N * N)) cs,
  ALL_DISTINCT (MAP FST moves) ->
  lookup v (const_fp_move_cs moves cs cs) = match ALOOKUP moves v with
                                            | SOME w => lookup w cs
                                            | NONE => lookup v cs
                                            end.
Proof.
  intros v moves cs Hd. destruct (ALOOKUP moves v) as [w|] eqn:E.
  - apply lookup_const_fp_move_cs_SOME; auto.
  - apply lookup_const_fp_move_cs_NONE; auto.
Qed.

End MoveCs.

Section Small.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "get_var_imm_cs_imp_get_var_imm" *)
Theorem get_var_imm_cs_imp_get_var_imm : forall (x : reg_imm a) y s cs,
  (forall v w, lookup v cs = SOME w -> get_var v s = SOME (Word w)) /\
  get_var_imm_cs x cs = SOME y ->
  get_var_imm x s = SOME (Word y).
Proof.
  intros [r|i] y s cs [Hcs H]; cbn in H |- *; [apply Hcs, H|injection H as <-; reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "get_var_set_var_thm" *)
Theorem get_var_set_var_thm : forall k1 k2 (v : word_loc a) s,
  get_var k1 (set_var k2 v s) = if decide (k1 = k2) then SOME v else get_var k1 s.
Proof. intros; unfold get_var, set_var; cbn [locals set_locals]. apply lookup_insert. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "get_var_mem_store_thm" *)
Theorem get_var_mem_store_thm : forall s' v addr (x : word_loc a) s,
  mem_store addr x s = SOME s' -> get_var v s' = get_var v s.
Proof.
  intros s' v addr x s H; unfold mem_store in H; destruct (classical_dec _); [|discriminate].
  injection H as <-. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "cs_delete_if_set" *)
Theorem cs_delete_if_set : forall (x : word_loc a) v1 v2 s cs w,
  (forall v w, lookup v cs = SOME w -> get_var v s = SOME (Word w)) /\
  lookup v2 (delete v1 cs) = SOME w ->
  get_var v2 (set_var v1 x s) = SOME (Word w).
Proof.
  intros x v1 v2 s cs w [Hcs H]. rewrite lookup_delete in H. rewrite get_var_set_var_thm.
  destruct (decide (v2 = v1)); [discriminate|]. apply Hcs, H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "cs_delete_if_set_x2" *)
Theorem cs_delete_if_set_x2 : forall (x1 x2 : word_loc a) v1 v2 v3 s cs w,
  (forall v w, lookup v cs = SOME w -> get_var v s = SOME (Word w)) /\
  lookup v3 (delete v2 (delete v1 cs)) = SOME w ->
  get_var v3 (set_var v2 x2 (set_var v1 x1 s)) = SOME (Word w).
Proof.
  intros x1 x2 v1 v2 v3 s cs w [Hcs H]. rewrite !lookup_delete in H. rewrite !get_var_set_var_thm.
  destruct (decide (v3 = v2)); [discriminate|]. destruct (decide (v3 = v1)); [discriminate|].
  apply Hcs, H.
Qed.

End Small.

Section Lookups.
Context {A : Type}.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "lookup_inter_eq_some" *)
Theorem lookup_inter_eq_some : forall `{EqDecision A} (m1 m2 : spt A) k x,
  lookup k (inter_eq m1 m2) = SOME x -> lookup k m1 = SOME x /\ lookup k m2 = SOME x.
Proof.
  intros EA m1 m2 k x H. rewrite lookup_inter_eq in H.
  destruct (lookup k m1); [|discriminate]. destruct (decide _) as [E|]; [|discriminate].
  injection H as ->. auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "lookup_filter_v_SOME" *)
Theorem lookup_filter_v_SOME : forall (t : spt A) k v f,
  lookup k (filter_v f t) = SOME v -> f v.
Proof.
  intros t k v f H. rewrite lookup_filter_v in H. destruct (lookup k t) as [u|]; [|discriminate].
  destruct (f u) eqn:E; [injection H as <-; exact E|discriminate].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "lookup_filter_v_SOME_imp" *)
Theorem lookup_filter_v_SOME_imp : forall (t : spt A) k v f,
  lookup k (filter_v f t) = SOME v -> lookup k t = SOME v.
Proof.
  intros t k v f H. rewrite lookup_filter_v in H. destruct (lookup k t) as [u|]; [|discriminate].
  destruct (f u); [exact H|discriminate].
Qed.

End Lookups.

(** ** Lists and stacks *)

Section ListRel.

Lemma LIST_REL_app_inv {A B} (R : A -> B -> Prop) l1 l2 l :
  LIST_REL R (l1 ++ l2) l ->
  LIST_REL R l1 (firstn (length l1) l) /\ LIST_REL R l2 (skipn (length l1) l).
Proof.
  revert l; induction l1 as [|x l1 IH]; intros l H; cbn; [split; [constructor|exact H]|].
  inversion H; subst. match goal with HH : LIST_REL R (l1 ++ l2) _ |- _ => destruct (IH _ HH) as [G1 G2] end. split; [constructor; assumption|exact G2].
Qed.

Lemma LIST_REL_app {A B} (R : A -> B -> Prop) l1 l2 m1 m2 :
  LIST_REL R l1 m1 -> LIST_REL R l2 m2 -> LIST_REL R (l1 ++ l2) (m1 ++ m2).
Proof. induction 1; intros G; cbn; [exact G|constructor; auto]. Qed.

Lemma LIST_REL_rev {A B} (R : A -> B -> Prop) l1 l2 :
  LIST_REL R l1 l2 -> LIST_REL R (rev l1) (rev l2).
Proof. induction 1; cbn; [constructor|]. apply LIST_REL_app; [assumption|repeat constructor; auto]. Qed.

Lemma LIST_REL_skipn {A B} (R : A -> B -> Prop) n l1 l2 :
  LIST_REL R l1 l2 -> LIST_REL R (skipn n l1) (skipn n l2).
Proof. revert l1 l2; induction n; intros l1 l2 H; [exact H|]. inversion H; subst; cbn; [constructor|auto]. Qed.

Lemma LIST_REL_firstn {A B} (R : A -> B -> Prop) n l1 l2 :
  LIST_REL R l1 l2 -> LIST_REL R (firstn n l1) (firstn n l2).
Proof. revert l1 l2; induction n; intros l1 l2 H; [constructor|]. inversion H; subst; cbn; constructor; auto. Qed.

(** Galette-only: [LASTN] as a [skipn]. *)
Lemma LASTN_skipn {A} n (l : list A) : LASTN n l = skipn (length l - N.to_nat n) l.
Proof. unfold LASTN. rewrite TAKE_firstn, firstn_rev, rev_involutive. reflexivity. Qed.

Lemma LIST_REL_LASTN {A B} (R : A -> B -> Prop) n l1 l2 :
  LIST_REL R l1 l2 -> LIST_REL R (LASTN n l1) (LASTN n l2).
Proof. intros H; rewrite !LASTN_skipn, (LIST_REL_length _ _ _ H). apply LIST_REL_skipn, H. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "LIST_REL_prefix" *)
Theorem LIST_REL_prefix : forall {A B} (R : A -> B -> Prop) l1 l2 l1' l2',
  LIST_REL R (l1 ++ l2) (l1' ++ l2') /\ LENGTH l1 = LENGTH l1' -> LIST_REL R l1 l1'.
Proof.
  intros A B R l1 l2 l1' l2' [H Hl]. apply LIST_REL_app_inv in H as [H _].
  rewrite !LENGTH_length in Hl. apply N2Nat.inj_iff in Hl. rewrite !Nat2N.id in Hl.
  rewrite Hl, firstn_app, Nat.sub_diag, firstn_all in H. cbn in H. rewrite app_nil_r in H. exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "LIST_REL_append_left" *)
Theorem LIST_REL_append_left : forall {A B} (l0 : list A) l1 (l2 : list B) R,
  LIST_REL R (l0 ++ l1) l2 ->
  LIST_REL R l0 (TAKE (LENGTH l0) l2) /\ LIST_REL R l1 (DROP (LENGTH l0) l2).
Proof.
  intros A B l0 l1 l2 R H. rewrite TAKE_firstn, DROP_skipn, LENGTH_length, Nat2N.id.
  apply LIST_REL_app_inv, H.
Qed.

End ListRel.

Section Stacks.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "push_env_set_store_stack" *)
Theorem push_env_set_store_stack : forall x1 (x2 : option (N * (prog a * (N * N)))) x3 x4 s,
  stack (push_env x1 x2 (set_store x3 x4 s)) = stack (push_env x1 x2 s).
Proof.
  intros x1 [[? [? [? ?]]]|] x3 x4 s; unfold push_env; cbn [permute set_store set_store_field];
    destruct (env_to_list _ _); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "pop_env_stack_gc" *)
Theorem pop_env_stack_gc : forall s' s, pop_env s = SOME s' -> gc_fun s' = gc_fun s.
Proof.
  intros s' s H; unfold pop_env in H. destruct (stack s) as [|[m e0 e [[n x]|]] xs];
    try discriminate; injection H as <-; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "ALOOKUP_LIST_REL_sf_gc_consts" *)
Theorem ALOOKUP_LIST_REL_sf_gc_consts : forall (l1 l2 : list (N * word_loc a)) k v,
  LIST_REL (fun '(ak, av) '(bk, bv) => ak = bk /\ (is_gc_word_const av -> bv = av)) l1 l2 /\
  is_gc_word_const v /\ ALOOKUP l1 k = SOME v ->
  ALOOKUP l2 k = SOME v.
Proof.
  intros l1 l2 k v [H [Hv Hl]]. induction H as [|[ak av] [bk bv] l1 l2 [-> Hb] H IH]; [exact Hl|].
  cbn [ALOOKUP] in Hl |- *. destruct (decide (bk = k)) as [->|]; [|apply IH, Hl].
  injection Hl as ->. rewrite Hb by exact Hv. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "ALOOKUP_LIST_REL_sf_gc_consts_NONE" *)
Theorem ALOOKUP_LIST_REL_sf_gc_consts_NONE : forall (l1 l2 : list (N * word_loc a)) k (v : word_loc a),
  LIST_REL (fun '(ak, av) '(bk, bv) => ak = bk /\ (is_gc_word_const av -> bv = av)) l1 l2 /\
  ALOOKUP l1 k = NONE ->
  ALOOKUP l2 k = NONE.
Proof.
  intros l1 l2 k v [H Hl]. induction H as [|[ak av] [bk bv] l1 l2 [-> Hb] H IH]; [exact Hl|].
  cbn [ALOOKUP] in Hl |- *. destruct (decide (bk = k)); [discriminate|apply IH, Hl].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "ALOOKUP_LIST_REL_value_rel" *)
Theorem ALOOKUP_LIST_REL_value_rel : forall {K V} `{EqDecision K} (f : V -> Prop) (l' l : list (K * V)) k v,
  LIST_REL (fun '(ak, av) '(bk, bv) => ak = bk /\ (f av -> bv = av)) l' l /\
  ALOOKUP l' k = SOME v /\ f v ->
  ALOOKUP l k = SOME v.
Proof.
  intros K V EK f l' l k v [H [Hl Hv]]. induction H as [|[ak av] [bk bv] l1 l2 [-> Hb] H IH]; [exact Hl|].
  cbn [ALOOKUP] in Hl |- *. destruct (decide (bk = k)) as [->|]; [|apply IH, Hl].
  injection Hl as ->. rewrite Hb by exact Hv. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "pop_env_gc_fun" *)
Theorem pop_env_gc_fun : forall s s', pop_env s = SOME s' -> gc_fun s' = gc_fun s.
Proof. intros s s' H; exact (pop_env_stack_gc s' s H). Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "pop_env_gc_fun_const_ok" *)
Theorem pop_env_gc_fun_const_ok : forall s s',
  pop_env s = SOME s' /\ gc_fun_const_ok (gc_fun s) -> gc_fun_const_ok (gc_fun s').
Proof. intros s s' [H Hg]. rewrite (pop_env_gc_fun _ _ H). exact Hg. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_gc_fun_const_ok" *)
Theorem evaluate_gc_fun_const_ok : forall (p : prog a) s res s',
  evaluate (p, s) = (res, s') /\ gc_fun_const_ok (gc_fun s) -> gc_fun_const_ok (gc_fun s').
Proof. intros p s res s' [H Hg]. destruct (evaluate_consts _ _ _ _ H) as [<- _]. exact Hg. Qed.

(** HOL's [EL] beyond the end of a list is unspecified; Galette's [EL]
    needs an [Inhabited] instance (Galette-only). *)
#[local] Instance stack_frame_inhabited : Inhabited (stack_frame a) := StackFrame NONE [] [] NONE.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "get_above_handler_def" *)
Definition get_above_handler (s : state a c ffi_t) : N :=
  match EL (LENGTH (stack s) - (handler s + 1)) (stack s) with
  | StackFrame _ _ _ (SOME (h, _)) => h
  | _ => ARB
  end.

End Stacks.

Section GcStacks.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.
#[local] Instance stack_frame_inhabited' : Inhabited (stack_frame a) := StackFrame NONE [] [] NONE.

Lemma ZIP_cons {A B} (x : A) xs (y : B) ys : ZIP (x :: xs, y :: ys) = (x, y) :: ZIP (xs, ys).
Proof. reflexivity. Qed.

Lemma LIST_REL_ZIP (l : list (N * word_loc a)) ys :
  LIST_REL (fun a0 b => is_gc_word_const a0 -> b = a0) (MAP SND l) ys ->
  LIST_REL (fun '(ak, av) '(bk, bv) => ak = bk /\ (is_gc_word_const av -> bv = av))
    l (ZIP (MAP FST l, ys)).
Proof.
  revert ys; induction l as [|[k v] l IH]; intros ys H; inversion H; subst; [constructor|].
  cbn [List.map fst snd]. rewrite ZIP_cons. constructor; [split; auto|]. apply IH; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "enc_stack_dec_stack_is_gc_word_const" *)
Theorem enc_stack_dec_stack_is_gc_word_const : forall (st sk' : list (stack_frame a)) s'l,
  LIST_REL (fun a0 b => is_gc_word_const a0 -> b = a0) (enc_stack st) s'l /\
  dec_stack s'l st = SOME sk' ->
  LIST_REL sf_gc_consts st sk'.
Proof.
  induction st as [|[n l0 l h] st IH]; intros sk' s'l [H1 H2]; cbn [enc_stack dec_stack] in *.
  - destruct s'l; [injection H2 as <-; constructor|discriminate].
  - destruct (LENGTH s'l <? LENGTH l); [discriminate|].
    destruct (dec_stack (DROP (LENGTH l) s'l) st) as [s0|] eqn:E; [|discriminate].
    injection H2 as <-. apply LIST_REL_app_inv in H1 as [G1 G2].
    rewrite length_map in G1, G2. constructor.
    + cbn. split; [|split; reflexivity]. apply LIST_REL_ZIP.
      rewrite TAKE_firstn, LENGTH_length, Nat2N.id. exact G1.
    + apply (IH s0 (DROP (LENGTH l) s'l)). split; [|exact E].
      rewrite DROP_skipn, LENGTH_length, Nat2N.id. exact G2.
Qed.

(** HOL's bound variables [s], [s'], [gc_fun], [memory], [mdomain],
    [store] are [sk], [sk'], [gf], [m], [md], [st] (they would shadow the
    state fields, or are not states). *)
(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "gc_fun_sf_gc_consts" *)
Theorem gc_fun_sf_gc_consts : forall (sk : list (stack_frame a)) s'l sk' (gf : gc_fun_type a) m m' md st st',
  gc_fun_const_ok gf /\ gf (enc_stack sk, (m, (md, st))) = SOME (s'l, (m', st')) /\
  dec_stack s'l sk = SOME sk' ->
  LIST_REL sf_gc_consts sk sk'.
Proof.
  intros sk s'l sk' gf m m' md st st' [Hok [Hg Hd]].
  apply (enc_stack_dec_stack_is_gc_word_const sk sk' s'l). split; [|exact Hd].
  exact (Hok _ _ Hg).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "gc_sf_gc_consts" *)
Theorem gc_sf_gc_consts : forall s s',
  gc_fun_const_ok (gc_fun s) /\ gc s = SOME s' -> LIST_REL sf_gc_consts (stack s) (stack s').
Proof.
  intros s s' [Hok H]; unfold gc in H.
  destruct (gc_fun s _) as [[wl [m st]]|] eqn:Eg; [|discriminate].
  destruct (dec_stack wl (stack s)) as [sk|] eqn:Ed; [|discriminate].
  injection H as <-. cbn. eapply gc_fun_sf_gc_consts; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "gc_handler" *)
Theorem gc_handler : forall s s', gc s = SOME s' -> handler s' = handler s.
Proof.
  intros s s' H; unfold gc in H. destruct (gc_fun s _) as [[wl [m st]]|]; [|discriminate].
  destruct (dec_stack wl (stack s)); [|discriminate]. injection H as <-. reflexivity.
Qed.

Lemma LIST_REL_nth {A B} (R : A -> B -> Prop) l1 l2 i d1 d2 :
  LIST_REL R l1 l2 -> (i < length l1)%nat -> R (nth i l1 d1) (nth i l2 d2).
Proof.
  intros H; revert i; induction H as [|x y l1 l2 Hxy H IH]; intros i Hi; cbn in Hi; [lia|].
  destruct i; cbn; [exact Hxy|apply IH; lia].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "sf_gc_consts_get_above_handler" *)
Theorem sf_gc_consts_get_above_handler : forall s s',
  LIST_REL sf_gc_consts (stack s) (stack s') /\ handler s' = handler s /\
  handler s < LENGTH (stack s) ->
  get_above_handler s' = get_above_handler s.
Proof.
  intros s s' [H [Hh Hl]]. unfold get_above_handler. rewrite Hh.
  pose proof (LIST_REL_length _ _ _ H) as HL. rewrite !LENGTH_length in *. rewrite <- HL.
  rewrite !EL_nth by (rewrite LENGTH_length; lia; rewrite HL; lia).
  pose proof (LIST_REL_nth _ _ _ (N.to_nat (N.of_nat (length (stack s)) - (handler s + 1)))
                ARB ARB H ltac:(lia)) as Hf.
  destruct (nth _ (stack s) ARB) as [m1 l1 e1 h1], (nth _ (stack s') ARB) as [m2 l2 e2 h2].
  cbn in Hf. destruct Hf as [_ [_ ->]]. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "LIST_REL_call_Result" *)
Theorem LIST_REL_call_Result : forall s (s' : state a c ffi_t) s'' s''' env (h : option (N * (prog a * (N * N)))),
  LIST_REL sf_gc_consts (stack (push_env env h s)) (stack s'') /\
  pop_env s'' = SOME s''' /\ handler s'' = handler (push_env env h s) ->
  LIST_REL sf_gc_consts (stack s) (stack s''') /\ handler s''' = handler s.
Proof.
  intros s s' s'' s''' env h [H [Hp Hh]].
  unfold pop_env in Hp.
  destruct h as [[hv [hp [l1 l2]]]|]; unfold push_env in H, Hh;
    destruct (env_to_list _ _) as [l perm];
    cbn [stack handler set_handler set_permute set_stack_max set_stack] in H, Hh;
    inversion H as [|f0 f' r0 rest Hf Hrest E1 E2]; subst;
    rewrite <- E2 in Hp;
    destruct f' as [m' e0' e' [[n x]|]]; cbn [sf_gc_consts] in Hf;
    destruct Hf as [_ [_ Hh']]; try discriminate Hh';
    injection Hp as <-; cbn [stack handler set_handler set_locals_size set_stack set_locals];
    (split; [exact Hrest|]).
  - injection Hh' as <- _. reflexivity.
  - exact Hh.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "get_above_handler_call_env_push_env_dec_clock" *)
Theorem get_above_handler_call_env_push_env_dec_clock :
  forall s s' (s'' : state a c ffi_t) args lsz env x0 x1 x2 x3,
  s' = call_env args lsz (push_env env (SOME (x0, (x1, (x2, x3)))) (dec_clock s)) /\
  handler s'' = get_above_handler s' ->
  handler s'' = handler s.
Proof.
  intros s s' s'' args lsz env x0 x1 x2 x3 [-> Hh]. rewrite Hh. unfold get_above_handler.
  unfold push_env. destruct (env_to_list _ _) as [l perm]. cbn.
  replace (N.succ (LENGTH (stack s)) - (LENGTH (stack s) + 1)) with 0 by lia. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "call_env_push_env_dec_clock_handler_length" *)
Theorem call_env_push_env_dec_clock_handler_length :
  forall s s' args lsz env x0 x1 x2 x3,
  s' = call_env args lsz (push_env env (SOME (x0, (x1, (x2, x3)))) (dec_clock s)) ->
  handler s' < LENGTH (stack s').
Proof.
  intros s s' args lsz env x0 x1 x2 x3 ->. unfold push_env.
  destruct (env_to_list _ _) as [l perm]. cbn. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "EVERY2_trans_LASTN_sf_gc_consts" *)
Theorem EVERY2_trans_LASTN_sf_gc_consts : forall (l l' l'' : list (stack_frame a)) n (R : Prop),
  n <= LENGTH l /\ LIST_REL sf_gc_consts l l' /\ LIST_REL sf_gc_consts (LASTN n l') l'' ->
  LIST_REL sf_gc_consts (LASTN n l) l''.
Proof.
  intros l l' l'' n R [_ [H1 H2]]. eapply LIST_REL_trans; [|apply LIST_REL_LASTN, H1|exact H2].
  intros x y z Hxy Hyz; apply (sf_gc_consts_trans x y z); split; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "LIST_REL_push_env" *)
Theorem LIST_REL_push_env : forall (R : stack_frame a -> stack_frame a -> Prop) s (s' : state a c ffi_t) env h,
  LIST_REL R (stack (push_env env h s)) (stack s') -> LIST_REL R (stack s) (TL (stack s')).
Proof.
  intros R s s' env h H. destruct h as [[? [? [? ?]]]|]; unfold push_env in H;
    destruct (env_to_list _ _); cbn in H; inversion H; subst; cbn; assumption.
Qed.

End GcStacks.

Section LastN.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "LASTN_LENGTH_CONS" *)
Theorem LASTN_LENGTH_CONS : forall {A} (l : list A) h, LASTN (LENGTH l) (h :: l) = l.
Proof.
  intros A l h. rewrite LASTN_skipn, LENGTH_length, Nat2N.id.
  change (Datatypes.length (h :: l)) with (Datatypes.S (Datatypes.length l)).
  rewrite Nat.sub_succ_l, Nat.sub_diag by lia. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "LASTN_TL_res" *)
Theorem LASTN_TL_res : forall {A} (l : list A) n h t,
  n < LENGTH l /\ LASTN (n + 1) l = h :: t -> t = LASTN n l.
Proof.
  intros A l n h t [Hn H]. rewrite LASTN_skipn in H |- *. rewrite LENGTH_length in Hn.
  replace (length l - N.to_nat n)%nat with (Datatypes.S (length l - N.to_nat (n + 1))) by lia.
  rewrite <- (skipn_skipn 1 (length l - N.to_nat (n + 1))), H. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "HD_LASTN" *)
Theorem HD_LASTN : forall {A} `{Inhabited A} (l : list A) n,
  0 < n /\ n <= LENGTH l -> HD (LASTN n l) = EL (LENGTH l - n) l.
Proof.
  intros A HA l n [H0 Hn]. rewrite LASTN_skipn. rewrite EL_nth by lia.
  rewrite LENGTH_length in *. rewrite N2Nat.inj_sub, Nat2N.id.
  remember (length l - N.to_nat n)%nat as k.
  assert (Hk : (k < length l)%nat) by lia. clear Heqk Hn H0.
  revert l Hk; induction k as [|k IH]; intros [|x l] Hk; cbn in *; try lia; [reflexivity|].
  apply IH; lia.
Qed.

End LastN.

Section PushPop.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "push_env_pop_env_locals_thm" *)
Theorem push_env_pop_env_locals_thm : forall s s' s'' s''' env (names : cutsets)
    (h : option (N * (prog a * (N * N)))),
  cut_envs names (locals s) = SOME env /\ push_env env h s = s' /\
  LIST_REL sf_gc_consts (stack s') (stack s'') /\ pop_env s'' = SOME s''' ->
  (forall v w, get_var v s = SOME w /\ is_gc_word_const w /\ lookup v (all_names names) <> NONE ->
               get_var v s''' = SOME w).
Proof.
  intros s s' s'' s''' env [n0 n1] h [Hc [Hp [HL Hpop]]] v w [Hv [Hg Hn]].
  unfold cut_envs, cut_names in Hc; cbn [FST SND fst snd] in Hc.
  destruct (classical_dec (domain n0 SUBSET domain (locals s))); [|discriminate].
  destruct (classical_dec (domain n1 SUBSET domain (locals s))); [|discriminate].
  injection Hc as <-. subst s'.
  destruct (env_to_list (inter (locals s) n1) (permute s)) as [l perm] eqn:Ee.
  destruct (Galette.cakeml.compiler.backend.semantics.wordProps.code.env_to_list_lookup_equiv
              _ _ _ _ Ee) as [Hl _].
  assert (HS : stack (push_env (inter (locals s) n0, inter (locals s) n1) h s) =
               StackFrame (locals_size s) (toAList (inter (locals s) n0)) l
                 (match h with NONE => NONE | SOME (_, (_, (l1, l2))) => SOME (handler s, (l1, l2)) end)
               :: stack s).
  { destruct h as [[? [? [? ?]]]|]; unfold push_env; cbn [FST SND fst snd]; rewrite Ee; reflexivity. }
  rewrite HS in HL. inversion HL as [|f0 f' r0 rest Hf Hrest E1 E2]; subst.
  unfold pop_env in Hpop. rewrite <- E2 in Hpop.
  destruct f' as [m' e0' e' h']. cbn [sf_gc_consts] in Hf. destruct Hf as [Hrel [<- _]].
  assert (Hloc : locals s''' = union (fromAList e') (fromAList (toAList (inter (locals s) n0)))).
  { destruct h' as [[? ?]|]; injection Hpop as <-; reflexivity. }
  unfold get_var in Hv |- *. rewrite Hloc, lookup_union, !lookup_fromAList.
  unfold all_names in Hn. rewrite lookup_union in Hn.
  destruct (lookup v n1) as [u|] eqn:E1.
  - assert (Ha : ALOOKUP l v = SOME w) by (rewrite Hl, lookup_inter, Hv, E1; reflexivity).
    rewrite (ALOOKUP_LIST_REL_sf_gc_consts l e' v w (conj Hrel (conj Hg Ha))). reflexivity.
  - assert (Ha : ALOOKUP l v = NONE) by (rewrite Hl, lookup_inter, Hv, E1; reflexivity).
    rewrite (ALOOKUP_LIST_REL_sf_gc_consts_NONE l e' v w (conj Hrel Ha)).
    rewrite <- lookup_fromAList, lookup_fromAList_toAList, lookup_inter, Hv.
    destruct (lookup v n0); [reflexivity|]. exfalso; apply Hn; reflexivity.
Qed.

End PushPop.

(** ** [evaluate_sf_gc_consts] *)

Section SfGcConsts.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.
#[local] Instance stack_frame_inhabited'' : Inhabited (stack_frame a) := StackFrame NONE [] [] NONE.

(** Galette-only: the conclusion of [evaluate_sf_gc_consts]. *)
Definition sf_post s (res : option (result a)) s' : Prop :=
  match res with
  | NONE => LIST_REL sf_gc_consts (stack s) (stack s') /\ handler s' = handler s
  | SOME (Result _ _) => LIST_REL sf_gc_consts (stack s) (stack s') /\ handler s' = handler s
  | SOME (Exception _ _) =>
      handler s < LENGTH (stack s) ->
      LIST_REL sf_gc_consts (LASTN (handler s) (stack s)) (stack s') /\
      handler s' = get_above_handler s
  | SOME (Break _) => LIST_REL sf_gc_consts (stack s) (stack s') /\ handler s' = handler s
  | SOME (Continue _) => LIST_REL sf_gc_consts (stack s) (stack s') /\ handler s' = handler s
  | _ => True
  end.

Lemma sf_refl (l : list (stack_frame a)) : LIST_REL sf_gc_consts l l.
Proof. apply LIST_REL_refl, sf_gc_consts_refl. Qed.

Lemma sf_trans (l1 l2 l3 : list (stack_frame a)) :
  LIST_REL sf_gc_consts l1 l2 -> LIST_REL sf_gc_consts l2 l3 -> LIST_REL sf_gc_consts l1 l3.
Proof. apply LIST_REL_trans. intros x y z H1 H2; exact (sf_gc_consts_trans x y z (conj H1 H2)). Qed.

Lemma get_above_handler_cong s t :
  stack s = stack t -> handler s = handler t -> get_above_handler s = get_above_handler t.
Proof. intros E1 E2; unfold get_above_handler; rewrite E1, E2; reflexivity. Qed.

Lemma sf_post_cong s0 s r t0 t :
  stack s = stack s0 -> handler s = handler s0 -> stack t = stack t0 -> handler t = handler t0 ->
  sf_post s0 r t0 -> sf_post s r t.
Proof.
  intros E1 E2 E3 E4 H. unfold sf_post in *. rewrite (get_above_handler_cong s s0 E1 E2).
  rewrite E1, E2, E3, E4. exact H.
Qed.

Lemma sf_post_trans s s1 r t :
  LIST_REL sf_gc_consts (stack s) (stack s1) -> handler s1 = handler s ->
  sf_post s1 r t -> sf_post s r t.
Proof.
  intros HL Hh H. destruct r as [[]|]; cbn in H |- *; auto;
    try (destruct H as [H1 H2]; split; [eapply sf_trans; eassumption|congruence]).
  intros Hlt. pose proof (LIST_REL_length _ _ _ HL) as Hlen.
  rewrite !LENGTH_length in *. rewrite Hh in H.
  destruct H as [H1 H2]; [rewrite <- Hlen; exact Hlt|]. split.
  - apply (EVERY2_trans_LASTN_sf_gc_consts _ (stack s1) _ _ True).
    split; [rewrite LENGTH_length; lia|split; assumption].
  - rewrite H2. apply sf_gc_consts_get_above_handler. split; [exact HL|split; [exact Hh|]].
    rewrite LENGTH_length; exact Hlt.
Qed.

Lemma sf_post_exit_loop s r t : sf_post s r t -> sf_post s (exit_loop r) t.
Proof. destruct r as [[]|]; cbn; auto. Qed.

Lemma alloc_sf w names s r t :
  gc_fun_const_ok (gc_fun s) -> alloc w names s = (r, t) -> r = NONE ->
  LIST_REL sf_gc_consts (stack s) (stack t) /\ handler t = handler s.
Proof.
  intros Hok H ->. unfold alloc in H.
  destruct (cut_envs names (locals s)) as [envs|] eqn:Ec; [|discriminate].
  destruct (gc _) as [s1|] eqn:Eg; [|discriminate].
  destruct (pop_env s1) as [s2|] eqn:Ep; [|discriminate].
  assert (G : LIST_REL sf_gc_consts (stack s) (stack s2) /\ handler s2 = handler s).
  { assert (Hok' : gc_fun_const_ok (gc_fun (push_env envs (NONE : option (N * (prog a * (N * N))))
                                                (set_store stackLang.AllocSize (Word w) s)))).
    { unfold push_env; destruct (env_to_list _ _); exact Hok. }
    pose proof (gc_sf_gc_consts _ _ (conj Hok' Eg)) as HL.
    pose proof (gc_handler _ _ Eg) as Hh.
    exact (LIST_REL_call_Result (set_store stackLang.AllocSize (Word w) s) s1 s1 s2 envs NONE
             (conj HL (conj Ep Hh))). }
  destruct (get_store stackLang.AllocSize s2); [|discriminate].
  destruct (has_space w0 s2) as [[]|]; try discriminate. injection H as <-. exact G.
Qed.

Lemma mem_store_sf x y s t :
  mem_store x y s = SOME t -> stack t = stack s /\ handler t = handler s.
Proof. intros H; pose proof (mem_store_const _ _ _ _ H); destr_conj; split; congruence. Qed.

Lemma share_inst_sf op v ad s r t :
  share_inst op v ad s = (r, t) -> r = NONE -> stack t = stack s /\ handler t = handler s.
Proof.
  intros H ->; destruct op; cbn [share_inst] in H;
    unfold sh_mem_set_var, sh_mem_load, sh_mem_load_byte, sh_mem_load16, sh_mem_load32,
      sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32 in H;
    split_H H;
    repeat match goal with
           | E : context [match ?x with _ => _ end] |- _ =>
               destruct x; cbn beta iota in E; try discriminate E
           end;
    try discriminate H; inversion H; subst;
    repeat match goal with E : mem_store _ _ _ = SOME _ |- _ => apply mem_store_sf in E end;
    destr_conj; cbn [stack handler set_var set_locals set_memory set_ffi]; auto.
Qed.



Lemma inst_sf i s t : inst i s = SOME t -> stack t = stack s /\ handler t = handler s.
Proof. intros H; pose proof (inst_const_full _ _ _ H); destr_conj; split; congruence. Qed.

Lemma jump_exc_sf s t l1 l2 :
  jump_exc s = SOME (t, (l1, l2)) ->
  LIST_REL sf_gc_consts (LASTN (handler s) (stack s)) (stack t) /\ handler t = get_above_handler s.
Proof.
  intros H; unfold jump_exc in H. destruct (handler s <? LENGTH (stack s)) eqn:Hl; [|discriminate].
  apply N.ltb_lt in Hl.
  destruct (LASTN (handler s + 1) (stack s)) as [|[m e0 e [[n [k1 k2]]|]] xs] eqn:E; try discriminate.
  injection H as <- _ _. cbn [stack handler set_locals_size set_stack set_locals set_handler].
  split.
  - rewrite <- (LASTN_TL_res (stack s) (handler s) _ xs (conj Hl E)). apply sf_refl.
  - unfold get_above_handler. rewrite <- HD_LASTN by lia. rewrite E. reflexivity.
Qed.

Lemma get_above_handler_push_NONE s envs (args : list (word_loc a)) lsz :
  handler s < LENGTH (stack s) ->
  get_above_handler (call_env args lsz (push_env envs (NONE : option (N * (prog a * (N * N))))
                                          (dec_clock s))) =
  get_above_handler s.
Proof.
  intros Hl. unfold get_above_handler, push_env. destruct (env_to_list _ _) as [l perm].
  cbn [stack handler call_env dec_clock set_stack_max set_locals_size set_locals set_clock
       set_permute set_stack LENGTH].
  rewrite (EL_nth (_ - _)) by (cbn [LENGTH]; lia).
  rewrite (EL_nth (_ - _) (stack s)) by lia.
  rewrite LENGTH_length in *.
  replace (N.to_nat (N.succ (N.of_nat (length (stack s))) - (handler s + 1)))
    with (Datatypes.S (N.to_nat (N.of_nat (length (stack s)) - (handler s + 1)))) by lia.
  reflexivity.
Qed.

Lemma LASTN_push_NONE s envs (args : list (word_loc a)) lsz :
  handler s < LENGTH (stack s) ->
  LASTN (handler s) (stack (call_env args lsz (push_env envs (NONE : option (N * (prog a * (N * N))))
                                                  (dec_clock s)))) =
  LASTN (handler s) (stack s).
Proof.
  intros Hl. unfold push_env. destruct (env_to_list _ _) as [l perm].
  cbn [stack call_env dec_clock set_stack_max set_locals_size set_locals set_clock set_permute
       set_stack]. rewrite !LASTN_skipn. rewrite LENGTH_length in Hl.
  change (Datatypes.length (?x :: ?y)) with (Datatypes.S (Datatypes.length y)).
  replace (Datatypes.S (Datatypes.length (stack s)) - N.to_nat (handler s))%nat
    with (Datatypes.S (Datatypes.length (stack s) - N.to_nat (handler s))) by lia.
  reflexivity.
Qed.

Lemma sf_same s t : stack t = stack s -> LIST_REL sf_gc_consts (stack s) (stack t).
Proof. intros ->; apply sf_refl. Qed.

Lemma alloc_post w names s r t :
  gc_fun_const_ok (gc_fun s) -> alloc w names s = (r, t) -> sf_post s r t.
Proof.
  intros Hok H. destruct r as [x|]; [|exact (alloc_sf w names s NONE t Hok H eq_refl)].
  assert (Hx : x = Error \/ x = NotEnoughSpace).
  { unfold alloc in H; split_H H; inversion H; auto. }
  destruct Hx as [-> | ->]; exact Logic.I.
Qed.

Lemma share_inst_post op v ad s r t : share_inst op v ad s = (r, t) -> sf_post s r t.
Proof.
  intros H. destruct r as [[]|]; cbn [sf_post]; auto.
  all: try (destruct op; cbn [share_inst] in H;
    unfold sh_mem_set_var, sh_mem_load, sh_mem_load_byte, sh_mem_load16, sh_mem_load32,
      sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32 in H;
    split_H H;
    repeat match goal with
           | E : context [match ?x with _ => _ end] |- _ =>
               destruct x; cbn beta iota in E; try discriminate E
           end;
    inversion H; fail).
  destruct (share_inst_sf op v ad s NONE t H eq_refl) as [E1 E2]. split; [apply sf_same, E1|exact E2].
Qed.

Ltac sf_cbn :=
  cbn [stack handler set_var set_vars set_locals unset_var set_store set_store_field set_memory
       set_ffi set_fp_regs set_code_buffer set_data_buffer set_code set_compile_oracle
       set_stack_max set_stack_size dec_clock set_clock set_fp_var set_termdep set_locals_size
       flush_state] in *.

Ltac sf_leaf Hok H :=
  lazymatch type of H with
  | alloc _ _ _ = _ => exact (alloc_post _ _ _ _ _ Hok H)
  | share_inst _ _ _ _ = _ => exact (share_inst_post _ _ _ _ _ _ H)
  | (_, _) = (_, _) =>
      injection H as <- <-; cbn [sf_post]; try exact Logic.I;
      repeat match goal with
             | E : inst _ _ = SOME _ |- _ => apply inst_sf in E; destruct E
             | E : mem_store _ _ _ = SOME _ |- _ => apply mem_store_sf in E; destruct E
             end;
      sf_cbn;
      first [ split; [apply sf_same; congruence|congruence]
            | intros _; match goal with E : jump_exc _ = SOME (_, (_, _)) |- _ =>
                exact (jump_exc_sf _ _ _ _ E) end ]
  end.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_sf_gc_consts" *)
Theorem evaluate_sf_gc_consts : forall (p : prog a) s s' res,
  evaluate (p, s) = (res, s') /\ gc_fun_const_ok (gc_fun s) ->
  match res with
  | NONE => LIST_REL sf_gc_consts (stack s) (stack s') /\ handler s' = handler s
  | SOME (Result _ _) => LIST_REL sf_gc_consts (stack s) (stack s') /\ handler s' = handler s
  | SOME (Exception _ _) =>
      handler s < LENGTH (stack s) ->
      LIST_REL sf_gc_consts (LASTN (handler s) (stack s)) (stack s') /\
      handler s' = get_above_handler s
  | SOME (Break _) => LIST_REL sf_gc_consts (stack s) (stack s') /\ handler s' = handler s
  | SOME (Continue _) => LIST_REL sf_gc_consts (stack s) (stack s') /\ handler s' = handler s
  | _ => True
  end.
Proof.
  intros p0 s0 s0' res0 [H0 Hok0]. change (sf_post s0 res0 s0').
  revert res0 s0' H0 Hok0.
  enough (G : forall x : prog a * state a c ffi_t, forall r t, evaluate x = (r, t) ->
            gc_fun_const_ok (gc_fun (snd x)) -> sf_post (snd x) r t)
    by (intros r t H Hok; exact (G (p0, s0) r t H Hok)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r t H Hok; cbn [snd] in *.
  rewrite evaluate_eqn in H. destruct p; cbn [evaluate_body] in H; rewrite ?fix_clock_evaluate in H.
  all: try solve [split_H H; sf_leaf Hok H].
  - (* MustTerminate *)
    destruct (termdep s =? 0) eqn:Et; [inversion H; exact Logic.I|].
    destruct (evaluate (p, set_termdep (termdep s - 1) (set_clock (MustTerminate_limit a) s)))
      as [r1 t1] eqn:E1.
    destruct (bool_decide (r1 = SOME TimeOut)); [inversion H; exact Logic.I|].
    injection H as <- <-.
    pose proof (IH (p, set_termdep (termdep s - 1) (set_clock (MustTerminate_limit a) s))
                  ltac:(wd_eval_lt) r1 t1 E1 Hok) as P.
    eapply sf_post_cong; [| | | |exact P]; reflexivity.
  - (* Call *)
    destruct (get_vars l s) as [xs|] eqn:Eg; [|inversion H; exact Logic.I].
    destruct (bad_dest_args o0 l) eqn:Ebd; [inversion H; exact Logic.I|].
    destruct (find_code o0 (add_ret_loc o xs) (code s) (state_stack_size s))
      as [[args1 [q ss]]|] eqn:Ef; [|inversion H; exact Logic.I].
    destruct o as [[n [names [rh [l1 l2]]]]|].
    2:{ destruct (⌜o1 = NONE⌝) eqn:Eh; [|inversion H; exact Logic.I].
        destruct (clock s =? 0) eqn:Ez; [inversion H; exact Logic.I|].
        destruct (evaluate (q, call_env args1 ss (dec_clock s))) as [r1 t1] eqn:E1.
        destruct (bad_fun_return r1) eqn:Eb; [inversion H; exact Logic.I|].
        injection H as <- <-.
        pose proof (IH (q, call_env args1 ss (dec_clock s)) ltac:(wd_eval_lt) r1 t1 E1 Hok) as P.
        eapply sf_post_cong; [| | | |exact P]; reflexivity. }
    destruct (⌜domain (FST names) = {}⌝ || negb (ALL_DISTINCT n)) eqn:Ec1;
      [inversion H; exact Logic.I|].
    destruct (cut_envs names (locals s)) as [envs|] eqn:Ece; [|inversion H; exact Logic.I].
    destruct (clock s =? 0) eqn:Ez; [inversion H; exact Logic.I|].
    rewrite ?fix_clock_evaluate in H.
    destruct (evaluate (q, call_env args1 ss (push_env envs o1 (dec_clock s)))) as [r1 t1] eqn:E1.
    pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
    assert (Hok1 : gc_fun_const_ok (gc_fun (call_env args1 ss (push_env envs o1 (dec_clock s))))).
    { unfold push_env; destruct o1 as [[? [? [? ?]]]|]; destruct (env_to_list _ _); exact Hok. }
    pose proof (IH (q, call_env args1 ss (push_env envs o1 (dec_clock s))) ltac:(wd_eval_lt)
                  r1 t1 E1 Hok1) as P1. cbn [SND snd] in P1.
    pose proof (evaluate_gc_fun_const_ok _ _ _ _ (conj E1 Hok1)) as Hokt1.
    destruct r1 as [[x ys|x y|k|k| | |f|]|]; try (inversion H; exact Logic.I).
    + (* Result *)
      destruct (negb (bool_decide (x = Loc l1 l2)) || negb (LENGTH ys =? LENGTH n)) eqn:Ec2;
        [inversion H; exact Logic.I|].
      destruct (pop_env t1) as [t2|] eqn:Ep; [|inversion H; exact Logic.I].
      destruct (⌜domain (locals t2) = domain (FST envs) UNION domain (SND envs)⌝) eqn:Ed;
        [|inversion H; exact Logic.I].
      assert (Hok2 : gc_fun_const_ok (gc_fun (set_vars n ys t2)))
        by (change (gc_fun (set_vars n ys t2)) with (gc_fun t2); rewrite (pop_env_gc_fun _ _ Ep);
            exact Hokt1).
      pose proof (IH (rh, set_vars n ys t2) ltac:(wd_eval_lt) r t H Hok2) as P2.
      destruct P1 as [HL1 Hh1].
      destruct (LIST_REL_call_Result (dec_clock s) t1 t1 t2 envs o1 (conj HL1 (conj Ep Hh1)))
        as [HL2 Hh2].
      exact (sf_post_trans s (set_vars n ys t2) r t HL2 Hh2 P2).
    + (* Exception *)
      destruct o1 as [[hn [hp [hl1 hl2]]]|].
      * destruct (negb (bool_decide (x = Loc hl1 hl2))) eqn:Ec2; [inversion H; exact Logic.I|].
        destruct (⌜domain (locals t1) = domain (FST envs) UNION domain (SND envs)⌝) eqn:Ed;
          [|inversion H; exact Logic.I].
        pose proof (call_env_push_env_dec_clock_handler_length s _ args1 ss envs hn hp hl1 hl2
                      eq_refl) as Hlt.
        destruct (P1 Hlt) as [HL Hh].
        pose proof (get_above_handler_call_env_push_env_dec_clock s _ t1 args1 ss envs hn hp hl1 hl2
                      (conj eq_refl Hh)) as Hh'.
        assert (HL' : LIST_REL sf_gc_consts (stack s) (stack t1)).
        { revert HL; unfold push_env; destruct (env_to_list _ _).
          cbn [SND snd stack handler call_env dec_clock set_stack_max set_locals_size set_locals set_clock
               set_permute set_stack set_handler].
          rewrite LASTN_LENGTH_CONS. auto. }
        assert (Hok2 : gc_fun_const_ok (gc_fun (set_var hn y t1))) by exact Hokt1.
        pose proof (IH (hp, set_var hn y t1) ltac:(wd_eval_lt) r t H Hok2) as P2.
        exact (sf_post_trans s (set_var hn y t1) r t HL' Hh' P2).
      * injection H as <- <-. cbn [sf_post]. intros Hlt.
        assert (Eh : handler (call_env args1 ss (push_env envs (NONE : option (N * (prog a * (N * N))))
                                                  (dec_clock s))) = handler s)
          by (unfold push_env; destruct (env_to_list _ _); reflexivity).
        assert (Hlt' : handler (call_env args1 ss (push_env envs (NONE : option (N * (prog a * (N * N))))
                                                    (dec_clock s))) <
                       LENGTH (stack (call_env args1 ss (push_env envs (NONE : option (N * (prog a * (N * N))))
                                                           (dec_clock s))))).
        { rewrite Eh. unfold push_env; destruct (env_to_list _ _).
          cbn [stack call_env dec_clock set_stack_max set_locals_size set_locals set_clock
               set_permute set_stack LENGTH]. lia. }
        destruct (P1 Hlt') as [HL Hh]. rewrite Eh in HL. rewrite LASTN_push_NONE in HL by exact Hlt.
        split; [exact HL|]. rewrite Hh. apply get_above_handler_push_NONE, Hlt.
  - (* Seq *)
    destruct (evaluate (p1, s)) as [r1 s1] eqn:E1.
    pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
    pose proof (IH (p1, s) ltac:(wd_eval_lt) r1 s1 E1 Hok) as P1.
    destruct (bool_decide (r1 = NONE)) eqn:En.
    + apply bool_decide_spec in En; subst r1.
      pose proof (evaluate_gc_fun_const_ok _ _ _ _ (conj E1 Hok)) as Hok1.
      pose proof (IH (p2, s1) ltac:(wd_eval_lt) r t H Hok1) as P2.
      destruct P1 as [HL Hh]. exact (sf_post_trans s s1 r t HL Hh P2).
    + injection H as <- <-. exact P1.
  - (* If *)
    split_H H; try (inversion H; exact Logic.I);
    match type of H with
    | evaluate (?q, s) = _ => exact (IH (q, s) ltac:(wd_eval_lt) r t H Hok)
    end.
  - (* Loop *)
    destruct (cut_state (s1, LN) s) as [s'|] eqn:Ec; [|inversion H; exact Logic.I].
    rewrite ?fix_clock_evaluate in H.
    pose proof (cut_state_clock _ _ _ Ec) as Hcs.
    apply cut_state_const in Ec as Ec'. destruct Ec' as [lc ->].
    destruct (evaluate (p, set_locals lc s)) as [r1 t1] eqn:E1.
    pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
    pose proof (IH (p, set_locals lc s) ltac:(wd_eval_lt) r1 t1 E1 Hok) as P1.
    pose proof (evaluate_gc_fun_const_ok _ _ _ _ (conj E1 Hok)) as Hok1.
    destruct (cont_loop r1) eqn:Ecl.
    + destruct (clock t1 =? 0) eqn:Ez; [inversion H; exact Logic.I|].
      unfold STOP in H.
      pose proof (IH (Loop s1 p s2, dec_clock t1) ltac:(wd_eval_lt) r t H Hok1) as P2.
      destruct r1 as [[| | |k| | | |]|]; cbn in Ecl; try discriminate Ecl;
        destruct P1 as [HL Hh]; exact (sf_post_trans s (dec_clock t1) r t HL Hh P2).
    + destruct (bool_decide (r1 = SOME (Break 0))) eqn:Eb.
      * apply bool_decide_spec in Eb; subst r1.
        destruct (cut_state (s2, LN) t1) as [t2|] eqn:Ec2; [|inversion H; exact Logic.I].
        injection H as <- <-. apply cut_state_const in Ec2. destruct Ec2 as [l2 ->].
        exact P1.
      * injection H as <- <-. apply sf_post_exit_loop.
        eapply sf_post_cong; [| | | |exact P1]; reflexivity.
Qed.
End SfGcConsts.

(** ** [evaluate_const_fp_loop] *)

Section ConstFp.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.

(** Galette-only: [cs] holds constants of [s]. *)
Definition cs_rel (cs : num_map (word a)) s : Prop :=
  forall v w, lookup v cs = SOME w -> get_var v s = SOME (Word w).

Lemma cs_rel_LN s : cs_rel LN s.
Proof. intros v w H; discriminate H. Qed.

Lemma cs_rel_locals cs s t : locals t = locals s -> cs_rel cs s -> cs_rel cs t.
Proof. intros E H v w Hl; unfold get_var; rewrite E; apply H, Hl. Qed.

Lemma get_var_set_fp_var' v x y s : get_var v (set_fp_var x y s) = get_var v s.
Proof. reflexivity. Qed.
Lemma get_var_set_memory v m s : get_var v (set_memory m s) = get_var v s.
Proof. reflexivity. Qed.
Lemma get_var_unset_var v x s : get_var v (unset_var x s) = if decide (v = x) then NONE else get_var v s.
Proof. unfold get_var, unset_var; cbn [locals set_locals]. apply lookup_delete. Qed.

Ltac cs_finish Hcs Hl :=
  repeat first
    [ rewrite get_var_set_var_thm | rewrite get_var_set_fp_var' | rewrite get_var_set_memory
    | rewrite get_var_unset_var
    | rewrite lookup_delete in Hl | rewrite lookup_insert in Hl ];
  repeat match goal with
         | |- context [decide ?P] => destruct (decide P)
         | Hl : context [decide ?P] |- _ => destruct (decide P)
         end;
  subst; try congruence; try discriminate Hl;
  first [ apply Hcs, Hl | injection Hl as <-; reflexivity ].

Lemma cs_rel_inst i cs s t : cs_rel cs s -> inst i s = SOME t -> cs_rel (const_fp_inst_cs i cs) t.
Proof.
  intros Hcs H v w Hl.
  destruct i as [|r w0|ar|m r [ad w0]|f];
    [|cbn [inst const_fp_inst_cs] in H, Hl|destruct ar|destruct m|destruct f];
    cbn [inst const_fp_inst_cs] in H, Hl; unfold assign in H; split_H H; try discriminate H;
    injection H as <-;
    repeat match goal with E : mem_store _ _ _ = SOME _ |- _ =>
             rewrite (get_var_mem_store_thm _ _ _ _ _ E); clear E end;
    try (cbn zeta in H; destruct (word_add_carry _ _ _) in H);
    try (destruct (dimindex a =? 64) in Hl);
    cs_finish Hcs Hl.
Qed.

(** HOL's free variable [cs] is quantified first; its unused [rest] is kept. *)
(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_drop_consts_1" *)
Theorem evaluate_drop_consts_1 : forall (cs : num_map (word a)) vs (rest : prog a) s,
  (forall v w, lookup v cs = SOME w -> get_var v s = SOME (Word w)) ->
  evaluate (drop_consts cs vs, s) = (NONE, s).
Proof.
  intros cs vs rest s Hcs. induction vs as [|n ns IH]; cbn [drop_consts]; [apply evaluate_Skip_eq|].
  destruct (lookup n cs) as [w|] eqn:E; [|exact IH].
  rewrite evaluate_SmartSeq, evaluate_Seq_eq, IH, bd_true by reflexivity.
  rewrite (evaluate_eqn (Assign _ _) s); cbn [evaluate_body word_exp]. f_equal.
  unfold set_var. pose proof (Hcs _ _ E) as G; unfold get_var in G.
  rewrite (insert_unchanged _ _ _ G). destruct s; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_drop_consts" *)
Theorem evaluate_drop_consts : forall (cs : num_map (word a)) vs (p : prog a) s,
  (forall v w, lookup v cs = SOME w -> get_var v s = SOME (Word w)) ->
  evaluate (SmartSeq (drop_consts cs vs) p, s) = evaluate (p, s).
Proof.
  intros cs vs p s Hcs. rewrite evaluate_SmartSeq, evaluate_Seq_eq.
  rewrite (evaluate_drop_consts_1 cs vs p s Hcs), bd_true by reflexivity. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "lookup_FOLDR_delete" *)
Theorem lookup_FOLDR_delete : forall (l : list N) (m : num_map (word a)) v w,
  lookup v (FOLDR delete m l) = SOME w -> lookup v m = SOME w /\ ~ MEM v l.
Proof.
  induction l as [|x l IH]; intros m v w H; cbn [FOLDR List.fold_right] in H.
  - split; [exact H|intros F; discriminate F].
  - rewrite lookup_delete in H. destruct (decide (v = x)); [discriminate|].
    destruct (IH _ _ _ H) as [H1 H2]. split; [exact H1|].
    intros F; cbn [MEM] in F; unfold is_true in F. apply Bool.orb_true_iff in F as [F|F].
    + apply bool_decide_spec in F; contradiction.
    + apply H2, F.
Qed.

(** HOL's free variable [v] is quantified first. *)
(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "get_var_set_vars_ignore" *)
Theorem get_var_set_vars_ignore : forall v xs (l : list (word_loc a)) (m : state a c ffi_t),
  ~ MEM v xs -> get_var v (set_vars xs l m) = get_var v m.
Proof.
  intros v; induction xs as [|x xs IH]; intros l m H; [reflexivity|].
  destruct l as [|y l]; [reflexivity|].
  unfold set_vars, get_var in *; cbn [alist_insert locals set_locals] in *.
  rewrite lookup_insert. destruct (decide (v = x)) as [->|Hne].
  - exfalso; apply H; cbn [MEM]; unfold is_true; rewrite bd_true by reflexivity; reflexivity.
  - apply IH. intros F; apply H; cbn [MEM]; unfold is_true in *; rewrite F, Bool.orb_true_r; reflexivity.
Qed.

Lemma Call_NONE_not_NONE dest args h s :
  fst (evaluate (@Call a NONE dest args h, s)) <> NONE.
Proof.
  rewrite evaluate_eqn; cbn [evaluate_body].
  repeat match goal with
         | |- context [match ?x with _ => _ end] =>
             let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
         end;
  cbn [fst bad_fun_return] in *; try congruence.
  all: match goal with o : option (result a) |- _ => destruct o as [[]|] end;
    cbn [bad_fun_return] in *; congruence.
Qed.

Lemma cut_env_lookup (names : cutsets) (l env : num_map (word_loc a)) v :
  cut_env names l = SOME env -> lookup v (all_names names) <> NONE -> lookup v env = lookup v l.
Proof.
  destruct names as [n0 n1]. unfold cut_env, cut_envs, cut_names, all_names; cbn [FST SND fst snd].
  destruct (classical_dec (domain n0 SUBSET domain l)); [|discriminate].
  destruct (classical_dec (domain n1 SUBSET domain l)); [|discriminate].
  intros H Hn; injection H as <-. cbn beta iota in Hn.
  rewrite lookup_union in Hn. rewrite lookup_union, !lookup_inter.
  destruct (lookup v n1), (lookup v n0), (lookup v l); try reflexivity; congruence.
Qed.

Lemma get_var_set_ffi v f s : get_var v (set_ffi f s) = get_var v s.
Proof. reflexivity. Qed.

Lemma evaluate_Move_eq' pri moves s :
  evaluate (@Move a pri moves, s) =
  if ALL_DISTINCT (MAP FST moves) then
    match get_vars (MAP SND moves) s with
    | NONE => (SOME Error, s)
    | SOME vs => (NONE, set_vars (MAP FST moves) vs s)
    end
  else (SOME Error, s).
Proof. rewrite (evaluate_eqn (Move pri moves) s); reflexivity. Qed.

Ltac err_case H := split; [exact H|intros ->; inversion H].

(** Locals unchanged: the [cs] invariant carries over. *)
Ltac cs_same Hcs :=
  eapply cs_rel_locals; [|exact Hcs];
  first [ reflexivity
        | match goal with E : mem_store _ _ _ = SOME ?t |- locals ?t = _ =>
            exact (proj1 (mem_store_const _ _ _ _ E)) end ].

Ltac default_case H Hc Hcs :=
  injection Hc as <- <-; split; [exact H|]; intros ->;
  rewrite evaluate_eqn in H; cbn [evaluate_body] in H; split_H H; inversion H; subst;
  cs_same Hcs.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_const_fp_loop" *)
Theorem evaluate_const_fp_loop : forall (p : prog a) cs p' cs' s res s',
  evaluate (p, s) = (res, s') /\ const_fp_loop p cs = (p', cs') /\ gc_fun_const_ok (gc_fun s) /\
  (forall v w, lookup v cs = SOME w -> get_var v s = SOME (Word w)) ->
  evaluate (p', s) = (res, s') /\
  (res = NONE -> (forall v w, lookup v cs' = SOME w -> get_var v s' = SOME (Word w))).
Proof.
  intros p; induction p as [ |pri moves|i|v e|v nm|v e|e v|q IHq|ret dest args h IHret IHh
                           |q1 q2 IH1 IH2|cmp lhs rhs q1 q2 IH1 IH2|names q exit_names IHq
                           |n names|t1 t2 ad off ws|n|n ns|n|n| |b v w|v l1|r1 r2 r3 r4 names
                           |r1 r2|r1 r2|ffi r1 r2 r3 r4 names|op v e]
    using prog_nested_ind;
    intros cs p' cs' st res st' [H [Hc [Hok Hcs]]]; cbn [const_fp_loop] in Hc;
    change (cs_rel cs st) in Hcs; change (_ -> cs_rel _ _) with (res = NONE -> cs_rel cs' st').
  - (* Skip *) default_case H Hc Hcs.
  - (* Move *)
    apply pair_equal_spec in Hc; destruct Hc as [<- <-]. split; [exact H|]. intros ->.
    rewrite evaluate_Move_eq' in H. destruct (ALL_DISTINCT (MAP FST moves)) eqn:D; [|inversion H].
    destruct (get_vars (MAP SND moves) st) as [l|] eqn:G; [|inversion H].
    injection H as <-. intros v w Hl.
    rewrite (get_var_move_thm st _ moves l v (conj G eq_refl)).
    rewrite (lookup_const_fp_move_cs v moves cs D) in Hl.
    destruct (ALOOKUP moves v); apply Hcs, Hl.
  - (* Inst *)
    apply pair_equal_spec in Hc; destruct Hc as [<- <-]. split; [exact H|]. intros ->.
    rewrite evaluate_eqn in H; cbn [evaluate_body] in H.
    destruct (inst i st) as [t|] eqn:E; inversion H; subst. exact (cs_rel_inst _ _ _ _ Hcs E).
  - (* Assign *)
    cbn zeta in Hc. pose proof (const_fp_exp_word_exp e cs st Hcs) as We.
    rewrite evaluate_eqn in H; cbn [evaluate_body] in H.
    destruct (const_fp_exp e cs) eqn:Ee; apply pair_equal_spec in Hc; destruct Hc as [<- <-];
      (split; [rewrite evaluate_eqn; cbn [evaluate_body]; rewrite We; exact H|]); intros ->;
      destruct (word_exp st e) as [x|] eqn:Ew; inversion H; subst; intros vv ww Hl.
    1:{ cbn [word_exp] in We. injection We as <-. cs_finish Hcs Hl. }
    all: cs_finish Hcs Hl.
  - (* Get *)
    apply pair_equal_spec in Hc; destruct Hc as [<- <-]. split; [exact H|]. intros ->.
    rewrite evaluate_eqn in H; cbn [evaluate_body] in H.
    destruct (get_store nm st); inversion H; subst. intros vv ww Hl. cs_finish Hcs Hl.
  - (* Set *) default_case H Hc Hcs.
  - (* Store *)
    apply pair_equal_spec in Hc; destruct Hc as [<- <-]. rewrite evaluate_eqn in H |- *; cbn [evaluate_body] in H |- *.
    rewrite (const_fp_exp_word_exp e cs st Hcs). split; [exact H|]. intros ->.
    split_H H; inversion H; subst. cs_same Hcs.
  - (* MustTerminate *)
    destruct (const_fp_loop q cs) as [q' cq] eqn:Eq. apply pair_equal_spec in Hc; destruct Hc as [<- <-].
    rewrite evaluate_eqn in H |- *; cbn [evaluate_body] in H |- *.
    destruct (termdep st =? 0); [err_case H|].
    destruct (evaluate (q, set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) st)))
      as [r1 t1] eqn:E1.
    assert (Hcs1 : cs_rel cs (set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) st)))
      by (cs_same Hcs).
    destruct (IHq cs q' cq _ r1 t1 (conj E1 (conj Eq (conj Hok Hcs1)))) as [Ev Hn].
    rewrite Ev. destruct (bool_decide (r1 = SOME TimeOut)); [err_case H|].
    split; [exact H|]. intros ->. injection H as -> <-.
    eapply cs_rel_locals; [|exact (Hn eq_refl)]. reflexivity.
  - (* Call *)
    destruct ret as [[n [names [rh [l1 l2]]]]|].
    2:{ apply pair_equal_spec in Hc; destruct Hc as [<- <-]. split; [rewrite evaluate_drop_consts by exact Hcs; exact H|].
        intros ->. exfalso. apply (Call_NONE_not_NONE dest args h st). rewrite H. reflexivity. }
    cbn beta iota in IHret.
    destruct h as [hh|].
    { apply pair_equal_spec in Hc; destruct Hc as [<- <-]. split; [rewrite evaluate_drop_consts by exact Hcs; exact H|].
      intros _; apply cs_rel_LN. }
    cbn zeta in Hc.
    destruct (const_fp_loop rh (delete_all n (filter_v is_gc_const (inter cs (all_names names)))))
      as [rh' crh] eqn:Erh.
    apply pair_equal_spec in Hc; destruct Hc as [<- <-]. rewrite evaluate_drop_consts by exact Hcs.
    rewrite evaluate_eqn in H |- *; cbn [evaluate_body add_ret_loc] in H |- *.
    destruct (get_vars args st) as [xs|] eqn:Eg; [|err_case H].
    destruct (bad_dest_args dest args) eqn:Ebd; [err_case H|].
    destruct (find_code dest (Loc l1 l2 :: xs) (code st) (state_stack_size st))
      as [[args1 [q ss]]|] eqn:Ef; [|err_case H].
    destruct (⌜domain (FST names) = {}⌝ || negb (ALL_DISTINCT n)) eqn:Ec1; [err_case H|].
    destruct (cut_envs names (locals st)) as [envs|] eqn:Ece; [|err_case H].
    destruct (clock st =? 0) eqn:Ez; [err_case H|].
    rewrite ?fix_clock_evaluate in H |- *.
    destruct (evaluate (q, call_env args1 ss (push_env envs NONE (dec_clock st)))) as [r1 t1] eqn:E1.
    assert (Hok1 : gc_fun_const_ok (gc_fun (call_env args1 ss (push_env envs
                     (NONE : option (N * (prog a * (N * N)))) (dec_clock st))))).
    { unfold push_env; destruct (env_to_list _ _); exact Hok. }
    pose proof (evaluate_sf_gc_consts _ _ _ _ (conj E1 Hok1)) as Hsf.
    pose proof (evaluate_gc_fun_const_ok _ _ _ _ (conj E1 Hok1)) as Hokt1.
    destruct r1 as [[x ys|x y|k|k| | |f|]|]; try (err_case H).
    destruct (negb (bool_decide (x = Loc l1 l2)) || negb (LENGTH ys =? LENGTH n)) eqn:Ec2;
      [err_case H|].
    destruct (pop_env t1) as [t2|] eqn:Ep; [|err_case H].
    destruct (⌜domain (locals t2) = domain (FST envs) UNION domain (SND envs)⌝) eqn:Ed;
      [|err_case H].
    assert (Hok2 : gc_fun_const_ok (gc_fun (set_vars n ys t2)))
      by (change (gc_fun (set_vars n ys t2)) with (gc_fun t2); rewrite (pop_env_gc_fun _ _ Ep);
          exact Hokt1).
    assert (Hcs2 : cs_rel (delete_all n (filter_v is_gc_const (inter cs (all_names names))))
                     (set_vars n ys t2)).
    { intros v w Hl. unfold delete_all in Hl. apply lookup_FOLDR_delete in Hl as [Hl Hnm].
      pose proof (lookup_filter_v_SOME _ _ _ _ Hl) as Hg.
      apply lookup_filter_v_SOME_imp in Hl.
      destruct (proj1 (proj1 (lookup_inter_EQ v cs (all_names names) w)) Hl) as [Hl' Hnn].
      rewrite get_var_set_vars_ignore by exact Hnm.
      destruct Hsf as [HL _].
      exact (push_env_pop_env_locals_thm (dec_clock st) _ t1 t2 envs names NONE
               (conj Ece (conj eq_refl (conj HL Ep))) v (Word w)
               (conj (Hcs v w Hl') (conj Hg Hnn))). }
    exact (IHret _ rh' crh (set_vars n ys t2) res st' (conj H (conj Erh (conj Hok2 Hcs2)))).
  - (* Seq *)
    destruct (const_fp_loop q1 cs) as [p1' cs1] eqn:E1c.
    destruct (const_fp_loop q2 cs1) as [p2' cs2] eqn:E2c. apply pair_equal_spec in Hc; destruct Hc as [<- <-].
    rewrite evaluate_Seq_eq in H |- *. destruct (evaluate (q1, st)) as [r1 s1] eqn:E1.
    destruct (IH1 cs p1' cs1 st r1 s1 (conj E1 (conj E1c (conj Hok Hcs)))) as [Ev1 Hn1].
    rewrite Ev1. destruct (bool_decide (r1 = NONE)) eqn:En.
    + apply bool_decide_spec in En; subst r1.
      pose proof (evaluate_gc_fun_const_ok _ _ _ _ (conj E1 Hok)) as Hok1.
      exact (IH2 cs1 p2' cs2 s1 res st' (conj H (conj E2c (conj Hok1 (Hn1 eq_refl))))).
    + injection H as <- <-. split; [reflexivity|]. intros ->.
      rewrite bd_true in En by reflexivity; discriminate.
  - (* If *)
    destruct (lookup lhs cs) as [clhs|] eqn:El; [destruct (get_var_imm_cs rhs cs) as [crhs|] eqn:Er|].
    + rewrite evaluate_eqn in H; cbn [evaluate_body] in H.
      rewrite (Hcs _ _ El) in H.
      rewrite (get_var_imm_cs_imp_get_var_imm rhs crhs st cs (conj Hcs Er)) in H.
      rewrite Galette.cakeml.compiler.backend.semantics.wordProps.code.word_cmp_Word_Word in H.
      destruct (asm.word_cmp cmp clhs crhs) eqn:Ec.
      * exact (IH1 cs p' cs' st res st' (conj H (conj Hc (conj Hok Hcs)))).
      * exact (IH2 cs p' cs' st res st' (conj H (conj Hc (conj Hok Hcs)))).
    + destruct (const_fp_loop q1 cs) as [p1' c1] eqn:E1c.
      destruct (const_fp_loop q2 cs) as [p2' c2] eqn:E2c. apply pair_equal_spec in Hc; destruct Hc as [<- <-].
      rewrite evaluate_eqn in H |- *; cbn [evaluate_body] in H |- *.
      split_H H; try (err_case H).
      * destruct (IH1 cs p1' c1 st res st' (conj H (conj E1c (conj Hok Hcs)))) as [Ev Hn].
        rewrite Ev. split; [reflexivity|]. intros Hr vv ww Hl.
        apply lookup_inter_eq_some in Hl as [Hl _]. exact (Hn Hr vv ww Hl).
      * destruct (IH2 cs p2' c2 st res st' (conj H (conj E2c (conj Hok Hcs)))) as [Ev Hn].
        rewrite Ev. split; [reflexivity|]. intros Hr vv ww Hl.
        apply lookup_inter_eq_some in Hl as [_ Hl]. exact (Hn Hr vv ww Hl).
    + destruct (const_fp_loop q1 cs) as [p1' c1] eqn:E1c.
      destruct (const_fp_loop q2 cs) as [p2' c2] eqn:E2c. apply pair_equal_spec in Hc; destruct Hc as [<- <-].
      rewrite evaluate_eqn in H |- *; cbn [evaluate_body] in H |- *.
      split_H H; try (err_case H).
      * destruct (IH1 cs p1' c1 st res st' (conj H (conj E1c (conj Hok Hcs)))) as [Ev Hn].
        rewrite Ev. split; [reflexivity|]. intros Hr vv ww Hl.
        apply lookup_inter_eq_some in Hl as [Hl _]. exact (Hn Hr vv ww Hl).
      * destruct (IH2 cs p2' c2 st res st' (conj H (conj E2c (conj Hok Hcs)))) as [Ev Hn].
        rewrite Ev. split; [reflexivity|]. intros Hr vv ww Hl.
        apply lookup_inter_eq_some in Hl as [_ Hl]. exact (Hn Hr vv ww Hl).
  - (* Loop *)
    apply pair_equal_spec in Hc; destruct Hc as [<- <-]. split; [|intros _; apply cs_rel_LN].
    rewrite (evaluate_Loop_body_cong_gc gc_fun_const_ok st names q _ exit_names); [exact H| |exact Hok].
    intros v Hv. destruct (const_fp_loop q LN) as [b' cb] eqn:Eb; cbn [FST fst].
    destruct (evaluate (q, v)) as [rr vv] eqn:Ev.
    exact (proj1 (IHq LN b' cb v rr vv (conj Ev (conj Eb (conj Hv (cs_rel_LN v)))))).
  - (* Alloc *)
    apply pair_equal_spec in Hc; destruct Hc as [<- <-]. split; [rewrite evaluate_drop_consts by exact Hcs; exact H|]. intros ->.
    rewrite evaluate_eqn in H; cbn [evaluate_body] in H.
    destruct (get_var n st) as [[w|]|]; try (inversion H; fail).
    unfold alloc in H.
    destruct (cut_envs names (locals st)) as [envs|] eqn:Ece; [|inversion H].
    destruct (gc _) as [s1|] eqn:Eg; [|inversion H].
    destruct (pop_env s1) as [s2|] eqn:Ep; [|inversion H].
    destruct (get_store stackLang.AllocSize s2); [|inversion H].
    destruct (has_space _ s2) as [[]|]; inversion H; subst.
    intros vv ww Hl. pose proof (lookup_filter_v_SOME _ _ _ _ Hl) as Hg.
    apply lookup_filter_v_SOME_imp in Hl.
    destruct (proj1 (proj1 (lookup_inter_EQ vv cs (all_names names) ww)) Hl) as [Hl' Hnn].
    assert (Hok' : gc_fun_const_ok (gc_fun (push_env envs (NONE : option (N * (prog a * (N * N))))
                                              (set_store stackLang.AllocSize (Word w) st)))).
    { unfold push_env; destruct (env_to_list _ _); exact Hok. }
    pose proof (gc_sf_gc_consts _ _ (conj Hok' Eg)) as HL.
    exact (push_env_pop_env_locals_thm (set_store stackLang.AllocSize (Word w) st) _ s1 st' envs names NONE
             (conj Ece (conj eq_refl (conj HL Ep))) vv (Word ww)
             (conj (Hcs vv ww Hl') (conj Hg Hnn))).
  - (* StoreConsts *)
    apply pair_equal_spec in Hc; destruct Hc as [<- <-]. split; [exact H|]. intros ->.
    rewrite evaluate_eqn in H; cbn [evaluate_body] in H. split_H H; inversion H; subst.
    intros vv ww Hl. cbn zeta. cs_finish Hcs Hl.
  - (* Raise *) default_case H Hc Hcs.
  - (* Return *) default_case H Hc Hcs.
  - (* Break *) default_case H Hc Hcs.
  - (* Continue *) default_case H Hc Hcs.
  - (* Tick *) default_case H Hc Hcs.
  - (* OpCurrHeap *)
    apply pair_equal_spec in Hc; destruct Hc as [<- <-]. split; [exact H|]. intros ->.
    rewrite evaluate_eqn in H; cbn [evaluate_body] in H. split_H H; inversion H; subst.
    intros vv ww Hl. cs_finish Hcs Hl.
  - (* LocValue *)
    apply pair_equal_spec in Hc; destruct Hc as [<- <-]. split; [exact H|]. intros ->.
    rewrite evaluate_eqn in H; cbn [evaluate_body] in H. split_H H; inversion H; subst.
    intros vv ww Hl. cs_finish Hcs Hl.
  - (* Install *)
    apply pair_equal_spec in Hc; destruct Hc as [<- <-]. split; [rewrite evaluate_drop_consts by exact Hcs; exact H|]. intros ->.
    rewrite evaluate_eqn in H; cbn [evaluate_body] in H. split_H H; inversion H; subst.
    intros vv ww Hl. rewrite lookup_delete in Hl. destruct (decide (vv = r1)); [discriminate|].
    apply lookup_filter_v_SOME_imp in Hl.
    destruct (proj1 (proj1 (lookup_inter_EQ vv cs (all_names names) ww)) Hl) as [Hl' Hnn].
    unfold get_var; cbn [locals set_stack_size set_stack_max set_compile_oracle set_fp_regs
      set_locals set_code set_data_buffer set_code_buffer].
    rewrite lookup_insert. destruct (decide (vv = r1)); [congruence|].
    match goal with E : cut_env names (locals st) = SOME _ |- _ => rewrite (cut_env_lookup _ _ _ _ E Hnn) end.
    apply Hcs, Hl'.
  - (* CodeBufferWrite *) default_case H Hc Hcs.
  - (* DataBufferWrite *) default_case H Hc Hcs.
  - (* FFI *)
    apply pair_equal_spec in Hc; destruct Hc as [<- <-]. split; [rewrite evaluate_drop_consts by exact Hcs; exact H|]. intros ->.
    rewrite evaluate_eqn in H; cbn [evaluate_body] in H. split_H H; inversion H; subst.
    intros vv ww Hl.
    destruct (proj1 (proj1 (lookup_inter_EQ vv cs (all_names names) ww)) Hl) as [Hl' Hnn].
    unfold get_var; cbn [locals set_ffi set_fp_regs set_locals set_memory].
    match goal with E : cut_env names (locals st) = SOME _ |- _ => rewrite (cut_env_lookup _ _ _ _ E Hnn) end.
    apply Hcs, Hl'.
  - (* ShareInst *)
    destruct op; cbn [const_fp_loop] in Hc; apply pair_equal_spec in Hc; destruct Hc as [<- <-];
      rewrite evaluate_eqn in H |- *; cbn [evaluate_body] in H |- *;
      rewrite (const_fp_exp_word_exp e cs st Hcs); (split; [exact H|]); intros ->;
      split_H H; try (inversion H; fail);
      cbn [share_inst] in H;
      unfold sh_mem_set_var, sh_mem_load, sh_mem_load_byte, sh_mem_load16, sh_mem_load32,
        sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32 in H;
      split_H H;
      repeat match goal with
             | E : context [match ?x with _ => _ end] |- _ =>
                 destruct x; cbn beta iota in E; try discriminate E
             end;
      inversion H; subst; intros vv ww Hl;
      repeat match goal with E : mem_store _ _ _ = SOME _ |- _ =>
               rewrite (get_var_mem_store_thm _ _ _ _ _ E); clear E end;
      rewrite ?get_var_set_ffi; cs_finish Hcs Hl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_const_fp" *)
Theorem evaluate_const_fp : forall (p : prog a) s,
  gc_fun_const_ok (gc_fun s) -> evaluate (const_fp p, s) = evaluate (p, s).
Proof.
  intros p s Hok. unfold const_fp. destruct (const_fp_loop p LN) as [p' cs'] eqn:E. cbn [FST fst].
  destruct (evaluate (p, s)) as [r t] eqn:Ev.
  exact (proj1 (evaluate_const_fp_loop p LN p' cs' s r t (conj Ev (conj E (conj Hok (cs_rel_LN s)))))).
Qed.

End ConstFp.

(** ** The duplicate-if pass *)

Section DupIf.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.

Lemma seq_assoc_eq (p1 p2 p3 : prog a) s :
  evaluate (Seq p1 (Seq p2 p3), s) = evaluate (Seq (Seq p1 p2) p3, s).
Proof.
  rewrite !evaluate_Seq_eq. destruct (evaluate (p1, s)) as [r t].
  destruct (bool_decide (r = NONE)) eqn:E; [rewrite evaluate_Seq_eq; reflexivity|rewrite E; reflexivity].
Qed.

Lemma seq_If_eq cmp r ri (b1 b2 x : prog a) s :
  evaluate (Seq (If cmp r ri b1 b2) x, s) = evaluate (If cmp r ri (Seq b1 x) (Seq b2 x), s).
Proof.
  rewrite evaluate_Seq_eq, !(evaluate_eqn (If _ _ _ _ _) s); cbn [evaluate_body].
  destruct (get_var r s); [|reflexivity]. destruct (get_var_imm ri s); [|reflexivity].
  destruct (wordSem.word_cmp cmp _ _) as [[]|]; [rewrite evaluate_Seq_eq; reflexivity..|].
  rewrite bd_false by discriminate. reflexivity.
Qed.

Lemma gc_fun_call_push s (args : list (word_loc a)) ss envs (h : option (N * (prog a * (N * N)))) :
  gc_fun (call_env args ss (push_env envs h (dec_clock s))) = gc_fun s.
Proof. unfold push_env; destruct h as [[? [? [? ?]]]|]; destruct (env_to_list _ _); reflexivity. Qed.

(** HOL's free variable [p3] is quantified first. *)
(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_try_if_hoist2" *)
Theorem evaluate_try_if_hoist2 : forall p3 N0 (p1 interm dummy p2 : prog a) s,
  try_if_hoist2 N0 p1 interm dummy p2 = SOME p3 ->
  gc_fun_const_ok (gc_fun s) ->
  evaluate (p3, s) = evaluate (Seq (Seq p1 interm) p2, s).
Proof.
  intros p3 N0 p1; revert N0.
  induction p1 as [ | | | | | | |q IHq|ret dest args h IHret IHh|q1 q2 IH1 IH2
                   |cmp lhs rhs q1 q2 IH1 IH2|names q exit_names IHq | | | | | | | | | | | | | |]
    using prog_nested_ind; intros N0 interm dummy p2 st H Hok; cbn [try_if_hoist2] in H;
    destruct (N0 =? 0); try discriminate H.
  - (* Seq *)
    destruct (dest_If q2) as [[cmp [lhs [rhs [br1 br2]]]]|] eqn:Ed.
    + cbn zeta in H. destruct (dest_Raise_num _ =? 0); [discriminate|].
      destruct (negb (_ + _ =? 3)); [discriminate|].
      injection H as <-. apply dest_If_thm in Ed; subst q2.
      rewrite <- (seq_assoc_eq (Seq q1 _) interm p2), <- (seq_assoc_eq q1 _ (Seq interm p2)).
      rewrite !(evaluate_Seq_eq q1). destruct (evaluate (q1, st)) as [r1 s1] eqn:E1.
      destruct (bool_decide (r1 = NONE)); [|reflexivity].
      rewrite evaluate_const_fp by exact (evaluate_gc_fun_const_ok _ _ _ _ (conj E1 Hok)).
      rewrite seq_If_eq. apply eq_eval_If; intros v; symmetry; apply seq_assoc_eq.
    + destruct (is_simple q2) eqn:Es; [|discriminate].
      rewrite (IH1 _ _ _ _ _ H Hok).
      transitivity (evaluate (Seq q1 (Seq q2 (Seq interm p2)), st)).
      * rewrite <- seq_assoc_eq. apply eq_eval_Seq; [intros v; reflexivity|].
        intros v; symmetry; apply seq_assoc_eq.
      * rewrite <- (seq_assoc_eq (Seq q1 q2) interm p2), <- seq_assoc_eq. reflexivity.
  - (* If *)
    cbn zeta in H. destruct (dest_Raise_num _ =? 0); [discriminate|].
    destruct (negb (_ + _ =? 3)); [discriminate|].
    injection H as <-. rewrite evaluate_const_fp by exact Hok.
    rewrite <- seq_assoc_eq, seq_If_eq. apply eq_eval_If; intros v; symmetry; apply seq_assoc_eq.
Qed.

(** HOL's free variables [p1], [p2], [p3], [s] are quantified. *)
(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_try_if_hoist1" *)
Theorem evaluate_try_if_hoist1 : forall (p1 p2 p3 : prog a) s,
  try_if_hoist1 p1 p2 = SOME p3 ->
  gc_fun_const_ok (gc_fun s) ->
  evaluate (p3, s) = evaluate (Seq p1 p2, s).
Proof.
  intros p1 p2 p3 s H Hok. unfold try_if_hoist1 in H.
  destruct (dest_If p2) as [[cmp [lhs [rhs [? ?]]]]|]; [|discriminate]. cbn zeta in H.
  rewrite (evaluate_try_if_hoist2 _ _ _ _ _ _ _ H Hok).
  rewrite (evaluate_Seq_eq (Seq p1 Skip) p2), evaluate_Seq_Skip, evaluate_Seq_eq. reflexivity.
Qed.

(** Galette-only: semantic equality on states with a [gc_fun_const_ok]
    collector. *)
Definition eq_eval_gc (p q : prog a) : Prop :=
  forall s : state a c ffi_t, gc_fun_const_ok (gc_fun s) -> evaluate (p, s) = evaluate (q, s).

Ltac gc_ok :=
  repeat first
    [ progress (rewrite ?gc_fun_call_push)
    | progress (change (gc_fun (set_vars ?x ?y ?z)) with (gc_fun z))
    | progress (change (gc_fun (set_var ?x ?y ?z)) with (gc_fun z))
    | match goal with
      | E : pop_env ?x = SOME ?y |- context [gc_fun ?y] => rewrite (pop_env_gc_fun _ _ E)
      | E : evaluate _ = (_, ?y) |- context [gc_fun ?y] =>
          rewrite <- (proj1 (evaluate_consts _ _ _ _ E))
      end ];
  assumption.

Ltac cong_split_gc :=
  repeat first
    [ progress (rewrite ?fix_clock_evaluate)
    | match goal with
      | H : eq_eval_gc ?p ?q |- context [evaluate (?p, ?s)] => rewrite (H s) by gc_ok
      end
    | match goal with
      | |- context [@bool_decide (SOME ?x = NONE) ?d] =>
          let F := fresh "F" in
          assert (F : @bool_decide (SOME x = NONE) d = false) by (apply bd_false; discriminate);
          rewrite F; clear F
      end
    | match goal with
      | |- context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
      end ];
  try reflexivity.

Lemma eq_eval_gc_Call (f : prog a -> prog a) ret dest args h :
  match ret with Some (_, (_, (q, _))) => eq_eval_gc (f q) q | None => True end ->
  match h with Some (_, (q, _)) => eq_eval_gc (f q) q | None => True end ->
  eq_eval_gc
    (Call (match ret with
           | None => None
           | Some (x1, (x2, (q1, (x3, x4)))) => Some (x1, (x2, (f q1, (x3, x4))))
           end) dest args
          (match h with
           | None => None
           | Some (y1, (q2, (y2, y3))) => Some (y1, (f q2, (y2, y3)))
           end))
    (Call ret dest args h).
Proof.
  intros H1 H2 s Hok.
  destruct ret as [[x1 [x2 [q1 [x3 x4]]]]|], h as [[y1 [q2 [y2 y3]]]|];
    cbn iota in H1, H2;
    rewrite !(evaluate_eqn (Call _ _ _ _) s); cbn [evaluate_body add_ret_loc];
    unfold push_env; cong_split_gc.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_simp_duplicate_if" *)
Theorem evaluate_simp_duplicate_if : forall (p : prog a) s,
  gc_fun_const_ok (gc_fun s) -> evaluate (simp_duplicate_if p, s) = evaluate (p, s).
Proof.
  intros p. change (eq_eval_gc (simp_duplicate_if p) p).
  induction p as [ | | | | | | |q IHq|ret dest args h IHret IHh|q1 q2 IH1 IH2
                  |cmp lhs rhs q1 q2 IH1 IH2|names q exit_names IHq | | | | | | | | | | | | | |]
    using prog_nested_ind; cbn [simp_duplicate_if]; try (intros st Hok; reflexivity).
  - (* MustTerminate *)
    intros st Hok. rewrite !(evaluate_eqn (MustTerminate _) st); cbn [evaluate_body].
    rewrite IHq by exact Hok. reflexivity.
  - (* Call *)
    apply (eq_eval_gc_Call simp_duplicate_if).
    + destruct ret as [[? [? [? ?]]]|]; [exact IHret|exact Logic.I].
    + destruct h as [[? [? ?]]|]; [exact IHh|exact Logic.I].
  - (* Seq *)
    intros st Hok. cbn zeta.
    assert (G : evaluate (Seq (simp_duplicate_if q1) (simp_duplicate_if q2), st) =
                evaluate (Seq q1 q2, st)).
    { rewrite !evaluate_Seq_eq, IH1 by exact Hok. destruct (evaluate (q1, st)) as [r1 s1] eqn:E1.
      destruct (bool_decide _); [|reflexivity].
      apply IH2. exact (evaluate_gc_fun_const_ok _ _ _ _ (conj E1 Hok)). }
    destruct (try_if_hoist1 (simp_duplicate_if q1) (simp_duplicate_if q2)) as [p3|] eqn:E; [|exact G].
    rewrite evaluate_Seq_assoc, (evaluate_try_if_hoist1 _ _ _ _ E Hok). exact G.
  - (* If *)
    intros st Hok. rewrite !(evaluate_eqn (If _ _ _ _ _) st); cbn [evaluate_body].
    destruct (get_var lhs st); [|reflexivity]. destruct (get_var_imm rhs st); [|reflexivity].
    destruct (wordSem.word_cmp _ _ _) as [[]|]; [apply IH1, Hok|apply IH2, Hok|reflexivity].
  - (* Loop *)
    intros st Hok. apply (evaluate_Loop_body_cong_gc gc_fun_const_ok); [|exact Hok].
    intros v Hv. apply IHq, Hv.
Qed.

Ltac not_none p s :=
  rewrite (evaluate_eqn p s); cbn [evaluate_body];
  repeat match goal with
         | |- context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta
         end;
  cbn [fst]; congruence.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "push_out_if_aux_T" *)
Theorem push_out_if_aux_T : forall (c2 c2' : prog a) res s s',
  push_out_if_aux c2 = (c2', true) -> evaluate (c2, s) = (res, s') -> res <> NONE.
Proof.
  intros c2.
  induction c2 as [ | | | | | | |q IHq|ret dest args h IHret IHh|q1 q2 IH1 IH2
                  |cmp lhs rhs q1 q2 IH1 IH2|names q exit_names IHq | | | | | | | | | | | | | |]
    using prog_nested_ind; intros c2' res st st' Ha H; cbn [push_out_if_aux] in Ha;
    try (injection Ha as _ Ha; discriminate Ha).
  - (* MustTerminate *)
    destruct (push_out_if_aux q) as [cq b] eqn:Eq. injection Ha as _ ->.
    rewrite evaluate_eqn in H; cbn [evaluate_body] in H.
    destruct (termdep st =? 0); [injection H as <- _; discriminate|].
    destruct (evaluate (q, _)) as [r t] eqn:E.
    destruct (bool_decide (r = SOME TimeOut)); [injection H as <- _; discriminate|].
    injection H as <- _. exact (IHq _ _ _ _ eq_refl E).
  - (* Call *)
    destruct ret; [injection Ha as _ Ha; discriminate Ha|].
    intros ->. apply (Call_NONE_not_NONE dest args h st). rewrite H. reflexivity.
  - (* Seq *)
    rewrite evaluate_Seq_eq in H. destruct (evaluate (q1, st)) as [r1 s1] eqn:E1.
    destruct (push_out_if_aux q1) as [c1' []] eqn:Ec1.
    + injection Ha as _. pose proof (IH1 _ _ _ _ eq_refl E1) as Hn.
      rewrite bd_false in H by exact Hn. injection H as <- _. exact Hn.
    + destruct (push_out_if_aux q2) as [c2'' b] eqn:Ec2. injection Ha as _ ->.
      destruct (bool_decide (r1 = NONE)) eqn:En; [exact (IH2 _ _ _ _ eq_refl H)|].
      injection H as <- _. intros ->. rewrite bd_true in En by reflexivity. discriminate.
  - (* If *)
    destruct (push_out_if_aux q1) as [c1' [] ] eqn:Ec1, (push_out_if_aux q2) as [c2'' [] ] eqn:Ec2;
      try (inversion Ha; fail).
    rewrite evaluate_eqn in H; cbn [evaluate_body] in H.
    split_H H; try (injection H as <- _; discriminate).
    + exact (IH1 _ _ _ _ eq_refl H).
    + exact (IH2 _ _ _ _ eq_refl H).
  - intros ->; match type of H with evaluate (?p, _) = _ => revert H; not_none p st end.
  - intros ->; match type of H with evaluate (?p, _) = _ => revert H; not_none p st end.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_simp_push_out_if" *)
Theorem evaluate_simp_push_out_if : forall (p : prog a) s,
  evaluate (push_out_if p, s) = evaluate (p, s).
Proof.
  intros p. unfold push_out_if. change (@eq_eval a c ffi_t (FST (push_out_if_aux p)) p).
  induction p as [ | | | | | | |q IHq|ret dest args h IHret IHh|q1 q2 IH1 IH2
                  |cmp lhs rhs q1 q2 IH1 IH2|names q exit_names IHq | | | | | | | | | | | | | |]
    using prog_nested_ind; cbn [push_out_if_aux]; try (intros st; reflexivity).
  - (* MustTerminate *)
    destruct (push_out_if_aux q) as [cq b] eqn:Eq. cbn [FST fst] in *.
    apply eq_eval_MustTerminate, IHq.
  - (* Call *) destruct ret; intros st; reflexivity.
  - (* Seq *)
    destruct (push_out_if_aux q1) as [c1' []] eqn:Ec1; cbn [FST fst] in *.
    + apply eq_eval_Seq; [exact IH1|apply eq_eval_refl].
    + destruct (push_out_if_aux q2) as [c2' b] eqn:Ec2; cbn [FST fst] in *.
      apply eq_eval_Seq; assumption.
  - (* If *)
    destruct (push_out_if_aux q1) as [c1' b1] eqn:Ec1, (push_out_if_aux q2) as [c2' b2] eqn:Ec2;
      cbn [FST fst] in *.
    destruct b1, b2; cbn [FST fst];
      try (apply eq_eval_If; assumption); intros st;
      rewrite evaluate_Seq_eq, !(evaluate_eqn (If _ _ _ _ _) st); cbn [evaluate_body];
      (destruct (get_var lhs st); [|rewrite bd_false by discriminate; reflexivity]);
      (destruct (get_var_imm rhs st); [|rewrite bd_false by discriminate; reflexivity]);
      (destruct (wordSem.word_cmp _ _ _) as [[]|]; [..|rewrite bd_false by discriminate; reflexivity]).
    + rewrite IH1. destruct (evaluate (q1, st)) as [r t] eqn:E.
      rewrite bd_false by exact (push_out_if_aux_T _ _ _ _ _ Ec1 E). reflexivity.
    + rewrite evaluate_Skip_eq, bd_true by reflexivity. apply IH2.
    + rewrite evaluate_Skip_eq, bd_true by reflexivity. apply IH1.
    + rewrite IH2. destruct (evaluate (q2, st)) as [r t] eqn:E.
      rewrite bd_false by exact (push_out_if_aux_T _ _ _ _ _ Ec2 E). reflexivity.
  - (* Loop *) apply eq_eval_Loop, IHq.
Qed.

End DupIf.

(** ** Putting it all together *)

Section CompileExp.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "compile_exp_thm" *)
Theorem compile_exp_thm : forall (prog : prog a) (s : state a c ffi_t) res s2,
  evaluate (prog, s) = (res, s2) /\ res <> SOME Error /\ gc_fun_const_ok (gc_fun s) ->
  evaluate (word_simp.compile_exp prog, s) = (res, s2).
Proof.
  intros prog s res s2 [H [_ Hok]]. unfold word_simp.compile_exp; cbn zeta.
  rewrite evaluate_simp_push_out_if, evaluate_simp_duplicate_if, evaluate_const_fp,
    evaluate_Seq_assoc by exact Hok. exact H.
Qed.

End CompileExp.
