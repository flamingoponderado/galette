(** * CakeML [wordProps]: the stack swap lemma

    Port of the "Stack Swap Lemma" part of
    [cakeml/compiler/backend/semantics/wordPropsScript.sml]: the relations
    [s_val_eq] (same values, e.g. recoloured keys) and [s_key_eq] (same
    keys, e.g. the result of [gc]) on stacks, their lemmas, and
    [evaluate_stack_swap] with its corollary
    [evaluate_NONE_stack_size_const].

    Carrier notes:
    - HOL's boolean relations [s_frame_val_eq], [s_val_eq],
      [s_frame_key_eq], [s_key_eq] are [Prop]-valued; HOL's [P = T]
      (the [*_refl] lemmas) is [P].
    - HOL [s with stack := xs] is [set_stack xs s] (similarly for the other
      fields); [s.stack_size] is [state_stack_size s].
    - HOL's [Abbrev (m = s1.locals_size)] (a proof-automation marker) is the
      equation [m = locals_size s1]. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
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
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import consts clock consts_with dec_clock code.
Open Scope N_scope.

Section Rel.
Context {a : N}.
Local Abbreviation frame := (stack_frame a).

(** Stacks look the same to the GC except for the keys (e.g. recoloured
    and in order). *)
(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_val_eq_def" *)
Definition s_frame_val_eq (f1 f2 : frame) : Prop :=
  match f1, f2 with
  | StackFrame n ls1 ls NONE, StackFrame n' ls1' ls' NONE => MAP SND ls = MAP SND ls' /\ n = n'
  | StackFrame n ls1 ls (SOME y), StackFrame n' ls1' ls' (SOME y') =>
      MAP SND ls = MAP SND ls' /\ y = y' /\ n = n'
  | _, _ => False
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_val_eq_def2" *)
Theorem s_frame_val_eq_def2 : forall n ls0 ls y n' ls0' ls' y',
  s_frame_val_eq (StackFrame n ls0 ls y) (StackFrame n' ls0' ls' y') <->
  MAP SND ls = MAP SND ls' /\ y = y' /\ n = n'.
Proof.
  intros; destruct y as [y|], y' as [y'|]; cbn; split; intros H; destr_conj; subst;
    try discriminate; try contradiction;
    try (match goal with E : SOME _ = SOME _ |- _ => injection E as -> end);
    repeat split; auto.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_def" *)
Fixpoint s_val_eq (l1 l2 : list frame) : Prop :=
  match l1, l2 with
  | [], [] => True
  | x :: xs, y :: ys => s_val_eq xs ys /\ s_frame_val_eq x y
  | _, _ => False
  end.

(** Stacks look the same except for the values of the GC-ed cutsets (e.g.
    result of [gc]). *)
(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_key_eq_def" *)
Definition s_frame_key_eq (f1 f2 : frame) : Prop :=
  match f1, f2 with
  | StackFrame n ls0 ls NONE, StackFrame n' ls0' ls' NONE =>
      MAP FST ls = MAP FST ls' /\ ls0 = ls0' /\ n = n'
  | StackFrame n ls0 ls (SOME y), StackFrame n' ls0' ls' (SOME y') =>
      MAP FST ls = MAP FST ls' /\ y = y' /\ ls0 = ls0' /\ n = n'
  | _, _ => False
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_key_eq_def2" *)
Theorem s_frame_key_eq_def2 : forall n ls0 ls y n' ls0' ls' y',
  s_frame_key_eq (StackFrame n ls0 ls y) (StackFrame n' ls0' ls' y') <->
  MAP FST ls = MAP FST ls' /\ y = y' /\ ls0 = ls0' /\ n = n'.
Proof.
  intros; destruct y as [y|], y' as [y'|]; cbn; split; intros H; destr_conj; subst;
    try discriminate; try contradiction;
    try (match goal with E : SOME _ = SOME _ |- _ => injection E as -> end);
    repeat split; auto.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_def" *)
Fixpoint s_key_eq (l1 l2 : list frame) : Prop :=
  match l1, l2 with
  | [], [] => True
  | x :: xs, y :: ys => s_key_eq xs ys /\ s_frame_key_eq x y
  | _, _ => False
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_def2" *)
Theorem s_key_eq_def2 : forall l1 l2, s_key_eq l1 l2 <-> LIST_REL s_frame_key_eq l1 l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2]; cbn.
  - split; [intros; constructor|tauto].
  - split; [tauto|intros H; inversion H].
  - split; [tauto|intros H; inversion H].
  - rewrite IH; split; [intros [H1 H2]; constructor; assumption|].
    intros H; inversion H; subst; split; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_def2" *)
Theorem s_val_eq_def2 : forall l1 l2, s_val_eq l1 l2 <-> LIST_REL s_frame_val_eq l1 l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2]; cbn.
  - split; [intros; constructor|tauto].
  - split; [tauto|intros H; inversion H].
  - split; [tauto|intros H; inversion H].
  - rewrite IH; split; [intros [H1 H2]; constructor; assumption|].
    intros H; inversion H; subst; split; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_key_eq_refl" *)
Theorem s_frame_key_eq_refl : forall ls, s_frame_key_eq ls ls.
Proof. intros [n l0 l [y|]]; cbn; repeat split. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_val_eq_refl" *)
Theorem s_frame_val_eq_refl : forall ls, s_frame_val_eq ls ls.
Proof. intros [n l0 l [y|]]; cbn; repeat split. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_refl" *)
Theorem s_key_eq_refl : forall ls, s_key_eq ls ls.
Proof. induction ls; cbn; [exact Logic.I|split; [assumption|apply s_frame_key_eq_refl]]. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_refl" *)
Theorem s_val_eq_refl : forall ls, s_val_eq ls ls.
Proof. induction ls; cbn; [exact Logic.I|split; [assumption|apply s_frame_val_eq_refl]]. Qed.

Local Ltac frame_tac :=
  repeat match goal with f : frame |- _ => destruct f as [? ? ? [?|]] end;
  cbn in *; destr_conj; try contradiction; repeat split; congruence.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_key_eq_trans" *)
Theorem s_frame_key_eq_trans : forall a0 b c0,
  s_frame_key_eq a0 b /\ s_frame_key_eq b c0 -> s_frame_key_eq a0 c0.
Proof. intros a0 b c0 [H1 H2]; frame_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_trans" *)
Theorem s_key_eq_trans : forall a0 b c0, s_key_eq a0 b /\ s_key_eq b c0 -> s_key_eq a0 c0.
Proof.
  induction a0 as [|x a0 IH]; intros [|y b] [|z c0] [H1 H2]; cbn in *; try tauto.
  destruct H1, H2; split; [eapply IH; split; eassumption|eapply s_frame_key_eq_trans; split; eassumption].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_val_eq_trans" *)
Theorem s_frame_val_eq_trans : forall a0 b c0,
  s_frame_val_eq a0 b /\ s_frame_val_eq b c0 -> s_frame_val_eq a0 c0.
Proof. intros a0 b c0 [H1 H2]; frame_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_trans" *)
Theorem s_val_eq_trans : forall a0 b c0, s_val_eq a0 b /\ s_val_eq b c0 -> s_val_eq a0 c0.
Proof.
  induction a0 as [|x a0 IH]; intros [|y b] [|z c0] [H1 H2]; cbn in *; try tauto.
  destruct H1, H2; split; [eapply IH; split; eassumption|eapply s_frame_val_eq_trans; split; eassumption].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_key_eq_sym" *)
Theorem s_frame_key_eq_sym : forall a0 b, s_frame_key_eq a0 b <-> s_frame_key_eq b a0.
Proof. intros a0 b; split; intros H; frame_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_sym" *)
Theorem s_key_eq_sym : forall a0 b, s_key_eq a0 b <-> s_key_eq b a0.
Proof.
  induction a0 as [|x a0 IH]; intros [|y b]; cbn; try tauto.
  rewrite IH, s_frame_key_eq_sym; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_val_eq_sym" *)
Theorem s_frame_val_eq_sym : forall a0 b, s_frame_val_eq a0 b <-> s_frame_val_eq b a0.
Proof. intros a0 b; split; intros H; frame_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_sym" *)
Theorem s_val_eq_sym : forall a0 b, s_val_eq a0 b <-> s_val_eq b a0.
Proof.
  induction a0 as [|x a0 IH]; intros [|y b]; cbn; try tauto.
  rewrite IH, s_frame_val_eq_sym; tauto.
Qed.

Lemma map_fst_snd_eq {A B} (l1 l2 : list (A * B)) :
  MAP FST l1 = MAP FST l2 -> MAP SND l1 = MAP SND l2 -> l1 = l2.
Proof.
  revert l2; induction l1 as [|[x y] l1 IH]; intros [|[x' y'] l2]; cbn; try discriminate; auto.
  intros H1 H2; injection H1 as -> H1; injection H2 as -> H2; f_equal; auto.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_val_and_key_eq" *)
Theorem s_frame_val_and_key_eq : forall s t,
  s_frame_val_eq s t /\ s_frame_key_eq s t -> s = t.
Proof.
  intros [n l0 l [y|]] [n' l0' l' [y'|]] [H1 H2]; cbn in *; destr_conj; try contradiction;
    subst; f_equal; apply map_fst_snd_eq; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "LIST_REL_CONJ2" *)
Theorem LIST_REL_CONJ2 : forall {A B} (P Q : A -> B -> Prop) l1 l2,
  LIST_REL (fun a b => P a b /\ Q a b) l1 l2 <-> LIST_REL P l1 l2 /\ LIST_REL Q l1 l2.
Proof.
  intros A B P Q l1 l2; split.
  - intros H; induction H as [|x y l1 l2 [Hp Hq] _ [IH1 IH2]]; split; constructor; assumption.
  - intros [H1 H2]; induction H1 as [|x y l1 l2 Hp _ IH]; [constructor|].
    inversion H2; subst; constructor; [split; assumption|apply IH; assumption].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_and_key_eq" *)
Theorem s_val_and_key_eq : forall s t, s_val_eq s t /\ s_key_eq s t -> s = t.
Proof.
  induction s as [|x s IH]; intros [|y t] [H1 H2]; cbn in *; try tauto.
  destruct H1, H2; f_equal; [apply s_frame_val_and_key_eq; split; assumption|apply IH; split; assumption].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_length" *)
Theorem s_val_eq_length : forall s t, s_val_eq s t -> LENGTH s = LENGTH t.
Proof.
  induction s as [|x s IH]; intros [|y t] H; cbn in H; try contradiction; [reflexivity|].
  specialize (IH t (proj1 H)); rewrite !LENGTH_length in *; cbn [length]; lia.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_length" *)
Theorem s_key_eq_length : forall s t, s_key_eq s t -> LENGTH s = LENGTH t.
Proof.
  induction s as [|x s IH]; intros [|y t] H; cbn in H; try contradiction; [reflexivity|].
  specialize (IH t (proj1 H)); rewrite !LENGTH_length in *; cbn [length]; lia.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_APPEND" *)
Theorem s_val_eq_APPEND : forall s t x y, s_val_eq s t /\ s_val_eq x y -> s_val_eq (s ++ x) (t ++ y).
Proof.
  induction s as [|f s IH]; intros [|g t] x y [H1 H2]; cbn in *; try tauto.
  destruct H1; split; [apply IH; split|]; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_REVERSE" *)
Theorem s_val_eq_REVERSE : forall s t, s_val_eq s t -> s_val_eq (REVERSE s) (REVERSE t).
Proof.
  induction s as [|f s IH]; intros [|g t] H; cbn in *; try tauto.
  destruct H; apply s_val_eq_APPEND; split; [apply IH; assumption|cbn; split; [exact Logic.I|assumption]].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_TAKE" *)
Theorem s_val_eq_TAKE : forall s t n, s_val_eq s t -> s_val_eq (TAKE n s) (TAKE n t).
Proof.
  induction s as [|f s IH]; intros [|g t] n H; cbn in *; try tauto.
  destruct (n =? 0); cbn; [exact Logic.I|]. destruct H; split; [apply IH|]; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_LASTN" *)
Theorem s_val_eq_LASTN : forall s t n, s_val_eq s t -> s_val_eq (LASTN n s) (LASTN n t).
Proof.
  intros s t n H; unfold LASTN. apply s_val_eq_REVERSE, s_val_eq_TAKE, s_val_eq_REVERSE, H.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_APPEND" *)
Theorem s_key_eq_APPEND : forall s t x y, s_key_eq s t /\ s_key_eq x y -> s_key_eq (s ++ x) (t ++ y).
Proof.
  induction s as [|f s IH]; intros [|g t] x y [H1 H2]; cbn in *; try tauto.
  destruct H1; split; [apply IH; split|]; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_REVERSE" *)
Theorem s_key_eq_REVERSE : forall s t, s_key_eq s t -> s_key_eq (REVERSE s) (REVERSE t).
Proof.
  induction s as [|f s IH]; intros [|g t] H; cbn in *; try tauto.
  destruct H; apply s_key_eq_APPEND; split; [apply IH; assumption|cbn; split; [exact Logic.I|assumption]].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_TAKE" *)
Theorem s_key_eq_TAKE : forall s t n, s_key_eq s t -> s_key_eq (TAKE n s) (TAKE n t).
Proof.
  induction s as [|f s IH]; intros [|g t] n H; cbn in *; try tauto.
  destruct (n =? 0); cbn; [exact Logic.I|]. destruct H; split; [apply IH|]; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_LASTN" *)
Theorem s_key_eq_LASTN : forall s t n, s_key_eq s t -> s_key_eq (LASTN n s) (LASTN n t).
Proof.
  intros s t n H; unfold LASTN. apply s_key_eq_REVERSE, s_key_eq_TAKE, s_key_eq_REVERSE, H.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_tail" *)
Theorem s_key_eq_tail : forall a0 b c0 d, s_key_eq (a0 :: b) (c0 :: d) -> s_key_eq b d.
Proof. intros a0 b c0 d [H _]; exact H. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_tail" *)
Theorem s_val_eq_tail : forall a0 b c0 d, s_val_eq (a0 :: b) (c0 :: d) -> s_val_eq b d.
Proof. intros a0 b c0 d [H _]; exact H. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_LASTN_exists" *)
Theorem s_key_eq_LASTN_exists : forall s t n m e0 e y xs,
  s_key_eq s t /\ LASTN n s = StackFrame m e0 e (SOME y) :: xs ->
  exists e' ls, LASTN n t = StackFrame m e0 e' (SOME y) :: ls /\ MAP FST e' = MAP FST e /\
                s_key_eq xs ls.
Proof.
  intros s t n m e0 e y xs [H1 H2]. pose proof (s_key_eq_LASTN s t n H1) as H. rewrite H2 in H.
  destruct (LASTN n t) as [|[m' e0' e' [y'|]] ls]; cbn in H; destr_conj; try contradiction.
  subst; exists e', ls; repeat split; auto.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_LASTN_exists" *)
Theorem s_val_eq_LASTN_exists : forall s t n m e0 e y xs,
  s_val_eq s t /\ LASTN n s = StackFrame m e0 e (SOME y) :: xs ->
  exists e0' e' ls, LASTN n t = StackFrame m e0' e' (SOME y) :: ls /\ MAP SND e' = MAP SND e /\
                    s_val_eq xs ls.
Proof.
  intros s t n m e0 e y xs [H1 H2]. pose proof (s_val_eq_LASTN s t n H1) as H. rewrite H2 in H.
  destruct (LASTN n t) as [|[m' e0' e' [y'|]] ls]; cbn in H; destr_conj; try contradiction.
  subst; exists e0', e', ls; repeat split; auto.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "LASTN_LENGTH_cond" *)
Theorem LASTN_LENGTH_cond : forall {A} n (xs : list A), n = LENGTH xs -> LASTN n xs = xs.
Proof.
  intros A n xs ->; unfold LASTN.
  assert (Ht : forall l : list A, TAKE (N.of_nat (length l)) l = l).
  { induction l as [|x l IH]; [reflexivity|]. cbn [TAKE length].
    replace (N.of_nat (S (length l)) =? 0) with false by (symmetry; apply N.eqb_neq; lia).
    replace (N.of_nat (S (length l)) - 1) with (N.of_nat (length l)) by lia.
    rewrite IH; reflexivity. }
  rewrite LENGTH_length, <- length_rev, Ht; apply rev_involutive.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_stack_size" *)
Theorem s_val_eq_stack_size : forall xs ys, s_val_eq xs ys -> stack_size xs = stack_size ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; cbn in H; try contradiction; [reflexivity|].
  destruct H as [H Hf].
  change (OPTION_MAP2 N.add (stack_size_frame x) (stack_size xs) =
          OPTION_MAP2 N.add (stack_size_frame y) (stack_size ys)).
  rewrite (IH ys H). destruct x as [? ? ? [?|]], y as [? ? ? [?|]]; cbn in Hf; destr_conj;
    try contradiction; subst; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_stack_size" *)
Theorem s_key_eq_stack_size : forall xs ys, s_key_eq xs ys -> stack_size xs = stack_size ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; cbn in H; try contradiction; [reflexivity|].
  destruct H as [H Hf].
  change (OPTION_MAP2 N.add (stack_size_frame x) (stack_size xs) =
          OPTION_MAP2 N.add (stack_size_frame y) (stack_size ys)).
  rewrite (IH ys H). destruct x as [? ? ? [?|]], y as [? ? ? [?|]]; cbn in Hf; destr_conj;
    try contradiction; subst; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_append_eq_stack_size" *)
Theorem s_val_append_eq_stack_size : forall stk stk' (frm : frame),
  s_val_eq stk stk' -> stack_size (frm :: stk) = stack_size (frm :: stk').
Proof.
  intros stk stk' frm H.
  change (OPTION_MAP2 N.add (stack_size_frame frm) (stack_size stk) =
          OPTION_MAP2 N.add (stack_size_frame frm) (stack_size stk')).
  rewrite (s_val_eq_stack_size _ _ H); reflexivity.
Qed.

End Rel.

(** ** Stacks of states *)

Local Lemma map_fst_ZIP {A B} (l1 : list A) (l2 : list B) :
  (length l1 <= length l2)%nat -> MAP FST (ZIP (l1, l2)) = l1.
Proof.
  revert l2; induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in *; try reflexivity; [lia|].
  f_equal; apply IH; lia.
Qed.

Local Lemma map_snd_ZIP {A B} (l1 : list A) (l2 : list B) :
  (length l2 <= length l1)%nat -> MAP SND (ZIP (l1, l2)) = l2.
Proof.
  revert l2; induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in *; try reflexivity; [lia|].
  f_equal; apply IH; lia.
Qed.

Local Lemma length_TAKE {A} n (l : list A) : length (TAKE n l) = Nat.min (N.to_nat n) (length l).
Proof.
  revert n; induction l as [|x l IH]; intros n; cbn; [lia|].
  destruct (N.eqb_spec n 0) as [->|Hn]; cbn; [reflexivity|]. rewrite IH; lia.
Qed.

Section StateRel.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "dec_stack_stack_key_eq" *)
Theorem dec_stack_stack_key_eq : forall (wl : list (word_loc a)) st st',
  dec_stack wl st = SOME st' -> s_key_eq st st'.
Proof.
  intros wl st; revert wl; induction st as [|[n l0 l h] st IH]; intros wl st' H; cbn in H.
  - destruct wl; [injection H as <-; exact Logic.I|discriminate].
  - destruct (LENGTH wl <? LENGTH l) eqn:El; [discriminate|].
    destruct (dec_stack (DROP (LENGTH l) wl) st) as [s|] eqn:E; [|discriminate].
    injection H as <-; cbn; split; [apply (IH _ _ E)|].
    apply N.ltb_ge in El; rewrite !LENGTH_length in El.
    apply s_frame_key_eq_def2; repeat split.
    symmetry; apply map_fst_ZIP. rewrite length_map, length_TAKE, LENGTH_length; lia.
Qed.

(** gc preserves the stack_key relation *)
(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "gc_s_key_eq" *)
Theorem gc_s_key_eq : forall (s x : state), gc s = SOME x -> s_key_eq (stack s) (stack x).
Proof.
  intros s x H; unfold gc in H. destruct (gc_fun s _) as [[wl [m st]]|]; [|discriminate].
  destruct (dec_stack wl (stack s)) as [stk|] eqn:E; [|discriminate].
  injection H as <-; exact (dec_stack_stack_key_eq _ _ _ E).
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_enc_stack" *)
Theorem s_val_eq_enc_stack : forall (st st' : list (stack_frame a)),
  s_val_eq st st' -> enc_stack st = enc_stack st'.
Proof.
  induction st as [|f st IH]; intros [|g st'] H; cbn [s_val_eq] in H; try contradiction; [reflexivity|].
  destruct H as [H Hf]; destruct f as [? ? ? ?], g as [? ? ? ?]; apply s_frame_val_eq_def2 in Hf.
  destr_conj; cbn; f_equal; [assumption|apply IH, H].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_dec_stack" *)
Theorem s_val_eq_dec_stack : forall (q : list (word_loc a)) st st' x,
  s_val_eq st st' /\ dec_stack q st = SOME x ->
  exists y, dec_stack q st' = SOME y /\ s_val_eq x y.
Proof.
  intros q st; revert q; induction st as [|[n l0 l h] st IH]; intros q [|[n' l0' l' h'] st'] x [Hv H];
    cbn [s_val_eq] in Hv; try contradiction.
  - exists x; split; [exact H|]. cbn in H; destruct q; [injection H as <-; exact Logic.I|discriminate].
  - destruct Hv as [Hv Hf]; apply s_frame_val_eq_def2 in Hf; destruct Hf as (Hm & <- & <-).
    assert (Hl : LENGTH l = LENGTH l') by (rewrite !LENGTH_length, <- (length_map snd l), Hm, length_map; reflexivity).
    cbn [dec_stack] in H |- *. rewrite <- Hl.
    destruct (LENGTH q <? LENGTH l) eqn:El; [discriminate|].
    destruct (dec_stack (DROP (LENGTH l) q) st) as [s1|] eqn:E; [|discriminate].
    injection H as <-.
    destruct (IH _ st' s1 (conj Hv E)) as [y [Hy Hyv]]. rewrite Hy.
    eexists; split; [reflexivity|]. cbn [s_val_eq]; split; [exact Hyv|].
    apply N.ltb_ge in El; rewrite !LENGTH_length in El, Hl.
    apply s_frame_val_eq_def2; repeat split.
    rewrite ?(LENGTH_length l') in Hl; apply Nat2N.inj in Hl.
    transitivity (TAKE (LENGTH l) q); [|symmetry]; apply map_snd_ZIP; rewrite length_TAKE, length_map, ?LENGTH_length, Nat2N.id; lia.
Qed.

(** gc succeeds on all stacks related by stack_val and there are relations
    in the result.  HOL's statement also quantifies a vacuous variable [x];
    it is omitted. *)
(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "gc_s_val_eq" *)
Theorem gc_s_val_eq : forall (s : state) st y,
  s_val_eq (stack s) st /\ gc s = SOME y ->
  exists z, gc (set_stack st s) = SOME (set_stack z y) /\ s_val_eq (stack y) z /\ s_key_eq z st.
Proof.
  intros s st y [Hv H]; unfold gc in *; cbn [stack set_stack memory mdomain store gc_fun] in *.
  rewrite <- (s_val_eq_enc_stack _ _ Hv).
  destruct (gc_fun s _) as [[wl [m st0]]|]; [|discriminate].
  destruct (dec_stack wl (stack s)) as [stk|] eqn:E; [|discriminate].
  injection H as <-.
  destruct (s_val_eq_dec_stack wl (stack s) st stk (conj Hv E)) as [z [Hz Hzv]].
  rewrite Hz; exists z; split; [reflexivity|]. split; [exact Hzv|].
  apply s_key_eq_sym, (dec_stack_stack_key_eq _ _ _ Hz).
Qed.

(** Slightly more general theorem allows the unused locals to be different. *)
(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "gc_s_val_eq_word_state" *)
Theorem gc_s_val_eq_word_state : forall (s : state) tlocs tstack y,
  s_val_eq (stack s) tstack /\ gc s = SOME y ->
  exists zlocs zstack,
    gc (set_locals tlocs (set_stack tstack s)) = SOME (set_locals zlocs (set_stack zstack y)) /\
    s_val_eq (stack y) zstack /\ s_key_eq zstack tstack.
Proof.
  intros s tlocs tstack y [Hv H]; unfold gc in *;
    cbn [stack set_stack set_locals memory mdomain store gc_fun] in *.
  rewrite <- (s_val_eq_enc_stack _ _ Hv).
  destruct (gc_fun s _) as [[wl [m st0]]|]; [|discriminate].
  destruct (dec_stack wl (stack s)) as [stk|] eqn:E; [|discriminate].
  injection H as <-.
  destruct (s_val_eq_dec_stack wl (stack s) tstack stk (conj Hv E)) as [z [Hz Hzv]].
  rewrite Hz; exists tlocs, z; split; [reflexivity|]. split; [exact Hzv|].
  apply s_key_eq_sym, (dec_stack_stack_key_eq _ _ _ Hz).
Qed.

(** Most generalised [gc_s_val_eq]. *)
(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "gc_s_val_eq_gen" *)
Theorem gc_s_val_eq_gen : forall (s t s' : state),
  gc_fun s = gc_fun t /\ memory s = memory t /\ mdomain s = mdomain t /\ store s = store t /\
  s_val_eq (stack s) (stack t) /\ state_stack_size s = state_stack_size t /\
  stack_max s = stack_max t /\ stack_limit s = stack_limit t /\ gc s = SOME s' ->
  exists t',
    gc t = SOME t' /\ s_val_eq (stack s') (stack t') /\ s_key_eq (stack t) (stack t') /\
    memory t' = memory s' /\ store t' = store s' /\ state_stack_size t' = state_stack_size s' /\
    stack_max t' = stack_max s' /\ stack_limit t' = stack_limit s'.
Proof.
  intros s t s' (Hg & Hm & Hd & Hs & Hv & Hss & Hsm & Hsl & H); unfold gc in *.
  rewrite <- Hg, <- Hm, <- Hd, <- Hs, <- (s_val_eq_enc_stack _ _ Hv).
  destruct (gc_fun s _) as [[wl [m st0]]|]; [|discriminate].
  destruct (dec_stack wl (stack s)) as [stk|] eqn:E; [|discriminate].
  injection H as <-.
  destruct (s_val_eq_dec_stack wl (stack s) (stack t) stk (conj Hv E)) as [z [Hz Hzv]].
  rewrite Hz; eexists; split; [reflexivity|]; cbn.
  repeat split; try assumption; try (symmetry; assumption).
  exact (dec_stack_stack_key_eq _ _ _ Hz).
Qed.

(** pushing and popping maintain the stack_key relation *)
(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "push_env_pop_env_s_key_eq" *)
Theorem push_env_pop_env_s_key_eq : forall x b (s t : state),
  s_key_eq (stack (push_env x b s)) (stack t) ->
  exists n l ls opt,
    stack t = StackFrame n (toAList (FST x)) l opt :: ls /\
    exists y, pop_env t = SOME y /\
      locals y = union (fromAList l) (fromAList (toAList (FST x))) /\
      domain (SND x) UNION domain (FST x) = domain (locals y) /\
      s_key_eq (stack s) (stack y).
Proof.
  intros x b s t H.
  assert (Hk : exists l', stack (push_env x b s) =
                 StackFrame (locals_size s) (toAList (FST x)) l' (match b with
                   | NONE => NONE | SOME (_, (_, (l1, l2))) => SOME (handler s, (l1, l2)) end)
                 :: stack s /\ MAP FST l' = MAP FST (FST (env_to_list (SND x) (permute s)))).
  { destruct b as [[? [? [? ?]]]|]; unfold push_env; destruct (env_to_list _ _) as [l' pq] eqn:E;
      exists l'; split; reflexivity. }
  destruct Hk as [l' [Hst Hm]]. rewrite Hst in H.
  destruct (stack t) as [|[n l0 l opt] ls] eqn:Et; cbn [s_key_eq] in H; [contradiction|].
  destruct H as [Hrest Hf]. apply s_frame_key_eq_def2 in Hf. destruct Hf as (Hml & Hopt & <- & <-).
  exists (locals_size s), l, ls, opt; split; [reflexivity|].
  unfold pop_env; rewrite Et.
  assert (Hdom : domain (SND x) UNION domain (FST x) =
                 domain (union (fromAList l) (fromAList (toAList (FST x))))).
  { rewrite domain_union, !domain_fromAList, <- Hml, Hm.
    apply set_ext; intros k; unfold pred_set.UNION, pred_set.IN.
    rewrite <- !set_MAP_FST_toAList_domain.
    destruct (env_to_list (SND x) (permute s)) as [q r] eqn:Eq; cbn [FST fst].
    pose proof (env_to_list_lookup_equiv _ _ _ _ Eq) as [Ha Hb].
    unfold is_true; rewrite !MEM_In, !in_map_iff.
    split; (intros [[[k' v] [<- Hk']]|[[k' v] [<- Hk']]]; [left|right]); try (exists (k', v); auto; fail).
    - apply MEM_In, MEM_toAList in Hk'. rewrite <- Ha in Hk'.
      apply ALOOKUP_MEM in Hk'. apply MEM_In in Hk'. exists (k', v); auto.
    - apply MEM_In in Hk'. apply Hb in Hk'. exists (k', v); split; [reflexivity|].
      apply MEM_In, MEM_toAList, Hk'. }
  destruct opt as [[hn hl]|]; eexists; (split; [reflexivity|]); cbn; repeat split;
    try exact Hdom; exact Hrest.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "get_vars_stack_swap" *)
Theorem get_vars_stack_swap : forall l (s t : state), locals s = locals t -> get_vars l s = get_vars l t.
Proof.
  induction l as [|x l IH]; intros s t H; cbn; [reflexivity|].
  unfold get_var; rewrite H, (IH s t H); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "handler_eq" *)
Theorem handler_eq : forall (x : state), set_handler (handler x) x = x.
Proof. intros x; destruct x; reflexivity. Qed.

End StateRel.

(** ** Commuting with [set_stack] (Galette-only) *)

Section SetStack.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

Lemma locals_set_stack xs s : locals (set_stack xs s) = locals s. Proof. reflexivity. Qed.
Lemma locals_size_set_stack xs s : locals_size (set_stack xs s) = locals_size s. Proof. reflexivity. Qed.
Lemma fp_regs_set_stack xs s : fp_regs (set_stack xs s) = fp_regs s. Proof. reflexivity. Qed.
Lemma store_set_stack xs s : store (set_stack xs s) = store s. Proof. reflexivity. Qed.
Lemma stack_limit_set_stack xs s : stack_limit (set_stack xs s) = stack_limit s. Proof. reflexivity. Qed.
Lemma stack_max_set_stack xs s : stack_max (set_stack xs s) = stack_max s. Proof. reflexivity. Qed.
Lemma state_stack_size_set_stack xs s : state_stack_size (set_stack xs s) = state_stack_size s. Proof. reflexivity. Qed.
Lemma memory_set_stack xs s : memory (set_stack xs s) = memory s. Proof. reflexivity. Qed.
Lemma mdomain_set_stack xs s : mdomain (set_stack xs s) = mdomain s. Proof. reflexivity. Qed.
Lemma sh_mdomain_set_stack xs s : sh_mdomain (set_stack xs s) = sh_mdomain s. Proof. reflexivity. Qed.
Lemma permute_set_stack xs s : permute (set_stack xs s) = permute s. Proof. reflexivity. Qed.
Lemma compile_set_stack xs s : compile (set_stack xs s) = compile s. Proof. reflexivity. Qed.
Lemma compile_oracle_set_stack xs s : compile_oracle (set_stack xs s) = compile_oracle s. Proof. reflexivity. Qed.
Lemma code_buffer_set_stack xs s : code_buffer (set_stack xs s) = code_buffer s. Proof. reflexivity. Qed.
Lemma data_buffer_set_stack xs s : data_buffer (set_stack xs s) = data_buffer s. Proof. reflexivity. Qed.
Lemma gc_fun_set_stack xs s : gc_fun (set_stack xs s) = gc_fun s. Proof. reflexivity. Qed.
Lemma handler_set_stack xs s : handler (set_stack xs s) = handler s. Proof. reflexivity. Qed.
Lemma clock_set_stack xs s : clock (set_stack xs s) = clock s. Proof. reflexivity. Qed.
Lemma termdep_set_stack xs s : termdep (set_stack xs s) = termdep s. Proof. reflexivity. Qed.
Lemma code_set_stack xs s : code (set_stack xs s) = code s. Proof. reflexivity. Qed.
Lemma be_set_stack xs s : be (set_stack xs s) = be s. Proof. reflexivity. Qed.
Lemma ffi_set_stack xs s : ffi (set_stack xs s) = ffi s. Proof. reflexivity. Qed.
Lemma stack_set_stack xs s : stack (set_stack xs s) = xs. Proof. reflexivity. Qed.
Lemma set_stack_set_stack xs ys s : set_stack xs (set_stack ys s) = set_stack xs s. Proof. reflexivity. Qed.
Lemma set_locals_set_stack v xs s : set_locals v (set_stack xs s) = set_stack xs (set_locals v s). Proof. reflexivity. Qed.
Lemma set_locals_size_set_stack v xs s : set_locals_size v (set_stack xs s) = set_stack xs (set_locals_size v s). Proof. reflexivity. Qed.
Lemma set_fp_regs_set_stack v xs s : set_fp_regs v (set_stack xs s) = set_stack xs (set_fp_regs v s). Proof. reflexivity. Qed.
Lemma set_store_field_set_stack v xs s : set_store_field v (set_stack xs s) = set_stack xs (set_store_field v s). Proof. reflexivity. Qed.
Lemma set_stack_max_set_stack v xs s : set_stack_max v (set_stack xs s) = set_stack xs (set_stack_max v s). Proof. reflexivity. Qed.
Lemma set_stack_size_set_stack v xs s : set_stack_size v (set_stack xs s) = set_stack xs (set_stack_size v s). Proof. reflexivity. Qed.
Lemma set_memory_set_stack v xs s : set_memory v (set_stack xs s) = set_stack xs (set_memory v s). Proof. reflexivity. Qed.
Lemma set_mdomain_set_stack v xs s : set_mdomain v (set_stack xs s) = set_stack xs (set_mdomain v s). Proof. reflexivity. Qed.
Lemma set_sh_mdomain_set_stack v xs s : set_sh_mdomain v (set_stack xs s) = set_stack xs (set_sh_mdomain v s). Proof. reflexivity. Qed.
Lemma set_permute_set_stack v xs s : set_permute v (set_stack xs s) = set_stack xs (set_permute v s). Proof. reflexivity. Qed.
Lemma set_compile_set_stack v xs s : set_compile v (set_stack xs s) = set_stack xs (set_compile v s). Proof. reflexivity. Qed.
Lemma set_compile_oracle_set_stack v xs s : set_compile_oracle v (set_stack xs s) = set_stack xs (set_compile_oracle v s). Proof. reflexivity. Qed.
Lemma set_code_buffer_set_stack v xs s : set_code_buffer v (set_stack xs s) = set_stack xs (set_code_buffer v s). Proof. reflexivity. Qed.
Lemma set_data_buffer_set_stack v xs s : set_data_buffer v (set_stack xs s) = set_stack xs (set_data_buffer v s). Proof. reflexivity. Qed.
Lemma set_gc_fun_set_stack v xs s : set_gc_fun v (set_stack xs s) = set_stack xs (set_gc_fun v s). Proof. reflexivity. Qed.
Lemma set_handler_set_stack v xs s : set_handler v (set_stack xs s) = set_stack xs (set_handler v s). Proof. reflexivity. Qed.
Lemma set_clock_set_stack v xs s : set_clock v (set_stack xs s) = set_stack xs (set_clock v s). Proof. reflexivity. Qed.
Lemma set_termdep_set_stack v xs s : set_termdep v (set_stack xs s) = set_stack xs (set_termdep v s). Proof. reflexivity. Qed.
Lemma set_code_set_stack v xs s : set_code v (set_stack xs s) = set_stack xs (set_code v s). Proof. reflexivity. Qed.
Lemma set_be_set_stack v xs s : set_be v (set_stack xs s) = set_stack xs (set_be v s). Proof. reflexivity. Qed.
Lemma set_ffi_set_stack v xs s : set_ffi v (set_stack xs s) = set_stack xs (set_ffi v s). Proof. reflexivity. Qed.
Lemma set_var_set_stack v x xs s : set_var v x (set_stack xs s) = set_stack xs (set_var v x s). Proof. reflexivity. Qed.
Lemma unset_var_set_stack v xs s : unset_var v (set_stack xs s) = set_stack xs (unset_var v s). Proof. reflexivity. Qed.
Lemma set_vars_set_stack vs ys xs s : set_vars vs ys (set_stack xs s) = set_stack xs (set_vars vs ys s). Proof. reflexivity. Qed.
Lemma set_store_set_stack v x xs s : set_store v x (set_stack xs s) = set_stack xs (set_store v x s). Proof. reflexivity. Qed.
Lemma set_fp_var_set_stack v x xs s : set_fp_var v x (set_stack xs s) = set_stack xs (set_fp_var v x s). Proof. reflexivity. Qed.
Lemma flush_state_true_set_stack xs s : flush_state true (set_stack xs s) = flush_state true s. Proof. reflexivity. Qed.
Lemma flush_state_false_set_stack xs s : flush_state false (set_stack xs s) = set_stack xs (flush_state false s). Proof. reflexivity. Qed.
Lemma dec_clock_set_stack xs s : dec_clock (set_stack xs s) = set_stack xs (dec_clock s). Proof. reflexivity. Qed.
Lemma get_var_set_stack v xs s : get_var v (set_stack xs s) = get_var v s. Proof. reflexivity. Qed.
Lemma get_vars_set_stack vs xs s : get_vars vs (set_stack xs s) = get_vars vs s.
Proof. induction vs as [|v vs IH]; cbn; [reflexivity|]. rewrite IH; reflexivity. Qed.
Lemma get_store_set_stack v xs s : get_store v (set_stack xs s) = get_store v s. Proof. reflexivity. Qed.
Lemma get_fp_var_set_stack v xs s : get_fp_var v (set_stack xs s) = get_fp_var v s. Proof. reflexivity. Qed.
Lemma mem_load_set_stack v xs s : mem_load v (set_stack xs s) = mem_load v s. Proof. reflexivity. Qed.
Lemma get_var_imm_set_stack ri xs s : get_var_imm ri (set_stack xs s) = get_var_imm ri s.
Proof. destruct ri; reflexivity. Qed.
Lemma has_space_set_stack x xs s : has_space x (set_stack xs s) = has_space x s. Proof. reflexivity. Qed.
Lemma word_exp_set_stack e xs s : word_exp (set_stack xs s) e = word_exp s e.
Proof. apply word_exp_state_cong; reflexivity. Qed.
Lemma mem_store_set_stack x y xs s :
  mem_store x y (set_stack xs s) = OPTION_MAP (set_stack xs) (mem_store x y s).
Proof. unfold mem_store; cbn [mdomain set_stack]. destruct (classical_dec _); reflexivity. Qed.
Lemma cut_state_set_stack names xs s :
  cut_state names (set_stack xs s) = OPTION_MAP (set_stack xs) (cut_state names s).
Proof. unfold cut_state; cbn [locals set_stack]. destruct (cut_env _ _); reflexivity. Qed.
Lemma inst_set_stack i xs s : inst i (set_stack xs s) = OPTION_MAP (set_stack xs) (inst i s).
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (inst_with_const i s 0 (code s) (compile s) (compile_oracle s) (permute s) xs)))))). Qed.
Lemma sh_mem_load_set_stack v xs s : sh_mem_load v (set_stack xs s) = sh_mem_load v s. Proof. reflexivity. Qed.
Lemma sh_mem_load_byte_set_stack v xs s : sh_mem_load_byte v (set_stack xs s) = sh_mem_load_byte v s. Proof. reflexivity. Qed.
Lemma sh_mem_load16_set_stack v xs s : sh_mem_load16 v (set_stack xs s) = sh_mem_load16 v s. Proof. reflexivity. Qed.
Lemma sh_mem_load32_set_stack v xs s : sh_mem_load32 v (set_stack xs s) = sh_mem_load32 v s. Proof. reflexivity. Qed.

End SetStack.

Create Rewrite HintDb wds.
Global Hint Rewrite @locals_set_stack @locals_size_set_stack @fp_regs_set_stack @store_set_stack @stack_limit_set_stack @stack_max_set_stack @state_stack_size_set_stack @memory_set_stack @mdomain_set_stack @sh_mdomain_set_stack @permute_set_stack @compile_set_stack @compile_oracle_set_stack @code_buffer_set_stack @data_buffer_set_stack @gc_fun_set_stack @handler_set_stack @clock_set_stack @termdep_set_stack @code_set_stack @be_set_stack @ffi_set_stack @stack_set_stack @set_stack_set_stack @set_locals_set_stack @set_locals_size_set_stack @set_fp_regs_set_stack @set_store_field_set_stack @set_stack_max_set_stack @set_stack_size_set_stack @set_memory_set_stack @set_mdomain_set_stack @set_sh_mdomain_set_stack @set_permute_set_stack @set_compile_set_stack @set_compile_oracle_set_stack @set_code_buffer_set_stack @set_data_buffer_set_stack @set_gc_fun_set_stack @set_handler_set_stack @set_clock_set_stack @set_termdep_set_stack @set_code_set_stack @set_be_set_stack @set_ffi_set_stack @set_var_set_stack @unset_var_set_stack @set_vars_set_stack @set_store_set_stack @set_fp_var_set_stack @flush_state_true_set_stack @flush_state_false_set_stack @dec_clock_set_stack @get_var_set_stack @get_vars_set_stack @get_store_set_stack @get_fp_var_set_stack @mem_load_set_stack @get_var_imm_set_stack @has_space_set_stack @word_exp_set_stack @mem_store_set_stack @cut_state_set_stack @inst_set_stack @sh_mem_load_set_stack @sh_mem_load_byte_set_stack @sh_mem_load16_set_stack @sh_mem_load32_set_stack : wds.

(** ** The stack swap theorem *)

Section Swap.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(** Galette-only: the conclusion of [evaluate_stack_swap] for a given result. *)
Definition swap_res (c0 : prog a) (s : state) (r : option (result a)) (s1 : state) : Prop :=
  match r with
  | SOME Error => True
  | SOME (FinalFFI e) => stack s1 = [] /\ locals s1 = LN /\
      (forall xs, s_val_eq (stack s) xs -> evaluate (c0, set_stack xs s) = (r, s1))
  | SOME TimeOut => stack s1 = [] /\ locals s1 = LN /\
      (forall xs, s_val_eq (stack s) xs -> evaluate (c0, set_stack xs s) = (r, s1))
  | SOME NotEnoughSpace => stack s1 = [] /\ locals s1 = LN /\
      (forall xs, s_val_eq (stack s) xs -> evaluate (c0, set_stack xs s) = (r, s1))
  | SOME (Exception x y) =>
      handler s < LENGTH (stack s) /\
      exists e0 e n ls m lss,
        LASTN (handler s + 1) (stack s) = StackFrame m e0 e (SOME n) :: ls /\
        m = locals_size s1 /\
        (MAP FST e = MAP FST lss /\ locals s1 = union (fromAList lss) (fromAList e0)) /\
        s_key_eq (stack s1) ls /\ handler s1 = (let '(a0, _) := n in a0) /\
        (forall xs e0' e' ls',
           LASTN (handler s + 1) xs = StackFrame m e0' e' (SOME n) :: ls' /\ s_val_eq (stack s) xs ->
           exists st locs,
             evaluate (c0, set_stack xs s) =
               (SOME (Exception x y),
                set_locals locs (set_handler (let '(a0, _) := n in a0) (set_stack st s1))) /\
             (exists lss', MAP FST e' = MAP FST lss' /\ locs = union (fromAList lss') (fromAList e0') /\
                           MAP SND lss = MAP SND lss') /\
             s_val_eq (stack s1) st /\ s_key_eq ls' st)
  | _ => s_key_eq (stack s) (stack s1) /\ handler s1 = handler s /\
      (forall xs, s_val_eq (stack s) xs ->
         exists st, evaluate (c0, set_stack xs s) = (r, set_stack st s1) /\
                    s_val_eq (stack s1) st /\ s_key_eq xs st)
  end.

Local Ltac rw_ctor :=
  repeat match goal with
         | E : ?X = ?v |- context [?X] =>
             lazymatch v with
             | true => idtac | false => idtac | SOME _ => idtac | NONE => idtac
             | left _ => idtac | right _ => idtac | (_, _) => idtac
             | FFI_return _ _ => idtac | FFI_final _ => idtac | Word _ => idtac | Loc _ _ => idtac
             end;
             rewrite E; cbn beta iota zeta
         end.

Local Ltac sw_simple :=
  unfold swap_res; cbn [stack locals handler set_stack set_var set_vars unset_var set_locals set_store
    set_store_field set_fp_var set_fp_regs set_memory set_code_buffer set_data_buffer set_ffi
    set_locals_size set_stack_max set_stack_size set_compile_oracle set_code dec_clock set_clock
    flush_state];
  repeat match goal with
         | E : stack _ = stack _ |- _ => rewrite E; clear E
         | E : handler _ = handler _ |- _ => rewrite E; clear E
         end;
  repeat split; try reflexivity; try apply s_key_eq_refl;
  intros xs Hxs; try (exists xs; split; [|split; [assumption|apply s_key_eq_refl]]);
  rewrite evaluate_eqn; cbn [evaluate_body];
  unfold share_inst, sh_mem_set_var, sh_mem_load, sh_mem_load_byte, sh_mem_load16, sh_mem_load32,
    sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32;
  autorewrite with wds;
  repeat progress (rw_ctor; autorewrite with wds; cbn [OPTION_MAP option_map PAIR_MAP combin.I]);
  try reflexivity.

Lemma swap_res_map (P Q : prog a) (s s' s1 : state) r (f : state -> state) :
  stack s' = stack s -> handler s' = handler s ->
  (forall t st, f (set_stack st t) = set_stack st (f t)) ->
  (forall t l, f (set_locals l t) = set_locals l (f t)) ->
  (forall t h, f (set_handler h t) = set_handler h (f t)) ->
  (forall t, stack (f t) = stack t) -> (forall t, locals (f t) = locals t) ->
  (forall t, handler (f t) = handler t) -> (forall t, locals_size (f t) = locals_size t) ->
  (forall xs t', s_val_eq (stack s) xs -> evaluate (Q, set_stack xs s') = (r, t') ->
     evaluate (P, set_stack xs s) = (r, f t')) ->
  swap_res Q s' r s1 -> swap_res P s r (f s1).
Proof.
  intros Hs Hh Fs Fl Fh Gs Gl Gh Gls Hev H.
  unfold swap_res in *; rewrite Hs, Hh in H.
  destruct r as [[x ys|x y|k|k| | |e|]|]; try exact Logic.I;
    try (destruct H as (H1 & H2 & H3); rewrite Gs, Gl; repeat split; try assumption;
         intros xs Hx; apply Hev; [exact Hx|apply H3, Hx]; fail);
    try (destruct H as (H1 & H2 & H3); rewrite Gs, Gh; repeat split; try assumption;
         intros xs Hx; destruct (H3 xs Hx) as (st & Hst & Hv & Hk); exists st;
         rewrite (Hev xs _ Hx Hst), Fs; repeat split; assumption; fail).
  destruct H as (H1 & e0 & e & n & ls & m & lss & H2 & H3 & [H4 H5] & H6 & H7 & H8).
  split; [exact H1|]. exists e0, e, n, ls, m, lss.
  rewrite Gls, Gl, Gs, Gh; repeat split; try assumption.
  intros xs e0' e' ls' [Hl Hv]. destruct (H8 xs e0' e' ls' (conj Hl Hv)) as (st & locs & He & Hlss & Hsv & Hsk).
  exists st, locs; rewrite (Hev xs _ Hv He), Fl, Fh, Fs; repeat split; assumption.
Qed.

Definition is_norm (r : option (result a)) : Prop :=
  match r with
  | NONE => True
  | SOME (Result _ _) => True
  | SOME (Break _) => True
  | SOME (Continue _) => True
  | _ => False
  end.

Definition swap_norm (c0 : prog a) (s : state) (r : option (result a)) (s1 : state) : Prop :=
  s_key_eq (stack s) (stack s1) /\ handler s1 = handler s /\
  (forall xs, s_val_eq (stack s) xs ->
     exists st, evaluate (c0, set_stack xs s) = (r, set_stack st s1) /\
                s_val_eq (stack s1) st /\ s_key_eq xs st).

Lemma swap_res_norm c0 s r s1 : is_norm r -> swap_res c0 s r s1 -> swap_norm c0 s r s1.
Proof. intros Hn H; destruct r as [[]|]; cbn in Hn; try contradiction; exact H. Qed.

Lemma swap_norm_res c0 s r s1 : is_norm r -> swap_norm c0 s r s1 -> swap_res c0 s r s1.
Proof. intros Hn H; destruct r as [[]|]; cbn in Hn; try contradiction; exact H. Qed.

Lemma swap_norm_map (P Q : prog a) (s s0 s1 : state) r1 r (f : state -> state) :
  stack s0 = stack s -> handler s0 = handler s ->
  (forall t st, f (set_stack st t) = set_stack st (f t)) ->
  (forall t, stack (f t) = stack t) -> (forall t, handler (f t) = handler t) ->
  is_norm r -> swap_norm Q s0 r1 s1 ->
  (forall xs st, s_val_eq (stack s) xs -> evaluate (Q, set_stack xs s0) = (r1, set_stack st s1) ->
     evaluate (P, set_stack xs s) = (r, set_stack st (f s1))) ->
  swap_res P s r (f s1).
Proof.
  intros Hs Hh Fc Fs Fh Hn [K [Hh1 V]] Hev; apply swap_norm_res; [exact Hn|].
  unfold swap_norm; rewrite Hs, Hh in *; rewrite Fs, Fh; repeat split; try assumption.
  intros xs Hx; destruct (V xs Hx) as (st & Hst & Hv & Hk); exists st.
  rewrite (Hev xs st Hx Hst); repeat split; assumption.
Qed.

Lemma swap_res_seq (P c1 c2 : prog a) (s s0 s1 s2 : state) r1 r (g : state -> state) :
  stack s0 = stack s -> handler s0 = handler s ->
  (forall t st, g (set_stack st t) = set_stack st (g t)) ->
  (forall t, stack (g t) = stack t) -> (forall t, handler (g t) = handler t) ->
  swap_norm c1 s0 r1 s1 -> swap_res c2 (g s1) r s2 ->
  (forall xs st, s_val_eq (stack s) xs -> evaluate (c1, set_stack xs s0) = (r1, set_stack st s1) ->
     evaluate (P, set_stack xs s) = evaluate (c2, set_stack st (g s1))) ->
  swap_res P s r s2.
Proof.
  intros Hs Hh Gc Gs Gh H1 H2 Hev.
  unfold swap_norm in H1; rewrite Hs, Hh in H1; destruct H1 as (K1 & Hh1 & V1).
  unfold swap_res in *; rewrite Gs, Gh in H2.
  destruct r as [[x ys|x y|k|k| | |e|]|]; try exact Logic.I;
    try (destruct H2 as (K2 & Hh2 & V2); split; [eapply s_key_eq_trans; split; eassumption|];
         split; [congruence|];
         intros xs Hx; destruct (V1 xs Hx) as (st & Hst & Hv & Hk);
         destruct (V2 st Hv) as (st' & Hst' & Hv' & Hk'); exists st';
         rewrite (Hev xs st Hx Hst), Hst'; repeat split; [assumption|];
         eapply s_key_eq_trans; split; eassumption; fail);
    try (destruct H2 as (K2 & Hh2 & V2); repeat split; try assumption;
         intros xs Hx; destruct (V1 xs Hx) as (st & Hst & Hv & Hk);
         rewrite (Hev xs st Hx Hst); apply V2, Hv; fail).
  destruct H2 as (Hlt & e0 & e & n & ls & m & lss & HL & Hm & [Hf Hloc] & Hk2 & Hhd & V2).
  assert (Hlen : LENGTH (stack s1) = LENGTH (stack s)) by (symmetry; apply s_key_eq_length, K1).
  rewrite Hh1 in Hlt, HL, V2; split; [rewrite <- Hlen; exact Hlt|].
  destruct (s_key_eq_LASTN_exists (stack s1) (stack s) (handler s + 1) m e0 e n ls
              (conj (proj1 (s_key_eq_sym _ _) K1) HL)) as (e_s & ls_s & HLs & Hfe & Hkl).
  exists e0, e_s, n, ls_s, m, lss; repeat split; try assumption.
  - congruence.
  - eapply s_key_eq_trans; split; eassumption.
  - intros xs e0' e' ls' [Hl Hv].
    destruct (V1 xs Hv) as (st & Hst & Hv1 & Hk1).
    destruct (s_key_eq_LASTN_exists xs st (handler s + 1) m e0' e' n ls' (conj Hk1 Hl))
      as (e'' & ls'' & HL2 & Hfe2 & Hkl2).
    destruct (V2 st e0' e'' ls'' (conj HL2 Hv1)) as (st2 & locs & He & (lss' & Hf' & Hl' & Hsnd) & Hsv & Hsk).
    exists st2, locs; rewrite (Hev xs st Hv Hst), He; repeat split; try assumption.
    + exists lss'; repeat split; congruence.
    + eapply s_key_eq_trans; split; eassumption.
Qed.

Lemma push_env_set_stack envs (h : option (N * (prog a * (N * N)))) (s : state) xs :
  s_val_eq (stack s) xs ->
  exists f, stack (push_env envs h s) = f :: stack s /\
    push_env envs h (set_stack xs s) = set_stack (f :: xs) (push_env envs h s) /\
    (h = NONE -> exists m l0 l, f = StackFrame m l0 l NONE).
Proof.
  intros Hv. destruct h as [[hn [hp [l1 l2]]]|]; unfold push_env; cbn [permute set_stack stack handler];
    destruct (env_to_list (SND envs) (permute s)) as [l p] eqn:E; eexists;
    (split; [reflexivity|]); (split; [|try discriminate; intros _; eauto]);
    cbn [stack set_stack stack_max handler]; rewrite <- (s_val_append_eq_stack_size _ _ _ Hv);
    try rewrite <- (s_val_eq_length _ _ Hv); reflexivity.
Qed.

Lemma pop_env_set_stack_cons (t : state) f r r' :
  stack t = f :: r -> pop_env (set_stack (f :: r') t) = OPTION_MAP (set_stack r') (pop_env t).
Proof.
  intros H; unfold pop_env; cbn [stack set_stack]; rewrite H.
  destruct f as [m e0 e [[n x]|]]; reflexivity.
Qed.

Lemma pop_env_none_frame (t t' : state) m e0 e r :
  stack t = StackFrame m e0 e NONE :: r -> pop_env t = SOME t' -> stack t' = r /\ handler t' = handler t.
Proof. intros H Hp; unfold pop_env in Hp; rewrite H in Hp; injection Hp as <-; split; reflexivity. Qed.

Lemma alloc_swap w names (s s1 : state) r :
  alloc w names s = (r, s1) ->
  match r with
  | NONE => s_key_eq (stack s) (stack s1) /\ handler s1 = handler s /\
      (forall xs, s_val_eq (stack s) xs -> exists st, alloc w names (set_stack xs s) = (r, set_stack st s1) /\
                  s_val_eq (stack s1) st /\ s_key_eq xs st)
  | SOME NotEnoughSpace => stack s1 = [] /\ locals s1 = LN /\
      (forall xs, s_val_eq (stack s) xs -> alloc w names (set_stack xs s) = (r, s1))
  | SOME Error => True
  | _ => False
  end.
Proof.
  intros H. pose proof H as H0. unfold alloc in H.
  destruct (cut_envs names (locals s)) as [envs|] eqn:Ec; [|injection H as <- <-; exact Logic.I].
  destruct (gc (push_env envs NONE (set_store stackLang.AllocSize (Word w) s))) as [s3|] eqn:Eg;
    [|injection H as <- <-; exact Logic.I].
  destruct (pop_env s3) as [s4|] eqn:Ep; [|injection H as <- <-; exact Logic.I].
  destruct (get_store stackLang.AllocSize s4) as [w'|] eqn:Es; [|injection H as <- <-; exact Logic.I].
  set (X := push_env envs NONE (set_store stackLang.AllocSize (Word w) s)) in *.
  assert (Hsw : forall xs, s_val_eq (stack s) xs ->
            exists z, alloc w names (set_stack xs s) =
              (match has_space w' s4 with
               | NONE => (SOME Error, set_stack z s4)
               | SOME true => (NONE, set_stack z s4)
               | SOME false => (SOME NotEnoughSpace, flush_state true s4) end) /\
              s_val_eq (stack s4) z /\ s_key_eq xs z).
  { intros xs Hx.
    destruct (push_env_set_stack envs NONE (set_store stackLang.AllocSize (Word w) s) xs Hx)
      as (f & Hst & Hpush & Hf). destruct (Hf eq_refl) as (fm & fl0 & fl & ->).
    pose proof (gc_s_key_eq _ _ Eg) as Hk3. fold X in Hst, Hpush, Hk3. rewrite Hst in Hk3.
    destruct (stack s3) as [|f3 r3] eqn:E3; cbn [s_key_eq] in Hk3; [contradiction|].
    destruct Hk3 as [Hkr Hkf].
    assert (Hvx : s_val_eq (stack X) (StackFrame fm fl0 fl NONE :: xs))
      by (rewrite Hst; cbn [s_val_eq]; split; [exact Hx|apply s_frame_val_eq_refl]).
    destruct (gc_s_val_eq X _ s3 (conj Hvx Eg)) as (z & Hgz & Hvz & Hkz).
    rewrite E3 in Hvz.
    destruct z as [|fz zr]; cbn [s_val_eq s_key_eq] in Hvz, Hkz; [contradiction|].
    destruct Hvz as [Hvr Hvf], Hkz as [Hkzr Hkzf].
    assert (Hf3 : f3 = fz).
    { apply s_frame_val_and_key_eq; split; [exact Hvf|].
      eapply s_frame_key_eq_trans; split; [apply s_frame_key_eq_sym; exact Hkf|apply s_frame_key_eq_sym; exact Hkzf]. }
    subst fz.
    exists zr. unfold alloc. rewrite locals_set_stack, Ec.
    rewrite set_store_set_stack, Hpush, Hgz. cbn [OPTION_MAP option_map].
    rewrite (pop_env_set_stack_cons s3 f3 r3 zr E3), Ep. cbn [OPTION_MAP option_map].
    autorewrite with wds. rewrite Es. rewrite has_space_set_stack.
    destruct f3 as [m3 e03 e3 [h3|]]; cbn in Hkf; [contradiction|].
    destruct (pop_env_none_frame _ _ _ _ _ _ E3 Ep) as [Hs4 _].
    split; [destruct (has_space w' s4) as [[]|]; reflexivity|].
    rewrite Hs4; split; [exact Hvr|apply s_key_eq_sym, Hkzr]. }
  assert (Hfacts : s_key_eq (stack s) (stack s4) /\ handler s4 = handler s).
  { destruct (push_env_set_stack envs NONE (set_store stackLang.AllocSize (Word w) s) (stack s) (s_val_eq_refl _))
      as (f & Hst & _ & Hf). destruct (Hf eq_refl) as (fm & fl0 & fl & ->).
    pose proof (gc_s_key_eq _ _ Eg) as Hk3. fold X in Hst, Hk3. rewrite Hst in Hk3.
    destruct (stack s3) as [|f3 r3] eqn:E3; cbn [s_key_eq] in Hk3; [contradiction|].
    destruct Hk3 as [Hkr Hkf].
    destruct f3 as [m3 e03 e3 [h3|]]; cbn in Hkf; [contradiction|].
    destruct (pop_env_none_frame _ _ _ _ _ _ E3 Ep) as [Hs4 Hh4].
    rewrite Hs4, Hh4; split; [exact Hkr|].
    pose proof (gc_const _ _ Eg) as Hgc.
    pose proof (push_env_const envs NONE (set_store stackLang.AllocSize (Word w) s)) as Hpc.
    destr_conj. unfold X in *. cbn [handler set_store set_store_field] in *. congruence. }
  destruct (has_space w' s4) as [[]|] eqn:Eh; injection H as <- <-.
  - destruct Hfacts as [Hk Hh]; split; [exact Hk|]; split; [exact Hh|].
    intros xs Hx; destruct (Hsw xs Hx) as (z & Hz & Hv & Hk'); exists z; rewrite Hz; auto.
  - split; [reflexivity|]; split; [reflexivity|].
    intros xs Hx; destruct (Hsw xs Hx) as (z & Hz & _); exact Hz.
  - exact Logic.I.
Qed.

Definition push_hdl (h : option (N * (prog a * (N * N)))) (hs : N) : option (N * (N * N)) :=
  match h with NONE => NONE | SOME (_, (_, (l1, l2))) => SOME (hs, (l1, l2)) end.

Lemma push_env_set_stack2 envs (h : option (N * (prog a * (N * N)))) (s : state) xs :
  s_val_eq (stack s) xs ->
  exists l, stack (push_env envs h s) =
              StackFrame (locals_size s) (toAList (FST envs)) l (push_hdl h (handler s)) :: stack s /\
    push_env envs h (set_stack xs s) =
      set_stack (StackFrame (locals_size s) (toAList (FST envs)) l (push_hdl h (handler s)) :: xs)
        (push_env envs h s) /\
    handler (push_env envs h s) = match h with NONE => handler s | SOME _ => LENGTH (stack s) end.
Proof.
  intros Hv. destruct h as [[hn [hp [l1 l2]]]|]; unfold push_env; cbn [permute set_stack stack handler];
    destruct (env_to_list (SND envs) (permute s)) as [l p] eqn:E; exists l;
    (split; [reflexivity|]); (split; [|reflexivity]);
    cbn [stack set_stack stack_max handler locals_size]; rewrite <- (s_val_append_eq_stack_size _ _ _ Hv);
    try rewrite <- (s_val_eq_length _ _ Hv); reflexivity.
Qed.

Lemma call_env_set_stack x ss (s : state) xs :
  s_val_eq (stack s) xs -> call_env x ss (set_stack xs s) = set_stack xs (call_env x ss s).
Proof. intros Hv; unfold call_env; cbn [stack set_stack]; rewrite <- (s_val_eq_stack_size _ _ Hv); reflexivity. Qed.

Lemma TAKE_app_le {A} n (l1 l2 : list A) : (N.to_nat n <= length l1)%nat -> TAKE n (l1 ++ l2) = TAKE n l1.
Proof.
  revert n; induction l1 as [|x l1 IH]; intros n Hn; cbn in *.
  - assert (n = 0) by lia; subst; destruct l2; reflexivity.
  - destruct (n =? 0) eqn:E; [reflexivity|]. apply N.eqb_neq in E. rewrite IH by lia; reflexivity.
Qed.

Lemma LASTN_cons_le {A} n (x : A) l : n <= LENGTH l -> LASTN n (x :: l) = LASTN n l.
Proof.
  intros Hn; unfold LASTN; cbn [rev]. rewrite TAKE_app_le; [reflexivity|].
  rewrite length_rev; rewrite LENGTH_length in Hn; lia.
Qed.

Lemma set_locals_handler_eta (t : state) st l h :
  locals t = l -> handler t = h -> set_locals l (set_handler h (set_stack st t)) = set_stack st t.
Proof. intros <- <-; destruct t; reflexivity. Qed.

Lemma swap_res_seq' (P c2 : prog a) (s s1 s2 : state) r (R : list (stack_frame a) -> list (stack_frame a) -> Prop) :
  s_key_eq (stack s) (stack s1) -> handler s1 = handler s ->
  (forall xs, s_val_eq (stack s) xs -> exists st, R xs st /\ s_val_eq (stack s1) st /\ s_key_eq xs st) ->
  swap_res c2 s1 r s2 ->
  (forall xs st, s_val_eq (stack s) xs -> R xs st ->
     evaluate (P, set_stack xs s) = evaluate (c2, set_stack st s1)) ->
  swap_res P s r s2.
Proof.
  intros K1 Hh1 V1 H2 Hev.
  unfold swap_res in *.
  destruct r as [[x ys|x y|k|k| | |e|]|]; try exact Logic.I;
    try (destruct H2 as (K2 & Hh2 & V2); split; [eapply s_key_eq_trans; split; eassumption|];
         split; [congruence|];
         intros xs Hx; destruct (V1 xs Hx) as (st & Hst & Hv & Hk);
         destruct (V2 st Hv) as (st' & Hst' & Hv' & Hk'); exists st';
         rewrite (Hev xs st Hx Hst), Hst'; repeat split; [assumption|];
         eapply s_key_eq_trans; split; eassumption; fail);
    try (destruct H2 as (K2 & Hh2 & V2); repeat split; try assumption;
         intros xs Hx; destruct (V1 xs Hx) as (st & Hst & Hv & Hk);
         rewrite (Hev xs st Hx Hst); apply V2, Hv; fail).
  destruct H2 as (Hlt & e0 & e & n & ls & m & lss & HL & Hm & [Hf Hloc] & Hk2 & Hhd & V2).
  assert (Hlen : LENGTH (stack s1) = LENGTH (stack s)) by (symmetry; apply s_key_eq_length, K1).
  rewrite Hh1 in Hlt, HL, V2; split; [rewrite <- Hlen; exact Hlt|].
  destruct (s_key_eq_LASTN_exists (stack s1) (stack s) (handler s + 1) m e0 e n ls
              (conj (proj1 (s_key_eq_sym _ _) K1) HL)) as (e_s & ls_s & HLs & Hfe & Hkl).
  exists e0, e_s, n, ls_s, m, lss; repeat split; try assumption.
  - congruence.
  - eapply s_key_eq_trans; split; eassumption.
  - intros xs e0' e' ls' [Hl Hv].
    destruct (V1 xs Hv) as (st & Hst & Hv1 & Hk1).
    destruct (s_key_eq_LASTN_exists xs st (handler s + 1) m e0' e' n ls' (conj Hk1 Hl))
      as (e'' & ls'' & HL2 & Hfe2 & Hkl2).
    destruct (V2 st e0' e'' ls'' (conj HL2 Hv1)) as (st2 & locs & He & (lss' & Hf' & Hl' & Hsnd) & Hsv & Hsk).
    exists st2, locs; rewrite (Hev xs st Hv Hst), He; repeat split; try assumption.
    + exists lss'; repeat split; congruence.
    + eapply s_key_eq_trans; split; eassumption.
Qed.

Lemma evaluate_stack_swap_G : forall (x : prog a * state) r s1,
  evaluate x = (r, s1) -> swap_res (fst x) (snd x) r s1.
Proof.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s1 H; cbn [fst snd].
  pose proof H as H0.
  rewrite evaluate_eqn in H; destruct p; cbn [evaluate_body] in H.
  all: try (unfold share_inst, sh_mem_set_var, sh_mem_load, sh_mem_load_byte, sh_mem_load16, sh_mem_load32,
              sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32 in H;
            split_H H; leaf H; try exact Logic.I;
            repeat match goal with E : ?v = _ |- _ => is_var v; subst v end;
            try (match goal with E : mem_store _ _ _ = SOME _ |- _ =>
                     let Hm := fresh in pose proof (mem_store_const _ _ _ _ E) as Hm; destr_conj end);
            try (match goal with E : inst _ _ = SOME _ |- _ =>
                     let Hm := fresh in pose proof (inst_const_full _ _ _ E) as Hm; destr_conj end);
            sw_simple; fail).
  - (* MustTerminate *)
    destruct (termdep s =? 0) eqn:Et; [injection H as <- <-; exact Logic.I|].
    destruct (evaluate (p, set_termdep (termdep s - 1) (set_clock (MustTerminate_limit a) s)))
      as [r1 s2] eqn:E1.
    destruct (bool_decide (r1 = SOME TimeOut)) eqn:Eb; [injection H as <- <-; exact Logic.I|].
    injection H as <- <-.
    pose proof (IH (p, set_termdep (termdep s - 1) (set_clock (MustTerminate_limit a) s)) ltac:(wd_eval_lt) r1 s2 E1) as Hi; cbn [fst snd] in Hi.
    apply (swap_res_map (MustTerminate p) p s (set_termdep (termdep s - 1) (set_clock (MustTerminate_limit a) s)) s2 r1 (fun t => set_termdep (termdep s) (set_clock (clock s) t)));
      try reflexivity; try exact Hi.
    intros xs t' Hx He. rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with wds.
    rewrite Et; cbn beta iota zeta.
    change (set_termdep (termdep s - 1) (set_clock (MustTerminate_limit a) (set_stack xs s)))
      with (set_stack xs (set_termdep (termdep s - 1) (set_clock (MustTerminate_limit a) s))).
    rewrite He; cbn beta iota zeta; rewrite Eb; reflexivity.
  - (* Call *)
    rename o into ret, o0 into dest, l into args, o1 into handler0.
    destruct (get_vars args s) as [xs0|] eqn:Eg; [|injection H as <- <-; exact Logic.I].
    cbn beta iota zeta in H.
    destruct (bad_dest_args dest args) eqn:Ebd; [injection H as <- <-; exact Logic.I|].
    destruct (find_code dest (add_ret_loc ret xs0) (code s) (state_stack_size s)) as [[args1 [prg ss]]|] eqn:Ef;
      [|injection H as <- <-; exact Logic.I].
    cbn beta iota zeta in H.
    Local Ltac call_pre Eg Ebd Ef :=
      rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with wds; rewrite Eg; cbn beta iota zeta;
      rewrite Ebd, Ef; cbn beta iota zeta.
    destruct ret as [[n [names [rh [l1 l2]]]]|].
    2:{ (* tail call *)
      destruct (⌜handler0 = NONE⌝) eqn:Eh; [|injection H as <- <-; exact Logic.I].
      destruct (clock s =? 0) eqn:Ez.
      - injection H as <- <-. unfold swap_res. split; [reflexivity|]. split; [reflexivity|].
        intros xs Hx. call_pre Eg Ebd Ef. rewrite Eh, Ez. reflexivity.
      - destruct (evaluate (prg, call_env args1 ss (dec_clock s))) as [r1 s2] eqn:E1.
        pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
        destruct (bad_fun_return r1) eqn:Eb; [injection H as <- <-; exact Logic.I|].
        injection H as <- <-.
        pose proof (IH (prg, call_env args1 ss (dec_clock s)) ltac:(wd_eval_lt) r1 s2 E1) as Hi.
        cbn [fst snd] in Hi.
        apply (swap_res_map _ prg s (call_env args1 ss (dec_clock s)) s2 r1 (fun t => t));
          try (intros; reflexivity); try exact Hi.
        intros xs t' Hx He. call_pre Eg Ebd Ef. rewrite Eh, Ez; cbn beta iota zeta.
        rewrite (call_env_set_stack _ _ (dec_clock s) xs Hx), He. cbn beta iota zeta. rewrite Eb. reflexivity. }
    destruct (⌜domain (FST names) = {}⌝ || negb (ALL_DISTINCT n)) eqn:Ed; [injection H as <- <-; exact Logic.I|].
    destruct (cut_envs names (locals s)) as [envs|] eqn:Ec; [|injection H as <- <-; exact Logic.I].
    destruct (clock s =? 0) eqn:Ez.
    { injection H as <- <-. unfold swap_res. split; [reflexivity|]. split; [reflexivity|].
      intros xs Hx. call_pre Eg Ebd Ef. rewrite Ed, Ec, Ez; cbn beta iota zeta.
      destruct (push_env_set_stack2 envs handler0 s xs Hx) as (fl & Hs2 & Hp2 & _). rewrite Hp2.
      rewrite call_env_set_stack;
        [autorewrite with wds; reflexivity|rewrite Hs2; cbn [s_val_eq]; split; [exact Hx|apply s_frame_val_eq_refl]]. }
    rewrite fix_clock_evaluate in H.
    destruct (push_env_set_stack2 envs handler0 (dec_clock s) (stack s) (s_val_eq_refl _)) as (fl & Hpst & _ & Hph).
    set (f := StackFrame (locals_size (dec_clock s)) (toAList (FST envs)) fl (push_hdl handler0 (handler (dec_clock s)))) in *.
    assert (Hcsw : forall xs, s_val_eq (stack s) xs ->
              call_env args1 ss (push_env envs handler0 (set_stack xs (dec_clock s))) =
              set_stack (f :: xs) (call_env args1 ss (push_env envs handler0 (dec_clock s)))).
    { intros xs Hx. destruct (push_env_set_stack2 envs handler0 (dec_clock s) xs Hx) as (fl' & Hpst' & Hp' & _).
      rewrite Hpst in Hpst'. injection Hpst' as <-. rewrite Hp'. apply call_env_set_stack.
      rewrite Hpst. cbn [s_val_eq]. split; [exact Hx|apply s_frame_val_eq_refl]. }
    set (cs := call_env args1 ss (push_env envs handler0 (dec_clock s))) in *.
    assert (Hcs : stack cs = f :: stack s) by exact Hpst.
    assert (Hccs : clock cs = clock s - 1 /\ termdep cs = termdep s)
      by (unfold cs; autorewrite with wdc; split; reflexivity).
    destruct Hccs as [Hccs Htcs].
    assert (Hhcs : handler cs = match handler0 with NONE => handler s | SOME _ => LENGTH (stack s) end)
      by exact Hph.
    destruct (evaluate (prg, cs)) as [r1 s2] eqn:E1.
    pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
    pose proof (IH (prg, cs) ltac:(unfold cs; wd_eval_lt) r1 s2 E1) as Hi1; cbn [fst snd] in Hi1.
    Local Ltac call_post Ed Ec Ez Hcsw Hx :=
      rewrite Ed, Ec, Ez; cbn beta iota zeta; rewrite fix_clock_evaluate, (Hcsw _ Hx).
    assert (Hvf : forall xs, s_val_eq (stack s) xs -> s_val_eq (stack cs) (f :: xs))
      by (intros xs Hx; rewrite Hcs; cbn [s_val_eq]; split; [exact Hx|apply s_frame_val_eq_refl]).
    destruct r1 as [[x ys|x y|k|k| | |e|]|]; try (injection H as <- <-; exact Logic.I).
    + (* Result *)
      destruct (negb ⌜x = Loc l1 l2⌝ || negb (LENGTH ys =? LENGTH n)) eqn:Ex; [injection H as <- <-; exact Logic.I|].
      destruct (pop_env s2) as [s3|] eqn:Ep; [|injection H as <- <-; exact Logic.I].
      destruct (⌜domain (locals s3) = domain (FST envs) UNION domain (SND envs)⌝) eqn:Edom;
        [|injection H as <- <-; exact Logic.I].
      pose proof (IH (rh, set_vars n ys s3) ltac:(wd_eval_lt) r s1 H) as Hi2; cbn [fst snd] in Hi2.
      destruct Hi1 as (K1 & Hh1 & V1). rewrite Hcs in K1.
      destruct (stack s2) as [|f2 r2] eqn:Es2; cbn [s_key_eq] in K1; [contradiction|].
      destruct K1 as [Kr Kf].
      assert (Hs3 : stack s3 = r2 /\ handler s3 = handler s).
      { unfold pop_env in Ep; rewrite Es2 in Ep.
        subst f; change (handler (dec_clock s)) with (handler s) in *;
          change (locals_size (dec_clock s)) with (locals_size s) in *.
        destruct handler0 as [[? [? [? ?]]]|]; cbn [push_hdl] in Kf, Hhcs;
          destruct f2 as [m2 e02 e2 [[hh hx]|]]; cbn [s_frame_key_eq] in Kf; destr_conj; try contradiction;
          injection Ep as <-; cbn [stack handler set_handler set_locals_size set_stack set_locals];
          (split; [reflexivity|]); congruence. }
      destruct Hs3 as [Hs3 Hh3].
      apply (swap_res_seq' _ rh s (set_vars n ys s3) s1 r
               (fun xs st => evaluate (prg, set_stack (f :: xs) cs) = (SOME (Result x ys), set_stack (f2 :: st) s2)));
        try assumption.
      * exact (ltac:(cbn [stack set_vars set_locals]; rewrite Hs3; exact Kr)).
      * intros xs Hx. destruct (V1 (f :: xs) (Hvf xs Hx)) as (st & Hst & Hv & Hk).
        destruct st as [|fz zr]; cbn [s_val_eq s_key_eq] in Hv, Hk; [contradiction|].
        destruct Hv as [Hvr Hvf'], Hk as [Hkr Hkf].
        assert (fz = f2) as ->.
        { symmetry; apply s_frame_val_and_key_eq; split; [exact Hvf'|].
          eapply s_frame_key_eq_trans; split; [apply s_frame_key_eq_sym; exact Kf|exact Hkf]. }
        exists zr; split; [exact Hst|]. cbn [stack set_vars set_locals]; rewrite Hs3.
        split; [exact Hvr|exact Hkr].
      * intros xs st Hx Hst. call_pre Eg Ebd Ef. call_post Ed Ec Ez Hcsw Hx. rewrite Hst; cbn beta iota zeta.
        rewrite Ex. rewrite (pop_env_set_stack_cons s2 f2 r2 st Es2), Ep. cbn [OPTION_MAP option_map].
        autorewrite with wds. rewrite Edom. reflexivity.
    + (* Exception *)
      destruct handler0 as [[hn [hp [hl1 hl2]]]|].
      * destruct (negb ⌜x = Loc hl1 hl2⌝) eqn:Ex; [injection H as <- <-; exact Logic.I|].
        destruct (⌜domain (locals s2) = domain (FST envs) UNION domain (SND envs)⌝) eqn:Edom;
          [|injection H as <- <-; exact Logic.I].
        pose proof (IH (hp, set_var hn y s2) ltac:(wd_eval_lt) r s1 H) as Hi2; cbn [fst snd] in Hi2.
        destruct Hi1 as (Hlt & e0 & e & nn & ls & m & lss & HL & Hm & [Hfe Hloc] & Hk & Hhd & V).
        rewrite Hhcs, Hcs in HL. rewrite Hhcs in V.
        assert (HLf : forall xs, s_val_eq (stack s) xs -> LASTN (LENGTH (stack s) + 1) (f :: xs) = f :: xs).
        { intros xs Hx; apply LASTN_LENGTH_cond. rewrite (s_val_eq_length _ _ Hx), !LENGTH_length; cbn; lia. }
        rewrite (HLf _ (s_val_eq_refl _)) in HL. injection HL as Hfm He0 He Hnn Hls.
        subst ls. rewrite <- Hnn in Hhd. cbn in Hhd.
        apply (swap_res_seq' _ hp s (set_var hn y s2) s1 r
                 (fun xs st => evaluate (prg, set_stack (f :: xs) cs) = (SOME (Exception x y), set_stack st s2)));
          try assumption.
        -- cbn [stack set_var set_locals]. apply s_key_eq_sym, Hk.
        -- intros xs Hx.
           assert (Hfeq : f = StackFrame m e0 e (SOME nn)) by (unfold f; cbn [push_hdl]; change (locals_size (dec_clock s)) with (locals_size s); change (handler (dec_clock s)) with (handler s); congruence).
           destruct (V (f :: xs) e0 e xs) as (st & locs & Hst & (lss' & Hf' & Hl' & Hsnd) & Hsv & Hsk);
             [split; [rewrite (HLf xs Hx), Hfeq; reflexivity|exact (Hvf xs Hx)]|].
           exists st. split; [|split; [exact Hsv|exact Hsk]].
           rewrite Hst. f_equal. rewrite <- Hnn; cbn.
           assert (lss = lss') as <- by (apply map_fst_snd_eq; congruence).
           apply set_locals_handler_eta; [congruence|]. rewrite Hhd; reflexivity.
        -- intros xs st Hx Hst. call_pre Eg Ebd Ef. call_post Ed Ec Ez Hcsw Hx. rewrite Hst; cbn beta iota zeta.
           rewrite Ex. autorewrite with wds. rewrite Edom. reflexivity.
      * injection H as <- <-.
        destruct Hi1 as (Hlt & e0 & e & nn & ls & m & lss & HL & Hm & [Hfe Hloc] & Hk & Hhd & V).
        rewrite Hhcs, Hcs in Hlt, HL. rewrite Hhcs in V.
        assert (Hle : handler s + 1 <= LENGTH (stack s)).
        { rewrite LENGTH_length in Hlt |- *; cbn [length] in Hlt.
          destruct (N.eq_dec (handler s + 1) (N.of_nat (S (length (stack s))))) as [Heq|Hne]; [|lia].
          exfalso. rewrite (LASTN_LENGTH_cond (handler s + 1) (f :: stack s)) in HL
            by (rewrite LENGTH_length; cbn [length]; exact Heq).
          injection HL as _ _ _ Hn _. subst f; discriminate Hn. }
        rewrite LASTN_cons_le in HL by exact Hle.
        unfold swap_res. split; [rewrite LENGTH_length in Hle |- *; lia|].
        exists e0, e, nn, ls, m, lss. repeat split; try assumption.
        intros xs e0' e' ls' [Hl Hx].
        assert (Hle' : handler s + 1 <= LENGTH xs) by (rewrite <- (s_val_eq_length _ _ Hx); exact Hle).
        destruct (V (f :: xs) e0' e' ls' (conj (eq_trans (LASTN_cons_le _ _ _ Hle') Hl) (Hvf xs Hx)))
          as (st & locs & Hst & Hlss & Hsv & Hsk).
        exists st, locs. split; [|split; [exact Hlss|split; assumption]].
        call_pre Eg Ebd Ef. call_post Ed Ec Ez Hcsw Hx. rewrite Hst; reflexivity.
    + (* TimeOut *)
      injection H as <- <-. destruct Hi1 as (H1 & H2 & H3). unfold swap_res; repeat split; try assumption.
      intros xs Hx. call_pre Eg Ebd Ef. call_post Ed Ec Ez Hcsw Hx. rewrite (H3 _ (Hvf xs Hx)); reflexivity.
    + (* NotEnoughSpace *)
      injection H as <- <-. destruct Hi1 as (H1 & H2 & H3). unfold swap_res; repeat split; try assumption.
      intros xs Hx. call_pre Eg Ebd Ef. call_post Ed Ec Ez Hcsw Hx. rewrite (H3 _ (Hvf xs Hx)); reflexivity.
    + (* FinalFFI *)
      injection H as <- <-. destruct Hi1 as (H1 & H2 & H3). unfold swap_res; repeat split; try assumption.
      intros xs Hx. call_pre Eg Ebd Ef. call_post Ed Ec Ez Hcsw Hx. rewrite (H3 _ (Hvf xs Hx)); reflexivity.
  - (* Seq *)
    rewrite fix_clock_evaluate in H.
    destruct (evaluate (p1, s)) as [r1 s2] eqn:E1.
    pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
    pose proof (IH (p1, s) ltac:(wd_eval_lt) r1 s2 E1) as Hi1; cbn [fst snd] in Hi1.
    destruct (bool_decide (r1 = NONE)) eqn:Eb.
    + pose proof Eb as Eb'; apply bool_decide_spec in Eb'; subst r1.
      pose proof (IH (p2, s2) ltac:(wd_eval_lt) r s1 H) as Hi2; cbn [fst snd] in Hi2.
      apply (swap_res_seq _ p1 p2 s s s2 s1 NONE r (fun t => t)); try reflexivity; try assumption;
        try (apply swap_res_norm; [exact Logic.I|exact Hi1]).
      intros xs st Hx He. rewrite evaluate_eqn; cbn [evaluate_body]; rewrite fix_clock_evaluate, He.
      cbn beta iota zeta; rewrite Eb; reflexivity.
    + injection H as <- <-.
      apply (swap_res_map _ p1 s s s2 r1 (fun t => t)); try reflexivity; try assumption.
      intros xs t' Hx He. rewrite evaluate_eqn; cbn [evaluate_body]; rewrite fix_clock_evaluate, He.
      cbn beta iota zeta; rewrite Eb; reflexivity.
  - (* If *)
    split_H H; try (injection H as <- <-; exact Logic.I);
      [pose proof (IH (p1, s) ltac:(wd_eval_lt) r s1 H) as Hi;
       apply (swap_res_map (If c0 n r0 p1 p2) p1 s s s1 r (fun t => t))
      |pose proof (IH (p2, s) ltac:(wd_eval_lt) r s1 H) as Hi;
       apply (swap_res_map (If c0 n r0 p1 p2) p2 s s s1 r (fun t => t))];
      try reflexivity; try exact Hi;
      intros xs t' Hx He; rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with wds; rw_ctor; first [exact He|reflexivity].
  - (* Loop *)
    rename s0 into nm1, s2 into nm2.
    destruct (cut_state (nm1, LN) s) as [s3|] eqn:Ec; [|injection H as <- <-; exact Logic.I].
    cbn beta iota zeta in H. rewrite fix_clock_evaluate in H.
    destruct (cut_state_const _ _ _ Ec) as [l ->].
    destruct (evaluate (p, set_locals l s)) as [r1 s4] eqn:E1.
    pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
    pose proof (cut_state_clock _ _ _ Ec) as Hc0.
    pose proof (IH (p, set_locals l s) ltac:(wd_eval_lt) r1 s4 E1) as Hi1; cbn [fst snd] in Hi1.
    assert (Hcut : forall xs, cut_state (nm1, LN) (set_stack xs s) = SOME (set_stack xs (set_locals l s)))
      by (intros xs; rewrite cut_state_set_stack, Ec; reflexivity).
    Local Ltac loop_pre Hcut E :=
      rewrite evaluate_eqn; cbn [evaluate_body]; rewrite Hcut; cbn beta iota zeta;
      rewrite fix_clock_evaluate, E; cbn beta iota zeta.
    destruct (cont_loop r1) eqn:Ecl.
    + assert (Hn1 : is_norm r1)
        by (destruct r1 as [[]|]; cbn in Ecl |- *; try discriminate; exact Logic.I).
      pose proof (swap_res_norm _ _ _ _ Hn1 Hi1) as N1.
      destruct (clock s4 =? 0) eqn:Ez.
      * injection H as <- <-.
        unfold swap_res. split; [reflexivity|]. split; [reflexivity|].
        intros xs Hx. destruct N1 as (_ & _ & V1). destruct (V1 xs Hx) as (st & Hst & _).
        loop_pre Hcut Hst. rewrite Ecl. autorewrite with wds. rewrite Ez. reflexivity.
      * pose proof (IH (STOP (Loop nm1 p nm2), dec_clock s4) ltac:(wd_eval_lt) r s1 H) as Hi2.
        cbn [fst snd] in Hi2.
        apply (swap_res_seq _ p (STOP (Loop nm1 p nm2)) s (set_locals l s) s4 s1 r1 r dec_clock);
          try (intros; reflexivity); try assumption.
        intros xs st Hx He. loop_pre Hcut He. rewrite Ecl. autorewrite with wds. rewrite Ez. reflexivity.
    + destruct (bool_decide (r1 = SOME (Break 0))) eqn:Eb.
      * destruct (cut_state (nm2, LN) s4) as [s5|] eqn:Ec2; [|injection H as <- <-; exact Logic.I].
        injection H as <- <-.
        pose proof Eb as Eb'; apply bool_decide_spec in Eb'; subst r1.
        destruct (cut_state_const _ _ _ Ec2) as [l2 ->].
        apply (swap_norm_map _ p s (set_locals l s) s4 (SOME (Break 0)) NONE (set_locals l2));
          try (intros; reflexivity); try exact Logic.I;
          [apply swap_res_norm; [exact Logic.I|exact Hi1]|].
        intros xs st Hx He. loop_pre Hcut He. rewrite Ecl, Eb.
        rewrite cut_state_set_stack, Ec2; reflexivity.
      * injection H as <- <-.
        destruct r1 as [[x ys|x y|k|k| | |e|]|]; try (cbn [cont_loop] in Ecl; discriminate);
          cbn [exit_loop];
          first
            [ match goal with Hi1 : swap_res _ _ ?r1 _ |- _ =>
                apply (swap_norm_map _ p s (set_locals l s) s4 r1 _ (fun t => t)) end;
              try (intros; reflexivity); try exact Logic.I;
              [apply swap_res_norm; [exact Logic.I|exact Hi1]|];
              intros xs st Hx He; loop_pre Hcut He; rewrite Ecl, Eb; reflexivity
            | apply (swap_res_map _ p s (set_locals l s) s4 _ (fun t => t));
              try (intros; reflexivity); try exact Hi1;
              intros xs t' Hx He; loop_pre Hcut He; rewrite Ecl, Eb; reflexivity ].
  - (* Alloc *)
    destruct (get_var n s) as [[w|]|] eqn:Eg; try (injection H as <- <-; exact Logic.I).
    pose proof (alloc_swap _ _ _ _ _ H) as Ha.
    destruct r as [[]|]; try contradiction; try exact Logic.I; unfold swap_res.
    + destruct Ha as (H1 & H2 & H3); repeat split; try assumption.
      intros xs Hx; rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with wds; rewrite Eg.
      apply H3, Hx.
    + destruct Ha as (H1 & H2 & H3); repeat split; try assumption.
      intros xs Hx; rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with wds; rewrite Eg.
      apply H3, Hx.
  - (* Raise *)
    destruct (get_var n s) as [w|] eqn:Eg; [|injection H as <- <-; exact Logic.I].
    destruct (jump_exc s) as [[s2 [l1 l2]]|] eqn:Ej; [|injection H as <- <-; exact Logic.I].
    injection H as <- <-.
    pose proof Ej as Ej'; unfold jump_exc in Ej.
    destruct (handler s <? LENGTH (stack s)) eqn:Elt; [|discriminate].
    destruct (LASTN (handler s + 1) (stack s)) as [|[m e0 e [[hn [l1' l2']]|]] xs'] eqn:HL; try discriminate.
    injection Ej as <- <- <-.
    pose proof Elt as Elt'; apply N.ltb_lt in Elt'.
    unfold swap_res. split; [exact Elt'|].
    exists e0, e, (hn, (l1', l2')), xs', m, e.
    split; [exact HL|]. split; [reflexivity|]. split; [split; reflexivity|].
    split; [apply s_key_eq_refl|]. split; [reflexivity|].
    intros xs e0' e' ls' [Hl Hv].
    pose proof (s_val_eq_LASTN _ _ (handler s + 1) Hv) as HvL. rewrite HL, Hl in HvL.
    cbn [s_val_eq] in HvL. destruct HvL as [Hrest Hfr].
    apply s_frame_val_eq_def2 in Hfr. destruct Hfr as (Hsnd & _ & _).
    exists ls', (union (fromAList e') (fromAList e0')).
    split; [|split; [exists e'; repeat split; auto|split; [exact Hrest|apply s_key_eq_refl]]].
    rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with wds; rewrite Eg.
    unfold jump_exc; cbn [handler stack set_stack].
    rewrite <- (s_val_eq_length _ _ Hv), Elt, Hl. reflexivity.
Qed.

(** Stack swap theorem for [evaluate].  HOL's [case n of (a,b,c) => a] is
    [let '(a0, _) := n in a0]. *)
(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_stack_swap" *)
Theorem evaluate_stack_swap : forall (c0 : prog a) (s : state),
  match evaluate (c0, s) with
  | (SOME Error, s1) => True
  | (SOME (FinalFFI e), s1) => stack s1 = [] /\ locals s1 = LN /\
      (forall xs, s_val_eq (stack s) xs -> evaluate (c0, set_stack xs s) = (SOME (FinalFFI e), s1))
  | (SOME TimeOut, s1) => stack s1 = [] /\ locals s1 = LN /\
      (forall xs, s_val_eq (stack s) xs -> evaluate (c0, set_stack xs s) = (SOME TimeOut, s1))
  | (SOME NotEnoughSpace, s1) => stack s1 = [] /\ locals s1 = LN /\
      (forall xs, s_val_eq (stack s) xs -> evaluate (c0, set_stack xs s) = (SOME NotEnoughSpace, s1))
  | (SOME (Exception x y), s1) =>
      handler s < LENGTH (stack s) /\
      exists e0 e n ls m lss,
        LASTN (handler s + 1) (stack s) = StackFrame m e0 e (SOME n) :: ls /\
        m = locals_size s1 /\
        (MAP FST e = MAP FST lss /\ locals s1 = union (fromAList lss) (fromAList e0)) /\
        s_key_eq (stack s1) ls /\ handler s1 = (let '(a0, _) := n in a0) /\
        (forall xs e0' e' ls',
           LASTN (handler s + 1) xs = StackFrame m e0' e' (SOME n) :: ls' /\ s_val_eq (stack s) xs ->
           exists st locs,
             evaluate (c0, set_stack xs s) =
               (SOME (Exception x y),
                set_locals locs (set_handler (let '(a0, _) := n in a0) (set_stack st s1))) /\
             (exists lss', MAP FST e' = MAP FST lss' /\ locs = union (fromAList lss') (fromAList e0') /\
                           MAP SND lss = MAP SND lss') /\
             s_val_eq (stack s1) st /\ s_key_eq ls' st)
  | (res, s1) => s_key_eq (stack s) (stack s1) /\ handler s1 = handler s /\
      (forall xs, s_val_eq (stack s) xs ->
         exists st, evaluate (c0, set_stack xs s) = (res, set_stack st s1) /\
                    s_val_eq (stack s1) st /\ s_key_eq xs st)
  end.
Proof.
  intros c0 s. destruct (evaluate (c0, s)) as [r s1] eqn:E.
  pose proof (evaluate_stack_swap_G (c0, s) r s1 E) as H; cbn [fst snd] in H.

  destruct r as [[]|]; exact H.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_NONE_stack_size_const" *)
Theorem evaluate_NONE_stack_size_const : forall (p : prog a) (s t : state),
  evaluate (p, s) = (NONE, t) -> stack_size (stack t) = stack_size (stack s).
Proof.
  intros p s t H. destruct (evaluate_stack_swap_G (p, s) NONE t H) as (K & _ & _).
  symmetry; apply s_key_eq_stack_size, K.
Qed.

End Swap.
