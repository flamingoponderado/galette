(** * HOL4 [location]: source locations

    Port of [HOL/examples/formal-languages/context-free/locationScript.sml].

    - [locnrow]/[locncol] (HOL record-field syntax [l.row]/[l.col]) and
      their update functions are defined in HOL on [POSN] only; HOL
      completes the missing cases with [ARB], and so does this port.
    - [locnle]/[locsle] are used computationally (by the PEG interpreter's
      error comparison), so they are [bool]; equalities are decided with
      [decide].  The final disjunct of [locnle] only inspects [row]/[col]
      when both locations are [POSN] (the boolean operators are lazy), so the
      [ARB] cases are never evaluated.
    - [merge_list_locs] recurses on [h1 :: t] after [h1 :: h2 :: t]; it is
      defined through a structural helper and HOL's equations are the tagged
      [merge_list_locs_def].  HOL's overlapping fourth clause applies only
      when the third does not, i.e. to lists of length at least three; HOL's
      definition theorem states it so, and so does this port. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
Open Scope N_scope.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "locn" *)
Inductive locn : Type :=
| UNKNOWNpt : locn
| EOFpt : locn
| POSN : N -> N -> locn.

#[global] Instance locn_eq_dec : EqDecision locn.
Proof.
  intros [| |r1 c1] [| |r2 c2]; try (left; reflexivity); try (right; discriminate).
  destruct (decide (r1 = r2)) as [->|n]; [|right; congruence].
  destruct (decide (c1 = c2)) as [->|n]; [left; reflexivity|right; congruence].
Defined.

#[global] Instance locn_inhabited : Inhabited locn := UNKNOWNpt.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "locnrow_def" *)
Definition locnrow (l : locn) : N := match l with POSN r c => r | _ => ARB end.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "locn_rowupdate_def" *)
Definition locn_rowupdate (f : N -> N) (l : locn) : locn :=
  match l with POSN r c => POSN (f r) c | _ => ARB end.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "locncol_def" *)
Definition locncol (l : locn) : N := match l with POSN r c => c | _ => ARB end.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "locn_colupdate_def" *)
Definition locn_colupdate (f : N -> N) (l : locn) : locn :=
  match l with POSN r c => POSN r (f c) | _ => ARB end.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "locs" *)
Inductive locs : Type := Locs : locn -> locn -> locs.

#[global] Instance locs_eq_dec : EqDecision locs.
Proof.
  intros [a b] [c d]; destruct (decide (a = c)) as [->|n]; [|right; congruence].
  destruct (decide (b = d)) as [->|n]; [left; reflexivity|right; congruence].
Defined.

#[global] Instance locs_inhabited : Inhabited locs := Locs UNKNOWNpt UNKNOWNpt.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "default_loc_def" *)
Definition default_loc : locn := POSN 0 0.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "start_locs_def" *)
Definition start_locs : locs := Locs default_loc default_loc.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "unknown_loc_def" *)
Definition unknown_loc : locs := Locs UNKNOWNpt UNKNOWNpt.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "locnle_def" *)
Definition locnle (l1 l2 : locn) : bool :=
  bool_decide (l1 = l2) || bool_decide (l1 = UNKNOWNpt) || bool_decide (l2 = EOFpt) ||
  (bool_decide (l2 <> UNKNOWNpt) && bool_decide (l1 <> EOFpt) &&
   (bool_decide (locnrow l1 < locnrow l2) ||
    bool_decide (locnrow l1 = locnrow l2) && bool_decide (locncol l1 < locncol l2))).

Lemma bool_decide_false_iff (P : Prop) `{Decision P} : bool_decide P = false <-> ~ P.
Proof. unfold bool_decide; destruct (decide P); split; congruence || tauto. Qed.

(** [locnle] by cases (Galette helper). *)
Definition locnle_P (l1 l2 : locn) : Prop :=
  match l1, l2 with
  | UNKNOWNpt, _ => True
  | _, EOFpt => True
  | EOFpt, _ => False
  | _, UNKNOWNpt => False
  | POSN r1 c1, POSN r2 c2 => r1 < r2 \/ r1 = r2 /\ c1 <= c2
  end.

Lemma POSN_neq r1 c1 r2 c2 : POSN r1 c1 <> POSN r2 c2 -> r1 <> r2 \/ c1 <> c2.
Proof.
  intros h; destruct (decide (r1 = r2)) as [->|n]; [right; congruence|left; exact n].
Qed.

Lemma locnle_P_iff l1 l2 : is_true (locnle l1 l2) <-> locnle_P l1 l2.
Proof.
  unfold is_true, locnle.
  destruct l1 as [| |r1 c1], l2 as [| |r2 c2]; cbn [locnle_P locnrow locncol];
  repeat match goal with
  | |- context [bool_decide ?P] =>
      let E := fresh "E" in
      destruct (bool_decide P) eqn:E;
      [apply bool_decide_spec in E|apply bool_decide_false_iff in E];
      try (exfalso; congruence); try (exfalso; apply E; discriminate)
  end; cbn; split; intros; try discriminate; try reflexivity; try tauto;
  repeat match goal with
  | H : POSN _ _ = POSN _ _ |- _ => injection H as <- <-
  | H : POSN _ _ <> POSN _ _ |- _ => apply POSN_neq in H
  end; try lia; exfalso; lia.
Qed.

Ltac locn_simpl := repeat rewrite locnle_P_iff in *; cbn [locnle_P] in *.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "locnle_REFL" *)
Theorem locnle_REFL : forall l, locnle l l.
Proof. intros [| |r c]; locn_simpl; auto; lia. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "locnle_total" *)
Theorem locnle_total : forall l1 l2, locnle l1 l2 \/ locnle l2 l1.
Proof. intros [| |r1 c1] [| |r2 c2]; locn_simpl; auto; lia. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "locnle_ANTISYM" *)
Theorem locnle_ANTISYM : forall l1 l2, locnle l1 l2 /\ locnle l2 l1 -> l1 = l2.
Proof.
  intros [| |r1 c1] [| |r2 c2]; locn_simpl; try tauto.
  intros h; assert (r1 = r2 /\ c1 = c2) as [-> ->] by lia; reflexivity.
Qed.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "locnle_TRANS" *)
Theorem locnle_TRANS : forall l1 l2 l3, locnle l1 l2 /\ locnle l2 l3 -> locnle l1 l3.
Proof. intros [| |r1 c1] [| |r2 c2] [| |r3 c3]; locn_simpl; tauto || lia. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "locnle_end" *)
Theorem locnle_end : forall l, locnle EOFpt l <-> l = EOFpt.
Proof. intros [| |r c]; locn_simpl; split; intros; congruence || tauto. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "locnle_unknown" *)
Theorem locnle_unknown : forall l, locnle l UNKNOWNpt <-> l = UNKNOWNpt.
Proof. intros [| |r c]; locn_simpl; split; intros; congruence || tauto. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "locsle_def" *)
Definition locsle (l1 l2 : locs) : bool :=
  match l1, l2 with Locs l1 _, Locs l2 _ => locnle l1 l2 end.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "locsle_REFL" *)
Theorem locsle_REFL : forall l, locsle l l.
Proof. intros [a b]; apply locnle_REFL. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "locsle_total" *)
Theorem locsle_total : forall l1 l2, locsle l1 l2 \/ locsle l2 l1.
Proof. intros [a b] [c d]; apply locnle_total. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "locsle_TRANS" *)
Theorem locsle_TRANS : forall l1 l2 l3, locsle l1 l2 /\ locsle l2 l3 -> locsle l1 l3.
Proof. intros [a b] [c d] [e f]; apply locnle_TRANS. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "merge_locs_def" *)
Definition merge_locs (l1 l2 : locs) : locs :=
  match l1, l2 with Locs l1 l2, Locs l3 l4 => Locs l1 l4 end.

(** Structural helper: [merge_list_locs_aux h1 t] is HOL's
    [merge_list_locs (h1 :: t)]. *)
Fixpoint merge_list_locs_aux (h1 : locs) (t : list locs) : locs :=
  match t with
  | [] => h1
  | [h2] => merge_locs h1 h2
  | _ :: t' => merge_list_locs_aux h1 t'
  end.

Definition merge_list_locs (l : list locs) : locs :=
  match l with [] => unknown_loc | h :: t => merge_list_locs_aux h t end.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "merge_list_locs_def" *)
Theorem merge_list_locs_def :
  merge_list_locs [] = unknown_loc /\
  (forall h, merge_list_locs [h] = h) /\
  (forall h1 h2, merge_list_locs [h1; h2] = merge_locs h1 h2) /\
  (forall h1 h2 h3 t, merge_list_locs (h1 :: h2 :: h3 :: t) = merge_list_locs (h1 :: h3 :: t)).
Proof. repeat split. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "map_loc_def" *)
Fixpoint map_loc {A} (l : list A) (n : N) : list (A * locs) :=
  match l with
  | [] => []
  | h :: t => (h, Locs (POSN 0 n) (POSN 0 n)) :: map_loc t (n + 1)
  end.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "merge_locs_assoc" *)
Theorem merge_locs_assoc : forall l1 l2 l3,
  merge_locs (merge_locs l1 l2) l3 = merge_locs l1 l3 /\
  merge_locs l1 (merge_locs l2 l3) = merge_locs l1 l3.
Proof. intros [] [] []; split; reflexivity. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "merge_list_locs_2" *)
Theorem merge_list_locs_2 : forall h1 h2 t,
  merge_list_locs (h1 :: h2 :: t) = merge_list_locs (merge_locs h1 h2 :: t).
Proof.
  intros h1 h2 t; revert h1 h2; induction t as [|h3 t IH]; intros h1 h2; [reflexivity|].
  change (merge_list_locs (h1 :: h3 :: t) = merge_list_locs (merge_locs h1 h2 :: h3 :: t)).
  rewrite !IH; destruct h1, h2, h3; reflexivity.
Qed.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "merge_list_locs_nested" *)
Theorem merge_list_locs_nested : forall h t1 t2,
  merge_list_locs (merge_list_locs (h :: t1) :: t2) = merge_list_locs (h :: t1 ++ t2).
Proof.
  intros h t1; revert h; induction t1 as [|a t1 IH]; intros h t2; [reflexivity|].
  cbn [app]; rewrite !merge_list_locs_2, <- IH; reflexivity.
Qed.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "merge_list_locs_sing" *)
Theorem merge_list_locs_sing : forall h, merge_list_locs [h] = h.
Proof. reflexivity. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/locationScript.sml" "merge_locs_idem" *)
Theorem merge_locs_idem : forall l, merge_locs l l = l.
Proof. intros []; reflexivity. Qed.
