(** * HOL4 [ternaryComparisons]: three-valued comparisons *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
Open Scope N_scope.

(*! HOL "HOL/src/sort/ternaryComparisonsScript.sml" "ordering" *)
Inductive ordering : Type := LESS | EQUAL | GREATER.

#[global] Instance ordering_eq_dec_inst : EqDecision ordering.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

#[global] Instance ordering_inhabited : Inhabited ordering := LESS.

(*! HOL "HOL/src/sort/ternaryComparisonsScript.sml" "bool_compare_def" *)
Definition bool_compare (b1 b2 : bool) : ordering :=
  match b1, b2 with
  | true, true => EQUAL
  | false, false => EQUAL
  | true, false => GREATER
  | false, true => LESS
  end.

(*! HOL "HOL/src/sort/ternaryComparisonsScript.sml" "pair_compare_def" *)
Definition pair_compare {A B} (c1 : A -> A -> ordering) (c2 : B -> B -> ordering)
  (p1 p2 : A * B) : ordering :=
  let (a, b) := p1 in let (x, y) := p2 in
  match c1 a x with EQUAL => c2 b y | res => res end.

(*! HOL "HOL/src/sort/ternaryComparisonsScript.sml" "option_compare_def" *)
Definition option_compare {A} (c : A -> A -> ordering) (o1 o2 : option A) : ordering :=
  match o1, o2 with
  | None, None => EQUAL
  | None, Some _ => LESS
  | Some _, None => GREATER
  | Some v1, Some v2 => c v1 v2
  end.

(*! HOL "HOL/src/sort/ternaryComparisonsScript.sml" "num_compare_def" *)
Definition num_compare (n1 n2 : N) : ordering :=
  if n1 =? n2 then EQUAL else if n1 <? n2 then LESS else GREATER.

(*! HOL "HOL/src/sort/ternaryComparisonsScript.sml" "list_compare_def" *)
Fixpoint list_compare {A} (cmp : A -> A -> ordering) (l1 l2 : list A) : ordering :=
  match l1, l2 with
  | [], [] => EQUAL
  | [], _ => LESS
  | _, [] => GREATER
  | x :: l1, y :: l2 =>
      match cmp x y with
      | LESS => LESS
      | EQUAL => list_compare cmp l1 l2
      | GREATER => GREATER
      end
  end.

(*! HOL "HOL/src/sort/ternaryComparisonsScript.sml" "compare_equal" *)
Theorem compare_equal : forall {A} (cmp : A -> A -> ordering),
  (forall x y, cmp x y = EQUAL <-> x = y) ->
  forall l1 l2, list_compare cmp l1 l2 = EQUAL <-> l1 = l2.
Proof.
  intros A cmp H l1; induction l1 as [|x l1 IH]; intros [|y l2]; cbn;
    try (split; congruence).
  destruct (cmp x y) eqn:E.
  - split; [discriminate|intros Hc; injection Hc as -> ->].
    rewrite (proj2 (H y y) eq_refl) in E; discriminate.
  - apply H in E as ->; rewrite IH; split; congruence.
  - split; [discriminate|intros Hc; injection Hc as -> ->].
    rewrite (proj2 (H y y) eq_refl) in E; discriminate.
Qed.

(*! HOL "HOL/src/sort/ternaryComparisonsScript.sml" "list_merge_def" *)
Fixpoint list_merge {A} (a_lt : A -> A -> bool) (l1 l2 : list A) : list A :=
  match l1 with
  | [] => l2
  | x :: l1' =>
      (fix merge_r (l2 : list A) : list A :=
         match l2 with
         | [] => l1
         | y :: l2' => if a_lt x y then x :: list_merge a_lt l1' l2 else y :: merge_r l2'
         end) l2
  end.

(*! HOL "HOL/src/sort/ternaryComparisonsScript.sml" "invert_comparison_def" *)
Definition invert_comparison (c : ordering) : ordering :=
  match c with GREATER => LESS | LESS => GREATER | EQUAL => EQUAL end.

(*! HOL "HOL/src/sort/ternaryComparisonsScript.sml" "invert_eq_EQUAL" *)
Theorem invert_eq_EQUAL : forall x, invert_comparison x = EQUAL <-> x = EQUAL.
Proof. intros []; cbn; split; congruence. Qed.

(*! HOL "HOL/src/sort/ternaryComparisonsScript.sml" "ordering_distinct1" *)
Theorem ordering_distinct1 : EQUAL <> LESS.
Proof. discriminate. Qed.

(*! HOL "HOL/src/sort/ternaryComparisonsScript.sml" "ordering_distinct2" *)
Theorem ordering_distinct2 : GREATER <> EQUAL.
Proof. discriminate. Qed.
