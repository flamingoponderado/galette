(** * HOL4 [mergesort]: (tail-recursive) merge sort

    The relation [R] is a boolean function (it is executed: CakeML's
    [mllist$sort] is [mergesort_tail]).  HOL [REV l acc] is
    [List.rev_append l acc] and HOL [DIV2 n] is [n DIV 2].

    [mergesortN_tail] recurses on a [num] that halves; it is computed with a
    fuel argument exceeding [n] ([mergesortN_tail_f]); HOL's equations are
    proved for [n >= 4] ([mergesortN_tail_rec]; smaller [n] compute).  HOL's definitions with overlapping
    patterns ([merge_def], [merge_tail_def], [mergesortN_tail_def]) are
    stored by HOL in pattern-completed form; their equations are proved here
    in the source form and not tagged. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Stdlib Require Import Permutation.
Open Scope N_scope.

Section Mergesort.
Context {A : Type}.

(*! HOL "HOL/src/sort/mergesortScript.sml" "sort2_def" *)
Definition sort2 (R : A -> A -> bool) (x y : A) : list A :=
  if R x y then [x; y] else [y; x].

(*! HOL "HOL/src/sort/mergesortScript.sml" "sort3_def" *)
Definition sort3 (R : A -> A -> bool) (x y z : A) : list A :=
  if R x y then
    if R y z then [x; y; z]
    else if R x z then [x; z; y]
    else [z; x; y]
  else if R y z then
    if R x z then [y; x; z]
    else [y; z; x]
  else [z; y; x].

(** HOL [merge]. *)
Fixpoint merge (R : A -> A -> bool) (l1 : list A) : list A -> list A :=
  fix merge_aux (l2 : list A) : list A :=
    match l1, l2 with
    | [], [] => []
    | l, [] => l
    | [], l => l
    | x :: l1', y :: l2' => if R x y then x :: merge R l1' (y :: l2') else y :: merge_aux l2'
    end.

(** HOL's [merge_def] clauses. *)
Theorem merge_eqns : forall R,
  (merge R [] [] = []) /\ (forall l, merge R l [] = l) /\ (forall l, merge R [] l = l) /\
  (forall x l1 y l2, merge R (x :: l1) (y :: l2) =
     if R x y then x :: merge R l1 (y :: l2) else y :: merge R (x :: l1) l2).
Proof. intros R; split; [|split; [|split]]; try reflexivity; intros [|? ?]; reflexivity. Qed.

(*! HOL "HOL/src/sort/mergesortScript.sml" "sort2_tail_def" *)
Definition sort2_tail (neg : bool) (R : A -> A -> bool) (x y : A) : list A :=
  if bool_decide (R x y <> neg) then [x; y] else [y; x].

(*! HOL "HOL/src/sort/mergesortScript.sml" "sort3_tail_def" *)
Definition sort3_tail (neg : bool) (R : A -> A -> bool) (x y z : A) : list A :=
  if bool_decide (R x y <> neg) then
    if bool_decide (R y z <> neg) then [x; y; z]
    else if bool_decide (R x z <> neg) then [x; z; y]
    else [z; x; y]
  else if bool_decide (R y z <> neg) then
    if bool_decide (R x z <> neg) then [y; x; z]
    else [y; z; x]
  else [z; y; x].

(** HOL [merge_tail]. *)
Fixpoint merge_tail (negate : bool) (R : A -> A -> bool) (l1 : list A) : list A -> list A -> list A :=
  fix aux (l2 acc : list A) : list A :=
    match l1, l2 with
    | [], [] => acc
    | l, [] => rev_append l acc
    | [], l => rev_append l acc
    | x :: l1', y :: l2' =>
        if bool_decide (R x y <> negate) then merge_tail negate R l1' (y :: l2') (x :: acc)
        else aux l2' (y :: acc)
    end.

(** HOL's [merge_tail_def] clauses. *)
Theorem merge_tail_eqns : forall negate R,
  (forall acc, merge_tail negate R [] [] acc = acc) /\
  (forall l acc, merge_tail negate R l [] acc = rev_append l acc) /\
  (forall l acc, merge_tail negate R [] l acc = rev_append l acc) /\
  (forall x l1 y l2 acc, merge_tail negate R (x :: l1) (y :: l2) acc =
     if bool_decide (R x y <> negate) then merge_tail negate R l1 (y :: l2) (x :: acc)
     else merge_tail negate R (x :: l1) l2 (y :: acc)).
Proof. intros; split; [|split; [|split]]; try reflexivity; intros [|? ?]; reflexivity. Qed.

(** HOL [mergesortN_tail], computed with fuel. *)
Fixpoint mergesortN_tail_f (fuel : nat) (negate : bool) (R : A -> A -> bool) (n : num) (l : list A)
    : list A :=
  match fuel with
  | O => []
  | S fuel =>
    match n, l with
    | 0, _ => []
    | 1, x :: _ => [x]
    | 1, [] => []
    | 2, x :: y :: _ => sort2_tail negate R x y
    | 2, [x] => [x]
    | 2, [] => []
    | 3, x :: y :: z :: _ => sort3_tail negate R x y z
    | 3, [x; y] => sort2_tail negate R x y
    | 3, [x] => [x]
    | 3, [] => []
    | _, _ =>
        let len1 := n DIV 2 in
        let neg := negb negate in
        merge_tail neg R (mergesortN_tail_f fuel neg R (n DIV 2) l)
                         (mergesortN_tail_f fuel neg R (n - len1) (DROP len1 l)) []
    end
  end.

Definition mergesortN_tail (negate : bool) (R : A -> A -> bool) (n : num) (l : list A) : list A :=
  mergesortN_tail_f (S (N.to_nat n)) negate R n l.

(*! HOL "HOL/src/sort/mergesortScript.sml" "mergesort_tail_def" *)
Definition mergesort_tail (R : A -> A -> bool) (l : list A) : list A :=
  mergesortN_tail false R (LENGTH l) l.

(** *** Fuel independence and HOL's recursion equation *)

Lemma mergesortN_tail_f_fuel : forall fuel1 fuel2 negate R n l,
  (N.to_nat n < fuel1)%nat -> (N.to_nat n < fuel2)%nat ->
  mergesortN_tail_f fuel1 negate R n l = mergesortN_tail_f fuel2 negate R n l.
Proof.
  induction fuel1 as [|f1 IH]; intros [|f2] negate R n l h1 h2; try lia.
  cbn [mergesortN_tail_f].
  destruct (N.lt_ge_cases n 4) as [hn|hn].
  - destruct n as [|p]; [reflexivity|].
    destruct p as [[[p|p|]|[p|p|]|]|[[p|p|]|[p|p|]|]|]; try lia; reflexivity.
  - assert (hrec : forall m l', m < n -> mergesortN_tail_f f1 (negb negate) R m l' =
                                  mergesortN_tail_f f2 (negb negate) R m l').
    { intros m l' hm; apply IH; lia. }
    assert (e1 : n DIV 2 < n) by (apply N.div_lt; lia).
    assert (e2 : n - n DIV 2 < n) by (assert (0 < n DIV 2) by (apply N.div_str_pos; lia); lia).
    destruct n as [|p]; [lia|].
    destruct p as [[[p|p|]|[p|p|]|]|[[p|p|]|[p|p|]|]|]; try lia;
      cbv zeta; rewrite !hrec by assumption; reflexivity.
Qed.

Lemma mergesortN_tail_rec negate R n l : 4 <= n ->
  mergesortN_tail negate R n l =
  merge_tail (negb negate) R (mergesortN_tail (negb negate) R (n DIV 2) l)
             (mergesortN_tail (negb negate) R (n - n DIV 2) (DROP (n DIV 2) l)) [].
Proof.
  intros hn; unfold mergesortN_tail; cbn [mergesortN_tail_f].
  assert (e1 : n DIV 2 < n) by (apply N.div_lt; lia).
  assert (e2 : n - n DIV 2 < n) by (assert (0 < n DIV 2) by (apply N.div_str_pos; lia); lia).
  rewrite (mergesortN_tail_f_fuel (N.to_nat n) (S (N.to_nat (n DIV 2)))) by lia.
  rewrite (mergesortN_tail_f_fuel (N.to_nat n) (S (N.to_nat (n - n DIV 2)))) by lia.
  destruct n as [|p]; [lia|].
  destruct p as [[[p|p|]|[p|p|]|]|[[p|p|]|[p|p|]|]|]; try lia; reflexivity.
Qed.

(** *** Permutation (Galette infrastructure; HOL's [PERM] is not ported) *)

Lemma rev_append_perm (l acc : list A) : Permutation (rev_append l acc) (l ++ acc).
Proof. rewrite rev_append_rev; apply Permutation_app_tail, Permutation_sym, Permutation_rev. Qed.

Lemma merge_tail_perm negate R l1 : forall l2 acc,
  Permutation (merge_tail negate R l1 l2 acc) (l1 ++ l2 ++ acc).
Proof.
  induction l1 as [|x l1 IH]; intros l2.
  - destruct l2 as [|y l2]; intros acc; cbn [merge_tail]; [reflexivity|].
    rewrite rev_append_perm; reflexivity.
  - induction l2 as [|y l2 IH2]; intros acc; cbn [merge_tail].
    + rewrite rev_append_perm; reflexivity.
    + destruct (bool_decide _).
      * rewrite IH; cbn [app]; symmetry.
        replace (l1 ++ y :: l2 ++ x :: acc) with ((l1 ++ y :: l2) ++ x :: acc)
          by (rewrite <- app_assoc; reflexivity).
        apply Permutation_cons_app; rewrite <- app_assoc; reflexivity.
      * rewrite IH2; cbn [app]; apply perm_skip, Permutation_app_head.
        apply Permutation_sym, Permutation_middle.
Qed.

Lemma TAKE_DROP_add (a b : num) (l : list A) :
  TAKE a l ++ TAKE b (DROP a l) = TAKE (a + b) l.
Proof.
  rewrite !TAKE_firstn, DROP_skipn, N2Nat.inj_add.
  revert l; induction (N.to_nat a) as [|k IH]; intros [|x l]; cbn; try reflexivity.
  - destruct (N.to_nat b); reflexivity.
  - f_equal; apply IH.
Qed.

Lemma perm3 (x y z : A) l :
  In l [[x; y; z]; [x; z; y]; [z; x; y]; [y; x; z]; [y; z; x]; [z; y; x]] -> Permutation l [x; y; z].
Proof.
  intros H; repeat destruct H as [<-|H]; try destruct H.
  - reflexivity.
  - apply perm_skip, perm_swap.
  - eapply perm_trans; [apply perm_swap|]; apply perm_skip, perm_swap.
  - apply perm_swap.
  - eapply perm_trans; [apply perm_skip, perm_swap|]; apply perm_swap.
  - eapply perm_trans; [apply perm_swap|]; eapply perm_trans; [apply perm_skip, perm_swap|].
    apply perm_swap.
Qed.

Ltac in6 := cbn; repeat (first [left; reflexivity|right]).

Lemma mergesortN_tail_f_perm : forall fuel negate R n l, (N.to_nat n < fuel)%nat ->
  Permutation (mergesortN_tail_f fuel negate R n l) (TAKE n l).
Proof.
  induction fuel as [|fuel IH]; intros negate R n l hf; [lia|]; cbn [mergesortN_tail_f].
  destruct (N.lt_ge_cases n 4) as [hn|hn].
  - rewrite TAKE_firstn.
    assert (h : n = 0 \/ n = 1 \/ n = 2 \/ n = 3) by lia.
    destruct h as [-> | [-> | [-> | ->]]]; cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
    + reflexivity.
    + destruct l; reflexivity.
    + destruct l as [|x [|y l]]; try reflexivity; unfold sort2_tail; cbn.
      destruct (bool_decide _); [reflexivity|apply perm_swap].
    + destruct l as [|x [|y [|z l]]]; try reflexivity; cbn.
      * unfold sort2_tail; destruct (bool_decide _); [reflexivity|apply perm_swap].
      * unfold sort3_tail; repeat destruct (bool_decide _); apply perm3; in6.
  - assert (e1 : n DIV 2 < n) by (apply N.div_lt; lia).
    assert (e2 : n - n DIV 2 < n) by (assert (0 < n DIV 2) by (apply N.div_str_pos; lia); lia).
    assert (hp : Permutation (mergesortN_tail_f fuel (negb negate) R (n DIV 2) l ++
                               mergesortN_tail_f fuel (negb negate) R (n - n DIV 2) (DROP (n DIV 2) l))
                             (TAKE (n DIV 2) l ++ TAKE (n - n DIV 2) (DROP (n DIV 2) l))).
    { apply Permutation_app; apply IH; lia. }
    rewrite TAKE_DROP_add in hp; replace (n DIV 2 + (n - n DIV 2)) with n in hp by lia.
    destruct n as [|p]; [lia|].
    destruct p as [[[p|p|]|[p|p|]|]|[[p|p|]|[p|p|]|]|]; try lia;
      cbv zeta; rewrite merge_tail_perm, app_nil_r; exact hp.
Qed.

Lemma mergesort_tail_perm R l : Permutation (mergesort_tail R l) l.
Proof.
  unfold mergesort_tail, mergesortN_tail; rewrite mergesortN_tail_f_perm by lia.
  rewrite TAKE_firstn, LENGTH_length, Nat2N.id, firstn_all; reflexivity.
Qed.

End Mergesort.
