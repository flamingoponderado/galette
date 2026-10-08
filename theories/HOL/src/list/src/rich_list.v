(** * HOL4 [rich_list]: list functions used by the compiler

    Recursion on a [num] uses [num_rec] (as in [list.v]); where HOL's
    definition is [nocompute] or a specification, the Rocq definition is
    the computational one and HOL's defining equations are proved and
    tagged. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.coretypes Require Import pair.
From Galette.HOL.src.list.src Require Import list.
Open Scope N_scope.

Section RichList.
Context {A : Type}.

(** HOL [REPLICATE]. *)
Definition REPLICATE (n : num) (x : A) : list A := num_rec [] (fun _ r => x :: r) n.

(*! HOL "HOL/src/list/src/rich_listScript.sml" "REPLICATE" *)
Theorem REPLICATE_thm : forall n (x : A),
  (REPLICATE 0 x = []) /\ (REPLICATE (SUC n) x = x :: REPLICATE n x).
Proof. intros; split; [reflexivity|unfold REPLICATE; rewrite num_rec_SUC; reflexivity]. Qed.

(*! HOL "HOL/src/list/src/rich_listScript.sml" "LENGTH_REPLICATE" *)
Theorem LENGTH_REPLICATE : forall n (x : A), LENGTH (REPLICATE n x) = n.
Proof.
  intros n x; induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (REPLICATE_thm n x)); cbn [LENGTH]; rewrite IH; reflexivity.
Qed.

(*! HOL "HOL/src/list/src/rich_listScript.sml" "REPLICATE_GENLIST" *)
Theorem REPLICATE_GENLIST : forall n (x : A), REPLICATE n x = GENLIST (K x) n.
Proof.
  intros n x; induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (REPLICATE_thm n x)), (proj2 (GENLIST_thm (K x) n)), SNOC_app, <- IH; unfold K.
  clear IH; induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (REPLICATE_thm n x)); cbn [app]; rewrite IH; reflexivity.
Qed.

(*! HOL "HOL/src/list/src/rich_listScript.sml" "SPLITP" *)
Fixpoint SPLITP (P : A -> bool) (l : list A) : list A * list A :=
  match l with
  | [] => ([], [])
  | x :: l => if P x then ([], x :: l) else let r := SPLITP P l in (x :: FST r, SND r)
  end.

(** HOL [SEG] (a [new_specification]; HOL's witness is [TAKE m (DROP k l)]). *)
Definition SEG (m k : num) (l : list A) : list A := TAKE m (DROP k l).

(** HOL's specification theorem [SEG] (declared inside a [local] block,
    which [check-hol-refs.py] does not recognise, hence untagged). *)
Theorem SEG_thm :
  (forall k (l : list A), SEG 0 k l = []) /\
  (forall m (x : A) l, SEG (SUC m) 0 (x :: l) = x :: SEG m 0 l) /\
  (forall m k (x : A) l, SEG (SUC m) (SUC k) (x :: l) = SEG (SUC m) k l).
Proof.
  unfold SEG; split; [|split].
  - intros k l; rewrite TAKE_firstn; reflexivity.
  - intros m x l; rewrite !TAKE_firstn, !DROP_skipn; cbn; rewrite N2Nat.inj_succ; reflexivity.
  - intros m k x l; rewrite !DROP_skipn, N2Nat.inj_succ; reflexivity.
Qed.

End RichList.

(*! HOL "HOL/src/list/src/rich_listScript.sml" "MAX_LIST_def" *)
Fixpoint MAX_LIST (l : list num) : num :=
  match l with [] => 0 | h :: t => MAX h (MAX_LIST t) end.

(** HOL [COUNT_LIST_AUX]. *)
Definition COUNT_LIST_AUX (n : num) : list num -> list num :=
  num_rec (fun l => l) (fun n r l => r (n :: l)) n.

(*! HOL "HOL/src/list/src/rich_listScript.sml" "COUNT_LIST_AUX_def" *)
Theorem COUNT_LIST_AUX_def : forall n l,
  (COUNT_LIST_AUX 0 l = l) /\ (COUNT_LIST_AUX (SUC n) l = COUNT_LIST_AUX n (n :: l)).
Proof. intros; split; [reflexivity|unfold COUNT_LIST_AUX; rewrite num_rec_SUC; reflexivity]. Qed.

(** HOL [COUNT_LIST] ([nocompute]; computed by [COUNT_LIST_compute]). *)
Definition COUNT_LIST (n : num) : list num := COUNT_LIST_AUX n [].

Lemma COUNT_LIST_AUX_GENLIST n l : COUNT_LIST_AUX n l = GENLIST I n ++ l.
Proof.
  revert l; induction n as [|n IH] using N.peano_ind; intros l; [reflexivity|].
  rewrite (proj2 (COUNT_LIST_AUX_def n l)), IH, (proj2 (GENLIST_thm I n)), SNOC_app, <- app_assoc.
  reflexivity.
Qed.

(*! HOL "HOL/src/list/src/rich_listScript.sml" "COUNT_LIST_compute" *)
Theorem COUNT_LIST_compute : forall n, COUNT_LIST n = COUNT_LIST_AUX n [].
Proof. reflexivity. Qed.

(*! HOL "HOL/src/list/src/rich_listScript.sml" "COUNT_LIST_GENLIST" *)
Theorem COUNT_LIST_GENLIST : forall n, COUNT_LIST n = GENLIST I n.
Proof. intros n; unfold COUNT_LIST; rewrite COUNT_LIST_AUX_GENLIST, app_nil_r; reflexivity. Qed.

Lemma GENLIST_CONS_aux {A} (f : num -> A) n :
  GENLIST f (SUC n) = f 0 :: GENLIST (fun i => f (SUC i)) n.
Proof.
  revert f; induction n as [|n IH] using N.peano_ind; intros f; [reflexivity|].
  rewrite (proj2 (GENLIST_thm f (SUC n))), IH, (proj2 (GENLIST_thm (fun i => f (SUC i)) n)), !SNOC_app.
  reflexivity.
Qed.

Lemma MAP_GENLIST_aux {A B} (g : A -> B) (f : num -> A) n : MAP g (GENLIST f n) = GENLIST (fun i => g (f i)) n.
Proof.
  induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite !(proj2 (GENLIST_thm _ n)), !SNOC_app, map_app, IH; reflexivity.
Qed.

(*! HOL "HOL/src/list/src/rich_listScript.sml" "COUNT_LIST_def" *)
Theorem COUNT_LIST_def : forall n,
  (COUNT_LIST 0 = []) /\ (COUNT_LIST (SUC n) = 0 :: MAP SUC (COUNT_LIST n)).
Proof.
  intros n; split; [reflexivity|].
  rewrite (COUNT_LIST_GENLIST (SUC n)), (COUNT_LIST_GENLIST n), GENLIST_CONS_aux, MAP_GENLIST_aux.
  reflexivity.
Qed.

(*! HOL "HOL/src/list/src/rich_listScript.sml" "LENGTH_COUNT_LIST" *)
Theorem LENGTH_COUNT_LIST : forall n, LENGTH (COUNT_LIST n) = n.
Proof.
  intros n; induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (COUNT_LIST_def n)); cbn [LENGTH]; rewrite LENGTH_length, length_map, <- LENGTH_length, IH.
  reflexivity.
Qed.
