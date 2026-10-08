(** * CakeML [mllist]: [sort]

    Only [sort] is ported so far (used by [pan_to_target] as [sort $<]).
    The relation is a boolean function. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.sort Require Import mergesort.
From Stdlib Require Import Permutation.
Open Scope N_scope.

(*! HOL "cakeml/basis/pure/mllistScript.sml" "sort_def" *)
Definition sort {A} : (A -> A -> bool) -> list A -> list A := mergesort_tail.

(*! HOL "cakeml/basis/pure/mllistScript.sml" "sort_thm" *)
Theorem sort_thm : forall {A} (R : A -> A -> bool) l, sort R l = mergesort_tail R l.
Proof. reflexivity. Qed.

(** HOL [sort_PERM] is stated with [sorting$PERM] (not ported); this is the
    same fact with Rocq's [Permutation]. *)
Lemma sort_Permutation {A} (R : A -> A -> bool) l : Permutation l (sort R l).
Proof. symmetry; apply mergesort_tail_perm. Qed.

(*! HOL "cakeml/basis/pure/mllistScript.sml" "sort_MEM" *)
Theorem sort_MEM : forall {A} `{EqDecision A} (x : A) (R : A -> A -> bool) L, MEM x (sort R L) <-> MEM x L.
Proof.
  intros A H x R L; unfold is_true; rewrite !MEM_In; split; apply Permutation_in;
    [symmetry|]; apply sort_Permutation.
Qed.

(*! HOL "cakeml/basis/pure/mllistScript.sml" "sort_LENGTH" *)
Theorem sort_LENGTH : forall {A} (R : A -> A -> bool) l, LENGTH (sort R l) = LENGTH l.
Proof.
  intros; rewrite !LENGTH_length, (Permutation_length (sort_Permutation R l)); reflexivity.
Qed.
