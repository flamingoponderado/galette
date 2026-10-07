(** * HOL4 [sum_num]: finite sums of natural-number functions *)

From Galette Require Import Base.

(*! HOL "HOL/src/n-bit/sum_numScript.sml" "GSUM_def" *)
Definition GSUM (p : nat * nat) (f : nat -> nat) : nat :=
  let (n, m) := p in
  (fix GSUM_n m := match m with 0 => 0 | S m => GSUM_n m + f (n + m) end) m.

Lemma GSUM_eqns n m f :
  GSUM (n, 0) f = 0 /\ GSUM (n, S m) f = GSUM (n, m) f + f (n + m).
Proof. split; reflexivity. Qed.

(*! HOL "HOL/src/n-bit/sum_numScript.sml" "SUM_def" *)
Fixpoint SUM (m : nat) (f : nat -> nat) : nat :=
  match m with
  | 0 => 0
  | S m => SUM m f + f m
  end.
