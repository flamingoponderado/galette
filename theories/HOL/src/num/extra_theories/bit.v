(** * HOL4 [bit]: bit operations on natural numbers *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "MOD_2EXP_def" *)
Definition MOD_2EXP (x n : nat) : nat := n MOD 2 ** x.

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "DIV_2EXP_def" *)
Definition DIV_2EXP (x n : nat) : nat := n DIV 2 ** x.

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "TIMES_2EXP_def" *)
Definition TIMES_2EXP (x n : nat) : nat := n * 2 ** x.

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "SBIT_def" *)
Definition SBIT (b : bool) (n : nat) : nat := if b then 2 ** n else 0.

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "BITS_def" *)
Definition BITS (h l n : nat) : nat := MOD_2EXP (SUC h - l) (DIV_2EXP l n).

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "BITV_def" *)
Definition BITV (n b : nat) : nat := BITS b b n.

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "BIT_def" *)
Definition BIT (b n : nat) : bool := BITS b b n =? 1.

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "SLICE_def" *)
Definition SLICE (h l n : nat) : nat := MOD_2EXP (SUC h) n - MOD_2EXP l n.

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "BITWISE_def" *)
Fixpoint BITWISE (n : nat) (op : bool -> bool -> bool) (x y : nat) : nat :=
  match n with
  | 0 => 0
  | S n => BITWISE n op x y + SBIT (op (BIT n x) (BIT n y)) n
  end.

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "BIT_MODIFY_def" *)
Fixpoint BIT_MODIFY (n : nat) (f : nat -> bool -> bool) (x : nat) : nat :=
  match n with
  | 0 => 0
  | S n => BIT_MODIFY n f x + SBIT (f n (BIT n x)) n
  end.

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "SIGN_EXTEND_def" *)
Definition SIGN_EXTEND (l h n : nat) : nat :=
  let m := n MOD 2 ** l in
  if BIT (l - 1) n then 2 ** h - 2 ** l + m else m.

(** HOL [LOG] is introduced by [new_specification] (logroot); for base [2]
    and positive arguments it is [Nat.log2].  Only [LOG2] is used here. *)
Definition LOG2 (n : nat) : nat := Nat.log2 n.

(** [BIT] agrees with Rocq's [Nat.testbit]; used to compute efficiently. *)
Lemma BIT_testbit b n : BIT b n = Nat.testbit n b.
Proof.
  unfold BIT, BITS, MOD_2EXP, DIV_2EXP.
  replace (S b - b) with 1 by lia. rewrite Nat.pow_1_r.
  rewrite Nat.testbit_eqb. reflexivity.
Qed.
