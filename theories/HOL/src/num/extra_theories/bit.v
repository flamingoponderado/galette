(** * HOL4 [bit]: bit operations on natural numbers *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
Open Scope N_scope.

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "MOD_2EXP_def" *)
Definition MOD_2EXP (x n : N) : N := n MOD 2 ** x.

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "DIV_2EXP_def" *)
Definition DIV_2EXP (x n : N) : N := n DIV 2 ** x.

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "TIMES_2EXP_def" *)
Definition TIMES_2EXP (x n : N) : N := n * 2 ** x.

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "SBIT_def" *)
Definition SBIT (b : bool) (n : N) : N := if b then 2 ** n else 0.

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "BITS_def" *)
Definition BITS (h l n : N) : N := MOD_2EXP (SUC h - l) (DIV_2EXP l n).

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "BITV_def" *)
Definition BITV (n b : N) : N := BITS b b n.

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "BIT_def" *)
Definition BIT (b n : N) : bool := BITS b b n =? 1.

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "SLICE_def" *)
Definition SLICE (h l n : N) : N := MOD_2EXP (SUC h) n - MOD_2EXP l n.

Definition BITWISE (n : N) (op : bool -> bool -> bool) (x y : N) : N :=
  num_rec 0 (fun n r => r + SBIT (op (BIT n x) (BIT n y)) n) n.

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "BITWISE_def" *)
Theorem BITWISE_def : forall op x y n,
  BITWISE 0 op x y = 0 /\
  BITWISE (SUC n) op x y = BITWISE n op x y + SBIT (op (BIT n x) (BIT n y)) n.
Proof. intros; split; [reflexivity|]. unfold BITWISE; rewrite num_rec_SUC; reflexivity. Qed.

Definition BIT_MODIFY (n : N) (f : N -> bool -> bool) (x : N) : N :=
  num_rec 0 (fun n r => r + SBIT (f n (BIT n x)) n) n.

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "BIT_MODIFY_def" *)
Theorem BIT_MODIFY_def : forall f x n,
  BIT_MODIFY 0 f x = 0 /\
  BIT_MODIFY (SUC n) f x = BIT_MODIFY n f x + SBIT (f n (BIT n x)) n.
Proof. intros; split; [reflexivity|]. unfold BIT_MODIFY; rewrite num_rec_SUC; reflexivity. Qed.

(*! HOL "HOL/src/num/extra_theories/bitScript.sml" "SIGN_EXTEND_def" *)
Definition SIGN_EXTEND (l h n : N) : N :=
  let m := n MOD 2 ** l in
  if BIT (l - 1) n then 2 ** h - 2 ** l + m else m.

(** HOL [LOG] is introduced by [new_specification] (logroot); for base [2]
    and positive arguments it is [N.log2].  Only [LOG2] is used here. *)
Definition LOG2 (n : N) : N := N.log2 n.

(** [BIT] agrees with Rocq's [N.testbit]; used to compute efficiently. *)
Lemma BIT_testbit b n : BIT b n = N.testbit n b.
Proof.
  unfold BIT, BITS, MOD_2EXP, DIV_2EXP.
  replace (SUC b - b) with 1 by lia. rewrite N.pow_1_r.
  rewrite N.testbit_eqb. reflexivity.
Qed.
