(** * HOL4 [sum_num]: finite sums of natural-number functions *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
Open Scope N_scope.

Definition GSUM (p : N * N) (f : N -> N) : N :=
  let (n, m) := p in num_rec 0 (fun m r => r + f (n + m)) m.

(*! HOL "HOL/src/n-bit/sum_numScript.sml" "GSUM_def" *)
Theorem GSUM_def : forall n m f,
  GSUM (n, 0) f = 0 /\ GSUM (n, SUC m) f = GSUM (n, m) f + f (n + m).
Proof. intros; split; [reflexivity|]. unfold GSUM; rewrite num_rec_SUC; reflexivity. Qed.

Definition SUM (m : N) (f : N -> N) : N := num_rec 0 (fun m r => r + f m) m.

(*! HOL "HOL/src/n-bit/sum_numScript.sml" "SUM_def" *)
Theorem SUM_def : forall m f, SUM 0 f = 0 /\ SUM (SUC m) f = SUM m f + f m.
Proof. intros; split; [reflexivity|]. unfold SUM; rewrite num_rec_SUC; reflexivity. Qed.
