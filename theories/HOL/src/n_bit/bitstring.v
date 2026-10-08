(** * HOL4 [bitstring]: bit vectors as [bool list] (the part used so far)

    HOL defines [testbit] through [field]/[fixwidth]; it is computed here by
    HOL's characterisation [testbit] (tagged [testbit_thm], the name clashes
    with the constant), and [v2w] is HOL's [FCP] definition. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.n_bit.words Require Import fcp_defs.
Open Scope N_scope.

Definition testbit (b : N) (v : list bool) : bool :=
  let n := LENGTH v in (b <? n) && EL (n - 1 - b) v.

(*! HOL "HOL/src/n-bit/bitstringScript.sml" "testbit" 405 *)
Theorem testbit_thm : forall b v,
  testbit b v = let n := LENGTH v in (b <? n) && EL (n - 1 - b) v.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/n-bit/bitstringScript.sml" "v2w_def" *)
Definition v2w {a : N} (v : list bool) : word a := FCP (fun i => testbit i v).

(** One-bit vectors (Galette helper). *)
Lemma v2w_sing {a : N} (b : bool) : (v2w [b] : word a) = if b then n2w 1 else n2w 0.
Proof.
  assert (Hd : 1 < dimword a).
  { unfold dimword; pose proof (DIMINDEX_GT_0 a).
    apply N.lt_le_trans with (2 ** 1); [reflexivity|apply N.pow_le_mono_r; lia]. }
  apply word_bit_ext; intros i Hi.
  unfold v2w; rewrite fcp_index_FCP by exact Hi. unfold testbit; cbn [LENGTH].
  rewrite fcp_index_testbit.
  destruct (N.eqb_spec i 0) as [->|Hne].
  - destruct b; rewrite w2n_n2w; [rewrite N.mod_small by exact Hd|rewrite N.Div0.mod_0_l]; reflexivity.
  - destruct (N.ltb_spec i (SUC 0)); [lia|]. cbn [andb].
    destruct b; rewrite w2n_n2w; [rewrite N.mod_small by exact Hd|rewrite N.Div0.mod_0_l].
    + symmetry; apply N.bits_above_log2; rewrite N.log2_1; lia.
    + symmetry; apply N.bits_0.
Qed.
