(** * HOL4 [bitstring]: bit vectors as [bool list] (the part used so far)

    HOL defines [testbit] through [field]/[fixwidth]; it is computed here by
    HOL's characterisation [testbit] (tagged [testbit_thm], the name clashes
    with the constant), and [v2w] is HOL's [FCP] definition. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list numposrep.
From Galette.HOL.src.list.src.list Require Import extra.
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

(** ** Conversions, extension and fields (used by the L3 ARMv8 model) *)

(*! HOL "HOL/src/n-bit/bitstringScript.sml" "bitify_def" *)
Fixpoint bitify (a : list N) (l : list bool) {struct l} : list N :=
  match l with
  | [] => a
  | false :: l => bitify (0 :: a) l
  | true :: l => bitify (1 :: a) l
  end.

(*! HOL "HOL/src/n-bit/bitstringScript.sml" "v2n_def" *)
Definition v2n (l : list bool) : N := l2n 2 (bitify [] l).

(*! HOL "HOL/src/n-bit/bitstringScript.sml" "zero_extend_def" *)
Definition zero_extend (n : N) (v : list bool) : list bool := PAD_LEFT false n v.

(*! HOL "HOL/src/n-bit/bitstringScript.sml" "fixwidth_def" *)
Definition fixwidth (n : N) (v : list bool) : list bool :=
  let l := LENGTH v in
  if l <? n then zero_extend n v else DROP (l - n) v.

(*! HOL "HOL/src/n-bit/bitstringScript.sml" "shiftl_def" *)
Definition shiftl (v : list bool) (m : N) : list bool := PAD_RIGHT false (LENGTH v + m) v.

(*! HOL "HOL/src/n-bit/bitstringScript.sml" "shiftr_def" *)
Definition shiftr (v : list bool) (m : N) : list bool := TAKE (LENGTH v - m) v.

(*! HOL "HOL/src/n-bit/bitstringScript.sml" "field_def" *)
Definition field (h l : N) (v : list bool) : list bool := fixwidth (SUC h - l) (shiftr v l).

(** HOL's [m MOD l] is unspecified for [l = 0]; that case returns [v]
    before the remainder is used. *)
(*! HOL "HOL/src/n-bit/bitstringScript.sml" "rotate_def" *)
Definition rotate (v : list bool) (m : N) : list bool :=
  let l := LENGTH v in
  let x := m mod l in
  if (l =? 0) || (x =? 0) then v else field (x - 1) 0 v ++ field (l - 1) x v.

(*! HOL "HOL/src/n-bit/bitstringScript.sml" "w2v_def" *)
Definition w2v {a : N} (w : word a) : list bool :=
  GENLIST (fun i => fcp_index w (dimindex a - 1 - i)) (dimindex a).

(*! HOL "HOL/src/n-bit/bitstringScript.sml" "bitwise_def" *)
Definition bitwise (f : bool -> bool -> bool) (v1 v2 : list bool) : list bool :=
  let m := MAX (LENGTH v1) (LENGTH v2) in
  MAP (fun p => f (fst p) (snd p)) (ZIP (fixwidth m v1, fixwidth m v2)).

(*! HOL "HOL/src/n-bit/bitstringScript.sml" "bxor_def" *)
Definition bxor : list bool -> list bool -> list bool :=
  bitwise (fun x y => negb (bool_decide (x = y))).

(*! HOL "HOL/src/n-bit/bitstringScript.sml" "replicate_def" *)
Definition replicate (v : list bool) (n : N) : list bool := FLAT (GENLIST (fun _ => v) n).
