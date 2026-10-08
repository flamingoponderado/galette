(** * CakeML [riscv_targetProof]: [encoder_correct] for RISC-V (in progress)

    Port of [cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml].

    HOL proves the per-instruction facts with the step evaluator
    ([riscv_stepLib]) and bit-blasting ([blastLib]); here decoding an
    encoded instruction is computed with the Galette-only bit lemmas below
    ([word_bit] of [word_concat], and [v2w] of a word's own bits). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.n_bit Require Import words bitstring.
From Galette.HOL.src.n_bit.words Require Import fcp_defs.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.examples.l3_machine_code.riscv.model Require Import riscv.
Open Scope N_scope.

(** ** Bit lemmas (Galette-only) *)

Section Bits.

Lemma fcp_index_w2w {a b : N} (w : word a) i : i < dimindex b -> fcp_index (w2w w : word b) i = fcp_index w i.
Proof. intros Hi; unfold w2w; rewrite fcp_index_n2w by exact Hi; rewrite BIT_testbit, fcp_index_testbit; reflexivity. Qed.

Lemma word_bit_alt {a : N} (w : word a) i : word_bit i w = (i <? dimindex a) && fcp_index w i.
Proof.
  unfold word_bit. pose proof (@dimindex_pos a) as H.
  destruct (N.leb_spec i (dimindex a - 1)), (N.ltb_spec i (dimindex a)); try reflexivity; lia.
Qed.

Lemma word_bit_concat {a b c : N} (v : word a) (w : word b) i :
  dimindex (a + b) = dimindex a + dimindex b -> i < dimindex c -> i < dimindex a + dimindex b ->
  word_bit i (word_concat v w : word c) =
  if i <? dimindex b then word_bit i w else word_bit (i - dimindex b) v.
Proof.
  intros Hd Hc Hab. rewrite !word_bit_alt.
  unfold word_concat, word_join; cbv zeta.
  rewrite fcp_index_w2w by exact Hc. rewrite fcp_index_word_or by lia.
  rewrite fcp_index_word_lsl by lia. rewrite !fcp_index_w2w by lia.
  destruct (N.ltb_spec i (dimindex c)); [|lia]. cbn [andb].
  destruct (N.ltb_spec i (dimindex b)) as [Hb|Hb].
  - destruct (N.leb_spec (dimindex b) i); [lia|]. cbn [andb orb].
    destruct (N.ltb_spec i (dimindex b)); [reflexivity|lia].
  - destruct (N.leb_spec (dimindex b) i); [|lia]. cbn [andb].
    rewrite (fcp_index_high w i) by lia. rewrite Bool.orb_false_r.
    destruct (N.ltb_spec (i - dimindex b) (dimindex a)); [reflexivity|lia].
Qed.

End Bits.
