(** * Four bytes as a [word32] (Galette helpers, no HOL original)

    HOL proves the 32-bit load equations ([panSem]/[wordSem]'s
    [mem_load_32_alt]) by evaluation and bit-blasting; these identities are
    the bit-level facts they need, proved bitwise. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words byte.
Import byte.ByteBits.
Open Scope N_scope.

Lemma word_of_bytes_4_le (b0 b1 b2 b3 : word8) :
  word_of_bytes false (n2w 0 : word32) [b0; b1; b2; b3] =
  ((w2w b0) || ((w2w b1) << 8) || ((w2w b2) << 16) || ((w2w b3) << 24))%w.
Proof.
  apply word_testbit_eq; intros i Hi.
  cbn [word_of_bytes].
  rewrite !testbit_set_byte, !testbit_or, !testbit_lsl, !testbit_w2w.
  unfold byte_index; cbn - [N.testbit].
  rewrite ?testbit_n2w.
  change (dimindex 32) with 32 in *; change (dimindex 8) with 8 in *.
  assert (i < 8 \/ (8 <= i < 16) \/ (16 <= i < 24) \/ (24 <= i < 32)) as [H|[H|[H|H]]] by lia;
  repeat match goal with
         | |- context [N.ltb ?x ?y] => destruct (N.ltb_spec x y); try lia
         | |- context [N.leb ?x ?y] => destruct (N.leb_spec x y); try lia
         end; cbn; rewrite ?testbit_word8_high by lia; try reflexivity.
  all: repeat match goal with
              | |- context [N.testbit (w2n ?b) ?j] => rewrite (testbit_word8_high b j) by lia
              end;
       rewrite ?N.sub_0_r, ?orb_false_r, ?orb_false_l; reflexivity.
Qed.

Lemma word_of_bytes_4_be (b0 b1 b2 b3 : word8) :
  word_of_bytes true (n2w 0 : word32) [b0; b1; b2; b3] =
  (((w2w b0) << 24) || ((w2w b1) << 16) || ((w2w b2) << 8) || (w2w b3))%w.
Proof.
  apply word_testbit_eq; intros i Hi.
  cbn [word_of_bytes].
  rewrite !testbit_set_byte, !testbit_or, !testbit_lsl, !testbit_w2w.
  unfold byte_index; cbn - [N.testbit].
  rewrite ?testbit_n2w.
  change (dimindex 32) with 32 in *; change (dimindex 8) with 8 in *.
  assert (i < 8 \/ (8 <= i < 16) \/ (16 <= i < 24) \/ (24 <= i < 32)) as [H|[H|[H|H]]] by lia;
  repeat match goal with
         | |- context [N.ltb ?x ?y] => destruct (N.ltb_spec x y); try lia
         | |- context [N.leb ?x ?y] => destruct (N.leb_spec x y); try lia
         end; cbn; rewrite ?testbit_word8_high by lia; try reflexivity.
  all: repeat match goal with
              | |- context [N.testbit (w2n ?b) ?j] => rewrite (testbit_word8_high b j) by lia
              end;
       rewrite ?N.sub_0_r, ?orb_false_r, ?orb_false_l; reflexivity.
Qed.

