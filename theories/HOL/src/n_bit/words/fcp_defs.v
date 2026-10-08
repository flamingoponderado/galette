(** * HOL4 [words]: the [FCP]-based defining equations

    Part of the port of [HOL/src/n-bit/wordsScript.sml] (see [words.v]).
    [words.v] defines the bitwise operations computationally, in [n2w]
    normal form.  HOL defines them with [FCP] and [fcp_index] ([w ' i]); this
    module proves HOL's defining equations ([w2n_def], [n2w_def],
    [word_and_def], [word_lsl_def], ...) and the bit-level [n2w] theorems
    ([word_and_n2w], [word_index], [w2w_n2w], ...).

    The key tools (untagged, Galette-only) are:
    - [fcp_index_FCP]: [(FCP f) ' i = f i] for [i < dimindex a] (HOL's
      [fcpTheory.FCP_BETA]);
    - [word_bit_ext]: two words with the same bits below [dimindex a] are
      equal (one direction of HOL's [fcpTheory.CART_EQ]). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.n_bit Require Import sum_num words.
Open Scope N_scope.

(** [w ' i] outside [word_scope], so that index arithmetic stays on [N]. *)
Local Notation "w ' i" := (fcp_index w i) (at level 9, i at level 9).

(** ** Bit arithmetic on [N] (Galette-only helpers) *)

Lemma testbit_lt_pow n d i : n < 2 ** d -> d <= i -> N.testbit n i = false.
Proof.
  intros Hn Hi; rewrite <- (N.mod_small n (2 ** d)) by exact Hn.
  apply N.mod_pow2_bits_high; lia.
Qed.

Lemma testbit_add_mul_pow x y k i : x < 2 ** k ->
  N.testbit (x + y * 2 ** k) i =
  if i <? k then N.testbit x i else N.testbit y (i - k).
Proof.
  intros Hx; assert (Hk : 2 ** k <> 0) by (apply N.pow_nonzero; lia).
  destruct (N.ltb_spec i k) as [Hi|Hi].
  - rewrite <- N.mod_pow2_bits_low with (n := k) by exact Hi.
    rewrite N.Div0.mod_add, N.mod_small by exact Hx; reflexivity.
  - replace i with ((i - k) + k) at 1 by lia.
    rewrite <- N.div_pow2_bits, N.div_add by exact Hk.
    rewrite N.div_small by exact Hx; reflexivity.
Qed.

Lemma testbit_mul_pow y k i :
  N.testbit (y * 2 ** k) i = if i <? k then false else N.testbit y (i - k).
Proof.
  rewrite <- (N.add_0_l (y * 2 ** k)), testbit_add_mul_pow
    by (apply N.neq_0_lt_0, N.pow_nonzero; lia).
  destruct (i <? k); [apply N.bits_0|reflexivity].
Qed.

Lemma SBIT_mul b n : SBIT b n = (if b then 1 else 0) * 2 ** n.
Proof. unfold SBIT; destruct b; lia. Qed.

Lemma SUM_SBIT_lt n f : SUM n (fun i => SBIT (f i) i) < 2 ** n.
Proof.
  induction n as [|n IH] using N.peano_ind; [cbn; lia|].
  rewrite (proj2 (SUM_def n _)), N.pow_succ_r'; cbv beta; rewrite (SBIT_mul (f n) n); destruct (f n); lia.
Qed.

Lemma testbit_SUM_SBIT n f i :
  N.testbit (SUM n (fun i => SBIT (f i) i)) i = (i <? n) && f i.
Proof.
  induction n as [|n IH] using N.peano_ind.
  - rewrite (proj1 (SUM_def 0 _)); destruct (N.ltb_spec i 0); [lia|]; apply N.bits_0.
  - rewrite (proj2 (SUM_def n _)); cbv beta.
    rewrite SBIT_mul, testbit_add_mul_pow by apply SUM_SBIT_lt.
    destruct (N.ltb_spec i n) as [Hi|Hi].
    + rewrite IH; destruct (N.ltb_spec i n), (N.ltb_spec i (N.succ n)); try lia;
        reflexivity.
    + destruct (N.ltb_spec i (N.succ n)) as [Hi'|Hi'].
      * replace i with n by lia; rewrite N.sub_diag.
        destruct (f n); reflexivity.
      * destruct (f n); cbn [andb];
          [apply N.bits_above_log2; change (N.log2 1) with 0; lia|apply N.bits_0].
Qed.

Lemma BITS_testbit h l n i :
  N.testbit (BITS h l n) i = (i + l <=? h) && N.testbit n (i + l).
Proof.
  unfold BITS, MOD_2EXP, DIV_2EXP.
  destruct (N.leb_spec (i + l) h) as [H|H].
  - rewrite N.mod_pow2_bits_low by lia; apply N.div_pow2_bits.
  - rewrite N.mod_pow2_bits_high by lia; reflexivity.
Qed.

Lemma testbit_ones_sub x d i : x < 2 ** d -> i < d ->
  N.testbit (2 ** d - 1 - x) i = negb (N.testbit x i).
Proof.
  intros Hx Hi.
  assert (Hl : N.log2 x < d).
  { destruct (N.eq_dec x 0) as [->|Hz]; [cbn; lia|].
    apply N.log2_lt_pow2; lia. }
  rewrite <- N.lnot_spec_low with (n := d) by exact Hi.
  rewrite N.lnot_sub_low, N.ones_equiv by exact Hl; f_equal; lia.
Qed.

Lemma ODD_odd n : ODD n = N.odd n.
Proof. reflexivity. Qed.

Section Bits.
Context {a : N}.

Lemma dimindex_pos : 0 < dimindex a.
Proof. apply DIMINDEX_GT_0. Qed.

Lemma fcp_index_testbit (w : word a) i : w ' i = N.testbit (w2n w) i.
Proof. apply BIT_testbit. Qed.

Lemma fcp_index_high (w : word a) i : dimindex a <= i -> w ' i = false.
Proof.
  intros Hi; rewrite fcp_index_testbit.
  apply testbit_lt_pow with (d := dimindex a); [apply w2n_lt|exact Hi].
Qed.

(** HOL [fcpTheory.FCP_BETA] at word type. *)
Lemma fcp_index_FCP (f : N -> bool) i :
  i < dimindex a -> (FCP f : word a) ' i = f i.
Proof.
  intros Hi; unfold FCP; rewrite fcp_index_testbit, w2n_n2w.
  rewrite N.mod_small by apply SUM_SBIT_lt.
  rewrite testbit_SUM_SBIT; destruct (N.ltb_spec i (dimindex a)); [reflexivity|lia].
Qed.

Lemma w2n_FCP (f : N -> bool) :
  w2n (FCP f : word a) = SUM (dimindex a) (fun i => SBIT (f i) i).
Proof. unfold FCP; rewrite w2n_n2w; apply N.mod_small, SUM_SBIT_lt. Qed.

(** Bit extensionality (one direction of HOL [fcpTheory.CART_EQ]). *)
Lemma word_bit_ext (v w : word a) :
  (forall i, i < dimindex a -> v ' i = w ' i) -> v = w.
Proof.
  intros H; apply word_eq_w2n, N.bits_inj; intros i.
  destruct (N.ltb_spec i (dimindex a)) as [Hi|Hi].
  - rewrite <- !fcp_index_testbit; apply H, Hi.
  - rewrite <- !fcp_index_testbit, !fcp_index_high by exact Hi; reflexivity.
Qed.

Lemma word_bit_ext_iff (v w : word a) :
  (forall i, i < dimindex a -> v ' i = w ' i) <-> v = w.
Proof. split; [apply word_bit_ext|intros -> i _; reflexivity]. Qed.

Lemma fcp_index_n2w n i : i < dimindex a -> (n2w n : word a) ' i = BIT i n.
Proof.
  intros Hi; unfold fcp_index; rewrite w2n_n2w, dimword_pow.
  apply BIT_mod_pow, Hi.
Qed.

(** ** HOL's defining equations *)

(*! HOL "HOL/src/n-bit/wordsScript.sml" "w2n_def" *)
Theorem w2n_def : forall w : word a,
  w2n w = SUM (dimindex a) (fun i => SBIT (w ' i) i).
Proof.
  intros w; rewrite <- w2n_FCP; f_equal; symmetry; apply word_bit_ext.
  intros i Hi; apply fcp_index_FCP, Hi.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "n2w_def" *)
Theorem n2w_def : forall n, (n2w n : word a) = FCP (fun i => BIT i n).
Proof.
  intros n; apply word_bit_ext; intros i Hi.
  rewrite fcp_index_FCP, fcp_index_n2w by exact Hi; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_1comp_def" *)
Theorem word_1comp_def : forall w : word a,
  word_1comp w = FCP (fun i => negb (w ' i)).
Proof.
  intros w; apply word_bit_ext; intros i Hi.
  rewrite fcp_index_FCP by exact Hi; unfold word_1comp.
  rewrite fcp_index_n2w, BIT_testbit, !fcp_index_testbit by exact Hi.
  apply testbit_ones_sub; [apply w2n_lt|exact Hi].
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_and_def" *)
Theorem word_and_def : forall v w : word a,
  word_and v w = FCP (fun i => v ' i && w ' i).
Proof.
  intros v w; apply word_bit_ext; intros i Hi.
  rewrite fcp_index_FCP by exact Hi; unfold word_and.
  rewrite fcp_index_n2w, BIT_testbit, !fcp_index_testbit by exact Hi.
  apply N.land_spec.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_or_def" *)
Theorem word_or_def : forall v w : word a,
  word_or v w = FCP (fun i => v ' i || w ' i).
Proof.
  intros v w; apply word_bit_ext; intros i Hi.
  rewrite fcp_index_FCP by exact Hi; unfold word_or.
  rewrite fcp_index_n2w, BIT_testbit, !fcp_index_testbit by exact Hi.
  apply N.lor_spec.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_xor_def" *)
Theorem word_xor_def : forall v w : word a,
  word_xor v w = FCP (fun i => negb (Bool.eqb (v ' i) (w ' i))).
Proof.
  intros v w; apply word_bit_ext; intros i Hi.
  rewrite fcp_index_FCP by exact Hi; unfold word_xor.
  rewrite fcp_index_n2w, BIT_testbit, !fcp_index_testbit by exact Hi.
  rewrite N.lxor_spec; destruct (N.testbit (w2n v) i), (N.testbit (w2n w) i);
    reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_lsb_def" *)
Theorem word_lsb_def : forall w : word a, word_lsb w = w ' 0.
Proof.
  intros w; unfold word_lsb; rewrite fcp_index_testbit, N.bit0_odd.
  reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_msb_def" *)
Theorem word_msb_def : forall w : word a, word_msb w = w ' (dimindex a - 1).
Proof. reflexivity. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_bits_def" *)
Theorem word_bits_def : forall h l,
  word_bits h l =
  (fun w : word a => FCP (fun i => (i + l <=? MIN h (dimindex a - 1)) && w ' (i + l))).
Proof.
  intros h l; extensionality w; apply word_bit_ext; intros i Hi.
  rewrite fcp_index_FCP by exact Hi; unfold word_bits.
  rewrite fcp_index_n2w, BIT_testbit, BITS_testbit, fcp_index_testbit by exact Hi.
  reflexivity.
Qed.

Lemma fcp_index_word_bits h l (w : word a) i : i < dimindex a ->
  (word_bits h l w) ' i = (i + l <=? MIN h (dimindex a - 1)) && w ' (i + l).
Proof. intros Hi; rewrite word_bits_def, fcp_index_FCP by exact Hi; reflexivity. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_lsl_def" *)
Theorem word_lsl_def : forall (w : word a) n,
  word_lsl w n = FCP (fun i => (i <? dimindex a) && (n <=? i) && w ' (i - n)).
Proof.
  intros w n; apply word_bit_ext; intros i Hi.
  rewrite fcp_index_FCP by exact Hi; unfold word_lsl.
  destruct (N.ltb_spec i (dimindex a)); [|lia].
  destruct (N.ltb_spec (dimindex a - 1) n) as [Hn|Hn].
  - rewrite fcp_index_n2w by exact Hi.
    rewrite BIT_testbit, N.bits_0.
    destruct (N.leb_spec n i); [lia|reflexivity].
  - rewrite fcp_index_n2w, BIT_testbit, testbit_mul_pow, fcp_index_testbit by exact Hi.
    destruct (N.ltb_spec i n), (N.leb_spec n i); try lia; reflexivity.
Qed.

Lemma fcp_index_word_lsl (w : word a) n i : i < dimindex a ->
  (word_lsl w n) ' i = (n <=? i) && w ' (i - n).
Proof.
  intros Hi; rewrite word_lsl_def, fcp_index_FCP by exact Hi.
  destruct (N.ltb_spec i (dimindex a)); [reflexivity|lia].
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_lsr_def" *)
Theorem word_lsr_def : forall (w : word a) n,
  word_lsr w n = FCP (fun i => (i + n <? dimindex a) && w ' (i + n)).
Proof.
  intros w n; apply word_bit_ext; intros i Hi.
  rewrite fcp_index_FCP by exact Hi; unfold word_lsr.
  rewrite fcp_index_word_bits by exact Hi.
  pose proof dimindex_pos.
  rewrite MIN_min, N.min_id.
  destruct (N.leb_spec (i + n) (dimindex a - 1)), (N.ltb_spec (i + n) (dimindex a));
    try lia; reflexivity.
Qed.

Lemma fcp_index_word_lsr (w : word a) n i : i < dimindex a ->
  (word_lsr w n) ' i = (i + n <? dimindex a) && w ' (i + n).
Proof. intros Hi; rewrite word_lsr_def, fcp_index_FCP by exact Hi; reflexivity. Qed.

Lemma fcp_index_word_or (v w : word a) i : i < dimindex a ->
  (word_or v w) ' i = v ' i || w ' i.
Proof. intros Hi; rewrite word_or_def, fcp_index_FCP by exact Hi; reflexivity. Qed.

Lemma fcp_index_word_and (v w : word a) i : i < dimindex a ->
  (word_and v w) ' i = v ' i && w ' i.
Proof. intros Hi; rewrite word_and_def, fcp_index_FCP by exact Hi; reflexivity. Qed.

Lemma fcp_index_word_xor (v w : word a) i : i < dimindex a ->
  (word_xor v w) ' i = negb (Bool.eqb (v ' i) (w ' i)).
Proof. intros Hi; rewrite word_xor_def, fcp_index_FCP by exact Hi; reflexivity. Qed.

Lemma fcp_index_word_1comp (w : word a) i : i < dimindex a ->
  (word_1comp w) ' i = negb (w ' i).
Proof. intros Hi; rewrite word_1comp_def, fcp_index_FCP by exact Hi; reflexivity. Qed.

Lemma fcp_index_word_T i : i < dimindex a -> (word_T : word a) ' i = true.
Proof.
  intros Hi; unfold word_T, UINT_MAX.
  rewrite fcp_index_n2w, BIT_testbit by exact Hi.
  rewrite dimword_pow, <- (N.sub_0_r (2 ** dimindex a - 1)).
  rewrite testbit_ones_sub by (try apply N.neq_0_lt_0, N.pow_nonzero; lia).
  rewrite N.bits_0; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_asr_def" *)
Theorem word_asr_def : forall (w : word a) n,
  word_asr w n =
  FCP (fun i => if dimindex a <=? i + n then word_msb w else w ' (i + n)).
Proof.
  intros w n; apply word_bit_ext; intros i Hi.
  rewrite fcp_index_FCP by exact Hi; unfold word_asr.
  destruct (word_msb w) eqn:Hm.
  - rewrite fcp_index_word_or, fcp_index_word_lsl, fcp_index_word_lsr by exact Hi.
    destruct (N.leb_spec (dimindex a) (i + n)) as [H|H].
    + rewrite fcp_index_word_T by lia.
      rewrite MIN_min; destruct (N.leb_spec (dimindex a - N.min n (dimindex a)) i);
        [reflexivity|lia].
    + rewrite MIN_min; destruct (N.leb_spec (dimindex a - N.min n (dimindex a)) i);
        [lia|]; destruct (N.ltb_spec (i + n) (dimindex a)); [reflexivity|lia].
  - rewrite fcp_index_word_lsr by exact Hi.
    destruct (N.leb_spec (dimindex a) (i + n)) as [H|H].
    + destruct (N.ltb_spec (i + n) (dimindex a)); [lia|].
      reflexivity.
    + destruct (N.ltb_spec (i + n) (dimindex a)); [reflexivity|lia].
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_ror_def" *)
Theorem word_ror_def : forall (w : word a) n,
  word_ror w n = FCP (fun i => w ' ((i + n) MOD dimindex a)).
Proof.
  intros w n; apply word_bit_ext; intros i Hi.
  rewrite fcp_index_FCP by exact Hi; unfold word_ror; cbv zeta.
  pose proof dimindex_pos as Hd.
  set (d := dimindex a) in *.
  set (x := n MOD d).
  assert (Hx : x < d) by (apply N.mod_lt; lia).
  rewrite fcp_index_n2w, BIT_testbit by exact Hi.
  rewrite testbit_add_mul_pow by (apply N.lt_le_trans with (2 ** (N.succ (d - 1) - x));
    [apply BITS_lt|apply N.pow_le_mono_r; lia]).
  rewrite fcp_index_testbit.
  assert (Hm : (i + n) MOD d = (i + x) MOD d).
  { unfold x; rewrite N.Div0.add_mod_idemp_r; reflexivity. }
  rewrite Hm.
  destruct (N.ltb_spec i (d - x)) as [H|H].
  - rewrite BITS_testbit, N.mod_small by lia.
    destruct (N.leb_spec (i + x) (d - 1)); [reflexivity|lia].
  - rewrite BITS_testbit.
    assert (Hx0 : 0 < x) by lia.
    replace ((i + x) MOD d) with (i - (d - x) + 0).
    + destruct (N.leb_spec (i - (d - x) + 0) (x - 1)); [reflexivity|lia].
    + rewrite N.add_0_r.
      replace (i + x) with ((i - (d - x)) + 1 * d) by lia.
      rewrite N.Div0.mod_add, N.mod_small by lia; reflexivity.
Qed.

(** ** Bit-level [n2w] theorems *)

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_index" *)
Theorem word_index : forall n i,
  i < dimindex a -> (n2w n : word a) ' i = BIT i n.
Proof. intros n i; apply fcp_index_n2w. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_lsb" 1066 *)
Theorem word_lsb_thm : (word_lsb : word a -> bool) = word_bit 0.
Proof.
  extensionality w; rewrite word_lsb_def; unfold word_bit.
  destruct (N.leb_spec 0 (dimindex a - 1)); [reflexivity|lia].
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_msb" 1072 *)
Theorem word_msb_thm : (word_msb : word a -> bool) = word_bit (dimindex a - 1).
Proof.
  extensionality w; rewrite word_msb_def; unfold word_bit.
  rewrite N.leb_refl; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_EQ" *)
Theorem WORD_EQ : forall v w : word a,
  (forall x, x < dimindex a -> word_bit x v = word_bit x w) <-> v = w.
Proof.
  intros v w; rewrite <- word_bit_ext_iff; unfold word_bit.
  split; intros H x Hx; specialize (H x Hx);
    destruct (N.leb_spec x (dimindex a - 1)); try lia; exact H.
Qed.

Lemma BITWISE_testbit n op x y i :
  N.testbit (BITWISE n op x y) i = (i <? n) && op (BIT i x) (BIT i y).
Proof.
  assert (H : BITWISE n op x y = SUM n (fun i => SBIT (op (BIT i x) (BIT i y)) i)).
  { induction n as [|n IHn] using N.peano_ind; [reflexivity|].
    rewrite (proj2 (BITWISE_def op x y n)), (proj2 (SUM_def n _)), IHn; reflexivity. }
  rewrite H, testbit_SUM_SBIT; reflexivity.
Qed.

Lemma BIT_BITWISE n op x y i :
  BIT i (BITWISE n op x y) = (i <? n) && op (BIT i x) (BIT i y).
Proof. rewrite BIT_testbit; apply BITWISE_testbit. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_and_n2w" *)
Theorem word_and_n2w : forall n m,
  word_and (n2w n : word a) (n2w m) = n2w (BITWISE (dimindex a) andb n m).
Proof.
  intros n m; apply word_bit_ext; intros i Hi.
  rewrite fcp_index_word_and, !fcp_index_n2w, BIT_BITWISE by exact Hi.
  destruct (N.ltb_spec i (dimindex a)); [reflexivity|lia].
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_or_n2w" *)
Theorem word_or_n2w : forall n m,
  word_or (n2w n : word a) (n2w m) = n2w (BITWISE (dimindex a) orb n m).
Proof.
  intros n m; apply word_bit_ext; intros i Hi.
  rewrite fcp_index_word_or, !fcp_index_n2w, BIT_BITWISE by exact Hi.
  destruct (N.ltb_spec i (dimindex a)); [reflexivity|lia].
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_xor_n2w" *)
Theorem word_xor_n2w : forall n m,
  word_xor (n2w n : word a) (n2w m) =
  n2w (BITWISE (dimindex a) (fun x y => negb (Bool.eqb x y)) n m).
Proof.
  intros n m; apply word_bit_ext; intros i Hi.
  rewrite fcp_index_word_xor, !fcp_index_n2w, BIT_BITWISE by exact Hi.
  destruct (N.ltb_spec i (dimindex a)); [reflexivity|lia].
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_2comp_n2w" *)
Theorem word_2comp_n2w : forall n,
  word_2comp (n2w n : word a) = n2w (dimword a - n MOD dimword a).
Proof. reflexivity. Qed.

End Bits.

(** ** Width changes *)

Section Widths.
Context {a b : N}.

Lemma BITS_0_mod h n : BITS h 0 n = n MOD 2 ** N.succ h.
Proof.
  unfold BITS, MOD_2EXP, DIV_2EXP; rewrite N.sub_0_r, N.pow_0_r, N.div_1_r.
  reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "w2w_n2w" *)
Theorem w2w_n2w : forall n,
  (w2w (n2w n : word a) : word b) =
  if dimindex b <=? dimindex a then n2w n else n2w (BITS (dimindex a - 1) 0 n).
Proof.
  intros n; unfold w2w; rewrite w2n_n2w, BITS_0_mod.
  pose proof (DIMINDEX_GT_0 a) as Ha; pose proof (DIMINDEX_GT_0 b) as Hb.
  replace (N.succ (dimindex a - 1)) with (dimindex a) by lia.
  destruct (N.leb_spec (dimindex b) (dimindex a)) as [Hle|Hle]; [|reflexivity].
  apply n2w_11; rewrite !dimword_pow.
  apply N.bits_inj; intros j.
  destruct (N.ltb_spec j (dimindex b)).
  - rewrite !N.mod_pow2_bits_low by lia; reflexivity.
  - rewrite !N.mod_pow2_bits_high by lia; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "w2n_w2w" *)
Theorem w2n_w2w : forall w : word a,
  w2n (w2w w : word b) =
  if dimindex a <=? dimindex b then w2n w
  else w2n (word_bits (dimindex b - 1) 0 w).
Proof.
  intros w; unfold w2w, word_bits; rewrite !w2n_n2w, BITS_0_mod.
  pose proof (DIMINDEX_GT_0 a) as Ha; pose proof (DIMINDEX_GT_0 b) as Hb.
  pose proof (w2n_lt w) as Hw; rewrite dimword_pow in Hw.
  destruct (N.leb_spec (dimindex a) (dimindex b)) as [Hle|Hle].
  - apply N.mod_small; rewrite dimword_pow.
    apply N.lt_le_trans with (1 := Hw), N.pow_le_mono_r; lia.
  - rewrite MIN_min; replace (N.min (dimindex b - 1) (dimindex a - 1))
      with (dimindex b - 1) by lia.
    replace (N.succ (dimindex b - 1)) with (dimindex b) by lia.
    rewrite (N.mod_small (w2n w MOD 2 ** dimindex b)); [reflexivity|].
    apply N.lt_le_trans with (2 ** dimindex b);
      [apply N.mod_lt, N.pow_nonzero; lia|].
    rewrite dimword_pow; apply N.pow_le_mono_r; lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "w2n_w2w_le" *)
Theorem w2n_w2w_le : forall w : word a, w2n (w2w w : word b) <= w2n w.
Proof.
  intros w; unfold w2w; rewrite w2n_n2w; apply N.Div0.mod_le.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "w2w_lt" *)
Theorem w2w_lt : forall w : word a, w2n (w2w w : word b) < dimword a.
Proof. intros w; eapply N.le_lt_trans; [apply w2n_w2w_le|apply w2n_lt]. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "w2w_0" *)
Theorem w2w_0 : (w2w (n2w 0 : word a) : word b) = n2w 0.
Proof. unfold w2w; rewrite w2n_n2w, N.Div0.mod_0_l; reflexivity. Qed.

Lemma fcp_index_w2w (w : word a) i : i < dimindex b ->
  (w2w w : word b) ' i = (i <? dimindex a) && w ' i.
Proof.
  intros Hi; unfold w2w; rewrite fcp_index_n2w by exact Hi.
  rewrite BIT_testbit, fcp_index_testbit.
  destruct (N.ltb_spec i (dimindex a)); [reflexivity|].
  apply testbit_lt_pow with (dimindex a); [apply w2n_lt|exact H].
Qed.

End Widths.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "w2w_id" *)
Theorem w2w_id : forall {a} (w : word a), (w2w w : word a) = w.
Proof. intros a w; unfold w2w; apply n2w_w2n. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "w2w_w2w" *)
Theorem w2w_w2w : forall {a b c} (w : word a),
  (w2w (w2w w : word b) : word c) = w2w (word_bits (dimindex b - 1) 0 w).
Proof.
  intros a b c w; apply word_bit_ext; intros i Hi.
  pose proof (DIMINDEX_GT_0 b) as Hb0.
  rewrite (fcp_index_w2w (b := c) (w2w w : word b)) by exact Hi.
  rewrite (fcp_index_w2w (b := c) (word_bits (dimindex b - 1) 0 w)) by exact Hi.
  destruct (N.ltb_spec i (dimindex a)) as [Ha|Ha]; cbn [andb].
  - rewrite fcp_index_word_bits, N.add_0_r, MIN_min by exact Ha.
    destruct (N.ltb_spec i (dimindex b)) as [Hb|Hb]; cbn [andb].
    + rewrite fcp_index_w2w by exact Hb.
      destruct (N.ltb_spec i (dimindex a)); [|lia].
      destruct (N.leb_spec i (N.min (dimindex b - 1) (dimindex a - 1)));
        [reflexivity|lia].
    + destruct (N.leb_spec i (N.min (dimindex b - 1) (dimindex a - 1)));
        [lia|reflexivity].
  - destruct (N.ltb_spec i (dimindex b)) as [Hb|Hb]; cbn [andb]; [|reflexivity].
    rewrite fcp_index_w2w by exact Hb.
    destruct (N.ltb_spec i (dimindex a)); [lia|reflexivity].
Qed.
