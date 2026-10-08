(** * HOL4 [alignment]: address alignment

    HOL defines [align p w] as the word slice [(dimindex(:'a) - 1 '' p) w]
    ([align_def]).  [word_slice] is not (yet) part of Galette's [words], so
    [align] is defined here by HOL's arithmetic characterisation [align_w2n]
    (which is proved and tagged); [align_def] itself is not tagged.

    [byte_align]/[byte_aligned] use [LOG2 (dimindex a DIV 8)].  HOL's [LOG2 0]
    is unspecified, while Galette's [LOG2] (bit.v) is [N.log2], so for
    widths below 8 the value is fixed here where HOL leaves it open; the
    defining equations are nevertheless syntactically HOL's. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.n_bit Require Import words.
Open Scope N_scope.

Section Alignment.
Context {a : N}.

(** ** Definitions *)

(** HOL [align] (defining equation: [align_w2n] below). *)
Definition align (p : N) (w : word a) : word a :=
  n2w (w2n w DIV 2 ** p * 2 ** p).

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "aligned_def" *)
Definition aligned (p : N) (w : word a) : bool := bool_decide (align p w = w).

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "byte_align_def" *)
Definition byte_align (w : word a) : word a := align (LOG2 (dimindex a DIV 8)) w.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "byte_aligned_def" *)
Definition byte_aligned (w : word a) : bool := aligned (LOG2 (dimindex a DIV 8)) w.

(** ** Local bit-level helpers (Galette infrastructure, untagged) *)

Lemma pow2_ne0 k : 2 ** k <> 0.
Proof. apply N.pow_nonzero; lia. Qed.

Lemma dimword_eq : dimword a = 2 ** dimindex a.
Proof. reflexivity. Qed.

Lemma tb_w2n_high (w : word a) i : dimindex a <= i -> N.testbit (w2n w) i = false.
Proof.
  intros Hi. rewrite <- (N.mod_small (w2n w) (2 ** dimindex a)) by apply w2n_lt.
  apply N.mod_pow2_bits_high; exact Hi.
Qed.

Lemma tb_w2n_n2w n i : i < dimindex a ->
  N.testbit (w2n (n2w n : word a)) i = N.testbit n i.
Proof. intros Hi; rewrite w2n_n2w, dimword_eq; apply N.mod_pow2_bits_low, Hi. Qed.

Lemma word_bit_ext (v w : word a) :
  (forall i, i < dimindex a -> N.testbit (w2n v) i = N.testbit (w2n w) i) -> v = w.
Proof.
  intros H; apply word_eq_w2n, N.bits_inj; intros i.
  destruct (N.lt_ge_cases i (dimindex a)) as [Hi|Hi].
  - apply H, Hi.
  - rewrite !tb_w2n_high by exact Hi; reflexivity.
Qed.

Lemma divmul_shift n p : n DIV 2 ** p * 2 ** p = N.shiftl (N.shiftr n p) p.
Proof. rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2; reflexivity. Qed.

Lemma tb_divmul n p i :
  N.testbit (n DIV 2 ** p * 2 ** p) i = (p <=? i) && N.testbit n i.
Proof.
  rewrite divmul_shift. destruct (N.leb_spec p i).
  - rewrite N.shiftl_spec_high', N.shiftr_spec' by lia.
    cbn; f_equal; lia.
  - rewrite N.shiftl_spec_low by lia; reflexivity.
Qed.

Lemma divmul_le n p : n DIV 2 ** p * 2 ** p <= n.
Proof.
  rewrite (N.mul_comm (n DIV 2 ** p)).
  pose proof (N.div_mod n (2 ** p) (pow2_ne0 p)).
  set (q := n DIV 2 ** p) in *; set (r := n MOD 2 ** p) in *; set (P := 2 ** p) in *.
  lia.
Qed.

Lemma w2n_align p (w : word a) : w2n (align p w) = w2n w DIV 2 ** p * 2 ** p.
Proof.
  unfold align; rewrite w2n_n2w; apply N.mod_small.
  pose proof (divmul_le (w2n w) p); pose proof (w2n_lt w); lia.
Qed.

Lemma tb_align p (w : word a) i :
  N.testbit (w2n (align p w)) i = (p <=? i) && N.testbit (w2n w) i.
Proof. rewrite w2n_align; apply tb_divmul. Qed.

Lemma mod_pow2_0_bits n p :
  n MOD 2 ** p = 0 <-> (forall i, i < p -> N.testbit n i = false).
Proof.
  split.
  - intros H i Hi. rewrite <- (N.mod_pow2_bits_low n p i Hi), H.
    apply N.bits_0.
  - intros H; apply N.bits_inj; intros i; rewrite N.bits_0.
    destruct (N.lt_ge_cases i p).
    + rewrite N.mod_pow2_bits_low by lia; apply H; lia.
    + apply N.mod_pow2_bits_high; lia.
Qed.

Lemma aligned_iff p (w : word a) : aligned p w <-> w2n w MOD 2 ** p = 0.
Proof.
  unfold aligned, is_true; rewrite bool_decide_spec; split.
  - intros H; apply (f_equal w2n) in H; rewrite w2n_align in H.
    pose proof (N.div_mod (w2n w) (2 ** p) (pow2_ne0 p)). lia.
  - intros H; apply word_eq_w2n; rewrite w2n_align.
    pose proof (N.div_mod (w2n w) (2 ** p) (pow2_ne0 p)). lia.
Qed.

Lemma aligned_bits p (w : word a) :
  aligned p w <-> (forall i, i < p -> N.testbit (w2n w) i = false).
Proof. rewrite aligned_iff; apply mod_pow2_0_bits. Qed.

Lemma ODD_odd n : ODD n = N.odd n.
Proof. reflexivity. Qed.

Lemma w2n_0 : w2n (n2w 0 : word a) = 0.
Proof. rewrite w2n_n2w; apply N.Div0.mod_0_l. Qed.

Lemma word_eq_0 (w : word a) : w = n2w 0 <-> w2n w = 0.
Proof.
  split; [intros ->; apply w2n_0|intros H; apply word_eq_w2n; rewrite H, w2n_0; reflexivity].
Qed.

Lemma w2n_add (v w : word a) : w2n (v + w)%w = (w2n v + w2n w) MOD dimword a.
Proof. reflexivity. Qed.

Lemma w2n_sub (v w : word a) :
  w2n (v - w)%w = (w2n v + (dimword a - w2n w)) MOD dimword a.
Proof.
  unfold word_sub, word_add, word_2comp; rewrite !w2n_n2w.
  apply N.Div0.add_mod_idemp_r.
Qed.

Lemma mod_dimword_mod_pow2 x p :
  p <= dimindex a -> (x MOD dimword a) MOD 2 ** p = x MOD 2 ** p.
Proof.
  intros Hp; apply N.bits_inj; intros i.
  destruct (N.lt_ge_cases i p).
  - rewrite !N.mod_pow2_bits_low by lia. rewrite dimword_eq.
    rewrite N.mod_pow2_bits_low by lia; reflexivity.
  - rewrite !N.mod_pow2_bits_high by lia; reflexivity.
Qed.

Lemma ge_dim_aligned p (w : word a) :
  dimindex a <= p -> aligned p w <-> w2n w = 0.
Proof.
  intros Hp; rewrite aligned_iff.
  pose proof (w2n_lt w); rewrite dimword_eq in H.
  assert (2 ** dimindex a <= 2 ** p) by (apply N.pow_le_mono_r; lia).
  rewrite N.mod_small by lia; reflexivity.
Qed.

(** Unsigned comparisons through [w2n] (local; HOL's [WORD_LO]/[WORD_LS]
    belong to [words]). *)
Lemma nzcv_carry (v w : word a) :
  w2n w <> 0 ->
  BIT (dimindex a) (w2n v + w2n (word_2comp w)) = (w2n w <=? w2n v).
Proof.
  intros Hw. unfold word_2comp; rewrite w2n_n2w.
  pose proof (w2n_lt v); pose proof (w2n_lt w).
  rewrite N.mod_small by lia.
  rewrite BIT_testbit, dimword_eq in *.
  set (D := 2 ** dimindex a) in *.
  assert (HD : D <> 0) by apply pow2_ne0.
  destruct (N.leb_spec (w2n w) (w2n v)).
  - replace (w2n v + (D - w2n w)) with ((w2n v - w2n w) + 1 * D) by lia.
    unfold D; rewrite N.testbit_eqb, N.div_add by apply pow2_ne0.
    rewrite N.div_small by (fold D; lia). reflexivity.
  - unfold D; rewrite N.testbit_eqb, N.div_small by (fold D; lia). reflexivity.
Qed.

Lemma word_lo_w2n (v w : word a) : word_lo v w = (w2n v <? w2n w).
Proof.
  unfold word_lo, nzcv; cbv beta iota zeta.
  destruct (N.eq_dec (w2n w) 0) as [H0|H0].
  - assert (w = n2w 0) by (apply word_eq_0, H0).
    rewrite H0, (proj2 (bool_decide_spec _) H), orb_true_r.
    destruct (w2n v); reflexivity.
  - rewrite nzcv_carry by exact H0.
    assert (bool_decide (w = n2w 0) = false).
    { destruct (bool_decide (w = n2w 0)) eqn:E; [|reflexivity].
      apply bool_decide_spec, word_eq_0 in E; contradiction. }
    rewrite H, orb_false_r.
    destruct (N.leb_spec (w2n w) (w2n v)), (N.ltb_spec (w2n v) (w2n w)); lia || reflexivity.
Qed.

Lemma bool_decide_eq_0 (x : word a) : bool_decide (x = n2w 0) = (w2n x =? 0).
Proof.
  destruct (bool_decide _) eqn:E.
  - apply bool_decide_spec, word_eq_0 in E; rewrite E; reflexivity.
  - symmetry; apply N.eqb_neq; intros H.
    apply word_eq_0, (proj2 (bool_decide_spec _)) in H; congruence.
Qed.

Lemma word_ls_w2n (v w : word a) : word_ls v w = (w2n v <=? w2n w).
Proof.
  unfold word_ls, nzcv; cbv beta iota zeta. rewrite !bool_decide_eq_0, w2n_n2w.
  pose proof (w2n_lt v) as Hv; pose proof (w2n_lt w) as Hw.
  destruct (N.eq_dec (w2n w) 0) as [H0|H0].
  - rewrite H0; cbn [N.eqb]; rewrite orb_true_r; cbn [negb orb].
    unfold word_2comp; rewrite w2n_n2w, H0, N.sub_0_r, N.Div0.mod_same, N.add_0_r,
      N.mod_small by exact Hv.
    destruct (w2n v); reflexivity.
  - rewrite nzcv_carry by exact H0.
    replace (w2n w =? 0) with false by (symmetry; apply N.eqb_neq, H0).
    rewrite orb_false_r.
    unfold word_2comp; rewrite w2n_n2w, (N.mod_small (_ - _)) by lia.
    destruct (N.leb_spec (w2n w) (w2n v)).
    + replace (w2n v + (dimword a - w2n w)) with ((w2n v - w2n w) + 1 * dimword a) by lia.
      rewrite N.Div0.mod_add, N.mod_small by lia. cbn [negb orb].
      destruct (N.eqb_spec (w2n v - w2n w) 0), (N.leb_spec (w2n v) (w2n w)); lia || reflexivity.
    + rewrite N.mod_small by lia. cbn [negb orb].
      symmetry; apply N.leb_le; lia.
Qed.

(** ** Theorems *)

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "align_w2n" *)
Theorem align_w2n : forall p (w : word a), align p w = n2w (w2n w DIV 2 ** p * 2 ** p).
Proof. reflexivity. Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "align_0" *)
Theorem align_0 : forall w : word a, align 0 w = w.
Proof.
  intros w; apply word_bit_ext; intros i _; rewrite tb_align; destruct (N.leb_spec 0 i); [reflexivity|lia].
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "align_align" *)
Theorem align_align : forall p (w : word a), align p (align p w) = align p w.
Proof.
  intros p w; apply word_bit_ext; intros i _; rewrite !tb_align.
  destruct (p <=? i); reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "aligned_align" *)
Theorem aligned_align : forall p (w : word a), aligned p (align p w).
Proof. intros p w; apply bool_decide_spec, align_align. Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "align_aligned" *)
Theorem align_aligned : forall p (w : word a), aligned p w -> align p w = w.
Proof. intros p w H; apply (proj1 (bool_decide_spec _)), H. Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "align_bitwise_and" *)
Theorem align_bitwise_and : forall p (w : word a), align p w = (w && UINT_MAXw << p)%w.
Proof.
  intros p w; apply word_bit_ext; intros i Hi.
  rewrite tb_align; unfold word_and; rewrite tb_w2n_n2w, N.land_spec by exact Hi.
  unfold word_lsl, word_T, UINT_MAX.
  destruct (N.ltb_spec (dimindex a - 1) p).
  - rewrite w2n_0, N.bits_0, andb_false_r.
    destruct (N.leb_spec p i); [lia|reflexivity].
  - rewrite tb_w2n_n2w by exact Hi. rewrite <- N.shiftl_mul_pow2.
    rewrite w2n_n2w, N.mod_small by (pose proof (ZERO_LT_dimword a); lia).
    destruct (N.leb_spec p i).
    + rewrite N.shiftl_spec_high' by lia.
      rewrite dimword_eq, N.sub_1_r, <- N.ones_equiv, N.ones_spec_low by lia.
      rewrite andb_true_r; reflexivity.
    + rewrite N.shiftl_spec_low by lia; rewrite andb_false_r; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "align_shift" *)
Theorem align_shift : forall p (w : word a), align p w = (w >>> p << p)%w.
Proof.
  intros p w; apply word_bit_ext; intros i Hi.
  rewrite tb_align. unfold word_lsl.
  destruct (N.ltb_spec (dimindex a - 1) p).
  - rewrite w2n_0, N.bits_0. destruct (N.leb_spec p i); [lia|reflexivity].
  - rewrite tb_w2n_n2w by exact Hi. rewrite <- N.shiftl_mul_pow2.
    unfold word_lsr, word_bits; rewrite w2n_n2w.
    rewrite N.mod_small.
    2:{ eapply N.lt_le_trans; [apply BITS_lt|]. rewrite dimword_eq.
        apply N.pow_le_mono_r; [lia|rewrite MIN_min; lia]. }
    destruct (N.leb_spec p i).
    + rewrite N.shiftl_spec_high' by lia.
      unfold BITS, MOD_2EXP, DIV_2EXP.
      rewrite N.mod_pow2_bits_low by (rewrite MIN_min; lia).
      rewrite N.div_pow2_bits. cbn. f_equal; lia.
    + rewrite N.shiftl_spec_low by lia; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "align_sub" *)
Theorem align_sub : forall p (w : word a),
  align p w = if decide (p = 0) then w else (w - (word_extract (p - 1) 0 w : word a))%w.
Proof.
  intros p w. destruct (decide (p = 0)) as [->|Hp]; [apply align_0|].
  apply word_eq_w2n. rewrite w2n_align, w2n_sub.
  unfold word_extract, w2w, word_bits. rewrite !w2n_n2w.
  pose proof (w2n_lt w). set (n := w2n w) in *.
  set (m := N.min p (dimindex a)).
  assert (Hb : BITS (MIN (p - 1) (dimindex a - 1)) 0 n = n MOD 2 ** m).
  { unfold BITS, MOD_2EXP, DIV_2EXP. rewrite MIN_min, N.pow_0_r, N.div_1_r.
    f_equal; f_equal; unfold m; pose proof (DIMINDEX_GT_0 a); lia. }
  rewrite Hb.
  assert (Hm : 2 ** m <= dimword a)
    by (rewrite dimword_eq; apply N.pow_le_mono_r; unfold m; lia).
  assert (Hr : n MOD 2 ** m < 2 ** m) by (apply N.mod_lt, pow2_ne0).
  rewrite !(N.mod_small (n MOD 2 ** m)) by lia.
  pose proof (N.div_mod n (2 ** m) (pow2_ne0 m)) as Hdm.
  pose proof (N.Div0.mod_le n (2 ** m)) as Hle.
  replace (n + (dimword a - n MOD 2 ** m)) with ((n - n MOD 2 ** m) + 1 * dimword a)
    by (set (r := n MOD 2 ** m) in *; set (D := dimword a) in *; lia).
  rewrite N.Div0.mod_add, N.mod_small
    by (set (r := n MOD 2 ** m) in *; set (D := dimword a) in *; lia).
  assert (Heq : n DIV 2 ** p * 2 ** p = n DIV 2 ** m * 2 ** m).
  { unfold m. destruct (N.le_ge_cases p (dimindex a)).
    - rewrite N.min_l by lia; reflexivity.
    - rewrite N.min_r by lia. rewrite dimword_eq in H.
      assert (2 ** dimindex a <= 2 ** p) by (apply N.pow_le_mono_r; lia).
      rewrite !N.div_small by lia; reflexivity. }
  rewrite Heq. rewrite (N.mul_comm (n DIV 2 ** m)).
  set (r := n MOD 2 ** m) in *; set (q := n DIV 2 ** m) in *; set (P := 2 ** m) in *. lia.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "aligned_extract" *)
Theorem aligned_extract : forall p (w : word a),
  aligned p w <-> p = 0 \/ (word_extract (p - 1) 0 w : word a) = n2w 0.
Proof.
  intros p w. destruct (N.eq_dec p 0) as [->|Hp].
  - split; [left; reflexivity|intros _; apply bool_decide_spec, align_0].
  - rewrite aligned_iff, word_eq_0.
    unfold word_extract, w2w, word_bits; rewrite !w2n_n2w.
    pose proof (w2n_lt w). set (n := w2n w) in *.
    set (m := N.min p (dimindex a)).
    assert (Hb : BITS (MIN (p - 1) (dimindex a - 1)) 0 n = n MOD 2 ** m).
    { unfold BITS, MOD_2EXP, DIV_2EXP. rewrite MIN_min, N.pow_0_r, N.div_1_r.
      f_equal; f_equal; unfold m; pose proof (DIMINDEX_GT_0 a); lia. }
    rewrite Hb.
    assert (Hm : 2 ** m <= dimword a)
      by (rewrite dimword_eq; apply N.pow_le_mono_r; unfold m; lia).
    assert (Hr : n MOD 2 ** m < 2 ** m) by (apply N.mod_lt, pow2_ne0).
    rewrite !(N.mod_small (n MOD 2 ** m)) by lia.
    assert (Heq : n MOD 2 ** p = n MOD 2 ** m).
    { unfold m. destruct (N.le_ge_cases p (dimindex a)).
      - rewrite N.min_l by lia; reflexivity.
      - rewrite N.min_r by lia. rewrite dimword_eq in H.
        assert (2 ** dimindex a <= 2 ** p) by (apply N.pow_le_mono_r; lia).
        rewrite !N.mod_small by lia; reflexivity. }
    rewrite Heq. split; [intros; right; assumption|intros [|]; [lia|assumption]].
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "aligned_0" *)
Theorem aligned_0 :
  (forall p, aligned p (n2w 0 : word a)) /\ (forall w : word a, aligned 0 w).
Proof.
  split.
  - intros p; apply aligned_iff; rewrite w2n_0; apply N.Div0.mod_0_l.
  - intros w; apply aligned_iff; rewrite N.pow_0_r; apply N.mod_1_r.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "aligned_1_lsb" *)
Theorem aligned_1_lsb : forall w : word a, aligned 1 w = negb (word_lsb w).
Proof.
  intros w; unfold word_lsb. rewrite <- N.bit0_odd.
  pose proof (N.bit0_mod (w2n w)) as Hb.
  assert (H := aligned_iff 1 w). change (2 ** 1) with 2 in H.
  unfold is_true in H; destruct H as [H1 H2].
  destruct (aligned 1 w), (N.testbit (w2n w) 0); cbn [N.b2n] in Hb; try reflexivity.
  - specialize (H1 eq_refl); lia.
  - specialize (H2 (eq_sym Hb)); discriminate.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "aligned_ge_dim" *)
Theorem aligned_ge_dim : forall p (w : word a),
  dimindex a <= p -> (aligned p w <-> w = n2w 0).
Proof. intros p w Hp; rewrite ge_dim_aligned, word_eq_0 by exact Hp; reflexivity. Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "aligned_bitwise_and" *)
Theorem aligned_bitwise_and : forall p (w : word a),
  aligned p w <-> (w && n2w (2 ** p - 1))%w = n2w 0.
Proof.
  intros p w. rewrite aligned_bits, word_eq_0. unfold word_and; rewrite w2n_n2w.
  assert (Hl : N.land (w2n w) (w2n (n2w (2 ** p - 1) : word a)) = w2n w MOD 2 ** p).
  { apply N.bits_inj; intros i. rewrite N.land_spec.
    destruct (N.lt_ge_cases i (dimindex a)).
    - rewrite tb_w2n_n2w by lia. rewrite N.sub_1_r, <- N.ones_equiv.
      destruct (N.lt_ge_cases i p).
      + rewrite N.ones_spec_low, N.mod_pow2_bits_low by lia; apply andb_true_r.
      + rewrite N.ones_spec_high, N.mod_pow2_bits_high by lia; apply andb_false_r.
    - rewrite tb_w2n_high by lia. destruct (N.lt_ge_cases i p).
      + rewrite N.mod_pow2_bits_low by lia. symmetry; apply tb_w2n_high; lia.
      + rewrite N.mod_pow2_bits_high by lia; reflexivity. }
  rewrite Hl, N.mod_small.
  2:{ pose proof (N.Div0.mod_le (w2n w) (2 ** p)); pose proof (w2n_lt w); lia. }
  symmetry; apply mod_pow2_0_bits.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "aligned_add_sub" *)
Theorem aligned_add_sub : forall p (a0 : word a) b,
  aligned p b ->
  aligned p (a0 + b)%w = aligned p a0 /\ aligned p (a0 - b)%w = aligned p a0.
Proof.
  intros p a0 b Hb.
  assert (Hiff : forall x y : word a, (aligned p x <-> aligned p y) -> aligned p x = aligned p y).
  { intros x y H; apply Bool.eq_true_iff_eq, H. }
  destruct (N.le_gt_cases (dimindex a) p) as [Hp|Hp].
  - apply ge_dim_aligned in Hb; [|exact Hp].
    assert (b = n2w 0) by (apply word_eq_0, Hb). subst b.
    assert (E1 : (a0 + n2w 0)%w = a0)
      by (apply word_eq_w2n; rewrite w2n_add, w2n_0, N.add_0_r; apply N.mod_small, w2n_lt).
    assert (E2 : (a0 - n2w 0)%w = a0)
      by (apply word_eq_w2n; rewrite w2n_sub, w2n_0, N.sub_0_r, N.Div0.add_mod,
            N.Div0.mod_same, N.add_0_r, N.Div0.mod_mod; apply N.mod_small, w2n_lt).
    rewrite E1, E2; split; reflexivity.
  - rewrite aligned_iff in Hb. split; apply Hiff; rewrite !aligned_iff.
    + rewrite w2n_add, mod_dimword_mod_pow2 by lia.
      rewrite N.Div0.add_mod, Hb, N.add_0_r, N.Div0.mod_mod; reflexivity.
    + rewrite w2n_sub, mod_dimword_mod_pow2 by lia.
      assert (Hd : dimword a MOD 2 ** p = 0).
      { rewrite dimword_eq. replace (dimindex a) with ((dimindex a - p) + p) by lia.
        rewrite N.pow_add_r; apply N.Div0.mod_mul. }
      assert (Hs : (dimword a - w2n b) MOD 2 ** p = 0).
      { apply N.Div0.mod_divides in Hd as [k Hk], Hb as [j Hj].
        pose proof (w2n_lt b).
        rewrite Hk, Hj, <- N.mul_sub_distr_l, N.mul_comm; apply N.Div0.mod_mul. }
      rewrite N.Div0.add_mod, Hs, N.add_0_r, N.Div0.mod_mod; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "aligned_add_sub_cor" *)
Theorem aligned_add_sub_cor : forall p (a0 : word a) b,
  aligned p a0 /\ aligned p b -> aligned p (a0 + b)%w /\ aligned p (a0 - b)%w.
Proof.
  intros p a0 b [Ha Hb]. destruct (aligned_add_sub p a0 b Hb) as [E1 E2].
  unfold is_true in *; rewrite E1, E2; split; assumption.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "aligned_mul_shift_1" *)
Theorem aligned_mul_shift_1 : forall p (w : word a), aligned p ((n2w 1 << p) * w)%w.
Proof.
  intros p w. unfold word_lsl. destruct (N.ltb_spec (dimindex a - 1) p).
  - apply aligned_iff. unfold word_mul; rewrite w2n_0, w2n_n2w, N.mul_0_l,
      ?N.Div0.mod_0_l; reflexivity.
  - apply aligned_iff. unfold word_mul.
    pose proof (DIMINDEX_GT_0 a).
    assert (Hlt : 2 ** p < dimword a) by (rewrite dimword_eq; apply N.pow_lt_mono_r; lia).
    pose proof (pow2_ne0 p).
    rewrite !w2n_n2w, (N.mod_small 1), N.mul_1_l, (N.mod_small (2 ** p)) by lia.
    rewrite mod_dimword_mod_pow2 by lia.
    rewrite (N.mul_comm (2 ** p)); apply N.Div0.mod_mul.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "aligned_add_sub_prod" *)
Theorem aligned_add_sub_prod : forall p (w : word a) x,
  aligned p (w + (n2w 1 << p) * x)%w = aligned p w /\
  aligned p (w - (n2w 1 << p) * x)%w = aligned p w.
Proof. intros p w x; apply aligned_add_sub, aligned_mul_shift_1. Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "aligned_imp" *)
Theorem aligned_imp : forall p q (w : word a), p < q /\ aligned q w -> aligned p w.
Proof.
  intros p q w [Hpq H]. rewrite aligned_bits in *. intros i Hi; apply H; lia.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "align_add_aligned" *)
Theorem align_add_aligned : forall p (a0 b : word a),
  aligned p a0 /\ w2n b < 2 ** p -> align p (a0 + b)%w = a0.
Proof.
  intros p a0 b [Ha Hb]. rewrite aligned_iff in Ha.
  apply word_eq_w2n; rewrite w2n_align, w2n_add.
  pose proof (w2n_lt a0) as HA. pose proof (w2n_lt b) as HB.
  apply N.Div0.mod_divides in Ha as [k Hk].
  destruct (N.le_gt_cases (dimindex a) p) as [Hp|Hp].
  - assert (2 ** dimindex a <= 2 ** p) by (apply N.pow_le_mono_r; lia).
    rewrite dimword_eq in *.
    assert (k = 0) by (destruct k; [reflexivity|]; rewrite Hk in HA; nia).
    subst k. rewrite N.mul_0_r in Hk. rewrite Hk, N.add_0_l, N.mod_small by lia.
    rewrite N.div_small by lia; reflexivity.
  - rewrite dimword_eq in *.
    replace (2 ** dimindex a) with (2 ** p * 2 ** (dimindex a - p)) in *
      by (rewrite <- N.pow_add_r; f_equal; lia).
    rewrite Hk in *.
    assert (k < 2 ** (dimindex a - p)) by (apply (N.mul_lt_mono_pos_l (2 ** p));
      [pose proof (pow2_ne0 p); lia|exact HA]).
    rewrite N.mod_small by nia.
    rewrite (N.mul_comm (2 ** p) k), N.div_add_l, N.div_small by (apply pow2_ne0 || lia).
    lia.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "lt_align_eq_0" *)
Theorem lt_align_eq_0 : forall (a0 : word a) p, w2n a0 < 2 ** p -> align p a0 = n2w 0.
Proof.
  intros a0 p H; apply word_eq_w2n; rewrite w2n_align, w2n_0, N.div_small by exact H.
  reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "aligned_or" *)
Theorem aligned_or : forall n (w v : word a),
  aligned n (w || v)%w <-> aligned n w /\ aligned n v.
Proof.
  intros n w v. rewrite !aligned_bits.
  assert (Ht : forall i, N.testbit (w2n (w || v)%w) i =
                         N.testbit (w2n w) i || N.testbit (w2n v) i).
  { intros i; destruct (N.lt_ge_cases i (dimindex a)).
    - unfold word_or; rewrite tb_w2n_n2w, N.lor_spec by lia; reflexivity.
    - rewrite !tb_w2n_high by lia; reflexivity. }
  split.
  - intros H; split; intros i Hi; specialize (H i Hi); rewrite Ht in H;
      apply orb_false_iff in H; tauto.
  - intros [H1 H2] i Hi; rewrite Ht, H1, H2 by exact Hi; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "aligned_w2n" *)
Theorem aligned_w2n : forall k (w : word a), aligned k w <-> w2n w MOD 2 ** k = 0.
Proof. exact aligned_iff. Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "MOD_0_aligned" *)
Theorem MOD_0_aligned : forall n p, n MOD 2 ** p = 0 -> aligned p (n2w n : word a).
Proof.
  intros n p H. rewrite mod_pow2_0_bits in H. apply aligned_bits; intros i Hi.
  destruct (N.lt_ge_cases i (dimindex a)).
  - rewrite tb_w2n_n2w by exact H0; apply H, Hi.
  - apply tb_w2n_high, H0.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "aligned_lsl_leq" *)
Theorem aligned_lsl_leq : forall k l (w : word a), k <= l -> aligned k (w << l)%w.
Proof.
  intros k l w H. unfold word_lsl. destruct (dimindex a - 1 <? l).
  - apply (proj1 aligned_0).
  - apply MOD_0_aligned. apply mod_pow2_0_bits; intros i Hi.
    rewrite <- N.shiftl_mul_pow2, N.shiftl_spec_low by lia.
    reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "aligned_lsl" *)
Theorem aligned_lsl : forall k (w : word a), aligned k (w << k)%w.
Proof. intros k w; apply aligned_lsl_leq; lia. Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "align_align_MAX" *)
Theorem align_align_MAX : forall k l (w : word a), align k (align l w) = align (MAX k l) w.
Proof.
  intros k l w; apply word_bit_ext; intros i _. rewrite !tb_align, MAX_max.
  destruct (N.leb_spec k i), (N.leb_spec l i), (N.leb_spec (N.max k l) i);
    try lia; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "pow2_eq_0" *)
Theorem pow2_eq_0 : forall k, dimindex a <= k -> (n2w (2 ** k) : word a) = n2w 0.
Proof.
  intros k H; apply word_eq_w2n; rewrite w2n_n2w, w2n_0, dimword_eq.
  replace k with ((k - dimindex a) + dimindex a) by lia.
  rewrite N.pow_add_r; apply N.Div0.mod_mul.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "aligned_pow2" *)
Theorem aligned_pow2 : forall k, aligned k (n2w (2 ** k) : word a).
Proof. intros k; apply MOD_0_aligned, N.Div0.mod_same. Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "word_msb_align" *)
Theorem word_msb_align : forall p (w : word a),
  p < dimindex a -> word_msb (align p w) = word_msb w.
Proof.
  intros p w H; unfold word_msb; rewrite !BIT_testbit, tb_align.
  destruct (N.leb_spec p (dimindex a - 1)); [reflexivity|lia].
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "align_ls" *)
Theorem align_ls : forall p (n : word a), (align p n <=+ n)%w.
Proof.
  intros p n; unfold is_true; rewrite word_ls_w2n, w2n_align; apply N.leb_le, divmul_le.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "align_lo" *)
Theorem align_lo : forall p (n : word a), ~ aligned p n -> (align p n <+ n)%w.
Proof.
  intros p n H; unfold is_true; rewrite word_lo_w2n, w2n_align; apply N.ltb_lt.
  rewrite aligned_iff in H.
  pose proof (N.div_mod (w2n n) (2 ** p) (pow2_ne0 p)).
  rewrite (N.mul_comm (2 ** p)) in H0.
  set (q := w2n n DIV 2 ** p) in *; set (r := w2n n MOD 2 ** p) in *;
    set (P := 2 ** p) in *; lia.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "aligned_between" *)
Theorem aligned_between : forall p (n m : word a),
  ~ aligned p n /\ aligned p m /\ (align p n <+ m)%w -> (n <+ m)%w.
Proof.
  intros p n m [Hn [Hm Hlo]]. unfold is_true in Hlo |- *; rewrite word_lo_w2n in Hlo |- *.
  rewrite w2n_align in Hlo. apply N.ltb_lt in Hlo. apply N.ltb_lt.
  rewrite aligned_iff in Hn, Hm.
  destruct (N.lt_ge_cases (w2n n) (w2n m)) as [|Hge]; [assumption|exfalso].
  pose proof (N.div_mod (w2n m) (2 ** p) (pow2_ne0 p)) as Em.
  assert (w2n m DIV 2 ** p <= w2n n DIV 2 ** p) by (apply N.Div0.div_le_mono, Hge).
  assert (w2n m DIV 2 ** p * 2 ** p <= w2n n DIV 2 ** p * 2 ** p)
    by (apply N.mul_le_mono_r; assumption).
  rewrite (N.mul_comm (2 ** p)) in Em.
  set (q := w2n n DIV 2 ** p) in *; set (q' := w2n m DIV 2 ** p) in *;
    set (r := w2n m MOD 2 ** p) in *; set (P := 2 ** p) in *; lia.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "align_add_aligned_gen" *)
Theorem align_add_aligned_gen : forall p (b : word a) (a0 : word a),
  aligned p a0 -> align p (a0 + b)%w = (a0 + align p b)%w.
Proof.
  intros p b a0 Ha. rewrite aligned_iff in Ha.
  apply word_eq_w2n; rewrite w2n_align, !w2n_add, w2n_align.
  set (A := w2n a0) in *; set (B := w2n b).
  set (D := dimword a). set (P := 2 ** p).
  assert (HP : P <> 0) by apply pow2_ne0.
  assert (HD : D <> 0) by (pose proof (ZERO_LT_dimword a); unfold D; lia).
  pose proof (w2n_lt a0); pose proof (w2n_lt b). fold A B D in H, H0.
  destruct (N.le_gt_cases (dimindex a) p) as [Hp|Hp].
  - assert (D <= P) by (unfold D, P; rewrite dimword_eq; apply N.pow_le_mono_r; lia).
    rewrite N.mod_small in Ha by lia. rewrite Ha, !N.add_0_l.
    rewrite (N.mod_small B) by lia. rewrite N.div_small by lia.
    rewrite N.mul_0_l, N.Div0.mod_0_l; reflexivity.
  - assert (HPD : D = P * 2 ** (dimindex a - p))
      by (unfold D, P; rewrite dimword_eq, <- N.pow_add_r; f_equal; lia).
    set (Q := 2 ** (dimindex a - p)) in HPD.
    apply N.Div0.mod_divides in Ha as [k Hk].
    (* (A + B) mod D, with A = P k *)
    assert (E : forall x, (x MOD D) DIV P * P = (x DIV P * P) MOD D).
    { intros x. rewrite HPD.
      rewrite N.Div0.mod_mul_r, (N.mul_comm P (_ MOD Q)).
      rewrite N.div_add by exact HP. rewrite N.div_small by (apply N.mod_lt; exact HP).
      rewrite N.add_0_l.
      rewrite (N.Div0.mod_mul_r (x DIV P * P)).
      rewrite N.Div0.mod_mul, N.add_0_l, N.div_mul by exact HP.
      apply N.mul_comm. }
    rewrite E. fold P in Hk.
    rewrite Hk, (N.mul_comm P k), N.div_add_l by exact HP.
    rewrite N.mul_add_distr_r; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "byte_align_aligned" *)
Theorem byte_align_aligned : forall x : word a, byte_aligned x <-> byte_align x = x.
Proof. intros x; unfold byte_aligned, aligned, byte_align, is_true; apply bool_decide_spec. Qed.

(*! HOL "HOL/src/n-bit/alignmentScript.sml" "byte_aligned_add" *)
Theorem byte_aligned_add : forall x y : word a,
  byte_aligned x /\ byte_aligned y -> byte_aligned (x + y)%w.
Proof. intros x y H; apply (aligned_add_sub_cor _ x y H). Qed.

End Alignment.
