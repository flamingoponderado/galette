(** * HOL4 [integer_word]: two's complement representation of integers

    HOL [int] is Rocq [Z].  HOL's [&n] ([int_of_num]) is written
    [Z.of_N n]; HOL [Num i] (for [0 <= i]) is [Z.to_N i].  HOL's integer
    division [/] and modulus [%] round towards negative infinity and are
    [Z.div] / [Z.modulo]; HOL leaves [i / 0] and [i % 0] unspecified, while
    [Z.div i 0 = 0] and [Z.modulo i 0 = i] (relevant for [word_sdiv_def] and
    [word_smod_def] only).

    This theory defines integer-valued constants [INT_MIN], [INT_MAX] and
    [UINT_MAX] (the HOL constants [integer_word$INT_MIN] etc.).  They have
    the same names as the natural-number constants of [words]; in this file
    the latter are written [words.INT_MIN] etc.  A module importing both
    sees whichever was imported last under the short name. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.n_bit Require Import words.

Local Open Scope Z_scope.

(** ** Definitions *)

(*! HOL "HOL/src/integer/integer_wordScript.sml" "i2w_def" *)
Definition i2w {a : N} (i : Z) : word a :=
  if i <? 0 then word_2comp (n2w (Z.to_N (- i))) else n2w (Z.to_N i).

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_def" *)
Definition w2i {a : N} (w : word a) : Z :=
  if word_msb w then - Z.of_N (w2n (word_2comp w)) else Z.of_N (w2n w).

(*! HOL "HOL/src/integer/integer_wordScript.sml" "UINT_MAX_def" *)
Definition UINT_MAX (a : N) : Z := Z.of_N (dimword a) - 1.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "INT_MAX_def" *)
Definition INT_MAX (a : N) : Z := Z.of_N (words.INT_MIN a) - 1.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "INT_MIN_def" *)
Definition INT_MIN (a : N) : Z := - INT_MAX a - 1.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "saturate_i2w_def" *)
Definition saturate_i2w {a : N} (i : Z) : word a :=
  if UINT_MAX a <=? i then word_T
  else if i <? 0 then n2w 0
  else n2w (Z.to_N i).

(*! HOL "HOL/src/integer/integer_wordScript.sml" "saturate_i2sw_def" *)
Definition saturate_i2sw {a : N} (i : Z) : word a :=
  if INT_MAX a <=? i then word_H
  else if i <=? INT_MIN a then word_L
  else i2w i.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "saturate_sw2sw_def" *)
Definition saturate_sw2sw {a b : N} (w : word a) : word b :=
  saturate_i2sw (w2i w).

(*! HOL "HOL/src/integer/integer_wordScript.sml" "saturate_w2sw_def" *)
Definition saturate_w2sw {a b : N} (w : word a) : word b :=
  saturate_i2sw (Z.of_N (w2n w)).

(*! HOL "HOL/src/integer/integer_wordScript.sml" "saturate_sw2w_def" *)
Definition saturate_sw2w {a b : N} (w : word a) : word b :=
  saturate_i2w (w2i w).

(*! HOL "HOL/src/integer/integer_wordScript.sml" "signed_saturate_add_def" *)
Definition signed_saturate_add {a : N} (a0 b : word a) : word a :=
  saturate_i2sw (w2i a0 + w2i b).

(*! HOL "HOL/src/integer/integer_wordScript.sml" "signed_saturate_sub_def" *)
Definition signed_saturate_sub {a : N} (a0 b : word a) : word a :=
  saturate_i2sw (w2i a0 - w2i b).

(*! HOL "HOL/src/integer/integer_wordScript.sml" "word_sdiv_def" *)
Definition word_sdiv {a : N} (a0 b : word a) : word a := i2w (w2i a0 / w2i b).

(*! HOL "HOL/src/integer/integer_wordScript.sml" "word_smod_def" *)
Definition word_smod {a : N} (a0 b : word a) : word a := i2w (w2i a0 mod w2i b).

(** ** Auxiliary facts (Galette) *)

Section Aux.
Context {a : N}.

Lemma dimword_twice : dimword a = (2 * words.INT_MIN a)%N.
Proof.
  unfold dimword, words.INT_MIN; rewrite dimindex_split at 1.
  rewrite N.pow_succ_r'; reflexivity.
Qed.

Lemma INT_MIN_pos : (0 < words.INT_MIN a)%N.
Proof. unfold words.INT_MIN; apply N.neq_0_lt_0, N.pow_nonzero; lia. Qed.

Lemma word_msb_iff (w : word a) :
  word_msb w = true <-> (words.INT_MIN a <= w2n w)%N.
Proof.
  unfold word_msb; rewrite BIT_testbit, N.testbit_eqb.
  pose proof (w2n_lt w) as Hl; rewrite dimword_twice in Hl.
  unfold words.INT_MIN in *.
  remember (2 ** (dimindex a - 1))%N as M.
  assert (HM : (0 < M)%N) by (subst; apply N.neq_0_lt_0, N.pow_nonzero; lia).
  rewrite N.eqb_eq.
  destruct (N.le_gt_cases M (w2n w)) as [H|H].
  - split; [intros; exact H|intros _].
    assert (Hq : (w2n w / M = 1)%N).
    { apply N.le_antisymm.
      - apply N.lt_succ_r, N.Div0.div_lt_upper_bound; lia.
      - apply N.div_le_lower_bound; lia. }
    rewrite Hq; reflexivity.
  - rewrite N.div_small by exact H; cbn; split; [discriminate|lia].
Qed.

Lemma word_msb_false_iff (w : word a) :
  word_msb w = false <-> (w2n w < words.INT_MIN a)%N.
Proof.
  pose proof (word_msb_iff w) as H; destruct (word_msb w).
  - split; [discriminate|intros; pose proof (proj1 H eq_refl); lia].
  - split; [intros _|reflexivity].
    destruct (N.le_gt_cases (words.INT_MIN a) (w2n w)) as [H1|H1]; [|exact H1].
    apply H in H1; discriminate.
Qed.

Lemma w2n_2comp (w : word a) :
  w2n (word_2comp w) = ((dimword a - w2n w) mod dimword a)%N.
Proof. reflexivity. Qed.

Lemma Z_dimword_pos : 0 < Z.of_N (dimword a).
Proof. pose proof (ZERO_LT_dimword a); lia. Qed.

Lemma Z_w2n_n2w n : Z.of_N (w2n (n2w n : word a)) = Z.of_N n mod Z.of_N (dimword a).
Proof. rewrite w2n_n2w, N2Z.inj_mod; reflexivity. Qed.

Lemma Z_w2n_eq (v w : word a) : Z.of_N (w2n v) = Z.of_N (w2n w) -> v = w.
Proof. intros H; apply word_eq_w2n; lia. Qed.

End Aux.

(** ** Basic characterisations *)

Section Thms.
Context {a : N}.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_eq_w2n" *)
Theorem w2i_eq_w2n : forall w : word a,
  w2i w =
  if (w2n w <? words.INT_MIN a)%N then Z.of_N (w2n w)
  else Z.of_N (w2n w) - Z.of_N (dimword a).
Proof.
  intros w; unfold w2i.
  pose proof (word_msb_iff w); pose proof (word_msb_false_iff w).
  pose proof (w2n_lt w).
  destruct (word_msb w) eqn:E.
  - assert (Hle : (words.INT_MIN a <= w2n w)%N) by (apply H; reflexivity).
    replace (w2n w <? words.INT_MIN a)%N with false
      by (symmetry; apply N.ltb_ge; exact Hle).
    rewrite w2n_2comp.
    pose proof (@INT_MIN_pos a).
    rewrite N.mod_small by lia. lia.
  - replace (w2n w <? words.INT_MIN a)%N with true
      by (symmetry; apply N.ltb_lt, H0; reflexivity).
    reflexivity.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2n_i2w" *)
Theorem w2n_i2w : forall n,
  Z.of_N (w2n (i2w n : word a)) = n mod Z.of_N (dimword a).
Proof.
  intros n; unfold i2w.
  pose proof (@Z_dimword_pos a) as HD.
  destruct (Z.ltb_spec n 0) as [Hn|Hn].
  - rewrite w2n_2comp, w2n_n2w.
    pose proof (N.mod_lt (Z.to_N (- n)) (dimword a)) as Hm.
    pose proof (ZERO_LT_dimword a).
    rewrite N2Z.inj_mod, N2Z.inj_sub by lia.
    rewrite N2Z.inj_mod, Z2N.id by lia.
    rewrite Zminus_mod_idemp_r.
    replace (Z.of_N (dimword a) - - n) with (n + 1 * Z.of_N (dimword a)) by lia.
    rewrite Z.mod_add by lia; reflexivity.
  - rewrite Z_w2n_n2w, Z2N.id by lia; reflexivity.
Qed.

Lemma w2i_bounds (w : word a) : INT_MIN a <= w2i w <= INT_MAX a.
Proof.
  rewrite w2i_eq_w2n; unfold INT_MIN, INT_MAX.
  pose proof (w2n_lt w); pose proof (@dimword_twice a).
  destruct (N.ltb_spec (w2n w) (words.INT_MIN a)); lia.
Qed.

Lemma w2n_i2w_small i :
  INT_MIN a <= i <= INT_MAX a ->
  Z.of_N (w2n (i2w i : word a)) = if i <? 0 then i + Z.of_N (dimword a) else i.
Proof.
  intros Hi; rewrite w2n_i2w; unfold INT_MIN, INT_MAX in Hi.
  pose proof (@dimword_twice a).
  destruct (Z.ltb_spec i 0).
  - rewrite <- (Z.mod_add i 1) by lia. rewrite Z.mul_1_l. apply Z.mod_small; lia.
  - apply Z.mod_small; lia.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_le" *)
Theorem w2i_le : forall w : word a, w2i w <= INT_MAX a.
Proof. intros w; apply w2i_bounds. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_ge" *)
Theorem w2i_ge : forall w : word a, INT_MIN a <= w2i w.
Proof. intros w; apply w2i_bounds. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "i2w_w2i" *)
Theorem i2w_w2i : forall w : word a, i2w (w2i w) = w.
Proof.
  intros w; apply Z_w2n_eq; rewrite w2n_i2w, w2i_eq_w2n.
  pose proof (w2n_lt w) as Hl.
  destruct (N.ltb_spec (w2n w) (words.INT_MIN a)).
  - apply Z.mod_small; lia.
  - replace (Z.of_N (w2n w) - Z.of_N (dimword a))
      with (Z.of_N (w2n w) + (-1) * Z.of_N (dimword a)) by lia.
    rewrite Z.mod_add by lia; apply Z.mod_small; lia.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_i2w" *)
Theorem w2i_i2w : forall i,
  INT_MIN a <= i /\ i <= INT_MAX a -> w2i (i2w i : word a) = i.
Proof.
  intros i Hi; rewrite w2i_eq_w2n.
  pose proof (w2n_i2w_small i Hi) as E.
  unfold INT_MIN, INT_MAX in Hi; pose proof (@dimword_twice a).
  destruct (Z.ltb_spec i 0);
    destruct (N.ltb_spec (w2n (i2w i : word a)) (words.INT_MIN a)); lia.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_11" *)
Theorem w2i_11 : forall v w : word a, w2i v = w2i w <-> v = w.
Proof.
  intros v w; split; [|intros ->; reflexivity].
  intros H; rewrite <- (i2w_w2i v), <- (i2w_w2i w), H; reflexivity.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "int_word_nchotomy" *)
Theorem int_word_nchotomy : forall w : word a, exists i, w = i2w i.
Proof. intros w; exists (w2i w); symmetry; apply i2w_w2i. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "ranged_int_word_nchotomy" *)
Theorem ranged_int_word_nchotomy : forall w : word a,
  exists i, w = i2w i /\ INT_MIN a <= i /\ i <= INT_MAX a.
Proof.
  intros w; exists (w2i w); split; [symmetry; apply i2w_w2i|apply w2i_bounds].
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_w2n_pos" *)
Theorem w2i_w2n_pos : forall (w : word a) n,
  ~ word_msb w /\ w2i w < Z.of_N n -> (w2n w < n)%N.
Proof.
  intros w n [H1 H2]; unfold w2i in H2.
  destruct (word_msb w); [exfalso; apply H1; reflexivity|lia].
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_n2w_pos" *)
Theorem w2i_n2w_pos : forall n,
  (n < words.INT_MIN a)%N -> w2i (n2w n : word a) = Z.of_N n.
Proof.
  intros n Hn; rewrite w2i_eq_w2n, w2n_n2w.
  pose proof (@dimword_twice a).
  rewrite N.mod_small by lia.
  replace (n <? words.INT_MIN a)%N with true by (symmetry; apply N.ltb_lt; lia).
  reflexivity.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_n2w_neg" *)
Theorem w2i_n2w_neg : forall n,
  (words.INT_MIN a <= n)%N /\ (n < dimword a)%N ->
  w2i (n2w n : word a) = - Z.of_N (dimword a - n).
Proof.
  intros n [H1 H2]; rewrite w2i_eq_w2n, w2n_n2w, N.mod_small by lia.
  replace (n <? words.INT_MIN a)%N with false by (symmetry; apply N.ltb_ge; lia).
  lia.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "word_msb_i2w" *)
Theorem word_msb_i2w : forall i,
  word_msb (i2w i : word a) <->
  Z.of_N (words.INT_MIN a) <= i mod Z.of_N (dimword a).
Proof.
  intros i; unfold is_true; rewrite word_msb_iff, <- w2n_i2w; lia.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "word_msb_i2w_lt_0" *)
Theorem word_msb_i2w_lt_0 : forall i,
  INT_MIN a <= i /\ i <= INT_MAX a -> (word_msb (i2w i : word a) <-> i < 0).
Proof.
  intros i Hi; unfold is_true; rewrite word_msb_iff.
  pose proof (w2n_i2w_small i Hi) as E.
  unfold INT_MIN, INT_MAX in Hi; pose proof (@dimword_twice a).
  destruct (Z.ltb_spec i 0); lia.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_i2w_pos" *)
Theorem w2i_i2w_pos : forall n,
  (n <= words.INT_MAX a)%N -> w2i (i2w (Z.of_N n) : word a) = Z.of_N n.
Proof.
  intros n Hn; apply w2i_i2w; unfold INT_MIN, INT_MAX; unfold words.INT_MAX in Hn.
  pose proof (@INT_MIN_pos a); lia.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_i2w_neg" *)
Theorem w2i_i2w_neg : forall n,
  (n <= words.INT_MIN a)%N -> w2i (i2w (- Z.of_N n) : word a) = - Z.of_N n.
Proof.
  intros n Hn; apply w2i_i2w; unfold INT_MIN, INT_MAX.
  pose proof (@INT_MIN_pos a); lia.
Qed.

End Thms.

(** ** Arithmetic *)

Section Aux2.
Context {a : N}.

Lemma w2i_msb_eq (w : word a) :
  w2i w = if word_msb w then Z.of_N (w2n w) - Z.of_N (dimword a)
          else Z.of_N (w2n w).
Proof.
  rewrite w2i_eq_w2n.
  pose proof (word_msb_iff w); pose proof (word_msb_false_iff w).
  destruct (word_msb w).
  - replace (w2n w <? words.INT_MIN a)%N with false; [reflexivity|].
    symmetry; apply N.ltb_ge, H; reflexivity.
  - replace (w2n w <? words.INT_MIN a)%N with true; [reflexivity|].
    symmetry; apply N.ltb_lt, H0; reflexivity.
Qed.

Lemma w2i_mod (w : word a) : w2i w mod Z.of_N (dimword a) = Z.of_N (w2n w).
Proof.
  pose proof (w2n_lt w); rewrite w2i_msb_eq; destruct (word_msb w).
  - replace (Z.of_N (w2n w) - Z.of_N (dimword a))
      with (Z.of_N (w2n w) + (-1) * Z.of_N (dimword a)) by lia.
    rewrite Z.mod_add by lia; apply Z.mod_small; lia.
  - apply Z.mod_small; lia.
Qed.

Lemma Z_w2n_add (v w : word a) :
  Z.of_N (w2n (word_add v w)) =
  (Z.of_N (w2n v) + Z.of_N (w2n w)) mod Z.of_N (dimword a).
Proof. unfold word_add; rewrite Z_w2n_n2w, N2Z.inj_add; reflexivity. Qed.

Lemma Z_w2n_mul (v w : word a) :
  Z.of_N (w2n (word_mul v w)) =
  (Z.of_N (w2n v) * Z.of_N (w2n w)) mod Z.of_N (dimword a).
Proof. unfold word_mul; rewrite Z_w2n_n2w, N2Z.inj_mul; reflexivity. Qed.

Lemma Z_w2n_2comp (w : word a) :
  Z.of_N (w2n (word_2comp w)) = (- Z.of_N (w2n w)) mod Z.of_N (dimword a).
Proof.
  pose proof (w2n_lt w); unfold word_2comp; rewrite Z_w2n_n2w, N2Z.inj_sub by lia.
  replace (Z.of_N (dimword a) - Z.of_N (w2n w))
    with (- Z.of_N (w2n w) + 1 * Z.of_N (dimword a)) by lia.
  rewrite Z.mod_add by lia; reflexivity.
Qed.

Lemma Z_w2n_sub (v w : word a) :
  Z.of_N (w2n (word_sub v w)) =
  (Z.of_N (w2n v) - Z.of_N (w2n w)) mod Z.of_N (dimword a).
Proof.
  unfold word_sub; rewrite Z_w2n_add, Z_w2n_2comp.
  rewrite Zplus_mod_idemp_r; reflexivity.
Qed.

Lemma w2n_add_cases (v w : word a) :
  Z.of_N (w2n (word_add v w)) =
  if Z.of_N (w2n v) + Z.of_N (w2n w) <? Z.of_N (dimword a)
  then Z.of_N (w2n v) + Z.of_N (w2n w)
  else Z.of_N (w2n v) + Z.of_N (w2n w) - Z.of_N (dimword a).
Proof.
  rewrite Z_w2n_add; pose proof (w2n_lt v); pose proof (w2n_lt w).
  destruct (Z.ltb_spec (Z.of_N (w2n v) + Z.of_N (w2n w)) (Z.of_N (dimword a))).
  - apply Z.mod_small; lia.
  - rewrite <- (Z.mod_add _ (-1)) by lia; rewrite Z.mod_small; lia.
Qed.

Lemma w2n_sub_cases (v w : word a) :
  Z.of_N (w2n (word_sub v w)) =
  if Z.of_N (w2n v) - Z.of_N (w2n w) <? 0
  then Z.of_N (w2n v) - Z.of_N (w2n w) + Z.of_N (dimword a)
  else Z.of_N (w2n v) - Z.of_N (w2n w).
Proof.
  rewrite Z_w2n_sub; pose proof (w2n_lt v); pose proof (w2n_lt w).
  destruct (Z.ltb_spec (Z.of_N (w2n v) - Z.of_N (w2n w)) 0).
  - rewrite <- (Z.mod_add _ 1) by lia; rewrite Z.mod_small; lia.
  - apply Z.mod_small; lia.
Qed.

Lemma word_msb_Z (w : word a) :
  word_msb w = (Z.of_N (words.INT_MIN a) <=? Z.of_N (w2n w)).
Proof.
  pose proof (word_msb_iff w); pose proof (word_msb_false_iff w).
  destruct (word_msb w); symmetry.
  - apply Z.leb_le; pose proof (proj1 H eq_refl); lia.
  - apply Z.leb_gt; pose proof (proj1 H0 eq_refl); lia.
Qed.

End Aux2.

Section Arith.
Context {a : N}.

Lemma bool_decide_sub_0 (v w : word a) :
  bool_decide (word_sub v w = n2w 0) = (Z.of_N (w2n v) =? Z.of_N (w2n w)).
Proof.
  destruct (Z.eqb_spec (Z.of_N (w2n v)) (Z.of_N (w2n w))) as [E|E].
  - apply bool_decide_spec; apply Z_w2n_eq; rewrite w2n_sub_cases, Z_w2n_n2w, Zmod_0_l.
    rewrite E, Z.sub_diag; reflexivity.
  - destruct (bool_decide (word_sub v w = n2w 0)) eqn:B; [|reflexivity].
    apply bool_decide_spec in B; apply (f_equal (fun x => Z.of_N (w2n x))) in B.
    rewrite w2n_sub_cases, Z_w2n_n2w, Zmod_0_l in B.
    pose proof (w2n_lt v); pose proof (w2n_lt w).
    destruct (Z.ltb_spec (Z.of_N (w2n v) - Z.of_N (w2n w)) 0); lia.
Qed.

Local Ltac cmp_solve a v w :=
  unfold nzcv; cbv zeta;
  change (@n2w a (w2n v + w2n (word_2comp w))) with (word_sub v w);
  rewrite ?bool_decide_sub_0;
  pose proof (w2n_sub_cases v w) as E;
  pose proof (@dimword_twice a) as D2;
  rewrite !word_msb_Z, !w2i_msb_eq, !word_msb_Z;
  rewrite E; clear E;
  pose proof (w2n_lt v); pose proof (w2n_lt w);
  let x := fresh "x" in let y := fresh "y" in
  remember (Z.of_N (w2n v)) as x; remember (Z.of_N (w2n w)) as y;
  assert (0 <= x /\ 0 <= y) by lia;
  destruct (Z.ltb_spec (x - y) 0);
  destruct (Z.leb_spec (Z.of_N (words.INT_MIN a)) x);
  destruct (Z.leb_spec (Z.of_N (words.INT_MIN a)) y);
  try destruct (Z.leb_spec (Z.of_N (words.INT_MIN a)) (x - y + Z.of_N (dimword a)));
  try destruct (Z.leb_spec (Z.of_N (words.INT_MIN a)) (x - y));
  try destruct (Z.eqb_spec x y);
  cbn [negb Bool.eqb andb orb]; symmetry;
  first [ apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
        | apply Z.leb_le; lia | apply Z.leb_gt; lia ].

Lemma word_lt_Z (v w : word a) : word_lt v w = (w2i v <? w2i w).
Proof. unfold word_lt; cmp_solve a v w. Qed.

Lemma word_le_Z (v w : word a) : word_le v w = (w2i v <=? w2i w).
Proof. unfold word_le; cmp_solve a v w. Qed.

Lemma word_gt_Z (v w : word a) : word_gt v w = (w2i w <? w2i v).
Proof. unfold word_gt; cmp_solve a v w. Qed.

Lemma word_ge_Z (v w : word a) : word_ge v w = (w2i w <=? w2i v).
Proof. unfold word_ge; cmp_solve a v w. Qed.

Lemma word_sub_eq_0 (v w : word a) : word_sub v w = n2w 0 <-> v = w.
Proof.
  split; [|intros ->].
  - intros H; apply Z_w2n_eq; apply (f_equal (fun x => Z.of_N (w2n x))) in H.
    rewrite w2n_sub_cases, Z_w2n_n2w, Zmod_0_l in H.
    pose proof (w2n_lt v); pose proof (w2n_lt w).
    destruct (Z.ltb_spec (Z.of_N (w2n v) - Z.of_N (w2n w)) 0); lia.
  - apply Z_w2n_eq; rewrite w2n_sub_cases, Z_w2n_n2w, Zmod_0_l.
    rewrite Z.sub_diag; reflexivity.
Qed.

End Arith.

Section Thms2.
Context {a : N}.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "WORD_LTi" *)
Theorem WORD_LTi : forall a0 b : word a, (a0 < b)%w <-> w2i a0 < w2i b.
Proof. intros a0 b; unfold is_true; rewrite word_lt_Z; apply Z.ltb_lt. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "WORD_GTi" *)
Theorem WORD_GTi : forall a0 b : word a, (a0 > b)%w <-> w2i a0 > w2i b.
Proof. intros a0 b; unfold is_true; rewrite word_gt_Z, Z.ltb_lt; lia. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "WORD_LEi" *)
Theorem WORD_LEi : forall a0 b : word a, (a0 <= b)%w <-> w2i a0 <= w2i b.
Proof. intros a0 b; unfold is_true; rewrite word_le_Z; apply Z.leb_le. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "WORD_GEi" *)
Theorem WORD_GEi : forall a0 b : word a, (a0 >= b)%w <-> w2i a0 >= w2i b.
Proof. intros a0 b; unfold is_true; rewrite word_ge_Z, Z.leb_le; lia. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "word_add_i2w_w2n" *)
Theorem word_add_i2w_w2n : forall a0 b : word a,
  i2w (Z.of_N (w2n a0) + Z.of_N (w2n b)) = (a0 + b)%w.
Proof. intros a0 b; apply Z_w2n_eq; rewrite w2n_i2w, Z_w2n_add; reflexivity. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "word_add_i2w" *)
Theorem word_add_i2w : forall a0 b : word a, i2w (w2i a0 + w2i b) = (a0 + b)%w.
Proof.
  intros a0 b; apply Z_w2n_eq; rewrite w2n_i2w, Z_w2n_add, Zplus_mod, !w2i_mod.
  reflexivity.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "word_sub_i2w_w2n" *)
Theorem word_sub_i2w_w2n : forall a0 b : word a,
  i2w (Z.of_N (w2n a0) - Z.of_N (w2n b)) = (a0 - b)%w.
Proof. intros a0 b; apply Z_w2n_eq; rewrite w2n_i2w, Z_w2n_sub; reflexivity. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "word_sub_i2w" *)
Theorem word_sub_i2w : forall a0 b : word a, i2w (w2i a0 - w2i b) = (a0 - b)%w.
Proof.
  intros a0 b; apply Z_w2n_eq; rewrite w2n_i2w, Z_w2n_sub, Zminus_mod, !w2i_mod.
  reflexivity.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "word_mul_i2w_w2n" *)
Theorem word_mul_i2w_w2n : forall a0 b : word a,
  i2w (Z.of_N (w2n a0) * Z.of_N (w2n b)) = (a0 * b)%w.
Proof. intros a0 b; apply Z_w2n_eq; rewrite w2n_i2w, Z_w2n_mul; reflexivity. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "word_mul_i2w" *)
Theorem word_mul_i2w : forall a0 b : word a, i2w (w2i a0 * w2i b) = (a0 * b)%w.
Proof.
  intros a0 b; apply Z_w2n_eq; rewrite w2n_i2w, Z_w2n_mul, Zmult_mod, !w2i_mod.
  reflexivity.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "word_i2w_add" *)
Theorem word_i2w_add : forall a0 b, (i2w a0 + i2w b : word a)%w = i2w (a0 + b).
Proof.
  intros a0 b; apply Z_w2n_eq; rewrite Z_w2n_add, !w2n_i2w, <- Zplus_mod; reflexivity.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "word_i2w_mul" *)
Theorem word_i2w_mul : forall a0 b, (i2w a0 * i2w b : word a)%w = i2w (a0 * b).
Proof.
  intros a0 b; apply Z_w2n_eq; rewrite Z_w2n_mul, !w2n_i2w, <- Zmult_mod; reflexivity.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "MULT_MINUS_ONE" *)
Theorem MULT_MINUS_ONE : forall i, (- n2w 1 * i2w i : word a)%w = i2w (- i).
Proof.
  intros i; apply Z_w2n_eq; rewrite Z_w2n_mul, Z_w2n_2comp, Z_w2n_n2w, !w2n_i2w.
  rewrite <- (Z.sub_0_l (Z.of_N 1 mod _)), Zminus_mod_idemp_r.
  rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r; f_equal; lia.
Qed.


(*! HOL "HOL/src/integer/integer_wordScript.sml" "word_0_w2i" *)
Theorem word_0_w2i : w2i (n2w 0 : word a) = 0.
Proof. rewrite w2i_n2w_pos; [reflexivity|apply INT_MIN_pos]. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_eq_0" *)
Theorem w2i_eq_0 : forall w : word a, w2i w = 0 <-> w = n2w 0.
Proof. intros w; rewrite <- word_0_w2i; apply w2i_11. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "i2w_pos" *)
Theorem i2w_pos : forall n, (i2w (Z.of_N n) : word a) = n2w n.
Proof.
  intros n; unfold i2w.
  replace (Z.of_N n <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite N2Z.id; reflexivity.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "i2w_w2n" *)
Theorem i2w_w2n : forall w : word a, i2w (Z.of_N (w2n w)) = w.
Proof. intros w; rewrite i2w_pos; apply n2w_w2n. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "i2w_w2n_w2w" *)
Theorem i2w_w2n_w2w : forall {b} (w : word a), i2w (Z.of_N (w2n w)) = (w2w w : word b).
Proof.
  intros b w; unfold i2w.
  replace (Z.of_N (w2n w) <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite N2Z.id; reflexivity.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "INT_MIN" 893 *)
Theorem INT_MIN_thm : INT_MIN a = - Z.of_N (words.INT_MIN a).
Proof. unfold INT_MIN, INT_MAX; lia. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "INT_MAX" 899 *)
Theorem INT_MAX_thm : INT_MAX a = Z.of_N (words.INT_MAX a).
Proof. unfold INT_MAX, words.INT_MAX; pose proof (@INT_MIN_pos a); lia. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "UINT_MAX" 906 *)
Theorem UINT_MAX_thm : UINT_MAX a = Z.of_N (words.UINT_MAX a).
Proof. unfold UINT_MAX, words.UINT_MAX; pose proof (ZERO_LT_dimword a); lia. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "INT_BOUND_ORDER" *)
Theorem INT_BOUND_ORDER :
  INT_MIN a < INT_MAX a /\ INT_MAX a < UINT_MAX a /\ UINT_MAX a < Z.of_N (dimword a).
Proof.
  unfold INT_MIN, INT_MAX, UINT_MAX; pose proof (@INT_MIN_pos a);
    pose proof (@dimword_twice a); lia.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "INT_ZERO_LT_INT_MIN" *)
Theorem INT_ZERO_LT_INT_MIN : INT_MIN a < 0.
Proof. unfold INT_MIN, INT_MAX; pose proof (@INT_MIN_pos a); lia. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "INT_ZERO_LT_INT_MAX" *)
Theorem INT_ZERO_LT_INT_MAX : (1 < dimindex a)%N -> 0 < INT_MAX a.
Proof.
  intros H; unfold INT_MAX, words.INT_MIN.
  assert (2 <= 2 ** (dimindex a - 1))%N.
  { replace (dimindex a - 1)%N with (N.succ (dimindex a - 2)) by lia.
    rewrite N.pow_succ_r'. pose proof (N.pow_nonzero 2 (dimindex a - 2)). lia. }
  lia.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "INT_ZERO_LE_INT_MAX" *)
Theorem INT_ZERO_LE_INT_MAX : 0 <= INT_MAX a.
Proof. unfold INT_MAX; pose proof (@INT_MIN_pos a); lia. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "INT_ZERO_LT_UINT_MAX" *)
Theorem INT_ZERO_LT_UINT_MAX : 0 < UINT_MAX a.
Proof.
  unfold UINT_MAX; pose proof (@INT_MIN_pos a); pose proof (@dimword_twice a); lia.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_1" *)
Theorem w2i_1 : w2i (n2w 1 : word a) = if (dimindex a =? 1)%N then -1 else 1.
Proof.
  pose proof (@dimword_twice a); pose proof (@INT_MIN_pos a).
  destruct (N.eqb_spec (dimindex a) 1) as [E|E].
  - assert (words.INT_MIN a = 1%N) by (unfold words.INT_MIN; rewrite E; reflexivity).
    rewrite w2i_n2w_neg by lia; lia.
  - rewrite w2i_n2w_pos; [reflexivity|].
    unfold words.INT_MIN.
    replace (dimindex a - 1)%N with (N.succ (dimindex a - 2))
      by (pose proof (DIMINDEX_GT_0 a); lia).
    rewrite N.pow_succ_r'. pose proof (N.pow_nonzero 2 (dimindex a - 2)). lia.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_INT_MINw" *)
Theorem w2i_INT_MINw : w2i (INT_MINw : word a) = INT_MIN a.
Proof.
  pose proof (@dimword_twice a); pose proof (@INT_MIN_pos a).
  unfold word_L; rewrite w2i_n2w_neg by lia; unfold INT_MIN, INT_MAX; lia.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_UINT_MAXw" *)
Theorem w2i_UINT_MAXw : w2i (UINT_MAXw : word a) = -1.
Proof.
  pose proof (@dimword_twice a); pose proof (@INT_MIN_pos a).
  unfold word_T, words.UINT_MAX; rewrite w2i_n2w_neg by lia; lia.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_INT_MAXw" *)
Theorem w2i_INT_MAXw : w2i (INT_MAXw : word a) = INT_MAX a.
Proof.
  pose proof (@dimword_twice a); pose proof (@INT_MIN_pos a).
  unfold word_H, words.INT_MAX; rewrite w2i_n2w_pos by lia; unfold INT_MAX; lia.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_lt_0" *)
Theorem w2i_lt_0 : forall w : word a, w2i w < 0 <-> (w < n2w 0)%w.
Proof. intros w; rewrite WORD_LTi, word_0_w2i; reflexivity. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_neg" *)
Theorem w2i_neg : forall w : word a, w <> INT_MINw -> w2i (- w)%w = - w2i w.
Proof.
  intros w Hw; pose proof (w2i_bounds w).
  assert (w2i w <> INT_MIN a) by (intros E; apply Hw, w2i_11; rewrite w2i_INT_MINw; exact E).
  assert (E : (- w)%w = (i2w (- w2i w) : word a)).
  { apply Z_w2n_eq; rewrite Z_w2n_2comp, w2n_i2w, <- w2i_mod.
    rewrite <- !Z.sub_0_l, Zminus_mod_idemp_r; reflexivity. }
  rewrite E; apply w2i_i2w; unfold INT_MIN, INT_MAX in *; lia.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "i2w_0" *)
Theorem i2w_0 : (i2w 0 : word a) = n2w 0.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "i2w_minus_1" *)
Theorem i2w_minus_1 : (i2w (-1) : word a) = (- n2w 1)%w.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "i2w_INT_MIN" *)
Theorem i2w_INT_MIN : (i2w (INT_MIN a) : word a) = INT_MINw.
Proof. rewrite <- w2i_INT_MINw; apply i2w_w2i. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "i2w_INT_MAX" *)
Theorem i2w_INT_MAX : (i2w (INT_MAX a) : word a) = INT_MAXw.
Proof. rewrite <- w2i_INT_MAXw; apply i2w_w2i. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "i2w_UINT_MAX" *)
Theorem i2w_UINT_MAX : (i2w (UINT_MAX a) : word a) = UINT_MAXw.
Proof.
  apply Z_w2n_eq; rewrite w2n_i2w; unfold word_T, UINT_MAX.
  rewrite Z_w2n_n2w; unfold words.UINT_MAX.
  pose proof (ZERO_LT_dimword a); rewrite N2Z.inj_sub by lia; reflexivity.
Qed.

End Thms2.

Local Ltac split_conds :=
  repeat match goal with
  | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
  | |- context [?x <=? ?y] => destruct (Z.leb_spec x y)
  end.

Section Overflow.
Context {a : N}.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "different_sign_then_no_overflow" *)
Theorem different_sign_then_no_overflow : forall x y : word a,
  word_msb x <> word_msb y -> w2i (x + y)%w = w2i x + w2i y.
Proof.
  intros x y; rewrite !w2i_msb_eq, !word_msb_Z, w2n_add_cases.
  pose proof (w2n_lt x); pose proof (w2n_lt y).
  pose proof (@dimword_twice a); pose proof (@INT_MIN_pos a).
  remember (Z.of_N (w2n x)) as X; remember (Z.of_N (w2n y)) as Y.
  split_conds; intuition (first [discriminate | congruence | lia]).
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "overflow" *)
Theorem overflow : forall x y : word a,
  w2i (x + y)%w <> w2i x + w2i y <->
  (word_msb x = word_msb y /\ word_msb x <> word_msb (x + y)%w).
Proof.
  intros x y; rewrite !w2i_msb_eq, !word_msb_Z, w2n_add_cases.
  pose proof (w2n_lt x); pose proof (w2n_lt y).
  pose proof (@dimword_twice a); pose proof (@INT_MIN_pos a).
  remember (Z.of_N (w2n x)) as X; remember (Z.of_N (w2n y)) as Y.
  split_conds; intuition (first [discriminate | congruence | lia]).
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "sub_overflow" *)
Theorem sub_overflow : forall x y : word a,
  w2i (x - y)%w <> w2i x - w2i y <->
  (word_msb x <> word_msb y /\ word_msb x <> word_msb (x - y)%w).
Proof.
  intros x y; rewrite !w2i_msb_eq, !word_msb_Z, w2n_sub_cases.
  pose proof (w2n_lt x); pose proof (w2n_lt y).
  pose proof (@dimword_twice a); pose proof (@INT_MIN_pos a).
  remember (Z.of_N (w2n x)) as X; remember (Z.of_N (w2n y)) as Y.
  split_conds; intuition (first [discriminate | congruence | lia]).
Qed.

End Overflow.

(** ** Width-changing maps *)

Lemma dimword_le {a b : N} :
  (dimindex a <= dimindex b)%N -> (dimword a <= dimword b)%N.
Proof. intros H; apply N.pow_le_mono_r; lia. Qed.

Lemma dimword_divide {a b : N} :
  (dimindex a <= dimindex b)%N -> (Z.of_N (dimword a) | Z.of_N (dimword b)).
Proof.
  intros H; exists (Z.of_N (2 ** (dimindex b - dimindex a))).
  rewrite <- N2Z.inj_mul; f_equal; unfold dimword.
  rewrite <- N.pow_add_r; f_equal; lia.
Qed.

Lemma Z_w2n_sw2sw {a b : N} (w : word a) :
  (dimindex a <= dimindex b)%N ->
  Z.of_N (w2n (sw2sw w : word b)) =
  if word_msb w then Z.of_N (w2n w) + Z.of_N (dimword b) - Z.of_N (dimword a)
  else Z.of_N (w2n w).
Proof.
  intros H; pose proof (dimword_le H); pose proof (w2n_lt w).
  unfold sw2sw, SIGN_EXTEND; cbv zeta.
  change (BIT (dimindex a - 1) (w2n w)) with (word_msb w).
  change (2 ** dimindex a)%N with (dimword a).
  change (2 ** dimindex b)%N with (dimword b).
  rewrite (N.mod_small (w2n w)) by lia.
  destruct (word_msb w); rewrite Z_w2n_n2w, Z.mod_small; lia.
Qed.

Lemma w2i_sw2sw {a b : N} (w : word a) :
  (dimindex a <= dimindex b)%N -> w2i (sw2sw w : word b) = w2i w.
Proof.
  intros H; pose proof (dimword_le H); pose proof (w2n_lt w).
  pose proof (@dimword_twice a); pose proof (@dimword_twice b).
  rewrite (w2i_msb_eq (sw2sw w : word b)), (word_msb_Z (sw2sw w : word b)),
    (Z_w2n_sw2sw w H), (w2i_msb_eq w).
  destruct (word_msb w) eqn:E;
    [apply word_msb_iff in E|apply word_msb_false_iff in E]; split_conds; lia.
Qed.

Lemma INT_MIN_mono {a b : N} : (dimindex a <= dimindex b)%N -> INT_MIN b <= INT_MIN a.
Proof.
  intros H; pose proof (dimword_le H).
  pose proof (@dimword_twice a); pose proof (@dimword_twice b).
  unfold INT_MIN, INT_MAX; lia.
Qed.

Lemma INT_MAX_mono {a b : N} : (dimindex a <= dimindex b)%N -> INT_MAX a <= INT_MAX b.
Proof.
  intros H; pose proof (dimword_le H).
  pose proof (@dimword_twice a); pose proof (@dimword_twice b).
  unfold INT_MAX; lia.
Qed.

Section Width.
Context {a b : N}.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "INT_MIN_MONOTONIC" *)
Theorem INT_MIN_MONOTONIC : (dimindex a <= dimindex b)%N -> INT_MIN b <= INT_MIN a.
Proof. apply INT_MIN_mono. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "INT_MAX_MONOTONIC" *)
Theorem INT_MAX_MONOTONIC : (dimindex a <= dimindex b)%N -> INT_MAX a <= INT_MAX b.
Proof. apply INT_MAX_mono. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2w_i2w" *)
Theorem w2w_i2w : forall i,
  (dimindex a <= dimindex b)%N -> w2w (i2w i : word b) = (i2w i : word a).
Proof.
  intros i H; apply Z_w2n_eq; unfold w2w.
  rewrite Z_w2n_n2w, !w2n_i2w.
  apply Z.mod_mod_divide, dimword_divide, H.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "sw2sw_i2w" *)
Theorem sw2sw_i2w : forall j,
  INT_MIN b <= j /\ j <= INT_MAX b /\ (dimindex b <= dimindex a)%N ->
  sw2sw (i2w j : word b) = (i2w j : word a).
Proof.
  intros j (H1 & H2 & H3).
  pose proof (@INT_MIN_mono b a H3); pose proof (@INT_MAX_mono b a H3).
  apply w2i_11; rewrite w2i_sw2sw by exact H3.
  rewrite !w2i_i2w; [reflexivity| |split; assumption]; lia.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_sw2sw_bounds" *)
Theorem w2i_sw2sw_bounds : forall w : word a,
  INT_MIN a <= w2i (sw2sw w : word b) /\ w2i (sw2sw w : word b) <= INT_MAX a.
Proof.
  intros w; destruct (N.le_gt_cases (dimindex a) (dimindex b)) as [H|H].
  - rewrite w2i_sw2sw by exact H; apply w2i_bounds.
  - pose proof (w2i_bounds (sw2sw w : word b)).
    pose proof (@INT_MIN_mono b a ltac:(lia)).
    pose proof (@INT_MAX_mono b a ltac:(lia)). lia.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_i2w_id" *)
Theorem w2i_i2w_id : forall i,
  INT_MIN a <= i /\ i <= INT_MAX a /\ (dimindex b <= dimindex a)%N ->
  (i = w2i (i2w i : word b) <-> (i2w i : word a) = sw2sw (i2w i : word b)).
Proof.
  intros i (H1 & H2 & H3); rewrite <- w2i_11, w2i_sw2sw by exact H3.
  rewrite (@w2i_i2w a i) by (split; assumption); split; intros; congruence.
Qed.

End Width.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_11_lift" *)
Theorem w2i_11_lift : forall {a b c : N} (a0 : word a) (b0 : word b),
  (dimindex a <= dimindex c)%N /\ (dimindex b <= dimindex c)%N ->
  (w2i a0 = w2i b0 <-> (sw2sw a0 : word c) = sw2sw b0).
Proof.
  intros a b c a0 b0 [H1 H2]; rewrite <- w2i_11, !w2i_sw2sw by assumption.
  reflexivity.
Qed.

Section Misc.
Context {a : N}.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "w2i_n2w_mod" *)
Theorem w2i_n2w_mod : forall n m,
  (n < dimword a)%N /\ (m <= dimindex a)%N ->
  Z.to_N (w2i (n2w n : word a) mod 2 ^ Z.of_N m) = (n MOD 2 ** m)%N.
Proof.
  intros n m [H1 H2].
  assert (E : 2 ^ Z.of_N m = Z.of_N (2 ** m)) by (rewrite N2Z.inj_pow; reflexivity).
  assert (P : (0 < 2 ** m)%N) by (apply N.neq_0_lt_0, N.pow_nonzero; lia).
  assert (D : Z.of_N (dimword a) = Z.of_N (2 ** (dimindex a - m)) * Z.of_N (2 ** m)).
  { rewrite <- N2Z.inj_mul, <- N.pow_add_r; unfold dimword; f_equal; f_equal; lia. }
  rewrite E, w2i_msb_eq, Z_w2n_n2w, (Z.mod_small (Z.of_N n)) by lia.
  destruct (word_msb (n2w n : word a)).
  - rewrite D.
    replace (Z.of_N n - Z.of_N (2 ** (dimindex a - m)) * Z.of_N (2 ** m))
      with (Z.of_N n + (- Z.of_N (2 ** (dimindex a - m))) * Z.of_N (2 ** m))
      by lia.
    rewrite Z.mod_add by lia.
    rewrite <- N2Z.inj_mod, N2Z.id; reflexivity.
  - rewrite <- N2Z.inj_mod, N2Z.id; reflexivity.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "word_abs_w2i" *)
Theorem word_abs_w2i : forall w : word a, word_abs w = n2w (Z.to_N (Z.abs (w2i w))).
Proof.
  intros w; unfold word_abs; rewrite word_lt_Z, word_0_w2i.
  apply Z_w2n_eq; rewrite Z_w2n_n2w.
  destruct (Z.ltb_spec (w2i w) 0).
  - rewrite Z_w2n_2comp, Z2N.id by lia; rewrite Z.abs_neq by lia.
    rewrite <- w2i_mod, <- !Z.sub_0_l, Zminus_mod_idemp_r; reflexivity.
  - rewrite Z2N.id by lia; rewrite Z.abs_eq by lia; rewrite w2i_mod; reflexivity.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "word_abs_i2w" *)
Theorem word_abs_i2w : forall i,
  INT_MIN a <= i /\ i <= INT_MAX a ->
  word_abs (i2w i) = (n2w (Z.to_N (Z.abs i)) : word a).
Proof. intros i H; rewrite word_abs_w2i, w2i_i2w by exact H; reflexivity. Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "saturate_i2w_0" *)
Theorem saturate_i2w_0 : (saturate_i2w 0 : word a) = n2w 0.
Proof.
  unfold saturate_i2w; pose proof (@INT_ZERO_LT_UINT_MAX a).
  destruct (Z.leb_spec (UINT_MAX a) 0); [lia|reflexivity].
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "saturate_i2sw_0" *)
Theorem saturate_i2sw_0 : (saturate_i2sw 0 : word a) = n2w 0.
Proof.
  unfold saturate_i2sw; pose proof (@INT_ZERO_LE_INT_MAX a);
    pose proof (@INT_ZERO_LT_INT_MIN a).
  destruct (Z.leb_spec (INT_MAX a) 0).
  - unfold word_H; f_equal; pose proof (@INT_MAX_thm a); lia.
  - destruct (Z.leb_spec 0 (INT_MIN a)); [lia|reflexivity].
Qed.

End Misc.

(** ** Arithmetic shift right *)

Lemma lor_disjoint (x y k : N) :
  (y < 2 ** k)%N -> N.lor (x * 2 ** k) y = (x * 2 ** k + y)%N.
Proof.
  intros Hy.
  assert (L : N.land (x * 2 ** k) y = 0%N).
  { apply N.bits_inj_0; intros i; rewrite N.land_spec.
    destruct (N.lt_ge_cases i k).
    - rewrite N.mul_pow2_bits_low by lia; reflexivity.
    - rewrite <- (N.mod_small y (2 ** k)) by exact Hy.
      rewrite N.mod_pow2_bits_high by lia; apply andb_false_r. }
  rewrite <- N.lxor_lor by exact L; rewrite N.add_nocarry_lxor by exact L.
  reflexivity.
Qed.

Section Asr.
Context {a : N}.

Lemma w2n_lsr (w : word a) n : w2n (w >>> n)%w = (w2n w / 2 ** n)%N.
Proof.
  unfold word_lsr, word_bits; rewrite w2n_n2w, MIN_min, N.min_id.
  unfold BITS, MOD_2EXP, DIV_2EXP.
  pose proof (w2n_lt w); unfold dimword in *.
  assert (Hq : (w2n w / 2 ** n < 2 ** (N.succ (dimindex a - 1) - n))%N).
  { destruct (N.le_gt_cases n (dimindex a)).
    - apply N.Div0.div_lt_upper_bound; rewrite <- N.pow_add_r.
      replace (n + (N.succ (dimindex a - 1) - n))%N with (dimindex a)
        by (pose proof (DIMINDEX_GT_0 a); lia); exact H.
    - rewrite N.div_small; [apply N.neq_0_lt_0, N.pow_nonzero; lia|].
      apply (N.lt_le_trans _ _ _ H); apply N.pow_le_mono_r; lia. }
  rewrite (N.mod_small (w2n w / 2 ** n)) by exact Hq.
  apply N.mod_small, (N.le_lt_trans _ (w2n w)); [|exact H].
  apply N.Div0.div_le_upper_bound.
  pose proof (N.pow_nonzero 2 n); nia.
Qed.

Lemma w2i_asr (w : word a) n :
  (n < dimindex a)%N -> w2i (w >> n)%w = w2i w / Z.of_N (2 ** n).
Proof.
  intros Hn.
  set (P := (2 ** n)%N); set (K2 := (2 ** (dimindex a - 1 - n))%N).
  assert (HP : (0 < P)%N) by (apply N.neq_0_lt_0, N.pow_nonzero; lia).
  assert (HK : (0 < K2)%N) by (apply N.neq_0_lt_0, N.pow_nonzero; lia).
  assert (HM : words.INT_MIN a = (P * K2)%N).
  { unfold words.INT_MIN, P, K2; rewrite <- N.pow_add_r; f_equal; lia. }
  pose proof (@dimword_twice a) as HD.
  assert (HK2 : (K2 <= P * K2)%N) by nia.
  pose proof (w2n_lt w) as Hw.
  set (x := w2n w) in *.
  pose proof (w2n_lsr w n) as Hl; fold x P in Hl.
  unfold word_asr.
  destruct (word_msb w) eqn:E.
  - apply word_msb_iff in E; fold x in E.
    assert (Hq1 : (K2 <= x / P)%N) by (apply N.div_le_lower_bound; lia).
    assert (Hq2 : (x / P < 2 * K2)%N) by (apply N.Div0.div_lt_upper_bound; lia).
    (* the value of the shifted word *)
    assert (V : w2n (word_or (word_lsl word_T (dimindex a - MIN n (dimindex a))) (w >>> n)%w)
                = (x / P + dimword a - 2 * K2)%N).
    { unfold word_or; rewrite w2n_n2w, Hl.
      rewrite MIN_min, N.min_l by lia.
      destruct (N.eq_dec n 0) as [->|Hn0].
      + unfold word_lsl; rewrite N.sub_0_r.
        replace (dimindex a - 1 <? dimindex a)%N with true
          by (symmetry; apply N.ltb_lt; pose proof (DIMINDEX_GT_0 a); lia).
        rewrite w2n_n2w, N.Div0.mod_0_l, N.lor_0_l.
        subst P; cbn [N.pow] in *.
        rewrite N.mod_small; lia.
      + unfold word_lsl.
        replace (dimindex a - 1 <? dimindex a - n)%N with false
          by (symmetry; apply N.ltb_ge; lia).
        assert (EK : (2 ** (dimindex a - n) = 2 * K2)%N).
        { unfold K2; rewrite <- N.pow_succ_r'; f_equal; lia. }
        unfold word_T, words.UINT_MAX; rewrite !w2n_n2w, EK.
        rewrite (N.mod_small (dimword a - 1)) by lia.
        assert (EV : ((dimword a - 1) * (2 * K2) mod dimword a = (P - 1) * (2 * K2))%N).
        { rewrite HD, HM.
          replace ((2 * (P * K2) - 1) * (2 * K2))%N
            with ((P - 1) * (2 * K2) + (2 * K2 - 1) * (2 * (P * K2)))%N by nia.
          rewrite N.Div0.mod_add, N.mod_small by nia; reflexivity. }
        rewrite EV.
        rewrite <- EK, lor_disjoint by (rewrite EK; exact Hq2).
        rewrite EK, N.mod_small; nia. }
    rewrite (w2i_msb_eq (word_or _ _)), (word_msb_Z (word_or _ _)), V.
    rewrite (w2i_msb_eq w), (word_msb_Z w); fold x.
    replace (Z.of_N (words.INT_MIN a) <=? Z.of_N x) with true
      by (symmetry; apply Z.leb_le; lia).
    replace (Z.of_N (words.INT_MIN a) <=? Z.of_N (x / P + dimword a - 2 * K2)) with true
      by (symmetry; apply Z.leb_le; nia).
    rewrite HD, HM.
    replace (Z.of_N x - Z.of_N (2 * (P * K2)))
      with (Z.of_N x + (- Z.of_N (2 * K2)) * Z.of_N P) by lia.
    rewrite Z.div_add by lia. rewrite <- N2Z.inj_div. lia.
  - apply word_msb_false_iff in E; fold x in E.
    assert (Hq : (x / P < K2)%N) by (apply N.Div0.div_lt_upper_bound; lia).
    rewrite w2i_msb_eq, word_msb_Z, Hl, (w2i_msb_eq w), (word_msb_Z w); fold x.
    replace (Z.of_N (words.INT_MIN a) <=? Z.of_N x) with false
      by (symmetry; apply Z.leb_gt; lia).
    replace (Z.of_N (words.INT_MIN a) <=? Z.of_N (x / P)) with false
      by (symmetry; apply Z.leb_gt; lia).
    rewrite N2Z.inj_div; reflexivity.
Qed.

(*! HOL "HOL/src/integer/integer_wordScript.sml" "i2w_DIV" *)
Theorem i2w_DIV : forall n i,
  (n < dimindex a)%N /\ INT_MIN a <= i /\ i <= INT_MAX a ->
  (i2w (i / 2 ^ Z.of_N n) : word a) = (i2w i >> n)%w.
Proof.
  intros n i (H1 & H2 & H3).
  rewrite <- (@w2i_i2w a i) at 1 by (split; assumption).
  replace (2 ^ Z.of_N n) with (Z.of_N (2 ** n)) by (rewrite N2Z.inj_pow; reflexivity).
  rewrite <- w2i_asr by exact H1; apply i2w_w2i.
Qed.

End Asr.
