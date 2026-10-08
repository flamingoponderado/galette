(** * HOL4 [words]: arithmetic and order theorems

    Part of the port of [HOL/src/n-bit/wordsScript.sml] (see [words.v]):
    the generic word theorems most cited by CakeML proofs (ring laws,
    [_n2w] theorems, unsigned and signed comparisons).

    Proof method (Galette-only helpers, untagged): word equalities are
    mapped to integer congruences modulo [dimword a] ([word_eq_Z],
    tactic [word_Z]), comparisons are reduced to [w2n] through an explicit
    description of [nzcv] ([nzcv_spec]).

    Theorems that HOL derives with [GEN_ALL] quantify their variables in
    HOL's term order (reverse alphabetical for variables of the same type);
    the Rocq statements follow that order. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.n_bit.words Require Import fcp_defs.
From Stdlib Require Import Zdiv Setoid Morphisms.
Open Scope N_scope.

Local Open Scope N_scope.

(** ** Widths *)

Section Widths.
Context {a : N}.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "ONE_LT_dimword" *)
Theorem ONE_LT_dimword : 1 < dimword a.
Proof.
  rewrite dimword_pow; pose proof (DIMINDEX_GT_0 a).
  apply N.lt_le_trans with (2 ** 1); [cbn; lia|apply N.pow_le_mono_r; lia].
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "dimword_IS_TWICE_INT_MIN" *)
Theorem dimword_IS_TWICE_INT_MIN : dimword a = 2 * INT_MIN a.
Proof.
  unfold INT_MIN; rewrite dimword_pow, <- N.pow_succ_r'.
  pose proof (DIMINDEX_GT_0 a); f_equal; lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "dimword_sub_int_min" *)
Theorem dimword_sub_int_min : dimword a - INT_MIN a = INT_MIN a.
Proof. rewrite dimword_IS_TWICE_INT_MIN; lia. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "ZERO_LT_INT_MIN" *)
Theorem ZERO_LT_INT_MIN : 0 < INT_MIN a.
Proof. unfold INT_MIN; apply N.neq_0_lt_0, N.pow_nonzero; lia. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "INT_MIN_LT_DIMWORD" *)
Theorem INT_MIN_LT_DIMWORD : INT_MIN a < dimword a.
Proof. rewrite dimword_IS_TWICE_INT_MIN; pose proof ZERO_LT_INT_MIN; lia. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "INT_MAX_LT_DIMWORD" *)
Theorem INT_MAX_LT_DIMWORD : INT_MAX a < dimword a.
Proof. unfold INT_MAX; pose proof INT_MIN_LT_DIMWORD; lia. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "ZERO_LT_UINT_MAX" *)
Theorem ZERO_LT_UINT_MAX : 0 < UINT_MAX a.
Proof. unfold UINT_MAX; pose proof ONE_LT_dimword; lia. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "ZERO_LE_INT_MAX" *)
Theorem ZERO_LE_INT_MAX : 0 <= INT_MAX a.
Proof. lia. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "dimindex_lt_dimword" *)
Theorem dimindex_lt_dimword : dimindex a < dimword a.
Proof. rewrite dimword_pow; apply N.pow_gt_lin_r; lia. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "BOUND_ORDER" *)
Theorem BOUND_ORDER :
  INT_MAX a < INT_MIN a /\ INT_MIN a <= UINT_MAX a /\ UINT_MAX a < dimword a.
Proof.
  unfold INT_MAX, UINT_MAX; pose proof ZERO_LT_INT_MIN; pose proof INT_MIN_LT_DIMWORD.
  lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "MOD_DIMINDEX" *)
Theorem MOD_DIMINDEX : forall n, n MOD dimword a = BITS (dimindex a - 1) 0 n.
Proof.
  intros n; rewrite BITS_0_mod, dimword_pow; pose proof (DIMINDEX_GT_0 a).
  f_equal; f_equal; lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "BITS_ZEROL_DIMINDEX" *)
Theorem BITS_ZEROL_DIMINDEX : forall n,
  n < dimword a -> BITS (dimindex a - 1) 0 n = n.
Proof. intros n H; rewrite <- MOD_DIMINDEX; apply N.mod_small, H. Qed.

End Widths.

(** ** The carrier *)

Section Carrier.
Context {a : N}.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_nchotomy" *)
Theorem word_nchotomy : forall w : word a, exists n, w = n2w n.
Proof. intros w; exists (w2n w); symmetry; apply n2w_w2n. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "ranged_word_nchotomy" *)
Theorem ranged_word_nchotomy : forall w : word a, exists n, w = n2w n /\ n < dimword a.
Proof. intros w; exists (w2n w); split; [symmetry; apply n2w_w2n|apply w2n_lt]. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "w2n_11" *)
Theorem w2n_11 : forall v w : word a, w2n v = w2n w <-> v = w.
Proof. intros v w; split; [apply word_eq_w2n|intros ->; reflexivity]. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_0_n2w" *)
Theorem word_0_n2w : w2n (n2w 0 : word a) = 0.
Proof. rewrite w2n_n2w; apply N.Div0.mod_0_l. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_1_n2w" *)
Theorem word_1_n2w : w2n (n2w 1 : word a) = 1.
Proof. rewrite w2n_n2w; apply N.mod_small, ONE_LT_dimword. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "w2n_eq_0" *)
Theorem w2n_eq_0 : forall w : word a, w2n w = 0 <-> w = n2w 0.
Proof.
  intros w; rewrite <- w2n_11, word_0_n2w; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "n2w_dimword" 1000 *)
Theorem n2w_dimword : (n2w (dimword a) : word a) = n2w 0.
Proof.
  apply n2w_11; rewrite N.Div0.mod_same, N.Div0.mod_0_l; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_INDUCT" *)
Theorem WORD_INDUCT : forall P : word a -> Prop,
  P (n2w 0) /\ (forall n, SUC n < dimword a -> P (n2w n) -> P (n2w (SUC n))) ->
  forall x : word a, P x.
Proof.
  intros P [H0 HS] x; rewrite <- (n2w_w2n x).
  pose proof (w2n_lt x) as Hx; revert Hx; generalize (w2n x) as n.
  induction n as [|n IHn] using N.peano_ind; intros Hn; [exact H0|].
  apply HS; [exact Hn|apply IHn; lia].
Qed.

End Carrier.

(** ** Integer view of word arithmetic (Galette-only helpers) *)

(** Congruence modulo [N], as an opaque relation so that [rewrite] works
    under [+], [-], [*] and opposite. *)
Inductive zcong (N x y : Z) : Prop :=
  zcong_intro : (x mod N = y mod N)%Z -> zcong N x y.

#[export] Instance zcong_equiv N : Equivalence (zcong N).
Proof.
  split; [intros x; constructor; reflexivity
         |intros x y [H]; constructor; auto
         |intros x y z [H] [H']; constructor; congruence].
Qed.

#[export] Instance zcong_add N : Proper (zcong N ==> zcong N ==> zcong N) Z.add.
Proof. intros x x' [H] y y' [H']; constructor; apply Zplus_eqm; assumption. Qed.

#[export] Instance zcong_mul N : Proper (zcong N ==> zcong N ==> zcong N) Z.mul.
Proof. intros x x' [H] y y' [H']; constructor; apply Zmult_eqm; assumption. Qed.

#[export] Instance zcong_sub N : Proper (zcong N ==> zcong N ==> zcong N) Z.sub.
Proof. intros x x' [H] y y' [H']; constructor; apply Zminus_eqm; assumption. Qed.

#[export] Instance zcong_opp N : Proper (zcong N ==> zcong N) Z.opp.
Proof. intros x x' [H]; constructor; apply Zopp_eqm; assumption. Qed.

Lemma zcong_mod N x : zcong N (x mod N) x.
Proof. constructor; apply Zmod_mod. Qed.

Lemma zcong_eq N x y : x = y -> zcong N x y.
Proof. intros ->; reflexivity. Qed.

Section ZView.
Context {a : N}.

Local Abbreviation D := (Z.of_N (dimword a)).

Definition Zw (w : word a) : Z := Z.of_N (w2n w).

Lemma D_pos : (0 < D)%Z.
Proof. pose proof (ZERO_LT_dimword a); lia. Qed.

Lemma Zw_bound (w : word a) : (0 <= Zw w < D)%Z.
Proof. unfold Zw; pose proof (w2n_lt w); lia. Qed.

Lemma word_eq_Z (v w : word a) : (Zw v mod D = Zw w mod D)%Z -> v = w.
Proof.
  intros H; rewrite !Z.mod_small in H by apply Zw_bound.
  apply word_eq_w2n; unfold Zw in H; lia.
Qed.

Lemma Zw_n2w n : Zw (n2w n : word a) = (Z.of_N n mod D)%Z.
Proof. unfold Zw; rewrite w2n_n2w, N2Z.inj_mod; reflexivity. Qed.

Lemma Zw_add (v w : word a) : Zw (word_add v w) = ((Zw v + Zw w) mod D)%Z.
Proof. unfold word_add; rewrite Zw_n2w, N2Z.inj_add; reflexivity. Qed.

Lemma Zw_mul (v w : word a) : Zw (word_mul v w) = ((Zw v * Zw w) mod D)%Z.
Proof. unfold word_mul; rewrite Zw_n2w, N2Z.inj_mul; reflexivity. Qed.

Lemma Zw_neg (w : word a) : Zw (word_2comp w) = ((- Zw w) mod D)%Z.
Proof.
  unfold word_2comp; rewrite Zw_n2w, N2Z.inj_sub by (apply N.lt_le_incl, w2n_lt).
  fold (Zw w); replace (D - Zw w)%Z with (- Zw w + 1 * D)%Z by ring.
  apply Z_mod_plus_full.
Qed.

Lemma Zw_sub (v w : word a) : Zw (word_sub v w) = ((Zw v + (- Zw w) mod D) mod D)%Z.
Proof. unfold word_sub; rewrite Zw_add, Zw_neg; reflexivity. Qed.

Lemma zcong_word_eq (v w : word a) : zcong D (Zw v) (Zw w) -> v = w.
Proof. intros [H]; apply word_eq_Z, H. Qed.

Lemma Zc_n2w n : zcong D (Zw (n2w n : word a)) (Z.of_N n).
Proof. rewrite Zw_n2w; apply zcong_mod. Qed.

Lemma Zc_add (v w : word a) : zcong D (Zw (word_add v w)) (Zw v + Zw w).
Proof. rewrite Zw_add; apply zcong_mod. Qed.

Lemma Zc_mul (v w : word a) : zcong D (Zw (word_mul v w)) (Zw v * Zw w).
Proof. rewrite Zw_mul; apply zcong_mod. Qed.

Lemma Zc_neg (w : word a) : zcong D (Zw (word_2comp w)) (- Zw w).
Proof. rewrite Zw_neg; apply zcong_mod. Qed.

Lemma Zc_sub (v w : word a) : zcong D (Zw (word_sub v w)) (Zw v - Zw w).
Proof.
  unfold word_sub; rewrite Zc_add, Zc_neg; apply zcong_eq; ring.
Qed.

End ZView.

(** [word_Z] reduces a word equation built from [+], [*], [-], [n2w] to a
    congruence of integers modulo [dimword a]. *)
Ltac word_Z :=
  apply zcong_word_eq;
  repeat rewrite ?Zc_add, ?Zc_mul, ?Zc_sub, ?Zc_neg, ?Zc_n2w.

Ltac word_ring := word_Z; apply zcong_eq; ring.

(** ** Arithmetic *)

Section Arith.
Context {a : N}.
Local Open Scope word_scope.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_add_n2w" *)
Theorem word_add_n2w : forall m n, (n2w m : word a) + n2w n = n2w (m + n).
Proof. intros m n; word_Z; rewrite N2Z.inj_add; reflexivity. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_mul_n2w" *)
Theorem word_mul_n2w : forall m n, (n2w m : word a) * n2w n = n2w (m * n).
Proof. intros m n; word_Z; rewrite N2Z.inj_mul; reflexivity. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_ADD_0" *)
Theorem WORD_ADD_0 :
  (forall w : word a, w + n2w 0 = w) /\ (forall w : word a, n2w 0 + w = w).
Proof. split; intros w; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_ADD_ASSOC" *)
Theorem WORD_ADD_ASSOC : forall v w x : word a, v + (w + x) = v + w + x.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_MULT_ASSOC" *)
Theorem WORD_MULT_ASSOC : forall v w x : word a, v * (w * x) = v * w * x.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_ADD_COMM" *)
Theorem WORD_ADD_COMM : forall v w : word a, v + w = w + v.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_MULT_COMM" *)
Theorem WORD_MULT_COMM : forall v w : word a, v * w = w * v.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_MULT_CLAUSES" *)
Theorem WORD_MULT_CLAUSES : forall v w : word a,
  n2w 0 * v = n2w 0 /\ v * n2w 0 = n2w 0 /\
  n2w 1 * v = v /\ v * n2w 1 = v /\
  (v + n2w 1) * w = v * w + w /\ v * (w + n2w 1) = v + v * w.
Proof. intros; repeat split; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LEFT_ADD_DISTRIB" *)
Theorem WORD_LEFT_ADD_DISTRIB : forall v w x : word a, v * (w + x) = v * w + v * x.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_RIGHT_ADD_DISTRIB" *)
Theorem WORD_RIGHT_ADD_DISTRIB : forall v w x : word a, (v + w) * x = v * x + w * x.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_ADD_SUB_ASSOC" *)
Theorem WORD_ADD_SUB_ASSOC : forall v w x : word a, v + w - x = v + (w - x).
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_ADD_SUB_SYM" *)
Theorem WORD_ADD_SUB_SYM : forall v w x : word a, v + w - x = v - x + w.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_ADD_LINV" *)
Theorem WORD_ADD_LINV : forall w : word a, - w + w = n2w 0.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_ADD_RINV" *)
Theorem WORD_ADD_RINV : forall w : word a, w + - w = n2w 0.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_SUB_REFL" *)
Theorem WORD_SUB_REFL : forall w : word a, w - w = n2w 0.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_SUB_ADD2" *)
Theorem WORD_SUB_ADD2 : forall v w : word a, v + (w - v) = w.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_ADD_SUB" *)
Theorem WORD_ADD_SUB : forall v w : word a, v + w - w = v.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_SUB_ADD" *)
Theorem WORD_SUB_ADD : forall v w : word a, v - w + w = v.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_ADD_EQ_SUB" *)
Theorem WORD_ADD_EQ_SUB : forall v w x : word a, v + w = x <-> v = x - w.
Proof.
  intros v w x; split; intros H; subst; word_ring.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_EQ_ADD_LCANCEL" *)
Theorem WORD_EQ_ADD_LCANCEL : forall v w x : word a, v + w = v + x <-> w = x.
Proof.
  intros v w x; split; intros H; [|subst; reflexivity].
  rewrite <- (WORD_ADD_SUB w v), <- (WORD_ADD_SUB x v), (WORD_ADD_COMM w),
    (WORD_ADD_COMM x), H; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_EQ_ADD_RCANCEL" *)
Theorem WORD_EQ_ADD_RCANCEL : forall v w x : word a, v + w = x + w <-> v = x.
Proof.
  intros v w x; split; intros H; [|subst; reflexivity].
  rewrite <- (WORD_ADD_SUB v w), <- (WORD_ADD_SUB x w), H; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_ADD_INV_0_EQ" *)
Theorem WORD_ADD_INV_0_EQ : forall v w : word a, v + w = v <-> w = n2w 0.
Proof.
  intros v w; rewrite <- (WORD_EQ_ADD_LCANCEL v w (n2w 0)), (proj1 WORD_ADD_0).
  reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NEG" *)
Theorem WORD_NEG : forall w : word a, - w = (¬ w) + n2w 1.
Proof.
  intros w; unfold word_1comp; rewrite word_add_n2w; unfold word_2comp.
  pose proof (w2n_lt w); f_equal; lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NOT" *)
Theorem WORD_NOT : forall w : word a, (¬ w) = - w - n2w 1.
Proof. intros w; rewrite WORD_NEG; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NEG_0" *)
Theorem WORD_NEG_0 : - (n2w 0 : word a) = n2w 0.
Proof. word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NEG_ADD" *)
Theorem WORD_NEG_ADD : forall v w : word a, - (v + w) = - v + - w.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NEG_NEG" *)
Theorem WORD_NEG_NEG : forall w : word a, - (- w) = w.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_SUB_LNEG" *)
Theorem WORD_SUB_LNEG : forall v w : word a, - v - w = - (v + w).
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_SUB_RNEG" *)
Theorem WORD_SUB_RNEG : forall v w : word a, v - - w = v + w.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_SUB_SUB" *)
Theorem WORD_SUB_SUB : forall v w x : word a, v - (w - x) = v + x - w.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_SUB_SUB2" *)
Theorem WORD_SUB_SUB2 : forall v w : word a, v - (v - w) = w.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_EQ_SUB_LADD" *)
Theorem WORD_EQ_SUB_LADD : forall v w x : word a, v = w - x <-> v + x = w.
Proof. intros v w x; split; intros H; subst; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_EQ_SUB_RADD" *)
Theorem WORD_EQ_SUB_RADD : forall v w x : word a, v - w = x <-> v = x + w.
Proof. intros v w x; split; intros H; subst; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_EQ_SUB_ZERO" *)
Theorem WORD_EQ_SUB_ZERO : forall w v : word a, v - w = n2w 0 <-> v = w.
Proof.
  intros w v; rewrite WORD_EQ_SUB_RADD, (proj2 WORD_ADD_0); reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LCANCEL_SUB" *)
Theorem WORD_LCANCEL_SUB : forall v w x : word a, v - w = x - w <-> v = x.
Proof.
  intros v w x; split; intros H; [|subst; reflexivity].
  rewrite <- (WORD_SUB_ADD v w), H; word_ring.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_RCANCEL_SUB" *)
Theorem WORD_RCANCEL_SUB : forall v w x : word a, v - w = v - x <-> w = x.
Proof.
  intros v w x; split; intros H; [|subst; reflexivity].
  rewrite <- (WORD_SUB_SUB2 v w), H; word_ring.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_SUB_PLUS" *)
Theorem WORD_SUB_PLUS : forall v w x : word a, v - (w + x) = v - w - x.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_SUB_LZERO" *)
Theorem WORD_SUB_LZERO : forall w : word a, n2w 0 - w = - w.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_SUB_RZERO" *)
Theorem WORD_SUB_RZERO : forall w : word a, w - n2w 0 = w.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_ADD_LID_UNIQ" *)
Theorem WORD_ADD_LID_UNIQ : forall v w : word a, v + w = w <-> v = n2w 0.
Proof.
  intros v w; rewrite WORD_ADD_EQ_SUB, WORD_SUB_REFL; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_ADD_RID_UNIQ" *)
Theorem WORD_ADD_RID_UNIQ : forall v w : word a, v + w = v <-> w = n2w 0.
Proof. intros v w; rewrite WORD_ADD_COMM; apply WORD_ADD_LID_UNIQ. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_SUM_ZERO" *)
Theorem WORD_SUM_ZERO : forall a0 b : word a, a0 + b = n2w 0 <-> a0 = - b.
Proof. intros a0 b; rewrite WORD_ADD_EQ_SUB, WORD_SUB_LZERO; reflexivity. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_ADD_SUB2" *)
Theorem WORD_ADD_SUB2 : forall v w : word a, w + v - w = v.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_ADD_SUB3" *)
Theorem WORD_ADD_SUB3 : forall v x : word a, v - (v + x) = - x.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_SUB_SUB3" *)
Theorem WORD_SUB_SUB3 : forall w v : word a, v - w - v = - w.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_EQ_NEG" *)
Theorem WORD_EQ_NEG : forall v w : word a, - v = - w <-> v = w.
Proof.
  intros v w; split; intros H; [|subst; reflexivity].
  rewrite <- (WORD_NEG_NEG v), H; apply WORD_NEG_NEG.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NEG_EQ" *)
Theorem WORD_NEG_EQ : forall w v : word a, - v = w <-> v = - w.
Proof.
  intros w v; rewrite <- (WORD_NEG_NEG w) at 1; apply WORD_EQ_NEG.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NEG_EQ_0" *)
Theorem WORD_NEG_EQ_0 : forall v : word a, - v = n2w 0 <-> v = n2w 0.
Proof. intros v; rewrite <- WORD_NEG_0 at 1; apply WORD_EQ_NEG. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_SUB" *)
Theorem WORD_SUB : forall v w : word a, - w + v = v - w.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_SUB_NEG" *)
Theorem WORD_SUB_NEG : forall v w : word a, - v - - w = w - v.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NEG_SUB" *)
Theorem WORD_NEG_SUB : forall w v : word a, - (v - w) = w - v.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_SUB_TRIANGLE" *)
Theorem WORD_SUB_TRIANGLE : forall v w x : word a, v - w + (w - x) = v - x.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_MULT_SUC" *)
Theorem WORD_MULT_SUC : forall (v : word a) n, v * n2w (n + 1) = v * n2w n + v.
Proof. intros; word_Z; rewrite N2Z.inj_add; apply zcong_eq; ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "n2w_SUC" *)
Theorem n2w_SUC : forall n, (n2w (SUC n) : word a) = n2w n + n2w 1.
Proof. intros; word_Z; rewrite N2Z.inj_succ; apply zcong_eq; ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NEG_LMUL" *)
Theorem WORD_NEG_LMUL : forall v w : word a, - (v * w) = (- v) * w.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NEG_RMUL" *)
Theorem WORD_NEG_RMUL : forall v w : word a, - (v * w) = v * - w.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NEG_MUL" *)
Theorem WORD_NEG_MUL : forall w : word a, - w = - n2w 1 * w.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LEFT_SUB_DISTRIB" *)
Theorem WORD_LEFT_SUB_DISTRIB : forall v w x : word a, v * (w - x) = v * w - v * x.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_RIGHT_SUB_DISTRIB" *)
Theorem WORD_RIGHT_SUB_DISTRIB : forall v w x : word a, (w - x) * v = w * v - x * v.
Proof. intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LITERAL_MULT" *)
Theorem WORD_LITERAL_MULT :
  (forall m n, (n2w m : word a) * - (n2w n) = - (n2w (m * n))) /\
  (forall m n, - (n2w m : word a) * - (n2w n) = n2w (m * n)).
Proof. split; intros; word_Z; rewrite N2Z.inj_mul; apply zcong_eq; ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "n2w_sub" *)
Theorem n2w_sub : forall a0 b, (b <= a0)%N -> (n2w (a0 - b) : word a) = n2w a0 - n2w b.
Proof.
  intros a0 b H; word_Z; rewrite N2Z.inj_sub by exact H; apply zcong_eq; ring.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "n2w_sub_eq_0" *)
Theorem n2w_sub_eq_0 : forall a0 b, (a0 <= b)%N -> (n2w (a0 - b) : word a) = n2w 0.
Proof. intros a0 b H; replace (a0 - b)%N with 0%N by lia; reflexivity. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LITERAL_ADD" *)
Theorem WORD_LITERAL_ADD :
  (forall m n, - (n2w m : word a) + - (n2w n) = - (n2w (m + n))) /\
  (forall m n, (n2w m : word a) + - (n2w n) =
     if n <=? m then n2w (m - n) else - (n2w (n - m))).
Proof.
  split; intros m n.
  - word_Z; rewrite N2Z.inj_add; apply zcong_eq; ring.
  - destruct (N.leb_spec n m) as [H|H]; word_Z; rewrite N2Z.inj_sub by lia;
      apply zcong_eq; ring.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_SUB_INTRO" *)
Theorem WORD_SUB_INTRO :
  (forall x y : word a, - y + x = x - y) /\
  (forall x y : word a, x + - y = x - y) /\
  (forall x y z : word a, - x * y + z = z - x * y) /\
  (forall x y z : word a, z + - x * y = z - x * y) /\
  (forall x : word a, - n2w 1 * x = - x) /\
  (forall x y z : word a, z - - x * y = z + x * y) /\
  (forall x y z : word a, - x * y - z = - (x * y + z)).
Proof. repeat split; intros; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NEG_T" *)
Theorem WORD_NEG_T : - (Tw : word a) = n2w 1.
Proof.
  unfold word_T, UINT_MAX; word_Z.
  rewrite N2Z.inj_sub by (pose proof (ZERO_LT_dimword a); lia).
  constructor; replace (- (Z.of_N (dimword a) - Z.of_N 1))%Z
    with (Z.of_N 1 + (-1) * Z.of_N (dimword a))%Z by lia.
  apply Z_mod_plus_full.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NEG_1" *)
Theorem WORD_NEG_1 : - (n2w 1 : word a) = Tw.
Proof. rewrite <- WORD_NEG_T; apply WORD_NEG_NEG. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "w2n_minus1" *)
Theorem w2n_minus1 : w2n (- (n2w 1) : word a) = (dimword a - 1)%N.
Proof.
  rewrite WORD_NEG_1; unfold word_T, UINT_MAX; rewrite w2n_n2w.
  apply N.mod_small; pose proof (ZERO_LT_dimword a); lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NOT_T" *)
Theorem WORD_NOT_T : (¬ (Tw : word a)) = n2w 0.
Proof. rewrite WORD_NOT, WORD_NEG_T; apply WORD_SUB_REFL. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NOT_0" *)
Theorem WORD_NOT_0 : (¬ (n2w 0 : word a)) = Tw.
Proof. rewrite WORD_NOT, WORD_NEG_0, WORD_SUB_LZERO; apply WORD_NEG_1. Qed.

End Arith.

(** ** Comparisons *)

(** Galette-only: [nzcv] in terms of [w2n]. *)

Lemma testbit_two_pow_range q k : q < 2 * 2 ** k -> N.testbit q k = (2 ** k <=? q).
Proof.
  intros Hq; destruct (N.leb_spec (2 ** k) q) as [H|H].
  - replace q with ((q - 2 ** k) + 1 * 2 ** k) by lia.
    rewrite testbit_add_mul_pow by lia.
    rewrite N.ltb_irrefl, N.sub_diag; reflexivity.
  - apply testbit_lt_pow with k; lia.
Qed.

Ltac bool_cases :=
  repeat match goal with
  | |- context [N.leb ?x ?y] => destruct (N.leb_spec x y)
  | |- context [N.ltb ?x ?y] => destruct (N.ltb_spec x y)
  | |- context [N.eqb ?x ?y] => destruct (N.eqb_spec x y)
  | _ : context [N.leb ?x ?y] |- _ => destruct (N.leb_spec x y)
  | _ : context [N.ltb ?x ?y] |- _ => destruct (N.ltb_spec x y)
  | _ : context [N.eqb ?x ?y] |- _ => destruct (N.eqb_spec x y)
  end.

Section Order.
Context {a : N}.

Lemma INT_MIN_pos : 0 < INT_MIN a.
Proof. apply ZERO_LT_INT_MIN. Qed.

Lemma word_msb_w2n (w : word a) : word_msb w = (INT_MIN a <=? w2n w).
Proof.
  unfold word_msb; rewrite BIT_testbit; unfold INT_MIN.
  apply testbit_two_pow_range.
  rewrite <- N.pow_succ_r', <- dimindex_split, <- dimword_pow; apply w2n_lt.
Qed.

Lemma bool_decide_eq_0 (w : word a) : bool_decide (w = n2w 0) = (w2n w =? 0).
Proof.
  destruct (N.eqb_spec (w2n w) 0) as [H|H];
    [apply bool_decide_spec, w2n_eq_0, H|].
  destruct (bool_decide (w = n2w 0)) eqn:E; [|reflexivity].
  apply bool_decide_spec, w2n_eq_0 in E; contradiction.
Qed.

Lemma mod_range x d : d <= x < 2 * d -> x MOD d = x - d.
Proof.
  intros H; replace x with ((x - d) + 1 * d) at 1 by lia.
  rewrite N.Div0.mod_add; apply N.mod_small; lia.
Qed.

Lemma nzcv_spec (a0 b : word a) :
  nzcv a0 b =
  (let r := if w2n b <=? w2n a0 then w2n a0 - w2n b
            else w2n a0 + dimword a - w2n b in
   (INT_MIN a <=? r, r =? 0, w2n b <=? w2n a0,
    negb (Bool.eqb (INT_MIN a <=? w2n a0) (INT_MIN a <=? w2n b)) &&
    negb (Bool.eqb (INT_MIN a <=? r) (INT_MIN a <=? w2n a0)))).
Proof.
  unfold nzcv; cbv zeta.
  rewrite !word_msb_w2n, !bool_decide_eq_0, !w2n_n2w, BIT_testbit.
  pose proof (w2n_lt a0) as HA; pose proof (w2n_lt b) as HB.
  pose proof (@dimword_IS_TWICE_INT_MIN a) as HD.
  unfold word_2comp; rewrite w2n_n2w.
  rewrite testbit_two_pow_range, <- dimword_pow.
  2:{ rewrite <- dimword_pow.
      destruct (N.eq_dec (w2n b) 0) as [E|E].
      - rewrite E, N.sub_0_r, N.Div0.mod_same; lia.
      - rewrite N.mod_small; lia. }
  destruct (N.eq_dec (w2n b) 0) as [E|E].
  - rewrite E, N.sub_0_r, N.Div0.mod_same, N.add_0_r, (N.mod_small (w2n a0))
      by lia.
    bool_cases; try lia; reflexivity.
  - rewrite (N.mod_small (dimword a - w2n b)) by lia.
    destruct (N.leb_spec (w2n b) (w2n a0)) as [L|L].
    + rewrite mod_range by lia.
      bool_cases; try lia; reflexivity.
    + rewrite N.mod_small by lia.
      bool_cases; try lia; reflexivity.
Qed.

Lemma word_lo_w2n (a0 b : word a) : word_lo a0 b = (w2n a0 <? w2n b).
Proof. unfold word_lo; rewrite nzcv_spec; cbv zeta; bool_cases; reflexivity || lia. Qed.

Lemma word_ls_w2n (a0 b : word a) : word_ls a0 b = (w2n a0 <=? w2n b).
Proof. unfold word_ls; rewrite nzcv_spec; cbv zeta; bool_cases; reflexivity || lia. Qed.

Lemma word_hi_w2n (a0 b : word a) : word_hi a0 b = (w2n b <? w2n a0).
Proof. unfold word_hi; rewrite nzcv_spec; cbv zeta; bool_cases; reflexivity || lia. Qed.

Lemma word_hs_w2n (a0 b : word a) : word_hs a0 b = (w2n b <=? w2n a0).
Proof. unfold word_hs; rewrite nzcv_spec; cbv zeta; bool_cases; reflexivity || lia. Qed.

(** Signed value of a word. *)
Definition Zs (w : word a) : Z :=
  if INT_MIN a <=? w2n w then (Z.of_N (w2n w) - Z.of_N (dimword a))%Z
  else Z.of_N (w2n w).

Lemma word_lt_Zs (a0 b : word a) : word_lt a0 b = (Zs a0 <? Zs b)%Z.
Proof.
  unfold word_lt, Zs; rewrite nzcv_spec; cbv zeta.
  pose proof (w2n_lt a0); pose proof (w2n_lt b).
  pose proof (@dimword_IS_TWICE_INT_MIN a).
  bool_cases; cbn [negb andb orb Bool.eqb]; symmetry; first [apply Z.ltb_lt; lia|apply Z.ltb_ge; lia].
Qed.

Lemma word_le_Zs (a0 b : word a) : word_le a0 b = (Zs a0 <=? Zs b)%Z.
Proof.
  unfold word_le, Zs; rewrite nzcv_spec; cbv zeta.
  pose proof (w2n_lt a0); pose proof (w2n_lt b).
  pose proof (@dimword_IS_TWICE_INT_MIN a).
  bool_cases; cbn [negb andb orb Bool.eqb]; symmetry; first [apply Z.leb_le; lia|apply Z.leb_gt; lia].
Qed.

Lemma word_gt_Zs (a0 b : word a) : word_gt a0 b = (Zs b <? Zs a0)%Z.
Proof.
  unfold word_gt, Zs; rewrite nzcv_spec; cbv zeta.
  pose proof (w2n_lt a0); pose proof (w2n_lt b).
  pose proof (@dimword_IS_TWICE_INT_MIN a).
  bool_cases; cbn [negb andb orb Bool.eqb]; symmetry; first [apply Z.ltb_lt; lia|apply Z.ltb_ge; lia].
Qed.

Lemma word_ge_Zs (a0 b : word a) : word_ge a0 b = (Zs b <=? Zs a0)%Z.
Proof.
  unfold word_ge, Zs; rewrite nzcv_spec; cbv zeta.
  pose proof (w2n_lt a0); pose proof (w2n_lt b).
  pose proof (@dimword_IS_TWICE_INT_MIN a).
  bool_cases; cbn [negb andb orb Bool.eqb]; symmetry; first [apply Z.leb_le; lia|apply Z.leb_gt; lia].
Qed.

Lemma Zs_inj (v w : word a) : Zs v = Zs w -> v = w.
Proof.
  unfold Zs; pose proof (w2n_lt v); pose proof (w2n_lt w).
  pose proof (@dimword_IS_TWICE_INT_MIN a).
  intros E; apply word_eq_w2n; bool_cases; lia.
Qed.

End Order.

Ltac word_cmp :=
  repeat match goal with
  | |- context [word_lo ?x ?y] => rewrite (word_lo_w2n x y)
  | |- context [word_ls ?x ?y] => rewrite (word_ls_w2n x y)
  | |- context [word_hi ?x ?y] => rewrite (word_hi_w2n x y)
  | |- context [word_hs ?x ?y] => rewrite (word_hs_w2n x y)
  | |- context [word_lt ?x ?y] => rewrite (word_lt_Zs x y)
  | |- context [word_le ?x ?y] => rewrite (word_le_Zs x y)
  | |- context [word_gt ?x ?y] => rewrite (word_gt_Zs x y)
  | |- context [word_ge ?x ?y] => rewrite (word_ge_Zs x y)
  end;
  unfold is_true;
  rewrite ?N.ltb_lt, ?N.leb_le, ?N.ltb_ge, ?N.leb_gt, ?Z.ltb_lt, ?Z.leb_le.

Section Compare.
Context {a : N}.
Local Open Scope word_scope.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LO" *)
Theorem WORD_LO : forall a0 b : word a, a0 <+ b <-> (w2n a0 < w2n b)%N.
Proof. intros; word_cmp; split; intros; lia. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LS" *)
Theorem WORD_LS : forall a0 b : word a, a0 <=+ b <-> (w2n a0 <= w2n b)%N.
Proof. intros; word_cmp; split; intros; lia. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_HI" *)
Theorem WORD_HI : forall a0 b : word a, a0 >+ b <-> (w2n a0 > w2n b)%N.
Proof. intros; word_cmp; split; intros; lia. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_HS" *)
Theorem WORD_HS : forall a0 b : word a, a0 >=+ b <-> (w2n a0 >= w2n b)%N.
Proof. intros; word_cmp; split; intros; lia. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_lo_n2w" *)
Theorem word_lo_n2w : forall a0 b,
  (n2w a0 : word a) <+ n2w b <-> (a0 MOD dimword a < b MOD dimword a)%N.
Proof. intros; word_cmp; rewrite !w2n_n2w; split; intros; lia. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_ls_n2w" *)
Theorem word_ls_n2w : forall a0 b,
  (n2w a0 : word a) <=+ n2w b <-> (a0 MOD dimword a <= b MOD dimword a)%N.
Proof. intros; word_cmp; rewrite !w2n_n2w; split; intros; lia. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_hi_n2w" *)
Theorem word_hi_n2w : forall a0 b,
  (n2w a0 : word a) >+ n2w b <-> (a0 MOD dimword a > b MOD dimword a)%N.
Proof. intros; word_cmp; rewrite !w2n_n2w; split; intros; lia. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_hs_n2w" *)
Theorem word_hs_n2w : forall a0 b,
  (n2w a0 : word a) >=+ n2w b <-> (a0 MOD dimword a >= b MOD dimword a)%N.
Proof. intros; word_cmp; rewrite !w2n_n2w; split; intros; lia. Qed.

Ltac signed_cases :=
  intros; word_cmp; rewrite ?word_msb_w2n; unfold Zs, is_true in *;
  pose proof (@dimword_IS_TWICE_INT_MIN a);
  repeat match goal with w : word a |- _ => pose proof (w2n_lt w); revert w end;
  intros; bool_cases;
  repeat match goal with
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y)
  | |- context [Z.leb ?x ?y] => destruct (Z.leb_spec x y)
  end.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LT" *)
Theorem WORD_LT : forall a0 b : word a,
  a0 < b <-> (word_msb a0 = word_msb b /\ (w2n a0 < w2n b)%N) \/
             (word_msb a0 /\ ~ word_msb b).
Proof.
  intros a0 b; rewrite word_lt_Zs, !word_msb_w2n; unfold Zs, is_true.
  pose proof (@dimword_IS_TWICE_INT_MIN a); pose proof (w2n_lt a0); pose proof (w2n_lt b).
  bool_cases; rewrite ?Z.ltb_lt, ?Z.ltb_ge; intuition (try discriminate; try lia).
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LE" *)
Theorem WORD_LE : forall a0 b : word a,
  a0 <= b <-> (word_msb a0 = word_msb b /\ (w2n a0 <= w2n b)%N) \/
              (word_msb a0 /\ ~ word_msb b).
Proof.
  intros a0 b; rewrite word_le_Zs, !word_msb_w2n; unfold Zs, is_true.
  pose proof (@dimword_IS_TWICE_INT_MIN a); pose proof (w2n_lt a0); pose proof (w2n_lt b).
  bool_cases; rewrite ?Z.leb_le, ?Z.leb_gt; intuition (try discriminate; try lia).
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_GT" *)
Theorem WORD_GT : forall a0 b : word a,
  a0 > b <-> (word_msb b = word_msb a0 /\ (w2n a0 > w2n b)%N) \/
             (word_msb b /\ ~ word_msb a0).
Proof.
  intros a0 b; rewrite word_gt_Zs, !word_msb_w2n; unfold Zs, is_true.
  pose proof (@dimword_IS_TWICE_INT_MIN a); pose proof (w2n_lt a0); pose proof (w2n_lt b).
  bool_cases; rewrite ?Z.ltb_lt, ?Z.ltb_ge; intuition (try discriminate; try lia).
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_GE" *)
Theorem WORD_GE : forall a0 b : word a,
  a0 >= b <-> (word_msb b = word_msb a0 /\ (w2n a0 >= w2n b)%N) \/
              (word_msb b /\ ~ word_msb a0).
Proof.
  intros a0 b; rewrite word_ge_Zs, !word_msb_w2n; unfold Zs, is_true.
  pose proof (@dimword_IS_TWICE_INT_MIN a); pose proof (w2n_lt a0); pose proof (w2n_lt b).
  bool_cases; rewrite ?Z.leb_le, ?Z.leb_gt; intuition (try discriminate; try lia).
Qed.

(** Signed order. *)

Lemma lt_Zs (a0 b : word a) : a0 < b <-> (Zs a0 < Zs b)%Z.
Proof. rewrite word_lt_Zs; unfold is_true; apply Z.ltb_lt. Qed.

Lemma le_Zs (a0 b : word a) : a0 <= b <-> (Zs a0 <= Zs b)%Z.
Proof. rewrite word_le_Zs; unfold is_true; apply Z.leb_le. Qed.

Lemma gt_Zs (a0 b : word a) : a0 > b <-> (Zs b < Zs a0)%Z.
Proof. rewrite word_gt_Zs; unfold is_true; apply Z.ltb_lt. Qed.

Lemma ge_Zs (a0 b : word a) : a0 >= b <-> (Zs b <= Zs a0)%Z.
Proof. rewrite word_ge_Zs; unfold is_true; apply Z.leb_le. Qed.

Lemma eq_Zs (a0 b : word a) : a0 = b <-> Zs a0 = Zs b.
Proof. split; [intros ->; reflexivity|apply Zs_inj]. Qed.

Ltac sord :=
  intros; rewrite ?lt_Zs, ?le_Zs, ?gt_Zs, ?ge_Zs, ?eq_Zs in *; lia.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_GREATER" *)
Theorem WORD_GREATER : forall a0 b : word a, a0 > b <-> b < a0.
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_GREATER_EQ" *)
Theorem WORD_GREATER_EQ : forall a0 b : word a, a0 >= b <-> b <= a0.
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NOT_LESS" *)
Theorem WORD_NOT_LESS : forall a0 b : word a, ~ (a0 < b) <-> b <= a0.
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NOT_LESS_EQUAL" *)
Theorem WORD_NOT_LESS_EQUAL : forall a0 b : word a, ~ (a0 <= b) <-> b < a0.
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LESS_OR_EQ" *)
Theorem WORD_LESS_OR_EQ : forall a0 b : word a, a0 <= b <-> a0 < b \/ a0 = b.
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_GREATER_OR_EQ" *)
Theorem WORD_GREATER_OR_EQ : forall a0 b : word a, a0 >= b <-> a0 > b \/ a0 = b.
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LESS_TRANS" *)
Theorem WORD_LESS_TRANS : forall a0 b c : word a, a0 < b /\ b < c -> a0 < c.
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LESS_EQ_TRANS" *)
Theorem WORD_LESS_EQ_TRANS : forall a0 b c : word a, a0 <= b /\ b <= c -> a0 <= c.
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LESS_EQ_LESS_TRANS" *)
Theorem WORD_LESS_EQ_LESS_TRANS : forall a0 b c : word a, a0 <= b /\ b < c -> a0 < c.
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LESS_LESS_EQ_TRANS" *)
Theorem WORD_LESS_LESS_EQ_TRANS : forall a0 b c : word a, a0 < b /\ b <= c -> a0 < c.
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LESS_EQ_CASES" *)
Theorem WORD_LESS_EQ_CASES : forall a0 b : word a, a0 <= b \/ b <= a0.
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LESS_CASES" *)
Theorem WORD_LESS_CASES : forall a0 b : word a, a0 < b \/ b <= a0.
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LESS_CASES_IMP" *)
Theorem WORD_LESS_CASES_IMP : forall a0 b : word a, ~ (a0 < b) /\ ~ (a0 = b) -> b < a0.
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LESS_ANTISYM" *)
Theorem WORD_LESS_ANTISYM : forall a0 b : word a, ~ (a0 < b /\ b < a0).
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LESS_EQ_ANTISYM" *)
Theorem WORD_LESS_EQ_ANTISYM : forall a0 b : word a, ~ (a0 < b /\ b <= a0).
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LESS_EQ_REFL" *)
Theorem WORD_LESS_EQ_REFL : forall a0 : word a, a0 <= a0.
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LESS_EQUAL_ANTISYM" *)
Theorem WORD_LESS_EQUAL_ANTISYM : forall a0 b : word a, a0 <= b /\ b <= a0 -> a0 = b.
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LESS_IMP_LESS_OR_EQ" *)
Theorem WORD_LESS_IMP_LESS_OR_EQ : forall a0 b : word a, a0 < b -> a0 <= b.
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LESS_REFL" *)
Theorem WORD_LESS_REFL : forall a0 : word a, ~ (a0 < a0).
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LESS_LESS_CASES" *)
Theorem WORD_LESS_LESS_CASES : forall a0 b : word a, a0 = b \/ a0 < b \/ b < a0.
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NOT_GREATER" *)
Theorem WORD_NOT_GREATER : forall a0 b : word a, ~ (a0 > b) <-> a0 <= b.
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LESS_NOT_EQ" *)
Theorem WORD_LESS_NOT_EQ : forall a0 b : word a, a0 < b -> ~ (a0 = b).
Proof. sord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NOT_LESS_EQ" *)
Theorem WORD_NOT_LESS_EQ : forall a0 b : word a, a0 = b -> ~ (a0 < b).
Proof. sord. Qed.

(** Unsigned order. *)

Ltac uord :=
  intros; rewrite ?WORD_LO, ?WORD_LS, ?WORD_HI, ?WORD_HS, <- ?w2n_11 in *; lia.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_HIGHER" *)
Theorem WORD_HIGHER : forall a0 b : word a, a0 >+ b <-> b <+ a0.
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_HIGHER_EQ" *)
Theorem WORD_HIGHER_EQ : forall a0 b : word a, a0 >=+ b <-> b <=+ a0.
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NOT_LOWER" *)
Theorem WORD_NOT_LOWER : forall a0 b : word a, ~ (a0 <+ b) <-> b <=+ a0.
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NOT_LOWER_EQUAL" *)
Theorem WORD_NOT_LOWER_EQUAL : forall a0 b : word a, ~ (a0 <=+ b) <-> b <+ a0.
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LOWER_OR_EQ" *)
Theorem WORD_LOWER_OR_EQ : forall a0 b : word a, a0 <=+ b <-> a0 <+ b \/ a0 = b.
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_HIGHER_OR_EQ" *)
Theorem WORD_HIGHER_OR_EQ : forall a0 b : word a, a0 >=+ b <-> a0 >+ b \/ a0 = b.
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LOWER_TRANS" *)
Theorem WORD_LOWER_TRANS : forall a0 b c : word a, a0 <+ b /\ b <+ c -> a0 <+ c.
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LOWER_EQ_TRANS" *)
Theorem WORD_LOWER_EQ_TRANS : forall a0 b c : word a, a0 <=+ b /\ b <=+ c -> a0 <=+ c.
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LOWER_EQ_LOWER_TRANS" *)
Theorem WORD_LOWER_EQ_LOWER_TRANS : forall a0 b c : word a, a0 <=+ b /\ b <+ c -> a0 <+ c.
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LOWER_LOWER_EQ_TRANS" *)
Theorem WORD_LOWER_LOWER_EQ_TRANS : forall a0 b c : word a, a0 <+ b /\ b <=+ c -> a0 <+ c.
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LOWER_EQ_CASES" *)
Theorem WORD_LOWER_EQ_CASES : forall a0 b : word a, a0 <=+ b \/ b <=+ a0.
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LOWER_CASES" *)
Theorem WORD_LOWER_CASES : forall a0 b : word a, a0 <+ b \/ b <=+ a0.
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LOWER_CASES_IMP" *)
Theorem WORD_LOWER_CASES_IMP : forall a0 b : word a, ~ (a0 <+ b) /\ ~ (a0 = b) -> b <+ a0.
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LOWER_ANTISYM" *)
Theorem WORD_LOWER_ANTISYM : forall a0 b : word a, ~ (a0 <+ b /\ b <+ a0).
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LOWER_EQ_ANTISYM" *)
Theorem WORD_LOWER_EQ_ANTISYM : forall a0 b : word a, ~ (a0 <+ b /\ b <=+ a0).
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LOWER_EQ_REFL" *)
Theorem WORD_LOWER_EQ_REFL : forall a0 : word a, a0 <=+ a0.
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LOWER_EQUAL_ANTISYM" *)
Theorem WORD_LOWER_EQUAL_ANTISYM : forall a0 b : word a, a0 <=+ b /\ b <=+ a0 -> a0 = b.
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LOWER_IMP_LOWER_OR_EQ" *)
Theorem WORD_LOWER_IMP_LOWER_OR_EQ : forall a0 b : word a, a0 <+ b -> a0 <=+ b.
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LOWER_REFL" *)
Theorem WORD_LOWER_REFL : forall a0 : word a, ~ (a0 <+ a0).
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LOWER_LOWER_CASES" *)
Theorem WORD_LOWER_LOWER_CASES : forall a0 b : word a, a0 = b \/ a0 <+ b \/ b <+ a0.
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NOT_HIGHER" *)
Theorem WORD_NOT_HIGHER : forall a0 b : word a, ~ (a0 >+ b) <-> a0 <=+ b.
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LOWER_NOT_EQ" *)
Theorem WORD_LOWER_NOT_EQ : forall a0 b : word a, a0 <+ b -> ~ (a0 = b).
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NOT_LOWER_EQ" *)
Theorem WORD_NOT_LOWER_EQ : forall a0 b : word a, a0 = b -> ~ (a0 <+ b).
Proof. uord. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_0_LS" *)
Theorem WORD_0_LS : forall w : word a, n2w 0 <=+ w.
Proof. intros; rewrite WORD_LS, word_0_n2w; lia. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LS_T" *)
Theorem WORD_LS_T : forall w : word a, w <=+ UINT_MAXw.
Proof.
  intros w; rewrite WORD_LS; unfold word_T, UINT_MAX; rewrite w2n_n2w, N.mod_small;
    pose proof (w2n_lt w); pose proof (ZERO_LT_dimword a); lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LS_word_0" *)
Theorem WORD_LS_word_0 : forall n : word a, n <=+ n2w 0 <-> n = n2w 0.
Proof. intros n; rewrite WORD_LS, word_0_n2w, <- w2n_eq_0; lia. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LO_word_0" *)
Theorem WORD_LO_word_0 :
  (forall n : word a, n2w 0 <+ n <-> ~ (n = n2w 0)) /\ (forall n : word a, ~ (n <+ n2w 0)).
Proof.
  split; intros n; rewrite WORD_LO, word_0_n2w; [rewrite <- w2n_eq_0|]; lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LO_word_0R" *)
Theorem WORD_LO_word_0R : forall n : word a, ~ (n <+ n2w 0).
Proof. apply WORD_LO_word_0. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_MSB_INT_MIN_LS" *)
Theorem WORD_MSB_INT_MIN_LS : forall a0 : word a, word_msb a0 <-> INT_MINw <=+ a0.
Proof.
  intros a0; rewrite WORD_LS, word_msb_w2n; unfold word_L; rewrite w2n_n2w, N.mod_small
    by apply INT_MIN_LT_DIMWORD.
  unfold is_true; apply N.leb_le.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_sub_w2n" *)
Theorem word_sub_w2n : forall x y : word a, y <=+ x -> w2n (x - y) = (w2n x - w2n y)%N.
Proof.
  intros x y H; rewrite WORD_LS in H.
  rewrite <- (n2w_w2n x), <- (n2w_w2n y) at 1.
  rewrite <- n2w_sub by exact H; rewrite w2n_n2w; apply N.mod_small.
  pose proof (w2n_lt x); lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "w2n_add_2" *)
Theorem w2n_add_2 : forall a0 b : word a,
  (w2n a0 + w2n b < dimword a)%N -> w2n (a0 + b) = (w2n a0 + w2n b)%N.
Proof. intros a0 b H; unfold word_add; rewrite w2n_n2w; apply N.mod_small, H. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "w2n_add" *)
Theorem w2n_add : forall a0 b : word a,
  ~ word_msb a0 /\ ~ word_msb b -> w2n (a0 + b) = (w2n a0 + w2n b)%N.
Proof.
  intros a0 b [Ha Hb]; apply w2n_add_2; rewrite !word_msb_w2n in *; unfold is_true in *.
  rewrite N.leb_le in Ha, Hb; pose proof (@dimword_IS_TWICE_INT_MIN a); lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_0_POS" *)
Theorem WORD_0_POS : ~ word_msb (n2w 0 : word a).
Proof.
  rewrite word_msb_w2n, word_0_n2w; pose proof (@ZERO_LT_INT_MIN a); unfold is_true.
  rewrite N.leb_le; lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_L_NEG" *)
Theorem WORD_L_NEG : word_msb (word_L : word a).
Proof.
  rewrite WORD_MSB_INT_MIN_LS; apply WORD_LOWER_EQ_REFL.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_H_POS" *)
Theorem WORD_H_POS : ~ word_msb (word_H : word a).
Proof.
  rewrite word_msb_w2n; unfold word_H, INT_MAX; rewrite w2n_n2w, N.mod_small.
  - pose proof (@ZERO_LT_INT_MIN a); unfold is_true; rewrite N.leb_le; lia.
  - pose proof (@INT_MIN_LT_DIMWORD a); lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_msb_neg" *)
Theorem word_msb_neg : forall w : word a, word_msb w <-> w < n2w 0.
Proof.
  intros w; rewrite lt_Zs, word_msb_w2n; unfold Zs; rewrite word_0_n2w.
  pose proof (@ZERO_LT_INT_MIN a); pose proof (w2n_lt w); unfold is_true.
  bool_cases; split; intros; try discriminate; try reflexivity; lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_ZERO_LE" *)
Theorem WORD_ZERO_LE : forall w : word a, n2w 0 <= w <-> (w2n w < INT_MIN a)%N.
Proof.
  intros w; rewrite le_Zs; unfold Zs; rewrite word_0_n2w.
  pose proof (@ZERO_LT_INT_MIN a); pose proof (w2n_lt w).
  pose proof (@dimword_IS_TWICE_INT_MIN a).
  bool_cases; split; intros; lia.
Qed.

End Compare.

(** ** Bitwise operations *)

Lemma fcp_index_zero {a} i : fcp_index (n2w 0 : word a) i = false.
Proof. unfold fcp_index; rewrite w2n_n2w, N.Div0.mod_0_l, BIT_testbit; apply N.bits_0. Qed.

Ltac bit_simp Hi :=
  repeat first
    [ rewrite fcp_index_word_and by exact Hi
    | rewrite fcp_index_word_or by exact Hi
    | rewrite fcp_index_word_xor by exact Hi
    | rewrite fcp_index_word_1comp by exact Hi
    | rewrite fcp_index_word_T by exact Hi
    | rewrite fcp_index_zero ].

Ltac bitwise :=
  intros; apply word_bit_ext; let i := fresh "i" in let Hi := fresh "Hi" in
  intros i Hi; bit_simp Hi;
  repeat match goal with |- context [fcp_index ?w ?j] => destruct (fcp_index w j) end;
  reflexivity.

Section Bitwise.
Context {a : N}.
Local Open Scope word_scope.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NOT_NOT" *)
Theorem WORD_NOT_NOT : forall a0 : word a, (¬ (¬ a0)) = a0.
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_DE_MORGAN_THM" *)
Theorem WORD_DE_MORGAN_THM : forall a0 b : word a,
  (¬ (a0 && b)) = ((¬ a0) || (¬ b)) /\ (¬ (a0 || b)) = ((¬ a0) && (¬ b)).
Proof. split; bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_NOT_XOR" *)
Theorem WORD_NOT_XOR : forall a0 b : word a,
  (¬ a0) ?? (¬ b) = a0 ?? b /\ a0 ?? (¬ b) = (¬ (a0 ?? b)) /\ (¬ a0) ?? b = (¬ (a0 ?? b)).
Proof. repeat split; bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_AND_CLAUSES" *)
Theorem WORD_AND_CLAUSES : forall a0 : word a,
  (Tw && a0 = a0) /\ (a0 && Tw = a0) /\
  (n2w 0 && a0 = n2w 0) /\ (a0 && n2w 0 = n2w 0) /\ (a0 && a0 = a0).
Proof. repeat split; bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_OR_CLAUSES" *)
Theorem WORD_OR_CLAUSES : forall a0 : word a,
  (Tw || a0 = Tw) /\ (a0 || Tw = Tw) /\
  (n2w 0 || a0 = a0) /\ (a0 || n2w 0 = a0) /\ (a0 || a0 = a0).
Proof. repeat split; bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_XOR_CLAUSES" *)
Theorem WORD_XOR_CLAUSES : forall a0 : word a,
  (Tw ?? a0 = (¬ a0)) /\ (a0 ?? Tw = (¬ a0)) /\
  (n2w 0 ?? a0 = a0) /\ (a0 ?? n2w 0 = a0) /\ (a0 ?? a0 = n2w 0).
Proof. repeat split; bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_AND_ASSOC" *)
Theorem WORD_AND_ASSOC : forall a0 b c : word a, (a0 && b) && c = a0 && (b && c).
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_OR_ASSOC" *)
Theorem WORD_OR_ASSOC : forall a0 b c : word a, (a0 || b) || c = a0 || (b || c).
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_XOR_ASSOC" *)
Theorem WORD_XOR_ASSOC : forall a0 b c : word a, (a0 ?? b) ?? c = a0 ?? (b ?? c).
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_AND_COMM" *)
Theorem WORD_AND_COMM : forall a0 b : word a, a0 && b = b && a0.
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_OR_COMM" *)
Theorem WORD_OR_COMM : forall a0 b : word a, a0 || b = b || a0.
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_XOR_COMM" *)
Theorem WORD_XOR_COMM : forall a0 b : word a, a0 ?? b = b ?? a0.
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_AND_IDEM" *)
Theorem WORD_AND_IDEM : forall a0 : word a, a0 && a0 = a0.
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_OR_IDEM" *)
Theorem WORD_OR_IDEM : forall a0 : word a, a0 || a0 = a0.
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_AND_ABSORD" *)
Theorem WORD_AND_ABSORD : forall a0 b : word a, a0 || (a0 && b) = a0.
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_OR_ABSORB" *)
Theorem WORD_OR_ABSORB : forall a0 b : word a, a0 && (a0 || b) = a0.
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_AND_COMP" *)
Theorem WORD_AND_COMP : forall a0 : word a, a0 && (¬ a0) = n2w 0.
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_OR_COMP" *)
Theorem WORD_OR_COMP : forall a0 : word a, a0 || (¬ a0) = Tw.
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_XOR_COMP" *)
Theorem WORD_XOR_COMP : forall a0 : word a, a0 ?? (¬ a0) = Tw.
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_RIGHT_AND_OVER_OR" *)
Theorem WORD_RIGHT_AND_OVER_OR : forall a0 b c : word a,
  (a0 || b) && c = (a0 && c) || (b && c).
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_RIGHT_OR_OVER_AND" *)
Theorem WORD_RIGHT_OR_OVER_AND : forall a0 b c : word a,
  (a0 && b) || c = (a0 || c) && (b || c).
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_RIGHT_AND_OVER_XOR" *)
Theorem WORD_RIGHT_AND_OVER_XOR : forall a0 b c : word a,
  (a0 ?? b) && c = (a0 && c) ?? (b && c).
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LEFT_AND_OVER_OR" *)
Theorem WORD_LEFT_AND_OVER_OR : forall a0 b c : word a,
  a0 && (b || c) = (a0 && b) || (a0 && c).
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LEFT_OR_OVER_AND" *)
Theorem WORD_LEFT_OR_OVER_AND : forall a0 b c : word a,
  a0 || (b && c) = (a0 || b) && (a0 || c).
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LEFT_AND_OVER_XOR" *)
Theorem WORD_LEFT_AND_OVER_XOR : forall a0 b c : word a,
  a0 && (b ?? c) = (a0 && b) ?? (a0 && c).
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_XOR" *)
Theorem WORD_XOR : forall a0 b : word a, a0 ?? b = (a0 && (¬ b)) || (b && (¬ a0)).
Proof. bitwise. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_MSB_1COMP" *)
Theorem WORD_MSB_1COMP : forall w : word a, word_msb (¬ w) = negb (word_msb w).
Proof.
  intros w; rewrite !word_msb_def, fcp_index_word_1comp by (pose proof (DIMINDEX_GT_0 a); lia).
  reflexivity.
Qed.

Lemma land_zero_of_word (a0 b : word a) :
  a0 && b = n2w 0 -> N.land (w2n a0) (w2n b) = 0%N.
Proof.
  intros H; apply N.bits_inj_0; intros i.
  rewrite N.land_spec, <- !fcp_index_testbit.
  destruct (N.ltb_spec i (dimindex a)) as [Hi|Hi].
  - apply (f_equal (fun w => fcp_index w i)) in H.
    rewrite fcp_index_word_and, fcp_index_zero in H by exact Hi; exact H.
  - rewrite fcp_index_high by exact Hi; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_ADD_OR" *)
Theorem WORD_ADD_OR : forall a0 b : word a, a0 && b = n2w 0 -> a0 + b = a0 || b.
Proof.
  intros a0 b H; apply land_zero_of_word in H.
  unfold word_add, word_or; f_equal.
  rewrite N.add_nocarry_lxor by exact H.
  apply N.bits_inj; intros i; rewrite N.lxor_spec, N.lor_spec.
  apply (f_equal (fun x => N.testbit x i)) in H.
  rewrite N.land_spec, N.bits_0 in H.
  destruct (N.testbit (w2n a0) i), (N.testbit (w2n b) i); try discriminate; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_ADD_XOR" *)
Theorem WORD_ADD_XOR : forall a0 b : word a, a0 && b = n2w 0 -> a0 + b = a0 ?? b.
Proof.
  intros a0 b H; apply land_zero_of_word in H.
  unfold word_add, word_xor; f_equal; apply N.add_nocarry_lxor, H.
Qed.

End Bitwise.

(** ** Shifts *)

Section Shifts.
Context {a : N}.
Local Open Scope word_scope.

Lemma word_lsr_n2w_div (w : word a) m : w >>> m = n2w (w2n w DIV 2 ** m).
Proof.
  apply word_bit_ext; intros i Hi.
  rewrite fcp_index_word_lsr, fcp_index_n2w, BIT_testbit, N.div_pow2_bits,
    fcp_index_testbit by exact Hi.
  destruct (N.ltb_spec (i + m) (dimindex a)); [reflexivity|].
  symmetry; apply testbit_lt_pow with (dimindex a); [apply w2n_lt|lia].
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "w2n_lsr" *)
Theorem w2n_lsr : forall (w : word a) m, w2n (w >>> m) = (w2n w DIV 2 ** m)%N.
Proof.
  intros w m; rewrite word_lsr_n2w_div, w2n_n2w; apply N.mod_small.
  apply N.le_lt_trans with (w2n w); [apply N.Div0.div_le_upper_bound|apply w2n_lt].
  assert (Hp : (2 ** m)%N <> 0%N) by (apply N.pow_nonzero; lia).
  set (p := (2 ** m)%N) in *; nia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_MUL_LSL" *)
Theorem WORD_MUL_LSL : forall (a0 : word a) n, a0 << n = n2w (2 ** n) * a0.
Proof.
  intros a0 n; unfold word_lsl, word_mul; rewrite w2n_n2w.
  destruct (N.ltb_spec (dimindex a - 1) n) as [H|H].
  - apply n2w_11; rewrite N.Div0.mod_0_l, N.Div0.mul_mod_idemp_l, dimword_pow.
    replace n with ((n - dimindex a) + dimindex a)%N by lia.
    rewrite N.pow_add_r, <- N.mul_assoc, (N.mul_comm (2 ** dimindex a)), N.mul_assoc.
    symmetry; apply N.Div0.mod_mul.
  - apply n2w_11; rewrite N.Div0.mul_mod_idemp_l, N.mul_comm; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_ADD_LSL" *)
Theorem WORD_ADD_LSL : forall n (a0 b : word a), (a0 + b) << n = a0 << n + b << n.
Proof. intros; rewrite !WORD_MUL_LSL; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "LSL_ONE" *)
Theorem LSL_ONE : forall w : word a, w << 1 = w + w.
Proof.
  intros; rewrite WORD_MUL_LSL; change (2 ** 1)%N with 2%N; word_Z.
  change (Z.of_N 2) with 2%Z; apply zcong_eq; ring.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "LSL_ADD" *)
Theorem LSL_ADD : forall (w : word a) m n, w << m << n = w << (m + n).
Proof.
  intros; rewrite !WORD_MUL_LSL, N.pow_add_r; word_Z; rewrite N2Z.inj_mul.
  apply zcong_eq; ring.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "LSR_ADD" *)
Theorem LSR_ADD : forall (w : word a) m n, w >>> m >>> n = w >>> (m + n).
Proof.
  intros; apply word_eq_w2n; rewrite !w2n_lsr, N.pow_add_r, N.Div0.div_div.
  reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "LSR_LIMIT" *)
Theorem LSR_LIMIT : forall (w : word a) n, (dimindex a <= n)%N -> w >>> n = n2w 0.
Proof.
  intros w n H; apply word_eq_w2n; rewrite w2n_lsr, word_0_n2w.
  apply N.div_small; eapply N.lt_le_trans; [apply w2n_lt|].
  rewrite dimword_pow; apply N.pow_le_mono_r; lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "LSL_LIMIT" *)
Theorem LSL_LIMIT : forall (w : word a) n, (dimindex a <= n)%N -> w << n = n2w 0.
Proof.
  intros w n H; unfold word_lsl; pose proof (DIMINDEX_GT_0 a).
  destruct (N.ltb_spec (dimindex a - 1) n); [reflexivity|lia].
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_2COMP_LSL" *)
Theorem WORD_2COMP_LSL : forall n (a0 : word a), (- a0) << n = - (a0 << n).
Proof. intros; rewrite !WORD_MUL_LSL; word_ring. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "LSR_BITWISE" *)
Theorem LSR_BITWISE :
  (forall n (v w : word a), (w >>> n) && (v >>> n) = (w && v) >>> n) /\
  (forall n (v w : word a), (w >>> n) || (v >>> n) = (w || v) >>> n) /\
  (forall n (v w : word a), (w >>> n) ?? (v >>> n) = (w ?? v) >>> n).
Proof.
  repeat split; intros n v w; apply word_bit_ext; intros i Hi; bit_simp Hi;
    rewrite !fcp_index_word_lsr by exact Hi;
    (destruct (N.ltb_spec (i + n) (dimindex a)); [|reflexivity]);
    bit_simp H; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "LSL_BITWISE" *)
Theorem LSL_BITWISE :
  (forall n (v w : word a), (w << n) && (v << n) = (w && v) << n) /\
  (forall n (v w : word a), (w << n) || (v << n) = (w || v) << n) /\
  (forall n (v w : word a), (w << n) ?? (v << n) = (w ?? v) << n).
Proof.
  repeat split; intros n v w; apply word_bit_ext; intros i Hi; bit_simp Hi;
    rewrite !fcp_index_word_lsl by exact Hi;
    (destruct (N.leb_spec n i); [|reflexivity]);
    (assert (Hin : (i - n < dimindex a)%N) by lia);
    bit_simp Hin; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_ALL_BITS" *)
Theorem WORD_ALL_BITS : forall (w : word a) h, (dimindex a - 1 <= h)%N -> (h -- 0) w = w.
Proof.
  intros w h H; apply word_bit_ext; intros i Hi.
  rewrite fcp_index_word_bits, N.add_0_r, MIN_min by exact Hi.
  destruct (N.leb_spec i (N.min h (dimindex a - 1))); [reflexivity|lia].
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_BITS_COMP_THM" *)
Theorem WORD_BITS_COMP_THM : forall h1 l1 h2 l2 (w : word a),
  (h2 -- l2) ((h1 -- l1) w) = (MIN h1 (h2 + l1) -- l2 + l1) w.
Proof.
  intros h1 l1 h2 l2 w; apply word_bit_ext; intros i Hi.
  rewrite (fcp_index_word_bits (MIN h1 (h2 + l1)) (l2 + l1) w i Hi).
  rewrite (fcp_index_word_bits h2 l2 _ i Hi), !MIN_min.
  destruct (N.leb_spec (i + l2) (N.min h2 (dimindex a - 1))) as [H|H]; cbn [andb].
  - rewrite fcp_index_word_bits, MIN_min by lia.
    replace (i + l2 + l1)%N with (i + (l2 + l1))%N by lia.
    bool_cases; try lia; reflexivity.
  - destruct (N.leb_spec (i + (l2 + l1)) (N.min (N.min h1 (h2 + l1)) (dimindex a - 1)));
      [lia|reflexivity].
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_BITS_EXTRACT" *)
Theorem WORD_BITS_EXTRACT : forall h l (w : word a), (h -- l) w = ((h >< l) w : word a).
Proof. intros; unfold word_extract; rewrite w2w_id; reflexivity. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_BITS_LSR" *)
Theorem WORD_BITS_LSR : forall h l (w : word a) n, (h -- l) w >>> n = (h -- (l + n)) w.
Proof.
  intros; unfold word_lsr; rewrite WORD_BITS_COMP_THM.
  apply word_bit_ext; intros i Hi.
  rewrite !fcp_index_word_bits, !MIN_min by exact Hi.
  replace (i + (n + l))%N with (i + (l + n))%N by lia.
  pose proof (DIMINDEX_GT_0 a).
  destruct (N.leb_spec (i + (l + n)) (N.min (N.min h (dimindex a - 1 + l)) (dimindex a - 1))),
    (N.leb_spec (i + (l + n)) (N.min h (dimindex a - 1))); try lia; reflexivity.
Qed.

End Shifts.

Section WordBit.
Context {a : N}.
Local Open Scope word_scope.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_bit_thm" *)
Theorem word_bit_thm : forall n (w : word a),
  word_bit n w <-> (n < dimindex a)%N /\ fcp_index w n.
Proof.
  intros n w; unfold word_bit, is_true; rewrite andb_true_iff, N.leb_le.
  pose proof (DIMINDEX_GT_0 a); split; intros [H1 H2]; split; auto; lia.
Qed.

Lemma word_bit_index n (w : word a) : word_bit n w = ((n <? dimindex a) && fcp_index w n)%bool.
Proof.
  unfold word_bit; pose proof (DIMINDEX_GT_0 a).
  destruct (N.leb_spec n (dimindex a - 1)), (N.ltb_spec n (dimindex a)); try lia;
    reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_bit_and" *)
Theorem word_bit_and : forall n (w1 w2 : word a),
  word_bit n (w1 && w2) <-> word_bit n w1 /\ word_bit n w2.
Proof.
  intros n w1 w2; rewrite !word_bit_index; unfold is_true.
  destruct (N.ltb_spec n (dimindex a)) as [H|H]; cbn [andb];
    [rewrite fcp_index_word_and by exact H; apply andb_true_iff|intuition discriminate].
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_bit_or" *)
Theorem word_bit_or : forall n (w1 w2 : word a),
  word_bit n (w1 || w2) <-> word_bit n w1 \/ word_bit n w2.
Proof.
  intros n w1 w2; rewrite !word_bit_index; unfold is_true.
  destruct (N.ltb_spec n (dimindex a)) as [H|H]; cbn [andb];
    [rewrite fcp_index_word_or by exact H; apply orb_true_iff|intuition discriminate].
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_bit_lsl" *)
Theorem word_bit_lsl : forall n (w : word a) i,
  word_bit n (w << i) <-> word_bit (n - i) w /\ (n < dimindex a)%N /\ (i <= n)%N.
Proof.
  intros n w i; rewrite !word_bit_index; unfold is_true.
  destruct (N.ltb_spec n (dimindex a)) as [H|H]; cbn [andb];
    [|intuition (try discriminate; try lia)].
  rewrite fcp_index_word_lsl by exact H.
  destruct (N.leb_spec i n); cbn [andb]; [|intuition (try discriminate; try lia)].
  destruct (N.ltb_spec (n - i) (dimindex a)); [|lia]; cbn [andb].
  intuition.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_bit_test" *)
Theorem word_bit_test : forall n (w : word a),
  word_bit n w <-> (w && n2w (2 ** n)) <> n2w 0.
Proof.
  intros n w; rewrite word_bit_index, <- word_bit_ext_iff; unfold is_true.
  split.
  - intros H Hall; apply andb_true_iff in H as [Hn Hw]; apply N.ltb_lt in Hn.
    specialize (Hall n Hn); rewrite fcp_index_word_and, fcp_index_zero,
      fcp_index_n2w, BIT_testbit, N.pow2_bits_true, Hw in Hall by exact Hn.
    discriminate.
  - intros H; destruct (N.ltb_spec n (dimindex a)) as [Hn|Hn]; cbn [andb].
    + destruct (fcp_index w n) eqn:E; [reflexivity|].
      exfalso; apply H; intros i Hi.
      rewrite fcp_index_word_and, fcp_index_zero, fcp_index_n2w, BIT_testbit by exact Hi.
      destruct (N.eq_dec i n) as [->|Ne]; [rewrite E; reflexivity|].
      rewrite N.pow2_bits_false by congruence; apply andb_false_r.
    + exfalso; apply H; intros i Hi.
      rewrite fcp_index_word_and, fcp_index_zero, fcp_index_n2w, BIT_testbit by exact Hi.
      rewrite N.pow2_bits_false by lia; apply andb_false_r.
Qed.

End WordBit.

(** ** Constants *)

Section Constants.
Context {a : N}.
Local Open Scope word_scope.

Lemma w2n_neg (w : word a) :
  w2n (- w) = if (w2n w =? 0)%N then 0%N else (dimword a - w2n w)%N.
Proof.
  unfold word_2comp; rewrite w2n_n2w; pose proof (w2n_lt w).
  destruct (N.eqb_spec (w2n w) 0) as [->|E].
  - rewrite N.sub_0_r; apply N.Div0.mod_same.
  - apply N.mod_small; lia.
Qed.

Lemma w2n_T : w2n (Tw : word a) = (dimword a - 1)%N.
Proof.
  unfold word_T, UINT_MAX; rewrite w2n_n2w; apply N.mod_small.
  pose proof (ZERO_LT_dimword a); lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_0" *)
Theorem word_0 : forall i, (i < dimindex a)%N -> ~ fcp_index (n2w 0 : word a) i.
Proof. intros i _; rewrite fcp_index_zero; discriminate. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_eq_0" *)
Theorem word_eq_0 : forall w : word a,
  w = n2w 0 <-> (forall i, (i < dimindex a)%N -> ~ fcp_index w i).
Proof.
  intros w; split.
  - intros -> i _; rewrite fcp_index_zero; discriminate.
  - intros H; apply word_bit_ext; intros i Hi; rewrite fcp_index_zero.
    specialize (H i Hi); destruct (fcp_index w i); [exfalso; apply H; reflexivity|reflexivity].
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_T" 1253 *)
Theorem word_T_thm : forall i, (i < dimindex a)%N -> fcp_index (Tw : word a) i.
Proof. intros i Hi; rewrite fcp_index_word_T by exact Hi; reflexivity. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_L" 1266 *)
Theorem word_L_thm : forall n, (n < dimindex a)%N ->
  fcp_index (INT_MINw : word a) n <-> n = (dimindex a - 1)%N.
Proof.
  intros n Hn; unfold word_L, INT_MIN; rewrite fcp_index_n2w, BIT_testbit by exact Hn.
  unfold is_true; destruct (N.eq_dec n (dimindex a - 1)) as [->|E].
  - rewrite N.pow2_bits_true; tauto.
  - rewrite N.pow2_bits_false by congruence; split; [discriminate|contradiction].
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_H" 1275 *)
Theorem word_H_thm : forall n, (n < dimindex a)%N ->
  fcp_index (INT_MAXw : word a) n <-> (n < dimindex a - 1)%N.
Proof.
  intros n Hn; unfold word_H, INT_MAX, INT_MIN; rewrite fcp_index_n2w, BIT_testbit by exact Hn.
  replace (2 ** (dimindex a - 1) - 1)%N with (N.ones (dimindex a - 1))
    by (rewrite N.ones_equiv; lia).
  unfold is_true.
  destruct (N.ltb_spec n (dimindex a - 1)) as [H|H].
  - rewrite N.ones_spec_low by exact H; tauto.
  - rewrite N.ones_spec_high by exact H; split; [discriminate|lia].
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "w2n_plus1" *)
Theorem w2n_plus1 : forall a0 : word a,
  (w2n a0 + 1)%N = if decide (a0 = UINT_MAXw) then dimword a else w2n (a0 + n2w 1).
Proof.
  intros a0; destruct (decide (a0 = UINT_MAXw)) as [->|E].
  - rewrite w2n_T; pose proof (ZERO_LT_dimword a); lia.
  - unfold word_add; rewrite word_1_n2w, w2n_n2w; symmetry; apply N.mod_small.
    pose proof (w2n_lt a0); destruct (N.eq_dec (w2n a0) (dimword a - 1)) as [F|F]; [|lia].
    exfalso; apply E, word_eq_w2n; rewrite w2n_T; exact F.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LESS_NEG_LEFT" *)
Theorem WORD_LESS_NEG_LEFT : forall a0 b : word a,
  - a0 <+ b <-> ~ (b = n2w 0) /\ (a0 = n2w 0 \/ - b <+ a0).
Proof.
  intros a0 b; rewrite !WORD_LO, !w2n_neg, <- !w2n_eq_0.
  pose proof (w2n_lt a0); pose proof (w2n_lt b).
  bool_cases; split; intros; lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LESS_NEG_RIGHT" *)
Theorem WORD_LESS_NEG_RIGHT : forall a0 b : word a,
  a0 <+ - b <-> ~ (b = n2w 0) /\ (a0 = n2w 0 \/ b <+ - a0).
Proof.
  intros a0 b; rewrite !WORD_LO, !w2n_neg, <- !w2n_eq_0.
  pose proof (w2n_lt a0); pose proof (w2n_lt b).
  bool_cases; split; intros; lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_T_not_zero" *)
Theorem word_T_not_zero : - n2w 1 <> (n2w 0 : word a).
Proof.
  rewrite WORD_NEG_1; intros H; apply (f_equal w2n) in H.
  rewrite w2n_T, word_0_n2w in H; pose proof (@ONE_LT_dimword a); lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LS_word_T" *)
Theorem WORD_LS_word_T :
  (forall n : word a, - n2w 1 <=+ n <-> n = - n2w 1) /\ (forall n : word a, n <=+ - n2w 1).
Proof.
  rewrite WORD_NEG_1; split; intros n; rewrite WORD_LS, w2n_T; pose proof (w2n_lt n);
    [rewrite <- w2n_11, w2n_T|]; lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LO_word_T" *)
Theorem WORD_LO_word_T :
  (forall n : word a, ~ (- n2w 1 <+ n)) /\ (forall n : word a, n <+ - n2w 1 <-> ~ (n = - n2w 1)).
Proof.
  rewrite WORD_NEG_1; split; intros n; rewrite WORD_LO, w2n_T; pose proof (w2n_lt n);
    [|rewrite <- w2n_11, w2n_T]; lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_lsb_word_T" *)
Theorem word_lsb_word_T : word_lsb (- n2w 1 : word a).
Proof.
  rewrite WORD_NEG_1, word_lsb_def, fcp_index_word_T by apply DIMINDEX_GT_0.
  reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_msb_word_T" *)
Theorem word_msb_word_T : word_msb (- n2w 1 : word a).
Proof.
  rewrite WORD_NEG_1, word_msb_def, fcp_index_word_T
    by (pose proof (DIMINDEX_GT_0 a); lia).
  reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_bit_0_word_T" *)
Theorem word_bit_0_word_T : word_bit 0 (- n2w 1 : word a).
Proof. rewrite <- word_lsb_thm; apply word_lsb_word_T. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "WORD_LESS_0_word_T" *)
Theorem WORD_LESS_0_word_T :
  ~ ((n2w 0 : word a) < - n2w 1) /\ ~ ((n2w 0 : word a) <= - n2w 1) /\
  (- n2w 1 : word a) < n2w 0 /\ (- n2w 1 : word a) <= n2w 0.
Proof.
  pose proof (@word_msb_word_T) as Hm; pose proof (@WORD_0_POS a) as H0.
  rewrite WORD_LT, WORD_LE, WORD_LT, WORD_LE.
  unfold is_true in *; rewrite Hm; destruct (word_msb (n2w 0 : word a));
    [exfalso; apply H0; reflexivity|].
  intuition discriminate.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_log2_1" *)
Theorem word_log2_1 : word_log2 (n2w 1 : word a) = n2w 0.
Proof. unfold word_log2; rewrite word_1_n2w; reflexivity. Qed.

End Constants.
