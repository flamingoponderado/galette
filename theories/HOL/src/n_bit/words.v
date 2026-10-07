(** * HOL4 [words]: machine words

    HOL's ['a word] is the finite Cartesian product [bool['a]] and most
    operations are defined bitwise with [FCP].  HOL evaluates words through
    [n2w]-normal forms ([w2n_n2w], [word_add_n2w], [word_lsl_n2w], ...).
    Galette's carrier [word a] is that normal form: a natural number below
    [dimword a], with an (irrelevant) proof of the bound.  The width index
    [a : nat] plays the role of HOL's type ['a]; [dimindex a] is [a] for
    positive [a] and [1] for [a = 0], mirroring HOL, where [dimindex(:'a) = 1]
    for any infinite ['a] and every [dimindex] is positive.

    Operations whose HOL definition is already in [n2w] form are tagged with
    their [_def].  The others are defined by their HOL [n2w] compute
    theorems, which are proved and tagged; HOL's [FCP]-based [_def]
    equations are tagged when proved over [FCP]/[fcp_index]. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.n_bit Require Import sum_num.
From Stdlib Require Import Eqdep_dec.

(** ** Widths *)

(** HOL [dimindex(:'a)]: the width of ['a word] (from [fcp]). *)
Definition dimindex (a : nat) : nat := Nat.max 1 a.

Lemma DIMINDEX_GT_0 a : 0 < dimindex a.
Proof. unfold dimindex; lia. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "dimword_def" *)
Definition dimword (a : nat) : nat := 2 ** dimindex a.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "INT_MIN_def" *)
Definition INT_MIN (a : nat) : nat := 2 ** (dimindex a - 1).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "UINT_MAX_def" *)
Definition UINT_MAX (a : nat) : nat := dimword a - 1.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "INT_MAX_def" *)
Definition INT_MAX (a : nat) : nat := INT_MIN a - 1.

Lemma ZERO_LT_dimword a : 0 < dimword a.
Proof. unfold dimword; apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia. Qed.

(** ** The carrier *)

Record word (a : nat) : Type := mk_word {
  w2n_val : nat;
  w2n_bound : Nat.ltb w2n_val (dimword a) = true
}.
Arguments mk_word {a} _ _.
Arguments w2n_val {a} _.
Arguments w2n_bound {a} _.

Abbreviation word1 := (word 1).
Abbreviation word2 := (word 2).
Abbreviation word3 := (word 3).
Abbreviation word4 := (word 4).
Abbreviation word5 := (word 5).
Abbreviation word6 := (word 6).
Abbreviation word7 := (word 7).
Abbreviation word8 := (word 8).
Abbreviation word12 := (word 12).
Abbreviation word13 := (word 13).
Abbreviation word16 := (word 16).
Abbreviation word20 := (word 20).
Abbreviation word21 := (word 21).
Abbreviation word32 := (word 32).
Abbreviation word64 := (word 64).

Declare Scope word_scope.
Delimit Scope word_scope with w.
Bind Scope word_scope with word.

Section Ops.
Context {a : nat}.

(** HOL [w2n].  ([w2n_def] is stated over [FCP] indices; see [w2n_def]
    below once [fcp_index] is available.) *)
Definition w2n (w : word a) : nat := w2n_val w.

Lemma n2w_bound n : Nat.ltb (n MOD dimword a) (dimword a) = true.
Proof. apply Nat.ltb_lt, Nat.mod_upper_bound. pose proof (ZERO_LT_dimword a); lia. Qed.

(** HOL [n2w]. *)
Definition n2w (n : nat) : word a := mk_word (n MOD dimword a) (n2w_bound n).

Lemma word_eq_w2n (v w : word a) : w2n v = w2n w -> v = w.
Proof.
  destruct v as [v Hv], w as [w Hw]; cbn; intros ->.
  f_equal; apply UIP_dec, bool_dec.
Qed.

#[global] Instance word_eq_dec : EqDecision (word a).
Proof.
  intros v w; destruct (Nat.eq_dec (w2n v) (w2n w)) as [e|n].
  - left; apply word_eq_w2n, e.
  - right; intros ->; apply n; reflexivity.
Defined.

#[global] Instance word_inhabited : Inhabited (word a) := n2w 0.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "w2n_lt" *)
Theorem w2n_lt : forall w : word a, w2n w < dimword a.
Proof. intros [w Hw]; apply Nat.ltb_lt, Hw. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "w2n_n2w" *)
Theorem w2n_n2w : forall n, w2n (n2w n : word a) = n MOD dimword a.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "n2w_w2n" *)
Theorem n2w_w2n : forall w : word a, n2w (w2n w) = w.
Proof.
  intros w; apply word_eq_w2n; rewrite w2n_n2w; apply Nat.mod_small, w2n_lt.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "n2w_11" *)
Theorem n2w_11 : forall m n,
  (n2w m : word a) = n2w n <-> m MOD dimword a = n MOD dimword a.
Proof.
  intros m n; split.
  - intros H; apply (f_equal w2n) in H; exact H.
  - intros H; apply word_eq_w2n; exact H.
Qed.

Lemma n2w_mod n : (n2w (n MOD dimword a) : word a) = n2w n.
Proof. apply n2w_11; apply Nat.Div0.mod_mod. Qed.

(** ** Constants *)

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_T_def" *)
Definition word_T : word a := n2w (UINT_MAX a).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_L_def" *)
Definition word_L : word a := n2w (INT_MIN a).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_H_def" *)
Definition word_H : word a := n2w (INT_MAX a).

(** ** Arithmetic *)

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_2comp_def" *)
Definition word_2comp (w : word a) : word a := n2w (dimword a - w2n w).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_add_def" *)
Definition word_add (v w : word a) : word a := n2w (w2n v + w2n w).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_mul_def" *)
Definition word_mul (v w : word a) : word a := n2w (w2n v * w2n w).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_exp_def" *)
Definition word_exp (v w : word a) : word a := n2w (w2n v ** w2n w).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_log2_def" *)
Definition word_log2 (w : word a) : word a := n2w (LOG2 (w2n w)).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_sub_def" *)
Definition word_sub (v w : word a) : word a := word_add v (word_2comp w).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_div_def" *)
Definition word_div (v w : word a) : word a := n2w (w2n v DIV w2n w).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_mod_def" *)
Definition word_mod (v w : word a) : word a := n2w (w2n v MOD w2n w).

(** ** Bitwise operations (computational forms; see the [_n2w] theorems) *)

Definition word_1comp (w : word a) : word a := n2w (dimword a - 1 - w2n w).
Definition word_and (v w : word a) : word a := n2w (Nat.land (w2n v) (w2n w)).
Definition word_or (v w : word a) : word a := n2w (Nat.lor (w2n v) (w2n w)).
Definition word_xor (v w : word a) : word a := n2w (Nat.lxor (w2n v) (w2n w)).

(** HOL [w ' i] ([fcp_index]).  Out-of-range indices are unspecified in HOL;
    here they read as [false]. *)
Definition fcp_index (w : word a) (i : nat) : bool := BIT i (w2n w).

(** HOL [FCP i. f i] at word type. *)
Definition FCP (f : nat -> bool) : word a :=
  n2w (SUM (dimindex a) (fun i => SBIT (f i) i)).

Definition word_lsb (w : word a) : bool := ODD (w2n w).
Definition word_msb (w : word a) : bool := BIT (dimindex a - 1) (w2n w).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_bit_def" *)
Definition word_bit (b : nat) (w : word a) : bool :=
  (b <=? dimindex a - 1) && fcp_index w b.

Definition word_bits (h l : nat) (w : word a) : word a :=
  n2w (BITS (MIN h (dimindex a - 1)) l (w2n w)).

Definition word_lsl (w : word a) (n : nat) : word a :=
  if dimindex a - 1 <? n then n2w 0 else n2w (w2n w * 2 ** n).

Definition word_lsr (w : word a) (n : nat) : word a :=
  word_bits (dimindex a - 1) n w.

Definition word_asr (w : word a) (n : nat) : word a :=
  if word_msb w then
    word_or (word_lsl word_T (dimindex a - MIN n (dimindex a))) (word_lsr w n)
  else word_lsr w n.

Definition word_ror (w : word a) (n : nat) : word a :=
  let x := n MOD dimindex a in
  n2w (BITS (dimindex a - 1) x (w2n w) + BITS (x - 1) 0 (w2n w) * 2 ** (dimindex a - x)).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_rol_def" *)
Definition word_rol (w : word a) (n : nat) : word a :=
  word_ror w (dimindex a - n MOD dimindex a).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_lsl_bv_def" *)
Definition word_lsl_bv (w n : word a) : word a := word_lsl w (w2n n).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_lsr_bv_def" *)
Definition word_lsr_bv (w n : word a) : word a := word_lsr w (w2n n).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_asr_bv_def" *)
Definition word_asr_bv (w n : word a) : word a := word_asr w (w2n n).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_sign_extend_def" *)
Definition word_sign_extend (n : nat) (w : word a) : word a :=
  n2w (SIGN_EXTEND n (dimindex a) (w2n w)).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_len_def" *)
Definition word_len (w : word a) : nat := dimindex a.

(** ** Comparisons *)

(*! HOL "HOL/src/n-bit/wordsScript.sml" "nzcv_def" *)
Definition nzcv (a0 b : word a) : bool * bool * bool * bool :=
  let q := w2n a0 + w2n (word_2comp b) in
  let r := (n2w q : word a) in
  (word_msb r, bool_decide (r = n2w 0),
   BIT (dimindex a) q || bool_decide (b = n2w 0),
   negb (Bool.eqb (word_msb a0) (word_msb b)) && negb (Bool.eqb (word_msb r) (word_msb a0))).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_lt_def" *)
Definition word_lt (a0 b : word a) : bool :=
  let '(n, z, c, v) := nzcv a0 b in negb (Bool.eqb n v).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_gt_def" *)
Definition word_gt (a0 b : word a) : bool :=
  let '(n, z, c, v) := nzcv a0 b in negb z && Bool.eqb n v.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_le_def" *)
Definition word_le (a0 b : word a) : bool :=
  let '(n, z, c, v) := nzcv a0 b in z || negb (Bool.eqb n v).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_ge_def" *)
Definition word_ge (a0 b : word a) : bool :=
  let '(n, z, c, v) := nzcv a0 b in Bool.eqb n v.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_ls_def" *)
Definition word_ls (a0 b : word a) : bool :=
  let '(n, z, c, v) := nzcv a0 b in negb c || z.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_hi_def" *)
Definition word_hi (a0 b : word a) : bool :=
  let '(n, z, c, v) := nzcv a0 b in c && negb z.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_lo_def" *)
Definition word_lo (a0 b : word a) : bool :=
  let '(n, z, c, v) := nzcv a0 b in negb c.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_hs_def" *)
Definition word_hs (a0 b : word a) : bool :=
  let '(n, z, c, v) := nzcv a0 b in c.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_min_def" *)
Definition word_min (a0 b : word a) : word a := if word_lo a0 b then a0 else b.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_max_def" *)
Definition word_max (a0 b : word a) : word a := if word_lo a0 b then b else a0.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_smin_def" *)
Definition word_smin (a0 b : word a) : word a := if word_lt a0 b then a0 else b.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_smax_def" *)
Definition word_smax (a0 b : word a) : word a := if word_lt a0 b then b else a0.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_abs_def" *)
Definition word_abs (w : word a) : word a :=
  if word_lt w (n2w 0) then word_2comp w else w.

End Ops.

(** ** Width-changing operations *)

(*! HOL "HOL/src/n-bit/wordsScript.sml" "w2w_def" *)
Definition w2w {a b : nat} (w : word a) : word b := n2w (w2n w).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "sw2sw_def" *)
Definition sw2sw {a b : nat} (w : word a) : word b :=
  n2w (SIGN_EXTEND (dimindex a) (dimindex b) (w2n w)).

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_extract_def" *)
Definition word_extract {a b : nat} (h l : nat) : word a -> word b :=
  w2w ∘ word_bits h l.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_join_def" *)
Definition word_join {a b : nat} (v : word a) (w : word b) : word (a + b) :=
  let cv := (w2w v : word (a + b)) in
  let cw := (w2w w : word (a + b)) in
  word_or (word_lsl cv (dimindex b)) cw.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_concat_def" *)
Definition word_concat {a b c : nat} (v : word a) (w : word b) : word c :=
  w2w (word_join v w).

(** ** HOL notation (HOL's overloads in [words]) *)

Notation "v + w" := (word_add v w) : word_scope.
Notation "v - w" := (word_sub v w) : word_scope.
Notation "v * w" := (word_mul v w) : word_scope.
Notation "- w" := (word_2comp w) : word_scope.
Notation "v ** w" := (word_exp v w) : word_scope.
Notation "v // w" := (word_div v w) (at level 40, left associativity) : word_scope.
Notation "~ w" := (word_1comp w) : word_scope.
Notation "v && w" := (word_and v w) : word_scope.
Notation "v || w" := (word_or v w) : word_scope.
Notation "v ?? w" := (word_xor v w) (at level 50, left associativity) : word_scope.
Notation "w << n" := (word_lsl w n) (at level 33, left associativity) : word_scope.
Notation "w >>> n" := (word_lsr w n) (at level 33, left associativity) : word_scope.
Notation "w >> n" := (word_asr w n) (at level 33, left associativity) : word_scope.
Notation "w #>> n" := (word_ror w n) (at level 33, left associativity) : word_scope.
Notation "w #<< n" := (word_rol w n) (at level 33, left associativity) : word_scope.
Notation "v < w" := (word_lt v w) : word_scope.
Notation "v <= w" := (word_le v w) : word_scope.
Notation "v > w" := (word_gt v w) : word_scope.
Notation "v >= w" := (word_ge v w) : word_scope.
Notation "v <+ w" := (word_lo v w) (at level 70, no associativity) : word_scope.
Notation "v <=+ w" := (word_ls v w) (at level 70, no associativity) : word_scope.
Notation "v >+ w" := (word_hi v w) (at level 70, no associativity) : word_scope.
Notation "v >=+ w" := (word_hs v w) (at level 70, no associativity) : word_scope.
Notation "( h -- l )" := (word_bits h l) : word_scope.
Notation "( h >< l )" := (word_extract h l) : word_scope.
Notation "v @@ w" := (word_concat v w) (at level 60, right associativity) : word_scope.
Notation "w ' i" := (fcp_index w i) (at level 9, i at level 9) : word_scope.
Abbreviation UINT_MAXw := word_T.
Abbreviation INT_MAXw := word_H.
Abbreviation INT_MINw := word_L.
Abbreviation Tw := word_T.

(** ** Compute theorems *)

Section Compute.
Context {a : nat}.

Lemma dimword_pow : dimword a = 2 ** dimindex a.
Proof. reflexivity. Qed.

Lemma dimindex_split : dimindex a = S (dimindex a - 1).
Proof. pose proof (DIMINDEX_GT_0 a); lia. Qed.

Lemma BIT_mod_pow i k n : i < k -> BIT i (n MOD 2 ** k) = BIT i n.
Proof.
  intros H; rewrite !BIT_testbit, Nat.mod_pow2_bits_low by exact H; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_msb_n2w" *)
Theorem word_msb_n2w : forall n, word_msb (n2w n : word a) = BIT (dimindex a - 1) n.
Proof.
  intros n; unfold word_msb; rewrite w2n_n2w, dimword_pow.
  apply BIT_mod_pow; pose proof (DIMINDEX_GT_0 a); lia.
Qed.

Lemma ODD_mod_even n k : 0 < k -> ODD (n MOD 2 ** k) = ODD n.
Proof.
  intros Hk.
  assert (Hodd : forall m, ODD m = Nat.odd m).
  { induction m; [reflexivity|]. cbn [ODD]. rewrite IHm, Nat.odd_succ, <- Nat.negb_odd.
    reflexivity. }
  rewrite !Hodd, <- !Nat.bit0_odd, Nat.mod_pow2_bits_low by exact Hk; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_lsb_n2w" *)
Theorem word_lsb_n2w : forall n, word_lsb (n2w n : word a) = ODD n.
Proof.
  intros n; unfold word_lsb; rewrite w2n_n2w, dimword_pow.
  apply ODD_mod_even, DIMINDEX_GT_0.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_bit_n2w" *)
Theorem word_bit_n2w : forall b n,
  word_bit b (n2w n : word a) = (b <=? dimindex a - 1) && BIT b n.
Proof.
  intros b n; unfold word_bit, fcp_index; rewrite w2n_n2w, dimword_pow.
  pose proof (DIMINDEX_GT_0 a).
  destruct (Nat.leb_spec b (dimindex a - 1)) as [Hb|Hb]; [|reflexivity].
  rewrite !andb_true_l; apply BIT_mod_pow; lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_1comp_n2w" *)
Theorem word_1comp_n2w : forall n,
  (~ (n2w n : word a))%w = n2w (dimword a - 1 - n MOD dimword a).
Proof. reflexivity. Qed.

Lemma BITS_lt h l n : BITS h l n < 2 ** (S h - l).
Proof. unfold BITS, MOD_2EXP; apply Nat.mod_upper_bound, Nat.pow_nonzero; lia. Qed.

Lemma BITS_mod_pow h l k n :
  h < k -> BITS h l (n MOD 2 ** k) = BITS h l n.
Proof.
  intros H; unfold BITS, MOD_2EXP, DIV_2EXP.
  apply Nat.bits_inj; intros i.
  destruct (Nat.ltb_spec i (S h - l)).
  - rewrite !Nat.mod_pow2_bits_low, !Nat.div_pow2_bits, Nat.mod_pow2_bits_low
      by lia; reflexivity.
  - rewrite !Nat.mod_pow2_bits_high by lia; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_bits_n2w" *)
Theorem word_bits_n2w : forall h l n,
  (h -- l)%w (n2w n : word a) = (n2w (BITS (MIN h (dimindex a - 1)) l n) : word a).
Proof.
  intros h l n; unfold word_bits; f_equal; rewrite w2n_n2w, dimword_pow.
  apply BITS_mod_pow. rewrite MIN_min. pose proof (DIMINDEX_GT_0 a); lia.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_lsl_n2w" *)
Theorem word_lsl_n2w : forall n m,
  ((n2w m : word a) << n)%w =
  if dimindex a - 1 <? n then n2w 0 else n2w (m * 2 ** n).
Proof.
  intros n m; unfold word_lsl; destruct (dimindex a - 1 <? n); [reflexivity|].
  apply n2w_11; rewrite w2n_n2w, Nat.Div0.mul_mod_idemp_l; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_lsr_n2w" *)
Theorem word_lsr_n2w : forall (w : word a) n, (w >>> n = (dimindex a - 1 -- n) w)%w.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_asr_n2w" 3660 *)
Theorem word_asr_n2w : forall n (w : word a),
  (w >> n =
  if word_msb w then Tw << (dimindex a - MIN n (dimindex a)) || w >>> n
  else w >>> n)%w.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/n-bit/wordsScript.sml" "word_ror_n2w" *)
Theorem word_ror_n2w : forall n a0,
  ((n2w a0 : word a) #>> n)%w =
  let x := n MOD dimindex a in
  n2w (BITS (dimindex a - 1) x a0 + BITS (x - 1) 0 a0 * 2 ** (dimindex a - x)).
Proof.
  intros n a0; unfold word_ror; cbv zeta; rewrite w2n_n2w, dimword_pow.
  assert (Hx : n MOD dimindex a < dimindex a)
    by (apply Nat.mod_upper_bound; pose proof (DIMINDEX_GT_0 a); lia).
  rewrite !BITS_mod_pow by lia; reflexivity.
Qed.

End Compute.
