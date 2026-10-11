(** * CakeML [lab_to_targetProof]: correctness of single instructions

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml] (HOL
    lines 1784-2931): alignment facts and [Inst_lemma], relating one ASM
    instruction executed by labSem and by the ASM semantics.

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v].
    - The memory cases of [Inst_lemma] are proved through Galette helpers
      describing [read_mem_word] and [write_mem_word] byte by byte
      ([read_mem_word_bits], [write_mem_word_mem]) and through the
      generic [state_rel_inst_step] (the fields of [state_rel] that an
      instruction does not touch); the bit-level identities
      [dimword_eq_32_imp_or_bytes] and [dimword_eq_64_imp_or_bytes] are
      ported but not used by them.
    - Not ported: the ML value [share_mem_state_rel_tac] (a tactic). *)

From Galette Require Import Base Classical.
From Stdlib Require Import Setoid.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.relation Require Import relation.
From Galette.HOL.src.finite_maps Require Import alist sptree.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.semantics.proofs Require Import evaluateProps.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.compiler.backend Require Import labLang lab_to_target.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend.semantics Require wordSem backendProps.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem targetProps.
From Galette.cakeml.compiler.backend.semantics Require Import labSem labProps.
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import basic bytes.
Import wordLang (word_loc, Word, Loc).
Import wordSem (mem_load_byte_aux, mem_store_byte_aux, write_bytearray, mem_load_32,
  mem_store_32, buffer, position, buffer_buffer, space_left).
Import ByteBits.
Open Scope N_scope.

(** Decide the comparisons of a goal by [lia] (Galette helper). *)
Ltac simpl_cmp :=
  repeat match goal with
         | |- context [?x <? ?y] =>
             first [rewrite (proj2 (N.ltb_lt x y)) by lia
                   |rewrite (proj2 (N.ltb_ge x y)) by lia]
         | |- context [?x <=? ?y] =>
             first [rewrite (proj2 (N.leb_le x y)) by lia
                   |rewrite (proj2 (N.leb_gt x y)) by lia]
         | |- context [?x =? ?y] =>
             first [rewrite (proj2 (N.eqb_eq x y)) by lia
                   |rewrite (proj2 (N.eqb_neq x y)) by lia]
         end; cbn [andb orb negb].

Ltac bit_solve :=
  simpl_cmp; rewrite ?Bool.orb_false_r, ?Bool.andb_true_r;
  try reflexivity; try (f_equal; lia).


Section Alignment.
Context {a : N}.
Local Open Scope word_scope.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "MULT_ADD_LESS_MULT" *)
Theorem MULT_ADD_LESS_MULT : forall m n k l j,
  (m < l /\ n < k /\ j <= k -> m * j + n < l * k)%N.
Proof. intros m n k l j (H1 & H2 & H3). nia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "aligned_IMP_ADD_LESS_dimword" *)
Theorem aligned_IMP_ADD_LESS_dimword : forall k (x : word a),
  aligned k x /\ (k <= dimindex a)%N -> (w2n x + (2 ** k - 1) < dimword a)%N.
Proof.
  intros k x [Ha Hk]. apply aligned_w2n in Ha. pose proof (w2n_lt x) as Hx.
  unfold dimword in *. replace (dimindex a) with (k + (dimindex a - k))%N in * by lia.
  rewrite N.pow_add_r in *.
  pose proof (N.pow_nonzero 2 k ltac:(lia)) as Hk0.
  pose proof (N.div_mod (w2n x) (2 ** k) Hk0) as Hd. rewrite Ha, N.add_0_r in Hd.
  assert (w2n x / 2 ** k < 2 ** (dimindex a - k))%N.
  { apply N.Div0.div_lt_upper_bound. lia. }
  nia.
Qed.

Lemma byte_align_good (x : word a) :
  good_dimindex a -> byte_align x = n2w (w2n x / (dimindex a / 8) * (dimindex a / 8)).
Proof.
  intros Hg. unfold byte_align. rewrite align_w2n, (byte_align_pow_good Hg). reflexivity.
Qed.

Lemma dimword_good : good_dimindex a ->
  (dimindex a = 32 /\ dimword a = 4294967296) \/ (dimindex a = 64 /\ dimword a = 18446744073709551616).
Proof. unfold dimword; intros [H|H]; rewrite H; [left|right]; split; reflexivity. Qed.

Lemma dimword_D_good : good_dimindex a ->
  dimindex a / 8 <> 0 /\ exists m, dimword a = (dimindex a / 8 * m)%N.
Proof.
  intros Hg. destruct (dimword_good Hg) as [[Hd Hw]|[Hd Hw]]; rewrite Hd, Hw; split;
    try discriminate.
  - exists 1073741824; reflexivity.
  - exists 2305843009213693952; reflexivity.
Qed.

(** Offsets inside an aligned word (Galette helper). *)
Lemma byte_offset_good (x : word a) k :
  good_dimindex a -> (w2n x mod (dimindex a / 8) + k < dimindex a / 8)%N ->
  byte_align (x + n2w k) = byte_align x /\
  (w2n (x + n2w k) mod (dimindex a / 8) = w2n x mod (dimindex a / 8) + k)%N /\
  w2n (x + n2w k) = (w2n x + k)%N.
Proof.
  intros Hg Hk. pose proof (w2n_lt x) as Hx.
  rewrite !byte_align_good by exact Hg.
  destruct (dimword_D_good Hg) as [HD [m Hm]].
  set (D := dimindex a / 8) in *.
  pose proof (N.div_mod (w2n x) D HD) as Hdm. pose proof (N.mod_lt (w2n x) D HD) as Hr.
  set (q := w2n x / D) in *. set (r := w2n x mod D) in *.
  assert (Hq : (q < m)%N) by nia.
  assert (E : w2n (x + n2w k) = (w2n x + k)%N).
  { unfold word_add. rewrite !w2n_n2w. rewrite (N.mod_small k) by nia. apply N.mod_small. nia. }
  assert (E2 : ((w2n x + k) / D = q)%N).
  { replace (w2n x + k)%N with (r + k + q * D)%N by lia.
    rewrite N.div_add by exact HD. rewrite (N.div_small (r + k)) by lia. lia. }
  assert (E3 : ((w2n x + k) mod D = r + k)%N).
  { replace (w2n x + k)%N with (r + k + q * D)%N by lia.
    rewrite N.Div0.mod_add. apply N.mod_small. lia. }
  rewrite E, E2, E3. split; [reflexivity|split; reflexivity].
Qed.

Lemma good_32 : dimindex a = 32 -> good_dimindex a.
Proof. intros H; left; exact H. Qed.
Lemma good_64 : dimindex a = 64 -> good_dimindex a.
Proof. intros H; right; exact H. Qed.

Lemma byte_align_id_good (x : word a) :
  good_dimindex a -> (w2n x mod (dimindex a / 8) = 0)%N -> byte_align x = x.
Proof.
  intros Hg H. rewrite byte_align_good by exact Hg.
  destruct (dimword_D_good Hg) as [HD _].
  assert (E : (w2n x / (dimindex a / 8) * (dimindex a / 8) = w2n x)%N).
  { pose proof (N.div_mod (w2n x) (dimindex a / 8) HD). lia. }
  rewrite E. apply n2w_w2n.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "aligned_2_imp" *)
Theorem aligned_2_imp : forall x : word a,
  aligned 2 x /\ dimindex a = 32 ->
  byte_align x = x /\
  byte_align (x + n2w 1) = x /\
  byte_align (x + n2w 2) = x /\
  byte_align (x + n2w 3) = x.
Proof.
  intros x [Ha Hd]. apply aligned_w2n in Ha. cbn in Ha.
  pose proof (good_32 Hd) as Hg.
  assert (H0 : (w2n x mod (dimindex a / 8) = 0)%N) by (rewrite Hd; exact Ha).
  pose proof (byte_align_id_good x Hg H0) as E.
  split; [exact E|].
  assert (Hk : forall k, (k < 4)%N -> byte_align (x + n2w k) = x).
  { intros k Hk. rewrite (proj1 (byte_offset_good x k Hg ltac:(rewrite H0, Hd; cbn; lia))).
    exact E. }
  repeat split; apply Hk; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "aligned_2_not_eq" *)
Theorem aligned_2_not_eq : forall (x a0 : word a),
  aligned 2 x /\ dimindex a = 32 /\ x <> byte_align a0 ->
  x <> a0 /\ x + n2w 1 <> a0 /\ x + n2w 2 <> a0 /\ x + n2w 3 <> a0.
Proof.
  intros x a0 (Ha & Hd & Hne). destruct (aligned_2_imp x (conj Ha Hd)) as (E0 & E1 & E2 & E3).
  repeat split; intros <-; apply Hne; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "aligned_3_imp" *)
Theorem aligned_3_imp : forall x : word a,
  aligned 3 x /\ dimindex a = 64 ->
  byte_align x = x /\
  byte_align (x + n2w 1) = x /\
  byte_align (x + n2w 2) = x /\
  byte_align (x + n2w 3) = x /\
  byte_align (x + n2w 4) = x /\
  byte_align (x + n2w 5) = x /\
  byte_align (x + n2w 6) = x /\
  byte_align (x + n2w 7) = x.
Proof.
  intros x [Ha Hd]. apply aligned_w2n in Ha. cbn in Ha.
  pose proof (good_64 Hd) as Hg.
  assert (H0 : (w2n x mod (dimindex a / 8) = 0)%N) by (rewrite Hd; exact Ha).
  pose proof (byte_align_id_good x Hg H0) as E.
  split; [exact E|].
  assert (Hk : forall k, (k < 8)%N -> byte_align (x + n2w k) = x).
  { intros k Hk. rewrite (proj1 (byte_offset_good x k Hg ltac:(rewrite H0, Hd; cbn; lia))).
    exact E. }
  repeat split; apply Hk; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "aligned_3_not_eq" *)
Theorem aligned_3_not_eq : forall (x a0 : word a),
  aligned 3 x /\ dimindex a = 64 /\ x <> byte_align a0 ->
  x <> a0 /\ x + n2w 1 <> a0 /\ x + n2w 2 <> a0 /\ x + n2w 3 <> a0 /\
  x + n2w 4 <> a0 /\ x + n2w 5 <> a0 /\ x + n2w 6 <> a0 /\ x + n2w 7 <> a0.
Proof.
  intros x a0 (Ha & Hd & Hne).
  destruct (aligned_3_imp x (conj Ha Hd)) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7).
  repeat split; intros <-; apply Hne; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "dimword_eq_32_imp_or_bytes" *)
Theorem dimword_eq_32_imp_or_bytes : forall x : word a,
  dimindex a = 32 ->
  (w2w (w2w x : word8) ||
   w2w (w2w (x >>> 8) : word8) << 8 ||
   w2w (w2w (x >>> 16) : word8) << 16 ||
   w2w (w2w (x >>> 24) : word8) << 24) = x.
Proof.
  intros x Hd. apply word_testbit_eq. intros i Hi.
  rewrite ?testbit_or, ?testbit_lsl, ?testbit_w2w, ?testbit_lsr, ?dimindex_8. rewrite Hd in *.
  rewrite (testbit_w2n x i). rewrite Hd.
  assert (i < 8 \/ (8 <= i < 16) \/ (16 <= i < 24) \/ (24 <= i < 32))%N as R by lia.
  destruct R as [R|[R|[R|R]]]; bit_solve.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "dimword_eq_64_imp_or_bytes" *)
Theorem dimword_eq_64_imp_or_bytes : forall x : word a,
  dimindex a = 64 ->
  (w2w (w2w x : word8) ||
   w2w (w2w (x >>> 8) : word8) << 8 ||
   w2w (w2w (x >>> 16) : word8) << 16 ||
   w2w (w2w (x >>> 24) : word8) << 24 ||
   w2w (w2w (x >>> 32) : word8) << 32 ||
   w2w (w2w (x >>> 40) : word8) << 40 ||
   w2w (w2w (x >>> 48) : word8) << 48 ||
   w2w (w2w (x >>> 56) : word8) << 56) = x.
Proof.
  intros x Hd. apply word_testbit_eq. intros i Hi.
  rewrite ?testbit_or, ?testbit_lsl, ?testbit_w2w, ?testbit_lsr, ?dimindex_8. rewrite Hd in *.
  rewrite (testbit_w2n x i). rewrite Hd.
  assert (i < 8 \/ (8 <= i < 16) \/ (16 <= i < 24) \/ (24 <= i < 32) \/ (32 <= i < 40) \/
          (40 <= i < 48) \/ (48 <= i < 56) \/ (56 <= i < 64))%N as R by lia.
  destruct R as [R|[R|[R|[R|[R|[R|[R|R]]]]]]]; bit_solve.
Qed.

Lemma byte_align_eq_good (x : word a) :
  good_dimindex a -> byte_align x + n2w (w2n x mod (dimindex a / 8)) = x.
Proof.
  intros Hg. rewrite byte_align_good by exact Hg. rewrite word_add_n2w.
  destruct (dimword_D_good Hg) as [HD _].
  rewrite N.mul_comm, <- (N.div_mod (w2n x) _ HD). apply n2w_w2n.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "byte_align_32_eq" *)
Theorem byte_align_32_eq : forall a0 : word a,
  dimindex a = 32 -> byte_align a0 + n2w (w2n a0 mod 4) = a0.
Proof. intros a0 Hd. pose proof (byte_align_eq_good a0 (good_32 Hd)) as H. rewrite Hd in H. exact H. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "byte_align_64_eq" *)
Theorem byte_align_64_eq : forall a0 : word a,
  dimindex a = 64 -> byte_align a0 + n2w (w2n a0 mod 8) = a0.
Proof. intros a0 Hd. pose proof (byte_align_eq_good a0 (good_64 Hd)) as H. rewrite Hd in H. exact H. Qed.

Lemma byte_align_plus_eq (a0 : word a) k D :
  byte_align a0 + n2w (w2n a0 mod D) = a0 -> byte_align a0 + n2w k = a0 ->
  (k < D)%N -> (D < dimword a)%N -> w2n a0 mod D = k.
Proof.
  intros E0 E2 Hk HD.
  assert (E3 : byte_align a0 + n2w (w2n a0 mod D) = byte_align a0 + n2w k) by congruence.
  clear E2 E0. rename E3 into E1'. apply WORD_EQ_ADD_LCANCEL in E1'. rename E1' into E1.
  apply n2w_11 in E1. destruct (N.eq_dec D 0) as [->|HD0]; [lia|].
  pose proof (N.mod_lt (w2n a0) D HD0).
  rewrite (N.mod_small k), (N.mod_small (w2n a0 mod D)) in E1 by lia. exact E1.
Qed.

Lemma dimword_gt_8 : good_dimindex a -> (8 < dimword a)%N.
Proof. intros Hg; destruct (dimword_good Hg) as [[_ H]|[_ H]]; rewrite H; lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "byte_align_32_IMP" *)
Theorem byte_align_32_IMP : forall a0 : word a,
  dimindex a = 32 ->
  (byte_align a0 = a0 -> (w2n a0 mod 4 = 0)%N) /\
  (byte_align a0 + n2w 1 = a0 -> (w2n a0 mod 4 = 1)%N) /\
  (byte_align a0 + n2w 2 = a0 -> (w2n a0 mod 4 = 2)%N) /\
  (byte_align a0 + n2w 3 = a0 -> (w2n a0 mod 4 = 3)%N).
Proof.
  intros a0 Hd. pose proof (byte_align_32_eq a0 Hd) as E.
  pose proof (dimword_gt_8 (good_32 Hd)) as Hdw.
  repeat split; intros Hx; apply (byte_align_plus_eq a0 _ 4 E); try lia;
  rewrite ?(proj1 WORD_ADD_0); exact Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "MOD4_CASES" *)
Theorem MOD4_CASES : forall n, (n mod 4 = 0 \/ n mod 4 = 1 \/ n mod 4 = 2 \/ n mod 4 = 3)%N.
Proof. intros n. pose proof (N.mod_lt n 4 ltac:(discriminate)). lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "byte_align_32_CASES" *)
Theorem byte_align_32_CASES : forall a0 : word a,
  dimindex a = 32 ->
  byte_align a0 + n2w 3 = a0 \/
  byte_align a0 + n2w 2 = a0 \/
  byte_align a0 + n2w 1 = a0 \/
  byte_align a0 = a0.
Proof.
  intros a0 Hd. pose proof (byte_align_32_eq a0 Hd) as E.
  destruct (MOD4_CASES (w2n a0)) as [H|[H|[H|H]]]; rewrite H in E;
    [right; right; right; rewrite (proj1 WORD_ADD_0) in E|right; right; left|right; left|left];
    exact E.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "MOD8_CASES" *)
Theorem MOD8_CASES : forall n,
  (n mod 8 = 0 \/ n mod 8 = 1 \/ n mod 8 = 2 \/ n mod 8 = 3 \/
   n mod 8 = 4 \/ n mod 8 = 5 \/ n mod 8 = 6 \/ n mod 8 = 7)%N.
Proof. intros n. pose proof (N.mod_lt n 8 ltac:(discriminate)). lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "byte_align_64_CASES" *)
Theorem byte_align_64_CASES : forall a0 : word a,
  dimindex a = 64 ->
  byte_align a0 + n2w 7 = a0 \/
  byte_align a0 + n2w 6 = a0 \/
  byte_align a0 + n2w 5 = a0 \/
  byte_align a0 + n2w 4 = a0 \/
  byte_align a0 + n2w 3 = a0 \/
  byte_align a0 + n2w 2 = a0 \/
  byte_align a0 + n2w 1 = a0 \/
  byte_align a0 = a0.
Proof.
  intros a0 Hd. pose proof (byte_align_64_eq a0 Hd) as E.
  destruct (MOD8_CASES (w2n a0)) as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; rewrite H in E;
    [do 7 right; rewrite (proj1 WORD_ADD_0) in E|do 6 right; left|do 5 right; left
    |do 4 right; left|do 3 right; left|do 2 right; left|right; left|left]; exact E.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "byte_align_64_IMP" *)
Theorem byte_align_64_IMP : forall a0 : word a,
  dimindex a = 64 ->
  (byte_align a0 + n2w 7 = a0 -> (w2n a0 mod 8 = 7)%N) /\
  (byte_align a0 + n2w 6 = a0 -> (w2n a0 mod 8 = 6)%N) /\
  (byte_align a0 + n2w 5 = a0 -> (w2n a0 mod 8 = 5)%N) /\
  (byte_align a0 + n2w 4 = a0 -> (w2n a0 mod 8 = 4)%N) /\
  (byte_align a0 + n2w 3 = a0 -> (w2n a0 mod 8 = 3)%N) /\
  (byte_align a0 + n2w 2 = a0 -> (w2n a0 mod 8 = 2)%N) /\
  (byte_align a0 + n2w 1 = a0 -> (w2n a0 mod 8 = 1)%N) /\
  (byte_align a0 = a0 -> (w2n a0 mod 8 = 0)%N).
Proof.
  intros a0 Hd. pose proof (byte_align_64_eq a0 Hd) as E.
  pose proof (dimword_gt_8 (good_64 Hd)) as Hdw.
  repeat split; intros Hx; apply (byte_align_plus_eq a0 _ 8 E); try lia;
    rewrite ?(proj1 WORD_ADD_0); exact Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "align2_not_align3_4w" *)
Theorem align2_not_align3_4w : forall x : word a,
  ~ aligned 3 x /\ aligned 2 x /\ dimindex a = 64 ->
  x = byte_align x + n2w 4 /\
  x + n2w 1 = byte_align x + n2w 5 /\
  x + n2w 2 = byte_align x + n2w 6 /\
  x + n2w 3 = byte_align x + n2w 7.
Proof.
  intros x (H3 & H2 & Hd). rewrite aligned_w2n in H2, H3. cbn in H2, H3.
  assert (H4 : (w2n x mod 8 = 4)%N) by lia.
  pose proof (byte_align_64_eq x Hd) as E. rewrite H4 in E.
  rewrite <- E at 1 3 5 7. repeat split; word_arith.
Qed.

End Alignment.

Lemma regs_rel_word {a : N} {c Ffi : Type} p labs (s1 : labSem.state a c Ffi) (t1 : asm_state a) r w :
  (forall r, word_loc_val p labs (regs s1 r) = SOME (asmSem.regs t1 r)) ->
  regs s1 r = Word w -> asmSem.regs t1 r = w.
Proof. intros H E. specialize (H r). rewrite E in H. cbn in H. congruence. Qed.

Ltac regs_known H :=
  unfold asmSem.read_reg, asmSem.reg_imm;
  repeat match goal with
         | E : regs ?s ?r = Word ?w |- context [asmSem.regs ?t ?r] =>
             let Ht := fresh "Ht" in
             pose proof (regs_rel_word _ _ _ _ _ _ H E) as Ht; rewrite Ht; clear Ht
         end.

Ltac upd_regs_tac H :=
  intros rx; cbn [labSem.upd_reg labSem.set_regs asmSem.upd_reg asmSem.set_regs labSem.regs
                  asmSem.regs labSem.assert labSem.set_failed asmSem.assert asmSem.set_failed];
  rewrite ?APPLY_UPDATE_THM;
  repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)); subst end;
  try (cbn [word_loc_val]; reflexivity); try apply H.


Section ArithFp.
Context {a : N} {c Ffi : Type}.
Implicit Types (t : asm_state a).



(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "arith_upd_lemma" *)
Theorem arith_upd_lemma : forall p labs (s1 : labSem.state a c Ffi) t1 (a0 : arith a),
  (forall r, word_loc_val p labs (regs s1 r) = SOME (asmSem.regs t1 r)) /\
  ~ (labSem.arith_upd a0 s1).(failed) ->
  forall r, word_loc_val p labs (regs (labSem.arith_upd a0 s1) r) =
            SOME (asmSem.regs (asmSem.arith_upd a0 t1) r).
Proof.
  intros p labs s1 t1 a0 [H Hf]. revert Hf.
  destruct a0 as [b r1 r2 ri|l r1 r2 ri|r1 r2 r3|r1 r2 r3 r4|r1 r2 r3 r4 r5|r1 r2 r3 r4
                 |r1 r2 r3 r4|r1 r2 r3 r4];
    cbn [labSem.arith_upd asmSem.arith_upd]; unfold asmSem.read_reg, asmSem.reg_imm.
  - destruct (regs s1 r2) as [w1|n1 n2] eqn:E2;
      [destruct ri as [rr|ww]; cbn [labSem.reg_imm];
       [destruct (regs s1 rr) as [w2|m1 m2] eqn:E3|]|].
    + intros _. regs_known H. destruct b; cbn [labSem.binop_upd asmSem.binop_upd]; upd_regs_tac H.
    + destruct (bool_decide (b = asm.Or) && bool_decide (Reg rr = Reg r2)) eqn:Eb;
        [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
      apply Bool.andb_true_iff in Eb as [Eb1 Eb2]. apply bool_decide_spec in Eb1, Eb2.
      injection Eb2 as ->. congruence.
    + intros _. regs_known H. destruct b; cbn [labSem.binop_upd asmSem.binop_upd]; upd_regs_tac H.
    + destruct (bool_decide (b = asm.Or) && bool_decide (ri = Reg r2)) eqn:Eb;
        [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
      intros _.
      apply Bool.andb_true_iff in Eb as [Eb1 Eb2]. apply bool_decide_spec in Eb1, Eb2. subst.
      cbn [asmSem.binop_upd]. rewrite WORD_OR_IDEM.
      intros rx; cbn [labSem.upd_reg labSem.set_regs asmSem.upd_reg asmSem.set_regs labSem.regs
                     asmSem.regs]. rewrite !APPLY_UPDATE_THM.
      destruct (decide (r1 = rx)); [subst; rewrite <- E2; apply H|apply H].
  - destruct (regs s1 r2) as [w1|n1 n2] eqn:E2; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    destruct ri as [rr|ww]; cbn [labSem.reg_imm];
      [destruct (regs s1 rr) as [w2|m1 m2] eqn:E3; [|cbn; intros Hf; exfalso; apply Hf; reflexivity]|];
      intros _; regs_known H; upd_regs_tac H.
  - destruct (regs s1 r3) as [w3|n1 n2] eqn:E3; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    destruct (regs s1 r2) as [w2|m1 m2] eqn:E2; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    intros _; regs_known H; upd_regs_tac H.
  - destruct (regs s1 r3) as [w3|n1 n2] eqn:E3; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    destruct (regs s1 r4) as [w4|m1 m2] eqn:E4; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    intros _; regs_known H; upd_regs_tac H.
  - destruct (regs s1 r3) as [w3|n1 n2] eqn:E3; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    destruct (regs s1 r4) as [w4|m1 m2] eqn:E4; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    destruct (regs s1 r5) as [w5|k1 k2] eqn:E5; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    intros _; regs_known H; upd_regs_tac H.
  - destruct (regs s1 r2) as [w2|n1 n2] eqn:E2; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    destruct (regs s1 r3) as [w3|m1 m2] eqn:E3; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    destruct (regs s1 r4) as [w4|k1 k2] eqn:E4; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    intros _; regs_known H; upd_regs_tac H.
  - destruct (regs s1 r2) as [w2|n1 n2] eqn:E2; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    destruct (regs s1 r3) as [w3|m1 m2] eqn:E3; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    intros _; regs_known H; upd_regs_tac H.
  - destruct (regs s1 r2) as [w2|n1 n2] eqn:E2; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    destruct (regs s1 r3) as [w3|m1 m2] eqn:E3; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    intros _; regs_known H; upd_regs_tac H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "arith_upd_fp_regs" *)
Theorem arith_upd_fp_regs : forall (a0 : arith a) (s : labSem.state a c Ffi) t,
  fp_regs (labSem.arith_upd a0 s) = fp_regs s /\
  asmSem.fp_regs (asmSem.arith_upd a0 t) = asmSem.fp_regs t.
Proof.
  intros a0 s t. split.
  - destruct a0 as [b r1 r2 ri|l r1 r2 ri|r1 r2 r3|r1 r2 r3 r4|r1 r2 r3 r4 r5|r1 r2 r3 r4
                   |r1 r2 r3 r4|r1 r2 r3 r4]; cbn [labSem.arith_upd];
      repeat match goal with |- context [match ?x with _ => _ end] => destruct x end;
      try destruct b; reflexivity.
  - destruct a0 as [b r1 r2 ri|l r1 r2 ri|r1 r2 r3|r1 r2 r3 r4|r1 r2 r3 r4 r5|r1 r2 r3 r4
                   |r1 r2 r3 r4|r1 r2 r3 r4]; cbn [asmSem.arith_upd]; try destruct b; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "fp_upd_lemma" *)
Theorem fp_upd_lemma : forall p labs (s1 : labSem.state a c Ffi) t1 (f : fp),
  (forall r, word_loc_val p labs (regs s1 r) = SOME (asmSem.regs t1 r)) /\
  (forall r, fp_regs s1 r = asmSem.fp_regs t1 r) /\
  ~ (labSem.fp_upd f s1).(failed) ->
  (forall r, fp_regs (labSem.fp_upd f s1) r = asmSem.fp_regs (asmSem.fp_upd f t1) r) /\
  (forall r, word_loc_val p labs (regs (labSem.fp_upd f s1) r) =
             SOME (asmSem.regs (asmSem.fp_upd f t1) r)).
Proof.
  intros p labs s1 t1 f (H & Hfp & Hf). revert Hf.
  destruct f; cbn [labSem.fp_upd asmSem.fp_upd];
    unfold labSem.read_fp_reg, asmSem.read_fp_reg, asmSem.read_reg in *; rewrite ?Hfp;
    cbn [labSem.upd_reg labSem.set_regs asmSem.upd_reg asmSem.set_regs labSem.regs asmSem.regs
         labSem.upd_fp_reg labSem.set_fp_regs asmSem.upd_fp_reg asmSem.set_fp_regs
         labSem.fp_regs asmSem.fp_regs].
  all: try (intros _; split; intros rx; rewrite ?APPLY_UPDATE_THM;
            repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)); subst end;
            try reflexivity; try apply Hfp; try apply H; fail).
  all: try (destruct (dimindex a =? 64);
            [|cbn [labSem.upd_reg labSem.set_regs labSem.regs]];
            intros _; split; intros rx; rewrite ?APPLY_UPDATE_THM;
            repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)); subst end;
            try reflexivity; try apply Hfp; try apply H; fail).
  - destruct (dimindex a =? 64); intros _;
      cbn [labSem.upd_reg labSem.set_regs asmSem.upd_reg asmSem.set_regs labSem.regs asmSem.regs
           labSem.fp_regs asmSem.fp_regs];
      split; intros rx; rewrite ?APPLY_UPDATE_THM;
      repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)); subst end;
      try reflexivity; try apply Hfp; try apply H.
  - destruct (dimindex a =? 64).
    + destruct (regs s1 n0) as [w1|] eqn:E2; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
      intros _. regs_known H.
      cbn [labSem.upd_fp_reg labSem.set_fp_regs labSem.fp_regs labSem.regs].
      split; intros rx; rewrite ?APPLY_UPDATE_THM;
        repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)); subst end;
        try reflexivity; try apply Hfp; try apply H.
    + destruct (regs s1 n0) as [w1|] eqn:E2; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
      destruct (regs s1 n1) as [w2|] eqn:E3; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
      intros _. regs_known H.
      cbn [labSem.upd_fp_reg labSem.set_fp_regs labSem.fp_regs labSem.regs].
      split; intros rx; rewrite ?APPLY_UPDATE_THM;
        repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)); subst end;
        try reflexivity; try apply Hfp; try apply H.
  - destruct (machine_ieee.fp64_to_int _ _) as [i|];
      [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    destruct (dimindex a =? 64); [|destruct (ODD n)]; intros _;
      cbn [labSem.upd_fp_reg labSem.set_fp_regs labSem.fp_regs labSem.regs labSem.assert
           labSem.set_failed asmSem.upd_fp_reg asmSem.set_fp_regs asmSem.fp_regs asmSem.regs
           asmSem.assert asmSem.set_failed];
      split; intros rx; rewrite ?APPLY_UPDATE_THM;
      repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)); subst end;
      rewrite ?Hfp; try reflexivity; try apply Hfp; try apply H.
Qed.

End ArithFp.

Section ShareHelpers.
Context {a : N} {B C Ffi : Type}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "Inst_share_mem_pc_update_helper" *)
Theorem Inst_share_mem_pc_update_helper : forall (mc_conf : machine_config a B C)
    (s1 : labSem.state a config Ffi) (t1 : asm_state a) (ms1 ms2 : B) pc',
  share_mem_state_rel mc_conf s1 t1 ms1 /\
  target_state_rel mc_conf.(target) (asmSem.set_pc pc' t1) ms2 ->
  share_mem_state_rel mc_conf (set_clock (clock s1 - 1) (set_pc (pc s1 + 1) s1))
    (asmSem.set_pc pc' t1) ms2.
Proof. intros mc_conf s1 t1 ms1 ms2 pc' [H _]. exact H. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "Inst_share_mem_reg_update_helper" *)
Theorem Inst_share_mem_reg_update_helper : forall (mc_conf : machine_config a B C)
    (s1 : labSem.state a config Ffi) (t1 : asm_state a) (ms1 ms2 : B) pc' n c,
  share_mem_state_rel mc_conf s1 t1 ms1 /\
  target_state_rel mc_conf.(target)
    (asmSem.set_pc pc' (asmSem.set_regs ((n =+ c) (asmSem.regs t1)) t1)) ms2 ->
  share_mem_state_rel mc_conf
    (set_clock (clock s1 - 1) (set_pc (pc s1 + 1) (set_regs ((n =+ Word c) (regs s1)) s1)))
    (asmSem.set_pc pc' (asmSem.set_regs ((n =+ c) (asmSem.regs t1)) t1)) ms2.
Proof. intros mc_conf s1 t1 ms1 ms2 pc' n c [H _]. exact H. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "arith_upd_share_mem_domain_unchange" *)
Theorem arith_upd_share_mem_domain_unchange : forall {cc} (a0 : arith a) (s1 : labSem.state a cc Ffi),
  shared_mem_domain (labSem.arith_upd a0 s1) = shared_mem_domain s1.
Proof. intros cc a0 s1. apply (arith_upd_consts a0 s1). Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "fp_upd_share_mem_domain_unchange" *)
Theorem fp_upd_share_mem_domain_unchange : forall {cc} (f : fp) (s1 : labSem.state a cc Ffi),
  shared_mem_domain (labSem.fp_upd f s1) = shared_mem_domain s1.
Proof. intros cc f s1. apply (fp_upd_consts f s1). Qed.

End ShareHelpers.

(** ** The fields of [state_rel] untouched by a single instruction *)

Section InstStep.
Context {a : N} {B C Ffi : Type}.

(** The remaining constant fields of labSem's [asm_inst] (Galette helper). *)
Lemma asm_inst_consts2 {cc} (i : asm.inst a) (s : labSem.state a cc Ffi) :
  mem_domain (asm_inst i s) = mem_domain s /\
  shared_mem_domain (asm_inst i s) = shared_mem_domain s /\
  be (asm_inst i s) = be s /\
  compile (asm_inst i s) = compile s /\
  compile_oracle (asm_inst i s) = compile_oracle s /\
  code_buffer (asm_inst i s) = code_buffer s.
Proof.
  destruct i as [| |y|m r y|y]; cbn [asm_inst].
  - repeat split.
  - repeat split.
  - destruct (arith_upd_consts y s) as (H1 & H2 & _ & _ & _ & _ & _ & _ & H3 & _ & _ & _ & _ & _
      & H4 & H5 & H6 & _). repeat split; assumption.
  - destruct m; cbn [mem_op]; unfold mem_load, mem_store, mem_load32, mem_store32,
      mem_load_byte, mem_store_byte, labSem.assert, labSem.upd_reg, labSem.upd_mem;
      repeat match goal with |- context [match ?x with _ => _ end] => destruct x end;
      repeat split.
  - destruct (fp_upd_consts y s) as (H1 & H2 & _ & _ & _ & _ & _ & _ & _ & _ & H3 & H4 & H5
      & H6 & _). repeat split; assumption.
Qed.

Lemma inst_consts (i : asm.inst a) (t : asm_state a) :
  asmSem.be (inst i t) = asmSem.be t /\ asmSem.lr (inst i t) = asmSem.lr t /\
  asmSem.align (inst i t) = asmSem.align t /\
  asmSem.mem_domain (inst i t) = asmSem.mem_domain t.
Proof. exact (asm_consts (Inst i) (n2w 0) t). Qed.

Lemma state_rel_inst_step (mc : machine_config a B C) code2 labs p
    (s1 s1' : labSem.state a config Ffi) (t1 t1' : asm_state a) (ms1 ms2 : B) :
  state_rel (mc, (code2, (labs, p))) s1 t1 ms1 ->
  target_state_rel mc.(target) t1' ms2 ->
  mem_domain s1' = mem_domain s1 -> shared_mem_domain s1' = shared_mem_domain s1 ->
  be s1' = be s1 -> ffi s1' = ffi s1 -> code s1' = code s1 -> compile s1' = compile s1 ->
  compile_oracle s1' = compile_oracle s1 -> code_buffer s1' = code_buffer s1 ->
  ptr_reg s1' = ptr_reg s1 -> len_reg s1' = len_reg s1 -> ptr2_reg s1' = ptr2_reg s1 ->
  len2_reg s1' = len2_reg s1 -> link_reg s1' = link_reg s1 -> ~ failed s1' ->
  asmSem.mem_domain t1' = asmSem.mem_domain t1 -> asmSem.be t1' = asmSem.be t1 ->
  asmSem.align t1' = asmSem.align t1 -> asmSem.lr t1' = asmSem.lr t1 ->
  ~ asmSem.failed t1' ->
  (forall a0, a0 NOTIN mem_domain s1 -> asmSem.mem t1' a0 = asmSem.mem t1 a0) ->
  asmSem.pc t1' = (p + n2w (pos_val (pc s1') 0 code2))%w ->
  (forall r, fp_regs s1' r = asmSem.fp_regs t1' r) ->
  (forall r, word_loc_val p labs (regs s1' r) = SOME (asmSem.regs t1' r)) ->
  (forall a0, byte_align a0 IN mem_domain s1 ->
     word_loc_val_byte p labs (mem s1') a0 (be s1) = SOME (asmSem.mem t1' a0)) ->
  state_rel (mc, (code2, (labs, p))) s1' t1' ms2.
Proof.
  intros H Htr Edm Esdm Ebe Effi Ecode Ecomp Eorc Ecb Eptr Elen Eptr2 Elen2 Elink Hf1
    Etdm Etbe Etal Etlr Hft Hmem Hpc Hfp Hregs Hm.
  apply state_rel_iff in H. apply state_rel_iff.
  assert (Hshare : share_mem_state_rel mc s1' t1' ms2).
  { pose proof (sr_share_mem_state_rel H) as X. unfold share_mem_state_rel in *.
    rewrite Effi. exact X. }
  destruct H.
  constructor; rewrite ?Edm, ?Esdm, ?Ebe, ?Effi, ?Ecode, ?Ecomp, ?Eorc, ?Ecb, ?Eptr, ?Elen,
    ?Eptr2, ?Elen2, ?Elink, ?Etdm, ?Etbe, ?Etal, ?Etlr; try assumption.
  - intros a0 Ha. destruct (ltac:(match goal with X : forall a0, byte_align a0 IN mem_domain s1 -> _ /\ _ |- _ => exact (X a0 Ha) end)) as (H1 & H2 & _).
    split; [exact H1|]. split; [exact H2|]. apply Hm, Ha.
  - apply (bytes_in_mem_asm_write_bytearray_lemma _ _ (asmSem.mem t1)); [|eassumption].
    intros a0 Ha. symmetry. apply Hmem, Ha.
  - apply (bytes_in_mem_asm_write_bytearray_lemma _ _ (asmSem.mem t1)); [|eassumption].
    intros a0 Ha. symmetry. apply Hmem, Ha.
Qed.

End InstStep.

(** ** Reading and writing words byte by byte (Galette helpers) *)

Section MemWord.
Context {a : N}.

Definition offs (be : bool) (ad : word a) (k : N) : word a :=
  if be then (ad - n2w k)%w else (ad + n2w k)%w.

Lemma offs_succ be (ad : word a) k :
  offs be (if be then (ad - n2w 1)%w else (ad + n2w 1)%w) k = offs be ad (k + 1).
Proof. unfold offs; destruct be; word_arith. Qed.

Lemma offs_0 be (ad : word a) : offs be ad 0 = ad.
Proof. unfold offs; destruct be; word_arith. Qed.

Lemma read_mem_word_snd : forall n (ad : word a) (t : asm_state a),
  (forall k, (k < n)%N -> offs (asmSem.be t) ad k IN asmSem.mem_domain t) ->
  snd (read_mem_word ad n t) = t.
Proof.
  intros n; induction n as [|n IH] using N.peano_ind; intros ad t Hd; [reflexivity|].
  rewrite (proj2 (read_mem_word_def ad n t)).
  rewrite surjective_pairing with (p := read_mem_word _ n t). cbn [snd].
  rewrite IH.
  - unfold asmSem.assert. destruct (classical_dec (ad IN asmSem.mem_domain t)) as [_|Hn].
    + destruct t; reflexivity.
    + exfalso. apply Hn. rewrite <- (offs_0 (asmSem.be t) ad). apply Hd. lia.
  - intros k Hk. rewrite offs_succ. apply Hd. lia.
Qed.

Lemma read_mem_word_bits : forall n (ad : word a) (t : asm_state a) i,
  N.testbit (w2n (fst (read_mem_word ad n t))) i =
  (i <? dimindex a)%N && (i <? 8 * n)%N &&
  N.testbit (w2n (asmSem.mem t (offs (asmSem.be t) ad (i / 8)))) (i mod 8).
Proof.
  intros n; induction n as [|n IH] using N.peano_ind; intros ad t i.
  - cbn [read_mem_word num_rec fst]. unfold read_mem_word; rewrite num_rec_0. cbn [fst].
    rewrite w2n_n2w, N.Div0.mod_0_l, N.bits_0.
    destruct (i <? dimindex a)%N; [|reflexivity]. replace (i <? 8 * 0)%N with false; [reflexivity|].
    symmetry; apply N.ltb_ge; lia.
  - rewrite (proj2 (read_mem_word_def ad n t)).
    destruct (read_mem_word _ n t) as [w s1] eqn:E. cbn [fst].
    pose proof (read_mem_word_IMP_mem_eq _ _ _ _ _ E) as Em.
    pose proof (IH (if asmSem.be t then (ad - n2w 1)%w else (ad + n2w 1)%w) t (i - 8)%N) as IHi.
    rewrite E in IHi. cbn [fst] in IHi.
    rewrite testbit_or, testbit_lsl, testbit_w2w. unfold asmSem.read_mem. rewrite Em.
    destruct (N.ltb_spec i 8) as [Hi8|Hi8].
    + replace (8 <=? i)%N with false by (symmetry; apply N.leb_gt; lia). cbn [andb orb].
      rewrite (N.div_small i 8) by lia. rewrite (N.mod_small i 8) by lia. rewrite offs_0.
      destruct (i <? dimindex a)%N; [|reflexivity].
      replace (i <? 8 * N.succ n)%N with true by (symmetry; apply N.ltb_lt; lia). reflexivity.
    + rewrite (proj2 (N.leb_le 8 i)) by lia.
      rewrite (testbit_word8_high _ i) by lia. rewrite Bool.andb_false_r, Bool.orb_false_r, Bool.andb_true_r.
      rewrite IHi, offs_succ.
      replace ((i - 8) / 8 + 1)%N with (i / 8)%N by lia.
      replace ((i - 8) mod 8)%N with (i mod 8)%N by lia.
      destruct (N.ltb_spec i (dimindex a)); [|reflexivity].
      replace (i - 8 <? dimindex a)%N with true by (symmetry; apply N.ltb_lt; lia).
      cbn [andb]. f_equal. apply Bool.eq_iff_eq_true. rewrite !N.ltb_lt. lia.
Qed.

(** [write_mem_word] (Galette helpers). *)
Lemma write_mem_word_other : forall n (ad w : word a) (t : asm_state a),
  (asmSem.mem_domain (write_mem_word ad n w t) = asmSem.mem_domain t) /\
  (asmSem.be (write_mem_word ad n w t) = asmSem.be t).
Proof.
  intros n ad w t. destruct (write_mem_word_consts n ad w t) as (H1 & _ & _ & H2). auto.
Qed.

Lemma write_mem_word_failed : forall n (ad w : word a) (t : asm_state a),
  (forall k, (k < n)%N -> offs (asmSem.be t) ad k IN asmSem.mem_domain t) ->
  asmSem.failed (write_mem_word ad n w t) = asmSem.failed t.
Proof.
  intros n; induction n as [|n IH] using N.peano_ind; intros ad w t Hd; [reflexivity|].
  rewrite (proj2 (write_mem_word_def ad n w t)). cbv zeta.
  unfold asmSem.assert, asmSem.upd_mem. cbn [asmSem.set_failed asmSem.set_mem asmSem.failed].
  rewrite (proj1 (write_mem_word_other _ _ _ _)).
  destruct (classical_dec (ad IN asmSem.mem_domain t)) as [_|Hn].
  - cbn [negb orb]. apply IH. intros k Hk. rewrite offs_succ. apply Hd. lia.
  - exfalso. apply Hn. rewrite <- (offs_0 (asmSem.be t) ad). apply Hd. lia.
Qed.

Lemma offs_inj be (ad : word a) j k :
  (j < dimword a)%N -> (k < dimword a)%N -> offs be ad j = offs be ad k -> j = k.
Proof.
  intros Hj Hk E. unfold offs in E.
  assert (E' : (n2w j : word a) = n2w k).
  { destruct be.
    - apply (f_equal (fun x => (ad - x)%w)) in E.
      replace (ad - (ad - n2w j))%w with (n2w j : word a) in E by word_arith.
      replace (ad - (ad - n2w k))%w with (n2w k : word a) in E by word_arith. exact E.
    - apply WORD_EQ_ADD_LCANCEL in E. exact E. }
  apply n2w_11 in E'. rewrite !N.mod_small in E' by lia. exact E'.
Qed.

Lemma lsr_0 (w : word a) : (w >>> 0)%w = w.
Proof.
  apply word_testbit_eq. intros i Hi. rewrite testbit_lsr, N.add_0_r. reflexivity.
Qed.

Lemma write_mem_word_mem_in : forall n (ad w : word a) (t : asm_state a) j,
  (n <= dimword a)%N -> (j < n)%N ->
  asmSem.mem (write_mem_word ad n w t) (offs (asmSem.be t) ad j) = w2w (w >>> (8 * j))%w.
Proof.
  intros n; induction n as [|n IH] using N.peano_ind; intros ad w t j Hn Hj; [lia|].
  rewrite (proj2 (write_mem_word_def ad n w t)). cbv zeta.
  unfold asmSem.assert, asmSem.upd_mem. cbn [asmSem.set_failed asmSem.set_mem asmSem.mem].
  rewrite APPLY_UPDATE_THM. destruct (decide (ad = offs (asmSem.be t) ad j)) as [E|Ne].
  - rewrite <- (offs_0 (asmSem.be t) ad) in E at 1.
    apply offs_inj in E; [|lia|lia]. subst j. rewrite N.mul_0_r, lsr_0. reflexivity.
  - destruct (N.eq_dec j 0) as [->|Hj0]; [rewrite offs_0 in Ne; congruence|].
    replace j with ((j - 1) + 1)%N by lia. rewrite <- offs_succ.
    rewrite IH by lia. rewrite LSR_ADD. do 2 f_equal. lia.
Qed.

Lemma write_mem_word_mem_out : forall n (ad w : word a) (t : asm_state a) y,
  (forall j, (j < n)%N -> y <> offs (asmSem.be t) ad j) ->
  asmSem.mem (write_mem_word ad n w t) y = asmSem.mem t y.
Proof.
  intros n; induction n as [|n IH] using N.peano_ind; intros ad w t y Hy; [reflexivity|].
  rewrite (proj2 (write_mem_word_def ad n w t)). cbv zeta.
  unfold asmSem.assert, asmSem.upd_mem. cbn [asmSem.set_failed asmSem.set_mem asmSem.mem].
  rewrite APPLY_UPDATE_THM. destruct (decide (ad = y)) as [E|Ne].
  - exfalso. apply (Hy 0); [lia|]. rewrite offs_0. symmetry. exact E.
  - apply IH. intros j Hj. rewrite offs_succ. apply Hy. lia.
Qed.

End MemWord.


(** ** Simulating one instruction (Galette helpers for [Inst_lemma]) *)

Section InstSim.
Context {a : N} {B C Ffi : Type}.

Definition inst_sim p labs (s1 : labSem.state a config Ffi) (t1 : asm_state a)
    (i : asm.inst a) : Prop :=
  ~ asmSem.failed (inst i t1) /\
  (forall a0, a0 NOTIN mem_domain s1 -> asmSem.mem (inst i t1) a0 = asmSem.mem t1 a0) /\
  (forall r, fp_regs (asm_inst i s1) r = asmSem.fp_regs (inst i t1) r) /\
  (forall r, word_loc_val p labs (regs (asm_inst i s1) r) = SOME (asmSem.regs (inst i t1) r)) /\
  (forall a0, byte_align a0 IN mem_domain s1 ->
     word_loc_val_byte p labs (mem (asm_inst i s1)) a0 (be s1) = SOME (asmSem.mem (inst i t1) a0)).

Lemma sr_mem_word (mc : machine_config a B C) code2 labs p (s1 : labSem.state a config Ffi) (t1 : asm_state a) (ms1 : B) x :
  state_rel_r mc code2 labs p s1 t1 ms1 ->
  byte_align x IN mem_domain s1 ->
  x IN asmSem.mem_domain t1 /\ x IN mem_domain s1 /\
  exists v, word_loc_val p labs (mem s1 (byte_align x)) = SOME v /\
            asmSem.mem t1 x = byte.get_byte x v (be s1).
Proof.
  intros R Hx. destruct (sr_mem R x Hx) as (H1 & H2 & H3). split; [exact H1|split; [exact H2|]].
  unfold word_loc_val_byte in H3. destruct (word_loc_val p labs (mem s1 (byte_align x))) as [v|];
    [|discriminate]. exists v. split; [reflexivity|]. injection H3 as H3. symmetry; exact H3.
Qed.

Lemma inst_sim_Skip (mc : machine_config a B C) code2 labs p (s1 : labSem.state a config Ffi) (t1 : asm_state a) (ms1 : B) :
  state_rel_r mc code2 labs p s1 t1 ms1 -> inst_sim p labs s1 t1 asm.Skip.
Proof.
  intros R. split; [exact (sr_t1_failed R)|]. split; [reflexivity|].
  split; [exact (sr_fp_regs R)|]. split; [exact (sr_regs R)|].
  intros a0 Ha. exact (proj2 (proj2 (sr_mem R a0 Ha))).
Qed.

Lemma inst_sim_Const (mc : machine_config a B C) code2 labs p (s1 : labSem.state a config Ffi) (t1 : asm_state a) (ms1 : B) r w :
  state_rel_r mc code2 labs p s1 t1 ms1 -> inst_sim p labs s1 t1 (Const r w).
Proof.
  intros R. split; [exact (sr_t1_failed R)|]. split; [reflexivity|].
  split; [exact (sr_fp_regs R)|]. split.
  - intros rx. cbn. rewrite !APPLY_UPDATE_THM. destruct (decide (r = rx)); [reflexivity|].
    apply (sr_regs R).
  - intros a0 Ha. exact (proj2 (proj2 (sr_mem R a0 Ha))).
Qed.

Lemma arith_upd_not_failed p labs (s1 : labSem.state a config Ffi) (t1 : asm_state a) (x : arith a) :
  (forall r, word_loc_val p labs (regs s1 r) = SOME (asmSem.regs t1 r)) ->
  ~ asmSem.failed t1 -> ~ failed (labSem.arith_upd x s1) ->
  ~ asmSem.failed (asmSem.arith_upd x t1).
Proof.
  intros H Ht. destruct x as [b r1 r2 ri|l r1 r2 ri|r1 r2 r3|r1 r2 r3 r4|r1 r2 r3 r4 r5|r1 r2 r3 r4
                 |r1 r2 r3 r4|r1 r2 r3 r4];
    cbn [labSem.arith_upd asmSem.arith_upd]; unfold asmSem.read_reg, asmSem.reg_imm.
  - intros _. destruct b; exact Ht.
  - destruct (regs s1 r2) as [w1|n1 n2] eqn:E2; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    destruct ri as [rr|ww]; cbn [labSem.reg_imm];
      [destruct (regs s1 rr) as [w2|m1 m2] eqn:E3; [|cbn; intros Hf; exfalso; apply Hf; reflexivity]|];
      regs_known H; cbn [labSem.assert labSem.set_failed labSem.failed asmSem.assert
                         asmSem.set_failed asmSem.failed asmSem.upd_reg asmSem.set_regs labSem.upd_reg
                         labSem.set_regs];
      intros Hf Hx; apply Hf; apply Bool.orb_true_iff in Hx as [Hx|Hx]; try discriminate;
      try (exfalso; exact (Ht Hx)); apply Bool.orb_true_iff; left; exact Hx.
  - destruct (regs s1 r3) as [w3|n1 n2] eqn:E3; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    destruct (regs s1 r2) as [w2|m1 m2] eqn:E2; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    regs_known H. cbn [labSem.assert labSem.set_failed labSem.failed asmSem.assert
                       asmSem.set_failed asmSem.failed asmSem.upd_reg asmSem.set_regs labSem.upd_reg
                       labSem.set_regs].
    intros Hf Hx; apply Hf; apply Bool.orb_true_iff in Hx as [Hx|Hx];
      try (exfalso; exact (Ht Hx)); apply Bool.orb_true_iff; left; exact Hx.
  - intros _. exact Ht.
  - destruct (regs s1 r3) as [w3|n1 n2] eqn:E3; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    destruct (regs s1 r4) as [w4|m1 m2] eqn:E4; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    destruct (regs s1 r5) as [w5|k1 k2] eqn:E5; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
    regs_known H. cbn [labSem.assert labSem.set_failed labSem.failed asmSem.assert
                       asmSem.set_failed asmSem.failed asmSem.upd_reg asmSem.set_regs labSem.upd_reg
                       labSem.set_regs].
    intros Hf Hx; apply Hf; apply Bool.orb_true_iff in Hx as [Hx|Hx];
      try (exfalso; exact (Ht Hx)); apply Bool.orb_true_iff; left; exact Hx.
  - intros _. exact Ht.
  - intros _. exact Ht.
  - intros _. exact Ht.
Qed.

Lemma inst_sim_Arith (mc : machine_config a B C) code2 labs p (s1 : labSem.state a config Ffi) (t1 : asm_state a) (ms1 : B) x :
  state_rel_r mc code2 labs p s1 t1 ms1 -> ~ failed (asm_inst (Arith x) s1) ->
  inst_sim p labs s1 t1 (Arith x).
Proof.
  intros R Hf. unfold inst_sim. cbn [asm_inst inst] in *.
  split; [exact (arith_upd_not_failed p labs s1 t1 x (sr_regs R) (sr_t1_failed R) Hf)|].
  split; [intros a0 _; cbn [inst]; rewrite (proj1 (proj2 (proj2 (asmProps.arith_upd_consts x t1)))); reflexivity|].
  split.
  { intros r. rewrite (proj1 (arith_upd_fp_regs x s1 t1)), (proj2 (arith_upd_fp_regs x s1 t1)).
    apply (sr_fp_regs R). }
  split; [exact (arith_upd_lemma p labs s1 t1 x (conj (sr_regs R) Hf))|].
  intros a0 Ha.
  destruct (labProps.arith_upd_consts x s1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Em & _).
  rewrite Em.
  rewrite (proj1 (proj2 (proj2 (asmProps.arith_upd_consts x t1)))).
  exact (proj2 (proj2 (sr_mem R a0 Ha))).
Qed.

Lemma fp_upd_not_failed (s1 : labSem.state a config Ffi) (t1 : asm_state a) (f : fp) :
  (forall r, fp_regs s1 r = asmSem.fp_regs t1 r) ->
  ~ asmSem.failed t1 -> ~ failed (labSem.fp_upd f s1) ->
  ~ asmSem.failed (asmSem.fp_upd f t1).
Proof.
  intros Hfp Ht. destruct f; cbn [labSem.fp_upd asmSem.fp_upd];
    unfold labSem.read_fp_reg, asmSem.read_fp_reg; rewrite ?Hfp;
    try (intros _; destruct (dimindex a =? 64); exact Ht).
  destruct (machine_ieee.fp64_to_int _ _) as [i|]; [|cbn; intros Hf; exfalso; apply Hf; reflexivity].
  destruct (dimindex a =? 64); [|destruct (ODD n)];
    cbn [labSem.upd_fp_reg labSem.set_fp_regs labSem.failed labSem.assert labSem.set_failed
         asmSem.upd_fp_reg asmSem.set_fp_regs asmSem.failed asmSem.assert asmSem.set_failed];
    intros Hf Hx; apply Hf; apply Bool.orb_true_iff in Hx as [Hx|Hx];
    try (exfalso; exact (Ht Hx)); apply Bool.orb_true_iff; left; exact Hx.
Qed.

Lemma inst_sim_FP (mc : machine_config a B C) code2 labs p (s1 : labSem.state a config Ffi) (t1 : asm_state a) (ms1 : B) f :
  state_rel_r mc code2 labs p s1 t1 ms1 -> ~ failed (asm_inst (FP f) s1) ->
  inst_sim p labs s1 t1 (FP f).
Proof.
  intros R Hf. unfold inst_sim. cbn [asm_inst inst] in *.
  destruct (fp_upd_lemma p labs s1 t1 f (conj (sr_regs R) (conj (sr_fp_regs R) Hf))) as [F1 F2].
  split; [exact (fp_upd_not_failed s1 t1 f (sr_fp_regs R) (sr_t1_failed R) Hf)|].
  split; [intros a0 _; cbn [inst]; rewrite (proj1 (proj2 (proj2 (asmProps.fp_upd_consts f t1)))); reflexivity|].
  split; [exact F1|]. split; [exact F2|].
  intros a0 Ha.
  destruct (labProps.fp_upd_consts f s1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Em & _).
  rewrite Em.
  rewrite (proj1 (proj2 (proj2 (asmProps.fp_upd_consts f t1)))).
  exact (proj2 (proj2 (sr_mem R a0 Ha))).
Qed.

End InstSim.

Ltac failed_false Hf :=
  cbn [labSem.assert labSem.set_failed labSem.failed] in Hf;
  exfalso; apply Hf; reflexivity.

Section MemSim.
Context {a : N} {B C Ffi : Type}.

Lemma byte_index_offset (w : word a) k be :
  good_dimindex a -> (w2n w mod (dimindex a / 8) + k < dimindex a / 8)%N ->
  byte_index (w + n2w k)%w be =
    if be then (8 * (dimindex a / 8 - 1 - (w2n w mod (dimindex a / 8) + k)))%N
    else (8 * (w2n w mod (dimindex a / 8) + k))%N.
Proof.
  intros Hg Hk. rewrite byte_index_mod.
  rewrite (proj1 (proj2 (byte_offset_good w k Hg Hk))). reflexivity.
Qed.

Lemma offs_start be (w : word a) m j :
  (j <= m)%N -> offs be (if be then (w + n2w m)%w else w) j =
                (w + n2w (if be then m - j else j))%w.
Proof.
  intros Hj. unfold offs. destruct be; [|reflexivity].
  rewrite n2w_sub by exact Hj. word_arith.
Qed.

Lemma mem_bytes_of_word (mc : machine_config a B C) code2 labs p (s1 : labSem.state a config Ffi)
    (t1 : asm_state a) (ms1 : B) (w : word a) v :
  state_rel_r mc code2 labs p s1 t1 ms1 ->
  byte_align w IN mem_domain s1 ->
  word_loc_val p labs (mem s1 (byte_align w)) = SOME v ->
  forall k, (w2n w mod (dimindex a / 8) + k < dimindex a / 8)%N ->
    (w + n2w k)%w IN asmSem.mem_domain t1 /\ (w + n2w k)%w IN mem_domain s1 /\
    asmSem.mem t1 (w + n2w k)%w = byte.get_byte (w + n2w k)%w v (be s1).
Proof.
  intros R Hw Hv k Hk. pose proof (sr_good_dimindex R) as Hg.
  destruct (byte_offset_good w k Hg Hk) as (Eb & _ & _).
  destruct (sr_mem_word mc code2 labs p s1 t1 ms1 (w + n2w k)%w R ltac:(rewrite Eb; exact Hw))
    as (H1 & H2 & v' & Hv' & H3).
  rewrite Eb, Hv in Hv'. injection Hv' as <-. auto.
Qed.

Lemma good_D (Hg : good_dimindex a) : (8 * (dimindex a / 8) = dimindex a)%N.
Proof. destruct Hg as [H|H]; rewrite H; reflexivity. Qed.

Lemma good_D_pos (Hg : good_dimindex a) : (0 < dimindex a / 8)%N.
Proof. destruct Hg as [H|H]; rewrite H; reflexivity. Qed.

Lemma good_D_dimword (Hg : good_dimindex a) : (dimindex a / 8 <= dimword a)%N.
Proof. destruct (dimword_good Hg) as [[H W]|[H W]]; rewrite H, W; cbn; lia. Qed.

Lemma aligned_LOG2_D (Hg : good_dimindex a) (w : word a) :
  aligned (LOG2 (dimindex a / 8)) w <-> (w2n w mod (dimindex a / 8) = 0)%N.
Proof. rewrite aligned_w2n, (byte_align_pow_good Hg). reflexivity. Qed.


Lemma inst_sim_Load (mc : machine_config a B C) code2 labs p (s1 : labSem.state a config Ffi)
    (t1 : asm_state a) (ms1 : B) r x :
  state_rel_r mc code2 labs p s1 t1 ms1 -> ~ failed (asm_inst (Mem Load r x) s1) ->
  inst_sim p labs s1 t1 (Mem Load r x).
Proof.
  intros R Hf. pose proof (sr_good_dimindex R) as Hg.
  destruct x as [n off]. unfold inst_sim. cbn [asm_inst inst labSem.mem_op asmSem.mem_op] in *.
  unfold labSem.mem_load, labSem.addr in Hf |- *.
  destruct (regs s1 n) as [wn|] eqn:En; [|failed_false Hf].
  pose proof (regs_rel_word _ _ _ _ _ _ (sr_regs R) En) as Etn.
  set (w := (wn + off)%w) in *.
  match type of Hf with context [labSem.assert ?c _] => destruct c eqn:Ec end;
    [|failed_false Hf].
  apply Bool.andb_true_iff in Ec as [Ec1 Ec2]. apply N.eqb_eq in Ec1. apply bool_decide_spec in Ec2.
  assert (Ebw : byte_align w = w) by (apply byte_align_id_good; assumption).
  destruct (sr_mem_word mc code2 labs p s1 t1 ms1 w R ltac:(rewrite Ebw; exact Ec2))
    as (_ & _ & v & Hv & _).
  rewrite Ebw in Hv.
  pose proof (mem_bytes_of_word mc code2 labs p s1 t1 ms1 w v R ltac:(rewrite Ebw; exact Ec2)
                ltac:(rewrite Ebw; exact Hv)) as Hb.
  rewrite Ec1 in Hb.
  unfold asmSem.mem_load, asmSem.addr, asmSem.read_reg. rewrite Etn. fold w.
  assert (Hrd : read_mem_word (if asmSem.be t1 then (w + n2w ((dimindex a / 8) - 1))%w else w) (dimindex a / 8) t1 = (v, t1)).
  { apply injective_projections; cbn [fst snd].
    - apply word_testbit_eq. intros i Hi. rewrite read_mem_word_bits.
      assert (HiD : (i / 8 <= (dimindex a / 8) - 1)%N).
      { pose proof (good_D Hg). lia. }
      rewrite offs_start by exact HiD.
      set (k' := if asmSem.be t1 then ((dimindex a / 8) - 1 - i / 8)%N else (i / 8)%N).
      assert (Hk' : (0 + k' < (dimindex a / 8))%N) by (pose proof (good_D_pos Hg); unfold k'; destruct (asmSem.be t1); lia).
      destruct (Hb k' Hk') as (_ & _ & Hm). rewrite Hm, testbit_get_byte.
      rewrite (byte_index_offset w k' (be s1) Hg) by (rewrite Ec1; exact Hk'). rewrite Ec1.
      rewrite (sr_be R). unfold k'.
      replace (i <? dimindex a)%N with true by (symmetry; apply N.ltb_lt; exact Hi).
      replace (i <? 8 * (dimindex a / 8))%N with true by (symmetry; apply N.ltb_lt; pose proof (good_D Hg); lia).
      replace (i mod 8 <? 8)%N with true by (symmetry; apply N.ltb_lt; apply N.mod_lt; discriminate).
      cbn [andb]. f_equal. destruct (asmSem.be t1); lia.
    - apply read_mem_word_snd. intros k Hk.
      rewrite offs_start by lia.
      refine (proj1 (Hb _ _)). destruct (asmSem.be t1); lia. }
  rewrite Hrd. cbv zeta.
  rewrite (proj2 (aligned_LOG2_D Hg w) Ec1).
  cbn [labSem.assert labSem.set_failed labSem.upd_reg labSem.set_regs labSem.regs labSem.fp_regs
       labSem.mem asmSem.assert asmSem.set_failed asmSem.upd_reg asmSem.set_regs asmSem.regs
       asmSem.failed asmSem.mem asmSem.fp_regs negb orb].
  split; [exact (sr_t1_failed R)|]. split; [intros; reflexivity|].
  split; [exact (sr_fp_regs R)|]. split.
  - intros rx. rewrite !APPLY_UPDATE_THM. destruct (decide (r = rx)); [exact Hv|apply (sr_regs R)].
  - intros a0 Ha. exact (proj2 (proj2 (sr_mem R a0 Ha))).
Qed.

Lemma write_mem_word_regs : forall n (ad w : word a) (t : asm_state a),
  asmSem.regs (write_mem_word ad n w t) = asmSem.regs t /\
  asmSem.fp_regs (write_mem_word ad n w t) = asmSem.fp_regs t.
Proof.
  intros n; induction n as [|n IH] using N.peano_ind; intros ad w t; [split; reflexivity|].
  rewrite (proj2 (write_mem_word_def ad n w t)). cbv zeta. apply IH.
Qed.

Lemma inst_sim_Store (mc : machine_config a B C) code2 labs p (s1 : labSem.state a config Ffi)
    (t1 : asm_state a) (ms1 : B) r x :
  state_rel_r mc code2 labs p s1 t1 ms1 -> ~ failed (asm_inst (Mem Store r x) s1) ->
  inst_sim p labs s1 t1 (Mem Store r x).
Proof.
  intros R Hf. pose proof (sr_good_dimindex R) as Hg.
  destruct x as [n off]. unfold inst_sim. cbn [asm_inst inst labSem.mem_op asmSem.mem_op] in *.
  unfold labSem.mem_store, labSem.addr in Hf |- *.
  destruct (regs s1 n) as [wn|] eqn:En; [|failed_false Hf].
  pose proof (regs_rel_word _ _ _ _ _ _ (sr_regs R) En) as Etn.
  set (w := (wn + off)%w) in *.
  match type of Hf with context [labSem.assert ?c _] => destruct c eqn:Ec end;
    [|failed_false Hf].
  apply Bool.andb_true_iff in Ec as [Ec1 Ec2]. apply N.eqb_eq in Ec1. apply bool_decide_spec in Ec2.
  assert (Ebw : byte_align w = w) by (apply byte_align_id_good; assumption).
  destruct (sr_mem_word mc code2 labs p s1 t1 ms1 w R ltac:(rewrite Ebw; exact Ec2))
    as (_ & _ & v & Hv & _).
  pose proof (mem_bytes_of_word mc code2 labs p s1 t1 ms1 w v R ltac:(rewrite Ebw; exact Ec2)
                Hv) as Hb.
  rewrite Ec1 in Hb.
  unfold asmSem.mem_store, asmSem.addr, asmSem.read_reg. rewrite Etn. fold w.
  rewrite (proj2 (aligned_LOG2_D Hg w) Ec1).
  set (st := if asmSem.be t1 then (w + n2w (dimindex a / 8 - 1))%w else w).
  assert (Hst : forall j, (j < dimindex a / 8)%N ->
            offs (asmSem.be t1) st j =
            (w + n2w (if asmSem.be t1 then dimindex a / 8 - 1 - j else j))%w).
  { intros j Hj. unfold st. apply offs_start. lia. }
  assert (Hdom : forall k, (k < dimindex a / 8)%N -> offs (asmSem.be t1) st k IN asmSem.mem_domain t1).
  { intros k Hk. rewrite (Hst k Hk). refine (proj1 (Hb _ _)). destruct (asmSem.be t1); lia. }
  pose proof (write_mem_word_regs (dimindex a / 8) st (asmSem.regs t1 r) t1) as [Er Efp].
  cbn [labSem.assert labSem.set_failed labSem.upd_mem labSem.set_mem labSem.regs labSem.fp_regs
       labSem.mem asmSem.assert asmSem.set_failed asmSem.regs asmSem.failed asmSem.mem
       asmSem.fp_regs negb orb].
  split; [rewrite write_mem_word_failed by exact Hdom; exact (sr_t1_failed R)|].
  split.
  { intros a0 Ha0. apply write_mem_word_mem_out. intros j Hj E. apply Ha0. rewrite E, (Hst j Hj).
    refine (proj1 (proj2 (Hb _ _))). destruct (asmSem.be t1); lia. }
  split; [rewrite Efp; exact (sr_fp_regs R)|]. split; [rewrite Er; exact (sr_regs R)|].
  intros a0 Ha. unfold word_loc_val_byte. rewrite APPLY_UPDATE_THM.
  destruct (decide (w = byte_align a0)) as [Ew|Nw].
  - rewrite (sr_regs R r).
    set (m := (w2n a0 mod (dimindex a / 8))%N).
    assert (Hm : (m < dimindex a / 8)%N) by (apply N.mod_lt; pose proof (good_D_pos Hg); lia).
    pose proof (byte_align_eq_good a0 Hg) as Ea0. rewrite <- Ew in Ea0. fold m in Ea0.
    set (j := if asmSem.be t1 then (dimindex a / 8 - 1 - m)%N else m).
    assert (Hj : (j < dimindex a / 8)%N) by (unfold j; destruct (asmSem.be t1); lia).
    assert (Eo : offs (asmSem.be t1) st j = a0).
    { rewrite (Hst j Hj). rewrite <- Ea0. f_equal. f_equal. unfold j.
      destruct (asmSem.be t1); lia. }
    rewrite <- Eo at 2. rewrite write_mem_word_mem_in by (try exact Hj; apply good_D_dimword, Hg).
    unfold byte.get_byte. rewrite (sr_be R). f_equal. f_equal. f_equal.
    rewrite byte_index_mod. fold m. unfold j. destruct (asmSem.be t1); lia.
  - rewrite write_mem_word_mem_out.
    + exact (proj2 (proj2 (sr_mem R a0 Ha))).
    + intros j Hj E. apply Nw. rewrite E, (Hst j Hj).
      rewrite (proj1 (byte_offset_good w (if asmSem.be t1 then (dimindex a / 8 - 1 - j)%N else j) Hg
                 ltac:(rewrite Ec1; destruct (asmSem.be t1); lia))).
      symmetry; exact Ebw.
Qed.

Lemma inst_sim_Load8 (mc : machine_config a B C) code2 labs p (s1 : labSem.state a config Ffi)
    (t1 : asm_state a) (ms1 : B) r x :
  state_rel_r mc code2 labs p s1 t1 ms1 -> ~ failed (asm_inst (Mem Load8 r x) s1) ->
  inst_sim p labs s1 t1 (Mem Load8 r x).
Proof.
  intros R Hf. pose proof (sr_good_dimindex R) as Hg.
  destruct x as [n off]. unfold inst_sim. cbn [asm_inst inst labSem.mem_op asmSem.mem_op] in *.
  unfold labSem.mem_load_byte, labSem.addr in Hf |- *.
  destruct (regs s1 n) as [wn|] eqn:En; [|failed_false Hf].
  pose proof (regs_rel_word _ _ _ _ _ _ (sr_regs R) En) as Etn.
  set (w := (wn + off)%w) in *.
  destruct (mem_load_byte_aux (mem s1) (mem_domain s1) (be s1) w) as [b|] eqn:Eb; [|failed_false Hf].
  unfold mem_load_byte_aux in Eb.
  destruct (mem s1 (byte_align w)) as [v|] eqn:Em; [|discriminate].
  destruct (classical_dec (byte_align w IN mem_domain s1)) as [Hd|]; [|discriminate].
  injection Eb as <-.
  destruct (sr_mem_word mc code2 labs p s1 t1 ms1 w R Hd) as (Ht & _ & v' & Hv' & Hm).
  rewrite Em in Hv'. cbn [word_loc_val] in Hv'. injection Hv' as <-.
  unfold asmSem.mem_load, asmSem.addr, asmSem.read_reg. rewrite Etn. fold w.
  replace (aligned (LOG2 1) w) with true by (symmetry; apply aligned_w2n; cbn; apply N.mod_1_r).
  assert (Hrd : read_mem_word (if asmSem.be t1 then (w + n2w (1 - 1))%w else w) 1 t1 =
                (w2w (byte.get_byte w v (be s1)), t1)).
  { assert (Hst : (if asmSem.be t1 then (w + n2w (1 - 1))%w else w) = w)
      by (destruct (asmSem.be t1); [exact (proj1 WORD_ADD_0 w)|reflexivity]).
    rewrite Hst. apply injective_projections; cbn [fst snd].
    - apply word_testbit_eq. intros i Hi. rewrite read_mem_word_bits, testbit_w2w.
      destruct (N.ltb_spec i 8) as [H8|H8].
      + rewrite (N.div_small i 8) by exact H8. rewrite (N.mod_small i 8) by exact H8.
        rewrite offs_0, Hm. replace (i <? 8 * 1)%N with true by (symmetry; apply N.ltb_lt; lia).
        rewrite Bool.andb_true_r. reflexivity.
      + replace (i <? 8 * 1)%N with false by (symmetry; apply N.ltb_ge; lia).
        rewrite (testbit_word8_high (byte.get_byte w v (be s1)) i H8). rewrite !Bool.andb_false_r. reflexivity.
    - apply read_mem_word_snd. intros k Hk. replace k with 0%N by lia. rewrite offs_0. exact Ht. }
  rewrite Hrd. cbv zeta.
  cbn [labSem.upd_reg labSem.set_regs labSem.regs labSem.fp_regs
       labSem.mem asmSem.assert asmSem.set_failed asmSem.upd_reg asmSem.set_regs asmSem.regs
       asmSem.failed asmSem.mem asmSem.fp_regs negb orb].
  split; [exact (sr_t1_failed R)|]. split; [intros; reflexivity|].
  split; [exact (sr_fp_regs R)|]. split.
  - intros rx. rewrite !APPLY_UPDATE_THM. destruct (decide (r = rx)); [reflexivity|apply (sr_regs R)].
  - intros a0 Ha. exact (proj2 (proj2 (sr_mem R a0 Ha))).
Qed.

Lemma inst_sim_Store8 (mc : machine_config a B C) code2 labs p (s1 : labSem.state a config Ffi)
    (t1 : asm_state a) (ms1 : B) r x :
  state_rel_r mc code2 labs p s1 t1 ms1 -> ~ failed (asm_inst (Mem Store8 r x) s1) ->
  inst_sim p labs s1 t1 (Mem Store8 r x).
Proof.
  intros R Hf. pose proof (sr_good_dimindex R) as Hg.
  destruct x as [n off]. unfold inst_sim. cbn [asm_inst inst labSem.mem_op asmSem.mem_op] in *.
  unfold labSem.mem_store_byte, labSem.addr in Hf |- *.
  destruct (regs s1 n) as [wn|] eqn:En; [|failed_false Hf].
  pose proof (regs_rel_word _ _ _ _ _ _ (sr_regs R) En) as Etn.
  set (w := (wn + off)%w) in *.
  destruct (regs s1 r) as [b|] eqn:Er; [|failed_false Hf].
  pose proof (regs_rel_word _ _ _ _ _ _ (sr_regs R) Er) as Etr.
  destruct (mem_store_byte_aux (mem s1) (mem_domain s1) (be s1) w (w2w b)) as [m'|] eqn:Eb;
    [|failed_false Hf].
  unfold mem_store_byte_aux in Eb.
  destruct (mem s1 (byte_align w)) as [v|] eqn:Em; [|discriminate].
  destruct (classical_dec (byte_align w IN mem_domain s1)) as [Hd|]; [|discriminate].
  injection Eb as <-.
  destruct (sr_mem_word mc code2 labs p s1 t1 ms1 w R Hd) as (Ht & Hs & v' & Hv' & Hm).
  rewrite Em in Hv'. cbn [word_loc_val] in Hv'. injection Hv' as <-.
  unfold asmSem.mem_store, asmSem.addr, asmSem.read_reg. rewrite Etn, Etr. fold w.
  replace (aligned (LOG2 1) w) with true by (symmetry; apply aligned_w2n; cbn; apply N.mod_1_r).
  set (st := if asmSem.be t1 then (w + n2w (1 - 1))%w else w).
  assert (Hst : offs (asmSem.be t1) st 0 = w)
    by (rewrite offs_0; unfold st; destruct (asmSem.be t1); [exact (proj1 WORD_ADD_0 w)|reflexivity]).
  assert (Hdom : forall k, (k < 1)%N -> offs (asmSem.be t1) st k IN asmSem.mem_domain t1)
    by (intros k Hk; replace k with 0%N by lia; rewrite Hst; exact Ht).
  pose proof (write_mem_word_regs 1 st b t1) as [Er' Efp].
  cbn [labSem.set_mem labSem.regs labSem.fp_regs labSem.mem asmSem.assert asmSem.set_failed
       asmSem.regs asmSem.failed asmSem.mem asmSem.fp_regs negb orb].
  assert (Hout : forall y, y <> w -> asmSem.mem (write_mem_word st 1 b t1) y = asmSem.mem t1 y).
  { intros y Hy. apply write_mem_word_mem_out. intros j Hj E. replace j with 0%N in E by lia.
    rewrite Hst in E. contradiction. }
  split; [rewrite write_mem_word_failed by exact Hdom; exact (sr_t1_failed R)|].
  split; [intros a0 Ha0; apply Hout; intros ->; contradiction|].
  split; [rewrite Efp; exact (sr_fp_regs R)|]. split; [rewrite Er'; exact (sr_regs R)|].
  intros a0 Ha. unfold word_loc_val_byte. rewrite APPLY_UPDATE_THM.
  destruct (decide (byte_align w = byte_align a0)) as [Ew|Nw].
  - cbn [word_loc_val]. destruct (decide (w = a0)) as [<-|Na].
    + rewrite good_dimindex_get_byte_set_byte by exact Hg.
      replace (asmSem.mem (write_mem_word st 1 b t1) w) with
        (asmSem.mem (write_mem_word st 1 b t1) (offs (asmSem.be t1) st 0)) by (rewrite Hst; reflexivity).
      rewrite write_mem_word_mem_in by (pose proof (good_D_dimword Hg); pose proof (good_D_pos Hg); lia).
      rewrite N.mul_0_r, lsr_0. reflexivity.
    + rewrite get_byte_set_byte_diff by (split; [exact Hg|split; [congruence|congruence]]).
      rewrite Hout by congruence.
      destruct (sr_mem_word mc code2 labs p s1 t1 ms1 a0 R Ha) as (_ & _ & v2 & Hv2 & Hm2).
      rewrite <- Ew, Em in Hv2. cbn in Hv2. injection Hv2 as <-. rewrite Hm2. reflexivity.
  - rewrite Hout by (intros ->; contradiction). exact (proj2 (proj2 (sr_mem R a0 Ha))).
Qed.

End MemSim.

Section Bytes32.

Lemma byte_index32 (j : N) be : (j < 4)%N ->
  byte_index (n2w j : word32) be = if be then (8 * (3 - j))%N else (8 * j)%N.
Proof.
  intros Hj. rewrite byte_index_mod. replace (dimindex 32) with 32%N by reflexivity.
  replace (32 / 8)%N with 4%N by reflexivity.
  rewrite w2n_n2w. replace (dimword 32) with 4294967296%N by reflexivity.
  rewrite (N.mod_small j) by lia. rewrite (N.mod_small j) by lia.
  destruct be; lia.
Qed.

Lemma word_of_bytes4_bits be (b0 b1 b2 b3 : word8) i : (i < 32)%N ->
  N.testbit (w2n (word_of_bytes be (n2w 0 : word32) [b0; b1; b2; b3])) i =
  N.testbit (w2n (if be then
                    (if (i <? 8)%N then b3 else if (i <? 16)%N then b2
                     else if (i <? 24)%N then b1 else b0)
                  else
                    (if (i <? 8)%N then b0 else if (i <? 16)%N then b1
                     else if (i <? 24)%N then b2 else b3)))
    (i mod 8).
Proof.
  intros Hi. cbn [word_of_bytes]. rewrite !word_add_n2w.
  rewrite !testbit_set_byte. rewrite !byte_index32 by lia.
  rewrite (testbit_n2w 0 i), N.bits_0, Bool.andb_false_r.
  replace (dimindex 32) with 32%N by reflexivity.
  assert (i < 8 \/ (8 <= i < 16) \/ (16 <= i < 24) \/ (24 <= i < 32))%N as Rg by lia.
  destruct be; destruct Rg as [Rg|[Rg|[Rg|Rg]]]; simpl_cmp; f_equal; lia.
Qed.

Lemma get_byte_w2w32 {a} (b : word a) (j : N) be : (j < 4)%N -> (32 <= dimindex a)%N ->
  byte.get_byte (n2w j : word32) (w2w b : word32) be =
  (w2w (b >>> (if be then 8 * (3 - j) else 8 * j)%N)%w : word8).
Proof.
  intros Hj Hd. apply word_testbit_eq. intros i Hi. replace (dimindex 8) with 8%N in Hi by reflexivity.
  rewrite testbit_get_byte, byte_index32 by exact Hj.
  rewrite !testbit_w2w, testbit_lsr.
  replace (dimindex 32) with 32%N by reflexivity. replace (dimindex 8) with 8%N by reflexivity.
  destruct be; simpl_cmp; f_equal; lia.
Qed.

End Bytes32.

Section MemSim32.
Context {a : N} {B C Ffi : Type}.

Lemma aligned2_offset (w : word a) :
  good_dimindex a -> aligned 2 w -> (w2n w mod (dimindex a / 8) + 3 < dimindex a / 8)%N.
Proof.
  intros Hg Ha. apply aligned_w2n in Ha. cbn in Ha.
  destruct Hg as [H|H]; rewrite H; cbn; lia.
Qed.

Lemma LOG2_4 : LOG2 4 = 2%N.
Proof. reflexivity. Qed.

Lemma inst_sim_Load32 (mc : machine_config a B C) code2 labs p (s1 : labSem.state a config Ffi)
    (t1 : asm_state a) (ms1 : B) r x :
  state_rel_r mc code2 labs p s1 t1 ms1 -> ~ failed (asm_inst (Mem Load32 r x) s1) ->
  inst_sim p labs s1 t1 (Mem Load32 r x).
Proof.
  intros R Hf. pose proof (sr_good_dimindex R) as Hg.
  destruct x as [n off]. unfold inst_sim. cbn [asm_inst inst labSem.mem_op asmSem.mem_op] in *.
  unfold labSem.mem_load32, labSem.addr in Hf |- *.
  destruct (regs s1 n) as [wn|] eqn:En; [|failed_false Hf].
  pose proof (regs_rel_word _ _ _ _ _ _ (sr_regs R) En) as Etn.
  set (w := (wn + off)%w) in *.
  destruct (mem_load_32 (mem s1) (mem_domain s1) (be s1) w) as [v32|] eqn:Eb; [|failed_false Hf].
  unfold mem_load_32 in Eb.
  destruct (aligned 2 w) eqn:Hal; [|discriminate].
  destruct (mem s1 (byte_align w)) as [v|] eqn:Em; [|discriminate].
  destruct (classical_dec (byte_align w IN mem_domain s1)) as [Hd|]; [|discriminate].
  injection Eb as <-.
  pose proof (aligned2_offset w Hg Hal) as Ho.
  pose proof (mem_bytes_of_word mc code2 labs p s1 t1 ms1 w v R Hd
                ltac:(rewrite Em; reflexivity)) as Hb.
  unfold asmSem.mem_load, asmSem.addr, asmSem.read_reg. rewrite Etn. fold w.
  rewrite LOG2_4, Hal.
  rewrite (sr_be R) in Hb |- *.
  assert (Hrd : read_mem_word (if asmSem.be t1 then (w + n2w (4 - 1))%w else w) 4 t1 =
    (w2w (word_of_bytes (asmSem.be t1) (n2w 0 : word32)
            [byte.get_byte w v (asmSem.be t1); byte.get_byte (w + n2w 1)%w v (asmSem.be t1);
             byte.get_byte (w + n2w 2)%w v (asmSem.be t1);
             byte.get_byte (w + n2w 3)%w v (asmSem.be t1)]), t1)).
  { replace (4 - 1)%N with 3%N by reflexivity.
    apply injective_projections; cbn [fst snd].
    - apply word_testbit_eq. intros i Hi. rewrite read_mem_word_bits, testbit_w2w.
      replace (dimindex 32) with 32%N by reflexivity.
      destruct (N.ltb_spec i 32) as [H32|H32].
      + rewrite word_of_bytes4_bits by exact H32.
        rewrite offs_start by lia.
        replace (i <? dimindex a)%N with true by (symmetry; apply N.ltb_lt; exact Hi).
        replace (i <? 8 * 4)%N with true by (symmetry; apply N.ltb_lt; lia).
        cbn [andb].
        assert (i < 8 \/ (8 <= i < 16) \/ (16 <= i < 24) \/ (24 <= i < 32))%N as Rg by lia.
        destruct (asmSem.be t1); destruct Rg as [Rg|[Rg|[Rg|Rg]]]; simpl_cmp;
          match goal with
          | |- N.testbit (w2n (asmSem.mem t1 (w + n2w ?e)%w)) _ =
               N.testbit (w2n (byte.get_byte (w + n2w ?k)%w v _)) _ =>
              replace e with k by lia; rewrite (proj2 (proj2 (Hb k ltac:(lia)))); reflexivity
          | |- N.testbit (w2n (asmSem.mem t1 (w + n2w ?e)%w)) _ =
               N.testbit (w2n (byte.get_byte w v _)) _ =>
              replace e with 0%N by lia; rewrite (proj2 (proj2 (Hb 0 ltac:(lia))));
              rewrite (proj1 WORD_ADD_0); reflexivity
          end.
      + replace (i <? 8 * 4)%N with false by (symmetry; apply N.ltb_ge; lia).
        rewrite (testbit_w2n_high _ i) by (replace (dimindex 32) with 32%N by reflexivity; lia).
        rewrite !Bool.andb_false_r. reflexivity.
    - apply read_mem_word_snd. intros k Hk. rewrite offs_start by lia.
      refine (proj1 (Hb _ _)). destruct (asmSem.be t1); lia. }
  rewrite Hrd. cbv zeta.
  cbn [labSem.upd_reg labSem.set_regs labSem.regs labSem.fp_regs
       labSem.mem asmSem.assert asmSem.set_failed asmSem.upd_reg asmSem.set_regs asmSem.regs
       asmSem.failed asmSem.mem asmSem.fp_regs negb orb].
  split; [exact (sr_t1_failed R)|]. split; [intros; reflexivity|].
  split; [exact (sr_fp_regs R)|]. split.
  - intros rx. rewrite !APPLY_UPDATE_THM. destruct (decide (r = rx)); [reflexivity|apply (sr_regs R)].
  - intros a0 Ha. rewrite <- (sr_be R). exact (proj2 (proj2 (sr_mem R a0 Ha))).
Qed.

Lemma get_byte_set_byte_cases (a0 w' : word a) (x : word8) (V : word a) be :
  good_dimindex a -> byte_align a0 = byte_align w' ->
  byte.get_byte a0 (set_byte w' x V be) be =
    if decide (a0 = w') then x else byte.get_byte a0 V be.
Proof.
  intros Hg Ha. destruct (decide (a0 = w')) as [->|Ne].
  - apply good_dimindex_get_byte_set_byte, Hg.
  - apply get_byte_set_byte_diff. split; [exact Hg|split; [exact Ne|exact Ha]].
Qed.

Lemma w_plus_neq (w : word a) j k :
  good_dimindex a -> (j < 4)%N -> (k < 4)%N -> j <> k -> (w + n2w j)%w <> (w + n2w k)%w.
Proof.
  intros Hg Hj Hk Hne E. apply WORD_EQ_ADD_LCANCEL in E. apply n2w_11 in E.
  pose proof (dimword_gt_8 Hg). rewrite !N.mod_small in E by lia. contradiction.
Qed.

Lemma asm_assert_true_fields (t : asm_state a) :
  asmSem.mem (asmSem.assert true t) = asmSem.mem t /\
  asmSem.regs (asmSem.assert true t) = asmSem.regs t /\
  asmSem.fp_regs (asmSem.assert true t) = asmSem.fp_regs t /\
  asmSem.failed (asmSem.assert true t) = asmSem.failed t.
Proof. repeat split. Qed.

Lemma inst_sim_Store32 (mc : machine_config a B C) code2 labs p (s1 : labSem.state a config Ffi)
    (t1 : asm_state a) (ms1 : B) r x :
  state_rel_r mc code2 labs p s1 t1 ms1 -> ~ failed (asm_inst (Mem Store32 r x) s1) ->
  inst_sim p labs s1 t1 (Mem Store32 r x).
Proof.
  intros R Hf. pose proof (sr_good_dimindex R) as Hg.
  destruct x as [n off]. unfold inst_sim. cbn [asm_inst inst labSem.mem_op asmSem.mem_op] in *.
  unfold labSem.mem_store32, labSem.addr in Hf |- *.
  destruct (regs s1 n) as [wn|] eqn:En; [|failed_false Hf].
  pose proof (regs_rel_word _ _ _ _ _ _ (sr_regs R) En) as Etn.
  set (w := (wn + off)%w) in *.
  destruct (regs s1 r) as [b|] eqn:Er; [|failed_false Hf].
  pose proof (regs_rel_word _ _ _ _ _ _ (sr_regs R) Er) as Etr.
  destruct (mem_store_32 (mem s1) (mem_domain s1) (be s1) w (w2w b)) as [m'|] eqn:Eb;
    [|failed_false Hf].
  unfold mem_store_32 in Eb.
  destruct (aligned 2 w) eqn:Hal; [|discriminate].
  destruct (mem s1 (byte_align w)) as [v|] eqn:Em; [|discriminate].
  destruct (classical_dec (byte_align w IN mem_domain s1)) as [Hd|]; [|discriminate].
  injection Eb as <-.
  pose proof (aligned2_offset w Hg Hal) as Ho.
  pose proof (mem_bytes_of_word mc code2 labs p s1 t1 ms1 w v R Hd
                ltac:(rewrite Em; reflexivity)) as Hb.
  assert (Hba : forall k, (k < 4)%N -> byte_align (w + n2w k)%w = byte_align w).
  { intros k Hk. exact (proj1 (byte_offset_good w k Hg ltac:(lia))). }
  assert (H32 : (32 <= dimindex a)%N) by (destruct Hg as [H|H]; rewrite H; lia).
  unfold asmSem.mem_store, asmSem.addr, asmSem.read_reg. rewrite Etn, Etr. fold w.
  rewrite LOG2_4, Hal.
  set (st := if asmSem.be t1 then (w + n2w (4 - 1))%w else w).
  assert (Hst : forall j, (j < 4)%N ->
            offs (asmSem.be t1) st j = (w + n2w (if asmSem.be t1 then 3 - j else j))%w).
  { intros j Hj. unfold st. replace (4 - 1)%N with 3%N by reflexivity. apply offs_start. lia. }
  assert (Hdom : forall k, (k < 4)%N -> offs (asmSem.be t1) st k IN asmSem.mem_domain t1).
  { intros k Hk. rewrite (Hst k Hk). refine (proj1 (Hb _ _)). destruct (asmSem.be t1); lia. }
  assert (Hout : forall y, (forall j, (j < 4)%N -> y <> (w + n2w j)%w) ->
            asmSem.mem (write_mem_word st 4 b t1) y = asmSem.mem t1 y).
  { intros y Hy. apply write_mem_word_mem_out. intros j Hj E. rewrite (Hst j Hj) in E.
    eapply Hy; [|exact E]. destruct (asmSem.be t1); lia. }
  assert (Hin : forall j, (j < 4)%N ->
            asmSem.mem (write_mem_word st 4 b t1) (w + n2w j)%w =
            w2w (b >>> (if asmSem.be t1 then 8 * (3 - j) else 8 * j)%N)%w).
  { intros j Hj.
    set (j' := if asmSem.be t1 then (3 - j)%N else j).
    assert (Hj' : (j' < 4)%N) by (unfold j'; destruct (asmSem.be t1); lia).
    replace (w + n2w j)%w with (offs (asmSem.be t1) st j')
      by (rewrite (Hst j' Hj'); unfold j'; destruct (asmSem.be t1); do 2 f_equal; lia).
    rewrite write_mem_word_mem_in by (pose proof (dimword_gt_8 Hg); lia).
    unfold j'. destruct (asmSem.be t1); do 3 f_equal; lia. }
  pose proof (write_mem_word_regs 4 st b t1) as [Er' Efp].
  destruct (asm_assert_true_fields (write_mem_word st 4 b t1)) as (Am & Ar & Afp & Af).
  rewrite Am, Ar, Afp, Af.
  cbn [labSem.set_mem labSem.regs labSem.fp_regs labSem.mem].
  split; [rewrite write_mem_word_failed by exact Hdom; exact (sr_t1_failed R)|].
  split.
  { intros a0 Ha0. apply Hout. intros j Hj ->. apply Ha0.
    refine (proj1 (proj2 (Hb _ _))). lia. }
  split; [rewrite Efp; exact (sr_fp_regs R)|]. split; [rewrite Er'; exact (sr_regs R)|].
  intros a0 Ha. unfold word_loc_val_byte. rewrite APPLY_UPDATE_THM.
  destruct (decide (byte_align w = byte_align a0)) as [Ew|Nw].
  - cbn [word_loc_val]. rewrite (sr_be R).
    assert (Hb0 : forall k, (k < 4)%N -> byte_align a0 = byte_align (w + n2w k)%w)
      by (intros k Hk; rewrite (Hba k Hk); symmetry; exact Ew).
    assert (Hbw : byte_align a0 = byte_align w) by (symmetry; exact Ew).
    rewrite !get_byte_set_byte_cases by first [exact Hg|apply Hb0; lia|exact Hbw].
    destruct (decide (a0 = (w + n2w 3)%w)) as [->|N3];
      [rewrite Hin by lia; rewrite get_byte_w2w32 by (try lia; exact H32); reflexivity|].
    destruct (decide (a0 = (w + n2w 2)%w)) as [->|N2];
      [rewrite Hin by lia; rewrite get_byte_w2w32 by (try lia; exact H32); reflexivity|].
    destruct (decide (a0 = (w + n2w 1)%w)) as [->|N1];
      [rewrite Hin by lia; rewrite get_byte_w2w32 by (try lia; exact H32); reflexivity|].
    destruct (decide (a0 = w)) as [->|N0].
    + replace (asmSem.mem (write_mem_word st 4 b t1) w) with
        (asmSem.mem (write_mem_word st 4 b t1) (w + n2w 0)%w) by (rewrite (proj1 WORD_ADD_0); reflexivity).
      rewrite Hin by lia.
      rewrite get_byte_w2w32 by (try lia; exact H32). reflexivity.
    + rewrite Hout.
      * destruct (sr_mem_word mc code2 labs p s1 t1 ms1 a0 R Ha) as (_ & _ & v2 & Hv2 & Hm2).
        rewrite Hbw, Em in Hv2. cbn in Hv2. injection Hv2 as <-. rewrite Hm2, (sr_be R).
        reflexivity.
      * intros j Hj Ej. assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3)%N as Hc by lia.
        destruct Hc as [ -> | [ -> | [ -> | -> ]]]; [rewrite (proj1 WORD_ADD_0) in Ej| | |]; contradiction.
  - rewrite Hout.
    + exact (proj2 (proj2 (sr_mem R a0 Ha))).
    + intros j Hj ->. apply Nw. rewrite (Hba j Hj). reflexivity.
Qed.

End MemSim32.

Section InstLemma.
Context {a : N} {B C Ffi : Type}.

Lemma inst_sim_all (mc : machine_config a B C) code2 labs p (s1 : labSem.state a config Ffi)
    (t1 : asm_state a) (ms1 : B) (i : asm.inst a) :
  state_rel_r mc code2 labs p s1 t1 ms1 -> ~ failed (asm_inst i s1) ->
  inst_sim p labs s1 t1 i.
Proof.
  intros R Hf. destruct i as [|r w|x|m r x|f].
  - apply (inst_sim_Skip mc code2 labs p s1 t1 ms1 R).
  - apply (inst_sim_Const mc code2 labs p s1 t1 ms1 r w R).
  - apply (inst_sim_Arith mc code2 labs p s1 t1 ms1 x R Hf).
  - destruct m.
    + apply (inst_sim_Load mc code2 labs p s1 t1 ms1 r x R Hf).
    + apply (inst_sim_Load8 mc code2 labs p s1 t1 ms1 r x R Hf).
    + exfalso. apply Hf. reflexivity.
    + apply (inst_sim_Load32 mc code2 labs p s1 t1 ms1 r x R Hf).
    + apply (inst_sim_Store mc code2 labs p s1 t1 ms1 r x R Hf).
    + apply (inst_sim_Store8 mc code2 labs p s1 t1 ms1 r x R Hf).
    + exfalso. apply Hf. reflexivity.
    + apply (inst_sim_Store32 mc code2 labs p s1 t1 ms1 r x R Hf).
  - apply (inst_sim_FP mc code2 labs p s1 t1 ms1 f R Hf).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "Inst_lemma" *)
Theorem Inst_lemma : forall (mc_conf : machine_config a B C) code2 labs p (i : asm.inst a)
    (s1 : labSem.state a config Ffi) (t1 : asm_state a) (ms1 ms2 : B) (bytes' : list word8),
  ~ (asm_inst i s1).(failed) /\
  state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 /\
  pos_val (pc s1 + 1) 0 code2 = pos_val (pc s1) 0 code2 + LENGTH bytes' ->
  ~ (inst i t1).(asmSem.failed) /\
  (forall a0, a0 NOTIN mem_domain s1 -> asmSem.mem (inst i t1) a0 = asmSem.mem t1 a0) /\
  (target_state_rel mc_conf.(target)
     (asmSem.upd_pc (asmSem.pc t1 + n2w (LENGTH bytes'))%w (inst i t1)) ms2 ->
   state_rel (mc_conf, (code2, (labs, p)))
     (inc_pc (dec_clock (asm_inst i s1)))
     (asmSem.upd_pc (asmSem.pc t1 + n2w (LENGTH bytes'))%w (inst i t1)) ms2).
Proof.
  intros mc_conf code2 labs p i s1 t1 ms1 ms2 bytes' (Hf & H & Hpos).
  pose proof H as R. apply state_rel_iff in R.
  destruct (inst_sim_all mc_conf code2 labs p s1 t1 ms1 i R Hf) as (S1 & S2 & S3 & S4 & S5).
  split; [exact S1|]. split; [exact S2|]. intros Htr.
  destruct (asm_inst_consts i s1) as (Cpc & Ccode & Cclk & Cffi & Cio & Ciofp & Ccc & Cccfp &
    Cptr & Clen & Cptr2 & Clen2 & Clink).
  destruct (asm_inst_consts2 i s1) as (Cdm & Csdm & Cbe & Ccomp & Corc & Ccb).
  destruct (inst_consts i t1) as (Tbe & Tlr & Tal & Tdm).
  apply (state_rel_inst_step mc_conf code2 labs p s1 _ t1 _ ms1 ms2 H Htr);
    cbn [inc_pc dec_clock set_pc set_clock labSem.mem_domain labSem.shared_mem_domain labSem.be
         labSem.ffi labSem.code labSem.compile labSem.compile_oracle labSem.code_buffer
         labSem.ptr_reg labSem.len_reg labSem.ptr2_reg labSem.len2_reg labSem.link_reg
         labSem.failed labSem.pc labSem.fp_regs labSem.regs labSem.mem
         asmSem.upd_pc asmSem.set_pc asmSem.mem_domain asmSem.be asmSem.align asmSem.lr
         asmSem.failed asmSem.mem asmSem.pc asmSem.fp_regs asmSem.regs];
    try assumption.
  - rewrite Cpc, (sr_pc R), Hpos. word_arith.
Qed.

End InstLemma.
