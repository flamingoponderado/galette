(** * HOL4 [byte]: byte-level manipulation of machine words

    Port of [HOL/src/n-bit/byteScript.sml].  HOL defines [word_slice_alt]
    (and through it [set_byte]) bitwise with [FCP]; here [word_slice_alt] is
    defined arithmetically (efficient after extraction) and HOL's [FCP]
    defining equation is proved as [word_slice_alt_def].  The remaining
    definitions follow HOL literally.  Proofs work bit by bit through
    [N.testbit]; the helper lemmas for that are local and untagged. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.n_bit Require Import sum_num words.
From Stdlib Require Import ZifyN.

Open Scope N_scope.

(** ** Bit-level helpers (Galette, untagged) *)

Module ByteBits.

Lemma dimindex_8 : dimindex 8 = 8.
Proof. reflexivity. Qed.

Lemma testbit_w2n_high {a} (w : word a) i :
  dimindex a <= i -> N.testbit (w2n w) i = false.
Proof.
  intros H. rewrite <- (N.mod_small (w2n w) (2 ** dimindex a)) by apply w2n_lt.
  apply N.mod_pow2_bits_high; exact H.
Qed.

Lemma testbit_w2n {a} (w : word a) i :
  N.testbit (w2n w) i = (i <? dimindex a) && N.testbit (w2n w) i.
Proof.
  destruct (N.ltb_spec i (dimindex a)); [reflexivity|].
  apply testbit_w2n_high; exact H.
Qed.

Lemma testbit_n2w {a} n i :
  N.testbit (w2n (n2w n : word a)) i = (i <? dimindex a) && N.testbit n i.
Proof.
  rewrite w2n_n2w, dimword_pow.
  destruct (N.ltb_spec i (dimindex a)).
  - apply N.mod_pow2_bits_low; exact H.
  - apply N.mod_pow2_bits_high; exact H.
Qed.

Lemma word_testbit_eq {a} (v w : word a) :
  (forall i, i < dimindex a -> N.testbit (w2n v) i = N.testbit (w2n w) i) ->
  v = w.
Proof.
  intros H; apply word_eq_w2n, N.bits_inj; intros i.
  destruct (N.ltb_spec i (dimindex a)).
  - apply H; exact H0.
  - rewrite !testbit_w2n_high by exact H0; reflexivity.
Qed.

Lemma fcp_index_testbit {a} (w : word a) i : fcp_index w i = N.testbit (w2n w) i.
Proof. apply BIT_testbit. Qed.

Lemma testbit_or {a} (v w : word a) i :
  N.testbit (w2n (word_or v w)) i = N.testbit (w2n v) i || N.testbit (w2n w) i.
Proof.
  unfold word_or; rewrite testbit_n2w, N.lor_spec.
  rewrite (testbit_w2n v), (testbit_w2n w).
  destruct (i <? dimindex a); reflexivity.
Qed.

Lemma testbit_and {a} (v w : word a) i :
  N.testbit (w2n (word_and v w)) i = N.testbit (w2n v) i && N.testbit (w2n w) i.
Proof.
  unfold word_and; rewrite testbit_n2w, N.land_spec.
  rewrite (testbit_w2n v).
  destruct (i <? dimindex a); reflexivity.
Qed.

Lemma testbit_w2w {a b} (w : word a) i :
  N.testbit (w2n (w2w w : word b)) i =
  (i <? dimindex b) && N.testbit (w2n w) i.
Proof. unfold w2w; apply testbit_n2w. Qed.

Lemma testbit_lsl {a} (w : word a) n i :
  N.testbit (w2n (word_lsl w n)) i =
  (i <? dimindex a) && (n <=? i) && N.testbit (w2n w) (i - n).
Proof.
  unfold word_lsl.
  destruct (N.ltb_spec (dimindex a - 1) n).
  - rewrite testbit_n2w, N.bits_0.
    destruct (N.ltb_spec i (dimindex a)); [|reflexivity].
    destruct (N.leb_spec n i); [lia|reflexivity].
  - rewrite testbit_n2w, <- N.shiftl_mul_pow2.
    destruct (N.leb_spec n i).
    + rewrite N.shiftl_spec_high by lia. destruct (i <? dimindex a); reflexivity.
    + rewrite N.shiftl_spec_low by lia. destruct (i <? dimindex a); reflexivity.
Qed.

Lemma testbit_lsr {a} (w : word a) n i :
  N.testbit (w2n (word_lsr w n)) i = N.testbit (w2n w) (i + n).
Proof.
  unfold word_lsr, word_bits, BITS, MOD_2EXP, DIV_2EXP.
  rewrite testbit_n2w, MIN_min, N.min_id.
  destruct (N.ltb_spec i (SUC (dimindex a - 1) - n)).
  - rewrite N.mod_pow2_bits_low, N.div_pow2_bits by exact H.
    pose proof (DIMINDEX_GT_0 a).
    replace (i <? dimindex a) with true by (symmetry; apply N.ltb_lt; lia).
    reflexivity.
  - rewrite N.mod_pow2_bits_high by exact H.
    pose proof (DIMINDEX_GT_0 a).
    rewrite testbit_w2n_high by lia. destruct (i <? dimindex a); reflexivity.
Qed.

Lemma testbit_add_shift x c k i :
  x < 2 ** k ->
  N.testbit (x + c * 2 ** k) i =
  if i <? k then N.testbit x i else N.testbit c (i - k).
Proof.
  intros Hx. destruct (N.ltb_spec i k).
  - rewrite <- (N.mod_pow2_bits_low _ k i) by exact H.
    rewrite N.Div0.mod_add, N.mod_small by exact Hx; reflexivity.
  - replace i with ((i - k) + k) at 1 by lia.
    rewrite <- N.div_pow2_bits, N.div_add, N.div_small by (try exact Hx; apply N.pow_nonzero; lia).
    reflexivity.
Qed.

Lemma SUM_SBIT_bound m f : SUM m (fun i => SBIT (f i) i) < 2 ** m.
Proof.
  induction m as [|m IH] using N.peano_ind; [cbn; lia|].
  rewrite (proj2 (SUM_def m _)).
  unfold SBIT in *; rewrite N.pow_succ_r'; destruct (f m); lia.
Qed.

Lemma testbit_SUM_SBIT m f i :
  N.testbit (SUM m (fun i => SBIT (f i) i)) i = (i <? m) && f i.
Proof.
  induction m as [|m IHm] using N.peano_ind.
  - rewrite (proj1 (SUM_def 0 _)), N.bits_0; destruct (N.ltb_spec i 0); [lia|reflexivity].
  - rewrite (proj2 (SUM_def m _)).
    replace (SBIT (f m) m) with ((if f m then 1 else 0) * 2 ** m)
      by (unfold SBIT; destruct (f m); lia).
    rewrite testbit_add_shift by apply SUM_SBIT_bound.
    rewrite IHm.
    destruct (N.ltb_spec i m), (N.ltb_spec i (SUC m)); try lia.
    + reflexivity.
    + replace i with m by lia. rewrite N.sub_diag.
      destruct (f m); reflexivity.
    + destruct (f m); [|apply N.bits_0].
      destruct (i - m) eqn:E; [lia|]. reflexivity.
Qed.

Lemma testbit_FCP {a} f i :
  N.testbit (w2n (FCP f : word a)) i = (i <? dimindex a) && f i.
Proof.
  unfold FCP; rewrite testbit_n2w, testbit_SUM_SBIT.
  destruct (i <? dimindex a); reflexivity.
Qed.

End ByteBits.

Import ByteBits.

(** ** Definitions *)

Section Defs.
Context {a : N}.

(*! HOL "HOL/src/n-bit/byteScript.sml" "byte_index_def" *)
Definition byte_index (a0 : word a) (is_bigendian : bool) : N :=
  let d := dimindex a DIV 8 in
  if is_bigendian then 8 * ((d - 1) - w2n a0 MOD d) else 8 * (w2n a0 MOD d).

(*! HOL "HOL/src/n-bit/byteScript.sml" "get_byte_def" *)
Definition get_byte (a0 w : word a) (is_bigendian : bool) : word8 :=
  w2w (w >>> byte_index a0 is_bigendian)%w.

(** HOL's [word_slice_alt h l w] keeps the bits [l <= i < h] of [w]
    ([FCP]-defined in HOL, see [word_slice_alt_def] below). *)
Definition word_slice_alt (h l : N) (w : word a) : word a :=
  n2w ((w2n w DIV 2 ** l) MOD 2 ** (h - l) * 2 ** l).

(*! HOL "HOL/src/n-bit/byteScript.sml" "set_byte_def" *)
Definition set_byte (a0 : word a) (b : word8) (w : word a) (is_bigendian : bool) : word a :=
  let i := byte_index a0 is_bigendian in
  (word_slice_alt (dimindex a) (i + 8) w
   || (w2w b << i
   || word_slice_alt i 0 w))%w.

(*! HOL "HOL/src/n-bit/byteScript.sml" "bytes_in_word_def" *)
Definition bytes_in_word : word a := n2w (dimindex a DIV 8).

(*! HOL "HOL/src/n-bit/byteScript.sml" "word_of_bytes_def" *)
Fixpoint word_of_bytes (be : bool) (a0 : word a) (l : list word8) : word a :=
  match l with
  | [] => n2w 0
  | b :: bs => set_byte a0 b (word_of_bytes be (a0 + n2w 1)%w bs) be
  end.

(** HOL defines [words_of_bytes] by well-founded recursion on the length of
    the byte list; here the recursion is bounded by that length (fuel), and
    HOL's equations are [words_of_bytes_def] below. *)
Fixpoint words_of_bytes_aux (fuel : nat) (be : bool) (bytes : list word8) : list (word a) :=
  match bytes with
  | [] => []
  | _ :: _ =>
      match fuel with
      | O => []
      | S fuel =>
          let xs := TAKE (MAX 1 (w2n (bytes_in_word : word a))) bytes in
          let ys := DROP (MAX 1 (w2n (bytes_in_word : word a))) bytes in
          word_of_bytes be (n2w 0) xs :: words_of_bytes_aux fuel be ys
      end
  end.

Definition words_of_bytes (be : bool) (bytes : list word8) : list (word a) :=
  words_of_bytes_aux (length bytes) be bytes.

(** HOL's [bytes_to_word_def] is the theorem of that name below (the
    recursion here is structural on the byte list). *)
Fixpoint bytes_to_word (k : N) (a0 : word a) (bs : list word8) (w : word a)
  (be : bool) : word a :=
  if k =? 0 then w else
    match bs with
    | [] => w
    | b :: bs => set_byte a0 b (bytes_to_word (k - 1) (a0 + n2w 1)%w bs w be) be
    end.

(** HOL's [word_to_bytes_aux_def] is the theorem of that name below. *)
Definition word_to_bytes_aux (n : N) (w : word a) (be : bool) : list word8 :=
  num_rec [] (fun n r => r ++ [get_byte (n2w n) w be]) n.

(*! HOL "HOL/src/n-bit/byteScript.sml" "word_to_bytes_def" *)
Definition word_to_bytes (w : word a) (be : bool) : list word8 :=
  word_to_bytes_aux (dimindex a DIV 8) w be.

(*! HOL "HOL/src/n-bit/byteScript.sml" "first_byte_at_def" *)
Fixpoint first_byte_at (k j : N) (a0 : word a) (bs : list word8) : word8 :=
  match bs with
  | [] => n2w 0
  | b :: bs => if w2n a0 MOD k =? j then b else first_byte_at k j (a0 + n2w 1)%w bs
  end.

(*! HOL "HOL/src/n-bit/byteScript.sml" "word_of_bytes_le_def" *)
Definition word_of_bytes_le : list word8 -> word a := word_of_bytes false (n2w 0).

(*! HOL "HOL/src/n-bit/byteScript.sml" "word_of_bytes_be_def" *)
Definition word_of_bytes_be : list word8 -> word a := word_of_bytes true (n2w 0).

(*! HOL "HOL/src/n-bit/byteScript.sml" "word_to_bytes_le_def" *)
Definition word_to_bytes_le (w : word a) : list word8 := word_to_bytes w false.

(*! HOL "HOL/src/n-bit/byteScript.sml" "word_to_bytes_be_def" *)
Definition word_to_bytes_be (w : word a) : list word8 := word_to_bytes w true.

End Defs.

Arguments bytes_in_word {a}.

(*! HOL "HOL/src/n-bit/byteScript.sml" "num_of_bytes_def" *)
Fixpoint num_of_bytes (l : list word8) : N :=
  match l with
  | [] => 0
  | b :: bs => w2n b + 256 * num_of_bytes bs
  end.

(** HOL's [bytes_of_num_def] is the theorem of that name below. *)
Definition bytes_of_num (k n : N) : list word8 :=
  num_rec (fun _ => []) (fun _ r n => (n2w n : word8) :: r (n DIV 256)) k n.

(** HOL's [be_bytes_def] is the theorem of that name below. *)
Definition be_bytes (l : N) (res bs : list word8) : list word8 :=
  num_rec (fun res _ => res)
    (fun _ r res bs =>
       match bs with
       | [] => r (n2w 0 :: res) []
       | x :: xs => r (x :: res) xs
       end) l res bs.

Section RecEqns.
Context {a : N}.

(*! HOL "HOL/src/n-bit/byteScript.sml" "word_to_bytes_aux_def" *)
Theorem word_to_bytes_aux_def : forall n (w : word a) be,
  word_to_bytes_aux 0 w be = [] /\
  word_to_bytes_aux (SUC n) w be = word_to_bytes_aux n w be ++ [get_byte (n2w n) w be].
Proof. intros; split; [reflexivity|]. unfold word_to_bytes_aux; rewrite num_rec_SUC; reflexivity. Qed.

End RecEqns.

(*! HOL "HOL/src/n-bit/byteScript.sml" "bytes_of_num_def" *)
Theorem bytes_of_num_def : forall k n,
  bytes_of_num 0 n = [] /\
  bytes_of_num (SUC k) n = (n2w n : word8) :: bytes_of_num k (n DIV 256).
Proof. intros; split; [reflexivity|]. unfold bytes_of_num; rewrite num_rec_SUC; reflexivity. Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "be_bytes_def" *)
Theorem be_bytes_def : forall l res x xs,
  be_bytes 0 res xs = res /\
  be_bytes (SUC l) res [] = be_bytes l (n2w 0 :: res) [] /\
  be_bytes (SUC l) res (x :: xs) = be_bytes l (x :: res) xs.
Proof.
  intros; repeat split; unfold be_bytes; rewrite ?num_rec_SUC; reflexivity.
Qed.

(** ** Bit-level characterisations (untagged) *)

Local Ltac cmp_cases :=
  repeat match goal with
  | |- context [?x <? ?y] => destruct (N.ltb_spec x y)
  | |- context [?x <=? ?y] => destruct (N.leb_spec x y)
  | |- context [?x =? ?y] => destruct (N.eqb_spec x y)
  end; cbn [andb orb negb]; try (exfalso; lia).

Local Ltac bfin :=
  repeat match goal with |- context [N.testbit ?x ?y] => destruct (N.testbit x y) end;
  reflexivity.

Lemma testbit_word_slice_alt {a} h l (w : word a) i :
  N.testbit (w2n (word_slice_alt h l w)) i =
  (l <=? i) && (i <? h) && N.testbit (w2n w) i.
Proof.
  unfold word_slice_alt; rewrite testbit_n2w, <- N.shiftl_mul_pow2.
  destruct (N.leb_spec l i).
  - rewrite N.shiftl_spec_high by lia.
    destruct (N.ltb_spec (i - l) (h - l)).
    + rewrite N.mod_pow2_bits_low, N.div_pow2_bits by lia.
      replace (i - l + l) with i by lia.
      rewrite (testbit_w2n w). cmp_cases; reflexivity.
    + rewrite N.mod_pow2_bits_high by lia. cmp_cases; reflexivity.
  - rewrite N.shiftl_spec_low by lia. cmp_cases; reflexivity.
Qed.

Lemma testbit_word8_high (b : word8) i : 8 <= i -> N.testbit (w2n b) i = false.
Proof. intros H; apply testbit_w2n_high; rewrite dimindex_8; exact H. Qed.

Lemma testbit_set_byte {a} (a0 : word a) b w be i :
  N.testbit (w2n (set_byte a0 b w be)) i =
  if (byte_index a0 be <=? i) && (i <? byte_index a0 be + 8)
  then (i <? dimindex a) && N.testbit (w2n b) (i - byte_index a0 be)
  else N.testbit (w2n w) i.
Proof.
  unfold set_byte; cbv zeta.
  rewrite !testbit_or, !testbit_word_slice_alt, testbit_lsl, testbit_w2w. try rewrite dimindex_8.
  rewrite (testbit_w2n w).
  set (k := byte_index a0 be).
  cmp_cases; try (rewrite testbit_word8_high by lia); bfin.
Qed.

Lemma testbit_get_byte {a} (a0 w : word a) be i :
  N.testbit (w2n (get_byte a0 w be)) i =
  (i <? 8) && N.testbit (w2n w) (i + byte_index a0 be).
Proof.
  unfold get_byte; rewrite testbit_w2w, dimindex_8, testbit_lsr; reflexivity.
Qed.

Lemma byte_index_bound {a} (a0 : word a) be :
  8 <= dimindex a -> byte_index a0 be + 8 <= dimindex a.
Proof.
  intros H. unfold byte_index; cbv zeta.
  assert (Hd : 0 < dimindex a / 8) by (apply N.div_str_pos; lia).
  pose proof (N.mod_upper_bound (w2n a0) (dimindex a / 8) ltac:(lia)).
  pose proof (N.Div0.mul_div_le (dimindex a) 8).
  set (k := dimindex a / 8) in *. set (r := w2n a0 MOD k) in *.
  destruct be; lia.
Qed.

Local Ltac wbits :=
  repeat progress rewrite ?testbit_set_byte, ?testbit_get_byte, ?testbit_word_slice_alt,
    ?testbit_or, ?testbit_and, ?testbit_lsl, ?testbit_lsr, ?testbit_w2w,
    ?testbit_FCP, ?fcp_index_testbit, ?testbit_n2w, ?dimindex_8, ?N.bits_0.

Lemma byte_index_mod {a} (a0 : word a) be :
  byte_index a0 be =
  if be then 8 * ((dimindex a DIV 8 - 1) - w2n a0 MOD (dimindex a DIV 8))
  else 8 * (w2n a0 MOD (dimindex a DIV 8)).
Proof. reflexivity. Qed.

(** ** Theorems *)

Section Thms.
Context {a : N}.

(*! HOL "HOL/src/n-bit/byteScript.sml" "word_slice_alt_def" *)
Theorem word_slice_alt_def : forall h l (w : word a),
  word_slice_alt h l w = FCP (fun i => (l <=? i) && ((i <? h) && (w ' i)%w)).
Proof.
  intros h l w; apply word_testbit_eq; intros i Hi; wbits.
  cmp_cases; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "set_byte_change_a" *)
Theorem set_byte_change_a : forall (a0 a' : word a) b w be,
  w2n a0 MOD (dimindex a DIV 8) = w2n a' MOD (dimindex a DIV 8) ->
  set_byte a0 b w be = set_byte a' b w be.
Proof. intros a0 a' b w be H; unfold set_byte, byte_index; rewrite H; reflexivity. Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "set_byte_eq_or" *)
Theorem set_byte_eq_or : forall (w : word a) ix bige b,
  (forall j, j < 8 -> ~ (w ' (byte_index ix bige + j))%w) ->
  set_byte ix b w bige = (w || (w2w b << byte_index ix bige))%w.
Proof.
  intros w ix bige b H; apply word_testbit_eq; intros i Hi; wbits.
  set (k := byte_index ix bige) in *.
  cmp_cases; try (rewrite testbit_word8_high by lia); try bfin.
  specialize (H (i - k) ltac:(lia)). rewrite fcp_index_testbit in H.
  replace (k + (i - k)) with i in H by lia.
  destruct (N.testbit (w2n w) i); [exfalso; apply H; reflexivity|bfin].
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "byte_index_lt_or_gt" *)
Theorem byte_index_lt_or_gt : forall (n m : word a) be,
  w2n n MOD (dimindex a DIV 8) <> w2n m MOD (dimindex a DIV 8) /\ 8 <= dimindex a ->
  byte_index n be + 8 <= byte_index m be \/ byte_index m be + 8 <= byte_index n be.
Proof.
  intros n m be [H1 H2]; rewrite !byte_index_mod.
  assert (Hd : 0 < dimindex a / 8) by (apply N.div_str_pos; lia).
  pose proof (N.mod_upper_bound (w2n n) (dimindex a / 8) ltac:(lia)).
  pose proof (N.mod_upper_bound (w2n m) (dimindex a / 8) ltac:(lia)).
  destruct be; lia.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "set_byte_transpose" *)
Theorem set_byte_transpose : forall (n m : word a) x y (w : word a) be,
  w2n n MOD (dimindex a DIV 8) <> w2n m MOD (dimindex a DIV 8) /\ 8 <= dimindex a ->
  set_byte n x (set_byte m y w be) be = set_byte m y (set_byte n x w be) be.
Proof.
  intros n m x y w be H.
  destruct (byte_index_lt_or_gt n m be H) as [Hs|Hs];
    apply word_testbit_eq; intros i Hi; wbits; cmp_cases; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "get_byte_set_byte" *)
Theorem get_byte_set_byte : forall (a0 : word a) b w be,
  8 <= dimindex a ->
  get_byte a0 (set_byte a0 b w be) be = b.
Proof.
  intros a0 b w be H; pose proof (byte_index_bound a0 be H).
  apply word_testbit_eq; intros i Hi; rewrite dimindex_8 in Hi; wbits.
  cmp_cases. rewrite N.add_sub; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "byte_index_offset" *)
Theorem byte_index_offset : forall (a0 : word a) be,
  8 <= dimindex a -> byte_index a0 be + 8 <= dimindex a.
Proof. intros; apply byte_index_bound; assumption. Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "DIV_not_0" *)
Theorem DIV_not_0 : forall d n, 1 < d -> (d <= n <-> 0 < n DIV d).
Proof.
  intros d n H; split; intros H'.
  - apply N.div_str_pos; lia.
  - destruct (N.le_gt_cases d n) as [|Hlt]; [assumption|].
    rewrite N.div_small in H' by exact Hlt; lia.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "get_byte_set_byte_irrelevant" *)
Theorem get_byte_set_byte_irrelevant : forall (a0 a' : word a) b w be,
  16 <= dimindex a /\
  w2n a0 MOD (dimindex a DIV 8) <> w2n a' MOD (dimindex a DIV 8) ->
  get_byte a' (set_byte a0 b w be) be = get_byte a' w be.
Proof.
  intros a0 a' b w be [H1 H2].
  destruct (byte_index_lt_or_gt a0 a' be (conj H2 (ltac:(lia) : 8 <= dimindex a))) as [Hs|Hs];
    apply word_testbit_eq; intros i Hi; rewrite dimindex_8 in Hi; wbits;
    cmp_cases; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "set_byte_get_byte" *)
Theorem set_byte_get_byte : forall (a0 w : word a) be,
  8 <= dimindex a ->
  set_byte a0 (get_byte a0 w be) w be = w.
Proof.
  intros a0 w be H; pose proof (byte_index_bound a0 be H).
  apply word_testbit_eq; intros i Hi; wbits; cmp_cases; try reflexivity.
  rewrite N.sub_add by lia; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "set_byte_get_byte'" *)
Theorem set_byte_get_byte' : forall (a0 w : word a) be,
  8 <= dimindex a ->
  set_byte a0 (get_byte a0 w be) w be = w.
Proof. exact set_byte_get_byte. Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "word_slice_alt_zero" *)
Theorem word_slice_alt_zero : forall h l,
  word_slice_alt h l (n2w 0 : word a) = n2w 0.
Proof.
  intros h l; apply word_testbit_eq; intros i Hi; wbits; cmp_cases; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "word_slice_alt_empty" *)
Theorem word_slice_alt_empty : forall h l (w : word a),
  h <= l -> word_slice_alt h l w = n2w 0.
Proof.
  intros h l w H; apply word_testbit_eq; intros i Hi; wbits; cmp_cases; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "word_slice_alt_full" *)
Theorem word_slice_alt_full : forall h (w : word a),
  dimindex a <= h -> word_slice_alt h 0 w = w.
Proof.
  intros h w H; apply word_testbit_eq; intros i Hi; wbits; cmp_cases; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "word_slice_alt_shift" *)
Theorem word_slice_alt_shift : forall h l (w : word a),
  h <= dimindex a ->
  word_slice_alt h l w = (w >>> l << l << (dimindex a - h) >>> (dimindex a - h))%w.
Proof.
  intros h l w H; apply word_testbit_eq; intros i Hi; wbits; cmp_cases; try reflexivity.
  all: f_equal; lia.
Qed.

End Thms.

(** ** Helpers on word arithmetic (untagged) *)

Lemma w2n_add_eq {a} (v w : word a) : w2n (v + w)%w = (w2n v + w2n w) MOD dimword a.
Proof. reflexivity. Qed.

Lemma w2n_n2w_small {a} n : n < dimword a -> w2n (n2w n : word a) = n.
Proof. intros H; rewrite w2n_n2w; apply N.mod_small, H. Qed.

Lemma dimindex_div8_lt {a} : dimindex a DIV 8 < dimword a.
Proof.
  unfold dimword. pose proof (N.pow_gt_lin_r 2 (dimindex a) ltac:(lia)).
  pose proof (N.Div0.div_le_upper_bound (dimindex a) 8 (dimindex a) ltac:(lia)). lia.
Qed.

Lemma w2n_bytes_in_word {a} : w2n (@bytes_in_word a) = dimindex a DIV 8.
Proof. apply w2n_n2w_small, dimindex_div8_lt. Qed.

Lemma mod_add_neq x m k : 0 < m < k -> (x + m) MOD k <> x MOD k.
Proof.
  intros [H1 H2]. rewrite <- N.Div0.add_mod_idemp_l.
  pose proof (N.mod_upper_bound x k ltac:(lia)).
  set (r := x MOD k) in *.
  destruct (N.ltb_spec (r + m) k).
  - rewrite N.mod_small by lia; lia.
  - replace (r + m) with ((r + m - k) + 1 * k) by lia.
    rewrite N.Div0.mod_add, N.mod_small by lia; lia.
Qed.

Section Thms2.
Context {a : N}.

(*! HOL "HOL/src/n-bit/byteScript.sml" "bytes_to_word_def" *)
Theorem bytes_to_word_def : forall k (a0 : word a) bs w be,
  bytes_to_word k a0 bs w be =
  if k =? 0 then w else
    match bs with
    | [] => w
    | b :: bs => set_byte a0 b (bytes_to_word (k - 1) (a0 + n2w 1)%w bs w be) be
    end.
Proof. intros k a0 [|b bs] w be; reflexivity. Qed.

Lemma bytes_to_word_cons k (a0 : word a) b bs w be :
  bytes_to_word (SUC k) a0 (b :: bs) w be =
  set_byte a0 b (bytes_to_word k (a0 + n2w 1)%w bs w be) be.
Proof.
  cbn [bytes_to_word]. destruct (N.eqb_spec (SUC k) 0); [lia|].
  rewrite N.sub_1_r, N.pred_succ; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "bytes_to_word_eq" *)
Theorem bytes_to_word_eq : forall (a0 : word a) bs w be k b,
  bytes_to_word 0 a0 bs w be = w /\
  bytes_to_word k a0 [] w be = w /\
  bytes_to_word (SUC k) a0 (b :: bs) w be =
    set_byte a0 b (bytes_to_word k (a0 + n2w 1)%w bs w be) be.
Proof.
  intros; split; [destruct bs; reflexivity|split].
  - cbn; destruct (k =? 0); reflexivity.
  - apply bytes_to_word_cons.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "word_of_bytes_bytes_to_word" *)
Theorem word_of_bytes_bytes_to_word : forall be (a0 : word a) bs k,
  LENGTH bs <= k ->
  word_of_bytes be a0 bs = bytes_to_word k a0 bs (n2w 0) be.
Proof.
  intros be a0 bs; revert a0; induction bs as [|b bs IH]; intros a0 k H.
  - cbn; destruct (k =? 0); reflexivity.
  - cbn [LENGTH] in H. replace k with (SUC (k - 1)) by lia.
    rewrite bytes_to_word_cons. cbn [word_of_bytes].
    rewrite (IH _ (k - 1)) by lia; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "bytes_to_word_same" *)
Theorem bytes_to_word_same : forall bw (k : word a) b1 w be b2,
  (forall n, n < bw -> n < LENGTH b1 /\ n < LENGTH b2 /\ EL n b1 = EL n b2) ->
  bytes_to_word bw k b1 w be = bytes_to_word bw k b2 w be.
Proof.
  induction bw as [|bw IH] using N.peano_ind; intros k b1 w be b2 H;
    [destruct b1, b2; reflexivity|].
  destruct b1 as [|x1 b1]; [destruct (H 0 ltac:(lia)) as [Hc _]; cbn in Hc; lia|].
  destruct b2 as [|x2 b2]; [destruct (H 0 ltac:(lia)) as [_ [Hc _]]; cbn in Hc; lia|].
  rewrite !bytes_to_word_cons.
  destruct (H 0 ltac:(lia)) as [_ [_ He]]; cbn in He; subst x2.
  rewrite (IH _ b1 w be b2); [reflexivity|].
  intros n Hn; destruct (H (SUC n) ltac:(lia)) as [H1 [H2 H3]]; cbn [LENGTH] in H1, H2.
  rewrite !EL_SUC in H3; cbn [TL] in H3.
  repeat split; try lia; exact H3.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "LENGTH_word_to_bytes_aux" *)
Theorem LENGTH_word_to_bytes_aux : forall n (w : word a) b,
  LENGTH (word_to_bytes_aux n w b) = n.
Proof.
  induction n as [|n IH] using N.peano_ind; intros w b; [reflexivity|].
  rewrite (proj2 (word_to_bytes_aux_def n w b)), LENGTH_length, length_app.
  pose proof (IH w b) as E; rewrite LENGTH_length in E; cbn [length]; lia.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "LENGTH_word_to_bytes" *)
Theorem LENGTH_word_to_bytes : forall (w : word a) be,
  LENGTH (word_to_bytes w be) = dimindex a DIV 8.
Proof. intros; apply LENGTH_word_to_bytes_aux. Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "EL_word_to_bytes_aux" *)
Theorem EL_word_to_bytes_aux : forall i n (w : word a) be,
  i < n -> EL i (word_to_bytes_aux n w be) = get_byte (n2w i) w be.
Proof.
  intros i n w be H; rewrite EL_nth by (rewrite LENGTH_word_to_bytes_aux; exact H).
  revert H; induction n as [|n IH] using N.peano_ind; intros H; [lia|].
  rewrite (proj2 (word_to_bytes_aux_def n w be)).
  pose proof (LENGTH_word_to_bytes_aux n w be) as HL; rewrite LENGTH_length in HL.
  destruct (N.ltb_spec i n).
  - rewrite app_nth1 by lia. apply IH; lia.
  - replace i with n by lia.
    rewrite app_nth2 by lia.
    replace (N.to_nat n - length (word_to_bytes_aux n w be))%nat with O by lia; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "byte_index_cycle" *)
Theorem byte_index_cycle : forall (a0 : word a) be,
  8 <= dimindex a ->
  byte_index (n2w (w2n a0 MOD (dimindex a DIV 8)) : word a) be = byte_index a0 be.
Proof.
  intros a0 be H; rewrite !byte_index_mod.
  rewrite w2n_n2w_small.
  - rewrite N.Div0.mod_mod; reflexivity.
  - pose proof (N.Div0.mod_le (w2n a0) (dimindex a DIV 8)).
    pose proof (w2n_lt a0); lia.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "get_byte_cycle" *)
Theorem get_byte_cycle : forall (a0 w : word a) be,
  8 <= dimindex a ->
  get_byte (n2w (w2n a0 MOD (dimindex a DIV 8)) : word a) w be = get_byte a0 w be.
Proof. intros a0 w be H; unfold get_byte; rewrite byte_index_cycle by exact H; reflexivity. Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "set_byte_cycle" *)
Theorem set_byte_cycle : forall (a0 : word a) b w be,
  8 <= dimindex a ->
  set_byte (n2w (w2n a0 MOD (dimindex a DIV 8)) : word a) b w be = set_byte a0 b w be.
Proof. intros a0 b w be H; unfold set_byte; rewrite byte_index_cycle by exact H; reflexivity. Qed.

End Thms2.

Lemma LENGTH_DROP {A} n (l : list A) : LENGTH (DROP n l) = LENGTH l - n.
Proof. rewrite !LENGTH_length, DROP_skipn, length_skipn; lia. Qed.

Lemma TAKE_app_le {A} n (l1 l2 : list A) :
  n <= LENGTH l1 -> TAKE n (l1 ++ l2) = TAKE n l1.
Proof.
  rewrite LENGTH_length, !TAKE_firstn, firstn_app; intros H.
  replace (N.to_nat n - length l1)%nat with O by lia. apply app_nil_r.
Qed.

Lemma DROP_app_le {A} n (l1 l2 : list A) :
  n <= LENGTH l1 -> DROP n (l1 ++ l2) = DROP n l1 ++ l2.
Proof.
  rewrite LENGTH_length, !DROP_skipn, skipn_app; intros H.
  replace (N.to_nat n - length l1)%nat with O by lia. reflexivity.
Qed.

Lemma words_of_bytes_aux_fuel {a} be : forall (f1 f2 : nat) (bytes : list word8),
  (length bytes <= f1)%nat -> (length bytes <= f2)%nat ->
  (words_of_bytes_aux f1 be bytes : list (word a)) = words_of_bytes_aux f2 be bytes.
Proof.
  induction f1 as [|f1 IH]; intros f2 bytes H1 H2.
  - destruct bytes; [destruct f2; reflexivity|cbn in H1; lia].
  - destruct bytes as [|x xs]; [destruct f2; reflexivity|].
    destruct f2 as [|f2]; [cbn in H2; lia|]. cbn [words_of_bytes_aux].
    f_equal. apply IH.
    + rewrite DROP_skipn, length_skipn; cbn [length] in *; rewrite MAX_max; lia.
    + rewrite DROP_skipn, length_skipn; cbn [length] in *; rewrite MAX_max; lia.
Qed.

Section Thms3.
Context {a : N}.

(*! HOL "HOL/src/n-bit/byteScript.sml" "words_of_bytes_def" *)
Theorem words_of_bytes_def :
  (forall be, words_of_bytes be [] = ([] : list (word a))) /\
  (forall be v2 v3,
     words_of_bytes be (v2 :: v3) =
     let xs := TAKE (MAX 1 (w2n (bytes_in_word : word a))) (v2 :: v3) in
     let ys := DROP (MAX 1 (w2n (bytes_in_word : word a))) (v2 :: v3) in
     (word_of_bytes be (n2w 0) xs : word a) :: words_of_bytes be ys).
Proof.
  split; [reflexivity|]. intros be v2 v3.
  unfold words_of_bytes at 1; cbn [words_of_bytes_aux length].
  cbv zeta. f_equal. apply words_of_bytes_aux_fuel; [|lia].
  rewrite DROP_skipn, length_skipn; cbn [length]; rewrite MAX_max; lia.
Qed.

Lemma words_of_bytes_cons be (x : word8) xs :
  (words_of_bytes be (x :: xs) : list (word a)) =
  word_of_bytes be (n2w 0) (TAKE (dimindex a DIV 8) (x :: xs))
  :: words_of_bytes be (DROP (dimindex a DIV 8) (x :: xs)) \/ dimindex a DIV 8 = 0.
Proof.
  destruct (N.eq_dec (dimindex a DIV 8) 0) as [|Hk]; [right; assumption|left].
  rewrite (proj2 words_of_bytes_def); cbv zeta.
  rewrite w2n_bytes_in_word, MAX_max. set (k := dimindex a DIV 8) in *. rewrite N.max_r by lia; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "LENGTH_words_of_bytes" *)
Theorem LENGTH_words_of_bytes :
  8 <= dimindex a ->
  forall be ls,
  LENGTH (words_of_bytes be ls : list (word a)) =
  LENGTH ls DIV w2n (bytes_in_word : word a) +
  MIN 1 (LENGTH ls MOD w2n (bytes_in_word : word a)).
Proof.
  intros Hd be ls. rewrite w2n_bytes_in_word, MIN_min.
  set (k := dimindex a DIV 8).
  assert (Hk : 0 < k) by (apply N.div_str_pos; lia).
  remember (length ls) as L eqn:HL. revert ls HL.
  induction L as [L IH] using lt_wf_ind; intros ls HL.
  destruct ls as [|x xs].
  - reflexivity.
  - destruct (words_of_bytes_cons be x xs) as [E|E]; [|lia].
    fold k in E; rewrite E. cbn [LENGTH].
    rewrite (IH (length (DROP k (x :: xs)))).
    2: { rewrite DROP_skipn, length_skipn, <- HL. cbn [length] in HL. lia. }
    2: reflexivity.
    rewrite LENGTH_DROP. cbn [LENGTH].
    set (M := SUC (LENGTH xs)).
    assert (HM : 0 < M) by (unfold M; lia).
    destruct (N.ltb_spec M k).
    + replace (M - k) with 0 by lia.
      rewrite N.Div0.div_0_l, N.Div0.mod_0_l, (N.div_small M k), (N.mod_small M k) by lia.
      lia.
    + assert (E1 : M DIV k = (M - k) DIV k + 1).
      { replace M with ((M - k) + 1 * k) at 1 by lia. rewrite N.div_add by lia; reflexivity. }
      assert (E2 : M MOD k = (M - k) MOD k).
      { replace M with ((M - k) + 1 * k) at 1 by lia. rewrite N.Div0.mod_add; reflexivity. }
      rewrite E1, E2. set (q := (M - k) DIV k). set (r := (M - k) MOD k). lia.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "words_of_bytes_append" *)
Theorem words_of_bytes_append : forall be,
  0 < w2n (bytes_in_word : word a) ->
  forall l1 l2,
  LENGTH l1 MOD w2n (bytes_in_word : word a) = 0 ->
  (words_of_bytes be (l1 ++ l2) : list (word a)) =
  words_of_bytes be l1 ++ words_of_bytes be l2.
Proof.
  intros be. rewrite w2n_bytes_in_word. set (k := dimindex a DIV 8). intros Hk l1.
  remember (length l1) as L eqn:HL. revert l1 HL.
  induction L as [L IH] using lt_wf_ind; intros l1 HL l2 Hm.
  destruct l1 as [|x xs]; [reflexivity|].
  assert (Hge : k <= LENGTH (x :: xs)).
  { destruct (N.le_gt_cases k (LENGTH (x :: xs))); [assumption|].
    rewrite N.mod_small in Hm by lia. cbn [LENGTH] in Hm; lia. }
  change ((x :: xs) ++ l2) with (x :: xs ++ l2).
  destruct (words_of_bytes_cons be x (xs ++ l2)) as [E|E]; [|lia].
  destruct (words_of_bytes_cons be x xs) as [E'|E']; [|lia].
  fold k in E, E'. rewrite E, E'. cbn [app]. f_equal.
  - change (x :: xs ++ l2) with ((x :: xs) ++ l2). rewrite TAKE_app_le by exact Hge; reflexivity.
  - change (x :: xs ++ l2) with ((x :: xs) ++ l2). rewrite DROP_app_le by exact Hge.
    apply (IH (length (DROP k (x :: xs)))).
    + rewrite DROP_skipn, length_skipn, <- HL. cbn [length] in HL. lia.
    + reflexivity.
    + rewrite LENGTH_DROP. set (M := LENGTH (x :: xs)) in *.
      replace M with ((M - k) + 1 * k) in Hm by lia.
      rewrite N.Div0.mod_add in Hm; exact Hm.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "words_of_bytes_append_word" *)
Theorem words_of_bytes_append_word : forall l1 l2 be,
  0 < LENGTH l1 /\ LENGTH l1 = w2n (bytes_in_word : word a) ->
  words_of_bytes be (l1 ++ l2) = (word_of_bytes be (n2w 0 : word a) l1 :: words_of_bytes be l2).
Proof.
  intros l1 l2 be [H1 H2]. rewrite w2n_bytes_in_word in H2.
  destruct l1 as [|x xs]; [cbn in H1; lia|].
  destruct (words_of_bytes_cons be x (xs ++ l2)) as [E|E]; [|lia].
  change ((x :: xs) ++ l2) with (x :: xs ++ l2). rewrite E.
  change (x :: xs ++ l2) with ((x :: xs) ++ l2).
  rewrite TAKE_app_le, DROP_app_le by lia. rewrite <- H2.
  rewrite TAKE_firstn, DROP_skipn, LENGTH_length, Nat2N.id, firstn_all, skipn_all.
  reflexivity.
Qed.

End Thms3.

Lemma dimword_ge_dimindex {a} : dimindex a < dimword a.
Proof. unfold dimword; apply N.pow_gt_lin_r; lia. Qed.

Lemma byte_index_n2w_le {a} j :
  j < dimindex a DIV 8 -> byte_index (n2w j : word a) false = 8 * j.
Proof.
  intros H; rewrite byte_index_mod, w2n_n2w_small, N.mod_small by
    (try exact H; pose proof (@dimindex_div8_lt a); lia).
  reflexivity.
Qed.

Lemma byte_index_n2w_be {a} j :
  j < dimindex a DIV 8 ->
  byte_index (n2w j : word a) true = 8 * (dimindex a DIV 8 - 1 - j).
Proof.
  intros H; rewrite byte_index_mod, w2n_n2w_small, N.mod_small by
    (try exact H; pose proof (@dimindex_div8_lt a); lia).
  reflexivity.
Qed.

Lemma word_add_n2w_0_l {a} j : (n2w 0 + n2w j : word a)%w = n2w j.
Proof.
  apply word_eq_w2n; rewrite w2n_add_eq, !w2n_n2w, N.Div0.mod_0_l, N.add_0_l.
  apply N.Div0.mod_mod.
Qed.

Section Thms4.
Context {a : N}.

(*! HOL "HOL/src/n-bit/byteScript.sml" "word_of_bytes_SNOC" *)
Theorem word_of_bytes_SNOC : forall bs (n : word a) be b,
  LENGTH bs < dimindex a DIV 8 /\ w2n n + LENGTH bs < dimword a ->
  word_of_bytes be n (SNOC b bs) =
  set_byte (n + n2w (LENGTH bs))%w b (word_of_bytes be n bs) be.
Proof.
  induction bs as [|h bs IH]; intros n be b [H1 H2].
  - cbn -[set_byte]. f_equal. apply word_eq_w2n.
    rewrite w2n_add_eq, w2n_n2w, N.Div0.mod_0_l, N.add_0_r.
    symmetry; apply N.mod_small, w2n_lt.
  - cbn [LENGTH] in H1, H2.
    assert (D1 : 1 < dimword a) by (pose proof (@dimindex_div8_lt a); lia).
    assert (En1 : w2n (n + n2w 1)%w = w2n n + 1).
    { rewrite w2n_add_eq, w2n_n2w_small, N.mod_small by lia; reflexivity. }
    change (SNOC b (h :: bs)) with (h :: SNOC b bs).
    cbn [word_of_bytes].
    rewrite IH by (rewrite En1; lia).
    assert (EN : ((n + n2w 1) + n2w (LENGTH bs))%w = (n + n2w (LENGTH (h :: bs)))%w).
    { apply word_eq_w2n. rewrite (w2n_add_eq (n + n2w 1)%w), En1, w2n_add_eq, !w2n_n2w_small by (cbn [LENGTH]; lia).
      cbn [LENGTH]. f_equal; lia. }
    rewrite EN.
    apply set_byte_transpose. split.
    + rewrite w2n_add_eq, w2n_n2w_small by (cbn [LENGTH]; lia).
      rewrite (N.mod_small (w2n n + _)) by (cbn [LENGTH]; lia).
      intros Heq; symmetry in Heq; revert Heq; apply mod_add_neq; cbn [LENGTH]; lia.
    + assert (2 <= dimindex a DIV 8) by lia.
      pose proof (N.Div0.mul_div_le (dimindex a) 8); lia.
Qed.

Lemma word_of_bytes_to_bytes_step (w : word a) n be :
  SUC n <= dimindex a DIV 8 -> 8 <= dimindex a ->
  word_of_bytes be (n2w 0 : word a) (word_to_bytes_aux (SUC n) w be) =
  set_byte (n2w n) (get_byte (n2w n) w be)
    (word_of_bytes be (n2w 0 : word a) (word_to_bytes_aux n w be)) be.
Proof.
  intros H1 H2. rewrite (proj2 (word_to_bytes_aux_def n w be)), <- SNOC_app.
  rewrite word_of_bytes_SNOC, LENGTH_word_to_bytes_aux, word_add_n2w_0_l; [reflexivity|].
  rewrite LENGTH_word_to_bytes_aux, w2n_n2w, N.Div0.mod_0_l.
  pose proof (@dimindex_div8_lt a). lia.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "word_of_bytes_word_to_bytes_aux_le" *)
Theorem word_of_bytes_word_to_bytes_aux_le : forall n (w : word a),
  n <= dimindex a DIV 8 /\ 8 <= dimindex a ->
  word_of_bytes false (n2w 0 : word a) (word_to_bytes_aux n w false) =
  word_slice_alt (8 * n) 0 w.
Proof.
  induction n as [|n IH] using N.peano_ind; intros w [H1 H2].
  - cbn. symmetry; apply word_slice_alt_empty; lia.
  - rewrite word_of_bytes_to_bytes_step, IH by lia.
    pose proof (byte_index_n2w_le (a := a) n ltac:(lia)) as Hb.
    apply word_testbit_eq; intros i Hi; wbits. rewrite Hb.
    cmp_cases; try reflexivity. f_equal; lia.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "word_of_bytes_word_to_bytes_aux_be" *)
Theorem word_of_bytes_word_to_bytes_aux_be : forall n (w : word a),
  n <= dimindex a DIV 8 /\ 8 <= dimindex a ->
  word_of_bytes true (n2w 0 : word a) (word_to_bytes_aux n w true) =
  word_slice_alt (8 * (dimindex a DIV 8)) (8 * (dimindex a DIV 8 - n)) w.
Proof.
  induction n as [|n IH] using N.peano_ind; intros w [H1 H2].
  - change (word_to_bytes_aux 0 w true) with (@nil word8). cbn [word_of_bytes]. symmetry; apply word_slice_alt_empty; lia.
  - rewrite word_of_bytes_to_bytes_step, IH by lia.
    pose proof (byte_index_n2w_be (a := a) n ltac:(lia)) as Hb.
    apply word_testbit_eq; intros i Hi; wbits. rewrite Hb.
    cmp_cases; try reflexivity. f_equal; lia.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "word_of_bytes_word_to_bytes" *)
Theorem word_of_bytes_word_to_bytes : forall be (w : word a),
  8 <= dimindex a /\ N.divide 8 (dimindex a) ->
  word_of_bytes be (n2w 0) (word_to_bytes w be) = w.
Proof.
  intros be w [H1 [q Hq]]. unfold word_to_bytes.
  assert (E : 8 * (dimindex a DIV 8) = dimindex a)
    by (rewrite Hq, N.div_mul by lia; lia).
  destruct be.
  - rewrite word_of_bytes_word_to_bytes_aux_be by lia.
    rewrite N.sub_diag, N.mul_0_r, E. apply word_slice_alt_full; lia.
  - rewrite word_of_bytes_word_to_bytes_aux_le by lia.
    rewrite E. apply word_slice_alt_full; lia.
Qed.

End Thms4.

(*! HOL "HOL/src/n-bit/byteScript.sml" "word_to_bytes_word_of_bytes_32" *)
Theorem word_to_bytes_word_of_bytes_32 : forall be (w : word32),
  word_of_bytes be (n2w 0) (word_to_bytes w be) = w.
Proof. intros; apply word_of_bytes_word_to_bytes; split; [cbn; lia|exists 4; reflexivity]. Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "word_to_bytes_word_of_bytes_64" *)
Theorem word_to_bytes_word_of_bytes_64 : forall be (w : word64),
  word_of_bytes be (n2w 0) (word_to_bytes w be) = w.
Proof. intros; apply word_of_bytes_word_to_bytes; split; [cbn; lia|exists 8; reflexivity]. Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "LENGTH_bytes_of_num" *)
Theorem LENGTH_bytes_of_num : forall k n, LENGTH (bytes_of_num k n) = k.
Proof.
  induction k as [|k IH] using N.peano_ind; intros n; [reflexivity|].
  rewrite (proj2 (bytes_of_num_def k n)); cbn [LENGTH]; rewrite IH; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "EL_bytes_of_num" *)
Theorem EL_bytes_of_num : forall i k n,
  i < k -> EL i (bytes_of_num k n) = n2w (n DIV 256 ** i).
Proof.
  intros i k; revert i; induction k as [|k IH] using N.peano_ind; intros i n H; [lia|].
  rewrite (proj2 (bytes_of_num_def k n)).
  destruct i as [|i] using N.peano_ind.
  - rewrite N.pow_0_r, N.div_1_r; reflexivity.
  - rewrite EL_SUC; cbn [TL]. rewrite IH by lia.
    rewrite N.Div0.div_div, <- N.pow_succ_r'; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "LENGTH_be_bytes" *)
Theorem LENGTH_be_bytes : forall l res bs, LENGTH (be_bytes l res bs) = l + LENGTH res.
Proof.
  induction l as [|l IH] using N.peano_ind; intros res bs; [reflexivity|].
  destruct bs as [|x xs].
  - rewrite (proj1 (proj2 (be_bytes_def l res (n2w 0) []))), IH; cbn [LENGTH]; lia.
  - rewrite (proj2 (proj2 (be_bytes_def l res x xs))), IH; cbn [LENGTH]; lia.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "num_of_bytes_APPEND" *)
Theorem num_of_bytes_APPEND : forall xs ys,
  num_of_bytes (xs ++ ys) = num_of_bytes xs + 256 ** LENGTH xs * num_of_bytes ys.
Proof.
  induction xs as [|x xs IH]; intros ys; cbn [app num_of_bytes LENGTH].
  - rewrite N.pow_0_r; lia.
  - rewrite IH, N.pow_succ_r'; lia.
Qed.

Lemma w2n_word8_lt (b : word8) : w2n b < 256.
Proof. exact (w2n_lt b). Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "num_of_bytes_DIV_EXP_MOD" *)
Theorem num_of_bytes_DIV_EXP_MOD : forall bs j,
  (num_of_bytes bs DIV (256 ** j)) MOD 256 =
  if j <? LENGTH bs then w2n (EL j bs) else 0.
Proof.
  induction bs as [|b bs IH]; intros j; cbn [num_of_bytes LENGTH].
  - rewrite N.Div0.div_0_l, N.Div0.mod_0_l. destruct (N.ltb_spec j 0); [lia|reflexivity].
  - pose proof (w2n_word8_lt b).
    destruct j as [|j] using N.peano_ind.
    + rewrite N.pow_0_r, N.div_1_r. destruct (N.ltb_spec 0 (SUC (LENGTH bs))); [|lia].
      rewrite (N.mul_comm 256), N.Div0.mod_add, N.mod_small by lia; reflexivity.
    + rewrite N.pow_succ_r', <- N.Div0.div_div.
      rewrite (N.mul_comm 256 (num_of_bytes bs)), N.div_add, (N.div_small (w2n b) 256), N.add_0_l by lia.
      rewrite IH, EL_SUC. cbn [TL].
      destruct (N.ltb_spec j (LENGTH bs)), (N.ltb_spec (SUC j) (SUC (LENGTH bs)));
        try lia; reflexivity.
Qed.

Section Thms5.
Context {a : N}.

(*! HOL "HOL/src/n-bit/byteScript.sml" "first_byte_at_offset" *)
Theorem first_byte_at_offset : forall bs m k j,
  0 < k /\ j < k /\ m < k /\ m <= j /\ k <= dimword a ->
  first_byte_at k j (n2w m : word a) bs =
  if j - m <? LENGTH bs then EL (j - m) bs else n2w 0.
Proof.
  induction bs as [|b bs IH]; intros m k j (H1 & H2 & H3 & H4 & H5).
  - cbn. destruct (N.ltb_spec (j - m) 0); [lia|reflexivity].
  - cbn [first_byte_at]. rewrite w2n_n2w_small, N.mod_small by lia.
    destruct (N.eqb_spec m j).
    + subst; rewrite N.sub_diag. cbn [LENGTH].
      destruct (N.ltb_spec 0 (SUC (LENGTH bs))); [reflexivity|lia].
    + assert (E : (n2w m + n2w 1 : word a)%w = n2w (m + 1)).
      { apply word_eq_w2n; rewrite w2n_add_eq, !w2n_n2w_small by lia; apply N.mod_small; lia. }
      rewrite E, IH by lia. cbn [LENGTH].
      replace (j - m) with (SUC (j - (m + 1))) by lia. rewrite EL_SUC; cbn [TL].
      destruct (N.ltb_spec (j - (m + 1)) (LENGTH bs)),
        (N.ltb_spec (SUC (j - (m + 1))) (SUC (LENGTH bs))); try lia; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "first_byte_at_0w" *)
Theorem first_byte_at_0w : forall k j bs,
  0 < k /\ j < k /\ k <= dimword a ->
  first_byte_at k j (n2w 0 : word a) bs = if j <? LENGTH bs then EL j bs else n2w 0.
Proof.
  intros k j bs (H1 & H2 & H3). rewrite first_byte_at_offset by lia.
  rewrite N.sub_0_r; reflexivity.
Qed.

Lemma get_byte_n2w_0 (a0 : word a) be : get_byte a0 (n2w 0) be = n2w 0.
Proof. apply word_testbit_eq; intros i Hi; wbits; cmp_cases; reflexivity. Qed.

Lemma get_byte_word_of_bytes_gen be : forall bs j (a0 : word a),
  8 <= dimindex a /\ j < dimindex a DIV 8 ->
  get_byte (n2w j) (word_of_bytes be a0 bs) be = first_byte_at (dimindex a DIV 8) j a0 bs.
Proof.
  induction bs as [|b bs IH]; intros j a0 [H1 H2].
  - apply get_byte_n2w_0.
  - cbn [word_of_bytes first_byte_at].
    pose proof (@dimindex_div8_lt a) as Hlt.
    assert (Hj : w2n (n2w j : word a) = j) by (apply w2n_n2w_small; lia).
    destruct (N.eqb_spec (w2n a0 MOD (dimindex a DIV 8)) j) as [E|E].
    + rewrite (set_byte_change_a a0 (n2w j)).
      * apply get_byte_set_byte; exact H1.
      * rewrite Hj, E, N.mod_small by exact H2; reflexivity.
    + assert (H16 : 16 <= dimindex a).
      { destruct (N.le_gt_cases 16 (dimindex a)); [assumption|].
        exfalso. assert (dimindex a DIV 8 = 1) by lia.
        apply E. rewrite H0, N.mod_1_r. lia. }
      rewrite get_byte_set_byte_irrelevant.
      * apply IH; split; assumption.
      * split; [exact H16|]. rewrite Hj, (N.mod_small j) by exact H2. exact E.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "get_byte_word_of_bytes_le" *)
Theorem get_byte_word_of_bytes_le : forall bs j (a0 : word a),
  8 <= dimindex a /\ j < dimindex a DIV 8 ->
  get_byte (n2w j) (word_of_bytes false a0 bs) false =
  first_byte_at (dimindex a DIV 8) j a0 bs.
Proof. apply get_byte_word_of_bytes_gen. Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "get_byte_word_of_bytes_be" *)
Theorem get_byte_word_of_bytes_be : forall bs j (a0 : word a),
  8 <= dimindex a /\ j < dimindex a DIV 8 ->
  get_byte (n2w j) (word_of_bytes true a0 bs) true =
  first_byte_at (dimindex a DIV 8) j a0 bs.
Proof. apply get_byte_word_of_bytes_gen. Qed.

Lemma pow256 i : 256 ** i = 2 ** (8 * i).
Proof. rewrite N.pow_mul_r; reflexivity. Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "get_byte_n2w_le" *)
Theorem get_byte_n2w_le : forall i (w : word a),
  8 <= dimindex a /\ i < dimindex a DIV 8 ->
  get_byte (n2w i : word a) w false = n2w (w2n w DIV 256 ** i).
Proof.
  intros i w [H1 H2]. rewrite pow256.
  apply word_testbit_eq; intros j Hj; rewrite dimindex_8 in Hj; wbits.
  rewrite byte_index_n2w_le by exact H2. rewrite N.div_pow2_bits.
  cmp_cases; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "get_byte_n2w_be" *)
Theorem get_byte_n2w_be : forall i (w : word a),
  8 <= dimindex a /\ i < dimindex a DIV 8 ->
  get_byte (n2w i : word a) w true =
  n2w (w2n w DIV 256 ** (dimindex a DIV 8 - 1 - i)).
Proof.
  intros i w [H1 H2]. rewrite pow256.
  apply word_testbit_eq; intros j Hj; rewrite dimindex_8 in Hj; wbits.
  rewrite byte_index_n2w_be by exact H2. rewrite N.div_pow2_bits.
  cmp_cases; reflexivity.
Qed.

(*! HOL "HOL/src/n-bit/byteScript.sml" "word_eq_of_get_byte" *)
Theorem word_eq_of_get_byte : forall (w1 w2 : word a) be,
  8 <= dimindex a /\ N.divide 8 (dimindex a) ->
  (forall j, j < dimindex a DIV 8 -> get_byte (n2w j) w1 be = get_byte (n2w j) w2 be) ->
  w1 = w2.
Proof.
  intros w1 w2 be [H1 [q Hq]] H.
  set (k := dimindex a DIV 8).
  assert (Ek : k = q) by (unfold k; rewrite Hq, N.div_mul by lia; reflexivity).
  apply word_testbit_eq; intros i Hi.
  assert (Hik : i DIV 8 < k) by (rewrite Ek; apply N.Div0.div_lt_upper_bound; lia).
  idtac.
  pose proof (N.mod_upper_bound i 8 ltac:(lia)) as Hm.
  destruct be.
  - specialize (H (k - 1 - i DIV 8) ltac:(lia)).
    apply (f_equal (fun w => N.testbit (w2n w) (i MOD 8))) in H.
    rewrite !testbit_get_byte, !byte_index_n2w_be in H by (fold k; lia).
    fold k in H. replace (8 * (k - 1 - (k - 1 - i DIV 8))) with (8 * (i DIV 8)) in H by lia.
    replace (i MOD 8 + 8 * (i DIV 8)) with i in H by lia.
    destruct (N.ltb_spec (i MOD 8) 8); [exact H|lia].
  - specialize (H (i DIV 8) ltac:(lia)).
    apply (f_equal (fun w => N.testbit (w2n w) (i MOD 8))) in H.
    rewrite !testbit_get_byte, !byte_index_n2w_le in H by (fold k; lia).
    replace (i MOD 8 + 8 * (i DIV 8)) with i in H by lia.
    destruct (N.ltb_spec (i MOD 8) 8); [exact H|lia].
Qed.

End Thms5.
