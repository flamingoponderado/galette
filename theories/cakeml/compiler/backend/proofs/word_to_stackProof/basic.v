(** * CakeML [word_to_stackProof]: preliminaries

    Part of the port of
    [cakeml/compiler/backend/proofs/word_to_stackProofScript.sml] (HOL lines
    1-700): the [perf = F] instances of the stub/handler code, the
    [set_var] commutations, list lemmas ([LASTN], [index_list],
    [filter_bitmap], [list_LUPDATE], [word_list]).

    Notes:
    - HOL's [LLOOKUP l n] (an overload on [oEL n l] in [misc]) is written
      [oEL n l].
    - HOL's [s with f := v] is [set_f v s]; the stackLang state is
      [stackSem.state], the wordLang state [wordSem.state].
    - [state_with_const] ([t with clock := t.clock = t]) is stated with
      [set_clock].
    - [push_env_set_store] is stated for the [NONE] handler of HOL's
      ML-level abbreviation [nn].
    - [word_shift_or_1], [word_or_eq_0] and [shift_shift_lemma] are word
      facts proved through [w2n]/bit reasoning instead of HOL's
      [bitstring] route.
    - [list_rearrange_I] is stated pointwise ([list_rearrange I l = l]).
    - HOL's ML bindings [the_eqn], [get_labels_def],
      [extract_labels_def], [nn], [s], [t] are not theorems and are not
      ported. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.n_bit.words Require Import lemmas fcp_defs.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend Require Import word_to_stack.
From Galette.cakeml.compiler.backend.semantics Require wordSem.
From Galette.cakeml.compiler.backend.semantics Require Import stackSem.
Import wordLang (word_loc, Word, Loc).
Open Scope N_scope.

Section HandlerF.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "StackHandlerArgs_F" *)
Theorem StackHandlerArgs_F : forall dest arg_count k f f',
  @StackHandlerArgs a false dest arg_count (k, (f, f')) =
    StackArgs dest arg_count (k, (f + 3, f' + 3)).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "PushHandler_F" *)
Theorem PushHandler_F : forall l1 l2 k f f',
  @PushHandler a false l1 l2 (k, (f, f')) =
    Seq (StackAlloc 3)
   (Seq (Inst (asm.Const k (n2w 1)))
   (Seq (StackStore k 0)
   (Seq (LocValue k l1 l2)
   (Seq (StackStore k 1)
   (Seq (Get k Handler)
   (Seq (StackStore k 2)
   (Seq Skip
   (Seq (StackGetSize k)
        (Set_ Handler k))))))))).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "PopHandler_F" *)
Theorem PopHandler_F : forall k f f' prog,
  @PopHandler a false (k, (f, f')) prog =
    Seq (StackLoad k 2)
   (Seq (Set_ Handler k)
   (Seq (StackFree 3) prog)).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "raise_stub_F" *)
Theorem raise_stub_F : forall k,
  @raise_stub a false k =
    Seq (Get k Handler)
   (Seq (StackSetSize k)
   (Seq Skip
   (Seq (StackLoad k 2)
   (Seq (Set_ Handler k)
   (Seq (StackLoad k 1)
   (Seq (StackFree 3)
        (Raise k))))))).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_ret_F" *)
Theorem copy_ret_F : forall is_handle k f f' vs kont,
  @copy_ret a false is_handle (k, (f, f')) vs kont =
    let n := num_stack_ret k vs in
    if n =? 0 then kont
    else Seq (copy_ret_aux k (if is_handle then f + 3 else f) n)
             (SeqStackFree n kont).
Proof. reflexivity. Qed.

End HandlerF.

(** ** State updates *)

Section StateLemmas.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "set_var_swap" *)
Theorem set_var_swap : forall a0 a' b b' (c0 : stackSem.state a c ffi_t),
  a0 <> a' ->
  stackSem.set_var a0 b (stackSem.set_var a' b' c0) = stackSem.set_var a' b' (stackSem.set_var a0 b c0).
Proof.
  intros a0 a' b b' c0 H. unfold stackSem.set_var, set_regs. cbn [regs].
  rewrite FUPDATE_COMMUTES by (intros E; apply H; symmetry; exact E). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "set_var_swap_word" *)
Theorem set_var_swap_word : forall a0 a' b b' (c0 : wordSem.state a c ffi_t),
  a0 <> a' ->
  wordSem.set_var a0 b (wordSem.set_var a' b' c0) = wordSem.set_var a' b' (wordSem.set_var a0 b c0).
Proof.
  intros a0 a' b b' c0 H. unfold wordSem.set_var, wordSem.set_locals. cbn [wordSem.locals].
  rewrite insert_swap by exact H. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "set_var_cancel" *)
Theorem set_var_cancel : forall a0 b b' (t : stackSem.state a c ffi_t),
  stackSem.set_var a0 b (stackSem.set_var a0 b' t) = stackSem.set_var a0 b t.
Proof.
  intros a0 b b' t. unfold stackSem.set_var, set_regs. cbn [regs].
  rewrite FUPDATE_EQ. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "set_var_cancel_word" *)
Theorem set_var_cancel_word : forall a0 b b' (s : wordSem.state a c ffi_t),
  wordSem.set_var a0 b (wordSem.set_var a0 b' s) = wordSem.set_var a0 b s.
Proof.
  intros a0 b b' s. unfold wordSem.set_var, wordSem.set_locals. cbn [wordSem.locals].
  rewrite insert_shadow. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "get_var_set_var" *)
Theorem get_var_set_var : forall k v (st : stackSem.state a c ffi_t),
  stackSem.get_var k (stackSem.set_var k v st) = SOME v.
Proof.
  intros k v st. unfold stackSem.get_var, stackSem.set_var. cbn [regs set_regs].
  rewrite FLOOKUP_UPDATE. destruct (decide (k = k)) as [_|n]; [reflexivity|contradiction].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_with_const" *)
Theorem state_with_const : forall (t : stackSem.state a c ffi_t), set_clock (clock t) t = t.
Proof. intros []; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "set_store_set_var" *)
Theorem set_store_set_var : forall a0 b c0 d (e : stackSem.state a c ffi_t),
  stackSem.set_store a0 b (stackSem.set_var c0 d e) = stackSem.set_var c0 d (stackSem.set_store a0 b e).
Proof. reflexivity. Qed.

End StateLemmas.

(** ** Galette-only list helpers *)

Lemma LENGTH_app' {A} (l1 l2 : list A) : LENGTH (l1 ++ l2) = LENGTH l1 + LENGTH l2.
Proof. rewrite !LENGTH_length, length_app; lia. Qed.

Lemma LENGTH_cons' {A} (x : A) l : LENGTH (x :: l) = LENGTH l + 1.
Proof. rewrite !LENGTH_length; cbn [length]; lia. Qed.

(** ** Lists *)

Section Lists.
Context {A : Type}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DROP_DROP_EQ" *)
Theorem DROP_DROP_EQ : forall n m (xs : list A), DROP m (DROP n xs) = DROP (m + n) xs.
Proof. intros n m xs. rewrite !DROP_skipn, skipn_skipn. f_equal. lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "TAKE_TAKE_MIN" *)
Theorem TAKE_TAKE_MIN : forall (xs : list A) m n, TAKE n (TAKE m xs) = TAKE (MIN m n) xs.
Proof.
  intros xs m n. rewrite !TAKE_firstn, firstn_firstn, MIN_min. f_equal. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "TAKE_DROP_EQ" *)
Theorem TAKE_DROP_EQ : forall (xs : list A) n m, TAKE m (DROP n xs) = DROP n (TAKE (m + n) xs).
Proof.
  intros xs n m. rewrite !TAKE_firstn, !DROP_skipn, skipn_firstn_comm. f_equal. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DROP_TAKE_NIL" *)
Theorem DROP_TAKE_NIL : forall n (xs : list A), DROP n (TAKE n xs) = [].
Proof.
  intros n xs. rewrite TAKE_firstn, DROP_skipn. apply skipn_all2. rewrite length_firstn. lia.
Qed.

End Lists.

Lemma MAX_LIST_snoc l x : MAX_LIST (l ++ [x]) = MAX (MAX_LIST l) x.
Proof.
  induction l as [|y l IH]; cbn [MAX_LIST app]; rewrite ?MAX_max in *; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAX_LIST_GENLIST_evens" *)
Theorem MAX_LIST_GENLIST_evens : forall n, MAX_LIST (GENLIST (fun x => 2 * x) n) = 2 * (n - 1).
Proof.
  induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (GENLIST_thm _ n)), SNOC_app, MAX_LIST_snoc, IH, MAX_max. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAX_LIST_GENLIST_evens2" *)
Theorem MAX_LIST_GENLIST_evens2 : forall n, MAX_LIST (GENLIST (fun x => 2 * (x + 1)) n) = 2 * n.
Proof.
  induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (GENLIST_thm _ n)), SNOC_app, MAX_LIST_snoc, IH, MAX_max. lia.
Qed.

(** ** Words *)

Section Words.
Context {a : N}.
Local Open Scope word_scope.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_or_eq_0" *)
Theorem word_or_eq_0 : forall (w v : word a), (w || v) = n2w 0 <-> w = n2w 0 /\ v = n2w 0.
Proof.
  intros w v. rewrite <- !word_bit_ext_iff. split.
  - intros H. split; intros i Hi; specialize (H i Hi); rewrite fcp_index_word_or in H by exact Hi;
      rewrite fcp_index_n2w in * by exact Hi; destruct (w ' i), (v ' i); cbn in *; auto.
  - intros [H1 H2] i Hi. rewrite fcp_index_word_or, H1, H2 by exact Hi. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "shift_shift_lemma" *)
Theorem shift_shift_lemma : forall (w : word a), ~ is_true (word_msb w) -> (w << 1 >>> 1) = w.
Proof.
  intros w Hm. apply word_bit_ext. intros i Hi.
  rewrite fcp_index_word_lsr by exact Hi.
  destruct (N.ltb_spec (i + 1) (dimindex a)) as [H1|H1]; cbn [andb].
  - rewrite fcp_index_word_lsl by exact H1. replace (1 <=? i + 1)%N with true by (symmetry; apply N.leb_le; lia).
    cbn [andb]. f_equal. lia.
  - rewrite word_msb_def in Hm. replace i with (dimindex a - 1)%N by lia.
    destruct (w ' (dimindex a - 1)%N); [exfalso; apply Hm; reflexivity|reflexivity].
Qed.

Lemma lor_even_1 e : N.even e = true -> N.lor e 1 = (e + 1)%N.
Proof.
  intros He. apply N.even_spec in He as [q ->]. apply N.bits_inj. intros i.
  rewrite N.lor_spec. destruct i as [|i] using N.peano_ind.
  - rewrite N.testbit_odd_0, N.testbit_even_0. reflexivity.
  - rewrite N.testbit_odd_succ, N.testbit_even_succ by lia.
    replace (N.testbit 1 (N.succ i)) with false; [apply orb_false_r|].
    symmetry. rewrite <- N.div2_bits by lia. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_shift_or_1" *)
Theorem word_shift_or_1 : forall (n : word a), ((n << 1) || n2w 1) = (n << 1) + n2w 1.
Proof.
  intros n. pose proof (@dimindex_pos a) as Hd. unfold word_lsl.
  destruct (N.ltb_spec (dimindex a - 1)%N 1) as [H|H].
  - unfold word_or, word_add. rewrite !w2n_n2w, N.Div0.mod_0_l by (unfold dimword; lia). reflexivity.
  - unfold word_or, word_add. rewrite !w2n_n2w.
    assert (HD : (2 <= dimword a)%N).
    { unfold dimword. replace (dimindex a) with (N.succ (dimindex a - 1)%N) by lia.
      rewrite N.pow_succ_r'. pose proof (N.pow_nonzero 2 (dimindex a - 1)). lia. }
    rewrite (N.mod_small 1) by lia. rewrite lor_even_1.
    + rewrite <- n2w_mod, N.Div0.add_mod_idemp_l by lia. rewrite n2w_mod. reflexivity.
    + assert (E : N.even (dimword a) = true).
      { unfold dimword. replace (dimindex a) with (N.succ (dimindex a - 1)%N) by lia.
        rewrite N.pow_succ_r'. apply N.even_spec. eexists; reflexivity. }
      apply N.even_spec in E as [d Ed]. apply N.even_spec.
      rewrite (N.mul_comm _ (2 ^ 1)%N), N.pow_1_r, Ed, N.Div0.mul_mod_distr_l by lia. eexists; reflexivity.
Qed.

End Words.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "push_env_set_store" *)
Theorem push_env_set_store : forall {a c ffi_t} env c0 (s : wordSem.state a c ffi_t),
  wordSem.push_env env NONE (wordSem.set_store AllocSize (Word c0) s) =
  wordSem.set_store AllocSize (Word c0) (wordSem.push_env env NONE s).
Proof.
  intros a c ffi_t env c0 s. unfold wordSem.push_env. cbv zeta.
  destruct (wordSem.env_to_list _ _) as [l perm] eqn:E. reflexivity.
Qed.

(** ** [LASTN], [oEL] *)

Lemma oEL_nth_error {A} n (l : list A) : oEL n l = nth_error l (N.to_nat n).
Proof.
  revert n; induction l as [|x l IH]; intros n; cbn [oEL]; [destruct (N.to_nat n); reflexivity|].
  destruct (N.eqb_spec n 0) as [->|Hn]; [reflexivity|].
  rewrite IH. replace (N.to_nat n) with (Datatypes.S (N.to_nat (n - 1))) by lia. reflexivity.
Qed.

Section Lastn.
Context {A : Type}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LASTN_DROP2" *)
Theorem LASTN_DROP2 : forall (l : list A) n, LASTN n l = DROP (LENGTH l - n) l.
Proof.
  intros l n. unfold LASTN. rewrite TAKE_firstn, DROP_skipn, firstn_rev, rev_involutive, LENGTH_length.
  f_equal. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LASTN_MORE" *)
Theorem LASTN_MORE : forall (ls : list A) n, ~ (n < LENGTH ls) -> LASTN n ls = ls.
Proof. intros ls n H. rewrite LASTN_DROP2. replace (LENGTH ls - n) with 0 by lia. rewrite DROP_skipn. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LASTN_LENGTH_BOUNDS" *)
Theorem LASTN_LENGTH_BOUNDS : forall n (ls : list A),
  let xs := LASTN n ls in LENGTH xs <= n /\ LENGTH xs <= LENGTH ls.
Proof.
  intros n ls. cbv zeta. rewrite LASTN_DROP2, DROP_skipn, !LENGTH_length, length_skipn. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LASTN_CONS_ID" *)
Theorem LASTN_CONS_ID : forall n (ls : list A) frame,
  n = LENGTH ls -> LASTN (SUC n) (frame :: ls) = frame :: ls.
Proof. intros n ls frame ->. apply LASTN_MORE. rewrite LENGTH_cons'. lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "EVERY_IMP_EVERY_LASTN" *)
Theorem EVERY_IMP_EVERY_LASTN : forall n (xs ys : list A) (P : A -> bool),
  EVERY P xs /\ LASTN n xs = ys -> EVERY P ys.
Proof.
  intros n xs ys P [H <-]. rewrite LASTN_DROP2, DROP_skipn. unfold is_true in *.
  rewrite EVERY_Forall in *. rewrite Forall_forall in *. intros x Hx. apply H.
  rewrite <- (firstn_skipn (N.to_nat (LENGTH xs - n)) xs). apply in_or_app. right. exact Hx.
Qed.

Context `{Inhabited A}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LASTN_LENGTH_ID2" *)
Theorem LASTN_LENGTH_ID2 : forall (stack : list A) x,
  x + 1 = LENGTH stack -> LASTN (x + 1) stack = HD stack :: LASTN x stack.
Proof.
  intros [|h t] x Hx; [cbn in Hx; lia|]. rewrite !LASTN_DROP2, LENGTH_cons' in *.
  replace (LENGTH t + 1 - (x + 1)) with 0 by lia. replace (LENGTH t + 1 - x) with 1 by lia.
  rewrite !DROP_skipn. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LASTN_HD" *)
Theorem LASTN_HD : forall (ls : list A) x,
  x <= LENGTH ls -> HD (LASTN x ls) = EL (LENGTH ls - x) ls.
Proof.
  intros ls x Hx. rewrite LASTN_DROP2. remember (LENGTH ls - x) as m eqn:Em. clear Em Hx.
  revert m; induction ls as [|y ls IH]; intros m.
  { cbn [DROP]. induction m as [|m IHm] using N.peano_ind; [reflexivity|]. rewrite EL_SUC. exact IHm. }
  cbn [DROP]. destruct (N.eqb_spec m 0) as [->|Hm]; [reflexivity|].
  rewrite IH. replace m with (SUC (m - 1)) at 2 by lia. rewrite EL_SUC. reflexivity.
Qed.

End Lastn.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LLOOKUP_TAKE" *)
Theorem LLOOKUP_TAKE : forall {A} n f (xs : list A), n < f -> oEL n (TAKE f xs) = oEL n xs.
Proof.
  intros A n f xs H. rewrite !oEL_nth_error, TAKE_firstn, nth_error_firstn.
  destruct (Nat.ltb_spec (N.to_nat n) (N.to_nat f)); [reflexivity|lia].
Qed.

(** ** Galette-only [GENLIST]/[EL] bridges *)

Lemma GENLIST_seq {A} (f : N -> A) n :
  GENLIST f n = List.map (fun i => f (N.of_nat i)) (List.seq 0 (N.to_nat n)).
Proof.
  induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (GENLIST_thm f n)), SNOC_app, IH, N2Nat.inj_succ, seq_S, map_app. cbn.
  rewrite N2Nat.id. reflexivity.
Qed.

Lemma LENGTH_GENLIST_N {A} (f : N -> A) n : LENGTH (GENLIST f n) = n.
Proof. rewrite GENLIST_seq, LENGTH_length, length_map, length_seq. lia. Qed.

Lemma EL_nth' {A} `{Inhabited A} n (l : list A) : EL n l = nth (N.to_nat n) l ARB.
Proof.
  revert l; induction n as [|n IH] using N.peano_ind; intros [|h t]; try reflexivity.
  - rewrite EL_SUC. cbn [TL]. rewrite IH. destruct (N.to_nat n) eqn:E; cbn; destruct (N.to_nat (N.succ n)); reflexivity.
  - rewrite EL_SUC, N2Nat.inj_succ. cbn [TL nth]. apply IH.
Qed.

Lemma GENLIST_EL_id {A} `{Inhabited A} (xs : list A) : GENLIST (fun i => EL i xs) (LENGTH xs) = xs.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  rewrite LENGTH_cons', N.add_1_r, GENLIST_CONS_aux. f_equal.
  rewrite <- IH at 2. rewrite !GENLIST_seq. apply map_ext. intros i. rewrite EL_SUC. reflexivity.
Qed.

(** ** [index_list] *)

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "index_list_def" *)
Fixpoint index_list {A} (l : list A) (n : N) : list (N * A) :=
  match l with
  | [] => []
  | x :: xs => (n + LENGTH xs, x) :: index_list xs n
  end.

Section IndexList.
Context {A : Type}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LENGTH_index_list" *)
Theorem LENGTH_index_list : forall (l : list A) n, LENGTH (index_list l n) = LENGTH l.
Proof. induction l as [|x l IH]; intros n; [reflexivity|]. cbn [index_list]. rewrite !LENGTH_cons', IH. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAP_SND_index_list" *)
Theorem MAP_SND_index_list : forall (xs : list A) k, MAP SND (index_list xs k) = xs.
Proof. induction xs as [|x xs IH]; intros k; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAP_FST_index_list" *)
Theorem MAP_FST_index_list : forall (xs : list A) k,
  MAP FST (index_list xs k) = REVERSE (MAP (fun x => k + x) (COUNT_LIST (LENGTH xs))).
Proof.
  induction xs as [|x xs IH]; intros k; [reflexivity|]. cbn [index_list MAP List.map FST fst].
  rewrite IH, LENGTH_cons', (COUNT_LIST_GENLIST (LENGTH xs + 1)), COUNT_LIST_GENLIST, !GENLIST_seq. replace (N.to_nat (LENGTH xs + 1)) with
    (Datatypes.S (N.to_nat (LENGTH xs))) by lia.
  rewrite seq_S, !map_app, rev_app_distr. cbn. rewrite N2Nat.id, map_map. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "index_list_eq_ZIP" *)
Theorem index_list_eq_ZIP : forall (xs : list A) k,
  index_list xs k = ZIP (REVERSE (MAP (fun x => k + x) (COUNT_LIST (LENGTH xs))), xs).
Proof.
  intros xs k. rewrite <- MAP_FST_index_list.
  assert (Z : forall l : list (N * A), ZIP (MAP FST l, MAP SND l) = l).
  { induction l as [|[u v] l IH]; [reflexivity|]. cbn. f_equal. exact IH. }
  rewrite <- (Z (index_list xs k)) at 1. rewrite MAP_SND_index_list. reflexivity.
Qed.

Context {HA : EqDecision A}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MEM_index_list_LIM" *)
Theorem MEM_index_list_LIM : forall (ls : list A) n v k,
  MEM (n, v) (index_list ls k) -> n - k < LENGTH ls.
Proof.
  induction ls as [|x ls IH]; intros n v k H; [discriminate|].
  cbn [index_list] in H. unfold is_true in H. rewrite MEM_In in H. destruct H as [E|H].
  - injection E as <- <-. rewrite LENGTH_cons'. lia.
  - rewrite <- MEM_In in H. apply IH in H. rewrite LENGTH_cons'. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "ALOOKUP_index_list" *)
Theorem ALOOKUP_index_list : forall (ls : list A) n k,
  n < LENGTH ls + k ->
  ALOOKUP (index_list ls k) n = oEL ((LENGTH ls + k) - (n + 1)) ls.
Proof.
  induction ls as [|x ls IH]; intros n k H; [reflexivity|].
  cbn [index_list ALOOKUP oEL]. rewrite LENGTH_cons' in *.
  destruct (decide (k + LENGTH ls = n)) as [E|E].
  - replace (LENGTH ls + 1 + k - (n + 1) =? 0) with true by (symmetry; apply N.eqb_eq; lia). reflexivity.
  - replace (LENGTH ls + 1 + k - (n + 1) =? 0) with false by (symmetry; apply N.eqb_neq; lia).
    destruct (N.ltb_spec n (LENGTH ls + k)) as [Hn|Hn].
    + rewrite IH by exact Hn. f_equal. lia.
    + assert (Hk : n < k) by lia.
      replace (LENGTH ls + 1 + k - (n + 1) - 1) with (LENGTH ls + (k - n - 1)) by lia.
      rewrite oEL_nth_error, (proj2 (nth_error_None _ _)) by (rewrite LENGTH_length in *; lia).
      clear IH H E Hn. induction ls as [|y ls IH2]; [reflexivity|]. cbn [index_list ALOOKUP].
      destruct (decide (k + LENGTH ls = n)); [lia|]. exact IH2.
Qed.

Context {HI : Inhabited A}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "EL_index_list" *)
Theorem EL_index_list : forall (xs : list A) i k,
  i < LENGTH xs -> EL i (index_list xs k) = (k + LENGTH xs - i - 1, EL i xs).
Proof.
  induction xs as [|x xs IH]; intros i k H; [cbn in H; lia|]. rewrite LENGTH_cons' in *.
  destruct i as [|i] using N.peano_ind; [cbn; f_equal; lia|].
  rewrite !EL_SUC. cbn [TL index_list]. rewrite IH by lia. f_equal. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "EL_index_list2" *)
Theorem EL_index_list2 : forall (xs : list A) i k,
  i < LENGTH xs -> EL i (index_list xs k) = (k + LENGTH xs - (i + 1), EL i xs).
Proof. intros xs i k H. rewrite EL_index_list by exact H. f_equal. lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MEM_index_list_EL" *)
Theorem MEM_index_list_EL : forall k (ls : list A) n v,
  MEM (n, v) (index_list ls k) -> EL (LENGTH ls - (n - k + 1)) ls = v.
Proof.
  intros k; induction ls as [|x ls IH]; intros n v H; [discriminate|].
  pose proof (MEM_index_list_LIM _ _ _ _ H) as Hl.
  cbn [index_list] in H. unfold is_true in H. rewrite MEM_In in H. rewrite LENGTH_cons' in *.
  destruct H as [E|H].
  - injection E as <- <-. replace (LENGTH ls + 1 - (k + LENGTH ls - k + 1)) with 0 by lia. reflexivity.
  - assert (Hm := H). rewrite <- MEM_In in Hm. pose proof (MEM_index_list_LIM _ _ _ _ Hm) as Hl2.
    apply IH in Hm. replace (LENGTH ls + 1 - (n - k + 1)) with (SUC (LENGTH ls - (n - k + 1))) by lia.
    rewrite EL_SUC. exact Hm.
Qed.

End IndexList.

(** ** [filter_bitmap] *)

Section FilterBitmap.
Context {A B : Type}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "IMP_filter_bitmap_EQ_SOME_NIL" *)
Theorem IMP_filter_bitmap_EQ_SOME_NIL : forall (xs : list bool) (ys zs : list A),
  LENGTH xs = LENGTH ys /\ zs = MAP FST (FILTER SND (ZIP (ys, xs))) ->
  filter_bitmap xs ys = SOME (zs, []).
Proof.
  induction xs as [|b xs IH]; intros [|y ys] zs [Hl ->]; rewrite ?LENGTH_cons' in Hl; try (cbn in Hl; lia);
    [reflexivity|].
  destruct b; cbn [filter_bitmap ZIP FILTER SND snd];
    rewrite (IH ys (MAP FST (FILTER SND (ZIP (ys, xs))))) by (split; [lia|reflexivity]); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "filter_bitmap_length" *)
Theorem filter_bitmap_length : forall (bs : list bool) (ls xs ys : list A),
  filter_bitmap bs ls = SOME (xs, ys) -> LENGTH xs <= LENGTH bs.
Proof.
  induction bs as [|b bs IH]; intros ls xs ys H; [cbn in H; injection H as <- <-; reflexivity|].
  destruct ls as [|l ls]; [destruct b; discriminate|]. rewrite LENGTH_cons'.
  destruct b; cbn in H.
  - destruct (filter_bitmap bs ls) as [[ts rs]|] eqn:E; [|discriminate].
    injection H as <- <-. apply IH in E. rewrite LENGTH_cons'. lia.
  - apply IH in H. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "filter_bitmap_length_input" *)
Theorem filter_bitmap_length_input : forall (xs : list bool) (ys : list A) ls,
  filter_bitmap xs ys = SOME ls -> LENGTH xs <= LENGTH ys.
Proof.
  induction xs as [|b xs IH]; intros ys ls H; [cbn; lia|].
  destruct ys as [|y ys]; [destruct b; discriminate|]. rewrite !LENGTH_cons'.
  destruct b; cbn in H.
  - destruct (filter_bitmap xs ys) as [[ts rs]|] eqn:E; [|discriminate]. apply IH in E. lia.
  - apply IH in H. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "filter_bitmap_MAP_IMP" *)
Theorem filter_bitmap_MAP_IMP : forall (ys : list bool) (xs l : list (A * B)),
  filter_bitmap ys (MAP SND xs) = SOME (MAP SND l, []) /\
  filter_bitmap ys (MAP FST xs) = SOME (MAP FST l, []) ->
  filter_bitmap ys xs = SOME (l, []).
Proof.
  induction ys as [|b ys IH]; intros [|x xs] l [H1 H2].
  - cbn in *. injection H1 as H1. destruct l; [reflexivity|discriminate].
  - cbn in *. injection H1 as H1. destruct l; [discriminate|discriminate].
  - destruct b; discriminate.
  - destruct b; cbn in H1, H2 |- *.
    + destruct (filter_bitmap ys (MAP SND xs)) as [[t1 r1]|] eqn:E1; [|discriminate].
      destruct (filter_bitmap ys (MAP FST xs)) as [[t2 r2]|] eqn:E2; [|discriminate].
      destruct l as [|[u v] l]; [discriminate|]. cbn in H1, H2.
      injection H1 as Hv H1 ->. injection H2 as Hu H2 ->. subst t1 t2.
      rewrite (IH xs l (conj E1 E2)). destruct x; cbn in *; subst; reflexivity.
    + apply IH. split; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "filter_bitmap_IMP_MAP_SND" *)
Theorem filter_bitmap_IMP_MAP_SND : forall (ys : list bool) (xs l : list (A * B)),
  filter_bitmap ys xs = SOME (l, []) -> filter_bitmap ys (MAP SND xs) = SOME (MAP SND l, []).
Proof.
  induction ys as [|b ys IH]; intros [|x xs] l H.
  - cbn in *. injection H as <-. reflexivity.
  - cbn in *. discriminate.
  - destruct b; discriminate.
  - destruct b; cbn in H |- *.
    + destruct (filter_bitmap ys xs) as [[t r]|] eqn:E; [|discriminate].
      injection H as <- ->. rewrite (IH _ _ E). reflexivity.
    + apply IH, H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "filter_bitmap_IMP_MAP_FST" *)
Theorem filter_bitmap_IMP_MAP_FST : forall (ys : list bool) (xs l : list (A * B)),
  filter_bitmap ys xs = SOME (l, []) -> filter_bitmap ys (MAP FST xs) = SOME (MAP FST l, []).
Proof.
  induction ys as [|b ys IH]; intros [|x xs] l H.
  - cbn in *. injection H as <-. reflexivity.
  - cbn in *. discriminate.
  - destruct b; discriminate.
  - destruct b; cbn in H |- *.
    + destruct (filter_bitmap ys xs) as [[t r]|] eqn:E; [|discriminate].
      injection H as <- ->. rewrite (IH _ _ E). reflexivity.
    + apply IH, H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "filter_bitmap_TAKE_LENGTH_IMP" *)
Theorem filter_bitmap_TAKE_LENGTH_IMP : forall (h5 : list bool) (x4 : list B) (l : list (A * B)),
  filter_bitmap h5 (TAKE (LENGTH h5) x4) = SOME (MAP SND l, []) ->
  filter_bitmap h5 x4 = SOME (MAP SND l, DROP (LENGTH h5) x4).
Proof.
  induction h5 as [|b h5 IH]; intros [|x x4] l H.
  - cbn in *. injection H as H. rewrite <- H. reflexivity.
  - cbn in *. injection H as H. rewrite <- H. reflexivity.
  - destruct b; discriminate.
  - rewrite LENGTH_cons' in *. cbn [TAKE DROP] in *.
    replace (LENGTH h5 + 1 =? 0) with false in * by (symmetry; apply N.eqb_neq; lia).
    replace (LENGTH h5 + 1 - 1) with (LENGTH h5) in * by lia.
    destruct b; cbn in H |- *.
    + destruct (filter_bitmap h5 (TAKE (LENGTH h5) x4)) as [[t r]|] eqn:E; [|discriminate].
      injection H as Ht ->. destruct l as [|[u v] l]; [discriminate|]. cbn in Ht.
      injection Ht as -> ->. rewrite (IH x4 l E). reflexivity.
    + apply IH, H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "filter_bitmap_MEM" *)
Theorem filter_bitmap_MEM : forall `{EqDecision A} (b : list bool) (ls ls' : list A) x,
  filter_bitmap b ls = SOME (ls', []) /\ MEM x ls' -> MEM x ls.
Proof.
  intros HE b; induction b as [|c b IH]; intros ls ls' x [H Hm].
  - cbn in H. injection H as <- ->. exact Hm.
  - destruct ls as [|y ls]; [destruct c; discriminate|]. unfold is_true in *. rewrite MEM_In in *. cbn.
    destruct c; cbn in H.
    + destruct (filter_bitmap b ls) as [[t r]|] eqn:E; [|discriminate]. injection H as <- ->.
      destruct Hm as [->|Hm]; [left; reflexivity|right]. rewrite <- MEM_In in *. apply (IH ls t). auto.
    + right. rewrite <- MEM_In in *. apply (IH ls ls'). auto.
Qed.

End FilterBitmap.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "filter_bitmap_lemma" *)
Theorem filter_bitmap_lemma : forall {B} (h5 : list bool) (x4 : list B) k (l : list (N * B)),
  filter_bitmap h5 (index_list (TAKE (LENGTH h5) x4) k) = SOME (l, []) ->
  filter_bitmap h5 x4 = SOME (MAP SND l, DROP (LENGTH h5) x4).
Proof.
  intros B h5 x4 k l H. apply filter_bitmap_IMP_MAP_SND in H. rewrite MAP_SND_index_list in H.
  apply filter_bitmap_TAKE_LENGTH_IMP. exact H.
Qed.


(** ** [LUPDATE], [list_LUPDATE] *)

Section LUpdate.
Context {A : Type}.

Lemma LUPDATE_cons_eq (x y : A) xs n :
  LUPDATE x n (y :: xs) = if n =? 0 then x :: xs else y :: LUPDATE x (n - 1) xs.
Proof. cbn [LUPDATE]. destruct (n =? 0); [reflexivity|]. unfold PRE. rewrite N.sub_1_r. reflexivity. Qed.

Lemma LENGTH_LUPDATE' (x : A) n xs : LENGTH (LUPDATE x n xs) = LENGTH xs.
Proof.
  revert n; induction xs as [|y xs IH]; intros n; [reflexivity|].
  rewrite LUPDATE_cons_eq. destruct (n =? 0); rewrite !LENGTH_cons', ?IH; reflexivity.
Qed.

Lemma LUPDATE_nil (x : A) n : LUPDATE x n [] = [].
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "TAKE_LUPDATE" *)
Theorem TAKE_LUPDATE : forall (xs : list A) n x i, TAKE n (LUPDATE x i xs) = LUPDATE x i (TAKE n xs).
Proof.
  induction xs as [|y xs IH]; intros n x i; [reflexivity|].
  rewrite LUPDATE_cons_eq. destruct (N.eqb_spec n 0) as [->|Hn]; [destruct (i =? 0); reflexivity|].
  assert (E : (n =? 0) = false) by (apply N.eqb_neq; exact Hn).
  cbn [TAKE]. rewrite E, LUPDATE_cons_eq. destruct (i =? 0); cbn [TAKE]; rewrite ?E; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DROP_LUPDATE_lemma1" *)
Theorem DROP_LUPDATE_lemma1 : forall (xs : list A) n m h,
  n <= m -> DROP n (LUPDATE h m xs) = LUPDATE h (m - n) (DROP n xs).
Proof.
  induction xs as [|y xs IH]; intros n m h Hnm; [reflexivity|].
  destruct (N.eqb_spec n 0) as [->|Hn].
  { rewrite N.sub_0_r, !DROP_skipn. reflexivity. }
  rewrite LUPDATE_cons_eq. cbn [DROP].
  - replace (m =? 0) with false by (symmetry; apply N.eqb_neq; lia). cbn [DROP].
    replace (n =? 0) with false by (symmetry; apply N.eqb_neq; lia).
    rewrite IH by lia. f_equal. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DROP_LUPDATE_lemma2" *)
Theorem DROP_LUPDATE_lemma2 : forall (xs : list A) n m h,
  m < n -> DROP n (LUPDATE h m xs) = DROP n xs.
Proof.
  induction xs as [|y xs IH]; intros n m h Hnm; [reflexivity|].
  rewrite LUPDATE_cons_eq. replace (n =? 0) with false by (symmetry; apply N.eqb_neq; lia).
  destruct (N.eqb_spec m 0) as [->|Hm]; cbn [DROP];
    replace (n =? 0) with false by (symmetry; apply N.eqb_neq; lia); [reflexivity|].
  apply IH. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DROP_LUPDATE" *)
Theorem DROP_LUPDATE : forall n (h : A) m xs,
  DROP n (LUPDATE h m xs) = if m <? n then DROP n xs else LUPDATE h (m - n) (DROP n xs).
Proof.
  intros n h m xs. destruct (N.ltb_spec m n).
  - apply DROP_LUPDATE_lemma2. exact H.
  - apply DROP_LUPDATE_lemma1. exact H.
Qed.

End LUpdate.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MIN_ADD" *)
Theorem MIN_ADD : forall m1 m2 n, MIN m1 m2 + n = MIN (m1 + n) (m2 + n).
Proof. intros. rewrite !MIN_min. lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "list_LUPDATE_def" *)
Fixpoint list_LUPDATE {A} (xs : list A) (n : N) (ys : list A) : list A :=
  match xs with
  | [] => ys
  | x :: xs => list_LUPDATE xs (n + 1) (LUPDATE x n ys)
  end.

Section ListLUpdate.
Context {A : Type}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LENGTH_list_LUPDATE" *)
Theorem LENGTH_list_LUPDATE : forall (xs : list A) n ys, LENGTH (list_LUPDATE xs n ys) = LENGTH ys.
Proof. induction xs as [|x xs IH]; intros n ys; [reflexivity|]. cbn. rewrite IH. apply LENGTH_LUPDATE'. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "TAKE_list_LUPDATE" *)
Theorem TAKE_list_LUPDATE : forall (ys : list A) xs n i,
  TAKE n (list_LUPDATE ys i xs) = list_LUPDATE ys i (TAKE n xs).
Proof. induction ys as [|y ys IH]; intros xs n i; [reflexivity|]. cbn. rewrite IH, TAKE_LUPDATE. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LLOOKUP_list_LUPDATE_IGNORE" *)
Theorem LLOOKUP_list_LUPDATE_IGNORE : forall (xs : list A) i n ys,
  i + LENGTH xs <= n -> oEL n (list_LUPDATE xs i ys) = oEL n ys.
Proof.
  induction xs as [|x xs IH]; intros i n ys H; [reflexivity|]. rewrite LENGTH_cons' in H. cbn.
  rewrite IH by lia. rewrite !oEL_nth_error. clear IH. revert i n H; induction ys as [|y ys IH2];
    intros i n H; [reflexivity|].
  rewrite LUPDATE_cons_eq. destruct (N.eqb_spec i 0) as [->|Hi].
  - replace (N.to_nat n) with (Datatypes.S (N.to_nat (n - 1))) by lia. reflexivity.
  - replace (N.to_nat n) with (Datatypes.S (N.to_nat (n - 1))) by lia. cbn [nth_error].
    rewrite <- !oEL_nth_error. rewrite !oEL_nth_error. apply (IH2 (i - 1)). lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DROP_list_LUPDATE" *)
Theorem DROP_list_LUPDATE : forall (ys : list A) n m xs,
  n <= m -> DROP n (list_LUPDATE ys m xs) = list_LUPDATE ys (m - n) (DROP n xs).
Proof.
  induction ys as [|y ys IH]; intros n m xs H; [reflexivity|]. cbn [list_LUPDATE].
  rewrite IH by lia. rewrite DROP_LUPDATE. replace (m <? n) with false by (symmetry; apply N.ltb_ge; lia).
  f_equal. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DROP_list_LUPDATE_IGNORE" *)
Theorem DROP_list_LUPDATE_IGNORE : forall (xs : list A) i ys n,
  LENGTH xs + i <= n -> DROP n (list_LUPDATE xs i ys) = DROP n ys.
Proof.
  induction xs as [|x xs IH]; intros i ys n H; [reflexivity|]. rewrite LENGTH_cons' in H. cbn [list_LUPDATE].
  rewrite IH by lia. rewrite DROP_LUPDATE. replace (i <? n) with true by (symmetry; apply N.ltb_lt; lia).
  reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "list_LUPDATE_NIL" *)
Theorem list_LUPDATE_NIL : forall (xs : list A) i, list_LUPDATE xs i [] = [].
Proof. induction xs as [|x xs IH]; intros i; [reflexivity|]. cbn. apply IH. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LUPDATE_TAKE_LEMMA" *)
Theorem LUPDATE_TAKE_LEMMA : forall (xs : list A) n w, LUPDATE w n xs = TAKE n xs ++ LUPDATE w 0 (DROP n xs).
Proof.
  induction xs as [|x xs IH]; intros n w; [reflexivity|].
  rewrite LUPDATE_cons_eq. cbn [TAKE DROP]. destruct (n =? 0); [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma length_LUPDATE' (x : A) n ys : length (LUPDATE x n ys) = length ys.
Proof. pose proof (LENGTH_LUPDATE' x n ys) as H. rewrite !LENGTH_length in H. lia. Qed.

Lemma nth_LUPDATE' (x : A) n ys j d : (j < length ys)%nat ->
  nth j (LUPDATE x n ys) d = if Nat.eqb j (N.to_nat n) then x else nth j ys d.
Proof.
  revert n j; induction ys as [|y ys IH]; intros n j Hj; [cbn in Hj; lia|].
  rewrite LUPDATE_cons_eq. destruct (N.eqb_spec n 0) as [->|Hn].
  - destruct j; reflexivity.
  - destruct j as [|j]; [cbn; destruct (N.to_nat n) eqn:E; [lia|reflexivity]|].
    cbn [nth]. rewrite IH by (cbn in Hj; lia).
    replace (Nat.eqb (Datatypes.S j) (N.to_nat n)) with (Nat.eqb j (N.to_nat (n - 1))); [reflexivity|].
    apply Bool.eq_true_iff_eq. rewrite !Nat.eqb_eq. lia.
Qed.

Lemma length_list_LUPDATE (xs : list A) n ys : length (list_LUPDATE xs n ys) = length ys.
Proof. pose proof (LENGTH_list_LUPDATE xs n ys) as H. rewrite !LENGTH_length in H. lia. Qed.

Lemma nth_list_LUPDATE (xs : list A) n ys j d : (j < length ys)%nat ->
  nth j (list_LUPDATE xs n ys) d =
  if (N.to_nat n <=? j)%nat && (j <? N.to_nat n + length xs)%nat then nth (j - N.to_nat n) xs d
  else nth j ys d.
Proof.
  revert n ys; induction xs as [|x xs IH]; intros n ys Hj.
  - cbn [list_LUPDATE length]. destruct (Nat.leb_spec (N.to_nat n) j), (Nat.ltb_spec j (N.to_nat n + 0));
      cbn [andb]; try reflexivity; lia.
  - cbn [list_LUPDATE length]. rewrite IH by (rewrite length_LUPDATE'; exact Hj).
    rewrite nth_LUPDATE' by exact Hj. replace (N.to_nat (n + 1)) with (Datatypes.S (N.to_nat n)) by lia.
    destruct (Nat.leb_spec (Datatypes.S (N.to_nat n)) j), (Nat.ltb_spec j (Datatypes.S (N.to_nat n) + length xs));
    destruct (Nat.leb_spec (N.to_nat n) j), (Nat.ltb_spec j (N.to_nat n + Datatypes.S (length xs)));
    destruct (Nat.eqb_spec j (N.to_nat n)); cbn [andb]; try lia; try reflexivity.
    all: try (subst j; rewrite Nat.sub_diag; reflexivity).
    all: replace (j - N.to_nat n)%nat with (Datatypes.S (j - Datatypes.S (N.to_nat n))) by lia; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "list_LUPDATE_TAKE_DROP" *)
Theorem list_LUPDATE_TAKE_DROP : forall (xs ys : list A) n,
  list_LUPDATE xs n ys = TAKE n ys ++ list_LUPDATE xs 0 (DROP n ys).
Proof.
  intros xs ys n. destruct ys as [|y0 ys0] eqn:Ey; [rewrite list_LUPDATE_NIL, list_LUPDATE_NIL; destruct n; reflexivity|].
  rewrite <- Ey. clear Ey. apply nth_ext with (d := y0) (d' := y0).
  - rewrite length_app, length_list_LUPDATE, TAKE_firstn, DROP_skipn, length_list_LUPDATE,
      length_firstn, length_skipn. lia.
  - intros j Hj. rewrite length_list_LUPDATE in Hj. rewrite nth_list_LUPDATE by exact Hj.
    rewrite TAKE_firstn, DROP_skipn. destruct (Nat.ltb_spec j (N.to_nat n)) as [Hl|Hl].
    + rewrite app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn.
      destruct (Nat.leb_spec (N.to_nat n) j); cbn [andb]; [lia|]. destruct (Nat.ltb_spec j (N.to_nat n)); [reflexivity|lia].
    + rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn, Nat.min_l by lia.
      rewrite nth_list_LUPDATE by (rewrite length_skipn; lia). cbn [N.to_nat].
      rewrite nth_skipn. replace (N.to_nat n + (j - N.to_nat n))%nat with j by lia.
      destruct (Nat.leb_spec (N.to_nat n) j); [|lia]. cbn [andb].
      rewrite Nat.sub_0_r. destruct (Nat.ltb_spec j (N.to_nat n + length xs)), (Nat.ltb_spec (j - N.to_nat n) (0 + length xs));
        cbn [andb Nat.leb]; try lia; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "list_LUPDATE_0_CONS" *)
Theorem list_LUPDATE_0_CONS : forall (xs : list A) x ys y,
  list_LUPDATE (x :: xs) 0 (y :: ys) = x :: list_LUPDATE xs 0 ys.
Proof.
  intros xs x ys y. cbn [list_LUPDATE]. rewrite LUPDATE_cons_eq. cbn -[list_LUPDATE].
  rewrite list_LUPDATE_TAKE_DROP. replace (0 + 1) with 1 by lia.
  rewrite TAKE_firstn, DROP_skipn. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "list_LUPDATE_APPEND" *)
Theorem list_LUPDATE_APPEND : forall (xs ys zs : list A),
  LENGTH xs = LENGTH ys -> list_LUPDATE xs 0 (ys ++ zs) = xs ++ zs.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] zs H; rewrite ?LENGTH_cons' in H; try (cbn in H; lia);
    [reflexivity|].
  cbn [app]. rewrite list_LUPDATE_0_CONS, IH by lia. reflexivity.
Qed.

End ListLUpdate.

(** ** [word_list], [list_rearrange] *)

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DIV_ADD_1" *)
Theorem DIV_ADD_1 : forall d m, 0 < d -> m DIV d + 1 = (m + d) DIV d.
Proof.
  intros d m H. rewrite <- (N.mul_1_l d) at 2. rewrite N.div_add by lia. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LENGTH_word_list_lemma" *)
Theorem LENGTH_word_list_lemma : forall {a} (xs : list bool) d,
  0 < d -> LENGTH (@word_list a xs d) = (LENGTH xs - 1) DIV d + 1.
Proof.
  intros a xs d Hd. remember (length xs) as n eqn:En. revert xs En.
  induction n as [n IH] using (well_founded_induction lt_wf). intros xs En.
  rewrite word_list_def. replace (d =? 0) with false by (symmetry; apply N.eqb_neq; lia).
  rewrite orb_false_r. destruct (N.leb_spec (LENGTH xs) d) as [H|H].
  - cbn [LENGTH]. rewrite N.div_small by lia. reflexivity.
  - rewrite LENGTH_cons', (IH (length (DROP d xs))); [|rewrite DROP_skipn, length_skipn, LENGTH_length in *; lia|reflexivity].
    rewrite DROP_skipn, !LENGTH_length, length_skipn. rewrite LENGTH_length in H.
    replace (N.of_nat (length xs) - 1) with (N.of_nat (length xs - N.to_nat d) - 1 + d) by lia.
    rewrite <- DIV_ADD_1 by exact Hd. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LENGTH_word_list" *)
Theorem LENGTH_word_list : forall {a} (xs : list bool) d,
  LENGTH (@word_list a xs d) = if d =? 0 then 1 else (LENGTH xs - 1) DIV d + 1.
Proof.
  intros a xs d. destruct (N.eqb_spec d 0) as [->|Hd].
  - rewrite word_list_def, orb_true_r. reflexivity.
  - apply LENGTH_word_list_lemma. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "list_rearrange_I" *)
Theorem list_rearrange_I : forall {A} `{Inhabited A}, @wordSem.list_rearrange A _ I = I.
Proof.
  intros A HA. apply functional_extensionality. intros xs. unfold wordSem.list_rearrange.
  destruct (classical_dec _) as [_|Hn].
  - unfold I at 2. rewrite <- (GENLIST_EL_id xs) at 2. reflexivity.
  - exfalso. apply Hn. unfold BIJ, INJ, SURJ, I, pred_set.IN. repeat split; auto.
    intros x Hx. exists x. auto.
Qed.
