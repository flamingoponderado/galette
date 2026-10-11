(** * CakeML [word_to_stackProof]: lemmas used by [comp_correct]

    Part of the port of
    [cakeml/compiler/backend/proofs/word_to_stackProofScript.sml]: the
    theorems stated between the cases of [comp_correct] (HOL lines
    5855-7767): constant stores ([copy_words_correct]), abstract-stack
    lengths, shared-memory instructions and the copying of results
    ([copy_ret_aux]).

    Notes: as in [state_rel.v].  HOL's [w ' i] (a [bool] in Galette) and
    HOL boolean equations [b = (P)] are written with [=?]/[is_true].
    [word_exp_Op_Add_0] and [evaluate_ShareInst_Var_eq_Op_Add] hold for word
    states of any compiler-configuration and ffi types, as in HOL. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words byte.
From Galette.HOL.src.n_bit.words Require Import lemmas fcp_defs.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend Require Import word_to_stack.
From Galette.cakeml.compiler.backend.semantics Require Import wordConvs.
From Galette.cakeml.compiler.backend.semantics Require wordSem.
From Galette.cakeml.compiler.backend.semantics Require Import stackSem stackProps.
From Galette.cakeml.compiler.backend.proofs.word_to_stackProof Require Import basic compile_props state_rel gc stack_rel moves inst syntax.
Import wordLang (word_loc, Word, Loc).
Import wordSem (stack_frame, StackFrame).
Open Scope N_scope.

(** ** Constant stores (HOL lines 5855-6040) *)

Lemma EL_0' {A} `{Inhabited A} (x : A) l : EL 0 (x :: l) = x.
Proof. rewrite EL_nth'. reflexivity. Qed.

Section ChunkToBits.
Context {a : N}.
Local Open Scope word_scope.

Lemma fcp_chunk_to_bits_cons (b : bool) (w : word a) ws i : (i < dimindex a)%N ->
  (chunk_to_bits ((b, w) :: ws)) ' i = if (i =? 0)%N then b else (chunk_to_bits ws) ' (i - 1)%N.
Proof.
  intros Hi. pose proof (@dimindex_pos a) as Hd. cbn [chunk_to_bits]. cbv zeta.
  destruct b.
  - rewrite <- word_shift_or_1. rewrite fcp_index_word_or, fcp_index_word_lsl, fcp_index_n2w by exact Hi.
    destruct (N.eqb_spec i 0) as [->|Hn].
    + reflexivity.
    + replace (1 <=? i)%N with true by (symmetry; apply N.leb_le; lia). cbn [andb].
      rewrite BIT_testbit. replace (N.testbit 1 i) with false; [apply orb_false_r|].
      symmetry. destruct i as [|p]; [lia|]. reflexivity.
  - rewrite fcp_index_word_lsl by exact Hi. destruct (N.eqb_spec i 0) as [->|Hn]; [reflexivity|].
    replace (1 <=? i)%N with true by (symmetry; apply N.leb_le; lia). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "chunk_to_bits_bound" *)
Theorem chunk_to_bits_bound : forall (ws : list (bool * word a)),
  (LENGTH ws < dimindex a)%N ->
  (chunk_to_bits ws) ' (LENGTH ws) /\
  forall i, (LENGTH ws < i)%N /\ (i < dimindex a)%N -> ~ is_true ((chunk_to_bits ws) ' i).
Proof.
  induction ws as [|[b w] ws IH]; intros Hl.
  - cbn [chunk_to_bits LENGTH]. split.
    + rewrite fcp_index_n2w by exact Hl. reflexivity.
    + intros i [H1 H2]. rewrite fcp_index_n2w by exact H2. rewrite BIT_testbit.
      destruct i as [|p]; [lia|]. destruct p; discriminate.
  - rewrite LENGTH_cons' in *. destruct (IH ltac:(lia)) as [IH1 IH2]. split.
    + rewrite fcp_chunk_to_bits_cons by lia. replace (LENGTH ws + 1 =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
      replace (LENGTH ws + 1 - 1)%N with (LENGTH ws) by lia. exact IH1.
    + intros i [H1 H2]. rewrite fcp_chunk_to_bits_cons by exact H2.
      replace (i =? 0)%N with false by (symmetry; apply N.eqb_neq; lia). apply IH2. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "chunk_to_bits_0" *)
Theorem chunk_to_bits_0 : forall b (w : word a) words,
  (chunk_to_bits ((b, w) :: words)) ' 0 = b.
Proof. intros b w words. rewrite fcp_chunk_to_bits_cons by apply dimindex_pos. reflexivity. Qed.

Lemma chunk_to_bits_lsr1 b (w : word a) ws :
  (LENGTH ((b, w) :: ws) < dimindex a)%N -> chunk_to_bits ((b, w) :: ws) >>> 1 = chunk_to_bits ws.
Proof.
  intros Hl. rewrite LENGTH_cons' in Hl. destruct (chunk_to_bits_bound ws ltac:(lia)) as [_ Hb].
  apply word_bit_ext. intros i Hi. rewrite fcp_index_word_lsr by exact Hi.
  destruct (N.ltb_spec (i + 1) (dimindex a)) as [H|H]; cbn [andb].
  - rewrite fcp_chunk_to_bits_cons by exact H. replace (i + 1 =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    f_equal. lia.
  - destruct ((chunk_to_bits ws) ' i) eqn:E; [|reflexivity]. exfalso. apply (Hb i); [lia|exact E].
Qed.

Lemma chunk_to_bits_neq_0_1 b (w : word a) ws :
  (LENGTH ((b, w) :: ws) < dimindex a)%N ->
  chunk_to_bits ((b, w) :: ws) <> n2w 0 /\ chunk_to_bits ((b, w) :: ws) <> n2w 1.
Proof.
  intros Hl. destruct (chunk_to_bits_bound _ Hl) as [H1 _]. rewrite LENGTH_cons' in *.
  split; intros E; rewrite E, fcp_index_n2w, BIT_testbit in H1 by lia.
  - rewrite N.bits_0 in H1. discriminate.
  - destruct (LENGTH ws + 1)%N as [|p] eqn:Ep; [lia|]. destruct p; discriminate.
Qed.

Lemma bytes_add_succ (ad : word a) n : ad + bytes_in_word + bytes_in_word * n2w n = ad + bytes_in_word * n2w (n + 1).
Proof. rewrite <- word_add_n2w. word_ring. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_words_for_pattern_thm" *)
Theorem copy_words_for_pattern_thm : forall (words : list (bool * word a)) xs (ad off : word a) ys dm m,
  (LENGTH words < dimindex a)%N /\ wordSem.const_addresses ad words dm ->
  copy_words_for_pattern (chunk_to_bits words) (LENGTH xs) ad off (xs ++ MAP SND words ++ ys) dm m =
  SOME ((LENGTH xs + LENGTH words)%N, (ad + bytes_in_word * n2w (LENGTH words), wordSem.const_writes ad off words m)).
Proof.
  induction words as [|[b w] words IH]; intros xs ad off ys dm m [Hl Hc].
  - cbn [chunk_to_bits LENGTH]. rewrite copy_words_for_pattern_def.
    rewrite bd_false' by (apply n2w_1_neq_0). rewrite bd_true' by reflexivity.
    rewrite N.add_0_r. f_equal. f_equal. f_equal. word_ring.
  - destruct (chunk_to_bits_neq_0_1 b w words Hl) as [N0 N1].
    cbn [wordSem.const_addresses] in Hc. apply andb_prop in Hc as [Ha Hc].
    rewrite copy_words_for_pattern_def. rewrite bd_false' by exact N0. rewrite bd_false' by exact N1.
    rewrite Ha. cbn [List.map app SND snd]. rewrite LENGTH_app', LENGTH_cons'.
    rewrite (proj2 (N.ltb_lt _ _)) by lia. cbn [andb]. cbv zeta.
    rewrite chunk_to_bits_0, chunk_to_bits_lsr1 by exact Hl.
    rewrite EL_app_N. rewrite N.ltb_irrefl, N.sub_diag, EL_0'.
    replace (xs ++ w :: MAP SND words ++ ys) with ((xs ++ [w]) ++ MAP SND words ++ ys) by (rewrite <- app_assoc; reflexivity).
    replace (LENGTH xs + 1)%N with (LENGTH (xs ++ [w])) by (rewrite LENGTH_app'; reflexivity).
    rewrite IH by (split; [rewrite LENGTH_cons' in Hl; lia|exact Hc]).
    cbn [wordSem.const_writes]. rewrite !LENGTH_app', !LENGTH_cons'.
    replace (LENGTH (@nil (word a))) with 0%N by reflexivity. rewrite bytes_add_succ.
    replace (LENGTH xs + (0 + 1) + LENGTH words)%N with (LENGTH xs + (LENGTH words + 1))%N by lia. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_msb_chunk_to_bits" *)
Theorem word_msb_chunk_to_bits : forall (words : list (bool * word a)),
  (LENGTH words < dimindex a)%N /\ good_dimindex a ->
  word_msb (chunk_to_bits words) = (LENGTH words =? dimindex a - 1)%N.
Proof.
  intros words [Hl Hg]. destruct (chunk_to_bits_bound words Hl) as [H1 H2]. rewrite word_msb_def.
  destruct (N.eqb_spec (LENGTH words) (dimindex a - 1)) as [E|E].
  - rewrite <- E. exact H1.
  - destruct ((chunk_to_bits words) ' (dimindex a - 1)) eqn:Eb; [|reflexivity].
    exfalso. apply (H2 (dimindex a - 1)%N); [|exact Eb]. pose proof (@dimindex_pos a). lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_words" *)
Theorem copy_words : forall (words : list (bool * word a)) xs (ad off : word a) ys dm m,
  wordSem.const_addresses ad words dm /\ good_dimindex a /\ (LENGTH words < dimindex a)%N ->
  copy_words (LENGTH xs) ad off (xs ++ chunk_to_bitmap words ++ ys) dm m =
  if (LENGTH words =? dimindex a - 1)%N then
    copy_words (LENGTH xs + (LENGTH words + 1)) (ad + bytes_in_word * n2w (LENGTH words)) off
      (xs ++ chunk_to_bitmap words ++ ys) dm (wordSem.const_writes ad off words m)
  else SOME (ad + bytes_in_word * n2w (LENGTH words), wordSem.const_writes ad off words m).
Proof.
  intros words xs ad off ys dm m (Hc & Hg & Hl). rewrite copy_words_def.
  unfold chunk_to_bitmap. cbn [app]. rewrite LENGTH_app', LENGTH_cons'.
  rewrite (proj2 (N.leb_gt _ _)) by lia. cbv zeta.
  rewrite EL_app_N, N.ltb_irrefl, N.sub_diag, EL_0'.
  replace (xs ++ chunk_to_bits words :: MAP SND words ++ ys)
    with ((xs ++ [chunk_to_bits words]) ++ MAP SND words ++ ys) by (rewrite <- !app_assoc; reflexivity).
  replace (LENGTH xs + 1)%N with (LENGTH (xs ++ [chunk_to_bits words])) by (rewrite LENGTH_app'; reflexivity).
  rewrite copy_words_for_pattern_thm by (split; assumption).
  rewrite word_msb_chunk_to_bits by (split; assumption). rewrite LENGTH_app', LENGTH_cons'.
  replace (LENGTH (@nil (word a))) with 0%N by reflexivity.
  destruct (LENGTH words =? dimindex a - 1)%N; [|reflexivity].
  replace (LENGTH xs + (0 + 1) + LENGTH words)%N with (LENGTH xs + (LENGTH words + 1))%N by lia.
  rewrite <- !app_assoc. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "const_writes_append" *)
Theorem const_writes_append : forall (h t : list (bool * word a)) (ad off : word a) m,
  wordSem.const_writes ad off (h ++ t) m =
  wordSem.const_writes (ad + bytes_in_word * n2w (LENGTH h)) off t (wordSem.const_writes ad off h m).
Proof.
  induction h as [|[b x] h IH]; intros t ad off m.
  - cbn [app wordSem.const_writes LENGTH]. f_equal. word_ring.
  - cbn [app wordSem.const_writes]. rewrite IH, LENGTH_cons', bytes_add_succ. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "const_addresses_append" *)
Theorem const_addresses_append : forall {B} (xs ys : list B) dm (ad : word a),
  wordSem.const_addresses ad (xs ++ ys) dm =
  (wordSem.const_addresses ad xs dm && wordSem.const_addresses (ad + bytes_in_word * n2w (LENGTH xs)) ys dm)%bool.
Proof.
  intros B xs; induction xs as [|x xs IH]; intros ys dm ad.
  - cbn [app wordSem.const_addresses LENGTH]. cbn [andb]. f_equal. word_ring.
  - cbn [app wordSem.const_addresses]. rewrite IH, LENGTH_cons', bytes_add_succ, andb_assoc. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_words_correct" *)
Theorem copy_words_correct : forall (words : list (bool * word a)) xs ys (ad off : word a) dm m,
  wordSem.const_addresses ad words dm /\ good_dimindex a ->
  stackSem.copy_words (LENGTH xs) ad off (xs ++ const_words_to_bitmap words (LENGTH words) ++ ys) dm m =
  SOME (ad + bytes_in_word * n2w (LENGTH words), wordSem.const_writes ad off words m).
Proof.
  intros words. remember (N.to_nat (LENGTH words)) as L eqn:EL. revert words EL.
  induction L as [L IH] using (well_founded_induction lt_wf).
  intros words EL xs ys ad off dm m [Hc Hg].
  assert (Hd : (2 <= dimindex a)%N) by (destruct Hg as [Hg|Hg]; rewrite Hg; lia).
  rewrite const_words_to_bitmap_def.
  destruct (orb (LENGTH words <? dimindex a - 1)%N (dimindex a - 1 =? 0)%N) eqn:Ec.
  - apply orb_true_iff in Ec as [Ec|Ec]; [apply N.ltb_lt in Ec|apply N.eqb_eq in Ec; lia].
    rewrite copy_words by (repeat split; try assumption; lia).
    rewrite (proj2 (N.eqb_neq _ _)) by lia. reflexivity.
  - apply orb_false_iff in Ec as [Ec _]. apply N.ltb_ge in Ec. cbv zeta.
    set (h := TAKE (dimindex a - 1) words). set (t := DROP (dimindex a - 1) words).
    assert (Ew : words = h ++ t) by (unfold h, t; rewrite TAKE_firstn, DROP_skipn; symmetry; apply firstn_skipn).
    assert (Hlh : LENGTH h = (dimindex a - 1)%N).
    { unfold h. rewrite TAKE_firstn, LENGTH_length, length_firstn. rewrite LENGTH_length in Ec. lia. }
    assert (Hlt : LENGTH t = (LENGTH words - (dimindex a - 1))%N) by (unfold t; apply LENGTH_DROP').
    rewrite Ew in Hc. rewrite const_addresses_append in Hc. apply andb_prop in Hc as [Hch Hct].
    rewrite <- !app_assoc. rewrite copy_words by (repeat split; try assumption; lia).
    rewrite Hlh, N.eqb_refl.
    replace (LENGTH xs + (dimindex a - 1 + 1))%N with (LENGTH (xs ++ chunk_to_bitmap h)).
    2:{ rewrite LENGTH_app'. unfold chunk_to_bitmap. rewrite LENGTH_cons'.
        assert (Hm : LENGTH (MAP SND h) = LENGTH h) by (rewrite !LENGTH_length, length_map; reflexivity).
        rewrite Hm, Hlh. lia. }
    rewrite app_assoc.
    replace (LENGTH words - (dimindex a - 1))%N with (LENGTH t) by exact Hlt.
    rewrite (IH (N.to_nat (LENGTH t))) by (try reflexivity; try (split; [rewrite Hlh in Hct; exact Hct|exact Hg]); lia).
    assert (EL' : LENGTH words = (dimindex a - 1 + LENGTH t)%N) by (rewrite Ew, LENGTH_app', Hlh; reflexivity).
    rewrite EL'. replace (wordSem.const_writes ad off words m) with (wordSem.const_writes ad off (h ++ t) m) by (rewrite <- Ew; reflexivity).
    rewrite const_writes_append, Hlh. f_equal. f_equal. rewrite <- word_add_n2w. word_ring.
Qed.

End ChunkToBits.

(** ** Abstract stacks (HOL lines 6581-6625) *)

Section AbsStackLemmas.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_aux_stack_size" *)
Theorem stack_rel_aux_stack_size : forall len k (frame : list (stack_frame a)) bits,
  stack_rel_aux len k frame bits ->
  the (handler_val bits) (wordSem.stack_size frame) = handler_val bits.
Proof.
  intros len k frame; induction frame as [|[n l0 l [[h1 [l1 l2]]|]] frame IH]; intros [|[[[loc hv]|] [bs fr]] bits] H;
    cbn [stack_rel_aux] in H; try contradiction.
  - reflexivity.
  - destruct H as (_ & _ & _ & _ & Hthe & Hr). specialize (IH _ Hr).
    change (wordSem.stack_size (StackFrame n l0 l (SOME (h1, (l1, l2))) :: frame))
      with (OPTION_MAP2 N.add (OPTION_MAP (N.add 3) n) (wordSem.stack_size frame)).
    cbn [handler_val]. destruct n as [v|]; [|reflexivity]. cbn [the] in Hthe. subst v.
    destruct (wordSem.stack_size frame) as [z|]; [|reflexivity]. cbn [the] in IH. subst z.
    rewrite ?om_some, om2_some. cbn [the]. lia.
  - destruct H as (_ & _ & Hthe & Hr). specialize (IH _ Hr).
    change (wordSem.stack_size (StackFrame n l0 l NONE :: frame))
      with (OPTION_MAP2 N.add n (wordSem.stack_size frame)).
    cbn [handler_val]. destruct n as [v|]; [|reflexivity]. cbn [the] in Hthe. subst v.
    destruct (wordSem.stack_size frame) as [z|]; [|reflexivity]. cbn [the] in IH. subst z.
    rewrite ?om_some, om2_some. cbn [the]. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_stack_CONS_NIL" *)
Theorem abs_stack_CONS_NIL : forall (bm : list (word a)) x rest l,
  abs_stack bm (x :: rest) [] l = NONE.
Proof. intros bm [n l0 l1 [h|]] rest [|len l]; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "SUB_ADD_EQ" *)
Theorem SUB_ADD_EQ : forall a0 b, a0 <= b -> a0 + (b - a0) = b.
Proof. intros; lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_stack_LENGTH" *)
Theorem abs_stack_LENGTH : forall (bitmaps0 : list (word a)) wstack tstack lens astack,
  abs_stack bitmaps0 wstack tstack lens = SOME astack -> handler_val astack = LENGTH tstack.
Proof. intros. eapply abs_stack_to_stack_LENGTH; eassumption. Qed.

Lemma handler_val_pos (st : list (option (word_loc a * word_loc a) * (list bool * list (word_loc a)))) :
  1 <= handler_val st.
Proof. destruct st as [|[[?|] [? ?]] st]; cbn [handler_val]; lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_stack_empty'" *)
Theorem abs_stack_empty' : forall (bs : list (word a)) xs lens stack,
  abs_stack bs xs [] lens = SOME stack <-> False.
Proof.
  intros bs xs lens stack. split; [|contradiction]. intros H.
  apply abs_stack_LENGTH in H. pose proof (handler_val_pos stack). cbn in H. lia.
Qed.

End AbsStackLemmas.

(** ** Constants and quantifier shuffles (HOL lines 6743-6943) *)

Section ConstInst.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_const_inst" *)
Theorem evaluate_const_inst : forall ac k f f' s t lens extra i,
  state_rel ac k f f' s t lens extra ->
  exists t' : stackSem.state a c ffi_t,
    evaluate (const_inst (k + 1) i, t) = (NONE, t') /\
    clock t = clock t' /\
    state_rel ac k f f' s t' lens extra /\
    LENGTH (stackSem.stack t') = LENGTH (stackSem.stack t) /\ stack_space t' = stack_space t /\
    stackSem.get_var (k + 1) t' = SOME (Word i).
Proof.
  intros ac k f f' s t lens extra i H. rewrite ev_inst, inst_const. eexists; split; [reflexivity|].
  split; [reflexivity|]. split; [apply state_rel_set_var_k; exact H|]. split; [reflexivity|]. split; [reflexivity|].
  apply sget_var_set_var_eq.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_const_inst_clock" *)
Theorem evaluate_const_inst_clock : forall clk k (i : word a) t,
  evaluate (const_inst k i, set_clock clk t) = (I ## (fun t => set_clock clk t)) (evaluate (const_inst k i, t)).
Proof. intros clk k i t. rewrite !ev_inst, !inst_const. destruct t; reflexivity. Qed.

End ConstInst.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "EXISTS_PULL_FORALL1" *)
Theorem EXISTS_PULL_FORALL1 : forall {X Y} (P : Y) (Q : X -> Y -> Prop),
  (exists x, forall y, y = P -> Q x y) <-> (forall y, y = P -> exists x, Q x y).
Proof.
  intros X Y P Q. split.
  - intros [x H] y Hy. exists x. apply H, Hy.
  - intros H. destruct (H P eq_refl) as [x Hx]. exists x. intros y ->. exact Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "EXISTS_PULL_FORALL2" *)
Theorem EXISTS_PULL_FORALL2 : forall {X Y Z} (P : Y * Z) (Q : X -> Y -> Z -> Prop),
  (exists x, forall y z, P = (y, z) -> Q x y z) <-> (forall y z, P = (y, z) -> exists x, Q x y z).
Proof.
  intros X Y Z [p1 p2] Q. split.
  - intros [x H] y z Hy. exists x. apply H, Hy.
  - intros H. destruct (H p1 p2 eq_refl) as [x Hx]. exists x. intros y z E. injection E as <- <-. exact Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "EXISTS_PULL_FORALL3" *)
Theorem EXISTS_PULL_FORALL3 : forall {X Y Z W} (P : Y * (Z * W)) (Q : X -> Y -> Z -> W -> Prop),
  (exists x, forall y z a0, P = (y, (z, a0)) -> Q x y z a0) <->
  (forall y z a0, P = (y, (z, a0)) -> exists x, Q x y z a0).
Proof.
  intros X Y Z W [p1 [p2 p3]] Q. split.
  - intros [x H] y z a0 Hy. exists x. apply H, Hy.
  - intros H. destruct (H p1 p2 p3 eq_refl) as [x Hx]. exists x. intros y z a0 E. injection E as <- <- <-. exact Hx.
Qed.

(** ** Shared-memory instructions (HOL lines 7166-7528) *)

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "flat_exp_conventions_ShareInst_exp_simp" *)
Theorem flat_exp_conventions_ShareInst_exp_simp : forall {a} op v (exp : wordLang.exp a),
  flat_exp_conventions (wordLang.ShareInst op v exp) ->
  (exists ad, exp = wordLang.Var ad) \/
  (exists ad offset, exp = wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const offset]).
Proof.
  intros a op v exp H. cbn [flat_exp_conventions] in H.
  destruct exp as [w|r|nm|e|bop l|sh e1 e2]; try discriminate H; [left; eauto|].
  right. destruct bop; try discriminate H.
  destruct l as [|[w1|r1|n1|e1'|b1 l1|s1 x1 y1] [|[w2|r2|n2|e2'|b2 l2|s2 x2 y2] [|? ?]]]; try discriminate H.
  eauto.
Qed.

Section ShareInst.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

Lemma wev_shareinst {C F : Type} op v (exp : wordLang.exp a) (s : wordSem.state a C F) :
  wordSem.evaluate (wordLang.ShareInst op v exp, s) =
  match wordSem.word_exp s exp with SOME (Word ad) => wordSem.share_inst op v ad s | _ => (SOME wordSem.Error, s) end.
Proof. rewrite wordSem.evaluate_eqn. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_exp_Op_Add_0" *)
Theorem word_exp_Op_Add_0 : forall {C F : Type} (s : wordSem.state a C F) exp x,
  wordSem.word_exp s exp = SOME (Word x) <->
  wordSem.word_exp s (wordLang.Op asm.Add [exp; wordLang.Const (n2w 0)]) = SOME (Word x).
Proof.
  intros C F s exp x. cbn [wordSem.word_exp List.map wordSem.the_words]. split.
  - intros ->. cbn. f_equal. f_equal. word_ring.
  - destruct (wordSem.word_exp s exp) as [[y|]|]; cbn; try discriminate.
    intros E. injection E as <-. f_equal. f_equal. word_ring.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_ShareInst_Var_eq_Op_Add" *)
Theorem evaluate_ShareInst_Var_eq_Op_Add : forall {C F : Type} op v ad (s : wordSem.state a C F),
  wordSem.evaluate (wordLang.ShareInst op v (wordLang.Var ad), s) =
  wordSem.evaluate (wordLang.ShareInst op v (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const (n2w 0)]), s).
Proof.
  intros C F op v ad s. rewrite !wev_shareinst. cbn [wordSem.word_exp List.map wordSem.the_words].
  destruct (wordSem.get_var ad s) as [[y|]|]; cbn; [|reflexivity|reflexivity].
  replace (y + (n2w 0 + n2w 0))%w with y by word_ring. reflexivity.
Qed.

Lemma state_rel_set_ffi ac k f f' s t lens extra nf :
  state_rel ac k f f' s t lens extra ->
  state_rel ac k f f' (wordSem.set_ffi nf s) (stackSem.set_ffi nf t) lens extra.
Proof. intros H. sr_destr H. sr_split; ws_fields; stk_fields; try assumption; reflexivity. Qed.

Lemma state_rel_sh_eqs ac k f f' s t lens extra :
  state_rel ac k f f' s t lens extra ->
  sh_mdomain t = wordSem.sh_mdomain s /\ ffi t = wordSem.ffi s /\ clock t = wordSem.clock s.
Proof. intros H. sr_destr H. auto. Qed.

Ltac sh_unfold :=
  unfold wordSem.share_inst, wordSem.sh_mem_set_var, wordSem.sh_mem_load, wordSem.sh_mem_load_byte,
    wordSem.sh_mem_load16, wordSem.sh_mem_load32, wordSem.sh_mem_store, wordSem.sh_mem_store_byte,
    wordSem.sh_mem_store16, wordSem.sh_mem_store32 in *;
  unfold sh_mem_op, stackSem.sh_mem_load, stackSem.sh_mem_load_byte, stackSem.sh_mem_load16,
    stackSem.sh_mem_load32, stackSem.sh_mem_store, stackSem.sh_mem_store_byte,
    stackSem.sh_mem_store16, stackSem.sh_mem_store32.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "share_load_lemma1" *)
Theorem share_load_lemma1 : forall ac k f f' s t lens op v ad' res s1,
  wordSem.share_inst op (2 * v) ad' s = (res, s1) /\
  state_rel ac k f f' s t lens 0 /\
  v < f' + k /\
  k <= v /\
  (op = asm.Load \/ op = Load8 \/ op = Load16 \/ op = Load32) /\
  res <> SOME wordSem.Error ->
  exists t1,
    sh_mem_op op k ad' t = (OPTION_MAP compile_result res, t1) /\
    ((exists fv, res = SOME (wordSem.FinalFFI fv) /\ wordSem.ffi s1 = ffi t1 /\ wordSem.clock s1 = clock t1) \/
     (res = NONE /\
      state_rel ac k f f' s1
        (set_stack (LUPDATE (THE (FLOOKUP (regs t1) k)) (stack_space t1 + (f + k - (v + 1))) (stackSem.stack t1)) t1) lens 0 /\
      (exists x, FLOOKUP (regs t1) k = SOME x) /\
      stack_space t1 = stack_space t /\
      LENGTH (stackSem.stack t1) = LENGTH (stackSem.stack t))).
Proof.
  intros ac k f f' s t lens op v ad' res s1 (Hs & H & Hv1 & Hv2 & Hop & Hres).
  destruct (state_rel_sh_eqs _ _ _ _ _ _ _ _ H) as (Esh & Effi & Eclk).
  destruct Hop as [-> | [-> | [-> | ->]]]; sh_unfold; rewrite Esh, Effi;
    match goal with |- context [classical_dec ?P] => destruct (classical_dec P) as [Hin|Hin] end;
    try (injection Hs as <- <-; congruence);
    match goal with |- context [call_FFI ?a1 ?a2 ?a3 ?a4] => destruct (call_FFI a1 a2 a3 a4) as [nf nb|o] end;
    injection Hs as <- <-; (eexists; split; [reflexivity|]).
  all: try (left; eexists; split; [reflexivity|]; cbn [wordSem.flush_state]; ws_fields; split; congruence).
  all: right; split; [reflexivity|]; stk_fields; rewrite FLOOKUP_UPDATE, decide_True by reflexivity; cbn [THE];
    (split; [|split; [eexists; reflexivity|split; reflexivity]]);
    replace (set_ffi nf (set_regs (regs t |+ (k, Word (word_of_bytes false (n2w 0) nb))) t))
      with (stackSem.set_ffi nf (stackSem.set_var k (Word (word_of_bytes false (n2w 0) nb)) t)) by (destruct t; reflexivity);
    replace (LUPDATE _ _ _) with (LUPDATE (Word (word_of_bytes false (n2w 0) nb))
        (stack_space (stackSem.set_ffi nf (stackSem.set_var k (Word (word_of_bytes false (n2w 0) nb)) t)) + (f + k - (v + 1)))
        (stackSem.stack (stackSem.set_ffi nf (stackSem.set_var k (Word (word_of_bytes false (n2w 0) nb)) t)))) by reflexivity;
    replace (wordSem.set_var (2 * v) _ (wordSem.set_ffi nf s)) with (wordSem.set_var (2 * v) (Word (word_of_bytes false (n2w 0) nb)) (wordSem.set_ffi nf s)) by reflexivity;
    apply state_rel_set_var2; (split; [apply state_rel_set_ffi, state_rel_set_var_k, H|]);
    (split; [lia|]); (split; [lia|]); split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "share_load_lemma2" *)
Theorem share_load_lemma2 : forall ac k f f' s t lens op v ad' res s1,
  wordSem.share_inst op (2 * v) ad' s = (res, s1) /\
  state_rel ac k f f' s t lens 0 /\
  v < k /\
  (op = asm.Load \/ op = Load8 \/ op = Load16 \/ op = Load32) /\
  res <> SOME wordSem.Error ->
  exists t1,
    sh_mem_op op v ad' t = (OPTION_MAP compile_result res, t1) /\
    ((exists fv, res = SOME (wordSem.FinalFFI fv) /\ wordSem.ffi s1 = ffi t1 /\ wordSem.clock s1 = clock t1) \/
     (res = NONE /\ state_rel ac k f f' s1 t1 lens 0)).
Proof.
  intros ac k f f' s t lens op v ad' res s1 (Hs & H & Hv & Hop & Hres).
  destruct (state_rel_sh_eqs _ _ _ _ _ _ _ _ H) as (Esh & Effi & Eclk).
  destruct Hop as [-> | [-> | [-> | ->]]]; sh_unfold; rewrite Esh, Effi;
    match goal with |- context [classical_dec ?P] => destruct (classical_dec P) as [Hin|Hin] end;
    try (injection Hs as <- <-; congruence);
    match goal with |- context [call_FFI ?a1 ?a2 ?a3 ?a4] => destruct (call_FFI a1 a2 a3 a4) as [nf nb|o] end;
    injection Hs as <- <-; (eexists; split; [reflexivity|]).
  all: try (left; eexists; split; [reflexivity|]; cbn [wordSem.flush_state]; ws_fields; split; congruence).
  all: right; split; [reflexivity|];
    replace (set_ffi nf (set_regs (regs t |+ (v, Word (word_of_bytes false (n2w 0) nb))) t))
      with (stackSem.set_var v (Word (word_of_bytes false (n2w 0) nb)) (stackSem.set_ffi nf t)) by (destruct t; reflexivity);
    apply state_rel_set_var; (split; [apply state_rel_set_ffi, H|lia]).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "share_store_lemma1" *)
Theorem share_store_lemma1 : forall ac k f f' s t lens op v ad' res s1,
  wordSem.share_inst op (2 * v) ad' s = (res, s1) /\
  state_rel ac k f f' s t lens 0 /\
  ~ (v < k) /\
  (op = asm.Store \/ op = Store8 \/ op = Store16 \/ op = Store32) /\
  res <> SOME wordSem.Error ->
  exists t1,
    sh_mem_op op (k + 1) ad'
      (set_regs (regs t |+ (k + 1, EL (stack_space t + (f + k - (v + 1))) (stackSem.stack t))) t) =
      (OPTION_MAP compile_result res, t1) /\
    ((exists fv, res = SOME (wordSem.FinalFFI fv) /\ wordSem.ffi s1 = ffi t1 /\ wordSem.clock s1 = clock t1) \/
     (res = NONE /\ state_rel ac k f f' s1 t1 lens 0)).
Proof.
  intros ac k f f' s t lens op v ad' res s1 (Hs & H & Hv & Hop & Hres).
  destruct (state_rel_sh_eqs _ _ _ _ _ _ _ _ H) as (Esh & Effi & Eclk).
  assert (H1 : state_rel ac k f f' s (stackSem.set_var (k + 1) (EL (stack_space t + (f + k - (v + 1))) (stackSem.stack t)) t) lens 0)
    by (apply state_rel_set_var_k; exact H).
  unfold stackSem.set_var in H1.
  destruct Hop as [-> | [-> | [-> | ->]]]; sh_unfold;
    (destruct (wordSem.get_var (2 * v) s) as [[w|]|] eqn:Eg; [|injection Hs as <- <-; congruence|injection Hs as <- <-; congruence]);
    rewrite (state_rel_get_var_imp2 ac k f f' s t lens v (Word w)) in H1 |- * by auto;
    unfold stackSem.get_var; stk_fields; rewrite FLOOKUP_UPDATE, decide_True by reflexivity;
    rewrite Esh, Effi;
    match goal with |- context [classical_dec ?P] => destruct (classical_dec P) as [Hin|Hin] end;
    try (injection Hs as <- <-; congruence);
    match goal with |- context [call_FFI ?a1 ?a2 ?a3 ?a4] => destruct (call_FFI a1 a2 a3 a4) as [nf nb|o] end;
    injection Hs as <- <-; (eexists; split; [reflexivity|]).
  all: try (left; eexists; split; [reflexivity|]; cbn [wordSem.flush_state]; ws_fields; stk_fields; split; congruence).
  all: right; split; [reflexivity|]; apply state_rel_set_ffi; exact H1.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "share_store_lemma2" *)
Theorem share_store_lemma2 : forall ac k f f' s t lens op v ad' res s1,
  wordSem.share_inst op (2 * v) ad' s = (res, s1) /\
  state_rel ac k f f' s t lens 0 /\
  v < k /\
  (op = asm.Store \/ op = Store8 \/ op = Store16 \/ op = Store32) /\
  res <> SOME wordSem.Error ->
  exists t1,
    sh_mem_op op v ad' t = (OPTION_MAP compile_result res, t1) /\
    ((exists fv, res = SOME (wordSem.FinalFFI fv) /\ wordSem.ffi s1 = ffi t1 /\ wordSem.clock s1 = clock t1) \/
     (res = NONE /\ state_rel ac k f f' s1 t1 lens 0)).
Proof.
  intros ac k f f' s t lens op v ad' res s1 (Hs & H & Hv & Hop & Hres).
  destruct (state_rel_sh_eqs _ _ _ _ _ _ _ _ H) as (Esh & Effi & Eclk).
  destruct Hop as [-> | [-> | [-> | ->]]]; sh_unfold;
    (destruct (wordSem.get_var (2 * v) s) as [[w|]|] eqn:Eg; [|injection Hs as <- <-; congruence|injection Hs as <- <-; congruence]);
    unfold stackSem.get_var; rewrite (state_rel_get_var_imp ac k f f' s t lens 0 v (Word w)) by auto;
    rewrite Esh, Effi;
    match goal with |- context [classical_dec ?P] => destruct (classical_dec P) as [Hin|Hin] end;
    try (injection Hs as <- <-; congruence);
    match goal with |- context [call_FFI ?a1 ?a2 ?a3 ?a4] => destruct (call_FFI a1 a2 a3 a4) as [nf nb|o] end;
    injection Hs as <- <-; (eexists; split; [reflexivity|]).
  all: try (left; eexists; split; [reflexivity|]; cbn [wordSem.flush_state]; ws_fields; split; congruence).
  all: right; split; [reflexivity|]; apply state_rel_set_ffi; exact H.
Qed.

Lemma ev_shmemop op r ad w (X : stackSem.state a c ffi_t) :
  evaluate (ShMemOp op r (Addr ad w), X) =
  match stackSem.word_exp X (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w]) with
  | SOME ad => if (clock X =? 0)%N then (SOME TimeOut, empty_env X) else sh_mem_op op r ad (dec_clock X)
  | _ => (SOME Error, X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma load_clock l (P : prog a) C t t1 :
  evaluate (wStackLoad l Skip, t) = (NONE, t1) ->
  evaluate (wStackLoad l P, set_clock C t) = evaluate (P, set_clock C t1).
Proof. intros E. rewrite evaluate_wStackLoad_seq, ev_seq, evaluate_wStackLoad_clock, E. reflexivity. Qed.

Lemma dec_clock_set_clock C t : dec_clock (set_clock (C + 1) t) = set_clock C t.
Proof. unfold dec_clock. stk_fields. replace (C + 1 - 1)%N with C by lia. destruct t; reflexivity. Qed.

Lemma dec_clock_set_clock' C t : dec_clock (set_clock (1 + C) t) = set_clock C t.
Proof. unfold dec_clock. stk_fields. replace (1 + C - 1)%N with C by lia. destruct t; reflexivity. Qed.

Lemma wshare_inv s op v ad offset res s1 :
  wordSem.evaluate (wordLang.ShareInst op v (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const offset]), s) = (res, s1) ->
  exists x, wordSem.get_var ad s = SOME (Word x) /\
    wordSem.share_inst op v (FOLDR word_add (n2w 0) [x; offset]) s = (res, s1) \/
    (res = SOME wordSem.Error).
Proof.
  rewrite wev_shareinst. cbn [wordSem.word_exp List.map wordSem.the_words].
  destruct (wordSem.get_var ad s) as [[x|]|]; cbn; intros H; [eauto| |]; injection H as <- _; exists (n2w 0); auto.
Qed.

Lemma sh_mem_op_use_stack op r ad (X Y : stackSem.state a c ffi_t) res :
  sh_mem_op op r ad X = (res, Y) -> use_stack Y = use_stack X.
Proof.
  intros E. destruct op;
    unfold sh_mem_op, stackSem.sh_mem_load, stackSem.sh_mem_load_byte, stackSem.sh_mem_load16,
      stackSem.sh_mem_load32, stackSem.sh_mem_store, stackSem.sh_mem_store_byte,
      stackSem.sh_mem_store16, stackSem.sh_mem_store32 in E;
    repeat (match type of E with context [match ?x with _ => _ end] =>
              lazymatch x with context [match _ with _ => _ end] => fail | _ => idtac end; destruct x end);
    injection E as _ <-; reflexivity.
Qed.

Lemma load_ad ac k f f' s t lens ad x l n2 :
  state_rel ac k f f' s t lens 0 -> wordSem.get_var (2 * ad) s = SOME (Word x) ->
  wReg1 (2 * ad) (k, (f, f')) = (l, n2) ->
  exists t1', evaluate (wStackLoad l Skip, t) = (NONE, t1') /\ clock t = clock t1' /\
    state_rel ac k f f' s t1' lens 0 /\ FLOOKUP (regs t1') n2 = SOME (Word x).
Proof.
  intros H Hg Ew. destruct (evaluate_wStackLoad_wReg1 ac k f f' (2 * ad) l n2 s t lens (Word x))
    as (t1' & E1 & Hc & H1 & _ & _ & _ & _ & _ & G); [split; [exact Ew|]; split; [apply N.even_spec; eexists; reflexivity|]; split; assumption|].
  exists t1'. unfold stackSem.get_var in G. auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_ShareInst_Load" *)
Theorem evaluate_ShareInst_Load : forall ac k f f' s t lens op v ad offset res s1,
  wordSem.evaluate (wordLang.ShareInst op (2 * v) (wordLang.Op asm.Add [wordLang.Var (2 * ad); wordLang.Const offset]), s) = (res, s1) /\
  res <> SOME wordSem.Error /\
  state_rel ac k f f' s t lens 0 /\
  v < f' + k /\
  ad < f' + k /\
  (op = asm.Load \/ op = Load8 \/ op = Load16 \/ op = Load32) ->
  exists ck t1,
    evaluate (wShareInst op (2 * v) (Addr (2 * ad) offset) (k, (f, f')), set_clock (ck + clock t) t) =
      (OPTION_MAP compile_result res, t1) /\
    ((exists fv, res = SOME (wordSem.FinalFFI fv) /\ wordSem.ffi s1 = ffi t1 /\ wordSem.clock s1 = clock t1) \/
     (res = NONE /\ state_rel ac k f f' s1 t1 lens 0)).
Proof.
  intros ac k f f' s t lens op v ad offset res s1 (Hev & Hres & H & Hv & Had & Hop).
  apply wshare_inv in Hev as (x & [(Hg & Hs) | ->]); [|congruence].
  exists 1.
  destruct Hop as [-> | [-> | [-> | ->]]]; cbn [wShareInst];
    destruct (wReg1 (2 * ad) (k, (f, f'))) as [l n2] eqn:Ew; destruct (load_ad ac k f f' s t lens ad x l n2 H Hg Ew) as (t1' & E1 & Hc & H1 & G);
    rewrite (load_clock _ _ _ _ _ E1); rewrite Hc;
    unfold wRegWrite1; rewrite mul2_div2;
    (destruct (v <? k) eqn:Ek; to_prop;
     [ rewrite ev_shmemop; rewrite (sword_exp_add_const _ n2 x offset) by (unfold stackSem.get_var; stk_fields; exact G);
       stk_fields; rewrite (proj2 (N.eqb_neq _ _)) by lia; rewrite dec_clock_set_clock', state_with_const;
       (match type of Hs with wordSem.share_inst ?op _ ?ad' _ = _ => destruct (share_load_lemma2 ac k f f' s t1' lens op v ad' res s1) as (t2 & E2 & HR); [split; [exact Hs|]; split; [exact H1|]; split; [lia|]; split; [auto|exact Hres]|] end);
       rewrite E2; eexists; split; [reflexivity|exact HR]
     | rewrite ev_seq, ev_shmemop; rewrite (sword_exp_add_const _ n2 x offset) by (unfold stackSem.get_var; stk_fields; exact G);
       stk_fields; rewrite (proj2 (N.eqb_neq _ _)) by lia; rewrite dec_clock_set_clock', state_with_const;
       (match type of Hs with wordSem.share_inst ?op _ ?ad' _ = _ => destruct (share_load_lemma1 ac k f f' s t1' lens op v ad' res s1) as (t2 & E2 & HR); [split; [exact Hs|]; split; [exact H1|]; split; [exact Hv|]; split; [lia|]; split; [auto|exact Hres]|] end);
       rewrite E2;
       destruct HR as [(fv & -> & HR1 & HR2)|(-> & HR & (xk & Hxk) & HS2 & HL2)];
       [ eexists; split; [reflexivity|left; eauto]
       | cbn [OPTION_MAP option_map]; rewrite ev_stackstore;
         assert (Hb : (stack_space t1' + f <= LENGTH (stackSem.stack t1') /\ use_stack t1' /\ (f' <> 0 -> f = f' + 1))%N)
           by (sr_destr H1; split; [lia|]; split; [exact Hus|]; intros Hf; destruct (f' =? 0) eqn:Ef; [apply N.eqb_eq in Ef; lia|lia]);
         destruct Hb as (Hb1 & Hb2 & Hb3);
         rewrite (sh_mem_op_use_stack _ _ _ _ _ _ E2);
         unfold is_true in Hb2; rewrite Hb2; cbn [negb];
         rewrite (proj2 (N.leb_gt _ _)) by lia; unfold stackSem.get_var; rewrite Hxk;
         eexists; split; [reflexivity|]; right; split; [reflexivity|];
         rewrite Hxk in HR; cbn [THE] in HR; replace (f - 1 - (v - k))%N with (f + k - (v + 1))%N by lia; exact HR ] ]).
Qed.

Lemma wReg1_neq k f f' r l n : wReg1 r (k, (f, f')) = (l, n) -> n <> k + 1.
Proof. unfold wReg1. cbv zeta. destruct (r DIV 2 <? k) eqn:E; to_prop; intros H; injection H as _ <-; lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_ShareInst_Store" *)
Theorem evaluate_ShareInst_Store : forall ac k f f' s t lens op v ad offset res s1,
  wordSem.evaluate (wordLang.ShareInst op (2 * v) (wordLang.Op asm.Add [wordLang.Var (2 * ad); wordLang.Const offset]), s) = (res, s1) /\
  state_rel ac k f f' s t lens 0 /\
  v < f' + k /\
  ad < f' + k /\
  res <> SOME wordSem.Error /\
  (op = asm.Store \/ op = Store8 \/ op = Store16 \/ op = Store32) ->
  exists ck t1,
    evaluate (wShareInst op (2 * v) (Addr (2 * ad) offset) (k, (f, f')), set_clock (ck + clock t) t) =
      (OPTION_MAP compile_result res, t1) /\
    ((exists fv, res = SOME (wordSem.FinalFFI fv) /\ wordSem.ffi s1 = ffi t1 /\ wordSem.clock s1 = clock t1) \/
     (res = NONE /\ state_rel ac k f f' s1 t1 lens 0)).
Proof.
  intros ac k f f' s t lens op v ad offset res s1 (Hev & H & Hv & Had & Hres & Hop).
  apply wshare_inv in Hev as (x & [(Hg & Hs) | ->]); [|congruence].
  exists 1.
  destruct Hop as [-> | [-> | [-> | ->]]]; cbn [wShareInst];
    destruct (wReg1 (2 * ad) (k, (f, f'))) as [l n2] eqn:Ew;
    pose proof (wReg1_neq _ _ _ _ _ _ Ew) as Hn2;
    destruct (load_ad ac k f f' s t lens ad x l n2 H Hg Ew) as (t1' & E1 & Hc & H1 & G);
    unfold wReg2; rewrite mul2_div2;
    (destruct (v <? k) eqn:Ek; to_prop; cbv beta iota; rewrite wStackLoad_append;
     rewrite (load_clock _ _ _ _ _ E1); rewrite Hc;
     [ rewrite wStackLoad_nil, ev_shmemop; rewrite (sword_exp_add_const _ n2 x offset) by (unfold stackSem.get_var; stk_fields; exact G);
       stk_fields; rewrite (proj2 (N.eqb_neq _ _)) by lia; rewrite dec_clock_set_clock', state_with_const;
       (match type of Hs with wordSem.share_inst ?op _ ?ad' _ = _ =>
          destruct (share_store_lemma2 ac k f f' s t1' lens op v ad' res s1) as (t2 & E2 & HR);
          [split; [exact Hs|]; split; [exact H1|]; split; [lia|]; split; [auto|exact Hres]|] end);
       rewrite E2; eexists; split; [reflexivity|exact HR]
     | cbn [wStackLoad]; rewrite ev_seq, ev_stackload; stk_fields;
       assert (Hb : (stack_space t1' + f <= LENGTH (stackSem.stack t1') /\ use_stack t1' /\ (f' <> 0 -> f = f' + 1))%N)
         by (sr_destr H1; split; [lia|]; split; [exact Hus|]; intros Hf; destruct (f' =? 0) eqn:Ef; [apply N.eqb_eq in Ef; lia|lia]);
       destruct Hb as (Hb1 & Hb2 & Hb3); unfold is_true in Hb2; rewrite Hb2; cbn [negb];
       rewrite (proj2 (N.ltb_lt _ _)) by lia;
       rewrite ev_shmemop; rewrite (sword_exp_add_const _ n2 x offset)
         by (unfold stackSem.get_var, stackSem.set_var; stk_fields; rewrite FLOOKUP_UPDATE, decide_False by lia; exact G);
       unfold stackSem.set_var; stk_fields; rewrite (proj2 (N.eqb_neq _ _)) by lia;
       replace (dec_clock (set_regs (regs t1' |+ (k + 1, EL (stack_space t1' + (f - 1 - (v - k))) (stackSem.stack t1'))) (set_clock (1 + clock t1') t1')))
         with (set_regs (regs t1' |+ (k + 1, EL (stack_space t1' + (f + k - (v + 1))) (stackSem.stack t1'))) t1')
         by (replace (f - 1 - (v - k))%N with (f + k - (v + 1))%N by lia; unfold dec_clock; stk_fields;
             replace (1 + clock t1' - 1)%N with (clock t1') by lia; destruct t1'; reflexivity);
       (match type of Hs with wordSem.share_inst ?op _ ?ad' _ = _ =>
          destruct (share_store_lemma1 ac k f f' s t1' lens op v ad' res s1) as (t2 & E2 & HR);
          [split; [exact Hs|]; split; [exact H1|]; split; [lia|]; split; [auto|exact Hres]|] end);
       rewrite E2; eexists; split; [reflexivity|exact HR] ]).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_ShareInst_correct_lemma" *)
Theorem evaluate_ShareInst_correct_lemma : forall ac k f f' s t lens op v ad offset res s1,
  wordSem.evaluate (wordLang.ShareInst op (2 * v) (wordLang.Op asm.Add [wordLang.Var (2 * ad); wordLang.Const offset]), s) = (res, s1) /\
  res <> SOME wordSem.Error /\
  state_rel ac k f f' s t lens 0 /\
  v < f' + k /\
  ad < f' + k ->
  exists ck t1,
    evaluate (wShareInst op (2 * v) (Addr (2 * ad) offset) (k, (f, f')), set_clock (ck + clock t) t) =
      (OPTION_MAP compile_result res, t1) /\
    ((res = NONE /\ state_rel ac k f f' s1 t1 lens 0) \/
     (exists fv, res = SOME (wordSem.FinalFFI fv) /\ wordSem.ffi s1 = ffi t1 /\ wordSem.clock s1 = clock t1)).
Proof.
  intros ac k f f' s t lens op v ad offset res s1 (Hev & Hres & H & Hv & Had).
  destruct op.
  1-4: match type of Hev with context [wordLang.ShareInst ?op _ _] =>
    destruct (evaluate_ShareInst_Load ac k f f' s t lens op v ad offset res s1) as (ck & t1 & E & HR);
    [split; [exact Hev|]; split; [exact Hres|]; split; [exact H|]; split; [exact Hv|]; split; [exact Had|auto]
    |exists ck, t1; split; [exact E|tauto]] end.
  all: match type of Hev with context [wordLang.ShareInst ?op _ _] =>
    destruct (evaluate_ShareInst_Store ac k f f' s t lens op v ad offset res s1) as (ck & t1 & E & HR);
    [split; [exact Hev|]; split; [exact H|]; split; [exact Hv|]; split; [exact Had|]; split; [exact Hres|auto]
    |exists ck, t1; split; [exact E|tauto]] end.
Qed.

End ShareInst.

(** ** Results and calls (HOL lines 7546-7767) *)

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "compile_prog_stack_size" *)
Theorem compile_prog_stack_size : forall {a} (ac : asm_config a) perf word_prog x k bs stack_prog fs bs2,
  compile_prog ac perf word_prog x k bs = (stack_prog, (fs, bs2)) -> x - k <= fs.
Proof.
  intros a ac perf word_prog x k bs stack_prog fs bs2 H. unfold compile_prog in H. cbv zeta in H.
  destruct (comp _ _ _ _ _) as [q1 bms] in H. injection H as _ <- _.
  unfold MAX. destruct (_ <? _) eqn:E1; destruct (_ =? 0) eqn:E2; to_prop; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "SUB_SUB_SUB_MAX" *)
Theorem SUB_SUB_SUB_MAX : forall a0 b c0, a0 - b - (c0 - b) = a0 - MAX b c0.
Proof. intros. unfold MAX. destruct (b <? c0) eqn:E; to_prop; lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAX_LE" *)
Theorem MAX_LE : forall a0 b, a0 <= b -> MAX a0 b = b.
Proof. intros. unfold MAX. destruct (a0 <? b) eqn:E; to_prop; lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_ret_aux_thm" *)
Theorem copy_ret_aux_thm : forall {a} k f n,
  @copy_ret_aux a k f 0 = Skip /\
  @copy_ret_aux a k f (SUC n) = list_Seq [StackLoad k n; StackStore k (n + f); copy_ret_aux k f n].
Proof.
  intros a k f n. split; [reflexivity|]. rewrite copy_ret_aux_def.
  replace (SUC n =? 0) with false by (symmetry; apply N.eqb_neq; lia). cbv zeta.
  replace (SUC n - 1) with n by lia. reflexivity.
Qed.

Section CopyRet.
Context {a : N} {c ffi_t : Type}.
Implicit Types (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_copy_ret_Seq" *)
Theorem evaluate_copy_ret_Seq : forall perf b kf vs (k0 : prog a) t,
  evaluate (copy_ret perf b kf vs k0, t) = evaluate (Seq (copy_ret perf b kf vs Skip) k0, t).
Proof.
  intros perf b [k [f f']] vs k0 t. unfold copy_ret. destruct (num_stack_ret k vs =? 0) eqn:E.
  - rewrite ev_seq, ev_skip. reflexivity.
  - rewrite ev_seq_assoc. apply ev_seq_congr. intros t1. unfold SeqStackFree. rewrite E.
    rewrite ev_seq_assoc. apply ev_seq_congr. intros t2. rewrite ev_seq, ev_skip. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_copy_ret_Seq'" *)
Theorem evaluate_copy_ret_Seq' : forall is_handle k f f' vs (k0 : prog a) t,
  evaluate (copy_ret false is_handle (k, (f, f')) vs k0, t) =
  let n := num_stack_ret k vs in
  evaluate (Seq (copy_ret_aux k (if is_handle then f + 3 else f) n) (SeqStackFree n k0), t).
Proof.
  intros is_handle k f f' vs k0 t. cbv zeta. unfold copy_ret. destruct (num_stack_ret k vs =? 0) eqn:E.
  - apply N.eqb_eq in E. rewrite E. rewrite (proj1 (copy_ret_aux_thm k _ 0)). unfold SeqStackFree. cbn [N.eqb].
    rewrite ev_seq, ev_skip. reflexivity.
  - reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "get_labels_copy_ret" *)
Theorem get_labels_copy_ret : forall perf is_handle kf vs (q : prog a),
  get_labels (copy_ret perf is_handle kf vs q) = get_labels q.
Proof.
  intros perf is_handle [k [f f']] vs q. unfold copy_ret.
  assert (Hc : forall n f0, get_labels (@copy_ret_aux a k f0 n) = EMPTY).
  { intros n f0. induction n as [|n IH] using N.peano_ind; [rewrite (proj1 (copy_ret_aux_thm k f0 0)); reflexivity|].
    rewrite (proj2 (copy_ret_aux_thm k f0 n)). cbn [list_Seq get_labels]. rewrite IH.
    apply set_ext; intros x; unfold pred_set.UNION, pred_set.EMPTY, pred_set.IN; tauto. }
  destruct (num_stack_ret k vs =? 0) eqn:E; [reflexivity|].
  cbn [get_labels]. rewrite Hc. unfold SeqStackFree. rewrite E. cbn [get_labels].
  apply set_ext; intros x; unfold pred_set.UNION, pred_set.EMPTY, pred_set.IN; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_copy_ret_aux" *)
Theorem evaluate_copy_ret_aux : forall k f n t,
  use_stack t /\ f <> 0 /\ f <= LENGTH (stackSem.stack t) - (stack_space t + n) ->
  exists t',
    evaluate (copy_ret_aux k f n, t) = (NONE, t') /\
    exists t'_stack t'_regs,
      t' = set_regs t'_regs (set_stack t'_stack t) /\
      LENGTH t'_stack = LENGTH (stackSem.stack t) /\
      stack_space t' = stack_space t /\
      DROP (f + n + stack_space t') t'_stack = DROP (f + n + stack_space t) (stackSem.stack t) /\
      (forall i, i <> k -> stackSem.get_var i t' = stackSem.get_var i t) /\
      (forall m, m < f - n ->
         EL m (DROP (n + stack_space t') t'_stack) = EL m (DROP (n + stack_space t) (stackSem.stack t))) /\
      (let stack' := DROP (stack_space t') t'_stack in
       let stack := DROP (stack_space t) (stackSem.stack t) in
       forall x, x < n -> EL (x + f) stack' = EL x stack).
Proof.
  intros k f n. induction n as [|n IH] using N.peano_ind; intros t (Hu & Hf & Hl).
  - exists t. rewrite (proj1 (copy_ret_aux_thm k f 0)), ev_skip. split; [reflexivity|].
    exists (stackSem.stack t), (regs t). split; [destruct t; reflexivity|].
    do 3 (split; [reflexivity|]). split; [reflexivity|]. split; [reflexivity|]. cbv zeta. intros x Hx; lia.
  - rewrite (proj2 (copy_ret_aux_thm k f n)). cbn [list_Seq].
    rewrite ev_seq, ev_stackload. unfold is_true in Hu. rewrite Hu. cbn [negb].
    rewrite (proj2 (N.ltb_lt _ _)) by lia.
    set (v := EL (stack_space t + n) (stackSem.stack t)).
    rewrite ev_seq, ev_stackstore. unfold stackSem.set_var. stk_fields. rewrite Hu. cbn [negb].
    rewrite (proj2 (N.leb_gt _ _)) by lia. unfold stackSem.get_var. stk_fields.
    rewrite FLOOKUP_UPDATE, decide_True by reflexivity.
    set (t2 := set_stack (LUPDATE v (stack_space t + (n + f)) (stackSem.stack t)) (set_regs (regs t |+ (k, v)) t)).
    destruct (IH t2) as (t3 & E3 & S & R & -> & HL & HS & HD & HG & HM & HX).
    { unfold t2. stk_fields. rewrite LENGTH_LUPDATE'. split; [exact Hu|]. split; [exact Hf|]. lia. }
    rewrite E3. eexists; split; [reflexivity|].
    exists S, R. unfold t2 in *. stk_fields. rewrite LENGTH_LUPDATE' in HL.
    split; [destruct t; reflexivity|]. split; [exact HL|]. split; [reflexivity|].
    split.
    { replace (f + N.succ n + stack_space t) with (1 + (f + n + stack_space t)) by lia.
      rewrite <- (DROP_DROP_EQ (f + n + stack_space t) 1 S), HD, DROP_DROP_EQ, DROP_LUPDATE_lt by lia. reflexivity. }
    split.
    { intros i Hi. specialize (HG i Hi). unfold stackSem.get_var in *. stk_fields. rewrite HG, FLOOKUP_UPDATE.
      rewrite decide_False by congruence. reflexivity. }
    split.
    { intros m Hm. specialize (HM (m + 1) ltac:(lia)). rewrite !EL_DROP_add in HM |- *.
      replace (N.succ n + stack_space t + m) with (n + stack_space t + (m + 1)) by lia. rewrite HM.
      rewrite EL_LUPDATE_if by lia. rewrite decide_False by lia. reflexivity. }
    cbv zeta in HX |- *. intros x Hx. rewrite !EL_DROP_add.
    destruct (N.eq_dec x n) as [->|Hxn].
    + rewrite (EL_DROP_eq (f + n + stack_space t) S (LUPDATE v (stack_space t + (n + f)) (stackSem.stack t))) by (exact HD || lia).
      replace (stack_space t + (n + f)) with (stack_space t + (n + f)) by reflexivity.
      rewrite EL_LUPDATE_if by lia. rewrite decide_True by lia. reflexivity.
    + specialize (HX x ltac:(lia)). rewrite !EL_DROP_add in HX. rewrite HX.
      rewrite EL_LUPDATE_if by lia. rewrite decide_False by lia. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_copy_ret_aux_clock" *)
Theorem evaluate_copy_ret_aux_clock : forall clk k f n t,
  evaluate (copy_ret_aux k f n, set_clock clk t) =
  (I ## (fun t => set_clock clk t)) (evaluate (copy_ret_aux k f n, t)).
Proof.
  intros clk k f n. induction n as [|n IH] using N.peano_ind; intros t.
  - rewrite (proj1 (copy_ret_aux_thm k f 0)), !ev_skip. reflexivity.
  - rewrite (proj2 (copy_ret_aux_thm k f n)). cbn [list_Seq]. rewrite !ev_seq, !ev_stackload. stk_fields.
    destruct (use_stack t) eqn:Eu; cbn [negb]; [|reflexivity].
    destruct (_ <? _); [|destruct t; reflexivity].
    rewrite !ev_seq, !ev_stackstore. unfold stackSem.set_var, stackSem.get_var. stk_fields. rewrite Eu. cbn [negb].
    destruct (_ <=? _); [destruct t; reflexivity|].
    rewrite !FLOOKUP_UPDATE, decide_True by reflexivity.
    replace (set_stack _ (set_regs _ (set_clock clk t))) with
      (set_clock clk (set_stack (LUPDATE (EL (stack_space t + n) (stackSem.stack t)) (stack_space t + (n + f)) (stackSem.stack t))
        (set_regs (regs t |+ (k, EL (stack_space t + n) (stackSem.stack t))) t))) by (destruct t; reflexivity).
    apply IH.
Qed.

End CopyRet.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_cont_loop_handler" *)
Theorem evaluate_cont_loop_handler : forall {a c ffi_t} (c0 : wordLang.prog a) (s : wordSem.state a c ffi_t) res s1,
  wordSem.evaluate (c0, s) = (res, s1) /\ wordSem.cont_loop res -> wordSem.handler s1 = wordSem.handler s.
Proof.
  intros a c ffi_t c0 s res s1 [E Hc]. pose proof (stack_swap.evaluate_stack_swap c0 s) as H. rewrite E in H.
  destruct res as [[]|]; cbn in Hc; try discriminate; destruct H as (_ & H & _); exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "get_labels_loc_check_subspt" *)
Theorem get_labels_loc_check_subspt : forall {a} (p : prog a) (c1 c2 : spt (prog a)),
  get_labels p SUBSET loc_check c1 /\ subspt c1 c2 -> get_labels p SUBSET loc_check c2.
Proof.
  intros a p c1 c2 [H1 H2] x Hx. apply (loc_check_SUBSET c1 c2 H2), H1, Hx.
Qed.

Section StateRelCut.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_dec_clock" *)
Theorem state_rel_dec_clock : forall ac k f f' (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t) lens extra,
  state_rel ac k f f' s t lens extra ->
  state_rel ac k f f' (wordSem.dec_clock s) (stackSem.dec_clock t) lens extra.
Proof.
  intros ac k f f' s t lens extra H. sr_destr H. unfold wordSem.dec_clock, stackSem.dec_clock.
  sr_split; ws_fields; stk_fields; try assumption. rewrite Hclock. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_cut_state" *)
Theorem state_rel_cut_state : forall ac k f f' (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t) lens names s',
  state_rel ac k f f' s t lens 0 /\
  wordSem.cut_state (names, LN) s = SOME s' ->
  state_rel ac k f f' s' t lens 0.
Proof.
  intros ac k f f' s t lens names s' [H Hc]. unfold wordSem.cut_state, wordSem.cut_env, wordSem.cut_envs, wordSem.cut_names in Hc.
  cbn [FST SND fst snd] in Hc.
  destruct (classical_dec (domain names SUBSET domain (wordSem.locals s))); [|discriminate].
  destruct (classical_dec (domain (@LN unit) SUBSET domain (wordSem.locals s))) as [_|C].
  2:{ exfalso. apply C. intros x Hx. cbn in Hx. unfold pred_set.EMPTY, pred_set.IN in Hx. contradiction. }
  injection Hc as <-. sr_destr H. sr_split; ws_fields; try assumption.
  - apply wf_union. split; apply wf_inter.
  - intros n v Hn. rewrite lookup_union, !lookup_inter, lookup_LN in Hn.
    destruct (lookup n (wordSem.locals s)) eqn:El; [|discriminate]. destruct (lookup n names); [|discriminate].
    injection Hn as <-. apply Hloc, El.
Qed.

End StateRelCut.
