(** * CakeML [word_to_stackProof]: liveness bitmaps and garbage collection

    Part of the port of
    [cakeml/compiler/backend/proofs/word_to_stackProofScript.sml] (HOL lines
    1600-2433): the stack encodings ([enc_stack], [dec_stack]) agree with
    the abstract stack, the garbage collector and [alloc] are simulated.

    Notes: as in [state_rel.v].  HOL's type abbreviation [result] (for
    [wordSem$result]) and the ML binding [stack_evaluate_add_clock_NONE]
    are not declarations of theorems and are not ported; wordSem's result
    constructors are written [wordSem.X].  [evaluate_wLive] drops HOL's
    unused existential [bs5]. *)

From Galette Require Import Base Classical.
From Stdlib Require Import Permutation Sorting.Sorted.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
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
From Galette.cakeml.compiler.backend.semantics Require Import wordConvs.
From Galette.cakeml.compiler.backend.semantics Require wordSem.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import stack_max dec_clock stack_swap.
From Galette.cakeml.compiler.backend.semantics Require Import stackSem stackProps.
From Galette.cakeml.compiler.backend.proofs.word_to_stackProof Require Import basic compile_props state_rel.
Import wordLang (word_loc, Word, Loc).
Import wordSem (stack_frame, StackFrame).
Open Scope N_scope.

Section Bitmaps.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "read_bitmap_not_empty" *)
Theorem read_bitmap_not_empty : forall (stack : list (word a)) a0,
  read_bitmap stack = SOME a0 -> stack <> [].
Proof. intros stack a0 H E. subst stack. discriminate. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "n2w_lsr_1" *)
Theorem n2w_lsr_1 : forall n, n < dimword a -> word_lsr (n2w n : word a) 1 = n2w (n DIV 2).
Proof.
  intros n H. apply word_eq_w2n. rewrite w2n_lsr, !w2n_n2w, N.mod_small by exact H.
  rewrite N.mod_small; [rewrite N.pow_1_r; reflexivity|].
  apply N.le_lt_trans with n; [apply N.Div0.div_le_upper_bound; lia|exact H].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "handler_bitmap_props" *)
Theorem handler_bitmap_props : forall (stack : list (word a)),
  good_dimindex a -> read_bitmap (n2w 4 :: stack) = SOME [false; false].
Proof.
  intros stack Hg. assert (Hd : dimindex a = 32 \/ dimindex a = 64) by exact Hg.
  cbn [read_bitmap]. rewrite word_msb_n2w, BIT_testbit.
  replace (N.testbit 4 (dimindex a - 1)) with false by (destruct Hd as [-> | ->]; reflexivity).
  unfold bit_length. rewrite w2n_n2w.
  assert (H4 : 4 < dimword a) by (unfold dimword; destruct Hd as [-> | ->]; reflexivity).
  rewrite N.mod_small by exact H4. replace (N.size 4 - 1) with 2 by reflexivity.
  rewrite GENLIST_seq. change (N.to_nat 2) with 2%nat. cbn [seq List.map N.of_nat].
  rewrite !fcp_index_n2w by (destruct Hd as [-> | ->]; lia).
  rewrite !BIT_testbit. reflexivity.
Qed.

End Bitmaps.

(** ** Inversion of [abs_stack] (Galette-only) *)

Section AbsStackInv.
Context {a : N}.

Lemma abs_stack_nil_inv (bs : list (word a)) sstack lens astack :
  abs_stack bs [] sstack lens = SOME astack -> sstack = [Word (n2w 0)] /\ lens = [] /\ astack = [].
Proof.
  destruct lens; [|discriminate]. cbn. destruct (decide _) as [->|]; [|discriminate].
  intros E; injection E as <-. auto.
Qed.

Lemma abs_stack_NONE_inv (bs : list (word a)) n l0 l xs sstack lens astack :
  abs_stack bs (StackFrame n l0 l NONE :: xs) sstack lens = SOME astack ->
  exists w stack len lens' bits ys,
    sstack = w :: stack /\ lens = len :: lens' /\ full_read_bitmap bs w = SOME bits /\
    LENGTH bits = len /\ len <= LENGTH stack /\
    abs_stack bs xs (DROP len stack) lens' = SOME ys /\
    astack = (NONE, (bits, TAKE len stack)) :: ys.
Proof.
  intros H. destruct sstack as [|w stack]; [discriminate|]. destruct lens as [|len lens']; [discriminate|].
  cbn [abs_stack] in H. destruct (full_read_bitmap bs w) as [bits|] eqn:Eb; [|discriminate].
  destruct (LENGTH bits =? len) eqn:El; cbn [negb] in H; [|discriminate].
  destruct (LENGTH stack <? len) eqn:Es; [discriminate|]. cbv zeta in H.
  destruct (abs_stack bs xs (DROP len stack) lens') as [ys|] eqn:Ey; [|discriminate].
  injection H as <-. apply N.eqb_eq in El. apply N.ltb_ge in Es.
  exists w, stack, len, lens', bits, ys. repeat split; auto.
Qed.

Lemma abs_stack_SOME_inv (bs : list (word a)) n l0 l hh xs sstack lens astack :
  abs_stack bs (StackFrame n l0 l (SOME hh) :: xs) sstack lens = SOME astack ->
  exists loc hv w stack len lens' bits ys,
    sstack = Word (n2w 1) :: loc :: hv :: w :: stack /\ lens = len :: lens' /\
    full_read_bitmap bs w = SOME bits /\
    LENGTH bits = len /\ len <= LENGTH stack /\
    abs_stack bs xs (DROP len stack) lens' = SOME ys /\
    astack = (SOME (loc, hv), (bits, TAKE len stack)) :: ys.
Proof.
  intros H. destruct sstack as [|w0 stack0]; [discriminate|]. destruct lens as [|len lens']; [discriminate|].
  cbn [abs_stack] in H. destruct (bool_decide (w0 = Word (n2w 1))) eqn:E1; cbn [negb] in H; [|discriminate].
  apply bool_decide_spec in E1. subst w0.
  destruct stack0 as [|loc [|hv [|w stack]]]; try discriminate.
  destruct (full_read_bitmap bs w) as [bits|] eqn:Eb; [|discriminate].
  destruct (LENGTH bits =? len) eqn:El; cbn [negb] in H; [|discriminate].
  destruct (LENGTH stack <? len) eqn:Es; [discriminate|]. cbv zeta in H.
  destruct (abs_stack bs xs (DROP len stack) lens') as [ys|] eqn:Ey; [|discriminate].
  injection H as <-. apply N.eqb_eq in El. apply N.ltb_ge in Es.
  exists loc, hv, w, stack, len, lens', bits, ys. repeat split; auto.
Qed.

Lemma full_read_bitmap_not_0 (bs : list (word a)) w bits :
  full_read_bitmap bs w = SOME bits -> w <> Word (n2w 0).
Proof. intros H ->. unfold full_read_bitmap in H. rewrite (proj2 (bool_decide_spec (n2w 0 = n2w 0))) in H by reflexivity. discriminate. Qed.

End AbsStackInv.

Section EncStack.
Context {a : N}.

Lemma stack_enc_stack_cons (bs : list (word a)) w ws :
  stackSem.enc_stack bs (w :: ws) =
  if bool_decide (w = Word (n2w 0)) then (if bool_decide (ws = []) then SOME [] else NONE)
  else
    match full_read_bitmap bs w with
    | NONE => NONE
    | SOME bits =>
        match filter_bitmap bits ws with
        | NONE => NONE
        | SOME (ts, ws') =>
            match stackSem.enc_stack bs ws' with
            | NONE => NONE
            | SOME rs => SOME (ts ++ rs)
            end
        end
    end.
Proof. exact (proj2 (@stackSem.enc_stack_def a) bs w ws). Qed.

Lemma n2w_1_neq_0 : (n2w 1 : word a) <> n2w 0.
Proof.
  intros E. apply (f_equal w2n) in E. rewrite !w2n_n2w in E.
  assert (H : 1 < dimword a).
  { unfold dimword. pose proof (@dimindex_pos a). apply N.lt_le_trans with (2 ^ 1); [reflexivity|].
    apply N.pow_le_mono_r; lia. }
  rewrite N.mod_small in E by exact H. rewrite N.Div0.mod_0_l in E. discriminate.
Qed.

Lemma bd_false' (P : Prop) {d : Decision P} : ~ P -> bool_decide P = false.
Proof. intros H. destruct (bool_decide P) eqn:E; [apply bool_decide_spec in E; contradiction|reflexivity]. Qed.

Lemma bd_true' (P : Prop) {d : Decision P} : P -> bool_decide P = true.
Proof. intros H. apply bool_decide_spec. exact H. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "enc_stack_lemma" *)
Theorem enc_stack_lemma : forall k len (bs : list (word a)) (wstack : list (stack_frame a)) sstack lens astack
    (bs' : list (word a)),
  good_dimindex a /\
  LENGTH bs + 1 < dimword a /\
  abs_stack bs wstack sstack lens = SOME astack /\
  1 <= LENGTH bs /\
  HD bs = n2w 4 /\
  stack_rel_aux k len wstack astack ->
  stackSem.enc_stack bs sstack = SOME (wordSem.enc_stack wstack).
Proof.
  intros k len bs wstack. induction wstack as [|[n l0 l h] xs IH];
    intros sstack lens astack bs' (Hg & Hl & Ha & H1 & H4 & Hr).
  - apply abs_stack_nil_inv in Ha as (-> & -> & ->). rewrite stack_enc_stack_cons.
    rewrite bd_true' by reflexivity. rewrite bd_true' by reflexivity. reflexivity.
  - destruct h as [[h1 [p1 p2]]|].
    + apply abs_stack_SOME_inv in Ha as (loc & hv & w & stack & len' & lens' & bits & ys & -> & -> & Hb & <- & Hls & Hy & ->).
      cbn [stack_rel_aux] in Hr. destruct Hr as (_ & _ & _ & Hf & _ & Hr).
      rewrite stack_enc_stack_cons. rewrite bd_false' by (intros E; apply (f_equal (fun x => match x with Word w => w | Loc _ _ => n2w 7 end)) in E;
        exact (n2w_1_neq_0 E)).
      destruct bs as [|b0 bs0]; [cbn in H1; lia|]. cbn [HD] in H4. subst b0.
      cbn [full_read_bitmap]. rewrite bd_false' by apply n2w_1_neq_0.
      rewrite WORD_SUB_REFL, w2n_n2w, N.Div0.mod_0_l. rewrite DROP_skipn. cbn [skipn N.to_nat].
      rewrite handler_bitmap_props by exact Hg. cbn [filter_bitmap].
      rewrite stack_enc_stack_cons. rewrite bd_false' by (apply (full_read_bitmap_not_0 _ _ _ Hb)).
      rewrite Hb. apply filter_bitmap_lemma in Hf. rewrite MAP_SND_MAP_FST in Hf.
      rewrite Hf. rewrite (IH _ _ _ bs' (conj Hg (conj Hl (conj Hy (conj H1 (conj eq_refl Hr)))))).
      reflexivity.
    + apply abs_stack_NONE_inv in Ha as (w & stack & len' & lens' & bits & ys & -> & -> & Hb & <- & Hls & Hy & ->).
      cbn [stack_rel_aux] in Hr. destruct Hr as (_ & Hf & _ & Hr).
      rewrite stack_enc_stack_cons. rewrite bd_false' by (apply (full_read_bitmap_not_0 _ _ _ Hb)).
      rewrite Hb. apply filter_bitmap_lemma in Hf. rewrite MAP_SND_MAP_FST in Hf.
      rewrite Hf. rewrite (IH _ _ _ bs' (conj Hg (conj Hl (conj Hy (conj H1 (conj H4 Hr)))))).
      reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "IMP_enc_stack" *)
Theorem IMP_enc_stack : forall {c ffi_t} ac k (s1 : wordSem.state a (N * c) ffi_t) (t1 : stackSem.state a c ffi_t) lens,
  state_rel ac k 0 0 s1 t1 lens 0 ->
  stackSem.enc_stack (bitmaps t1) (DROP (stack_space t1) (stackSem.stack t1)) =
    SOME (wordSem.enc_stack (wordSem.stack s1)).
Proof.
  intros c ffi_t ac k s1 t1 lens H. sr_destr H. destruct Hsr as (_ & astack & Ha & _ & Hr).
  rewrite N.add_0_r in Ha. rewrite (DROP_skipn 0) in Ha. cbn [N.to_nat skipn] in Ha.
  eapply (enc_stack_lemma k _ _ _ _ _ _ []). repeat split; try eassumption. lia.
Qed.

End EncStack.

(** ** [map_bitmap] and [dec_stack] *)

Section MapBitmap.
Context {A B : Type}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "map_bitmap_success" *)
Theorem map_bitmap_success : forall (bs : list bool) (stack a0 b ls : list A),
  filter_bitmap bs stack = SOME (a0, b) /\ LENGTH ls = LENGTH a0 ->
  exists x (z : list A),
    map_bitmap bs ls stack = SOME (x, ([], DROP (LENGTH bs) stack)) /\
    filter_bitmap bs x = SOME (ls, []).
Proof.
  induction bs as [|c bs IH]; intros stack a0 b ls [H Hl].
  - cbn in H. injection H as <- <-. destruct ls; [|cbn in Hl; lia].
    exists [], []. rewrite DROP_skipn. split; reflexivity.
  - destruct stack as [|r stack]; [destruct c; discriminate|].
    destruct c; cbn in H.
    + destruct (filter_bitmap bs stack) as [[ts rs]|] eqn:E; [|discriminate]. injection H as <- <-.
      destruct ls as [|t ls]; [cbn in Hl; lia|]. rewrite !LENGTH_cons' in Hl.
      assert (Hl' : LENGTH ls = LENGTH ts) by (cbn [LENGTH] in Hl; lia).
      destruct (IH stack ts rs ls (conj E Hl')) as (x & z & H1 & H2).
      exists (t :: x), z. cbn [map_bitmap filter_bitmap]. rewrite H1, H2. split; [|reflexivity].
      rewrite LENGTH_cons'. cbn [DROP]. replace (LENGTH bs + 1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
      replace (LENGTH bs + 1 - 1) with (LENGTH bs) by lia. reflexivity.
    + destruct (IH stack a0 b ls (conj H Hl)) as (x & z & H1 & H2).
      exists (r :: x), z. cbn [map_bitmap filter_bitmap]. rewrite H1, H2. split; [|reflexivity].
      rewrite LENGTH_cons'. cbn [DROP]. replace (LENGTH bs + 1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
      replace (LENGTH bs + 1 - 1) with (LENGTH bs) by lia. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "map_bitmap_more" *)
Theorem map_bitmap_more : forall (bs : list bool) (ls stack : list A) (n : N) a0 c0 ls',
  map_bitmap bs ls stack = SOME (a0, ([], c0)) ->
  map_bitmap bs (ls ++ ls') stack = SOME (a0, (ls', c0)).
Proof.
  induction bs as [|b bs IH]; intros ls stack n a0 c0 ls' H.
  - cbn in H. injection H as Ha Hl Hc. subst. reflexivity.
  - destruct b; cbn in H |- *.
    + destruct ls as [|t ls]; [discriminate|]. destruct stack as [|r stack]; [discriminate|].
      destruct (map_bitmap bs ls stack) as [[xs [ys zs]]|] eqn:E; [|discriminate].
      injection H as Ha Hy Hz. subst. cbn [app]. rewrite (IH ls stack n xs c0 ls' E). reflexivity.
    + destruct stack as [|r stack]; [discriminate|].
      destruct (map_bitmap bs ls stack) as [[xs [ys zs]]|] eqn:E; [|discriminate].
      injection H as Ha Hy Hz. subst. rewrite (IH ls stack n xs c0 ls' E). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "map_bitmap_more_simp" *)
Theorem map_bitmap_more_simp : forall (bs : list bool) (l : list B) (ls stack : list A) a0 c0,
  map_bitmap bs (TAKE (LENGTH l) ls) stack = SOME (a0, ([], c0)) ->
  map_bitmap bs ls stack = SOME (a0, (DROP (LENGTH l) ls, c0)).
Proof.
  intros bs l ls stack a0 c0 H. apply (map_bitmap_more _ _ _ 0 _ _ (DROP (LENGTH l) ls)) in H.
  rewrite TAKE_firstn, DROP_skipn, firstn_skipn in H. rewrite DROP_skipn. exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "map_bitmap_LLOOKUP_F" *)
Theorem map_bitmap_LLOOKUP_F : forall (bm : list bool) (ls stack : list A) n res ls1 stack1,
  oEL n bm = SOME false /\
  map_bitmap bm ls stack = SOME (res, (ls1, stack1)) ->
  exists v, oEL n res = SOME v /\ oEL n stack = SOME v.
Proof.
  induction bm as [|b bm IH]; intros ls stack n res ls1 stack1 [Hn H]; [discriminate|].
  cbn [oEL] in Hn. destruct b; cbn in H.
  - destruct ls as [|t ls]; [discriminate|]. destruct stack as [|r stack]; [discriminate|].
    destruct (map_bitmap bm ls stack) as [[xs [ys zs]]|] eqn:E; [|discriminate].
    injection H as Ha Hy Hz. subst. destruct (n =? 0) eqn:En; [discriminate|].
    destruct (IH ls stack (n - 1) xs ls1 stack1 (conj Hn E)) as (v & H1 & H2).
    exists v. cbn [oEL]. rewrite En. split; assumption.
  - destruct stack as [|r stack]; [discriminate|].
    destruct (map_bitmap bm ls stack) as [[xs [ys zs]]|] eqn:E; [|discriminate].
    injection H as Ha Hy Hz. subst. cbn [oEL]. destruct (n =? 0).
    + exists r. split; reflexivity.
    + exact (IH ls stack (n - 1) xs ls1 stack1 (conj Hn E)).
Qed.

End MapBitmap.

Section DecStack.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_stack_dec_stack_shape" *)
Theorem word_stack_dec_stack_shape : forall (ls : list (word_loc a)) wstack res n,
  wordSem.dec_stack ls wstack = SOME res /\ n < LENGTH wstack ->
  (is_true (is_handler_frame (EL n wstack)) <-> is_true (is_handler_frame (EL n res))).
Proof.
  intros ls wstack; revert ls. induction wstack as [|[m l0 l h] ws IH]; intros ls res n [H Hn];
    [cbn in Hn; lia|].
  cbn [wordSem.dec_stack] in H. destruct (_ <? _); [discriminate|].
  destruct (wordSem.dec_stack (DROP (LENGTH l) ls) ws) as [r|] eqn:E; [|discriminate].
  injection H as <-. destruct n as [|n] using N.peano_ind; [cbn; destruct h; reflexivity|].
  rewrite !EL_SUC. cbn [TL]. apply (IH (DROP (LENGTH l) ls) r n). split; [exact E|]. rewrite LENGTH_cons' in Hn. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "sorted_env_zip" *)
Theorem sorted_env_zip : forall (l0 : list (N * word_loc a)) (l : list (N * word_loc a)) (ls : list (word_loc a)) x n,
  sorted_env (StackFrame n l0 l x) /\ LENGTH ls = LENGTH l ->
  sorted_env (StackFrame n l0 (ZIP (MAP FST l, ls)) x).
Proof.
  intros l0 l ls x n [H Hl]. unfold sorted_env in *.
  assert (M : forall {B} (f : B -> N) (l' : list B), SORTED (fun x y => f x > f y) l' <->
            SORTED (fun x y => x > y) (List.map f l')).
  { intros B f. induction l' as [|x' [|y' l'] IH]; [tauto|cbn; tauto|]. cbn [SORTED List.map] in *.
    rewrite IH. reflexivity. }
  apply (M _ FST) in H. apply (M _ FST).
  replace (List.map FST (ZIP (MAP FST l, ls))) with (List.map FST l); [exact H|].
  rewrite !LENGTH_length in Hl. apply Nat2N.inj in Hl. clear H M. revert ls Hl. induction l as [|[k v] l IH]; intros [|w ls] Hl;
    cbn in Hl |- *; try lia; [reflexivity|]. f_equal. apply IH. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_stack_dec_stack_sorted" *)
Theorem word_stack_dec_stack_sorted : forall (ls : list (word_loc a)) (wstack : list (stack_frame a)) res,
  wordSem.dec_stack ls wstack = SOME res /\
  EVERY (fun f => ⌜sorted_env f⌝) wstack ->
  EVERY (fun f => ⌜sorted_env f⌝) res.
Proof.
  intros ls wstack; revert ls. induction wstack as [|[m l0 l h] ws IH]; intros ls res [H He].
  - destruct ls; [|discriminate]. injection H as <-. reflexivity.
  - cbn [wordSem.dec_stack] in H. destruct (_ <? _) eqn:El; [discriminate|].
    destruct (wordSem.dec_stack (DROP (LENGTH l) ls) ws) as [r|] eqn:E; [|discriminate].
    injection H as <-. cbn [EVERY] in *. unfold is_true in *. rewrite andb_true_iff in *. destruct He as [H1 H2].
    split; [|eapply IH; split; [exact E|exact H2]].
    apply bool_decide_spec in H1. apply bool_decide_spec. apply sorted_env_zip. split; [exact H1|].
    apply N.ltb_ge in El. rewrite TAKE_firstn, !LENGTH_length, length_firstn. rewrite !LENGTH_length in El. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_stack_empty" *)
Theorem abs_stack_empty : forall (bs : list (word a)) ls stack lens,
  abs_stack bs [] ls lens = SOME stack -> ls = [Word (n2w 0)] /\ lens = [].
Proof. intros bs ls stack lens H. apply abs_stack_nil_inv in H as (? & ? & _). auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_frame_eq_def" *)
Definition abs_frame_eq (p q : option (word_loc a * word_loc a) * (list bool * list (word_loc a))) : Prop :=
  FST p = FST q /\ FST (SND p) = FST (SND q) /\ LENGTH (SND (SND p)) = LENGTH (SND (SND q)).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LIST_REL_abs_frame_eq_handler_val" *)
Theorem LIST_REL_abs_frame_eq_handler_val : forall xs ys,
  LIST_REL abs_frame_eq xs ys -> handler_val xs = handler_val ys.
Proof.
  intros xs ys H. induction H as [|[p1 [b1 f1]] [p2 [b2 f2]] l1 l2 Hr H IH]; [reflexivity|].
  destruct Hr as (E1 & E2 & E3). cbn in E1, E2, E3. subst p2 b2.
  destruct p1; cbn [handler_val]; rewrite E3, IH; reflexivity.
Qed.

End DecStack.

(** ** Decoding the stack after garbage collection *)

Section DecStackLemma.
Context {a : N}.

Lemma stack_dec_stack_cons (bs : list (word a)) ts w ws :
  stackSem.dec_stack bs ts (w :: ws) =
  if bool_decide (w = Word (n2w 0)) then
    (if andb (bool_decide (ts = [])) (bool_decide (ws = [])) then SOME [Word (n2w 0)] else NONE)
  else
    match full_read_bitmap bs w with
    | NONE => NONE
    | SOME bits =>
        match map_bitmap bits ts ws with
        | NONE => NONE
        | SOME (hd, (ts', ws')) =>
            match stackSem.dec_stack bs ts' ws' with
            | NONE => NONE
            | SOME rest => SOME (([w] ++ hd) ++ rest)
            end
        end
    end.
Proof. exact (proj2 (@stackSem.dec_stack_def a) bs ts w ws). Qed.

Lemma LIST_REL_LENGTH {A B} (R : A -> B -> Prop) xs ys : LIST_REL R xs ys -> LENGTH xs = LENGTH ys.
Proof. intros H. induction H; [reflexivity|]. rewrite !LENGTH_cons'. lia. Qed.

Lemma LIST_REL_DROP {A B} (R : A -> B -> Prop) xs ys n :
  LIST_REL R xs ys -> LIST_REL R (DROP n xs) (DROP n ys).
Proof.
  intros H. revert n. induction H as [|x y xs ys Hr H IH]; intros n; [constructor|].
  cbn [DROP]. destruct (n =? 0); [constructor; assumption|]. apply IH.
Qed.

Lemma LIST_REL_LASTN {A B} (R : A -> B -> Prop) xs ys n :
  LIST_REL R xs ys -> LIST_REL R (LASTN n xs) (LASTN n ys).
Proof.
  intros H. rewrite !LASTN_DROP2. rewrite (LIST_REL_LENGTH _ _ _ H). apply LIST_REL_DROP, H.
Qed.

Lemma MAP_FST_index_list_LENGTH {A B} (x : list A) (y : list B) k :
  LENGTH x = LENGTH y -> MAP FST (index_list x k) = MAP FST (index_list y k).
Proof. intros H. rewrite !MAP_FST_index_list, H. reflexivity. Qed.

Lemma ALOOKUP_ZIP_MAP_FST {B C} (l : list (N * B)) (ys : list C) n :
  LENGTH ys = LENGTH l -> (ALOOKUP (ZIP (MAP FST l, ys)) n = NONE <-> ALOOKUP l n = NONE).
Proof.
  revert ys; induction l as [|[k v] l IH]; intros [|y ys] H; rewrite ?LENGTH_cons' in H;
    try (cbn in H; lia); [split; reflexivity|].
  cbn [MAP List.map FST fst ZIP ALOOKUP]. cbn [ZIP] in IH.
  destruct (decide (k = n)); [split; discriminate|]. apply IH. lia.
Qed.

Lemma oEL_SOME_lt {A} n (l : list A) v : oEL n l = SOME v -> n < LENGTH l.
Proof.
  intros H. rewrite oEL_nth_error in H. assert (H2 : nth_error l (N.to_nat n) <> None) by congruence.
  apply nth_error_Some in H2. rewrite LENGTH_length. lia.
Qed.

Lemma oEL_TAKE_lt {A} n m (l : list A) : n < m -> oEL n (TAKE m l) = oEL n l.
Proof. intros H. apply LLOOKUP_TAKE. exact H. Qed.

(** One frame of [dec_stack] (Galette-only). *)
Lemma dec_frame_step (bs : list (word a)) w bits (stack ls : list (word_loc a)) k
    (l : list (N * word_loc a)) sdec' :
  full_read_bitmap bs w = SOME bits ->
  LENGTH bits <= LENGTH stack ->
  filter_bitmap bits (index_list (TAKE (LENGTH bits) stack) k) = SOME (MAP_FST adjust_names l, []) ->
  LENGTH l <= LENGTH ls ->
  stackSem.dec_stack bs (DROP (LENGTH l) ls) (DROP (LENGTH bits) stack) = SOME sdec' ->
  exists x,
    stackSem.dec_stack bs ls (w :: stack) = SOME (w :: x ++ sdec') /\
    LENGTH x = LENGTH bits /\
    filter_bitmap bits x = SOME (TAKE (LENGTH l) ls, []) /\
    (forall p, oEL p bits = SOME false -> oEL p x = oEL p stack).
Proof.
  intros Hb Hls Hf Hll Hd. assert (Hf2 := filter_bitmap_lemma _ _ _ _ Hf).
  rewrite MAP_SND_MAP_FST in Hf2.
  destruct (map_bitmap_success bits stack (MAP SND l) (DROP (LENGTH bits) stack) (TAKE (LENGTH l) ls))
    as (x & z & Hm & Hfx).
  { split; [exact Hf2|]. rewrite TAKE_firstn, !LENGTH_length, length_firstn, length_map.
    rewrite !LENGTH_length in Hll. lia. }
  apply map_bitmap_more_simp in Hm. exists x.
  pose proof (map_bitmap_length _ _ _ _ _ _ Hm) as [Hl1 Hl2].
  rewrite stack_dec_stack_cons, bd_false' by (apply (full_read_bitmap_not_0 _ _ _ Hb)).
  rewrite Hb, Hm, Hd. split; [reflexivity|]. split; [exact Hl2|]. split; [exact Hfx|].
  intros p Hp. destruct (map_bitmap_LLOOKUP_F bits _ _ p _ _ _ (conj Hp Hm)) as (v & H1 & H2).
  rewrite H1, H2. reflexivity.
Qed.

Lemma MAP_FST_MAP_FST {A B C} (f : A -> C) (xs : list (A * B)) : MAP FST (MAP_FST f xs) = MAP f (MAP FST xs).
Proof. induction xs as [|[x y] xs IH]; [reflexivity|]. cbn. f_equal. exact IH. Qed.

Lemma MAP_FST_ZIP {A B} (xs : list A) (ys : list B) : LENGTH ys = LENGTH xs -> MAP FST (ZIP (xs, ys)) = xs.
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys] H; rewrite ?LENGTH_cons' in H;
    try (cbn in H; lia); [reflexivity|]. cbn. f_equal. cbn in IH. apply IH. lia.
Qed.

Lemma MAP_SND_ZIP {A B} (xs : list A) (ys : list B) : LENGTH ys = LENGTH xs -> MAP SND (ZIP (xs, ys)) = ys.
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys] H; rewrite ?LENGTH_cons' in H;
    try (cbn in H; lia); [reflexivity|]. cbn. f_equal. cbn in IH. apply IH. lia.
Qed.

Lemma LENGTH_TAKE_le {A} n (l : list A) : n <= LENGTH l -> LENGTH (TAKE n l) = n.
Proof. intros H. rewrite TAKE_firstn, !LENGTH_length, length_firstn. rewrite LENGTH_length in H. lia. Qed.

Lemma LENGTH_DROP' {A} n (l : list A) : LENGTH (DROP n l) = LENGTH l - n.
Proof. rewrite DROP_skipn, !LENGTH_length, length_skipn. lia. Qed.

(** The frame relation is preserved by [dec_stack] (Galette-only). *)
Lemma frame_rel_step k (l0 l : list (N * word_loc a)) bits (stack ls x : list (word_loc a)) :
  (forall n v, ALOOKUP l0 n = SOME v /\ ALOOKUP l n = NONE ->
     adjust_names n < k + LENGTH bits /\
     oEL (k + LENGTH bits - (adjust_names n + 1)) bits = SOME false /\
     ALOOKUP (index_list (TAKE (LENGTH bits) stack) k) (n DIV 2) = SOME v) ->
  filter_bitmap bits (index_list (TAKE (LENGTH bits) stack) k) = SOME (MAP_FST adjust_names l, []) ->
  LENGTH bits <= LENGTH stack -> LENGTH l <= LENGTH ls ->
  LENGTH x = LENGTH bits ->
  filter_bitmap bits x = SOME (TAKE (LENGTH l) ls, []) ->
  (forall p, oEL p bits = SOME false -> oEL p x = oEL p stack) ->
  (forall n v, ALOOKUP l0 n = SOME v /\ ALOOKUP (ZIP (MAP FST l, TAKE (LENGTH l) ls)) n = NONE ->
     adjust_names n < k + LENGTH bits /\
     oEL (k + LENGTH bits - (adjust_names n + 1)) bits = SOME false /\
     ALOOKUP (index_list x k) (n DIV 2) = SOME v) /\
  filter_bitmap bits (index_list x k) = SOME (MAP_FST adjust_names (ZIP (MAP FST l, TAKE (LENGTH l) ls)), []).
Proof.
  intros Hold Hf Hls Hll Hlx Hfx Hp.
  assert (HT : LENGTH (TAKE (LENGTH l) ls) = LENGTH l) by (apply LENGTH_TAKE_le; exact Hll).
  assert (HT' : LENGTH (TAKE (LENGTH l) ls) = LENGTH (MAP FST l)) by (rewrite HT, !LENGTH_length, length_map; reflexivity).
  split.
  - intros n v [H1 H2]. apply (ALOOKUP_ZIP_MAP_FST l (TAKE (LENGTH l) ls) n HT) in H2.
    destruct (Hold n v (conj H1 H2)) as (A1 & A2 & A3). split; [exact A1|]. split; [exact A2|].
    unfold adjust_names in *.
    assert (HTb : LENGTH (TAKE (LENGTH bits) stack) = LENGTH bits) by (apply LENGTH_TAKE_le; exact Hls).
    rewrite ALOOKUP_index_list in A3 by lia. rewrite ALOOKUP_index_list by lia.
    rewrite HTb in A3. rewrite Hlx.
    assert (Hlt := oEL_SOME_lt _ _ _ A3). rewrite HTb in Hlt.
    rewrite oEL_TAKE_lt in A3 by lia.
    replace (LENGTH bits + k - (n DIV 2 + 1)) with (k + LENGTH bits - (n DIV 2 + 1)) in * by lia.
    rewrite Hp by exact A2. exact A3.
  - apply filter_bitmap_MAP_IMP. split.
    + rewrite MAP_SND_index_list, MAP_SND_MAP_FST, MAP_SND_ZIP by exact HT'. exact Hfx.
    + rewrite (MAP_FST_index_list_LENGTH x (TAKE (LENGTH bits) stack)).
      * apply filter_bitmap_IMP_MAP_FST in Hf. rewrite Hf. rewrite !MAP_FST_MAP_FST, MAP_FST_ZIP by exact HT'.
        reflexivity.
      * rewrite LENGTH_TAKE_le by exact Hls. exact Hlx.
Qed.

Lemma TAKE_app_exact {A} n (x y : list A) : LENGTH x = n -> TAKE n (x ++ y) = x.
Proof. intros <-. rewrite TAKE_firstn, LENGTH_length, Nat2N.id, firstn_app, firstn_all, Nat.sub_diag, app_nil_r. reflexivity. Qed.

Lemma DROP_app_exact' {A} n (x y : list A) : LENGTH x = n -> DROP n (x ++ y) = y.
Proof. intros <-. rewrite DROP_skipn, LENGTH_length, Nat2N.id, skipn_app, skipn_all, Nat.sub_diag. reflexivity. Qed.

Lemma abs_stack_NONE_eq (bs : list (word a)) n l0 l xs w bits stack len lens :
  full_read_bitmap bs w = SOME bits -> LENGTH bits = len -> len <= LENGTH stack ->
  abs_stack bs (StackFrame n l0 l NONE :: xs) (w :: stack) (len :: lens) =
  match abs_stack bs xs (DROP len stack) lens with
  | NONE => NONE
  | SOME ys => SOME ((NONE, (bits, TAKE len stack)) :: ys)
  end.
Proof.
  intros Hb Hl Hs. cbn [abs_stack]. rewrite Hb. rewrite (proj2 (N.eqb_eq _ _) Hl). cbn [negb].
  rewrite (proj2 (N.ltb_ge _ _) Hs). reflexivity.
Qed.

Lemma abs_stack_SOME_eq (bs : list (word a)) n l0 l hh xs loc hv w bits stack len lens :
  full_read_bitmap bs w = SOME bits -> LENGTH bits = len -> len <= LENGTH stack ->
  abs_stack bs (StackFrame n l0 l (SOME hh) :: xs) (Word (n2w 1) :: loc :: hv :: w :: stack) (len :: lens) =
  match abs_stack bs xs (DROP len stack) lens with
  | NONE => NONE
  | SOME ys => SOME ((SOME (loc, hv), (bits, TAKE len stack)) :: ys)
  end.
Proof.
  intros Hb Hl Hs. cbn [abs_stack]. rewrite bd_true' by reflexivity. cbn [negb]. rewrite Hb.
  rewrite (proj2 (N.eqb_eq _ _) Hl). cbn [negb]. rewrite (proj2 (N.ltb_ge _ _) Hs). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "dec_stack_lemma1" *)
Theorem dec_stack_lemma1 : forall k len (bs : list (word a)) (wstack : list (stack_frame a)) sstack lens astack wdec ls,
  good_dimindex a /\
  1 <= LENGTH bs /\
  HD bs = n2w 4 /\
  abs_stack bs wstack sstack lens = SOME astack /\
  stack_rel_aux k len wstack astack /\
  wordSem.dec_stack ls wstack = SOME wdec ->
  exists sdec bstack,
    stackSem.dec_stack bs ls sstack = SOME sdec /\
    abs_stack bs wdec sdec lens = SOME bstack /\
    stack_rel_aux k len wdec bstack /\
    LIST_REL abs_frame_eq astack bstack.
Proof.
  intros k len bs wstack. induction wstack as [|[n l0 l h] xs IH];
    intros sstack lens astack wdec ls (Hg & H1 & H4 & Ha & Hr & Hd).
  - apply abs_stack_nil_inv in Ha as (-> & -> & ->). destruct ls; [|discriminate]. injection Hd as <-.
    exists [Word (n2w 0)], []. rewrite stack_dec_stack_cons, !bd_true' by reflexivity. cbn [andb].
    split; [reflexivity|]. split; [cbn [abs_stack]; destruct (decide _) as [_|C]; [reflexivity|congruence]|].
    split; [exact Logic.I|constructor].
  - cbn [wordSem.dec_stack] in Hd. destruct (LENGTH ls <? LENGTH l) eqn:Ell; [discriminate|].
    apply N.ltb_ge in Ell.
    destruct (wordSem.dec_stack (DROP (LENGTH l) ls) xs) as [r|] eqn:Er; [|discriminate].
    injection Hd as <-.
    destruct h as [[h1 [p1 p2]]|].
    + apply abs_stack_SOME_inv in Ha as (loc & hv & w & stack & len' & lens' & bits & ys & -> & -> & Hb & <- & Hls & Hy & ->).
      cbn [stack_rel_aux] in Hr. destruct Hr as (Hhv & Hlc & Hal & Hf & Hthe & Hr).
      destruct (IH _ _ _ _ _ (conj Hg (conj H1 (conj H4 (conj Hy (conj Hr Er))))))
        as (sdec' & bstack' & Hd' & Ha' & Hr' & HL').
      destruct (dec_frame_step bs w bits stack ls k l sdec' Hb Hls Hf Ell Hd') as (x & Hx1 & Hx2 & Hx3 & Hx4).
      destruct (frame_rel_step k l0 l bits stack ls x Hal Hf Hls Ell Hx2 Hx3 Hx4) as [R1 R2].
      exists (Word (n2w 1) :: loc :: hv :: w :: x ++ sdec'), ((SOME (loc, hv), (bits, x)) :: bstack').
      split; [|split; [|split]].
      * rewrite stack_dec_stack_cons, bd_false' by (intros E; apply (f_equal (fun x => match x with Word w => w | Loc _ _ => n2w 7 end)) in E;
          exact (n2w_1_neq_0 E)).
        destruct bs as [|b0 bs0]; [cbn in H1; lia|]. cbn [HD] in H4. subst b0.
        cbn [full_read_bitmap]. rewrite bd_false' by apply n2w_1_neq_0.
        rewrite WORD_SUB_REFL, w2n_n2w, N.Div0.mod_0_l, DROP_skipn. cbn [N.to_nat skipn].
        rewrite handler_bitmap_props by exact Hg. cbn [map_bitmap]. rewrite Hx1. reflexivity.
      * rewrite abs_stack_SOME_eq with (bits := bits); [|exact Hb|reflexivity|rewrite LENGTH_app'; lia].
        rewrite DROP_app_exact', TAKE_app_exact by exact Hx2. rewrite Ha'. reflexivity.
      * cbn [stack_rel_aux]. split; [|split; [exact Hlc|split; [exact R1|split; [exact R2|split; [|exact Hr']]]]].
        -- intros [Hh1 Hhf]. pose proof (LIST_REL_LENGTH _ _ _ HL') as EL'.
           destruct (abs_stack_IMP_LENGTH _ _ _ _ _ Hy) as [Ey _].
           rewrite <- (LIST_REL_abs_frame_eq_handler_val _ _ (LIST_REL_LASTN _ _ _ (h1 + 1) HL')).
           apply Hhv. rewrite EL'. split; [exact Hh1|].
           apply (word_stack_dec_stack_shape (DROP (LENGTH l) ls) xs r). split; [exact Er|lia].
           exact Hhf.
        -- rewrite Hx2. rewrite LENGTH_TAKE_le in Hthe by exact Hls. exact Hthe.
      * constructor; [|exact HL']. unfold abs_frame_eq. cbn. repeat split.
        rewrite Hx2, LENGTH_TAKE_le by exact Hls. reflexivity.
    + apply abs_stack_NONE_inv in Ha as (w & stack & len' & lens' & bits & ys & -> & -> & Hb & <- & Hls & Hy & ->).
      cbn [stack_rel_aux] in Hr. destruct Hr as (Hal & Hf & Hthe & Hr).
      destruct (IH _ _ _ _ _ (conj Hg (conj H1 (conj H4 (conj Hy (conj Hr Er))))))
        as (sdec' & bstack' & Hd' & Ha' & Hr' & HL').
      destruct (dec_frame_step bs w bits stack ls k l sdec' Hb Hls Hf Ell Hd') as (x & Hx1 & Hx2 & Hx3 & Hx4).
      destruct (frame_rel_step k l0 l bits stack ls x Hal Hf Hls Ell Hx2 Hx3 Hx4) as [R1 R2].
      exists (w :: x ++ sdec'), ((NONE, (bits, x)) :: bstack'). split; [exact Hx1|split; [|split]].
      * rewrite abs_stack_NONE_eq with (bits := bits); [|exact Hb|reflexivity|rewrite LENGTH_app'; lia].
        rewrite DROP_app_exact', TAKE_app_exact by exact Hx2. rewrite Ha'. reflexivity.
      * cbn [stack_rel_aux]. split; [exact R1|split; [exact R2|split; [|exact Hr']]].
        rewrite Hx2. rewrite LENGTH_TAKE_le in Hthe by exact Hls. exact Hthe.
      * constructor; [|exact HL']. unfold abs_frame_eq. cbn. repeat split.
        rewrite Hx2, LENGTH_TAKE_le by exact Hls. reflexivity.
Qed.

End DecStackLemma.

Section DecStackLemma2.
Context {a : N} {c ffi_t : Type}.

Lemma wordSem_dec_stack_length (ls : list (word_loc a)) st res :
  wordSem.dec_stack ls st = SOME res -> LENGTH res = LENGTH st.
Proof.
  revert ls res; induction st as [|[n l0 l h] st IH]; intros ls res H.
  - destruct ls; [|discriminate]. injection H as <-. reflexivity.
  - cbn [wordSem.dec_stack] in H. destruct (_ <? _); [discriminate|].
    destruct (wordSem.dec_stack (DROP (LENGTH l) ls) st) as [r|] eqn:E; [|discriminate].
    injection H as <-. rewrite !LENGTH_cons', (IH _ _ E). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "dec_stack_lemma" *)
Theorem dec_stack_lemma : forall k lens x0 x (s1 : wordSem.state a (N * c) ffi_t) (t1 : stackSem.state a c ffi_t),
  good_dimindex a /\
  1 <= LENGTH (bitmaps t1) /\
  HD (bitmaps t1) = n2w 4 /\
  stack_space t1 <= LENGTH (stackSem.stack t1) /\
  stackSem.enc_stack (bitmaps t1) (DROP (stack_space t1) (stackSem.stack t1)) =
    SOME (wordSem.enc_stack (wordSem.stack s1)) /\
  wordSem.dec_stack x0 (wordSem.stack s1) = SOME x /\
  stack_rel k (wordSem.handler s1) (wordSem.stack s1) (SOME (FAPPLY (stackSem.store t1) Handler))
    (DROP (stack_space t1) (stackSem.stack t1)) (LENGTH (stackSem.stack t1)) (bitmaps t1) lens /\
  LENGTH (wordSem.enc_stack (wordSem.stack s1)) = LENGTH x0 ->
  exists yy,
    stackSem.dec_stack (bitmaps t1) x0 (DROP (stack_space t1) (stackSem.stack t1)) = SOME yy /\
    stack_space t1 + LENGTH yy = LENGTH (stackSem.stack t1) /\
    stack_rel k (wordSem.handler s1) x (SOME (FAPPLY (stackSem.store t1) Handler)) yy
      (LENGTH (stackSem.stack t1)) (bitmaps t1) lens.
Proof.
  intros k lens x0 x s1 t1 (Hg & H1 & H4 & Hsp & He & Hd & Hsr & Hl).
  destruct Hsr as (Hsorted & astack & Ha & Hh & Hr).
  destruct (dec_stack_lemma1 k (LENGTH (stackSem.stack t1)) _ _ _ _ _ _ _
    (conj Hg (conj H1 (conj H4 (conj Ha (conj Hr Hd))))))
    as (sdec & bstack & Hsd & Ha' & Hr' & HL).
  exists sdec. split; [exact Hsd|]. split.
  - apply stackProps.dec_stack_length in Hsd. rewrite LENGTH_DROP' in Hsd. lia.
  - split; [eapply word_stack_dec_stack_sorted; split; [exact Hd|exact Hsorted]|].
    exists bstack. split; [exact Ha'|]. split; [|exact Hr'].
    intros [Hh1 Hhf]. pose proof (LIST_REL_LENGTH _ _ _ HL) as EL.
    destruct (abs_stack_IMP_LENGTH _ _ _ _ _ Ha) as [Ea _].
    destruct (abs_stack_IMP_LENGTH _ _ _ _ _ Ha') as [Ea' _].
    rewrite <- (LIST_REL_abs_frame_eq_handler_val _ _ (LIST_REL_LASTN _ _ _ (wordSem.handler s1 + 1) HL)).
    pose proof (wordSem_dec_stack_length _ _ _ Hd) as Ex.
    apply Hh. split; [lia|].
    apply (word_stack_dec_stack_shape x0 (wordSem.stack s1) x); [split; [exact Hd|lia]|].
    rewrite Ex in Hhf. exact Hhf.
Qed.


(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "dec_stack_stack_size" *)
Theorem dec_stack_stack_size : forall (xs : list (word_loc a)) (st st' : list (stack_frame a)),
  wordSem.dec_stack xs st = SOME st' -> wordSem.stack_size st = wordSem.stack_size st'.
Proof.
  intros xs st; revert xs; induction st as [|[n l0 l h] st IH]; intros xs st' H.
  - destruct xs; [|discriminate]. injection H as <-. reflexivity.
  - cbn [wordSem.dec_stack] in H. destruct (_ <? _); [discriminate|].
    destruct (wordSem.dec_stack (DROP (LENGTH l) xs) st) as [r|] eqn:E; [|discriminate].
    injection H as <-. rewrite !(proj1 (stack_size_eq2 _ _)), (IH _ _ E). reflexivity.
Qed.

Lemma DROP_0_eq {A} (l : list A) : DROP 0 l = l.
Proof. rewrite DROP_skipn. reflexivity. Qed.

Lemma TAKE_0_eq {A} (l : list A) : TAKE 0 l = [].
Proof. rewrite TAKE_firstn. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "gc_state_rel" *)
Theorem gc_state_rel : forall ac k lens (s1 s2 : wordSem.state a (N * c) ffi_t) (t1 : stackSem.state a c ffi_t),
  wordSem.gc s1 = SOME s2 /\
  state_rel ac k 0 0 s1 t1 lens 0 ->
  exists t2,
    stackSem.gc t1 = SOME t2 /\
    state_rel ac k 0 0 (wordSem.set_locals LN s2) t2 lens 0 /\
    LENGTH (stackSem.stack t2) = LENGTH (stackSem.stack t1) /\ stack_space t2 = stack_space t1.
Proof.
  intros ac k lens s1 s2 t1 [G1 H].
  pose proof (IMP_enc_stack _ _ _ _ _ H) as He.
  unfold wordSem.gc in G1. cbv zeta in G1.
  destruct (wordSem.gc_fun s1 _) as [[wl [m st]]|] eqn:Ef; [|discriminate].
  destruct (wordSem.dec_stack wl (wordSem.stack s1)) as [x|] eqn:Ed; [|discriminate].
  injection G1 as <-.
  sr_destr H. rewrite !N.add_0_r, DROP_0_eq, TAKE_0_eq in *.
  rewrite Hgc, <- Hmem, <- Hmd, Hstore in Ef.
  destruct (Hgcok _ _ _ _ _ _ _ (conj HH Ef)) as (Gl & Gst & Gf).
  rewrite (FLOOKUP_FAPPLY _ _ HH) in Hsr.
  destruct (dec_stack_lemma k lens wl x s1 t1
    (conj Hgd (conj Hbm1 (conj Hhd (conj Hsp (conj He (conj Ed (conj Hsr Gl))))))))
    as (yy & Gd & Gyy & Gsr).
  unfold stackSem.gc. rewrite (proj2 (N.ltb_ge _ _) Hsp). cbv zeta. rewrite He, Gf, Gd.
  eexists. split; [reflexivity|].
  assert (GL : LENGTH (TAKE (stack_space t1) (stackSem.stack t1) ++ yy) = LENGTH (stackSem.stack t1)).
  { rewrite LENGTH_app', LENGTH_TAKE_le by exact Hsp. lia. }
  split; [|split; [stk_fields; exact GL|reflexivity]].
  assert (GT : LENGTH (TAKE (stack_space t1) (stackSem.stack t1)) = stack_space t1) by (apply LENGTH_TAKE_le; exact Hsp).
  sr_split; ws_fields; stk_fields; try assumption; try reflexivity.
  all: try (rewrite DOMSUB_FUPDATE, DOMSUB_NOT_IN_DOM by exact Gst; reflexivity).
  all: try (rewrite FDOM_FUPDATE; left; reflexivity).
  all: try (rewrite GL; first [lia|exact Hsl]).
  all: try (unfold stack_size_rel in *; rewrite GL; destruct Hssr as (S1 & S2 & S3); split; [exact S1|];
    split; [exact S2|];
    intros sm Hsm; destruct (S3 sm Hsm) as (S4 & S5 & ss & S6 & S7); split; [exact S4|]; split; [exact S5|];
    exists ss; split; [|exact S7]; rewrite <- (dec_stack_stack_size _ _ _ Ed); exact S6).
  all: try (rewrite FLOOKUP_UPDATE; destruct (decide (Handler = Handler)) as [_|C]; [|contradiction];
    rewrite N.add_0_r, DROP_0_eq, DROP_app_exact' by exact GT; rewrite GL; exact Gsr).
  all: intros n v Hn; rewrite lookup_LN in Hn; discriminate.
Qed.

End DecStackLemma2.

Section Alloc.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : wordSem.state a (N * c) ffi_t.

Lemma gc_set_locals LS L s :
  wordSem.gc (wordSem.set_locals_size LS (wordSem.set_locals L s)) =
  OPTION_MAP (fun s' => wordSem.set_locals_size LS (wordSem.set_locals L s')) (wordSem.gc s).
Proof.
  unfold wordSem.gc. cbv zeta. destruct s. ws_fields.
  destruct (gc_fun _) as [[wl [m st]]|]; [|reflexivity].
  destruct (wordSem.dec_stack wl _); reflexivity.
Qed.

Lemma pop_env_set_locals LS L s :
  wordSem.pop_env (wordSem.set_locals_size LS (wordSem.set_locals L s)) = wordSem.pop_env s.
Proof.
  unfold wordSem.pop_env. destruct s. ws_fields.
  destruct stack as [|[m e0 e [[n x]|]] xs]; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "alloc_alt" *)
Theorem alloc_alt : forall c0 names s,
  FST (wordSem.alloc c0 names s) <> SOME wordSem.Error ->
  wordSem.alloc c0 names s =
  match wordSem.cut_envs names (wordSem.locals s) with
  | NONE => (SOME wordSem.Error, s)
  | SOME env =>
      match wordSem.gc (wordSem.set_store AllocSize (Word c0)
              (wordSem.set_locals_size (SOME 0) (wordSem.set_locals LN (wordSem.push_env env NONE s)))) with
      | NONE => (SOME wordSem.Error, s)
      | SOME s' =>
          match wordSem.pop_env s' with
          | NONE => (SOME wordSem.Error, s')
          | SOME s' =>
              match wordSem.get_store AllocSize s' with
              | NONE => (SOME wordSem.Error, s')
              | SOME w =>
                  match wordSem.has_space w s' with
                  | NONE => (SOME wordSem.Error, s')
                  | SOME true => (NONE, s')
                  | SOME false => (SOME wordSem.NotEnoughSpace, wordSem.flush_state true s')
                  end
              end
          end
      end
  end.
Proof.
  intros c0 names s H. unfold wordSem.alloc in *.
  destruct (wordSem.cut_envs names (wordSem.locals s)) as [env|]; [|exfalso; apply H; reflexivity].
  rewrite push_env_set_store in *.
  replace (wordSem.set_store AllocSize (Word c0) (wordSem.set_locals_size (SOME 0) (wordSem.set_locals LN
      (wordSem.push_env env NONE s))))
    with (wordSem.set_locals_size (SOME 0) (wordSem.set_locals LN
      (wordSem.set_store AllocSize (Word c0) (wordSem.push_env env NONE s)))) by reflexivity.
  rewrite gc_set_locals.
  destruct (wordSem.gc (wordSem.set_store AllocSize (Word c0) (wordSem.push_env env NONE s))) as [s'|];
    [|exfalso; apply H; reflexivity].
  cbn [OPTION_MAP]. rewrite pop_env_set_locals.
  destruct (wordSem.pop_env s') as [s''|]; [reflexivity|exfalso; apply H; reflexivity].
Qed.


(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_set_store_0" *)
Theorem state_rel_set_store_0 : forall ac k s5 (t5 : stackSem.state a c ffi_t) len extra w,
  state_rel ac k 0 0 s5 t5 len extra ->
  state_rel ac k 0 0 (wordSem.set_store AllocSize w s5) (stackSem.set_store AllocSize w t5) len extra.
Proof.
  intros ac k s5 t5 len extra w H. sr_destr H. unfold wordSem.set_store, stackSem.set_store.
  sr_split; ws_fields; stk_fields; try assumption.
  all: try (rewrite Hstore; apply fmap_ext; intros x; rewrite FLOOKUP_UPDATE, !DOMSUB_FLOOKUP_THM, FLOOKUP_UPDATE;
    destruct (decide (AllocSize = x)) as [<-|]; destruct (decide (Handler = AllocSize)); try discriminate; reflexivity).
  all: try (rewrite FDOM_FUPDATE; right; exact HH).
  all: try (rewrite FLOOKUP_UPDATE; destruct (decide (AllocSize = Handler)); [discriminate|exact Hsr]).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "s_key_eq_stack_size" *)
Theorem s_key_eq_stack_size : forall (stack stack' : list (stack_frame a)),
  s_key_eq stack stack' -> wordSem.stack_size stack = wordSem.stack_size stack'.
Proof.
  induction stack as [|[n l0 l h] st IH]; intros [|[n' l0' l' h'] st'] H; try contradiction; [reflexivity|].
  destruct H as [H1 H2]. rewrite !(proj1 (stack_size_eq2 _ _)), (IH _ H1).
  destruct h, h'; cbn in H2; try contradiction;
    repeat match type of H2 with _ /\ _ => destruct H2 as [_ H2] end; subst; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "s_key_eq_push_env_locals_size" *)
Theorem s_key_eq_push_env_locals_size : forall env opt1 (s : wordSem.state a (N * c) ffi_t) n l0 l opt2 stack',
  s_key_eq (wordSem.stack (wordSem.push_env env opt1 s)) (StackFrame n l0 l opt2 :: stack') ->
  n = wordSem.locals_size s /\ wordSem.stack_size (wordSem.stack s) = wordSem.stack_size stack'.
Proof.
  intros env opt1 s n l0 l opt2 stack' H. unfold wordSem.push_env in H.
  destruct opt1 as [[w [h [l1 l2]]]|]; cbv zeta in H;
    destruct (wordSem.env_to_list _ _) as [ll perm]; ws_fields; destruct H as [H1 H2];
    split; try (apply s_key_eq_stack_size; exact H1);
    destruct opt2; cbn in H2; try contradiction;
    repeat match type of H2 with _ /\ _ => destruct H2 as [_ H2] end; symmetry; exact H2.
Qed.


Lemma oEL_cons_pos {A} m (x : A) xs : 0 < m -> oEL m (x :: xs) = oEL (m - 1) xs.
Proof. intros H. cbn [oEL]. replace (m =? 0) with false by (symmetry; apply N.eqb_neq; lia). reflexivity. Qed.

Lemma oEL_EL {A} {HA : Inhabited A} n (l : list A) : n < LENGTH l -> oEL n l = SOME (EL n l).
Proof.
  intros H. rewrite oEL_nth_error, EL_nth'. rewrite LENGTH_length in H.
  apply nth_error_nth'. lia.
Qed.

Lemma LASTN_cons_le {A} n (x : A) xs : n <= LENGTH xs -> LASTN n (x :: xs) = LASTN n xs.
Proof.
  intros H. rewrite !LASTN_DROP2, LENGTH_cons'. replace (LENGTH xs + 1 - n) with (SUC (LENGTH xs - n)) by lia.
  rewrite !DROP_skipn, N2Nat.inj_succ. reflexivity.
Qed.

(** The state after the [pop_env] of [alloc] (Galette-only helper of
    [alloc_IMP_alloc]). *)
Lemma pop_state_rel ac k f f' lens envs names (s : wordSem.state a (N * c) ffi_t)
    (t5 t2 : stackSem.state a c ffi_t) x s3 :
  1 <= f ->
  (forall y, domain (FST names) y -> EVEN y /\ k <= y DIV 2) ->
  (forall y, domain (SND names) y -> EVEN y /\ k <= y DIV 2) ->
  wordSem.cut_envs names (wordSem.locals s) = SOME envs ->
  state_rel ac k f f' s t5 lens 0 ->
  state_rel ac k 0 0 (wordSem.set_locals LN x) t2 (f' :: lens) 0 ->
  s_key_eq (wordSem.stack (wordSem.push_env envs NONE s)) (wordSem.stack x) ->
  wordSem.stack_max x = wordSem.stack_max (wordSem.push_env envs NONE s) ->
  wordSem.pop_env x = SOME s3 ->
  LENGTH (stackSem.stack t2) = LENGTH (stackSem.stack t5) -> stack_space t2 = stack_space t5 ->
  state_rel ac k f f' s3 t2 lens 0.
Proof.
  intros Hf Hn1 Hn2 Hcut R0 R2 Hkey Hmax Hpop HL HS.
  destruct (push_env_pop_env_s_key_eq _ _ _ _ Hkey) as (n & l & ls & opt & Hx & y & Hy & Hyl & Hyd & Hyk).
  rewrite Hy in Hpop. injection Hpop as <-.
  destruct (s_key_eq_push_env_locals_size _ _ _ _ _ _ _ _ (eq_ind _ (fun st => s_key_eq _ st) Hkey _ Hx))
    as [Hn Hss].
  assert (Hopt : opt = NONE).
  { unfold wordSem.push_env in Hkey. cbv zeta in Hkey. destruct (wordSem.env_to_list _ _).
    ws_fields. rewrite Hx in Hkey. destruct Hkey as [_ Hk]. destruct opt; [contradiction|reflexivity]. }
  subst opt. unfold wordSem.pop_env in Hy. rewrite Hx in Hy. injection Hy as <-.
  pose proof R0 as R0'. sr_destr R0'. sr_destr R2. ws_fields.
  assert (Hff' : f = f' + 1) by (destruct (f' =? 0); lia).
  (* the top frame *)
  rewrite N.add_0_r, DROP_0_eq in *.
  destruct Hsr0 as (Hsorted & astack & Ha & Hh & Hr). rewrite Hx in Ha, Hr, Hh, Hsorted.
  apply abs_stack_NONE_inv in Ha as (w & stack' & len' & lens' & bits & ys & Hst & Hlens & Hb & Hlb & Hls & Hy & ->).
  injection Hlens as <- <-.
  cbn [stack_rel_aux] in Hr. destruct Hr as (Hal & Hfb & Hthe & Hr).
  assert (HT : LENGTH (TAKE f' stack') = f') by (apply LENGTH_TAKE_le; exact Hls).
  sr_split; ws_fields; stk_fields; try assumption.
  - rewrite HS, HL. lia.
  - apply wf_union. split; apply wf_fromAList.
  - unfold stack_size_rel in *. destruct Hssr as (S1 & S2 & S3). destruct Hssr0 as (T1 & T2 & T3).
    split; [rewrite Hn; exact S1|]. split; [exact T2|].
    intros sm Hsm. destruct (T3 sm Hsm) as (T4 & _ & ss & T6 & T7).
    rewrite Hmax in Hsm. unfold wordSem.push_env in Hsm. cbv zeta in Hsm.
    destruct (wordSem.env_to_list _ _) as [l' perm]. ws_fields.
    destruct (wordSem.stack_max s) as [sm0|] eqn:Esm; [|discriminate].
    destruct (S3 sm0 eq_refl) as (S4 & S5 & ss0 & S6 & S7).
    split; [lia|]. split; [rewrite Hn; exact S5|]. exists ss0. split; [rewrite <- Hss; exact S6|].
    rewrite S7, HL, HS. lia.
  - unfold stack_rel. split.
    + cbn [EVERY] in Hsorted. unfold is_true in Hsorted. apply andb_true_iff in Hsorted. apply Hsorted.
    + exists ys. rewrite N.add_0_r, Hst, Hff'. cbn [DROP]. replace (f' + 1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
      replace (f' + 1 - 1) with f' by lia. split; [exact Hy|]. split; [|exact Hr].
      intros [Hh1 Hh2]. destruct (abs_stack_IMP_LENGTH _ _ _ _ _ Hy) as [Ey _].
      rewrite <- (LASTN_cons_le _ (NONE, (bits, TAKE f' stack'))) by lia.
      apply Hh. rewrite LENGTH_cons'. split; [lia|].
      replace (LENGTH ls + 1 - (wordSem.handler x + 1)) with (SUC (LENGTH ls - (wordSem.handler x + 1))) by lia.
      rewrite EL_SUC. exact Hh2.
  - intros n0 v Hv.
    assert (Hd0 : domain (union (fromAList l) (fromAList (toAList (FST envs)))) n0).
    { apply domain_lookup. eauto. }
    assert (Hd : (domain (SND envs) UNION domain (FST envs)) n0).
    { rewrite Hyd. exact Hd0. }
    unfold pred_set.UNION, pred_set.IN in Hd.
    unfold wordSem.cut_envs, wordSem.cut_names in Hcut.
    destruct (classical_dec _) as [D1|D1] in Hcut; [|discriminate].
    destruct (classical_dec _) as [D2|D2] in Hcut; [|discriminate]. injection Hcut as <-.
    cbn [FST SND fst snd] in *.
    assert (Hev : EVEN n0 /\ k <= n0 DIV 2).
    { destruct Hd as [Hd|Hd]; rewrite domain_inter in Hd; destruct Hd as [_ Hd]; [apply Hn2|apply Hn1]; exact Hd. }
    destruct Hev as [Hev Hk2]. split; [exact Hev|].
    replace (n0 DIV 2 <? k) with false by (symmetry; apply N.ltb_ge; exact Hk2).
    rewrite N.add_0_r, Hst, Hff'. cbn [TAKE]. replace (f' + 1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
    replace (f' + 1 - 1) with f' by lia.
    rewrite lookup_union, !lookup_fromAList in Hv.
    destruct (ALOOKUP l n0) as [v'|] eqn:El.
    + injection Hv as <-. apply ALOOKUP_MEM in El.
      assert (Hm : MEM (n0 DIV 2, v') (MAP_FST adjust_names l)).
      { unfold is_true in *. rewrite MEM_In in *. unfold MAP_FST. apply in_map_iff. exists (n0, v'). split; [reflexivity|exact El]. }
      pose proof (filter_bitmap_MEM bits _ _ _ (conj Hfb Hm)) as Hm2.
      pose proof (MEM_index_list_EL k _ _ _ Hm2) as He. pose proof (MEM_index_list_LIM _ _ _ _ Hm2) as Hlim.
      rewrite HT in He, Hlim. split; [|lia].
      rewrite oEL_cons_pos by lia. rewrite oEL_EL by (rewrite HT; lia).
      rewrite <- He. f_equal. f_equal. lia.
    + destruct (Hal n0 v (conj Hv El)) as (A1 & A2 & A3). unfold adjust_names in *.
      rewrite ALOOKUP_index_list in A3 by (rewrite HT; lia). rewrite HT in A3. split; [|lia].
      rewrite oEL_cons_pos by lia. rewrite <- A3. f_equal. lia.
Qed.

Lemma wgc_stack_max s x : wordSem.gc s = SOME x -> wordSem.stack_max x = wordSem.stack_max s.
Proof.
  unfold wordSem.gc. cbv zeta. destruct (wordSem.gc_fun s _) as [[wl [m st]]|]; [|discriminate].
  destruct (wordSem.dec_stack _ _); [|discriminate]. intros E; injection E as <-. reflexivity.
Qed.

Lemma sgc_length (t t' : stackSem.state a c ffi_t) :
  stackSem.gc t = SOME t' -> stack_space t' = stack_space t.
Proof.
  unfold stackSem.gc. destruct (_ <? _); [discriminate|]. cbv zeta.
  destruct (stackSem.enc_stack _ _); [|discriminate]. destruct (gc_fun t _) as [[wl [m st]]|]; [|discriminate].
  destruct (stackSem.dec_stack _ _ _); [|discriminate]. intros E; injection E as <-. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "alloc_IMP_alloc" *)
Theorem alloc_IMP_alloc : forall ac k f f' lens c0 names (s s1 : wordSem.state a (N * c) ffi_t)
    (t5 : stackSem.state a c ffi_t) envs (res : option (wordSem.result a)),
  wordSem.alloc c0 names s = (res, s1) /\
  (forall x, x IN domain (FST names) -> EVEN x /\ k <= x DIV 2) /\
  (forall x, x IN domain (SND names) -> EVEN x /\ k <= x DIV 2) /\
  1 <= f /\
  state_rel ac k f f' s t5 lens 0 /\
  state_rel ac k 0 0 (wordSem.set_locals_size (SOME 0) (wordSem.set_locals LN (wordSem.push_env envs NONE s)))
    t5 (f' :: lens) 0 /\
  wordSem.cut_envs names (wordSem.locals s) = SOME envs /\
  res <> SOME wordSem.Error ->
  exists (t1 : stackSem.state a c ffi_t) res1,
    stackSem.alloc c0 t5 = (res1, t1) /\
    if decide (res = NONE) then
      res1 = NONE /\
      state_rel ac k f f' s1 t1 lens 0 /\
      LENGTH (stackSem.stack t1) = LENGTH (stackSem.stack t5) /\
      stack_space t1 = stack_space t5
    else
      res = SOME wordSem.NotEnoughSpace /\ res1 = SOME (Halt (Word (n2w 1))) /\
      wordSem.clock s1 = stackSem.clock t1 /\ wordSem.ffi s1 = stackSem.ffi t1.
Proof.
  intros ac k f f' lens c0 names s s1 t5 envs res (Ha & Hn1 & Hn2 & Hf & R0 & R1 & Hcut & Hres).
  assert (Hne : FST (wordSem.alloc c0 names s) <> SOME wordSem.Error) by (rewrite Ha; exact Hres).
  rewrite (alloc_alt c0 names s Hne), Hcut in Ha.
  pose proof (state_rel_set_store_0 _ _ _ _ _ _ (Word c0) R1) as R2.
  destruct (wordSem.gc _) as [x|] eqn:Eg; [|injection Ha as <- _; contradiction].
  destruct (gc_state_rel _ _ _ _ _ _ (conj Eg R2)) as (t2 & Gt & R3 & GL & GS).
  destruct (wordSem.pop_env x) as [s3|] eqn:Ep; [|injection Ha as <- _; contradiction].
  assert (R4 : state_rel ac k f f' s3 t2 lens 0).
  { eapply (pop_state_rel ac k f f' lens envs names s t5 t2 x s3); try eassumption.
    all: first [ (pose proof (gc_s_key_eq _ _ Eg) as K; ws_fields; exact K)
               | (rewrite (wgc_stack_max _ _ Eg); reflexivity)
               | (rewrite GL; reflexivity) | (rewrite GS; reflexivity) ]. }
  unfold stackSem.alloc. rewrite Gt.
  pose proof R3 as R3'. sr_destr R3'. ws_fields.
  assert (Hst : forall nm, nm <> Handler -> wordSem.get_store nm s3 = FLOOKUP (store t2) nm).
  { intros nm Hnm. unfold wordSem.pop_env in Ep.
    destruct (wordSem.stack x) as [|[m e0 e [[hh ?]|]] xs]; try discriminate; injection Ep as <-.
    all: unfold wordSem.get_store; ws_fields; rewrite Hstore, DOMSUB_FLOOKUP_THM.
    all: destruct (decide (Handler = nm)); [congruence|reflexivity]. }
  rewrite <- (Hst AllocSize) by discriminate.
  destruct (wordSem.get_store AllocSize s3) as [w|]; [|injection Ha as <- _; contradiction].
  assert (Hspc : stackSem.has_space w (store t2) = wordSem.has_space w s3).
  { unfold stackSem.has_space, wordSem.has_space. rewrite <- !Hst by discriminate. reflexivity. }
  rewrite Hspc. destruct (wordSem.has_space w s3) as [[|]|]; injection Ha as <- <-;
    [|exists (empty_env t2), (SOME (Halt (Word (n2w 1))))|contradiction].
  - exists t2, NONE. split; [reflexivity|]. destruct (decide _) as [_|C]; [|contradiction].
    split; [reflexivity|]. split; [exact R4|]. split; [rewrite GL; reflexivity|rewrite GS; reflexivity].
  - split; [reflexivity|]. destruct (decide _) as [C|_]; [discriminate|].
    sr_destr R4. unfold wordSem.flush_state. ws_fields. stk_fields. repeat split; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_gc_empty_frame" *)
Theorem word_gc_empty_frame : forall (s x y : wordSem.state a (N * c) ffi_t) n,
  wordSem.gc (wordSem.set_stack (StackFrame n [] [] NONE :: wordSem.stack s) s) = SOME x /\
  wordSem.pop_env x = SOME y ->
  wordSem.locals y = LN /\
  wordSem.gc s = SOME (wordSem.set_locals_size (wordSem.locals_size s) (wordSem.set_locals (wordSem.locals s) y)).
Proof.
  intros s x y n [Hg Hp]. unfold wordSem.gc in *. cbv zeta in *. ws_fields.
  cbn [wordSem.enc_stack MAP List.map app] in Hg.
  destruct (wordSem.gc_fun s _) as [[wl [m st]]|]; [|discriminate].
  cbn [wordSem.dec_stack] in Hg. replace (LENGTH wl <? LENGTH (@nil (N * word_loc a))) with false in Hg
    by (symmetry; apply N.ltb_ge; cbn; lia).
  rewrite DROP_0_eq in Hg.
  destruct (wordSem.dec_stack wl (wordSem.stack s)) as [r|]; [|discriminate].
  injection Hg as <-. unfold wordSem.pop_env in Hp. ws_fields. injection Hp as <-.
  split; [reflexivity|]. destruct s. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "inter_eq_empty_2" *)
Theorem inter_eq_empty_2 : forall {B} (s : spt B) (t : num_set), domain t = {} -> inter s t = LN.
Proof.
  intros B s t H. apply inter_eq_LN. apply functional_extensionality. intros z.
  apply propositional_extensionality. rewrite H. unfold EMPTY. tauto.
Qed.

Lemma push_env_LN (s : wordSem.state a (N * c) ffi_t) :
  wordSem.push_env (LN, LN) NONE s =
  wordSem.set_permute (fun n => wordSem.permute s (n + 1))
    (wordSem.set_stack_max (OPTION_MAP2 MAX (wordSem.stack_max s)
        (wordSem.stack_size (StackFrame (wordSem.locals_size s) [] [] NONE :: wordSem.stack s)))
      (wordSem.set_stack (StackFrame (wordSem.locals_size s) [] [] NONE :: wordSem.stack s) s)).
Proof.
  unfold wordSem.push_env, wordSem.env_to_list. cbv zeta.
  replace (toAList (@LN (word_loc a))) with (@nil (N * word_loc a)) by reflexivity.
  replace (mllist.sort wordSem.key_val_compare (@nil (N * word_loc a))) with (@nil (N * word_loc a))
    by reflexivity.
  replace (wordSem.list_rearrange (wordSem.permute s 0) (@nil (N * word_loc a))) with (@nil (N * word_loc a))
    by (unfold wordSem.list_rearrange; destruct (classical_dec _); reflexivity).
  reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "alloc_IMP_alloc2" *)
Theorem alloc_IMP_alloc2 : forall ac k lens c0 names (s s1 : wordSem.state a (N * c) ffi_t)
    (t : stackSem.state a c ffi_t) (res : option (wordSem.result a)),
  wordSem.alloc c0 names s = (res, s1) /\
  state_rel ac k 0 0 s t lens 0 /\
  domain (FST names) = {} /\
  domain (SND names) = {} /\
  res <> SOME wordSem.Error ->
  exists (t1 : stackSem.state a c ffi_t) res1,
    stackSem.alloc c0 t = (res1, t1) /\
    if decide (res = NONE) then
      res1 = NONE /\
      state_rel ac k 0 0 s1 t1 lens 0 /\
      LENGTH (stackSem.stack t1) = LENGTH (stackSem.stack t) /\
      stack_space t1 = stack_space t
    else
      res = SOME wordSem.NotEnoughSpace /\ res1 = SOME (Halt (Word (n2w 1))) /\
      wordSem.clock s1 = stackSem.clock t1 /\ wordSem.ffi s1 = stackSem.ffi t1.
Proof.
  intros ac k lens c0 names s s1 t res (Ha & R0 & D1 & D2 & Hres).
  assert (Hne : FST (wordSem.alloc c0 names s) <> SOME wordSem.Error) by (rewrite Ha; exact Hres).
  rewrite (alloc_alt c0 names s Hne) in Ha.
  assert (Hcut : wordSem.cut_envs names (wordSem.locals s) = SOME (LN, LN)).
  { unfold wordSem.cut_envs, wordSem.cut_names.
    destruct (classical_dec _) as [_|C]; [|exfalso; apply C; rewrite D1; intros z []].
    destruct (classical_dec _) as [_|C]; [|exfalso; apply C; rewrite D2; intros z []].
    rewrite !inter_eq_empty_2 by assumption. reflexivity. }
  rewrite Hcut, push_env_LN in Ha.
  set (fr := StackFrame (wordSem.locals_size s) [] [] NONE) in Ha.
  set (M := OPTION_MAP2 MAX (wordSem.stack_max s) (wordSem.stack_size (fr :: wordSem.stack s))) in Ha.
  set (B0 := wordSem.set_permute (fun n => wordSem.permute s (n + 1)) (wordSem.set_stack_max M
               (wordSem.set_locals_size (SOME 0) (wordSem.set_locals LN s)))).
  set (B := wordSem.set_store AllocSize (Word c0) B0).
  replace (wordSem.set_store AllocSize (Word c0) (wordSem.set_locals_size (SOME 0) (wordSem.set_locals LN
      (wordSem.set_permute (fun n => wordSem.permute s (n + 1)) (wordSem.set_stack_max M
        (wordSem.set_stack (fr :: wordSem.stack s) s))))))
    with (wordSem.set_stack (fr :: wordSem.stack B) B) in Ha by (destruct s; reflexivity).
  destruct (wordSem.gc (wordSem.set_stack (fr :: wordSem.stack B) B)) as [x|] eqn:Eg;
    [|injection Ha as <- _; contradiction].
  destruct (wordSem.pop_env x) as [y|] eqn:Ep; [|injection Ha as <- _; contradiction].
  destruct (word_gc_empty_frame B x y (wordSem.locals_size s) (conj Eg Ep)) as [Hyl HgB].
  assert (RB0 : state_rel ac k 0 0 B0 t lens 0).
  { pose proof R0 as R. sr_destr R. unfold B0. sr_split; ws_fields; try assumption.
    - apply functional_extensionality. intros n. rewrite Hperm. reflexivity.
    - reflexivity.
    - unfold stack_size_rel in *. destruct Hssr as (S1 & S2 & S3). split; [intros C; lia|]. split; [exact S2|].
      intros sm Hsm. unfold M, OPTION_MAP2 in Hsm. destruct (wordSem.stack_max s) as [sm0|]; [|discriminate].
      destruct (wordSem.stack_size (fr :: wordSem.stack s)) as [z|]; [|discriminate].
      injection Hsm as <-. destruct (S3 sm0 eq_refl) as (S4 & S5 & ss & S6 & S7).
      split; [rewrite MAX_max; lia|]. split; [reflexivity|]. exists ss. auto.
    - intros n v Hn. rewrite lookup_LN in Hn. discriminate. }
  pose proof (state_rel_set_store_0 _ _ _ _ _ _ (Word c0) RB0) as RB.
  destruct (gc_state_rel _ _ _ _ _ _ (conj HgB RB)) as (t2 & Gt & R3 & GL & GS).
  assert (Hpop : exists n0 e0 e xs, wordSem.stack x = StackFrame n0 e0 e NONE :: xs /\
            y = wordSem.set_locals_size n0 (wordSem.set_stack xs
                  (wordSem.set_locals (union (fromAList e) (fromAList e0)) x)) /\ n0 = wordSem.locals_size s).
  { pose proof (gc_s_key_eq _ _ Eg) as K. ws_fields. unfold wordSem.pop_env in Ep.
    destruct (wordSem.stack x) as [|[n0 e0 e h] xs]; [contradiction|]. destruct K as [_ K].
    destruct h as [[hh ?]|]; [cbn in K; contradiction|]. injection Ep as <-.
    exists n0, e0, e, xs. split; [reflexivity|]. split; [reflexivity|]. cbn in K. symmetry. apply K. }
  destruct Hpop as (n0 & e0 & e & xs & Hxs & Hy & Hn0).
  assert (Hymax : wordSem.stack_max y = M).
  { rewrite Hy. ws_fields. rewrite (wgc_stack_max _ _ Eg). unfold B, B0. ws_fields. reflexivity. }
  assert (R4 : state_rel ac k 0 0 y t2 lens 0).
  { pose proof R3 as R. sr_destr R. pose proof R0 as R'. sr_destr R'. ws_fields.
    assert (Ey : y = wordSem.set_locals_size (wordSem.locals_size y) (wordSem.set_locals LN
                  (wordSem.set_locals_size (SOME 0) (wordSem.set_locals LN y)))) by (destruct y; ws_fields; cbn in Hyl; subst; reflexivity).
    rewrite Ey. sr_split; ws_fields; try assumption.
    unfold stack_size_rel in *. destruct Hssr as (S1 & S2 & S3). split; [intros C; lia|]. split; [exact S2|].
    intros sm Hsm. destruct (S3 sm Hsm) as (S4 & S5 & S6). split; [exact S4|]. split; [|exact S6].
    rewrite Hymax in Hsm. unfold M, OPTION_MAP2 in Hsm. destruct (wordSem.stack_max s) as [sm0|] eqn:Esm; [|discriminate].
    destruct Hssr0 as (_ & _ & S7). destruct (S7 sm0 eq_refl) as (_ & S8 & _).
    rewrite Hy. ws_fields. rewrite Hn0. exact S8. }
  unfold stackSem.alloc. rewrite Gt.
  pose proof R4 as R4'. sr_destr R4'.
  assert (Hst : forall nm, nm <> Handler -> wordSem.get_store nm y = FLOOKUP (store t2) nm).
  { intros nm Hnm. unfold wordSem.get_store. rewrite Hstore, DOMSUB_FLOOKUP_THM.
    destruct (decide (Handler = nm)); [congruence|reflexivity]. }
  rewrite <- (Hst AllocSize) by discriminate.
  destruct (wordSem.get_store AllocSize y) as [w|]; [|injection Ha as <- _; contradiction].
  assert (Hspc : stackSem.has_space w (store t2) = wordSem.has_space w y).
  { unfold stackSem.has_space, wordSem.has_space. rewrite <- !Hst by discriminate. reflexivity. }
  rewrite Hspc. destruct (wordSem.has_space w y) as [[|]|]; injection Ha as <- <-;
    [|exists (empty_env t2), (SOME (Halt (Word (n2w 1))))|contradiction].
  - exists t2, NONE. split; [reflexivity|]. destruct (decide _) as [_|C]; [|contradiction].
    split; [reflexivity|]. split; [exact R4|]. stk_fields. split; [rewrite GL; reflexivity|rewrite GS; reflexivity].
  - split; [reflexivity|]. destruct (decide _) as [C|_]; [discriminate|].
    unfold wordSem.flush_state. ws_fields. stk_fields. repeat split; congruence.
Qed.

End Alloc.



(** ** [compile_result] *)

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "compile_result_def" *)
Definition compile_result {a} (r : wordSem.result a) : stackSem.result a :=
  match r with
  | wordSem.Result w1 w2 => Result w1
  | wordSem.Exception w1 w2 => Exception w1
  | wordSem.TimeOut => TimeOut
  | wordSem.NotEnoughSpace => Halt (Word (n2w 1))
  | wordSem.FinalFFI f => FinalFFI f
  | wordSem.Break k => Break k
  | wordSem.Continue k => Continue k
  | wordSem.Error => Error
  end.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "Halt_EQ_compile_result" *)
Theorem Halt_EQ_compile_result : forall {a} (z : wordSem.result a),
  (Halt (Word (n2w 1)) = compile_result z <-> z = wordSem.NotEnoughSpace) /\
  (good_dimindex a -> Halt (Word (n2w 2 : word a)) <> compile_result z).
Proof.
  intros a z. split.
  - destruct z; cbn; split; intros H; try discriminate; try reflexivity.
  - intros Hg. destruct z; cbn; try discriminate.
    intros E. assert (H4 : 4 <= dimword a) by (unfold dimword; destruct Hg as [-> | ->]; cbn; lia).
    apply (f_equal (fun x => match x with Halt (Word w) => w2n w | _ => 0 end)) in E. cbv beta iota in E.
    rewrite !w2n_n2w, !N.mod_small in E by lia. discriminate.
Qed.

(** ** [wLive] *)

Section WLive.
Context {a : N} {c ffi_t : Type}.

Lemma wlive_eval k w (t : stackSem.state a c ffi_t) :
  use_stack t -> stack_space t < LENGTH (stackSem.stack t) ->
  evaluate (Seq (Inst (asm.Const k w)) (StackStore k 0), t) =
  (NONE, set_stack (LUPDATE (Word w) (stack_space t) (stackSem.stack t)) (stackSem.set_var k (Word w) t)).
Proof.
  intros Hu Hl. rewrite ev_seq, ev_inst, inst_const. cbv beta iota.
  rewrite ev_stackstore. unfold stackSem.set_var at 1 2 3. stk_fields. unfold is_true in Hu. rewrite Hu.
  cbn [negb]. replace (LENGTH (stackSem.stack t) <=? stack_space t + 0) with false
    by (symmetry; apply N.leb_gt; lia).
  rewrite (get_var_set_var k (Word w) t). rewrite N.add_0_r. reflexivity.
Qed.

Lemma oEL_LUPDATE_neq {A} (x : A) i n l : i <> n -> oEL i (LUPDATE x n l) = oEL i l.
Proof.
  revert i n; induction l as [|y l IH]; intros i n H; [reflexivity|].
  rewrite LUPDATE_cons_eq. cbn [oEL].
  destruct (N.eqb_spec n 0) as [->|Hn]; cbn [oEL];
    destruct (N.eqb_spec i 0) as [->|Hi]; try reflexivity; [lia|].
  apply IH. lia.
Qed.

Lemma DROP_LUPDATE_self {A} (x : A) n l : n < LENGTH l -> DROP n (LUPDATE x n l) = x :: DROP (n + 1) l.
Proof.
  revert n; induction l as [|y l IH]; intros n H; [cbn in H; lia|].
  rewrite LUPDATE_cons_eq. rewrite LENGTH_cons' in H. destruct (N.eqb_spec n 0) as [->|Hn].
  - rewrite !DROP_skipn. reflexivity.
  - cbn [DROP]. replace (n =? 0) with false by (symmetry; apply N.eqb_neq; exact Hn).
    replace (n + 1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
    rewrite IH by lia. f_equal. f_equal. lia.
Qed.

Lemma DROP_EL_cons {A} {HA : Inhabited A} n (l : list A) : n < LENGTH l -> DROP n l = EL n l :: DROP (n + 1) l.
Proof.
  revert n; induction l as [|y l IH]; intros n H; [cbn in H; lia|]. rewrite LENGTH_cons' in H.
  destruct (N.eqb_spec n 0) as [->|Hn].
  - rewrite !DROP_skipn. reflexivity.
  - cbn [DROP]. replace (n =? 0) with false by (symmetry; apply N.eqb_neq; exact Hn).
    replace (n + 1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
    rewrite IH by lia. f_equal; [|f_equal; lia].
    rewrite !EL_nth'. replace (N.to_nat n) with (Datatypes.S (N.to_nat (n - 1))) by lia. reflexivity.
Qed.

Lemma DROP_TAKE_cons {A} (x : A) l f : 1 <= f ->
  DROP f (x :: l) = DROP (f - 1) l /\ TAKE f (x :: l) = x :: TAKE (f - 1) l.
Proof. intros H. cbn [DROP TAKE]. replace (f =? 0) with false by (symmetry; apply N.eqb_neq; lia). split; reflexivity. Qed.

(** The old frame is untouched by [wLive]'s stores (Galette-only). *)
Lemma wlive_state_rel_old ac k f f' (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t) lens w :
  1 <= f -> state_rel ac k f f' s t lens 0 ->
  state_rel ac k f f' s (set_stack (LUPDATE (Word w) (stack_space t) (stackSem.stack t)) (stackSem.set_var k (Word w) t)) lens 0.
Proof.
  intros Hf H. sr_destr H. rewrite N.add_0_r in *.
  assert (Hlt : stack_space t < LENGTH (stackSem.stack t)) by lia.
  pose proof (DROP_LUPDATE_self (Word w) _ _ Hlt) as HD.
  pose proof (DROP_EL_cons _ _ Hlt) as HD2.
  destruct (DROP_TAKE_cons (Word w) (DROP (stack_space t + 1) (stackSem.stack t)) f Hf) as [E1 E2].
  destruct (DROP_TAKE_cons (EL (stack_space t) (stackSem.stack t)) (DROP (stack_space t + 1) (stackSem.stack t)) f Hf) as [E3 E4].
  rewrite HD2, E3, E4 in *.
  unfold stackSem.set_var. sr_split; stk_fields; try assumption; rewrite ?N.add_0_r, ?HD, ?E1, ?E2, ?LENGTH_LUPDATE'; try assumption.
  - unfold stack_size_rel in *. rewrite LENGTH_LUPDATE'. exact Hssr.
  - intros n v Hn. destruct (Hloc n v Hn) as [Hev Hr]. split; [exact Hev|].
    destruct (n DIV 2 <? k) eqn:Ek.
    + rewrite FLOOKUP_UPDATE. destruct (decide (k = n DIV 2)) as [C|]; [apply N.ltb_lt in Ek; lia|exact Hr].
    + destruct Hr as [Hr1 Hr2]. split; [|exact Hr2]. apply N.ltb_ge in Ek.
      assert (Hff' : f = f' + 1) by (destruct (f' =? 0); lia).
      rewrite oEL_cons_pos in Hr1 |- * by lia. exact Hr1.
Qed.

End WLive.

(** ** The frame bitmap written by [wLive] (Galette-only) *)

Section WLiveBitmap.
Context {a : N}.

Lemma In_index_list_bounds {A} (T : list A) k p v : In (p, v) (index_list T k) -> k <= p < k + LENGTH T.
Proof.
  induction T as [|x T IH]; [intros []|]. cbn [index_list]. rewrite LENGTH_cons'.
  intros [E|Hin]; [injection E as <- _; lia|]. specialize (IH Hin). lia.
Qed.

Lemma index_list_SS {A} (T : list A) k : StronglySorted (fun x y => FST x > FST y) (index_list T k).
Proof.
  induction T as [|x T IH]; cbn [index_list]; constructor; [exact IH|].
  apply Forall_forall. intros [p v] Hin. cbn [FST fst].
  pose proof (In_index_list_bounds T k p v Hin). lia.
Qed.

Lemma In_index_list {A} {HA : Inhabited A} {HE : EqDecision A} (T : list A) k p v :
  In (p, v) (index_list T k) <-> k <= p < k + LENGTH T /\ EL (k + LENGTH T - (p + 1)) T = v.
Proof.
  split.
  - intros Hin. assert (Hm : MEM (p, v) (index_list T k)) by (apply MEM_In; exact Hin).
    pose proof (MEM_index_list_EL k _ _ _ Hm) as H2. pose proof (In_index_list_bounds _ _ _ _ Hin) as H1.
    split; [lia|]. rewrite <- H2. f_equal. lia.
  - intros [Hr He]. assert (Ha := ALOOKUP_index_list T p k ltac:(lia)).
    replace (LENGTH T + k - (p + 1)) with (k + LENGTH T - (p + 1)) in Ha by lia.
    rewrite oEL_EL in Ha by lia. rewrite He in Ha. apply ALOOKUP_MEM in Ha. apply MEM_In, Ha.
Qed.

Lemma filter_bitmap_FILTER {A} (bits : list bool) (xs : list A) :
  LENGTH bits = LENGTH xs ->
  filter_bitmap bits xs = SOME (MAP FST (FILTER SND (ZIP (xs, bits))), []).
Proof. intros H. apply IMP_filter_bitmap_EQ_SOME_NIL. split; [exact H|reflexivity]. Qed.

Lemma In_FILTER_ZIP {A} {HA : Inhabited A} (xs : list A) (bits : list bool) x :
  LENGTH bits = LENGTH xs ->
  (In x (MAP FST (FILTER SND (ZIP (xs, bits)))) <->
   exists i, i < LENGTH xs /\ EL i xs = x /\ EL i bits = true).
Proof.
  revert bits; induction xs as [|y xs IH]; intros [|b bits] H; rewrite ?LENGTH_cons' in H;
    try (cbn in H; lia).
  - cbn. split; [intros []|intros (i & Hi & _); cbn in Hi; lia].
  - cbn [ZIP FILTER SND snd]. specialize (IH bits ltac:(lia)).
    split.
    + intros Hin. destruct b; cbn [MAP List.map FST fst In] in Hin.
      * destruct Hin as [<-|Hin]; [exists 0; rewrite LENGTH_cons'; split; [lia|split; reflexivity]|].
        apply IH in Hin as (i & Hi & H1 & H2). exists (SUC i). rewrite LENGTH_cons', !EL_SUC. auto with *.
        split; [lia|split; assumption].
      * apply IH in Hin as (i & Hi & H1 & H2). exists (SUC i). rewrite LENGTH_cons', !EL_SUC.
        split; [lia|split; assumption].
    + intros (i & Hi & H1 & H2). revert Hi H1 H2. destruct i as [|i] using N.peano_ind; intros Hi H1 H2.
      * cbn in H1, H2. subst. cbn. left; reflexivity.
      * rewrite EL_SUC in H1. rewrite EL_SUC in H2. cbn [TL] in H1, H2. rewrite LENGTH_cons' in Hi.
        assert (Hin : In x (MAP FST (FILTER SND (ZIP (xs, bits))))) by (apply IH; exists i; split; [lia|auto]).
        destruct b; cbn; [right|]; exact Hin.
Qed.


Lemma EL_GENLIST_N {A} {HA : Inhabited A} (g : N -> A) n i : i < n -> EL i (GENLIST g n) = g i.
Proof.
  intros H. rewrite EL_nth', GENLIST_seq. rewrite (nth_indep _ ARB (g (N.of_nat 0))) by
    (rewrite length_map, length_seq; lia).
  rewrite (map_nth (fun i0 => g (N.of_nat i0))), seq_nth by lia. f_equal. lia.
Qed.

Lemma SS_FILTER_ZIP {A} (R : A -> A -> Prop) (xs : list A) (bs : list bool) :
  StronglySorted R xs -> StronglySorted R (MAP FST (FILTER SND (ZIP (xs, bs)))).
Proof.
  revert bs; induction xs as [|x xs IH]; intros [|b bs] H; cbn; try constructor.
  apply StronglySorted_inv in H as [H F]. destruct b; cbn [MAP List.map FST fst]; [|apply IH, H].
  constructor; [apply IH, H|]. rewrite Forall_forall in *. intros y Hy. apply F.
  clear -Hy. revert bs Hy; induction xs as [|z xs IH]; intros [|b bs] Hy; cbn in Hy; try contradiction.
  destruct b; cbn in Hy; [destruct Hy as [<-|Hy]; [left; reflexivity|right; eapply IH; eauto]|right; eapply IH; eauto].
Qed.

Lemma SS_map_in {A B} (R : A -> A -> Prop) (R' : B -> B -> Prop) (f : A -> B) l :
  (forall x y, In x l -> In y l -> R x y -> R' (f x) (f y)) ->
  StronglySorted R l -> StronglySorted R' (List.map f l).
Proof.
  intros HR H. induction H as [|x l H IH F]; cbn; constructor.
  - apply IH. intros u v Hu Hv. apply HR; right; assumption.
  - rewrite Forall_forall in *. intros y Hy. apply in_map_iff in Hy as (z & <- & Hz).
    apply HR; [left; reflexivity|right; exact Hz|apply F, Hz].
Qed.

Lemma wlive_filter k f' (names : num_set * num_set) (locals : num_map (word_loc a))
    (l : list (N * word_loc a)) (T : list (word_loc a)) :
  LENGTH T = f' ->
  (forall x, x IN domain (SND names) -> EVEN x /\ k <= x DIV 2) ->
  (domain (SND names) SUBSET domain locals) ->
  (forall r v, lookup r locals = SOME v -> k <= r DIV 2 ->
     oEL (f' - 1 - (r DIV 2 - k)) T = SOME v /\ r DIV 2 < k + f') ->
  SORTED (fun x y => FST x > FST y) l ->
  Permutation (toAList (inter locals (SND names))) l ->
  filter_bitmap (GENLIST (fun x => MEM x (MAP (fun '(r, y) => f' - 1 - (r DIV 2 - k)) (toAList (SND names)))) f')
    (index_list T k) = SOME (MAP_FST adjust_names l, []).
Proof.
  intros HT Hev Hsub Hloc Hsort Hperm.
  rewrite filter_bitmap_FILTER by (rewrite LENGTH_GENLIST_N, LENGTH_index_list; lia).
  f_equal. f_equal. symmetry.
  assert (Hinl : forall r v, In (r, v) l <-> lookup r locals = SOME v /\ domain (SND names) r).
  { intros r v. split.
    - intros Hin. apply (Permutation_in _ (Permutation_sym Hperm)) in Hin. rewrite <- MEM_In in Hin.
      apply MEM_toAList in Hin. rewrite lookup_inter_alt in Hin.
      destruct (decide (domain (SND names) r)); [split; assumption|discriminate].
    - intros [H1 H2]. apply (Permutation_in _ Hperm). rewrite <- MEM_In. apply MEM_toAList.
      rewrite lookup_inter_alt. destruct (decide (domain (SND names) r)); [exact H1|contradiction]. }
  apply SORTED_IMP_EQ_LISTS. split; [|split].
  - eapply StronglySorted_SORTED; [|apply SS_FILTER_ZIP, index_list_SS]. intros x y H; exact H.
  - apply SORTED_StronglySorted in Hsort; [|intros; lia].
    eapply StronglySorted_SORTED; [intros x y H; exact H|].
    unfold MAP_FST. apply SS_map_in with (R := fun x y => FST x > FST y); [|exact Hsort].
    intros [r1 v1] [r2 v2] H1 H2 Hr. cbn [FST fst] in *. unfold adjust_names.
    apply Hinl in H1 as [_ H1]. apply Hinl in H2 as [_ H2].
    apply EVEN_GT. split; [apply Hev, H1|]. split; [apply Hev, H2|exact Hr].
  - intros [p v]. unfold is_true. rewrite !MEM_In. rewrite In_FILTER_ZIP by (rewrite LENGTH_GENLIST_N, LENGTH_index_list; lia).
    unfold MAP_FST. rewrite in_map_iff. rewrite LENGTH_index_list, HT. split.
    + intros (i & Hi & E1 & E2). rewrite EL_index_list in E1 by lia. rewrite HT in E1. injection E1 as Ep Ev.
      rewrite EL_GENLIST_N in E2 by exact Hi. unfold is_true in E2. rewrite MEM_In, in_map_iff in E2.
      destruct E2 as ([r []] & Er & Hin). rewrite <- MEM_In in Hin. apply MEM_toAList in Hin.
      assert (Hd : domain (SND names) r) by (apply domain_lookup; eauto).
      destruct (Hev r Hd) as [Hr1 Hr2]. destruct (proj1 (domain_lookup _ _) (Hsub r Hd)) as [v' Hv'].
      destruct (Hloc r v' Hv' Hr2) as [H3 H4].
      exists (r, v'). split.
      * cbn [FST fst SND snd]. unfold adjust_names. f_equal; [lia|].
        rewrite <- Ev. assert (H5 := oEL_SOME_lt _ _ _ H3). rewrite oEL_EL in H3 by exact H5.
        injection H3 as H3. rewrite <- H3. f_equal. lia.
      * apply Hinl. split; [exact Hv'|exact Hd].
    + intros ([r v'] & E & Hin). injection E as <- <-. apply Hinl in Hin as [H1 H2].
      destruct (Hev r H2) as [Hr1 Hr2]. destruct (Hloc r v' H1 Hr2) as [H3 H4].
      exists (f' - 1 - (r DIV 2 - k)). split; [lia|]. split.
      * rewrite EL_index_list by lia. rewrite HT. unfold adjust_names. f_equal; [lia|].
        assert (H5 := oEL_SOME_lt _ _ _ H3). rewrite oEL_EL in H3 by exact H5. injection H3 as H3. exact H3.
      * rewrite EL_GENLIST_N by lia. unfold is_true. rewrite MEM_In, in_map_iff. exists (r, tt). split; [reflexivity|].
        rewrite <- MEM_In. apply MEM_toAList. apply domain_lookup in H2 as [[] H2]. exact H2.
Qed.


End WLiveBitmap.

Section WLiveNew.
Context {a : N} {c ffi_t : Type}.

(** The new frame pushed by [wLive] (Galette-only helper of [evaluate_wLive]). *)
Lemma wlive_state_rel_new ac k f f' lens envs names (s : wordSem.state a (N * c) ffi_t)
    (t : stackSem.state a c ffi_t) n :
  1 <= f ->
  (forall x, x IN domain (FST names) -> EVEN x /\ k <= x DIV 2) ->
  (forall x, x IN domain (SND names) -> EVEN x /\ k <= x DIV 2) ->
  state_rel ac k f f' s t lens 0 ->
  wordSem.cut_envs names (wordSem.locals s) = SOME envs ->
  read_bitmap (DROP n (bitmaps t)) =
    SOME (GENLIST (fun x => MEM x (MAP (fun '(r, y) => f' - 1 - (r DIV 2 - k)) (toAList (SND names)))) f') ->
  n + 1 < dimword a ->
  state_rel ac k 0 0 (wordSem.set_locals_size (SOME 0) (wordSem.set_locals LN (wordSem.push_env envs NONE s)))
    (set_stack (LUPDATE (Word (n2w (n + 1))) (stack_space t) (stackSem.stack t))
       (stackSem.set_var k (Word (n2w (n + 1))) t)) (f' :: lens) 0.
Proof.
  intros Hf Hn1 Hn2 R Hcut Hrb Hnw.
  pose proof R as R'. sr_destr R'. rewrite N.add_0_r in *.
  assert (Hff' : f = f' + 1) by (destruct (f' =? 0) eqn:E; [lia|exact Hff]).
  assert (Hlt : stack_space t < LENGTH (stackSem.stack t)) by lia.
  unfold wordSem.cut_envs, wordSem.cut_names in Hcut.
  destruct (classical_dec _) as [D1|D1] in Hcut; [|discriminate].
  destruct (classical_dec _) as [D2|D2] in Hcut; [|discriminate]. injection Hcut as <-.
  unfold wordSem.push_env. cbv zeta. cbn [FST SND fst snd].
  destruct (wordSem.env_to_list (inter (wordSem.locals s) (SND names)) (wordSem.permute s)) as [l perm] eqn:El.
  rewrite Hperm in El. destruct (env_to_list_K_I_IMP _ _ _ El) as (Lsort & -> & Lperm).
  set (bits := GENLIST _ f') in Hrb.
  set (fr := StackFrame (wordSem.locals_size s) (toAList (inter (wordSem.locals s) (FST names))) l NONE).
  pose proof (DROP_LUPDATE_self (Word (n2w (n + 1))) _ _ Hlt) as HD.
  pose proof (DROP_EL_cons _ _ Hlt) as HD2.
  set (rest := DROP (stack_space t + 1) (stackSem.stack t)) in *.
  assert (Hlr : f' <= LENGTH rest).
  { unfold rest. rewrite LENGTH_DROP'. lia. }
  assert (HDf : DROP f (DROP (stack_space t) (stackSem.stack t)) = DROP f' rest).
  { rewrite HD2. cbn [DROP]. replace (f =? 0) with false by (symmetry; apply N.eqb_neq; lia).
    f_equal. lia. }
  assert (HTf : TAKE f (DROP (stack_space t) (stackSem.stack t)) = EL (stack_space t) (stackSem.stack t) :: TAKE f' rest).
  { rewrite HD2. cbn [TAKE]. replace (f =? 0) with false by (symmetry; apply N.eqb_neq; lia).
    f_equal. f_equal. lia. }
  assert (Hthe : the f (wordSem.locals_size s) = f).
  { unfold stack_size_rel in Hssr. destruct Hssr as (S1 & _). apply S1. lia. }
  unfold stackSem.set_var. sr_split; ws_fields; stk_fields; try assumption; rewrite ?LENGTH_LUPDATE', ?N.add_0_r in *;
    try assumption; try lia; try reflexivity.
  - (* stack_size_rel *)
    unfold stack_size_rel in *. rewrite LENGTH_LUPDATE'. destruct Hssr as (S1 & S2 & S3).
    split; [intros C; lia|]. split; [exact S2|]. intros sm Hsm.
    unfold OPTION_MAP2 in Hsm. destruct (wordSem.stack_max s) as [sm0|] eqn:Esm; [|discriminate].
    destruct (S3 sm0 eq_refl) as (S4 & S5 & ss & S6 & S7).
    destruct (wordSem.locals_size s) as [z|] eqn:Ez; [|discriminate]. cbn in Hthe. subst z.
    assert (Hfr : wordSem.stack_size (fr :: wordSem.stack s) = SOME (f + ss)).
    { rewrite (proj1 (stack_size_eq2 _ _)), S6. unfold fr. cbn [wordSem.stack_size_frame]. try rewrite Ez. reflexivity. }
    rewrite Hfr in Hsm. injection Hsm as <-. rewrite MAX_max.
    split; [lia|]. split; [reflexivity|]. exists (f + ss). split; [exact Hfr|lia].
  - (* stack_rel *)
    rewrite DROP_0_eq, HD. rewrite HDf in Hsr. destruct Hsr as (Hsorted & astack & Ha & Hh & Hr).
    split.
    + cbn [EVERY]. unfold is_true in *. rewrite Hsorted, andb_true_r. apply bool_decide_spec. exact Lsort.
    + exists ((NONE, (bits, TAKE f' rest)) :: astack).
      assert (Hfb : full_read_bitmap (bitmaps t) (Word (n2w (n + 1))) = SOME bits).
      { cbn [full_read_bitmap]. rewrite bd_false'.
        - rewrite <- word_add_n2w, WORD_ADD_SUB, w2n_n2w, N.mod_small by lia. exact Hrb.
        - intros E. apply (f_equal w2n) in E. rewrite !w2n_n2w, N.mod_small, N.Div0.mod_0_l in E by lia. lia. }
      assert (Hlb : LENGTH bits = f') by (unfold bits; apply LENGTH_GENLIST_N).
      assert (HTl : LENGTH (TAKE f' rest) = f') by (apply LENGTH_TAKE_le; exact Hlr).
      (* locals of the current frame *)
      assert (Hcur : forall r v, lookup r (wordSem.locals s) = SOME v -> k <= r DIV 2 ->
                 oEL (f' - 1 - (r DIV 2 - k)) (TAKE f' rest) = SOME v /\ r DIV 2 < k + f').
      { intros r v Hr1 Hr2. destruct (Hloc r v Hr1) as [_ Hrr].
        replace (r DIV 2 <? k) with false in Hrr by (symmetry; apply N.ltb_ge; exact Hr2).
        destruct Hrr as [Hrr1 Hrr2]. rewrite HTf in Hrr1. rewrite oEL_cons_pos in Hrr1 by lia.
        split; [|exact Hrr2]. rewrite <- Hrr1. f_equal. lia. }
      split; [unfold fr; rewrite abs_stack_NONE_eq with (bits := bits) by assumption; rewrite Ha; reflexivity|].
      split.
      * intros [Hh1 Hh2]. destruct (abs_stack_IMP_LENGTH _ _ _ _ _ Ha) as [Ea _].
        rewrite LENGTH_cons' in Hh1, Hh2.
        destruct (N.eq_dec (wordSem.handler s) (LENGTH (wordSem.stack s))) as [Eh|Eh].
        -- rewrite Eh in Hh2. replace (LENGTH (wordSem.stack s) + 1 - (LENGTH (wordSem.stack s) + 1)) with 0 in Hh2 by lia.
           cbn in Hh2. discriminate.
        -- rewrite LASTN_cons_le by lia. apply Hh. split; [lia|].
           replace (LENGTH (wordSem.stack s) + 1 - (wordSem.handler s + 1)) with
             (SUC (LENGTH (wordSem.stack s) - (wordSem.handler s + 1))) in Hh2 by lia.
           rewrite EL_SUC in Hh2. exact Hh2.
      * cbn [stack_rel_aux]. split; [|split; [|split; [rewrite HTl, <- Hff'; exact Hthe|exact Hr]]].
        -- intros r v [Hl0 Hln]. rewrite ALOOKUP_toAList, lookup_inter_alt in Hl0.
           destruct (decide (domain (FST names) r)) as [Hd|]; [|discriminate].
           destruct (Hn1 r Hd) as [Hev Hkr]. destruct (Hcur r v Hl0 Hkr) as [Hc1 Hc2].
           unfold adjust_names. rewrite Hlb. split; [lia|]. split.
           ++ unfold bits. rewrite oEL_EL by (rewrite LENGTH_GENLIST_N; lia).
              rewrite EL_GENLIST_N by lia. f_equal.
              destruct (MEM _ _) eqn:Em; [|reflexivity]. exfalso.
              unfold is_true in Em. rewrite MEM_In, in_map_iff in Em. destruct Em as ([r' []] & Er & Hin).
              rewrite <- MEM_In in Hin. apply MEM_toAList in Hin.
              assert (Hd' : domain (SND names) r') by (apply domain_lookup; eauto).
              destruct (Hn2 r' Hd') as [Hev' Hkr']. destruct (proj1 (domain_lookup _ _) (D2 r' Hd')) as [v' Hv'].
              destruct (Hcur r' v' Hv' Hkr') as [_ Hc2'].
              assert (Er' : r' = r) by (apply EVEN_DIV2_INJ; split; [exact Hev'|split; [exact Hev|lia]]).
              subst r'. apply ALOOKUP_None_iff in Hln. apply Hln. apply in_map_iff.
              exists (r, v). split; [reflexivity|]. apply (Permutation_in _ Lperm). rewrite <- MEM_In.
              apply MEM_toAList. rewrite lookup_inter_alt. destruct (decide (domain (SND names) r)); [exact Hl0|contradiction].
           ++ rewrite ALOOKUP_index_list by (rewrite HTl; lia). rewrite HTl. rewrite <- Hc1. f_equal. lia.
        -- apply (wlive_filter k f' names (wordSem.locals s) l (TAKE f' rest)); try assumption.
  - intros n0 v Hn. rewrite lookup_LN in Hn. discriminate.
Qed.

End WLiveNew.

Section EvaluateWLive.
Context {a : N} {c ffi_t : Type}.

(** HOL's conclusion also binds an unused [bs5] of unconstrained type; it is
    dropped here. *)
(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wLive" *)
Theorem evaluate_wLive : forall ac k f f' lens names bs n wlive_prog bs' n'
    (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t) envs,
  wLive names (bs, n) (k, (f, f')) = (wlive_prog, (bs', n')) /\
  (forall x, x IN domain (FST names) -> EVEN x /\ k <= x DIV 2) /\
  (forall x, x IN domain (SND names) -> EVEN x /\ k <= x DIV 2) /\
  state_rel ac k f f' s t lens 0 /\
  1 <= f /\
  wordSem.cut_envs names (wordSem.locals s) = SOME envs /\
  LENGTH (append bs) <= n /\ n - LENGTH (append bs) <= LENGTH (bitmaps t) /\
  isPREFIX (append bs') (DROP (n - LENGTH (append bs)) (bitmaps t)) ->
  exists t5 : stackSem.state a c ffi_t,
    evaluate (wlive_prog, t) = (NONE, t5) /\
    state_rel ac k 0 0 (wordSem.set_locals_size (SOME 0) (wordSem.set_locals LN (wordSem.push_env envs NONE s)))
      t5 (f' :: lens) 0 /\
    state_rel ac k f f' s t5 lens 0 /\
    LENGTH (stackSem.stack t5) = LENGTH (stackSem.stack t) /\ stack_space t5 = stack_space t /\
    (forall i, i <> k -> stackSem.get_var i t5 = stackSem.get_var i t).
Proof.
  intros ac k f f' lens names bs n wlive_prog bs' n' s t envs
    (Hw & Hn1 & Hn2 & R & Hf & Hcut & Hl1 & Hl2 & Hpre).
  unfold wLive in Hw. replace (f =? 0) with false in Hw by (symmetry; apply N.eqb_neq; lia).
  cbn [insert_bitmap] in Hw. injection Hw as <- <- <-.
  set (wb := @write_bitmap a (SND names) k f') in *.
  pose proof R as R'. sr_destr R'. rewrite N.add_0_r in *.
  assert (Hlt : stack_space t < LENGTH (stackSem.stack t)) by lia.
  rewrite (proj1 (append_thm _ _ [])), (proj1 (proj2 (append_thm bs bs wb))) in Hpre.
  apply isPREFIX_iff in Hpre as [rest Hrest].
  assert (HDn : DROP n (bitmaps t) = wb ++ rest).
  { replace n with (LENGTH (append bs) + (n - LENGTH (append bs))) by lia.
    rewrite <- DROP_DROP_EQ, Hrest, <- app_assoc. apply DROP_app_exact'. reflexivity. }
  assert (Hwb : 1 <= LENGTH wb).
  { unfold wb, write_bitmap. cbv zeta. rewrite LENGTH_word_list.
    destruct (dimindex a - 1 =? 0); [lia|]. apply N.le_add_l. }
  assert (Hnw : n + 1 < dimword a).
  { assert (E := f_equal (@LENGTH _) Hrest). rewrite LENGTH_DROP', !LENGTH_app' in E. lia. }
  assert (Hrb : read_bitmap (DROP n (bitmaps t)) =
      SOME (GENLIST (fun x => MEM x (MAP (fun '(r, y) => f' - 1 - (r DIV 2 - k)) (toAList (SND names)))) f')).
  { rewrite HDn. apply read_bitmap_append_extra. unfold wb. apply read_bitmap_write_bitmap. exact H8. }
  exists (set_stack (LUPDATE (Word (n2w (n + 1))) (stack_space t) (stackSem.stack t))
           (stackSem.set_var k (Word (n2w (n + 1))) t)).
  split; [apply wlive_eval; assumption|].
  split; [apply (wlive_state_rel_new ac k f f' lens envs names s t n); assumption|].
  split; [apply wlive_state_rel_old; assumption|].
  split; [stk_fields; apply LENGTH_LUPDATE'|]. split; [reflexivity|].
  intros i Hi. unfold stackSem.get_var, stackSem.set_var. stk_fields. rewrite FLOOKUP_UPDATE.
  destruct (decide (k = i)); [congruence|reflexivity].
Qed.

End EvaluateWLive.
