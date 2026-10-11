(** * CakeML [word_to_stackProof]: properties of the stack relation

    Part of the port of
    [cakeml/compiler/backend/proofs/word_to_stackProofScript.sml] (HOL lines
    2433-2796): [push_locals], prefixes of the abstract stack, and
    [stack_rel_raise] (raising to a handler frame).

    Notes: as in [state_rel.v].  [SORTED_FST_PERM_IMP_ALIST_EQ] is stated
    with Rocq's [Permutation] for HOL's [PERM] (not ported) and is
    untagged.  [SORTED_CONS_IMP], [SORTED_IMP_ALL_DISTINCT_LEMMA] and
    [MEM_toAList_fromAList] carry HOL's [num # 'a] element type with an
    [EqDecision] instance (for [MEM]). *)

From Galette Require Import Base Classical.
From Stdlib Require Import Permutation Sorting.Sorted.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend Require Import word_to_stack.
From Galette.cakeml.compiler.backend.semantics Require wordSem.
From Galette.cakeml.compiler.backend.proofs.word_to_stackProof Require Import basic compile_props state_rel gc.
Import wordLang (word_loc, Word, Loc).
Import wordSem (stack_frame, StackFrame).
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "push_locals_def" *)
Definition push_locals {a c ffi_t} l0 l (s : wordSem.state a c ffi_t) : wordSem.state a c ffi_t :=
  wordSem.set_stack (StackFrame (wordSem.locals_size s) l0 l NONE :: wordSem.stack s)
    (wordSem.set_locals_size (SOME 0) (wordSem.set_locals LN s)).

(** ** [LASTN] helpers (Galette-only) *)

Lemma LENGTH_LASTN' {A} n (l : list A) : LENGTH (LASTN n l) = N.min n (LENGTH l).
Proof. rewrite LASTN_DROP2, LENGTH_DROP'. lia. Qed.

Lemma LASTN_DROP_le {A} n m (l : list A) : n <= LENGTH (DROP m l) -> LASTN n (DROP m l) = LASTN n l.
Proof.
  intros H. rewrite LENGTH_DROP' in H. rewrite !LASTN_DROP2, LENGTH_DROP', DROP_DROP_EQ.
  destruct (N.le_gt_cases m (LENGTH l)) as [Hm|Hm]; [f_equal; lia|].
  rewrite !DROP_skipn, !skipn_all2; [reflexivity| |]; rewrite ?LENGTH_length in *; lia.
Qed.

Lemma LASTN_cons_lt {A} n (x : A) xs : n <= LENGTH xs -> LASTN n (x :: xs) = LASTN n xs.
Proof. apply LASTN_cons_le. Qed.

Lemma DROP_1_cons {A} (x : A) xs : DROP 1 (x :: xs) = xs.
Proof. rewrite DROP_skipn. reflexivity. Qed.

Lemma LASTN_all {A} n (l : list A) : LENGTH l <= n -> LASTN n l = l.
Proof. intros H. apply LASTN_MORE. lia. Qed.

Section StackRel.
Context {a : N}.

Lemma stack_rel_aux_tail k len (x : stack_frame a) xs y ys :
  stack_rel_aux k len (x :: xs) (y :: ys) -> stack_rel_aux k len xs ys.
Proof.
  destruct x as [n l0 l [[h1 [l1 l2]]|]], y as [[[loc hv]|] [bits frame]]; cbn [stack_rel_aux]; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_aux_LENGTH" *)
Theorem stack_rel_aux_LENGTH : forall k len (xs : list (stack_frame a)) ys,
  stack_rel_aux k len xs ys -> LENGTH xs = LENGTH ys.
Proof.
  intros k len xs; induction xs as [|x xs IH]; intros [|y ys] H.
  - reflexivity.
  - destruct y; cbn in H; contradiction.
  - destruct x as [? ? ? [[? [? ?]]|]]; cbn in H; contradiction.
  - rewrite !LENGTH_cons'. apply stack_rel_aux_tail in H. rewrite (IH _ H). reflexivity.
Qed.

Lemma stack_rel_aux_DROP k len : forall m (xs : list (stack_frame a)) ys,
  stack_rel_aux k len xs ys -> stack_rel_aux k len (DROP m xs) (DROP m ys).
Proof.
  intros m. induction m as [|m IH] using N.peano_ind; intros xs ys H.
  - rewrite !DROP_0_eq. exact H.
  - destruct xs as [|x xs], ys as [|y ys].
    + rewrite !DROP_skipn. destruct (N.to_nat _); exact H.
    + destruct y; cbn in H; contradiction.
    + destruct x as [? ? ? [[? [? ?]]|]]; cbn in H; contradiction.
    + rewrite !DROP_skipn, N2Nat.inj_succ. cbn [skipn]. rewrite <- !DROP_skipn.
      apply IH. eapply stack_rel_aux_tail; exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_aux_LASTN" *)
Theorem stack_rel_aux_LASTN : forall k len (xs : list (stack_frame a)) ys n,
  stack_rel_aux k len xs ys -> stack_rel_aux k len (LASTN n xs) (LASTN n ys).
Proof.
  intros k len xs ys n H. pose proof (stack_rel_aux_LENGTH _ _ _ _ H) as E.
  rewrite !LASTN_DROP2, E. apply stack_rel_aux_DROP, H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_stack_to_stack_LENGTH" *)
Theorem abs_stack_to_stack_LENGTH : forall (bs : list (word a)) wstack sstack lens stack,
  abs_stack bs wstack sstack lens = SOME stack -> handler_val stack = LENGTH sstack.
Proof.
  intros bs wstack; induction wstack as [|[n l0 l [hh|]] xs IH]; intros sstack lens stack H.
  - apply abs_stack_nil_inv in H as (-> & -> & ->). reflexivity.
  - apply abs_stack_SOME_inv in H as (loc & hv & w & st & len & lens' & bits & ys & -> & -> & _ & _ & Hl & Hy & ->).
    cbn [handler_val]. rewrite (IH _ _ _ Hy), LENGTH_TAKE_le, LENGTH_DROP', !LENGTH_cons' by exact Hl. lia.
  - apply abs_stack_NONE_inv in H as (w & st & len & lens' & bits & ys & -> & -> & _ & _ & Hl & Hy & ->).
    cbn [handler_val]. rewrite (IH _ _ _ Hy), LENGTH_TAKE_le, LENGTH_DROP', !LENGTH_cons' by exact Hl. lia.
Qed.

(** The [abs_stack] half of [abs_stack_prefix_drop] (Galette-only). *)
Lemma abs_stack_prefix_drop_abs : forall (bs : list (word a)) wstack sstack lens stack h,
  h <= LENGTH wstack ->
  abs_stack bs wstack sstack lens = SOME stack ->
  abs_stack bs (LASTN h wstack) (LASTN (handler_val (LASTN h stack)) sstack) (LASTN h lens) =
    SOME (LASTN h stack).
Proof.
  intros bs wstack; induction wstack as [|x xs IH]; intros sstack lens stack h Hh H.
  - pose proof H as H'. apply abs_stack_nil_inv in H' as (-> & -> & ->).
    rewrite !LASTN_all by (cbn; lia). exact H.
  - pose proof (abs_stack_IMP_LENGTH _ _ _ _ _ H) as [El1 El2].
    destruct (N.eq_dec h (LENGTH (x :: xs))) as [->|Hne].
    + rewrite (LASTN_all _ (x :: xs)), (LASTN_all _ stack), (LASTN_all _ lens) by lia.
      rewrite (abs_stack_to_stack_LENGTH _ _ _ _ _ H), LASTN_all by lia. exact H.
    + rewrite LENGTH_cons' in Hne, Hh. assert (Hh' : h <= LENGTH xs) by lia.
      rewrite LASTN_cons_lt by exact Hh'.
      destruct x as [n l0 l [hh|]].
      * pose proof H as H'.
        apply abs_stack_SOME_inv in H' as (loc & hv & w & st & len & lens' & bits & ys & -> & -> & _ & _ & Hl & Hy & ->).
        pose proof (abs_stack_IMP_LENGTH _ _ _ _ _ Hy) as [Ey1 Ey2].
        rewrite (LASTN_cons_lt h _ ys), (LASTN_cons_lt h _ lens') by lia.
        specialize (IH _ _ _ _ Hh' Hy).
        pose proof (abs_stack_to_stack_LENGTH _ _ _ _ _ IH) as Hv.
        rewrite LENGTH_LASTN' in Hv.
        assert (Hle : handler_val (LASTN h ys) <= LENGTH (DROP len st)) by lia.
        rewrite LASTN_DROP_le in IH by exact Hle.
        rewrite LENGTH_DROP' in Hle.
        rewrite !LASTN_cons_lt by (rewrite ?LENGTH_cons'; lia). exact IH.
      * pose proof H as H'.
        apply abs_stack_NONE_inv in H' as (w & st & len & lens' & bits & ys & -> & -> & _ & _ & Hl & Hy & ->).
        pose proof (abs_stack_IMP_LENGTH _ _ _ _ _ Hy) as [Ey1 Ey2].
        rewrite (LASTN_cons_lt h _ ys), (LASTN_cons_lt h _ lens') by lia.
        specialize (IH _ _ _ _ Hh' Hy).
        pose proof (abs_stack_to_stack_LENGTH _ _ _ _ _ IH) as Hv.
        rewrite LENGTH_LASTN' in Hv.
        assert (Hle : handler_val (LASTN h ys) <= LENGTH (DROP len st)) by lia.
        rewrite LASTN_DROP_le in IH by exact Hle.
        rewrite LENGTH_DROP' in Hle.
        rewrite !LASTN_cons_lt by (rewrite ?LENGTH_cons'; lia). exact IH.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_stack_prefix_drop" *)
Theorem abs_stack_prefix_drop : forall (bs : list (word a)) wstack sstack lens stack h wrest k len,
  h <= LENGTH wstack /\
  LASTN h wstack = wrest /\
  abs_stack bs wstack sstack lens = SOME stack /\
  stack_rel_aux k len wstack stack ->
  let rest := LASTN h stack in
  let lrest := LASTN h lens in
  let srest := LASTN (handler_val rest) sstack in
  abs_stack bs wrest srest lrest = SOME rest /\
  stack_rel_aux k len wrest rest.
Proof.
  intros bs wstack sstack lens stack h wrest k len (Hh & <- & H & Hr). cbv zeta. split.
  - apply abs_stack_prefix_drop_abs; assumption.
  - apply stack_rel_aux_LASTN, Hr.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_stack_len" *)
Theorem abs_stack_len : forall (bs : list (word a)) wstack sstack lens stack handler,
  abs_stack bs wstack sstack lens = SOME stack ->
  handler_val (LASTN handler stack) <= LENGTH sstack.
Proof.
  intros bs wstack sstack lens stack handler H.
  pose proof (abs_stack_IMP_LENGTH _ _ _ _ _ H) as [E1 E2].
  destruct (N.le_gt_cases handler (LENGTH wstack)) as [Hh|Hh].
  - pose proof (abs_stack_prefix_drop_abs _ _ _ _ _ _ Hh H) as H2.
    apply abs_stack_to_stack_LENGTH in H2. rewrite H2, LENGTH_LASTN'. lia.
  - rewrite LASTN_all by lia. rewrite (abs_stack_to_stack_LENGTH _ _ _ _ _ H). lia.
Qed.

End StackRel.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "EL_REVERSE_REWRITE" *)
Theorem EL_REVERSE_REWRITE : forall {A} `{Inhabited A} (l : list A) n k,
  n < LENGTH l /\ k < n ->
  EL (LENGTH l - n + k) l = EL (n - k - 1) (REVERSE l).
Proof.
  intros A HA l n k [H1 H2]. rewrite !EL_nth'. rewrite LENGTH_length in *.
  rewrite rev_nth by lia. f_equal. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LASTN_LESS" *)
Theorem LASTN_LESS : forall {A} (ls : list A) n x xs,
  n + 1 <= LENGTH ls /\ LASTN (n + 1) ls = x :: xs -> LASTN n ls = xs.
Proof.
  intros A ls n x xs [H1 H2]. rewrite LASTN_DROP2 in *.
  replace (LENGTH ls - n) with (1 + (LENGTH ls - (n + 1))) by lia.
  rewrite <- DROP_DROP_EQ, H2. apply DROP_1_cons.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "ALOOKUP_IFF_MEM" *)
Theorem ALOOKUP_IFF_MEM : forall {K V} `{EqDecision K} `{EqDecision V} (l : list (K * V)) q r,
  ALL_DISTINCT (MAP FST l) ->
  (ALOOKUP l q = SOME r <-> MEM (q, r) l).
Proof.
  intros K V HK HV l q r H. split.
  - apply ALOOKUP_MEM.
  - intros Hm. apply ALOOKUP_ALL_DISTINCT_MEM. split; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "SORTED_CONS_IMP" *)
Theorem SORTED_CONS_IMP : forall {B} `{EqDecision B} (h : N * B) t,
  SORTED (fun x y => FST x > FST y) (h :: t) ->
  ~ is_true (MEM h t) /\ SORTED (fun x y => FST x > FST y) t /\
  (forall x, MEM x t -> FST h > FST x).
Proof.
  intros B HB h t H. destruct (SORTED_FST_LESS_IMP _ _ H) as (? & ? & ?). auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "SORTED_IMP_ALL_DISTINCT_LEMMA" *)
Theorem SORTED_IMP_ALL_DISTINCT_LEMMA : forall {B} `{EqDecision B} (l : list (N * B)),
  SORTED (fun x y => FST x > FST y) l -> ALL_DISTINCT (MAP FST l).
Proof.
  intros B HB l H. apply SORTED_StronglySorted in H; [|intros; lia].
  apply ALL_DISTINCT_iff. induction H as [|x l Hs IH F]; cbn [MAP map]; constructor; [|exact IH].
  rewrite in_map_iff. intros [y [Ey Hy]]. rewrite Forall_forall in F. specialize (F y Hy).
  cbn [FST] in *. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MEM_toAList_fromAList" *)
Theorem MEM_toAList_fromAList : forall {B} `{EqDecision B} (l : list (N * B)) a0,
  SORTED (fun x y => FST x > FST y) l ->
  MEM a0 (toAList (fromAList l)) = MEM a0 l.
Proof.
  intros B HB l [q r] H. apply SORTED_IMP_ALL_DISTINCT_LEMMA in H.
  apply Bool.eq_iff_eq_true. split; intros Hm.
  - apply (ALOOKUP_IFF_MEM l q r H). apply MEM_toAList in Hm. rewrite lookup_fromAList in Hm. exact Hm.
  - apply MEM_toAList. rewrite lookup_fromAList. apply (ALOOKUP_IFF_MEM l q r H), Hm.
Qed.

(** HOL's [SORTED_FST_PERM_IMP_ALIST_EQ] with Rocq's [Permutation] for
    [PERM] (not ported); hence untagged. *)
Lemma SORTED_FST_PERM_IMP_ALIST_EQ {B} `{EqDecision B} (l q : list (N * B)) :
  SORTED (fun x y => FST x > FST y) l /\
  SORTED (fun x y => FST x > FST y) q /\
  Permutation (toAList (fromAList l)) q ->
  q = l.
Proof.
  intros (H1 & H2 & H3). apply SORTED_IMP_EQ_LISTS. split; [exact H1|split; [exact H2|]].
  intros x. rewrite <- (MEM_toAList_fromAList l x H1). unfold is_true. rewrite !MEM_In.
  split; intros Hx; [apply (Permutation_in _ H3)|apply (Permutation_in _ (Permutation_sym H3))]; exact Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "inter_union_left" *)
Theorem inter_union_left : forall {A} (s t : spt A),
  wf s -> inter (union s t) s = s.
Proof.
  intros A s t Hw. apply spt_eq_thm; [split; [apply wf_inter|exact Hw]|].
  intros n. rewrite lookup_inter, lookup_union. destruct (lookup n s); [reflexivity|]. destruct (lookup n t); reflexivity.
Qed.

Lemma EL_DROP_add {A} `{Inhabited A} m i (l : list A) : EL i (DROP m l) = EL (m + i) l.
Proof. rewrite !EL_nth', DROP_skipn, nth_skipn. f_equal. lia. Qed.

Section Raise.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_raise" *)
Theorem stack_rel_raise : forall n (sstack : list (word_loc a)) handler (wstack : list (stack_frame a))
    l m l0 h1 l3 l4 rest bs lens stack k,
  n <= LENGTH sstack /\
  handler + 1 <= LENGTH wstack /\ SORTED (fun x y => FST x > FST y) l /\
  LASTN (handler + 1) wstack = StackFrame m l0 l (SOME (h1, (l3, l4))) :: rest /\
  abs_stack bs wstack (DROP n sstack) lens = SOME stack /\
  stack_rel_aux k (LENGTH sstack) wstack stack ->
  exists ex payload,
    LASTN (handler + 1) stack = (SOME ex, payload) :: LASTN handler stack /\
    3 <= LENGTH sstack /\ 3 <= handler_val (LASTN (handler + 1) stack) /\
    EL (LENGTH sstack - handler_val (LASTN (handler + 1) stack) + 1) sstack = Loc l3 l4 /\
    ((h1 < LENGTH rest /\ is_handler_frame (EL (LENGTH rest - (h1 + 1)) rest) ->
      EL (LENGTH sstack - handler_val (LASTN (handler + 1) stack) + 2) sstack =
        Word (n2w (LENGTH sstack - handler_val (LASTN (h1 + 1) (LASTN (handler + 1) stack)))))) /\
    stack_rel_aux k (LENGTH sstack)
      (StackFrame m l0 (FST (wordSem.env_to_list (fromAList l) (K I))) NONE :: rest)
      ((NONE, payload) :: LASTN handler stack) /\
    abs_stack bs
      (StackFrame m l0 (FST (wordSem.env_to_list (fromAList l) (K I))) NONE :: rest)
      (DROP (LENGTH sstack - handler_val (LASTN (handler + 1) stack) + 3) sstack)
      (LASTN (handler + 1) lens) = SOME ((NONE, payload) :: LASTN handler stack).
Proof.
  intros n sstack handler wstack l m l0 h1 l3 l4 rest bs lens stack k (Hn & Hh & Hs & Hw & Habs & Hrel).
  pose proof (abs_stack_IMP_LENGTH _ _ _ _ _ Habs) as [El1 El2].
  pose proof (abs_stack_prefix_drop_abs _ _ _ _ _ (handler + 1) Hh Habs) as Hp. rewrite Hw in Hp.
  pose proof (stack_rel_aux_LASTN _ _ _ _ (handler + 1) Hrel) as Hr. rewrite Hw in Hr.
  remember (handler_val (LASTN (handler + 1) stack)) as hv eqn:Ehv0.
  pose proof (abs_stack_to_stack_LENGTH _ _ _ _ _ Hp) as Ehv.
  rewrite LENGTH_LASTN', LENGTH_DROP' in Ehv.
  assert (Hle : hv <= LENGTH (DROP n sstack)) by (rewrite LENGTH_DROP'; lia).
  rewrite (LASTN_DROP_le _ _ _ Hle), (LASTN_DROP2 sstack hv) in Hp.
  apply abs_stack_SOME_inv in Hp as (loc & hvw & w & st & len & lens' & bits & ys & Ed & El & Hb & Hlb & Hl & Hy & Est).
  assert (Ely : LASTN handler stack = ys).
  { apply (LASTN_LESS _ _ (SOME (loc, hvw), (bits, TAKE len st))). split; [lia|exact Est]. }
  rewrite Est in Hr. cbn [stack_rel_aux] in Hr. destruct Hr as (Hhv & Hloc & Hl0 & Hfb & Hthe & Hrest).
  pose proof (stack_rel_aux_LENGTH _ _ _ _ Hrest) as Erest.
  rewrite Est in Ehv0. cbn [handler_val] in Ehv0.
  assert (Ld : LENGTH (DROP (LENGTH sstack - hv) sstack) = 4 + LENGTH st) by (rewrite Ed, !LENGTH_cons'; lia).
  rewrite LENGTH_DROP' in Ld.
  assert (Hel : forall i, EL (LENGTH sstack - hv + i) sstack =
                 EL i (Word (n2w 1) :: loc :: hvw :: w :: st)).
  { intros i. rewrite <- Ed, EL_DROP_add. reflexivity. }
  destruct (wordSem.env_to_list (fromAList l) (K I)) as [l' orc] eqn:Een. cbn [FST fst].
  apply env_to_list_K_I_IMP in Een as (Hs' & _ & Hperm).
  assert (El' : l' = l) by (apply SORTED_FST_PERM_IMP_ALIST_EQ; auto). subst l'.
  exists (loc, hvw), (bits, TAKE len st).
  split; [rewrite Ely; exact Est|].
  split; [lia|]. split; [lia|].
  split; [rewrite Hel, EL_nth'; exact Hloc|].
  split.
  { intros [Hh1 Hhf]. rewrite Hel, EL_nth'. cbn [nth N.to_nat Pos.to_nat Pos.iter_op Nat.add].
    rewrite Est, LASTN_cons_lt by lia. apply Hhv. rewrite <- Erest. split; assumption. }
  split.
  { cbn [stack_rel_aux]. rewrite Ely. refine (conj Hl0 (conj Hfb (conj Hthe Hrest))). }
  rewrite El, Ely. replace (LENGTH sstack - hv + 3) with (3 + (LENGTH sstack - hv)) by lia.
  rewrite <- DROP_DROP_EQ, Ed, DROP_skipn. cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add skipn].
  rewrite (abs_stack_NONE_eq _ _ _ _ _ _ _ _ _ _ Hb Hlb Hl), Hy. reflexivity.
Qed.

End Raise.
