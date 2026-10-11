(** * CakeML [word_to_stackProof]: properties of the bitmap threading

    Part of the port of
    [cakeml/compiler/backend/proofs/word_to_stackProofScript.sml]: the
    syntactic facts about how [comp], [compile_prog] and
    [compile_word_to_stack] thread the bitmaps and code names (HOL lines
    2797-2856 and 5594-5717).  They are collected here, ahead of the
    semantic sections, because they only depend on the compiler.

    Notes:
    - HOL's [l1 ≼ l2] is [isPREFIX l1 l2].
    - HOL's variable [a] (the live sets of [wLive]) is [live] here, since
      [a] is the word width.
    - Proofs are by structural induction on wordLang programs (HOL:
      [comp_ind]). *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend Require Import word_to_stack.
From Galette.cakeml.compiler.backend.semantics Require Import wordConvs.
From Galette.cakeml.compiler.backend.semantics Require Import stackSem stackProps.
From Galette.cakeml.compiler.backend.proofs.word_to_stackProof Require Import basic.
Open Scope N_scope.

(** ** Galette-only helpers *)

Lemma isPREFIX_iff {A} `{EqDecision A} (l1 l2 : list A) :
  is_true (isPREFIX l1 l2) <-> exists l, l2 = l1 ++ l.
Proof.
  revert l2; induction l1 as [|x l1 IH]; intros [|y l2]; cbn; unfold is_true.
  - split; [exists []; reflexivity|reflexivity].
  - split; [eexists; reflexivity|reflexivity].
  - split; [discriminate|intros [l E]; discriminate].
  - rewrite andb_true_iff, bool_decide_spec. fold (is_true (isPREFIX l1 l2)). rewrite IH.
    split; [intros [-> [l ->]]; exists l; reflexivity|intros [l E]; injection E as -> ->; eauto].
Qed.

Lemma isPREFIX_app_r {A} `{EqDecision A} (l1 l2 : list A) : is_true (isPREFIX l1 (l1 ++ l2)).
Proof. apply isPREFIX_iff; eauto. Qed.

Lemma isPREFIX_trans' {A} `{EqDecision A} (l1 l2 l3 : list A) :
  is_true (isPREFIX l1 l2) -> is_true (isPREFIX l2 l3) -> is_true (isPREFIX l1 l3).
Proof. intros H1 H2; apply (isPREFIX_TRANS l1 l2 l3); auto. Qed.

(** Destruct the pair-[let]s ([match X with (_, _) => _ end]) of a
    hypothesis. *)
Ltac destr_pair_lets H :=
  repeat match type of H with
  | context [match ?X with (_, _) => _ end] =>
      lazymatch X with
      | (_, _) => fail
      | _ => let E := fresh "E" in destruct X as [? ?] eqn:E
      end; cbn beta iota zeta in H
  end.

(** Destruct all [let]s, [match]es and [if]s of a hypothesis, keeping
    equations for the pair-[let]s. *)
Ltac destr_all H :=
  repeat match type of H with
  | context [match ?X with (_, _) => _ end] =>
      lazymatch X with
      | (_, _) => fail
      | _ => let E := fresh "E" in destruct X as [? ?] eqn:E
      end; cbn beta iota zeta in H
  | context [match ?X with _ => _ end] =>
      lazymatch X with (_, _) => fail | _ => destruct X end; cbn beta iota zeta in H
  | context [if ?X then _ else _] => destruct X; cbn beta iota zeta in H
  end.

Section Prefix.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "insert_bitmap_isPREFIX" *)
Theorem insert_bitmap_isPREFIX : forall (bm : list (word a)) bs bs' i,
  insert_bitmap bm bs = (bs', i) ->
  isPREFIX (append (FST bs)) (append (FST bs')).
Proof.
  intros bm [d l] bs' i E. cbn in E. injection E as <- _. cbn [FST fst].
  rewrite (proj1 (append_thm _ _ [])), (proj1 (proj2 (append_thm d d bm))). apply isPREFIX_app_r.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wLive_isPREFIX" *)
Theorem wLive_isPREFIX : forall live bs (c : kf_ty) q bs',
  @wLive a live bs c = (q, bs') ->
  isPREFIX (append (FST bs)) (append (FST bs')).
Proof.
  intros live bs [k [f f']] q bs' E. unfold wLive in E.
  destruct (f =? 0).
  - injection E as _ <-. apply isPREFIX_REFL.
  - destruct (insert_bitmap _ bs) as [nb i] eqn:Ei. injection E as _ <-.
    eapply insert_bitmap_isPREFIX; exact Ei.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_IMP_isPREFIX" *)
Theorem comp_IMP_isPREFIX : forall ac perf (c1 : wordLang.prog a) bs r q1 bs',
  comp ac perf c1 bs r = (q1, bs') -> isPREFIX (append (FST bs)) (append (FST bs')).
Proof.
  intros ac perf c1. induction c1 using wordConvs.prog_nested_ind; intros bs0 r0 q0 bs1 Ec;
    cbn [comp] in Ec; destr_all Ec;
    try (injection Ec as _ <-; apply isPREFIX_REFL);
    try (injection Ec as _ <-; eauto using isPREFIX_trans'; fail).
  all: try (injection Ec as _ <-; eapply insert_bitmap_isPREFIX; eassumption).
  all: try (eapply IHc1; exact Ec).
  all: injection Ec as _ <-; cbn beta iota in *;
    repeat match goal with
    | H : comp _ _ ?p _ _ = _, IH : forall bs r q bs', comp _ _ ?p bs r = (q, bs') -> _ |- _ =>
        apply IH in H
    | H : wLive _ _ _ = _ |- _ => apply wLive_isPREFIX in H
    end; cbn [FST fst SND snd] in *; eauto using isPREFIX_trans'.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "compile_prog_isPREFIX" *)
Theorem compile_prog_isPREFIX : forall ac perf (x : wordLang.prog a) y k bs prog fs bs1,
  compile_prog ac perf x y k bs = (prog, (fs, bs1)) ->
  isPREFIX (append (FST bs)) (append (FST bs1)).
Proof.
  intros ac perf x y k bs prog fs bs1 E. unfold compile_prog in E. cbv zeta in E.
  destruct (comp _ _ _ _ _) as [q1 bm] eqn:Ec in E. injection E as _ _ <-.
  eapply comp_IMP_isPREFIX; exact Ec.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "compile_word_to_stack_isPREFIX" *)
Theorem compile_word_to_stack_isPREFIX : forall ac perf (code : list (N * (N * wordLang.prog a))) k bs progs1 fs1 bs1,
  compile_word_to_stack ac perf k code bs = (progs1, (fs1, bs1)) ->
  isPREFIX (append (FST bs)) (append (FST bs1)).
Proof.
  intros ac perf code; induction code as [|[i [n p]] code IH]; intros k bs progs1 fs1 bs1 E;
    cbn [compile_word_to_stack] in E.
  - injection E as _ _ <-. apply isPREFIX_REFL.
  - destr_all E. injection E as _ _ <-.
    eapply isPREFIX_trans'; [eapply compile_prog_isPREFIX; eassumption|eapply IH; eassumption].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "get_labels_wStackLoad" *)
Theorem get_labels_wStackLoad : forall xs (p : prog a),
  get_labels (wStackLoad xs p) = get_labels p.
Proof.
  induction xs as [|[r i] xs IH]; intros p; cbn [wStackLoad]; [reflexivity|].
  cbn [get_labels]. rewrite IH. apply set_ext; intros x; unfold pred_set.UNION, pred_set.EMPTY, pred_set.IN; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "loc_check_SUBSET" *)
Theorem loc_check_SUBSET : forall (s t : spt (prog a)),
  subspt s t -> loc_check s SUBSET loc_check t.
Proof.
  intros s t H [l1 l2] Hl. pose proof (proj1 (subspt_lookup s t) H) as H2; clear H; rename H2 into H. unfold loc_check, pred_set.IN in *.
  destruct Hl as [[-> Hd]|(n & e & Hn & He)].
  - left; split; [reflexivity|]. apply domain_lookup in Hd as [v Hv]. apply domain_lookup. eauto.
  - right. exists n, e. auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAP_FST_compile_word_to_stack" *)
Theorem MAP_FST_compile_word_to_stack : forall ac perf k (ps : list (N * (N * wordLang.prog a))) bm ps' bm',
  compile_word_to_stack ac perf k ps bm = (ps', bm') -> MAP FST ps' = MAP FST ps.
Proof.
  intros ac perf k ps; induction ps as [|[i [n p]] ps IH]; intros bm ps' bm' E;
    cbn [compile_word_to_stack] in E.
  - injection E as <- _. reflexivity.
  - destr_all E. injection E as <- _. cbn [MAP List.map FST fst]. f_equal. eapply IH; eassumption.
Qed.

Lemma insert_bitmap_LENGTH (ws : list (word a)) bs bs' i :
  insert_bitmap ws bs = (bs', i) -> LENGTH (append (FST bs)) <= SND bs ->
  LENGTH (append (FST bs')) <= SND bs' /\
  SND bs - LENGTH (append (FST bs)) = SND bs' - LENGTH (append (FST bs')).
Proof.
  destruct bs as [d l]; intros E H. cbn [insert_bitmap] in E. injection E as <- _.
  cbn [FST SND fst snd] in *. rewrite (proj1 (append_thm _ _ [])), (proj1 (proj2 (append_thm d d _))).
  rewrite LENGTH_app' in *. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wLive_LENGTH" *)
Theorem wLive_LENGTH : forall live bs (c : kf_ty) q bs',
  @wLive a live bs c = (q, bs') /\
  LENGTH (append (FST bs)) <= SND bs ->
  LENGTH (append (FST bs')) <= SND bs' /\
  SND bs - LENGTH (append (FST bs)) = SND bs' - LENGTH (append (FST bs')).
Proof.
  intros live [d l] [k [f f']] q bs' [E H]. unfold wLive in E. cbn [FST SND fst snd] in *.
  destruct (f =? 0).
  - injection E as _ <-. split; [exact H|reflexivity].
  - cbn [insert_bitmap] in E. injection E as _ <-. cbn [FST SND fst snd].
    rewrite (proj1 (append_thm _ _ [])), (proj1 (proj2 (append_thm d d _))).
    rewrite LENGTH_app' in *. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_IMP_LENGTH" *)
Theorem comp_IMP_LENGTH : forall ac perf (c1 : wordLang.prog a) bs r q1 bs',
  comp ac perf c1 bs r = (q1, bs') /\
  LENGTH (append (FST bs)) <= SND bs ->
  LENGTH (append (FST bs')) <= SND bs' /\
  SND bs - LENGTH (append (FST bs)) = SND bs' - LENGTH (append (FST bs')).
Proof.
  intros ac perf c1. induction c1 using wordConvs.prog_nested_ind; intros bs0 r0 q0 bs1 [Ec Hl];
    cbn [comp] in Ec; destr_all Ec;
    try (injection Ec as _ <-; split; [exact Hl|reflexivity]).
  all: try (eapply IHc1; split; [exact Ec|exact Hl]).
  all: injection Ec as _ <-; cbn beta iota in *;
    repeat match goal with
    | H : comp _ _ ?p ?b _ = _, IH : forall bs r q bs', comp _ _ ?p bs r = (q, bs') /\ _ -> _,
      Hb : LENGTH (append (FST ?b)) <= SND ?b |- _ =>
        let H2 := fresh "HL" in
        destruct (IH _ _ _ _ (conj H Hb)) as [H2 ?]; clear H
    | H : wLive _ ?b _ = _, Hb : LENGTH (append (FST ?b)) <= SND ?b |- _ =>
        let H2 := fresh "HL" in
        destruct (wLive_LENGTH _ _ _ _ _ (conj H Hb)) as [H2 ?]; clear H
    | H : insert_bitmap _ ?b = _, Hb : LENGTH (append (FST ?b)) <= SND ?b |- _ =>
        let H2 := fresh "HL" in
        destruct (insert_bitmap_LENGTH _ _ _ _ H Hb) as [H2 ?]; clear H
    end; split; [assumption|congruence].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "compile_prog_LENGTH" *)
Theorem compile_prog_LENGTH : forall ac perf (prog : wordLang.prog a) arg reg bm i prog' fs' bm' i',
  compile_prog ac perf prog arg reg (bm, i) = (prog', (fs', (bm', i'))) /\
  LENGTH (append bm) <= i ->
  LENGTH (append bm') <= i' /\
  i - LENGTH (append bm) = i' - LENGTH (append bm').
Proof.
  intros ac perf prog arg reg bm i prog' fs' bm' i' [E H]. unfold compile_prog in E. cbv zeta in E.
  destruct (comp _ _ _ _ _) as [q1 [bm1 i1]] eqn:Ec in E. injection E as _ _ <- <-.
  exact (comp_IMP_LENGTH _ _ _ _ _ _ _ (conj Ec H)).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "compile_word_to_stack_IMP_LENGTH" *)
Theorem compile_word_to_stack_IMP_LENGTH : forall ac perf (code : list (N * (N * wordLang.prog a))) k bm i progs fs bm' i',
  compile_word_to_stack ac perf k code (bm, i) = (progs, (fs, (bm', i'))) /\
  LENGTH (append bm) <= i ->
  LENGTH (append bm') <= i' /\
  i - LENGTH (append bm) = i' - LENGTH (append bm').
Proof.
  intros ac perf code; induction code as [|[n [m p]] code IH]; intros k bm i progs fs bm' i' [E H];
    cbn [compile_word_to_stack] in E.
  - injection E as _ _ <- <-. split; [exact H|reflexivity].
  - destr_all E. injection E; intros; subst.
    match goal with
    | H1 : compile_prog _ _ _ _ _ _ = (_, (_, ?b)) |- _ =>
        destruct b as [bm1 i1];
        destruct (compile_prog_LENGTH _ _ _ _ _ _ _ _ _ _ _ (conj H1 H)) as [Hl1 He1]
    end.
    match goal with
    | H2 : compile_word_to_stack _ _ _ _ _ = _ |- _ =>
        destruct (IH _ _ _ _ _ _ _ (conj H2 Hl1)) as [Hl2 He2]
    end.
    split; [exact Hl2|congruence].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "compile_word_to_stack_bitmaps" *)
Theorem compile_word_to_stack_bitmaps : forall c (p : list (N * (N * wordLang.prog a))) bitmaps c2 prog1,
  word_to_stack.compile c false p = (bitmaps, (c2, prog1)) ->
  match bitmaps with [] => False | h :: v1 => n2w 4 = h end /\
  bitmaps_length c2 = LENGTH bitmaps.
Proof.
  intros c p bitmaps c2 prog1 E. unfold word_to_stack.compile in E. cbv zeta in E.
  destruct (compile_word_to_stack _ _ _ _ _) as [progs [fs [bm i]]] eqn:Ec in E.
  injection E as <- <- _. cbn [FST SND fst snd bitmaps_length]. split.
  - apply compile_word_to_stack_isPREFIX in Ec. cbn [FST fst] in Ec.
    rewrite (proj1 (proj2 (append_thm (@Nil (word a)) Nil [n2w 4]))) in Ec.
    apply isPREFIX_iff in Ec as [l ->]. reflexivity.
  - destruct (compile_word_to_stack_IMP_LENGTH _ _ _ _ _ _ _ _ _ _ (conj Ec (N.le_refl _))) as [H1 H2].
    rewrite (proj1 (proj2 (append_thm (@Nil (word a)) Nil [n2w 4]))) in H2. cbn in H2. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "compile_word_to_stack_IMP_ALOOKUP" *)
Theorem compile_word_to_stack_IMP_ALOOKUP : forall ac perf (code : list (N * (N * wordLang.prog a))) k bs i progs fs bs' i' n arg_count word_prog x,
  compile_word_to_stack ac perf k code (bs, i) = (progs, (fs, (bs', i'))) /\
  ALOOKUP code n = SOME (arg_count, word_prog) /\
  LENGTH (append bs) <= i /\ i - LENGTH (append bs) <= LENGTH x /\
  isPREFIX (append bs') (DROP (i - LENGTH (append bs)) x) ->
  exists bs i bs2 i2 f stack_prog,
    compile_prog ac perf word_prog arg_count k (bs, i) = (stack_prog, (f, (bs2, i2))) /\
    LENGTH (append bs) <= i /\ i - LENGTH (append bs) <= LENGTH x /\
    isPREFIX (append bs2) (DROP (i - LENGTH (append bs)) x) /\
    ALOOKUP progs n = SOME stack_prog.
Proof.
  intros ac perf code; induction code as [|[n0 [m p]] code IH];
    intros k bs i progs fs bs' i' n arg_count word_prog x (E & Ha & H1 & H2 & H3);
    [discriminate|].
  cbn [compile_word_to_stack] in E. destr_all E. injection E; intros; subst.
  match goal with
  | Hc : compile_prog _ _ _ _ _ _ = (_, (_, ?b)) |- _ => destruct b as [bm1 i1]; rename Hc into Hc1
  end.
  match goal with Hw : compile_word_to_stack _ _ _ _ _ = _ |- _ => rename Hw into Hc2 end.
  pose proof (compile_word_to_stack_isPREFIX _ _ _ _ _ _ _ _ Hc2) as Hp. cbn [FST fst] in Hp.
  destruct (compile_prog_LENGTH _ _ _ _ _ _ _ _ _ _ _ (conj Hc1 H1)) as [Hl1 He1].
  cbn [ALOOKUP] in Ha |- *. destruct (decide (n0 = n)) as [<-|Hne].
  - injection Ha as <- <-. exists bs, i, bm1, i1, n1, p0. repeat split; try assumption.
    eapply isPREFIX_trans'; [exact Hp|exact H3].
  - assert (H2' : i1 - LENGTH (append bm1) <= LENGTH x) by lia.
    assert (H3' : isPREFIX (append bs') (DROP (i1 - LENGTH (append bm1)) x)) by (rewrite <- He1; exact H3).
    destruct (IH _ _ _ _ _ _ _ _ _ _ x (conj Hc2 (conj Ha (conj Hl1 (conj H2' H3'))))) as (bs2 & i2 & bs3 & i3 & f3 & sp & R).
    exists bs2, i2, bs3, i3, f3, sp. exact R.
Qed.

End Prefix.
