(** * CakeML [lab_to_targetProof]: observable semantics

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml] (HOL
    lines 9355-9590): [init_ok] and [machine_sem_EQ_sem].

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v].
    - HOL's [machine_sem mc s.ffi ms = { semantics s }] compares sets; here
      [machine_sem] is a predicate and the statement is an equality of
      predicates.
    - Not ported: the [saveState]/[loadState] calls inside a HOL comment. *)

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
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.semantics.proofs Require Import evaluateProps.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.compiler.backend Require Import labLang lab_to_target.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend.semantics Require wordSem backendProps.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem targetProps.
From Galette.cakeml.compiler.backend.semantics Require Import labSem labProps.
From Galette.cakeml.compiler.backend.proofs Require lab_filterProof.
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import
  basic bytes inst compile_lemmas rl_syntax rl_invariants rl_nop rl_labels rl_compute rl_remove
  code_props pos_props shmem cc_setup cc_asm cc_jump cc_ffi cc_install cc_share compile_correct.
Import wordLang (word_loc, Word, Loc).
Import wordSem (mem_load_byte_aux, mem_store_byte_aux, write_bytearray, mem_load_32,
  mem_store_32, buffer, position, buffer_buffer, space_left).
Import ByteBits.
Open Scope N_scope.




Section MachineSem.
Context {a : N} {B C Ffi : Type}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "init_ok_def" *)
Definition init_ok (x : machine_config a B C * word a) (s : labSem.state a config Ffi) (ms : B) : Prop :=
  let '(mc_conf, p) := x in
  exists code2 labs t1,
    state_rel (mc_conf, (code2, (labs, p))) s t1 ms /\
    oracle_tie mc_conf ms s.

Lemma halt_ne_err o : Halt o <> Error. Proof. discriminate. Qed.
Lemma halt_ne_to o : Halt o <> TimeOut. Proof. discriminate. Qed.
Lemma to_ne_err : TimeOut <> Error. Proof. discriminate. Qed.
Lemma err_ne_to : Error <> TimeOut. Proof. discriminate. Qed.

Lemma machine_io_chain (mc_conf : machine_config a B C) (st : ffi_state Ffi) (ms : B) :
  lprefix_chain (IMAGE (fun k => fromList (io_events (snd (snd (targetSem.evaluate mc_conf st k ms))))) UNIV).
Proof.
  assert (E : IMAGE (fun k => fromList (io_events (snd (snd (targetSem.evaluate mc_conf st k ms))))) UNIV =
              IMAGE fromList (IMAGE (fun k => io_events (snd (snd (targetSem.evaluate mc_conf st k ms)))) UNIV)).
  { apply functional_extensionality; intros y; apply propositional_extensionality.
    unfold IMAGE, UNIV. split.
    - intros (k & -> & _). eexists; split; [reflexivity|]. exists k. split; [reflexivity|exact Logic.I].
    - intros (l & -> & (k & -> & _)). exists k. split; [reflexivity|exact Logic.I]. }
  rewrite E. apply prefix_chain_lprefix_chain.
  intros l1 l2 [(k1 & -> & _) (k2 & -> & _)].
  destruct (N.le_ge_cases k1 k2); [left|right]; apply targetProps.evaluate_add_clock_io_events_mono; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "machine_sem_EQ_sem" *)
Theorem machine_sem_EQ_sem : forall (mc_conf : machine_config a B C) p (ms : B) (s1 : labSem.state a config Ffi),
  encoder_correct mc_conf.(target) /\
  init_ok (mc_conf, p) s1 ms /\ semantics s1 <> Fail ->
  machine_sem mc_conf (ffi s1) ms = (semantics s1) INSERT {}.
Proof.
  intros mc_conf p ms s1 (Henc & (code2 & labs & t1 & R & Ho) & Hsem).
  assert (CC : forall k r s', labSem.evaluate (set_clock k s1) = (r, s') -> r <> Error ->
                 exists k' ms2, targetSem.evaluate mc_conf (ffi s1) (k + k') ms = (r, (ms2, ffi s'))).
  { intros k r s' Ev Hr.
    destruct (compile_correct (set_clock k s1) r mc_conf s' code2 labs t1 ms p) as (k' & _ & ms2 & E).
    { split; [exact (oracle_tie_clock _ _ _ k Ho)|]. split; [exact Ev|]. split; [exact Hr|].
      split; [exact Henc|exact (state_rel_clock _ _ _ _ k R)]. }
    exists k', ms2. exact E. }
  assert (NoErr : forall k, FST (labSem.evaluate (set_clock k s1)) <> Error).
  { intros k Hk. apply Hsem. unfold semantics. destruct (classical_dec _) as [_|Hn]; [reflexivity|].
    exfalso. apply Hn. exists k. exact Hk. }
  apply functional_extensionality. intros b. apply propositional_extensionality.
  change ((semantics s1 INSERT {}) b) with (b IN (semantics s1 INSERT {})). rewrite IN_SING.
  unfold semantics. destruct (classical_dec _) as [[k Hk]|_]; [exfalso; exact (NoErr k Hk)|].
  destruct (some _) as [res|] eqn:Es.
  - (* termination *)
    apply some_SOME in Es as (k & t & o & Ev & ->).
    destruct (CC k _ _ Ev (halt_ne_err o)) as (k' & ms2 & Em).
    split.
    + intros Hb. destruct b as [io|o' io|]; cbn [machine_sem] in Hb.
      * exfalso. destruct Hb as [Hto _]. destruct (Hto (k + k')) as (ms' & st' & E'). rewrite Em in E'. discriminate.
      * destruct Hb as (k2 & ms' & st' & E2 & <-).
        pose proof (evaluate_ignore_clocks mc_conf (ffi s1) (k + k') ms _ _ _ k2 _ _ _
                      (conj Em (conj (halt_ne_to o) (conj E2 (halt_ne_to o'))))) as X.
        injection X as -> _ ->. reflexivity.
      * exfalso. destruct Hb as [k2 Hk2]. destruct (targetSem.evaluate mc_conf (ffi s1) k2 ms) as [r [ms' st']] eqn:E2.
        cbn in Hk2. subst r.
        pose proof (evaluate_ignore_clocks mc_conf (ffi s1) (k + k') ms _ _ _ k2 _ _ _
                      (conj Em (conj (halt_ne_to o) (conj E2 err_ne_to)))) as X.
        discriminate X.
    + intros ->. cbn [machine_sem]. exists (k + k'), ms2, (ffi t). split; [exact Em|reflexivity].
  - (* divergence *)
    pose proof (some_NONE _ Es) as NoHalt. clear Es.
    assert (AllTO : forall k, exists s', labSem.evaluate (set_clock k s1) = (TimeOut, s')).
    { intros k. destruct (labSem.evaluate (set_clock k s1)) as [r s'] eqn:Ev. exists s'.
      destruct r as [o| |].
      - exfalso. apply (NoHalt (Terminate o (io_events (ffi s')))). exists k, s', o. split; [exact Ev|reflexivity].
      - exfalso. apply (NoErr k). rewrite Ev. reflexivity.
      - reflexivity. }
    assert (MTO : forall k, exists ms' st', targetSem.evaluate mc_conf (ffi s1) k ms = (TimeOut, (ms', st'))).
    { intros k. destruct (targetSem.evaluate mc_conf (ffi s1) k ms) as [r [ms' st']] eqn:E. exists ms', st'.
      destruct (N.eq_dec 0 0) as [_|]; [|congruence].
      destruct r as [o| |]; [| |reflexivity]; exfalso.
      - destruct (AllTO k) as [s' Ev]. destruct (CC k _ _ Ev to_ne_err) as (k' & ms2 & Em).
        pose proof (targetProps.evaluate_add_clock mc_conf (ffi s1) k ms k' _ _ _ (conj E (halt_ne_to o))) as E'.
        rewrite Em in E'. discriminate E'.
      - destruct (AllTO k) as [s' Ev]. destruct (CC k _ _ Ev to_ne_err) as (k' & ms2 & Em).
        pose proof (targetProps.evaluate_add_clock mc_conf (ffi s1) k ms k' _ _ _ (conj E err_ne_to)) as E'.
        rewrite Em in E'. discriminate E'. }
    set (L1 := IMAGE (fun k => fromList (io_events (snd (snd (targetSem.evaluate mc_conf (ffi s1) k ms))))) UNIV).
    set (L2 := IMAGE (fun k => fromList (io_events (ffi (SND (labSem.evaluate (set_clock k s1)))))) UNIV).
    assert (C1 : lprefix_chain L1) by apply machine_io_chain.
    assert (C2 : lprefix_chain L2) by apply lab_filterProof.io_chain.
    assert (EQ : equiv_lprefix_chain L1 L2).
    { apply (equiv_lprefix_chain_thm L1 L2 (conj C1 C2)). unfold L1, L2, IMAGE, UNIV. split.
      - intros ll1 n x [(k & -> & _) Hx].
        destruct (AllTO k) as [s' Ev]. destruct (CC k _ _ Ev to_ne_err) as (k' & ms2 & Em).
        eexists; split; [exists k; split; [reflexivity|exact Logic.I]|].
        rewrite Ev. cbn [SND snd].
        pose proof (targetProps.evaluate_add_clock_io_events_mono mc_conf (ffi s1) k ms (k + k') ltac:(lia)) as P.
        rewrite Em in P. cbn [SND snd] in P.
        exact (lab_filterProof.LNTH_fromList_prefix _ _ n x P Hx).
      - intros ll2 n x [(k & -> & _) Hx].
        destruct (AllTO k) as [s' Ev]. destruct (CC k _ _ Ev to_ne_err) as (k' & ms2 & Em).
        eexists; split; [exists (k + k'); split; [reflexivity|exact Logic.I]|].
        rewrite Em. cbn [snd]. rewrite Ev in Hx. cbn [SND snd] in Hx. exact Hx. }
    split.
    + intros Hb. destruct b as [io|o' io|]; cbn [machine_sem] in Hb.
      * destruct Hb as [_ Hlub]. f_equal. apply (unique_lprefix_lub L2). split.
        -- apply (lprefix_lub_new_chain L1 L2). split; [exact C2|split; [exact EQ|exact Hlub]].
        -- apply build_lprefix_lub_thm, C2.
      * exfalso. destruct Hb as (k2 & ms' & st' & E2 & _). destruct (MTO k2) as (ms3 & st3 & E3).
        rewrite E2 in E3. discriminate.
      * exfalso. destruct Hb as [k2 Hk2]. destruct (MTO k2) as (ms3 & st3 & E3). rewrite E3 in Hk2. discriminate.
    + intros ->. cbn [machine_sem]. split; [exact MTO|].
      apply (lprefix_lub_new_chain L2 L1). split; [exact C1|split; [|apply build_lprefix_lub_thm, C2]].
      apply (equiv_lprefix_chain_thm L2 L1 (conj C2 C1)).
      apply (equiv_lprefix_chain_thm L1 L2 (conj C1 C2)) in EQ as [EQ1 EQ2]. split; assumption.
Qed.

End MachineSem.
