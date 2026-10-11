(** * CakeML [lab_to_targetProof]: [compile_correct], labelled instructions

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml]: the
    cases [Jump], [JumpCmp], [Call], [LocValue] and [Halt] of
    [compile_correct] (HOL lines 7971-8302 and 9300-9353).

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v]; the cases
      are stated with [cc_goal] (see [lab_to_targetProof/cc_setup.v]).
    - HOL's case [JumpCmp] is split into [cc_JumpCmp_true] (tagged) and
      [cc_JumpCmp_false]. *)

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
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import
  basic bytes inst compile_lemmas rl_syntax rl_invariants rl_nop rl_labels rl_compute rl_remove
  code_props pos_props shmem cc_setup cc_asm.
Import wordLang (word_loc, Word, Loc).
Import wordSem (mem_load_byte_aux, mem_store_byte_aux, write_bytearray, mem_load_32,
  mem_store_32, buffer, position, buffer_buffer, space_left).
Import ByteBits.
Open Scope N_scope.


Section Jumps.
Context {a : N} {B C Ffi : Type}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "compile_correct" case "Jump" *)
Lemma cc_Jump p (s1 : labSem.state a config Ffi) l1 l2 w bytes n x :
  clock s1 <> 0 ->
  asm_fetch s1 = SOME (LabAsm (Jump (Lab l1 l2)) w bytes n) ->
  loc_to_pc l1 l2 (code s1) = SOME x ->
  (forall s', clock s' < clock s1 -> @cc_goal a B C Ffi p s') ->
  forall res (mc_conf : machine_config a B C) s2 code2 labs (t1 : asm_state a) ms1,
    oracle_tie mc_conf ms1 s1 ->
    labSem.evaluate (upd_pc x (dec_clock s1)) = (res, s2) -> res <> Error ->
    encoder_correct mc_conf.(target) ->
    state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 ->
    exists k (t2 : asm_state a) ms2,
      targetSem.evaluate mc_conf (ffi s1) (clock s1 + k) ms1 = (res, (ms2, ffi s2)).
Proof.
  intros Hc Hf Hx IH res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R.
  pose proof R as R0. apply state_rel_iff in R0.
  set (cfg := asmProps.config mc_conf.(target)) in *.
  set (ffis := TAKE (THE (mmio_pcs_min_index mc_conf.(ffi_names))) mc_conf.(ffi_names)).
  destruct (IMP_bytes_in_memory_Jump mc_conf s1 t1 code2 labs ffis p (Lab l1 l2) w bytes n
              (conj (sr_code_similar R0) (conj (sr_all_enc_ok R0) (conj (sr_code_bytes R0) Hf))))
    as (tt & enc & Htt & Henc' & Hbm & Hok). subst enc.
  pose proof (sr_loc_to_pc R0 _ _ _ Hx) as Hll.
  pose proof (lab_lookup_IMP _ _ _ _ Hll) as Hfp.
  rewrite Hfp in Htt.
  destruct (fetch_line mc_conf code2 labs p s1 t1 ms1 _ R Hf) as (j & Hsim & Hjok & _ & _ & _ & Hdis).
  { intros op re a0 bs l E. discriminate E. }
  destruct j as [| | y w2 bytes2 len2]; cbn in Hsim; try contradiction. subst y.
  cbn [line_ok get_label] in Hjok. rewrite Hll in Hjok. cbv zeta in Hjok.
  destruct Hjok as (He2 & _ & _). cbn [lab_inst] in He2. rewrite <- Htt in He2.
  apply enc_with_nop_thm in He2 as [m Hb2]. cbn [line_bytes] in Hdis. rewrite Hb2 in Hdis.
  set (t1' := asm (asm.Jump tt) (asmSem.pc t1 + n2w (LENGTH (encode cfg (asm.Jump tt))))%w t1).
  assert (Hft : ~ asmSem.failed t1') by (unfold t1'; ast_cbn; exact (sr_t1_failed R0)).
  destruct (asm_step_IMP_evaluate_step_find_next mc_conf t1 ms1 (ffi s1) (asm.Jump tt))
    as (l & ms2 & Hl).
  { split; [exact Henc|]. split; [exact (sr_prog_addresses R0)|].
    split; [exact (ffi_entry_pcs_disjoint_LENGTH_shorter _ _ _ _ (conj Hdis (le_LENGTH_app _ _)))|].
    split; [exact (sr_interference_ok R0)|].
    split; [|exact (sr_tsr R0)].
    unfold asm_step. split; [rewrite (sr_pc R0); exact Hbm|]. split; [exact (sr_lr R0)|].
    split; [exact (sr_t1_be R0)|]. split; [exact (sr_t1_align R0)|].
    split; [reflexivity|]. split; [exact Hft|exact Hok]. }
  fold cfg t1' in Hl.
  apply (cc_step p s1 (upd_pc x (dec_clock s1)) mc_conf l ms1 ms2 t1' code2 labs res s2).
  - exact Hc.
  - lst_cbn. reflexivity.
  - lst_cbn. reflexivity.
  - intros k. exact (proj1 (Hl k)).
  - exact (proj2 (proj2 (proj2 (Hl 0)))).
  - apply IH. lst_cbn. lia.
  - apply (oracle_tie_step_same mc_conf ms1 s1); [exact Ho|intros k; exact (proj1 (proj2 (Hl k)))|..];
      lst_cbn; reflexivity.
  - exact Hev.
  - exact Hres.
  - exact Henc.
  - apply state_rel_shift_interfer. unfold upd_pc.
    apply (state_rel_pc_step mc_conf code2 labs p s1 t1 t1' ms1 ms2 x R).
    + exact (proj1 (proj2 (proj2 (Hl 0)))).
    + unfold t1'. ast_cbn. rewrite (sr_pc R0), Htt. word_ring.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + exact Hft.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "compile_correct" case "JumpCmp" *)
Lemma cc_JumpCmp_true p (s1 : labSem.state a config Ffi) cmp rr ri l1 l2 w bytes n x :
  clock s1 <> 0 ->
  asm_fetch s1 = SOME (LabAsm (JumpCmp cmp rr ri (Lab l1 l2)) w bytes n) ->
  wordSem.word_cmp cmp (read_reg rr s1) (labSem.reg_imm ri s1) = SOME true ->
  loc_to_pc l1 l2 (code s1) = SOME x ->
  (forall s', clock s' < clock s1 -> @cc_goal a B C Ffi p s') ->
  forall res (mc_conf : machine_config a B C) s2 code2 labs (t1 : asm_state a) ms1,
    oracle_tie mc_conf ms1 s1 ->
    labSem.evaluate (upd_pc x (dec_clock s1)) = (res, s2) -> res <> Error ->
    encoder_correct mc_conf.(target) ->
    state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 ->
    exists k (t2 : asm_state a) ms2,
      targetSem.evaluate mc_conf (ffi s1) (clock s1 + k) ms1 = (res, (ms2, ffi s2)).
Proof.
  intros Hc Hf Hcmp Hx IH res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R.
  pose proof R as R0. apply state_rel_iff in R0.
  set (cfg := asmProps.config mc_conf.(target)) in *.
  set (ffis := TAKE (THE (mmio_pcs_min_index mc_conf.(ffi_names))) mc_conf.(ffi_names)).
  pose proof (word_cmp_lemma mc_conf code2 labs p s1 t1 ms1 cmp rr ri true (conj R Hcmp)) as Hcmp'.
  destruct (IMP_bytes_in_memory_JumpCmp mc_conf s1 t1 code2 labs ffis p cmp rr ri (Lab l1 l2) w bytes n
              (conj (sr_code_similar R0) (conj (sr_all_enc_ok R0) (conj (sr_code_bytes R0) Hf))))
    as (tt & enc & Htt & Henc' & Hbm & Hok). subst enc.
  pose proof (sr_loc_to_pc R0 _ _ _ Hx) as Hll.
  pose proof (lab_lookup_IMP _ _ _ _ Hll) as Hfp.
  rewrite Hfp in Htt.
  destruct (fetch_line mc_conf code2 labs p s1 t1 ms1 _ R Hf) as (j & Hsim & Hjok & _ & _ & _ & Hdis).
  { intros op re a0 bs l E. discriminate E. }
  destruct j as [| | y w2 bytes2 len2]; cbn in Hsim; try contradiction. subst y.
  cbn [line_ok get_label] in Hjok. rewrite Hll in Hjok. cbv zeta in Hjok.
  destruct Hjok as (He2 & _ & _). cbn [lab_inst] in He2. rewrite <- Htt in He2.
  apply enc_with_nop_thm in He2 as [m Hb2]. cbn [line_bytes] in Hdis. rewrite Hb2 in Hdis.
  set (i := asm.JumpCmp cmp rr ri tt).
  set (t1' := asm i (asmSem.pc t1 + n2w (LENGTH (encode cfg i)))%w t1).
  assert (Ht1' : t1' = asmSem.upd_pc (asmSem.pc t1 + tt)%w t1).
  { unfold t1', i. cbn [asm]. rewrite <- Hcmp'. reflexivity. }
  assert (Hft : ~ asmSem.failed t1') by (rewrite Ht1'; ast_cbn; exact (sr_t1_failed R0)).
  destruct (asm_step_IMP_evaluate_step_find_next mc_conf t1 ms1 (ffi s1) i) as (l & ms2 & Hl).
  { split; [exact Henc|]. split; [exact (sr_prog_addresses R0)|].
    split; [exact (ffi_entry_pcs_disjoint_LENGTH_shorter _ _ _ _ (conj Hdis (le_LENGTH_app _ _)))|].
    split; [exact (sr_interference_ok R0)|].
    split; [|exact (sr_tsr R0)].
    unfold asm_step. split; [rewrite (sr_pc R0); exact Hbm|]. split; [exact (sr_lr R0)|].
    split; [exact (sr_t1_be R0)|]. split; [exact (sr_t1_align R0)|].
    split; [reflexivity|]. split; [exact Hft|exact Hok]. }
  fold cfg t1' in Hl.
  apply (cc_step p s1 (upd_pc x (dec_clock s1)) mc_conf l ms1 ms2 t1' code2 labs res s2).
  - exact Hc.
  - lst_cbn. reflexivity.
  - lst_cbn. reflexivity.
  - intros k. exact (proj1 (Hl k)).
  - exact (proj2 (proj2 (proj2 (Hl 0)))).
  - apply IH. lst_cbn. lia.
  - apply (oracle_tie_step_same mc_conf ms1 s1); [exact Ho|intros k; exact (proj1 (proj2 (Hl k)))|..];
      lst_cbn; reflexivity.
  - exact Hev.
  - exact Hres.
  - exact Henc.
  - apply state_rel_shift_interfer. unfold upd_pc.
    apply (state_rel_pc_step mc_conf code2 labs p s1 t1 t1' ms1 ms2 x R);
      [exact (proj1 (proj2 (proj2 (Hl 0))))|..|exact Hft]; rewrite Ht1'; ast_cbn; try reflexivity.
    rewrite (sr_pc R0), Htt. word_ring.
Qed.

Lemma cc_JumpCmp_false p (s1 : labSem.state a config Ffi) cmp rr ri jt w bytes n :
  clock s1 <> 0 ->
  asm_fetch s1 = SOME (LabAsm (JumpCmp cmp rr ri jt) w bytes n) ->
  wordSem.word_cmp cmp (read_reg rr s1) (labSem.reg_imm ri s1) = SOME false ->
  (forall s', clock s' < clock s1 -> @cc_goal a B C Ffi p s') ->
  forall res (mc_conf : machine_config a B C) s2 code2 labs (t1 : asm_state a) ms1,
    oracle_tie mc_conf ms1 s1 ->
    labSem.evaluate (inc_pc (dec_clock s1)) = (res, s2) -> res <> Error ->
    encoder_correct mc_conf.(target) ->
    state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 ->
    exists k (t2 : asm_state a) ms2,
      targetSem.evaluate mc_conf (ffi s1) (clock s1 + k) ms1 = (res, (ms2, ffi s2)).
Proof.
  intros Hc Hf Hcmp IH res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R.
  pose proof R as R0. apply state_rel_iff in R0.
  set (cfg := asmProps.config mc_conf.(target)) in *.
  set (ffis := TAKE (THE (mmio_pcs_min_index mc_conf.(ffi_names))) mc_conf.(ffi_names)).
  pose proof (word_cmp_lemma mc_conf code2 labs p s1 t1 ms1 cmp rr ri false (conj R Hcmp)) as Hcmp'.
  destruct (IMP_bytes_in_memory_JumpCmp_1 mc_conf s1 t1 code2 labs ffis p cmp rr ri jt w bytes n
              (conj (sr_code_similar R0) (conj (sr_all_enc_ok R0) (conj (sr_code_bytes R0) Hf))))
    as (tt & bytes' & Htt & He & Hbm & Hpv & Hok).
  destruct (fetch_line mc_conf code2 labs p s1 t1 ms1 _ R Hf) as (j & _ & _ & _ & _ & Hpv' & Hdis).
  { intros op re a0 bs l E. discriminate E. }
  assert (Hlen : LENGTH (line_bytes j) = LENGTH bytes') by lia.
  rewrite Hlen in Hdis.
  set (i := asm.JumpCmp cmp rr ri tt).
  set (t1' := asm i (asmSem.pc t1 + n2w (LENGTH bytes'))%w t1).
  assert (Ht1' : t1' = asmSem.upd_pc (asmSem.pc t1 + n2w (LENGTH bytes'))%w t1).
  { unfold t1', i. cbn [asm]. rewrite <- Hcmp'. reflexivity. }
  assert (Hft : ~ asmSem.failed t1') by (rewrite Ht1'; ast_cbn; exact (sr_t1_failed R0)).
  destruct (asm_step_IMP_evaluate_step_nop mc_conf t1 ms1 (ffi s1) i t1' bytes') as (l & ms2 & Hl).
  { split; [exact Henc|]. split; [exact (sr_prog_addresses R0)|]. split; [exact Hdis|].
    split; [exact (sr_interference_ok R0)|].
    split; [rewrite Ht1'; ast_cbn; rewrite (sr_pc R0); exact Hbm|].
    split.
    { unfold asm_step_nop. split; [rewrite (sr_pc R0); exact Hbm|]. split; [exact He|].
      split; [exact (sr_lr R0)|]. split; [exact (sr_t1_be R0)|]. split; [exact (sr_t1_align R0)|].
      split; [reflexivity|]. split; [exact Hft|exact Hok]. }
    split; [reflexivity|]. split; [exact (sr_tsr R0)|]. intros y E; discriminate E. }
  apply (cc_step p s1 (inc_pc (dec_clock s1)) mc_conf l ms1 ms2 t1' code2 labs res s2).
  - exact Hc.
  - lst_cbn. reflexivity.
  - lst_cbn. reflexivity.
  - intros k. exact (proj1 (Hl k)).
  - exact (proj2 (proj2 (proj2 (Hl 0)))).
  - apply IH. lst_cbn. lia.
  - apply (oracle_tie_step_same mc_conf ms1 s1); [exact Ho|intros k; exact (proj1 (proj2 (Hl k)))|..];
      lst_cbn; reflexivity.
  - exact Hev.
  - exact Hres.
  - exact Henc.
  - apply state_rel_shift_interfer. unfold inc_pc.
    change (pc (dec_clock s1) + 1) with (pc s1 + 1).
    apply (state_rel_pc_step mc_conf code2 labs p s1 t1 t1' ms1 ms2 (pc s1 + 1) R);
      [exact (proj1 (proj2 (proj2 (Hl 0))))|..|exact Hft]; rewrite Ht1'; ast_cbn; try reflexivity.
    rewrite (sr_pc R0), Hpv, <- WORD_ADD_ASSOC, word_add_n2w. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "compile_correct" case "Call" *)
Lemma cc_Call (s1 : labSem.state a config Ffi) lab w bytes n :
  asm_fetch s1 = SOME (LabAsm (Call lab) w bytes n) ->
  forall p (mc_conf : machine_config a B C) code2 labs (t1 : asm_state a) ms1,
    state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 -> False.
Proof.
  intros Hf p mc_conf code2 labs t1 ms1 R. apply state_rel_iff in R.
  exact (IMP_bytes_in_memory_Call mc_conf s1 t1 code2 labs _ p lab w bytes n
           (conj (sr_code_similar R) (conj (sr_all_enc_ok R) (conj (sr_code_bytes R) Hf)))).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "compile_correct" case "LocValue" *)
Lemma cc_LocValue p (s1 : labSem.state a config Ffi) r l1 l2 w bytes n x :
  clock s1 <> 0 ->
  asm_fetch s1 = SOME (LabAsm (LocValue r (Lab l1 l2)) w bytes n) ->
  loc_to_pc l1 l2 (code s1) = SOME x ->
  (forall s', clock s' < clock s1 -> @cc_goal a B C Ffi p s') ->
  forall res (mc_conf : machine_config a B C) s2 code2 labs (t1 : asm_state a) ms1,
    oracle_tie mc_conf ms1 s1 ->
    labSem.evaluate (inc_pc (dec_clock (upd_reg r (Loc l1 l2) s1))) = (res, s2) -> res <> Error ->
    encoder_correct mc_conf.(target) ->
    state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 ->
    exists k (t2 : asm_state a) ms2,
      targetSem.evaluate mc_conf (ffi s1) (clock s1 + k) ms1 = (res, (ms2, ffi s2)).
Proof.
  intros Hc Hf Hx IH res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R.
  pose proof R as R0. apply state_rel_iff in R0.
  set (cfg := asmProps.config mc_conf.(target)) in *.
  set (ffis := TAKE (THE (mmio_pcs_min_index mc_conf.(ffi_names))) mc_conf.(ffi_names)).
  destruct (IMP_bytes_in_memory_LocValue mc_conf s1 t1 code2 labs ffis p r l1 l2 w bytes n
              (conj (sr_code_similar R0) (conj (sr_all_enc_ok R0) (conj (sr_code_bytes R0) Hf))))
    as (tt & bytes' & Htt & He & Hbm & Hpv & Hok).
  pose proof (sr_loc_to_pc R0 _ _ _ Hx) as Hll.
  pose proof (lab_lookup_IMP _ _ _ _ Hll) as Hfp.
  rewrite Hfp in Htt.
  destruct (fetch_line mc_conf code2 labs p s1 t1 ms1 _ R Hf) as (j & _ & _ & _ & _ & Hpv' & Hdis).
  { intros op re a0 bs l E. discriminate E. }
  assert (Hlen : LENGTH (line_bytes j) = LENGTH bytes') by lia.
  rewrite Hlen in Hdis.
  set (i := asm.Loc r tt).
  set (t1' := asm i (asmSem.pc t1 + n2w (LENGTH bytes'))%w t1).
  assert (Hft : ~ asmSem.failed t1') by (unfold t1', i; ast_cbn; exact (sr_t1_failed R0)).
  destruct (asm_step_IMP_evaluate_step_nop mc_conf t1 ms1 (ffi s1) i t1' bytes') as (l & ms2 & Hl).
  { split; [exact Henc|]. split; [exact (sr_prog_addresses R0)|]. split; [exact Hdis|].
    split; [exact (sr_interference_ok R0)|].
    split; [unfold t1', i; ast_cbn; rewrite (sr_pc R0); exact Hbm|].
    split.
    { unfold asm_step_nop. split; [rewrite (sr_pc R0); exact Hbm|]. split; [exact He|].
      split; [exact (sr_lr R0)|]. split; [exact (sr_t1_be R0)|]. split; [exact (sr_t1_align R0)|].
      split; [reflexivity|]. split; [exact Hft|exact Hok]. }
    split; [reflexivity|]. split; [exact (sr_tsr R0)|]. intros y E; discriminate E. }
  apply (cc_step p s1 (inc_pc (dec_clock (upd_reg r (Loc l1 l2) s1))) mc_conf l ms1 ms2 t1' code2 labs res s2).
  - exact Hc.
  - lst_cbn. reflexivity.
  - lst_cbn. reflexivity.
  - intros k. exact (proj1 (Hl k)).
  - exact (proj2 (proj2 (proj2 (Hl 0)))).
  - apply IH. lst_cbn. lia.
  - apply (oracle_tie_step_same mc_conf ms1 s1); [exact Ho|intros k; exact (proj1 (proj2 (Hl k)))|..];
      lst_cbn; reflexivity.
  - exact Hev.
  - exact Hres.
  - exact Henc.
  - apply state_rel_shift_interfer.
    apply (state_rel_inst_step mc_conf code2 labs p s1 _ t1 t1' ms1 ms2 R
             (proj1 (proj2 (proj2 (Hl 0)))));
      unfold t1', i; lst_cbn; ast_cbn; try reflexivity.
    + exact (sr_s1_failed R0).
    + exact Hft.
    + rewrite (sr_pc R0), Hpv, <- WORD_ADD_ASSOC, word_add_n2w. reflexivity.
    + exact (sr_fp_regs R0).
    + intros r'. rewrite !APPLY_UPDATE_THM. destruct (decide (r = r')) as [<-|].
      * cbn [word_loc_val]. rewrite Hll, (sr_pc R0), Htt. f_equal. word_ring.
      * exact (sr_regs R0 r').
    + intros a0 Ha. exact (proj2 (proj2 (sr_mem R0 a0 Ha))).
Qed.

Lemma reg_ok_tsr (mc_conf : machine_config a B C) (t : asm_state a) ms r :
  target_state_rel mc_conf.(target) t ms -> reg_ok r (asmProps.config mc_conf.(target)) ->
  get_reg mc_conf.(target) ms r = asmSem.regs t r.
Proof.
  intros (_ & _ & _ & Hr & _) Hok. apply Hr. unfold reg_ok in Hok.
  apply Bool.andb_true_iff in Hok as [H1 H2]. apply N.ltb_lt in H1.
  apply Bool.negb_true_iff in H2. split; [exact H1|]. intros Hm. unfold is_true in Hm. congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "compile_correct" case "Halt" *)
Lemma cc_Halt p (s1 : labSem.state a config Ffi) w bytes n :
  clock s1 <> 0 ->
  asm_fetch s1 = SOME (LabAsm labLang.Halt w bytes n) ->
  forall res (mc_conf : machine_config a B C) s2 code2 labs (t1 : asm_state a) ms1,
    oracle_tie mc_conf ms1 s1 ->
    (match regs s1 (ptr_reg s1) with
     | Word w0 => if bool_decide (w0 = n2w 0) then (Halt Success, s1) else (Halt Resource_limit_hit, s1)
     | _ => (Error, s1)
     end) = (res, s2) -> res <> Error ->
    encoder_correct mc_conf.(target) ->
    state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 ->
    exists k (t2 : asm_state a) ms2,
      targetSem.evaluate mc_conf (ffi s1) (clock s1 + k) ms1 = (res, (ms2, ffi s2)).
Proof.
  intros Hc Hf res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R.
  pose proof R as R0. apply state_rel_iff in R0.
  set (cfg := asmProps.config mc_conf.(target)) in *.
  set (ffis := TAKE (THE (mmio_pcs_min_index mc_conf.(ffi_names))) mc_conf.(ffi_names)).
  destruct (regs s1 (ptr_reg s1)) as [w0|] eqn:Ep; [|injection Hev as <- _; contradiction].
  assert (Hev' : res = (if bool_decide (w0 = n2w 0) then Halt Success else Halt Resource_limit_hit) /\ s2 = s1)
    by (destruct (bool_decide _); injection Hev as <- <-; auto).
  clear Hev. destruct Hev' as [-> ->].
  assert (Ew0 : asmSem.regs t1 (ptr_reg s1) = w0).
  { pose proof (sr_regs R0 (ptr_reg s1)) as E. rewrite Ep in E. cbn [word_loc_val] in E.
    injection E as E. auto. }
  destruct (IMP_bytes_in_memory_Halt mc_conf s1 t1 code2 labs ffis p w bytes n
              (conj (sr_code_similar R0) (conj (sr_all_enc_ok R0) (conj (sr_code_bytes R0) Hf))))
    as (tt & enc & Htt & Henc' & Hbm & Hok). subst enc.
  destruct (fetch_line mc_conf code2 labs p s1 t1 ms1 _ R Hf) as (j & Hsim & Hjok & _ & _ & _ & Hdis).
  { intros op re a0 bs l E. discriminate E. }
  destruct j as [| | y w2 bytes2 len2]; cbn in Hsim; try contradiction. subst y.
  cbn [line_ok] in Hjok. cbv zeta in Hjok. destruct Hjok as (He2 & _ & _).
  rewrite <- Htt in He2.
  apply enc_with_nop_thm in He2 as [m Hb2]. cbn [line_bytes] in Hdis. rewrite Hb2 in Hdis.
  set (t1' := asm (asm.Jump tt) (asmSem.pc t1 + n2w (LENGTH (encode cfg (asm.Jump tt))))%w t1).
  assert (Hft : ~ asmSem.failed t1') by (unfold t1'; ast_cbn; exact (sr_t1_failed R0)).
  destruct (asm_step_IMP_evaluate_step_find_next mc_conf t1 ms1 (ffi s1) (asm.Jump tt))
    as (l & ms2 & Hl).
  { split; [exact Henc|]. split; [exact (sr_prog_addresses R0)|].
    split; [exact (ffi_entry_pcs_disjoint_LENGTH_shorter _ _ _ _ (conj Hdis (le_LENGTH_app _ _)))|].
    split; [exact (sr_interference_ok R0)|].
    split; [|exact (sr_tsr R0)].
    unfold asm_step. split; [rewrite (sr_pc R0); exact Hbm|]. split; [exact (sr_lr R0)|].
    split; [exact (sr_t1_be R0)|]. split; [exact (sr_t1_align R0)|].
    split; [reflexivity|]. split; [exact Hft|exact Hok]. }
  fold cfg t1' in Hl.
  destruct (Hl (clock s1)) as (E1 & _ & Htsr & _).
  pose proof Htsr as (_ & Hpc & _).
  assert (Hpc' : get_pc mc_conf.(target) ms2 = mc_conf.(halt_pc)).
  { rewrite Hpc. unfold t1'. ast_cbn. rewrite (sr_pc R0), Htt, <- (sr_halt_pos R0), <- word_add_n2w.
    word_ring. }
  exists l, t1, ms2. rewrite E1, targetSem.evaluate_eqn.
  rewrite (proj2 (N.eqb_neq _ _) Hc). unfold targetSem.evaluate_body.
  change (target (shift_interfer l mc_conf)) with (target mc_conf).
  change (prog_addresses (shift_interfer l mc_conf)) with (prog_addresses mc_conf).
  change (halt_pc (shift_interfer l mc_conf)) with (halt_pc mc_conf).
  change (targetSem.ptr_reg (shift_interfer l mc_conf)) with (targetSem.ptr_reg mc_conf).
  destruct (classical_dec _) as [Hin|_].
  { exfalso. rewrite Hpc' in Hin. apply (sr_halt_pc R0). exact (proj1 Hin). }
  rewrite Hpc'. destruct (decide (halt_pc mc_conf = halt_pc mc_conf)) as [_|]; [|congruence].
  rewrite (sr_ptr_reg R0), (reg_ok_tsr mc_conf t1' ms2 _ Htsr (sr_ptr_reg_ok R0)).
  unfold t1'. ast_cbn. rewrite Ew0.
  destruct (decide (w0 = n2w 0)) as [E|E].
  - rewrite (proj2 (bool_decide_spec _) E). reflexivity.
  - rewrite (bool_decide_false _ E). reflexivity.
Qed.

End Jumps.
