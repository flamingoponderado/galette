(** * CakeML [lab_to_targetProof]: [compile_correct], ASM instructions

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml]: the
    cases [Asm] (instructions and [JumpReg]) and [CBW] of
    [compile_correct] (HOL lines 7564-7845).

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v]; the cases
      are stated with [cc_goal] (see [lab_to_targetProof/cc_setup.v]).
    - HOL's case [Asm] is split into [cc_Asm_Inst] (tagged) and
      [cc_Asm_JumpReg]. *)

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
  code_props pos_props shmem cc_setup.
Import wordLang (word_loc, Word, Loc).
Import wordSem (mem_load_byte_aux, mem_store_byte_aux, write_bytearray, mem_load_32,
  mem_store_32, buffer, position, buffer_buffer, space_left).
Import ByteBits.
Open Scope N_scope.

Section AsmInst.
Context {a : N} {B C Ffi : Type}.

Lemma oracle_tie_step_same (mc_conf : machine_config a B C) ms1 (s1 s1' : labSem.state a config Ffi) l ms2 :
  oracle_tie mc_conf ms1 s1 ->
  (forall k, find_next_interference mc_conf (ffi s1) (k + l) ms1 =
             find_next_interference (shift_interfer l mc_conf) (ffi s1) k ms2) ->
  io_regs s1' = io_regs s1 -> io_fp_regs s1' = io_fp_regs s1 ->
  cc_regs s1' = cc_regs s1 -> cc_fp_regs s1' = cc_fp_regs s1 -> ffi s1' = ffi s1 ->
  oracle_tie (shift_interfer l mc_conf) ms2 s1'.
Proof.
  intros Ho H E1 E2 E3 E4 E5.
  exact (oracle_tie_step mc_conf ms1 s1 l ms2 s1' (conj Ho (conj H (conj E1 (conj E2 (conj E3 (conj E4 E5))))))).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "compile_correct" case "Asm" *)
Lemma cc_Asm_Inst p (s1 : labSem.state a config Ffi) i bytes len :
  clock s1 <> 0 ->
  asm_fetch s1 = SOME (Asm (Asmi (Inst i)) bytes len) ->
  ~ failed (asm_inst i s1) ->
  (forall s', clock s' < clock s1 -> @cc_goal a B C Ffi p s') ->
  forall res (mc_conf : machine_config a B C) s2 code2 labs (t1 : asm_state a) ms1,
    oracle_tie mc_conf ms1 s1 ->
    labSem.evaluate (inc_pc (dec_clock (asm_inst i s1))) = (res, s2) -> res <> Error ->
    encoder_correct mc_conf.(target) ->
    state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 ->
    exists k (t2 : asm_state a) ms2,
      targetSem.evaluate mc_conf (ffi s1) (clock s1 + k) ms1 = (res, (ms2, ffi s2)).
Proof.
  intros Hc Hf Hfail IH res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R.
  pose proof R as R0. apply state_rel_iff in R0.
  set (ffis := TAKE (THE (mmio_pcs_min_index mc_conf.(ffi_names))) mc_conf.(ffi_names)).
  destruct (IMP_bytes_in_memory_Inst mc_conf s1 t1 code2 labs ffis p i bytes len
              (conj (sr_code_similar R0) (conj (sr_all_enc_ok R0) (conj (sr_code_bytes R0) Hf))))
    as (bytes' & He & Hbm & Hbm' & Hpv & Hok).
  destruct (Inst_lemma mc_conf code2 labs p i s1 t1 ms1 ms1 bytes' (conj Hfail (conj R Hpv)))
    as (Hfi & Hmi & _).
  set (t1' := asm (Inst i) (asmSem.pc t1 + n2w (LENGTH bytes'))%w t1).
  assert (Hdis : ffi_entry_pcs_disjoint mc_conf t1 (LENGTH bytes')).
  { apply (IMP_ffi_entry_pcs_disjoint_Asm s1 mc_conf code2 labs ffis (Asmi (Inst i)) bytes len p).
    split; [exact (sr_code_similar R0)|]. split; [exact (sr_all_enc_ok R0)|].
    split; [exact (asm_fetch_aux_of _ _ Hf)|]. split; [intros op re a0 E; discriminate E|].
    split; [exact (sr_share_mem_domain_code_rel R0)|]. split; [exact Hbm'|].
    split; [rewrite Hpv; apply N.add_comm|exact (sr_pc R0)]. }
  destruct (asm_step_IMP_evaluate_step_nop mc_conf t1 ms1 (ffi s1) (Inst i) t1' bytes') as (l & ms2 & Hl).
  { split; [exact Henc|]. split; [exact (sr_prog_addresses R0)|]. split; [exact Hdis|].
    split; [exact (sr_interference_ok R0)|].
    split.
    { rewrite (sr_pc R0). apply (bytes_in_mem_IMP_memory _ (mem_domain s1) (asmSem.mem t1)).
      - intros a0 Ha0. symmetry. apply Hmi, Ha0.
      - exact Hbm'. }
    split.
    { unfold asm_step_nop. split; [rewrite (sr_pc R0); exact Hbm|]. split; [exact He|].
      split; [exact (sr_lr R0)|]. split; [exact (sr_t1_be R0)|]. split; [exact (sr_t1_align R0)|].
      split; [reflexivity|]. split; [exact Hfi|exact Hok]. }
    split; [reflexivity|]. split; [exact (sr_tsr R0)|]. intros x E; discriminate E. }
  destruct (asm_inst_consts i s1) as (Cpc & Ccode & Cclock & Cffi & Cio & Ciofp & Ccc & Cccfp & _).
  apply (cc_step p s1 (inc_pc (dec_clock (asm_inst i s1))) mc_conf l ms1 ms2 t1' code2 labs res s2).
  - exact Hc.
  - lst_cbn. rewrite Cclock. reflexivity.
  - lst_cbn. exact Cffi.
  - intros k. exact (proj1 (Hl k)).
  - exact (proj2 (proj2 (proj2 (Hl 0)))).
  - apply IH. lst_cbn. rewrite Cclock. lia.
  - apply (oracle_tie_step_same mc_conf ms1 s1); [exact Ho|intros k; exact (proj1 (proj2 (Hl k)))|..];
      lst_cbn; assumption.
  - exact Hev.
  - exact Hres.
  - exact Henc.
  - apply state_rel_shift_interfer.
    destruct (Inst_lemma mc_conf code2 labs p i s1 t1 ms1 ms2 bytes' (conj Hfail (conj R Hpv)))
      as (_ & _ & Hsr).
    apply Hsr. exact (proj1 (proj2 (proj2 (Hl 0)))).
Qed.

Lemma le_LENGTH_app {X} (l1 l2 : list X) : LENGTH l1 <= LENGTH (l1 ++ l2).
Proof. rewrite LENGTH_app. lia. Qed.

Lemma failed_false (t : asm_state a) : ~ asmSem.failed t -> asmSem.failed t = false.
Proof. destruct (asmSem.failed t); [intros H; exfalso; apply H; reflexivity|reflexivity]. Qed.

Lemma cc_Asm_JumpReg p (s1 : labSem.state a config Ffi) r1 bytes len l1 l2 x :
  clock s1 <> 0 ->
  asm_fetch s1 = SOME (Asm (Asmi (JumpReg r1)) bytes len) ->
  read_reg r1 s1 = Loc l1 l2 ->
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
  intros Hc Hf Hr Hx IH res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R.
  pose proof R as R0. apply state_rel_iff in R0.
  set (cfg := asmProps.config mc_conf.(target)) in *.
  assert (Hreg : asmSem.regs t1 r1 = (p + n2w (pos_val x 0 code2))%w).
  { pose proof (sr_regs R0 r1) as E. rewrite Hr in E. cbn [word_loc_val] in E.
    rewrite (sr_loc_to_pc R0 _ _ _ Hx) in E. injection E as E. symmetry. exact E. }
  destruct (fetch_line mc_conf code2 labs p s1 t1 ms1 _ R Hf) as (j & Hsim & Hok & Hbm & _ & _ & Hdis).
  { intros op re a0 bs l E. discriminate E. }
  destruct j as [| b bytes2 len2 |]; cbn in Hsim; try contradiction. subst b.
  destruct Hok as (He & _ & Hasm_ok). cbn [cbw_to_asm] in He, Hasm_ok.
  apply enc_with_nop_thm in He as [n Hb2]. cbn [line_bytes] in Hbm, Hdis.
  rewrite Hb2 in Hbm, Hdis. apply bytes_in_memory_APPEND in Hbm as [Hbm _].
  set (t1' := asm (JumpReg r1) (asmSem.pc t1 + n2w (LENGTH (encode cfg (JumpReg r1))))%w t1).
  assert (Hal : aligned (asmSem.align t1) (asmSem.regs t1 r1) = true).
  { rewrite Hreg, (sr_t1_align R0). exact (state_rel_aligned_pos _ _ _ _ _ _ _ x R Henc). }
  assert (Hft : ~ asmSem.failed t1').
  { unfold t1'. ast_cbn. rewrite Hal, (failed_false _ (sr_t1_failed R0)). cbn. discriminate. }
  destruct (asm_step_IMP_evaluate_step_find_next mc_conf t1 ms1 (ffi s1) (JumpReg r1))
    as (l & ms2 & Hl).
  { split; [exact Henc|]. split; [exact (sr_prog_addresses R0)|].
    split.
    { apply (ffi_entry_pcs_disjoint_LENGTH_shorter _ _ _ _ (conj Hdis (le_LENGTH_app _ _))). }
    split; [exact (sr_interference_ok R0)|].
    split; [|exact (sr_tsr R0)].
    unfold asm_step. split; [exact Hbm|]. split; [exact (sr_lr R0)|].
    split; [exact (sr_t1_be R0)|]. split; [exact (sr_t1_align R0)|].
    split; [reflexivity|]. split; [exact Hft|exact Hasm_ok]. }
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
    + unfold t1'. ast_cbn. exact Hreg.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + exact Hft.
Qed.

End AsmInst.

Section Cbw.
Context {a : N} {B C Ffi : Type}.

Lemma store8_fields (t : asm_state a) r1 r2 :
  asmSem.regs t r1 IN asmSem.mem_domain t ->
  let t' := inst (Mem Store8 r2 (Addr r1 (n2w 0))) t in
  (forall y, asmSem.mem t' y = (asmSem.regs t r1 =+ w2w (asmSem.regs t r2)) (asmSem.mem t) y) /\
  asmSem.regs t' = asmSem.regs t /\ asmSem.fp_regs t' = asmSem.fp_regs t /\
  asmSem.failed t' = asmSem.failed t /\ asmSem.mem_domain t' = asmSem.mem_domain t /\
  asmSem.be t' = asmSem.be t /\ asmSem.align t' = asmSem.align t /\ asmSem.lr t' = asmSem.lr t.
Proof.
  intros Hd t'. unfold t'. cbn [inst asmSem.mem_op].
  unfold asmSem.mem_store, asmSem.addr, asmSem.read_reg. cbv zeta.
  rewrite (proj1 WORD_ADD_0).
  set (w := asmSem.regs t r1).
  replace (aligned (LOG2 1) w) with true by (symmetry; apply aligned_w2n; cbn; apply N.mod_1_r).
  set (st := if asmSem.be t then (w + n2w (1 - 1))%w else w).
  assert (Hst : offs (asmSem.be t) st 0 = w)
    by (rewrite offs_0; unfold st; destruct (asmSem.be t); [exact (proj1 WORD_ADD_0 w)|reflexivity]).
  assert (Hdom : forall k, (k < 1)%N -> offs (asmSem.be t) st k IN asmSem.mem_domain t)
    by (intros k Hk; replace k with 0%N by lia; rewrite Hst; exact Hd).
  pose proof (write_mem_word_regs 1 st (asmSem.regs t r2) t) as [Er' Efp].
  destruct (write_mem_word_consts 1 st (asmSem.regs t r2) t) as (Cbe & Clr & Cal & Cdm).
  unfold asmSem.assert. cbn [asmSem.set_failed asmSem.regs asmSem.fp_regs asmSem.mem asmSem.failed
    asmSem.mem_domain asmSem.be asmSem.align asmSem.lr negb orb].
  split; [|split; [exact Er'|split; [exact Efp|split; [apply write_mem_word_failed, Hdom|]]]].
  - intros y. rewrite APPLY_UPDATE_THM. destruct (decide (w = y)) as [<-|Ne].
    + assert (Hdw : 1 <= dimword a)
        by (unfold dimword; pose proof (N.pow_nonzero 2 (dimindex a)); lia).
      rewrite <- Hst at 1. rewrite write_mem_word_mem_in by lia. rewrite N.mul_0_r, lsr_0. reflexivity.
    + apply write_mem_word_mem_out. intros j Hj E. replace j with 0%N in E by lia. rewrite Hst in E.
      congruence.
  - auto.
Qed.

Lemma add_n2w_inj (p : word a) x y :
  x < dimword a -> y < dimword a -> (p + n2w x)%w = (p + n2w y)%w -> x = y.
Proof.
  intros Hx Hy E. apply WORD_EQ_ADD_LCANCEL in E. apply n2w_11 in E.
  rewrite !N.mod_small in E by lia. exact E.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "compile_correct" case "CBW" *)
Lemma cc_Cbw p (s1 : labSem.state a config Ffi) r1 r2 bytes len w1 w2 new_cb :
  clock s1 <> 0 ->
  asm_fetch s1 = SOME (Asm (Cbw r1 r2) bytes len) ->
  read_reg r1 s1 = Word w1 -> read_reg r2 s1 = Word w2 ->
  wordSem.buffer_write (code_buffer s1) w1 (w2w w2) = SOME new_cb ->
  (forall s', clock s' < clock s1 -> @cc_goal a B C Ffi p s') ->
  forall res (mc_conf : machine_config a B C) s2 code2 labs (t1 : asm_state a) ms1,
    oracle_tie mc_conf ms1 s1 ->
    labSem.evaluate (inc_pc (dec_clock (set_code_buffer new_cb s1))) = (res, s2) -> res <> Error ->
    encoder_correct mc_conf.(target) ->
    state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 ->
    exists k (t2 : asm_state a) ms2,
      targetSem.evaluate mc_conf (ffi s1) (clock s1 + k) ms1 = (res, (ms2, ffi s2)).
Proof.
  intros Hc Hf Hr1 Hr2 Hbw IH res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R.
  pose proof R as R0. apply state_rel_iff in R0.
  set (cfg := asmProps.config mc_conf.(target)) in *.
  set (ffis := TAKE (THE (mmio_pcs_min_index mc_conf.(ffi_names))) mc_conf.(ffi_names)).
  assert (Et1 : asmSem.regs t1 r1 = w1).
  { pose proof (sr_regs R0 r1) as E. rewrite Hr1 in E. cbn [word_loc_val] in E. injection E as E. auto. }
  assert (Et2 : asmSem.regs t1 r2 = w2).
  { pose proof (sr_regs R0 r2) as E. rewrite Hr2 in E. cbn [word_loc_val] in E. injection E as E. auto. }
  set (cb := code_buffer s1) in *.
  unfold wordSem.buffer_write in Hbw.
  destruct (bool_decide _ && _) eqn:Ebw; [|discriminate]. injection Hbw as <-.
  apply Bool.andb_true_iff in Ebw as [Ew1 Hsp]. apply bool_decide_spec in Ew1. apply N.ltb_lt in Hsp.
  assert (Hw1 : w1 = (position cb + n2w (LENGTH (buffer_buffer cb) + 0))%w).
  { rewrite <- Ew1, N.add_0_r. replace (dimindex 8 DIV 8) with 1 by reflexivity. word_ring. }
  destruct (sr_cb_space R0 0 Hsp) as [Hw1d Hw1s]. fold cb in Hw1d, Hw1s. rewrite <- Hw1 in Hw1d, Hw1s.
  destruct (store8_fields t1 r1 r2 ltac:(rewrite Et1; exact Hw1d))
    as (Fm & Fr & Ffp & Ff & Fdm & Fbe & Fal & Flr).
  rewrite Et1, Et2 in Fm.
  destruct (IMP_bytes_in_memory_Cbw mc_conf s1 t1 code2 labs ffis p r1 r2 bytes len
              (conj (sr_code_similar R0) (conj (sr_all_enc_ok R0) (conj (sr_code_bytes R0) Hf))))
    as (bytes' & He & Hbm & Hbm' & Hpv & Hok).
  set (jj := Mem Store8 r2 (Addr r1 (n2w 0) : asm.addr a)) in *.
  set (t1' := asm (Inst jj) (asmSem.pc t1 + n2w (LENGTH bytes'))%w t1).
  pose proof (pos_val_bound (pc s1 + 1) 0 code2 cfg labs ffis 0 (sr_all_enc_ok R0)) as Hpb.
  pose proof (sr_cb_bound R0) as Hcbb. fold cb in Hcbb.
  pose proof (sr_cb_position R0) as Hcbp. fold cb in Hcbp.
  assert (Hw1p : w1 = (p + n2w (LENGTH (prog_to_bytes code2) + LENGTH (buffer_buffer cb)))%w).
  { rewrite Hw1, Hcbp, N.add_0_r, <- word_add_n2w. word_ring. }
  assert (Hne : forall n, n < LENGTH bytes' -> (asmSem.pc t1 + n2w n)%w <> w1).
  { intros n Hn E. rewrite (sr_pc R0), Hw1p, <- WORD_ADD_ASSOC, word_add_n2w in E.
    apply add_n2w_inj in E; lia. }
  assert (Hfail' : ~ asmSem.failed t1').
  { unfold t1'. ast_cbn. rewrite Ff. exact (sr_t1_failed R0). }
  assert (Hdis : ffi_entry_pcs_disjoint mc_conf t1 (LENGTH bytes')).
  { apply (IMP_ffi_entry_pcs_disjoint_Asm s1 mc_conf code2 labs ffis (Cbw r1 r2) bytes len p).
    split; [exact (sr_code_similar R0)|]. split; [exact (sr_all_enc_ok R0)|].
    split; [exact (asm_fetch_aux_of _ _ Hf)|]. split; [intros op re a0 E; discriminate E|].
    split; [exact (sr_share_mem_domain_code_rel R0)|]. split; [exact Hbm'|].
    split; [rewrite Hpv; apply N.add_comm|exact (sr_pc R0)]. }
  destruct (asm_step_IMP_evaluate_step_nop mc_conf t1 ms1 (ffi s1) (Inst jj) t1' bytes') as (l & ms2 & Hl).
  { split; [exact Henc|]. split; [exact (sr_prog_addresses R0)|]. split; [exact Hdis|].
    split; [exact (sr_interference_ok R0)|].
    split.
    { rewrite (sr_pc R0). apply (bytes_in_memory_change_mem _ _ (asmSem.mem t1)). split; [exact Hbm|].
      intros n Hn. unfold t1'. ast_cbn. rewrite Fm, APPLY_UPDATE_THM.
      destruct (decide (w1 = (p + n2w (pos_val (pc s1) 0 code2) + n2w n)%w)) as [E|]; [|reflexivity].
      exfalso. apply (Hne n Hn). rewrite (sr_pc R0). symmetry. exact E. }
    split.
    { unfold asm_step_nop. split; [rewrite (sr_pc R0); exact Hbm|]. split; [exact He|].
      split; [exact (sr_lr R0)|]. split; [exact (sr_t1_be R0)|]. split; [exact (sr_t1_align R0)|].
      split; [reflexivity|]. split; [exact Hfail'|exact Hok]. }
    split; [reflexivity|]. split; [exact (sr_tsr R0)|]. intros x E; discriminate E. }
  apply (cc_step p s1 (inc_pc (dec_clock (set_code_buffer
     (wordSem.mk_buffer (position cb) (buffer_buffer cb ++ [w2w w2]) (space_left cb - 1)) s1)))
     mc_conf l ms1 ms2 t1' code2 labs res s2).
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
  - apply state_rel_shift_interfer. apply state_rel_iff.
    pose proof (proj1 (proj2 (proj2 (Hl 0)))) as Htsr.
    pose proof (sr_mem R0) as Smem. pose proof (sr_cb_space R0) as Scbs.
    pose proof (sr_cb_ffi_entry R0) as Sffe. pose proof (sr_pc R0) as Spc.
    destruct R0. constructor; lst_cbn; unfold t1'; ast_cbn;
      rewrite ?Fr, ?Ffp, ?Fdm, ?Fbe, ?Fal, ?Flr; try assumption.
    all: cbn [position buffer_buffer space_left wordSem.position wordSem.buffer_buffer wordSem.space_left].
    + intros a0 Ha. destruct (Smem a0 Ha) as (H1 & H2 & H3).
      split; [exact H1|split; [exact H2|]]. rewrite Fm, APPLY_UPDATE_THM.
      destruct (decide (w1 = a0)) as [<-|]; [exfalso; exact (Hw1s H2)|exact H3].
    + intros n Hn. cbv zeta in Scbs. rewrite LENGTH_app. change (LENGTH [w2w w2 : word8]) with 1.
      replace (LENGTH (buffer_buffer cb) + 1 + n) with (LENGTH (buffer_buffer cb) + (n + 1)) by lia.
      apply Scbs. cbn [wordSem.space_left] in Hn. unfold cb in *. lia.
    + assert (Fm' : asmSem.mem (inst jj t1) = (w1 =+ w2w w2) (asmSem.mem t1))
        by (apply functional_extensionality; exact Fm).
      rewrite Fm'. apply bytes_in_mem_UPDATE. split; [|assumption].
      intros n Hn E. rewrite Hw1p in E. apply add_n2w_inj in E; lia.
    + assert (Fm' : asmSem.mem (inst jj t1) = (w1 =+ w2w w2) (asmSem.mem t1))
        by (apply functional_extensionality; exact Fm).
      rewrite Fm'. apply bytes_in_mem_APPEND. split.
      * apply bytes_in_mem_UPDATE. split; [|assumption].
        intros n Hn E. rewrite Hw1 in E. apply add_n2w_inj in E; lia.
      * cbn [bytes_in_mem]. rewrite <- (N.add_0_r (LENGTH (buffer_buffer cb))), <- Hw1.
        split; [exact Hw1d|]. split; [exact Hw1s|]. split; [|exact Logic.I].
        rewrite APPLY_UPDATE_THM. destruct (decide (w1 = w1)); [reflexivity|congruence].
    + rewrite LENGTH_app. change (LENGTH [w2w w2 : word8]) with 1. lia.
    + intros bn Hbn. apply Sffe. cbn [wordSem.space_left wordSem.buffer_buffer] in Hbn. unfold cb in *. rewrite LENGTH_app in Hbn. change (LENGTH [w2w w2 : word8]) with 1 in Hbn. lia.
    + rewrite Spc, Hpv, <- WORD_ADD_ASSOC, word_add_n2w. reflexivity.
Qed.

End Cbw.
