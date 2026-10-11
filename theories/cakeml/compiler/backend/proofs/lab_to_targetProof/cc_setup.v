(** * CakeML [lab_to_targetProof]: [compile_correct], set-up

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml]: the
    statement of [compile_correct] (HOL line 7528) as a predicate on the
    source state ([cc_goal], Galette helper) and the generic step that
    combines one machine step with the induction hypothesis.

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v].
    - HOL proves [compile_correct] by induction on [labSem.evaluate] with
      [p] fixed; [cc_goal p s1] is the statement for one state [s1]. *)

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
  code_props pos_props shmem.
Import wordLang (word_loc, Word, Loc).
Import wordSem (mem_load_byte_aux, mem_store_byte_aux, write_bytearray, mem_load_32,
  mem_store_32, buffer, position, buffer_buffer, space_left).
Import ByteBits.
Open Scope N_scope.

(** Reduce projections of [labSem] state updates (Galette tactic). *)
Ltac lst_cbn :=
  cbn [regs fp_regs mem mem_domain shared_mem_domain pc be ffi io_regs cc_regs io_fp_regs
       cc_fp_regs code compile compile_oracle code_buffer clock failed ptr_reg len_reg
       ptr2_reg len2_reg link_reg
       set_regs set_fp_regs set_mem set_mem_domain set_shared_mem_domain set_pc set_be
       set_ffi set_io_regs set_cc_regs set_io_fp_regs set_cc_fp_regs set_code set_compile
       set_compile_oracle set_code_buffer set_clock set_failed set_ptr_reg set_len_reg
       set_ptr2_reg set_len2_reg set_link_reg
       upd_pc upd_reg dec_clock inc_pc] in *.

(** Reduce projections of [asmSem] state updates (Galette tactic). *)
Ltac ast_cbn :=
  cbn [asmSem.regs asmSem.fp_regs asmSem.mem asmSem.mem_domain asmSem.pc asmSem.lr
       asmSem.align asmSem.be asmSem.failed
       asmSem.set_regs asmSem.set_fp_regs asmSem.set_mem asmSem.set_mem_domain asmSem.set_pc
       asmSem.set_lr asmSem.set_align asmSem.set_be asmSem.set_failed
       asmSem.upd_pc asmSem.upd_reg asmSem.assert asmSem.jump_to_offset asmSem.read_reg asm] in *;
  unfold asmSem.read_reg in *.

Section MachineSteps.
Context {a : N} {B C Ffi : Type}.

(** A machine step at an FFI entry point of an external call (Galette
    helper). *)
Lemma evaluate_ExtCall_step (mc : machine_config a B C) (ffi0 : ffi_state Ffi) K ms idx name xb xb2 :
  K <> 0 ->
  get_pc mc.(target) ms NOTIN mc.(prog_addresses) ->
  get_pc mc.(target) ms <> mc.(halt_pc) ->
  get_pc mc.(target) ms <> mc.(ccache_pc) ->
  find_index (get_pc mc.(target) ms) mc.(ffi_entry_pcs) 0 = SOME idx ->
  EL idx mc.(ffi_names) = ExtCall name ->
  ALOOKUP mc.(mmio_info) idx = NONE ->
  read_ffi_bytearrays mc ms = (SOME xb, SOME xb2) ->
  targetSem.evaluate mc ffi0 K ms =
  match call_FFI ffi0 (ExtCall name) xb xb2 with
  | FFI_final outcome => (Halt (FFI_outcome outcome), (ms, ffi0))
  | FFI_return new_ffi new_bytes =>
      targetSem.evaluate (set_ffi_interfer (shift_seq 1 mc.(ffi_interfer)) mc) new_ffi (K - 1)
        (mc.(ffi_interfer) 0 (idx, (new_bytes, ms)))
  end.
Proof.
  intros HK Hp Hh Hc Hf He Ha Hr. rewrite targetSem.evaluate_eqn, (proj2 (N.eqb_neq _ _) HK).
  unfold targetSem.evaluate_body.
  destruct (classical_dec _) as [Hin|_]; [exfalso; exact (Hp (proj1 Hin))|].
  destruct (decide _) as [E|_]; [contradiction|].
  destruct (decide _) as [E|_]; [contradiction|].
  rewrite Hf, He, Ha, Hr. destruct (call_FFI ffi0 (ExtCall name) xb xb2); reflexivity.
Qed.

(** A machine step at the clear-cache entry point (Galette helper). *)
Lemma evaluate_ccache_step (mc : machine_config a B C) (ffi0 : ffi_state Ffi) K ms :
  K <> 0 ->
  get_pc mc.(target) ms NOTIN mc.(prog_addresses) ->
  get_pc mc.(target) ms <> mc.(halt_pc) ->
  get_pc mc.(target) ms = mc.(ccache_pc) ->
  targetSem.evaluate mc ffi0 K ms =
  targetSem.evaluate (set_ccache_interfer (shift_seq 1 mc.(ccache_interfer)) mc) ffi0 (K - 1)
    (mc.(ccache_interfer) 0 (get_reg mc.(target) ms mc.(targetSem.ptr_reg),
                             (get_reg mc.(target) ms mc.(targetSem.len_reg), ms))).
Proof.
  intros HK Hp Hh Hc. rewrite targetSem.evaluate_eqn, (proj2 (N.eqb_neq _ _) HK).
  unfold targetSem.evaluate_body.
  destruct (classical_dec _) as [Hin|_]; [exfalso; exact (Hp (proj1 Hin))|].
  destruct (decide _) as [E|_]; [contradiction|].
  destruct (decide _) as [_|E]; [|contradiction].
  reflexivity.
Qed.

End MachineSteps.

Section WordLocMono.
Context {a : N}.

Lemma word_loc_val_mono (p : word a) labs labs' w v :
  (forall l1 l2 x, lab_lookup l1 l2 labs = SOME x -> lab_lookup l1 l2 labs' = SOME x) ->
  word_loc_val p labs w = SOME v -> word_loc_val p labs' w = SOME v.
Proof.
  intros Hm H. destruct w as [w0|k1 k2]; cbn [word_loc_val] in *; [exact H|].
  destruct (lab_lookup k1 k2 labs) as [q|] eqn:E; [|discriminate]. rewrite (Hm _ _ _ E). exact H.
Qed.

Lemma word_loc_val_byte_mono (p : word a) labs labs' m a0 be v :
  (forall l1 l2 x, lab_lookup l1 l2 labs = SOME x -> lab_lookup l1 l2 labs' = SOME x) ->
  word_loc_val_byte p labs m a0 be = SOME v -> word_loc_val_byte p labs' m a0 be = SOME v.
Proof.
  intros Hm H. unfold word_loc_val_byte in *.
  destruct (word_loc_val p labs (m (byte_align a0))) as [w|] eqn:E; [|discriminate].
  rewrite (word_loc_val_mono p labs labs' _ _ Hm E). exact H.
Qed.

End WordLocMono.

Lemma find_index_TAKE_gen {X} `{EqDecision X} (x : X) : forall l i k j,
  find_index x l k = SOME j -> j < k + i -> find_index x (TAKE i l) k = SOME j.
Proof.
  induction l as [|y l IH]; intros i k j Hf Hj; [discriminate|].
  cbn [TAKE]. destruct (N.eqb_spec i 0) as [->|Hi].
  - apply find_index_LESS_LENGTH in Hf. lia.
  - cbn [find_index] in Hf |- *. destruct (decide (y = x)); [exact Hf|].
    apply IH; [exact Hf|lia].
Qed.

Lemma find_index_TAKE {X} `{EqDecision X} (x : X) l i j :
  find_index x l 0 = SOME j -> j < i -> find_index x (TAKE i l) 0 = SOME j.
Proof. intros Hf Hj. apply find_index_TAKE_gen; [exact Hf|lia]. Qed.

Section Goal.
Context {a : N} {B C Ffi : Type}.

(** The statement of [compile_correct] for one source state (Galette
    helper). *)
Definition cc_goal (p : word a) (s1 : labSem.state a config Ffi) : Prop :=
  forall res (mc_conf : machine_config a B C) s2 code2 labs (t1 : asm_state a) ms1,
    oracle_tie mc_conf ms1 s1 /\
    labSem.evaluate s1 = (res, s2) /\ res <> Error /\
    encoder_correct mc_conf.(target) /\
    state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 ->
    exists k (t2 : asm_state a) ms2,
      targetSem.evaluate mc_conf s1.(ffi) (s1.(clock) + k) ms1 = (res, (ms2, s2.(ffi))).

(** One machine step [l] followed by the induction hypothesis (Galette
    helper). *)
Lemma cc_step p (s1 s1' : labSem.state a config Ffi) (mc_conf : machine_config a B C) l ms1 ms2
    (t1' : asm_state a) code2 labs res s2 :
  clock s1 <> 0 ->
  clock s1' = clock s1 - 1 ->
  ffi s1' = ffi s1 ->
  (forall k, targetSem.evaluate mc_conf (ffi s1) (k + l) ms1 =
             targetSem.evaluate (shift_interfer l mc_conf) (ffi s1) k ms2) ->
  l <> 0 ->
  cc_goal p s1' ->
  oracle_tie (shift_interfer l mc_conf) ms2 s1' ->
  labSem.evaluate s1' = (res, s2) -> res <> Error ->
  encoder_correct mc_conf.(target) ->
  state_rel (shift_interfer l mc_conf, (code2, (labs, p))) s1' t1' ms2 ->
  exists k (t2 : asm_state a) ms2',
    targetSem.evaluate mc_conf (ffi s1) (clock s1 + k) ms1 = (res, (ms2', ffi s2)).
Proof.
  intros Hc Hc' Hf Hev Hl IH Ho Hs Hres Henc Hr.
  destruct (IH res (shift_interfer l mc_conf) s2 code2 labs t1' ms2) as (k & t2 & ms2' & E).
  { split; [exact Ho|]. split; [exact Hs|]. split; [exact Hres|]. split; [|exact Hr].
    rewrite shift_interfer_target. exact Henc. }
  exists (k + l - 1), t2, ms2'. rewrite Hc', Hf in E.
  replace (clock s1 + (k + l - 1)) with ((clock s1 - 1 + k) + l) by lia.
  rewrite Hev. exact E.
Qed.

(** Code addresses are aligned (Galette helper). *)
Lemma state_rel_aligned_pos (mc_conf : machine_config a B C) code2 labs p
    (s1 : labSem.state a config Ffi) (t1 : asm_state a) ms1 x :
  state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 ->
  encoder_correct mc_conf.(target) ->
  aligned (code_alignment (asmProps.config mc_conf.(target))) (p + n2w (pos_val x 0 code2))%w.
Proof.
  intros R Henc. apply state_rel_iff in R.
  apply (aligned_add_sub_cor _ p (n2w (pos_val x 0 code2))). split.
  - apply aligned_bitwise_and. rewrite <- (sr_t1_align R). exact (sr_p_align R).
  - apply (all_enc_ok_aligned_pos_val mc_conf labs code2 x
             (TAKE (THE (mmio_pcs_min_index mc_conf.(ffi_names))) mc_conf.(ffi_names))).
    split; [exact (sr_all_enc_ok R)|]. split; [|exact Henc].
    intros Hodd. apply (has_odd_inst_alignment _ labs
      (TAKE (THE (mmio_pcs_min_index mc_conf.(ffi_names))) mc_conf.(ffi_names)) 0 code2).
    split; [exact (sr_enc_ok R)|]. split; [exact (sr_all_enc_ok R)|exact Hodd].
Qed.

(** [state_rel] after a step that only moves the program counters
    (Galette helper). *)
Lemma state_rel_pc_step (mc_conf : machine_config a B C) code2 labs p
    (s1 : labSem.state a config Ffi) (t1 t1' : asm_state a) ms1 ms2 x :
  state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 ->
  target_state_rel mc_conf.(target) t1' ms2 ->
  asmSem.pc t1' = (p + n2w (pos_val x 0 code2))%w ->
  asmSem.regs t1' = asmSem.regs t1 -> asmSem.fp_regs t1' = asmSem.fp_regs t1 ->
  asmSem.mem t1' = asmSem.mem t1 -> asmSem.mem_domain t1' = asmSem.mem_domain t1 ->
  asmSem.be t1' = asmSem.be t1 -> asmSem.align t1' = asmSem.align t1 ->
  asmSem.lr t1' = asmSem.lr t1 -> ~ asmSem.failed t1' ->
  state_rel (mc_conf, (code2, (labs, p))) (set_pc x (dec_clock s1)) t1' ms2.
Proof.
  intros R Htr Hpc Er Efp Em Edm Ebe Eal Elr Hf.
  pose proof R as R0. apply state_rel_iff in R0.
  apply (state_rel_inst_step mc_conf code2 labs p s1 _ t1 t1' ms1 ms2 R Htr);
    lst_cbn; try reflexivity; try assumption.
  - exact (sr_s1_failed R0).
  - intros a0 _. rewrite Em. reflexivity.
  - intros r. rewrite Efp. apply (sr_fp_regs R0).
  - intros r. rewrite Er. apply (sr_regs R0).
  - intros a0 Ha. apply (sr_mem R0) in Ha as (_ & _ & Hm). rewrite Em. exact Hm.
Qed.

Lemma asm_fetch_aux_not_Label pc0 (code0 : list (sec a)) k1 k2 l :
  asm_fetch_aux pc0 code0 <> SOME (Label k1 k2 l).
Proof.
  revert pc0. induction code0 as [|k ys IH|k y ys xs IH] using code_ind; intros pc0 E.
  - discriminate.
  - exact (IH pc0 E).
  - rewrite (proj2 (proj2 asm_fetch_aux_def)) in E.
    destruct (is_Label y) eqn:Hy; [exact (IH _ E)|].
    destruct (pc0 =? 0); [injection E as ->; discriminate|exact (IH _ E)].
Qed.

(** The fetched instruction in the target code, with FFI entry points
    disjoint from its bytes (Galette helper). *)
Lemma fetch_line (mc_conf : machine_config a B C) code2 labs p
    (s1 : labSem.state a config Ffi) (t1 : asm_state a) ms1 x :
  state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 ->
  asm_fetch s1 = SOME x ->
  (forall op re a0 bs l, x <> Asm (ShareMem op re a0) bs l) ->
  exists j,
    line_similar x j /\
    line_ok (asmProps.config mc_conf.(target)) labs
      (TAKE (THE (mmio_pcs_min_index mc_conf.(ffi_names))) mc_conf.(ffi_names))
      (pos_val (pc s1) 0 code2) j /\
    bytes_in_memory (asmSem.pc t1) (line_bytes j) (asmSem.mem t1) (asmSem.mem_domain t1) /\
    bytes_in_mem (asmSem.pc t1) (line_bytes j) (asmSem.mem t1) (asmSem.mem_domain t1) (mem_domain s1) /\
    pos_val (pc s1 + 1) 0 code2 = pos_val (pc s1) 0 code2 + LENGTH (line_bytes j) /\
    ffi_entry_pcs_disjoint mc_conf t1 (LENGTH (line_bytes j)).
Proof.
  intros R Hf Hx. pose proof R as R0. apply state_rel_iff in R0.
  set (ffis := TAKE (THE (mmio_pcs_min_index mc_conf.(ffi_names))) mc_conf.(ffi_names)).
  destruct (IMP_bytes_in_memory mc_conf s1.(code) code2 labs ffis s1.(pc) x p
              (asmSem.mem t1) (asmSem.mem_domain t1) (mem_domain s1)
              (conj (sr_code_similar R0) (conj (sr_all_enc_ok R0) (conj Hf (sr_code_bytes R0)))))
    as (j & Hbm & Hok & Hpv & Hsim).
  exists j. split; [exact Hsim|]. split; [exact Hok|].
  rewrite (sr_pc R0). split; [exact (bytes_in_mem_IMP _ _ _ _ _ Hbm)|]. split; [exact Hbm|].
  split; [exact Hpv|].
  assert (Hpv' : pos_val (pc s1 + 1) 0 code2 = LENGTH (line_bytes j) + pos_val (pc s1) 0 code2)
    by lia.
  destruct x as [k1 k2 l|b bytes len|y w bytes len].
  - exfalso. destruct j; cbn in Hsim; try contradiction.
    exact (asm_fetch_aux_not_Label _ _ _ _ _ Hf).
  - apply (IMP_ffi_entry_pcs_disjoint_Asm s1 mc_conf code2 labs ffis b bytes len p).
    split; [exact (sr_code_similar R0)|]. split; [exact (sr_all_enc_ok R0)|].
    split; [exact Hf|]. split; [intros op re a0 E; subst b; exact (Hx _ _ _ _ _ eq_refl)|].
    split; [exact (sr_share_mem_domain_code_rel R0)|]. split; [exact Hbm|].
    split; [exact Hpv'|exact (sr_pc R0)].
  - apply (IMP_ffi_entry_pcs_disjoint_LabAsm s1 mc_conf code2 labs ffis y w bytes len p).
    split; [exact (sr_code_similar R0)|]. split; [exact (sr_all_enc_ok R0)|].
    split; [exact Hf|]. split; [exact (sr_share_mem_domain_code_rel R0)|]. split; [exact Hbm|].
    split; [exact Hpv'|exact (sr_pc R0)].
Qed.

Lemma halt_ne_ccache (mc_conf : machine_config a B C) code2 labs p
    (s1 : labSem.state a config Ffi) (t1 : asm_state a) ms1 :
  state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 -> mc_conf.(halt_pc) <> mc_conf.(ccache_pc).
Proof.
  intros R E. apply state_rel_iff in R.
  rewrite <- (sr_halt_pos R), <- (sr_ccache_pos R) in E.
  apply (f_equal (fun x => (p - x)%w)) in E.
  replace (p - (p - n2w ffi_offset))%w with (n2w ffi_offset : word a) in E by word_ring.
  replace (p - (p - n2w (2 * ffi_offset)))%w with (n2w (2 * ffi_offset) : word a) in E by word_ring.
  apply n2w_11 in E. unfold ffi_offset in E.
  assert (Hd : 64 < dimword a).
  { destruct (sr_good_dimindex R) as [Hg|Hg]; unfold dimword; rewrite Hg; reflexivity. }
  rewrite !N.mod_small in E by lia. discriminate.
Qed.

End Goal.
