(** * CakeML [lab_to_targetProof]: [compile_correct], FFI calls

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml]: the case
    [CallFFI] of [compile_correct] (HOL lines 8304-8737).

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v]; the case is
      stated with [cc_goal] (see [lab_to_targetProof/cc_setup.v]). *)

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
  code_props pos_props shmem cc_setup cc_asm cc_jump.
Import wordLang (word_loc, Word, Loc).
Import wordSem (mem_load_byte_aux, mem_store_byte_aux, write_bytearray, mem_load_32,
  mem_store_32, buffer, position, buffer_buffer, space_left).
Import ByteBits.
Open Scope N_scope.


Ltac mc_cbn :=
  cbn [set_ffi_interfer set_next_interfer set_ccache_interfer shift_interfer
       target prog_addresses shared_addresses ffi_entry_pcs ffi_names targetSem.ptr_reg
       targetSem.len_reg targetSem.ptr2_reg targetSem.len2_reg ffi_interfer callee_saved_regs
       next_interfer halt_pc ccache_pc ccache_interfer mmio_info] in *.

Section CallFFI.
Context {a : N} {B C Ffi : Type}.

Lemma state_rel_CallFFI (mc_conf : machine_config a B C) code2 labs p (s1 : labSem.state a config Ffi)
    (t1 : asm_state a) ms1 ms3 l name wp2 wl2 n1 n2 new_pc xb2 new_ffi new_bytes :
  state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 ->
  regs s1 (ptr2_reg s1) = Word wp2 ->
  regs s1 (len2_reg s1) = Word wl2 ->
  regs s1 (link_reg s1) = Loc n1 n2 ->
  loc_to_pc n1 n2 (code s1) = SOME new_pc ->
  read_bytearray wp2 (w2n wl2) (mem_load_byte_aux (mem s1) (mem_domain s1) (be s1)) = SOME xb2 ->
  call_FFI_rel (ffi s1) new_ffi ->
  LENGTH new_bytes = w2n wl2 ->
  let t1'' := asmSem.set_pc (p + n2w (pos_val new_pc 0 code2))%w
                (asmSem.set_mem (asm_write_bytearray wp2 new_bytes (asmSem.mem t1))
                (asmSem.set_fp_regs (fun n => io_fp_regs s1 0 n)
                (asmSem.set_regs (fun a0 => get_reg_value (io_regs s1 0 (ExtCall name) a0)
                                               (asmSem.regs t1 a0) I) t1))) in
  target_state_rel mc_conf.(target) t1'' ms3 ->
  state_rel (set_ffi_interfer (shift_seq 1 mc_conf.(ffi_interfer)) (shift_interfer l mc_conf),
             (code2, (labs, p)))
    (mk_state
       (fun a0 => get_reg_value (io_regs s1 0 (ExtCall name) a0) (regs s1 a0) Word)
       (fun n => io_fp_regs s1 0 n)
       (write_bytearray wp2 new_bytes (mem s1) (mem_domain s1) (be s1))
       (mem_domain s1) (shared_mem_domain s1) new_pc (be s1) new_ffi
       (shift_seq 1 (io_regs s1)) (cc_regs s1) (shift_seq 1 (io_fp_regs s1)) (cc_fp_regs s1) (code s1)
       (compile s1) (compile_oracle s1) (code_buffer s1) (clock s1 - 1) (failed s1)
       (ptr_reg s1) (len_reg s1) (ptr2_reg s1) (len2_reg s1) (link_reg s1))
    t1'' ms3.
Proof.
  intros R Hp2 Hl2 Hlink Hnp Hrb Hrel Hlen t1'' Htsr.
  pose proof R as R0. apply state_rel_iff in R0.
  assert (Hrb' : read_bytearray wp2 (LENGTH new_bytes)
                   (mem_load_byte_aux (mem s1) (mem_domain s1) (be s1)) = SOME xb2)
    by (rewrite Hlen; exact Hrb).
  assert (Hdm : forall a0, byte_align a0 IN mem_domain s1 -> a0 IN mem_domain s1)
    by (intros a0 Ha; exact (proj1 (proj2 (sr_mem R0 a0 Ha)))).
  pose proof (sr_mem R0) as Smem. pose proof (sr_ffi R0) as Sffi.
  pose proof (sr_share_mem_state_rel R0) as Sshare.
  pose proof (sr_regs R0) as Sregs. pose proof (sr_interference_ok R0) as Sint.
  pose proof (sr_code_bytes R0) as Scode. pose proof (sr_cb_bytes R0) as Scb.
  apply state_rel_iff.
  destruct R0. constructor; unfold t1''; lst_cbn; ast_cbn; mc_cbn; try assumption.
  - intros ms2 k index nb t1x bytes bytes2 st new_st i (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    exact (Sffi ms2 (k + 1) index nb t1x bytes bytes2 st new_st i
             (conj H1 (conj H2 (conj H3 (conj (RTC_RTC _ _ _ (RTC_SINGLE _ _ _ Hrel) _ H4)
                (conj H5 (conj H6 (conj H7 H8)))))))).
  - intros i ms. apply Sint.
  - intros r. reflexivity.
  - intros r. destruct (io_regs s1 0 (ExtCall name) r); cbn [get_reg_value word_loc_val];
      [reflexivity|apply Sregs].
  - intros a0 Ha. destruct (Smem a0 Ha) as (H1 & H2 & H3). split; [exact H1|split; [exact H2|]].
    assert (Hbe : be s1 = big_endian (asmProps.config mc_conf.(target))) by congruence.
    rewrite Hbe in H3. rewrite Hbe at 2.
    apply (CallFFI_bytearray_lemma mc_conf s1 t1 p labs a0 wp2 new_bytes xb2).
    split; [exact Ha|]. split; [assumption|]. split; [exact H1|]. split; [exact H2|].
    split; [exact Hbe|]. split; [exact Hrb'|exact H3].
  - exact (bytes_in_mem_asm_write_bytearray s1 t1 wp2 new_bytes xb2 p _ (conj Hdm Hrb') Scode).
  - exact (bytes_in_mem_asm_write_bytearray s1 t1 wp2 new_bytes xb2 _ _ (conj Hdm Hrb') Scb).
  - reflexivity.
  - unfold share_mem_state_rel in *. destruct Sshare as [S1 S2]. split; [|exact S2].
    intros ms2 k index nb t1x n_b ad offs re pc' ad' st new_st i (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    exact (S1 ms2 (k + 1) index nb t1x n_b ad offs re pc' ad' st new_st i
             (conj H1 (conj H2 (conj H3 (conj (RTC_RTC _ _ _ (RTC_SINGLE _ _ _ Hrel) _ H4)
                (conj H5 (conj H6 (conj H7 H8)))))))).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "compile_correct" case "CallFFI" *)
Lemma cc_CallFFI p (s1 : labSem.state a config Ffi) name w bytes n wl wp wl2 wp2 n1 n2 xb xb2 new_pc :
  clock s1 <> 0 ->
  asm_fetch s1 = SOME (LabAsm (CallFFI name) w bytes n) ->
  regs s1 (len_reg s1) = Word wl -> regs s1 (ptr_reg s1) = Word wp ->
  regs s1 (len2_reg s1) = Word wl2 -> regs s1 (ptr2_reg s1) = Word wp2 ->
  regs s1 (link_reg s1) = Loc n1 n2 ->
  read_bytearray wp (w2n wl) (mem_load_byte_aux (mem s1) (mem_domain s1) (be s1)) = SOME xb ->
  read_bytearray wp2 (w2n wl2) (mem_load_byte_aux (mem s1) (mem_domain s1) (be s1)) = SOME xb2 ->
  loc_to_pc n1 n2 (code s1) = SOME new_pc ->
  (forall s', clock s' < clock s1 -> @cc_goal a B C Ffi p s') ->
  forall res (mc_conf : machine_config a B C) s2 code2 labs (t1 : asm_state a) ms1,
    oracle_tie mc_conf ms1 s1 ->
    (match call_FFI (ffi s1) (ExtCall name) xb xb2 with
     | FFI_final outcome => (Halt (FFI_outcome outcome), s1)
     | FFI_return new_ffi new_bytes =>
         let new_io_regs := shift_seq 1 (io_regs s1) in
         let new_io_fp_regs := shift_seq 1 (io_fp_regs s1) in
         let new_m := write_bytearray wp2 new_bytes (mem s1) (mem_domain s1) (be s1) in
         labSem.evaluate (mk_state
                (fun a0 => get_reg_value (io_regs s1 0 (ExtCall name) a0) (regs s1 a0) Word)
                (fun n => io_fp_regs s1 0 n)
                new_m (mem_domain s1) (shared_mem_domain s1) new_pc (be s1) new_ffi
                new_io_regs (cc_regs s1) new_io_fp_regs (cc_fp_regs s1) (code s1)
                (compile s1) (compile_oracle s1) (code_buffer s1) (clock s1 - 1) (failed s1)
                (ptr_reg s1) (len_reg s1) (ptr2_reg s1) (len2_reg s1) (link_reg s1))
     end) = (res, s2) ->
    res <> Error ->
    encoder_correct mc_conf.(target) ->
    state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 ->
    exists k (t2 : asm_state a) ms2,
      targetSem.evaluate mc_conf (ffi s1) (clock s1 + k) ms1 = (res, (ms2, ffi s2)).
Proof.
  intros Hc Hf Hl1 Hp1 Hl2 Hp2 Hlink Hxb Hxb2 Hnp IH res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R.
  pose proof R as R0. apply state_rel_iff in R0.
  set (cfg := asmProps.config mc_conf.(target)) in *.
  set (ffis := TAKE (THE (mmio_pcs_min_index mc_conf.(ffi_names))) mc_conf.(ffi_names)).
  (* registers of the source state in the target state *)
  assert (Hreg : forall r w0, regs s1 r = Word w0 -> asmSem.regs t1 r = w0).
  { intros r w0 E. pose proof (sr_regs R0 r) as E'. rewrite E in E'. cbn [word_loc_val] in E'.
    injection E' as E'. auto. }
  assert (Hlinkv : asmSem.regs t1 (link_reg s1) = (p + n2w (pos_val new_pc 0 code2))%w).
  { pose proof (sr_regs R0 (link_reg s1)) as E. rewrite Hlink in E. cbn [word_loc_val] in E.
    rewrite (sr_loc_to_pc R0 _ _ _ Hnp) in E. injection E as E. auto. }
  (* the jump to the FFI entry point *)
  destruct (IMP_bytes_in_memory_CallFFI mc_conf s1 t1 code2 labs ffis p name w bytes n
              (conj (sr_code_similar R0) (conj (sr_all_enc_ok R0) (conj (sr_code_bytes R0) Hf))))
    as (tt & enc & Htt & Henc' & Hbm & Hok). subst enc.
  destruct (fetch_line mc_conf code2 labs p s1 t1 ms1 _ R Hf) as (j & Hsim & Hjok & _ & _ & _ & Hdis).
  { intros op re a0 bs l E. discriminate E. }
  destruct j as [| | y w2 bytes2 len2]; cbn in Hsim; try contradiction. subst y.
  cbn [line_ok] in Hjok. cbv zeta in Hjok. destruct Hjok as (He2 & _ & _).
  fold ffis in He2. rewrite <- Htt in He2.
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
  pose proof (proj1 (proj2 (proj2 (Hl 0)))) as Htsr.
  pose proof (proj2 (proj2 (proj2 (Hl 0)))) as Hl0.
  (* the FFI index *)
  assert (Hmem : is_true (MEM (ExtCall name) mc_conf.(ffi_names))).
  { destruct (has_io_name_find_index (code s1) name (IMP_has_io_name s1 name w bytes n Hf)) as [y Hy].
    assert (Hm : is_true (MEM (ExtCall name) (find_ffi_names (code s1)))).
    { destruct (MEM (ExtCall name) (find_ffi_names (code s1))) eqn:E; [reflexivity|].
      exfalso. pose proof (proj1 (find_index_NOT_MEM (find_ffi_names (code s1)) (ExtCall name) 0)) as Hn.
      rewrite Hn in Hy; [discriminate|rewrite E; discriminate]. }
    pose proof (sr_ffi_names_subset R0) as Hsub. unfold list_subset, is_true in Hsub.
    rewrite EVERY_Forall, List.Forall_forall in Hsub. apply Hsub.
    apply filter_In. split; [apply MEM_In, Hm|]. apply bool_decide_spec. eauto. }
  destruct (sr_mmio R0) as (i & Hi & Hmm).
  assert (Hlt : get_ffi_index mc_conf.(ffi_names) (ExtCall name) < i)
    by (apply (ffi_name_NOT_Mapped _ i (ExtCall name)); split; [exact Hi|split; [eauto|exact Hmem]]).
  set (idx := get_ffi_index mc_conf.(ffi_names) (ExtCall name)) in *.
  assert (Hidx : get_ffi_index ffis (ExtCall name) = idx).
  { clear -Hmem Hlt Hi. unfold ffis, idx, get_ffi_index in *. rewrite Hi. cbn [THE].
    destruct (find_index_MEM mc_conf.(ffi_names) (ExtCall name) 0 Hmem) as (j & Hj & _ & _).
    rewrite Hj in Hlt |- *. cbn [the] in Hlt |- *.
    rewrite (find_index_TAKE _ _ _ _ Hj Hlt). reflexivity. }
  rewrite Hidx in Htt.
  destruct (sr_ffi_pos R0 (ExtCall name) i (conj Hmem (conj Hi Hlt))) as (_ & Hnotin & Hnh & Hnc & Hfind).
  fold idx in Hnotin, Hnh, Hnc, Hfind.
  assert (Hpc2 : get_pc mc_conf.(target) ms2 = (p - n2w ((3 + idx) * ffi_offset))%w).
  { pose proof Htsr as (_ & E & _). rewrite E. unfold t1'. ast_cbn.
    rewrite (sr_pc R0), Htt, <- word_add_n2w. word_ring. }
  assert (HEL : EL idx mc_conf.(ffi_names) = ExtCall name) by exact (EL_get_ffi_index_MEM _ _ Hmem).
  assert (HAL : ALOOKUP mc_conf.(mmio_info) idx = NONE).
  { specialize (Hmm idx). destruct (decide (i <= idx < LENGTH mc_conf.(ffi_names))) as [[H1 _]|]; [lia|exact Hmm]. }
  assert (Hbytes : forall ad, ad IN mc_conf.(prog_addresses) ->
                   get_byte mc_conf.(target) ms2 ad = asmSem.mem t1 ad).
  { intros ad Had. pose proof Htsr as (_ & _ & E & _). rewrite (sr_prog_addresses R0) in Had.
    unfold t1' in E. ast_cbn. apply E. exact Had. }
  assert (Hgr : forall r, reg_ok r cfg -> get_reg mc_conf.(target) ms2 r = asmSem.regs t1 r).
  { intros r Hr. rewrite (reg_ok_tsr mc_conf t1' ms2 r Htsr Hr). unfold t1'. ast_cbn. reflexivity. }
  assert (Hread : read_ffi_bytearrays mc_conf ms2 = (SOME xb, SOME xb2)).
  { unfold read_ffi_bytearrays, read_ffi_bytearray.
    rewrite (sr_ptr_reg R0), (sr_len_reg R0), (sr_ptr2_reg R0), (sr_len2_reg R0).
    rewrite !Hgr by first [exact (sr_ptr_reg_ok R0)|exact (sr_len_reg_ok R0)|
                            exact (sr_ptr2_reg_ok R0)|exact (sr_len2_reg_ok R0)].
    rewrite (Hreg _ _ Hl1), (Hreg _ _ Hp1), (Hreg _ _ Hl2), (Hreg _ _ Hp2).
    assert (Ef : (fun ad => if classical_dec (ad IN mc_conf.(prog_addresses))
                            then SOME (get_byte mc_conf.(target) ms2 ad) else NONE) =
                 (fun ad => if classical_dec (ad IN mc_conf.(prog_addresses))
                            then SOME (asmSem.mem t1 ad) else NONE)).
    { apply functional_extensionality. intros ad. destruct (classical_dec _) as [Had|]; [|reflexivity].
      rewrite Hbytes by exact Had. reflexivity. }
    rewrite Ef.
    rewrite (read_bytearray_state_rel mc_conf code2 labs p s1 t1 ms1 _ _ _ (conj R Hxb)).
    rewrite (read_bytearray_state_rel mc_conf code2 labs p s1 t1 ms1 _ _ _ (conj R Hxb2)).
    reflexivity. }
  rewrite <- Hpc2 in Hnotin, Hnh, Hnc, Hfind.
  assert (Hstep : forall K, K <> 0 ->
    targetSem.evaluate (shift_interfer l mc_conf) (ffi s1) K ms2 =
    match call_FFI (ffi s1) (ExtCall name) xb xb2 with
    | FFI_final outcome => (Halt (FFI_outcome outcome), (ms2, ffi s1))
    | FFI_return new_ffi new_bytes =>
        targetSem.evaluate (set_ffi_interfer (shift_seq 1 mc_conf.(ffi_interfer)) (shift_interfer l mc_conf))
          new_ffi (K - 1) (mc_conf.(ffi_interfer) 0 (idx, (new_bytes, ms2)))
    end).
  { intros K HK. exact (evaluate_ExtCall_step (shift_interfer l mc_conf) (ffi s1) K ms2 idx name xb xb2
                          HK Hnotin Hnh Hnc Hfind HEL HAL Hread). }
  destruct (call_FFI (ffi s1) (ExtCall name) xb xb2) as [new_ffi new_bytes|outcome] eqn:Ecall.
  - (* FFI_return *)
    cbv zeta in Hev.
    set (t1'' := asmSem.set_pc (p + n2w (pos_val new_pc 0 code2))%w
                (asmSem.set_mem (asm_write_bytearray wp2 new_bytes (asmSem.mem t1))
                (asmSem.set_fp_regs (fun n => io_fp_regs s1 0 n)
                (asmSem.set_regs (fun a0 => get_reg_value (io_regs s1 0 (ExtCall name) a0)
                                               (asmSem.regs t1 a0) I) t1)))).
    set (ms3 := mc_conf.(ffi_interfer) 0 (idx, (new_bytes, ms2))).
    assert (Hfn : forall k, find_next_interference mc_conf (ffi s1) (k + l) ms1 =
                            find_next_interference (shift_interfer l mc_conf) (ffi s1) k ms2)
      by (intros k; exact (proj1 (proj2 (Hl k)))).
    assert (HnotinD : get_pc mc_conf.(target) ms2 NOTIN mc_conf.(prog_addresses) DIFF set mc_conf.(ffi_entry_pcs))
      by (intros [H1 _]; exact (Hnotin H1)).
    destruct (oracle_tie_ExtCall_residues mc_conf ms1 s1 ms2 l idx name xb xb2 new_ffi new_bytes t1
                (conj Ho (conj Hfn (conj HnotinD (conj Hnh (conj Hnc (conj Hfind (conj HEL
                   (conj HAL (conj Hread Ecall)))))))))) as [Eregs Efp].
    assert (Htsr3 : target_state_rel mc_conf.(target) t1'' ms3).
    { assert (Hal : aligned (code_alignment cfg) (asmSem.regs t1 (link_reg s1)) = true).
      { rewrite Hlinkv. exact (state_rel_aligned_pos _ _ _ _ _ _ _ new_pc R Henc). }
      assert (Ht1'eq : asmSem.set_pc (p - n2w ((3 + idx) * ffi_offset))%w t1 = t1').
      { unfold t1'. cbn [asm]. unfold asmSem.jump_to_offset, asmSem.upd_pc. f_equal.
        rewrite (sr_pc R0), Htt, <- word_add_n2w. word_ring. }
      assert (Ecall' : call_FFI (ffi s1) (EL idx mc_conf.(ffi_names)) xb xb2 = FFI_return new_ffi new_bytes)
        by (rewrite HEL; exact Ecall).
      assert (Htsr' : target_state_rel mc_conf.(target)
                        (asmSem.set_pc (p - n2w ((3 + idx) * ffi_offset))%w t1) ms2)
        by (rewrite Ht1'eq; exact Htsr).
      pose proof (sr_ffi R0 ms2 0 idx new_bytes t1 xb xb2 (ffi s1) new_ffi i
                   (conj Hi (conj Hlt (conj Hread (conj (RTC_REFL _ _) (conj Ecall'
                      (conj (sr_prog_addresses R0) (conj Htsr' Hal)))))))) as X.
      cbv zeta in X.
      rewrite <- Eregs, <- Efp, Hlinkv, (Hreg _ _ Hp2) in X. exact X. }
    destruct (IH (mk_state
                (fun a0 => get_reg_value (io_regs s1 0 (ExtCall name) a0) (regs s1 a0) Word)
                (fun n => io_fp_regs s1 0 n)
                (write_bytearray wp2 new_bytes (mem s1) (mem_domain s1) (be s1))
                (mem_domain s1) (shared_mem_domain s1) new_pc (be s1) new_ffi
                (shift_seq 1 (io_regs s1)) (cc_regs s1) (shift_seq 1 (io_fp_regs s1)) (cc_fp_regs s1) (code s1)
                (compile s1) (compile_oracle s1) (code_buffer s1) (clock s1 - 1) (failed s1)
                (ptr_reg s1) (len_reg s1) (ptr2_reg s1) (len2_reg s1) (link_reg s1))
             ltac:(cbn [clock]; lia) res
             (set_ffi_interfer (shift_seq 1 mc_conf.(ffi_interfer)) (shift_interfer l mc_conf))
             s2 code2 labs t1'' ms3) as (k' & t2 & ms' & E).
    { split.
      { apply (oracle_tie_ffi_next (shift_interfer l mc_conf) ms2 s1 idx new_bytes ms2 ms3
                 (set_ffi_interfer (shift_seq 1 mc_conf.(ffi_interfer)) (shift_interfer l mc_conf)) new_ffi).
        split; [exact (oracle_tie_shift_interfer mc_conf ms1 s1 l ms2 (conj Ho Hfn))|].
        split.
        { apply (next_interference_ExtCall (shift_interfer l mc_conf) ms2 idx name xb xb2 (ffi s1) new_ffi new_bytes).
          split; [exact HnotinD|]. split; [exact Hnh|]. split; [exact Hnc|]. split; [exact Hfind|].
          split; [exact HEL|]. split; [exact HAL|]. split; [exact Hread|exact Ecall]. }
        repeat split. }
      split; [exact Hev|]. split; [exact Hres|]. split; [exact Henc|].
      apply (state_rel_CallFFI mc_conf code2 labs p s1 t1 ms1 ms3 l name wp2 wl2 n1 n2 new_pc xb2 new_ffi
               new_bytes R Hp2 Hl2 Hlink Hnp Hxb2).
      - exists (ExtCall name), xb, xb2, new_bytes. exact Ecall.
      - pose proof (call_FFI_LENGTH _ _ _ _ _ _ Ecall) as E1.
        pose proof (read_bytearray_LENGTH _ _ _ _ Hxb2) as E2. lia.
      - exact Htsr3. }
    assert (HK : clock s1 + k' <> 0) by lia.
    exists (k' + l), t2, ms'. rewrite N.add_assoc, (proj1 (Hl (clock s1 + k'))), (Hstep _ HK).
    cbn [clock ffi] in E. replace (clock s1 + k' - 1) with (clock s1 - 1 + k') by lia. exact E.
  - (* FFI_final *)
    injection Hev as <- <-. exists l, t1, ms2.
    rewrite (proj1 (Hl (clock s1))), (Hstep _ Hc). reflexivity.
Qed.

End CallFFI.
