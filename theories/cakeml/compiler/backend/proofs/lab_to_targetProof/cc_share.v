(** * CakeML [lab_to_targetProof]: [compile_correct], shared memory

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml]: the case
    [ShareMemOp] of [compile_correct] (HOL lines 7846-7970).

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v]; the case is
      stated with [cc_goal] (see [lab_to_targetProof/cc_setup.v]).
    - The eight memory operations are handled together through
      [get_memop_info] (HOL does a case split on the operation). *)

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
  code_props pos_props shmem cc_setup cc_asm cc_jump cc_ffi cc_install.
Import wordLang (word_loc, Word, Loc).
Import wordSem (mem_load_byte_aux, mem_store_byte_aux, write_bytearray, mem_load_32,
  mem_store_32, buffer, position, buffer_buffer, space_left).
Import ByteBits.
Open Scope N_scope.




Section ShareMem.
Context {a : N} {B C Ffi : Type}.

Lemma state_rel_ffi_step (mc_conf : machine_config a B C) code2 labs p (s1 s1' : labSem.state a config Ffi)
    (t1 t1' : asm_state a) ms1 ms3 :
  state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 ->
  call_FFI_rel (ffi s1) (ffi s1') ->
  target_state_rel mc_conf.(target) t1' ms3 ->
  mem s1' = mem s1 -> mem_domain s1' = mem_domain s1 -> shared_mem_domain s1' = shared_mem_domain s1 ->
  be s1' = be s1 -> code s1' = code s1 -> compile s1' = compile s1 ->
  compile_oracle s1' = compile_oracle s1 -> code_buffer s1' = code_buffer s1 ->
  ptr_reg s1' = ptr_reg s1 -> len_reg s1' = len_reg s1 -> ptr2_reg s1' = ptr2_reg s1 ->
  len2_reg s1' = len2_reg s1 -> link_reg s1' = link_reg s1 -> failed s1' = failed s1 ->
  fp_regs s1' = fp_regs s1 ->
  asmSem.mem t1' = asmSem.mem t1 -> asmSem.mem_domain t1' = asmSem.mem_domain t1 ->
  asmSem.fp_regs t1' = asmSem.fp_regs t1 -> asmSem.be t1' = asmSem.be t1 ->
  asmSem.align t1' = asmSem.align t1 -> asmSem.lr t1' = asmSem.lr t1 ->
  asmSem.failed t1' = asmSem.failed t1 ->
  asmSem.pc t1' = (p + n2w (pos_val (pc s1') 0 code2))%w ->
  (forall r, word_loc_val p labs (regs s1' r) = SOME (asmSem.regs t1' r)) ->
  state_rel (set_ffi_interfer (shift_seq 1 mc_conf.(ffi_interfer)) mc_conf, (code2, (labs, p))) s1' t1' ms3.
Proof.
  intros R Hrel Htsr Em Edm Esdm Ebe Ecode Ecomp Eorc Ecb Ep El Ep2 El2 Elink Ef Efp
    Etm Etdm Etfp Etbe Etal Etlr Etf Epc Hregs.
  pose proof R as R0. apply state_rel_iff in R0.
  pose proof (sr_ffi R0) as Sffi. pose proof (sr_share_mem_state_rel R0) as Sshare.
  pose proof (sr_fp_regs R0) as Sfp.
  apply state_rel_iff.
  destruct R0. constructor; mc_cbn;
    rewrite ?Em, ?Edm, ?Esdm, ?Ebe, ?Ecode, ?Ecomp, ?Eorc, ?Ecb, ?Ep, ?El, ?Ep2, ?El2, ?Elink, ?Ef, ?Efp,
      ?Etm, ?Etdm, ?Etfp, ?Etbe, ?Etal, ?Etlr, ?Etf; try assumption.
  - intros ms2 k index nb t1x bytes bytes2 st new_st i (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    exact (Sffi ms2 (k + 1) index nb t1x bytes bytes2 st new_st i
             (conj H1 (conj H2 (conj H3 (conj (RTC_RTC _ _ _ (RTC_SINGLE _ _ _ Hrel) _ H4)
                (conj H5 (conj H6 (conj H7 H8)))))))).
  - unfold share_mem_state_rel in *. destruct Sshare as [S1 S2]. split; [|exact S2].
    intros ms2 k index nb t1x n_b ad offs re pc' ad' st new_st i (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    exact (S1 ms2 (k + 1) index nb t1x n_b ad offs re pc' ad' st new_st i
             (conj H1 (conj H2 (conj H3 (conj (RTC_RTC _ _ _ (RTC_SINGLE _ _ _ Hrel) _ H4)
                (conj H5 (conj H6 (conj H7 H8)))))))).
Qed.

Lemma share_mem_op_split m r ad (s : labSem.state a config Ffi) :
  share_mem_op m r ad s =
  let '(name, nb) := get_memop_info m in
  match name with
  | MappedRead => share_mem_load r ad s (w2n nb)
  | MappedWrite => share_mem_store r ad s (w2n nb)
  end.
Proof. destruct m; reflexivity. Qed.

Lemma memop_nb m name (nb : word8) :
  get_memop_info m = (name, nb) ->
  n2w (w2n nb) = nb /\ (w2n nb =? 0) = bool_decide (nb = n2w 0).
Proof. destruct m; cbn; intros E; inversion E; subst; split; reflexivity. Qed.

Lemma memop_read_valid {P} (t : asmProps.target a B C) ms md m nb (pc0 : word a) r ad (pc' : P) :
  get_memop_info m = (MappedRead, nb) ->
  bytes_in_memory pc0 (encode (asmProps.config t) (Inst (Mem m r ad))) (get_byte t ms) md ->
  is_valid_mapped_read pc0 nb ad r pc' t ms md.
Proof. destruct m; cbn; intros E; inversion E; subst; intros H; exact H. Qed.

Lemma memop_write_valid {P} (t : asmProps.target a B C) ms md m nb (pc0 : word a) r ad (pc' : P) :
  get_memop_info m = (MappedWrite, nb) ->
  bytes_in_memory pc0 (encode (asmProps.config t) (Inst (Mem m r ad))) (get_byte t ms) md ->
  is_valid_mapped_write pc0 nb ad r pc' t ms md.
Proof. destruct m; cbn; intros E; inversion E; subst; intros H; exact H. Qed.

Lemma word_to_bytes_aux_prefix (w : word a) be : forall m n, n <= m ->
  exists X, word_to_bytes_aux m w be = word_to_bytes_aux n w be ++ X.
Proof.
  intros m. induction m as [|m IH] using N.peano_ind; intros n Hn.
  - assert (n = 0) as -> by lia. exists []. rewrite app_nil_r. reflexivity.
  - destruct (N.eq_dec n (N.succ m)) as [->|Hne]; [exists []; rewrite app_nil_r; reflexivity|].
    destruct (IH n ltac:(lia)) as [X HX]. exists (X ++ [byte.get_byte (n2w m) w be]).
    rewrite (proj2 (word_to_bytes_aux_def m w be)), HX, app_assoc. reflexivity.
Qed.

Lemma LENGTH_word_to_bytes_aux (w : word a) be : forall n, LENGTH (word_to_bytes_aux n w be) = n.
Proof.
  intros n. induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (word_to_bytes_aux_def n w be)), LENGTH_app, IH. cbn. lia.
Qed.

Lemma TAKE_LENGTH_app {X} (l1 l2 : list X) : TAKE (LENGTH l1) (l1 ++ l2) = l1.
Proof.
  induction l1 as [|x l1 IH]; cbn [TAKE LENGTH app].
  - destruct l2; reflexivity.
  - rewrite (proj2 (N.eqb_neq _ _)) by lia. replace (N.succ (LENGTH l1) - 1) with (LENGTH l1) by lia.
    rewrite IH. reflexivity.
Qed.

Lemma memop_store_bytes m nb (w : word a) :
  good_dimindex a -> get_memop_info m = (MappedWrite, nb) ->
  (if w2n nb =? 0 then word_to_bytes w false else TAKE (w2n nb) (word_to_bytes w false)) =
  (if decide (nb = n2w 0) then word_to_bytes w false else word_to_bytes_aux (w2n nb) w false).
Proof.
  intros Hg E.
  assert (Hpre : forall n, n <= 4 -> TAKE n (word_to_bytes w false) = word_to_bytes_aux n w false).
  { intros n Hn. unfold word_to_bytes.
    destruct (word_to_bytes_aux_prefix w false (dimindex a DIV 8) n) as [X ->].
    - destruct Hg as [Hg|Hg]; rewrite Hg; cbn; lia.
    - rewrite <- (LENGTH_word_to_bytes_aux w false n) at 1. apply TAKE_LENGTH_app. }
  destruct m; cbn in E; inversion E; subst; cbn [w2n N.eqb];
    try (rewrite Hpre by (cbn; lia)); reflexivity.
Qed.

Lemma set_pc_same (t : asm_state a) : asmSem.set_pc (asmSem.pc t) t = t.
Proof. destruct t; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "compile_correct" case "ShareMemOp" *)
Lemma cc_ShareMem p (s1 : labSem.state a config Ffi) m r ad bytes len :
  clock s1 <> 0 ->
  asm_fetch s1 = SOME (Asm (ShareMem m r ad) bytes len) ->
  (forall s', clock s' < clock s1 -> @cc_goal a B C Ffi p s') ->
  forall res (mc_conf : machine_config a B C) s2 code2 labs (t1 : asm_state a) ms1,
    oracle_tie mc_conf ms1 s1 ->
    (match share_mem_op m r ad s1 with
     | SOME (FFI_final outcome, s') => (Halt (FFI_outcome outcome), s')
     | SOME (FFI_return _ _, s') =>
         labSem.evaluate (set_io_fp_regs (shift_seq 1 (io_fp_regs s'))
                (set_io_regs (shift_seq 1 (io_regs s')) s'))
     | NONE => (Error, s1)
     end) = (res, s2) ->
    res <> Error ->
    encoder_correct mc_conf.(target) ->
    state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 ->
    exists k (t2 : asm_state a) ms2,
      targetSem.evaluate mc_conf (ffi s1) (clock s1 + k) ms1 = (res, (ms2, ffi s2)).
Proof.
  intros Hc Hf IH res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R.
  pose proof R as R0. apply state_rel_iff in R0.
  set (cfg := asmProps.config mc_conf.(target)) in *.
  set (ffis := TAKE (THE (mmio_pcs_min_index mc_conf.(ffi_names))) mc_conf.(ffi_names)).
  destruct (IMP_bytes_in_memory_ShareMem mc_conf s1 t1 code2 labs ffis p m r ad bytes len
              (conj (asm_fetch_aux_of _ _ Hf) (conj (sr_code_similar R0) (conj (sr_all_enc_ok R0) (sr_code_bytes R0)))))
    as (bytes' & Hfa2 & He & Hbm & Hbm' & Hpv & Hok).
  destruct (sr_mmio R0) as (i & Hi & _).
  pose proof (sr_share_mem_domain_code_rel R0) as (D1 & D2 & D3 & D4).
  destruct (D1 (pc s1) m r ad bytes' (LENGTH bytes') i (conj Hfa2 Hi)) as (index & Hle & Hfind & Hinfo).
  destruct (get_memop_info m) as [name nb] eqn:Hgm.
  destruct Hinfo as [HEL HAL].
  destruct (memop_nb m name nb Hgm) as [Hnb1 Hnb2].
  pose proof (sr_tsr R0) as Htsr. pose proof Htsr as (_ & Hpc1 & Hmem1 & Hregs1 & _).
  rewrite (sr_pc R0) in Hpc1.
  rewrite <- Hpc1 in Hfind.
  pose proof (sr_share_mem_state_rel R0) as [S1 S2].
  assert (Hidx : index < LENGTH mc_conf.(ffi_names)).
  { pose proof (find_index_LESS_LENGTH _ _ _ _ Hfind) as [_ H]. rewrite (sr_ffi_length R0). lia. }
  destruct (S2 index i (conj Hi (conj Hidx Hle))) as [Hnh Hnc].
  pose proof (find_index_EL _ _ _ _ Hfind) as Eidx. rewrite N.sub_0_r in Eidx.
  rewrite Eidx in Hnh, Hnc.
  assert (Hmemp : is_true (MEM (get_pc mc_conf.(target) ms1) mc_conf.(ffi_entry_pcs))).
  { destruct (MEM _ _) eqn:E; [reflexivity|]. exfalso.
    pose proof (proj1 (find_index_NOT_MEM mc_conf.(ffi_entry_pcs) (get_pc mc_conf.(target) ms1) 0)) as X.
    rewrite X in Hfind; [discriminate|rewrite E; discriminate]. }
  destruct ad as [r0 off].
  cbn [asm_ok inst_ok] in Hok. apply Bool.andb_true_iff in Hok as [Hok _].
  apply Bool.andb_true_iff in Hok as [Hokr Hokr0].
  assert (Hgr : forall q, reg_ok q cfg -> get_reg mc_conf.(target) ms1 q = asmSem.regs t1 q)
    by (intros q Hq; exact (reg_ok_tsr mc_conf t1 ms1 q Htsr Hq)).
  assert (Hreg : forall q w0, regs s1 q = Word w0 -> asmSem.regs t1 q = w0).
  { intros q w0 E. pose proof (sr_regs R0 q) as E'. rewrite E in E'. cbn [word_loc_val] in E'.
    injection E' as E'. auto. }
  assert (Hbytes_ms : bytes_in_memory (get_pc mc_conf.(target) ms1)
                        (encode cfg (Inst (Mem m r (Addr r0 off)))) (get_byte mc_conf.(target) ms1)
                        mc_conf.(prog_addresses)).
  { apply enc_with_nop_thm in He as [nn Hb]. rewrite Hb in Hbm. apply bytes_in_memory_APPEND in Hbm as [Hbm _].
    rewrite Hpc1, (sr_prog_addresses R0).
    apply (bytes_in_memory_eq_mem t1 mc_conf ms1). split; [|exact Hbm].
    intros a0 Ha0. apply Hmem1, Ha0. }
  (* one machine step at the FFI entry point *)
  assert (Hstep : forall K, K <> 0 ->
    targetSem.evaluate mc_conf (ffi s1) K ms1 =
    targetSem.evaluate_body (fun mc ffi ms => targetSem.evaluate mc ffi (K - 1) ms) mc_conf (ffi s1) ms1)
    by (intros K HK; rewrite targetSem.evaluate_eqn, (proj2 (N.eqb_neq _ _) HK); reflexivity).
  assert (HnotinD : get_pc mc_conf.(target) ms1 NOTIN mc_conf.(prog_addresses) DIFF set mc_conf.(ffi_entry_pcs))
    by (intros [_ H2]; apply H2, IN_set, MEM_In, Hmemp).
  rewrite share_mem_op_split, Hgm in Hev.
  destruct name.
  - (* MappedRead *)
    unfold share_mem_load, labSem.addr in Hev.
    destruct (regs s1 r0) as [w0|] eqn:Er0; [|injection Hev as <- _; contradiction].
    set (v := (w0 + off)%w) in *.
    assert (Hv : (get_reg mc_conf.(target) ms1 r0 + off)%w = v)
      by (unfold v; rewrite (Hgr _ Hokr0), (Hreg _ _ Er0); reflexivity).
    destruct (if w2n nb =? 0 then _ else _) eqn:Econd; [|injection Hev as <- _; contradiction].
    assert (Hcond : (if decide (nb = n2w 0) then w2n v MOD (dimindex a DIV 8) = 0 else True) /\
                    v IN mc_conf.(shared_addresses)).
    { rewrite (D4 : mc_conf.(shared_addresses) = shared_mem_domain s1). rewrite Hnb2 in Econd.
      destruct (decide (nb = n2w 0)) as [E0|E0].
      - rewrite (proj2 (bool_decide_spec _) E0) in Econd.
        apply Bool.andb_true_iff in Econd as [E1 E2]. apply N.eqb_eq in E1. apply bool_decide_spec in E2.
        split; assumption.
      - rewrite (bool_decide_false _ E0) in Econd. apply bool_decide_spec in Econd.
        split; [exact Logic.I|]. apply D3, Econd. }
    rewrite Hnb1 in Hev.
    destruct (call_FFI (ffi s1) (SharedMem MappedRead) [nb] (word_to_bytes v false)) as [new_ffi new_bytes|outcome] eqn:Ecall.
    + (* FFI_return *)
      set (s1' := set_clock (clock s1 - 1) (set_pc (pc s1 + 1)
                    (set_regs ((r =+ Word (word_of_bytes false (n2w 0) new_bytes)) (regs s1))
                      (set_ffi new_ffi s1)))) in Hev.
      set (s1'' := set_io_fp_regs (shift_seq 1 (io_fp_regs s1')) (set_io_regs (shift_seq 1 (io_regs s1')) s1')) in Hev.
      set (ms3 := mc_conf.(ffi_interfer) 0 (index, (new_bytes, ms1))).
      set (pc' := (p + n2w (pos_val (pc s1) 0 code2 + LENGTH bytes'))%w) in *.
      set (t1'' := asmSem.set_regs
                     (fun n => if decide (n = r) then word_of_bytes false (n2w 0) new_bytes else asmSem.regs t1 n)
                     (asmSem.set_pc pc' t1)).
      assert (Hvalid : is_valid_mapped_read (get_pc mc_conf.(target) ms1) nb (Addr r0 off) r pc'
                         mc_conf.(target) ms1 mc_conf.(prog_addresses))
        by exact (memop_read_valid mc_conf.(target) ms1 _ m nb _ r (Addr r0 off) pc' Hgm Hbytes_ms).
      assert (Htsr3 : target_state_rel mc_conf.(target) t1'' ms3).
      { assert (Htsr0 : target_state_rel mc_conf.(target)
                          (asmSem.set_pc (EL index mc_conf.(ffi_entry_pcs)) t1) ms1)
          by (rewrite Eidx, Hpc1, <- (sr_pc R0), set_pc_same; exact Htsr).
        destruct (S1 ms1 0 index new_bytes t1 nb r0 off r pc' (get_reg mc_conf.(target) ms1 r0 + off)%w
                    (ffi s1) new_ffi i
                    (conj Hi (conj Hle (conj Hidx (conj (RTC_REFL _ _) (conj HAL
                       (conj (sr_prog_addresses R0) (conj eq_refl Htsr0))))))))
          as (op & Eop & X).
        rewrite HEL in Eop. injection Eop as <-.
        apply X. rewrite Hv. split; [exact (proj1 Hcond)|]. split; [exact (proj2 Hcond)|].
        split; [exact Hvalid|]. exact Ecall. }
      destruct (IH s1'' ltac:(unfold s1'', s1'; lst_cbn; lia) res
                  (set_ffi_interfer (shift_seq 1 mc_conf.(ffi_interfer)) mc_conf)
                  s2 code2 labs t1'' ms3) as (k' & t2 & ms' & E).
      { split.
        { apply (oracle_tie_ffi_next mc_conf ms1 s1 index new_bytes ms1 ms3
                   (set_ffi_interfer (shift_seq 1 mc_conf.(ffi_interfer)) mc_conf) new_ffi s1'').
          split; [exact Ho|]. split; [|unfold s1'', s1'; lst_cbn; repeat split].
          apply (next_interference_SharedMem mc_conf ms1 index MappedRead nb r0 off r pc' (ffi s1) new_ffi new_bytes).
          split; [exact HnotinD|]. split; [exact (fun E => Hnh (eq_sym E))|].
          split; [exact (fun E => Hnc (eq_sym E))|]. split; [exact Hfind|].
          split; [exact HEL|]. split; [exact HAL|].
          split; [rewrite Hv; intros E0; destruct (decide (nb = n2w 0)); [exact (proj1 Hcond)|contradiction]|].
          split; [rewrite Hv; exact (proj2 Hcond)|].
          split; [intros _; split; [exact Hvalid|rewrite HEL, Hv; exact Ecall]|]. intros E0; discriminate E0. }
        split; [exact Hev|]. split; [exact Hres|]. split; [exact Henc|].
        apply (state_rel_ffi_step mc_conf code2 labs p s1 s1'' t1 t1'' ms1 ms3 R);
          unfold s1'', s1', t1''; lst_cbn; ast_cbn; try reflexivity; try exact Htsr3.
        - exists (SharedMem MappedRead), [nb], (word_to_bytes v false), new_bytes. exact Ecall.
        - unfold pc'. rewrite Hpv. reflexivity.
        - intros q. rewrite APPLY_UPDATE_THM. destruct (decide (r = q)) as [<-|Hne].
          + destruct (decide (r = r)); [reflexivity|congruence].
          + destruct (decide (q = r)); [congruence|]. apply (sr_regs R0). }
      assert (HK : clock s1 + k' <> 0) by lia.
      exists k', t2, ms'. rewrite (Hstep _ HK). unfold targetSem.evaluate_body.
      destruct (classical_dec _) as [Hin|_]; [exfalso; exact (HnotinD Hin)|].
      destruct (decide (get_pc mc_conf.(target) ms1 = mc_conf.(halt_pc))) as [Eh|_];
        [exfalso; exact (Hnh (eq_sym Eh))|].
      destruct (decide (get_pc mc_conf.(target) ms1 = mc_conf.(ccache_pc))) as [Ecc|_];
        [exfalso; exact (Hnc (eq_sym Ecc))|].
      rewrite Hfind, HEL, HAL. cbv zeta. rewrite Hv.
      destruct (classical_dec _) as [_|Hn]; [|exfalso; apply Hn; split; [exact (proj1 Hcond)|split; [exact (proj2 Hcond)|exact Hvalid]]].
      rewrite Ecall. unfold apply_oracle.
      unfold s1'', s1' in E. lst_cbn. replace (clock s1 + k' - 1) with (clock s1 - 1 + k') by lia. exact E.
    + (* FFI_final *)
      injection Hev as <- <-. exists 0, t1, ms1. rewrite N.add_0_r, (Hstep _ Hc).
      unfold targetSem.evaluate_body.
      destruct (classical_dec _) as [Hin|_]; [exfalso; exact (HnotinD Hin)|].
      destruct (decide (get_pc mc_conf.(target) ms1 = mc_conf.(halt_pc))) as [Eh|_];
        [exfalso; exact (Hnh (eq_sym Eh))|].
      destruct (decide (get_pc mc_conf.(target) ms1 = mc_conf.(ccache_pc))) as [Ecc|_];
        [exfalso; exact (Hnc (eq_sym Ecc))|].
      rewrite Hfind, HEL, HAL. cbv zeta. rewrite Hv.
      destruct (classical_dec _) as [_|Hn].
      2:{ exfalso. apply Hn. split; [exact (proj1 Hcond)|]. split; [exact (proj2 Hcond)|].
          exact (memop_read_valid mc_conf.(target) ms1 _ m nb _ r (Addr r0 off) _ Hgm Hbytes_ms). }
      rewrite Ecall. reflexivity.
  - (* MappedWrite *)
    unfold share_mem_store, labSem.addr in Hev.
    destruct (regs s1 r) as [wr|] eqn:Er; [|injection Hev as <- _; contradiction].
    destruct (regs s1 r0) as [w0|] eqn:Er0; [|injection Hev as <- _; contradiction].
    set (v := (w0 + off)%w) in *.
    assert (Hv : (get_reg mc_conf.(target) ms1 r0 + off)%w = v)
      by (unfold v; rewrite (Hgr _ Hokr0), (Hreg _ _ Er0); reflexivity).
    assert (Hwr : get_reg mc_conf.(target) ms1 r = wr) by (rewrite (Hgr _ Hokr); exact (Hreg _ _ Er)).
    destruct (if w2n nb =? 0 then _ else _) eqn:Econd; [|injection Hev as <- _; contradiction].
    assert (Hcond : (if decide (nb = n2w 0) then w2n v MOD (dimindex a DIV 8) = 0 else True) /\
                    v IN mc_conf.(shared_addresses)).
    { rewrite (D4 : mc_conf.(shared_addresses) = shared_mem_domain s1). rewrite Hnb2 in Econd.
      destruct (decide (nb = n2w 0)) as [E0|E0].
      - rewrite (proj2 (bool_decide_spec _) E0) in Econd.
        apply Bool.andb_true_iff in Econd as [E1 E2]. apply N.eqb_eq in E1. apply bool_decide_spec in E2.
        split; assumption.
      - rewrite (bool_decide_false _ E0) in Econd. apply bool_decide_spec in Econd.
        split; [exact Logic.I|]. apply D3, Econd. }
    rewrite Hnb1, (memop_store_bytes m nb wr (sr_good_dimindex R0) Hgm) in Hev.
    set (wbytes := (if decide (nb = n2w 0) then word_to_bytes wr false
                    else word_to_bytes_aux (w2n nb) wr false) ++ word_to_bytes v false) in Hev.
    assert (Hvalid : forall pc0 : word a, is_valid_mapped_write (get_pc mc_conf.(target) ms1) nb (Addr r0 off) r pc0
                       mc_conf.(target) ms1 mc_conf.(prog_addresses))
      by (intros pc0; exact (memop_write_valid mc_conf.(target) ms1 _ m nb _ r (Addr r0 off) pc0 Hgm Hbytes_ms)).
    destruct (call_FFI (ffi s1) (SharedMem MappedWrite) [nb] wbytes) as [new_ffi new_bytes|outcome] eqn:Ecall.
    + (* FFI_return *)
      set (s1' := inc_pc (dec_clock (set_ffi new_ffi s1))) in Hev.
      set (s1'' := set_io_fp_regs (shift_seq 1 (io_fp_regs s1')) (set_io_regs (shift_seq 1 (io_regs s1')) s1')) in Hev.
      set (ms3 := mc_conf.(ffi_interfer) 0 (index, (new_bytes, ms1))).
      set (pc' := (p + n2w (pos_val (pc s1) 0 code2 + LENGTH bytes'))%w) in *.
      set (t1'' := asmSem.set_pc pc' t1).
      assert (Ecall' : call_FFI (ffi s1) (SharedMem MappedWrite) [nb]
                         ((let w := get_reg mc_conf.(target) ms1 r in
                           if decide (nb = n2w 0) then word_to_bytes w false
                           else word_to_bytes_aux (w2n nb) w false) ++
                          word_to_bytes (get_reg mc_conf.(target) ms1 r0 + off)%w false) =
                       FFI_return new_ffi new_bytes)
        by (cbv zeta; rewrite Hwr, Hv; exact Ecall).
      assert (Htsr3 : target_state_rel mc_conf.(target) t1'' ms3).
      { assert (Htsr0 : target_state_rel mc_conf.(target)
                          (asmSem.set_pc (EL index mc_conf.(ffi_entry_pcs)) t1) ms1)
          by (rewrite Eidx, Hpc1, <- (sr_pc R0), set_pc_same; exact Htsr).
        destruct (S1 ms1 0 index new_bytes t1 nb r0 off r pc' (get_reg mc_conf.(target) ms1 r0 + off)%w
                    (ffi s1) new_ffi i
                    (conj Hi (conj Hle (conj Hidx (conj (RTC_REFL _ _) (conj HAL
                       (conj (sr_prog_addresses R0) (conj eq_refl Htsr0))))))))
          as (op & Eop & X).
        rewrite HEL in Eop. injection Eop as <-.
        apply X. rewrite Hv. split; [exact (proj1 Hcond)|]. split; [exact (proj2 Hcond)|].
        split; [exact (Hvalid pc')|]. rewrite <- Hv. exact Ecall'. }
      destruct (IH s1'' ltac:(unfold s1'', s1'; lst_cbn; lia) res
                  (set_ffi_interfer (shift_seq 1 mc_conf.(ffi_interfer)) mc_conf)
                  s2 code2 labs t1'' ms3) as (k' & t2 & ms' & E).
      { split.
        { apply (oracle_tie_ffi_next mc_conf ms1 s1 index new_bytes ms1 ms3
                   (set_ffi_interfer (shift_seq 1 mc_conf.(ffi_interfer)) mc_conf) new_ffi s1'').
          split; [exact Ho|]. split; [|unfold s1'', s1'; lst_cbn; repeat split].
          apply (next_interference_SharedMem mc_conf ms1 index MappedWrite nb r0 off r pc' (ffi s1) new_ffi new_bytes).
          split; [exact HnotinD|]. split; [exact (fun E => Hnh (eq_sym E))|].
          split; [exact (fun E => Hnc (eq_sym E))|]. split; [exact Hfind|].
          split; [exact HEL|]. split; [exact HAL|].
          split; [rewrite Hv; intros E0; destruct (decide (nb = n2w 0)); [exact (proj1 Hcond)|contradiction]|].
          split; [rewrite Hv; exact (proj2 Hcond)|].
          split; [intros E0; discriminate E0|].
          intros _. split; [exact (Hvalid pc')|rewrite HEL; exact Ecall']. }
        split; [exact Hev|]. split; [exact Hres|]. split; [exact Henc|].
        apply (state_rel_ffi_step mc_conf code2 labs p s1 s1'' t1 t1'' ms1 ms3 R);
          unfold s1'', s1', t1''; lst_cbn; ast_cbn; try reflexivity; try exact Htsr3.
        - exists (SharedMem MappedWrite), [nb], wbytes, new_bytes. exact Ecall.
        - unfold pc'. rewrite Hpv. reflexivity.
        - exact (sr_regs R0). }
      assert (HK : clock s1 + k' <> 0) by lia.
      exists k', t2, ms'. rewrite (Hstep _ HK). unfold targetSem.evaluate_body.
      destruct (classical_dec _) as [Hin|_]; [exfalso; exact (HnotinD Hin)|].
      destruct (decide (get_pc mc_conf.(target) ms1 = mc_conf.(halt_pc))) as [Eh|_];
        [exfalso; exact (Hnh (eq_sym Eh))|].
      destruct (decide (get_pc mc_conf.(target) ms1 = mc_conf.(ccache_pc))) as [Ecc|_];
        [exfalso; exact (Hnc (eq_sym Ecc))|].
      rewrite Hfind, HEL, HAL. cbv zeta. rewrite Hv.
      destruct (classical_dec _) as [_|Hn];
        [|exfalso; apply Hn; split; [exact (proj1 Hcond)|split; [exact (proj2 Hcond)|exact (Hvalid _)]]].
      rewrite Hwr. cbv zeta in Ecall'. rewrite Hwr, Hv in Ecall'. rewrite Ecall'. unfold apply_oracle.
      unfold s1'', s1' in E. lst_cbn. replace (clock s1 + k' - 1) with (clock s1 - 1 + k') by lia. exact E.
    + (* FFI_final *)
      injection Hev as <- <-. exists 0, t1, ms1. rewrite N.add_0_r, (Hstep _ Hc).
      unfold targetSem.evaluate_body.
      destruct (classical_dec _) as [Hin|_]; [exfalso; exact (HnotinD Hin)|].
      destruct (decide (get_pc mc_conf.(target) ms1 = mc_conf.(halt_pc))) as [Eh|_];
        [exfalso; exact (Hnh (eq_sym Eh))|].
      destruct (decide (get_pc mc_conf.(target) ms1 = mc_conf.(ccache_pc))) as [Ecc|_];
        [exfalso; exact (Hnc (eq_sym Ecc))|].
      rewrite Hfind, HEL, HAL. cbv zeta. rewrite Hv.
      destruct (classical_dec _) as [_|Hn].
      2:{ exfalso. apply Hn. split; [exact (proj1 Hcond)|]. split; [exact (proj2 Hcond)|exact (Hvalid _)]. }
      rewrite Hwr. unfold wbytes in Ecall. rewrite Ecall. reflexivity.
Qed.

End ShareMem.
