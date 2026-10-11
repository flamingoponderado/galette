(** * CakeML [lab_to_targetProof]: [compile_correct], installing code

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml]: the case
    [Install] of [compile_correct] (HOL lines 8738-9298).

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
  code_props pos_props shmem cc_setup cc_asm cc_jump cc_ffi.
Import wordLang (word_loc, Word, Loc).
Import wordSem (mem_load_byte_aux, mem_store_byte_aux, write_bytearray, mem_load_32,
  mem_store_32, buffer, position, buffer_buffer, space_left).
Import ByteBits.
Open Scope N_scope.



Section Install.
Context {a : N} {B C Ffi : Type}.

Lemma TAKE_LENGTH_ID' {X} (l : list X) : TAKE (LENGTH l) l = l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [TAKE LENGTH]. rewrite (proj2 (N.eqb_neq _ _)) by lia.
  replace (N.succ (LENGTH l) - 1) with (LENGTH l) by lia. rewrite IH. reflexivity. Qed.

Lemma install_fetch_code2 (mc_conf : machine_config a B C) code2 labs p (s1 : labSem.state a config Ffi)
    (t1 : asm_state a) ms1 w bs nn :
  state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 ->
  asm_fetch s1 = SOME (LabAsm Install w bs nn) ->
  exists w' bs' nn', asm_fetch_aux (pc s1) code2 = SOME (LabAsm Install w' bs' nn').
Proof.
  intros R Hf. apply state_rel_iff in R.
  pose proof (code_similar_IMP_asm_fetch_aux_line_similar (pc s1) _ _ (sr_code_similar R)) as Hr.
  rewrite (asm_fetch_aux_of _ _ Hf) in Hr. destruct Hr as [[Hc _]|(x0 & y0 & E1 & E2 & Hsim)]; [discriminate|].
  injection E1 as <-. destruct y0 as [| |x w' bs' nn']; cbn in Hsim; try contradiction. subst x. eauto.
Qed.

Lemma install_no_share_mem (mc_conf : machine_config a B C) code2 labs p (s1 : labSem.state a config Ffi)
    (t1 : asm_state a) ms1 w bs nn :
  state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 ->
  asm_fetch s1 = SOME (LabAsm Install w bs nn) ->
  no_share_mem_inst code2 /\ EVERY (fun x => ⌜exists s, x = ExtCall s⌝) mc_conf.(ffi_names) /\
  mmio_pcs_min_index mc_conf.(ffi_names) = SOME (LENGTH mc_conf.(ffi_names)).
Proof.
  intros R Hf. destruct (install_fetch_code2 _ _ _ _ _ _ _ _ _ _ R Hf) as (w' & bs' & nn' & Hf2).
  apply state_rel_iff in R. pose proof (sr_no_install_or_no_share_mem R) as Hn.
  destruct (sr_mmio R) as (i & Hi & _).
  pose proof (no_share_mem_lemma _ i (pc s1) code2 w' bs' nn' (conj Hi (conj Hf2 Hn))) as Ei.
  destruct Hn as [[H1 H2]|Hn]; [|exfalso; exact (Hn _ _ _ _ Hf2)].
  split; [exact H1|]. split; [exact H2|]. rewrite <- Ei. exact Hi.
Qed.

Lemma state_rel_Install (mc_conf : machine_config a B C) code2 labs p (s1 : labSem.state a config Ffi)
    (t1 : asm_state a) ms1 ms12 l w1 w2 n1 n2 new_pc bytes cb cfg prog0 k lines rest sec_list l1 cfg'
    w bs nn :
  state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 ->
  encoder_correct mc_conf.(target) ->
  asm_fetch s1 = SOME (LabAsm Install w bs nn) ->
  regs s1 (ptr_reg s1) = Word w1 ->
  regs s1 (len_reg s1) = Word w2 ->
  regs s1 (link_reg s1) = Loc n1 n2 ->
  loc_to_pc n1 n2 (code s1) = SOME new_pc ->
  wordSem.buffer_flush (code_buffer s1) w1 w2 = SOME (bytes, cb) ->
  compile_oracle s1 0 = (cfg, prog0) ->
  prog0 = Section_ k lines :: rest ->
  FST (compile_oracle s1 1) = cfg' ->
  remove_labels (init_clock cfg) (asmProps.config mc_conf.(target)) (pos cfg) (labels cfg)
    mc_conf.(ffi_names) prog0 = SOME (sec_list, l1) ->
  bytes = prog_to_bytes sec_list ->
  cfg'.(labels) = l1 ->
  cfg'.(pos) = LENGTH (prog_to_bytes sec_list) + cfg.(pos) ->
  cfg'.(lab_to_target.ffi_names) = SOME mc_conf.(ffi_names) ->
  list_subset (find_ffi_names prog0) mc_conf.(ffi_names) ->
  let t2 := asmSem.set_pc (asmSem.regs t1 (link_reg s1))
              (asmSem.set_fp_regs (fun n => cc_fp_regs s1 0 n)
              (asmSem.set_regs ((ptr_reg s1 =+ asmSem.regs t1 (ptr_reg s1))
                 (fun a0 => get_reg_value (cc_regs s1 0 a0) (asmSem.regs t1 a0) I)) t1)) in
  target_state_rel mc_conf.(target) t2 ms12 ->
  state_rel (set_ccache_interfer (shift_seq 1 mc_conf.(ccache_interfer)) (shift_interfer l mc_conf),
             (code2 ++ sec_list, (l1, p)))
    (mk_state ((ptr_reg s1 =+ Loc k 0) (fun a0 => get_reg_value (cc_regs s1 0 a0) (regs s1 a0) Word))
       (fun n => cc_fp_regs s1 0 n) (mem s1) (mem_domain s1) (shared_mem_domain s1) new_pc (be s1) (ffi s1)
       (io_regs s1) (shift_seq 1 (cc_regs s1)) (io_fp_regs s1) (shift_seq 1 (cc_fp_regs s1))
       (code s1 ++ prog0) (compile s1) (shift_seq 1 (compile_oracle s1)) cb (clock s1 - 1) (failed s1)
       (ptr_reg s1) (len_reg s1) (ptr2_reg s1) (len2_reg s1) (link_reg s1))
    t2 ms12.
Proof.
  intros R Henc Hf Hptr Hlen Hlink Hnp Hbf Horc Hprog Horc1 Hrl Hbytes Hl1 Hpos1 Hffi1 Hsub t2 Htsr.
  pose proof R as R0. apply state_rel_iff in R0.
  set (cfgA := asmProps.config mc_conf.(target)) in *.
  destruct (install_no_share_mem _ _ _ _ _ _ _ _ _ _ R Hf) as (Hns & Hext & Hmmio).
  destruct (install_fetch_code2 _ _ _ _ _ _ _ _ _ _ R Hf) as (wI & bsI & nnI & HfI).
  pose proof (sr_oracle R0 Hns 0) as Ho0. rewrite Horc in Ho0.
  destruct Ho0 as (Hgood & Hns0 & Hk0). destruct (Hk0 eq_refl) as (Elabs & Epos & Effi). clear Hk0.
  pose proof Hgood as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  rewrite Elabs in G5, G6, Hrl. rewrite Epos in Hrl, Hpos1.
  destruct (remove_labels_thm (init_clock cfg) cfgA (LENGTH (prog_to_bytes code2)) labs mc_conf.(ffi_names)
              prog0 sec_list l1) as (Hok2 & Hsim2 & Hodd2 & Hev2 & Hmono & Hloc2).
  { split; [exact Hrl|]. split; [exact (sr_enc_ok R0)|]. split; [exact G1|]. split; [exact G2|].
    split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [exact G7|].
    split; [exact (sr_code_even R0)|].
    intros q1 q2. destruct (lab_lookup q1 q2 labs) as [x|] eqn:E; [|reflexivity].
    exact (sr_labs_even R0 _ _ _ E). }
  (* the code buffer *)
  unfold wordSem.buffer_flush in Hbf.
  destruct (bool_decide _ && bool_decide _) eqn:Ebf; [|discriminate]. injection Hbf as <- <-.
  apply Bool.andb_true_iff in Ebf as [Ew1 Ew2]. apply bool_decide_spec in Ew1, Ew2.
  replace (dimindex 8 DIV 8) with 1 in Ew2 by reflexivity.
  assert (Hw2 : w2 = (p + n2w (LENGTH (prog_to_bytes code2) + LENGTH (prog_to_bytes sec_list)))%w).
  { rewrite <- Ew2, <- Hbytes, (sr_cb_position R0), <- word_add_n2w. word_ring. }
  assert (Hw1 : w1 = (p + n2w (LENGTH (prog_to_bytes code2)))%w) by (rewrite <- Ew1; exact (sr_cb_position R0)).
  apply state_rel_iff.
  pose proof (sr_regs R0) as Sregs. pose proof (sr_mem R0) as Smem. pose proof (sr_ffi R0) as Sffi.
  pose proof (sr_ccache R0) as Sccache. pose proof (sr_oracle R0) as Sorc.
  pose proof (sr_cb_space R0) as Scbs. pose proof (sr_cb_ffi_entry R0) as Sffe.
  pose proof (sr_loc_to_pc R0) as Sloc. pose proof (sr_all_enc_ok R0) as Saeo.
  pose proof (sr_share_mem_state_rel R0) as Sshare. pose proof (sr_share_mem_domain_code_rel R0) as Sdom.
  pose proof (sr_cb_bytes R0) as Scbb. pose proof (sr_code_bytes R0) as Scode.
  pose proof (sr_cb_bound R0) as Scbbd. pose proof (sr_interference_ok R0) as Sint.
  pose proof (sr_ffi_names_subset R0) as Ssub. pose proof (sr_pc R0) as Spc.
  destruct R0. constructor; unfold t2; lst_cbn; ast_cbn; mc_cbn; try assumption.
  all: cbn [wordSem.position wordSem.buffer_buffer wordSem.space_left LENGTH] in *.
  (* facts shared by several conjuncts *)
  all: assert (Hok1 : EVERY sec_labels_ok (code s1))
         by exact (code_similar_sec_labels_ok _ _ (conj sr_sec_labels_ok (code_similar_sym _ _ sr_code_similar))).
  all: assert (HokAll : EVERY sec_labels_ok (code s1 ++ prog0)) by (rewrite EVERY_app, Hok1, G2; reflexivity).
  all: assert (Hz2 : EVERY sec_label_zero sec_list) by exact (all_enc_ok_imp_sec_label_zero _ _ _ _ _ Hok2).
  all: assert (Hns2 : no_share_mem_inst sec_list) by exact (code_similar_IMP_both_no_share_mem _ _ (conj Hsim2 Hns0)).
  all: assert (HnsA : no_share_mem_inst (code2 ++ sec_list)) by exact (no_share_mem_APPEND _ _ (conj Hns Hns2)).
  all: assert (Haeo : all_enc_ok cfgA labs mc_conf.(ffi_names) 0 code2)
         by (rewrite Hmmio in Saeo; cbn [THE] in Saeo; rewrite TAKE_LENGTH_ID' in Saeo; exact Saeo).
  all: assert (HLp : SUM (MAP (SUM ∘ MAP line_length ∘ Section_lines) code2) = LENGTH (prog_to_bytes code2))
         by exact (LENGTH_prog_to_bytes2 code2 0 _ _ _ _ Haeo).
  all: assert (Hlen_nl : SUM (MAP (fun s => len_no_lab (Section_lines s)) (code s1)) =
                         SUM (MAP (fun s => len_no_lab (Section_lines s)) code2))
         by (f_equal; exact (code_similar_len_no_lab _ _ sr_code_similar)).
  all: assert (Hbound1 : forall q1 q2 x, loc_to_pc q1 q2 (code s1) = SOME x ->
                 x <= SUM (MAP (fun s => len_no_lab (Section_lines s)) code2))
         by (intros q1 q2 x Hx; rewrite (code_similar_loc_to_pc q1 q2 _ _ sr_code_similar) in Hx;
             exact (loc_to_pc_bound code2 q1 q2 x (conj sr_sec_labels_ok Hx))).
  all: assert (Hlinkv : asmSem.regs t1 (link_reg s1) = (p + n2w (pos_val new_pc 0 code2))%w)
         by (pose proof (Sregs (link_reg s1)) as E; rewrite Hlink in E; cbn [word_loc_val] in E;
             rewrite (Sloc _ _ _ Hnp) in E; injection E as E; auto).
  all: assert (Hptrv : asmSem.regs t1 (ptr_reg s1) = w1)
         by (pose proof (Sregs (ptr_reg s1)) as E; rewrite Hptr in E; cbn [word_loc_val] in E;
             injection E as E; auto).
  - (* ccache *)
    intros ms2 t1x kk a1 a2 H. exact (Sccache ms2 t1x (kk + 1) a1 a2 H).
  - (* oracle *)
    intros _ kk. unfold shift_seq. pose proof (Sorc Hns (kk + 1)) as X.
    destruct (compile_oracle s1 (kk + 1)) as [cfgk codek] eqn:Ek.
    destruct X as (X1 & X2 & _). split; [exact X1|]. split; [exact X2|]. intros ->.
    cbn [N.add] in Ek. rewrite Ek in Horc1. cbn [FST fst] in Horc1. subst cfgk.
    split; [exact Hl1|]. split; [|exact Hffi1].
    rewrite Hpos1, prog_to_bytes_APPEND, LENGTH_app. lia.
  - (* ffi names *)
    unfold list_subset, is_true in *. rewrite EVERY_Forall, List.Forall_forall in *.
    intros x Hx. apply filter_In in Hx as [Hx Px]. rewrite find_ffi_names_append in Hx.
    apply in_app_iff in Hx as [Hx|Hx].
    + exact (Hsub x Hx).
    + apply filter_In in Hx as [Hx _]. apply Ssub. apply filter_In. split; assumption.
  - (* code even *)
    rewrite prog_to_bytes_APPEND, LENGTH_app. unfold is_true. rewrite N.even_add.
    rewrite sr_code_even.
    rewrite (all_enc_ok_prog_to_bytes_EVEN sec_list 0 cfgA l1 _ _ (conj sr_code_even Hok2)). reflexivity.
  - (* interference *)
    intros i ms. apply Sint.
  - (* loc_to_pc *)
    intros q1 q2 x2 H. rewrite loc_to_pc_append in H by exact HokAll.
    rewrite pos_val_append by exact Hz2.
    destruct (loc_to_pc q1 q2 (code s1)) as [x|] eqn:Ex.
    + injection H as <-. pose proof (Hbound1 _ _ _ Ex) as Hb.
      rewrite (proj2 (N.leb_le _ _) Hb). exact (Hmono _ _ _ (Sloc _ _ _ Ex)).
    + destruct (loc_to_pc q1 q2 prog0) as [y|] eqn:Ey; [|discriminate]. injection H as <-.
      rewrite (Hloc2 _ _ _ Ey), Hlen_nl.
      set (S := SUM (MAP (fun s => len_no_lab (Section_lines s)) code2)).
      destruct (N.leb_spec (y + S) S) as [Hle|Hgt].
      * assert (y = 0) as -> by lia. rewrite N.add_0_l.
        rewrite (pos_val_0 sec_list _ _ _ _ Hok2). unfold S. rewrite pos_val_acc, HLp. reflexivity.
      * replace (y + S - S) with y by lia. rewrite N.add_0_l, HLp. reflexivity.
  - (* fp regs *)
    intros r. reflexivity.
  - (* regs *)
    intros r. rewrite !APPLY_UPDATE_THM. destruct (decide (ptr_reg s1 = r)) as [<-|Hne].
    + cbn [word_loc_val].
      assert (Hl0 : loc_to_pc k 0 prog0 = SOME 0).
      { rewrite loc_to_pc_thm by exact G2. rewrite Hprog, N.eqb_refl.
        destruct lines; reflexivity. }
      rewrite (Hloc2 _ _ _ Hl0), (pos_val_0 sec_list _ _ _ _ Hok2), Hptrv, Hw1. reflexivity.
    + destruct (cc_regs s1 0 r) as [v|]; cbn [get_reg_value]; [reflexivity|].
      exact (word_loc_val_mono p labs l1 _ _ Hmono (Sregs r)).
  - (* mem *)
    intros a0 Ha. destruct (Smem a0 Ha) as (H1 & H2 & H3).
    split; [exact H1|]. split; [exact H2|]. exact (word_loc_val_byte_mono p labs l1 _ _ _ _ Hmono H3).
  - (* cb space *)
    intros n Hn.
    assert (E : (w2 + n2w (0 + n))%w =
                (position (code_buffer s1) + n2w (LENGTH (buffer_buffer (code_buffer s1)) + n))%w)
      by (rewrite <- Ew2, N.add_0_l, <- word_add_n2w; word_ring).
    rewrite E. apply Scbs, Hn.
  - (* code bytes *)
    rewrite prog_to_bytes_APPEND. apply bytes_in_mem_APPEND. split; [exact Scode|].
    rewrite <- Hbytes, <- sr_cb_position. exact Scbb.
  - (* cb position *)
    rewrite Hw2, prog_to_bytes_APPEND, LENGTH_app. reflexivity.
  - (* cb bytes *)
    exact Logic.I.
  - (* cb bound *)
    rewrite prog_to_bytes_APPEND, LENGTH_app, <- Hbytes. lia.
  - (* cb ffi entry *)
    intros bn Hbn.
    assert (E : (w2 + n2w bn)%w =
                (position (code_buffer s1) + n2w (LENGTH (buffer_buffer (code_buffer s1)) + bn))%w)
      by (rewrite <- Ew2, <- word_add_n2w; word_ring).
    rewrite E. apply Sffe. lia.
  - (* pc *)
    rewrite Hlinkv, pos_val_append by exact Hz2.
    rewrite (proj2 (N.leb_le _ _) (Hbound1 _ _ _ Hnp)). reflexivity.
  - (* all_enc_ok *)
    rewrite Hmmio. cbn [THE]. rewrite TAKE_LENGTH_ID'.
    apply all_enc_ok_append. split.
    + apply (all_enc_ok_labs_mono _ labs). split; [exact Hmono|exact Haeo].
    + rewrite N.add_0_l. exact Hok2.
  - (* sec_labels_ok *)
    unfold is_true. rewrite EVERY_app, sr_sec_labels_ok.
    rewrite (code_similar_sec_labels_ok _ _ (conj G2 Hsim2)). reflexivity.
  - (* code_similar *)
    exact (code_similar_append _ _ _ _ (conj sr_code_similar Hsim2)).
  - (* share_mem_domain_code_rel *)
    unfold share_mem_domain_code_rel in *. destruct Sdom as (D1 & D2 & D3 & D4).
    split; [intros pc0 op re a0 inst len i (Hfa & _); exfalso; exact (HnsA _ _ _ _ _ _ Hfa)|].
    split; [|split; [exact D3|exact D4]].
    intros pc0 line (Hfa & Hnot). destruct (N.lt_ge_cases pc0 (num_pcs code2)) as [Hl|Hg].
    + rewrite asm_fetch_aux_APPEND1 in Hfa by exact Hl. rewrite pos_val_APPEND1 by exact Hl.
      exact (D2 pc0 line (conj Hfa Hnot)).
    + replace pc0 with ((pc0 - num_pcs code2) + num_pcs code2) in Hfa |- * by lia.
      set (pc' := pc0 - num_pcs code2) in *.
      rewrite asm_fetch_aux_APPEND2 in Hfa.
      rewrite (pos_val_APPEND2 _ _ _ _ pc' code2 sec_list Haeo).
      pose proof (asm_fetch_aux_pos_val_SUC pc' 0 sec_list _ _ _ _ line (conj Hok2 Hfa)) as Hsuc.
      pose proof (pos_val_bound (pc' + 1) 0 sec_list _ _ _ _ Hok2) as Hpb.
      rewrite IN_DISJOINT. intros (x & Hx1 & (a0 & -> & Ha0)).
      apply (Sffe (a0 + pos_val pc' 0 sec_list)).
      * rewrite Hbytes. lia.
      * rewrite sr_cb_position, <- !word_add_n2w. unfold pred_set.IN in Hx1.
        apply IN_set in Hx1. apply MEM_In.
        replace (p + n2w (LENGTH (prog_to_bytes code2)) + (n2w a0 + n2w (pos_val pc' 0 sec_list)))%w
          with (p + n2w a0 + (n2w (LENGTH (prog_to_bytes code2)) + n2w (pos_val pc' 0 sec_list)))%w
          by word_ring.
        rewrite <- word_add_n2w in Hx1. exact Hx1.
  - (* no_install_or_no_share_mem *)
    left. split; [exact HnsA|exact Hext].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "compile_correct" case "Install" *)
Lemma cc_Install p (s1 : labSem.state a config Ffi) w bs nn w1 w2 n1 n2 bytes cb new_pc cfg prog0
    bytes' cfg' k lines rest :
  clock s1 <> 0 ->
  asm_fetch s1 = SOME (LabAsm Install w bs nn) ->
  regs s1 (ptr_reg s1) = Word w1 -> regs s1 (len_reg s1) = Word w2 ->
  regs s1 (link_reg s1) = Loc n1 n2 ->
  wordSem.buffer_flush (code_buffer s1) w1 w2 = SOME (bytes, cb) ->
  loc_to_pc n1 n2 (code s1) = SOME new_pc ->
  compile_oracle s1 0 = (cfg, prog0) ->
  compile s1 cfg prog0 = SOME (bytes', cfg') ->
  prog0 = Section_ k lines :: rest ->
  bytes = bytes' ->
  FST (compile_oracle s1 1) = cfg' ->
  (forall s', clock s' < clock s1 -> @cc_goal a B C Ffi p s') ->
  forall res (mc_conf : machine_config a B C) s2 code2 labs (t1 : asm_state a) ms1,
    oracle_tie mc_conf ms1 s1 ->
    labSem.evaluate (mk_state ((ptr_reg s1 =+ Loc k 0)
                       (fun a0 => get_reg_value (cc_regs s1 0 a0) (regs s1 a0) Word))
       (fun n => cc_fp_regs s1 0 n) (mem s1) (mem_domain s1) (shared_mem_domain s1) new_pc (be s1) (ffi s1)
       (io_regs s1) (shift_seq 1 (cc_regs s1)) (io_fp_regs s1) (shift_seq 1 (cc_fp_regs s1))
       (code s1 ++ prog0) (compile s1) (shift_seq 1 (compile_oracle s1)) cb (clock s1 - 1) (failed s1)
       (ptr_reg s1) (len_reg s1) (ptr2_reg s1) (len2_reg s1) (link_reg s1)) = (res, s2) ->
    res <> Error ->
    encoder_correct mc_conf.(target) ->
    state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 ->
    exists k (t2 : asm_state a) ms2,
      targetSem.evaluate mc_conf (ffi s1) (clock s1 + k) ms1 = (res, (ms2, ffi s2)).
Proof.
  intros Hc Hf Hptr Hlen Hlink Hbf Hnp Horc Hcomp Hprog Hb Horc1 IH res mc_conf s2 code2 labs t1 ms1
    Ho Hev Hres Henc R.
  pose proof R as R0. apply state_rel_iff in R0.
  set (cfgA := asmProps.config mc_conf.(target)) in *.
  set (ffis := TAKE (THE (mmio_pcs_min_index mc_conf.(ffi_names))) mc_conf.(ffi_names)).
  destruct (install_no_share_mem _ _ _ _ _ _ _ _ _ _ R Hf) as (Hns & Hext & Hmmio).
  (* the compiled code *)
  pose proof (sr_oracle R0 Hns 0) as Ho0. rewrite Horc in Ho0.
  destruct Ho0 as (Hgood & Hns0 & Hk0). destruct (Hk0 eq_refl) as (Elabs & Epos & Effi). clear Hk0.
  rewrite (sr_compile R0) in Hcomp. unfold compile_lab in Hcomp. rewrite Effi in Hcomp.
  cbv zeta in Hcomp.
  destruct (list_subset (find_ffi_names prog0) mc_conf.(ffi_names)) eqn:Hsub; [|discriminate].
  destruct (remove_labels (init_clock cfg) (asmProps.config (target mc_conf)) (pos cfg) (labels cfg)
              mc_conf.(ffi_names) prog0) as [[sec_list l1]|] eqn:Hrl; [|discriminate].
  fold cfgA in Hrl.
  pose proof Hgood as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  assert (Hsim2 : code_similar prog0 sec_list).
  { rewrite Elabs, Epos in Hrl. rewrite Elabs in G5, G6.
    destruct (remove_labels_thm (init_clock cfg) cfgA (LENGTH (prog_to_bytes code2)) labs mc_conf.(ffi_names)
                prog0 sec_list l1) as (_ & Hs & _).
    { split; [exact Hrl|]. split; [exact (sr_enc_ok R0)|]. split; [exact G1|]. split; [exact G2|].
      split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [exact G7|].
      split; [exact (sr_code_even R0)|].
      intros q1 q2. destruct (lab_lookup q1 q2 labs) as [x|] eqn:E; [|reflexivity].
      exact (sr_labs_even R0 _ _ _ E). }
    exact Hs. }
  rewrite (no_share_mem_IMP_get_shmem_info sec_list (pos cfg) [] []
             (code_similar_IMP_both_no_share_mem _ _ (conj Hsim2 Hns0))) in Hcomp.
  injection Hcomp as Hbytes' Hcfg'. subst bytes'.
  assert (Hl1 : cfg'.(labels) = l1) by (rewrite <- Hcfg'; reflexivity).
  assert (Hpos1 : cfg'.(pos) = LENGTH (prog_to_bytes sec_list) + LENGTH (prog_to_bytes code2))
    by (rewrite <- Hcfg', <- Epos; reflexivity).
  assert (Hffi1 : cfg'.(lab_to_target.ffi_names) = SOME mc_conf.(ffi_names))
    by (rewrite <- Hcfg'; cbn; rewrite app_nil_r; reflexivity).
  (* the jump to the clear-cache entry point *)
  destruct (IMP_bytes_in_memory_Install mc_conf s1 t1 code2 labs ffis p w bs nn
              (conj (sr_code_similar R0) (conj (sr_all_enc_ok R0) (conj (sr_code_bytes R0) Hf))))
    as (tt & enc & Htt & Henc' & Hbm & Hok). subst enc.
  destruct (fetch_line mc_conf code2 labs p s1 t1 ms1 _ R Hf) as (j & Hsim & Hjok & _ & _ & _ & Hdis).
  { intros op re a0 bs0 l0 E. discriminate E. }
  destruct j as [| | y w2' bytes2 len2]; cbn in Hsim; try contradiction. subst y.
  cbn [line_ok] in Hjok. cbv zeta in Hjok. destruct Hjok as (He2 & _ & _).
  rewrite <- Htt in He2.
  apply enc_with_nop_thm in He2 as [m Hb2]. cbn [line_bytes] in Hdis. rewrite Hb2 in Hdis.
  set (t1' := asm (asm.Jump tt) (asmSem.pc t1 + n2w (LENGTH (encode cfgA (asm.Jump tt))))%w t1).
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
  fold cfgA t1' in Hl.
  pose proof (proj1 (proj2 (proj2 (Hl 0)))) as Htsr.
  assert (Ht1'eq : asmSem.set_pc (p - n2w (2 * ffi_offset))%w t1 = t1').
  { unfold t1'. cbn [asm]. unfold asmSem.jump_to_offset, asmSem.upd_pc. f_equal.
    rewrite (sr_pc R0), Htt, <- word_add_n2w. word_ring. }
  assert (Hpc2 : get_pc mc_conf.(target) ms2 = mc_conf.(ccache_pc)).
  { pose proof Htsr as (_ & E & _). rewrite E, <- Ht1'eq, <- (sr_ccache_pos R0). reflexivity. }
  assert (Hnotin : get_pc mc_conf.(target) ms2 NOTIN mc_conf.(prog_addresses))
    by (rewrite Hpc2; exact (sr_ccache_pc R0)).
  assert (HnotinD : get_pc mc_conf.(target) ms2 NOTIN mc_conf.(prog_addresses) DIFF set mc_conf.(ffi_entry_pcs))
    by (intros [H1 _]; exact (Hnotin H1)).
  assert (Hnh : get_pc mc_conf.(target) ms2 <> mc_conf.(halt_pc))
    by (rewrite Hpc2; intros E; exact (halt_ne_ccache _ _ _ _ _ _ _ R (eq_sym E))).
  assert (Hgr : forall r, reg_ok r cfgA -> get_reg mc_conf.(target) ms2 r = asmSem.regs t1 r).
  { intros r Hr. rewrite (reg_ok_tsr mc_conf t1' ms2 r Htsr Hr). unfold t1'. ast_cbn. reflexivity. }
  assert (Gp : get_reg mc_conf.(target) ms2 mc_conf.(targetSem.ptr_reg) = asmSem.regs t1 (ptr_reg s1))
    by (rewrite (sr_ptr_reg R0); exact (Hgr _ (sr_ptr_reg_ok R0))).
  assert (Gl : get_reg mc_conf.(target) ms2 mc_conf.(targetSem.len_reg) = asmSem.regs t1 (len_reg s1))
    by (rewrite (sr_len_reg R0); exact (Hgr _ (sr_len_reg_ok R0))).
  assert (Hfn : forall kk, find_next_interference mc_conf (ffi s1) (kk + l) ms1 =
                           find_next_interference (shift_interfer l mc_conf) (ffi s1) kk ms2)
    by (intros kk; exact (proj1 (proj2 (Hl kk)))).
  destruct (oracle_tie_ccache_residues mc_conf (shift_interfer l mc_conf) ms1 s1 ms2 l t1
              (conj Ho (conj Hfn (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl
                 (conj HnotinD (conj Hnh Hpc2))))))))) as [Eregs Efp].
  rewrite Gp, Gl, (sr_ptr_reg R0) in Eregs. rewrite Gp, Gl in Efp.
  set (ms12 := mc_conf.(ccache_interfer) 0 (asmSem.regs t1 (ptr_reg s1), (asmSem.regs t1 (len_reg s1), ms2))) in *.
  set (t2 := asmSem.set_pc (asmSem.regs t1 (link_reg s1))
              (asmSem.set_fp_regs (fun n => cc_fp_regs s1 0 n)
              (asmSem.set_regs ((ptr_reg s1 =+ asmSem.regs t1 (ptr_reg s1))
                 (fun a0 => get_reg_value (cc_regs s1 0 a0) (asmSem.regs t1 a0) I)) t1))).
  assert (Htsr2 : target_state_rel mc_conf.(target) t2 ms12).
  { assert (Hal : aligned (code_alignment cfgA) (asmSem.regs t1 (link_reg s1)) = true).
    { assert (Hlinkv : asmSem.regs t1 (link_reg s1) = (p + n2w (pos_val new_pc 0 code2))%w).
      { pose proof (sr_regs R0 (link_reg s1)) as E. rewrite Hlink in E. cbn [word_loc_val] in E.
        rewrite (sr_loc_to_pc R0 _ _ _ Hnp) in E. injection E as E. auto. }
      rewrite Hlinkv. exact (state_rel_aligned_pos _ _ _ _ _ _ _ new_pc R Henc). }
    assert (Htsr' : target_state_rel mc_conf.(target) (asmSem.set_pc (p - n2w (2 * ffi_offset))%w t1) ms2)
      by (rewrite Ht1'eq; exact Htsr).
    pose proof (sr_ccache R0 ms2 t1 0 (asmSem.regs t1 (ptr_reg s1)) (asmSem.regs t1 (len_reg s1))
                  (conj Htsr' Hal)) as X.
    cbv zeta in X. fold ms12 in X.
    replace t2 with
      (asmSem.set_pc (asmSem.regs t1 (link_reg s1))
       (asmSem.set_fp_regs (fun n => get_fp_reg mc_conf.(target) ms12 n)
       (asmSem.set_regs
          (fun a0 => if MEM a0 mc_conf.(callee_saved_regs) || bool_decide (a0 = ptr_reg s1) ||
                        negb (a0 <? reg_count cfgA) || MEM a0 (avoid_regs cfgA)
                     then asmSem.regs t1 a0
                     else get_reg mc_conf.(target) ms12 a0) t1))); [exact X|].
    unfold t2. f_equal. f_equal. all: try (symmetry; exact Efp). f_equal.
    apply functional_extensionality. intros r. rewrite APPLY_UPDATE_THM.
    destruct (decide (ptr_reg s1 = r)) as [<-|Hne].
    - rewrite (proj2 (bool_decide_spec _) eq_refl), !Bool.orb_true_r. reflexivity.
    - pose proof (f_equal (fun f => f r) Eregs) as E. cbn beta in E. rewrite E. reflexivity. }
  set (mc3 := set_ccache_interfer (shift_seq 1 mc_conf.(ccache_interfer)) (shift_interfer l mc_conf)).
  destruct (IH (mk_state ((ptr_reg s1 =+ Loc k 0)
                       (fun a0 => get_reg_value (cc_regs s1 0 a0) (regs s1 a0) Word))
       (fun n => cc_fp_regs s1 0 n) (mem s1) (mem_domain s1) (shared_mem_domain s1) new_pc (be s1) (ffi s1)
       (io_regs s1) (shift_seq 1 (cc_regs s1)) (io_fp_regs s1) (shift_seq 1 (cc_fp_regs s1))
       (code s1 ++ prog0) (compile s1) (shift_seq 1 (compile_oracle s1)) cb (clock s1 - 1) (failed s1)
       (ptr_reg s1) (len_reg s1) (ptr2_reg s1) (len2_reg s1) (link_reg s1))
             ltac:(cbn [clock]; lia) res mc3 s2 (code2 ++ sec_list) l1 t2 ms12) as (k' & t2' & ms' & E).
  { split.
    { apply (oracle_tie_ccache_next (shift_interfer l mc_conf) ms2 s1
               (asmSem.regs t1 (ptr_reg s1)) (asmSem.regs t1 (len_reg s1)) ms2 ms12 mc3 (ffi s1)).
      split; [exact (oracle_tie_shift_interfer mc_conf ms1 s1 l ms2 (conj Ho Hfn))|].
      split; [|repeat split].
      rewrite (next_interference_ccache (shift_interfer l mc_conf) ms2 (ffi s1) (conj HnotinD (conj Hnh Hpc2))).
      change (target (shift_interfer l mc_conf)) with (target mc_conf).
      change (targetSem.ptr_reg (shift_interfer l mc_conf)) with (targetSem.ptr_reg mc_conf).
      change (targetSem.len_reg (shift_interfer l mc_conf)) with (targetSem.len_reg mc_conf).
      rewrite Gp, Gl. reflexivity. }
    split; [exact Hev|]. split; [exact Hres|]. split; [exact Henc|].
    apply (state_rel_Install mc_conf code2 labs p s1 t1 ms1 ms12 l w1 w2 n1 n2 new_pc bytes cb cfg prog0 k
             lines rest sec_list l1 cfg' w bs nn R Henc Hf Hptr Hlen Hlink Hnp ltac:(exact Hbf) Horc Hprog Horc1
             Hrl ltac:(rewrite Hb; reflexivity) Hl1 ltac:(rewrite <- Hcfg'; reflexivity) Hffi1 Hsub Htsr2). }
  assert (HK : clock s1 + k' <> 0) by lia.
  exists (k' + l), t2', ms'. rewrite N.add_assoc, (proj1 (Hl (clock s1 + k'))).
  rewrite (evaluate_ccache_step (shift_interfer l mc_conf) (ffi s1) _ ms2 HK Hnotin Hnh Hpc2).
  change (targetSem.ptr_reg (shift_interfer l mc_conf)) with (targetSem.ptr_reg mc_conf).
  change (targetSem.len_reg (shift_interfer l mc_conf)) with (targetSem.len_reg mc_conf).
  change (target (shift_interfer l mc_conf)) with (target mc_conf).
  rewrite Gp, Gl. cbn [clock ffi] in E. replace (clock s1 + k' - 1) with (clock s1 - 1 + k') by lia.
  exact E.
Qed.

End Install.
