(** * CakeML [lab_to_targetProof]: shared memory and appended code

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml] (HOL
    lines 6958-7525): FFI entry points, [mmio_pcs_min_index], fetching and
    [pos_val] on appended code, [get_shmem_info], [no_share_mem_inst] and
    [no_install] on appended and similar code, and [oracle_tie] under
    shifted interference oracles.

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v].
    - [oracle_tie_ccache_residues]: HOL's condition (a disjunction of
      propositions) is the [bool] disjunction used by [oracle_tie_ccache_step]
      ([|| bool_decide (a = ptr_reg) ||], [negb (a <? reg_count)]); HOL's
      variable [a] (a register) is renamed [r], [a] being the word size
      here.
    - [no_share_mem_lemma]: HOL's free variables [c], [l], [n] are [c0],
      [l0], [n0].
    - Not ported: the ML tactic [share_mem_eval_expand_tac] and the
      [say] binding. *)

From Galette Require Import Base Classical.
From Stdlib Require Import Setoid.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import alist sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.compiler.backend Require Import labLang lab_to_target lab_filter.
From Galette.cakeml.compiler.backend.semantics Require backendProps.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem targetProps.
From Galette.cakeml.compiler.backend.semantics Require Import labSem labProps.
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import
  basic bytes compile_lemmas rl_syntax rl_invariants rl_nop rl_labels rl_compute code_props pos_props.
Import backendProps (restrict_zero, restrict_nonzero).
Open Scope N_scope.

Section FfiEntry.
Context {a : N} {B C : Type}.

Lemma find_index_EL {X} `{EqDecision X} `{Inhabited X} (x : X) ls n i :
  find_index x ls n = SOME i -> EL (i - n) ls = x.
Proof.
  revert n. induction ls as [|h ls IH]; intros n Hf; cbn in Hf; [discriminate|].
  destruct (decide (h = x)) as [->|Hne].
  - injection Hf as <-. rewrite N.sub_diag. reflexivity.
  - pose proof (find_index_LESS_LENGTH _ _ _ _ Hf) as [Hle _].
    specialize (IH _ Hf). replace (i - n) with (N.succ (i - (n + 1))) by lia.
    rewrite EL_SUC. exact IH.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "ffi_entry_pcs_NOT_ccache_OR_halt_pc" *)
Theorem ffi_entry_pcs_NOT_ccache_OR_halt_pc : forall (mc_conf : machine_config a B C) pc index,
  find_index pc mc_conf.(ffi_entry_pcs) 0 = SOME index /\
  mc_conf.(halt_pc) <> EL index mc_conf.(ffi_entry_pcs) /\
  mc_conf.(ccache_pc) <> EL index mc_conf.(ffi_entry_pcs) ->
  pc <> mc_conf.(ccache_pc) /\
  pc <> mc_conf.(halt_pc).
Proof.
  intros mc_conf pc index (H & H1 & H2). apply find_index_EL in H. rewrite N.sub_0_r in H.
  rewrite H in H1, H2. split; intros ->; auto.
Qed.

End FfiEntry.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "mmio_pcs_min_index_is_SOME" *)
Theorem mmio_pcs_min_index_is_SOME : forall i (ffi_names : list ffiname),
  mmio_pcs_min_index ffi_names = SOME i ->
  i <= LENGTH ffi_names /\
  (forall j, j < i -> exists s, EL j ffi_names = ExtCall s) /\
  (forall j, i <= j /\ j < LENGTH ffi_names -> exists op, EL j ffi_names = SharedMem op).
Proof.
  intros i ffi_names H. unfold mmio_pcs_min_index, some in H.
  destruct (classical_dec _) as [Hex|_]; [|discriminate]. injection H as <-.
  exact (select_spec _ Hex).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "ffi_name_NOT_Mapped" *)
Theorem ffi_name_NOT_Mapped : forall (ffi_names : list ffiname) i s,
  mmio_pcs_min_index ffi_names = SOME i /\ (exists str, s = ExtCall str) /\
  MEM s ffi_names ->
  get_ffi_index ffi_names s < i.
Proof.
  intros ffi_names i s (H & (str & ->) & Hm).
  apply mmio_pcs_min_index_is_SOME in H as (_ & _ & H3).
  pose proof (EL_get_ffi_index_MEM _ _ Hm) as HE.
  destruct (find_index_MEM ffi_names (ExtCall str) 0 Hm) as (j & Hj & Hjl & _).
  unfold get_ffi_index in HE |- *. rewrite Hj in HE |- *. cbn [the] in HE |- *.
  destruct (N.lt_ge_cases (0 + j) i) as [Hl|Hg]; [exact Hl|exfalso].
  assert (Hj' : 0 + j < LENGTH ffi_names) by lia.
  destruct (H3 (0 + j) (conj Hg Hj')) as [op Hop]. rewrite Hop in HE. discriminate.
Qed.

Section Append.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "no_share_mem_lemma" *)
Theorem no_share_mem_lemma : forall (ffi_names : list ffiname) i pc (code : list (sec a)) c0 l0 n0,
  mmio_pcs_min_index ffi_names = SOME i /\
  asm_fetch_aux pc code = SOME (LabAsm Install c0 l0 n0) /\
  no_install_or_no_share_mem code ffi_names ->
  i = LENGTH ffi_names.
Proof.
  intros ffi_names i pc code c0 l0 n0 (H & Hf & Hn).
  apply mmio_pcs_min_index_is_SOME in H as (H1 & _ & H3).
  destruct Hn as [(_ & He)|Hn]; [|exfalso; exact (Hn _ _ _ _ Hf)].
  destruct (N.eq_dec i (LENGTH ffi_names)) as [E|Hne]; [exact E|exfalso].
  assert (Hi : i < LENGTH ffi_names) by lia.
  destruct (H3 i (conj (N.le_refl _) Hi)) as [op Hop].
  unfold is_true in He. rewrite EVERY_Forall, List.Forall_forall in He.
  specialize (He _ (EL_In_lt _ _ Hi)). apply bool_decide_spec in He as [s Hs].
  rewrite Hop in Hs. discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "asm_fetch_aux_APPEND1" *)
Theorem asm_fetch_aux_APPEND1 : forall pc (code sec_list : list (sec a)),
  pc < num_pcs code ->
  asm_fetch_aux pc (code ++ sec_list) = asm_fetch_aux pc code.
Proof.
  intros pc code sec_list. revert pc.
  induction code as [|k ys IH|k y ys xs IH] using code_ind; intros pc H.
  - cbn in H. lia.
  - exact (IH _ H).
  - rewrite (proj2 (proj2 (num_pcs_def k y ys xs))) in H. rewrite <- app_comm_cons.
    rewrite !(proj2 (proj2 asm_fetch_aux_def)).
    destruct (is_Label y); [apply IH, H|]. destruct (N.eqb_spec pc 0); [reflexivity|]. apply IH. lia.
Qed.

Lemma pos_val_APPEND1_gen : forall pc q (code sec_list : list (sec a)),
  pc < num_pcs code ->
  pos_val pc q (code ++ sec_list) = pos_val pc q code.
Proof.
  intros pc q code sec_list. revert pc q.
  induction code as [|k ys IH|k y ys xs IH] using code_ind; intros pc q H.
  - cbn in H. lia.
  - exact (IH _ _ H).
  - rewrite (proj2 (proj2 (num_pcs_def k y ys xs))) in H. rewrite <- app_comm_cons.
    rewrite !(proj2 (proj2 (pos_val_def _ _ _ _ y ys))).
    destruct (is_Label y); [apply IH, H|]. destruct (N.eqb_spec pc 0); [reflexivity|]. apply IH. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pos_val_APPEND1" *)
Theorem pos_val_APPEND1 : forall pc (code sec_list : list (sec a)),
  pc < num_pcs code ->
  pos_val pc 0 (code ++ sec_list) = pos_val pc 0 code.
Proof. intros pc code sec_list. apply pos_val_APPEND1_gen. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "asm_fetch_aux_APPEND2" *)
Theorem asm_fetch_aux_APPEND2 : forall pc (code sec_list : list (sec a)),
  asm_fetch_aux (pc + num_pcs code) (code ++ sec_list) =
  asm_fetch_aux pc sec_list.
Proof.
  intros pc code sec_list. revert pc.
  induction code as [|k ys IH|k y ys xs IH] using code_ind; intros pc.
  - cbn. rewrite N.add_0_r. reflexivity.
  - exact (IH pc).
  - rewrite (proj2 (proj2 (num_pcs_def k y ys xs))). rewrite <- app_comm_cons.
    rewrite (proj2 (proj2 asm_fetch_aux_def)).
    destruct (is_Label y); [apply IH|].
    rewrite (proj2 (N.eqb_neq _ _)) by lia.
    replace (pc + (1 + num_pcs (Section_ k ys :: xs)) - 1) with (pc + num_pcs (Section_ k ys :: xs)) by lia.
    apply IH.
Qed.

Lemma pos_val_APPEND2_gen : forall c labs ffis p pc q (code sec_list : list (sec a)),
  all_enc_ok c labs ffis p code ->
  pos_val (pc + num_pcs code) q (code ++ sec_list) =
  pos_val pc (q + LENGTH (prog_to_bytes code)) sec_list.
Proof.
  intros c labs ffis p pc q code sec_list. revert p q.
  induction code as [|k ys IH|k y ys xs IH] using code_ind; intros p q H.
  - cbn. rewrite !N.add_0_r. reflexivity.
  - destruct H as [_ H]. exact (IH _ q H).
  - destruct H as [Hy H]. rewrite (proj2 (proj2 (num_pcs_def k y ys xs))). rewrite <- app_comm_cons.
    rewrite (proj2 (proj2 (pos_val_def _ _ _ _ y ys))).
    rewrite (proj2 (proj2 (prog_to_bytes_def k y ys xs))), LENGTH_app,
      (line_ok_line_byte_length _ _ _ _ _ Hy).
    destruct (is_Label y).
    + rewrite (IH _ _ H). f_equal. lia.
    + rewrite (proj2 (N.eqb_neq _ _)) by lia.
      replace (pc + (1 + num_pcs (Section_ k ys :: xs)) - 1) with (pc + num_pcs (Section_ k ys :: xs)) by lia.
      rewrite (IH _ _ H). f_equal. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pos_val_APPEND2" *)
Theorem pos_val_APPEND2 : forall c labs ffis p pc (code sec_list : list (sec a)),
  all_enc_ok c labs ffis p code ->
  pos_val (pc + num_pcs code) 0 (code ++ sec_list) =
  LENGTH (prog_to_bytes code) + pos_val pc 0 sec_list.
Proof.
  intros c labs ffis p pc code sec_list H. rewrite (pos_val_APPEND2_gen _ _ _ _ _ _ _ _ H).
  rewrite pos_val_acc_0. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "get_shmem_info_MappedRead_or_MappedWrite" *)
Theorem get_shmem_info_MappedRead_or_MappedWrite : forall (sec : list (sec a)) pos ffi_names info
    new_ffi_names new_info,
  get_shmem_info sec pos ffi_names info = (new_ffi_names, new_info) ->
  exists l, new_ffi_names = ffi_names ++ l /\
    EVERY (fun x => ⌜exists op, x = SharedMem op⌝) l.
Proof.
  intros sec. induction sec as [|k ys IH|k y ys xs IH] using code_ind;
    intros pos ffi_names info new_ffi_names new_info H.
  - injection H as <- _. exists []. rewrite app_nil_r. split; reflexivity.
  - exact (IH _ _ _ _ _ H).
  - destruct y as [n1 n2 n3|[i|r1 r2|m r ad] bytes l|x1 x2 bytes l].
    + change (get_shmem_info (Section_ k (Label n1 n2 n3 :: ys) :: xs) pos ffi_names info)
        with (get_shmem_info (Section_ k ys :: xs) pos ffi_names info) in H.
      exact (IH _ _ _ _ _ H).
    + change (get_shmem_info (Section_ k (Asm (Asmi i) bytes l :: ys) :: xs) pos ffi_names info)
        with (get_shmem_info (Section_ k ys :: xs) (pos + LENGTH bytes) ffi_names info) in H.
      exact (IH _ _ _ _ _ H).
    + change (get_shmem_info (Section_ k (Asm (Cbw r1 r2) bytes l :: ys) :: xs) pos ffi_names info)
        with (get_shmem_info (Section_ k ys :: xs) (pos + LENGTH bytes) ffi_names info) in H.
      exact (IH _ _ _ _ _ H).
    + change (get_shmem_info (Section_ k (Asm (ShareMem m r ad) bytes l :: ys) :: xs) pos ffi_names info)
        with (let '(name, nb) := get_memop_info m in
              get_shmem_info (Section_ k ys :: xs) (pos + LENGTH bytes)
                (ffi_names ++ [SharedMem name])
                (info ++
                 [{| entry_pc := pos;
                     nbytes := nb;
                     addr_reg := match ad with Addr r off => r end;
                     addr_off := match ad with Addr r off => w2n off end;
                     reg := r;
                     exit_pc := pos + LENGTH bytes |}])) in H.
      destruct (get_memop_info m) as [name nb]. destruct (IH _ _ _ _ _ H) as (l' & -> & Hl').
      exists (SharedMem name :: l'). rewrite <- app_assoc. split; [reflexivity|].
      cbn [EVERY]. rewrite Hl', Bool.andb_true_r. apply bool_decide_spec. eauto.
    + change (get_shmem_info (Section_ k (LabAsm x1 x2 bytes l :: ys) :: xs) pos ffi_names info)
        with (get_shmem_info (Section_ k ys :: xs) (pos + LENGTH bytes) ffi_names info) in H.
      exact (IH _ _ _ _ _ H).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "no_share_mem_APPEND" *)
Theorem no_share_mem_APPEND : forall (code secs : list (sec a)),
  no_share_mem_inst code /\
  no_share_mem_inst secs ->
  no_share_mem_inst (code ++ secs).
Proof.
  intros code secs (H1 & H2) p op re a0 inst len E.
  destruct (N.lt_ge_cases p (num_pcs code)) as [Hl|Hg].
  - rewrite asm_fetch_aux_APPEND1 in E by exact Hl. exact (H1 _ _ _ _ _ _ E).
  - replace p with ((p - num_pcs code) + num_pcs code) in E by lia.
    rewrite asm_fetch_aux_APPEND2 in E. exact (H2 _ _ _ _ _ _ E).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "no_install_APPEND_IMP" *)
Theorem no_install_APPEND_IMP : forall (code secs : list (sec a)),
  no_install (code ++ secs) ->
  no_install code /\ no_install secs.
Proof.
  intros code secs H. split.
  - intros p w bytes l E. pose proof (asm_fetch_SOME_IMP_LESS_num_pcs _ _ _ E) as Hl.
    apply (H p w bytes l). rewrite asm_fetch_aux_APPEND1 by exact Hl. exact E.
  - intros p w bytes l E. apply (H (p + num_pcs code) w bytes l).
    rewrite asm_fetch_aux_APPEND2. exact E.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_IMP_both_no_share_mem" *)
Theorem code_similar_IMP_both_no_share_mem : forall (code sec_list : list (sec a)),
  code_similar code sec_list /\
  no_share_mem_inst code ->
  no_share_mem_inst sec_list.
Proof.
  intros code sec_list (Hs & H) p op re a0 inst len E.
  pose proof (code_similar_IMP_asm_fetch_aux_line_similar p _ _ Hs) as Hr. rewrite E in Hr.
  destruct Hr as [[_ Hc]|(x0 & y0 & E1 & E2 & Hsim)]; [discriminate|].
  injection E2 as <-. destruct x0 as [| b bytes l |]; cbn in Hsim; try contradiction. subst b.
  exact (H _ _ _ _ _ _ E1).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_IMP_both_no_install_or_no_share_mem" *)
Theorem code_similar_IMP_both_no_install_or_no_share_mem : forall (code sec_list : list (sec a)) ffi_names,
  code_similar code sec_list /\
  no_install_or_no_share_mem code ffi_names ->
  no_install_or_no_share_mem sec_list ffi_names.
Proof.
  intros code sec_list ffi_names (Hs & [(H & He)|H]).
  - left. split; [|exact He]. exact (code_similar_IMP_both_no_share_mem _ _ (conj Hs H)).
  - right. intros p w bytes l E.
    pose proof (code_similar_IMP_asm_fetch_aux_line_similar p _ _ Hs) as Hr. rewrite E in Hr.
    destruct Hr as [[_ Hc]|(x0 & y0 & E1 & E2 & Hsim)]; [discriminate|].
    injection E2 as <-. destruct x0 as [| | x w' bytes' l']; cbn in Hsim; try contradiction. subst x.
    exact (H _ _ _ _ E1).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "no_share_mem_IMP_get_shmem_info" *)
Theorem no_share_mem_IMP_get_shmem_info : forall (code : list (sec a)) p ffi_names shmem_info,
  no_share_mem_inst code ->
  get_shmem_info code p ffi_names shmem_info = (ffi_names, shmem_info).
Proof.
  intros code. induction code as [|k ys IH|k y ys xs IH] using code_ind; intros p ffi_names shmem_info H.
  - reflexivity.
  - apply IH. intros q op re a0 inst len E. apply (H q op re a0 inst len). exact E.
  - assert (Ht : no_share_mem_inst (Section_ k ys :: xs)).
    { intros q op re a0 inst len E. destruct (is_Label y) eqn:Hl.
      - apply (H q op re a0 inst len). rewrite (proj2 (proj2 asm_fetch_aux_def)), Hl. exact E.
      - apply (H (q + 1) op re a0 inst len). rewrite (proj2 (proj2 asm_fetch_aux_def)), Hl.
        rewrite (proj2 (N.eqb_neq _ _)) by lia. rewrite N.add_sub. exact E. }
    destruct y as [n1 n2 n3|[i|r1 r2|m r ad] bytes l|x1 x2 bytes l].
    + exact (IH _ _ _ Ht).
    + exact (IH _ _ _ Ht).
    + exact (IH _ _ _ Ht).
    + exfalso. apply (H 0 m r ad bytes l). reflexivity.
    + exact (IH _ _ _ Ht).
Qed.

End Append.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "Sh_not_Ext" *)
Theorem Sh_not_Ext : forall x,
  (exists s, x = SharedMem s) <-> (forall s, x <> ExtCall s).
Proof.
  intros [s|s]; split.
  - intros [s' E]; discriminate.
  - intros H. exfalso. exact (H s eq_refl).
  - intros _ s' E; discriminate.
  - intros _. eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "not_Sh_Ext" *)
Theorem not_Sh_Ext : forall x,
  (forall s, x <> SharedMem s) <-> (exists s, x = ExtCall s).
Proof.
  intros [s|s]; split.
  - intros _. eauto.
  - intros _ s' E; discriminate.
  - intros H. exfalso. exact (H s eq_refl).
  - intros [s' E]; discriminate.
Qed.

Section OracleShift.
Context {a : N} {B C Ffi : Type} {c : Type}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "oracle_tie_shift_gen" *)
Theorem oracle_tie_shift_gen : forall (mc_conf mc2 : machine_config a B C) ms1
    (s1 : labSem.state a c Ffi) ms2 l,
  oracle_tie mc_conf ms1 s1 /\
  (forall k, find_next_interference mc_conf s1.(ffi) (k + l) ms1 =
             find_next_interference mc2 s1.(ffi) k ms2) /\
  mc2.(target) = mc_conf.(target) /\
  mc2.(callee_saved_regs) = mc_conf.(callee_saved_regs) /\
  mc2.(targetSem.ptr_reg) = mc_conf.(targetSem.ptr_reg) ->
  oracle_tie mc2 ms2 s1.
Proof.
  intros mc_conf mc2 ms1 s1 ms2 l (Ht & H & E1 & E2 & E3).
  pose proof (next_interference_shift _ _ _ _ _ _ _ H) as E.
  destruct (constructed_oracles_EQ _ _ _ _ _ _ (conj E (conj (eq_sym E1) (conj (eq_sym E2) (eq_sym E3)))))
    as (F1 & F2 & F3 & F4).
  destruct Ht as (H1 & H2 & H3 & H4). unfold oracle_tie.
  rewrite H1, H2, H3, H4, F1, F2, F3, F4. repeat split.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "oracle_tie_ccache_residues" *)
Theorem oracle_tie_ccache_residues : forall (mc_conf mc2 : machine_config a B C) ms1
    (s1 : labSem.state a c Ffi) ms2 l (t1 : asm_state a),
  oracle_tie mc_conf ms1 s1 /\
  (forall k, find_next_interference mc_conf s1.(ffi) (k + l) ms1 =
             find_next_interference mc2 s1.(ffi) k ms2) /\
  mc2.(target) = mc_conf.(target) /\
  mc2.(targetSem.ptr_reg) = mc_conf.(targetSem.ptr_reg) /\
  mc2.(targetSem.len_reg) = mc_conf.(targetSem.len_reg) /\
  mc2.(ccache_interfer) = mc_conf.(ccache_interfer) /\
  get_pc mc2.(target) ms2 NOTIN mc2.(prog_addresses) DIFF set mc2.(ffi_entry_pcs) /\
  get_pc mc2.(target) ms2 <> mc2.(halt_pc) /\
  get_pc mc2.(target) ms2 = mc2.(ccache_pc) ->
  (fun r => get_reg_value (s1.(cc_regs) 0 r) (t1.(asmSem.regs) r) I) =
    (fun r => if MEM r mc_conf.(callee_saved_regs) || bool_decide (r = mc_conf.(targetSem.ptr_reg)) ||
                 negb (r <? reg_count (asmProps.config mc_conf.(target))) ||
                 MEM r (avoid_regs (asmProps.config mc_conf.(target)))
              then t1.(asmSem.regs) r
              else get_reg mc_conf.(target)
                     (mc_conf.(ccache_interfer) 0
                        (get_reg mc_conf.(target) ms2 mc_conf.(targetSem.ptr_reg),
                         (get_reg mc_conf.(target) ms2 mc_conf.(targetSem.len_reg), ms2))) r) /\
  (fun n => s1.(cc_fp_regs) 0 n) =
    (fun n => get_fp_reg mc_conf.(target)
                (mc_conf.(ccache_interfer) 0
                   (get_reg mc_conf.(target) ms2 mc_conf.(targetSem.ptr_reg),
                    (get_reg mc_conf.(target) ms2 mc_conf.(targetSem.len_reg), ms2))) n).
Proof.
  intros mc_conf mc2 ms1 s1 ms2 l t1 (Ht & H & E1 & E2 & E3 & E4 & H1 & H2 & H3).
  pose proof (next_interference_shift _ _ _ _ _ _ _ H) as E.
  rewrite (next_interference_ccache mc2 ms2 s1.(ffi) (conj H1 (conj H2 H3))) in E.
  rewrite E1, E2, E3, E4 in E.
  destruct (oracle_tie_ccache_step mc_conf ms1 s1 _ _ _ _ _ _ (conj Ht E)) as (Hr & Hf & _).
  split.
  - apply functional_extensionality. intros r. rewrite Hr.
    destruct (_ || _); reflexivity.
  - apply functional_extensionality. intros n. apply Hf.
Qed.

End OracleShift.
