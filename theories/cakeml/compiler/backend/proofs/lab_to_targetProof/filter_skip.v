(** * CakeML [lab_to_targetProof]: [filter_skip] and the initial state

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml] (HOL
    lines 10540-11010): facts about [lab_filter.filter_skip] used to
    connect [lab_to_target.compile] (which filters [Skip] instructions)
    with [compile_lab].

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v].
    - [implements_intro_gen]: HOL's boolean variable [b] is a [Prop].
    - [no_install_or_no_share_mem_filter_skip] is proved with
      [asm_fetch_aux_filter_skip] (HOL goes through [all_pc_adjust_pc] and
      [lab_filterProof.asm_fetch_aux_eq]); [all_pc_adjust_pc] is still
      ported.
    - Not ported: the HOL theorems that are commented out in the HOL source
      ([no_share_mem_inst_APPEND_IMP], [no_share_mem_inst_EVERY],
      [compile_lab_ffi_names_SOME], [compile_lab_no_share_mem_ffi_names_SOME]).
    - The [fs_*] lemmas are Galette-only helpers. *)

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
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.semantics.proofs Require Import evaluateProps.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.compiler.backend Require Import labLang lab_filter lab_to_target.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend.semantics Require wordSem backendProps.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem targetProps.
From Galette.cakeml.compiler.backend.semantics Require Import labSem labProps.
From Galette.cakeml.semantics.proofs Require Import semanticsProps.
From Galette.cakeml.compiler.backend.proofs Require lab_filterProof.
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import
  basic bytes inst compile_lemmas rl_syntax rl_invariants rl_nop rl_labels rl_compute rl_remove
  code_props pos_props shmem cc_setup cc_asm cc_jump cc_ffi cc_install cc_share compile_correct
  sem_machine init_defs init_state_rel.
Import wordLang (word_loc, Word, Loc).
Import wordSem (mem_load_byte_aux, mem_store_byte_aux, write_bytearray, mem_load_32,
  mem_store_32, buffer, position, buffer_buffer, space_left).
Import ByteBits.
Open Scope N_scope.

Section FilterSkip.
Context {a : N}.

Lemma fs_EVERY_FILTER {X} (P Q : X -> bool) (l : list X) :
  EVERY P l -> EVERY P (FILTER Q l).
Proof.
  unfold is_true. rewrite !EVERY_Forall, !List.Forall_forall. intros H x Hx.
  apply filter_In in Hx as [Hx _]. exact (H x Hx).
Qed.

Lemma fs_filter_skip_sec n (ys : list (line a)) (xs : list (sec a)) :
  Section_ n (FILTER not_skip ys) :: filter_skip xs = filter_skip (Section_ n ys :: xs).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "make_init_filter_skip" *)
Theorem make_init_filter_skip : forall {B C Ffi} (mc_conf : machine_config a B C) (ffi : ffi_state Ffi)
    t m dm sdm ms (code : list (sec a)) cbpos cbspace (coracle : N -> config * list (sec a)),
  semantics
    (make_init mc_conf ffi t m dm sdm ms (filter_skip code)
       (compile_lab (asmProps.config mc_conf.(target))) cbpos cbspace
       ((fun '(a0, b) => (a0, filter_skip b)) ∘ coracle)) =
  semantics
    (make_init mc_conf ffi t m dm sdm ms code
       (fun c p => compile_lab (asmProps.config mc_conf.(target)) c (filter_skip p)) cbpos cbspace coracle).
Proof.
  intros B C Ffi mc_conf ffi t m dm sdm ms code cbpos cbspace coracle.
  apply lab_filterProof.filter_skip_semantics.
  split; [reflexivity|]. split; [exact (fun H => Bool.diff_false_true H)|].
  split; [|exact (fun H => Bool.diff_false_true H)].
  exists (compile_lab (asmProps.config mc_conf.(target))). split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "find_ffi_names_filter_skip" *)
Theorem find_ffi_names_filter_skip : forall code : list (sec a),
  find_ffi_names (filter_skip code) = find_ffi_names code.
Proof.
  induction code as [|k xs IH|k y ys xs IH] using code_ind; [reflexivity|exact IH|].
  rewrite lab_filterProof.filter_skip_cons'. destruct (not_skip y) eqn:Hs.
  - rewrite (proj2 (proj2 (find_ffi_names_def k y (FILTER not_skip ys) (filter_skip xs)))).
    rewrite (proj2 (proj2 (find_ffi_names_def k y ys xs))). rewrite fs_filter_skip_sec, IH. reflexivity.
  - apply lab_filterProof.not_skip_false in Hs as (x & z & ->).
    rewrite (proj2 (proj2 (find_ffi_names_def k _ ys xs))). rewrite fs_filter_skip_sec. exact IH.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_ok_pre_filter_skip" *)
Theorem all_enc_ok_pre_filter_skip : forall (code : list (sec a)) c,
  all_enc_ok_pre c code -> all_enc_ok_pre c (filter_skip code).
Proof.
  unfold is_true. induction code as [|[k ls] code IH]; intros c H; [reflexivity|].
  cbn [filter_skip EVERY] in *. apply andb_prop in H as [H1 H2].
  apply andb_true_intro. split; [|apply IH, H2]. cbn [sec_ok_pre] in *. apply fs_EVERY_FILTER, H1.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "MAP_Section_num_filter_skip" *)
Theorem MAP_Section_num_filter_skip : forall code : list (sec a),
  MAP Section_num (filter_skip code) = MAP Section_num code.
Proof. induction code as [|[k ls] code IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma fs_extract_labels_FILTER (ls : list (line a)) :
  extract_labels (FILTER not_skip ls) = extract_labels ls.
Proof.
  induction ls as [|l ls IH]; [reflexivity|]. cbn [List.filter].
  destruct (not_skip l) eqn:E.
  - destruct l; cbn [extract_labels]; rewrite IH; reflexivity.
  - apply lab_filterProof.not_skip_false in E as (x & y & ->). exact IH.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "filter_skip_extract_labels" *)
Theorem filter_skip_extract_labels : forall code : list (sec a),
  MAP (extract_labels ∘ Section_lines) (filter_skip code) = MAP (extract_labels ∘ Section_lines) code.
Proof.
  induction code as [|[k ls] code IH]; [reflexivity|]. cbn [filter_skip MAP map].
  rewrite IH. f_equal. cbn. apply fs_extract_labels_FILTER.
Qed.

Lemma fs_BIGUNION_IMAGE_FILTER {X} (f : line a -> X -> Prop) (ls : list (line a)) :
  (forall l, not_skip l = false -> f l = {}) ->
  BIGUNION (IMAGE f (set (FILTER not_skip ls))) = BIGUNION (IMAGE f (set ls)).
Proof.
  intros H. induction ls as [|x ls IH]; [reflexivity|]. cbn [List.filter].
  destruct (not_skip x) eqn:E.
  - rewrite !BIGUNION_IMAGE_cons, IH. reflexivity.
  - rewrite BIGUNION_IMAGE_cons, (H x E), (proj1 UNION_EMPTY). exact IH.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "get_code_labels_filter_skip" *)
Theorem get_code_labels_filter_skip : forall code : list (sec a),
  get_code_labels (filter_skip code) = get_code_labels code.
Proof.
  induction code as [|[n ls] code IH]; [reflexivity|]. cbn [filter_skip].
  rewrite !get_code_labels_cons, IH. unfold sec_get_code_labels.
  rewrite fs_BIGUNION_IMAGE_FILTER; [reflexivity|].
  intros l E. apply lab_filterProof.not_skip_false in E as (x & y & ->). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "get_labels_filter_skip" *)
Theorem get_labels_filter_skip : forall code : list (sec a),
  get_labels (filter_skip code) = get_labels code.
Proof.
  induction code as [|[n ls] code IH]; [reflexivity|]. cbn [filter_skip].
  rewrite !get_labels_cons, IH. unfold sec_get_labels.
  rewrite fs_BIGUNION_IMAGE_FILTER; [reflexivity|].
  intros l E. apply lab_filterProof.not_skip_false in E as (x & y & ->). reflexivity.
Qed.

End FilterSkip.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "implements_intro_gen" *)
Theorem implements_intro_gen : forall (b : Prop) (x : behaviour) (y : behaviour -> Prop),
  (b /\ x <> Fail -> y = x INSERT {}) -> b -> implements' true y (x INSERT {}).
Proof.
  intros b x y H Hb Hf.
  assert (Hx : x <> Fail) by (intros ->; apply Hf; apply IN_INSERT; left; reflexivity).
  rewrite (H (conj Hb Hx)). intros z Hz. exact Hz.
Qed.

Section FilterSkip2.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "find_ffi_names_ALL_DISTINCT" *)
Theorem find_ffi_names_ALL_DISTINCT : forall code : list (sec a),
  ALL_DISTINCT (find_ffi_names code).
Proof.
  induction code as [|k xs IH|k y ys xs IH] using code_ind; [reflexivity|exact IH|].
  rewrite (proj2 (proj2 (find_ffi_names_def k y ys xs))).
  destruct y as [| |[]]; try exact IH.
  rewrite list_add_if_fresh_thm. destruct (MEM _ _) eqn:Em; [exact IH|].
  apply ALL_DISTINCT_iff. apply ALL_DISTINCT_iff in IH. apply NoDup_app; [exact IH| |].
  - constructor; [intros []|constructor].
  - intros z Hz [<-|[]]. apply MEM_In in Hz. rewrite Hz in Em. discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "not_not_skip_IMP_Skip" *)
Theorem not_not_skip_IMP_Skip : forall inst' : line a,
  ~ not_skip inst' -> exists l n, inst' = Asm (Asmi (Inst asm.Skip)) l n.
Proof. intros inst' H. apply lab_filterProof.not_skip_false, Bool.not_true_is_false, H. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "asm_fetch_aux_filter_skip" *)
Theorem asm_fetch_aux_filter_skip : forall (inst' : line a) (code : list (sec a)) p,
  asm_fetch_aux p (filter_skip code) = SOME inst' /\ not_skip inst' ->
  exists p', asm_fetch_aux p' code = SOME inst'.
Proof.
  intros inst'.
  induction code as [|k xs IH|k y ys xs IH] using code_ind; intros p (Hf & Hn).
  - discriminate.
  - destruct (IH p (conj Hf Hn)) as [p' Hp']. exists p'. exact Hp'.
  - rewrite lab_filterProof.filter_skip_cons' in Hf. destruct (not_skip y) eqn:Hs.
    + destruct (is_Label y) eqn:HL.
      * rewrite lab_filterProof.fetch_label in Hf by exact HL. rewrite fs_filter_skip_sec in Hf.
        destruct (IH p (conj Hf Hn)) as [p' Hp']. exists p'.
        rewrite lab_filterProof.fetch_label by exact HL. exact Hp'.
      * rewrite lab_filterProof.fetch_nonlabel in Hf by exact HL.
        destruct (N.eqb_spec p 0) as [->|Hp].
        -- exists 0. rewrite lab_filterProof.fetch_nonlabel by exact HL. exact Hf.
        -- rewrite fs_filter_skip_sec in Hf. destruct (IH _ (conj Hf Hn)) as [p' Hp'].
           exists (p' + 1). rewrite lab_filterProof.fetch_nonlabel by exact HL.
           destruct (N.eqb_spec (p' + 1) 0) as [E|_]; [lia|]. rewrite N.add_sub. exact Hp'.
    + rewrite fs_filter_skip_sec in Hf. destruct (IH _ (conj Hf Hn)) as [p' Hp'].
      apply lab_filterProof.not_skip_false in Hs as (x & z & ->).
      exists (p' + 1). rewrite lab_filterProof.fetch_nonlabel by reflexivity.
      destruct (N.eqb_spec (p' + 1) 0) as [E|_]; [lia|]. rewrite N.add_sub. exact Hp'.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "IMP_asm_fetch_aux_filter_skip" *)
Theorem IMP_asm_fetch_aux_filter_skip : forall p (code : list (sec a)) i,
  asm_fetch_aux p code = SOME i /\ not_skip i ->
  exists p', asm_fetch_aux p' (filter_skip code) = SOME i.
Proof.
  intros p code i. revert p.
  induction code as [|k xs IH|k y ys xs IH] using code_ind; intros p (Hf & Hn).
  - discriminate.
  - destruct (IH p (conj Hf Hn)) as [p' Hp']. exists p'. exact Hp'.
  - rewrite lab_filterProof.filter_skip_cons'. destruct (is_Label y) eqn:HL.
    + rewrite lab_filterProof.fetch_label in Hf by exact HL.
      destruct (IH p (conj Hf Hn)) as [p' Hp']. exists p'.
      rewrite (lab_filterProof.label_not_skip y HL). rewrite lab_filterProof.fetch_label by exact HL.
      rewrite fs_filter_skip_sec. exact Hp'.
    + rewrite lab_filterProof.fetch_nonlabel in Hf by exact HL.
      destruct (p =? 0) eqn:E0.
      * injection Hf as Ey. subst y. rewrite Hn. exists 0.
        rewrite lab_filterProof.fetch_nonlabel by exact HL. reflexivity.
      * destruct (IH _ (conj Hf Hn)) as [p' Hp']. rewrite <- fs_filter_skip_sec in Hp'.
        destruct (not_skip y).
        -- exists (p' + 1). rewrite lab_filterProof.fetch_nonlabel by exact HL.
           destruct (N.eqb_spec (p' + 1) 0) as [E|_]; [lia|]. rewrite N.add_sub. exact Hp'.
        -- exists p'. exact Hp'.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "no_share_mem_filter_skip" *)
Theorem no_share_mem_filter_skip : forall code : list (sec a),
  no_share_mem_inst (filter_skip code) <-> no_share_mem_inst code.
Proof.
  intros code. split.
  - intros H p op re a0 inst len E.
    destruct (IMP_asm_fetch_aux_filter_skip p code _ (conj E eq_refl)) as [p' Hp'].
    exact (H _ _ _ _ _ _ Hp').
  - intros H p op re a0 inst len E.
    destruct (asm_fetch_aux_filter_skip _ code p (conj E eq_refl)) as [p' Hp'].
    exact (H _ _ _ _ _ _ Hp').
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_pc_adjust_pc" *)
Theorem all_pc_adjust_pc : forall (code : list (sec a)) p,
  p < num_pcs (filter_skip code) ->
  exists k, lab_filterProof.adjust_pc k code = p.
Proof.
  induction code as [|k xs IH|k y ys xs IH] using code_ind; intros p Hp.
  - cbn in Hp. lia.
  - destruct (IH p Hp) as [k' Hk']. exists k'. rewrite lab_filterProof.adjust_pc_nil_sec. exact Hk'.
  - rewrite lab_filterProof.filter_skip_cons' in Hp. destruct (is_Label y) eqn:HL.
    + rewrite (lab_filterProof.label_not_skip y HL) in Hp.
      rewrite (proj2 (proj2 (num_pcs_def _ _ _ _))), HL, fs_filter_skip_sec in Hp.
      destruct (IH p Hp) as [k' Hk']. exists k'. rewrite lab_filterProof.adjust_pc_label by exact HL.
      exact Hk'.
    + destruct (not_skip y) eqn:Hs.
      * rewrite (proj2 (proj2 (num_pcs_def _ _ _ _))), HL, fs_filter_skip_sec in Hp.
        destruct (N.eqb_spec p 0) as [->|Hp0].
        -- exists 0. apply lab_filterProof.adjust_pc_0.
        -- destruct (IH (p - 1) ltac:(lia)) as [k' Hk']. exists (k' + 1).
           rewrite lab_filterProof.adjust_pc_nonlabel by (exact HL || lia).
           rewrite N.add_sub, Hk', Hs. lia.
      * rewrite fs_filter_skip_sec in Hp. destruct (IH p Hp) as [k' Hk']. exists (k' + 1).
        rewrite lab_filterProof.adjust_pc_nonlabel by (exact HL || lia).
        rewrite N.add_sub, Hk', Hs. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "no_install_or_no_share_mem_filter_skip" *)
Theorem no_install_or_no_share_mem_filter_skip : forall (code : list (sec a)) ffi_names,
  no_install_or_no_share_mem code ffi_names ->
  no_install_or_no_share_mem (filter_skip code) ffi_names.
Proof.
  intros code ffi_names [[H He]|H].
  - left. split; [apply no_share_mem_filter_skip, H|exact He].
  - right. intros p w bytes l E.
    destruct (asm_fetch_aux_filter_skip _ code p (conj E eq_refl)) as [p' Hp'].
    exact (H _ _ _ _ Hp').
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "asm_fetch_aux_MEM" *)
Theorem asm_fetch_aux_MEM : forall (x : line a) l n,
  MEM x l /\ ~ is_Label x ->
  exists p, asm_fetch_aux p [Section_ n l] = SOME x.
Proof.
  intros x l n. induction l as [|y l IH]; intros (Hm & Hl); [discriminate|].
  cbn [MEM] in Hm. apply orb_prop in Hm as [Hm|Hm].
  - apply bool_decide_spec in Hm. subst y. exists 0.
    rewrite lab_filterProof.fetch_nonlabel by (apply Bool.not_true_is_false, Hl). reflexivity.
  - destruct (IH (conj Hm Hl)) as [p Hp]. destruct (is_Label y) eqn:HL.
    + exists p. rewrite lab_filterProof.fetch_label by exact HL. exact Hp.
    + exists (p + 1). rewrite lab_filterProof.fetch_nonlabel by exact HL.
      destruct (N.eqb_spec (p + 1) 0) as [E|_]; [lia|]. rewrite N.add_sub. exact Hp.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "find_ffi_names_EVERY" *)
Theorem find_ffi_names_EVERY : forall (code : list (sec a)) ls,
  find_ffi_names code = ls -> EVERY (fun x => ⌜exists s, x = ExtCall s⌝) ls.
Proof.
  intros code ls <-. unfold is_true. rewrite EVERY_Forall.
  induction code as [|k xs IH|k y ys xs IH] using code_ind; [constructor|exact IH|].
  rewrite (proj2 (proj2 (find_ffi_names_def k y ys xs))).
  destruct y as [| |[]]; try exact IH.
  rewrite list_add_if_fresh_thm. destruct (MEM _ _); [exact IH|].
  apply Forall_app. split; [exact IH|]. constructor; [|constructor].
  apply bool_decide_spec. eexists; reflexivity.
Qed.

End FilterSkip2.
