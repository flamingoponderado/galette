(** * CakeML [lab_to_targetProof]: correctness of [remove_labels]

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml] (HOL
    lines 5922-6268): the main loop invariant [remove_labels_loop_thm],
    [remove_labels_thm] and the label domain of the assembled code.

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v].
    - HOL's [ALL_DISTINCT o extract_labels o Section_lines] is written with
      [∘].
    - [remove_labels_loop_domain_labs]: HOL's bound variable [a] (the
      clock) is renamed [a0], [a] being the word size here.
    - HOL's [local] theorems are ported as ordinary theorems. *)

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
  basic bytes rl_syntax rl_invariants rl_nop rl_labels rl_compute.
Import backendProps (restrict_zero, restrict_nonzero).
Open Scope N_scope.

Open Scope N_scope.

(** Split syntactic conjunctions only (not [enc_ok]). *)
Ltac splits := repeat match goal with |- _ /\ _ => split end.

Section RemoveLabels.
Context {a : N}.

Lemma EVERY_ALL_DISTINCT_extract_labels (l : list (sec a)) :
  EVERY (ALL_DISTINCT ∘ extract_labels ∘ Section_lines) l =
  EVERY ALL_DISTINCT (MAP (extract_labels ∘ Section_lines) l).
Proof. induction l as [|s l IH]; [reflexivity|]. cbn [EVERY MAP map]. rewrite IH. reflexivity. Qed.

(** The hypotheses and conclusions of [remove_labels_loop_thm] (Galette
    helpers). *)
Definition rl_pre (c : asm_config a) init_pos init_labs (code : list (sec a)) : Prop :=
  EVERY sec_ends_with_label code /\
  EVERY sec_labels_ok code /\
  ALL_DISTINCT (MAP Section_num code) /\
  EVERY (ALL_DISTINCT ∘ extract_labels ∘ Section_lines) code /\
  DISJOINT (domain init_labs) (set (MAP Section_num code)) /\
  restrict_nonzero (get_labels code) SUBSET get_code_labels code UNION labs_domain init_labs /\
  all_enc_ok_pre c code /\
  all_encd0 (encode c) code /\
  enc_ok c /\
  EVEN init_pos /\
  (forall l1 l2, OPTION_ALL EVEN (lab_lookup l1 l2 init_labs)).

Definition rl_post (c : asm_config a) init_pos init_labs ffis (code code2 : list (sec a)) labs : Prop :=
  all_enc_ok_pre c code2 /\
  EVERY sec_labels_ok code2 /\
  all_enc_ok c labs ffis init_pos code2 /\
  code_similar code code2 /\
  (has_odd_inst code2 -> code_alignment c = 0) /\
  (forall l1 l2 x, lab_lookup l1 l2 labs = SOME x -> EVEN x) /\
  (forall l1 l2 x, lab_lookup l1 l2 init_labs = SOME x ->
                   lab_lookup l1 l2 labs = SOME x) /\
  (forall l1 l2 x2,
     loc_to_pc l1 l2 code = SOME x2 ->
     lab_lookup l1 l2 labs = SOME (pos_val x2 init_pos code2)).

Lemma rl_pre_similar c init_pos init_labs (code code1 : list (sec a)) :
  code_similar code code1 -> all_encd0 (encode c) code1 ->
  EVERY sec_ends_with_label code ->
  EVERY sec_labels_ok code ->
  ALL_DISTINCT (MAP Section_num code) ->
  EVERY (ALL_DISTINCT ∘ extract_labels ∘ Section_lines) code ->
  DISJOINT (domain init_labs) (set (MAP Section_num code)) ->
  restrict_nonzero (get_labels code) SUBSET get_code_labels code UNION labs_domain init_labs ->
  all_enc_ok_pre c code ->
  enc_ok c ->
  EVEN init_pos ->
  (forall l1 l2, OPTION_ALL EVEN (lab_lookup l1 l2 init_labs)) ->
  rl_pre c init_pos init_labs code1.
Proof.
  intros Hs He H1 H2 H3 H4 H5 H6 H7 H9 H10 H11.
  pose proof (code_similar_MAP_Section_num _ _ Hs) as Hm.
  split; [rewrite <- (code_similar_ends_with_label _ _ Hs); exact H1|].
  split; [exact (code_similar_sec_labels_ok _ _ (conj H2 Hs))|].
  split; [rewrite <- Hm; exact H3|].
  split; [rewrite EVERY_ALL_DISTINCT_extract_labels, <- (code_similar_extract_labels _ _ Hs),
            <- EVERY_ALL_DISTINCT_extract_labels; exact H4|].
  split; [rewrite <- Hm; exact H5|].
  split; [rewrite <- (code_similar_get_labels _ _ Hs), <- (code_similar_get_code_labels _ _ Hs); exact H6|].
  split; [rewrite <- (code_similar_all_enc_ok_pre c _ _ Hs); exact H7|].
  splits; first [assumption|reflexivity].
Qed.

Lemma rl_done c init_pos init_labs ffis (code code1 sec_list : list (sec a)) :
  enc_secs_again init_pos (compute_labels_alt init_pos code init_labs) ffis (encode c) code =
    (code1, true) ->
  enc_secs_again init_pos (compute_labels_alt init_pos (upd_lab_len init_pos code1) init_labs) ffis
    (encode c) (upd_lab_len init_pos code1) = (sec_list, true) ->
  EVERY (sec_ok_light c) (pad_code (encode c (Inst asm.Skip)) sec_list) ->
  zero_labs_acc_exist (compute_labels_alt init_pos (upd_lab_len init_pos code1) init_labs)
    (pad_code (encode c (Inst asm.Skip)) sec_list) ->
  rl_pre c init_pos init_labs code ->
  rl_post c init_pos init_labs ffis code (pad_code (encode c (Inst asm.Skip)) sec_list)
    (compute_labels_alt init_pos (upd_lab_len init_pos code1) init_labs).
Proof.
  intros E1 E2 Hlight Hzero Hpre.
  pose proof Hpre as (Hends & Hok & Hdist & Hdl & Hdisj & Hsub & Hpre0 & Hencd0 & Hc & Hev & Hinit).
  set (code2' := upd_lab_len init_pos code1) in *.
  set (labs := compute_labels_alt init_pos code2' init_labs) in *.
  set (nop := encode c (Inst asm.Skip)) in *.
  set (pad := pad_code nop sec_list) in *.
  pose proof Hc as (Hc1 & Hc2 & _).
  (* similarity *)
  assert (S1 : code_similar code code1) by exact (enc_secs_again_IMP_similar _ _ _ _ _ _ _ E1).
  assert (S2 : code_similar code1 code2').
  { apply code_similar_sym. apply code_similar_upd_lab_len, code_similar_refl. }
  assert (S3 : code_similar code2' sec_list) by exact (enc_secs_again_IMP_similar _ _ _ _ _ _ _ E2).
  assert (S4 : code_similar sec_list pad) by (apply code_similar_pad_code, code_similar_refl).
  assert (S : code_similar code pad).
  { eapply code_similar_trans. split; [exact S1|]. eapply code_similar_trans. split; [exact S2|].
    eapply code_similar_trans. split; [exact S3|exact S4]. }
  assert (S' : code_similar code code2').
  { eapply code_similar_trans. split; [exact S1|exact S2]. }
  (* invariants *)
  assert (F1 : all_encd0 (encode c) code1) by exact (enc_secs_again_encd0 _ _ _ _ _ _ _ (conj E1 Hencd0)).
  assert (F2 : EVERY sec_label_one code2') by apply upd_lab_len_label_one.
  assert (F3 : all_encd0 (encode c) code2') by exact (upd_lab_len_encd0 _ _ _ F1).
  assert (F4 : all_encd (encode c) labs ffis init_pos sec_list)
    by exact (enc_secs_again_encd _ _ _ _ _ _ (conj E2 (conj F2 F3))).
  assert (Hends1 : EVERY sec_ends_with_label code1)
    by exact (enc_secs_again_ends_with_label _ _ _ _ _ _ _ (conj E1 Hends)).
  assert (F5 : LENGTH nop <> 1 ->
               EVERY (sec_aligned (LENGTH nop)) sec_list /\ EVERY sec_label_zero sec_list).
  { intros Hn1.
    assert (Ha : code_alignment c <> 0).
    { intros Ha. apply Hn1. replace (LENGTH nop) with (2 ** code_alignment c) by exact Hc1.
      rewrite Ha. reflexivity. }
    assert (Hz2 : EVERY sec_label_zero code2').
    { apply (upd_lab_len_encd0_label_zero c (encode c)).
      splits; first [assumption|reflexivity]. }
    split; [|exact (enc_secs_again_label_zero _ _ _ _ _ _ _ (conj E2 Hz2))].
    apply (enc_secs_again_aligned (LENGTH nop) init_pos labs ffis (encode c) code2' sec_list true).
    split; [|split; [exact E2|]].
    - intros a0. replace (LENGTH nop) with (2 ** code_alignment c) by exact Hc1.
      apply (proj1 (Hc2 a0)).
    - apply (all_encd0_aligned c (encode c)). splits; first [assumption|reflexivity]. }
  assert (F6 : EVERY sec_label_one sec_list)
    by exact (enc_secs_again_label_one _ _ _ _ _ _ _ (conj E2 F2)).
  assert (F7 : all_length_leq sec_list) by exact (all_encd_length_leq _ _ _ _ _ F4).
  assert (F8 : EVERY sec_label_prefix_zero code2')
    by exact (upd_lab_len_label_prefix_zero _ _ (conj Hev Hends1)).
  assert (F9 : EVERY sec_label_prefix_zero sec_list)
    by exact (enc_secs_again_label_prefix_zero _ _ _ _ _ _ _ (conj E2 F8)).
  assert (F10 : all_lab_len_pos_ok init_pos sec_list)
    by exact (enc_secs_again_pos_ok _ _ _ _ _ _ (conj E2 (upd_lab_len_pos_ok _ _))).
  assert (F5z : LENGTH nop <> 1 -> EVERY sec_label_zero sec_list) by (intros Hn; apply F5, Hn).
  (* conclusions *)
  assert (C1 : all_enc_ok_pre c pad) by (rewrite <- (code_similar_all_enc_ok_pre c _ _ S); exact Hpre0).
  assert (C2 : EVERY sec_labels_ok pad) by exact (code_similar_sec_labels_ok _ _ (conj Hok S)).
  assert (Cnop : all_enc_with_nop (encode c) labs ffis init_pos pad).
  { apply all_enc_with_nop_pad_code. split; [apply N.neq_0_lt_0, (proj2 (Hc2 _))|].
    split; [reflexivity|]. splits; try assumption; apply F5; assumption. }
  assert (Cz : EVERY sec_label_zero pad) by exact (all_enc_with_nop_label_zero _ _ _ _ _ Cnop).
  assert (Cpos : all_lab_len_pos_ok init_pos pad).
  { apply all_lab_len_pos_ok_pad_code. splits; first [assumption|reflexivity]. }
  assert (Cends : EVERY sec_ends_with_label pad).
  { apply pad_code_ends_with_label. apply (enc_secs_again_ends_with_label init_pos labs ffis (encode c) code2' sec_list true).
    split; [exact E2|]. apply upd_lab_len_ends_with_label. exact Hends1. }
  assert (Hlabs_dom : labs_domain labs = get_code_labels code UNION labs_domain init_labs).
  { unfold labs. rewrite labs_domain_compute_labels_alt.
    - rewrite <- (code_similar_get_code_labels _ _ S'). reflexivity.
    - rewrite <- (code_similar_MAP_Section_num _ _ S'). split; assumption. }
  assert (Cex : all_labs_exist labs pad).
  { apply all_labs_exist_get_labels. apply zero_labs_acc_exist_eq in Hzero.
    rewrite <- (code_similar_get_labels _ _ S) in Hzero |- *.
    intros [n1 n2] Hin. destruct (N.eq_dec n2 0) as [->|Hn2].
    - apply Hzero. set_unfold. cbn. auto.
    - rewrite Hlabs_dom. apply Hsub. set_unfold. cbn. auto. }
  assert (Coff : offset_ok labs ffis init_pos pad).
  { apply offset_ok_pad_code. splits; try assumption.
    exact (enc_secs_again_offset_ok _ _ _ _ _ _ _ E2). }
  assert (C3 : all_enc_ok c labs ffis init_pos pad).
  { apply all_enc_ok_pre_light_imp_all_enc_ok. splits; try assumption.
    apply even_labels_ends_imp_strong. splits; try assumption.
    apply label_zero_pos_ok_even_labels. split; assumption. }
  assert (Hlabs : labs = compute_labels_alt init_pos pad init_labs).
  { unfold pad. rewrite pad_code_compute_labels by (splits; first [assumption|reflexivity]).
    symmetry. exact (enc_secs_again_compute_labels _ _ _ _ _ _ _ E2). }
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact S|].
  split; [intros Hodd; exact (has_odd_inst_alignment c labs ffis init_pos pad (conj Hc (conj C3 Hodd)))|].
  split.
  { intros l1 l2 x Hx. apply (all_enc_ok_lab_lookup_even c labs ffis init_pos pad l1 l2 init_labs x).
    split; [exact C3|split; [rewrite <- Hlabs; exact Hx|split; [|exact Hev]]].
    intros x' Hx'. specialize (Hinit l1 l2). rewrite Hx' in Hinit. exact Hinit. }
  split.
  { intros l1 l2 x Hx. unfold labs. rewrite lab_lookup_compute_labels_alt_ignore; [exact Hx|].
    unfold is_true. rewrite MEM_In. intros Hin.
    rewrite <- (code_similar_MAP_Section_num _ _ S') in Hin.
    rewrite IN_DISJOINT in Hdisj. apply Hdisj. exists l1. split.
    - apply domain_lookup. unfold lab_lookup in Hx. destruct (lookup l1 init_labs); [eexists; reflexivity|discriminate].
    - apply IN_set. exact Hin. }
  intros l1 l2 x2 Hx2. rewrite Hlabs.
  apply (lab_lookup_compute_labels_test init_pos pad init_labs l1 l2 x2 c labs ffis).
  split; [exact C2|]. split; [rewrite <- (code_similar_MAP_Section_num _ _ S); exact Hdist|].
  split; [change (is_true (EVERY (ALL_DISTINCT ∘ extract_labels ∘ Section_lines) pad));
          rewrite EVERY_ALL_DISTINCT_extract_labels, <- (code_similar_extract_labels _ _ S),
            <- EVERY_ALL_DISTINCT_extract_labels; exact Hdl|].
  split; [exact Cz|]. split; [exact C3|].
  rewrite <- (code_similar_loc_to_pc _ _ _ _ S). exact Hx2.
Qed.

Lemma remove_labels_loop_rl : forall n c init_pos init_labs ffis (code code2 : list (sec a)) labs,
  remove_labels_loop n c init_pos init_labs ffis code = SOME (code2, labs) ->
  rl_pre c init_pos init_labs code ->
  rl_post c init_pos init_labs ffis code code2 labs.
Proof.
  intros n. induction n as [|n IHn] using N.peano_ind;
    intros c init_pos init_labs ffis code code2 labs Hrl Hpre;
    rewrite remove_labels_loop_def in Hrl; cbv zeta in Hrl;
    destruct (enc_secs_again init_pos (compute_labels_alt init_pos code init_labs) ffis (encode c) code)
      as [code1 done] eqn:E1;
    (destruct done; [|cbn [N.eqb] in Hrl]).
  1, 3:
    destruct (enc_secs_again init_pos (compute_labels_alt init_pos (upd_lab_len init_pos code1) init_labs)
                ffis (encode c) (upd_lab_len init_pos code1)) as [sec_list done2] eqn:E2;
    destruct done2; [|discriminate];
    destruct (EVERY (sec_ok_light c) (pad_code (encode c (Inst asm.Skip)) sec_list)) eqn:Hlight;
      [|discriminate];
    destruct (zero_labs_acc_exist _ (pad_code (encode c (Inst asm.Skip)) sec_list)) eqn:Hzero;
      [|discriminate];
    cbn [andb] in Hrl; injection Hrl as <- <-;
    exact (rl_done c init_pos init_labs ffis code code1 sec_list E1 E2 Hlight Hzero Hpre).
  - discriminate.
  - rewrite (proj2 (N.eqb_neq _ _)) in Hrl by lia. rewrite N.sub_1_r, N.pred_succ in Hrl.
    pose proof (enc_secs_again_IMP_similar _ _ _ _ _ _ _ E1) as S1.
    pose proof Hpre as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & Hencd0 & P9 & P10 & P11).
    assert (Hpre1 : rl_pre c init_pos init_labs code1).
    { apply (rl_pre_similar c init_pos init_labs code); try assumption.
      exact (enc_secs_again_encd0 _ _ _ _ _ _ _ (conj E1 Hencd0)). }
    destruct (IHn _ _ _ _ _ _ _ Hrl Hpre1) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    split; [eapply code_similar_trans; split; [exact S1|exact H4]|].
    split; [exact H5|]. split; [exact H6|]. split; [exact H7|].
    intros l1 l2 x2 Hx2. apply H8. rewrite <- (code_similar_loc_to_pc _ _ _ _ S1). exact Hx2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "remove_labels_loop_thm" *)
Theorem remove_labels_loop_thm : forall n (c : asm_config a) init_pos init_labs ffis
    (code code2 : list (sec a)) labs,
  remove_labels_loop n c init_pos init_labs ffis code = SOME (code2, labs) /\
  EVERY sec_ends_with_label code /\
  EVERY sec_labels_ok code /\
  ALL_DISTINCT (MAP Section_num code) /\
  EVERY (ALL_DISTINCT ∘ extract_labels ∘ Section_lines) code /\
  DISJOINT (domain init_labs) (set (MAP Section_num code)) /\
  restrict_nonzero (get_labels code) SUBSET get_code_labels code UNION labs_domain init_labs /\
  all_enc_ok_pre c code /\
  all_encd0 (encode c) code /\
  enc_ok c /\
  EVEN init_pos /\
  (forall l1 l2, OPTION_ALL EVEN (lab_lookup l1 l2 init_labs)) ->
  all_enc_ok_pre c code2 /\
  EVERY sec_labels_ok code2 /\
  all_enc_ok c labs ffis init_pos code2 /\
  code_similar code code2 /\
  (has_odd_inst code2 -> code_alignment c = 0) /\
  (forall l1 l2 x, lab_lookup l1 l2 labs = SOME x -> EVEN x) /\
  (forall l1 l2 x, lab_lookup l1 l2 init_labs = SOME x ->
                   lab_lookup l1 l2 labs = SOME x) /\
  (forall l1 l2 x2,
     loc_to_pc l1 l2 code = SOME x2 ->
     lab_lookup l1 l2 labs = SOME (pos_val x2 init_pos code2)).
Proof.
  intros n c init_pos init_labs ffis code code2 labs [H Hpre].
  exact (remove_labels_loop_rl n c init_pos init_labs ffis code code2 labs H Hpre).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "loc_to_pc_enc_sec_list" *)
Theorem loc_to_pc_enc_sec_list : forall e l1 l2 (code : list (sec a)),
  loc_to_pc l1 l2 (enc_sec_list e code) = loc_to_pc l1 l2 code.
Proof.
  intros e l1 l2 code. apply code_similar_loc_to_pc.
  apply code_similar_enc_sec_list, code_similar_refl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_ok_pre_enc_sec_list" *)
Theorem all_enc_ok_pre_enc_sec_list : forall (code : list (sec a)) enc c,
  all_enc_ok_pre c code ->
  all_enc_ok_pre c (enc_sec_list enc code).
Proof.
  intros code enc c H. rewrite (code_similar_all_enc_ok_pre c _ code); [exact H|].
  apply code_similar_enc_sec_list, code_similar_refl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "remove_labels_thm" *)
Theorem remove_labels_thm : forall clock conf init_pos init_labs ffi_names (code code2 : list (sec a)) labs,
  remove_labels clock conf init_pos init_labs ffi_names code = SOME (code2, labs) /\
  enc_ok conf /\
  EVERY sec_ends_with_label code /\
  EVERY sec_labels_ok code /\
  ALL_DISTINCT (MAP Section_num code) /\
  EVERY (ALL_DISTINCT ∘ extract_labels ∘ Section_lines) code /\
  DISJOINT (domain init_labs) (set (MAP Section_num code)) /\
  restrict_nonzero (get_labels code) SUBSET get_code_labels code UNION labs_domain init_labs /\
  all_enc_ok_pre conf code /\
  EVEN init_pos /\
  (forall l1 l2, OPTION_ALL EVEN (lab_lookup l1 l2 init_labs)) ->
  all_enc_ok conf labs ffi_names init_pos code2 /\
  code_similar code code2 /\
  (has_odd_inst code2 -> code_alignment conf = 0) /\
  (forall l1 l2 x, lab_lookup l1 l2 labs = SOME x -> EVEN x) /\
  (forall l1 l2 x, lab_lookup l1 l2 init_labs = SOME x ->
                   lab_lookup l1 l2 labs = SOME x) /\
  (forall l1 l2 x2,
     loc_to_pc l1 l2 code = SOME x2 ->
     lab_lookup l1 l2 labs = SOME (pos_val x2 init_pos code2)).
Proof.
  intros clock conf init_pos init_labs ffi_names code code2 labs
    (H & Hc & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  unfold remove_labels in H.
  assert (S : code_similar code (enc_sec_list (encode conf) code)).
  { apply code_similar_sym, code_similar_enc_sec_list, code_similar_refl. }
  assert (Hpre : rl_pre conf init_pos init_labs (enc_sec_list (encode conf) code)).
  { apply (rl_pre_similar conf init_pos init_labs code); try assumption. apply enc_sec_list_encd0. }
  destruct (remove_labels_loop_rl _ _ _ _ _ _ _ _ H Hpre) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  split; [exact C3|]. split; [eapply code_similar_trans; split; [exact S|exact C4]|].
  split; [exact C5|]. split; [exact C6|]. split; [exact C7|].
  intros l1 l2 x2 Hx2. apply C8. rewrite loc_to_pc_enc_sec_list. exact Hx2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "compute_labels_alt_domain_labs" *)
Theorem compute_labels_alt_domain_labs : forall pos (code : list (sec a)) labs,
  domain (compute_labels_alt pos code labs) =
  IMAGE FST (get_code_labels code) UNION domain labs.
Proof.
  intros pos code; revert pos. induction code as [|[k lines] rest IH]; intros pos labs.
  - cbn [compute_labels_alt]. rewrite get_code_labels_nil. apply EXTENSION. intros y.
    rewrite IN_UNION, IMAGE_EMPTY. pose proof (NOT_IN_EMPTY y). tauto.
  - cbn [compute_labels_alt]. destruct (section_labels pos lines []) as [np sl].
    rewrite IH. apply EXTENSION. intros y.
    rewrite get_code_labels_cons, !IN_UNION, !IN_IMAGE.
    change (y IN domain (insert k (fromAList ((0, pos) :: sl)) labs)) with
      (domain (insert k (fromAList ((0, pos) :: sl)) labs) y).
    rewrite domain_insert. change (domain labs y) with (y IN domain labs).
    cbn [sec_get_code_labels]. split.
    + intros [([m1 m2] & -> & Hm)|[->|Hd]].
      * left. exists (m1, m2). split; [reflexivity|]. apply IN_UNION. right. exact Hm.
      * left. exists (k, 0). split; [reflexivity|]. apply IN_UNION. left. apply IN_INSERT. left. reflexivity.
      * right. exact Hd.
    + intros [([m1 m2] & -> & Hm)|Hd]; [|right; right; exact Hd].
      apply IN_UNION in Hm as [Hm|Hm].
      * right. left. apply IN_INSERT in Hm as [E|Hm]; [injection E as -> _; reflexivity|].
        apply IN_IMAGE in Hm as (z & E & _). injection E as -> _. reflexivity.
      * left. exists (m1, m2). split; [reflexivity|exact Hm].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "remove_labels_loop_domain_labs" *)
Theorem remove_labels_loop_domain_labs : forall a0 b c d e (f g : list (sec a)) h,
  remove_labels_loop a0 b c d e f = SOME (g, h) ->
  domain h = IMAGE FST (get_code_labels f) UNION domain d.
Proof.
  intros a0. induction a0 as [|n IHn] using N.peano_ind; intros b c d e f g h Hrl;
    rewrite remove_labels_loop_def in Hrl; cbv zeta in Hrl;
    destruct (enc_secs_again c (compute_labels_alt c f d) e (encode b) f) as [code1 done] eqn:E1;
    pose proof (enc_secs_again_IMP_similar _ _ _ _ _ _ _ E1) as S1;
    (destruct done; [|cbn [N.eqb] in Hrl]).
  1, 3:
    destruct (enc_secs_again c (compute_labels_alt c (upd_lab_len c code1) d) e (encode b)
                (upd_lab_len c code1)) as [sec_list done2];
    destruct (done2 && _ && _); [|discriminate];
    injection Hrl as _ <-;
    rewrite compute_labels_alt_domain_labs, (code_similar_get_code_labels f (upd_lab_len c code1));
    [reflexivity|];
    eapply code_similar_trans; split; [exact S1|];
    apply code_similar_sym, code_similar_upd_lab_len, code_similar_refl.
  - discriminate.
  - rewrite (proj2 (N.eqb_neq _ _)) in Hrl by lia. rewrite N.sub_1_r, N.pred_succ in Hrl.
    rewrite (IHn _ _ _ _ _ _ _ Hrl), (code_similar_get_code_labels _ _ S1). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "remove_labels_domain_labs" *)
Theorem remove_labels_domain_labs : forall c t k init_labs f (p q : list (sec a)) labs,
  remove_labels c t k init_labs f p = SOME (q, labs) ->
  domain labs = IMAGE FST (get_code_labels p) UNION domain init_labs.
Proof.
  intros c t k init_labs f p q labs H. unfold remove_labels in H.
  rewrite (remove_labels_loop_domain_labs _ _ _ _ _ _ _ _ H).
  rewrite (code_similar_get_code_labels (enc_sec_list (encode t) p) p); [reflexivity|].
  apply code_similar_enc_sec_list, code_similar_refl.
Qed.

End RemoveLabels.
