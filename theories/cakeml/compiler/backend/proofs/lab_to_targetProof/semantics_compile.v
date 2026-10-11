(** * CakeML [lab_to_targetProof]: [semantics_compile]

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml] (HOL
    lines 11011-11303): [semantics_compile_lemma'],
    [semantics_compile_lemma] and the main theorem [semantics_compile].

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v].
    - HOL's [compile] is [lab_to_target.compile]; HOL's [c.ffi_names] (the
      compiler configuration field) is [c.(lab_to_target.ffi_names)].
    - HOL's [dm ∩ byte_aligned] is [dm INTER (fun w => byte_aligned w)].
    - HOL's [{x}] is [x INSERT {}].
    - HOL derives [semantics_compile_lemma] from [semantics_compile_lemma']
      by ML rule manipulation with [implements_intro_gen]; here it is
      stated explicitly.
    - HOL uses [semanticsProps.implements'_trans] (not ported in
      [semanticsProps]); only its [precise = true] instance is needed and
      is proved here as the Galette-only helper [sc_implements'_T_trans].
    - Not ported: the HOL theorems that are commented out in the HOL source
      ([get_shmem_info_FST_eq], [get_shmem_info_FST_SND_LENGTH_eq],
      [start_pc_ok_not_vacuous_lemma]).
    - The [sc_*] lemmas are Galette-only helpers. *)

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
  sem_machine init_defs init_state_rel filter_skip.
Import wordLang (word_loc, Word, Loc).
Import wordSem (mem_load_byte_aux, mem_store_byte_aux, write_bytearray, mem_load_32,
  mem_store_32, buffer, position, buffer_buffer, space_left).
Import ByteBits.
Open Scope N_scope.

Section Helpers.
Context {a : N}.

Lemma sc_implements'_T_trans (x y z : behaviour -> Prop) :
  implements' true y z -> implements' true x y -> implements' true x z.
Proof.
  unfold implements', extend_with_resource_limit'. intros H1 H2 Hz w Hw.
  apply H1; [exact Hz|]. apply H2; [|exact Hw].
  intros Hy. apply Hz. exact (H1 Hz Fail Hy).
Qed.

Lemma sc_TAKE_LENGTH_APPEND {X} (l1 l2 : list X) : TAKE (LENGTH l1) (l1 ++ l2) = l1.
Proof.
  rewrite TAKE_firstn, LENGTH_length, Nat2N.id, firstn_app, firstn_all, Nat.sub_diag. cbn.
  apply app_nil_r.
Qed.

Lemma sc_DROP_LENGTH_APPEND {X} (l1 l2 : list X) : DROP (LENGTH l1) (l1 ++ l2) = l2.
Proof.
  rewrite DROP_skipn, LENGTH_length, Nat2N.id, skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma sc_EVERY_extract_labels_filter_skip (code : list (sec a)) :
  EVERY (ALL_DISTINCT ∘ extract_labels ∘ Section_lines) (filter_skip code) =
  EVERY (ALL_DISTINCT ∘ extract_labels ∘ Section_lines) code.
Proof.
  induction code as [|[k ls] code IH]; [reflexivity|]. cbn [filter_skip EVERY].
  rewrite IH. f_equal. cbn. rewrite fs_extract_labels_FILTER. reflexivity.
Qed.

Lemma sc_sec_labels_ok_filter_skip (code : list (sec a)) :
  EVERY sec_labels_ok code -> EVERY sec_labels_ok (filter_skip code).
Proof.
  unfold is_true. induction code as [|[k ls] code IH]; intros H; [reflexivity|].
  cbn [filter_skip EVERY] in *. apply andb_prop in H as [H1 H2].
  apply andb_true_intro. split; [|apply IH, H2]. cbn [sec_labels_ok] in *. apply fs_EVERY_FILTER, H1.
Qed.

Lemma sc_good_code_filter_skip {X} c (labs : spt (spt X)) (code : list (sec a)) :
  good_code c labs code -> good_code c labs (filter_skip code).
Proof.
  intros (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  split; [apply lab_filterProof.sec_ends_with_label_filter_skip, G1|].
  split; [apply sc_sec_labels_ok_filter_skip, G2|].
  split; [rewrite MAP_Section_num_filter_skip; exact G3|].
  split; [unfold is_true; rewrite sc_EVERY_extract_labels_filter_skip; exact G4|].
  split; [rewrite MAP_Section_num_filter_skip; exact G5|].
  split; [rewrite get_labels_filter_skip, get_code_labels_filter_skip; exact G6|].
  apply all_enc_ok_pre_filter_skip, G7.
Qed.

Lemma sc_compile_lab_inv (cfg : asm_config a) (c c' : config) (code : list (sec a)) bytes :
  compile_lab cfg c code = SOME (bytes, c') ->
  exists ffis code2 labs new_ffis shinfo,
    list_subset (find_ffi_names code) ffis /\
    (forall f, c.(lab_to_target.ffi_names) = SOME f -> f = ffis) /\
    (c.(lab_to_target.ffi_names) = NONE -> ffis = find_ffi_names code) /\
    remove_labels (init_clock c) cfg (pos c) (labels c) ffis code = SOME (code2, labs) /\
    get_shmem_info code2 (pos c) [] [] = (new_ffis, shinfo) /\
    bytes = prog_to_bytes code2 /\
    c'.(labels) = labs /\
    c'.(lab_to_target.ffi_names) = SOME (ffis ++ new_ffis) /\
    c'.(shmem_extra) = shinfo.
Proof.
  unfold compile_lab. cbv zeta. intros H.
  destruct (lab_to_target.ffi_names c) as [f|] eqn:Ecf.
  - destruct (list_subset (find_ffi_names code) f) eqn:Eok; [|discriminate].
    destruct (remove_labels _ _ _ _ _ _) as [[code2 labs]|] eqn:Erl; [|discriminate].
    destruct (get_shmem_info code2 (pos c) [] []) as [nf sh] eqn:Eg.
    injection H as <- <-.
    exists f, code2, labs, nf, sh. split; [exact Eok|]. split; [intros f' E; injection E as <-; reflexivity|].
    split; [discriminate|]. repeat split; assumption || reflexivity.
  - destruct (remove_labels _ _ _ _ _ _) as [[code2 labs]|] eqn:Erl; [|discriminate].
    destruct (get_shmem_info code2 (pos c) [] []) as [nf sh] eqn:Eg.
    injection H as <- <-.
    exists (find_ffi_names code), code2, labs, nf, sh. split; [apply list_subset_refl|].
    split; [discriminate|]. split; [reflexivity|]. repeat split; assumption || reflexivity.
Qed.

End Helpers.

Section SemanticsCompile.
Context {a : N} {B C Ffi : Type}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "semantics_compile_lemma'" *)
Theorem semantics_compile_lemma' : forall (mc_conf : machine_config a B C) (code : list (sec a))
    (coracle : N -> config * list (sec a)) (c c' : config) (asm_conf : asm_config a) bytes (ms : B)
    cbspace (t : asm_state a) m dm sdm i (ffi : ffi_state Ffi),
  mc_conf_ok mc_conf /\
  (no_share_mem_inst code ->
     compiler_oracle_ok coracle c'.(labels) (LENGTH bytes) asm_conf mc_conf.(ffi_names)) /\
  good_code (asmProps.config mc_conf.(target)) (@LN (spt N)) code /\
  asm_conf = asmProps.config mc_conf.(target) /\
  c.(labels) = LN /\ c.(pos) = 0 /\
  lab_to_target.compile asm_conf c code = SOME (bytes, c') /\
  c'.(lab_to_target.ffi_names) = SOME mc_conf.(ffi_names) /\
  good_init_state mc_conf ms bytes cbspace t m dm sdm /\
  MAP (fun rec => w2n (get_pc mc_conf.(target) ms) + entry_pc rec) c'.(shmem_extra) =
    DROP i (MAP w2n mc_conf.(ffi_entry_pcs)) /\
  mc_conf.(mmio_info) =
    ZIP (GENLIST (fun index => index + i) (LENGTH c'.(shmem_extra)),
         MAP (fun rec => (nbytes rec, (Addr (addr_reg rec) (n2w (addr_off rec)),
                (reg rec, (n2w (exit_pc rec) + get_pc mc_conf.(target) ms)%w)))) c'.(shmem_extra)) /\
  no_install_or_no_share_mem code mc_conf.(ffi_names) /\
  mmio_pcs_min_index mc_conf.(ffi_names) = SOME i /\
  cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword a /\
  (forall ffis, c.(lab_to_target.ffi_names) = SOME ffis ->
     EVERY (fun x => ⌜exists s, x = ExtCall s⌝) ffis) /\
  semantics (make_init mc_conf ffi t m dm sdm ms code (lab_to_target.compile asm_conf)
    (get_pc mc_conf.(target) ms + n2w (LENGTH bytes))%w cbspace coracle) <> Fail ->
  machine_sem mc_conf ffi ms =
    (semantics (make_init mc_conf ffi t m dm sdm ms code (lab_to_target.compile asm_conf)
      (get_pc mc_conf.(target) ms + n2w (LENGTH bytes))%w cbspace coracle)) INSERT {}.
Proof.
  intros mc_conf code coracle c c' asm_conf bytes ms cbspace t m dm sdm i ffi
    (Hmc & Horc & Hgood & -> & Hlab & Hpos & Hcomp & Hffi & Hgis & Hmap & Hmmio_info & Hnios
     & Hmmio & Hbound & Hffis & Hsem).
  set (cfg := asmProps.config mc_conf.(target)) in *.
  set (pc0 := get_pc mc_conf.(target) ms) in *.
  unfold lab_to_target.compile in Hcomp.
  destruct (sc_compile_lab_inv _ _ _ _ _ Hcomp)
    as (ffis & code2 & labs & nf & sh & Hsub & Hsome & Hnone & Hrl & Hg & -> & Elabs & Effi & Esh).
  rewrite Hlab, Hpos in Hrl. rewrite Hpos in Hg.
  rewrite Elabs in Horc. rewrite Esh in Hmap, Hmmio_info.
  rewrite Effi in Hffi. injection Hffi as Efn.
  (* the ffi names given to the compiler are all [ExtCall]s *)
  assert (Hext : EVERY (fun x => ⌜exists s, x = ExtCall s⌝) ffis).
  { destruct (lab_to_target.ffi_names c) as [f|] eqn:Ecf.
    - rewrite <- (Hsome f eq_refl). exact (Hffis f eq_refl).
    - rewrite (Hnone eq_refl). exact (find_ffi_names_EVERY _ _ eq_refl). }
  destruct (get_shmem_info_MappedRead_or_MappedWrite _ _ _ _ _ _ Hg) as (l & El & Hl).
  cbn [app] in El. subst l.
  assert (Hi : mmio_pcs_min_index mc_conf.(ffi_names) = SOME (LENGTH ffis)).
  { rewrite <- Efn. apply mmio_pcs_min_index_APPEND_thm. split; [|exact Hext].
    unfold is_true in *. rewrite EVERY_Forall, List.Forall_forall in *. intros x Hx.
    apply bool_decide_spec. apply Sh_not_Ext. exact (proj1 (bool_decide_spec _) (Hl x Hx)). }
  rewrite Hmmio in Hi. injection Hi as ->.
  assert (Es : semantics (make_init mc_conf ffi t m dm sdm ms code (fun c0 p => compile_lab cfg c0 (filter_skip p))
             (pc0 + n2w (LENGTH (prog_to_bytes code2)))%w cbspace coracle) =
           semantics (make_init mc_conf ffi t m dm sdm ms (filter_skip code) (compile_lab cfg)
             (pc0 + n2w (LENGTH (prog_to_bytes code2)))%w cbspace
             ((fun '(a0, b) => (a0, filter_skip b)) ∘ coracle)))
    by (symmetry; apply make_init_filter_skip).
  change (lab_to_target.compile cfg) with (fun c0 p => compile_lab cfg c0 (filter_skip p)) in Hsem |- *.
  rewrite Es in Hsem |- *.
  pose proof Hmc as (Mg & Menc & _).
  pose proof Hgis as (_ & _ & I3 & I4 & _). rewrite I3 in I4.
  pose proof I4 as (_ & _ & _ & _ & _ & _ & _ & i' & Si & S8 & _ & _).
  rewrite Hmmio in Si. injection Si as <-.
  apply (semantics_make_init mc_conf (filter_skip code) code2 _ labs (LENGTH ffis) (init_clock c) ms
           cbspace t m dm sdm nf sh
           (MAP (fun rec => {| entry_pc := w2n pc0 + entry_pc rec; nbytes := nbytes rec;
                               addr_reg := addr_reg rec; addr_off := addr_off rec; reg := reg rec;
                               exit_pc := w2n pc0 + exit_pc rec |}) sh) ffi).
  split; [exact Menc|].
  split; [exact (sc_good_code_filter_skip _ _ _ Hgood)|].
  split; [exact Hmc|].
  split.
  { intros Hns. apply (proj1 (no_share_mem_filter_skip code)) in Hns. destruct (Horc Hns) as [O1 O2]. split.
    - intros k. specialize (O1 k). cbv beta. destruct (coracle k) as [cf cd].
      destruct O1 as [Og On]. split; [exact (sc_good_code_filter_skip _ _ _ Og)|].
      apply (proj2 (no_share_mem_filter_skip cd)), On.
    - cbv beta. destruct (coracle 0) as [cf cd]. exact O2. }
  split.
  { rewrite <- Efn, sc_TAKE_LENGTH_APPEND, find_ffi_names_filter_skip.
    rewrite (FILTER_EVERY_id _ _ (find_ffi_names_EVERY code _ eq_refl)).
    rewrite <- find_ffi_names_filter_skip. exact Hsub. }
  split; [rewrite <- Efn, sc_TAKE_LENGTH_APPEND; exact Hrl|].
  split; [exact Hgis|].
  split; [exact Hg|].
  split; [reflexivity|].
  split; [rewrite <- Efn; apply sc_DROP_LENGTH_APPEND|].
  split; [exact Hmmio|].
  split; [rewrite map_map; exact Hmap|].
  split.
  { rewrite Hmmio_info, LENGTH_MAP', map_map. f_equal. f_equal. apply map_ext. intros rec.
    cbn [nbytes addr_reg addr_off reg exit_pc]. f_equal. f_equal. f_equal.
    unfold pc0. rewrite <- word_add_n2w, n2w_w2n. apply WORD_ADD_COMM. }
  split; [apply no_install_or_no_share_mem_filter_skip, Hnios|].
  split; [|exact Hsem].
  (* the code buffer does not overlap the ffi entry points *)
  intros bn Hbn Hm. apply MEM_TAKE_EL in Hm as (k & Hk & _ & Hel).
  destruct (S8 k Hk) as (_ & _ & _ & _ & Hf).
  pose proof (find_index_EL _ _ _ _ Hf) as Hel'.
  rewrite N.sub_0_r, Hel in Hel'.
  set (X := (3 + k) * ffi_offset) in *.
  set (L := LENGTH (prog_to_bytes code2)) in *.
  assert (Hz : (n2w (bn + L + X) : word a) = n2w 0).
  { rewrite <- !word_add_n2w. unfold pc0 in *.
    transitivity ((n2w bn + n2w L + get_pc mc_conf.(target) ms) - get_pc mc_conf.(target) ms + n2w X)%w;
      [word_ring|]. rewrite Hel'. word_ring. }
  apply (f_equal w2n) in Hz. rewrite !w2n_n2w in Hz.
  assert (Hlt : bn + L + X < dimword a) by (unfold X, ffi_offset in *; lia).
  rewrite N.mod_small in Hz by exact Hlt. rewrite N.mod_small in Hz by lia.
  unfold X, ffi_offset in Hz. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "semantics_compile_lemma" *)
Theorem semantics_compile_lemma : forall (mc_conf : machine_config a B C) (code : list (sec a))
    (coracle : N -> config * list (sec a)) (c c' : config) (asm_conf : asm_config a) bytes (ms : B)
    cbspace (t : asm_state a) m dm sdm i (ffi : ffi_state Ffi),
  mc_conf_ok mc_conf /\
  (no_share_mem_inst code ->
     compiler_oracle_ok coracle c'.(labels) (LENGTH bytes) asm_conf mc_conf.(ffi_names)) /\
  good_code (asmProps.config mc_conf.(target)) (@LN (spt N)) code /\
  asm_conf = asmProps.config mc_conf.(target) /\
  c.(labels) = LN /\ c.(pos) = 0 /\
  lab_to_target.compile asm_conf c code = SOME (bytes, c') /\
  c'.(lab_to_target.ffi_names) = SOME mc_conf.(ffi_names) /\
  good_init_state mc_conf ms bytes cbspace t m dm sdm /\
  MAP (fun rec => w2n (get_pc mc_conf.(target) ms) + entry_pc rec) c'.(shmem_extra) =
    DROP i (MAP w2n mc_conf.(ffi_entry_pcs)) /\
  mc_conf.(mmio_info) =
    ZIP (GENLIST (fun index => index + i) (LENGTH c'.(shmem_extra)),
         MAP (fun rec => (nbytes rec, (Addr (addr_reg rec) (n2w (addr_off rec)),
                (reg rec, (n2w (exit_pc rec) + get_pc mc_conf.(target) ms)%w)))) c'.(shmem_extra)) /\
  no_install_or_no_share_mem code mc_conf.(ffi_names) /\
  mmio_pcs_min_index mc_conf.(ffi_names) = SOME i /\
  cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword a /\
  (forall ffis, c.(lab_to_target.ffi_names) = SOME ffis ->
     EVERY (fun x => ⌜exists s, x = ExtCall s⌝) ffis) ->
  implements' true (machine_sem mc_conf ffi ms)
    ((semantics (make_init mc_conf ffi t m dm sdm ms code (lab_to_target.compile asm_conf)
      (get_pc mc_conf.(target) ms + n2w (LENGTH bytes))%w cbspace coracle)) INSERT {}).
Proof.
  intros mc_conf code coracle c c' asm_conf bytes ms cbspace t m dm sdm i ffi H.
  refine (implements_intro_gen _ _ _ _ H). intros [Hb Hx].
  apply (semantics_compile_lemma' mc_conf code coracle c c' asm_conf bytes ms cbspace t m dm sdm i ffi).
  destruct Hb as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15).
  repeat (split; [eassumption|]). exact Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "semantics_compile" *)
Theorem semantics_compile : forall (mc_conf : machine_config a B C) (code : list (sec a))
    (coracle : N -> config * list (sec a)) (c c' : config) (asm_conf : asm_config a) bytes (ms : B)
    cbspace (t : asm_state a) m dm sdm i (ffi : ffi_state Ffi),
  mc_conf_ok mc_conf /\
  (no_share_mem_inst code ->
     compiler_oracle_ok coracle c'.(labels) (LENGTH bytes) asm_conf mc_conf.(ffi_names)) /\
  good_code asm_conf c.(labels) code /\
  asm_conf = asmProps.config mc_conf.(target) /\
  c.(labels) = LN /\ c.(pos) = 0 /\
  lab_to_target.compile asm_conf c code = SOME (bytes, c') /\
  c'.(lab_to_target.ffi_names) = SOME mc_conf.(ffi_names) /\
  good_init_state mc_conf ms bytes cbspace t m dm sdm /\
  mmio_pcs_min_index mc_conf.(ffi_names) = SOME i /\
  MAP (fun rec => w2n (get_pc mc_conf.(target) ms) + entry_pc rec) c'.(shmem_extra) =
    DROP i (MAP w2n mc_conf.(ffi_entry_pcs)) /\
  mc_conf.(mmio_info) =
    ZIP (GENLIST (fun index => index + i) (LENGTH c'.(shmem_extra)),
         MAP (fun rec => (nbytes rec, (Addr (addr_reg rec) (n2w (addr_off rec)),
                (reg rec, (n2w (exit_pc rec) + get_pc mc_conf.(target) ms)%w)))) c'.(shmem_extra)) /\
  no_install_or_no_share_mem code mc_conf.(ffi_names) /\
  cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword a /\
  (forall ffis, c.(lab_to_target.ffi_names) = SOME ffis ->
     EVERY (fun x => ⌜exists s, x = ExtCall s⌝) ffis) ->
  implements' true (machine_sem mc_conf ffi ms)
    ((semantics (make_init mc_conf ffi t m (dm INTER (fun w => byte_aligned w))
       (sdm INTER (fun w => byte_aligned w)) ms code (lab_to_target.compile asm_conf)
       (get_pc mc_conf.(target) ms + n2w (LENGTH bytes))%w cbspace coracle)) INSERT {}).
Proof.
  intros mc_conf code coracle c c' asm_conf bytes ms cbspace t m dm sdm i ffi
    (Hmc & Horc & Hgood & Hconf & Hlab & Hpos & Hcomp & Hffi & Hgis & Hmmio & Hmap & Hmmio_info
     & Hnios & Hbound & Hffis).
  pose proof Hmc as (Mg & _).
  set (ss := fun dm' sdm' => make_init mc_conf ffi t m dm' sdm' ms code (lab_to_target.compile asm_conf)
       (get_pc mc_conf.(target) ms + n2w (LENGTH bytes))%w cbspace coracle).
  change (implements' true (machine_sem mc_conf ffi ms)
    (semantics (ss (dm INTER (fun w => byte_aligned w)) (sdm INTER (fun w => byte_aligned w))) INSERT {})).
  apply (sc_implements'_T_trans _ (semantics (ss dm (sdm INTER (fun w => byte_aligned w))) INSERT {})).
  { change (ss (dm INTER (fun w => byte_aligned w)) (sdm INTER (fun w => byte_aligned w)))
      with (align_dm (ss dm (sdm INTER (fun w => byte_aligned w)))).
    apply implements_align_dm, Mg. }
  apply (sc_implements'_T_trans _ (semantics (ss dm sdm) INSERT {})).
  { change (ss dm (sdm INTER (fun w => byte_aligned w))) with (align_sdm (ss dm sdm)).
    apply implements_align_sdm, Mg. }
  rewrite Hlab in Hgood. subst asm_conf.
  apply (semantics_compile_lemma mc_conf code coracle c c' _ bytes ms cbspace t m dm sdm i ffi).
  repeat (split; [eassumption|]). split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

End SemanticsCompile.
