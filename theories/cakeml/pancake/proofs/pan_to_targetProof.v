(** * Correctness of the Pancake-to-target composition.
    Port of [cakeml/pancake/proofs/pan_to_targetProofScript.sml], in progress.
    HOL's [PERMUTES] is [BIJ f UNIV UNIV]; quantified predicates inside
    boolean [EVERY] are reflected using [bool_decide]. *)
From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.coretypes Require Import pair option.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map sptree alist.
From Galette.HOL.examples.machine_code.hoare_triple Require Import set_sep.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmProps asmSem.
From Galette.cakeml.compiler.backend Require wordLang word_to_word word_to_stack
  word_depth stack_to_lab backend lab_to_target.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem.
From Galette.cakeml.compiler.backend Require Import labLang.
From Galette.cakeml.compiler.backend.semantics Require wordSem wordConvs stackProps labProps backendProps.
From Galette.cakeml.compiler.backend.semantics.wordProps Require consts code clock consts_with.
From Galette.cakeml.compiler.backend.proofs Require backendProof stack_to_labProof
  word_to_stackProof word_to_wordProof lab_to_targetProof wordConvsProof stack_removeProof stack_namesProof stack_allocProof.
From Galette.cakeml.pancake Require Import panLang.
From Galette.cakeml.pancake Require pan_to_word pan_to_target crep_to_loop.
From Galette.cakeml.pancake.proofs Require pan_to_wordProof.
Open Scope N_scope.

Section Composition.
Context {a : N}.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "pancake_good_code_def" *)
Definition pancake_good_code (pan_code : list (decl a)) : bool :=
  EVERY pan_to_wordProof.good_panops pan_code.


(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "pan_to_lab_good_code_lemma" *)
Theorem pan_to_lab_good_code_lemma (c : backend.config) lim1 lim2 offs stack_prog code0
    (asm_conf3 conf : asm_config a) bm wc fs word_prog word_conf word_prog0 col pan_prog :
  stack_to_lab.compile (backend.stack_conf c) (backend.data_conf c) lim1 lim2 offs stack_prog = code0 /\
  word_to_stack.compile asm_conf3 false word_prog = (bm, (wc, (fs, stack_prog))) /\
  word_to_word.compile word_conf asm_conf3 word_prog0 = (col, word_prog) /\
  pan_to_word.compile_prog (ISA asm_conf3) pan_prog = word_prog0 /\
  stack_to_labProof.labels_ok code0 /\ labProps.all_enc_ok_pre conf code0 ->
  basic.good_code conf (LN : spt (spt N)) code0.
Proof.
  intros [Hs [Hw [Hc [Hp [Hl He]]]]].
  destruct (stack_to_labProof.labels_ok_imp code0 Hl) as [Hsl [Had Hel]].
  assert (Hhandlers : stackProps.stack_good_handler_labels stack_prog).
  { eapply syntax.word_to_stack_good_handler_labels; [|exact Hw].
    pose proof (pan_to_wordProof.pan_to_word_good_handlers _ _ _ Hp) as H.
    pose proof (wordConvsProof.word_good_handlers_word_to_word word_conf asm_conf3 word_prog0 H) as H1.
    rewrite Hc in H1; exact H1. }
  unfold basic.good_code; repeat split; try assumption.
  - rewrite <- Hs; unfold stack_to_lab.compile; apply stack_to_labProof.EVERY_sec_ends_with_label_MAP_prog_to_section.
  - unfold DISJOINT, domain; cbn.
    apply functional_extensionality; intros x; apply propositional_extensionality; unfold pred_set.INTER, pred_set.EMPTY, pred_set.IN; tauto.
  - intros x Hx; left.
    eapply stack_to_labProof.stack_to_lab_stack_good_handler_labels; [repeat split; eassumption|exact Hx].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "word_to_stack_compile_FST" *)
Theorem word_to_stack_compile_FST {B C : Type} (mc : machine_config a B C)
    wprog bitmaps c'' fs p :
  word_to_stack.compile (asmProps.config (target mc)) false wprog =
    (bitmaps, (c'', (fs, p))) ->
  MAP FST p = wordLang.raise_stub_location ::
    wordLang.store_consts_stub_location :: MAP FST wprog.
Proof.
  unfold word_to_stack.compile; cbv zeta.
  destruct (word_to_stack.compile_word_to_stack _ _ _ _ _) as [ps [sizes bm]] eqn:E.
  intros H; inversion H; subst; cbn [MAP List.map FST fst].
  do 2 f_equal; eapply compile_props.MAP_FST_compile_word_to_stack; exact E.
Qed.

Lemma word_compile_names (wc : word_to_word.config) (ac : asm_config a) ps col qs :
  ISA ac <> Ag32 -> word_to_word.compile wc ac ps = (col, qs) ->
  MAP FST qs = MAP FST ps.
Proof.
  intros HI HC; apply (backendProof.compile_to_word_conventions2 wc ac ps col qs).
  split; [exact HC|]. apply EVERY_Forall; apply Forall_forall.
  intros [n [m p]] _; apply bool_decide_spec; right; exact HI.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "pan_to_stack_first_ALL_DISTINCT" *)
Theorem pan_to_stack_first_ALL_DISTINCT {B C : Type}
    (mc : machine_config a B C) (c : backend.config)
    pan_code wprog0 col wprog bitmaps c'' fs p :
  pan_to_word.compile_prog (ISA (asmProps.config (target mc))) pan_code = wprog0 /\
  word_to_word.compile (backend.word_to_word_conf c) (asmProps.config (target mc)) wprog0 = (col, wprog) /\
  ISA (asmProps.config (target mc)) <> Ag32 /\
  word_to_stack.compile (asmProps.config (target mc)) false wprog = (bitmaps, (c'', (fs, p))) /\
  ALL_DISTINCT (MAP FST (functions pan_code)) -> ALL_DISTINCT (MAP FST p).
Proof.
  intros (Hp & Hw & HI & Hs & HD).
  rewrite (word_to_stack_compile_FST mc _ _ _ _ _ Hs),
    (word_compile_names _ _ _ _ _ HI Hw).
  apply ALL_DISTINCT_NoDup_list; constructor.
  - cbn [In wordLang.raise_stub_location wordLang.store_consts_stub_location].
    intros [H|H]; [discriminate|].
    pose proof (pan_to_wordProof.pan_to_word_compile_prog_lab_min _ _ _ Hp) as HM.
    apply EVERY_Forall in HM; rewrite Forall_forall in HM.
    apply in_map_iff in H as [x [Hx HxIn]].
    specialize (HM x HxIn); apply N.leb_le in HM.
    change (FST x = 5) in Hx; rewrite Hx in HM; lia.
  - constructor.
    + intros H; pose proof (pan_to_wordProof.pan_to_word_compile_prog_lab_min _ _ _ Hp) as HM.
    apply EVERY_Forall in HM; rewrite Forall_forall in HM.
    apply in_map_iff in H as [x [Hx HxIn]].
    specialize (HM x HxIn); apply N.leb_le in HM.
    change (FST x = 6) in Hx; rewrite Hx in HM; lia.
    + apply ALL_DISTINCT_NoDup_list.
      rewrite <- Hp; apply pan_to_wordProof.first_compile_prog_all_distinct; exact HD.
Qed.

Local Definition word_labels (x : N * (N * wordLang.prog a)) : bool :=
  let '(n, (m, p)) := x in
  EVERY (fun '(l1,l2) => (l1 =? n) && negb (l2 =? 0) && negb (l2 =? 1))
    (wordConvs.extract_labels p) && ALL_DISTINCT (wordConvs.extract_labels p).

Local Lemma word_labels_preserved ps qs :
  MAP FST qs = MAP FST ps ->
  LIST_REL wordConvs.labels_rel
    (MAP (wordConvs.extract_labels ∘ SND ∘ SND) ps)
    (MAP (wordConvs.extract_labels ∘ SND ∘ SND) qs) ->
  EVERY word_labels ps -> EVERY word_labels qs.
Proof.
  revert qs; induction ps as [|[n [m p]] ps IH]; intros [|[n' [m' p']] qs] HN HR HE;
    cbn [MAP List.map FST fst] in HN; try discriminate; [reflexivity|].
  injection HN as Hn Hns; subst n'.
  cbn [MAP List.map SND snd] in HR; inversion HR as [|? ? ? ? HL HT]; subst.
  change (is_true (word_labels (n, (m, p)) && EVERY word_labels ps)) in HE.
  apply andb_true_iff in HE as [HE HP]. apply andb_true_iff; split; [|eapply IH; eassumption].
  cbn [word_labels] in HE |- *; apply andb_true_iff in HE as [HE HD].
  destruct HL as [HD' HS]; apply andb_true_iff; split; [|apply HD'; exact HD].
  apply EVERY_Forall; apply EVERY_Forall in HE; rewrite Forall_forall in HE |- *.
  intros x Hx; apply HE; apply IN_set, HS, IN_set; exact Hx.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "pan_to_stack_compile_lab_pres" *)
Theorem pan_to_stack_compile_lab_pres {B C : Type}
    (mc : machine_config a B C) (c : backend.config)
    pan_code wprog0 col wprog bitmaps c'' fs p :
  pan_to_word.compile_prog (ISA (asmProps.config (target mc))) pan_code = wprog0 /\
  word_to_word.compile (backend.word_to_word_conf c) (asmProps.config (target mc)) wprog0 = (col, wprog) /\
  ISA (asmProps.config (target mc)) <> Ag32 /\
  word_to_stack.compile (asmProps.config (target mc)) false wprog = (bitmaps, (c'', (fs, p))) /\
  ALL_DISTINCT (MAP FST (functions pan_code)) ->
  ALL_DISTINCT (MAP FST p) /\
  EVERY (fun n => negb (n =? 0) && negb (n =? 1) && negb (n =? 2) && negb (n =? stackLang.gc_stub_location)) (MAP FST p) /\
  EVERY (fun '(n, p) =>
    EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0) && negb (l2 =? 1)) (stackProps.extract_labels p) &&
    ALL_DISTINCT (stackProps.extract_labels p)) p.
Proof.
  intros (Hp & Hw & HI & Hs & HD); split.
  - exact (pan_to_stack_first_ALL_DISTINCT mc c pan_code wprog0 col wprog bitmaps c'' fs p (conj Hp (conj Hw (conj HI (conj Hs HD))))) .
  - assert (HS : EVERY (fun '(_, (_, prg)) => bool_decide (wordConvs.no_share_inst prg \/
      ISA (asmProps.config (target mc)) <> Ag32)) wprog0).
    { apply EVERY_Forall; apply Forall_forall; intros [n [m prg]] _; apply bool_decide_spec; auto. }
    destruct (backendProof.compile_to_word_conventions2 _ _ _ _ _ (conj Hw HS)) as [HN [HR HC]].
    pose proof (pan_to_wordProof.pan_to_word_compile_lab_pres _ _ _ Hp) as HL.
    pose proof (word_labels_preserved _ _ HN HR HL) as HL'.
    pose proof (syntax.word_to_stack_compile_lab_pres (asmProps.config (target mc)) wprog HL') as HSP.
    rewrite Hs in HSP; cbn beta iota zeta in HSP; split; [|exact (proj2 HSP)].
    rewrite (proj1 HSP), HN.
    change (is_true (true && (true && EVERY
      (fun n => negb (n =? 0) && negb (n =? 1) && negb (n =? 2) && negb (n =? 4)) (MAP FST wprog0)))).
    cbn [andb]. apply EVERY_Forall; rewrite Forall_map, Forall_forall.
    pose proof (pan_to_wordProof.pan_to_word_compile_prog_lab_min _ _ _ Hp) as HM.
    apply EVERY_Forall in HM; rewrite Forall_forall in HM.
    intros x Hx; specialize (HM x Hx); apply N.leb_le in HM.
    apply andb_true_iff; split; [apply andb_true_iff; split; [apply andb_true_iff; split|]|];
      apply Bool.negb_true_iff, N.eqb_neq; lia.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "pan_to_lab_labels_ok" *)
Theorem pan_to_lab_labels_ok {B C : Type}
    (mc : machine_config a B C) (c : backend.config)
    pan_code wprog0 col wprog bitmaps c'' fs p max_heap sp lprog :
  pan_to_word.compile_prog (ISA (asmProps.config (target mc))) pan_code = wprog0 /\
  word_to_word.compile (backend.word_to_word_conf c) (asmProps.config (target mc)) wprog0 = (col, wprog) /\
  ISA (asmProps.config (target mc)) <> Ag32 /\
  word_to_stack.compile (asmProps.config (target mc)) false wprog = (bitmaps, (c'', (fs, p))) /\
  stack_to_lab.compile (backend.stack_conf c) (backend.data_conf c) max_heap sp
    (addr_offset (asmProps.config (target mc))) p = lprog /\
  ALL_DISTINCT (MAP FST (functions pan_code)) -> stack_to_labProof.labels_ok lprog.
Proof.
  intros (Hp & Hw & HI & Hs & <- & HD).
  apply stack_to_labProof.stack_to_lab_compile_lab_pres.
  destruct (pan_to_stack_compile_lab_pres mc c _ _ _ _ _ _ _ _
    (conj Hp (conj Hw (conj HI (conj Hs HD))))) as [H1 [H2 H3]]; auto.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "FLOOKUP_MAP_KEYS_LINV" *)
Theorem FLOOKUP_MAP_KEYS_LINV {A V : Type} `{Inhabited A}
    (f : A -> A) (m : fmap A V) i :
  BIJ f UNIV UNIV -> FLOOKUP (MAP_KEYS (LINV f UNIV) m) i = FLOOKUP m (f i).
Proof.
  intros HB; rewrite <- (LINV_DEF f UNIV UNIV (proj1 HB) i Logic.I) at 1.
  apply FLOOKUP_MAP_KEYS_MAPPED, (proj1 (BIJ_LINV_BIJ f UNIV UNIV HB)).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "word_to_stack_good_code_lemma" *)
Theorem word_to_stack_good_code_lemma {B C : Type} (mc : machine_config a B C)
    (c : backend.config) pan_code col wprog bitmaps c'' fs p :
  word_to_word.compile (backend.word_to_word_conf c) (asmProps.config (target mc))
    (pan_to_word.compile_prog (ISA (asmProps.config (target mc))) pan_code) = (col,wprog) /\
  ISA (asmProps.config (target mc)) <> Ag32 /\
  word_to_stack.compile (asmProps.config (target mc)) false wprog = (bitmaps,(c'',(fs,p))) /\
  LENGTH (avoid_regs (asmProps.config (target mc))) + 13 <= reg_count (asmProps.config (target mc)) /\
  ALL_DISTINCT (MAP FST (functions pan_code)) ->
  stack_to_labProof.good_code (reg_count (asmProps.config (target mc)) -
    (LENGTH (avoid_regs (asmProps.config (target mc))) + 3)) p.
Proof.
  intros (Hw & HI & Hs & HB & HD).
  set (ac := asmProps.config (target mc)) in *.
  set (ps := pan_to_word.compile_prog (ISA ac) pan_code) in *.
  assert (HS : EVERY (fun '(_, (_, prg)) => bool_decide (wordConvs.no_share_inst prg \/ ISA ac <> Ag32)) ps).
  { apply EVERY_Forall; apply Forall_forall; intros [n [m prg]] _; apply bool_decide_spec; auto. }
  destruct (backendProof.compile_to_word_conventions2 _ _ _ _ _ (conj Hw HS)) as [HN [HR HC]].
  assert (HA : EVERY (wordConvs.post_alloc_conventions (reg_count ac - (5 + LENGTH (avoid_regs ac))))
      (MAP (fun x => SND (SND x)) wprog)).
  { apply EVERY_Forall; rewrite Forall_map; apply EVERY_Forall in HC.
    eapply Forall_impl; [|exact HC]; intros [n [m prg]] HE.
    apply bool_decide_spec in HE; exact (proj1 (proj2 HE)). }
  set (k := reg_count ac - (5 + LENGTH (avoid_regs ac))).
  assert (Hk : 4 <= k) by (unfold k; lia).
  destruct (syntax.word_to_stack_stack_convs ac wprog bitmaps c'' fs p k
    (conj Hs (conj HA (conj eq_refl Hk)))) as [Halloc [Hreg Hcall]].
  destruct (pan_to_stack_compile_lab_pres mc c pan_code ps col wprog bitmaps c'' fs p
    (conj eq_refl (conj Hw (conj HI (conj Hs HD))))) as [Hdistinct [Hnum Hlabels]].
  unfold stack_to_labProof.good_code; split; [exact Hdistinct|]. split.
  - apply EVERY_Forall; apply EVERY_Forall in Halloc; rewrite Forall_map, Forall_forall in Halloc.
    apply Forall_forall; intros [n prg] Hin; apply andb_true_iff; split; [|exact (Halloc _ Hin)].
    assert (Hmem : In n (MAP FST p)) by (apply in_map_iff; exists (n,prg); auto).
    rewrite (word_to_stack_compile_FST mc _ _ _ _ _ Hs), HN in Hmem.
    cbn [In] in Hmem; destruct Hmem as [Hn|[Hn|Hn]].
    + subst n; reflexivity.
    + subst n; reflexivity.
    + apply in_map_iff in Hn as [x [<- Hx]].
      pose proof (pan_to_wordProof.pan_to_word_compile_prog_lab_min (ISA ac) pan_code ps eq_refl) as HM.
      apply EVERY_Forall in HM; rewrite Forall_forall in HM; specialize (HM x Hx).
      apply N.leb_le in HM; apply N.leb_le; change (5 <= FST x); lia.
  - split; [exact Hcall|]. split; [|exact Hlabels].
    replace (reg_count ac - (LENGTH (avoid_regs ac) + 3)) with (k + 2) by (unfold k; lia).
    exact Hreg.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "good_dimindex_0w_8w" *)
Theorem good_dimindex_0w_8w : good_dimindex a ->
  word_le (n2w 0 : word a) (n2w 8) /\ word_le (word_2comp (n2w 8 : word a)) (n2w 0).
Proof.
  intros H; unfold good_dimindex, dimindex in H.
  assert (a = 32 \/ a = 64) as HA by lia; destruct HA as [HA|HA]; subst a; vm_compute; auto.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "pan_installed_def" *)
Definition pan_installed {B C : Type} (bytes : list word8) (cbspace : N)
    (bitmaps : list (word a)) (data_sp : N) ffi_names (rs : N * N)
    (mc : machine_config a B C) (shmem_extra : list lab_to_target.shmem_info_num)
    (ms : B) (p_mem : word a -> wordLang.word_loc a) (p_dom sdm' : word a -> Prop) : Prop :=
  let '(r1,r2) := rs in
  exists (t : asm_state a) m bitmap_ptr bitmaps_dm sdm,
  let heap_stack_dm := fun w => word_ls (regs t r1) w /\ word_lo w (regs t r2) in
  (forall ad, ad IN p_dom -> m ad = p_mem ad) /\
  good_init_state mc ms bytes cbspace t m (heap_stack_dm UNION bitmaps_dm) sdm /\
  sdm' = sdm INTER (fun w => byte_aligned w) /\
  byte_aligned (regs t r1) /\ byte_aligned (regs t r2) /\ byte_aligned bitmap_ptr /\
  word_ls (regs t r1) (regs t r2) /\
  word_ls (n2w 1024 * bytes_in_word)%w (regs t r2 - regs t r1)%w /\
  DISJOINT heap_stack_dm bitmaps_dm /\
  m (regs t r1) = wordLang.Word bitmap_ptr /\
  m (regs t r1 + bytes_in_word)%w = wordLang.Word (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps))%w /\
  m (regs t r1 + n2w 2 * bytes_in_word)%w = wordLang.Word
    (bitmap_ptr + bytes_in_word * n2w data_sp + bytes_in_word * n2w (LENGTH bitmaps))%w /\
  m (regs t r1 + n2w 3 * bytes_in_word)%w = wordLang.Word (get_pc (target mc) ms + n2w (LENGTH bytes))%w /\
  m (regs t r1 + n2w 4 * bytes_in_word)%w = wordLang.Word (get_pc (target mc) ms + n2w cbspace + n2w (LENGTH bytes))%w /\
  STAR (word_list bitmap_ptr (MAP wordLang.Word bitmaps))
    (word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps))%w data_sp)
    (fun2set (m, (fun w => byte_aligned w) INTER bitmaps_dm)) /\
  ffi_names = SOME (targetSem.ffi_names mc) /\
  (forall i, mmio_pcs_min_index (targetSem.ffi_names mc) = SOME i ->
    MAP (fun rec => w2n (get_pc (target mc) ms) + lab_to_target.entry_pc rec) shmem_extra =
      DROP i (MAP w2n (ffi_entry_pcs mc)) /\
    mmio_info mc = ZIP (GENLIST (fun index => index + i) (LENGTH shmem_extra),
      MAP (fun rec => (lab_to_target.nbytes rec,
        (Addr (lab_to_target.addr_reg rec) (n2w (lab_to_target.addr_off rec)),
         (lab_to_target.reg rec, (n2w (lab_to_target.exit_pc rec) + get_pc (target mc) ms)%w)))) shmem_extra) /\
    cbspace + LENGTH bytes + lab_to_target.ffi_offset * (i + 3) < dimword a).

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "pan_installed_imp_installed" *)
Theorem pan_installed_imp_installed {B C : Type} bytes cbspace bitmaps data_sp ffi_names r1 r2
    (mc : machine_config a B C) shmem_extra ms p_mem p_dom sdm :
  pan_installed bytes cbspace bitmaps data_sp ffi_names (r1,r2) mc shmem_extra ms p_mem p_dom sdm ->
  installed bytes cbspace bitmaps data_sp ffi_names (r1,r2) mc shmem_extra ms.
Proof.
  unfold pan_installed, installed; cbn beta iota zeta.
  intros [t [m [ptr [dm [sdm0 H]]]]]; exists t, m, ptr, dm, sdm0; tauto.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "compile_prog_max_def" *)
Definition compile_prog_max {B C : Type} (c : backend.config)
    (mc : machine_config a B C) (prog : list (decl a)) :=
  let asm_conf := asmProps.config (target mc) in
  let prog := pan_to_word.compile_prog (ISA asm_conf) prog in
  let '(col, wprog) := word_to_word.compile (backend.word_to_word_conf c) asm_conf prog in
  let '(bm, (c', (fs, p))) := word_to_stack.compile asm_conf false wprog in
  let max := word_depth.max_depth (word_to_stack.stack_frame_size c')
    (word_depth.full_call_graph bvl_to_bvi.InitGlobals_location (fromAList wprog)) in
  (backend.from_stack asm_conf c LN p bm, max).

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "good_dimindex_div_mul" *)
Theorem good_dimindex_div_mul : good_dimindex a -> forall n,
  n * dimindex a DIV 8 = n * (dimindex a DIV 8).
Proof. intros [H|H] n; rewrite H; cbn [dimindex]; nia. Qed.

End Composition.

Local Opaque stack_rawcall.compile stack_alloc.compile stack_remove.compile stack_names.compile.
Section Initialisation.
Context {a : N} {c ffi_t : Type}.
Local Lemma make_init_any_be ggc mh bm dsp co jump off sp cd
    (s : stackSem.state a c ffi_t) :
  stackSem.be (stack_removeProof.make_init_any ggc mh bm dsp co jump off sp cd s) = stackSem.be s.
Proof.
  unfold stack_removeProof.make_init_any, stack_removeProof.make_init_opt.
  destruct (stackSem.evaluate _) as [[r|] t] eqn:E; [reflexivity|].
  destruct (classical_dec _); [|reflexivity].
  cbn [stack_removeProof.init_reduce stackSem.be].
  exact (proj1 (proj2 (proj2 (proj2 (stackProps.evaluate_consts _ _ _ _ E))))).
Qed.

Local Lemma stack_alloc_init_be dc cd co (s : stackSem.state a c ffi_t) :
 stackSem.be (stack_allocProof.make_init dc cd co s) = stackSem.be s.
Proof. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "full_make_init_be" *)
Theorem full_make_init_be sc dc mh sp off bm code0 (s : labSem.state a c ffi_t) save dsp co :
  stackSem.be (FST (stack_to_labProof.full_make_init sc dc mh sp off bm code0 s save dsp co)) <-> labSem.be s.
Proof.
  unfold stack_to_labProof.full_make_init; cbn [FST fst].
  rewrite stack_alloc_init_be, make_init_any_be; reflexivity.
Qed.
End Initialisation.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "option_lt_def" *)
Definition option_lt (n0 n1 : option N) : Prop :=
  match n0, n1 with _, NONE => True | NONE, SOME _ => False
  | SOME n1, SOME n2 => n1 < n2 end.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "option_lt_SOME" *)
Theorem option_lt_SOME : forall x n,
  option_lt x (SOME n) <-> exists m, x = SOME m /\ m < n.
Proof. intros [m|] n; cbn [option_lt]; split; intros H; try contradiction.
  - exists m; auto.
  - destruct H as [k [H Hk]]; inversion H; subst; exact Hk.
  - destruct H as [k [H _]]; discriminate.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "InitGlobals_location_eq_first_name" *)
Theorem InitGlobals_location_eq_first_name :
  bvl_to_bvi.InitGlobals_location = crep_to_loop.first_name.
Proof. reflexivity. Qed.

Section Memory.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (wordSem.state a c ffi_t).

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "fun2set_update_eq" *)
Theorem fun2set_update_eq {A B : Type} `{EqDecision A} (m m' : A -> B) md x v :
  fun2set (m, md) = fun2set (m', md) ->
  fun2set ((x =+ v) m, md) = fun2set ((x =+ v) m', md).
Proof.
  rewrite !fun2set_eq; intros HE i Hi; rewrite !APPLY_UPDATE_THM.
  destruct (decide (x = i)); auto.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "get_var_const_memory" *)
Theorem get_var_const_memory x (y : state) m :
  wordSem.get_var x (wordSem.set_memory m y) = wordSem.get_var x y.
Proof. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "set_var_const_memory" *)
Theorem set_var_const_memory v x (y : state) m :
  wordSem.set_var v x (wordSem.set_memory m y) =
  wordSem.set_memory m (wordSem.set_var v x y).
Proof. destruct y; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "unset_var_const_memory" *)
Theorem unset_var_const_memory v (y : state) m :
  wordSem.unset_var v (wordSem.set_memory m y) =
  wordSem.set_memory m (wordSem.unset_var v y).
Proof. destruct y; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "get_vars_const_memory" *)
Theorem get_vars_const_memory x (y : state) m :
  wordSem.get_vars x (wordSem.set_memory m y) = wordSem.get_vars x y.
Proof. induction x as [|v vs IH]; cbn [wordSem.get_vars]; rewrite ?get_var_const_memory, ?IH; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "set_vars_const_memory" *)
Theorem set_vars_const_memory vs xs (y : state) m :
  wordSem.set_vars vs xs (wordSem.set_memory m y) =
  wordSem.set_memory m (wordSem.set_vars vs xs y).
Proof. destruct y; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "get_var_imm_const_memory" *)
Theorem get_var_imm_const_memory ri (s : state) m :
  wordSem.get_var_imm ri (wordSem.set_memory m s) = wordSem.get_var_imm ri s.
Proof. destruct ri; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "mem_load_const_memory" *)
Theorem mem_load_const_memory ad (s : state) m :
  fun2set (wordSem.memory s, wordSem.mdomain s) = fun2set (m, wordSem.mdomain s) ->
  wordSem.mem_load ad (wordSem.set_memory m s) = wordSem.mem_load ad s.
Proof.
  intros H; pose proof (proj1 (fun2set_eq _ _ _) H) as HE; unfold wordSem.mem_load; cbn [wordSem.mdomain wordSem.set_memory].
  destruct (classical_dec _); [rewrite HE by assumption|]; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "mem_store_const_memory" *)
Theorem mem_store_const_memory ad w (s : state) m :
  fun2set (wordSem.memory s, wordSem.mdomain s) = fun2set (m, wordSem.mdomain s) ->
  (wordSem.mem_store ad w s = NONE <->
   wordSem.mem_store ad w (wordSem.set_memory m s) = NONE) /\
  (wordSem.mem_store ad w s = SOME (wordSem.set_memory ((ad =+ w) (wordSem.memory s)) s) <->
   wordSem.mem_store ad w (wordSem.set_memory m s) = SOME (wordSem.set_memory ((ad =+ w) m) s)).
Proof.
  intros _; unfold wordSem.mem_store; cbn [wordSem.mdomain wordSem.set_memory].
  destruct (classical_dec _); destruct s; cbn; intuition congruence.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "mem_load_32_const_memory" *)
Theorem mem_load_32_const_memory (m m' : word a -> wordLang.word_loc a) dm be ad :
  fun2set (m, dm) = fun2set (m', dm) ->
  wordSem.mem_load_32 m dm be ad = wordSem.mem_load_32 m' dm be ad.
Proof.
  intros H; pose proof (proj1 (fun2set_eq _ _ _) H) as HE; unfold wordSem.mem_load_32.
  destruct (aligned 2 ad); [|reflexivity].
  destruct (classical_dec (byte_align ad IN dm)) as [Hd|Hd].
  - rewrite HE by exact Hd; reflexivity.
  - destruct (m (byte_align ad)), (m' (byte_align ad)); reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "mem_store_32_const_memory" *)
Theorem mem_store_32_const_memory (m m' : word a -> wordLang.word_loc a) dm be ad hw :
  fun2set (m, dm) = fun2set (m', dm) ->
  (wordSem.mem_store_32 m dm be ad hw = NONE <-> wordSem.mem_store_32 m' dm be ad hw = NONE) /\
  fun2set (THE (wordSem.mem_store_32 m dm be ad hw), dm) =
  fun2set (THE (wordSem.mem_store_32 m' dm be ad hw), dm).
Proof.
  intros H; pose proof (proj1 (fun2set_eq m m' dm) H) as HE.
  unfold wordSem.mem_store_32; destruct (aligned 2 ad); [|split; reflexivity].
  destruct (classical_dec (byte_align ad IN dm)) as [Hd|Hd].
  - rewrite <- HE by exact Hd; destruct (m (byte_align ad)); cbn [THE].
    + split; [split; discriminate|apply fun2set_update_eq; exact H].
    + split; reflexivity.
  - destruct (m (byte_align ad)), (m' (byte_align ad)); split; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "word_exp_const_memory" *)
Theorem word_exp_const_memory : forall (s : state) exp m,
  fun2set (wordSem.memory s, wordSem.mdomain s) = fun2set (m, wordSem.mdomain s) ->
  wordSem.word_exp (wordSem.set_memory m s) exp = wordSem.word_exp s exp.
Proof.
  intros s exp m H.
  induction exp as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using wordConvs.exp_nested_ind;
    cbn [wordSem.word_exp]; try reflexivity.
  - rewrite IH; destruct (wordSem.word_exp s e) as [[w|? ?]|]; try reflexivity.
    apply mem_load_const_memory; exact H.
  - assert (HM : MAP (wordSem.word_exp (wordSem.set_memory m s)) es = MAP (wordSem.word_exp s) es).
    { induction IH as [|x xs Hx Hxs IHL]; cbn [MAP List.map]; [reflexivity|]. rewrite Hx, IHL; reflexivity. }
    rewrite HM; reflexivity.
  - rewrite IH1, IH2; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "mem_load_byte_aux_const_memory" *)
Theorem mem_load_byte_aux_const_memory (m m' : word a -> wordLang.word_loc a) dm be w :
  fun2set (m, dm) = fun2set (m', dm) ->
  wordSem.mem_load_byte_aux m' dm be w = wordSem.mem_load_byte_aux m dm be w.
Proof.
  intros H; pose proof (proj1 (fun2set_eq _ _ _) H) as HE; unfold wordSem.mem_load_byte_aux.
  destruct (classical_dec (byte_align w IN dm)) as [Hd|Hd].
  - rewrite HE by exact Hd; reflexivity.
  - destruct (m (byte_align w)), (m' (byte_align w)); reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "mem_store_byte_aux_const_memory" *)
Theorem mem_store_byte_aux_const_memory (m m' : word a -> wordLang.word_loc a) dm be w b :
  fun2set (m, dm) = fun2set (m', dm) ->
  (wordSem.mem_store_byte_aux m dm be w b = NONE <-> wordSem.mem_store_byte_aux m' dm be w b = NONE) /\
  fun2set (THE (wordSem.mem_store_byte_aux m' dm be w b), dm) =
  fun2set (THE (wordSem.mem_store_byte_aux m dm be w b), dm).
Proof.
  intros H; pose proof (proj1 (fun2set_eq m m' dm) H) as HE.
  unfold wordSem.mem_store_byte_aux.
  destruct (classical_dec (byte_align w IN dm)) as [Hd|Hd].
  - rewrite <- HE by exact Hd; destruct (m (byte_align w)); cbn [THE].
    + split; [split; discriminate|symmetry; apply fun2set_update_eq; exact H].
    + split; reflexivity.
  - destruct (m (byte_align w)), (m' (byte_align w)); split; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "read_bytearray_const_memory" *)
Theorem read_bytearray_const_memory (m m' : word a -> wordLang.word_loc a) dm ptr len be :
  fun2set (m, dm) = fun2set (m', dm) ->
  read_bytearray ptr len (wordSem.mem_load_byte_aux m dm be) =
  read_bytearray ptr len (wordSem.mem_load_byte_aux m' dm be).
Proof.
  intros H; f_equal; apply functional_extensionality; intros w.
  symmetry; apply mem_load_byte_aux_const_memory; exact H.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "write_bytearray_const_memory" *)
Theorem write_bytearray_const_memory : forall ls ptr (m m' : word a -> wordLang.word_loc a) dm be,
  fun2set (m, dm) = fun2set (m', dm) ->
  fun2set (wordSem.write_bytearray ptr ls m dm be, dm) =
  fun2set (wordSem.write_bytearray ptr ls m' dm be, dm).
Proof.
  induction ls as [|b bs IH]; intros ptr m m' dm be H; cbn [wordSem.write_bytearray]; [exact H|].
  pose proof (IH (ptr + n2w 1)%w m m' dm be H) as HT.
  pose proof (mem_store_byte_aux_const_memory _ _ _ be ptr b HT) as [HN HE].
  destruct (wordSem.mem_store_byte_aux (wordSem.write_bytearray (ptr + n2w 1)%w bs m dm be) dm be ptr b) eqn:E;
  destruct (wordSem.mem_store_byte_aux (wordSem.write_bytearray (ptr + n2w 1)%w bs m' dm be) dm be ptr b) eqn:E';
    try (exfalso; intuition discriminate).
  - cbn [THE] in HE; symmetry; exact HE.
  - exact H.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "const_writes_const_memory" *)
Theorem const_writes_const_memory : forall c' off words (m m' : word a -> wordLang.word_loc a) md,
  fun2set (m, md) = fun2set (m', md) ->
  fun2set (wordSem.const_writes c' off words m, md) =
  fun2set (wordSem.const_writes c' off words m', md).
Proof.
  intros c' off words; revert c'; induction words as [|[b w] ws IH]; intros c' m m' md H;
    cbn [wordSem.const_writes]; [exact H|]. apply IH, fun2set_update_eq; exact H.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "mem_upd_lemma" *)
Local Theorem mem_upd_lemma (s t : state) :
  wordSem.set_memory ARB s = wordSem.set_memory ARB t ->
  exists m, s = wordSem.set_memory m t.
Proof.
  intros H; exists (wordSem.memory s); destruct s, t; cbn in H |- *.
  inversion H; reflexivity.
Qed.

Local Ltac share_unfold :=
  unfold wordSem.share_inst, wordSem.sh_mem_set_var, wordSem.sh_mem_load,
    wordSem.sh_mem_load_byte, wordSem.sh_mem_load16, wordSem.sh_mem_load32,
    wordSem.sh_mem_store, wordSem.sh_mem_store_byte, wordSem.sh_mem_store16,
    wordSem.sh_mem_store32 in *.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "share_inst_const_memory" *)
Theorem share_inst_const_memory : forall (s : state) op v ad m res t,
  fun2set (wordSem.memory s, wordSem.mdomain s) = fun2set (m, wordSem.mdomain s) /\
  wordSem.share_inst op v ad s = (res,t) ->
  wordSem.memory t = wordSem.memory s /\ wordSem.mdomain t = wordSem.mdomain s /\
  wordSem.share_inst op v ad (wordSem.set_memory m s) = (res,wordSem.set_memory m t).
Proof.
  intros s op v ad m res t [_ HE]; destruct op; share_unfold; unfold wordSem.get_var in *;
    cbn [wordSem.get_var wordSem.locals wordSem.ffi wordSem.sh_mdomain wordSem.set_memory] in *;
    wordSem.split_H HE; consts.leaf HE;
    unfold wordSem.get_var in *; cbn [wordSem.locals] in *;
    repeat match goal with E : ?x = _ |- context [?x] => rewrite E end;
    repeat split; try reflexivity; destruct s; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "push_env_mem_upd" *)
Local Theorem push_env_mem_upd : forall env params (s : state) m,
  wordSem.push_env env params (wordSem.set_memory m s) =
  wordSem.set_memory m (wordSem.push_env env params s).
Proof.
  intros env [[w [p [l1 l2]]]|] s m; unfold wordSem.push_env;
  cbn [wordSem.permute wordSem.set_memory];
  destruct (wordSem.env_to_list _ _) as [l perm]; destruct s; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "push_env_mem_const" *)
Local Theorem push_env_mem_const : forall env params (s : state),
  wordSem.memory (wordSem.push_env env params s) = wordSem.memory s /\
  wordSem.mdomain (wordSem.push_env env params s) = wordSem.mdomain s.
Proof.
  intros env [[w [p [l1 l2]]]|] s; unfold wordSem.push_env;
  destruct (wordSem.env_to_list _ _) as [l perm]; split; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "cut_state_with_mem_const" *)
Local Theorem cut_state_with_mem_const x (s : state) m :
  wordSem.cut_state x (wordSem.set_memory m s) =
  OPTION_MAP (fun s' => wordSem.set_memory m s') (wordSem.cut_state x s).
Proof.
  unfold wordSem.cut_state; cbn [wordSem.locals wordSem.set_memory].
  destruct (wordSem.cut_env _ _); cbn [OPTION_MAP]; [destruct s|]; reflexivity.
Qed.

End Memory.

Section StackBounds.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (wordSem.state a c ffi_t).

Local Lemma inst_stack_fields i (s t : state) : wordSem.inst i s = SOME t ->
  wordSem.state_stack_size t = wordSem.state_stack_size s /\
  wordSem.stack_limit t = wordSem.stack_limit s /\
  wordSem.stack_max t = wordSem.stack_max s.
Proof.
  intros H; destruct i as [|r w|ar|m r [ad w]|f];
    [|cbn [wordSem.inst] in H|destruct ar|destruct m|destruct f];
    cbn [wordSem.inst] in H; unfold wordSem.assign in H;
    wordSem.split_H H; consts.leaf H;
    repeat match goal with E : wordSem.mem_store _ _ _ = SOME _ |- _ =>
      apply consts.mem_store_const in E end;
    consts.destr_conj; unfold wordSem.set_var, wordSem.set_vars, wordSem.set_fp_var in *;
    consts.unfold_sets; repeat split; congruence.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "inst_stack_size_const_panLang" *)
Theorem inst_stack_size_const_panLang : forall i (s t : state),
  wordSem.inst i s = SOME t -> wordSem.state_stack_size t = wordSem.state_stack_size s.
Proof. intros i s t H; exact (proj1 (inst_stack_fields i s t H)). Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "inst_stack_limit_const_panLang" *)
Theorem inst_stack_limit_const_panLang : forall i (s t : state),
  wordSem.inst i s = SOME t -> wordSem.stack_limit t = wordSem.stack_limit s.
Proof. intros i s t H; exact (proj1 (proj2 (inst_stack_fields i s t H))). Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "inst_stack_max_const_panLang" *)
Theorem inst_stack_max_const_panLang : forall i (s t : state),
  wordSem.inst i s = SOME t -> wordSem.stack_max t = wordSem.stack_max s.
Proof. intros i s t H; exact (proj2 (proj2 (inst_stack_fields i s t H))). Qed.

End StackBounds.

Section SharedInstructions.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (wordSem.state a c ffi_t).

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "share_inst_modifies" *)
Theorem share_inst_modifies op v ad (s t : state) res :
  wordSem.share_inst op v ad s = (res,t) ->
  exists ls ffi stk lsz st,
    t = wordSem.set_store_field st (wordSem.set_locals_size lsz (wordSem.set_stack stk
      (wordSem.set_ffi ffi (wordSem.set_locals ls s)))).
Proof.
  intros HE; exists (wordSem.locals t), (wordSem.ffi t), (wordSem.stack t),
    (wordSem.locals_size t), (wordSem.store t).
  destruct op; unfold wordSem.share_inst, wordSem.sh_mem_set_var, wordSem.sh_mem_load,
    wordSem.sh_mem_load_byte, wordSem.sh_mem_load16, wordSem.sh_mem_load32,
    wordSem.sh_mem_store, wordSem.sh_mem_store_byte, wordSem.sh_mem_store16,
    wordSem.sh_mem_store32 in HE;
  wordSem.split_H HE; consts.leaf HE; destruct s; reflexivity.
Qed.

Local Lemma share_inst_no_space op v ad (s t : state) res :
  wordSem.share_inst op v ad s = (res,t) -> res <> SOME wordSem.NotEnoughSpace.
Proof.
  intros HE; destruct op; unfold wordSem.share_inst, wordSem.sh_mem_set_var, wordSem.sh_mem_load,
    wordSem.sh_mem_load_byte, wordSem.sh_mem_load16, wordSem.sh_mem_load32,
    wordSem.sh_mem_store, wordSem.sh_mem_store_byte, wordSem.sh_mem_store16,
    wordSem.sh_mem_store32 in HE;
  wordSem.split_H HE; consts.leaf HE; discriminate.
Qed.

End SharedInstructions.

Section CompilationSafety.
Context {a : N}.

Local Lemma compile_single_code_pred P t rc alg (ac : asm_config a) ps orc :
  ALL_DISTINCT (MAP FST ps) ->
  (forall k n p, lookup k (fromAList ps) = SOME (n,p) -> wordConvs.not_created_subprogs P p) ->
  forall k n p,
    lookup k (fromAList (MAP (word_to_word.compile_single t rc alg ac) (ZIP (ps,orc)))) = SOME (n,p) ->
    wordConvs.not_created_subprogs P p.
Proof.
  intros HD HP k n p H; rewrite lookup_fromAList in H.
  apply ALOOKUP_MEM in H; apply MEM_In in H; apply in_map_iff in H as [x [Hx Hin]].
  destruct x as [[k0 [n0 p0]] o].
  pose proof (wordConvsProof.compile_single_not_created_subprogs P t rc alg ac ((k0,(n0,p0)),o)) as HC.
  cbn [FST fst SND snd] in HC; rewrite Hx in HC; cbn [SND snd] in HC; apply HC.
  apply (HP k0 n0 p0); rewrite lookup_fromAList; apply ALOOKUP_NoDup_In.
  - apply ALL_DISTINCT_NoDup_list; exact HD.
  - unfold ZIP in Hin; eapply in_combine_l; exact Hin.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "word_to_word_compile_no_install_no_alloc" *)
Theorem word_to_word_compile_no_install_no_alloc (wc : word_to_word.config) (ac : asm_config a)
    progs0 col progs :
  word_to_word.compile wc ac progs0 = (col,progs) /\
  ALL_DISTINCT (MAP FST progs0) /\ code.no_mt_code (fromAList progs0) /\
  code.no_install_code (fromAList progs0) ->
  code.no_install_code (fromAList progs) /\
  (code.no_alloc_code (fromAList progs0) -> code.no_alloc_code (fromAList progs)).
Proof.
  intros (HC & HD & HM & HNI).
  pose proof (word_to_wordProof.LENGTH_next_n_oracle (LENGTH progs0) (word_to_word.col_oracle wc)) as HL.
  unfold word_to_word.compile in HC.
  destruct (word_to_word.next_n_oracle _ _) as [orc col0] eqn:EO; cbn [fst] in HL.
  change ((col0, MAP (word_to_word.full_compile_single (two_reg_arith ac)
    (reg_count ac - (5 + LENGTH (avoid_regs ac))) (word_to_word.reg_alg wc) ac) (ZIP (progs0, orc))) = (col,progs)) in HC.
  assert (Hw : progs = MAP (word_to_word.full_compile_single (two_reg_arith ac)
    (reg_count ac - (5 + LENGTH (avoid_regs ac))) (word_to_word.reg_alg wc) ac) (ZIP (progs0, orc))) by congruence.
  rewrite Hw; clear HC.
  rewrite word_to_wordProof.no_mt_code_full_compile_single by (repeat split; assumption).
  split; unfold code.no_install_code, code.no_alloc_code, wordConvs.no_install, wordConvs.no_alloc in *.
  - eapply compile_single_code_pred; eassumption.
  - intros HA; eapply compile_single_code_pred; eassumption.
Qed.

End CompilationSafety.

Section NoSpace.
Import wordSem wordConvs consts clock consts_with code.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (wordSem.state a c ffi_t).
Local Ltac safety_code_facts :=
  repeat match goal with
         | E : alloc _ _ _ = (_, _) |- _ => apply alloc_const in E
         | E : inst _ _ = SOME _ |- _ => apply inst_const_full in E
         | E : mem_store _ _ _ = SOME _ |- _ => apply mem_store_const in E
         | E : jump_exc _ = SOME (_, _) |- _ => apply jump_exc_const in E
         | E : share_inst _ _ _ _ = (_, _) |- _ => apply share_inst_const in E
         | E : pop_env _ = SOME _ |- _ => apply pop_env_const in E
         | E : cut_state _ _ = SOME _ |- _ =>
             let l := fresh "l" in apply cut_state_const in E; destruct E as [l ->]
         end;
  repeat match goal with
         | |- context [push_env ?x ?y ?z] =>
             lazymatch goal with
             | _ : clock (push_env x y z) = _ |- _ => fail
             | _ => pose proof (push_env_const x y z); destr_conj
             end
         | H : context [push_env ?x ?y ?z] |- _ =>
             lazymatch goal with
             | _ : clock (push_env x y z) = _ |- _ => fail
             | _ => pose proof (push_env_const x y z); destr_conj
             end
         end;
  destr_conj;
  unfold flush_state, dec_clock, call_env, set_var, set_vars, unset_var, set_store in *;
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  cbn [fst snd] in *; unfold_sets.



(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "no_alloc_word_evaluate" *)
Theorem no_alloc_word_evaluate : forall prog (s : state) res t,
 wordSem.evaluate (prog,s) = (res,t) /\
 code.no_install_code (wordSem.code s) /\ code.no_alloc_code (wordSem.code s) /\
 wordConvs.no_install prog /\ wordConvs.no_alloc prog -> res <> SOME wordSem.NotEnoughSpace.
Proof.
 enough (G : forall x : wordLang.prog a * state, forall r t, wordSem.evaluate x = (r,t) ->
   wordConvs.no_install (fst x) -> code.no_install_code (wordSem.code (snd x)) ->
   wordConvs.no_alloc (fst x) -> code.no_alloc_code (wordSem.code (snd x)) ->
   r <> SOME wordSem.NotEnoughSpace /\ wordSem.code (snd x) = wordSem.code t)
 by (intros p s r t (H & HNI & HNA & Hpi & Hpa); exact (proj1 (G (p,s) r t H Hpi HNI Hpa HNA))).
 intros x; induction x as [[p s] IH] using (well_founded_induction wordSem.eval_lt_wf).
 intros r t H Hpi HNI Hpa HNA; cbn [fst snd] in *.
 assert (HC : wordSem.code s = wordSem.code t) by
   (apply (code.no_install_evaluate_const_code p s r t); auto).
 split; [|exact HC].
 rewrite wordSem.evaluate_eqn in H; destruct p; cbn [wordSem.evaluate_body] in H; clock.io_step IH H;
 repeat match goal with E : (_,_) = (_,_) |- _ => injection E as <- <- end;
 repeat match goal with E : ?v = (_,_) |- _ => is_var v; subst v end;
 try (exfalso; unfold wordConvs.no_install in Hpi; cbn [wordConvs.not_created_subprogs] in Hpi; apply Hpi; reflexivity);
 try (exfalso; unfold wordConvs.no_alloc in Hpa; cbn [wordConvs.not_created_subprogs] in Hpa; apply Hpa; reflexivity);
 cbn [FST SND fst snd] in *;
 try (match goal with E : share_inst ?op ?v ?ad ?s = (?r,?t) |- _ =>
   destruct op; unfold share_inst, sh_mem_set_var, sh_mem_load, sh_mem_load_byte, sh_mem_load16, sh_mem_load32, sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32 in E; split_H E; leaf E; discriminate end);
 safety_code_facts;
 repeat multimatch goal with
 | Hi : ?A -> code.no_install_code ?cs -> ?B -> code.no_alloc_code ?cs -> _ |- _ =>
   let H1 := fresh "Hpi" in let H2 := fresh "Hpa" in
   let H3 := fresh "Hni" in let H4 := fresh "Hna" in
   assert (H1 : A) by
    (first [ eapply code.no_install_find_code; split; eassumption
           | unfold wordConvs.no_install in *; cbn [wordConvs.not_created_subprogs wordSem.STOP] in *; consts.destr_conj; assumption ]);
   assert (H2 : B) by
    (first [ eapply code.no_alloc_find_code; split; eassumption
           | unfold wordConvs.no_alloc in *; cbn [wordConvs.not_created_subprogs wordSem.STOP] in *; consts.destr_conj; assumption ]);
   assert (H3 : code.no_install_code cs) by
    (replace cs with (wordSem.code s) by congruence; assumption);
   assert (H4 : code.no_alloc_code cs) by
    (replace cs with (wordSem.code s) by congruence; assumption);
   specialize (Hi H1 H3 H2 H4); destruct Hi
 end;
 try discriminate; try congruence.
 destruct o as [r0|]; [destruct r0|]; cbn [wordSem.exit_loop]; congruence.
Qed.
(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "evaluate_stack_size_limit_const_panLang" *)
Theorem evaluate_stack_size_limit_const_panLang : forall prog (s : state) res t,
 wordSem.evaluate (prog,s) = (res,t) /\
 wordConvs.no_install prog /\ code.no_install_code (wordSem.code s) /\
 wordConvs.no_alloc prog /\ code.no_alloc_code (wordSem.code s) -> wordSem.state_stack_size t = wordSem.state_stack_size s /\ wordSem.stack_limit t = wordSem.stack_limit s.
Proof.
 enough (G : forall x : wordLang.prog a * state, forall r t, wordSem.evaluate x = (r,t) ->
   wordConvs.no_install (fst x) -> code.no_install_code (wordSem.code (snd x)) ->
   wordConvs.no_alloc (fst x) -> code.no_alloc_code (wordSem.code (snd x)) ->
   wordSem.state_stack_size t = wordSem.state_stack_size (snd x) /\ wordSem.stack_limit t = wordSem.stack_limit (snd x) /\ wordSem.code (snd x) = wordSem.code t)
 by (intros p s r t (H & Hpi & HNI & Hpa & HNA); pose proof (G (p,s) r t H Hpi HNI Hpa HNA) as [HS [HL HC]]; auto).
 intros x; induction x as [[p s] IH] using (well_founded_induction wordSem.eval_lt_wf).
 intros r t H Hpi HNI Hpa HNA; cbn [fst snd] in *.
 assert (HC : wordSem.code s = wordSem.code t) by
   (apply (code.no_install_evaluate_const_code p s r t); auto).

 rewrite wordSem.evaluate_eqn in H; destruct p; cbn [wordSem.evaluate_body] in H; clock.io_step IH H;
 repeat match goal with E : (_,_) = (_,_) |- _ => injection E as <- <- end;
 repeat match goal with E : ?v = (_,_) |- _ => is_var v; subst v end;
 try (exfalso; unfold wordConvs.no_install in Hpi; cbn [wordConvs.not_created_subprogs] in Hpi; apply Hpi; reflexivity);
 try (exfalso; unfold wordConvs.no_alloc in Hpa; cbn [wordConvs.not_created_subprogs] in Hpa; apply Hpa; reflexivity);
 cbn [FST SND fst snd] in *;
 repeat match goal with E : share_inst ?op ?v ?ad ?s = (?r,?t) |- _ =>
   destruct (share_inst_modifies op v ad s t r E) as (ls & f & stk & sz & st & ->); clear E end;
 safety_code_facts;
 repeat multimatch goal with
 | Hi : ?A -> code.no_install_code ?cs -> ?B -> code.no_alloc_code ?cs -> _ |- _ =>
   let H1 := fresh "Hpi" in let H2 := fresh "Hpa" in
   let H3 := fresh "Hni" in let H4 := fresh "Hna" in
   assert (H1 : A) by
    (first [ eapply code.no_install_find_code; split; eassumption
           | unfold wordConvs.no_install in *; cbn [wordConvs.not_created_subprogs wordSem.STOP] in *; consts.destr_conj; assumption ]);
   assert (H2 : B) by
    (first [ eapply code.no_alloc_find_code; split; eassumption
           | unfold wordConvs.no_alloc in *; cbn [wordConvs.not_created_subprogs wordSem.STOP] in *; consts.destr_conj; assumption ]);
   assert (H3 : code.no_install_code cs) by
    (replace cs with (wordSem.code s) by congruence; assumption);
   assert (H4 : code.no_alloc_code cs) by
    (replace cs with (wordSem.code s) by congruence; assumption);
   specialize (Hi H1 H3 H2 H4); consts.destr_conj
 end;
 consts.unfold_sets; repeat split; try congruence.
Qed.

End NoSpace.

Section SafetyCorollaries.
Context {a : N}.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "panLang_wordSem_neq_NotEnoughSpace" *)
Theorem panLang_wordSem_neq_NotEnoughSpace {B C cfg_t ffi_t : Type}
    (mc : machine_config a B C) (c : backend.config) pan_code col wprog
    (s t : wordSem.state a cfg_t ffi_t) start k res :
  wordSem.evaluate (wordLang.Call NONE (SOME start) [0] NONE, wordSem.set_clock k s) = (res,t) /\
  ALL_DISTINCT (MAP FST (functions pan_code)) /\
  word_to_word.compile (backend.word_to_word_conf c) (asmProps.config (target mc))
    (pan_to_word.compile_prog (ISA (asmProps.config (target mc))) pan_code) = (col,wprog) /\
  wordSem.code s = fromAList wprog -> res <> SOME wordSem.NotEnoughSpace.
Proof.
  intros (HE & HD & HC & Hcode).
  set (ps := pan_to_word.compile_prog (ISA (asmProps.config (target mc))) pan_code) in *.
  pose proof (pan_to_wordProof.first_compile_prog_all_distinct
    (ISA (asmProps.config (target mc))) pan_code HD) as Hdistinct.
  pose proof (pan_to_wordProof.pan_to_word_compile_prog_no_install_code (ISA (asmProps.config (target mc))) pan_code ps eq_refl) as HNI.
  pose proof (pan_to_wordProof.pan_to_word_compile_prog_no_alloc_code (ISA (asmProps.config (target mc))) pan_code ps eq_refl) as HNA.
  pose proof (pan_to_wordProof.pan_to_word_compile_prog_no_mt_code (ISA (asmProps.config (target mc))) pan_code ps eq_refl) as HMT.
  destruct (word_to_word_compile_no_install_no_alloc _ _ _ _ _
    (conj HC (conj Hdistinct (conj HMT HNI)))) as [HI HA].
  eapply no_alloc_word_evaluate; split; [exact HE|].
  cbn [wordSem.code wordSem.set_clock]; rewrite Hcode.
  split; [exact HI|]. split; [apply HA; exact HNA|].
  split; unfold wordConvs.no_install, wordConvs.no_alloc; cbn [wordConvs.not_created_subprogs]; repeat split; try exact Logic.I; intros H; discriminate.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "from_pan_to_lab_no_install" *)
Theorem from_pan_to_lab_no_install (ac : asm_config a) wc
    pan_code isa wprog0 col wprog bm c fs p scc dc lim regc off :
  ALL_DISTINCT (MAP FST (functions pan_code)) /\ ISA ac <> Ag32 /\
  pan_to_word.compile_prog isa pan_code = wprog0 /\
  word_to_word.compile wc ac wprog0 = (col,wprog) /\
  word_to_stack.compile ac false wprog = (bm,(c,(fs,p))) ->
  labProps.no_install (stack_to_lab.compile scc dc lim regc off p).
Proof.
  intros (HD & Hisa & HP & HW & HS).
  pose proof (pan_to_wordProof.first_compile_prog_all_distinct isa pan_code HD) as Hdistinct.
  rewrite HP in Hdistinct.
  pose proof (pan_to_wordProof.pan_to_word_compile_prog_no_install_code _ _ _ HP) as HNI.
  pose proof (pan_to_wordProof.pan_to_word_compile_prog_no_mt_code _ _ _ HP) as HMT.
  destruct (word_to_word_compile_no_install_no_alloc _ _ _ _ _
    (conj HW (conj Hdistinct (conj HMT HNI)))) as [HI HA].
  apply (stack_to_labProof.stack_to_lab_compile_no_install scc dc lim regc off p
    (stack_to_lab.compile scc dc lim regc off p)); split; [|reflexivity].
  apply (syntax.word_to_stack_compile_no_install wprog ac bm c fs p).
  split; [rewrite (word_compile_names _ _ _ _ _ Hisa HW); exact Hdistinct|]. auto.
Qed.

End SafetyCorollaries.

Section Addresses.
Context {a : N}.
Local Lemma word_list_domain {B : Type} (xs : list B) (ad : word a) S :
 word_list ad xs S -> IMAGE FST S = stack_removeProof.addresses ad (LENGTH xs).
Proof.
 revert ad S; induction xs as [|x xs IH]; intros ad S H.
 - cbn [word_list] in H; unfold emp in H; subst S.
   change (IMAGE FST (EMPTY : word a * B -> Prop) = stack_removeProof.addresses ad 0).
   rewrite (proj1 (stack_removeProof.addresses_def ad 0)).
   apply set_ext; intros w; unfold pred_set.IMAGE, pred_set.IN, pred_set.EMPTY; firstorder.
 - cbn [word_list] in H; destruct H as (u & v & [HU HD] & Hone & Htail).
   unfold one in Hone; subst u; rewrite <- HU.
   rewrite stack_removeProof.LENGTH_cons_N, (proj2 (stack_removeProof.addresses_def ad (LENGTH xs))).
   rewrite <- (IH _ _ Htail).
   apply set_ext; intros w; cbv beta delta [pred_set.IMAGE pred_set.IN pred_set.UNION pred_set.INSERT pred_set.EMPTY FST] in *.
   split.
   + intros ([ad' x'] & Hw & [HE|Hv]); [destruct HE as [HE|[]]; injection HE as -> ->; cbn in Hw; subst w; left; reflexivity|right; exists (ad',x'); auto].
   + intros [->|(p & Hp & Hv)]; [exists (ad,x); cbn; auto|exists p; auto].
Qed.
Local Lemma addresses_length_eq (ad : word a) n m : good_dimindex a ->
 n <= dimword a / (dimindex a DIV 8) -> m < dimword a / (dimindex a DIV 8) ->
 stack_removeProof.addresses ad n = stack_removeProof.addresses ad m -> n = m.
Proof.
 intros Hg Hn Hm HE.
 destruct (stack_removeProof.good_dimindex_d Hg) as [Hd Hd0].
 assert (Hinj : forall i j, i < dimword a / (dimindex a DIV 8) ->
   j < dimword a / (dimindex a DIV 8) ->
   (ad + n2w i * bytes_in_word)%w = (ad + n2w j * bytes_in_word)%w -> i = j).
 { intros i j Hi Hj Hij; unfold bytes_in_word in Hij.
   rewrite !word_mul_n2w in Hij.
   apply (f_equal (fun w => (w - ad)%w)) in Hij.
   replace ((ad + n2w (i * (dimindex a DIV 8))) - ad)%w with (n2w (i * (dimindex a DIV 8)) : word a) in Hij by stack_removeProof.wring.
   replace ((ad + n2w (j * (dimindex a DIV 8))) - ad)%w with (n2w (j * (dimindex a DIV 8)) : word a) in Hij by stack_removeProof.wring.
   apply (f_equal w2n) in Hij; rewrite !w2n_n2w in Hij.
   pose proof (N.div_mod (dimword a) (dimindex a DIV 8) ltac:(lia)) as Hdiv.
   rewrite !N.mod_small in Hij by nia.
   nia. }
 destruct (N.lt_trichotomy n m) as [Hlt|[Heq|Hgt]]; [|exact Heq|].
 - assert (Hin : stack_removeProof.addresses ad m (ad + n2w n * bytes_in_word)%w).
   { rewrite stack_removeProof.addresses_thm; exists n; auto. }
   rewrite <- HE, stack_removeProof.addresses_thm in Hin.
   destruct Hin as [i [Hi Hin]]; assert (i=n) by (apply Hinj; try lia; symmetry; exact Hi); lia.
 - assert (Hin : stack_removeProof.addresses ad n (ad + n2w m * bytes_in_word)%w).
   { rewrite stack_removeProof.addresses_thm; exists m; auto. }
   rewrite HE, stack_removeProof.addresses_thm in Hin.
   destruct Hin as [i [Hi Hin]]; assert (i=m) by (apply Hinj; try lia; symmetry; exact Hi); lia.
Qed.
(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "word_list_exists_addresses" *)
Theorem word_list_exists_addresses (ad : word a) n (d : word a -> wordLang.word_loc a) m :
 word_list_exists ad n (fun2set (d, stack_removeProof.addresses ad m)) /\ good_dimindex a /\
 m < dimword a / w2n (bytes_in_word : word a) -> n = m.
Proof.
 intros (HW & Hg & Hm); unfold word_list_exists, SEP_EXISTS in HW.
 destruct HW as [xs HW]. apply (proj2 (cond_STAR _ _ _)) in HW as [HL HW].
 pose proof (stack_removeProof.word_list_len_bound xs ad emp d (stack_removeProof.addresses ad m) Hg) as Hbound.
 rewrite stack_removeProof.STAR_emp_r' in Hbound; specialize (Hbound HW).
 pose proof (word_list_domain xs ad _ HW) as Hdom.
 assert (Hd : IMAGE FST (fun2set (d,stack_removeProof.addresses ad m)) = stack_removeProof.addresses ad m).
 { apply set_ext; intros w; cbv beta delta [pred_set.IMAGE FST fun2set pred_set.IN]. split.
   - intros ([x y] & HE & z & Hpair & HZ); cbn in HE; inversion Hpair; subst; exact HZ.
   - intros Hw; exists (w,d w); split; [reflexivity|exists w; auto]. }
 rewrite Hd in Hdom; rewrite HL in Hbound, Hdom.
 apply (addresses_length_eq ad n m Hg Hbound); [rewrite <- (proj1 (stack_removeProof.good_dimindex_d Hg)); exact Hm|symmetry; exact Hdom].
Qed.
End Addresses.

Section InstMemory.
Import wordSem.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (wordSem.state a c ffi_t).
(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "inst_const_memory" *)
Theorem inst_const_memory `{Hinh : Inhabited state} i (s : state) m :
 fun2set (memory s,mdomain s) = fun2set (m,mdomain s) ->
 (inst i s = NONE <-> inst i (set_memory m s) = NONE) /\
 (inst i s <> NONE -> exists m', THE (inst i (set_memory m s)) = set_memory m' (THE (inst i s)) /\
   let x := THE (inst i s) in fun2set (memory x,mdomain x) = fun2set (m',mdomain x)).
Proof.
 intros HM;
 assert (HBL : forall w, mem_load_byte_aux m (mdomain s) (be s) w = mem_load_byte_aux (memory s) (mdomain s) (be s) w) by (intros; apply mem_load_byte_aux_const_memory; exact HM);
 assert (HL32 : forall w, mem_load_32 m (mdomain s) (be s) w = mem_load_32 (memory s) (mdomain s) (be s) w) by (intros; symmetry; apply mem_load_32_const_memory; exact HM);
 destruct i as [|r w|ar|mop r [ad w]|f];
 [| |destruct ar|destruct mop|destruct f];
 unfold inst, assign;
 rewrite ?word_exp_const_memory by exact HM;
 rewrite ?get_vars_const_memory, ?get_var_const_memory;
 rewrite ?mem_load_const_memory by exact HM;
 assert (HGFP : forall v, get_fp_var v (set_memory m s) = get_fp_var v s) by (intros; reflexivity);
 rewrite ?HGFP;
 cbn [fp_regs set_memory get_var_imm memory mdomain be];
 rewrite ?mem_load_32_const_memory by exact HM;
 rewrite <- ?mem_load_byte_aux_const_memory by exact HM;
 rewrite ?get_var_const_memory;
 unfold mem_store; cbn [mdomain set_memory];
 repeat first [
 progress rewrite ?mem_load_const_memory by exact HM
 | progress rewrite ?HL32, ?HBL
 | match goal with |- context [match ?x with _ => _ end] =>
   let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta end ];
 cbn [THE];
 try (split; [reflexivity|intros Hnone; exfalso; apply Hnone; reflexivity]);
 try (split; [split; discriminate|intros _; eexists; split; [destruct s; reflexivity|exact HM]]).
all: consts.unfold_sets.
all: try (repeat match goal with E : context [classical_dec ?P] |- _ => destruct (classical_dec P); cbn beta iota zeta in * end;
  repeat match goal with E : SOME _ = SOME _ |- _ => injection E as <- end;
  try discriminate;
  split; [split; discriminate|intros _; eexists; split; [destruct s; reflexivity|apply fun2set_update_eq; exact HM]]).
all: try (exfalso; congruence).

all: try (exfalso; match goal with E : context [classical_dec ?P] |- _ =>
 destruct (classical_dec P); cbn beta iota zeta in *; congruence end).
all: try (match goal with
 | E : mem_store_byte_aux (memory ?st) (mdomain ?st) ?be ?ad ?b = ?r1,
   E' : mem_store_byte_aux ?mem (mdomain ?st) ?be ?ad ?b = ?r2,
 HM : fun2set (memory ?st,mdomain ?st) = fun2set (?mem,mdomain ?st) |- _ =>
   let HN := fresh "HN" in let HE := fresh "HE" in
   destruct (mem_store_byte_aux_const_memory (memory st) mem (mdomain st) be ad b HM) as [HN HE];
   rewrite E, E' in HN, HE; cbn [THE] in HE;
   first [exfalso; intuition discriminate |split; [split; discriminate|intros _; eexists; split; [destruct st; reflexivity|symmetry; exact HE]]]
 end).
all: try (match goal with
 | E : mem_store_32 (memory ?st) (mdomain ?st) ?be ?ad ?b = ?r1,
   E' : mem_store_32 ?mem (mdomain ?st) ?be ?ad ?b = ?r2,
 HM : fun2set (memory ?st,mdomain ?st) = fun2set (?mem,mdomain ?st) |- _ =>
   let HN := fresh "HN" in let HE := fresh "HE" in
   destruct (mem_store_32_const_memory (memory st) mem (mdomain st) be ad b HM) as [HN HE];
   rewrite E, E' in HN, HE; cbn [THE] in HE;
   first [exfalso; intuition discriminate |split; [split; discriminate|intros _; eexists; split; [destruct st; reflexivity|exact HE]]]
 end).
Qed.
End InstMemory.

Section MemorySwap.
Import wordSem wordConvs consts consts_with.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (wordSem.state a c ffi_t).

Local Lemma mc_clock k (st : state) m : set_clock k (set_memory m st) = set_memory m (set_clock k st). Proof. destruct st; reflexivity. Qed.
Local Lemma mc_termdep k (st : state) m : set_termdep k (set_memory m st) = set_memory m (set_termdep k st). Proof. destruct st; reflexivity. Qed.
Local Lemma mc_call_env xs ss (st : state) m : call_env xs ss (set_memory m st) = set_memory m (call_env xs ss st). Proof. destruct st; reflexivity. Qed.
Local Lemma mc_dec_clock (st : state) m : dec_clock (set_memory m st) = set_memory m (dec_clock st). Proof. destruct st; reflexivity. Qed.
Local Lemma mc_set_var n v (st : state) m : set_var n v (set_memory m st) = set_memory m (set_var n v st). Proof. destruct st; reflexivity. Qed.
Local Lemma mc_set_vars n v (st : state) m : set_vars n v (set_memory m st) = set_memory m (set_vars n v st). Proof. destruct st; reflexivity. Qed.
Local Lemma mc_locals ls (st : state) m : set_locals ls (set_memory m st) = set_memory m (set_locals ls st). Proof. destruct st; reflexivity. Qed.
Local Lemma mc_jump (st : state) m : jump_exc (set_memory m st) = OPTION_MAP (fun x => (set_memory m (FST x),SND x)) (jump_exc st).
Proof. unfold jump_exc; cbn [handler stack set_memory]; destruct (handler st <? LENGTH (stack st)); [|reflexivity]; destruct (lastn.LASTN _ _) as [|[sz e0 e [[n [l1 l2]]|]] xs]; destruct st; reflexivity. Qed.
Local Lemma mc_jump_fields (st st1 : state) ret : jump_exc st = SOME (st1,ret) -> memory st1 = memory st /\ mdomain st1 = mdomain st.
Proof. unfold jump_exc; destruct (handler st <? LENGTH (stack st)); [|discriminate]; destruct (lastn.LASTN _ _) as [|[sz e0 e [[n [l1 l2]]|]] xs]; intros H; inversion H; subst; split; reflexivity. Qed.
Local Lemma mc_pop (st : state) m : pop_env (set_memory m st) = OPTION_MAP (fun x => set_memory m x) (pop_env st).
Proof. unfold pop_env; cbn [stack set_memory]; destruct (stack st) as [|[sz e0 e ret] xs]; [reflexivity|]; destruct ret as [[n r]|]; destruct st; reflexivity. Qed.
Local Lemma mc_push_code xs ret (st : state) : code (push_env xs ret st) = code st. Proof. pose proof (push_env_const xs ret st); consts.destr_conj; assumption. Qed.
Local Ltac mm_fields := cbn [set_locals set_locals_size set_fp_regs set_store_field set_stack set_stack_limit set_stack_max set_stack_size set_memory set_mdomain set_sh_mdomain set_permute set_compile set_compile_oracle set_code_buffer set_data_buffer set_gc_fun set_handler set_clock set_termdep set_code set_be set_ffi set_var set_vars set_store set_fp_var dec_clock set_var set_vars call_env memory mdomain code]; repeat rewrite ?(proj1 (push_env_mem_const _ _ _)), ?(proj2 (push_env_mem_const _ _ _)), ?mc_push_code.
Local Theorem memory_swap_strengthened : forall x : wordLang.prog a * state, forall r t, evaluate x = (r,t) ->
 forall m, fun2set (memory (snd x),mdomain (snd x)) = fun2set (m,mdomain (snd x)) ->
 code.no_install_code (code (snd x)) -> code.no_alloc_code (code (snd x)) ->
 no_install (fst x) -> no_alloc (fst x) ->
 exists m', evaluate (fst x,set_memory m (snd x)) = (r,set_memory m' t) /\
 fun2set (memory t,mdomain t) = fun2set (m',mdomain t).
Proof.
 intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
 intros r t H m HM HNI HNA Hpi Hpa; cbn [fst snd] in *.
 rewrite evaluate_eqn in H; destruct p; cbn [evaluate_body] in H; clock.io_step IH H;
 repeat match goal with E : (_,_) = (_,_) |- _ => injection E as <- <- end;
 try (exfalso; unfold no_install in Hpi; cbn [not_created_subprogs] in Hpi; apply Hpi; reflexivity);
 try (exfalso; unfold no_alloc in Hpa; cbn [not_created_subprogs] in Hpa; apply Hpa; reflexivity);
 rewrite evaluate_eqn; cbn [evaluate_body];
 rewrite ?get_var_const_memory, ?get_vars_const_memory, ?get_var_imm_const_memory;
 rewrite ?word_exp_const_memory by exact HM;
 cbn [locals set_memory memory mdomain be state_stack_size get_store store clock termdep code fp_regs ffi code_buffer data_buffer];
 repeat match goal with E : ?z = _ |- context [?z] => rewrite E; cbn beta iota zeta end;
 try solve [exists m; split; [unfold set_var, set_vars, set_store, flush_state, dec_clock; destruct s; reflexivity|cbn [set_var set_vars set_store flush_state dec_clock set_clock set_memory set_code_buffer set_data_buffer set_locals set_locals_size set_store_field set_stack memory mdomain]; first [exact HM|reflexivity]]].
all: try (unfold get_store; cbn [store set_memory]; repeat match goal with E : get_store _ _ = _ |- _ => unfold get_store in E end; repeat match goal with E : ?z = _ |- context [?z] => rewrite E; cbn beta iota zeta end).
all: try solve [exists m; split; [unfold set_var, set_vars, set_store, flush_state, dec_clock; destruct s; reflexivity|cbn [set_var set_vars set_store flush_state dec_clock set_clock set_memory set_code_buffer set_data_buffer set_locals set_locals_size set_store_field set_stack memory mdomain]; first [exact HM|reflexivity]]].
all: try solve [match goal with E : inst ?i ?st = SOME ?t0 |- _ =>
 pose proof (@inst_const_memory a c ffi_t st i st m HM) as [HN HS];
 destruct (HS ltac:(congruence)) as [m1 [HT HF]]; rewrite E in HT, HF; cbn [THE] in HT, HF;
 destruct (inst i (set_memory m st)) as [t1|] eqn:EI;
 [cbn [THE] in HT; subst t1; exists m1; split; [reflexivity|exact HF]|exfalso; assert (inst i st = NONE) by (apply (proj2 HN); reflexivity); congruence] end].
all: try solve [match goal with E : inst ?i ?st = NONE |- _ =>
 pose proof (@inst_const_memory a c ffi_t st i st m HM) as [HN HS];
 rewrite (proj1 HN E); exists m; split; reflexivity end].
all: try solve [match goal with E : share_inst ?op ?v ?ad ?st = (?r,?t) |- _ =>
 pose proof (share_inst_const_memory st op v ad m r t (conj HM E)) as [Hmem [Hdm HE]]; exists m; split; [exact HE|rewrite Hmem, Hdm; exact HM] end].
all: try solve [match goal with E : mem_store ?ad ?w ?st = SOME _ |- _ =>
 unfold mem_store in E |- *; cbn [mdomain set_memory];
 destruct (classical_dec (ad IN mdomain st)); cbn beta iota zeta in E |- *; try discriminate;
 injection E as <-; exists ((ad =+ w) m); split; [destruct st; reflexivity|cbn [set_memory memory mdomain]; apply fun2set_update_eq; exact HM] end].
all: try solve [match goal with E : mem_store ?ad ?w ?st = NONE |- _ =>
 pose proof (proj1 (mem_store_const_memory ad w st m HM)) as HN; rewrite (proj1 HN E); exists m; split; reflexivity end].
all: repeat multimatch goal with E : pop_env ?st = SOME ?st1 |- _ => lazymatch goal with _ : memory st1 = memory st |- _ => fail | _ => let HF := fresh "HFpop" in pose proof (pop_env_const st st1 E) as HF; consts.destr_conj end end.
all: repeat match goal with E : cut_state ?xs ?st = SOME ?st1 |- _ => is_var st1; let ls := fresh "ls" in let Hstate := fresh "Hstate" in destruct (cut_state_const xs st st1 E) as [ls Hstate]; subst st1 end.
all: rewrite ?cut_state_with_mem_const; repeat match goal with H : ?z = _ |- context [?z] => rewrite H; cbn beta iota zeta end; cbn [OPTION_MAP]; rewrite ?fix_clock_evaluate.
all: cbn [FST SND fst snd] in *.
all: rewrite ?fix_clock_evaluate.
all: rewrite ?mc_clock, ?mc_termdep, ?mc_dec_clock, ?push_env_mem_upd, ?mc_call_env, ?mc_set_var, ?mc_set_vars, ?mc_locals.
all: repeat multimatch goal with
 Hi : forall mm, _ |- context [evaluate (?pp,set_memory ?mem ?ss)] =>
 let Hsp := fresh "Hsp" in pose proof (Hi mem) as Hsp;
 lazymatch type of Hsp with
 | ?A -> ?B -> ?C -> ?D -> ?E -> exists mout, evaluate (pp,set_memory mem ss) = _ /\ _ =>
 let HA := fresh "HA" in let HB := fresh "HB" in let HC := fresh "HC" in let HD := fresh "HD" in let HE := fresh "HE" in
 assert (HA : A) by (mm_fields; repeat multimatch goal with H : memory ?st1 = memory ?st |- context [memory ?st1] => progress rewrite H end; repeat multimatch goal with H : mdomain ?st1 = mdomain ?st |- context [mdomain ?st1] => progress rewrite H end; first [assumption|reflexivity]);
 assert (HB : B) by (mm_fields; repeat multimatch goal with E : pop_env ?st = SOME ?st1, H : code ?st1 = code ?st |- context [code ?st1] => progress rewrite H end; assumption);
 assert (HC : C) by (mm_fields; repeat multimatch goal with E : pop_env ?st = SOME ?st1, H : code ?st1 = code ?st |- context [code ?st1] => progress rewrite H end; assumption);
 assert (HD : D) by (first [eapply code.no_install_find_code; split; [|eassumption]; assumption|unfold no_install in *; cbn [not_created_subprogs STOP] in *; consts.destr_conj; assumption]);
 assert (HE : E) by (first [eapply code.no_alloc_find_code; split; eassumption|unfold no_alloc in *; cbn [not_created_subprogs STOP] in *; consts.destr_conj; assumption]);
 let mnew := fresh "mnew" in let HEval := fresh "HEval" in let HMnew := fresh "HMnew" in
 destruct (Hsp HA HB HC HD HE) as [mnew [HEval HMnew]]; clear Hi Hsp;
 let HCode := fresh "HCode" in pose proof (code.no_install_evaluate_const_code _ _ _ _ (conj HEval (conj HD HB))) as HCode; cbn [code set_memory] in HCode;
 let HNIout := fresh "HNIout" in let HNAout := fresh "HNAout" in pose proof HB as HNIout; pose proof HC as HNAout; rewrite HCode in HNIout, HNAout;
 rewrite HEval; cbn [clock termdep set_memory];
 rewrite ?mc_pop, ?cut_state_with_mem_const;
 repeat match goal with H : ?z = _ |- context [?z] => rewrite H; cbn beta iota zeta end;
 cbn [OPTION_MAP locals set_memory];
 rewrite ?mc_clock, ?mc_termdep, ?mc_dec_clock, ?push_env_mem_upd, ?mc_call_env, ?mc_set_var, ?mc_set_vars, ?mc_locals;
 repeat match goal with H : ?z = _ |- context [?z] => rewrite H; cbn beta iota zeta end
 end
 end.
all: try solve [eexists; split; [reflexivity|first [assumption|reflexivity]]].
all: try (let HR := fresh "HR" in assert (HR : forall ptr len, read_bytearray ptr len (mem_load_byte_aux m (mdomain s) (be s)) = read_bytearray ptr len (mem_load_byte_aux (memory s) (mdomain s) (be s))) by (intros; symmetry; apply read_bytearray_const_memory; exact HM); rewrite ?HR; cbn [ffi set_memory]; repeat match goal with H : ?z = _ |- context [?z] => rewrite H; cbn beta iota zeta end).
all: try solve [exists m; split; [unfold flush_state; destruct s; reflexivity|cbn [flush_state set_memory set_locals_size set_store_field set_stack set_locals memory mdomain]; first [exact HM|reflexivity]]].
all: try solve [match goal with |- context [write_bytearray ?ptr ?ls ?mem (mdomain ?st) (be ?st)] =>
 exists (write_bytearray ptr ls mem (mdomain st) (be st)); split; [destruct st; reflexivity|cbn [set_memory set_ffi set_fp_regs set_locals memory mdomain]; apply write_bytearray_const_memory; exact HM] end].
all: try solve [match goal with |- context [const_writes ?ad ?off ?ls ?mem] => exists (const_writes ad off ls mem); split; [unfold set_var, unset_var; destruct s; reflexivity|cbn [set_var unset_var set_locals set_memory memory mdomain]; apply const_writes_const_memory; exact HM] end].
all: try solve [match goal with E : jump_exc ?st = SOME (?st1,?ret) |- _ =>
 rewrite mc_jump, E; cbn [OPTION_MAP FST SND]; exists m; split; [reflexivity|pose proof (mc_jump_fields st st1 ret E) as Hf; consts.destr_conj; repeat match goal with H : memory _ = _ |- _ => rewrite H end; repeat match goal with H : mdomain _ = _ |- _ => rewrite H end; exact HM] end].
all: try solve [match goal with E : jump_exc ?st = NONE |- _ => rewrite mc_jump, E; cbn [OPTION_MAP]; exists m; split; reflexivity end].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "memory_swap_lemma1" *)
Local Theorem memory_swap_lemma1 : forall prog (st : state) res rst m,
 evaluate (prog,st) = (res,rst) /\
 fun2set (memory st,mdomain st) = fun2set (m,mdomain st) /\
 code.no_alloc_code (code st) /\ code.no_install_code (code st) /\
 no_alloc prog /\ no_install prog ->
 exists st', evaluate (prog,set_memory m st) = (res,st') /\
 set_memory ARB st' = set_memory ARB rst /\
 fun2set (memory rst,mdomain rst) = fun2set (memory st',mdomain rst).
Proof.
 intros p st res rst m (He & Hm & Hna & Hni & Hpa & Hpi).
 destruct (memory_swap_strengthened (p,st) res rst He m Hm Hni Hna Hpi Hpa) as [m1 [He1 Hm1]].
 exists (set_memory m1 rst); split; [exact He1|]; split; [destruct rst; reflexivity|exact Hm1].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "memory_swap_lemma" *)
Local Theorem memory_swap_lemma : forall prog (st : state) res rst m,
 evaluate (prog,st) = (res,rst) /\
 fun2set (memory st,mdomain st) = fun2set (m,mdomain st) /\
 code.no_alloc_code (code st) /\ code.no_install_code (code st) /\
 no_alloc prog /\ no_install prog ->
 exists m', evaluate (prog,set_memory m st) = (res,set_memory m' rst) /\
 fun2set (memory rst,mdomain rst) = fun2set (m',mdomain rst).
Proof.
 intros p st res rst m (He & Hm & Hna & Hni & Hpa & Hpi).
 exact (memory_swap_strengthened (p,st) res rst He m Hm Hni Hna Hpi Hpa).
Qed.

End MemorySwap.
