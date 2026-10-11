(** * CakeML [lab_to_targetProof]: the initial state satisfies [state_rel]

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml] (HOL
    lines 10134-10538): [IMP_state_rel_make_init], [make_init_simp] and
    [semantics_make_init].

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v].
    - HOL's record updates [rec with <|entry_pc := ..; exit_pc := ..|>] are
      written as full records.
    - HOL's [IMP_state_rel_make_init] is proved with [suspend]/[Resume]
      pieces ISR1..ISR17; here it is one proof (one bullet per field of
      [state_rel]).
    - HOL derives [semantics_make_init] by ML rule manipulation of
      [machine_sem_EQ_sem]; here it is stated explicitly (hypotheses of
      [IMP_state_rel_make_init] plus [encoder_correct] and
      [semantics <> Fail]) and proved from [machine_sem_EQ_sem],
      [IMP_state_rel_make_init] and [oracle_tie_make_init].
    - The [isr_*] lemmas are Galette-only helpers. *)

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
From Galette.cakeml.compiler.backend Require Import labLang lab_to_target.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend.semantics Require wordSem backendProps.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem targetProps.
From Galette.cakeml.compiler.backend.semantics Require Import labSem labProps.
From Galette.cakeml.compiler.backend.proofs Require lab_filterProof.
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import
  basic bytes inst compile_lemmas rl_syntax rl_invariants rl_nop rl_labels rl_compute rl_remove
  code_props pos_props shmem cc_setup cc_asm cc_jump cc_ffi cc_install cc_share compile_correct
  sem_machine init_defs.
Import wordLang (word_loc, Word, Loc).
Import wordSem (mem_load_byte_aux, mem_store_byte_aux, write_bytearray, mem_load_32,
  mem_store_32, buffer, position, buffer_buffer, space_left).
Import ByteBits.
Open Scope N_scope.






Section Helpers.

Lemma isr_TAKE_DROP {X} n (l : list X) : TAKE n l ++ DROP n l = l.
Proof. rewrite TAKE_firstn, DROP_skipn. apply firstn_skipn. Qed.

Lemma isr_MAP_DROP {X Y} (f : X -> Y) n l : MAP f (DROP n l) = DROP n (MAP f l).
Proof. rewrite !DROP_skipn. symmetry. apply skipn_map. Qed.

Lemma isr_LENGTH_DROP {X} n (l : list X) : LENGTH (DROP n l) = LENGTH l - n.
Proof. rewrite DROP_skipn, !LENGTH_length, length_skipn. lia. Qed.

Lemma isr_ALOOKUP_ZIP_GENLIST {V} `{Inhabited V} (l : list V) : forall i k,
  ALOOKUP (ZIP (GENLIST (fun j => j + i) (LENGTH l), l)) k =
  if decide (i <= k < i + LENGTH l) then SOME (EL (k - i) l) else NONE.
Proof.
  induction l as [|x l IH]; intros i k.
  - cbn. destruct (decide _); [lia|reflexivity].
  - replace (LENGTH (x :: l)) with (SUC (LENGTH l)) by (cbn [LENGTH]; lia).
    rewrite GENLIST_CONS_aux.
    replace (fun j => SUC j + i) with (fun j => j + SUC i)
      by (apply functional_extensionality; intros; lia).
    cbn [ZIP ALOOKUP]. unfold ZIP in IH |- *. cbn. destruct (decide (i = k)) as [E|E].
    + subst k.
      destruct (decide (i <= i < i + SUC (LENGTH l))) as [_|n]; [|lia]. rewrite N.sub_diag. reflexivity.
    + rewrite IH. destruct (decide (SUC i <= k < SUC i + LENGTH l)) as [h|h];
        destruct (decide (i <= k < i + SUC (LENGTH l))) as [h'|h']; try lia; [|reflexivity].
      replace (k - i) with (SUC (k - SUC i)) by lia. rewrite EL_SUC. reflexivity.
Qed.

Lemma isr_find_index_shift {X} `{EqDecision X} (x : X) l : forall n k j,
  find_index x l n = SOME j -> find_index x l (n + k) = SOME (j + k).
Proof.
  induction l as [|h l IH]; intros n k j; cbn; [discriminate|].
  destruct (decide (h = x)); [intros E; injection E as <-; reflexivity|].
  intros E. replace (n + k + 1) with (n + 1 + k) by lia. exact (IH _ _ _ E).
Qed.

Lemma isr_w2n_add_ge {a} (p : word a) x :
  x < dimword a -> w2n p <= w2n (p + n2w x)%w -> w2n (p + n2w x)%w = w2n p + x.
Proof.
  intros Hx Hle. assert (E0 : w2n (p + n2w x)%w = (w2n p + x) mod dimword a).
  { rewrite <- (n2w_w2n p) at 1. rewrite word_add_n2w, w2n_n2w. reflexivity. }
  rewrite E0 in *.
  pose proof (w2n_lt p) as Hp. pose proof (ZERO_LT_dimword a) as Hd.
  set (d := dimword a) in *. set (s := w2n p + x) in *.
  destruct (N.lt_ge_cases s d) as [Hs|Hs]; [apply N.mod_small, Hs|].
  exfalso. assert (E : s mod d = s - d).
  { symmetry. apply (N.mod_unique s d 1); lia. }
  rewrite E in Hle. lia.
Qed.

Lemma isr_ALOOKUP_ZIP_GENLIST_MAP {X V} `{Inhabited V} (f : X -> V) (l : list X) i k :
  ALOOKUP (ZIP (GENLIST (fun j => j + i) (LENGTH l), MAP f l)) k =
  if decide (i <= k < i + LENGTH l) then SOME (EL (k - i) (MAP f l)) else NONE.
Proof. rewrite <- (LENGTH_MAP' f l). apply isr_ALOOKUP_ZIP_GENLIST. Qed.

Lemma isr_w2n_add_lt {a} (p : word a) x :
  w2n p + x < dimword a -> w2n (p + n2w x)%w = w2n p + x.
Proof. intros H. rewrite <- (n2w_w2n p) at 1. rewrite word_add_n2w, w2n_n2w. apply N.mod_small, H. Qed.

End Helpers.

#[local] Instance isr_shmem_info_num_inhabited : Inhabited shmem_info_num :=
  {| entry_pc := 0; nbytes := n2w 0; addr_reg := 0; addr_off := 0; reg := 0; exit_pc := 0 |}.


Section ISR.
Context {a : N} {B C Ffi : Type}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "IMP_state_rel_make_init" *)
Theorem IMP_state_rel_make_init : forall (mc_conf : machine_config a B C) (code code2 : list (sec a))
    (coracle : N -> config * list (sec a)) labs i clock (ms : B) cbspace (t : asm_state a) m dm sdm
    new_ffi_names shmem_info new_shmem_info (ffi : ffi_state Ffi),
  good_code (asmProps.config mc_conf.(target)) (@LN (spt N)) code /\
  mc_conf_ok mc_conf /\
  (no_share_mem_inst code ->
     compiler_oracle_ok coracle labs (LENGTH (prog_to_bytes code2)) (asmProps.config mc_conf.(target))
       mc_conf.(ffi_names)) /\
  list_subset (FILTER (fun x => ⌜exists s, x = ExtCall s⌝) (find_ffi_names code))
    (TAKE i mc_conf.(ffi_names)) /\
  remove_labels clock (asmProps.config mc_conf.(target)) 0 LN (TAKE i mc_conf.(ffi_names)) code =
    SOME (code2, labs) /\
  good_init_state mc_conf ms (prog_to_bytes code2) cbspace t m dm sdm /\
  get_shmem_info code2 0 [] [] = (new_ffi_names, shmem_info) /\
  new_shmem_info =
    MAP (fun rec => {| entry_pc := w2n (get_pc mc_conf.(target) ms) + entry_pc rec;
                       nbytes := nbytes rec; addr_reg := addr_reg rec; addr_off := addr_off rec;
                       reg := reg rec;
                       exit_pc := w2n (get_pc mc_conf.(target) ms) + exit_pc rec |}) shmem_info /\
  DROP i mc_conf.(ffi_names) = new_ffi_names /\
  mmio_pcs_min_index mc_conf.(ffi_names) = SOME i /\
  MAP (fun rec => entry_pc rec) new_shmem_info = DROP i (MAP w2n mc_conf.(ffi_entry_pcs)) /\
  mc_conf.(mmio_info) =
    ZIP (GENLIST (fun index => index + i) (LENGTH new_shmem_info),
         MAP (fun rec => (nbytes rec, (Addr (addr_reg rec) (n2w (addr_off rec)),
                                       (reg rec, n2w (exit_pc rec))))) new_shmem_info) /\
  no_install_or_no_share_mem code mc_conf.(ffi_names) /\
  (forall bn, bn < cbspace ->
     ~ MEM (n2w bn + n2w (LENGTH (prog_to_bytes code2)) + get_pc mc_conf.(target) ms)%w
         (TAKE i mc_conf.(ffi_entry_pcs))) ->
  state_rel (mc_conf, (code2, (labs, get_pc mc_conf.(target) ms)))
    (make_init mc_conf ffi t m dm sdm ms code (compile_lab (asmProps.config mc_conf.(target)))
       (get_pc mc_conf.(target) ms + n2w (LENGTH (prog_to_bytes code2)))%w cbspace coracle) t ms.
Proof.
  intros mc_conf code code2 coracle labs i clock ms cbspace t m dm sdm nfn shi nshi ffi
    (Hgood & Hmc & Horc & Hsub & Hrl & Hgis & Hgsi & Ensi & Edrop & Hmmio & Hmap & Hmmio_info & Hnios & Hcb).
  set (cfg := asmProps.config mc_conf.(target)) in *.
  set (L := LENGTH (prog_to_bytes code2)) in *.
  pose proof Hmc as (Mg & Menc & Mptr & Mlen & Mptr2 & Mlen2 & Mlink & Menc_ok).
  pose proof Hgood as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  destruct (remove_labels_thm clock cfg 0 LN (TAKE i mc_conf.(ffi_names)) code code2 labs)
    as (Hok2 & Hsim & Hodd & Hev & _ & Hloc).
  { split; [exact Hrl|]. split; [exact Menc_ok|]. split; [exact G1|]. split; [exact G2|].
    split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [exact G7|].
    split; [reflexivity|]. intros q1 q2. unfold lab_lookup. rewrite lookup_LN. reflexivity. }
  pose proof Hgis as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14 & I15 & I16 & I17 & I18).
  pose proof I2 as (C1 & C2 & C3 & C4 & C5).
  pose proof I4 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & i' & Si & S8 & S9 & S10).
  rewrite Hmmio in Si. injection Si as <-.
  set (pc0 := get_pc mc_conf.(target) ms) in *.
  rewrite I3 in *.
  destruct (mmio_pcs_min_index_is_SOME _ _ Hmmio) as (Hi_le & Hi_ext & Hi_sh).
  pose proof (shmem_entries_thm cfg labs (TAKE i mc_conf.(ffi_names)) code2 0 [] [] 0 Hok2) as E0.
  rewrite Hgsi in E0. cbn [app] in E0. injection E0 as Enfn Eshi.
  assert (Hent : forall r, In r shi -> entry_pc r < L).
  { intros r Hr. rewrite Eshi in Hr. apply in_map_iff in Hr as (x & <- & Hx).
    apply shmem_entries_entry in Hx as (j & op & re & a0 & bytes & len & _ & Hj & ->). cbn [snd entry_pc].
    pose proof (pos_val_mono j 0 code2 (num_pcs code2) 0 cfg labs (TAKE i mc_conf.(ffi_names))
                  (conj Hj (conj (N.le_refl _) (conj Hok2 Menc_ok)))) as Hm.
    rewrite (pos_val_num_pcs cfg labs (TAKE i mc_conf.(ffi_names)) 0 code2 0 Hok2) in Hm. unfold L. lia. }
  assert (Hdrop : forall y, In y (DROP i (MAP w2n mc_conf.(ffi_entry_pcs))) ->
                            w2n pc0 <= y /\ y < w2n pc0 + L).
  { intros y Hy. rewrite <- Hmap, Ensi, map_map in Hy. apply in_map_iff in Hy as (r & <- & Hr).
    cbn [entry_pc]. pose proof (Hent r Hr). lia. }
  assert (Hlen_nshi : LENGTH nshi = LENGTH mc_conf.(ffi_names) - i).
  { rewrite S10, <- (LENGTH_MAP' (fun rec => entry_pc rec) nshi), Hmap, isr_LENGTH_DROP, LENGTH_MAP'.
    reflexivity. }
  assert (Hgsi' : get_shmem_info code2 (w2n pc0) (TAKE i mc_conf.(ffi_names)) [] = (mc_conf.(ffi_names), nshi)).
  { rewrite (shmem_entries_thm cfg labs (TAKE i mc_conf.(ffi_names)) code2 (w2n pc0) (TAKE i mc_conf.(ffi_names)) [] 0 Hok2).
    destruct (get_shmem_info_init_pc_offset cfg labs (TAKE i mc_conf.(ffi_names)) 0 code2 (w2n pc0) Hok2) as [F1 F2].
    rewrite Hgsi in F1, F2.
    rewrite (shmem_entries_thm cfg labs (TAKE i mc_conf.(ffi_names)) code2 (w2n pc0) [] [] 0 Hok2) in F1, F2.
    cbn [FST SND fst snd app] in F1, F2. cbn [app].
    rewrite <- F1, <- F2, <- Edrop, isr_TAKE_DROP, Ensi. reflexivity. }
  apply state_rel_iff. unfold make_init. constructor; lst_cbn; try assumption.
  - exact (eq_sym C4).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - (* ISR1 *)
    exists i. split; [exact Hmmio|]. intros index. rewrite Hmmio_info, isr_ALOOKUP_ZIP_GENLIST_MAP, Hlen_nshi.
    destruct (decide (i <= index < LENGTH mc_conf.(ffi_names))) as [h|h];
      destruct (decide (i <= index < i + (LENGTH mc_conf.(ffi_names) - i))) as [h'|h']; try lia;
      [eexists; reflexivity|reflexivity].
  - (* ISR2 *)
    intros ms2 k index new_bytes t1 bytes bytes2 st new_st i0
      (Hi0 & Hlt & Hrd & _ & Hcall & Hdom & Hrel & Hal).
    destruct (mmio_pcs_min_index_is_SOME _ _ Hi0) as (Hle & _ & _).
    apply (ffi_interfer_ok_post_ffi_asm pc0 mc_conf index i0 t1 ms2 bytes bytes2 new_bytes k).
    split; [exact I7|]. split; [lia|]. split; [exact Hi0|]. split; [exact Hlt|].
    split; [exact Hdom|]. split; [exact Hrd|].
    split; [symmetry; exact (call_FFI_LENGTH _ _ _ _ _ _ Hcall)|].
    split; [intros E; rewrite E in Hcall; unfold call_FFI in Hcall;
            rewrite bool_decide_eq_true_2 in Hcall by reflexivity; cbn in Hcall;
            injection Hcall as _ <-; reflexivity|].
    split; [|exact Hal].
    replace (- n2w ((3 + index) * ffi_offset) + pc0)%w with (pc0 - n2w ((3 + index) * ffi_offset))%w
      by word_ring. exact Hrel.
  - (* ISR3 *)
    intros ms2 t1 k a1 a2 (Hrel & Hal).
    apply (ccache_interfer_ok_post_ccache_asm pc0 mc_conf t1 ms2 k a1 a2).
    split; [exact I8|]. split; [|exact Hal].
    replace (- n2w (2 * ffi_offset) + pc0)%w with (pc0 - n2w (2 * ffi_offset))%w
      by word_ring. exact Hrel.
  - reflexivity.
  - (* ISR4 *)
    intros Hns k.
    specialize (Horc (code_similar_IMP_both_no_share_mem _ _ (conj (code_similar_sym _ _ Hsim) Hns))).
    unfold compiler_oracle_ok in Horc. destruct Horc as [Ho1 Ho2]. specialize (Ho1 k).
    destruct (coracle k) as [cf cd] eqn:Ek. destruct Ho1 as [Ho1 Ho3].
    split; [exact Ho1|]. split; [exact Ho3|]. intros ->. rewrite Ek in Ho2. exact Ho2.
  - exact (list_subset_trans _ _ _ (conj Hsub (list_subset_TAKE _ _))).
  - exact (all_enc_ok_prog_to_bytes_EVEN code2 0 _ _ _ 0 (conj eq_refl Hok2)).
  - (* ISR8 *)
    intros name i0 (Hm & Hi0 & Hlt). rewrite Hmmio in Hi0. injection Hi0 as <-.
    destruct (find_index_MEM _ name 0 Hm) as (j & Hj & Hjl & Hjel).
    unfold get_ffi_index in *. rewrite Hj in *. cbn [the] in *. rewrite N.add_0_l in *.
    destruct (mmio_pcs_min_index_is_SOME _ _ Hmmio) as (_ & Hext & _).
    destruct (Hext j Hlt) as [s Hs]. rewrite Hjel in Hs.
    destruct (S8 j Hlt) as (T1 & T2 & T3 & T4 & T5).
    split; [exists s; exact Hs|]. repeat split; assumption.
  - rewrite C4. exact I6.
  - reflexivity.
  - intros r. reflexivity.
  - (* ISR9 *)
    intros a0 Ha. assert (Hd := I12 a0 Ha). split; [apply I11; exact Hd|]. split; [exact Hd|].
    destruct (I16 a0) as (w & Hw1 & Hw2). unfold word_loc_val_byte. rewrite Hw2. cbn.
    rewrite Hw1. reflexivity.
  - cbn [space_left position buffer_buffer LENGTH length]. intros n Hn.
    destruct (I17 n Hn) as [J1 J2]. replace (pc0 + n2w L + n2w (0 + n))%w with (n2w (n + L) + pc0)%w.
    + split; assumption.
    + rewrite N.add_0_l, <- word_add_n2w. word_ring.
  - reflexivity.
  - cbn. exact Logic.I.
  - cbn [space_left position buffer_buffer LENGTH length]. lia.
  - (* ISR12 *)
    cbn [space_left position buffer_buffer LENGTH length]. intros bn Hbn Hm.
    apply MEM_In in Hm. rewrite <- (isr_TAKE_DROP i (ffi_entry_pcs mc_conf)) in Hm.
    apply in_app_or in Hm as [Hm|Hm].
    + apply (Hcb bn); [lia|]. apply MEM_In.
      replace (n2w bn + n2w L + pc0)%w with (pc0 + n2w L + n2w bn)%w by word_ring. exact Hm.
    + apply (in_map w2n) in Hm. rewrite isr_MAP_DROP in Hm.
      apply Hdrop in Hm as [Hm1 Hm2]. rewrite <- WORD_ADD_ASSOC, word_add_n2w in Hm1, Hm2.
      assert (Hb : L + bn < dimword a) by lia.
      rewrite (isr_w2n_add_ge _ _ Hb Hm1) in Hm2. lia.
  - intros Hf; discriminate Hf.
  - exact (eq_sym C2).
  - rewrite I3, (pos_val_0 _ _ _ _ _ Hok2). symmetry. apply WORD_ADD_0.
  - rewrite WORD_AND_COMM. exact I5.
  - rewrite Hmmio. exact Hok2.
  - exact (code_similar_sec_labels_ok _ _ (conj G2 Hsim)).
  - (* ISR15 *)
    split.
    + intros ms2 k index new_bytes t1 nb ad offs re pc' ad' st new_st i0
        (Hi0 & Hle & Hlt & _ & Hal & Hdom & _ & Hrel).
      rewrite Hmmio in Hi0. injection Hi0 as <-.
      destruct (Hi_sh index (conj Hle Hlt)) as [op Hop]. exists op. split; [exact Hop|].
      destruct (I7 ms2 k index new_bytes t1 [] [] i (conj Hlt (conj Hmmio Hdom))) as [_ Hhi].
      destruct (Hhi (conj Hle Hrel)) as (info & Hinfo & Hrd & Hwr). rewrite Hal in Hinfo.
      injection Hinfo as <-.
      destruct op; intros _; [exact (Hrd Hop new_bytes)|exact (Hwr Hop)].
    + intros index i0 (Hi0 & Hlt & Hle). rewrite Hmmio in Hi0. injection Hi0 as <-.
      exact (S9 index (conj Hlt Hle)).
  - (* ISR16 *)
    unfold share_mem_domain_code_rel.
    assert (Hext_take : EVERY (fun x => ⌜exists s, x = ExtCall s⌝) (TAKE i mc_conf.(ffi_names))).
    { unfold is_true. rewrite EVERY_Forall, List.Forall_forall. intros x Hx. apply bool_decide_spec.
      apply (proj2 (MEM_In _ _)) in Hx. apply MEM_TAKE_EL in Hx as (k & Hk & _ & <-). exact (Hi_ext k Hk). }
    assert (HLlt : L < dimword a) by lia.
    destruct (get_shmem_info_ok_lemma cfg labs (TAKE i mc_conf.(ffi_names)) 0 code2 (w2n pc0)
                (TAKE i mc_conf.(ffi_names)) mc_conf.(ffi_names) nshi
                (conj Hok2 (conj Menc_ok (conj HLlt (conj Hext_take Hgsi'))))) as [K1 K2].
    assert (Hidx : forall index, index < i ->
       (- n2w (ffi_offset * (index + 3)) + pc0)%w NOTIN mc_conf.(prog_addresses) /\
       (- n2w (ffi_offset * (index + 3)) + pc0)%w NOTIN mc_conf.(shared_addresses) /\
       (- n2w (ffi_offset * (index + 3)) + pc0)%w <> mc_conf.(halt_pc) /\
       (- n2w (ffi_offset * (index + 3)) + pc0)%w <> mc_conf.(ccache_pc) /\
       find_index (- n2w (ffi_offset * (index + 3)) + pc0)%w mc_conf.(ffi_entry_pcs) 0 = SOME index).
    { intros index Hix. replace (- n2w (ffi_offset * (index + 3)) + pc0)%w
        with (pc0 - n2w ((3 + index) * ffi_offset))%w.
      - exact (S8 index Hix).
      - replace (ffi_offset * (index + 3)) with ((3 + index) * ffi_offset) by lia. word_ring. }
    assert (Hbim : bytes_in_mem pc0 (prog_to_bytes code2) (asmSem.mem t) mc_conf.(prog_addresses) dm)
      by (rewrite <- C4; exact I10).
    assert (Hnot_take : forall pc line a1, asm_fetch_aux pc code2 = SOME line ->
              a1 < LENGTH (line_bytes line) ->
              ~ MEM (pc0 + n2w a1 + n2w (pos_val pc 0 code2))%w (TAKE i mc_conf.(ffi_entry_pcs))).
    { intros pc line a1 Hf Ha1.
      exact (asm_fetch_NOT_ffi_entry_pcs mc_conf code2 i labs (TAKE i mc_conf.(ffi_names)) ms t dm pc line a1
               (conj HLlt (conj Hmmio (conj S10 (conj Hok2 (conj Menc_ok (conj Hidx
                  (conj Hbim (conj Hf Ha1))))))))). }
    split; [|split; [|split; [exact I14|exact (eq_sym I13)]]].
    + intros pc op re a0 inst len i0 (Hf & Hi0). rewrite Hmmio in Hi0. injection Hi0 as <-.
      destruct (K1 pc op re a0 inst len i (conj Hf Hmmio)) as (index & Hfind & Hrest).
      set (pv := pos_val pc 0 code2) in *.
      rewrite Hmap in Hfind.
      assert (Hin : is_true (MEM (w2n pc0 + pv) (DROP i (MAP w2n (ffi_entry_pcs mc_conf))))).
      { destruct (classic (is_true (MEM (w2n pc0 + pv) (DROP i (MAP w2n (ffi_entry_pcs mc_conf))))))
          as [H|H]; [exact H|].
        apply (find_index_NOT_MEM _ _ 0) in H. rewrite H in Hfind. discriminate. }
      assert (Hpv : w2n pc0 + pv < dimword a).
      { apply MEM_In in Hin. rewrite <- isr_MAP_DROP in Hin. apply in_map_iff in Hin as (x & Hx & _).
        rewrite <- Hx. apply w2n_lt. }
      assert (Hfd : find_index (pc0 + n2w pv)%w (DROP i (ffi_entry_pcs mc_conf)) 0 = SOME index).
      { rewrite <- find_index_MAP_w2n, isr_MAP_DROP, (isr_w2n_add_lt _ _ Hpv). exact Hfind. }
      assert (Hpos : 0 < LENGTH inst).
      { pose proof (all_enc_ok_asm_fetch_aux_IMP_line_ok _ _ _ _ _ _ _ (conj Hok2 Hf)) as Hl.
        exact (line_ok_not_Label_pos _ _ _ _ _ Menc_ok Hl (fun e => Bool.diff_false_true e)). }
      pose proof (Hnot_take pc _ 0 Hf Hpos) as Hnt. fold pv in Hnt.
      rewrite (proj1 WORD_ADD_0) in Hnt.
      apply (find_index_NOT_MEM _ _ 0) in Hnt.
      pose proof (find_index_LESS_LENGTH _ _ _ _ Hfind) as Hil. rewrite <- Hmap, LENGTH_MAP' in Hil.
      exists (index + i). split; [lia|]. split.
      * rewrite <- (isr_TAKE_DROP i (ffi_entry_pcs mc_conf)), find_index_append, Hnt.
        rewrite LENGTH_TAKE by lia. exact (isr_find_index_shift _ _ 0 i index Hfd).
      * destruct (get_memop_info op) as [name nb]. destruct Hrest as [R1 R2]. split; [exact R1|].
        rewrite Hmmio_info, isr_ALOOKUP_ZIP_GENLIST_MAP.
        destruct (decide (i <= index + i < i + LENGTH nshi)) as [_|h]; [|lia].
        replace (index + i - i) with index by lia. rewrite EL_MAP_lt by lia.
        assert (Ee : EL index nshi =
          {| entry_pc := entry_pc (EL index nshi); nbytes := nb;
             addr_reg := match a0 with Addr r _ => r end;
             addr_off := match a0 with Addr _ off => w2n off end;
             reg := re; exit_pc := w2n pc0 + (pv + len) |}) by exact R2.
        rewrite Ee. cbn [nbytes addr_reg addr_off reg exit_pc].
        destruct a0 as [r off]. rewrite n2w_w2n, <- word_add_n2w, n2w_w2n. reflexivity.
    + intros pc line (Hf & Hnot). specialize (K2 pc line (conj Hf Hnot)).
      rewrite IN_DISJOINT. intros (x & Hx1 & (a1 & -> & Ha1)).
      set (pv := pos_val pc 0 code2) in *.
      apply IN_set in Hx1. rewrite <- (isr_TAKE_DROP i (ffi_entry_pcs mc_conf)) in Hx1.
      apply in_app_or in Hx1 as [Hx1|Hx1].
      { apply (Hnot_take pc line a1 Hf Ha1). apply MEM_In. exact Hx1. }
      apply (in_map w2n) in Hx1. rewrite isr_MAP_DROP in Hx1.
      pose proof (Hdrop _ Hx1) as [Hge _].
      pose proof (asm_fetch_aux_pos_val_SUC pc 0 code2 0 _ _ _ line (conj Hok2 Hf)) as Hs.
      pose proof (pos_val_bound (pc + 1) 0 code2 _ _ _ _ Hok2) as Hb. fold pv in Hs.
      assert (Hlt : a1 + pv < dimword a) by (unfold L in HLlt; lia).
      rewrite <- WORD_ADD_ASSOC, word_add_n2w in Hx1, Hge.
      rewrite (isr_w2n_add_ge _ _ Hlt Hge) in Hx1.
      rewrite IN_DISJOINT in K2. apply K2. exists (w2n pc0 + (a1 + pv)). split.
      * apply IN_set. rewrite Hmap. exact Hx1.
      * hnf. exists a1. split; [lia|exact Ha1].
  - exact (code_similar_IMP_both_no_install_or_no_share_mem _ _ _ (conj Hsim Hnios)).

Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "make_init_simp" *)
Theorem make_init_simp : forall {c} (mc_conf : machine_config a B C) (ffi : ffi_state Ffi) t m dm sdm ms
    code (cmp : c -> list (sec a) -> option (list word8 * c)) cbpos cbspace coracle,
  (make_init mc_conf ffi t m dm sdm ms code cmp cbpos cbspace coracle).(labSem.ffi) = ffi /\
  (make_init mc_conf ffi t m dm sdm ms code cmp cbpos cbspace coracle).(labSem.pc) = 0 /\
  (make_init mc_conf ffi t m dm sdm ms code cmp cbpos cbspace coracle).(labSem.code) = code.
Proof. intros. repeat split. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "semantics_make_init" *)
Theorem semantics_make_init : forall (mc_conf : machine_config a B C) (code code2 : list (sec a))
    (coracle : N -> config * list (sec a)) labs i clock (ms : B) cbspace (t : asm_state a) m dm sdm
    new_ffi_names shmem_info new_shmem_info (ffi : ffi_state Ffi),
  encoder_correct mc_conf.(target) /\
  good_code (asmProps.config mc_conf.(target)) (@LN (spt N)) code /\
  mc_conf_ok mc_conf /\
  (no_share_mem_inst code ->
     compiler_oracle_ok coracle labs (LENGTH (prog_to_bytes code2)) (asmProps.config mc_conf.(target))
       mc_conf.(ffi_names)) /\
  list_subset (FILTER (fun x => ⌜exists s, x = ExtCall s⌝) (find_ffi_names code))
    (TAKE i mc_conf.(ffi_names)) /\
  remove_labels clock (asmProps.config mc_conf.(target)) 0 LN (TAKE i mc_conf.(ffi_names)) code =
    SOME (code2, labs) /\
  good_init_state mc_conf ms (prog_to_bytes code2) cbspace t m dm sdm /\
  get_shmem_info code2 0 [] [] = (new_ffi_names, shmem_info) /\
  new_shmem_info =
    MAP (fun rec => {| entry_pc := w2n (get_pc mc_conf.(target) ms) + entry_pc rec;
                       nbytes := nbytes rec; addr_reg := addr_reg rec; addr_off := addr_off rec;
                       reg := reg rec;
                       exit_pc := w2n (get_pc mc_conf.(target) ms) + exit_pc rec |}) shmem_info /\
  DROP i mc_conf.(ffi_names) = new_ffi_names /\
  mmio_pcs_min_index mc_conf.(ffi_names) = SOME i /\
  MAP (fun rec => entry_pc rec) new_shmem_info = DROP i (MAP w2n mc_conf.(ffi_entry_pcs)) /\
  mc_conf.(mmio_info) =
    ZIP (GENLIST (fun index => index + i) (LENGTH new_shmem_info),
         MAP (fun rec => (nbytes rec, (Addr (addr_reg rec) (n2w (addr_off rec)),
                                       (reg rec, n2w (exit_pc rec))))) new_shmem_info) /\
  no_install_or_no_share_mem code mc_conf.(ffi_names) /\
  (forall bn, bn < cbspace ->
     ~ MEM (n2w bn + n2w (LENGTH (prog_to_bytes code2)) + get_pc mc_conf.(target) ms)%w
         (TAKE i mc_conf.(ffi_entry_pcs))) /\
  semantics (make_init mc_conf ffi t m dm sdm ms code (compile_lab (asmProps.config mc_conf.(target)))
       (get_pc mc_conf.(target) ms + n2w (LENGTH (prog_to_bytes code2)))%w cbspace coracle) <> Fail ->
  machine_sem mc_conf ffi ms =
    (semantics (make_init mc_conf ffi t m dm sdm ms code (compile_lab (asmProps.config mc_conf.(target)))
       (get_pc mc_conf.(target) ms + n2w (LENGTH (prog_to_bytes code2)))%w cbspace coracle)) INSERT {}.
Proof.
  intros mc_conf code code2 coracle labs i clock ms cbspace t m dm sdm nfn shi nshi ffi
    (Henc & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & Hsem).
  set (s := make_init mc_conf ffi t m dm sdm ms code (compile_lab (asmProps.config mc_conf.(target)))
       (get_pc mc_conf.(target) ms + n2w (LENGTH (prog_to_bytes code2)))%w cbspace coracle) in *.
  change ffi with (labSem.ffi s) at 1.
  apply (machine_sem_EQ_sem mc_conf (get_pc mc_conf.(target) ms) ms s).
  split; [exact Henc|]. split; [|exact Hsem].
  exists code2, labs, t. split.
  - exact (IMP_state_rel_make_init mc_conf code code2 coracle labs i clock ms cbspace t m dm sdm
             nfn shi nshi ffi (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8
             (conj H9 (conj H10 (conj H11 (conj H12 (conj H13 H14)))))))))))))).
  - apply oracle_tie_make_init.
Qed.

End ISR.
