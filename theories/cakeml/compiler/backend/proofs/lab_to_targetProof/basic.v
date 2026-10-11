(** * CakeML [lab_to_targetProof]: definitions and the state relation

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml] (HOL
    lines 1-1153): [sec_loc_to_pc], the nop-padded asm step
    ([asm_step_IMP_evaluate_step_nop]), the syntactic relations
    ([code_similar], [line_ok], [all_enc_ok], [pos_val]), [good_code], the
    shared-memory relations, [oracle_tie] and [state_rel].

    Notes:
    - Names: labSem's state fields ([pc], [regs], [mem], ...) and
      functions ([upd_pc], [upd_reg], [evaluate], ...) are the short names;
      the asm state's are written [asmSem.pc] etc., the target machine's
      [targetSem.evaluate], [targetSem.ptr_reg] etc.  labLang's [Jump],
      [JumpCmp], [Call] are the short names, ASM's [asm.Jump] etc.;
      [Halt] is targetSem's machine result, labLang's instruction is
      [labLang.Halt].  HOL's [mc_conf.target.config] is
      [asmProps.config mc_conf.(target)].
    - HOL's [s with f := v] is [set_<f> v s] (labSem or asmSem helpers;
      targetSem's for machine configurations).
    - HOL's tuples are right-nested: [state_rel (mc_conf,code2,labs,p)] is
      [state_rel (mc_conf, (code2, (labs, p)))].
    - [line_similar], [code_similar], [has_io_name], [enc_with_nop],
      [asm_step_nop], [line_ok], [lines_ok], [all_enc_ok], [good_code] and
      the relations are [Prop]-valued; [has_odd_inst] is [bool]-valued.
    - [sec_loc_to_pc] decides HOL's [?n1 k. z = Label n1 n2 k]
      classically ([⌜_⌝]), as labSem's [loc_to_pc] does.
    - HOL's overload [len_no_lab] is an [Abbreviation].
    - Not ported: the ML value [evaluate_nop_step] (a specialisation of
      [asm_step_IMP_evaluate_step_find_next], used inline), the ML
      bindings [line_similar_ind], [code_similar_ind], [has_io_name_ind],
      [line_ok_ind], [all_enc_ok_ind], [pos_val_ind],
      [sec_loc_to_pc_ind] (structural induction is used instead). *)

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
Import wordLang (word_loc, Word, Loc).
Import wordSem (mem_load_byte_aux, mem_store_byte_aux, write_bytearray).
Import backendProps (restrict_nonzero).
Open Scope N_scope.

(** ** Clocks of the target semantics *)

Section Clocks.
Context {a : N} {B C Ffi : Type}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "evaluate_ignore_clocks" *)
Theorem evaluate_ignore_clocks : forall (mc_conf : machine_config a B C) (ffi : ffi_state Ffi)
    k ms r1 ms1 st1 k' r2 ms2 st2,
  targetSem.evaluate mc_conf ffi k ms = (r1, (ms1, st1)) /\ r1 <> TimeOut /\
  targetSem.evaluate mc_conf ffi k' ms = (r2, (ms2, st2)) /\ r2 <> TimeOut ->
  (r1, (ms1, st1)) = (r2, (ms2, st2)).
Proof.
  intros mc_conf ffi k ms r1 ms1 st1 k' r2 ms2 st2 (H1 & Hr1 & H2 & Hr2).
  pose proof (evaluate_add_clock mc_conf ffi k ms k' r1 ms1 st1 (conj H1 Hr1)) as E1.
  pose proof (evaluate_add_clock mc_conf ffi k' ms k r2 ms2 st2 (conj H2 Hr2)) as E2.
  rewrite N.add_comm in E2. rewrite E1 in E2. exact E2.
Qed.

End Clocks.

(** ** [sec_loc_to_pc] *)

Section SecLoc.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_loc_to_pc_def" *)
Fixpoint sec_loc_to_pc (n2 : N) (xs : list (line a)) : option N :=
  if n2 =? 0 then SOME 0
  else match xs with
       | [] => NONE
       | z :: zs =>
           if ⌜exists n1 k, z = Label n1 n2 k⌝ then SOME 0
           else if is_Label z then sec_loc_to_pc n2 zs
           else OPTION_MAP SUC (sec_loc_to_pc n2 zs)
       end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_loc_to_pc_cons" *)
Theorem sec_loc_to_pc_cons : forall n2 l lines,
  sec_loc_to_pc n2 (l :: lines) =
  if ⌜n2 = 0 \/ (exists n1 k, l = Label n1 n2 k)⌝ then SOME 0
  else OPTION_MAP (if is_Label l then I else SUC) (sec_loc_to_pc n2 lines).
Proof.
  intros n2 l lines. cbn [sec_loc_to_pc].
  destruct (N.eqb_spec n2 0) as [E|E].
  - rewrite (proj2 (bool_decide_spec _)) by (left; exact E). reflexivity.
  - destruct (bool_decide (exists n1 k, l = Label n1 n2 k)) eqn:H.
    + rewrite (proj2 (bool_decide_spec _)); [reflexivity|].
      right; exact (proj1 (bool_decide_spec _) H).
    + destruct (bool_decide (n2 = 0 \/ (exists n1 k, l = Label n1 n2 k))) eqn:H2.
      * apply bool_decide_spec in H2. destruct H2 as [H2|H2]; [contradiction|].
        rewrite (proj2 (bool_decide_spec _) H2) in H. discriminate.
      * destruct (is_Label l); [|reflexivity].
        destruct (sec_loc_to_pc n2 lines); reflexivity.
Qed.

End SecLoc.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "len_no_lab" *)
Abbreviation len_no_lab xs := (LENGTH (FILTER (negb ∘ is_Label) xs)).

Section LocToPc.
Context {a : N}.

Lemma option_map_add_0 (x : option N) : OPTION_MAP (N.add 0) x = x.
Proof. destruct x; reflexivity. Qed.

Lemma bool_decide_true (P : Prop) `{Decision P} : P -> bool_decide P = true.
Proof. apply bool_decide_spec. Qed.

Lemma bool_decide_false (P : Prop) `{Decision P} : ~ P -> bool_decide P = false.
Proof.
  intros H'. destruct (bool_decide P) eqn:E; [|reflexivity].
  apply bool_decide_spec in E. contradiction.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "loc_to_pc_thm" *)
Theorem loc_to_pc_thm : forall n1 n2 (ls : list (sec a)),
  EVERY sec_labels_ok ls ->
  loc_to_pc n1 n2 ls =
    match ls with
    | [] => NONE
    | Section_ k xs :: ys =>
        if n1 =? k then
          match sec_loc_to_pc n2 xs with
          | NONE => OPTION_MAP (N.add (LENGTH (FILTER (negb ∘ is_Label) xs))) (loc_to_pc n1 n2 ys)
          | x => x
          end
        else OPTION_MAP (N.add (LENGTH (FILTER (negb ∘ is_Label) xs))) (loc_to_pc n1 n2 ys)
    end.
Proof.
  intros n1 n2 ls Hok. destruct ls as [|[k xs] ys]; [reflexivity|].
  cbn [EVERY sec_labels_ok] in Hok. apply Bool.andb_true_iff in Hok as [Hok _].
  induction xs as [|z zs IH].
  - rewrite (proj2 loc_to_pc_def) . cbn [sec_loc_to_pc FILTER LENGTH].
    destruct (N.eqb_spec n1 k) as [->|Hk].
    + rewrite N.eqb_refl. destruct (N.eqb_spec n2 0); cbn; [reflexivity|].
      symmetry; apply option_map_add_0.
    + rewrite (proj2 (N.eqb_neq k n1)) by congruence. cbn. symmetry; apply option_map_add_0.
  - cbn [EVERY] in Hok. apply Bool.andb_true_iff in Hok as [Hz Hok].
    specialize (IH Hok).
    rewrite (proj2 loc_to_pc_def).
    change (LENGTH (FILTER (negb ∘ is_Label) (z :: zs)))
      with (LENGTH (if negb (is_Label z) then z :: FILTER (negb ∘ is_Label) zs
                    else FILTER (negb ∘ is_Label) zs)).
    destruct (N.eqb_spec n1 k) as [->|Hk].
    + rewrite N.eqb_refl. destruct (N.eqb_spec n2 0) as [->|Hn2].
      * cbn. reflexivity.
      * cbn [andb negb] in IH |- *. rewrite ?Bool.andb_true_r in IH |- *.
        cbn [sec_loc_to_pc]. rewrite (proj2 (N.eqb_neq n2 0) Hn2).
        assert (Hex : bool_decide (exists k0, z = Label k n2 k0) =
                      bool_decide (exists n0 k0, z = Label n0 n2 k0)).
        { destruct z as [l1 l2 l3| |]; cbn in Hz.
          - apply Bool.andb_true_iff in Hz as [Hz _]. apply N.eqb_eq in Hz; subst l1.
            destruct (decide (l2 = n2)) as [->|Hne].
            + rewrite !bool_decide_true; [reflexivity| |]; eauto.
            + rewrite !bool_decide_false; [reflexivity| |];
                intros H'; destruct H' as (? & ? & H') || destruct H' as (? & H');
                injection H'; intros; congruence.
          - rewrite !bool_decide_false; [reflexivity| |];
              intros H'; repeat destruct H' as (? & H'); discriminate.
          - rewrite !bool_decide_false; [reflexivity| |];
              intros H'; repeat destruct H' as (? & H'); discriminate. }
        rewrite Hex.
        destruct (bool_decide (exists n0 k0, z = Label n0 n2 k0)); [reflexivity|].
        rewrite IH. destruct (is_Label z); cbn [negb andb].
        -- destruct (sec_loc_to_pc n2 zs); reflexivity.
        -- destruct (sec_loc_to_pc n2 zs); cbn [andb option_map LENGTH]; [f_equal; lia|].
           destruct (loc_to_pc k n2 ys); cbn; [f_equal; lia|reflexivity].
    + rewrite (proj2 (N.eqb_neq k n1)) by congruence. cbn [andb].
      assert (Hex : bool_decide (exists k0, z = Label n1 n2 k0) = false).
      { apply bool_decide_false. intros [k0 ->]. cbn in Hz.
        apply Bool.andb_true_iff in Hz as [Hz _]. apply N.eqb_eq in Hz. congruence. }
      rewrite Hex. cbn [andb].
      rewrite IH. destruct (is_Label z); cbn [negb]; [reflexivity|].
      cbn [LENGTH]. destruct (loc_to_pc n1 n2 ys); cbn; [f_equal; lia|reflexivity].
Qed.

End LocToPc.

(** Word arithmetic with literals (Galette helper). *)
Ltac word_arith :=
  apply zcong_word_eq;
  repeat rewrite ?Zc_add, ?Zc_mul, ?Zc_sub, ?Zc_neg, ?Zc_n2w;
  rewrite ?N2Z.inj_add, ?N2Z.inj_mul, ?N2Z.inj_succ;
  apply zcong_eq; ring.

(** ** Relating an asm step to target evaluation, with nop padding *)

Section NopSteps.
Context {a : N} {B C Ffi : Type}.
Local Open Scope word_scope.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_with_nop_def" *)
Definition enc_with_nop (enc : asm.asm a -> list word8) (b : asm.asm a) (bytes : list word8) : Prop :=
  let init := enc b in
  let step := enc (Inst asm.Skip) in
  if (LENGTH step =? 0)%N then bytes = init else
    let n := ((LENGTH bytes - LENGTH init) DIV LENGTH step)%N in
    bytes = init ++ FLAT (REPLICATE n step).

Lemma LENGTH_app {X} (l1 l2 : list X) : LENGTH (l1 ++ l2) = (LENGTH l1 + LENGTH l2)%N.
Proof. rewrite !LENGTH_length, length_app; lia. Qed.

Lemma LENGTH_FLAT_REPLICATE {X} n (l : list X) :
  LENGTH (FLAT (REPLICATE n l)) = (n * LENGTH l)%N.
Proof.
  induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (REPLICATE_thm n l)). cbn [FLAT concat].
  rewrite LENGTH_app, IH; lia.
Qed.

Lemma FLAT_REPLICATE_NIL {X} n : FLAT (REPLICATE n ([] : list X)) = [].
Proof.
  induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (REPLICATE_thm n [])). cbn. exact IH.
Qed.

Lemma LENGTH_NIL {X} (l : list X) : LENGTH l = 0%N <-> l = [].
Proof. destruct l; cbn [LENGTH]; split; intros; try discriminate; try reflexivity; lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_with_nop_thm" *)
Theorem enc_with_nop_thm : forall enc (b : asm.asm a) bytes,
  enc_with_nop enc b bytes <->
  exists n, bytes = enc b ++ FLAT (REPLICATE n (enc (Inst asm.Skip))).
Proof.
  intros enc b bytes. unfold enc_with_nop. cbv zeta.
  destruct (N.eqb_spec (LENGTH (enc (Inst asm.Skip))) 0) as [E|E].
  - apply LENGTH_NIL in E. rewrite E. split.
    + intros ->. exists 0%N. rewrite FLAT_REPLICATE_NIL, app_nil_r; reflexivity.
    + intros [n ->]. rewrite FLAT_REPLICATE_NIL, app_nil_r; reflexivity.
  - split; [intros H; eexists; exact H|].
    intros [n Hn]. rewrite Hn at 1. do 3 f_equal.
    rewrite Hn, LENGTH_app, LENGTH_FLAT_REPLICATE.
    replace (LENGTH (enc b) + n * LENGTH (enc (Inst asm.Skip)) - LENGTH (enc b))%N
      with (n * LENGTH (enc (Inst asm.Skip)))%N by lia.
    rewrite N.div_mul by exact E. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "asm_step_nop_def" *)
Definition asm_step_nop (bytes : list word8) (c : asm_config a) (s1 : asm_state a)
    (i : asm.asm a) (s2 : asm_state a) : Prop :=
  bytes_in_memory s1.(asmSem.pc) bytes s1.(asmSem.mem) s1.(asmSem.mem_domain) /\
  enc_with_nop (encode c) i bytes /\
  (match asm.link_reg c with NONE => True | SOME r => s1.(asmSem.lr) = r end) /\
  (s1.(asmSem.be) = big_endian c) /\ s1.(asmSem.align) = code_alignment c /\
  asm i (s1.(asmSem.pc) + n2w (LENGTH bytes)) s1 = s2 /\ ~ s2.(asmSem.failed) /\
  asm_ok i c.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "shift_interfer_0" *)
Theorem shift_interfer_0 : @shift_interfer a B C 0 = I.
Proof.
  apply functional_extensionality; intros [] ; unfold shift_interfer, set_next_interfer, I.
  cbn. f_equal. unfold shift_seq. apply functional_extensionality; intros i.
  rewrite N.add_0_r. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "upd_pc_with_pc" *)
Theorem upd_pc_with_pc : forall s1 : asm_state a, asmSem.upd_pc s1.(asmSem.pc) s1 = s1.
Proof. intros []; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "shift_interfer_twice" *)
Theorem shift_interfer_twice : forall l' l (c : machine_config a B C),
  shift_interfer l' (shift_interfer l c) = shift_interfer (l + l') c.
Proof. intros. rewrite shift_interfer_intro, N.add_comm; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "ffi_entry_pcs_disjoint_LENGTH_shorter" *)
Theorem ffi_entry_pcs_disjoint_LENGTH_shorter : forall (c : machine_config a B C) s1 l1 l2,
  ffi_entry_pcs_disjoint c s1 l1 /\ (l2 <= l1)%N ->
  ffi_entry_pcs_disjoint c s1 l2.
Proof.
  intros c s1 l1 l2 [H Hle]. unfold ffi_entry_pcs_disjoint in *.
  rewrite DISJOINT_ALT in *. intros x Hx (a0 & -> & Ha).
  apply (H _ Hx). exists a0. split; [reflexivity|lia].
Qed.

Lemma shift_interfer_target l (c : machine_config a B C) :
  target (shift_interfer l c) = target c.
Proof. reflexivity. Qed.

Lemma asm_Skip_ok (cfg : asm_config a) : asm_ok (Inst asm.Skip) cfg = true.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "evaluate_nop_steps" *)
Theorem evaluate_nop_steps : forall n (s1 : asm_state a) (ms1 : B) (c : machine_config a B C)
    (io : ffi_state Ffi),
  encoder_correct c.(target) /\
  c.(prog_addresses) = s1.(asmSem.mem_domain) /\
  ffi_entry_pcs_disjoint c s1
    (n * LENGTH (encode (asmProps.config c.(target)) (Inst asm.Skip))) /\
  interference_ok c.(next_interfer) (proj c.(target) s1.(asmSem.mem_domain)) /\
  bytes_in_memory s1.(asmSem.pc)
    (FLAT (REPLICATE n (encode (asmProps.config c.(target)) (Inst asm.Skip)))) s1.(asmSem.mem)
    s1.(asmSem.mem_domain) /\
  (match asm.link_reg (asmProps.config c.(target)) with NONE => True | SOME r => s1.(asmSem.lr) = r end) /\
  (s1.(asmSem.be) = big_endian (asmProps.config c.(target))) /\
  s1.(asmSem.align) = code_alignment (asmProps.config c.(target)) /\ ~ s1.(asmSem.failed) /\
  target_state_rel c.(target) s1 ms1 ->
  exists l ms2, forall k,
    targetSem.evaluate c io (k + l) ms1 = targetSem.evaluate (shift_interfer l c) io k ms2 /\
    find_next_interference c io (k + l) ms1 =
      find_next_interference (shift_interfer l c) io k ms2 /\
    target_state_rel c.(target)
      (asmSem.upd_pc
        (s1.(asmSem.pc) +
         n2w (n * LENGTH (encode (asmProps.config c.(target)) (Inst asm.Skip)))) s1)
      ms2.
Proof.
  induction n as [|n IH] using N.peano_ind;
    intros s1 ms1 c io (Henc & Hdom & Hdis & Hint & Hb & Hlr & Hbe & Hal & Hf & Hrel).
  - exists 0%N, ms1. intros k. rewrite shift_interfer_0, N.add_0_r. unfold I.
    split; [reflexivity|split; [reflexivity|]].
    rewrite N.mul_0_l, (proj1 WORD_ADD_0), upd_pc_with_pc. exact Hrel.
  - set (cfg := asmProps.config c.(target)) in *.
    set (sk := encode cfg (Inst asm.Skip)) in *.
    rewrite (proj2 (REPLICATE_thm n sk)) in Hb. cbn [FLAT concat] in Hb.
    apply bytes_in_memory_APPEND in Hb as [Hb1 Hb2].
    destruct (asm_step_IMP_evaluate_step_find_next c s1 ms1 io (Inst asm.Skip)) as (l & ms2 & Hl).
    { split; [exact Henc|split; [exact Hdom|split; [|split; [exact Hint|split; [|exact Hrel]]]]].
      - apply (ffi_entry_pcs_disjoint_LENGTH_shorter c s1 (SUC n * LENGTH sk)).
        split; [exact Hdis|]. fold cfg sk. lia.
      - unfold asm_step. fold cfg sk. split; [exact Hb1|]. split; [exact Hlr|].
        split; [exact Hbe|]. split; [exact Hal|]. split; [reflexivity|].
        split; [exact Hf|]. apply asm_Skip_ok. }
    fold cfg sk in Hl.
    destruct (IH (asmSem.upd_pc (s1.(asmSem.pc) + n2w (LENGTH sk)) s1) ms2
                 (shift_interfer l c) io) as (l' & ms2' & Hl').
    { rewrite shift_interfer_target. fold cfg sk.
      split; [exact Henc|]. split; [exact Hdom|].
      split.
      { unfold ffi_entry_pcs_disjoint in *. rewrite DISJOINT_ALT in *.
        intros x Hx (a0 & -> & Ha). apply (Hdis _ Hx).
        exists (LENGTH sk + a0)%N. cbn [asmSem.upd_pc asmSem.set_pc asmSem.pc].
        split; [|lia]. rewrite <- WORD_ADD_ASSOC, word_add_n2w. reflexivity. }
      split; [intros i ms; apply Hint|].
      split; [exact Hb2|]. split; [exact Hlr|]. split; [exact Hbe|].
      split; [exact Hal|]. split; [exact Hf|].
      destruct (Hl 0%N) as (_ & _ & H & _). exact H. }
    exists (l' + l)%N, ms2'. intros k.
    destruct (Hl (k + l')%N) as (E1 & E2 & _ & _).
    destruct (Hl' k) as (E1' & E2' & E3').
    rewrite shift_interfer_target in E3'. fold cfg sk in E3'.
    rewrite shift_interfer_intro in E1', E2'.
    rewrite N.add_assoc, E1, E2, E1', E2'. split; [reflexivity|split; [reflexivity|]].
    revert E3'. unfold asmSem.upd_pc, asmSem.set_pc; cbn [asmSem.pc asmSem.regs asmSem.fp_regs
      asmSem.mem asmSem.mem_domain asmSem.lr asmSem.align asmSem.be asmSem.failed].
    match goal with |- target_state_rel _ ?x _ -> target_state_rel _ ?y _ =>
      replace y with x; [exact (fun H => H)|] end.
    f_equal. word_arith.
Qed.

Lemma asm_pc_cases (i : asm.asm a) (s : asm_state a) :
  (forall x, i <> asm.Call x) ->
  (forall w w', asm i w s = asm i w' s) \/
  (forall w, asm i w s = asmSem.upd_pc w (asm i (n2w 0) s)).
Proof.
  intros Hc. destruct i as [i0|w|cmp r ri w|w|r|r w]; cbn [asm].
  - right; intros; reflexivity.
  - left; intros; reflexivity.
  - destruct (word_cmp cmp (asmSem.read_reg r s) (asmSem.reg_imm ri s)); [left|right];
      intros; reflexivity.
  - exfalso; exact (Hc w eq_refl).
  - left; intros; reflexivity.
  - right; intros; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "asm_step_IMP_evaluate_step_nop" *)
Theorem asm_step_IMP_evaluate_step_nop : forall (c : machine_config a B C) (s1 : asm_state a) ms1
    (io : ffi_state Ffi) i s2 bytes,
  encoder_correct c.(target) /\
  c.(prog_addresses) = s1.(asmSem.mem_domain) /\
  ffi_entry_pcs_disjoint c s1 (LENGTH bytes) /\
  interference_ok c.(next_interfer) (proj c.(target) s1.(asmSem.mem_domain)) /\
  bytes_in_memory s1.(asmSem.pc) bytes s2.(asmSem.mem) s1.(asmSem.mem_domain) /\
  asm_step_nop bytes (asmProps.config c.(target)) s1 i s2 /\
  s2 = asm i (s1.(asmSem.pc) + n2w (LENGTH bytes)) s1 /\
  target_state_rel c.(target) s1 ms1 /\
  (forall x, i <> asm.Call x) ->
  exists l ms2, forall k,
    targetSem.evaluate c io (k + l) ms1 = targetSem.evaluate (shift_interfer l c) io k ms2 /\
    find_next_interference c io (k + l) ms1 =
      find_next_interference (shift_interfer l c) io k ms2 /\
    target_state_rel c.(target) s2 ms2 /\ l <> 0%N.
Proof.
  intros c s1 ms1 io i s2 bytes (Henc & Hdom & Hdis & Hint & Hb2 & Hnop & Hs2 & Hrel & Hcall).
  destruct Hnop as (Hb & Hen & Hlr & Hbe & Hal & _ & Hf & Hok).
  subst s2.
  set (cfg := asmProps.config c.(target)) in *.
  apply enc_with_nop_thm in Hen as [n Hbytes].
  set (ei := encode cfg i) in *. set (sk := encode cfg (Inst asm.Skip)) in *.
  rewrite Hbytes in Hb. apply bytes_in_memory_APPEND in Hb as [Hb1 _].
  destruct (asm_step_IMP_evaluate_step_find_next c s1 ms1 io i) as (l & ms2 & Hl).
  { split; [exact Henc|]. split; [exact Hdom|]. split.
    { apply (ffi_entry_pcs_disjoint_LENGTH_shorter c s1 (LENGTH bytes)).
      split; [exact Hdis|]. rewrite Hbytes, LENGTH_app. fold cfg ei. lia. }
    split; [exact Hint|]. split; [|exact Hrel].
    unfold asm_step. fold cfg ei. split; [exact Hb1|]. split; [exact Hlr|].
    split; [exact Hbe|]. split; [exact Hal|]. split; [reflexivity|].
    split; [|exact Hok].
    rewrite (asm_failed_ignore_new_pc i (s1.(asmSem.pc) + n2w (LENGTH bytes))). exact Hf. }
  fold cfg ei in Hl.
  destruct (asm_pc_cases i s1 Hcall) as [Hind|Hupd].
  - exists l, ms2. intros k. destruct (Hl k) as (E1 & E2 & E3 & E4).
    split; [exact E1|]. split; [exact E2|]. split; [|exact E4].
    rewrite (Hind _ (s1.(asmSem.pc) + n2w (LENGTH ei))). exact E3.
  - set (smid := asm i (s1.(asmSem.pc) + n2w (LENGTH ei)) s1) in *.
    destruct (asm_consts i (s1.(asmSem.pc) + n2w (LENGTH ei)) s1) as (Cbe & Clr & Cal & Cdom).
    fold smid in Cbe, Clr, Cal, Cdom.
    assert (Hpc : smid.(asmSem.pc) = s1.(asmSem.pc) + n2w (LENGTH ei)).
    { unfold smid. rewrite (Hupd (s1.(asmSem.pc) + n2w (LENGTH ei))). reflexivity. }
    destruct (evaluate_nop_steps n smid ms2 (shift_interfer l c) io) as (l' & ms2' & Hl').
    { rewrite shift_interfer_target. fold cfg sk.
      split; [exact Henc|]. split; [rewrite Cdom; exact Hdom|].
      split.
      { unfold ffi_entry_pcs_disjoint in *. rewrite DISJOINT_ALT in *.
        intros x Hx (a0 & -> & Ha). apply (Hdis _ Hx).
        exists (LENGTH ei + a0)%N. rewrite Hpc.
        split; [rewrite <- WORD_ADD_ASSOC, word_add_n2w; reflexivity|].
        rewrite Hbytes, LENGTH_app, LENGTH_FLAT_REPLICATE. fold ei sk. lia. }
      split; [rewrite Cdom; intros j ms; apply Hint|].
      split.
      { rewrite Hbytes in Hb2. apply bytes_in_memory_APPEND in Hb2 as [_ Hb2].
        rewrite Hpc, Cdom. fold ei sk in Hb2.
        rewrite (asm_mem_ignore_new_pc i (s1.(asmSem.pc) + n2w (LENGTH ei))) in Hb2.
        exact Hb2. }
      split; [rewrite Clr; exact Hlr|]. split; [rewrite Cbe; exact Hbe|].
      split; [rewrite Cal; exact Hal|].
      split; [unfold smid; rewrite (asm_failed_ignore_new_pc i (s1.(asmSem.pc) + n2w (LENGTH bytes))); exact Hf|].
      destruct (Hl 0%N) as (_ & _ & H & _). exact H. }
    exists (l' + l)%N, ms2'. intros k.
    destruct (Hl (k + l')%N) as (E1 & E2 & _ & E4).
    destruct (Hl' k) as (E1' & E2' & E3').
    rewrite shift_interfer_target in E3'. fold cfg sk in E3'.
    rewrite shift_interfer_intro in E1', E2'.
    rewrite N.add_assoc, E1, E2, E1', E2'. split; [reflexivity|split; [reflexivity|]].
    split; [|lia].
    revert E3'. rewrite Hpc. unfold smid.
    rewrite (Hupd (s1.(asmSem.pc) + n2w (LENGTH ei))), (Hupd (s1.(asmSem.pc) + n2w (LENGTH bytes))).
    unfold asmSem.upd_pc, asmSem.set_pc; cbn [asmSem.pc asmSem.regs asmSem.fp_regs
      asmSem.mem asmSem.mem_domain asmSem.lr asmSem.align asmSem.be asmSem.failed].
    match goal with |- target_state_rel _ ?x _ -> target_state_rel _ ?y _ =>
      replace y with x; [exact (fun H => H)|] end.
    f_equal. rewrite Hbytes, LENGTH_app, LENGTH_FLAT_REPLICATE. fold ei sk. word_arith.
Qed.

End NopSteps.

(** ** Label lookup *)

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lab_lookup_def" *)
Definition lab_lookup {X} (k1 k2 : N) (labs : spt (spt X)) : option X :=
  match lookup k1 labs with
  | NONE => NONE
  | SOME f => lookup k2 f
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lab_lookup_IMP" *)
Theorem lab_lookup_IMP : forall l1 l2 labs x,
  lab_lookup l1 l2 labs = SOME x -> find_pos (Lab l1 l2) labs = x.
Proof.
  intros l1 l2 labs x. unfold lab_lookup, find_pos, lookup_any.
  destruct (lookup l1 labs) as [f|]; [|discriminate].
  intros H. rewrite H. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "labs_domain_def" *)
Definition labs_domain {X} (labs : spt (spt X)) : N * N -> Prop :=
  fun x => exists n1 n2, x = (n1, n2) /\ lab_lookup n1 n2 labs <> NONE.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "labs_domain_LN" *)
Theorem labs_domain_LN : forall X, labs_domain (@LN (spt X)) = {}.
Proof.
  intros X. apply EXTENSION. intros x. split; [|intros []].
  intros (n1 & n2 & _ & H). apply H. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "labs_domain_insert" *)
Theorem labs_domain_insert : forall {X} k (s : spt X) labs,
  k NOTIN domain labs ->
  labs_domain (insert k s labs) =
    IMAGE (fun n2 => (k, n2)) (domain s) UNION labs_domain labs.
Proof.
  intros X k s labs Hk. apply EXTENSION. intros x.
  rewrite IN_UNION, IN_IMAGE. unfold labs_domain, lab_lookup, pred_set.IN.
  setoid_rewrite lookup_insert. split.
  - intros (n1 & n2 & -> & H). destruct (decide (n1 = k)) as [->|Hne].
    + left. exists n2. split; [reflexivity|]. apply domain_lookup.
      destruct (lookup n2 s); [eexists; reflexivity|congruence].
    + right. exists n1, n2. split; [reflexivity|exact H].
  - intros [(n2 & -> & H)|(n1 & n2 & -> & H)].
    + exists k, n2. split; [reflexivity|]. destruct (decide (k = k)); [|congruence].
      apply domain_lookup in H. destruct H as [v Hv]. rewrite Hv. discriminate.
    + exists n1, n2. split; [reflexivity|]. destruct (decide (n1 = k)) as [->|]; [|exact H].
      exfalso. apply Hk. apply domain_lookup.
      destruct (lookup k labs); [eexists; reflexivity|]. exfalso; apply H; reflexivity.
Qed.

(** ** Syntactic relations between the source and the assembled code *)

Section Similar.
Context {a : N}.

(** HOL [has_odd_inst]: recursion on the sections, then on the lines. *)
Fixpoint has_odd_inst (l : list (sec a)) : bool :=
  match l with
  | [] => false
  | Section_ k ys :: xs =>
      (fix go (ys : list (line a)) : bool :=
         match ys with
         | [] => has_odd_inst xs
         | y :: ys => negb (EVEN (line_length y)) || go ys
         end) ys
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "has_odd_inst_def" *)
Theorem has_odd_inst_def : forall k xs y ys,
  has_odd_inst [] = false /\
  has_odd_inst (Section_ k [] :: xs) = has_odd_inst xs /\
  has_odd_inst (Section_ k (y :: ys) :: xs) =
    (negb (EVEN (line_length y)) || has_odd_inst (Section_ k ys :: xs)).
Proof. repeat split. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_def" *)
Definition line_similar (l1 l2 : line a) : Prop :=
  match l1, l2 with
  | Label k1 k2 l, Label k1' k2' l' => k1 = k1' /\ k2 = k2'
  | Asm b bytes l, Asm b' bytes' l' => b = b'
  | LabAsm a0 w bytes l, LabAsm a' w' bytes' l' => a0 = a'
  | _, _ => False
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_def" *)
Fixpoint code_similar (c1 c2 : list (sec a)) : Prop :=
  match c1, c2 with
  | [], [] => True
  | Section_ s1 lines1 :: rest1, Section_ s2 lines2 :: rest2 =>
      code_similar rest1 rest2 /\ LIST_REL line_similar lines1 lines2 /\ s1 = s2
  | _, _ => False
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_sym" *)
Theorem line_similar_sym : forall l1 l2, line_similar l1 l2 -> line_similar l2 l1.
Proof. intros [] [] H; cbn in *; intuition congruence. Qed.

Lemma LIST_REL_sym {X} (R : X -> X -> Prop) l1 l2 :
  (forall x y, R x y -> R y x) -> LIST_REL R l1 l2 -> LIST_REL R l2 l1.
Proof. intros HR H; induction H; constructor; auto. Qed.

Lemma LIST_REL_refl {X} (R : X -> X -> Prop) l : (forall x, R x x) -> LIST_REL R l l.
Proof. intros HR; induction l; constructor; auto. Qed.

Lemma LIST_REL_trans {X} (R : X -> X -> Prop) l1 l2 l3 :
  (forall x y z, R x y -> R y z -> R x z) ->
  LIST_REL R l1 l2 -> LIST_REL R l2 l3 -> LIST_REL R l1 l3.
Proof.
  intros HR H; revert l3; induction H; intros l3 H3; inversion H3; subst; constructor; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_sym" *)
Theorem code_similar_sym : forall code1 code2,
  code_similar code1 code2 -> code_similar code2 code1.
Proof.
  induction code1 as [|[k1 l1] c1 IH]; intros [|[k2 l2] c2]; cbn; try tauto.
  intros (H1 & H2 & ->). split; [apply IH, H1|]. split; [|reflexivity].
  apply LIST_REL_sym; [exact line_similar_sym|exact H2].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_refl" *)
Theorem line_similar_refl : forall l, line_similar l l.
Proof. intros []; cbn; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_refl" *)
Theorem code_similar_refl : forall code, code_similar code code.
Proof.
  induction code as [|[k l] c IH]; cbn; [exact Logic.I|].
  split; [exact IH|split; [apply LIST_REL_refl, line_similar_refl|reflexivity]].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_trans" *)
Theorem line_similar_trans : forall x y z,
  line_similar x y /\ line_similar y z -> line_similar x z.
Proof. intros [] [] [] [H1 H2]; cbn in *; intuition congruence. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_trans" *)
Theorem code_similar_trans : forall c1 c2 c3,
  code_similar c1 c2 /\ code_similar c2 c3 -> code_similar c1 c3.
Proof.
  induction c1 as [|[k1 l1] c1 IH]; intros [|[k2 l2] c2] [|[k3 l3] c3]; cbn; try tauto.
  intros [(H1 & H2 & ->) (H1' & H2' & ->)]. split; [apply (IH c2); auto|].
  split; [|reflexivity]. eapply LIST_REL_trans; [|exact H2|exact H2'].
  intros x y z Hxy Hyz; apply (line_similar_trans x y z); auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_nil" *)
Theorem code_similar_nil : forall l,
  (code_similar [] l <-> l = []) /\ (code_similar l [] <-> l = []).
Proof. intros [|[]]; cbn; split; split; intros; try discriminate; tauto. Qed.

Lemma LIST_REL_app {X Y} (R : X -> Y -> Prop) l1 l2 r1 r2 :
  LIST_REL R l1 l2 -> LIST_REL R r1 r2 -> LIST_REL R (l1 ++ r1) (l2 ++ r2).
Proof. intros H; induction H; intros; cbn; [assumption|constructor; auto]. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_append" *)
Theorem code_similar_append : forall l1 l2 r1 r2,
  code_similar l1 l2 /\ code_similar r1 r2 -> code_similar (l1 ++ r1) (l2 ++ r2).
Proof.
  induction l1 as [|[k1 x1] l1 IH]; intros [|[k2 x2] l2] r1 r2; cbn; try tauto.
  intros [(H1 & H2 & ->) H3]. split; [apply IH; auto|auto].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_sec_label_ok" *)
Theorem line_similar_sec_label_ok : forall s l1 l2,
  EVERY (sec_label_ok s) l1 /\ LIST_REL line_similar l1 l2 ->
  EVERY (sec_label_ok s) l2.
Proof.
  intros s l1 l2 [H1 H2]. induction H2 as [|x y l1 l2 Hxy Hl IH]; [reflexivity|].
  cbn [EVERY] in *. apply Bool.andb_true_iff in H1 as [Hx H1].
  apply Bool.andb_true_iff. split; [|apply IH, H1].
  destruct x, y; cbn in Hxy |- *; try contradiction; try reflexivity.
  destruct Hxy as [<- <-]. exact Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_sec_labels_ok" *)
Theorem code_similar_sec_labels_ok : forall c1 c2,
  EVERY sec_labels_ok c1 /\ code_similar c1 c2 -> EVERY sec_labels_ok c2.
Proof.
  induction c1 as [|[k1 x1] c1 IH]; intros [|[k2 x2] c2]; cbn; try tauto.
  intros [H1 (H2 & H3 & ->)]. apply Bool.andb_true_iff in H1 as [Ha Hb].
  apply Bool.andb_true_iff. split; [apply (line_similar_sec_label_ok k2 x1); auto|apply IH; auto].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_len_no_lab" *)
Theorem line_similar_len_no_lab : forall l1 l2,
  LIST_REL line_similar l1 l2 ->
  LENGTH (FILTER (negb ∘ is_Label) l1) = LENGTH (FILTER (negb ∘ is_Label) l2).
Proof.
  intros l1 l2 H. induction H as [|x y l1 l2 Hxy Hl IH]; [reflexivity|].
  destruct x, y; cbn in Hxy |- *; try contradiction; cbn [LENGTH]; rewrite IH; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_len_no_lab" *)
Theorem code_similar_len_no_lab : forall c1 c2 : list (sec a),
  code_similar c1 c2 ->
  MAP ((fun xs => LENGTH (FILTER (negb ∘ is_Label) xs)) ∘ Section_lines) c1 =
  MAP ((fun xs => LENGTH (FILTER (negb ∘ is_Label) xs)) ∘ Section_lines) c2.
Proof.
  induction c1 as [|[k1 x1] c1 IH]; intros [|[k2 x2] c2]; cbn; try tauto.
  intros (H1 & H2 & ->). rewrite (line_similar_len_no_lab _ _ H2), (IH _ H1). reflexivity.
Qed.

End Similar.

Section LineOk.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "word_loc_val_def" *)
Definition word_loc_val (p : word a) (labs : spt (spt N)) (x : word_loc a) : option (word a) :=
  match x with
  | Word w => SOME w
  | Loc k1 k2 =>
      match lab_lookup k1 k2 labs with
      | NONE => NONE
      | SOME q => SOME (p + n2w q)%w
      end
  end.

(** HOL [has_io_name]: recursion on the sections, then on the lines. *)
Fixpoint has_io_name (index : mlstring) (l : list (sec a)) : Prop :=
  match l with
  | [] => False
  | Section_ k ys :: xs =>
      (fix go (ys : list (line a)) : Prop :=
         match ys with
         | [] => has_io_name index xs
         | y :: ys =>
             go ys \/ match y with LabAsm (CallFFI i) _ _ _ => i = index | _ => False end
         end) ys
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "has_io_name_def" *)
Theorem has_io_name_def : forall index k xs y ys,
  (has_io_name index [] <-> False) /\
  (has_io_name index (Section_ k [] :: xs) <-> has_io_name index xs) /\
  (has_io_name index (Section_ k (y :: ys) :: xs) <->
     has_io_name index (Section_ k ys :: xs) \/
     match y with LabAsm (CallFFI i) _ _ _ => i = index | _ => False end).
Proof. intros; repeat match goal with |- _ /\ _ => split end; split; intro Hx; exact Hx. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "word_loc_val_byte_def" *)
Definition word_loc_val_byte (p : word a) (labs : spt (spt N)) (m : word a -> word_loc a)
    (a0 : word a) (be : bool) : option word8 :=
  match word_loc_val p labs (m (byte_align a0)) with
  | SOME w => SOME (byte.get_byte a0 w be)
  | NONE => NONE
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_ok_def" *)
Definition line_ok (c : asm_config a) (labs : spt (spt N)) (ffis : list ffiname) (pos : N)
    (l : line a) : Prop :=
  match l with
  | Label _ _ l => EVEN pos /\ l = 0%N
  | Asm b bytes l =>
      enc_with_nop (encode c) (cbw_to_asm b) bytes /\
      LENGTH bytes = l /\ asm_ok (cbw_to_asm b) c
  | LabAsm labLang.Halt w bytes l =>
      let w1 := (n2w 0 - n2w (pos + ffi_offset))%w in
      enc_with_nop (encode c) (asm.Jump w1) bytes /\
      LENGTH bytes = l /\ asm_ok (asm.Jump w1) c
  | LabAsm Install w bytes l =>
      let w1 := (n2w 0 - n2w (pos + 2 * ffi_offset))%w in
      enc_with_nop (encode c) (asm.Jump w1) bytes /\
      LENGTH bytes = l /\ asm_ok (asm.Jump w1) c
  | LabAsm (CallFFI index) w bytes l =>
      let w1 := (n2w 0 - n2w (pos + (3 + get_ffi_index ffis (ExtCall index)) * ffi_offset))%w in
      enc_with_nop (encode c) (asm.Jump w1) bytes /\
      LENGTH bytes = l /\ asm_ok (asm.Jump w1) c
  | LabAsm (Call v24) w bytes l => False
  | LabAsm a0 w bytes l =>
      match get_label a0 with
      | Lab l1 l2 =>
          match lab_lookup l1 l2 labs with
          | NONE => False
          | SOME t =>
              let w1 := (n2w t - n2w pos)%w in
              enc_with_nop (encode c) (lab_inst w1 a0) bytes /\
              LENGTH bytes = l /\ asm_ok (lab_inst w1 a0) c
          end
      end
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_ok_def" *)
Fixpoint lines_ok (c : asm_config a) (labs : spt (spt N)) (ffis : list ffiname) (pos : N)
    (l : list (line a)) : Prop :=
  match l with
  | [] => True
  | y :: ys => line_ok c labs ffis pos y /\ lines_ok c labs ffis (pos + line_length y) ys
  end.

(** HOL [all_enc_ok]: recursion on the sections, then on the lines. *)
Fixpoint all_enc_ok (c : asm_config a) (labs : spt (spt N)) (ffis : list ffiname) (pos : N)
    (l : list (sec a)) : Prop :=
  match l with
  | [] => True
  | Section_ k ys :: xs =>
      (fix go (pos : N) (ys : list (line a)) : Prop :=
         match ys with
         | [] => EVEN pos /\ all_enc_ok c labs ffis pos xs
         | y :: ys => line_ok c labs ffis pos y /\ go (pos + line_length y) ys
         end) pos ys
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_ok_def" *)
Theorem all_enc_ok_def : forall c labs ffis pos k xs y ys,
  (all_enc_ok c labs ffis pos [] <-> True) /\
  (all_enc_ok c labs ffis pos (Section_ k [] :: xs) <->
     EVEN pos /\ all_enc_ok c labs ffis pos xs) /\
  (all_enc_ok c labs ffis pos (Section_ k (y :: ys) :: xs) <->
     line_ok c labs ffis pos y /\
     all_enc_ok c labs ffis (pos + line_length y) (Section_ k ys :: xs)).
Proof. intros; repeat match goal with |- _ /\ _ => split end; split; intro Hx; exact Hx. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_ok_cons" *)
Theorem all_enc_ok_cons : forall c labs ffis k xs ls pos,
  all_enc_ok c labs ffis pos (Section_ k ls :: xs) <->
  all_enc_ok c labs ffis (pos + SUM (MAP line_length ls)) xs /\
  EVEN (pos + SUM (MAP line_length ls)) /\
  lines_ok c labs ffis pos ls.
Proof.
  intros c labs ffis k xs ls. induction ls as [|y ys IH]; intros pos.
  - cbn [SUM MAP lines_ok]. rewrite N.add_0_r. cbn. tauto.
  - change (all_enc_ok c labs ffis pos (Section_ k (y :: ys) :: xs)) with
      (line_ok c labs ffis pos y /\ all_enc_ok c labs ffis (pos + line_length y) (Section_ k ys :: xs)).
    rewrite IH. cbn [SUM MAP lines_ok]. rewrite N.add_assoc. tauto.
Qed.

(** HOL [pos_val]: recursion on the sections, then on the lines. *)
Fixpoint pos_val (i pos : N) (l : list (sec a)) : N :=
  match l with
  | [] => pos
  | Section_ k ys :: xs =>
      (fix go (i pos : N) (ys : list (line a)) : N :=
         match ys with
         | [] => pos_val i pos xs
         | y :: ys =>
             if is_Label y then go i (pos + line_length y) ys
             else if i =? 0 then pos
             else go (i - 1) (pos + line_length y) ys
         end) i pos ys
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pos_val_def" *)
Theorem pos_val_def : forall i pos k xs y ys,
  pos_val i pos [] = pos /\
  pos_val i pos (Section_ k [] :: xs) = pos_val i pos xs /\
  pos_val i pos (Section_ k (y :: ys) :: xs) =
    if is_Label y then pos_val i (pos + line_length y) (Section_ k ys :: xs)
    else if i =? 0 then pos
    else pos_val (i - 1) (pos + line_length y) (Section_ k ys :: xs).
Proof. intros; repeat split. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pos_val_0" *)
Theorem pos_val_0 : forall xs c labs ffis pos,
  all_enc_ok c labs ffis pos xs -> pos_val 0 pos xs = pos.
Proof.
  induction xs as [|[k ys] xs IH]; intros c labs ffis pos H; [reflexivity|].
  revert pos H. induction ys as [|y ys IHy]; intros pos H.
  - destruct H as [_ H]. exact (IH _ _ _ _ H).
  - destruct H as [Hy H]. change (pos_val 0 pos (Section_ k (y :: ys) :: xs)) with
      (if is_Label y then pos_val 0 (pos + line_length y) (Section_ k ys :: xs)
       else if 0 =? 0 then pos else pos_val (0 - 1) (pos + line_length y) (Section_ k ys :: xs)).
    destruct y as [l1 l2 l3| |]; cbn [is_Label]; [|reflexivity|reflexivity].
    destruct Hy as [_ ->]. unfold line_length in H |- *. rewrite N.eqb_refl, N.add_0_r in H |- *.
    exact (IHy pos H).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_pos_val_def" *)
Fixpoint sec_pos_val (i pos : N) (l : list (line a)) : option N :=
  match l with
  | [] => NONE
  | y :: ys =>
      if is_Label y then sec_pos_val i (pos + line_length y) ys
      else if i =? 0 then SOME pos
      else sec_pos_val (i - 1) (pos + line_length y) ys
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_pos_val_too_big" *)
Theorem sec_pos_val_too_big : forall i pos lines,
  LENGTH (FILTER (negb ∘ is_Label) lines) <= i -> sec_pos_val i pos lines = NONE.
Proof.
  intros i pos lines; revert i pos; induction lines as [|y ys IH]; intros i pos H; [reflexivity|].
  cbn [sec_pos_val]. cbn [FILTER] in H. destruct (is_Label y); cbn [negb LENGTH] in H.
  - apply IH, H.
  - destruct (N.eqb_spec i 0); [lia|]. apply IH. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "EVERY_is_Label_sec_pos_val" *)
Theorem EVERY_is_Label_sec_pos_val : forall n pos lines,
  EVERY is_Label lines -> sec_pos_val n pos lines = NONE.
Proof.
  intros n pos lines; revert pos; induction lines as [|y ys IH]; intros pos H; [reflexivity|].
  cbn [EVERY] in H. apply Bool.andb_true_iff in H as [Hy H]. cbn [sec_pos_val].
  rewrite Hy. apply IH, H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pos_val_thm0" *)
Theorem pos_val_thm0 : forall i pos acc,
  pos_val i pos acc =
    match acc with
    | [] => pos
    | Section_ k s :: ss =>
        match sec_pos_val i pos s with
        | NONE => pos_val (i - LENGTH (FILTER (negb ∘ is_Label) s))
                    (pos + SUM (MAP line_length s)) ss
        | SOME x => x
        end
    end.
Proof.
  intros i pos [|[k s] ss]; [reflexivity|]. revert i pos.
  induction s as [|y ys IH]; intros i pos.
  - cbn. rewrite N.sub_0_r, N.add_0_r. reflexivity.
  - change (pos_val i pos (Section_ k (y :: ys) :: ss)) with
      (if is_Label y then pos_val i (pos + line_length y) (Section_ k ys :: ss)
       else if i =? 0 then pos else pos_val (i - 1) (pos + line_length y) (Section_ k ys :: ss)).
    cbn [sec_pos_val FILTER MAP SUM]. destruct (is_Label y); cbn [negb LENGTH].
    + rewrite IH, N.add_assoc. reflexivity.
    + destruct (N.eqb_spec i 0) as [->|Hi]; [reflexivity|].
      rewrite IH, N.add_assoc. destruct (sec_pos_val _ _ _); [reflexivity|].
      f_equal. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pos_val_thm" *)
Theorem pos_val_thm : forall i pos k s ss,
  pos_val i pos [] = pos /\
  pos_val i pos (Section_ k s :: ss) =
    match sec_pos_val i pos s with
    | NONE => pos_val (i - LENGTH (FILTER (negb ∘ is_Label) s))
                (pos + SUM (MAP line_length s)) ss
    | SOME x => x
    end.
Proof. intros. split; [reflexivity|]. exact (pos_val_thm0 i pos (Section_ k s :: ss)). Qed.

End LineOk.

(** ** Good code, shared memory and the state relation *)

Section GoodCode.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "good_code_def" *)
Definition good_code {X} (c : asm_config a) (labs : spt (spt X)) (code : list (sec a)) : Prop :=
  EVERY sec_ends_with_label code /\
  EVERY sec_labels_ok code /\
  ALL_DISTINCT (MAP Section_num code) /\
  EVERY (ALL_DISTINCT ∘ extract_labels ∘ Section_lines) code /\
  DISJOINT (domain labs) (set (MAP Section_num code)) /\
  restrict_nonzero (get_labels code) SUBSET (get_code_labels code UNION labs_domain labs) /\
  all_enc_ok_pre c code.

(** HOL [num_pcs]: recursion on the sections, then on the lines. *)
Fixpoint num_pcs (l : list (sec a)) : N :=
  match l with
  | [] => 0
  | Section_ k xs :: rest =>
      (fix go (xs : list (line a)) : N :=
         match xs with
         | [] => num_pcs rest
         | x :: xs => if is_Label x then go xs else 1 + go xs
         end) xs
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "num_pcs_def" *)
Theorem num_pcs_def : forall k x xs rest,
  num_pcs [] = 0 /\
  num_pcs (Section_ k [] :: rest) = num_pcs rest /\
  num_pcs (Section_ k (x :: xs) :: rest) =
    if is_Label x then num_pcs (Section_ k xs :: rest)
    else 1 + num_pcs (Section_ k xs :: rest).
Proof. intros; repeat split. Qed.

End GoodCode.

Import wordSem (buffer, position, buffer_buffer, space_left).

Section StateRel.
Context {a : N} {B C Ffi : Type}.
Implicit Types (mc_conf : machine_config a B C).

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "share_mem_domain_code_rel_def" *)
Definition share_mem_domain_code_rel mc_conf (p : word a) (code2 : list (sec a))
    (s1_shared_mem_domain : word a -> Prop) : Prop :=
  (forall pc op re a0 inst len i,
     asm_fetch_aux pc code2 = SOME (Asm (ShareMem op re a0) inst len) /\
     mmio_pcs_min_index mc_conf.(ffi_names) = SOME i ->
     exists index,
       i <= index /\
       find_index (p + n2w (pos_val pc 0 code2))%w mc_conf.(ffi_entry_pcs) 0 = SOME index /\
       (let '(name, nb) := get_memop_info op in
        EL index mc_conf.(ffi_names) = SharedMem name /\
        ALOOKUP mc_conf.(mmio_info) index =
          SOME (nb, (a0, (re, (p + n2w (pos_val pc 0 code2 + len))%w))))) /\
  (forall pc line,
     asm_fetch_aux pc code2 = SOME line /\
     (forall op re a0 inst len, line <> Asm (ShareMem op re a0) inst len) ->
     DISJOINT (set mc_conf.(ffi_entry_pcs))
       (fun x => exists a0, x = (p + n2w a0 + n2w (pos_val pc 0 code2))%w /\
                 a0 < LENGTH (line_bytes line))) /\
  (forall a0, byte_align a0 IN s1_shared_mem_domain -> a0 IN s1_shared_mem_domain) /\
  mc_conf.(shared_addresses) = s1_shared_mem_domain.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "share_mem_state_rel_def" *)
Definition share_mem_state_rel mc_conf (s1 : labSem.state a config Ffi) (t1 : asm_state a)
    (ms1 : B) : Prop :=
  (forall ms2 k index new_bytes (t1 : asm_state a) nb ad offs re pc' ad' st new_st i,
     mmio_pcs_min_index mc_conf.(ffi_names) = SOME i /\
     i <= index /\ index < LENGTH mc_conf.(ffi_names) /\
     RTC call_FFI_rel s1.(ffi) st /\
     ALOOKUP mc_conf.(mmio_info) index = SOME (nb, (Addr ad offs, (re, pc'))) /\
     mc_conf.(prog_addresses) = t1.(asmSem.mem_domain) /\
     ad' = (get_reg mc_conf.(target) ms2 ad + offs)%w /\
     target_state_rel mc_conf.(target)
       (asmSem.set_pc (EL index mc_conf.(ffi_entry_pcs)) t1) ms2 ->
     exists op, EL index mc_conf.(ffi_names) = SharedMem op /\
       match op with
       | MappedRead =>
           (if decide (nb = n2w 0)
            then w2n ad' MOD (dimindex a DIV 8) = 0 else True) /\
           ad' IN mc_conf.(shared_addresses) /\
           is_valid_mapped_read (get_pc mc_conf.(target) ms2) nb (Addr ad offs) re pc'
             mc_conf.(target) ms2 mc_conf.(prog_addresses) /\
           call_FFI st (SharedMem MappedRead) [nb] (word_to_bytes ad' false) =
             FFI_return new_st new_bytes ->
           target_state_rel mc_conf.(target)
             (asmSem.set_regs
                (fun n => if decide (n = re) then word_of_bytes false (n2w 0) new_bytes
                          else t1.(asmSem.regs) n)
                (asmSem.set_pc pc' t1))
             (mc_conf.(ffi_interfer) k (index, (new_bytes, ms2)))
       | MappedWrite =>
           (if decide (nb = n2w 0)
            then w2n ad' MOD (dimindex a DIV 8) = 0 else True) /\
           ad' IN mc_conf.(shared_addresses) /\
           is_valid_mapped_write (get_pc mc_conf.(target) ms2) nb (Addr ad offs) re pc'
             mc_conf.(target) ms2 mc_conf.(prog_addresses) /\
           call_FFI st (SharedMem MappedWrite) [nb]
             ((let w := get_reg mc_conf.(target) ms2 re in
               if decide (nb = n2w 0) then word_to_bytes w false
               else word_to_bytes_aux (w2n nb) w false)
              ++ word_to_bytes ad' false) =
             FFI_return new_st new_bytes ->
           target_state_rel mc_conf.(target)
             (asmSem.set_pc pc' t1)
             (mc_conf.(ffi_interfer) k (index, (new_bytes, ms2)))
       end) /\
  (forall index i,
     mmio_pcs_min_index mc_conf.(ffi_names) = SOME i /\
     index < LENGTH mc_conf.(ffi_names) /\ i <= index ->
     mc_conf.(halt_pc) <> EL index mc_conf.(ffi_entry_pcs) /\
     mc_conf.(ccache_pc) <> EL index mc_conf.(ffi_entry_pcs)).

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "no_install_or_no_share_mem_def" *)
Definition no_install_or_no_share_mem (code : list (sec a)) (ffi_names : list ffiname) : Prop :=
  (no_share_mem_inst code /\ EVERY (fun x => ⌜exists s, x = ExtCall s⌝) ffi_names) \/
  no_install code.

End StateRel.

(** ** [oracle_tie] *)

Section OracleTie.
Context {a : N} {B C Ffi : Type} {c : Type}.
Implicit Types (mc_conf : machine_config a B C).

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "oracle_tie_def" *)
Definition oracle_tie mc_conf (ms : B) (s1 : labSem.state a c Ffi) : Prop :=
  s1.(io_regs) = target_io_regs mc_conf s1.(ffi) ms /\
  s1.(io_fp_regs) = target_io_fp_regs mc_conf s1.(ffi) ms /\
  s1.(cc_regs) = target_cc_regs mc_conf s1.(ffi) ms /\
  s1.(cc_fp_regs) = target_cc_fp_regs mc_conf s1.(ffi) ms.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "oracle_tie_shift_interfer" *)
Theorem oracle_tie_shift_interfer : forall mc_conf ms1 s1 l ms2,
  oracle_tie mc_conf ms1 s1 /\
  (forall k, find_next_interference mc_conf s1.(ffi) (k + l) ms1 =
             find_next_interference (shift_interfer l mc_conf) s1.(ffi) k ms2) ->
  oracle_tie (shift_interfer l mc_conf) ms2 s1.
Proof.
  intros mc_conf ms1 s1 l ms2 [Ht H].
  pose proof (next_interference_shift _ _ _ _ _ _ _ H) as E.
  destruct (constructed_oracles_EQ _ _ _ _ _ _ (conj E (conj eq_refl (conj eq_refl eq_refl))))
    as (E1 & E2 & E3 & E4).
  destruct Ht as (H1 & H2 & H3 & H4). unfold oracle_tie.
  rewrite H1, H2, H3, H4, E1, E2, E3, E4. repeat split.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "oracle_tie_step" *)
Theorem oracle_tie_step : forall mc_conf ms1 s1 l ms2 s2,
  oracle_tie mc_conf ms1 s1 /\
  (forall k, find_next_interference mc_conf s1.(ffi) (k + l) ms1 =
             find_next_interference (shift_interfer l mc_conf) s1.(ffi) k ms2) /\
  s2.(io_regs) = s1.(io_regs) /\
  s2.(io_fp_regs) = s1.(io_fp_regs) /\
  s2.(cc_regs) = s1.(cc_regs) /\ s2.(cc_fp_regs) = s1.(cc_fp_regs) /\
  s2.(ffi) = s1.(ffi) ->
  oracle_tie (shift_interfer l mc_conf) ms2 s2.
Proof.
  intros mc_conf ms1 s1 l ms2 s2 (Ht & H & E1 & E2 & E3 & E4 & E5).
  pose proof (oracle_tie_shift_interfer mc_conf ms1 s1 l ms2 (conj Ht H)) as (H1 & H2 & H3 & H4).
  unfold oracle_tie. rewrite E1, E2, E3, E4, E5. auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "oracle_tie_ffi_step" *)
Theorem oracle_tie_ffi_step : forall mc_conf ms1 s1 index new_bytes ms_pre ms_post mc' ffi',
  oracle_tie mc_conf ms1 s1 /\
  next_interference mc_conf s1.(ffi) ms1 =
    SOME (FfiApp index new_bytes ms_pre ms_post, (mc', ffi')) ->
  (forall name r,
     s1.(io_regs) 0 name r =
       if MEM r mc_conf.(callee_saved_regs) ||
          negb (r <? reg_count (asmProps.config mc_conf.(target))) ||
          MEM r (avoid_regs (asmProps.config mc_conf.(target)))
       then NONE else SOME (get_reg mc_conf.(target) ms_post r)) /\
  (forall i, s1.(io_fp_regs) 0 i = get_fp_reg mc_conf.(target) ms_post i) /\
  target_io_regs mc' ffi' ms_post = shift_seq 1 s1.(io_regs) /\
  target_io_fp_regs mc' ffi' ms_post = shift_seq 1 s1.(io_fp_regs) /\
  target_cc_regs mc' ffi' ms_post = s1.(cc_regs) /\
  target_cc_fp_regs mc' ffi' ms_post = s1.(cc_fp_regs).
Proof.
  intros mc_conf ms1 s1 index new_bytes ms_pre ms_post mc' ffi' [(H1 & H2 & H3 & H4) H].
  pose proof (fun name r i k => constructed_oracles_ffi_step _ _ _ _ _ _ _ _ _ name r i k H) as S.
  rewrite H1, H2, H3, H4.
  repeat split.
  - intros name r. exact (proj1 (S name r 0 0)).
  - intros i. exact (proj1 (proj2 (S (ExtCall (strlit [])) 0 i 0))).
  - apply functional_extensionality; intros k; apply functional_extensionality; intros name;
      apply functional_extensionality; intros r.
    unfold shift_seq. rewrite N.add_1_r. symmetry.
    destruct (S name r 0 k) as (_ & _ & X & _). exact X.
  - apply functional_extensionality; intros k; apply functional_extensionality; intros i.
    unfold shift_seq. rewrite N.add_1_r. symmetry.
    destruct (S (ExtCall (strlit [])) 0 i k) as (_ & _ & _ & X & _). exact X.
  - apply functional_extensionality; intros k; apply functional_extensionality; intros r.
    symmetry. destruct (S (ExtCall (strlit [])) r 0 k) as (_ & _ & _ & _ & X & _). exact X.
  - apply functional_extensionality; intros k; apply functional_extensionality; intros i.
    symmetry. destruct (S (ExtCall (strlit [])) 0 i k) as (_ & _ & _ & _ & _ & X). exact X.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "oracle_tie_ccache_step" *)
Theorem oracle_tie_ccache_step : forall mc_conf ms1 s1 a1 a2 ms_pre ms_post mc' ffi',
  oracle_tie mc_conf ms1 s1 /\
  next_interference mc_conf s1.(ffi) ms1 =
    SOME (CcApp a1 a2 ms_pre ms_post, (mc', ffi')) ->
  (forall r,
     s1.(cc_regs) 0 r =
       if MEM r mc_conf.(callee_saved_regs) || bool_decide (r = mc_conf.(targetSem.ptr_reg)) ||
          negb (r <? reg_count (asmProps.config mc_conf.(target))) ||
          MEM r (avoid_regs (asmProps.config mc_conf.(target)))
       then NONE else SOME (get_reg mc_conf.(target) ms_post r)) /\
  (forall i, s1.(cc_fp_regs) 0 i = get_fp_reg mc_conf.(target) ms_post i) /\
  target_cc_regs mc' ffi' ms_post = shift_seq 1 s1.(cc_regs) /\
  target_cc_fp_regs mc' ffi' ms_post = shift_seq 1 s1.(cc_fp_regs) /\
  target_io_regs mc' ffi' ms_post = s1.(io_regs) /\
  target_io_fp_regs mc' ffi' ms_post = s1.(io_fp_regs).
Proof.
  intros mc_conf ms1 s1 a1 a2 ms_pre ms_post mc' ffi' [(H1 & H2 & H3 & H4) H].
  pose proof (fun r i k name => constructed_oracles_cc_step _ _ _ _ _ _ _ _ _ r i k name H) as S.
  rewrite H1, H2, H3, H4.
  repeat split.
  - intros r. exact (proj1 (S r 0 0 (ExtCall (strlit [])))).
  - intros i. exact (proj1 (proj2 (S 0 i 0 (ExtCall (strlit []))))).
  - apply functional_extensionality; intros k; apply functional_extensionality; intros r.
    unfold shift_seq. rewrite N.add_1_r. symmetry.
    destruct (S r 0 k (ExtCall (strlit []))) as (_ & _ & X & _). exact X.
  - apply functional_extensionality; intros k; apply functional_extensionality; intros i.
    unfold shift_seq. rewrite N.add_1_r. symmetry.
    destruct (S 0 i k (ExtCall (strlit []))) as (_ & _ & _ & X & _). exact X.
  - apply functional_extensionality; intros k; apply functional_extensionality; intros name;
      apply functional_extensionality; intros r. symmetry.
    destruct (S r 0 k name) as (_ & _ & _ & _ & X & _). exact X.
  - apply functional_extensionality; intros k; apply functional_extensionality; intros i.
    symmetry. destruct (S 0 i k (ExtCall (strlit []))) as (_ & _ & _ & _ & _ & X). exact X.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "oracle_tie_ffi_next" *)
Theorem oracle_tie_ffi_next : forall mc_conf ms1 s1 index new_bytes ms_pre ms_post mc' ffi' s2,
  oracle_tie mc_conf ms1 s1 /\
  next_interference mc_conf s1.(ffi) ms1 =
    SOME (FfiApp index new_bytes ms_pre ms_post, (mc', ffi')) /\
  s2.(io_regs) = shift_seq 1 s1.(io_regs) /\
  s2.(io_fp_regs) = shift_seq 1 s1.(io_fp_regs) /\
  s2.(cc_regs) = s1.(cc_regs) /\ s2.(cc_fp_regs) = s1.(cc_fp_regs) /\
  s2.(ffi) = ffi' ->
  oracle_tie mc' ms_post s2.
Proof.
  intros mc_conf ms1 s1 index new_bytes ms_pre ms_post mc' ffi' s2 (Ht & H & E1 & E2 & E3 & E4 & E5).
  destruct (oracle_tie_ffi_step mc_conf ms1 s1 index new_bytes ms_pre ms_post mc' ffi' (conj Ht H))
    as (_ & _ & F1 & F2 & F3 & F4).
  unfold oracle_tie. rewrite E1, E2, E3, E4, E5, F1, F2, F3, F4. auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "oracle_tie_ccache_next" *)
Theorem oracle_tie_ccache_next : forall mc_conf ms1 s1 a1 a2 ms_pre ms_post mc' ffi' s2,
  oracle_tie mc_conf ms1 s1 /\
  next_interference mc_conf s1.(ffi) ms1 =
    SOME (CcApp a1 a2 ms_pre ms_post, (mc', ffi')) /\
  s2.(cc_regs) = shift_seq 1 s1.(cc_regs) /\
  s2.(cc_fp_regs) = shift_seq 1 s1.(cc_fp_regs) /\
  s2.(io_regs) = s1.(io_regs) /\ s2.(io_fp_regs) = s1.(io_fp_regs) /\
  s2.(ffi) = ffi' ->
  oracle_tie mc' ms_post s2.
Proof.
  intros mc_conf ms1 s1 a1 a2 ms_pre ms_post mc' ffi' s2 (Ht & H & E1 & E2 & E3 & E4 & E5).
  destruct (oracle_tie_ccache_step mc_conf ms1 s1 a1 a2 ms_pre ms_post mc' ffi' (conj Ht H))
    as (_ & _ & F1 & F2 & F3 & F4).
  unfold oracle_tie. rewrite E1, E2, E3, E4, E5, F1, F2, F3, F4. auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "oracle_tie_ExtCall_residues" *)
Theorem oracle_tie_ExtCall_residues : forall mc_conf ms1 s1 ms2 l index name bytes bytes2 new_ffi
    new_bytes (t1 : asm_state a),
  oracle_tie mc_conf ms1 s1 /\
  (forall k, find_next_interference mc_conf s1.(ffi) (k + l) ms1 =
             find_next_interference
               (set_next_interfer (shift_seq l mc_conf.(next_interfer)) mc_conf)
               s1.(ffi) k ms2) /\
  get_pc mc_conf.(target) ms2 NOTIN mc_conf.(prog_addresses) DIFF set mc_conf.(ffi_entry_pcs) /\
  get_pc mc_conf.(target) ms2 <> mc_conf.(halt_pc) /\
  get_pc mc_conf.(target) ms2 <> mc_conf.(ccache_pc) /\
  find_index (get_pc mc_conf.(target) ms2) mc_conf.(ffi_entry_pcs) 0 = SOME index /\
  EL index mc_conf.(ffi_names) = ExtCall name /\
  ALOOKUP mc_conf.(mmio_info) index = NONE /\
  read_ffi_bytearrays mc_conf ms2 = (SOME bytes, SOME bytes2) /\
  call_FFI s1.(ffi) (ExtCall name) bytes bytes2 = FFI_return new_ffi new_bytes ->
  (fun a0 => get_reg_value (s1.(io_regs) 0 (ExtCall name) a0) (t1.(asmSem.regs) a0) I) =
    (fun a0 => if MEM a0 mc_conf.(callee_saved_regs) ||
                  negb (a0 <? reg_count (asmProps.config mc_conf.(target))) ||
                  MEM a0 (avoid_regs (asmProps.config mc_conf.(target)))
               then t1.(asmSem.regs) a0
               else get_reg mc_conf.(target)
                      (mc_conf.(ffi_interfer) 0 (index, (new_bytes, ms2))) a0) /\
  (fun n => s1.(io_fp_regs) 0 n) =
    (fun n => get_fp_reg mc_conf.(target)
                (mc_conf.(ffi_interfer) 0 (index, (new_bytes, ms2))) n).
Proof.
  intros mc_conf ms1 s1 ms2 l index name bytes bytes2 new_ffi new_bytes t1
    (Ht & Hf & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  pose proof (next_interference_shift _ _ _ _ _ _ _ Hf) as E.
  set (mc2 := set_next_interfer (shift_seq l mc_conf.(next_interfer)) mc_conf) in *.
  assert (Hn : next_interference mc2 s1.(ffi) ms2 =
    SOME (FfiApp index new_bytes ms2 (mc_conf.(ffi_interfer) 0 (index, (new_bytes, ms2))),
          (set_ffi_interfer (shift_seq 1 mc_conf.(ffi_interfer)) mc2, new_ffi))).
  { apply (next_interference_ExtCall mc2 ms2 index name bytes bytes2).
    repeat split; assumption. }
  rewrite <- E in Hn.
  destruct (oracle_tie_ffi_step _ _ _ _ _ _ _ _ _ (conj Ht Hn)) as (F1 & F2 & _).
  split; apply functional_extensionality; intros x.
  - rewrite F1. destruct (_ || _); reflexivity.
  - apply F2.
Qed.

End OracleTie.

Section StateRelDef.
Context {a : N} {B C Ffi : Type}.

(* The code buffer is set-up to immediately follow the current code:
   |---code---|---cb---| *)
(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "state_rel_def" *)
Definition state_rel (x : machine_config a B C * (list (sec a) * (spt (spt N) * word a)))
    (s1 : labSem.state a config Ffi) (t1 : asm_state a) (ms1 : B) : Prop :=
  let '(mc_conf, (code2, (labs, p))) := x in
  target_state_rel mc_conf.(target) t1 ms1 /\
  good_dimindex a /\
  mc_conf.(prog_addresses) = t1.(asmSem.mem_domain) /\
  mc_conf.(halt_pc) NOTIN mc_conf.(prog_addresses) /\
  mc_conf.(ccache_pc) NOTIN mc_conf.(prog_addresses) /\
  reg_ok s1.(ptr_reg) (asmProps.config mc_conf.(target)) /\
  mc_conf.(targetSem.ptr_reg) = s1.(ptr_reg) /\
  reg_ok s1.(len_reg) (asmProps.config mc_conf.(target)) /\
  mc_conf.(targetSem.len_reg) = s1.(len_reg) /\
  reg_ok s1.(ptr2_reg) (asmProps.config mc_conf.(target)) /\
  mc_conf.(targetSem.ptr2_reg) = s1.(ptr2_reg) /\
  reg_ok s1.(len2_reg) (asmProps.config mc_conf.(target)) /\
  mc_conf.(targetSem.len2_reg) = s1.(len2_reg) /\
  reg_ok s1.(link_reg) (asmProps.config mc_conf.(target)) /\
  (exists i, mmio_pcs_min_index mc_conf.(ffi_names) = SOME i /\
     (forall index, if decide (i <= index /\ index < LENGTH mc_conf.(ffi_names))
                    then exists info, ALOOKUP mc_conf.(mmio_info) index = SOME info
                    else ALOOKUP mc_conf.(mmio_info) index = NONE)) /\
  (forall ms2 k index new_bytes (t1 : asm_state a) bytes bytes2 st new_st i,
     mmio_pcs_min_index mc_conf.(ffi_names) = SOME i /\
     index < i /\
     read_ffi_bytearrays mc_conf ms2 = (SOME bytes, SOME bytes2) /\
     RTC call_FFI_rel s1.(ffi) st /\
     call_FFI st (EL index mc_conf.(ffi_names)) bytes bytes2 = FFI_return new_st new_bytes /\
     mc_conf.(prog_addresses) = t1.(asmSem.mem_domain) /\
     target_state_rel mc_conf.(target)
       (asmSem.set_pc (p - n2w ((3 + index) * ffi_offset))%w t1) ms2 /\
     aligned (code_alignment (asmProps.config mc_conf.(target))) (t1.(asmSem.regs) s1.(link_reg)) ->
     let ms' := mc_conf.(ffi_interfer) k (index, (new_bytes, ms2)) in
     target_state_rel mc_conf.(target)
       (asmSem.set_pc (t1.(asmSem.regs) s1.(link_reg))
       (asmSem.set_mem (asm_write_bytearray (t1.(asmSem.regs) s1.(ptr2_reg)) new_bytes t1.(asmSem.mem))
       (asmSem.set_fp_regs (fun n => get_fp_reg mc_conf.(target) ms' n)
       (asmSem.set_regs
          (fun a0 => if MEM a0 mc_conf.(callee_saved_regs) ||
                        negb (a0 <? reg_count (asmProps.config mc_conf.(target))) ||
                        MEM a0 (avoid_regs (asmProps.config mc_conf.(target)))
                     then t1.(asmSem.regs) a0
                     else get_reg mc_conf.(target) ms' a0) t1))))
       ms') /\
  (forall ms2 (t1 : asm_state a) k a1 a2,
     target_state_rel mc_conf.(target)
       (asmSem.set_pc (p - n2w (2 * ffi_offset))%w t1) ms2 /\
     aligned (code_alignment (asmProps.config mc_conf.(target))) (t1.(asmSem.regs) s1.(link_reg)) ->
     let ms' := mc_conf.(ccache_interfer) k (a1, (a2, ms2)) in
     target_state_rel mc_conf.(target)
       (asmSem.set_pc (t1.(asmSem.regs) s1.(link_reg))
       (asmSem.set_fp_regs (fun n => get_fp_reg mc_conf.(target) ms' n)
       (asmSem.set_regs
          (fun a0 => if MEM a0 mc_conf.(callee_saved_regs) ||
                        bool_decide (a0 = s1.(ptr_reg)) ||
                        negb (a0 <? reg_count (asmProps.config mc_conf.(target))) ||
                        MEM a0 (avoid_regs (asmProps.config mc_conf.(target)))
                     then t1.(asmSem.regs) a0
                     else get_reg mc_conf.(target) ms' a0) t1)))
       ms') /\
  s1.(compile) = compile_lab (asmProps.config mc_conf.(target)) /\
  (no_share_mem_inst code2 ->
     forall k, let '(cfg, code) := s1.(compile_oracle) k in
       good_code (asmProps.config mc_conf.(target)) cfg.(labels) code /\
       no_share_mem_inst code /\
       (k = 0 ->
        cfg.(labels) = labs /\
        cfg.(pos) = LENGTH (prog_to_bytes code2) /\
        cfg.(lab_to_target.ffi_names) = SOME mc_conf.(ffi_names))) /\
  (forall l1 l2 x, lab_lookup l1 l2 labs = SOME x -> EVEN x) /\
  (n2w 1 && p)%w = n2w 0 /\
  list_subset
       (FILTER (fun x => ⌜exists s, x = ExtCall s⌝) (find_ffi_names s1.(code)))
       mc_conf.(ffi_names) /\
  EVEN (LENGTH (prog_to_bytes code2)) /\
  (forall name i,
     MEM name mc_conf.(ffi_names) /\
     mmio_pcs_min_index mc_conf.(ffi_names) = SOME i /\
     get_ffi_index mc_conf.(ffi_names) name < i ->
     (exists s, name = ExtCall s) /\
     (p - n2w ((3 + get_ffi_index mc_conf.(ffi_names) name) * ffi_offset))%w
       NOTIN mc_conf.(prog_addresses) /\
     (p - n2w ((3 + get_ffi_index mc_conf.(ffi_names) name) * ffi_offset))%w <> mc_conf.(halt_pc) /\
     (p - n2w ((3 + get_ffi_index mc_conf.(ffi_names) name) * ffi_offset))%w <> mc_conf.(ccache_pc) /\
     find_index (p - n2w ((3 + get_ffi_index mc_conf.(ffi_names) name) * ffi_offset))%w
       mc_conf.(ffi_entry_pcs) 0 = SOME (get_ffi_index mc_conf.(ffi_names) name)) /\
  (p - n2w ffi_offset)%w = mc_conf.(halt_pc) /\
  (p - n2w (2 * ffi_offset))%w = mc_conf.(ccache_pc) /\
  interference_ok mc_conf.(next_interfer) (proj mc_conf.(target) t1.(asmSem.mem_domain)) /\
  (forall l1 l2 x2,
     loc_to_pc l1 l2 s1.(code) = SOME x2 ->
     lab_lookup l1 l2 labs = SOME (pos_val x2 0 code2)) /\
  (forall r, s1.(fp_regs) r = t1.(asmSem.fp_regs) r) /\
  (forall r, word_loc_val p labs (s1.(regs) r) = SOME (t1.(asmSem.regs) r)) /\
  (forall a0, byte_align a0 IN s1.(mem_domain) ->
     a0 IN t1.(asmSem.mem_domain) /\ a0 IN s1.(mem_domain) /\
     word_loc_val_byte p labs s1.(mem) a0 s1.(be) = SOME (t1.(asmSem.mem) a0)) /\
  (forall n,
     n < s1.(code_buffer).(space_left) ->
     let addr := (s1.(code_buffer).(position) +
                  n2w (LENGTH s1.(code_buffer).(buffer_buffer) + n))%w in
     addr IN t1.(asmSem.mem_domain) /\ addr NOTIN s1.(mem_domain)) /\
  bytes_in_mem p (prog_to_bytes code2) t1.(asmSem.mem) t1.(asmSem.mem_domain) s1.(mem_domain) /\
  s1.(code_buffer).(position) = (p + n2w (LENGTH (prog_to_bytes code2)))%w /\
  bytes_in_mem s1.(code_buffer).(position) s1.(code_buffer).(buffer_buffer)
     t1.(asmSem.mem) t1.(asmSem.mem_domain) s1.(mem_domain) /\
  LENGTH (prog_to_bytes code2) + LENGTH s1.(code_buffer).(buffer_buffer) +
     s1.(code_buffer).(space_left) < dimword a /\
  (forall bn,
     bn < LENGTH s1.(code_buffer).(buffer_buffer) + s1.(code_buffer).(space_left) ->
     ~ MEM (s1.(code_buffer).(position) + n2w bn)%w mc_conf.(ffi_entry_pcs)) /\
  ~ s1.(failed) /\
  ~ t1.(asmSem.failed) /\
  s1.(be) = t1.(asmSem.be) /\
  t1.(asmSem.pc) = (p + n2w (pos_val s1.(pc) 0 code2))%w /\
  (p && n2w (2 ** t1.(asmSem.align) - 1))%w = n2w 0 /\
  (match asm.link_reg (asmProps.config mc_conf.(target)) with NONE => True | SOME r => t1.(asmSem.lr) = r end) /\
  t1.(asmSem.be) = big_endian (asmProps.config mc_conf.(target)) /\
  t1.(asmSem.align) = code_alignment (asmProps.config mc_conf.(target)) /\
  enc_ok (asmProps.config mc_conf.(target)) /\
  all_enc_ok (asmProps.config mc_conf.(target)) labs
     (TAKE (THE (mmio_pcs_min_index mc_conf.(ffi_names))) mc_conf.(ffi_names)) 0 code2 /\
  EVERY sec_labels_ok code2 /\
  code_similar s1.(code) code2 /\
  share_mem_state_rel mc_conf s1 t1 ms1 /\
  share_mem_domain_code_rel mc_conf p code2 s1.(shared_mem_domain) /\
  LENGTH mc_conf.(ffi_names) = LENGTH mc_conf.(ffi_entry_pcs) /\
  no_install_or_no_share_mem code2 mc_conf.(ffi_names).

(** The conjuncts of [state_rel], named (Galette helper). *)
Record state_rel_r (mc_conf : machine_config a B C) (code2 : list (sec a))
    (labs : spt (spt N)) (p : word a)
    (s1 : labSem.state a config Ffi) (t1 : asm_state a) (ms1 : B) : Prop := {
  sr_tsr : target_state_rel mc_conf.(target) t1 ms1;
  sr_good_dimindex : good_dimindex a;
  sr_prog_addresses : mc_conf.(prog_addresses) = t1.(asmSem.mem_domain);
  sr_halt_pc : mc_conf.(halt_pc) NOTIN mc_conf.(prog_addresses);
  sr_ccache_pc : mc_conf.(ccache_pc) NOTIN mc_conf.(prog_addresses);
  sr_ptr_reg_ok : reg_ok s1.(ptr_reg) (asmProps.config mc_conf.(target));
  sr_ptr_reg : mc_conf.(targetSem.ptr_reg) = s1.(ptr_reg);
  sr_len_reg_ok : reg_ok s1.(len_reg) (asmProps.config mc_conf.(target));
  sr_len_reg : mc_conf.(targetSem.len_reg) = s1.(len_reg);
  sr_ptr2_reg_ok : reg_ok s1.(ptr2_reg) (asmProps.config mc_conf.(target));
  sr_ptr2_reg : mc_conf.(targetSem.ptr2_reg) = s1.(ptr2_reg);
  sr_len2_reg_ok : reg_ok s1.(len2_reg) (asmProps.config mc_conf.(target));
  sr_len2_reg : mc_conf.(targetSem.len2_reg) = s1.(len2_reg);
  sr_link_reg_ok : reg_ok s1.(link_reg) (asmProps.config mc_conf.(target));
  sr_mmio : (exists i, mmio_pcs_min_index mc_conf.(ffi_names) = SOME i /\
     (forall index, if decide (i <= index /\ index < LENGTH mc_conf.(ffi_names))
                    then exists info, ALOOKUP mc_conf.(mmio_info) index = SOME info
                    else ALOOKUP mc_conf.(mmio_info) index = NONE));
  sr_ffi : (forall ms2 k index new_bytes (t1 : asm_state a) bytes bytes2 st new_st i,
     mmio_pcs_min_index mc_conf.(ffi_names) = SOME i /\
     index < i /\
     read_ffi_bytearrays mc_conf ms2 = (SOME bytes, SOME bytes2) /\
     RTC call_FFI_rel s1.(ffi) st /\
     call_FFI st (EL index mc_conf.(ffi_names)) bytes bytes2 = FFI_return new_st new_bytes /\
     mc_conf.(prog_addresses) = t1.(asmSem.mem_domain) /\
     target_state_rel mc_conf.(target)
       (asmSem.set_pc (p - n2w ((3 + index) * ffi_offset))%w t1) ms2 /\
     aligned (code_alignment (asmProps.config mc_conf.(target))) (t1.(asmSem.regs) s1.(link_reg)) ->
     let ms' := mc_conf.(ffi_interfer) k (index, (new_bytes, ms2)) in
     target_state_rel mc_conf.(target)
       (asmSem.set_pc (t1.(asmSem.regs) s1.(link_reg))
       (asmSem.set_mem (asm_write_bytearray (t1.(asmSem.regs) s1.(ptr2_reg)) new_bytes t1.(asmSem.mem))
       (asmSem.set_fp_regs (fun n => get_fp_reg mc_conf.(target) ms' n)
       (asmSem.set_regs
          (fun a0 => if MEM a0 mc_conf.(callee_saved_regs) ||
                        negb (a0 <? reg_count (asmProps.config mc_conf.(target))) ||
                        MEM a0 (avoid_regs (asmProps.config mc_conf.(target)))
                     then t1.(asmSem.regs) a0
                     else get_reg mc_conf.(target) ms' a0) t1))))
       ms');
  sr_ccache : (forall ms2 (t1 : asm_state a) k a1 a2,
     target_state_rel mc_conf.(target)
       (asmSem.set_pc (p - n2w (2 * ffi_offset))%w t1) ms2 /\
     aligned (code_alignment (asmProps.config mc_conf.(target))) (t1.(asmSem.regs) s1.(link_reg)) ->
     let ms' := mc_conf.(ccache_interfer) k (a1, (a2, ms2)) in
     target_state_rel mc_conf.(target)
       (asmSem.set_pc (t1.(asmSem.regs) s1.(link_reg))
       (asmSem.set_fp_regs (fun n => get_fp_reg mc_conf.(target) ms' n)
       (asmSem.set_regs
          (fun a0 => if MEM a0 mc_conf.(callee_saved_regs) ||
                        bool_decide (a0 = s1.(ptr_reg)) ||
                        negb (a0 <? reg_count (asmProps.config mc_conf.(target))) ||
                        MEM a0 (avoid_regs (asmProps.config mc_conf.(target)))
                     then t1.(asmSem.regs) a0
                     else get_reg mc_conf.(target) ms' a0) t1)))
       ms');
  sr_compile : s1.(compile) = compile_lab (asmProps.config mc_conf.(target));
  sr_oracle : (no_share_mem_inst code2 ->
     forall k, let '(cfg, code) := s1.(compile_oracle) k in
       good_code (asmProps.config mc_conf.(target)) cfg.(labels) code /\
       no_share_mem_inst code /\
       (k = 0 ->
        cfg.(labels) = labs /\
        cfg.(pos) = LENGTH (prog_to_bytes code2) /\
        cfg.(lab_to_target.ffi_names) = SOME mc_conf.(ffi_names)));
  sr_labs_even : (forall l1 l2 x, lab_lookup l1 l2 labs = SOME x -> EVEN x);
  sr_p_odd : (n2w 1 && p)%w = n2w 0;
  sr_ffi_names_subset : list_subset
       (FILTER (fun x => ⌜exists s, x = ExtCall s⌝) (find_ffi_names s1.(code)))
       mc_conf.(ffi_names);
  sr_code_even : EVEN (LENGTH (prog_to_bytes code2));
  sr_ffi_pos : (forall name i,
     MEM name mc_conf.(ffi_names) /\
     mmio_pcs_min_index mc_conf.(ffi_names) = SOME i /\
     get_ffi_index mc_conf.(ffi_names) name < i ->
     (exists s, name = ExtCall s) /\
     (p - n2w ((3 + get_ffi_index mc_conf.(ffi_names) name) * ffi_offset))%w
       NOTIN mc_conf.(prog_addresses) /\
     (p - n2w ((3 + get_ffi_index mc_conf.(ffi_names) name) * ffi_offset))%w <> mc_conf.(halt_pc) /\
     (p - n2w ((3 + get_ffi_index mc_conf.(ffi_names) name) * ffi_offset))%w <> mc_conf.(ccache_pc) /\
     find_index (p - n2w ((3 + get_ffi_index mc_conf.(ffi_names) name) * ffi_offset))%w
       mc_conf.(ffi_entry_pcs) 0 = SOME (get_ffi_index mc_conf.(ffi_names) name));
  sr_halt_pos : (p - n2w ffi_offset)%w = mc_conf.(halt_pc);
  sr_ccache_pos : (p - n2w (2 * ffi_offset))%w = mc_conf.(ccache_pc);
  sr_interference_ok : interference_ok mc_conf.(next_interfer) (proj mc_conf.(target) t1.(asmSem.mem_domain));
  sr_loc_to_pc : (forall l1 l2 x2,
     loc_to_pc l1 l2 s1.(code) = SOME x2 ->
     lab_lookup l1 l2 labs = SOME (pos_val x2 0 code2));
  sr_fp_regs : (forall r, s1.(fp_regs) r = t1.(asmSem.fp_regs) r);
  sr_regs : (forall r, word_loc_val p labs (s1.(regs) r) = SOME (t1.(asmSem.regs) r));
  sr_mem : (forall a0, byte_align a0 IN s1.(mem_domain) ->
     a0 IN t1.(asmSem.mem_domain) /\ a0 IN s1.(mem_domain) /\
     word_loc_val_byte p labs s1.(mem) a0 s1.(be) = SOME (t1.(asmSem.mem) a0));
  sr_cb_space : (forall n,
     n < s1.(code_buffer).(space_left) ->
     let addr := (s1.(code_buffer).(position) +
                  n2w (LENGTH s1.(code_buffer).(buffer_buffer) + n))%w in
     addr IN t1.(asmSem.mem_domain) /\ addr NOTIN s1.(mem_domain));
  sr_code_bytes : bytes_in_mem p (prog_to_bytes code2) t1.(asmSem.mem) t1.(asmSem.mem_domain) s1.(mem_domain);
  sr_cb_position : s1.(code_buffer).(position) = (p + n2w (LENGTH (prog_to_bytes code2)))%w;
  sr_cb_bytes : bytes_in_mem s1.(code_buffer).(position) s1.(code_buffer).(buffer_buffer)
     t1.(asmSem.mem) t1.(asmSem.mem_domain) s1.(mem_domain);
  sr_cb_bound : LENGTH (prog_to_bytes code2) + LENGTH s1.(code_buffer).(buffer_buffer) +
     s1.(code_buffer).(space_left) < dimword a;
  sr_cb_ffi_entry : (forall bn,
     bn < LENGTH s1.(code_buffer).(buffer_buffer) + s1.(code_buffer).(space_left) ->
     ~ MEM (s1.(code_buffer).(position) + n2w bn)%w mc_conf.(ffi_entry_pcs));
  sr_s1_failed : ~ s1.(failed);
  sr_t1_failed : ~ t1.(asmSem.failed);
  sr_be : s1.(be) = t1.(asmSem.be);
  sr_pc : t1.(asmSem.pc) = (p + n2w (pos_val s1.(pc) 0 code2))%w;
  sr_p_align : (p && n2w (2 ** t1.(asmSem.align) - 1))%w = n2w 0;
  sr_lr : (match asm.link_reg (asmProps.config mc_conf.(target)) with NONE => True | SOME r => t1.(asmSem.lr) = r end);
  sr_t1_be : t1.(asmSem.be) = big_endian (asmProps.config mc_conf.(target));
  sr_t1_align : t1.(asmSem.align) = code_alignment (asmProps.config mc_conf.(target));
  sr_enc_ok : enc_ok (asmProps.config mc_conf.(target));
  sr_all_enc_ok : all_enc_ok (asmProps.config mc_conf.(target)) labs
     (TAKE (THE (mmio_pcs_min_index mc_conf.(ffi_names))) mc_conf.(ffi_names)) 0 code2;
  sr_sec_labels_ok : EVERY sec_labels_ok code2;
  sr_code_similar : code_similar s1.(code) code2;
  sr_share_mem_state_rel : share_mem_state_rel mc_conf s1 t1 ms1;
  sr_share_mem_domain_code_rel : share_mem_domain_code_rel mc_conf p code2 s1.(shared_mem_domain);
  sr_ffi_length : LENGTH mc_conf.(ffi_names) = LENGTH mc_conf.(ffi_entry_pcs);
  sr_no_install_or_no_share_mem : no_install_or_no_share_mem code2 mc_conf.(ffi_names)
}.

Lemma state_rel_iff mc_conf code2 labs p s1 t1 ms1 :
  state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 <-> state_rel_r mc_conf code2 labs p s1 t1 ms1.
Proof.
  split.
  - intros (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & H35 & H36 & H37 & H38 & H39 & H40 & H41 & H42 & H43 & H44 & H45 & H46 & H47 & H48 & H49 & H50 & H51 & H52).
    exact {| sr_tsr := H0; sr_good_dimindex := H1; sr_prog_addresses := H2; sr_halt_pc := H3; sr_ccache_pc := H4; sr_ptr_reg_ok := H5; sr_ptr_reg := H6; sr_len_reg_ok := H7; sr_len_reg := H8; sr_ptr2_reg_ok := H9; sr_ptr2_reg := H10; sr_len2_reg_ok := H11; sr_len2_reg := H12; sr_link_reg_ok := H13; sr_mmio := H14; sr_ffi := H15; sr_ccache := H16; sr_compile := H17; sr_oracle := H18; sr_labs_even := H19; sr_p_odd := H20; sr_ffi_names_subset := H21; sr_code_even := H22; sr_ffi_pos := H23; sr_halt_pos := H24; sr_ccache_pos := H25; sr_interference_ok := H26; sr_loc_to_pc := H27; sr_fp_regs := H28; sr_regs := H29; sr_mem := H30; sr_cb_space := H31; sr_code_bytes := H32; sr_cb_position := H33; sr_cb_bytes := H34; sr_cb_bound := H35; sr_cb_ffi_entry := H36; sr_s1_failed := H37; sr_t1_failed := H38; sr_be := H39; sr_pc := H40; sr_p_align := H41; sr_lr := H42; sr_t1_be := H43; sr_t1_align := H44; sr_enc_ok := H45; sr_all_enc_ok := H46; sr_sec_labels_ok := H47; sr_code_similar := H48; sr_share_mem_state_rel := H49; sr_share_mem_domain_code_rel := H50; sr_ffi_length := H51; sr_no_install_or_no_share_mem := H52 |}.
  - intros [H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49 H50 H51 H52].
    cbv beta iota zeta.
    repeat (split; [eassumption|]); eassumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "oracle_tie_clock" *)
Theorem oracle_tie_clock : forall {c} (mc_conf : machine_config a B C) ms (s1 : labSem.state a c Ffi) k,
  oracle_tie mc_conf ms s1 -> oracle_tie mc_conf ms (set_clock k s1).
Proof. intros c mc_conf ms s1 k H. exact H. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "state_rel_clock" *)
Theorem state_rel_clock : forall x s1 (t1 : asm_state a) (ms : B) k,
  state_rel x s1 t1 ms -> state_rel x (set_clock k s1) t1 ms.
Proof.
  intros [mc_conf [code2 [labs p]]] s1 t1 ms k H.
  apply state_rel_iff in H. apply state_rel_iff. destruct H. constructor; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "share_mem_state_rel_shift_interfer" *)
Theorem share_mem_state_rel_shift_interfer : forall (mc_conf : machine_config a B C)
    (s1 : labSem.state a config Ffi) (t1 : asm_state a) (x : B) l,
  share_mem_state_rel mc_conf s1 t1 x ->
  share_mem_state_rel
    (set_next_interfer (fun i => mc_conf.(next_interfer) (i + l)) mc_conf) s1 t1 x.
Proof. intros mc_conf s1 t1 x l H. exact H. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "share_mem_domain_code_rel_shift_interfer" *)
Theorem share_mem_domain_code_rel_shift_interfer : forall (mc_conf : machine_config a B C) p code2
    (s1 : labSem.state a config Ffi) l,
  share_mem_domain_code_rel mc_conf p code2 s1.(shared_mem_domain) ->
  share_mem_domain_code_rel
    (set_next_interfer (fun i => mc_conf.(next_interfer) (i + l)) mc_conf)
    p code2 s1.(shared_mem_domain).
Proof. intros mc_conf p code2 s1 l H. exact H. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "state_rel_shift_interfer" *)
Theorem state_rel_shift_interfer : forall (mc_conf : machine_config a B C) code2 labs p s1 t1 (x : B) l,
  state_rel (mc_conf, (code2, (labs, p))) s1 t1 x ->
  state_rel (shift_interfer l mc_conf, (code2, (labs, p))) s1 t1 x.
Proof.
  intros mc_conf code2 labs p s1 t1 x l H.
  apply state_rel_iff in H. apply state_rel_iff. destruct H.
  constructor; try assumption.
  intros i ms. apply sr_interference_ok0.
Qed.

End StateRelDef.

Arguments sr_tsr {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_good_dimindex {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_prog_addresses {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_halt_pc {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_ccache_pc {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_ptr_reg_ok {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_ptr_reg {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_len_reg_ok {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_len_reg {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_ptr2_reg_ok {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_ptr2_reg {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_len2_reg_ok {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_len2_reg {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_link_reg_ok {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_mmio {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_ffi {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_ccache {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_compile {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_oracle {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_labs_even {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_p_odd {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_ffi_names_subset {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_code_even {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_ffi_pos {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_halt_pos {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_ccache_pos {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_interference_ok {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_loc_to_pc {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_fp_regs {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_regs {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_mem {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_cb_space {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_code_bytes {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_cb_position {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_cb_bytes {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_cb_bound {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_cb_ffi_entry {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_s1_failed {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_t1_failed {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_be {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_pc {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_p_align {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_lr {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_t1_be {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_t1_align {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_enc_ok {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_all_enc_ok {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_sec_labels_ok {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_code_similar {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_share_mem_state_rel {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_share_mem_domain_code_rel {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_ffi_length {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.
Arguments sr_no_install_or_no_share_mem {a B C Ffi mc_conf code2 labs p s1 t1 ms1} _.

(** Induction over programs, section by section and line by line (the
    shape of HOL's [asm_code_length_ind], [pos_val_ind]; Galette helper). *)
Lemma code_ind {a : N} (P : list (sec a) -> Prop) :
  P [] ->
  (forall k xs, P xs -> P (Section_ k [] :: xs)) ->
  (forall k y ys xs, P (Section_ k ys :: xs) -> P (Section_ k (y :: ys) :: xs)) ->
  forall l, P l.
Proof.
  intros H0 H1 H2 l. induction l as [|[k ys] xs IH]; [exact H0|].
  induction ys as [|y ys IHy]; [apply H1, IH|apply H2, IHy].
Qed.
