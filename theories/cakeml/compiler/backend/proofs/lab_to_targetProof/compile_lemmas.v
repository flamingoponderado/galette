(** * CakeML [lab_to_targetProof]: lemmas for [compile_correct]

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml] (HOL
    lines 2932-3122): alignment of [pos_val], comparisons through
    [state_rel], [list_add_if_fresh], [find_index] and [has_io_name].

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v].
    - HOL's ML value [pos_val_MOD_0] (a [Q.prove] that is not stored) is
      the untagged Galette lemma of the same name, stated as HOL's ML code
      specialises it ([pos = 0]).  The ML values [IMP_IMP2] and the second
      [list_add_if_fresh_simp] (an instance) are not ported.
    - [find_ffi_names_ind] is replaced by induction on the program
      ([code_ind]). *)

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
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import basic bytes inst.
Import wordLang (word_loc, Word, Loc).
Import ByteBits.
Open Scope N_scope.

Section PosVal.
Context {a : N} {B C : Type}.

Lemma LENGTH_enc_nops (c : asm_config a) (i : asm.asm a) n :
  enc_ok c ->
  LENGTH (encode c i ++ FLAT (REPLICATE n (encode c (Inst asm.Skip)))) mod 2 ** code_alignment c = 0.
Proof.
  intros (H1 & H2 & _). rewrite LENGTH_app, LENGTH_FLAT_REPLICATE.
  destruct (H2 i) as [Hi _]. rewrite <- H1.
  pose proof (N.pow_nonzero 2 (code_alignment c) ltac:(discriminate)) as Hnz.
  rewrite N.Div0.add_mod, Hi, N.add_0_l, N.Div0.mod_mod, N.Div0.mod_mul. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_length_MOD_0" *)
Theorem line_length_MOD_0 : forall (mc_conf : machine_config a B C) labs ffi_names p h,
  encoder_correct mc_conf.(target) /\
  (~ EVEN p -> code_alignment (asmProps.config mc_conf.(target)) = 0) /\
  line_ok (asmProps.config mc_conf.(target)) labs ffi_names p h ->
  line_length h mod 2 ** code_alignment (asmProps.config mc_conf.(target)) = 0.
Proof.
  intros mc_conf labs ffi_names p h (Henc & _ & Hok).
  assert (Hc : enc_ok (asmProps.config mc_conf.(target))) by exact (proj1 (proj1 Henc)).
  destruct h as [l1 l2 l3|b bytes l|x w bytes l]; cbn [line_ok line_length] in *.
  - destruct Hok as [_ ->]. reflexivity.
  - destruct Hok as (He & _ & _). apply enc_with_nop_thm in He as [nn ->].
    apply LENGTH_enc_nops, Hc.
  - destruct x as [[l1 l2]|cmp r ri [l1 l2]|v|r [l1 l2]|s| |]; cbn [get_label] in Hok;
      try contradiction;
      try (destruct (lab_lookup l1 l2 labs); [|contradiction]);
      destruct Hok as (He & _ & _); apply enc_with_nop_thm in He as [nn ->];
      apply LENGTH_enc_nops, Hc.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pos_val_MOD_0_lemma" *)
Theorem pos_val_MOD_0_lemma : forall (mc_conf : machine_config a B C),
  0 mod 2 ** code_alignment (asmProps.config mc_conf.(target)) = 0.
Proof. intros. apply N.Div0.mod_0_l. Qed.

Lemma pos_val_MOD_0_gen (mc_conf : machine_config a B C) labs ffi_names : forall x pos code2,
  encoder_correct mc_conf.(target) /\
  (has_odd_inst code2 -> code_alignment (asmProps.config mc_conf.(target)) = 0) /\
  (~ EVEN pos -> code_alignment (asmProps.config mc_conf.(target)) = 0) /\
  pos mod 2 ** code_alignment (asmProps.config mc_conf.(target)) = 0 /\
  all_enc_ok (asmProps.config mc_conf.(target)) labs ffi_names pos code2 ->
  pos_val x pos code2 mod 2 ** code_alignment (asmProps.config mc_conf.(target)) = 0.
Proof.
  set (k := code_alignment (asmProps.config mc_conf.(target))).
  intros x pos code2. revert x pos.
  induction code2 as [|kk xs IH|kk y ys xs IH] using code_ind;
    intros x pos (Henc & Hodd & Hev & Hm & Hok).
  - exact Hm.
  - destruct Hok as [He Hok]. apply IH. exact (conj Henc (conj Hodd (conj Hev (conj Hm Hok)))).
  - destruct Hok as [Hy Hok].
    rewrite (proj2 (proj2 (pos_val_def x pos kk xs y ys))).
    assert (Hy0 : line_length y mod 2 ** k = 0)
      by (apply (line_length_MOD_0 mc_conf labs ffi_names pos y); auto).
    assert (Hpk : 0 < 2 ** k) by (apply N.neq_0_lt_0, N.pow_nonzero; discriminate).
    assert (Hm' : (pos + line_length y) mod 2 ** k = 0).
    { rewrite N.Div0.add_mod, Hm, Hy0. reflexivity. }
    assert (Hodd' : has_odd_inst (Section_ kk ys :: xs) -> k = 0).
    { intros Ho. apply Hodd. change (negb (EVEN (line_length y)) ||
        has_odd_inst (Section_ kk ys :: xs) = true). rewrite Ho, Bool.orb_true_r. reflexivity. }
    assert (Hev' : ~ EVEN (pos + line_length y) -> k = 0).
    { intros He. destruct (EVEN pos) eqn:Ep; [|apply Hev; congruence].
      destruct (EVEN (line_length y)) eqn:El.
      - exfalso. apply He. rewrite N.even_add, Ep, El. reflexivity.
      - apply Hodd. change (negb (EVEN (line_length y)) ||
          has_odd_inst (Section_ kk ys :: xs) = true). rewrite El. reflexivity. }
    destruct (is_Label y); [apply IH; exact (conj Henc (conj Hodd' (conj Hev' (conj Hm' Hok))))|].
    destruct (N.eqb_spec x 0); [exact Hm|apply IH; exact (conj Henc (conj Hodd' (conj Hev' (conj Hm' Hok))))].
Qed.

(** HOL's ML value [pos_val_MOD_0] (Galette helper, untagged). *)
Lemma pos_val_MOD_0 (mc_conf : machine_config a B C) labs ffi_names : forall x code2,
  encoder_correct mc_conf.(target) /\
  (has_odd_inst code2 -> code_alignment (asmProps.config mc_conf.(target)) = 0) /\
  all_enc_ok (asmProps.config mc_conf.(target)) labs ffi_names 0 code2 ->
  pos_val x 0 code2 mod 2 ** code_alignment (asmProps.config mc_conf.(target)) = 0.
Proof.
  intros x code2 (H1 & H2 & H3). apply (pos_val_MOD_0_gen mc_conf labs ffi_names).
  refine (conj H1 (conj H2 (conj _ (conj (pos_val_MOD_0_lemma mc_conf) H3)))).
  intros H; exfalso; apply H; reflexivity.
Qed.

End PosVal.

Section Cmp.
Context {a : N} {B C Ffi : Type}.

Lemma and1_eq0 (w : word a) : (n2w 1 && w)%w = n2w 0 <-> N.testbit (w2n w) 0 = false.
Proof.
  pose proof (DIMINDEX_GT_0 a) as Hd.
  split.
  - intros H. apply (f_equal (fun v => N.testbit (w2n v) 0)) in H.
    rewrite testbit_and, !testbit_n2w in H.
    replace (0 <? dimindex a) with true in H by (symmetry; apply N.ltb_lt; lia).
    cbn in H. exact H.
  - intros H. apply word_testbit_eq. intros i Hi. rewrite testbit_and, !testbit_n2w.
    destruct (N.eqb_spec i 0) as [->|Hi0].
    + rewrite H, Bool.andb_false_r. cbn. rewrite Bool.andb_false_r. reflexivity.
    + replace (N.testbit 1 i) with false.
      * rewrite N.bits_0, !Bool.andb_false_r. reflexivity.
      * symmetry. destruct i as [|pi]; [contradiction|]. reflexivity.
Qed.

Lemma testbit0_add (p : word a) x :
  N.testbit (w2n (p + n2w x)%w) 0 = xorb (N.testbit (w2n p) 0) (N.testbit x 0).
Proof.
  pose proof (DIMINDEX_GT_0 a) as Hd.
  unfold word_add. rewrite w2n_n2w, w2n_n2w. unfold dimword.
  rewrite N.mod_pow2_bits_low by lia. rewrite !N.bit0_odd, N.odd_add.
  rewrite <- !N.bit0_odd. rewrite N.mod_pow2_bits_low by lia. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "EVEN_add_AND" *)
Theorem EVEN_add_AND : forall (p : word a) x,
  (n2w 1 && p)%w = n2w 0 /\ EVEN x -> (n2w 1 && (p + n2w x))%w = n2w 0.
Proof.
  intros p x [Hp Hx]. apply and1_eq0 in Hp. apply and1_eq0.
  rewrite testbit0_add, Hp, N.bit0_odd. rewrite <- N.negb_even, Hx. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "word_cmp_lemma" *)
Theorem word_cmp_lemma : forall (mc_conf : machine_config a B C) code2 labs p
    (s1 : labSem.state a config Ffi) (t1 : asm_state a) (ms1 : B) cmp rr ri x,
  state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 /\
  wordSem.word_cmp cmp (regs s1 rr) (labSem.reg_imm ri s1) = SOME x ->
  x = word_cmp cmp (asmSem.read_reg rr t1) (asmSem.reg_imm ri t1).
Proof.
  intros mc_conf code2 labs p s1 t1 ms1 cmp rr ri x [H Hc].
  apply state_rel_iff in H.
  destruct ri as [n|w]; cbn [labSem.reg_imm asmSem.reg_imm] in Hc |- *; unfold asmSem.read_reg.
  - destruct (regs s1 rr) as [w1|k1 k2] eqn:E1; destruct (regs s1 n) as [w2|m1 m2] eqn:E2;
      try (destruct cmp; discriminate).
    + rewrite (regs_rel_word _ _ _ _ _ _ (sr_regs H) E1),
              (regs_rel_word _ _ _ _ _ _ (sr_regs H) E2).
      destruct cmp; cbn in Hc |- *; injection Hc as <-; reflexivity.
    + rewrite (regs_rel_word _ _ _ _ _ _ (sr_regs H) E2).
      pose proof (sr_regs H rr) as Hr. rewrite E1 in Hr. cbn [word_loc_val] in Hr.
      destruct (lab_lookup k1 k2 labs) as [q|] eqn:El; [|discriminate]. injection Hr as Hr.
      pose proof (sr_labs_even H k1 k2 q El) as Hq.
      destruct cmp; cbn in Hc; try discriminate;
        (destruct (N.eqb_spec k2 0); [|discriminate]);
        (destruct (bool_decide (w2 = n2w 1)) eqn:Ew; [|discriminate]);
        apply bool_decide_spec in Ew; subst w2; injection Hc as <-; cbn [word_cmp];
        rewrite <- Hr, WORD_AND_COMM, (EVEN_add_AND p q (conj (sr_p_odd H) Hq));
        rewrite (proj2 (bool_decide_spec _) eq_refl); reflexivity.
  - destruct (regs s1 rr) as [w1|k1 k2] eqn:E1.
    + rewrite (regs_rel_word _ _ _ _ _ _ (sr_regs H) E1).
      destruct cmp; cbn in Hc |- *; injection Hc as <-; reflexivity.
    + pose proof (sr_regs H rr) as Hr. rewrite E1 in Hr. cbn [word_loc_val] in Hr.
      destruct (lab_lookup k1 k2 labs) as [q|] eqn:El; [|discriminate]. injection Hr as Hr.
      pose proof (sr_labs_even H k1 k2 q El) as Hq.
      destruct cmp; cbn in Hc; try discriminate;
        (destruct (N.eqb_spec k2 0); [|discriminate]);
        (destruct (bool_decide (w = n2w 1)) eqn:Ew; [|discriminate]);
        apply bool_decide_spec in Ew; subst w; injection Hc as <-; cbn [word_cmp];
        rewrite <- Hr, WORD_AND_COMM, (EVEN_add_AND p q (conj (sr_p_odd H) Hq));
        rewrite (proj2 (bool_decide_spec _) eq_refl); reflexivity.
Qed.

End Cmp.

Section FfiNames.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "list_add_if_fresh_simp" 3027 *)
Theorem list_add_if_fresh_simp : forall {A} `{EqDecision A} (l : list A) n (s : A),
  list_add_if_fresh s l = if decide (find_index s l n = NONE) then l ++ [s] else l.
Proof.
  intros A HA l; induction l as [|h l IH]; intros n s; [reflexivity|].
  cbn [list_add_if_fresh find_index]. rewrite (IH (n + 1) s).
  destruct (decide (s = h)) as [->|Hne]; destruct (decide (h = _)) as [E|E]; try congruence.
  - destruct (decide (SOME n = NONE)); [discriminate|reflexivity].
  - destruct (decide (find_index s l (n + 1) = NONE)); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "list_add_if_fresh_thm" *)
Theorem list_add_if_fresh_thm : forall {A} `{EqDecision A} (s : A) l,
  list_add_if_fresh s l = if MEM s l then l else l ++ [s].
Proof.
  intros A HA s l. rewrite (list_add_if_fresh_simp l 0 s).
  destruct (MEM s l) eqn:E.
  - destruct (decide (find_index s l 0 = NONE)) as [Hn|]; [|reflexivity].
    apply (find_index_NOT_MEM l s 0) in Hn. rewrite E in Hn. exfalso; apply Hn; reflexivity.
  - destruct (decide (find_index s l 0 = NONE)) as [|Hn]; [reflexivity|].
    exfalso. apply Hn. apply find_index_NOT_MEM. rewrite E. discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "find_index_append" *)
Theorem find_index_append : forall {A} `{EqDecision A} (s : A) l l' n,
  find_index s (l ++ l') n =
    match find_index s l n with
    | NONE => find_index s l' (n + LENGTH l)
    | SOME i => SOME i
    end.
Proof.
  intros A HA s l; induction l as [|h l IH]; intros l' n; cbn [app find_index LENGTH].
  - rewrite N.add_0_r. reflexivity.
  - destruct (decide (h = s)); [reflexivity|]. rewrite IH.
    replace (n + 1 + LENGTH l) with (n + N.succ (LENGTH l)) by lia. reflexivity.
Qed.

Lemma find_ffi_names_cons k (x : line a) xs rest :
  find_ffi_names (Section_ k (x :: xs) :: rest) =
    match x with
    | LabAsm (CallFFI s) _ _ _ =>
        list_add_if_fresh (ExtCall s) (find_ffi_names (Section_ k xs :: rest))
    | _ => find_ffi_names (Section_ k xs :: rest)
    end.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "has_io_name_find_index" *)
Theorem has_io_name_find_index : forall (l : list (sec a)) s,
  has_io_name s l -> exists y, find_index (ExtCall s) (find_ffi_names l) 0 = SOME y.
Proof.
  intros l s. induction l as [|k xs IH|k x xs rest IH] using code_ind; intros H.
  - contradiction.
  - exact (IH H).
  - rewrite find_ffi_names_cons.
    change (has_io_name s (Section_ k xs :: rest) \/
            match x with LabAsm (CallFFI i) _ _ _ => i = s | _ => False end) in H.
    assert (Hg : forall l', (exists y, find_index (ExtCall s) l' 0 = SOME y) ->
              exists y, find_index (ExtCall s) l' 0 = SOME y) by auto.
    destruct x as [| |y w bs ln]; try (destruct H as [H|[]]; exact (IH H)).
    destruct y as [l0|c0 r0 ri0 l0|l0|r0 l0|m| |]; try (destruct H as [H|[]]; exact (IH H)).
    rewrite (list_add_if_fresh_simp _ 0).
    destruct (decide (find_index (ExtCall m) (find_ffi_names (Section_ k xs :: rest)) 0 = NONE))
      as [En|En].
    + rewrite find_index_append. destruct H as [H|<-].
      * destruct (IH H) as [y Hy]. rewrite Hy. eauto.
      * rewrite En. cbn [find_index]. destruct (decide (ExtCall m = ExtCall m)); [eauto|congruence].
    + destruct H as [H|<-]; [exact (IH H)|].
      destruct (find_index (ExtCall m) (find_ffi_names (Section_ k xs :: rest)) 0); [eauto|congruence].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "find_index_in_range" *)
Theorem find_index_in_range : forall {A} `{EqDecision A} (s : A) l x n,
  find_index s l n = SOME x -> x < n + LENGTH l /\ x >= n.
Proof. intros A HA s l x n H. apply find_index_LESS_LENGTH in H. lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "find_index_in_range0" *)
Theorem find_index_in_range0 : forall {A} `{EqDecision A} (s : A) l x,
  find_index s l 0 = SOME x -> x < LENGTH l /\ x >= 0.
Proof. intros A HA s l x H. apply find_index_LESS_LENGTH in H. lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "EL_get_ffi_index_MEM" *)
Theorem EL_get_ffi_index_MEM : forall {A} `{EqDecision A} `{Inhabited A} (s : A) ls,
  MEM s ls -> EL (get_ffi_index ls s) ls = s.
Proof.
  intros A HA HI s ls H. unfold get_ffi_index.
  destruct (find_index_MEM ls s 0 H) as (i & Hi & _ & He). rewrite Hi. exact He.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "has_io_name_EXISTS" *)
Theorem has_io_name_EXISTS : forall name (ls : list (sec a)),
  has_io_name name ls <->
  EXISTS (fun x => ⌜match x with LabAsm (CallFFI i) _ _ _ => i = name | _ => False end⌝)
    (FLAT (MAP Section_lines ls)).
Proof.
  intros name ls. induction ls as [|k xs IH|k x xs rest IH] using code_ind.
  - cbn. split; [intros []|discriminate].
  - exact IH.
  - change (has_io_name name (Section_ k xs :: rest) \/
            match x with LabAsm (CallFFI i) _ _ _ => i = name | _ => False end <->
            is_true (EXISTS (fun x => ⌜match x with LabAsm (CallFFI i) _ _ _ => i = name | _ => False end⌝)
              (x :: FLAT (MAP Section_lines (Section_ k xs :: rest))))).
    rewrite IH. cbn [EXISTS]. unfold is_true. rewrite Bool.orb_true_iff, bool_decide_spec.
    tauto.
Qed.

End FfiNames.
