(** * CakeML [lab_to_targetProof]: syntactic properties of [remove_labels] (2)

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml] (HOL
    lines 3613-4101): the invariants [encd0], [length_leq], [label_one],
    [encd], [length_ok], [label_zero] and [aligned] of the passes of
    [remove_labels].

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v].
    - The invariants used under [EVERY] ([line_encd0], [line_length_leq],
      [label_one], [label_zero], [line_length_ok], [line_aligned] and
      their [sec_] versions) are [bool]-valued, HOL's existential in
      [line_encd0] being decided classically ([⌜_⌝]); [line_encd],
      [lines_encd] and [all_encd] are [Prop]-valued.
    - HOL's overloads [all_encd0] and [all_length_leq] are [Abbreviation]s.
    - The ML binding [line_encd_ind] is not ported. *)

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
From Galette.cakeml.compiler.backend.semantics Require Import targetSem targetProps.
From Galette.cakeml.compiler.backend.semantics Require Import labSem labProps.
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import basic bytes rl_syntax.
Open Scope N_scope.

Ltac bool_iff :=
  unfold is_true in *;
  rewrite ?Bool.andb_true_iff, ?Bool.orb_true_iff, ?bool_decide_spec, ?N.eqb_eq, ?N.leb_le,
    ?N.ltb_lt in *.

Section Encd0.
Context {a : N}.

(** ** Invariant: lines are encoded and non-label lengths annotated *)

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_encd0_def" *)
Definition line_encd0 (enc : asm.asm a -> list word8) (l : line a) : bool :=
  match l with
  | Asm b bytes len => bool_decide (enc (cbw_to_asm b) = bytes) && (len =? LENGTH bytes)
  | LabAsm l w bytes len =>
      bool_decide (enc (lab_inst w l) = bytes) && (LENGTH bytes <=? len) &&
      ⌜exists w', len = LENGTH (enc (lab_inst w' l))⌝
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_encd0_def" *)
Definition sec_encd0 (enc : asm.asm a -> list word8) (s : sec a) : bool :=
  match s with Section_ _ ls => EVERY (line_encd0 enc) ls end.

End Encd0.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_encd0" *)
Abbreviation all_encd0 enc l := (EVERY (sec_encd0 enc) l).

Section Encd0Lemmas.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_sec_list_encd0" *)
Theorem enc_sec_list_encd0 : forall enc (ls : list (sec a)), all_encd0 enc (enc_sec_list enc ls).
Proof.
  intros enc ls. unfold enc_sec_list; cbv zeta.
  induction ls as [|[k lines] rest IH]; [reflexivity|].
  cbn [MAP map EVERY enc_sec sec_encd0]. rewrite IH, Bool.andb_true_r.
  induction lines as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IHl]; [reflexivity| | |];
    cbn [MAP map EVERY enc_line]; rewrite IHl, Bool.andb_true_r; try reflexivity; cbv zeta;
    unfold line_encd0; bool_iff.
  - split; reflexivity.
  - split; [split; [reflexivity|lia]|]. exists (n2w 0). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_encd0" *)
Theorem enc_lines_again_encd0 : forall labs ffis pos enc (lines : list (line a)) acc ok res ok',
  enc_lines_again labs ffis pos enc lines (acc, ok) = (res, ok') /\
  EVERY (line_encd0 enc) lines /\ EVERY (line_encd0 enc) acc ->
  EVERY (line_encd0 enc) res.
Proof.
  intros labs ffis pos enc lines. revert pos.
  induction lines as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos acc ok res ok' (H & Hl & Ha);
    cbn [enc_lines_again] in H; cbn [EVERY] in Hl.
  - injection H as <- _. rewrite EVERY_rev. exact Ha.
  - eapply IH; split; [exact H|split; [exact Hl|]]. cbn [EVERY]. rewrite Ha. reflexivity.
  - apply Bool.andb_true_iff in Hl as [Hx Hl].
    eapply IH; split; [exact H|split; [exact Hl|]]. cbn [EVERY]. rewrite Hx, Ha. reflexivity.
  - apply Bool.andb_true_iff in Hl as [Hx Hl]. cbv zeta in H. destruct (decide _).
    + eapply IH; split; [exact H|split; [exact Hl|]]. cbn [EVERY]. rewrite Hx, Ha. reflexivity.
    + eapply IH; split; [exact H|split; [exact Hl|]]. cbn [EVERY]. rewrite Ha, Bool.andb_true_r.
      unfold line_encd0 in Hx |- *. bool_iff. destruct Hx as [[_ Hx1] [w' Hw']].
      split; [split; [reflexivity|rewrite MAX_max; lia]|].
      rewrite MAX_max. destruct (N.max_spec (LENGTH (enc (lab_inst (get_jump_offset x ffis labs pos) x))) l)
        as [[_ ->]|[_ ->]]; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_secs_again_encd0" *)
Theorem enc_secs_again_encd0 : forall pos labs ffis enc (ls res : list (sec a)) ok,
  enc_secs_again pos labs ffis enc ls = (res, ok) /\ all_encd0 enc ls -> all_encd0 enc res.
Proof.
  intros pos labs ffis enc ls; revert pos.
  induction ls as [|[k lines] rest IH]; intros pos res ok (H & Hok); cbn [enc_secs_again] in H.
  - injection H as <- _. reflexivity.
  - destruct (enc_lines_again labs ffis pos enc lines ([], true)) as [lines1 [pos1 ok1]] eqn:E1.
    destruct (enc_secs_again pos1 labs ffis enc rest) as [rest1 ok2] eqn:E2.
    injection H as <- _. cbn in Hok |- *. apply Bool.andb_true_iff in Hok as [H1 H2].
    apply Bool.andb_true_iff. split; [|exact (IH _ _ _ (conj E2 H2))].
    exact (enc_lines_again_encd0 _ _ _ _ _ [] true _ _ (conj E1 (conj H1 eq_refl))).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_upd_lab_len_encd0" *)
Theorem lines_upd_lab_len_encd0 : forall enc pos (ls acc : list (line a)),
  EVERY (line_encd0 enc) ls /\ EVERY (line_encd0 enc) acc ->
  EVERY (line_encd0 enc) (FST (lines_upd_lab_len pos ls acc)).
Proof.
  intros enc pos ls; revert pos.
  induction ls as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos acc (Hl & Ha);
    cbn [lines_upd_lab_len]; cbn [EVERY] in Hl.
  - cbn. rewrite EVERY_rev. exact Ha.
  - apply IH. split; [exact Hl|]. cbn [EVERY]. rewrite Ha. reflexivity.
  - apply Bool.andb_true_iff in Hl as [Hx Hl]. apply IH. split; [exact Hl|].
    cbn [EVERY]. rewrite Hx, Ha. reflexivity.
  - apply Bool.andb_true_iff in Hl as [Hx Hl]. apply IH. split; [exact Hl|].
    cbn [EVERY]. rewrite Hx, Ha. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "upd_lab_len_encd0" *)
Theorem upd_lab_len_encd0 : forall enc pos (ss : list (sec a)),
  all_encd0 enc ss -> all_encd0 enc (upd_lab_len pos ss).
Proof.
  intros enc pos ss; revert pos; induction ss as [|[k lines] rest IH]; intros pos H; [reflexivity|].
  cbn [upd_lab_len]. cbn in H. apply Bool.andb_true_iff in H as [H1 H2].
  pose proof (lines_upd_lab_len_encd0 enc pos lines [] (conj H1 eq_refl)) as Hl.
  destruct (lines_upd_lab_len pos lines []) as [lines1 pos1].
  cbn. apply Bool.andb_true_iff. split; [exact Hl|apply IH, H2].
Qed.

End Encd0Lemmas.

(** ** Invariants: annotated lengths not too small; label lengths 0 or 1 *)

Section LengthLeq.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_length_leq_def" *)
Definition line_length_leq (l : line a) : bool :=
  match l with
  | LabAsm _ _ bytes l => LENGTH bytes <=? l
  | Asm _ bytes l => LENGTH bytes <=? l
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_length_leq_def" *)
Definition sec_length_leq (s : sec a) : bool :=
  match s with Section_ _ ls => EVERY line_length_leq ls end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "label_one_def" *)
Definition label_one (l : line a) : bool :=
  match l with
  | Label _ _ n => n <=? 1
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_label_one_def" *)
Definition sec_label_one (s : sec a) : bool :=
  match s with Section_ _ ls => EVERY label_one ls end.

End LengthLeq.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_length_leq" *)
Abbreviation all_length_leq l := (EVERY sec_length_leq l).

Section LabelOne.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_upd_lab_len_label_one" *)
Theorem lines_upd_lab_len_label_one : forall pos (ls acc : list (line a)),
  EVERY label_one acc -> EVERY label_one (FST (lines_upd_lab_len pos ls acc)).
Proof.
  intros pos ls; revert pos.
  induction ls as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos acc Ha; cbn [lines_upd_lab_len].
  - cbn. rewrite EVERY_rev. exact Ha.
  - apply IH. cbn [EVERY]. rewrite Ha, Bool.andb_true_r. cbn. destruct (EVEN pos); reflexivity.
  - apply IH. cbn [EVERY]. rewrite Ha. reflexivity.
  - apply IH. cbn [EVERY]. rewrite Ha. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "upd_lab_len_label_one" *)
Theorem upd_lab_len_label_one : forall pos (ss : list (sec a)),
  EVERY sec_label_one (upd_lab_len pos ss).
Proof.
  intros pos ss; revert pos; induction ss as [|[k lines] rest IH]; intros pos; [reflexivity|].
  cbn [upd_lab_len].
  pose proof (lines_upd_lab_len_label_one pos lines [] eq_refl) as Hl.
  destruct (lines_upd_lab_len pos lines []) as [lines1 pos1].
  cbn. apply Bool.andb_true_iff. split; [exact Hl|apply IH].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_simp_label_one" *)
Theorem enc_lines_again_simp_label_one : forall labs ffis pos enc (ls res : list (line a)) ok,
  enc_lines_again_simp labs ffis pos enc ls = (res, ok) /\ EVERY label_one ls ->
  EVERY label_one res.
Proof.
  intros labs ffis pos enc ls; revert pos.
  induction ls as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos res ok (H & Hl);
    cbn [enc_lines_again_simp] in H; cbn [EVERY] in Hl.
  - injection H as <- _. reflexivity.
  - apply Bool.andb_true_iff in Hl as [Hx Hl].
    destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok1] eqn:E.
    injection H as <- _. cbn [EVERY]. rewrite Hx. exact (IH _ _ _ (conj E Hl)).
  - destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok1] eqn:E.
    injection H as <- _. exact (IH _ _ _ (conj E Hl)).
  - cbv zeta in H. destruct (decide _).
    + destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok1] eqn:E.
      injection H as <- _. exact (IH _ _ _ (conj E Hl)).
    + destruct (enc_lines_again_simp labs ffis _ enc xs) as [rest ok1] eqn:E.
      injection H as <- _. exact (IH _ _ _ (conj E Hl)).
Qed.

Lemma enc_lines_again_simp_of labs ffis pos enc (lines : list (line a)) lines1 pos1 ok1 :
  enc_lines_again labs ffis pos enc lines ([], true) = (lines1, (pos1, ok1)) ->
  enc_lines_again_simp labs ffis pos enc lines = (lines1, ok1) /\ pos1 = sec_length lines1 pos.
Proof.
  intros H. pose proof (enc_lines_again_simp_EQ labs ffis pos enc lines [] true) as E.
  destruct (enc_lines_again_simp labs ffis pos enc lines) as [ls' flag]. rewrite E in H.
  injection H as <- <- <-. split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_secs_again_label_one" *)
Theorem enc_secs_again_label_one : forall pos labs ffis enc (lines res : list (sec a)) ok,
  enc_secs_again pos labs ffis enc lines = (res, ok) /\ EVERY sec_label_one lines ->
  EVERY sec_label_one res.
Proof.
  intros pos labs ffis enc ls; revert pos.
  induction ls as [|[k lines] rest IH]; intros pos res ok (H & Hok); cbn [enc_secs_again] in H.
  - injection H as <- _. reflexivity.
  - destruct (enc_lines_again labs ffis pos enc lines ([], true)) as [lines1 [pos1 ok1]] eqn:E1.
    destruct (enc_secs_again pos1 labs ffis enc rest) as [rest1 ok2] eqn:E2.
    injection H as <- _. cbn in Hok |- *. apply Bool.andb_true_iff in Hok as [H1 H2].
    apply Bool.andb_true_iff. split; [|exact (IH _ _ _ (conj E2 H2))].
    destruct (enc_lines_again_simp_of _ _ _ _ _ _ _ _ E1) as [Es _].
    exact (enc_lines_again_simp_label_one _ _ _ _ _ _ _ (conj Es H1)).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_length_pad_section1" *)
Theorem line_length_pad_section1 : forall (nop : list word8) (ls acc : list (line a)),
  LENGTH nop = 1 /\ EVERY label_one ls /\ EVERY line_length_leq ls /\
  ~ EVERY is_Label acc /\ SUM (MAP line_length acc) = SUM (MAP line_len acc) ->
  SUM (MAP line_length (pad_section nop ls acc)) = SUM (MAP line_len ls) + SUM (MAP line_len acc).
Proof.
  intros nop ls; induction ls as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH];
    intros acc (Hn & H1 & H2 & H3 & H4); cbn [pad_section]; cbn [EVERY] in H1, H2.
  - rewrite !map_rev, !SUM_rev. cbn. lia.
  - apply Bool.andb_true_iff in H1 as [Hx H1]. cbn [label_one] in Hx. apply N.leb_le in Hx.
    rewrite IH.
    + cbn [MAP map SUM line_len]. destruct (N.eqb_spec l 0) as [->|Hl0].
      * lia.
      * rewrite line_len_add_nop1 by exact H3. lia.
    + split; [exact Hn|split; [exact H1|split; [exact H2|split]]].
      * cbn [EVERY is_Label andb]. destruct (l =? 0); [exact H3|].
        rewrite EVERY_is_Label_add_nop_preserved. exact H3.
      * cbn [MAP map SUM line_length line_len N.eqb Pos.eqb]. destruct (N.eqb_spec l 0) as [->|Hl0]; [lia|].
        rewrite line_length_add_nop1, line_len_add_nop1 by exact H3. lia.
  - apply Bool.andb_true_iff in H2 as [Hx H2]. cbn [line_length_leq] in Hx. apply N.leb_le in Hx.
    rewrite IH.
    + cbn [MAP map SUM line_len]. lia.
    + split; [exact Hn|split; [exact H1|split; [exact H2|split]]].
      * cbn [EVERY is_Label andb]. discriminate.
      * cbn [MAP map SUM line_length line_len N.eqb Pos.eqb]. rewrite LENGTH_pad_bytes by lia. lia.
  - apply Bool.andb_true_iff in H2 as [Hx H2]. cbn [line_length_leq] in Hx. apply N.leb_le in Hx.
    rewrite IH.
    + cbn [MAP map SUM line_len]. lia.
    + split; [exact Hn|split; [exact H1|split; [exact H2|split]]].
      * cbn [EVERY is_Label andb]. discriminate.
      * cbn [MAP map SUM line_length line_len N.eqb Pos.eqb]. rewrite LENGTH_pad_bytes by lia. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_len_pad_section1" *)
Theorem line_len_pad_section1 : forall (nop : list word8) (xs aux : list (line a)),
  LENGTH nop = 1 /\ EVERY label_one xs /\ ~ EVERY is_Label aux ->
  SUM (MAP line_len (pad_section nop xs aux)) = SUM (MAP line_len xs) + SUM (MAP line_len aux).
Proof.
  intros nop xs; induction xs as [|[k1 k2 l|x1 x2 l|x w bytes l] ys IH];
    intros aux (Hn & H1 & H3); cbn [pad_section]; cbn [EVERY] in H1.
  - rewrite !map_rev, !SUM_rev. cbn. lia.
  - apply Bool.andb_true_iff in H1 as [Hx H1]. cbn [label_one] in Hx. apply N.leb_le in Hx.
    rewrite IH.
    + cbn [MAP map SUM line_len]. destruct (N.eqb_spec l 0) as [->|Hl0]; [lia|].
      rewrite line_len_add_nop1 by exact H3. lia.
    + split; [exact Hn|split; [exact H1|]].
      cbn [EVERY is_Label andb]. destruct (l =? 0); [exact H3|].
      rewrite EVERY_is_Label_add_nop_preserved. exact H3.
  - rewrite IH; [cbn [MAP map SUM line_len]; lia|].
    split; [exact Hn|split; [exact H1|]]. cbn [EVERY is_Label andb]. discriminate.
  - rewrite IH; [cbn [MAP map SUM line_len]; lia|].
    split; [exact Hn|split; [exact H1|]]. cbn [EVERY is_Label andb]. discriminate.
Qed.

End LabelOne.

(** ** Invariant: lines are encoded and annotated lengths are correct *)

Section Encd.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_encd_def" *)
Definition line_encd (enc : asm.asm a -> list word8) (labs : spt (spt N)) (ffis : list ffiname)
    (pos : N) (l : line a) : Prop :=
  match l with
  | Asm b bytes len => enc (cbw_to_asm b) = bytes /\ len = LENGTH bytes
  | LabAsm labLang.Halt _ bytes len =>
      enc (asm.Jump (- n2w (pos + ffi_offset))%w) = bytes /\ LENGTH bytes <= len
  | LabAsm Install _ bytes len =>
      enc (asm.Jump (- n2w (pos + 2 * ffi_offset))%w) = bytes /\ LENGTH bytes <= len
  | LabAsm (CallFFI s) _ bytes len =>
      enc (asm.Jump (- n2w (pos + (get_ffi_index ffis (ExtCall s) + 3) * ffi_offset))%w) = bytes /\
      LENGTH bytes <= len
  | LabAsm (Jump l) _ bytes len =>
      enc (asm.Jump (n2w (find_pos l labs) + - n2w pos)%w) = bytes /\ LENGTH bytes <= len
  | LabAsm (JumpCmp a0 b c l) _ bytes len =>
      enc (asm.JumpCmp a0 b c (n2w (find_pos l labs) + - n2w pos)%w) = bytes /\ LENGTH bytes <= len
  | LabAsm (LocValue k l) _ bytes len =>
      enc (asm.Loc k (n2w (find_pos l labs) + - n2w pos)%w) = bytes /\ LENGTH bytes <= len
  | LabAsm (Call l) _ bytes len =>
      enc (asm.Call (n2w (find_pos l labs) + - n2w pos)%w) = bytes /\ LENGTH bytes <= len
  | _ => True
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_encd_def" *)
Fixpoint lines_encd (enc : asm.asm a -> list word8) (labs : spt (spt N)) (ffis : list ffiname)
    (pos : N) (ls : list (line a)) : Prop :=
  match ls with
  | [] => True
  | l :: ls => line_encd enc labs ffis pos l /\ lines_encd enc labs ffis (pos + line_len l) ls
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_encd_def" *)
Fixpoint all_encd (enc : asm.asm a -> list word8) (labs : spt (spt N)) (ffis : list ffiname)
    (pos : N) (ss : list (sec a)) : Prop :=
  match ss with
  | [] => True
  | Section_ k ls :: ss =>
      lines_encd enc labs ffis pos ls /\
      all_encd enc labs ffis (pos + SUM (MAP line_len ls)) ss
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_encd_length_leq" *)
Theorem line_encd_length_leq : forall enc labs ffis pos (l : line a),
  line_encd enc labs ffis pos l -> line_length_leq l.
Proof.
  intros enc labs ffis pos l H.
  destruct l as [k1 k2 l|b bytes l|x w bytes l]; [reflexivity| |destruct x];
    cbn in H |- *; try reflexivity; apply N.leb_le; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_encd_length_leq" *)
Theorem lines_encd_length_leq : forall enc labs ffis pos (ls : list (line a)),
  lines_encd enc labs ffis pos ls -> EVERY line_length_leq ls.
Proof.
  intros enc labs ffis pos ls; revert pos; induction ls as [|l ls IH]; intros pos H;
    [reflexivity|]. destruct H as [H1 H2]. cbn [EVERY]. apply Bool.andb_true_iff.
  split; [exact (line_encd_length_leq _ _ _ _ _ H1)|exact (IH _ H2)].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_encd_length_leq" *)
Theorem all_encd_length_leq : forall enc labs ffis pos (ls : list (sec a)),
  all_encd enc labs ffis pos ls -> all_length_leq ls.
Proof.
  intros enc labs ffis pos ls; revert pos; induction ls as [|[k l] ls IH]; intros pos H;
    [reflexivity|]. destruct H as [H1 H2]. cbn [EVERY sec_length_leq]. apply Bool.andb_true_iff.
  split; [exact (lines_encd_length_leq _ _ _ _ _ H1)|exact (IH _ H2)].
Qed.

Lemma line_encd_of_offset enc labs ffis pos (x : asm_with_lab a) w bytes len :
  enc (lab_inst (get_jump_offset x ffis labs pos) x) = bytes -> LENGTH bytes <= len ->
  line_encd enc labs ffis pos (LabAsm x w bytes len).
Proof.
  intros H1 H2. destruct x as [l|c r ri l|l|r l|s| |]; cbn [line_encd lab_inst get_jump_offset] in *;
    (split; [|exact H2]); rewrite <- H1; f_equal; try f_equal;
    try match goal with |- context [get_ffi_index ?f ?e + 3] =>
          replace (get_ffi_index f e + 3) with (3 + get_ffi_index f e) by lia end;
    word_arith.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_simp_encd" *)
Theorem enc_lines_again_simp_encd : forall labs ffis pos enc (lines res : list (line a)),
  enc_lines_again_simp labs ffis pos enc lines = (res, true) /\
  EVERY label_one lines /\ EVERY (line_encd0 enc) lines ->
  lines_encd enc labs ffis pos res.
Proof.
  intros labs ffis pos enc lines; revert pos.
  induction lines as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos res (H & H1 & H2);
    cbn [enc_lines_again_simp] in H; cbn [EVERY] in H1, H2.
  - injection H as <-. exact Logic.I.
  - apply Bool.andb_true_iff in H1 as [_ H1].
    destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok] eqn:E.
    injection H as <- ->. split; [exact Logic.I|exact (IH _ _ (conj E (conj H1 H2)))].
  - apply Bool.andb_true_iff in H2 as [Hx H2].
    destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok] eqn:E.
    injection H as <- ->. split; [|exact (IH _ _ (conj E (conj H1 H2)))].
    unfold line_encd0 in Hx. bool_iff. destruct Hx as [Hx1 Hx2]. cbn. split; assumption.
  - apply Bool.andb_true_iff in H2 as [Hx H2]. cbv zeta in H. destruct (decide _) as [Ew|Nw].
    + destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok] eqn:E.
      injection H as <- ->. split; [|exact (IH _ _ (conj E (conj H1 H2)))].
      unfold line_encd0 in Hx. bool_iff. destruct Hx as [[Hx1 Hx2] _].
      apply line_encd_of_offset; [rewrite <- Ew; exact Hx1|exact Hx2].
    + destruct (enc_lines_again_simp labs ffis _ enc xs) as [rest ok] eqn:E.
      injection H as <- Hok. apply Bool.andb_true_iff in Hok as [Hl ->]. apply N.eqb_eq in Hl.
      split.
      * apply line_encd_of_offset; [reflexivity|]. rewrite MAX_max. lia.
      * cbn [line_len]. rewrite Hl in E |- *. exact (IH _ _ (conj E (conj H1 H2))).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_secs_again_encd" *)
Theorem enc_secs_again_encd : forall pos labs ffis enc (ls res : list (sec a)),
  enc_secs_again pos labs ffis enc ls = (res, true) /\ EVERY sec_label_one ls /\ EVERY (sec_encd0 enc) ls ->
  all_encd enc labs ffis pos res.
Proof.
  intros pos labs ffis enc ls; revert pos.
  induction ls as [|[k lines] rest IH]; intros pos res (H & H1 & H2); cbn [enc_secs_again] in H.
  - injection H as <-. exact Logic.I.
  - destruct (enc_lines_again labs ffis pos enc lines ([], true)) as [lines1 [pos1 ok1]] eqn:E1.
    destruct (enc_secs_again pos1 labs ffis enc rest) as [rest1 ok2] eqn:E2.
    injection H as <- Hok. apply Bool.andb_true_iff in Hok as [-> ->].
    cbn [EVERY sec_label_one sec_encd0] in H1, H2.
    apply Bool.andb_true_iff in H1 as [H1a H1b]. apply Bool.andb_true_iff in H2 as [H2a H2b].
    destruct (enc_lines_again_simp_of _ _ _ _ _ _ _ _ E1) as [Es Ep].
    split.
    + exact (enc_lines_again_simp_encd _ _ _ _ _ _ (conj Es (conj H1a H2a))).
    + rewrite Ep, sec_length_sum_line_len in E2. rewrite N.add_comm.
      exact (IH _ _ (conj E2 (conj H1b H2b))).
Qed.

End Encd.

(** ** Invariant: annotated lengths are correct *)

Section LengthOk.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_length_ok_def" *)
Definition line_length_ok (l : line a) : bool := LENGTH (line_bytes l) =? line_len l.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_length_ok_def" *)
Definition sec_length_ok (s : sec a) : bool :=
  match s with Section_ _ ls => EVERY line_length_ok ls end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_length_sum_line_length" *)
Theorem sec_length_sum_line_length : forall (ls : list (line a)) n,
  EVERY line_length_ok ls -> sec_length ls n = SUM (MAP line_length ls) + n.
Proof.
  induction ls as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros n H; [cbn; lia| | |];
    cbn [EVERY] in H; apply Bool.andb_true_iff in H as [Hx H];
    unfold line_length_ok in Hx; cbn [line_bytes line_len LENGTH] in Hx; apply N.eqb_eq in Hx;
    cbn [sec_length MAP map SUM line_length]; rewrite IH by exact H.
  - subst l. cbn. lia.
  - lia.
  - lia.
Qed.

End LengthOk.

(** ** Invariant: all labels annotated with length 0 *)

Section LabelZero.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "label_zero_def" *)
Definition label_zero (l : line a) : bool :=
  match l with
  | Label _ _ n => n =? 0
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_label_zero_def" *)
Definition sec_label_zero (s : sec a) : bool :=
  match s with Section_ _ ls => EVERY label_zero ls end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "EVERY_label_zero_add_nop" *)
Theorem EVERY_label_zero_add_nop : forall nop (xs : list (line a)),
  EVERY label_zero (add_nop nop xs) = EVERY label_zero xs.
Proof. intros nop xs; induction xs as [|[] ys IH]; cbn; [reflexivity|rewrite IH| |]; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "EVERY_label_zero_pad_section" *)
Theorem EVERY_label_zero_pad_section : forall nop (xs aux : list (line a)),
  EVERY label_zero aux -> EVERY label_zero (pad_section nop xs aux).
Proof.
  intros nop xs; induction xs as [|[k1 k2 l|x1 x2 l|x w bytes l] ys IH]; intros aux H;
    cbn [pad_section].
  - rewrite EVERY_rev. exact H.
  - apply IH. cbn [EVERY label_zero N.eqb andb]. destruct (l =? 0); [exact H|].
    rewrite EVERY_label_zero_add_nop. exact H.
  - apply IH. exact H.
  - apply IH. exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "EVERY_sec_label_zero_pad_code" *)
Theorem EVERY_sec_label_zero_pad_code : forall nop (ls : list (sec a)),
  EVERY sec_label_zero (pad_code nop ls).
Proof.
  intros nop ls; induction ls as [|[k xs] ls IH]; [reflexivity|].
  cbn [pad_code EVERY sec_label_zero]. rewrite IH, Bool.andb_true_r.
  apply EVERY_label_zero_pad_section. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_simp_label_zero" *)
Theorem enc_lines_again_simp_label_zero : forall labs ffis pos enc (ls res : list (line a)) ok,
  enc_lines_again_simp labs ffis pos enc ls = (res, ok) /\ EVERY label_zero ls ->
  EVERY label_zero res.
Proof.
  intros labs ffis pos enc ls; revert pos.
  induction ls as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos res ok (H & Hl);
    cbn [enc_lines_again_simp] in H; cbn [EVERY] in Hl.
  - injection H as <- _. reflexivity.
  - apply Bool.andb_true_iff in Hl as [Hx Hl].
    destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok1] eqn:E.
    injection H as <- _. cbn [EVERY]. rewrite Hx. exact (IH _ _ _ (conj E Hl)).
  - destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok1] eqn:E.
    injection H as <- _. exact (IH _ _ _ (conj E Hl)).
  - cbv zeta in H. destruct (decide _).
    + destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok1] eqn:E.
      injection H as <- _. exact (IH _ _ _ (conj E Hl)).
    + destruct (enc_lines_again_simp labs ffis _ enc xs) as [rest ok1] eqn:E.
      injection H as <- _. exact (IH _ _ _ (conj E Hl)).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_secs_again_label_zero" *)
Theorem enc_secs_again_label_zero : forall pos labs ffis enc (lines res : list (sec a)) ok,
  enc_secs_again pos labs ffis enc lines = (res, ok) /\ EVERY sec_label_zero lines ->
  EVERY sec_label_zero res.
Proof.
  intros pos labs ffis enc ls; revert pos.
  induction ls as [|[k lines] rest IH]; intros pos res ok (H & Hok); cbn [enc_secs_again] in H.
  - injection H as <- _. reflexivity.
  - destruct (enc_lines_again labs ffis pos enc lines ([], true)) as [lines1 [pos1 ok1]] eqn:E1.
    destruct (enc_secs_again pos1 labs ffis enc rest) as [rest1 ok2] eqn:E2.
    injection H as <- _. cbn in Hok |- *. apply Bool.andb_true_iff in Hok as [H1 H2].
    apply Bool.andb_true_iff. split; [|exact (IH _ _ _ (conj E2 H2))].
    destruct (enc_lines_again_simp_of _ _ _ _ _ _ _ _ E1) as [Es _].
    exact (enc_lines_again_simp_label_zero _ _ _ _ _ _ _ (conj Es H1)).
Qed.

Lemma enc_ok_EVEN (c : asm_config a) (i : asm.asm a) :
  enc_ok c -> code_alignment c <> 0 -> EVEN (LENGTH (encode c i)).
Proof.
  intros (H1 & H2 & _) Hc. destruct (H2 i) as [Hm _].
  apply N.even_spec. exists (LENGTH (encode c i) / 2).
  assert (E : LENGTH (encode c i) mod 2 = 0).
  { replace (code_alignment c) with (1 + (code_alignment c - 1)) in Hm by lia.
    rewrite N.pow_add_r in Hm. rewrite N.Div0.mod_mul_r in Hm. lia. }
  pose proof (N.div_mod (LENGTH (encode c i)) 2 ltac:(discriminate)). lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_upd_lab_len_encd0_label_zero" *)
Theorem lines_upd_lab_len_encd0_label_zero : forall (c : asm_config a) enc pos (lines aux : list (line a)),
  enc_ok c /\ enc = encode c /\ code_alignment c <> 0 /\
  EVERY (line_encd0 enc) lines /\ EVEN pos /\ EVERY label_zero aux ->
  EVERY label_zero (FST (lines_upd_lab_len pos lines aux)).
Proof.
  intros c enc pos lines; revert pos.
  induction lines as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos aux (Hc & -> & Ha & Hl & He & Hz);
    cbn [lines_upd_lab_len]; cbn [EVERY] in Hl.
  - cbn. rewrite EVERY_rev. exact Hz.
  - rewrite He. apply IH. split; [exact Hc|split; [reflexivity|split; [exact Ha|split; [exact Hl|]]]].
    split; [rewrite N.add_0_r; exact He|]. cbn [EVERY label_zero]. rewrite Hz. reflexivity.
  - apply Bool.andb_true_iff in Hl as [Hx Hl]. unfold line_encd0 in Hx. bool_iff.
    destruct Hx as [Hx1 Hx2]. apply IH. split; [exact Hc|split; [reflexivity|split; [exact Ha|split; [exact Hl|]]]].
    split; [|exact Hz]. rewrite N.even_add, He, Hx2, <- Hx1, enc_ok_EVEN by assumption. reflexivity.
  - apply Bool.andb_true_iff in Hl as [Hx Hl]. unfold line_encd0 in Hx. bool_iff.
    destruct Hx as [_ [w' Hw']]. apply IH. split; [exact Hc|split; [reflexivity|split; [exact Ha|split; [exact Hl|]]]].
    split; [|exact Hz]. rewrite N.even_add, He, Hw', enc_ok_EVEN by assumption. reflexivity.
Qed.

Lemma NULL_LAST_cons (x : line a) xs :
  is_Label (LAST (x :: xs)) = match xs with [] => is_Label x | _ => is_Label (LAST xs) end.
Proof. destruct xs; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "EVEN_sec_length_lines_upd_lab_len" *)
Theorem EVEN_sec_length_lines_upd_lab_len : forall pos (lines acc : list (line a)),
  (if NULL lines then EVEN pos /\ EVEN (SUM (MAP line_len acc))
   else is_Label (LAST lines) /\ EVEN (pos + SUM (MAP line_len acc))) ->
  EVEN (SUM (MAP line_len (FST (lines_upd_lab_len pos lines acc)))).
Proof.
  intros pos lines; revert pos.
  induction lines as [|x xs IH]; intros pos acc H.
  - cbn [lines_upd_lab_len FST]. rewrite map_rev, SUM_rev. apply H.
  - cbn [NULL] in H. destruct H as [Hl He]. rewrite NULL_LAST_cons in Hl.
    destruct x as [k1 k2 l|x1 x2 l|x w bytes l]; cbn [lines_upd_lab_len].
    + set (l1 := if EVEN pos then 0 else 1).
      apply IH. destruct xs as [|y ys]; cbn [NULL].
      * cbn [NULL MAP map SUM line_len]. unfold l1. rewrite !N.even_add in *.
        destruct (EVEN pos) eqn:Ep; destruct (EVEN (SUM (MAP line_len acc))) eqn:Es;
          cbn in *; try discriminate; split; reflexivity.
      * split; [exact Hl|]. cbn [MAP map SUM line_len].
        replace (pos + l1 + (l1 + SUM (MAP line_len acc))) with (pos + SUM (MAP line_len acc) + 2 * l1) by lia.
        rewrite N.even_add, He, N.even_mul. reflexivity.
    + apply IH. destruct xs as [|y ys]; [discriminate|]. split; [exact Hl|].
      cbn [MAP map SUM line_len].
      replace (pos + l + (l + SUM (MAP line_len acc))) with (pos + SUM (MAP line_len acc) + 2 * l) by lia.
      rewrite N.even_add, He, N.even_mul. reflexivity.
    + apply IH. destruct xs as [|y ys]; [discriminate|]. split; [exact Hl|].
      cbn [MAP map SUM line_len].
      replace (pos + l + (l + SUM (MAP line_len acc))) with (pos + SUM (MAP line_len acc) + 2 * l) by lia.
      rewrite N.even_add, He, N.even_mul. reflexivity.
Qed.

End LabelZero.

Section LabelZero2.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "upd_lab_len_encd0_label_zero" *)
Theorem upd_lab_len_encd0_label_zero : forall (c : asm_config a) enc pos (code : list (sec a)),
  enc_ok c /\ enc = encode c /\ code_alignment c <> 0 /\
  all_encd0 enc code /\ EVEN pos /\ EVERY sec_ends_with_label code ->
  EVERY sec_label_zero (upd_lab_len pos code).
Proof.
  intros c enc pos code; revert pos.
  induction code as [|[k lines] rest IH]; intros pos (Hc & -> & Ha & He0 & Hp & Hend); [reflexivity|].
  cbn [upd_lab_len]. cbn [EVERY sec_encd0 sec_ends_with_label] in He0, Hend.
  apply Bool.andb_true_iff in He0 as [He0 He1]. apply Bool.andb_true_iff in Hend as [Hend0 Hend1].
  pose proof (lines_upd_lab_len_encd0_label_zero c (encode c) pos lines []
                (conj Hc (conj eq_refl (conj Ha (conj He0 (conj Hp eq_refl)))))) as Hz.
  pose proof (SND_lines_upd_lab_len pos lines []) as Hs.
  pose proof (EVEN_sec_length_lines_upd_lab_len pos lines []) as Hev.
  destruct (lines_upd_lab_len pos lines []) as [lines1 pos1].
  cbn [FST SND MAP map SUM] in Hz, Hs, Hev.
  cbn [EVERY sec_label_zero]. apply Bool.andb_true_iff. split; [exact Hz|].
  apply IH. split; [exact Hc|split; [reflexivity|split; [exact Ha|split; [exact He1|split; [|exact Hend1]]]]].
  rewrite Hs. apply Bool.andb_true_iff in Hend0 as [Hnn Hlast].
  destruct lines as [|y ys]; [discriminate|].
  rewrite N.add_0_r in Hev. specialize (Hev (conj Hlast Hp)).
  rewrite N.sub_0_r, N.even_add, Hp, Hev. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_pos_val_0" *)
Theorem sec_pos_val_0 : forall pos (lines : list (line a)),
  ~ EVERY is_Label lines /\ EVERY label_zero lines -> sec_pos_val 0 pos lines = SOME pos.
Proof.
  intros pos lines; revert pos; induction lines as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH];
    intros pos [H1 H2]; cbn in H1, H2 |- *; [exfalso; apply H1; reflexivity| |reflexivity|reflexivity].
  apply Bool.andb_true_iff in H2 as [Hl H2]. apply N.eqb_eq in Hl. subst l.
  rewrite N.add_0_r. apply IH. split; [exact H1|exact H2].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_len_pad_section0" *)
Theorem line_len_pad_section0 : forall nop (ls aux : list (line a)),
  EVERY label_zero ls ->
  SUM (MAP line_len (pad_section nop ls aux)) = SUM (MAP line_len ls) + SUM (MAP line_len aux).
Proof.
  intros nop ls; induction ls as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros aux H;
    cbn [pad_section]; cbn [EVERY] in H.
  - rewrite map_rev, SUM_rev. cbn. lia.
  - apply Bool.andb_true_iff in H as [Hl H]. apply N.eqb_eq in Hl. subst l.
    rewrite IH by exact H. cbn [MAP map SUM line_len N.eqb]. lia.
  - rewrite IH by exact H. cbn [MAP map SUM line_len]. lia.
  - rewrite IH by exact H. cbn [MAP map SUM line_len]. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_label_zero_pos_val_0" *)
Theorem sec_label_zero_pos_val_0 : forall (xs : list (sec a)) pos,
  EVERY sec_label_zero xs -> pos_val 0 pos xs = pos.
Proof.
  intros xs pos. induction xs as [|k ys IH|k y ys xs IH] using code_ind; intros H.
  - reflexivity.
  - exact (IH H).
  - rewrite (proj2 (proj2 (pos_val_def 0 pos k xs y ys))).
    cbn [EVERY sec_label_zero] in H, IH. apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff in H1 as [Hy H1].
    destruct y as [k1 k2 l|x1 x2 l|x w bytes l]; cbn [is_Label N.eqb]; [|reflexivity|reflexivity].
    cbn [label_zero] in Hy. apply N.eqb_eq in Hy. subst l. cbn [line_length N.eqb].
    rewrite N.add_0_r. apply IH. apply Bool.andb_true_iff. split; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_ok_imp_sec_label_zero" *)
Theorem all_enc_ok_imp_sec_label_zero : forall (conf : asm_config a) labs ffis n code,
  all_enc_ok conf labs ffis n code -> EVERY sec_label_zero code.
Proof.
  intros conf labs ffis n code. revert n.
  induction code as [|k ys IH|k y ys xs IH] using code_ind; intros n H.
  - reflexivity.
  - destruct H as [_ H]. cbn. exact (IH _ H).
  - destruct H as [Hy H]. specialize (IH _ H). cbn [EVERY sec_label_zero] in IH |- *.
    apply Bool.andb_true_iff in IH as [H1 H2]. rewrite H1, H2.
    destruct y as [k1 k2 l|x1 x2 l|x w bytes l]; [|reflexivity|reflexivity].
    destruct Hy as [_ ->]. reflexivity.
Qed.

End LabelZero2.

(** ** Invariant: lines aligned *)

Section Aligned.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_aligned_def" *)
Definition line_aligned (m : N) (l : line a) : bool :=
  (line_len l mod m =? 0) && (line_length l mod m =? 0).

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_aligned_def" *)
Definition sec_aligned (noplen : N) (s : sec a) : bool :=
  match s with Section_ _ ls => EVERY (line_aligned noplen) ls end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_encd0_aligned" *)
Theorem all_encd0_aligned : forall (c : asm_config a) enc (code : list (sec a)),
  enc_ok c /\ enc = encode c /\ all_encd0 enc code /\ EVERY sec_label_zero code ->
  EVERY (sec_aligned (LENGTH (enc (Inst asm.Skip)))) code.
Proof.
  intros c enc code (Hc & -> & H1 & H2).
  destruct Hc as (Hc1 & Hc2 & _). rewrite <- Hc1.
  induction code as [|[k lines] rest IH]; [reflexivity|].
  cbn [EVERY sec_encd0 sec_label_zero sec_aligned] in H1, H2 |- *.
  apply Bool.andb_true_iff in H1 as [H1a H1b]. apply Bool.andb_true_iff in H2 as [H2a H2b].
  apply Bool.andb_true_iff. split; [|apply IH; assumption].
  clear -H1a H2a Hc2. induction lines as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IHl]; [reflexivity| | |];
    cbn [EVERY] in H1a, H2a |- *; apply Bool.andb_true_iff in H1a as [Hx1 H1a];
    apply Bool.andb_true_iff in H2a as [Hx2 H2a]; apply Bool.andb_true_iff;
    (split; [|apply IHl; assumption]); unfold line_aligned; cbn [line_len line_length].
  - cbn [label_zero] in Hx2. apply N.eqb_eq in Hx2. subst l. rewrite N.eqb_refl, !N.Div0.mod_0_l. reflexivity.
  - unfold line_encd0 in Hx1. bool_iff. destruct Hx1 as [<- ->].
    destruct (Hc2 (cbw_to_asm x1)) as [E _]. rewrite E. split; reflexivity.
  - unfold line_encd0 in Hx1. bool_iff. destruct Hx1 as [[<- _] [w' ->]].
    destruct (Hc2 (lab_inst w' x)) as [E1 _]. destruct (Hc2 (lab_inst w x)) as [E2 _].
    rewrite E1, E2. split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_simp_aligned" *)
Theorem enc_lines_again_simp_aligned : forall len labs ffis pos enc (ls res : list (line a)) ok,
  (forall a0, LENGTH (enc a0) mod len = 0) /\
  enc_lines_again_simp labs ffis pos enc ls = (res, ok) /\
  EVERY (line_aligned len) ls ->
  EVERY (line_aligned len) res.
Proof.
  intros len labs ffis pos enc ls; revert pos.
  induction ls as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos res ok (Henc & H & Hl);
    cbn [enc_lines_again_simp] in H; cbn [EVERY] in Hl.
  - injection H as <- _. reflexivity.
  - apply Bool.andb_true_iff in Hl as [Hx Hl].
    destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok1] eqn:E.
    injection H as <- _. cbn [EVERY]. rewrite Hx. exact (IH _ _ _ (conj Henc (conj E Hl))).
  - apply Bool.andb_true_iff in Hl as [Hx Hl].
    destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok1] eqn:E.
    injection H as <- _. cbn [EVERY]. rewrite Hx. exact (IH _ _ _ (conj Henc (conj E Hl))).
  - apply Bool.andb_true_iff in Hl as [Hx Hl]. cbv zeta in H. destruct (decide _).
    + destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok1] eqn:E.
      injection H as <- _. cbn [EVERY]. rewrite Hx. exact (IH _ _ _ (conj Henc (conj E Hl))).
    + destruct (enc_lines_again_simp labs ffis _ enc xs) as [rest ok1] eqn:E.
      injection H as <- _. cbn [EVERY]. apply Bool.andb_true_iff.
      split; [|exact (IH _ _ _ (conj Henc (conj E Hl)))].
      unfold line_aligned in Hx |- *. cbn [line_len line_length] in Hx |- *. bool_iff.
      rewrite MAX_max. split; [|apply Henc].
      destruct (N.max_spec (LENGTH (enc (lab_inst (get_jump_offset x ffis labs pos) x))) l)
        as [[_ ->]|[_ ->]]; [apply Hx|apply Henc].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_secs_again_aligned" *)
Theorem enc_secs_again_aligned : forall len pos labs ffis enc (lines res : list (sec a)) ok,
  (forall a0, LENGTH (enc a0) mod len = 0) /\
  enc_secs_again pos labs ffis enc lines = (res, ok) /\
  EVERY (sec_aligned len) lines ->
  EVERY (sec_aligned len) res.
Proof.
  intros len pos labs ffis enc ls; revert pos.
  induction ls as [|[k lines] rest IH]; intros pos res ok (Henc & H & Hok); cbn [enc_secs_again] in H.
  - injection H as <- _. reflexivity.
  - destruct (enc_lines_again labs ffis pos enc lines ([], true)) as [lines1 [pos1 ok1]] eqn:E1.
    destruct (enc_secs_again pos1 labs ffis enc rest) as [rest1 ok2] eqn:E2.
    injection H as <- _. cbn in Hok |- *. apply Bool.andb_true_iff in Hok as [H1 H2].
    apply Bool.andb_true_iff. split; [|exact (IH _ _ _ (conj Henc (conj E2 H2)))].
    destruct (enc_lines_again_simp_of _ _ _ _ _ _ _ _ E1) as [Es _].
    exact (enc_lines_again_simp_aligned _ _ _ _ _ _ _ _ (conj Henc (conj Es H1))).
Qed.

End Aligned.
