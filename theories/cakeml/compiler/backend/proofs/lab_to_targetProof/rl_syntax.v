(** * CakeML [lab_to_targetProof]: syntactic properties of [remove_labels] (1)

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml] (HOL
    lines 3123-3612): annotated lengths, [enc_lines_again_simp], padding,
    and the preservation of [code_similar] and [sec_labels_ok] by the
    passes of [remove_labels].

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v].
    - HOL's induction principles ([section_labels_ind], [add_nop_ind],
      [pad_section_ind], ...) are replaced by structural induction.
    - HOL's ML value [lines_upd_lab_len_AUX] (an unstored [Q.prove]) is
      the untagged Galette lemma of the same name; [enc_lines_again_simp_ind]
      is not ported.
    - Untagged Galette list helpers: [EVERY_app], [EVERY_rev], [SUM_app],
      [SUM_rev], [LIST_REL_length], [LIST_REL_rev], [LIST_REL_app_inv]. *)

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
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import basic bytes.
Open Scope N_scope.

(** ** List helpers (Galette) *)

Lemma EVERY_app {X} (P : X -> bool) l1 l2 : EVERY P (l1 ++ l2) = EVERY P l1 && EVERY P l2.
Proof. induction l1 as [|x l1 IH]; cbn; [reflexivity|]. rewrite IH, Bool.andb_assoc. reflexivity. Qed.

Lemma EVERY_rev {X} (P : X -> bool) l : EVERY P (REVERSE l) = EVERY P l.
Proof.
  induction l as [|x l IH]; cbn [REVERSE rev]; [reflexivity|].
  rewrite EVERY_app, IH. cbn. rewrite Bool.andb_true_r, Bool.andb_comm. reflexivity.
Qed.

Lemma SUM_app l1 l2 : SUM (l1 ++ l2) = SUM l1 + SUM l2.
Proof. induction l1 as [|x l1 IH]; cbn; [reflexivity|]. rewrite IH; lia. Qed.

Lemma SUM_rev l : SUM (REVERSE l) = SUM l.
Proof. induction l as [|x l IH]; cbn [rev]; [reflexivity|]. rewrite SUM_app, IH. cbn. lia. Qed.

Lemma LIST_REL_length {X Y} (R : X -> Y -> Prop) l1 l2 : LIST_REL R l1 l2 -> LENGTH l1 = LENGTH l2.
Proof. intros H; induction H; cbn; [reflexivity|]. rewrite IHLIST_REL. reflexivity. Qed.

Lemma LIST_REL_rev {X Y} (R : X -> Y -> Prop) l1 l2 :
  LIST_REL R l1 l2 -> LIST_REL R (REVERSE l1) (REVERSE l2).
Proof.
  intros H; induction H; cbn [rev]; [constructor|].
  apply LIST_REL_app; [exact IHLIST_REL|constructor; [exact H|constructor]].
Qed.

Lemma LIST_REL_app_inv {X Y} (R : X -> Y -> Prop) l1 l2 l :
  LIST_REL R (l1 ++ l2) l -> exists m1 m2, l = m1 ++ m2 /\ LIST_REL R l1 m1 /\ LIST_REL R l2 m2.
Proof.
  revert l; induction l1 as [|x l1 IH]; intros l H.
  - exists [], l. split; [reflexivity|split; [constructor|exact H]].
  - inversion H as [|? y ? l' Hxy Hl]; subst.
    destruct (IH _ Hl) as (m1 & m2 & -> & H1 & H2).
    exists (y :: m1), m2. split; [reflexivity|split; [constructor; assumption|exact H2]].
Qed.

Section Lengths.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_len_def" *)
Definition line_len (l : line a) : N :=
  match l with
  | Label _ _ l => l
  | Asm _ _ l => l
  | LabAsm _ _ _ l => l
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_length_add" *)
Theorem sec_length_add : forall (ls : list (line a)) n m, sec_length ls (n + m) = sec_length ls n + m.
Proof.
  induction ls as [|[k1 k2 l0|x1 x2 l0|x0 w0 b0 l0] ls IH]; intros n m; cbn [sec_length]; [reflexivity| | |];
    rewrite <- IH; f_equal; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_length_sum_line_len" *)
Theorem sec_length_sum_line_len : forall (ls : list (line a)) n,
  sec_length ls n = SUM (MAP line_len ls) + n.
Proof.
  induction ls as [|[k1 k2 l0|x1 x2 l0|x0 w0 b0 l0] ls IH]; intros n; cbn [sec_length MAP SUM line_len]; [lia| | |];
    rewrite IH; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_simp_def" *)
Fixpoint enc_lines_again_simp (labs : spt (spt N)) (ffis : list ffiname) (pos : N)
    (enc : asm.asm a -> list word8) (l : list (line a)) : list (line a) * bool :=
  match l with
  | [] => ([], true)
  | LabAsm a0 w bytes l :: xs =>
      let w1 := get_jump_offset a0 ffis labs pos in
      if decide (w = w1) then
        let '(rest, ok) := enc_lines_again_simp labs ffis (pos + l) enc xs in
        (LabAsm a0 w bytes l :: rest, ok)
      else
        let bs := enc (lab_inst w1 a0) in
        let l1 := MAX (LENGTH bs) l in
        let '(rest, ok) := enc_lines_again_simp labs ffis (pos + l1) enc xs in
        (LabAsm a0 w1 bs l1 :: rest, (l1 =? l) && ok)
  | Label k1 k2 l :: xs =>
      let '(rest, ok) := enc_lines_again_simp labs ffis (pos + l) enc xs in
      (Label k1 k2 l :: rest, ok)
  | Asm x1 x2 l :: xs =>
      let '(rest, ok) := enc_lines_again_simp labs ffis (pos + l) enc xs in
      (Asm x1 x2 l :: rest, ok)
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_simp_EQ" *)
Theorem enc_lines_again_simp_EQ : forall labs ffis pos enc (ls : list (line a)) acc b,
  let '(ls', flag) := enc_lines_again_simp labs ffis pos enc ls in
  enc_lines_again labs ffis pos enc ls (acc, b) =
    (REVERSE acc ++ ls', (sec_length ls' pos, b && flag)).
Proof.
  intros labs ffis pos enc ls. revert pos.
  induction ls as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos acc b.
  - cbn. rewrite app_nil_r, Bool.andb_true_r. reflexivity.
  - cbn [enc_lines_again_simp enc_lines_again].
    specialize (IH (pos + l) (Label k1 k2 l :: acc) b).
    destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok].
    rewrite IH. cbn [rev]. rewrite <- app_assoc. reflexivity.
  - cbn [enc_lines_again_simp enc_lines_again].
    specialize (IH (pos + l) (Asm x1 x2 l :: acc) b).
    destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok].
    rewrite IH. cbn [rev]. rewrite <- app_assoc. reflexivity.
  - cbn [enc_lines_again_simp enc_lines_again]. cbv zeta.
    destruct (decide (w = get_jump_offset x ffis labs pos)).
    + specialize (IH (pos + l) (LabAsm x w bytes l :: acc) b).
      destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok].
      rewrite IH. cbn [rev]. rewrite <- app_assoc. reflexivity.
    + set (l1 := MAX (LENGTH (enc (lab_inst (get_jump_offset x ffis labs pos) x))) l).
      specialize (IH (pos + l1)
        (LabAsm x (get_jump_offset x ffis labs pos)
           (enc (lab_inst (get_jump_offset x ffis labs pos) x)) l1 :: acc) (b && (l1 =? l))).
      destruct (enc_lines_again_simp labs ffis (pos + l1) enc xs) as [rest ok].
      rewrite IH. cbn [rev]. rewrite <- app_assoc. cbn [sec_length].
      f_equal. f_equal. rewrite Bool.andb_assoc. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_simp_len" *)
Theorem enc_lines_again_simp_len : forall labs ffis pos enc (lines : list (line a)) res,
  enc_lines_again_simp labs ffis pos enc lines = (res, true) ->
  MAP line_len res = MAP line_len lines.
Proof.
  intros labs ffis pos enc lines. revert pos.
  induction lines as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos res H;
    cbn [enc_lines_again_simp] in H.
  - injection H as <-. reflexivity.
  - destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok] eqn:E.
    injection H as <- ->. cbn. rewrite (IH _ _ E). reflexivity.
  - destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok] eqn:E.
    injection H as <- ->. cbn. rewrite (IH _ _ E). reflexivity.
  - cbv zeta in H. destruct (decide _).
    + destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok] eqn:E.
      injection H as <- ->. cbn. rewrite (IH _ _ E). reflexivity.
    + destruct (enc_lines_again_simp labs ffis _ enc xs) as [rest ok] eqn:E.
      injection H as <- Hok. apply Bool.andb_true_iff in Hok as [Hl ->].
      apply N.eqb_eq in Hl. cbn. rewrite Hl, (IH _ _ E). reflexivity.
Qed.

Lemma LENGTH_TAKE {X} n (l : list X) : n <= LENGTH l -> LENGTH (TAKE n l) = n.
Proof.
  intros H. rewrite TAKE_firstn, LENGTH_length, length_firstn. rewrite LENGTH_length in H. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "LENGTH_pad_bytes" *)
Theorem LENGTH_pad_bytes : forall (nop bytes : list word8) l,
  0 < LENGTH nop /\ LENGTH bytes <= l -> LENGTH (pad_bytes bytes l nop) = l.
Proof.
  intros nop bytes l [H1 H2]. unfold pad_bytes. cbv zeta.
  destruct (N.leb_spec l (LENGTH bytes)); [lia|].
  apply LENGTH_TAKE. rewrite LENGTH_app, LENGTH_FLAT_REPLICATE. nia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "section_labels_sec_length" *)
Theorem section_labels_sec_length : forall pos (lines : list (line a)) acc,
  FST (section_labels pos lines acc) = sec_length lines pos.
Proof.
  intros pos lines; revert pos; induction lines as [|[k1 k2 l0|x1 x2 l0|x0 w0 b0 l0] xs IH]; intros pos acc;
    cbn [section_labels sec_length]; [reflexivity| | |]; try apply IH.
  destruct (k2 =? 0); apply IH.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "section_labels_append" *)
Theorem section_labels_append : forall pos (l1 : list (line a)) labs l2,
  section_labels pos (l1 ++ l2) labs =
  section_labels (pos + SUM (MAP line_len l1)) l2 (SND (section_labels pos l1 labs)).
Proof.
  intros pos l1; revert pos; induction l1 as [|[k1 k2 l0|x1 x2 l0|x0 w0 b0 l0] xs IH]; intros pos labs l2;
    cbn [app section_labels MAP SUM line_len].
  - rewrite N.add_0_r. reflexivity.
  - destruct (k2 =? 0); rewrite IH, N.add_assoc; reflexivity.
  - rewrite IH, N.add_assoc; reflexivity.
  - rewrite IH, N.add_assoc; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_length_add_nop1" *)
Theorem line_length_add_nop1 : forall nop (ls : list (line a)),
  ~ EVERY is_Label ls ->
  SUM (MAP line_length (add_nop nop ls)) = SUM (MAP line_length ls) + LENGTH nop.
Proof.
  intros nop ls; induction ls as [|[k1 k2 l0|x1 x2 l0|x0 w0 b0 l0] xs IH]; intros H; cbn in H |- *;
    [exfalso; apply H; reflexivity| | |].
  - rewrite IH by exact H. lia.
  - rewrite LENGTH_app. lia.
  - rewrite LENGTH_app. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_length_add_nop" *)
Theorem line_length_add_nop : forall nop (ls : list (line a)),
  EVERY is_Label ls -> SUM (MAP line_length (add_nop nop ls)) = SUM (MAP line_length ls).
Proof.
  intros nop ls; induction ls as [|[k1 k2 l0|x1 x2 l0|x0 w0 b0 l0] xs IH]; intros H; cbn in H |- *; try discriminate;
    [reflexivity|]. rewrite IH by exact H. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_len_add_nop1" *)
Theorem line_len_add_nop1 : forall nop (ls : list (line a)),
  ~ EVERY is_Label ls -> SUM (MAP line_len (add_nop nop ls)) = SUM (MAP line_len ls) + 1.
Proof.
  intros nop ls; induction ls as [|[k1 k2 l0|x1 x2 l0|x0 w0 b0 l0] xs IH]; intros H; cbn in H |- *;
    [exfalso; apply H; reflexivity| | |].
  - rewrite IH by exact H. lia.
  - lia.
  - lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_len_add_nop" *)
Theorem line_len_add_nop : forall nop (ls : list (line a)),
  EVERY is_Label ls -> SUM (MAP line_len (add_nop nop ls)) = SUM (MAP line_len ls).
Proof.
  intros nop ls; induction ls as [|[k1 k2 l0|x1 x2 l0|x0 w0 b0 l0] xs IH]; intros H; cbn in H |- *; try discriminate;
    [reflexivity|]. rewrite IH by exact H. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "add_nop_append" *)
Theorem add_nop_append : forall nop (l1 l2 : list (line a)),
  add_nop nop (l1 ++ l2) = if EVERY is_Label l1 then l1 ++ add_nop nop l2 else add_nop nop l1 ++ l2.
Proof.
  intros nop l1 l2; induction l1 as [|[k1 k2 l0|x1 x2 l0|x0 w0 b0 l0] xs IH]; cbn; [reflexivity| | |]; [|reflexivity|reflexivity].
  rewrite IH. destruct (EVERY is_Label xs); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "EXISTS_not_Label_add_nop" *)
Theorem EXISTS_not_Label_add_nop : forall nop (acc : list (line a)),
  EXISTS (negb ∘ is_Label) (add_nop nop acc) = EXISTS (negb ∘ is_Label) acc.
Proof. intros nop acc; induction acc as [|[k1 k2 l0|x1 x2 l0|x0 w0 b0 l0] xs IH]; cbn; [reflexivity|exact IH|reflexivity|reflexivity]. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "EVERY_is_Label_add_nop_preserved" *)
Theorem EVERY_is_Label_add_nop_preserved : forall nop (acc : list (line a)),
  EVERY is_Label (add_nop nop acc) = EVERY is_Label acc.
Proof. intros nop acc; induction acc as [|[k1 k2 l0|x1 x2 l0|x0 w0 b0 l0] xs IH]; cbn; [reflexivity|exact IH|reflexivity|reflexivity]. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "EVERY_is_Label_add_nop" *)
Theorem EVERY_is_Label_add_nop : forall nop (ls : list (line a)),
  EVERY is_Label ls -> add_nop nop ls = ls.
Proof.
  intros nop ls; induction ls as [|[k1 k2 l0|x1 x2 l0|x0 w0 b0 l0] xs IH]; intros H; cbn in H |- *; try discriminate;
    [reflexivity|]. rewrite IH by exact H. reflexivity.
Qed.

Lemma lines_upd_lab_len_shape : forall (lines : list (line a)) pos acc,
  exists res, lines_upd_lab_len pos lines acc = (REVERSE acc ++ res, pos + SUM (MAP line_len res)).
Proof.
  induction lines as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos acc; cbn [lines_upd_lab_len].
  - exists []. rewrite app_nil_r. cbn. f_equal. lia.
  - destruct (IH (pos + (if EVEN pos then 0 else 1)) (Label k1 k2 (if EVEN pos then 0 else 1) :: acc))
      as [res E]. rewrite E. exists (Label k1 k2 (if EVEN pos then 0 else 1) :: res).
    cbn [rev]. rewrite <- app_assoc. cbn [app MAP SUM line_len]. f_equal. lia.
  - destruct (IH (pos + l) (Asm x1 x2 l :: acc)) as [res E]. rewrite E.
    exists (Asm x1 x2 l :: res). cbn [rev]. rewrite <- app_assoc. cbn. f_equal. lia.
  - destruct (IH (pos + l) (LabAsm x w bytes l :: acc)) as [res E]. rewrite E.
    exists (LabAsm x w bytes l :: res). cbn [rev]. rewrite <- app_assoc. cbn. f_equal. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "SND_lines_upd_lab_len" *)
Theorem SND_lines_upd_lab_len : forall pos (lines : list (line a)) acc,
  SND (lines_upd_lab_len pos lines acc) =
  pos + SUM (MAP line_len (FST (lines_upd_lab_len pos lines acc))) - SUM (MAP line_len acc).
Proof.
  intros pos lines acc. destruct (lines_upd_lab_len_shape lines pos acc) as [res E].
  rewrite E. cbn [FST SND]. rewrite map_app, SUM_app, map_rev, SUM_rev. lia.
Qed.

End Lengths.

(** ** [code_similar] preservation *)

Section Similar.
Context {a : N}.

Lemma line_similar_add_nop_refl nop (ls : list (line a)) : LIST_REL line_similar ls (add_nop nop ls).
Proof.
  induction ls as [|[k1 k2 l0|x1 x2 l0|x0 w0 b0 l0] xs IH]; cbn [add_nop]; constructor;
    try exact IH; try (apply LIST_REL_refl, line_similar_refl); cbn; auto.
Qed.

Lemma LIST_REL_line_similar_trans (l1 l2 l3 : list (line a)) :
  LIST_REL line_similar l1 l2 -> LIST_REL line_similar l2 l3 -> LIST_REL line_similar l1 l3.
Proof.
  apply LIST_REL_trans. intros x y z H1 H2. apply (line_similar_trans x y z). auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_add_nop" *)
Theorem line_similar_add_nop : forall (ls ls' : list (line a)) h,
  LIST_REL line_similar ls ls' -> LIST_REL line_similar ls (add_nop h ls').
Proof.
  intros ls ls' h H. eapply LIST_REL_line_similar_trans; [exact H|apply line_similar_add_nop_refl].
Qed.

Lemma pad_section_similar nop : forall (l2 aux : list (line a)),
  LIST_REL line_similar (REVERSE aux ++ l2) (pad_section nop l2 aux).
Proof.
  induction l2 as [|[k1 k2 len|x1 x2 len|y w bytes len] xs IH]; intros aux; cbn [pad_section].
  - rewrite app_nil_r. apply LIST_REL_refl, line_similar_refl.
  - eapply LIST_REL_line_similar_trans; [|apply IH]. cbn [rev]. rewrite <- app_assoc.
    apply LIST_REL_app; [|constructor; [cbn; auto|apply LIST_REL_refl, line_similar_refl]].
    apply LIST_REL_rev. destruct (len =? 0); [apply LIST_REL_refl, line_similar_refl|].
    apply line_similar_add_nop_refl.
  - eapply LIST_REL_line_similar_trans; [|apply IH]. cbn [rev]. rewrite <- app_assoc.
    apply LIST_REL_app; [apply LIST_REL_refl, line_similar_refl|].
    constructor; [cbn; auto|apply LIST_REL_refl, line_similar_refl].
  - eapply LIST_REL_line_similar_trans; [|apply IH]. cbn [rev]. rewrite <- app_assoc.
    apply LIST_REL_app; [apply LIST_REL_refl, line_similar_refl|].
    constructor; [cbn; auto|apply LIST_REL_refl, line_similar_refl].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_pad_section" *)
Theorem line_similar_pad_section : forall nop (l2 aux l1 : list (line a)),
  LIST_REL line_similar l1 (REVERSE aux ++ l2) ->
  LIST_REL line_similar l1 (pad_section nop l2 aux).
Proof.
  intros nop l2 aux l1 H. eapply LIST_REL_line_similar_trans; [exact H|apply pad_section_similar].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_pad_code" *)
Theorem code_similar_pad_code : forall nop (code1 code2 : list (sec a)),
  code_similar code1 code2 -> code_similar code1 (pad_code nop code2).
Proof.
  intros nop code1; induction code1 as [|[k1 l1] c1 IH]; intros [|[k2 l2] c2] H; cbn in H |- *;
    try contradiction; [exact Logic.I|].
  destruct H as (H1 & H2 & ->). split; [apply IH, H1|split; [|reflexivity]].
  apply line_similar_pad_section. exact H2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "LIST_REL_enc_line" *)
Theorem LIST_REL_enc_line : forall enc len (ls ls' : list (line a)),
  LIST_REL line_similar ls ls' <->
  LIST_REL line_similar (MAP (enc_line enc len) ls) ls'.
Proof.
  intros enc len ls; induction ls as [|x ls IH]; intros ls'; split; intros H.
  - exact H.
  - exact H.
  - inversion H as [|? y ? ys Hxy Hl]; subst. cbn [MAP map]. constructor; [|apply IH, Hl].
    destruct x, y; cbn in *; auto.
  - cbn [MAP map] in H. inversion H as [|? y ? ys Hxy Hl]; subst. constructor; [|apply IH, Hl].
    destruct x, y; cbn in *; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_enc_sec_list" *)
Theorem code_similar_enc_sec_list : forall (code1 code2 : list (sec a)) n,
  code_similar (enc_sec_list n code1) code2 <-> code_similar code1 code2.
Proof.
  intros code1; unfold enc_sec_list; cbv zeta.
  induction code1 as [|[k1 l1] c1 IH]; intros [|[k2 l2] c2] n; cbn; try tauto.
  rewrite IH, <- LIST_REL_enc_line. tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_IMP_similar" *)
Theorem enc_lines_again_IMP_similar : forall labs ffis pos enc (lines : list (line a)) acc ok
    lines' ok' curr,
  enc_lines_again labs ffis pos enc lines (acc, ok) = (lines', ok') ->
  LIST_REL line_similar curr (REVERSE acc) ->
  LIST_REL line_similar (curr ++ lines) lines'.
Proof.
  intros labs ffis pos enc lines. revert pos.
  induction lines as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos acc ok lines' ok' curr H Hc;
    cbn [enc_lines_again] in H.
  - injection H as <- _. rewrite app_nil_r. exact Hc.
  - replace (curr ++ Label k1 k2 l :: xs) with ((curr ++ [Label k1 k2 l]) ++ xs) by
      (rewrite <- app_assoc; reflexivity).
    apply (IH _ _ _ _ _ _ H). cbn [rev]. apply LIST_REL_app; [exact Hc|constructor; [cbn; auto|constructor]].
  - replace (curr ++ Asm x1 x2 l :: xs) with ((curr ++ [Asm x1 x2 l]) ++ xs) by
      (rewrite <- app_assoc; reflexivity).
    apply (IH _ _ _ _ _ _ H). cbn [rev]. apply LIST_REL_app; [exact Hc|constructor; [cbn; auto|constructor]].
  - replace (curr ++ LabAsm x w bytes l :: xs) with ((curr ++ [LabAsm x w bytes l]) ++ xs) by
      (rewrite <- app_assoc; reflexivity).
    cbv zeta in H. destruct (decide _); apply (IH _ _ _ _ _ _ H); cbn [rev];
      (apply LIST_REL_app; [exact Hc|constructor; [cbn; auto|constructor]]).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_secs_again_IMP_similar" *)
Theorem enc_secs_again_IMP_similar : forall pos labs ffis enc (code code1 : list (sec a)) ok,
  enc_secs_again pos labs ffis enc code = (code1, ok) -> code_similar code code1.
Proof.
  intros pos labs ffis enc code; revert pos.
  induction code as [|[k lines] rest IH]; intros pos code1 ok H; cbn [enc_secs_again] in H.
  - injection H as <- _. exact Logic.I.
  - destruct (enc_lines_again labs ffis pos enc lines ([], true)) as [lines1 [pos1 ok1]] eqn:E1.
    destruct (enc_secs_again pos1 labs ffis enc rest) as [rest1 ok2] eqn:E2.
    injection H as <- _. cbn. split; [exact (IH _ _ _ E2)|split; [|reflexivity]].
    exact (enc_lines_again_IMP_similar labs ffis pos enc lines [] true lines1 _ [] E1 (LIST_REL_nil _)).
Qed.

(** HOL's ML value [lines_upd_lab_len_AUX] (Galette helper, untagged). *)
Lemma lines_upd_lab_len_AUX : forall (l aux : list (line a)) pos,
  FST (lines_upd_lab_len pos l aux) = REVERSE aux ++ FST (lines_upd_lab_len pos l []).
Proof.
  induction l as [|[k1 k2 l0|x1 x2 l0|x0 w0 b0 l0] xs IH]; intros aux pos; cbn [lines_upd_lab_len].
  - cbn. rewrite app_nil_r. reflexivity.
  - rewrite IH, (IH [_]). cbn [rev app]. rewrite <- app_assoc. reflexivity.
  - rewrite IH, (IH [_]). cbn [rev app]. rewrite <- app_assoc. reflexivity.
  - rewrite IH, (IH [_]). cbn [rev app]. rewrite <- app_assoc. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_lines_upd_lab_len" *)
Theorem line_similar_lines_upd_lab_len : forall (l aux : list (line a)) pos l1,
  LIST_REL line_similar (FST (lines_upd_lab_len pos l [])) l1 <-> LIST_REL line_similar l l1.
Proof.
  intros l aux. clear aux.
  induction l as [|[k1 k2 l0|x1 x2 l0|x0 w0 b0 l0] xs IH]; intros pos l1; cbn [lines_upd_lab_len].
  - reflexivity.
  - rewrite lines_upd_lab_len_AUX. cbn [rev app].
    split; intros H; inversion H as [|? y ? ys Hxy Hl]; subst; constructor;
      [destruct y; cbn in *; tauto|exact (proj1 (IH _ _) Hl)|destruct y; cbn in *; tauto|exact (proj2 (IH _ _) Hl)].
  - rewrite lines_upd_lab_len_AUX. cbn [rev app].
    split; intros H; inversion H as [|? y ? ys Hxy Hl]; subst; constructor;
      [exact Hxy|exact (proj1 (IH _ _) Hl)|exact Hxy|exact (proj2 (IH _ _) Hl)].
  - rewrite lines_upd_lab_len_AUX. cbn [rev app].
    split; intros H; inversion H as [|? y ? ys Hxy Hl]; subst; constructor;
      [exact Hxy|exact (proj1 (IH _ _) Hl)|exact Hxy|exact (proj2 (IH _ _) Hl)].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_upd_lab_len" *)
Theorem code_similar_upd_lab_len : forall (code : list (sec a)) pos code1,
  code_similar (upd_lab_len pos code) code1 <-> code_similar code code1.
Proof.
  induction code as [|[k lines] rest IH]; intros pos code1; cbn [upd_lab_len]; [reflexivity|].
  destruct (lines_upd_lab_len pos lines []) as [lines1 pos1] eqn:E.
  destruct code1 as [|[k2 l2] c2]; cbn; [tauto|].
  rewrite IH. pose proof (line_similar_lines_upd_lab_len lines [] pos l2) as H.
  rewrite E in H. cbn [FST] in H. rewrite H. tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_upd_lab_len_similar" *)
Theorem lines_upd_lab_len_similar : forall pos (lines aux : list (line a)),
  LIST_REL line_similar (FST (lines_upd_lab_len pos lines aux)) (REVERSE aux ++ lines).
Proof.
  intros pos lines aux. rewrite lines_upd_lab_len_AUX.
  apply LIST_REL_app; [apply LIST_REL_refl, line_similar_refl|].
  apply (proj2 (line_similar_lines_upd_lab_len lines [] pos lines)).
  apply LIST_REL_refl, line_similar_refl.
Qed.

(** ** Implications of [code_similar] *)

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_MAP_Section_num" *)
Theorem code_similar_MAP_Section_num : forall c1 c2 : list (sec a),
  code_similar c1 c2 -> MAP Section_num c1 = MAP Section_num c2.
Proof.
  induction c1 as [|[k1 l1] c1 IH]; intros [|[k2 l2] c2] H; cbn in H |- *; try contradiction;
    [reflexivity|]. destruct H as (H1 & _ & ->). rewrite (IH _ H1). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_extract_labels" *)
Theorem code_similar_extract_labels : forall code1 code2 : list (sec a),
  code_similar code1 code2 ->
  MAP (extract_labels ∘ Section_lines) code1 = MAP (extract_labels ∘ Section_lines) code2.
Proof.
  induction code1 as [|[k1 l1] c1 IH]; intros [|[k2 l2] c2] H; cbn in H |- *; try contradiction;
    [reflexivity|]. destruct H as (H1 & H2 & ->). rewrite (IH _ H1). f_equal.
  clear -H2. induction H2 as [|x y xs ys Hxy Hl IHl]; [reflexivity|].
  destruct x, y; cbn in Hxy |- *; try contradiction; try exact IHl.
  destruct Hxy as [-> ->]. rewrite IHl. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_loc_to_pc" *)
Theorem code_similar_loc_to_pc : forall l1 l2 (c1 c2 : list (sec a)),
  code_similar c1 c2 -> loc_to_pc l1 l2 c1 = loc_to_pc l1 l2 c2.
Proof.
  intros l1 l2 c1. induction c1 as [|k xs IH|k x xs rest IH] using code_ind; intros c2 H.
  - destruct c2 as [|[]]; [reflexivity|contradiction].
  - destruct c2 as [|[k2 [|y2 ys2]] c2]; try contradiction.
    + destruct H as (H & _ & <-). rewrite !(proj2 loc_to_pc_def). rewrite (IH _ H). reflexivity.
    + destruct H as (_ & H & _). inversion H.
  - destruct c2 as [|[k2 [|y2 ys2]] c2]; try contradiction.
    + destruct H as (_ & H & _). inversion H.
    + destruct H as (Hr & Hl & <-). inversion Hl as [|? ? ? ? Hxy Hl']; subst.
      assert (Hs : code_similar (Section_ k xs :: rest) (Section_ k ys2 :: c2))
        by (split; [exact Hr|split; [exact Hl'|reflexivity]]).
      rewrite (proj2 loc_to_pc_def l1 l2 k (x :: xs) rest),
              (proj2 loc_to_pc_def l1 l2 k (y2 :: ys2) c2).
      assert (Ex : bool_decide (exists k0, x = Label l1 l2 k0) =
                   bool_decide (exists k0, y2 = Label l1 l2 k0)).
      { destruct x, y2; cbn in Hxy; try contradiction.
        - destruct Hxy as [-> ->]. apply Bool.eq_iff_eq_true. rewrite !bool_decide_spec.
          split; intros [k0 E]; injection E as -> ->; eauto.
        - apply Bool.eq_iff_eq_true. rewrite !bool_decide_spec.
          split; intros [k0 E]; discriminate.
        - apply Bool.eq_iff_eq_true. rewrite !bool_decide_spec.
          split; intros [k0 E]; discriminate. }
      rewrite Ex, (is_Label_similar _ _ Hxy), (IH _ Hs). reflexivity.
Qed.

End Similar.

(** ** [sec_label_ok] preservation *)

Section LabelsOk.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_sec_list_sec_labels_ok" *)
Theorem enc_sec_list_sec_labels_ok : forall enc (code : list (sec a)),
  EVERY sec_labels_ok code -> EVERY sec_labels_ok (enc_sec_list enc code).
Proof.
  intros enc code. unfold enc_sec_list; cbv zeta.
  induction code as [|[k lines] rest IH]; intros H; [reflexivity|].
  cbn in H |- *. apply Bool.andb_true_iff in H as [H1 H2].
  apply Bool.andb_true_iff. split; [|apply IH, H2].
  rewrite <- H1. clear. induction lines as [|[] xs IHl]; [reflexivity| | |];
    cbn [MAP map EVERY enc_line sec_label_ok]; rewrite IHl; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_sec_labels_ok" *)
Theorem enc_lines_again_sec_labels_ok : forall labs ffis pos enc (lines : list (line a)) acc ok
    res ok' k,
  enc_lines_again labs ffis pos enc lines (acc, ok) = (res, ok') /\
  EVERY (sec_label_ok k) acc /\ EVERY (sec_label_ok k) lines ->
  EVERY (sec_label_ok k) res.
Proof.
  intros labs ffis pos enc lines. revert pos.
  induction lines as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos acc ok res ok' k (H & Ha & Hl);
    cbn [enc_lines_again] in H; cbn [EVERY] in Hl.
  - injection H as <- _. rewrite EVERY_rev. exact Ha.
  - apply Bool.andb_true_iff in Hl as [Hx Hl].
    eapply IH; split; [exact H|split; [|exact Hl]]. cbn [EVERY]. rewrite Hx, Ha. reflexivity.
  - eapply IH; split; [exact H|split; [|exact Hl]]. cbn [EVERY]. rewrite Ha. reflexivity.
  - cbv zeta in H. destruct (decide _);
      (eapply IH; split; [exact H|split; [|exact Hl]]; cbn [EVERY]; rewrite Ha; reflexivity).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_secs_again_sec_labels_ok" *)
Theorem enc_secs_again_sec_labels_ok : forall pos ffis labs enc (ls res : list (sec a)) ok,
  enc_secs_again pos ffis labs enc ls = (res, ok) /\ EVERY sec_labels_ok ls ->
  EVERY sec_labels_ok res.
Proof.
  intros pos ffis labs enc ls; revert pos.
  induction ls as [|[k lines] rest IH]; intros pos res ok (H & Hok); cbn [enc_secs_again] in H.
  - injection H as <- _. reflexivity.
  - destruct (enc_lines_again ffis labs pos enc lines ([], true)) as [lines1 [pos1 ok1]] eqn:E1.
    destruct (enc_secs_again pos1 ffis labs enc rest) as [rest1 ok2] eqn:E2.
    injection H as <- _. cbn in Hok |- *. apply Bool.andb_true_iff in Hok as [H1 H2].
    apply Bool.andb_true_iff. split; [|exact (IH _ _ _ (conj E2 H2))].
    exact (enc_lines_again_sec_labels_ok _ _ _ _ _ [] true _ _ k (conj E1 (conj eq_refl H1))).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_upd_lab_len_sec_label_ok" *)
Theorem lines_upd_lab_len_sec_label_ok : forall pos (lines acc : list (line a)) k,
  EVERY (sec_label_ok k) lines /\ EVERY (sec_label_ok k) acc ->
  EVERY (sec_label_ok k) (FST (lines_upd_lab_len pos lines acc)).
Proof.
  intros pos lines; revert pos.
  induction lines as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos acc k (Hl & Ha);
    cbn [lines_upd_lab_len]; cbn [EVERY] in Hl.
  - cbn. rewrite EVERY_rev. exact Ha.
  - apply Bool.andb_true_iff in Hl as [Hx Hl]. apply IH. split; [exact Hl|].
    cbn [EVERY]. rewrite Ha, Bool.andb_true_r. exact Hx.
  - apply IH. split; [exact Hl|]. cbn [EVERY]. rewrite Ha. reflexivity.
  - apply IH. split; [exact Hl|]. cbn [EVERY]. rewrite Ha. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "upd_lab_len_sec_labels_ok" *)
Theorem upd_lab_len_sec_labels_ok : forall n (ls : list (sec a)),
  EVERY sec_labels_ok ls -> EVERY sec_labels_ok (upd_lab_len n ls).
Proof.
  intros n ls; revert n; induction ls as [|[k lines] rest IH]; intros n H; [reflexivity|].
  cbn [upd_lab_len]. cbn in H. apply Bool.andb_true_iff in H as [H1 H2].
  pose proof (lines_upd_lab_len_sec_label_ok n lines [] k (conj H1 eq_refl)) as Hl.
  destruct (lines_upd_lab_len n lines []) as [lines1 pos1].
  cbn. apply Bool.andb_true_iff. split; [exact Hl|apply IH, H2].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "add_nop_sec_label_ok" *)
Theorem add_nop_sec_label_ok : forall k nop (aux : list (line a)),
  EVERY (sec_label_ok k) aux -> EVERY (sec_label_ok k) (add_nop nop aux).
Proof.
  intros k nop aux; induction aux as [|[] xs IH]; intros H; cbn in H |- *; try exact H.
  apply Bool.andb_true_iff in H as [H1 H2]. rewrite H1. apply IH, H2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pad_section_sec_label_ok" *)
Theorem pad_section_sec_label_ok : forall nop (xs acc : list (line a)) k,
  EVERY (sec_label_ok k) xs /\ EVERY (sec_label_ok k) acc ->
  EVERY (sec_label_ok k) (pad_section nop xs acc).
Proof.
  intros nop xs; induction xs as [|[k1 k2 l|x1 x2 l|x w bytes l] ys IH]; intros acc k (Hl & Ha);
    cbn [pad_section]; cbn [EVERY] in Hl.
  - rewrite EVERY_rev. exact Ha.
  - apply Bool.andb_true_iff in Hl as [Hx Hl]. apply IH. split; [exact Hl|].
    cbn [EVERY]. apply Bool.andb_true_iff. split; [exact Hx|].
    destruct (l =? 0); [exact Ha|apply add_nop_sec_label_ok, Ha].
  - apply IH. split; [exact Hl|]. cbn [EVERY]. rewrite Ha. reflexivity.
  - apply IH. split; [exact Hl|]. cbn [EVERY]. rewrite Ha. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pad_code_sec_labels_ok" *)
Theorem pad_code_sec_labels_ok : forall nop (code : list (sec a)),
  EVERY sec_labels_ok code -> EVERY sec_labels_ok (pad_code nop code).
Proof.
  intros nop code; induction code as [|[k lines] rest IH]; intros H; [reflexivity|].
  cbn in H |- *. apply Bool.andb_true_iff in H as [H1 H2].
  apply Bool.andb_true_iff. split; [|apply IH, H2].
  apply pad_section_sec_label_ok. split; [exact H1|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_labels_ok_filter_skip" *)
Theorem sec_labels_ok_filter_skip : forall code : list (sec a),
  EVERY sec_labels_ok (filter_skip code) = EVERY sec_labels_ok code.
Proof.
  induction code as [|[k lines] rest IH]; [reflexivity|]. cbn [filter_skip EVERY sec_labels_ok].
  rewrite IH. f_equal. clear. induction lines as [|x xs IHl]; [reflexivity|].
  cbn [FILTER filter EVERY]. destruct (not_skip x) eqn:E; cbn [EVERY]; rewrite IHl; [reflexivity|].
  destruct x as [| [[]| |] | ]; cbn in E |- *; try discriminate. reflexivity.
Qed.

End LabelsOk.
