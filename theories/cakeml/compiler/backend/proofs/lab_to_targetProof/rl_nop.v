(** * CakeML [lab_to_targetProof]: syntactic properties of [remove_labels] (3)

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml] (HOL
    lines 4169-4989): the invariants [label_prefix_zero], [enc_with_nop],
    [lab_len_pos_ok] and [offset_ok] of the passes of [remove_labels].

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v].
    - [label_prefix_zero], [line_enc_with_nop], [lines_enc_with_nop],
      [all_enc_with_nop], [line_offset_ok], [lines_offset_ok] and
      [offset_ok] are [Prop]-valued; [sec_label_prefix_zero] (used under
      [EVERY]) decides [label_prefix_zero] classically ([⌜_⌝]);
      [line_lab_len_pos_ok], [lab_len_pos_ok] and [all_lab_len_pos_ok]
      are [bool]-valued.
    - Not ported: the ML bindings [line_enc_with_nop_ind],
      [all_enc_with_nop_ind], [all_lab_len_pos_ok_ind], [offset_ok_ind]. *)

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
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import
  basic bytes rl_syntax rl_invariants.
Open Scope N_scope.

(** ** Invariant: all initial labels have annotated length 0 *)

Section PrefixZero.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "label_prefix_zero_def" *)
Definition label_prefix_zero (ls : list (line a)) : Prop :=
  forall n, n < LENGTH ls /\ (forall m, m <= n -> is_Label (EL m ls)) ->
    forall m, m <= n -> line_len (EL m ls) = 0.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_label_prefix_zero_def" *)
Definition sec_label_prefix_zero (s : sec a) : bool :=
  match s with Section_ k ls => ⌜label_prefix_zero ls⌝ end.

Lemma EL_cons_SUC (x : line a) ls n : EL (N.succ n) (x :: ls) = EL n ls.
Proof. apply EL_SUC. Qed.

Lemma label_prefix_zero_nil : label_prefix_zero [].
Proof. intros n [Hn _]. cbn in Hn. lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "label_prefix_zero_cons" *)
Theorem label_prefix_zero_cons : forall l1 l2 len (ls : list (line a)) a0 b c d e f g,
  (label_prefix_zero (Label l1 l2 len :: ls) <-> len = 0 /\ label_prefix_zero ls) /\
  (label_prefix_zero (Asm a0 b c :: ls) <-> True) /\
  (label_prefix_zero (LabAsm d e f g :: ls) <-> True).
Proof.
  intros l1 l2 len ls a0 b c d e f g. split; [|split].
  - split.
    + intros H. split.
      * assert (Hlen : 0 < LENGTH (Label l1 l2 len :: ls)) by (cbn [LENGTH]; lia).
        assert (Hall : forall m, m <= 0 -> is_Label (EL m (Label l1 l2 len :: ls))).
        { intros m Hm. replace m with 0 by lia. reflexivity. }
        apply (H 0 (conj Hlen Hall) 0). lia.
      * intros n [Hn Hl] m Hm.
        assert (Hlen : N.succ n < LENGTH (Label l1 l2 len :: ls)) by (cbn [LENGTH]; lia).
        assert (Hall : forall m', m' <= N.succ n -> is_Label (EL m' (Label l1 l2 len :: ls))).
        { intros m' Hm'. destruct (N.eq_dec m' 0) as [->|Hm0]; [reflexivity|].
          replace m' with (N.succ (m' - 1)) by lia. rewrite EL_cons_SUC. apply Hl. lia. }
        rewrite <- (EL_cons_SUC (Label l1 l2 len)). apply (H (N.succ n) (conj Hlen Hall)). lia.
    + intros [-> H] n [Hn Hl] m Hm. destruct (N.eq_dec m 0) as [->|Hm0]; [reflexivity|].
      replace m with (N.succ (m - 1)) by lia. rewrite EL_cons_SUC.
      cbn [LENGTH] in Hn. destruct (N.eq_dec n 0) as [->|Hn0]; [lia|].
      apply (H (n - 1)); [split; [lia|]|lia].
      intros m' Hm'. specialize (Hl (N.succ m') ltac:(lia)). rewrite EL_cons_SUC in Hl. exact Hl.
  - split; [intros _; exact Logic.I|]. intros _ n [_ Hl] m Hm. specialize (Hl 0 ltac:(lia)).
    discriminate.
  - split; [intros _; exact Logic.I|]. intros _ n [_ Hl] m Hm. specialize (Hl 0 ltac:(lia)).
    discriminate.
Qed.

Lemma lpz_Label l1 l2 len (ls : list (line a)) :
  label_prefix_zero (Label l1 l2 len :: ls) <-> len = 0 /\ label_prefix_zero ls.
Proof.
  exact (proj1 (label_prefix_zero_cons l1 l2 len ls (Asmi (Inst asm.Skip)) [] 0
    labLang.Halt (n2w 0) [] 0)).
Qed.

Lemma lpz_not_Label (x : line a) ls : ~ is_Label x -> label_prefix_zero (x :: ls).
Proof.
  intros Hx. destruct x as [l1 l2 len|x1 x2 x3|x1 x2 x3 x4]; [exfalso; apply Hx; reflexivity| |].
  - apply (proj1 (proj2 (label_prefix_zero_cons 0 0 0 ls x1 x2 x3 labLang.Halt (n2w 0) [] 0))).
    exact Logic.I.
  - apply (proj2 (proj2 (label_prefix_zero_cons 0 0 0 ls (Asmi (Inst asm.Skip)) [] 0 x1 x2 x3 x4))).
    exact Logic.I.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "label_prefix_zero_append_suff" *)
Theorem label_prefix_zero_append_suff : forall l1 l2 : list (line a),
  label_prefix_zero l1 /\ label_prefix_zero l2 -> label_prefix_zero (l1 ++ l2).
Proof.
  induction l1 as [|[k1 k2 len|x1 x2 x3|x1 x2 x3 x4] xs IH]; intros l2 [H1 H2]; [exact H2| | |].
  - apply lpz_Label in H1 as [-> H1]. cbn [app]. apply lpz_Label. split; [reflexivity|].
    apply IH. split; assumption.
  - apply lpz_not_Label. discriminate.
  - apply lpz_not_Label. discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "label_prefix_zero_append_suff2" *)
Theorem label_prefix_zero_append_suff2 : forall l1 l2 : list (line a),
  label_prefix_zero l1 /\ EXISTS (negb ∘ is_Label) l1 -> label_prefix_zero (l1 ++ l2).
Proof.
  induction l1 as [|[k1 k2 len|x1 x2 x3|x1 x2 x3 x4] xs IH]; intros l2 [H1 H2];
    [discriminate| | |].
  - apply lpz_Label in H1 as [-> H1]. cbn [app]. apply lpz_Label. split; [reflexivity|].
    apply IH. split; [exact H1|exact H2].
  - apply lpz_not_Label. discriminate.
  - apply lpz_not_Label. discriminate.
Qed.

Lemma EXISTS_rev {X} (P : X -> bool) l : EXISTS P (REVERSE l) = EXISTS P l.
Proof.
  induction l as [|x l IH]; cbn [rev]; [reflexivity|].
  assert (forall l1 l2, EXISTS P (l1 ++ l2) = EXISTS P l1 || EXISTS P l2) as Hp.
  { intros l1 l2; induction l1 as [|y l1 IHl]; cbn; [reflexivity|]. rewrite IHl, Bool.orb_assoc. reflexivity. }
  rewrite Hp, IH. cbn. rewrite Bool.orb_false_r, Bool.orb_comm. reflexivity.
Qed.

Lemma EVERY_is_Label_EXISTS (l : list (line a)) :
  EVERY is_Label l = negb (EXISTS (negb ∘ is_Label) l).
Proof. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite IH. destruct (is_Label x); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_upd_lab_len_label_prefix_zero" *)
Theorem lines_upd_lab_len_label_prefix_zero : forall pos (ls acc : list (line a)),
  (EVERY is_Label acc -> EVEN pos) /\ label_prefix_zero (REVERSE acc) ->
  label_prefix_zero (FST (lines_upd_lab_len pos ls acc)).
Proof.
  intros pos ls; revert pos.
  induction ls as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos acc [H1 H2]; cbn [lines_upd_lab_len].
  - exact H2.
  - apply IH. split.
    + cbn [EVERY is_Label andb]. intros Ha. specialize (H1 Ha).
      rewrite H1, N.add_0_r. exact H1.
    + cbn [rev]. destruct (EVERY is_Label acc) eqn:Ea.
      * apply label_prefix_zero_append_suff. split; [exact H2|].
        apply lpz_Label. rewrite (H1 eq_refl). split; [reflexivity|apply label_prefix_zero_nil].
      * apply label_prefix_zero_append_suff2. split; [exact H2|].
        rewrite EXISTS_rev. rewrite EVERY_is_Label_EXISTS in Ea.
        destruct (EXISTS _ acc); [reflexivity|discriminate].
  - apply IH. split; [cbn; intros Hc; discriminate|]. cbn [rev].
    destruct (EVERY is_Label acc) eqn:Ea.
    + apply label_prefix_zero_append_suff. split; [exact H2|apply lpz_not_Label; discriminate].
    + apply label_prefix_zero_append_suff2. split; [exact H2|].
      rewrite EXISTS_rev. rewrite EVERY_is_Label_EXISTS in Ea.
      destruct (EXISTS _ acc); [reflexivity|discriminate].
  - apply IH. split; [cbn; intros Hc; discriminate|]. cbn [rev].
    destruct (EVERY is_Label acc) eqn:Ea.
    + apply label_prefix_zero_append_suff. split; [exact H2|apply lpz_not_Label; discriminate].
    + apply label_prefix_zero_append_suff2. split; [exact H2|].
      rewrite EXISTS_rev. rewrite EVERY_is_Label_EXISTS in Ea.
      destruct (EXISTS _ acc); [reflexivity|discriminate].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "upd_lab_len_label_prefix_zero" *)
Theorem upd_lab_len_label_prefix_zero : forall pos (ss : list (sec a)),
  EVEN pos /\ EVERY sec_ends_with_label ss -> EVERY sec_label_prefix_zero (upd_lab_len pos ss).
Proof.
  intros pos ss; revert pos. induction ss as [|[k lines] rest IH]; intros pos [Hp Hend]; [reflexivity|].
  cbn [upd_lab_len]. cbn [EVERY sec_ends_with_label] in Hend.
  apply Bool.andb_true_iff in Hend as [Hend0 Hend1].
  pose proof (lines_upd_lab_len_label_prefix_zero pos lines []
                (conj (fun _ => Hp) label_prefix_zero_nil)) as Hz.
  pose proof (SND_lines_upd_lab_len pos lines []) as Hs.
  pose proof (EVEN_sec_length_lines_upd_lab_len pos lines []) as Hev.
  destruct (lines_upd_lab_len pos lines []) as [lines1 pos1].
  cbn [FST SND MAP map SUM] in Hz, Hs, Hev.
  cbn [EVERY sec_label_prefix_zero]. apply Bool.andb_true_iff.
  split; [apply bool_decide_spec, Hz|].
  apply IH. split; [|exact Hend1].
  rewrite Hs. apply Bool.andb_true_iff in Hend0 as [Hnn Hlast].
  destruct lines as [|y ys]; [discriminate|].
  rewrite N.add_0_r in Hev. specialize (Hev (conj Hlast Hp)).
  rewrite N.sub_0_r, N.even_add, Hp, Hev. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_simp_label_prefix_zero" *)
Theorem enc_lines_again_simp_label_prefix_zero : forall labs ffis pos enc (ls res : list (line a)) ok,
  enc_lines_again_simp labs ffis pos enc ls = (res, ok) /\ label_prefix_zero ls ->
  label_prefix_zero res.
Proof.
  intros labs ffis pos enc ls; revert pos.
  induction ls as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos res ok (H & Hl);
    cbn [enc_lines_again_simp] in H.
  - injection H as <- _. exact label_prefix_zero_nil.
  - apply lpz_Label in Hl as [-> Hl].
    destruct (enc_lines_again_simp labs ffis (pos + 0) enc xs) as [rest ok1] eqn:E.
    injection H as <- _. apply lpz_Label. split; [reflexivity|]. exact (IH _ _ _ (conj E Hl)).
  - destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok1] eqn:E.
    injection H as <- _. apply lpz_not_Label. discriminate.
  - cbv zeta in H. destruct (decide _).
    + destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok1] eqn:E.
      injection H as <- _. apply lpz_not_Label. discriminate.
    + destruct (enc_lines_again_simp labs ffis _ enc xs) as [rest ok1] eqn:E.
      injection H as <- _. apply lpz_not_Label. discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_secs_again_label_prefix_zero" *)
Theorem enc_secs_again_label_prefix_zero : forall pos labs ffis enc (lines res : list (sec a)) ok,
  enc_secs_again pos labs ffis enc lines = (res, ok) /\ EVERY sec_label_prefix_zero lines ->
  EVERY sec_label_prefix_zero res.
Proof.
  intros pos labs ffis enc ls; revert pos.
  induction ls as [|[k lines] rest IH]; intros pos res ok (H & Hok); cbn [enc_secs_again] in H.
  - injection H as <- _. reflexivity.
  - destruct (enc_lines_again labs ffis pos enc lines ([], true)) as [lines1 [pos1 ok1]] eqn:E1.
    destruct (enc_secs_again pos1 labs ffis enc rest) as [rest1 ok2] eqn:E2.
    injection H as <- _. cbn in Hok |- *. apply Bool.andb_true_iff in Hok as [H1 H2].
    apply Bool.andb_true_iff. split; [|exact (IH _ _ _ (conj E2 H2))].
    destruct (enc_lines_again_simp_of _ _ _ _ _ _ _ _ E1) as [Es _].
    apply bool_decide_spec in H1. apply bool_decide_spec.
    exact (enc_lines_again_simp_label_prefix_zero _ _ _ _ _ _ _ (conj Es H1)).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_length_pad_section" *)
Theorem line_length_pad_section : forall (nop : list word8) (ls acc : list (line a)),
  LENGTH nop = 1 /\ EVERY label_one ls /\ EVERY line_length_leq ls /\
  SUM (MAP line_length acc) = SUM (MAP line_len acc) /\
  EVERY is_Label acc /\ label_prefix_zero ls ->
  SUM (MAP line_length (pad_section nop ls acc)) = SUM (MAP line_len ls) + SUM (MAP line_len acc).
Proof.
  intros nop ls; induction ls as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH];
    intros acc (Hn & H1 & H2 & H3 & H4 & H5); cbn [pad_section]; cbn [EVERY] in H1, H2.
  - rewrite !map_rev, !SUM_rev. cbn. lia.
  - apply lpz_Label in H5 as [-> H5]. rewrite N.eqb_refl. rewrite IH.
    + cbn [MAP map SUM line_len]. lia.
    + split; [exact Hn|split; [exact H1|split; [exact H2|split; [|split; [exact H4|exact H5]]]]].
      cbn [MAP map SUM line_length line_len N.eqb Pos.eqb]. lia.
  - apply Bool.andb_true_iff in H2 as [Hx H2]. cbn [line_length_leq] in Hx. apply N.leb_le in Hx.
    rewrite line_length_pad_section1.
    + cbn [MAP map SUM line_len]. lia.
    + split; [exact Hn|split; [exact H1|split; [exact H2|split]]].
      * cbn [EVERY is_Label andb]. discriminate.
      * cbn [MAP map SUM line_length line_len]. rewrite LENGTH_pad_bytes by lia. lia.
  - apply Bool.andb_true_iff in H2 as [Hx H2]. cbn [line_length_leq] in Hx. apply N.leb_le in Hx.
    rewrite line_length_pad_section1.
    + cbn [MAP map SUM line_len]. lia.
    + split; [exact Hn|split; [exact H1|split; [exact H2|split]]].
      * cbn [EVERY is_Label andb]. discriminate.
      * cbn [MAP map SUM line_length line_len]. rewrite LENGTH_pad_bytes by lia. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "label_zero_line_length_pad_section" *)
Theorem label_zero_line_length_pad_section : forall (nop : list word8) (ls acc : list (line a)),
  0 < LENGTH nop /\ EVERY label_zero ls /\ MAP line_length acc = MAP line_len acc /\
  EVERY line_length_leq ls ->
  MAP line_length (pad_section nop ls acc) = MAP line_len (REVERSE acc ++ ls).
Proof.
  intros nop ls; induction ls as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH];
    intros acc (Hn & H1 & H2 & H3); cbn [pad_section]; cbn [EVERY] in H1, H3.
  - rewrite app_nil_r, !map_rev, H2. reflexivity.
  - apply Bool.andb_true_iff in H1 as [Hl H1]. apply N.eqb_eq in Hl. subst l.
    rewrite N.eqb_refl. rewrite IH.
    + cbn [rev]. rewrite <- app_assoc, !map_app. reflexivity.
    + split; [exact Hn|split; [exact H1|split; [|exact H3]]]. cbn. rewrite H2. reflexivity.
  - apply Bool.andb_true_iff in H3 as [Hx H3]. cbn [line_length_leq] in Hx. apply N.leb_le in Hx.
    rewrite IH.
    + cbn [rev]. rewrite <- app_assoc, !map_app. reflexivity.
    + split; [exact Hn|split; [exact H1|split; [|exact H3]]].
      cbn [MAP map line_length line_len]. rewrite LENGTH_pad_bytes by lia. rewrite H2. reflexivity.
  - apply Bool.andb_true_iff in H3 as [Hx H3]. cbn [line_length_leq] in Hx. apply N.leb_le in Hx.
    rewrite IH.
    + cbn [rev]. rewrite <- app_assoc, !map_app. reflexivity.
    + split; [exact Hn|split; [exact H1|split; [|exact H3]]].
      cbn [MAP map line_length line_len]. rewrite LENGTH_pad_bytes by lia. rewrite H2. reflexivity.
Qed.

End PrefixZero.

(** ** Invariant: lines encoded with nops *)

Section EncWithNop.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_enc_with_nop_def" *)
Definition line_enc_with_nop (enc : asm.asm a -> list word8) (labs : spt (spt N))
    (ffis : list ffiname) (pos : N) (l : line a) : Prop :=
  match l with
  | Asm b bytes len => enc_with_nop enc (cbw_to_asm b) bytes /\ LENGTH bytes = len
  | LabAsm labLang.Halt _ bytes len =>
      enc_with_nop enc (asm.Jump (- n2w (pos + ffi_offset))%w) bytes /\ LENGTH bytes = len
  | LabAsm Install _ bytes len =>
      enc_with_nop enc (asm.Jump (- n2w (pos + 2 * ffi_offset))%w) bytes /\ LENGTH bytes = len
  | LabAsm (CallFFI s) _ bytes len =>
      enc_with_nop enc
        (asm.Jump (- n2w (pos + (get_ffi_index ffis (ExtCall s) + 3) * ffi_offset))%w) bytes /\
      LENGTH bytes = len
  | LabAsm (Jump l) _ bytes len =>
      enc_with_nop enc (asm.Jump (n2w (find_pos l labs) + - n2w pos)%w) bytes /\ LENGTH bytes = len
  | LabAsm (JumpCmp a0 b c l) _ bytes len =>
      enc_with_nop enc (asm.JumpCmp a0 b c (n2w (find_pos l labs) + - n2w pos)%w) bytes /\
      LENGTH bytes = len
  | LabAsm (LocValue k l) _ bytes len =>
      enc_with_nop enc (asm.Loc k (n2w (find_pos l labs) + - n2w pos)%w) bytes /\ LENGTH bytes = len
  | LabAsm _ _ bytes len => LENGTH bytes = len
  | Label _ _ len => len = 0
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_enc_with_nop_def" *)
Fixpoint lines_enc_with_nop (enc : asm.asm a -> list word8) (labs : spt (spt N))
    (ffis : list ffiname) (pos : N) (ls : list (line a)) : Prop :=
  match ls with
  | [] => True
  | l :: ls =>
      line_enc_with_nop enc labs ffis pos l /\
      lines_enc_with_nop enc labs ffis (pos + line_length l) ls
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_enc_with_nop_append" *)
Theorem lines_enc_with_nop_append : forall enc labs ffis pos (l1 l2 : list (line a)),
  lines_enc_with_nop enc labs ffis pos (l1 ++ l2) <->
  lines_enc_with_nop enc labs ffis pos l1 /\
  lines_enc_with_nop enc labs ffis (pos + SUM (MAP line_length l1)) l2.
Proof.
  intros enc labs ffis pos l1; revert pos; induction l1 as [|x l1 IH]; intros pos l2.
  - cbn. rewrite N.add_0_r. tauto.
  - cbn [app lines_enc_with_nop MAP map SUM]. rewrite IH, N.add_assoc. tauto.
Qed.

(** HOL [all_enc_with_nop]: recursion on the sections, then on the lines. *)
Fixpoint all_enc_with_nop (enc : asm.asm a -> list word8) (labs : spt (spt N))
    (ffis : list ffiname) (pos : N) (l : list (sec a)) : Prop :=
  match l with
  | [] => True
  | Section_ k ys :: xs =>
      (fix go (pos : N) (ys : list (line a)) : Prop :=
         match ys with
         | [] => all_enc_with_nop enc labs ffis pos xs
         | y :: ys => line_enc_with_nop enc labs ffis pos y /\ go (pos + line_length y) ys
         end) pos ys
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_with_nop_def" *)
Theorem all_enc_with_nop_def : forall enc labs ffis pos k xs y ys,
  (all_enc_with_nop enc labs ffis pos [] <-> True) /\
  (all_enc_with_nop enc labs ffis pos (Section_ k [] :: xs) <->
     all_enc_with_nop enc labs ffis pos xs) /\
  (all_enc_with_nop enc labs ffis pos (Section_ k (y :: ys) :: xs) <->
     line_enc_with_nop enc labs ffis pos y /\
     all_enc_with_nop enc labs ffis (pos + line_length y) (Section_ k ys :: xs)).
Proof. intros; repeat match goal with |- _ /\ _ => split end; split; intro Hx; exact Hx. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_with_nop_alt" *)
Theorem all_enc_with_nop_alt : forall enc labs ffis pos k (ls : list (line a)) ss,
  (all_enc_with_nop enc labs ffis pos [] <-> True) /\
  (all_enc_with_nop enc labs ffis pos (Section_ k ls :: ss) <->
     lines_enc_with_nop enc labs ffis pos ls /\
     all_enc_with_nop enc labs ffis (pos + SUM (MAP line_length ls)) ss).
Proof.
  intros enc labs ffis pos k ls ss. split; [tauto|]. revert pos.
  induction ls as [|y ys IH]; intros pos.
  - cbn. rewrite N.add_0_r. tauto.
  - change (all_enc_with_nop enc labs ffis pos (Section_ k (y :: ys) :: ss)) with
      (line_enc_with_nop enc labs ffis pos y /\
       all_enc_with_nop enc labs ffis (pos + line_length y) (Section_ k ys :: ss)).
    rewrite IH. cbn [lines_enc_with_nop MAP map SUM]. rewrite N.add_assoc. tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_enc_with_nop_length_ok" *)
Theorem line_enc_with_nop_length_ok : forall enc labs ffis pos (line : line a),
  line_enc_with_nop enc labs ffis pos line -> line_length_ok line.
Proof.
  intros enc labs ffis pos line H. unfold line_length_ok. apply N.eqb_eq.
  destruct line as [k1 k2 l|b bytes l|[] w bytes l]; cbn in H |- *; try tauto; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_enc_with_nop_length_ok" *)
Theorem lines_enc_with_nop_length_ok : forall enc labs ffis pos (ls : list (line a)),
  lines_enc_with_nop enc labs ffis pos ls -> EVERY line_length_ok ls.
Proof.
  intros enc labs ffis pos ls; revert pos; induction ls as [|l ls IH]; intros pos H; [reflexivity|].
  destruct H as [H1 H2]. cbn [EVERY]. apply Bool.andb_true_iff.
  split; [exact (line_enc_with_nop_length_ok _ _ _ _ _ H1)|exact (IH _ H2)].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_enc_with_nop_label_zero" *)
Theorem line_enc_with_nop_label_zero : forall enc labs ffis pos (line : line a),
  line_enc_with_nop enc labs ffis pos line -> label_zero line.
Proof.
  intros enc labs ffis pos [k1 k2 l|b bytes l|x w bytes l] H; [|reflexivity|reflexivity].
  cbn in H |- *. subst l. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_enc_with_nop_label_zero" *)
Theorem lines_enc_with_nop_label_zero : forall enc labs ffis pos (lines : list (line a)),
  lines_enc_with_nop enc labs ffis pos lines -> EVERY label_zero lines.
Proof.
  intros enc labs ffis pos ls; revert pos; induction ls as [|l ls IH]; intros pos H; [reflexivity|].
  destruct H as [H1 H2]. cbn [EVERY]. apply Bool.andb_true_iff.
  split; [exact (line_enc_with_nop_label_zero _ _ _ _ _ H1)|exact (IH _ H2)].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_with_nop_label_zero" *)
Theorem all_enc_with_nop_label_zero : forall enc labs ffis pos (ls : list (sec a)),
  all_enc_with_nop enc labs ffis pos ls -> EVERY sec_label_zero ls.
Proof.
  intros enc labs ffis pos ls; revert pos; induction ls as [|[k lines] ls IH]; intros pos H;
    [reflexivity|].
  apply (proj2 (all_enc_with_nop_alt enc labs ffis pos k lines ls)) in H as [H1 H2].
  cbn [EVERY sec_label_zero]. apply Bool.andb_true_iff.
  split; [exact (lines_enc_with_nop_label_zero _ _ _ _ _ H1)|exact (IH _ H2)].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_ok_line_enc_with_nop" *)
Theorem line_ok_line_enc_with_nop : forall (c : asm_config a) labs ffis pos (line : line a),
  line_ok c labs ffis pos line -> line_enc_with_nop (encode c) labs ffis pos line.
Proof.
  intros c labs ffis pos line H.
  destruct line as [k1 k2 l|b bytes l|x w bytes l]; cbn [line_ok line_enc_with_nop] in H |- *.
  - exact (proj2 H).
  - destruct H as (H1 & H2 & _). split; assumption.
  - destruct x as [[l1 l2]|cmp r ri [l1 l2]|v|r [l1 l2]|s| |]; cbn [get_label] in H;
      try (destruct (lab_lookup l1 l2 labs) as [t|] eqn:Et; [|contradiction];
           apply lab_lookup_IMP in Et; cbn [find_pos] in Et |- *; rewrite Et);
      try contradiction;
      destruct H as (H1 & H2 & _); (split; [|exact H2]);
      cbn [lab_inst] in H1; cbv zeta in H1;
      match goal with
      | H : enc_with_nop _ ?i1 _ |- enc_with_nop _ ?i2 _ => replace i2 with i1; [exact H|]
      end; f_equal; try f_equal;
      try match goal with |- context [get_ffi_index ?f ?e + 3] =>
            replace (get_ffi_index f e + 3) with (3 + get_ffi_index f e) by lia end;
      word_arith.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_ok_lines_enc_with_nop" *)
Theorem lines_ok_lines_enc_with_nop : forall (c : asm_config a) labs ffis pos (lines : list (line a)),
  lines_ok c labs ffis pos lines -> lines_enc_with_nop (encode c) labs ffis pos lines.
Proof.
  intros c labs ffis pos ls; revert pos; induction ls as [|l ls IH]; intros pos H; [exact Logic.I|].
  destruct H as [H1 H2]. split; [exact (line_ok_line_enc_with_nop _ _ _ _ _ H1)|exact (IH _ H2)].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_with_nop_pad_bytes_length" *)
Theorem enc_with_nop_pad_bytes_length : forall enc (x : asm.asm a),
  enc_with_nop enc x (pad_bytes (enc x) (LENGTH (enc x)) (enc (Inst asm.Skip))).
Proof.
  intros enc x. unfold pad_bytes. cbv zeta. rewrite N.leb_refl.
  apply enc_with_nop_thm. exists 0. rewrite app_nil_r. reflexivity.
Qed.

Lemma TAKE_app_ge {X} n (l1 l2 : list X) :
  LENGTH l1 <= n -> TAKE n (l1 ++ l2) = l1 ++ TAKE (n - LENGTH l1) l2.
Proof.
  intros H. rewrite !TAKE_firstn, firstn_app. rewrite LENGTH_length in *.
  rewrite firstn_all2 by lia. f_equal. f_equal. lia.
Qed.

Lemma TAKE_FLAT_REPLICATE (nop : list word8) k n :
  k <= n -> TAKE (k * LENGTH nop) (FLAT (REPLICATE n nop)) = FLAT (REPLICATE k nop).
Proof.
  revert n. induction k as [|k IH] using N.peano_ind; intros n Hk.
  - rewrite TAKE_firstn. reflexivity.
  - destruct n as [|n] using N.peano_ind; [lia|].
    rewrite !(proj2 (REPLICATE_thm _ nop)). cbn [FLAT concat].
    rewrite TAKE_app_ge by nia.
    replace (N.succ k * LENGTH nop - LENGTH nop) with (k * LENGTH nop) by nia.
    rewrite IH by lia. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_with_nop_pad_bytes" *)
Theorem enc_with_nop_pad_bytes : forall enc (x : asm.asm a) nop len,
  nop = enc (Inst asm.Skip) /\ LENGTH (enc x) <= len /\
  LENGTH (enc x) mod LENGTH nop = 0 /\ len mod LENGTH nop = 0 /\ 0 < LENGTH nop ->
  enc_with_nop enc x (pad_bytes (enc x) len nop).
Proof.
  intros enc x nop len (Hn & H1 & H2 & H3 & H4). apply enc_with_nop_thm. unfold pad_bytes. cbv zeta.
  destruct (N.leb_spec len (LENGTH (enc x))).
  - exists 0. rewrite app_nil_r. reflexivity.
  - rewrite <- Hn. set (L := LENGTH nop) in *.
    pose proof (N.div_mod (LENGTH (enc x)) L ltac:(lia)) as D1.
    pose proof (N.div_mod len L ltac:(lia)) as D2. rewrite H2, N.add_0_r in D1. rewrite H3, N.add_0_r in D2.
    exists (len / L - LENGTH (enc x) / L).
    rewrite TAKE_app_ge by lia. f_equal.
    replace (len - LENGTH (enc x)) with ((len / L - LENGTH (enc x) / L) * L) by nia.
    apply TAKE_FLAT_REPLICATE. nia.
Qed.

End EncWithNop.

Section PadNop.
Context {a : N}.

Lemma FLAT_REPLICATE_comm (nop : list word8) n :
  nop ++ FLAT (REPLICATE n nop) = FLAT (REPLICATE n nop) ++ nop.
Proof.
  induction n as [|n IH] using N.peano_ind.
  - rewrite (proj1 (REPLICATE_thm 0 nop)). cbn [FLAT concat]. rewrite app_nil_r. reflexivity.
  - rewrite (proj2 (REPLICATE_thm n nop)). cbn [FLAT concat]. rewrite <- app_assoc. f_equal. exact IH.
Qed.

Lemma FLAT_REPLICATE_snoc (nop : list word8) n :
  FLAT (REPLICATE (N.succ n) nop) = FLAT (REPLICATE n nop) ++ nop.
Proof. rewrite (proj2 (REPLICATE_thm n nop)). cbn [FLAT concat]. apply FLAT_REPLICATE_comm. Qed.

Lemma enc_with_nop_snoc (enc : asm.asm a -> list word8) (i : asm.asm a) bytes :
  enc_with_nop enc i bytes -> enc_with_nop enc i (bytes ++ enc (Inst asm.Skip)).
Proof.
  intros H. apply enc_with_nop_thm in H as [n ->]. apply enc_with_nop_thm. exists (N.succ n).
  rewrite FLAT_REPLICATE_snoc, app_assoc. reflexivity.
Qed.

Lemma line_enc_with_nop_pos enc labs ffis pos pos' (x : line a) :
  pos = pos' -> line_enc_with_nop enc labs ffis pos x -> line_enc_with_nop enc labs ffis pos' x.
Proof. intros ->; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_enc_with_nop_add_nop" *)
Theorem lines_enc_with_nop_add_nop : forall enc labs ffis pos (ls : list (line a)),
  LENGTH (enc (Inst asm.Skip)) = 1 /\ lines_enc_with_nop enc labs ffis pos (REVERSE ls) ->
  lines_enc_with_nop enc labs ffis pos (REVERSE (add_nop (enc (Inst asm.Skip)) ls)).
Proof.
  intros enc labs ffis pos ls. induction ls as [|x ls IH]; intros [Hn H]; [exact H|].
  cbn [rev] in H. apply lines_enc_with_nop_append in H as [H1 [H2 _]].
  destruct x as [k1 k2 l|b bytes l|y w bytes l]; cbn [add_nop rev].
  - apply lines_enc_with_nop_append. split; [apply IH; split; assumption|].
    split; [exact H2|exact Logic.I].
  - apply lines_enc_with_nop_append. split; [exact H1|]. split; [|exact Logic.I].
    destruct H2 as [He Hl]. split; [apply enc_with_nop_snoc, He|].
    rewrite LENGTH_app, Hn, Hl. reflexivity.
  - apply lines_enc_with_nop_append. split; [exact H1|]. split; [|exact Logic.I].
    destruct y as [l0|c r ri l0|l0|r l0|s| |]; cbn [line_enc_with_nop] in H2 |- *;
      try (destruct H2 as [He Hl]; split; [apply enc_with_nop_snoc, He|rewrite LENGTH_app, Hn, Hl; reflexivity]).
    rewrite LENGTH_app, Hn, H2. reflexivity.
Qed.

Lemma lines_enc_with_nop_SUM enc labs ffis pos (ls : list (line a)) :
  lines_enc_with_nop enc labs ffis pos ls -> SUM (MAP line_length ls) = SUM (MAP line_len ls).
Proof.
  intros H. apply lines_enc_with_nop_length_ok in H.
  pose proof (sec_length_sum_line_length ls 0 H) as E1.
  pose proof (sec_length_sum_line_len ls 0) as E2. lia.
Qed.

Lemma line_encd_pad_enc_with_nop enc labs ffis pos (y : asm_with_lab a) w bytes len nop :
  nop = enc (Inst asm.Skip) -> 0 < LENGTH nop ->
  line_encd enc labs ffis pos (LabAsm y w bytes len) ->
  LENGTH bytes mod LENGTH nop = 0 -> len mod LENGTH nop = 0 ->
  line_enc_with_nop enc labs ffis pos (LabAsm y w (pad_bytes bytes len nop) len).
Proof.
  intros Hn Hp H A1 A2.
  destruct y as [l0|c r ri l0|l0|r l0|s| |]; cbn [line_encd line_enc_with_nop] in H |- *;
    destruct H as [<- Hle];
    first [ (split; [|apply LENGTH_pad_bytes; split; lia]);
            apply enc_with_nop_pad_bytes;
            (split; [exact Hn|split; [exact Hle|split; [exact A1|split; [exact A2|exact Hp]]]])
          | apply LENGTH_pad_bytes; split; lia ].
Qed.

(** The [LENGTH nop = 1] cases of HOL's [lines_enc_with_nop_pad_section1]
    and [lines_enc_with_nop_pad_section] (Galette helper). *)
Lemma lines_enc_with_nop_pad_section_gen enc labs ffis nop : forall (code aux : list (line a)) pos,
  nop = enc (Inst asm.Skip) /\ LENGTH nop = 1 /\
  lines_encd enc labs ffis (pos + SUM (MAP line_len aux)) code /\
  lines_enc_with_nop enc labs ffis pos (REVERSE aux) /\
  EVERY label_one code /\ (EVERY is_Label aux -> label_prefix_zero code) ->
  lines_enc_with_nop enc labs ffis pos (pad_section nop code aux).
Proof.
  induction code as [|[k1 k2 l|x1 x2 l|y w bytes l] xs IH]; intros aux pos (Hn & H1 & H2 & H3 & H4 & H5);
    cbn [pad_section].
  - exact H3.
  - cbn [EVERY] in H4. apply Bool.andb_true_iff in H4 as [Hx H4]. cbn [label_one] in Hx.
    apply N.leb_le in Hx. destruct H2 as [_ H2]. cbn [line_len] in H2.
    destruct (N.eqb_spec l 0) as [->|Hl0].
    + apply IH. split; [exact Hn|split; [exact H1|split; [|split; [|split; [exact H4|]]]]].
      * cbn [MAP map SUM line_len]. rewrite N.add_0_l. rewrite N.add_0_r in H2. exact H2.
      * cbn [rev]. apply lines_enc_with_nop_append. split; [exact H3|split; [reflexivity|exact Logic.I]].
      * intros He. cbn [EVERY is_Label andb] in He. specialize (H5 He). apply lpz_Label in H5. apply H5.
    + assert (Hl1 : l = 1) by lia. subst l.
      assert (Hna : ~ EVERY is_Label aux).
      { intros He. specialize (H5 He). apply lpz_Label in H5 as [Hc _]. discriminate. }
      apply IH. split; [exact Hn|split; [exact H1|split; [|split; [|split; [exact H4|]]]]].
      * cbn [MAP map SUM line_len]. rewrite N.add_0_l, line_len_add_nop1 by exact Hna.
        rewrite N.add_assoc. exact H2.
      * cbn [rev]. apply lines_enc_with_nop_append. split; [|split; [reflexivity|exact Logic.I]].
        rewrite Hn. apply lines_enc_with_nop_add_nop. split; [rewrite <- Hn; exact H1|exact H3].
      * intros He. cbn [EVERY is_Label andb] in He. rewrite EVERY_is_Label_add_nop_preserved in He.
        contradiction.
  - destruct H2 as [Hx H2]. cbn [line_encd line_len] in Hx, H2. destruct Hx as [Hb Hlen].
    apply IH. split; [exact Hn|split; [exact H1|split; [|split; [|split; [exact H4|]]]]].
    + cbn [MAP map SUM line_len].
      replace (pos + (l + SUM (MAP line_len aux))) with (pos + SUM (MAP line_len aux) + l) by lia.
      exact H2.
    + cbn [rev]. apply lines_enc_with_nop_append. split; [exact H3|split; [|exact Logic.I]].
      cbn [line_enc_with_nop]. subst x2 l. split.
      * rewrite Hn. apply enc_with_nop_pad_bytes_length.
      * apply LENGTH_pad_bytes. lia.
    + cbn. intros Hc; discriminate.
  - destruct H2 as [Hx H2]. cbn [line_len] in H2.
    apply IH. split; [exact Hn|split; [exact H1|split; [|split; [|split; [exact H4|]]]]].
    + cbn [MAP map SUM line_len].
      replace (pos + (l + SUM (MAP line_len aux))) with (pos + SUM (MAP line_len aux) + l) by lia.
      exact H2.
    + cbn [rev]. apply lines_enc_with_nop_append. split; [exact H3|split; [|exact Logic.I]].
      rewrite (lines_enc_with_nop_SUM _ _ _ _ _ H3), map_rev, SUM_rev.
      apply line_encd_pad_enc_with_nop; [exact Hn|lia|exact Hx| |]; rewrite H1; apply N.mod_1_r.
    + cbn. intros Hc; discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_enc_with_nop_pad_section1" *)
Theorem lines_enc_with_nop_pad_section1 : forall enc labs ffis nop (code aux : list (line a)) pos,
  nop = enc (Inst asm.Skip) /\ LENGTH nop = 1 /\
  lines_encd enc labs ffis (pos + SUM (MAP line_len aux)) code /\
  lines_enc_with_nop enc labs ffis pos (REVERSE aux) /\
  ~ EVERY is_Label aux /\ EVERY label_one code ->
  lines_enc_with_nop enc labs ffis pos (pad_section nop code aux).
Proof.
  intros enc labs ffis nop code aux pos (H1 & H2 & H3 & H4 & H5 & H6).
  apply lines_enc_with_nop_pad_section_gen.
  repeat (split; [assumption|]). intros He; contradiction.
Qed.

(** The general case of HOL's [lines_enc_with_nop_pad_section01] and
    [lines_enc_with_nop_pad_section0] (Galette helper). *)
Lemma lines_enc_with_nop_pad_section0_gen enc labs ffis nop : forall (code aux : list (line a)) pos,
  nop = enc (Inst asm.Skip) /\ 0 < LENGTH nop /\
  EVERY (line_aligned (LENGTH nop)) code /\
  lines_encd enc labs ffis (pos + SUM (MAP line_len aux)) code /\
  lines_enc_with_nop enc labs ffis pos (REVERSE aux) /\
  EVERY label_zero code ->
  lines_enc_with_nop enc labs ffis pos (pad_section nop code aux).
Proof.
  induction code as [|[k1 k2 l|x1 x2 l|y w bytes l] xs IH]; intros aux pos (Hn & H1 & Hal & H2 & H3 & H4);
    cbn [pad_section]; cbn [EVERY] in Hal, H4.
  - exact H3.
  - apply Bool.andb_true_iff in H4 as [Hx H4]. cbn [label_zero] in Hx. apply N.eqb_eq in Hx. subst l.
    apply Bool.andb_true_iff in Hal as [_ Hal].
    destruct H2 as [_ H2]. cbn [line_len] in H2. rewrite N.eqb_refl.
    apply IH. split; [exact Hn|split; [exact H1|split; [exact Hal|split; [|split; [|exact H4]]]]].
    + cbn [MAP map SUM line_len]. rewrite N.add_0_l. rewrite N.add_0_r in H2. exact H2.
    + cbn [rev]. apply lines_enc_with_nop_append. split; [exact H3|split; [reflexivity|exact Logic.I]].
  - apply Bool.andb_true_iff in Hal as [_ Hal].
    destruct H2 as [Hx H2]. cbn [line_encd line_len] in Hx, H2. destruct Hx as [Hb Hlen].
    apply IH. split; [exact Hn|split; [exact H1|split; [exact Hal|split; [|split; [|exact H4]]]]].
    + cbn [MAP map SUM line_len].
      replace (pos + (l + SUM (MAP line_len aux))) with (pos + SUM (MAP line_len aux) + l) by lia.
      exact H2.
    + cbn [rev]. apply lines_enc_with_nop_append. split; [exact H3|split; [|exact Logic.I]].
      cbn [line_enc_with_nop]. subst x2 l. split.
      * rewrite Hn. apply enc_with_nop_pad_bytes_length.
      * apply LENGTH_pad_bytes. lia.
  - apply Bool.andb_true_iff in Hal as [Hax Hal].
    destruct H2 as [Hx H2]. cbn [line_len] in H2.
    apply IH. split; [exact Hn|split; [exact H1|split; [exact Hal|split; [|split; [|exact H4]]]]].
    + cbn [MAP map SUM line_len].
      replace (pos + (l + SUM (MAP line_len aux))) with (pos + SUM (MAP line_len aux) + l) by lia.
      exact H2.
    + cbn [rev]. apply lines_enc_with_nop_append. split; [exact H3|split; [|exact Logic.I]].
      rewrite (lines_enc_with_nop_SUM _ _ _ _ _ H3), map_rev, SUM_rev.
      unfold line_aligned in Hax. cbn [line_len line_length] in Hax.
      apply Bool.andb_true_iff in Hax as [A1 A2]. apply N.eqb_eq in A1, A2.
      apply line_encd_pad_enc_with_nop; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_enc_with_nop_pad_section01" *)
Theorem lines_enc_with_nop_pad_section01 : forall enc labs ffis nop (code aux : list (line a)) pos,
  nop = enc (Inst asm.Skip) /\ 0 < LENGTH nop /\
  EVERY (line_aligned (LENGTH nop)) code /\
  lines_encd enc labs ffis (pos + SUM (MAP line_len aux)) code /\
  lines_enc_with_nop enc labs ffis pos (REVERSE aux) /\
  ~ EVERY is_Label aux /\ EVERY label_zero code ->
  lines_enc_with_nop enc labs ffis pos (pad_section nop code aux).
Proof.
  intros enc labs ffis nop code aux pos (H1 & H2 & H3 & H4 & H5 & _ & H7).
  apply lines_enc_with_nop_pad_section0_gen. repeat (split; [assumption|]). assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_enc_with_nop_pad_section0" *)
Theorem lines_enc_with_nop_pad_section0 : forall enc labs ffis nop (code aux : list (line a)) pos,
  nop = enc (Inst asm.Skip) /\ 0 < LENGTH nop /\
  EVERY (line_aligned (LENGTH nop)) code /\
  lines_encd enc labs ffis (pos + SUM (MAP line_len aux)) code /\
  lines_enc_with_nop enc labs ffis pos (REVERSE aux) /\
  EVERY is_Label aux /\ EVERY label_zero code ->
  lines_enc_with_nop enc labs ffis pos (pad_section nop code aux).
Proof.
  intros enc labs ffis nop code aux pos (H1 & H2 & H3 & H4 & H5 & _ & H7).
  apply lines_enc_with_nop_pad_section0_gen. repeat (split; [assumption|]). assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_enc_with_nop_pad_section" *)
Theorem lines_enc_with_nop_pad_section : forall enc labs ffis nop (code aux : list (line a)) pos,
  nop = enc (Inst asm.Skip) /\ LENGTH nop = 1 /\
  lines_encd enc labs ffis (pos + SUM (MAP line_len aux)) code /\
  lines_enc_with_nop enc labs ffis pos (REVERSE aux) /\
  EVERY is_Label aux /\ EVERY label_one code /\ label_prefix_zero code ->
  lines_enc_with_nop enc labs ffis pos (pad_section nop code aux).
Proof.
  intros enc labs ffis nop code aux pos (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  apply lines_enc_with_nop_pad_section_gen. repeat (split; [assumption|]). intros _; exact H7.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_with_nop_pad_code" *)
Theorem all_enc_with_nop_pad_code : forall enc labs ffis nop (code : list (sec a)) pos,
  0 < LENGTH nop /\ nop = enc (Inst asm.Skip) /\
  (LENGTH nop <> 1 -> EVERY (sec_aligned (LENGTH nop)) code /\ EVERY sec_label_zero code) /\
  EVERY sec_label_one code /\ EVERY sec_length_leq code /\
  EVERY sec_label_prefix_zero code /\ all_encd enc labs ffis pos code ->
  all_enc_with_nop enc labs ffis pos (pad_code nop code).
Proof.
  intros enc labs ffis nop code. induction code as [|[k xs] rest IH];
    intros pos (H1 & H2 & H3 & H4 & H5 & H6 & H7); [exact Logic.I|].
  cbn [pad_code]. apply (proj2 (all_enc_with_nop_alt enc labs ffis pos k _ _)).
  cbn [EVERY sec_label_one sec_length_leq sec_label_prefix_zero] in H4, H5, H6.
  apply Bool.andb_true_iff in H4 as [H4a H4b]. apply Bool.andb_true_iff in H5 as [H5a H5b].
  apply Bool.andb_true_iff in H6 as [H6a H6b]. apply bool_decide_spec in H6a.
  destruct H7 as [H7a H7b].
  assert (E1 : lines_encd enc labs ffis (pos + SUM (MAP line_len ([] : list (line a)))) xs)
    by (cbn [MAP map SUM]; rewrite N.add_0_r; exact H7a).
  assert (E2 : lines_enc_with_nop enc labs ffis pos (REVERSE ([] : list (line a)))) by exact Logic.I.
  destruct (N.eq_dec (LENGTH nop) 1) as [Hn1|Hn1].
  - split.
    + exact (lines_enc_with_nop_pad_section enc labs ffis nop xs [] pos
               (conj H2 (conj Hn1 (conj E1 (conj E2 (conj eq_refl (conj H4a H6a))))))).
    + rewrite (line_length_pad_section nop xs []
                 (conj Hn1 (conj H4a (conj H5a (conj eq_refl (conj eq_refl H6a)))))).
      cbn [MAP map SUM]. rewrite N.add_0_r. apply IH.
      refine (conj H1 (conj H2 (conj _ (conj H4b (conj H5b (conj H6b H7b)))))).
      intros Hc. destruct (H3 Hc) as [A B]. cbn in A, B.
      apply Bool.andb_true_iff in A as [_ A]. apply Bool.andb_true_iff in B as [_ B]. auto.
  - destruct (H3 Hn1) as [A B]. cbn [EVERY sec_aligned sec_label_zero] in A, B.
    apply Bool.andb_true_iff in A as [A1 A2]. apply Bool.andb_true_iff in B as [B1 B2].
    split.
    + exact (lines_enc_with_nop_pad_section0 enc labs ffis nop xs [] pos
               (conj H2 (conj H1 (conj A1 (conj E1 (conj E2 (conj eq_refl B1))))))).
    + rewrite (label_zero_line_length_pad_section nop xs []
                 (conj H1 (conj B1 (conj eq_refl H5a)))).
      cbn [rev app].

      apply IH. refine (conj H1 (conj H2 (conj _ (conj H4b (conj H5b (conj H6b H7b)))))).
      intros _. split; assumption.
Qed.

End PadNop.

(** ** Invariant: label annotations record the alignment *)

Section LabLenPos.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_lab_len_pos_ok_def" *)
Definition line_lab_len_pos_ok (pos : N) (l : line a) : bool :=
  match l with
  | Label _ _ l => if EVEN pos then l =? 0 else l =? 1
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lab_len_pos_ok_def" *)
Fixpoint lab_len_pos_ok (pos : N) (ls : list (line a)) : bool :=
  match ls with
  | [] => true
  | l :: ls => line_lab_len_pos_ok pos l && lab_len_pos_ok (pos + line_len l) ls
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lab_len_pos_ok_append" *)
Theorem lab_len_pos_ok_append : forall (l1 : list (line a)) pos l2,
  lab_len_pos_ok pos (l1 ++ l2) =
  lab_len_pos_ok pos l1 && lab_len_pos_ok (pos + SUM (MAP line_len l1)) l2.
Proof.
  induction l1 as [|x l1 IH]; intros pos l2; cbn [app lab_len_pos_ok MAP map SUM].
  - rewrite N.add_0_r. reflexivity.
  - rewrite IH, N.add_assoc, Bool.andb_assoc. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_lab_len_pos_ok_def" *)
Fixpoint all_lab_len_pos_ok (pos : N) (ss : list (sec a)) : bool :=
  match ss with
  | [] => true
  | Section_ k ls :: ss => lab_len_pos_ok pos ls && all_lab_len_pos_ok (pos + sec_length ls 0) ss
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_upd_lab_len_pos_ok" *)
Theorem lines_upd_lab_len_pos_ok : forall pos (lines : list (line a)),
  lab_len_pos_ok pos (FST (lines_upd_lab_len pos lines [])).
Proof.
  intros pos lines; revert pos. induction lines as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos;
    [reflexivity| | |]; cbn [lines_upd_lab_len]; rewrite lines_upd_lab_len_AUX; cbn [rev app lab_len_pos_ok];
    rewrite IH, Bool.andb_true_r; [|reflexivity|reflexivity].
  cbn [line_lab_len_pos_ok]. destruct (EVEN pos); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "upd_lab_len_pos_ok" *)
Theorem upd_lab_len_pos_ok : forall pos (code : list (sec a)),
  all_lab_len_pos_ok pos (upd_lab_len pos code).
Proof.
  intros pos code; revert pos. induction code as [|[k lines] rest IH]; intros pos; [reflexivity|].
  cbn [upd_lab_len].
  pose proof (SND_lines_upd_lab_len pos lines []) as Hs.
  pose proof (lines_upd_lab_len_pos_ok pos lines) as Hp.
  destruct (lines_upd_lab_len pos lines []) as [lines1 pos1].
  cbn [FST SND MAP map SUM] in Hs, Hp. cbn [all_lab_len_pos_ok]. rewrite Hp.
  rewrite sec_length_sum_line_len, N.add_0_r. replace (pos + SUM (MAP line_len lines1)) with pos1 by lia.
  apply IH.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_simp_pos_ok" *)
Theorem enc_lines_again_simp_pos_ok : forall labs ffis pos enc (lines res : list (line a)),
  enc_lines_again_simp labs ffis pos enc lines = (res, true) /\ lab_len_pos_ok pos lines ->
  lab_len_pos_ok pos res.
Proof.
  intros labs ffis pos enc lines; revert pos.
  induction lines as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos res (H & Hl);
    cbn [enc_lines_again_simp] in H; cbn [lab_len_pos_ok] in Hl; apply Bool.andb_true_iff in Hl as [Hx Hl] || idtac.
  - injection H as <-. reflexivity.
  - destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok] eqn:E.
    injection H as <- ->. cbn [lab_len_pos_ok]. rewrite Hx. exact (IH _ _ (conj E Hl)).
  - destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok] eqn:E.
    injection H as <- ->. exact (IH _ _ (conj E Hl)).
  - cbv zeta in H. destruct (decide _).
    + destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok] eqn:E.
      injection H as <- ->. exact (IH _ _ (conj E Hl)).
    + destruct (enc_lines_again_simp labs ffis _ enc xs) as [rest ok] eqn:E.
      injection H as <- Hok. apply Bool.andb_true_iff in Hok as [Hl1 ->]. apply N.eqb_eq in Hl1.
      cbn [lab_len_pos_ok line_lab_len_pos_ok line_len andb]. rewrite Hl1 in E |- *.
      exact (IH _ _ (conj E Hl)).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_secs_again_pos_ok" *)
Theorem enc_secs_again_pos_ok : forall pos labs ffis enc (code res : list (sec a)),
  enc_secs_again pos labs ffis enc code = (res, true) /\ all_lab_len_pos_ok pos code ->
  all_lab_len_pos_ok pos res.
Proof.
  intros pos labs ffis enc ls; revert pos.
  induction ls as [|[k lines] rest IH]; intros pos res (H & Hok); cbn [enc_secs_again] in H.
  - injection H as <-. reflexivity.
  - destruct (enc_lines_again labs ffis pos enc lines ([], true)) as [lines1 [pos1 ok1]] eqn:E1.
    destruct (enc_secs_again pos1 labs ffis enc rest) as [rest1 ok2] eqn:E2.
    injection H as <- Hok'. apply Bool.andb_true_iff in Hok' as [-> ->].
    cbn [all_lab_len_pos_ok] in Hok |- *. apply Bool.andb_true_iff in Hok as [H1 H2].
    destruct (enc_lines_again_simp_of _ _ _ _ _ _ _ _ E1) as [Es Ep].
    pose proof (enc_lines_again_simp_len _ _ _ _ _ _ Es) as Hlen.
    rewrite (enc_lines_again_simp_pos_ok _ _ _ _ _ _ (conj Es H1)).
    rewrite Ep, sec_length_sum_line_len in E2. rewrite (sec_length_sum_line_len lines1 0).
    rewrite N.add_0_r, N.add_comm. apply IH. split; [exact E2|].
    rewrite sec_length_sum_line_len, N.add_0_r in H2. rewrite Hlen, N.add_comm. exact H2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lab_len_pos_ok_even_prefix_zero" *)
Theorem lab_len_pos_ok_even_prefix_zero : forall pos (ls : list (line a)),
  EVEN pos /\ lab_len_pos_ok pos ls -> label_prefix_zero ls.
Proof.
  intros pos ls; revert pos. induction ls as [|[k1 k2 l|x1 x2 x3|x1 x2 x3 x4] xs IH];
    intros pos [He H]; [exact label_prefix_zero_nil| |apply lpz_not_Label; discriminate
                       |apply lpz_not_Label; discriminate].
  cbn [lab_len_pos_ok line_lab_len_pos_ok line_len] in H. rewrite He in H.
  apply Bool.andb_true_iff in H as [Hl H]. apply N.eqb_eq in Hl. subst l.
  apply lpz_Label. split; [reflexivity|]. apply (IH (pos + 0)). rewrite N.add_0_r in *. auto.
Qed.

End LabLenPos.

Section PadPos.
Context {a : N}.

Lemma add_nop_nonlabel_head nop (h : line a) t :
  ~ is_Label h ->
  exists h', add_nop nop (h :: t) = h' :: t /\ ~ is_Label h' /\ line_len h' = line_len h + 1 /\
             label_zero h' = label_zero h /\
             (forall pos, line_lab_len_pos_ok pos h' = line_lab_len_pos_ok pos h).
Proof.
  intros Hh. destruct h as [k1 k2 l|x1 x2 l|x w bytes l]; [exfalso; apply Hh; reflexivity| |].
  - eexists. split; [reflexivity|]. split; [discriminate|]. split; [reflexivity|]. split; reflexivity.
  - eexists. split; [reflexivity|]. split; [discriminate|]. split; [reflexivity|]. split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pad_section_pos_ok" *)
Theorem pad_section_pos_ok : forall nop (lines aux : list (line a)) pos,
  lab_len_pos_ok (pos + SUM (MAP line_len aux)) lines /\
  lab_len_pos_ok pos (REVERSE aux) /\
  EVERY label_zero aux /\
  (NULL aux \/ is_Label (HD aux) -> label_prefix_zero lines) ->
  lab_len_pos_ok pos (pad_section nop lines aux).
Proof.
  intros nop lines. induction lines as [|[k1 k2 len|x1 x2 l|y w bytes l] xs IH];
    intros aux pos (H1 & H2 & H3 & H4); cbn [pad_section].
  - exact H2.
  - cbn [lab_len_pos_ok line_lab_len_pos_ok line_len] in H1. apply Bool.andb_true_iff in H1 as [Hl H1].
    set (P := pos + SUM (MAP line_len aux)) in *.
    destruct (EVEN P) eqn:EP; apply N.eqb_eq in Hl; subst len.
    + rewrite N.eqb_refl. apply IH. split; [|split; [|split]].
      * cbn [MAP map SUM line_len]. rewrite N.add_0_l. rewrite N.add_0_r in H1. exact H1.
      * cbn [rev]. rewrite lab_len_pos_ok_append, H2. cbn [lab_len_pos_ok line_lab_len_pos_ok line_len].
        rewrite map_rev, SUM_rev. fold P. rewrite EP. reflexivity.
      * cbn [EVERY label_zero N.eqb]. exact H3.
      * intros _. apply (lab_len_pos_ok_even_prefix_zero P). rewrite N.add_0_r in H1. split; [exact EP|exact H1].
    + assert (Hna : ~ (NULL aux \/ is_Label (HD aux))).
      { intros Hc. specialize (H4 Hc). apply lpz_Label in H4 as [Hc' _]. discriminate. }
      destruct aux as [|h t]; [exfalso; apply Hna; left; reflexivity|].
      assert (Hh : ~ is_Label h) by (intros Hc; apply Hna; right; exact Hc).
      destruct (add_nop_nonlabel_head nop h t Hh) as (h' & E & Hh' & Hlen & Hz & Hp).
      cbn [N.eqb Pos.eqb]. rewrite E. apply IH. split; [|split; [|split]].
      * cbn [MAP map SUM line_len] in *. rewrite Hlen.
        replace (pos + (0 + (line_len h + 1 + SUM (MAP line_len t)))) with (P + 1) by (unfold P; lia).
        exact H1.
      * cbn [rev] in H2 |- *. rewrite !lab_len_pos_ok_append in *.
        apply Bool.andb_true_iff in H2 as [H2a H2b]. rewrite H2a.
        cbn [lab_len_pos_ok] in H2b |- *. rewrite Hp.
        apply Bool.andb_true_iff in H2b as [H2b _]. rewrite H2b. cbn [andb line_lab_len_pos_ok].
        rewrite !map_app, !SUM_app, !map_rev, !SUM_rev. cbn [MAP map SUM]. rewrite Hlen.
        replace (pos + (SUM (MAP line_len t) + (line_len h + 1 + 0))) with (P + 1)
          by (unfold P; cbn [MAP map SUM]; lia).
        rewrite N.even_add, EP. reflexivity.
      * cbn [EVERY label_zero N.eqb andb] in H3 |- *. rewrite Hz. exact H3.
      * intros _. apply (lab_len_pos_ok_even_prefix_zero (P + 1)). split; [rewrite N.even_add, EP; reflexivity|].
        exact H1.
  - cbn [lab_len_pos_ok line_lab_len_pos_ok line_len andb] in H1. apply IH. split; [|split; [|split]].
    + cbn [MAP map SUM line_len]. replace (pos + (l + SUM (MAP line_len aux))) with
        (pos + SUM (MAP line_len aux) + l) by lia. exact H1.
    + cbn [rev]. rewrite lab_len_pos_ok_append, H2. reflexivity.
    + exact H3.
    + intros [Hc|Hc]; discriminate.
  - cbn [lab_len_pos_ok line_lab_len_pos_ok line_len andb] in H1. apply IH. split; [|split; [|split]].
    + cbn [MAP map SUM line_len]. replace (pos + (l + SUM (MAP line_len aux))) with
        (pos + SUM (MAP line_len aux) + l) by lia. exact H1.
    + cbn [rev]. rewrite lab_len_pos_ok_append, H2. reflexivity.
    + exact H3.
    + intros [Hc|Hc]; discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_len_pad_section" *)
Theorem line_len_pad_section : forall nop (xs aux : list (line a)),
  LENGTH nop = 1 /\ EVERY label_one xs /\ (EVERY is_Label aux -> label_prefix_zero xs) ->
  SUM (MAP line_len (pad_section nop xs aux)) = SUM (MAP line_len xs) + SUM (MAP line_len aux).
Proof.
  intros nop xs; induction xs as [|[k1 k2 l|x1 x2 l|y w bytes l] ys IH];
    intros aux (Hn & H1 & H5); cbn [pad_section]; cbn [EVERY] in H1.
  - rewrite map_rev, SUM_rev. cbn. lia.
  - apply Bool.andb_true_iff in H1 as [Hx H1]. cbn [label_one] in Hx. apply N.leb_le in Hx.
    destruct (N.eqb_spec l 0) as [->|Hl0].
    + rewrite IH; [cbn [MAP map SUM line_len]; lia|].
      split; [exact Hn|split; [exact H1|]]. intros He. cbn [EVERY is_Label andb] in He.
      specialize (H5 He). apply lpz_Label in H5. apply H5.
    + assert (l = 1) by lia. subst l.
      assert (Hna : ~ EVERY is_Label aux).
      { intros He. specialize (H5 He). apply lpz_Label in H5 as [Hc _]. discriminate. }
      rewrite IH.
      * cbn [MAP map SUM line_len]. rewrite line_len_add_nop1 by exact Hna. lia.
      * split; [exact Hn|split; [exact H1|]]. intros He. cbn [EVERY is_Label andb] in He.
        rewrite EVERY_is_Label_add_nop_preserved in He. contradiction.
  - rewrite IH; [cbn [MAP map SUM line_len]; lia|].
    split; [exact Hn|split; [exact H1|]]. cbn. intros Hc; discriminate.
  - rewrite IH; [cbn [MAP map SUM line_len]; lia|].
    split; [exact Hn|split; [exact H1|]]. cbn. intros Hc; discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_lab_len_pos_ok_pad_code" *)
Theorem all_lab_len_pos_ok_pad_code : forall nop (code : list (sec a)) pos,
  all_lab_len_pos_ok pos code /\
  (LENGTH nop <> 1 -> EVERY sec_label_zero code) /\
  EVERY sec_label_one code /\ EVERY sec_label_prefix_zero code ->
  all_lab_len_pos_ok pos (pad_code nop code).
Proof.
  intros nop code. induction code as [|[k xs] rest IH]; intros pos (H1 & H2 & H3 & H4); [reflexivity|].
  cbn [pad_code all_lab_len_pos_ok] in *.
  apply Bool.andb_true_iff in H1 as [H1a H1b].
  cbn [EVERY sec_label_one sec_label_prefix_zero] in H3, H4.
  apply Bool.andb_true_iff in H3 as [H3a H3b]. apply Bool.andb_true_iff in H4 as [H4a H4b].
  apply bool_decide_spec in H4a.
  apply Bool.andb_true_iff. split.
  - apply pad_section_pos_ok. split; [cbn; rewrite N.add_0_r; exact H1a|].
    split; [reflexivity|]. split; [reflexivity|]. intros _; exact H4a.
  - assert (Hs : SUM (MAP line_len (pad_section nop xs [])) = SUM (MAP line_len xs)).
    { destruct (N.eq_dec (LENGTH nop) 1) as [Hn|Hn].
      - rewrite line_len_pad_section; [cbn; lia|]. split; [exact Hn|split; [exact H3a|intros _; exact H4a]].
      - specialize (H2 Hn). cbn [EVERY sec_label_zero] in H2. apply Bool.andb_true_iff in H2 as [H2a _].
        rewrite line_len_pad_section0 by exact H2a. cbn. lia. }
    rewrite !sec_length_sum_line_len, Hs. rewrite sec_length_sum_line_len in H1b.
    apply IH. split; [exact H1b|split; [|split; [exact H3b|exact H4b]]].
    intros Hn. specialize (H2 Hn). cbn [EVERY] in H2. apply Bool.andb_true_iff in H2 as [_ H2]. exact H2.
Qed.

End PadPos.

(** ** Invariant: jump offsets ok *)

Section OffsetOk.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_offset_ok_def" *)
Definition line_offset_ok (labs : spt (spt N)) (ffis : list ffiname) (pos : N) (l : line a) : Prop :=
  match l with
  | LabAsm a0 w bytes _ => w = get_jump_offset a0 ffis labs pos
  | _ => True
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_offset_ok_def" *)
Fixpoint lines_offset_ok (labs : spt (spt N)) (ffis : list ffiname) (pos : N) (ls : list (line a))
    : Prop :=
  match ls with
  | [] => True
  | l :: ls => line_offset_ok labs ffis pos l /\ lines_offset_ok labs ffis (pos + line_len l) ls
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_offset_ok_append" *)
Theorem lines_offset_ok_append : forall labs ffis pos (l1 l2 : list (line a)),
  lines_offset_ok labs ffis pos (l1 ++ l2) <->
  lines_offset_ok labs ffis pos l1 /\
  lines_offset_ok labs ffis (pos + SUM (MAP line_len l1)) l2.
Proof.
  intros labs ffis pos l1; revert pos; induction l1 as [|x l1 IH]; intros pos l2.
  - cbn. rewrite N.add_0_r. tauto.
  - cbn [app lines_offset_ok MAP map SUM]. rewrite IH, N.add_assoc. tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "offset_ok_def" *)
Fixpoint offset_ok (labs : spt (spt N)) (ffis : list ffiname) (pos : N) (ss : list (sec a)) : Prop :=
  match ss with
  | [] => True
  | Section_ k ls :: ss =>
      lines_offset_ok labs ffis pos ls /\ offset_ok labs ffis (pos + SUM (MAP line_len ls)) ss
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_simp_offset_ok" *)
Theorem enc_lines_again_simp_offset_ok : forall labs ffis pos enc (lines res : list (line a)) ok,
  enc_lines_again_simp labs ffis pos enc lines = (res, ok) -> lines_offset_ok labs ffis pos res.
Proof.
  intros labs ffis pos enc lines; revert pos.
  induction lines as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos res ok H;
    cbn [enc_lines_again_simp] in H.
  - injection H as <- _. exact Logic.I.
  - destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok1] eqn:E.
    injection H as <- _. split; [exact Logic.I|exact (IH _ _ _ E)].
  - destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok1] eqn:E.
    injection H as <- _. split; [exact Logic.I|exact (IH _ _ _ E)].
  - cbv zeta in H. destruct (decide _) as [Ew|Nw].
    + destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok1] eqn:E.
      injection H as <- _. split; [exact Ew|exact (IH _ _ _ E)].
    + destruct (enc_lines_again_simp labs ffis _ enc xs) as [rest ok1] eqn:E.
      injection H as <- _. split; [reflexivity|exact (IH _ _ _ E)].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_secs_again_offset_ok" *)
Theorem enc_secs_again_offset_ok : forall pos labs ffis enc (ls res : list (sec a)) ok,
  enc_secs_again pos labs ffis enc ls = (res, ok) -> offset_ok labs ffis pos res.
Proof.
  intros pos labs ffis enc ls; revert pos.
  induction ls as [|[k lines] rest IH]; intros pos res ok H; cbn [enc_secs_again] in H.
  - injection H as <- _. exact Logic.I.
  - destruct (enc_lines_again labs ffis pos enc lines ([], true)) as [lines1 [pos1 ok1]] eqn:E1.
    destruct (enc_secs_again pos1 labs ffis enc rest) as [rest1 ok2] eqn:E2.
    injection H as <- _.
    pose proof (enc_lines_again_simp_EQ labs ffis pos enc lines [] true) as EQ.
    destruct (enc_lines_again_simp labs ffis pos enc lines) as [ls' fl] eqn:Es.
    rewrite E1 in EQ. injection EQ as -> -> _.
    split; [exact (enc_lines_again_simp_offset_ok _ _ _ _ _ _ _ Es)|].
    rewrite sec_length_sum_line_len, N.add_comm in E2. exact (IH _ _ _ E2).
Qed.

Lemma no_label_one_head P (xs : list (line a)) :
  EVEN P -> lab_len_pos_ok P xs -> ~ (~ NULL xs /\ is_Label (HD xs) /\ line_len (HD xs) = 1).
Proof.
  intros EP H1 [Hn [Hlab Hlen]]. destruct xs as [|x xs']; [exact (Hn eq_refl)|].
  destruct x as [k1' k2' l'|x1' x2' x3'|y1 y2 y3 y4]; cbn [HD is_Label] in Hlab; try discriminate.
  cbn [lab_len_pos_ok line_lab_len_pos_ok line_len HD] in H1, Hlen. subst l'.
  rewrite EP in H1. discriminate.
Qed.

Lemma add_nop_offset nop (h : line a) t h' :
  ~ is_Label h -> add_nop nop (h :: t) = h' :: t ->
  forall labs ffis p, line_offset_ok labs ffis p h' <-> line_offset_ok labs ffis p h.
Proof.
  intros Hh E labs ffis p. destruct h as [k1 k2 l|x1 x2 l|x w bytes l];
    [exfalso; apply Hh; reflexivity| |]; cbn [add_nop] in E; injection E as <-; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_offset_ok_pad_section" *)
Theorem lines_offset_ok_pad_section : forall nop (lines aux : list (line a)) labs ffis pos,
  lab_len_pos_ok (pos + SUM (MAP line_len aux)) lines /\
  lab_len_pos_ok pos (REVERSE aux) /\ EVERY label_zero aux /\
  (~ NULL lines /\ is_Label (HD lines) /\ line_len (HD lines) = 1 ->
   ~ NULL aux /\ ~ is_Label (HD aux)) /\
  lines_offset_ok labs ffis pos (REVERSE aux ++ lines) ->
  lines_offset_ok labs ffis pos (pad_section nop lines aux).
Proof.
  intros nop lines. induction lines as [|[k1 k2 len|x1 x2 l|y w bytes l] xs IH];
    intros aux labs ffis pos (H1 & H2 & H3 & H4 & H5); cbn [pad_section].
  - rewrite app_nil_r in H5. exact H5.
  - cbn [lab_len_pos_ok line_lab_len_pos_ok line_len] in H1. apply Bool.andb_true_iff in H1 as [Hl H1].
    set (P := pos + SUM (MAP line_len aux)) in *.
    apply lines_offset_ok_append in H5 as [H5a H5b].
    cbn [lines_offset_ok line_offset_ok line_len] in H5b. destruct H5b as [_ H5b].
    rewrite map_rev, SUM_rev in H5b. fold P in H5b.
    destruct (EVEN P) eqn:EP; apply N.eqb_eq in Hl; subst len.
    + rewrite N.eqb_refl. apply IH. split; [|split; [|split; [|split]]].
      * cbn [MAP map SUM line_len]. rewrite N.add_0_l. rewrite N.add_0_r in H1. exact H1.
      * cbn [rev]. rewrite lab_len_pos_ok_append, H2. cbn [lab_len_pos_ok line_lab_len_pos_ok line_len].
        rewrite map_rev, SUM_rev. fold P. rewrite EP. reflexivity.
      * cbn [EVERY label_zero N.eqb]. exact H3.
      * intros Hc. exfalso. apply (no_label_one_head (P + 0) xs); [rewrite N.add_0_r; exact EP|exact H1|exact Hc].
      * cbn [rev]. rewrite <- app_assoc. apply lines_offset_ok_append. split; [exact H5a|].
        split; [exact Logic.I|]. rewrite map_rev, SUM_rev. fold P. rewrite N.add_0_r in H5b |- *. exact H5b.
    + assert (Hna : ~ NULL aux /\ ~ is_Label (HD aux)) by (apply H4; split; [discriminate|split; reflexivity]).
      destruct aux as [|h t]; [exfalso; apply (proj1 Hna); reflexivity|].
      destruct Hna as [_ Hh]. cbn [HD] in Hh.
      destruct (add_nop_nonlabel_head nop h t Hh) as (h' & E & Hh' & Hlen & Hz & Hp).
      cbn [N.eqb Pos.eqb]. rewrite E. apply IH. split; [|split; [|split; [|split]]].
      * cbn [MAP map SUM line_len] in *. rewrite Hlen.
        replace (pos + (0 + (line_len h + 1 + SUM (MAP line_len t)))) with (P + 1) by (unfold P; lia).
        exact H1.
      * cbn [rev] in H2 |- *. rewrite !lab_len_pos_ok_append in *.
        apply Bool.andb_true_iff in H2 as [H2a H2b]. rewrite H2a.
        cbn [lab_len_pos_ok] in H2b |- *. rewrite Hp.
        apply Bool.andb_true_iff in H2b as [H2b _]. rewrite H2b. cbn [andb line_lab_len_pos_ok].
        rewrite !map_app, !SUM_app, !map_rev, !SUM_rev. cbn [MAP map SUM]. rewrite Hlen.
        replace (pos + (SUM (MAP line_len t) + (line_len h + 1 + 0))) with (P + 1)
          by (unfold P; cbn [MAP map SUM]; lia).
        rewrite N.even_add, EP. reflexivity.
      * cbn [EVERY label_zero N.eqb andb] in H3 |- *. rewrite Hz. exact H3.
      * intros Hc. exfalso. apply (no_label_one_head (P + 1) xs); [rewrite N.even_add, EP; reflexivity| |exact Hc].
        exact H1.
      * cbn [rev] in H5a |- *. apply lines_offset_ok_append in H5a as [H5c H5d].
        rewrite <- !app_assoc. apply lines_offset_ok_append. split; [exact H5c|].
        cbn [app lines_offset_ok]. split.
        { destruct H5d as [H5d _]. rewrite (add_nop_offset nop h t h' Hh E). exact H5d. }
        split; [exact Logic.I|].
        match goal with |- lines_offset_ok _ _ ?q xs => replace q with (P + 1) end; [exact H5b|].
        unfold P. cbn [MAP map SUM line_len]. rewrite Hlen, map_rev, SUM_rev. lia.
  - cbn [lab_len_pos_ok line_lab_len_pos_ok line_len andb] in H1. apply IH.
    split; [|split; [|split; [|split]]].
    + cbn [MAP map SUM line_len]. replace (pos + (l + SUM (MAP line_len aux))) with
        (pos + SUM (MAP line_len aux) + l) by lia. exact H1.
    + cbn [rev]. rewrite lab_len_pos_ok_append, H2. reflexivity.
    + exact H3.
    + intros _. split; discriminate.
    + cbn [rev]. rewrite <- app_assoc. apply lines_offset_ok_append in H5 as [A B].
      apply lines_offset_ok_append. split; [exact A|]. destruct B as [Bx B]. split; [exact Bx|exact B].
  - cbn [lab_len_pos_ok line_lab_len_pos_ok line_len andb] in H1. apply IH.
    split; [|split; [|split; [|split]]].
    + cbn [MAP map SUM line_len]. replace (pos + (l + SUM (MAP line_len aux))) with
        (pos + SUM (MAP line_len aux) + l) by lia. exact H1.
    + cbn [rev]. rewrite lab_len_pos_ok_append, H2. reflexivity.
    + exact H3.
    + intros _. split; discriminate.
    + cbn [rev]. rewrite <- app_assoc. apply lines_offset_ok_append in H5 as [A B].
      apply lines_offset_ok_append. split; [exact A|]. destruct B as [Bx B]. split; [exact Bx|exact B].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "offset_ok_pad_code" *)
Theorem offset_ok_pad_code : forall nop labs ffis pos (code : list (sec a)),
  (LENGTH nop <> 1 -> EVERY sec_label_zero code) /\
  EVERY sec_label_one code /\ EVERY sec_label_prefix_zero code /\
  all_lab_len_pos_ok pos code /\ offset_ok labs ffis pos code ->
  offset_ok labs ffis pos (pad_code nop code).
Proof.
  intros nop labs ffis pos code. revert pos.
  induction code as [|[k ls] rest IH]; intros pos (H1 & H2 & H3 & H4 & H5); [exact Logic.I|].
  cbn [pad_code offset_ok] in *. destruct H5 as [H5a H5b].
  cbn [EVERY sec_label_one sec_label_prefix_zero all_lab_len_pos_ok] in H2, H3, H4.
  apply Bool.andb_true_iff in H2 as [H2a H2b]. apply Bool.andb_true_iff in H3 as [H3a H3b].
  apply Bool.andb_true_iff in H4 as [H4a H4b]. apply bool_decide_spec in H3a.
  assert (Hs : SUM (MAP line_len (pad_section nop ls [])) = SUM (MAP line_len ls)).
  { destruct (N.eq_dec (LENGTH nop) 1) as [Hn|Hn].
    - rewrite line_len_pad_section; [cbn; lia|]. split; [exact Hn|split; [exact H2a|intros _; exact H3a]].
    - specialize (H1 Hn). cbn [EVERY sec_label_zero] in H1. apply Bool.andb_true_iff in H1 as [H1a _].
      rewrite line_len_pad_section0 by exact H1a. cbn. lia. }
  split.
  - apply lines_offset_ok_pad_section. split; [cbn; rewrite N.add_0_r; exact H4a|].
    split; [reflexivity|]. split; [reflexivity|]. split; [|exact H5a].
    intros [Hn [Hlab Hlen]]. exfalso. destruct ls as [|x ls']; [exact (Hn eq_refl)|].
    destruct x as [k1 k2 l|x1 x2 x3|y1 y2 y3 y4]; cbn [HD is_Label] in Hlab; try discriminate.
    cbn [HD line_len] in Hlen. subst l. apply lpz_Label in H3a as [Hc _]. discriminate.
  - rewrite Hs. apply IH. split; [|split; [exact H2b|split; [exact H3b|split; [|exact H5b]]]].
    + intros Hn. specialize (H1 Hn). cbn [EVERY] in H1. apply Bool.andb_true_iff in H1 as [_ H1]. exact H1.
    + rewrite sec_length_sum_line_len, N.add_0_r in H4b. exact H4b.
Qed.

End OffsetOk.
