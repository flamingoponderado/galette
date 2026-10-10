(** * CakeML [wordConvsProof]: syntactic properties of the wordLang passes

    Port of [cakeml/compiler/backend/proofs/wordConvsProofScript.sml].  All
    of HOL's declarations are ported.

    Notes:
    - HOL's [word_get_code_labels] and [word_good_handlers] are wordConvs'
      [get_code_labels] and [good_handlers]; code-label sets are [N -> Prop]
      and HOL set equalities are proved with [set_ext].
    - HOL's free variables are quantified explicitly (the predicate [P] of
      [not_created_subprogs] and [every_inst] first).  HOL tuples nest to
      the right ([(a,b,c)] is [(a, (b, c))]); HOL [num] is [N]; HOL's [0w] is
      [n2w 0].
    - Boolean properties ([every_inst], [flat_exp_conventions], ...) use the
      [is_true] coercion; HOL's [⇔] between them is [=] on [bool].
      [not_created_subprogs] is [Prop]-valued, so HOL's [=]/[⇔] between its
      instances is [<->].
    - HOL's [word_alloc$merge_moves] and [word_unreach$merge_moves] are
      qualified where needed; [word_simp$compile_exp] is
      [word_simp.compile_exp].
    - [const_fp_loop_Seq] (HOL: the [Seq] clauses of [const_fp_loop_def]) is
      stated as the [Seq] equation; [helper] (HOL: the contrapositive of
      [MEM_extract_labels_Seq_assoc_right_lemma]) is stated with the
      contrapositive spelled out.
    - Not ported: the ML proof helpers [FIRST_THEN],
      [try_cancel_labels_rel_append], [boring_tac], [convs] and [rmt_convs]
      (tactics and theorem lists).
    - Proofs are by structural induction ([prog_nested_ind], or the
      Galette-only [exp_deep_ind] for [inst_select_exp]) instead of HOL's
      recursion-induction principles, and often go through Galette-only
      equation-form helpers ([..._eq], [..._aux]) or shape lemmas
      ([simple_prog], [SimpSeq_cases], [word_alloc_cases], [subseq]); these
      and the tactics below have no HOL original. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From Galette.cakeml.compiler.backend Require stackLang.
From Galette.cakeml.compiler.backend Require Import wordLang word_simp word_inst word_alloc
  word_unreach word_remove word_cse word_copy word_to_word.
From Galette.cakeml.compiler.backend.semantics Require Import wordConvs.
From Stdlib Require Import Permutation Btauto.
Open Scope N_scope.

(** ** Galette-only tactics *)

Ltac bsplit :=
  unfold is_true in *;
  repeat match goal with
  | H : is_true (andb _ _) |- _ => apply andb_prop in H; destruct H
  | H : andb _ _ = true |- _ => apply andb_prop in H; destruct H
  | H : _ /\ _ |- _ => destruct H
  | |- is_true (andb _ _) => apply andb_true_intro; split
  | |- andb _ _ = true => apply andb_true_intro; split
  | |- _ /\ _ => split
  end.

Lemma bd_true (P : Prop) `{Decision P} : P -> bool_decide P = true.
Proof. apply bool_decide_spec. Qed.
Lemma bd_false (P : Prop) `{Decision P} : ~ P -> bool_decide P = false.
Proof. intros HP; destruct (bool_decide P) eqn:E; [|reflexivity]. apply bool_decide_spec in E; tauto. Qed.

Ltac solve_disj := first [reflexivity | left; solve_disj | right; solve_disj].

(** Decide [bool_decide]s of (disjunctions of) constructor equalities. *)
Ltac bd_simp :=
  repeat match goal with
  | |- context [@bool_decide ?P ?d] =>
      first [ rewrite (@bd_true P d) by solve_disj
            | rewrite (@bd_false P d) by (intuition discriminate) ]
  | H : context [@bool_decide ?P ?d] |- _ =>
      first [ rewrite (@bd_true P d) in H by solve_disj
            | rewrite (@bd_false P d) in H by (intuition discriminate) ]
  end.

Lemma Some_eq_inv {A} (x y : A) : Some x = Some y -> x = y.
Proof. intros H; injection H; auto. Qed.

Ltac inv_eqs :=
  repeat match goal with
  | H : (_, _) = (_, _) |- _ => apply pair_equal_spec in H; destruct H; subst
  | H : Some _ = Some _ |- _ => apply Some_eq_inv in H; subst
  | H : Some _ = None |- _ => discriminate H
  | H : None = Some _ |- _ => discriminate H
  end.

Ltac case_split :=
  match goal with
  | H : context [match ?e with _ => _ end] |- _ =>
      let E := fresh "E" in destruct e eqn:E; try rewrite E in *
  | |- context [match ?e with _ => _ end] =>
      let E := fresh "E" in destruct e eqn:E; try rewrite E in *
  end.

Ltac use_ih :=
  repeat match goal with
  | IH : forall c x y, ?f ?q c = (x, y) -> _, E : ?f ?q ?c0 = (?x0, ?y0) |- _ =>
      specialize (IH _ _ _ E)
  end.

Ltac set_leaf :=
  first [ assumption | reflexivity | exact Logic.I
        | left; set_leaf | right; set_leaf ].

Ltac sets_core x :=
  cbv beta in *;
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H
  | H : False |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  | H : ?y = x |- _ => subst y
  | H : x = ?y |- _ => is_var y; subst y
  | H : forall y : _, _ -> _ |- _ => specialize (H x ltac:(set_leaf)); cbv beta in H
  end;
  set_leaf.

Ltac pose_new t :=
  let T := type of t in
  lazymatch goal with
  | _ : T |- _ => fail
  | _ => pose proof t
  end.

Ltac sets :=
  repeat match goal with
         | H : ?T |- _ =>
             lazymatch T with
             | pred_set.SUBSET _ _ => fail
             | _ = _ => fail
             | forall _, _ => clear H
             end
         end;
  repeat match goal with |- context [match ?e with _ => _ end] => destruct e end;
  unfold pred_set.SUBSET, pred_set.UNION, pred_set.INSERT, pred_set.EMPTY, pred_set.IN in *;
  lazymatch goal with
  | |- _ = _ =>
      apply set_ext; let x := fresh "x" in intro x; split; intro; sets_core x
  | |- _ => let x := fresh "x" in intros x ?; sets_core x
  end.

Ltac set_eq := sets.

(** Galette-only: [labels_rel] up to permutation of the old labels. *)
Lemma labels_rel_perm_l (xs xs' ys : list (N * N)) :
  Permutation xs xs' -> labels_rel xs' ys -> labels_rel xs ys.
Proof.
  intros HP H; eapply labels_rel_TRANS; split; [|exact H].
  apply PERM_IMP_labels_rel; symmetry; exact HP.
Qed.

Lemma labels_rel_nil (ys : list (N * N)) : labels_rel ys [].
Proof. split; [intros; reflexivity|intros x Hx; rewrite IN_set in Hx; destruct Hx]. Qed.

Lemma labels_rel_app_l (xs ys zs : list (N * N)) :
  labels_rel xs zs -> labels_rel (xs ++ ys) zs.
Proof.
  intros H; rewrite <- (app_nil_r zs); apply labels_rel_APPEND; split; [exact H|].
  apply labels_rel_nil.
Qed.

Lemma labels_rel_app_r (xs ys zs : list (N * N)) :
  labels_rel ys zs -> labels_rel (xs ++ ys) zs.
Proof.
  intros H; eapply labels_rel_perm_l; [apply Permutation_app_comm|]; apply labels_rel_app_l, H.
Qed.

Ltac lr :=
  repeat first
    [ apply labels_rel_refl
    | apply labels_rel_nil
    | apply labels_rel_APPEND; split
    | assumption ].

Section Simp.
Context {a : N}.
Implicit Types p q : prog a.

(** ** word_simp$compile_exp *)

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_SmartSeq" *)
Theorem extract_labels_SmartSeq : forall (p1 p2 : prog a),
  extract_labels (SmartSeq p1 p2) = extract_labels (Seq p1 p2).
Proof. intros [] p2; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_Seq_assoc_lemma" *)
Theorem extract_labels_Seq_assoc_lemma : forall (p1 p2 : prog a),
  extract_labels (Seq_assoc p1 p2) = extract_labels p1 ++ extract_labels p2.
Proof.
  intros p1 p2; revert p1; induction p2 using prog_nested_ind; intros p0;
    cbn [Seq_assoc]; rewrite ?extract_labels_SmartSeq; cbn [extract_labels];
    rewrite ?app_nil_r; try reflexivity.
  - rewrite IHp2; reflexivity.
  - destruct ret as [[? [? [? [? ?]]]]|], h as [[? [? [? ?]]]|];
      cbn [extract_labels]; rewrite ?H, ?H0; reflexivity.
  - rewrite IHp2_2, IHp2_1, app_assoc; reflexivity.
  - rewrite IHp2_1, IHp2_2; reflexivity.
  - rewrite IHp2; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_Seq_assoc" *)
Theorem extract_labels_Seq_assoc : forall p,
  extract_labels (Seq_assoc Skip p) = extract_labels p.
Proof. intros p; rewrite extract_labels_Seq_assoc_lemma; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_drop_consts_1" *)
Theorem extract_labels_drop_consts_1 : forall cs ls,
  extract_labels (@drop_consts a cs ls) = [].
Proof.
  intros cs ls; induction ls as [|x ls IH]; [reflexivity|]; cbn [drop_consts].
  destruct (lookup x cs); [rewrite extract_labels_SmartSeq; cbn [extract_labels]; rewrite IH|];
    auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_drop_consts" *)
Theorem extract_labels_drop_consts : forall cs ls p,
  extract_labels (SmartSeq (drop_consts cs ls) p) = extract_labels p.
Proof.
  intros; rewrite extract_labels_SmartSeq; cbn [extract_labels];
    rewrite extract_labels_drop_consts_1; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_const_fp_loop" *)
Theorem extract_labels_const_fp_loop : forall p cs p1 cs1,
  const_fp_loop p cs = (p1, cs1) ->
  labels_rel (extract_labels p) (extract_labels p1).
Proof.
  intros p; induction p using prog_nested_ind; intros cs p' cs' Hc;
    cbn [const_fp_loop] in Hc.
  all: repeat (case_split; inv_eqs); inv_eqs.
  all: rewrite ?extract_labels_drop_consts; cbn [extract_labels]; try apply labels_rel_refl.
  all: try solve [ eauto
                 | apply labels_rel_CONS; split; [apply labels_rel_refl|eauto]
                 | apply labels_rel_APPEND; split; eauto
                 | apply labels_rel_app_l; eauto
                 | apply labels_rel_app_r; eauto ].
  destruct (const_fp_loop p LN) eqn:E; cbn [FST]; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_const_fp" *)
Theorem extract_labels_const_fp : forall p,
  labels_rel (extract_labels p) (extract_labels (const_fp p)).
Proof.
  intros p; unfold const_fp; destruct (const_fp_loop p LN) eqn:E; cbn [FST].
  eapply extract_labels_const_fp_loop; eauto.
Qed.

End Simp.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "labels_rel_append_imp" *)
Theorem labels_rel_append_imp : forall {A} `{EqDecision A} (X Y Z : list A),
  labels_rel (Y ++ X) Z -> labels_rel (X ++ Y) Z.
Proof.
  intros A EA X Y Z H; eapply labels_rel_TRANS; split; [|exact H].
  apply PERM_IMP_labels_rel, Permutation_app_comm.
Qed.

Section Simp2.
Context {a : N}.
Implicit Types p q : prog a.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "const_fp_loop_Seq" *)
Theorem const_fp_loop_Seq : forall (p1 p2 : prog a) cs,
  const_fp_loop (Seq p1 p2) cs =
  let '(p1', cs') := const_fp_loop p1 cs in
  let '(p2', cs'') := const_fp_loop p2 cs' in
  (Seq p1' p2', cs'').
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "const_fp_loop_dummy_cases" *)
Theorem const_fp_loop_dummy_cases : forall cmp lhs (rhs : reg_imm a) cs (p2 : prog a) cs2,
  const_fp_loop (If cmp lhs rhs (Raise 1) (Raise 2)) cs = (p2, cs2) ->
  (dest_Raise_num p2 = 1 /\
   (forall br1 br2 : prog a, const_fp_loop (If cmp lhs rhs br1 br2) cs = const_fp_loop br1 cs)) \/
  (dest_Raise_num p2 = 2 /\
   (forall br1 br2 : prog a, const_fp_loop (If cmp lhs rhs br1 br2) cs = const_fp_loop br2 cs)) \/
  dest_Raise_num p2 = 0.
Proof.
  intros cmp lhs rhs cs p2 cs2 H; cbn [const_fp_loop] in H.
  destruct (lookup lhs cs) eqn:E1, (get_var_imm_cs rhs cs) eqn:E2;
    [destruct (word_cmp cmp w w0) eqn:E3| | |]; inv_eqs.
  - left; split; [reflexivity|]. intros; cbn [const_fp_loop]; rewrite E1, E2, E3; reflexivity.
  - right; left; split; [reflexivity|]. intros; cbn [const_fp_loop]; rewrite E1, E2, E3; reflexivity.
  - destruct (const_fp_loop (Raise 1) cs), (const_fp_loop (Raise 2) cs); inv_eqs; auto.
  - destruct (const_fp_loop (Raise 1) cs), (const_fp_loop (Raise 2) cs); inv_eqs; auto.
  - destruct (const_fp_loop (Raise 1) cs), (const_fp_loop (Raise 2) cs); inv_eqs; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "dest_If_thm" *)
Theorem dest_If_thm : forall (x2 : prog a) g1 g2 g3 g4 g5,
  dest_If x2 = Some (g1, (g2, (g3, (g4, g5)))) <-> x2 = If g1 g2 g3 g4 g5.
Proof.
  intros [] g1 g2 g3 g4 g5; cbn; split; intros H; inv_eqs; try discriminate; try reflexivity.
  injection H as; subst; reflexivity.
Qed.

(** Galette-only: what a successful hoist test says about [const_fp]. *)
Lemma hoist_branch cmp lhs (rhs : reg_imm a) (b interm br1 br2 : prog a) :
  dest_Raise_num (SND (dest_Seq (const_fp (Seq (Seq b interm)
     (If cmp lhs rhs (Raise 1) (Raise 2)))))) <> 0 ->
  exists b' cs',
    const_fp_loop (Seq b interm) LN = (b', cs') /\
    ((dest_Raise_num (SND (dest_Seq (const_fp (Seq (Seq b interm)
        (If cmp lhs rhs (Raise 1) (Raise 2)))))) = 1 /\
      FST (const_fp_loop (Seq (Seq b interm) (If cmp lhs rhs br1 br2)) LN) =
      Seq b' (FST (const_fp_loop br1 cs'))) \/
     (dest_Raise_num (SND (dest_Seq (const_fp (Seq (Seq b interm)
        (If cmp lhs rhs (Raise 1) (Raise 2)))))) = 2 /\
      FST (const_fp_loop (Seq (Seq b interm) (If cmp lhs rhs br1 br2)) LN) =
      Seq b' (FST (const_fp_loop br2 cs')))).
Proof.
  unfold const_fp; rewrite !(const_fp_loop_Seq (Seq b interm)).
  destruct (const_fp_loop (Seq b interm) LN) as [b' cs'] eqn:E1.
  destruct (const_fp_loop (If cmp lhs rhs (Raise 1) (Raise 2)) cs') as [d cd] eqn:E2.
  cbn [FST SND dest_Seq]. intros Hd. exists b', cs'; split; [reflexivity|].
  apply const_fp_loop_dummy_cases in E2 as [[H1 H2]|[[H1 H2]|H1]]; [left|right|contradiction].
  - split; [exact H1|]. rewrite H2. destruct (const_fp_loop br1 cs'); reflexivity.
  - split; [exact H1|]. rewrite H2. destruct (const_fp_loop br2 cs'); reflexivity.
Qed.

Lemma labels_rel_swap4 (A B C D A' B' C' D' : list (N * N)) :
  labels_rel A A' -> labels_rel B B' -> labels_rel C C' -> labels_rel D D' ->
  labels_rel ((A ++ B) ++ (C ++ D)) ((A' ++ C') ++ (B' ++ D')) /\
  labels_rel ((A ++ B) ++ (C ++ D)) ((A' ++ D') ++ (B' ++ C')).
Proof.
  intros HA HB HC HD; split.
  - apply labels_rel_perm_l with ((A ++ C) ++ (B ++ D)).
    + rewrite <- !app_assoc; apply Permutation_app_head.
      rewrite !app_assoc; apply Permutation_app_tail, Permutation_app_comm.
    + lr.
  - apply labels_rel_perm_l with ((A ++ D) ++ (B ++ C)).
    + rewrite <- !app_assoc; apply Permutation_app_head.
      rewrite (Permutation_app_comm C D), !app_assoc.
      apply Permutation_app_tail, Permutation_app_comm.
    + lr.
Qed.

Lemma const_fp_loop_If_LN c l r (x y : prog a) :
  FST (const_fp_loop (If c l r x y) LN) =
  If c l r (FST (const_fp_loop x LN)) (FST (const_fp_loop y LN)).
Proof.
  cbn [const_fp_loop lookup]. destruct (const_fp_loop x LN), (const_fp_loop y LN); reflexivity.
Qed.

Lemma labels_Seq_interm (b interm : prog a) b' cs' :
  extract_labels interm = [] ->
  const_fp_loop (Seq b interm) LN = (b', cs') ->
  labels_rel (extract_labels b) (extract_labels b').
Proof.
  intros Hi H; apply extract_labels_const_fp_loop in H; cbn [extract_labels] in H.
  rewrite Hi, app_nil_r in H; exact H.
Qed.

Lemma labels_hoist_If (b1 b2 interm : prog a) cmp lhs rhs br1 br2 c' l' r' :
  extract_labels interm = [] ->
  dest_Raise_num (SND (dest_Seq (const_fp (Seq (Seq b1 interm)
     (If cmp lhs rhs (Raise 1) (Raise 2)))))) <> 0 ->
  dest_Raise_num (SND (dest_Seq (const_fp (Seq (Seq b1 interm)
     (If cmp lhs rhs (Raise 1) (Raise 2)))))) +
  dest_Raise_num (SND (dest_Seq (const_fp (Seq (Seq b2 interm)
     (If cmp lhs rhs (Raise 1) (Raise 2)))))) = 3 ->
  labels_rel ((extract_labels b1 ++ extract_labels b2) ++ (extract_labels br1 ++ extract_labels br2))
    (extract_labels (const_fp (If c' l' r' (Seq (Seq b1 interm) (If cmp lhs rhs br1 br2))
                                          (Seq (Seq b2 interm) (If cmp lhs rhs br1 br2))))).
Proof.
  intros Hi Hd1 H3.
  destruct (hoist_branch cmp lhs rhs b1 interm br1 br2 Hd1) as [b1' [cs1 [E1 [[R1 F1]|[R1 F1]]]]];
  rewrite R1 in H3;
  (assert (Hd2 : dest_Raise_num (SND (dest_Seq (const_fp (Seq (Seq b2 interm)
     (If cmp lhs rhs (Raise 1) (Raise 2)))))) <> 0) by lia);
  destruct (hoist_branch cmp lhs rhs b2 interm br1 br2 Hd2) as [b2' [cs2 [E2 [[R2 F2]|[R2 F2]]]]];
    rewrite ?R2 in H3; try lia.
  all: unfold const_fp at 1; rewrite const_fp_loop_If_LN, F1, F2; cbn [extract_labels].
  all: apply labels_Seq_interm in E1, E2; auto.
  - destruct (const_fp_loop br1 cs1) eqn:B1, (const_fp_loop br2 cs2) eqn:B2; cbn [FST].
    apply extract_labels_const_fp_loop in B1, B2.
    apply (labels_rel_swap4 _ _ _ _ _ _ _ _ E1 E2 B1 B2).
  - destruct (const_fp_loop br2 cs1) eqn:B1, (const_fp_loop br1 cs2) eqn:B2; cbn [FST].
    apply extract_labels_const_fp_loop in B1, B2.
    apply (labels_rel_swap4 _ _ _ _ _ _ _ _ E1 E2 B2 B1).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "labels_rel_hoist2" *)
Theorem labels_rel_hoist2 : forall N0 (p1 interm dummy p2 p3 : prog a) cmp lhs rhs br1 br2,
  try_if_hoist2 N0 p1 interm dummy p2 = Some p3 ->
  dest_If p2 = Some (cmp, (lhs, (rhs, (br1, br2)))) ->
  dummy = If cmp lhs rhs (Raise 1) (Raise 2) ->
  extract_labels interm = [] ->
  labels_rel (extract_labels p1 ++ extract_labels p2) (extract_labels p3).
Proof.
  intros N0 p1; revert N0; induction p1 using prog_nested_ind;
    intros N0 interm dummy p2 p3 cmp lhs rhs br1 br2 Hh Hp2 Hd Hi;
    apply dest_If_thm in Hp2; subst p2 dummy; cbn [try_if_hoist2] in Hh;
    destruct (N0 =? 0); try discriminate Hh.
  - (* Seq *)
    destruct (dest_If p1_2) as [[c' [l' [r' [b1 b2]]]]|] eqn:E.
    + apply dest_If_thm in E; subst p1_2.
      destruct (_ =? 0) eqn:Z1 in Hh; [discriminate Hh|].
      destruct (negb _) eqn:Z2 in Hh; [discriminate Hh|]. inv_eqs.
      apply N.eqb_neq in Z1. apply negb_false_iff, N.eqb_eq in Z2.
      cbn [extract_labels]; rewrite <- app_assoc; apply labels_rel_APPEND; split;
        [apply labels_rel_refl|].
      cbn [extract_labels] in *. apply labels_hoist_If; auto.
    + destruct (is_simple p1_2) eqn:S; [|discriminate Hh].
      assert (L4 : extract_labels p1_2 = []) by (destruct p1_2; try discriminate S; reflexivity).
      cbn [extract_labels]; rewrite L4, app_nil_r.
      specialize (IHp1_1 _ _ _ _ _ cmp lhs rhs br1 br2 Hh eq_refl eq_refl).
      apply IHp1_1. cbn [extract_labels]; rewrite L4, Hi; reflexivity.
  - (* If *)
    destruct (_ =? 0) eqn:Z1 in Hh; [discriminate Hh|].
    destruct (negb _) eqn:Z2 in Hh; [discriminate Hh|]. inv_eqs.
    apply N.eqb_neq in Z1. apply negb_false_iff, N.eqb_eq in Z2.
    cbn [extract_labels]. apply labels_hoist_If; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "labels_rel_simp_duplicate_if" *)
Theorem labels_rel_simp_duplicate_if : forall p,
  labels_rel (extract_labels p) (extract_labels (simp_duplicate_if p)).
Proof.
  intros p; induction p using prog_nested_ind; cbn [simp_duplicate_if extract_labels];
    try apply labels_rel_refl.
  - exact IHp.
  - destruct ret as [[? [? [? [? ?]]]]|], h as [[? [? [? ?]]]|]; cbn [extract_labels];
      lr; auto using labels_rel_refl.
  - destruct (try_if_hoist1 (simp_duplicate_if p1) (simp_duplicate_if p2)) as [p3|] eqn:T.
    + rewrite extract_labels_Seq_assoc.
      unfold try_if_hoist1 in T.
      destruct (dest_If (simp_duplicate_if p2)) as [[c [l [r [b1 b2]]]]|] eqn:D; [|discriminate T].
      eapply labels_rel_TRANS; split; [apply labels_rel_APPEND; split; [exact IHp1|exact IHp2]|].
      eapply labels_rel_hoist2; eauto.
    + cbn [extract_labels]; lr.
  - lr.
  - exact IHp.
Qed.

(** Galette-only: [push_out_if_aux] form of [labels_rel_push_out_if]. *)
Lemma labels_rel_push_out_if_aux : forall p,
  labels_rel (extract_labels p) (extract_labels (FST (push_out_if_aux p))).
Proof.
  intros p; induction p using prog_nested_ind; cbn [push_out_if_aux]; try apply labels_rel_refl.
  - destruct (push_out_if_aux p) eqn:E; cbn [FST extract_labels] in *; exact IHp.
  - destruct ret as [[? [? [? [? ?]]]]|]; apply labels_rel_refl.
  - destruct (push_out_if_aux p1) as [c1 []] eqn:E1; cbn [FST extract_labels] in *.
    + lr.
    + destruct (push_out_if_aux p2) as [c2 b2] eqn:E2; cbn [FST extract_labels] in *; lr.
  - destruct (push_out_if_aux p1) as [c1 []] eqn:E1, (push_out_if_aux p2) as [c2 []] eqn:E2;
      cbn [FST extract_labels] in *; rewrite ?app_nil_r; try (lr; fail).
    apply labels_rel_append_imp; lr.
  - cbn [FST extract_labels]; exact IHp.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "labels_rel_push_out_if" *)
Theorem labels_rel_push_out_if : forall p,
  labels_rel (extract_labels p) (extract_labels (push_out_if p)).
Proof. exact labels_rel_push_out_if_aux. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_compile_exp" *)
Theorem extract_labels_compile_exp : forall p,
  labels_rel (extract_labels p) (extract_labels (word_simp.compile_exp p)).
Proof.
  intros p; unfold word_simp.compile_exp.
  eapply labels_rel_TRANS; split; [|apply labels_rel_push_out_if].
  eapply labels_rel_TRANS; split; [|apply labels_rel_simp_duplicate_if].
  eapply labels_rel_TRANS; split; [|apply extract_labels_const_fp].
  rewrite extract_labels_Seq_assoc; apply labels_rel_refl.
Qed.

(** *** inst_ok_less *)

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "dest_Seq_no_inst" *)
Theorem dest_Seq_no_inst : forall P (prog : prog a),
  every_inst P prog ->
  every_inst P (FST (dest_Seq prog)) /\ every_inst P (SND (dest_Seq prog)).
Proof. intros P [] H; cbn in *; bsplit; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "every_inst_SmartSeq" *)
Theorem every_inst_SmartSeq : forall P (p q : prog a),
  every_inst P (SmartSeq p q) = (every_inst P p && every_inst P q).
Proof. intros P [] q; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "Seq_assoc_no_inst" *)
Theorem Seq_assoc_no_inst : forall P (p1 p2 : prog a),
  every_inst P p1 /\ every_inst P p2 -> every_inst P (Seq_assoc p1 p2).
Proof.
  intros P p1 p2; revert p1; induction p2 using prog_nested_ind; intros p0 [H1 H2];
    cbn [Seq_assoc]; rewrite ?every_inst_SmartSeq; cbn [every_inst] in *; bsplit; auto.
  all: try (destruct ret as [[? [? [? [? ?]]]]|]; [destruct h as [[? [? [? ?]]]|]|];
      cbn [every_inst] in *; bsplit; auto).
  all: try (apply IHp2_2; split; [apply IHp2_1; split|]; auto).
  all: first [eapply IHp2|eapply IHp2_1|eapply IHp2_2|eapply H|eapply H0];
    split; [reflexivity|assumption].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "every_inst_drop_consts" *)
Theorem every_inst_drop_consts : forall P cs ls (p : prog a),
  every_inst P (SmartSeq (drop_consts cs ls) p) = every_inst P p.
Proof.
  intros P cs ls p; rewrite every_inst_SmartSeq.
  assert (H : every_inst P (@drop_consts a cs ls) = true).
  { induction ls as [|x ls IH]; [reflexivity|]; cbn [drop_consts].
    destruct (lookup x cs); [rewrite every_inst_SmartSeq, IH|]; auto. }
  rewrite H; reflexivity.
Qed.

Ltac cfl_tac :=
  repeat (case_split; inv_eqs); inv_eqs;
  try match goal with
      | |- context [FST (const_fp_loop ?p ?c)] =>
          let E := fresh "E" in destruct (const_fp_loop p c) eqn:E; cbn [FST]
      end.

(** Galette-only: [const_fp_loop] form of [every_inst_const_fp]. *)
Lemma every_inst_const_fp_loop : forall P (p : prog a) cs p1 cs1,
  const_fp_loop p cs = (p1, cs1) -> every_inst P p -> every_inst P p1.
Proof.
  intros P p; induction p using prog_nested_ind; intros cs p' cs' Hc Hp;
    cbn [const_fp_loop] in Hc; cfl_tac.
  all: rewrite ?every_inst_drop_consts; cbn [every_inst] in *; bsplit; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "every_inst_const_fp" *)
Theorem every_inst_const_fp : forall P (prog : prog a),
  every_inst P prog -> every_inst P (const_fp prog).
Proof.
  intros P prog H; unfold const_fp; destruct (const_fp_loop prog LN) eqn:E; cbn [FST].
  eapply every_inst_const_fp_loop; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "try_if_hoist2_no_inst" *)
Theorem try_if_hoist2_no_inst : forall P N0 (p1 interm dummy p2 p3 : prog a),
  try_if_hoist2 N0 p1 interm dummy p2 = Some p3 ->
  every_inst P p1 -> every_inst P interm -> every_inst P p2 -> every_inst P p3.
Proof.
  intros P N0 p1; revert N0; induction p1 using prog_nested_ind;
    intros N0 interm dummy p2 p3 Hh H1 Hi H2; cbn [try_if_hoist2] in Hh;
    destruct (N0 =? 0); try discriminate Hh.
  - destruct (dest_If p1_2) as [[c' [l' [r' [b1 b2]]]]|] eqn:E.
    + apply dest_If_thm in E; subst p1_2.
      destruct (_ =? 0) in Hh; [discriminate Hh|].
      destruct (negb _) in Hh; [discriminate Hh|]. inv_eqs.
      cbn [every_inst] in *; bsplit; auto.
      apply every_inst_const_fp; cbn [every_inst]; bsplit; auto.
    + destruct (is_simple p1_2) eqn:S; [|discriminate Hh].
      cbn [every_inst] in H1; bsplit.
      eapply IHp1_1; eauto. cbn [every_inst]; bsplit; auto.
  - destruct (_ =? 0) in Hh; [discriminate Hh|].
    destruct (negb _) in Hh; [discriminate Hh|]. inv_eqs.
    cbn [every_inst] in *; bsplit.
    apply every_inst_const_fp; cbn [every_inst]; bsplit; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "simp_duplicate_if_no_inst" *)
Theorem simp_duplicate_if_no_inst : forall P (p : prog a),
  every_inst P p -> every_inst P (simp_duplicate_if p).
Proof.
  intros P p; induction p using prog_nested_ind; intros Hp; cbn [simp_duplicate_if];
    cbn [every_inst] in *; bsplit; eauto.
  all: try (destruct ret as [[? [? [? [? ?]]]]|]; [destruct h as [[? [? [? ?]]]|]|];
            cbn [every_inst] in *; bsplit; eauto; fail).
  destruct (try_if_hoist1 (simp_duplicate_if p1) (simp_duplicate_if p2)) as [p3|] eqn:T.
  - apply Seq_assoc_no_inst; split; [reflexivity|].
    unfold try_if_hoist1 in T.
    destruct (dest_If (simp_duplicate_if p2)) as [[c [l [r [b1 b2]]]]|] eqn:D; [|discriminate T].
    eapply try_if_hoist2_no_inst; unfold is_true in *; eauto.
  - cbn [every_inst]; bsplit; auto.
Qed.

(** Galette-only: [push_out_if_aux] form of [simp_push_out_if_no_inst]. *)
Lemma push_out_if_aux_no_inst : forall P (p : prog a),
  every_inst P p -> every_inst P (FST (push_out_if_aux p)).
Proof.
  intros P p; induction p using prog_nested_ind; intros Hp; cbn [push_out_if_aux];
    cbn [every_inst] in *; bsplit; eauto.
  all: repeat (case_split; inv_eqs); cbn [FST every_inst] in *; bsplit; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "simp_push_out_if_no_inst" *)
Theorem simp_push_out_if_no_inst : forall P (p : prog a),
  every_inst P p -> every_inst P (push_out_if p).
Proof. exact push_out_if_aux_no_inst. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "compile_exp_no_inst" *)
Theorem compile_exp_no_inst : forall P (prog : prog a),
  every_inst P prog -> every_inst P (word_simp.compile_exp prog).
Proof.
  intros P prog H; unfold word_simp.compile_exp.
  apply simp_push_out_if_no_inst, simp_duplicate_if_no_inst, every_inst_const_fp,
    Seq_assoc_no_inst; split; [reflexivity|exact H].
Qed.

(** *** not_created_subprogs *)

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "not_created_subprogs_SmartSeq" *)
Theorem not_created_subprogs_SmartSeq : forall P (p1 p2 : prog a),
  not_created_subprogs P (SmartSeq p1 p2) <->
  (not_created_subprogs P p1 /\ not_created_subprogs P p2).
Proof. intros P [] p2; cbn [SmartSeq not_created_subprogs]; tauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "not_created_subprogs_Seq_assoc" *)
Theorem not_created_subprogs_Seq_assoc : forall P (p1 p2 : prog a),
  not_created_subprogs P (Seq_assoc p1 p2) <->
  (not_created_subprogs P p1 /\ not_created_subprogs P p2).
Proof.
  intros P p1 p2; revert p1; induction p2 using prog_nested_ind; intros p0;
    cbn [Seq_assoc]; rewrite ?not_created_subprogs_SmartSeq; cbn [not_created_subprogs];
    try tauto.
  - rewrite IHp2; cbn [not_created_subprogs]; tauto.
  - destruct ret as [[? [? [? [? ?]]]]|], h as [[? [? [? ?]]]|];
      cbn [not_created_subprogs] in *; rewrite ?H, ?H0; cbn [not_created_subprogs]; tauto.
  - rewrite IHp2_2, IHp2_1; cbn [not_created_subprogs]; tauto.
  - rewrite IHp2_1, IHp2_2; cbn [not_created_subprogs]; tauto.
  - rewrite IHp2; cbn [not_created_subprogs]; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "not_created_subprogs_drop_consts" *)
Theorem not_created_subprogs_drop_consts : forall P cs ls (p : prog a),
  not_created_subprogs P (SmartSeq (drop_consts cs ls) p) <-> not_created_subprogs P p.
Proof.
  intros P cs ls p; rewrite not_created_subprogs_SmartSeq.
  assert (H : not_created_subprogs P (@drop_consts a cs ls)).
  { induction ls as [|x ls IH]; [exact Logic.I|]; cbn [drop_consts].
    destruct (lookup x cs); [rewrite not_created_subprogs_SmartSeq|]; cbn; auto. }
  tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "not_created_subprogs_const_fp_loop" *)
Theorem not_created_subprogs_const_fp_loop : forall P (p : prog a) cs p1 cs1,
  const_fp_loop p cs = (p1, cs1) ->
  not_created_subprogs P p -> not_created_subprogs P p1.
Proof.
  intros P p; induction p using prog_nested_ind; intros cs p' cs' Hc Hp;
    cbn [const_fp_loop] in Hc; cfl_tac.
  all: rewrite ?not_created_subprogs_drop_consts; cbn [not_created_subprogs] in *;
    intuition eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "not_created_subprogs_const_fp" *)
Theorem not_created_subprogs_const_fp : forall P (p : prog a),
  not_created_subprogs P p -> not_created_subprogs P (const_fp p).
Proof.
  intros P p H; unfold const_fp; destruct (const_fp_loop p LN) eqn:E; cbn [FST].
  eapply not_created_subprogs_const_fp_loop; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "not_created_subprogs_hoist2" *)
Theorem not_created_subprogs_hoist2 : forall P N0 (p1 interm dummy p2 p3 : prog a),
  try_if_hoist2 N0 p1 interm dummy p2 = Some p3 ->
  not_created_subprogs P p1 -> not_created_subprogs P interm ->
  not_created_subprogs P p2 -> not_created_subprogs P p3.
Proof.
  intros P N0 p1; revert N0; induction p1 using prog_nested_ind;
    intros N0 interm dummy p2 p3 Hh H1 Hi H2; cbn [try_if_hoist2] in Hh;
    destruct (N0 =? 0); try discriminate Hh.
  - destruct (dest_If p1_2) as [[c' [l' [r' [b1 b2]]]]|] eqn:E.
    + apply dest_If_thm in E; subst p1_2.
      destruct (_ =? 0) in Hh; [discriminate Hh|].
      destruct (negb _) in Hh; [discriminate Hh|]. inv_eqs.
      cbn [not_created_subprogs] in *; intuition.
      apply not_created_subprogs_const_fp; cbn [not_created_subprogs]; tauto.
    + destruct (is_simple p1_2) eqn:S; [|discriminate Hh].
      cbn [not_created_subprogs] in H1.
      eapply IHp1_1; eauto; cbn [not_created_subprogs]; tauto.
  - destruct (_ =? 0) in Hh; [discriminate Hh|].
    destruct (negb _) in Hh; [discriminate Hh|]. inv_eqs.
    cbn [not_created_subprogs] in *.
    apply not_created_subprogs_const_fp; cbn [not_created_subprogs]; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "not_created_subprogs_simp_duplicate_if" *)
Theorem not_created_subprogs_simp_duplicate_if : forall P (p : prog a),
  not_created_subprogs P p -> not_created_subprogs P (simp_duplicate_if p).
Proof.
  intros P p; induction p using prog_nested_ind; intros Hp; cbn [simp_duplicate_if];
    cbn [not_created_subprogs] in *; try tauto.
  all: try (destruct ret as [[? [? [? [? ?]]]]|], h as [[? [? [? ?]]]|];
            cbn [not_created_subprogs] in *; tauto).
  destruct (try_if_hoist1 (simp_duplicate_if p1) (simp_duplicate_if p2)) as [p3|] eqn:T.
  - apply not_created_subprogs_Seq_assoc; split; [exact Logic.I|].
    unfold try_if_hoist1 in T.
    destruct (dest_If (simp_duplicate_if p2)) as [[c [l [r [b1 b2]]]]|] eqn:D; [|discriminate T].
    eapply not_created_subprogs_hoist2; eauto; first [exact Logic.I|tauto].
  - cbn [not_created_subprogs]; tauto.
Qed.

(** Galette-only: [push_out_if_aux] form of [not_created_subprogs_push_out_if]. *)
Lemma not_created_subprogs_push_out_if_aux : forall P (p : prog a),
  not_created_subprogs P (FST (push_out_if_aux p)) <-> not_created_subprogs P p.
Proof.
  intros P p; induction p using prog_nested_ind; cbn [push_out_if_aux]; try tauto.
  all: repeat (case_split; inv_eqs); cbn [FST not_created_subprogs] in *; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "not_created_subprogs_push_out_if" *)
Theorem not_created_subprogs_push_out_if : forall P (p : prog a),
  not_created_subprogs P (push_out_if p) <-> not_created_subprogs P p.
Proof. exact not_created_subprogs_push_out_if_aux. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "compile_exp_not_created_subprogs" *)
Theorem compile_exp_not_created_subprogs : forall P (p : prog a),
  not_created_subprogs P p -> not_created_subprogs P (word_simp.compile_exp p).
Proof.
  intros P p H; unfold word_simp.compile_exp.
  apply not_created_subprogs_push_out_if, not_created_subprogs_simp_duplicate_if,
    not_created_subprogs_const_fp, not_created_subprogs_Seq_assoc; split; [exact Logic.I|exact H].
Qed.

(** *** code labels and handlers *)

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_SmartSeq" *)
Theorem word_get_code_labels_SmartSeq : forall (p q : prog a),
  get_code_labels (SmartSeq p q) = get_code_labels p UNION get_code_labels q.
Proof. intros [] q; cbn [SmartSeq get_code_labels]; try reflexivity; set_eq. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_drop_consts" *)
Theorem word_get_code_labels_drop_consts : forall l args,
  get_code_labels (@drop_consts a l args) = {}.
Proof.
  intros l args; induction args as [|x args IH]; [reflexivity|]; cbn [drop_consts].
  destruct (lookup x l); [rewrite word_get_code_labels_SmartSeq, IH; cbn; set_eq|exact IH].
Qed.

(** Galette-only: [const_fp_loop] form of [word_get_code_labels_const_fp_loop]. *)
Lemma get_code_labels_const_fp_loop_eq : forall (p : prog a) cs p1 cs1,
  const_fp_loop p cs = (p1, cs1) -> get_code_labels p1 SUBSET get_code_labels p.
Proof.
  intros p; induction p using prog_nested_ind; intros cs p' cs' Hc;
    cbn [const_fp_loop] in Hc; cfl_tac; use_ih.
  all: rewrite ?word_get_code_labels_SmartSeq, ?word_get_code_labels_drop_consts;
    cbn [get_code_labels] in *; try (sets; fail).
  all: try (match goal with E : const_fp_loop ?q ?c = _, IH : forall c x y, const_fp_loop ?q c = _ -> _ |- _ =>
              specialize (IH _ _ _ E) end; sets).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_const_fp_loop" *)
Theorem word_get_code_labels_const_fp_loop : forall (p : prog a) l,
  get_code_labels (FST (const_fp_loop p l)) SUBSET get_code_labels p.
Proof.
  intros p l; destruct (const_fp_loop p l) eqn:E; cbn [FST].
  eapply get_code_labels_const_fp_loop_eq; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_SmartSeq" *)
Theorem word_good_handlers_SmartSeq : forall n (p q : prog a),
  good_handlers n (SmartSeq p q) = (good_handlers n p && good_handlers n q).
Proof. intros n [] q; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_drop_consts" *)
Theorem word_good_handlers_drop_consts : forall n l args,
  good_handlers n (@drop_consts a l args).
Proof.
  intros n l args; induction args as [|x args IH]; [reflexivity|]; cbn [drop_consts].
  destruct (lookup x l); [rewrite word_good_handlers_SmartSeq; bsplit|]; auto.
Qed.

(** Galette-only: [const_fp_loop] form of [word_good_handlers_const_fp_loop]. *)
Lemma good_handlers_const_fp_loop_eq : forall n (p : prog a) cs p1 cs1,
  const_fp_loop p cs = (p1, cs1) -> good_handlers n p -> good_handlers n p1.
Proof.
  intros n p; induction p using prog_nested_ind; intros cs p' cs' Hc Hp;
    cbn [const_fp_loop] in Hc; cfl_tac.
  all: rewrite ?word_good_handlers_SmartSeq; cbn [good_handlers] in *; bsplit;
    eauto; apply word_good_handlers_drop_consts.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_const_fp_loop" *)
Theorem word_good_handlers_const_fp_loop : forall n (p : prog a) l,
  good_handlers n p -> good_handlers n (FST (const_fp_loop p l)).
Proof.
  intros n p l H; destruct (const_fp_loop p l) eqn:E; cbn [FST].
  eapply good_handlers_const_fp_loop_eq; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_Seq_assoc" *)
Theorem word_get_code_labels_Seq_assoc : forall (p1 p2 : prog a),
  get_code_labels (Seq_assoc p1 p2) = get_code_labels p1 UNION get_code_labels p2.
Proof.
  intros p1 p2; revert p1; induction p2 using prog_nested_ind; intros p0;
    cbn [Seq_assoc]; rewrite ?word_get_code_labels_SmartSeq; cbn [get_code_labels];
    try (set_eq; fail).
  all: try (destruct ret as [[? [? [? [? ?]]]]|], h as [[? [? [? ?]]]|];
            cbn [get_code_labels] in *; rewrite ?H, ?H0; cbn [get_code_labels]; set_eq).
  all: rewrite ?IHp2, ?IHp2_2, ?IHp2_1; cbn [get_code_labels]; set_eq.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_Seq_assoc" *)
Theorem word_good_handlers_Seq_assoc : forall n (p1 p2 : prog a),
  good_handlers n (Seq_assoc p1 p2) = (good_handlers n p1 && good_handlers n p2).
Proof.
  intros n p1 p2; revert p1; induction p2 using prog_nested_ind; intros p0;
    cbn [Seq_assoc]; rewrite ?word_good_handlers_SmartSeq; cbn [good_handlers];
    try btauto.
  all: try (destruct ret as [[? [? [? [? ?]]]]|], h as [[? [? [? ?]]]|];
            cbn [good_handlers] in *; rewrite ?H, ?H0; cbn [good_handlers]; btauto).
  all: rewrite ?IHp2, ?IHp2_2, ?IHp2_1; cbn [good_handlers]; btauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_try_if_hoist2" *)
Theorem word_good_handlers_try_if_hoist2 : forall n N0 (p1 interm dummy p2 p3 : prog a),
  try_if_hoist2 N0 p1 interm dummy p2 = Some p3 ->
  good_handlers n p1 /\ good_handlers n p2 /\ good_handlers n interm ->
  good_handlers n p3.
Proof.
  intros n N0 p1; revert N0; induction p1 using prog_nested_ind;
    intros N0 interm dummy p2 p3 Hh [H1 [H2 Hi]]; cbn [try_if_hoist2] in Hh;
    destruct (N0 =? 0); try discriminate Hh.
  - destruct (dest_If p1_2) as [[c' [l' [r' [b1 b2]]]]|] eqn:E.
    + apply dest_If_thm in E; subst p1_2.
      destruct (_ =? 0) in Hh; [discriminate Hh|].
      destruct (negb _) in Hh; [discriminate Hh|]. inv_eqs.
      cbn [good_handlers] in *; bsplit; auto.
      apply word_good_handlers_const_fp_loop; cbn [good_handlers]; bsplit; auto.
    + destruct (is_simple p1_2) eqn:S; [|discriminate Hh].
      cbn [good_handlers] in H1; bsplit.
      eapply IHp1_1; [exact Hh|]. cbn [good_handlers]; bsplit; auto.
  - destruct (_ =? 0) in Hh; [discriminate Hh|].
    destruct (negb _) in Hh; [discriminate Hh|]. inv_eqs.
    cbn [good_handlers] in *; bsplit.
    apply word_good_handlers_const_fp_loop; cbn [good_handlers]; bsplit; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_simp_duplicate_if" *)
Theorem word_good_handlers_simp_duplicate_if : forall n (p : prog a),
  good_handlers n p -> good_handlers n (simp_duplicate_if p).
Proof.
  intros n p; induction p using prog_nested_ind; intros Hp; cbn [simp_duplicate_if];
    cbn [good_handlers] in *; bsplit; eauto.
  all: try (destruct ret as [[? [? [? [? ?]]]]|]; [destruct h as [[? [? [? ?]]]|]|];
            cbn [good_handlers] in *; bsplit; eauto; fail).
  destruct (try_if_hoist1 (simp_duplicate_if p1) (simp_duplicate_if p2)) as [p3|] eqn:T.
  - rewrite word_good_handlers_Seq_assoc; cbn [good_handlers andb].
    unfold try_if_hoist1 in T.
    destruct (dest_If (simp_duplicate_if p2)) as [[c [l [r [b1 b2]]]]|] eqn:D; [|discriminate T].
    eapply word_good_handlers_try_if_hoist2; [exact T|]; bsplit; auto.
  - cbn [good_handlers]; bsplit; auto.
Qed.

(** Galette-only: [push_out_if_aux] form of [word_good_handlers_simp_push_out_if]. *)
Lemma good_handlers_push_out_if_aux : forall n (p : prog a),
  good_handlers n p -> good_handlers n (FST (push_out_if_aux p)).
Proof.
  intros n p; induction p using prog_nested_ind; intros Hp; cbn [push_out_if_aux];
    cbn [good_handlers] in *; bsplit; eauto.
  all: repeat (case_split; inv_eqs); cbn [FST good_handlers] in *; bsplit; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_simp_push_out_if" *)
Theorem word_good_handlers_simp_push_out_if : forall n (p : prog a),
  good_handlers n p -> good_handlers n (push_out_if p).
Proof. exact good_handlers_push_out_if_aux. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_word_simp" *)
Theorem word_good_handlers_word_simp : forall n (ps : prog a),
  good_handlers n ps -> good_handlers n (word_simp.compile_exp ps).
Proof.
  intros n ps H; unfold word_simp.compile_exp.
  apply word_good_handlers_simp_push_out_if, word_good_handlers_simp_duplicate_if.
  unfold const_fp; apply word_good_handlers_const_fp_loop.
  rewrite word_good_handlers_Seq_assoc; exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_try_if_hoist2" *)
Theorem word_get_code_labels_try_if_hoist2 : forall N0 (p1 interm dummy p2 p3 : prog a),
  try_if_hoist2 N0 p1 interm dummy p2 = Some p3 ->
  get_code_labels p3 SUBSET
  (get_code_labels p1 UNION get_code_labels interm UNION get_code_labels p2).
Proof.
  intros N0 p1; revert N0; induction p1 using prog_nested_ind;
    intros N0 interm dummy p2 p3 Hh; cbn [try_if_hoist2] in Hh;
    destruct (N0 =? 0); try discriminate Hh.
  - destruct (dest_If p1_2) as [[c' [l' [r' [b1 b2]]]]|] eqn:E.
    + apply dest_If_thm in E; subst p1_2.
      destruct (_ =? 0) in Hh; [discriminate Hh|].
      destruct (negb _) in Hh; [discriminate Hh|]. inv_eqs.
      pose proof (word_get_code_labels_const_fp_loop
        (If c' l' r' (Seq (Seq b1 interm) p2) (Seq (Seq b2 interm) p2)) LN) as T.
      unfold const_fp; cbn [get_code_labels] in *; sets.
    + destruct (is_simple p1_2) eqn:S; [|discriminate Hh].
      specialize (IHp1_1 _ _ _ _ _ Hh). cbn [get_code_labels] in *; sets.
  - destruct (_ =? 0) in Hh; [discriminate Hh|].
    destruct (negb _) in Hh; [discriminate Hh|]. inv_eqs.
    pose proof (word_get_code_labels_const_fp_loop
      (If c r ri (Seq (Seq p1_1 interm) p2) (Seq (Seq p1_2 interm) p2)) LN) as T.
    unfold const_fp; cbn [get_code_labels] in *; sets.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_simp_duplicate_if" *)
Theorem word_get_code_labels_simp_duplicate_if : forall (p : prog a),
  get_code_labels (simp_duplicate_if p) SUBSET get_code_labels p.
Proof.
  intros p; induction p using prog_nested_ind; cbn [simp_duplicate_if];
    cbn [get_code_labels] in *; try (sets; fail).
  all: try (destruct ret as [[? [? [? [? ?]]]]|], h as [[? [? [? ?]]]|];
            cbn [get_code_labels] in *; sets; fail).
  destruct (try_if_hoist1 (simp_duplicate_if p1) (simp_duplicate_if p2)) as [p3|] eqn:T.
  - rewrite word_get_code_labels_Seq_assoc; cbn [get_code_labels].
    unfold try_if_hoist1 in T.
    destruct (dest_If (simp_duplicate_if p2)) as [[c [l [r [b1 b2]]]]|] eqn:D; [|discriminate T].
    apply word_get_code_labels_try_if_hoist2 in T; cbn [get_code_labels] in T; sets.
  - cbn [get_code_labels]; sets.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_push_out_if" *)
Theorem word_get_code_labels_push_out_if : forall (p : prog a),
  get_code_labels (push_out_if p) SUBSET get_code_labels p.
Proof.
  unfold push_out_if; intros p; induction p using prog_nested_ind; cbn [push_out_if_aux];
    cbn [get_code_labels] in *; try (sets; fail).
  all: repeat (case_split; inv_eqs); cbn [FST get_code_labels] in *; sets.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_word_simp" *)
Theorem word_get_code_labels_word_simp : forall (ps : prog a),
  get_code_labels (word_simp.compile_exp ps) SUBSET get_code_labels ps.
Proof.
  intros ps; unfold word_simp.compile_exp.
  pose proof (word_get_code_labels_push_out_if
    (simp_duplicate_if (const_fp (Seq_assoc Skip ps)))) as T1.
  pose proof (word_get_code_labels_simp_duplicate_if (const_fp (Seq_assoc Skip ps))) as T2.
  pose proof (word_get_code_labels_const_fp_loop (Seq_assoc Skip ps) LN) as T3.
  rewrite word_get_code_labels_Seq_assoc in T3. unfold const_fp in *; cbn [get_code_labels] in *.
  sets.
Qed.

End Simp2.

(** ** inst_select *)

Section Inst.
Context {a : N}.

(** Galette-only: a size of expressions, for an induction principle that
    covers the nested recursive calls of [inst_select_exp]. *)
Fixpoint esize (e : exp a) : nat :=
  match e with
  | Load e => Datatypes.S (esize e)
  | Op _ l => Datatypes.S (list_sum (List.map esize l))
  | Shift _ e1 e2 => Datatypes.S (esize e1 + esize e2)
  | _ => 1
  end.

Lemma exp_deep_ind (P : exp a -> Prop) :
  (forall e, (forall e', (esize e' < esize e)%nat -> P e') -> P e) -> forall e, P e.
Proof.
  intros H e. remember (esize e) as n eqn:Hn. revert e Hn.
  induction n as [n IH] using (well_founded_induction lt_wf); intros e Hn; subst n.
  apply H; intros e' Hlt; eapply IH; eauto.
Qed.

Ltac isel_ih :=
  repeat match goal with
  | IH : forall e', (esize e' < esize ?e)%nat -> _ |- context [inst_select_exp ?c ?t1 ?t2 ?x] =>
      lazymatch goal with
      | _ : context [inst_select_exp c t1 t2 x] |- _ => fail
      | _ => pose proof (IH x ltac:(cbn; lia) t1 t2)
      end
  end.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "inst_select_exp_no_lab" *)
Theorem inst_select_exp_no_lab : forall c tar temp (exp : exp a),
  extract_labels (inst_select_exp c tar temp exp) = [].
Proof.
  intros c tar temp e; revert tar temp; induction e using exp_deep_ind; intros tar temp.
  destruct e; cbn [inst_select_exp]; repeat case_split; isel_ih; cbn [extract_labels] in *;
    repeat match goal with H : ?l = [] |- context [?l] => rewrite H end; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "inst_select_lab_pres" *)
Theorem inst_select_lab_pres : forall c temp (prog : prog a),
  extract_labels prog = extract_labels (inst_select c temp prog).
Proof.
  intros c temp prog; induction prog using prog_nested_ind; cbn [inst_select];
    repeat case_split; cbn [extract_labels] in *;
    rewrite ?inst_select_exp_no_lab; try reflexivity.
  all: rewrite <- ?IHprog, <- ?IHprog1, <- ?IHprog2, <- ?H, <- ?H0; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "inst_select_exp_flat_exp_conventions" *)
Theorem inst_select_exp_flat_exp_conventions : forall c tar temp (exp : exp a),
  flat_exp_conventions (inst_select_exp c tar temp exp).
Proof.
  intros c tar temp e; revert tar temp; induction e using exp_deep_ind; intros tar temp.
  destruct e; cbn [inst_select_exp]; repeat case_split; isel_ih;
    cbn [flat_exp_conventions] in *; bsplit; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "inst_select_flat_exp_conventions" *)
Theorem inst_select_flat_exp_conventions : forall c temp (prog : prog a),
  flat_exp_conventions (inst_select c temp prog).
Proof.
  intros c temp prog; induction prog using prog_nested_ind; cbn [inst_select];
    repeat case_split; cbn [flat_exp_conventions] in *; bsplit; auto;
    apply inst_select_exp_flat_exp_conventions.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "inst_select_exp_not_created_subprogs" *)
Theorem inst_select_exp_not_created_subprogs : forall P c c' n (exp : exp a),
  not_created_subprogs P (inst_select_exp c c' n exp).
Proof.
  intros P c tar temp e; revert tar temp; induction e using exp_deep_ind; intros tar temp.
  destruct e; cbn [inst_select_exp]; repeat case_split; isel_ih;
    cbn [not_created_subprogs] in *; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "inst_select_not_created_subprogs" *)
Theorem inst_select_not_created_subprogs : forall P c n (prog : prog a),
  not_created_subprogs P prog -> not_created_subprogs P (inst_select c n prog).
Proof.
  intros P c temp prog; induction prog using prog_nested_ind; intros Hp; cbn [inst_select];
    repeat case_split; cbn [not_created_subprogs] in *;
    repeat split; try tauto; try apply inst_select_exp_not_created_subprogs.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "inst_select_exp_full_inst_ok_less" *)
Theorem inst_select_exp_full_inst_ok_less : forall c tar temp (exp : exp a),
  addr_offset_ok c (n2w 0) -> full_inst_ok_less c (inst_select_exp c tar temp exp).
Proof.
  intros c tar temp e Ha; revert tar temp; induction e using exp_deep_ind; intros tar temp.
  destruct e; cbn [inst_select_exp]; repeat case_split; isel_ih;
    cbn [full_inst_ok_less inst_ok_less] in *; bsplit; auto.
  all: rewrite n2w_w2n; auto.
  match goal with Z : (w2n ?w =? 0) = false |- _ =>
    rewrite (bd_false (w = n2w 0)); [reflexivity|] end.
  intros ->. rewrite w2n_n2w, N.Div0.mod_0_l in *; discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "inst_select_full_inst_ok_less" *)
Theorem inst_select_full_inst_ok_less : forall c temp (prog : prog a),
  addr_offset_ok c (n2w 0) /\ hw_offset_ok c (n2w 0) /\ byte_offset_ok c (n2w 0) /\ every_inst (inst_ok_less c) prog ->
  full_inst_ok_less c (inst_select c temp prog).
Proof.
  intros c temp prog [Ha [Hh [Hb Hp]]]; induction prog using prog_nested_ind;
    cbn [inst_select]; repeat case_split; cbn [full_inst_ok_less every_inst] in *; bsplit;
    eauto; try (apply inst_select_exp_full_inst_ok_less; exact Ha).
  all: try (unfold inst_ok_less; cbn; bsplit; auto; fail).
  all: try (destruct op; cbn in *; bsplit; auto; fail).
  all: destruct op; cbn [exp_to_addr MEM] in *; bd_simp; cbn in *;
    rewrite ?orb_false_r, ?andb_true_r in *; bsplit; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_inst_select_exp" *)
Theorem word_get_code_labels_inst_select_exp : forall c tar temp (exp : exp a),
  get_code_labels (inst_select_exp c tar temp exp) = {}.
Proof.
  intros c tar temp e; revert tar temp; induction e using exp_deep_ind; intros tar temp.
  destruct e; cbn [inst_select_exp]; repeat case_split; isel_ih; cbn [get_code_labels] in *;
    repeat match goal with H : get_code_labels _ = {} |- _ => rewrite H; clear H end;
    try reflexivity; set_eq.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_inst_select" *)
Theorem word_get_code_labels_inst_select : forall ac v (ps : prog a),
  get_code_labels (inst_select ac v ps) = get_code_labels ps.
Proof.
  intros ac v ps; induction ps using prog_nested_ind; cbn [inst_select];
    repeat case_split; cbn [get_code_labels] in *;
    rewrite ?word_get_code_labels_inst_select_exp; try reflexivity.
  all: rewrite ?IHps, ?IHps1, ?IHps2, ?H, ?H0; try reflexivity; set_eq.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_inst_select_exp" *)
Theorem word_good_handlers_inst_select_exp : forall n c tar temp (exp : exp a),
  good_handlers n (inst_select_exp c tar temp exp).
Proof.
  intros n c tar temp e; revert tar temp; induction e using exp_deep_ind; intros tar temp.
  destruct e; cbn [inst_select_exp]; repeat case_split; isel_ih; cbn [good_handlers] in *;
    bsplit; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_inst_select" *)
Theorem word_good_handlers_inst_select : forall n ac v (ps : prog a),
  good_handlers n (inst_select ac v ps) = good_handlers n ps.
Proof.
  intros n ac v ps; induction ps using prog_nested_ind; cbn [inst_select];
    repeat case_split; cbn [good_handlers andb] in *;
    rewrite ?word_good_handlers_inst_select_exp; try reflexivity.
  all: rewrite ?IHps, ?IHps1, ?IHps2, ?H, ?H0; try reflexivity.
  all: pose proof (word_good_handlers_inst_select_exp n) as G; unfold is_true in G; rewrite ?G;
    reflexivity.
Qed.

End Inst.

(** ** full_ssa_cc_trans *)

Section SSA.
Context {a : N}.

(** Galette-only: programs built from [Skip], [Inst], [Move] and [Seq]; the
    administrative code that SSA introduces is of this form. *)
Inductive simple_prog : prog a -> Prop :=
| sp_Skip : simple_prog Skip
| sp_Inst i : simple_prog (Inst i)
| sp_Move pri l : simple_prog (Move pri l)
| sp_Seq p q : simple_prog p -> simple_prog q -> simple_prog (Seq p q).
Local Hint Constructors simple_prog : core.

Lemma simple_labels p : simple_prog p -> extract_labels p = [].
Proof. induction 1; cbn; rewrite ?IHsimple_prog1, ?IHsimple_prog2; reflexivity. Qed.
Lemma simple_code_labels p : simple_prog p -> get_code_labels p = {}.
Proof.
  induction 1; cbn; rewrite ?IHsimple_prog1, ?IHsimple_prog2; try reflexivity; set_eq.
Qed.
Lemma simple_good_handlers n p : simple_prog p -> good_handlers n p = true.
Proof. induction 1; cbn; rewrite ?IHsimple_prog1, ?IHsimple_prog2; reflexivity. Qed.
Lemma simple_flat p : simple_prog p -> flat_exp_conventions p = true.
Proof. induction 1; cbn; rewrite ?IHsimple_prog1, ?IHsimple_prog2; reflexivity. Qed.
Lemma simple_wf_cutsets p : simple_prog p -> wf_cutsets p = true.
Proof. induction 1; cbn; rewrite ?IHsimple_prog1, ?IHsimple_prog2; reflexivity. Qed.
Lemma simple_ncs P p : simple_prog p -> not_created_subprogs P p.
Proof. induction 1; cbn; auto. Qed.

Lemma fake_seq_simple (ls : list N) :
  simple_prog (FOLDR Seq Skip (MAP (fun r => @fake_move a r) ls)).
Proof. induction ls; cbn; unfold fake_move; auto. Qed.

Lemma fake_moves_simple : forall prio (ls : list N) sl sr na d e r,
  @fake_moves a prio ls sl sr na = (d, (e, r)) -> simple_prog d /\ simple_prog e.
Proof.
  intros prio ls; induction ls as [|x ls IH]; intros sl sr na d e r H; cbn [fake_moves] in H.
  - inv_eqs; auto.
  - destruct (fake_moves prio ls sl sr na) as [d0 [e0 [n0 [s1 s2]]]] eqn:E.
    destruct (IH _ _ _ _ _ _ E) as [H1 H2].
    repeat (case_split; inv_eqs); inv_eqs; unfold fake_move; auto.
Qed.

Lemma ssa_reconcile_simple cur tgt ns : simple_prog (@ssa_reconcile a cur tgt ns).
Proof. unfold ssa_reconcile; case_split; auto. Qed.

Lemma lnvrm_simple : forall ssa n ls p r,
  @list_next_var_rename_move a ssa n ls = (p, r) -> simple_prog p.
Proof.
  intros ssa n ls p r H; unfold list_next_var_rename_move in H.
  destruct (list_next_var_rename ls ssa n) as [x [y z]]; inv_eqs; auto.
Qed.

Lemma loop_setup_simple : forall names exit_names ssa na p r,
  @loop_setup a names exit_names ssa na = (p, r) -> simple_prog p.
Proof.
  intros names exit_names ssa na p r H; unfold loop_setup in H.
  destruct (list_next_var_rename _ ssa na) as [x [y z]].
  destruct (list_next_var_rename_move y z _) as [m [r1 r2]] eqn:E; inv_eqs.
  constructor; [apply fake_seq_simple|eapply lnvrm_simple; eauto].
Qed.

Lemma fix_inconsistencies_simple : forall prio sl sr na p q r,
  @fix_inconsistencies a prio sl sr na = (p, (q, r)) -> simple_prog p /\ simple_prog q.
Proof.
  intros prio sl sr na p q r H; unfold fix_inconsistencies in H.
  destruct (word_alloc.merge_moves _ sl sr na) as [l1 [l2 [n1 [s1 s2]]]].
  destruct (fake_moves prio _ s1 s2 n1) as [d [e [n2 [s3 s4]]]] eqn:E; inv_eqs.
  destruct (fake_moves_simple _ _ _ _ _ _ _ _ E); auto.
Qed.

Lemma ssa_cc_trans_inst_simple : forall i ssa na p r,
  @ssa_cc_trans_inst a i ssa na = (p, r) -> simple_prog p.
Proof.
  intros i ssa na p r H; unfold ssa_cc_trans_inst in H;
    repeat (case_split; inv_eqs); inv_eqs; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "fake_moves_no_labs" *)
Theorem fake_moves_no_labs : forall prio (ls : list N) a0 b c (d e : prog a) f g h,
  fake_moves prio ls a0 b c = (d, (e, (f, (g, h)))) ->
  extract_labels d = [] /\ extract_labels e = [].
Proof.
  intros; edestruct fake_moves_simple; eauto; split; apply simple_labels; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "fake_seq_no_labs" *)
Theorem fake_seq_no_labs : forall (ls : list N),
  extract_labels (FOLDR Seq Skip (MAP (fun r => @fake_move a r) ls)) = [].
Proof. intros; apply simple_labels, fake_seq_simple. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "fake_seq_get_code_labels" *)
Theorem fake_seq_get_code_labels : forall (ls : list N),
  get_code_labels (FOLDR Seq Skip (MAP (fun r => @fake_move a r) ls)) = {}.
Proof. intros; apply simple_code_labels, fake_seq_simple. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "fake_seq_good_handlers" *)
Theorem fake_seq_good_handlers : forall n (ls : list N),
  good_handlers n (FOLDR Seq Skip (MAP (fun r => @fake_move a r) ls)).
Proof. intros; apply simple_good_handlers, fake_seq_simple. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "fake_seq_flat_exp_conventions" *)
Theorem fake_seq_flat_exp_conventions : forall (ls : list N),
  flat_exp_conventions (FOLDR Seq Skip (MAP (fun r => @fake_move a r) ls)).
Proof. intros; apply simple_flat, fake_seq_simple. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "fake_seq_wf_cutsets" *)
Theorem fake_seq_wf_cutsets : forall (ls : list N),
  wf_cutsets (FOLDR Seq Skip (MAP (fun r => @fake_move a r) ls)).
Proof. intros; apply simple_wf_cutsets, fake_seq_simple. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "ssa_reconcile_no_labs" *)
Theorem ssa_reconcile_no_labs : forall cur_ssa tgt_ssa ns,
  extract_labels (@ssa_reconcile a cur_ssa tgt_ssa ns) = [].
Proof. intros; apply simple_labels, ssa_reconcile_simple. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "ssa_reconcile_get_code_labels" *)
Theorem ssa_reconcile_get_code_labels : forall cur_ssa tgt_ssa ns,
  get_code_labels (@ssa_reconcile a cur_ssa tgt_ssa ns) = {}.
Proof. intros; apply simple_code_labels, ssa_reconcile_simple. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "ssa_reconcile_good_handlers" *)
Theorem ssa_reconcile_good_handlers : forall n cur_ssa tgt_ssa ns,
  good_handlers n (@ssa_reconcile a cur_ssa tgt_ssa ns).
Proof. intros; apply simple_good_handlers, ssa_reconcile_simple. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "ssa_reconcile_flat_exp_conventions" *)
Theorem ssa_reconcile_flat_exp_conventions : forall cur_ssa tgt_ssa ns,
  flat_exp_conventions (@ssa_reconcile a cur_ssa tgt_ssa ns).
Proof. intros; apply simple_flat, ssa_reconcile_simple. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "ssa_reconcile_wf_cutsets" *)
Theorem ssa_reconcile_wf_cutsets : forall cur_ssa tgt_ssa ns,
  wf_cutsets (@ssa_reconcile a cur_ssa tgt_ssa ns).
Proof. intros; apply simple_wf_cutsets, ssa_reconcile_simple. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "loop_setup_no_labs" *)
Theorem loop_setup_no_labs : forall names exit_names ssa na (setup_prog : prog a) ssa' na',
  loop_setup names exit_names ssa na = (setup_prog, (ssa', na')) ->
  extract_labels setup_prog = [].
Proof. intros; eapply simple_labels, loop_setup_simple; eauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "loop_setup_get_code_labels" *)
Theorem loop_setup_get_code_labels : forall names exit_names ssa na (setup_prog : prog a) ssa' na',
  loop_setup names exit_names ssa na = (setup_prog, (ssa', na')) ->
  get_code_labels setup_prog = {}.
Proof. intros; eapply simple_code_labels, loop_setup_simple; eauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "loop_setup_good_handlers" *)
Theorem loop_setup_good_handlers : forall n names exit_names ssa na (setup_prog : prog a) ssa' na',
  loop_setup names exit_names ssa na = (setup_prog, (ssa', na')) ->
  good_handlers n setup_prog.
Proof. intros; eapply simple_good_handlers, loop_setup_simple; eauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "loop_setup_flat_exp_conventions" *)
Theorem loop_setup_flat_exp_conventions : forall names exit_names ssa na (setup_prog : prog a) ssa' na',
  loop_setup names exit_names ssa na = (setup_prog, (ssa', na')) ->
  flat_exp_conventions setup_prog.
Proof. intros; eapply simple_flat, loop_setup_simple; eauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "loop_setup_wf_cutsets" *)
Theorem loop_setup_wf_cutsets : forall names exit_names ssa na (setup_prog : prog a) ssa' na',
  loop_setup names exit_names ssa na = (setup_prog, (ssa', na')) ->
  wf_cutsets setup_prog.
Proof. intros; eapply simple_wf_cutsets, loop_setup_simple; eauto. Qed.

(** Galette-only: every administrative program that [ssa_cc_trans]
    introduces is simple. *)
Ltac ssa_simple :=
  repeat match goal with
  | E : ssa_cc_trans_inst _ _ _ = (?p, _) |- _ =>
      let S := fresh "S" in pose proof (ssa_cc_trans_inst_simple _ _ _ _ _ E) as S; clear E
  | E : list_next_var_rename_move _ _ _ = (?p, _) |- _ =>
      let S := fresh "S" in pose proof (lnvrm_simple _ _ _ _ _ E) as S; clear E
  | E : loop_setup _ _ _ _ = (?p, _) |- _ =>
      let S := fresh "S" in pose proof (loop_setup_simple _ _ _ _ _ _ E) as S; clear E
  | E : fix_inconsistencies _ _ _ _ = (?p, (?q, _)) |- _ =>
      let S := fresh "S" in pose proof (fix_inconsistencies_simple _ _ _ _ _ _ _ E) as S;
      destruct S; clear E
  end.

Ltac use_ih4 :=
  repeat match goal with
  | IH : forall s n l x y, ssa_cc_trans ?q s n l = (x, y) -> _,
    E : ssa_cc_trans ?q ?s0 ?n0 ?l0 = (?x0, ?y0) |- _ =>
      specialize (IH _ _ _ _ _ E)
  end.

Ltac ssa_tac :=
  repeat (case_split; inv_eqs); inv_eqs; ssa_simple; use_ih4.

(** Galette-only: [ssa_cc_trans] preserves the label list. *)
Lemma ssa_cc_trans_labels : forall (p : prog a) ssa na lt p' r,
  ssa_cc_trans p ssa na lt = (p', r) -> extract_labels p' = extract_labels p.
Proof.
  intros p; induction p using prog_nested_ind; intros ssa na lt p' rr Hc;
    cbn [ssa_cc_trans] in Hc; ssa_tac.
  all: cbn [extract_labels] in *;
    repeat match goal with S : simple_prog _ |- _ => rewrite (simple_labels _ S) in *; clear S end;
    rewrite ?ssa_reconcile_no_labs; cbn [app] in *; rewrite ?app_nil_r in *;
    try reflexivity; try congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "full_ssa_cc_trans_lab_pres" *)
Theorem full_ssa_cc_trans_lab_pres : forall (prog : prog a) n,
  extract_labels prog = extract_labels (full_ssa_cc_trans n prog).
Proof.
  intros prog n; unfold full_ssa_cc_trans, setup_ssa.
  destruct (list_next_var_rename _ _ _) as [x [y z]].
  destruct (ssa_cc_trans prog y z []) as [p' [r1 r2]] eqn:E; cbn [extract_labels app].
  symmetry; eapply ssa_cc_trans_labels; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "ssa_cc_trans_inst_not_created_subprogs" *)
Theorem ssa_cc_trans_inst_not_created_subprogs : forall P i ssa na (i' : prog a) ssa' na',
  ssa_cc_trans_inst i ssa na = (i', (ssa', na')) -> not_created_subprogs P i'.
Proof. intros; eapply simple_ncs, ssa_cc_trans_inst_simple; eauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "fake_moves_not_created_subprogs" *)
Theorem fake_moves_not_created_subprogs : forall P prio ls nL nR n (prog1 prog2 : prog a) n' ssa ssa',
  fake_moves prio ls nL nR n = (prog1, (prog2, (n', (ssa, ssa')))) ->
  not_created_subprogs P prog1 /\ not_created_subprogs P prog2.
Proof. intros; edestruct fake_moves_simple; eauto; split; apply simple_ncs; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "fake_seq_not_created_subprogs" *)
Theorem fake_seq_not_created_subprogs : forall P (ls : list N),
  not_created_subprogs P (FOLDR Seq Skip (MAP (fun r => @fake_move a r) ls)).
Proof. intros; apply simple_ncs, fake_seq_simple. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "loop_setup_not_created_subprogs" *)
Theorem loop_setup_not_created_subprogs : forall P names exit_names ssa na (setup_prog : prog a) ssa' na',
  loop_setup names exit_names ssa na = (setup_prog, (ssa', na')) ->
  not_created_subprogs P setup_prog.
Proof. intros; eapply simple_ncs, loop_setup_simple; eauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "ssa_cc_trans_not_created_subprogs" *)
Theorem ssa_cc_trans_not_created_subprogs : forall P (prog : prog a) ssa n lt prog' ssa' na,
  not_created_subprogs P prog /\ ssa_cc_trans prog ssa n lt = (prog', (ssa', na)) ->
  not_created_subprogs P prog'.
Proof.
  intros P prog ssa n lt prog' ssa' na [Hp Hc]; revert ssa n lt prog' ssa' na Hc.
  induction prog using prog_nested_ind; intros ssa n0 lt prog' ssa' na Hc;
    cbn [ssa_cc_trans] in Hc; repeat (case_split; inv_eqs); inv_eqs; ssa_simple.
  all: repeat match goal with
         | IH : not_created_subprogs ?P0 ?q -> forall s n l x y z, ssa_cc_trans ?q s n l = (x, (y, z)) -> _,
           E : ssa_cc_trans ?q _ _ _ = (_, (_, _)) |- _ =>
             cbn [not_created_subprogs] in Hp; specialize (IH ltac:(tauto) _ _ _ _ _ _ E)
         end.
  all: repeat match goal with S : simple_prog ?q |- _ =>
         pose proof (simple_ncs P _ S); clear S end.
  all: cbn [not_created_subprogs] in *; try tauto.
  all: repeat split; try tauto; apply simple_ncs, ssa_reconcile_simple.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "setup_ssa_not_created_subprogs" *)
Theorem setup_ssa_not_created_subprogs : forall P n v (prog mov : prog a) ssa na,
  not_created_subprogs P prog /\ setup_ssa n v prog = (mov, (ssa, na)) ->
  not_created_subprogs P mov.
Proof.
  intros P n v prog mov ssa na [_ H]; unfold setup_ssa in H.
  destruct (list_next_var_rename _ _ _) as [x [y z]]; inv_eqs; exact Logic.I.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "full_ssa_cc_trans_not_created_subprogs" *)
Theorem full_ssa_cc_trans_not_created_subprogs : forall P n (prog : prog a),
  not_created_subprogs P prog -> not_created_subprogs P (full_ssa_cc_trans n prog).
Proof.
  intros P n prog H; unfold full_ssa_cc_trans.
  destruct (setup_ssa n (limit_var prog) prog) as [mov [ssa na]] eqn:E1.
  destruct (ssa_cc_trans prog ssa na []) as [p' [r1 r2]] eqn:E2; cbn [not_created_subprogs].
  split; [eapply setup_ssa_not_created_subprogs; eauto|].
  eapply ssa_cc_trans_not_created_subprogs; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_fake_moves" *)
Theorem word_get_code_labels_fake_moves : forall prio a0 b c d (e f : prog a) g h i,
  fake_moves prio a0 b c d = (e, (f, (g, (h, i)))) ->
  get_code_labels e = {} /\ get_code_labels f = {}.
Proof. intros; edestruct fake_moves_simple; eauto; split; apply simple_code_labels; auto. Qed.

Ltac simple_rw f :=
  repeat match goal with S : simple_prog _ |- _ => rewrite (f _ S) in *; clear S end.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_ssa_cc_trans" *)
Theorem word_get_code_labels_ssa_cc_trans : forall (x : prog a) y z lt a0 b c,
  ssa_cc_trans x y z lt = (a0, (b, c)) -> get_code_labels a0 = get_code_labels x.
Proof.
  intros p; induction p using prog_nested_ind; intros ssa na lt p' rr1 rr2 Hc;
    cbn [ssa_cc_trans] in Hc; repeat (case_split; inv_eqs); inv_eqs; ssa_simple.
  all: repeat match goal with
         | IH : forall s n l x y z, ssa_cc_trans ?q s n l = (x, (y, z)) -> _,
           E : ssa_cc_trans ?q _ _ _ = (_, (_, _)) |- _ => specialize (IH _ _ _ _ _ _ E)
         end.
  all: cbn [get_code_labels] in *; simple_rw simple_code_labels;
    rewrite ?ssa_reconcile_get_code_labels in *;
    repeat match goal with H : get_code_labels _ = get_code_labels _ |- _ => rewrite H in *; clear H end;
    try reflexivity; set_eq.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_full_ssa_cc_trans" *)
Theorem word_get_code_labels_full_ssa_cc_trans : forall m (p : prog a),
  get_code_labels (full_ssa_cc_trans m p) = get_code_labels p.
Proof.
  intros m p; unfold full_ssa_cc_trans, setup_ssa.
  destruct (list_next_var_rename _ _ _) as [x [y z]].
  destruct (ssa_cc_trans p y z []) as [p' [r1 r2]] eqn:E; cbn [get_code_labels].
  apply word_get_code_labels_ssa_cc_trans in E; rewrite E; set_eq.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_fake_moves" *)
Theorem word_good_handlers_fake_moves : forall n prio a0 b c d (e f : prog a) g h i,
  fake_moves prio a0 b c d = (e, (f, (g, (h, i)))) ->
  good_handlers n e /\ good_handlers n f.
Proof. intros; edestruct fake_moves_simple; eauto; split; apply simple_good_handlers; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_ssa_cc_trans" *)
Theorem word_good_handlers_ssa_cc_trans : forall n (x : prog a) y z lt a0 b c,
  ssa_cc_trans x y z lt = (a0, (b, c)) -> good_handlers n a0 = good_handlers n x.
Proof.
  intros n p; induction p using prog_nested_ind; intros ssa na lt p' rr1 rr2 Hc;
    cbn [ssa_cc_trans] in Hc; repeat (case_split; inv_eqs); inv_eqs; ssa_simple.
  all: repeat match goal with
         | IH : forall s n l x y z, ssa_cc_trans ?q s n l = (x, (y, z)) -> _,
           E : ssa_cc_trans ?q _ _ _ = (_, (_, _)) |- _ => specialize (IH _ _ _ _ _ _ E)
         end.
  all: cbn [good_handlers] in *; simple_rw (simple_good_handlers n);
    pose proof (ssa_reconcile_good_handlers n) as G; unfold is_true in G; rewrite ?G in *;
    repeat match goal with H : good_handlers _ _ = good_handlers _ _ |- _ => rewrite H in *; clear H end;
    cbn [andb]; rewrite ?andb_true_r; try reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_full_ssa_cc_trans" *)
Theorem word_good_handlers_full_ssa_cc_trans : forall n m (p : prog a),
  good_handlers n (full_ssa_cc_trans m p) = good_handlers n p.
Proof.
  intros n m p; unfold full_ssa_cc_trans, setup_ssa.
  destruct (list_next_var_rename _ _ _) as [x [y z]].
  destruct (ssa_cc_trans p y z []) as [p' [r1 r2]] eqn:E; cbn [good_handlers andb].
  eapply word_good_handlers_ssa_cc_trans; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "flat_exp_conventions_ShareInst" *)
Theorem flat_exp_conventions_ShareInst : forall op v (exp : exp a),
  flat_exp_conventions (ShareInst op v exp) <->
  ((exists v c, exp = Op asm.Add [Var v; Const c]) \/ (exists v, exp = Var v)).
Proof.
  intros op v e; split.
  - cbn [flat_exp_conventions]; intros H; repeat (case_split; inv_eqs); try discriminate H;
      eauto.
  - intros [[v' [c' ->]]|[v' ->]]; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "flat_exp_conventions_fake_moves" *)
Theorem flat_exp_conventions_fake_moves : forall prio ls ssal ssar na (l r : prog a) a0 b c,
  fake_moves prio ls ssal ssar na = (l, (r, (a0, (b, c)))) ->
  flat_exp_conventions l /\ flat_exp_conventions r.
Proof. intros; edestruct fake_moves_simple; eauto; split; apply simple_flat; auto. Qed.

(** Galette-only: equation form of [ssa_cc_trans_flat_exp_conventions]. *)
Lemma ssa_cc_trans_flat_eq : forall (p : prog a) ssa na lt p' r,
  ssa_cc_trans p ssa na lt = (p', r) -> flat_exp_conventions p -> flat_exp_conventions p'.
Proof.
  intros p; induction p using prog_nested_ind; intros ssa na lt p' rr Hc Hp;
    cbn [ssa_cc_trans] in Hc; repeat (case_split; inv_eqs); inv_eqs; ssa_simple; use_ih4.
  all: cbn [flat_exp_conventions ssa_cc_trans_exp MAP] in *; simple_rw simple_flat;
    rewrite ?(simple_flat _ (ssa_reconcile_simple _ _ _)); bsplit; eauto.
  all: revert Hp; destruct e; cbn [ssa_cc_trans_exp MAP]; intros H;
    repeat (case_split; inv_eqs; cbn [MAP ssa_cc_trans_exp] in *); try discriminate; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "ssa_cc_trans_flat_exp_conventions" *)
Theorem ssa_cc_trans_flat_exp_conventions : forall (prog : prog a) ssa na lt,
  flat_exp_conventions prog -> flat_exp_conventions (FST (ssa_cc_trans prog ssa na lt)).
Proof.
  intros prog ssa na lt H; destruct (ssa_cc_trans prog ssa na lt) eqn:E; cbn [FST].
  eapply ssa_cc_trans_flat_eq; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "full_ssa_cc_trans_flat_exp_conventions" *)
Theorem full_ssa_cc_trans_flat_exp_conventions : forall (prog : prog a) n,
  flat_exp_conventions prog -> flat_exp_conventions (full_ssa_cc_trans n prog).
Proof.
  intros prog n H; unfold full_ssa_cc_trans, setup_ssa.
  destruct (list_next_var_rename _ _ _) as [x [y z]].
  destruct (ssa_cc_trans prog y z []) as [p' [r1 r2]] eqn:E; cbn [flat_exp_conventions andb].
  eapply ssa_cc_trans_flat_eq; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "fake_moves_wf_cutsets" *)
Theorem fake_moves_wf_cutsets : forall prio ls A B C (L R : prog a) D E G,
  fake_moves prio ls A B C = (L, (R, (D, (E, G)))) -> wf_cutsets L /\ wf_cutsets R.
Proof. intros; edestruct fake_moves_simple; eauto; split; apply simple_wf_cutsets; auto. Qed.

(** Galette-only: equation form of [ssa_cc_trans_wf_cutsets]. *)
Lemma ssa_cc_trans_wf_eq : forall (p : prog a) ssa na lt p' r,
  ssa_cc_trans p ssa na lt = (p', r) -> wf_cutsets p'.
Proof.
  intros p; induction p using prog_nested_ind; intros ssa na lt p' rr Hc;
    cbn [ssa_cc_trans] in Hc; repeat (case_split; inv_eqs); inv_eqs; ssa_simple; use_ih4.
  all: cbn [wf_cutsets] in *; simple_rw simple_wf_cutsets;
    rewrite ?(simple_wf_cutsets _ (ssa_reconcile_simple _ _ _));
    unfold wf_names, apply_nummaps_key, apply_nummap_key; cbn [FST SND];
    bsplit; eauto; apply wf_fromAList.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "ssa_cc_trans_wf_cutsets" *)
Theorem ssa_cc_trans_wf_cutsets : forall (prog : prog a) ssa na lt,
  let '(prog', (ssa', na')) := ssa_cc_trans prog ssa na lt in wf_cutsets prog'.
Proof.
  intros prog ssa na lt; destruct (ssa_cc_trans prog ssa na lt) as [p' [s' n']] eqn:E.
  eapply ssa_cc_trans_wf_eq; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "full_ssa_cc_trans_wf_cutsets" *)
Theorem full_ssa_cc_trans_wf_cutsets : forall n (prog : prog a),
  wf_cutsets (full_ssa_cc_trans n prog).
Proof.
  intros n prog; unfold full_ssa_cc_trans, setup_ssa.
  destruct (list_next_var_rename _ _ _) as [x [y z]].
  destruct (ssa_cc_trans prog y z []) as [p' [r1 r2]] eqn:E; cbn [wf_cutsets andb].
  eapply ssa_cc_trans_wf_eq; eauto.
Qed.

End SSA.

(** ** remove_dead_prog *)

Section RemoveDead.
Context {a : N}.

Lemma is_Skip_true (p : prog a) : is_Skip p = true -> p = Skip.
Proof. destruct p; cbn; congruence. Qed.

Ltac fst_ih_rd :=
  repeat match goal with
  | E : remove_dead ?q ?l ?n ?t = _,
    IH : forall (l' : num_set) (n' : list stackLang.store_name) (t' : list (num_set * num_set)), _ |- _ =>
      let T := fresh "T" in pose proof (IH l n t) as T;
      lazymatch type of T with
      | context [remove_dead q l n t] => rewrite E in T; cbn [FST] in T; clear IH
      | _ => clear T; fail
      end
  end;
  repeat match goal with
         | H : is_Skip ?x = true |- _ => apply is_Skip_true in H; subst x
         | H : is_Skip _ && is_Skip _ = true |- _ => apply andb_prop in H; destruct H
         end.

Ltac rd_start :=
  let p := fresh "p" in
  intros p; induction p using prog_nested_ind; intros live nlive lt; cbn [remove_dead];
  repeat (case_split; inv_eqs); inv_eqs; fst_ih_rd; cbn [FST].

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "remove_dead_not_created_subprogs" *)
Theorem remove_dead_not_created_subprogs : forall P (prog : prog a) q r lt,
  not_created_subprogs P prog -> not_created_subprogs P (FST (remove_dead prog q r lt)).
Proof.
  intros P; rd_start.
  all: intros; cbn [not_created_subprogs] in *; intuition eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "remove_dead_prog_not_created_subprogs" *)
Theorem remove_dead_prog_not_created_subprogs : forall P (prog : prog a),
  not_created_subprogs P prog -> not_created_subprogs P (remove_dead_prog prog).
Proof. intros; apply remove_dead_not_created_subprogs; auto. Qed.

Ltac rd_bool :=
  intros; cbn [flat_exp_conventions full_inst_ok_less every_inst every_stack_var
               call_arg_convention wf_cutsets] in *; bsplit; eauto.

Lemma remove_dead_flat : forall (p : prog a) live nlive lt,
  flat_exp_conventions p -> flat_exp_conventions (FST (remove_dead p live nlive lt)).
Proof. rd_start. all: rd_bool. Qed.

Lemma remove_dead_full_inst_ok_less : forall c (p : prog a) live nlive lt,
  full_inst_ok_less c p -> full_inst_ok_less c (FST (remove_dead p live nlive lt)).
Proof. intros c; rd_start. all: rd_bool. Qed.

Lemma remove_dead_every_inst : forall P (p : prog a) live nlive lt,
  every_inst P p -> every_inst P (FST (remove_dead p live nlive lt)).
Proof. intros P; rd_start. all: rd_bool. Qed.

Lemma remove_dead_every_stack_var : forall P (p : prog a) live nlive lt,
  every_stack_var P p -> every_stack_var P (FST (remove_dead p live nlive lt)).
Proof. intros P; rd_start. all: rd_bool. Qed.

Lemma remove_dead_call_arg_convention : forall (p : prog a) live nlive lt,
  call_arg_convention p -> call_arg_convention (FST (remove_dead p live nlive lt)).
Proof. rd_start. all: rd_bool. Qed.

Lemma remove_dead_wf_cutsets : forall (p : prog a) live nlive lt,
  wf_cutsets p -> wf_cutsets (FST (remove_dead p live nlive lt)).
Proof. rd_start. all: rd_bool. Qed.

Lemma remove_dead_labels : forall (p : prog a) live nlive lt,
  extract_labels p = extract_labels (FST (remove_dead p live nlive lt)).
Proof.
  rd_start.
  all: cbn [extract_labels] in *; rewrite <- ?T, <- ?T0, <- ?H, <- ?H0; cbn [extract_labels];
    rewrite ?app_nil_r; try reflexivity.
  all: repeat match goal with H : extract_labels ?x = [] |- context [extract_labels ?x] =>
         rewrite H end; rewrite ?app_nil_r; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "remove_dead_conventions" *)
Theorem remove_dead_conventions : forall P (p : prog a) live nlive lt c (k : N),
  let comp := FST (remove_dead p live nlive lt) in
  (flat_exp_conventions p -> flat_exp_conventions comp) /\
  (full_inst_ok_less c p -> full_inst_ok_less c comp) /\
  (pre_alloc_conventions p -> pre_alloc_conventions comp) /\
  (every_inst P p -> every_inst P comp) /\
  (wf_cutsets p -> wf_cutsets comp) /\
  (extract_labels p = extract_labels comp).
Proof.
  intros P p live nlive lt c k comp; subst comp; unfold pre_alloc_conventions;
    repeat split; intros.
  - apply remove_dead_flat; auto.
  - apply remove_dead_full_inst_ok_less; auto.
  - bsplit; [apply remove_dead_every_stack_var|apply remove_dead_call_arg_convention]; auto.
  - apply remove_dead_every_inst; auto.
  - apply remove_dead_wf_cutsets; auto.
  - apply remove_dead_labels.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "remove_dead_prog_conventions" *)
Theorem remove_dead_prog_conventions : forall P (p : prog a) c (k : N),
  let comp := remove_dead_prog p in
  (flat_exp_conventions p -> flat_exp_conventions comp) /\
  (full_inst_ok_less c p -> full_inst_ok_less c comp) /\
  (pre_alloc_conventions p -> pre_alloc_conventions comp) /\
  (every_inst P p -> every_inst P comp) /\
  (wf_cutsets p -> wf_cutsets comp) /\
  (extract_labels p = extract_labels comp).
Proof. intros P p c k; exact (remove_dead_conventions P p LN [] [] c k). Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_remove_dead" *)
Theorem word_get_code_labels_remove_dead : forall (ps : prog a) live nlive lt,
  get_code_labels (FST (remove_dead ps live nlive lt)) SUBSET get_code_labels ps.
Proof.
  rd_start.
  all: cbn [get_code_labels] in *;
    try match goal with
        | H : forall l n t, get_code_labels (FST (remove_dead ?q l n t)) SUBSET _
          |- context [remove_dead ?q ?l ?n ?t] => pose proof (H l n t)
        end; sets.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_remove_dead_prog" *)
Theorem word_get_code_labels_remove_dead_prog : forall (ps : prog a),
  get_code_labels (remove_dead_prog ps) SUBSET get_code_labels ps.
Proof. intros; apply word_get_code_labels_remove_dead. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_remove_dead" *)
Theorem word_good_handlers_remove_dead : forall n (ps : prog a) live nlive lt,
  good_handlers n (FST (remove_dead ps live nlive lt)) = good_handlers n ps.
Proof.
  intros n; rd_start.
  all: cbn [good_handlers] in *; rewrite ?H0;
    repeat match goal with H : _ = good_handlers _ _ |- _ => rewrite <- H; clear H end;
    cbn [andb]; rewrite ?andb_true_r; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_remove_dead_prog" *)
Theorem word_good_handlers_remove_dead_prog : forall n (ps : prog a),
  good_handlers n (remove_dead_prog ps) = good_handlers n ps.
Proof. intros; apply word_good_handlers_remove_dead. Qed.

End RemoveDead.

(** ** word_common_subexp_elim *)

Section CSE.
Context {a : N}.

(** Galette-only: the shapes of the programs that [word_cse] produces from a
    single instruction. *)
Lemma add_to_data_aux_shape : forall data r i (x : prog a) d' p,
  add_to_data_aux data r i x = (d', p) -> p = x \/ exists k, p = Move 0 [(r, k)].
Proof.
  intros data r i x d' p H; unfold add_to_data_aux in H;
    repeat (case_split; inv_eqs); inv_eqs; eauto.
Qed.

Lemma word_cseInst_shape : forall data (i : inst a) d' p,
  word_cseInst data i = (d', p) -> p = Inst i \/ exists r k, p = Move 0 [(r, k)].
Proof.
  intros data i d' p H; unfold word_cseInst in H; repeat (case_split; inv_eqs); inv_eqs; eauto.
  all: try match goal with
         | E : add_to_data_aux _ _ _ _ = _ |- _ =>
             apply add_to_data_aux_shape in E as [->|[? ->]]; eauto
         end.
  all: try (unfold add_to_data in *; match goal with
         | E : add_to_data_aux _ _ _ _ = _ |- _ =>
             apply add_to_data_aux_shape in E as [->|[? ->]]; eauto
         end).
  all: try (unfold add_to_load_aux in *; repeat (case_split; inv_eqs); inv_eqs; eauto).
  all: try (unfold add_to_data_const in *; repeat (case_split; inv_eqs); inv_eqs; eauto).
Qed.

Ltac cse_shape :=
  repeat match goal with
  | E : word_cseInst _ _ = (_, _) |- _ =>
      apply word_cseInst_shape in E as [->|[? [? ->]]]
  | E : add_to_data_aux _ _ _ _ = (_, _) |- _ =>
      apply add_to_data_aux_shape in E as [->|[? ->]]
  end.

Ltac use_ih2 :=
  repeat match goal with
  | IH : forall d x y, word_cse d ?q = (x, y) -> _, E : word_cse ?d0 ?q = (?x0, ?y0) |- _ =>
      specialize (IH _ _ _ E)
  end.

Ltac cse_start :=
  let p := fresh "p" in
  intros p; induction p using prog_nested_ind; intros data dd1 pp1 Hc; cbn [word_cse] in Hc;
  repeat (case_split; inv_eqs); inv_eqs; cse_shape; use_ih2.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_cse_extract_labels" *)
Theorem word_cse_extract_labels : forall (p : prog a) d d1 p1,
  word_cse d p = (d1, p1) -> extract_labels p1 = extract_labels p.
Proof. cse_start. all: cbn [extract_labels]; congruence. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_word_common_subexp_elim" *)
Theorem extract_labels_word_common_subexp_elim : forall (p : prog a),
  extract_labels (word_common_subexp_elim p) = extract_labels p.
Proof.
  intros p; unfold word_common_subexp_elim; destruct (word_cse empty_data p) eqn:E.
  eapply word_cse_extract_labels; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_cseInst_not_created_subprogs" *)
Theorem word_cseInst_not_created_subprogs : forall P env (i : inst a),
  not_created_subprogs P (SND (word_cseInst env i)).
Proof.
  intros P env i; destruct (word_cseInst env i) eqn:E; cbn [SND].
  apply word_cseInst_shape in E as [->|[? [? ->]]]; exact Logic.I.
Qed.

(** Galette-only: equation form of [word_cse_not_created_subprogs]. *)
Lemma word_cse_ncs_eq : forall P (p : prog a) data d1 p1,
  word_cse data p = (d1, p1) -> not_created_subprogs P p -> not_created_subprogs P p1.
Proof. intros P; cse_start. all: intros; cbn [not_created_subprogs] in *; intuition eauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_cse_not_created_subprogs" *)
Theorem word_cse_not_created_subprogs : forall P (p : prog a) env,
  not_created_subprogs P p -> not_created_subprogs P (SND (word_cse env p)).
Proof.
  intros P p env H; destruct (word_cse env p) eqn:E; cbn [SND]; eapply word_cse_ncs_eq; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_common_subexp_elim_not_created_subprogs" *)
Theorem word_common_subexp_elim_not_created_subprogs : forall P (prog : prog a),
  not_created_subprogs P prog -> not_created_subprogs P (word_common_subexp_elim prog).
Proof.
  intros P p H; unfold word_common_subexp_elim; destruct (word_cse empty_data p) eqn:E.
  eapply word_cse_ncs_eq; eauto.
Qed.

(** Galette-only: equation form for [word_good_handlers_word_common_subexp_elim]. *)
Lemma word_cse_good_handlers : forall q (p : prog a) data d1 p1,
  word_cse data p = (d1, p1) -> good_handlers q p1 = good_handlers q p.
Proof. intros q; cse_start. all: cbn [good_handlers]; congruence. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_word_common_subexp_elim" *)
Theorem word_good_handlers_word_common_subexp_elim : forall q (p : prog a),
  good_handlers q (word_common_subexp_elim p) = good_handlers q p.
Proof.
  intros q p; unfold word_common_subexp_elim; destruct (word_cse empty_data p) eqn:E.
  eapply word_cse_good_handlers; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_cse_get_code_labels" *)
Theorem word_cse_get_code_labels : forall (p : prog a) data data' q,
  word_cse data p = (data', q) -> get_code_labels q SUBSET get_code_labels p.
Proof. cse_start. all: cbn [get_code_labels] in *; sets. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_word_common_subexp_elim" *)
Theorem word_get_code_labels_word_common_subexp_elim : forall (p : prog a),
  get_code_labels (word_common_subexp_elim p) SUBSET get_code_labels p.
Proof.
  intros p; unfold word_common_subexp_elim; destruct (word_cse empty_data p) eqn:E.
  eapply word_cse_get_code_labels; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_cse_flat_exp_conventions" *)
Theorem word_cse_flat_exp_conventions : forall (p : prog a) data data' q,
  flat_exp_conventions p /\ word_cse data p = (data', q) -> flat_exp_conventions q.
Proof.
  intros p data data' q [H1 H2]; revert data data' q H2 H1; revert p.
  cse_start. all: intros; cbn [flat_exp_conventions] in *; bsplit; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "flat_exp_conventions_word_common_subexp_elim" *)
Theorem flat_exp_conventions_word_common_subexp_elim : forall (p : prog a),
  flat_exp_conventions p -> flat_exp_conventions (word_common_subexp_elim p).
Proof.
  intros p H; unfold word_common_subexp_elim; destruct (word_cse empty_data p) eqn:E.
  eapply word_cse_flat_exp_conventions; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_cse_wf_cutsets" *)
Theorem word_cse_wf_cutsets : forall (p : prog a) data data' q,
  wf_cutsets p /\ word_cse data p = (data', q) -> wf_cutsets q.
Proof.
  intros p data data' q [H1 H2]; revert data data' q H2 H1; revert p.
  cse_start. all: intros; cbn [wf_cutsets] in *; bsplit; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "wf_cutsets_word_common_subexp_elim" *)
Theorem wf_cutsets_word_common_subexp_elim : forall (p : prog a),
  wf_cutsets p -> wf_cutsets (word_common_subexp_elim p).
Proof.
  intros p H; unfold word_common_subexp_elim; destruct (word_cse empty_data p) eqn:E.
  eapply word_cse_wf_cutsets; eauto.
Qed.

End CSE.

(** ** copy_prop *)

Section Copy.
Context {a : N}.

(** Galette-only: shape of [copy_prop_inst]'s output. *)
Lemma copy_prop_inst_shape : forall (i : inst a) cs p cs',
  copy_prop_inst i cs = (p, cs') -> p = Skip \/ exists i', p = Inst i'.
Proof.
  intros i cs p cs' H; unfold copy_prop_inst in H; repeat (case_split; inv_eqs); inv_eqs; eauto.
Qed.

Ltac cp_ih :=
  repeat match goal with
  | E : copy_prop_prog ?q ?c = _, IH : forall cs : copy_state, _ |- _ =>
      let T := fresh "T" in pose proof (IH c) as T;
      lazymatch type of T with
      | context [copy_prop_prog q c] => rewrite E in T; cbn [FST SND] in T; clear IH
      | _ => clear T; fail
      end
  end.

Ltac cp_start :=
  let p := fresh "p" in
  intros p; induction p using prog_nested_ind; intros cs; cbn [copy_prop_prog];
  repeat (case_split; inv_eqs); inv_eqs; cp_ih; cbn [FST].

Ltac cp_shape :=
  try match goal with
      | |- context [copy_prop_inst ?i ?c] =>
          let E := fresh "E" in destruct (copy_prop_inst i c) eqn:E; cbn [FST];
          apply copy_prop_inst_shape in E as [->|[? ->]]
      end.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "wf_cutsets_copy_prop_aux" *)
Theorem wf_cutsets_copy_prop_aux : forall (p : prog a) cs,
  wf_cutsets p -> wf_cutsets (FST (copy_prop_prog p cs)).
Proof. cp_start. all: cp_shape; intros; cbn [wf_cutsets] in *; bsplit; eauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "wf_cutsets_copy_prop" *)
Theorem wf_cutsets_copy_prop : forall (p : prog a),
  wf_cutsets p -> wf_cutsets (copy_prop p).
Proof. intros; apply wf_cutsets_copy_prop_aux; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_copy_prop_aux" *)
Theorem extract_labels_copy_prop_aux : forall (p : prog a) cs,
  extract_labels (FST (copy_prop_prog p cs)) = extract_labels p.
Proof. cp_start. all: cp_shape; cbn [extract_labels] in *; congruence. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_copy_prop" *)
Theorem extract_labels_copy_prop : forall (p : prog a),
  extract_labels (copy_prop p) = extract_labels p.
Proof. intros; apply extract_labels_copy_prop_aux. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "flat_exp_conventions_copy_prop_aux" *)
Theorem flat_exp_conventions_copy_prop_aux : forall (p : prog a) cs,
  flat_exp_conventions p -> flat_exp_conventions (FST (copy_prop_prog p cs)).
Proof.
  cp_start. all: cp_shape; intros; cbn [flat_exp_conventions] in *; bsplit; eauto.
  all: unfold copy_prop_share; revert H; repeat (case_split; inv_eqs); try discriminate;
    reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "flat_exp_conventions_copy_prop" *)
Theorem flat_exp_conventions_copy_prop : forall (p : prog a),
  flat_exp_conventions p -> flat_exp_conventions (copy_prop p).
Proof. intros; apply flat_exp_conventions_copy_prop_aux; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_copy_prop" *)
Theorem word_get_code_labels_copy_prop : forall (ps : prog a),
  get_code_labels (copy_prop ps) = get_code_labels ps.
Proof.
  intros ps; unfold copy_prop; generalize empty_eq; revert ps.
  cp_start. all: cp_shape; cbn [get_code_labels] in *; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_copy_prop" *)
Theorem word_good_handlers_copy_prop : forall n (ps : prog a),
  good_handlers n (copy_prop ps) = good_handlers n ps.
Proof.
  intros n ps; unfold copy_prop; generalize empty_eq; revert ps.
  cp_start. all: cp_shape; cbn [good_handlers] in *; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "copy_prop_not_created_subprogs" *)
Theorem copy_prop_not_created_subprogs : forall P (prog : prog a),
  not_created_subprogs P prog -> not_created_subprogs P (copy_prop prog).
Proof.
  intros P prog; unfold copy_prop; generalize empty_eq; revert prog.
  cp_start. all: cp_shape; intros; cbn [not_created_subprogs] in *; intuition eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "copy_prop_prog_not_alloc_var_aux1" *)
Theorem copy_prop_prog_not_alloc_var_aux1 : forall cs x y,
  (forall x, ~ is_alloc_var x -> lookup x (to_eq cs) = None) ->
  ~ is_alloc_var x -> lookup x (to_eq (remove_eq cs y)) = None.
Proof.
  intros cs x y H Hx; unfold remove_eq; destruct (lookup y (to_eq cs)); auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "copy_prop_prog_not_alloc_var_aux2" *)
Theorem copy_prop_prog_not_alloc_var_aux2 : forall x yy cs,
  (forall x, ~ is_alloc_var x -> lookup x (to_eq cs) = None) ->
  ~ is_alloc_var x -> lookup x (to_eq (remove_eqs cs yy)) = None.
Proof.
  intros x yy; induction yy as [|y yy IH]; intros cs H Hx; cbn [remove_eqs]; auto.
  apply IH; auto. intros; apply copy_prop_prog_not_alloc_var_aux1; auto.
Qed.

(** Galette-only: the invariant of [copy_prop_prog_not_alloc_var]. *)
Definition na_inv (cs : copy_state) : Prop :=
  forall x, ~ is_alloc_var x -> lookup x (to_eq cs) = None.

Lemma na_inv_empty : na_inv empty_eq.
Proof. intros x _; reflexivity. Qed.

Lemma na_inv_remove_eq cs y : na_inv cs -> na_inv (remove_eq cs y).
Proof. intros H x Hx; apply copy_prop_prog_not_alloc_var_aux1; auto. Qed.

Lemma na_inv_remove_eqs cs yy : na_inv cs -> na_inv (remove_eqs cs yy).
Proof. intros H x Hx; apply copy_prop_prog_not_alloc_var_aux2; auto. Qed.

Lemma na_inv_set_eq cs x y : na_inv cs -> na_inv (set_eq cs x y).
Proof.
  intros H z Hz; unfold set_eq.
  destruct (is_alloc_var x) eqn:Ex, (is_alloc_var y) eqn:Ey; cbn [andb]; auto.
  repeat (case_split; inv_eqs); cbn [to_eq]; rewrite ?lookup_insert;
    repeat case_split; subst; try congruence; auto.
Qed.

Lemma na_inv_set_store_eq cs s y : na_inv cs -> na_inv (set_store_eq cs s y).
Proof.
  intros H z Hz; unfold set_store_eq.
  destruct (is_alloc_var y) eqn:Ey; [|reflexivity].
  repeat (case_split; inv_eqs); cbn [to_eq]; rewrite ?lookup_insert;
    repeat case_split; subst; try congruence; auto.
Qed.

Lemma na_inv_merge_eqs cs ds : na_inv cs -> na_inv (merge_eqs cs ds).
Proof.
  intros H z Hz; unfold merge_eqs; cbn [to_eq]; rewrite lookup_inter_eq, (H z Hz); reflexivity.
Qed.

Lemma na_inv_copy_prop_move : forall l cs l' cs',
  copy_prop_move l cs = (l', cs') -> na_inv cs -> na_inv cs'.
Proof.
  intros l; induction l as [|[x y] l IH]; intros cs l' cs' Hc Hi; cbn [copy_prop_move] in Hc.
  - inv_eqs; auto.
  - destruct (copy_prop_move l cs) eqn:E; inv_eqs.
    apply na_inv_set_eq, na_inv_remove_eq; eapply IH; eauto.
Qed.

Lemma na_inv_copy_prop_inst : forall (i : inst a) cs p cs',
  copy_prop_inst i cs = (p, cs') -> na_inv cs -> na_inv cs'.
Proof.
  intros i cs p cs' H Hi; unfold copy_prop_inst in H; repeat (case_split; inv_eqs); inv_eqs;
    auto using na_inv_remove_eq, na_inv_remove_eqs.
Qed.

Lemma na_inv_copy_prop_prog : forall (p : prog a) cs p' cs',
  copy_prop_prog p cs = (p', cs') -> na_inv cs -> na_inv cs'.
Proof.
  intros p; induction p using prog_nested_ind; intros cs p' cs' Hc Hi; cbn [copy_prop_prog] in Hc;
    repeat (case_split; inv_eqs); inv_eqs;
    eauto using na_inv_empty, na_inv_remove_eq, na_inv_remove_eqs, na_inv_set_store_eq,
      na_inv_merge_eqs, na_inv_copy_prop_move, na_inv_copy_prop_inst.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "copy_prop_prog_not_alloc_var" *)
Theorem copy_prop_prog_not_alloc_var : forall (p : prog a) cs,
  (forall x, ~ is_alloc_var x -> lookup x (to_eq cs) = None) ->
  (forall x, ~ is_alloc_var x -> lookup x (to_eq (SND (copy_prop_prog p cs))) = None).
Proof.
  intros p cs H; destruct (copy_prop_prog p cs) eqn:E; cbn [SND].
  eapply na_inv_copy_prop_prog; eauto.
Qed.

Lemma bd_negb_true (P : Prop) `{Decision P} : negb (bool_decide P) = true -> ~ P.
Proof.
  intros Hn HP; rewrite (bd_true P HP) in Hn; discriminate Hn.
Qed.

Ltac bd_hyps :=
  repeat match goal with
  | H : negb (bool_decide _) = true |- _ => apply bd_negb_true in H
  | H : bool_decide _ = true |- _ => apply bool_decide_spec in H
  end.

Ltac bd_goal :=
  repeat match goal with
  | |- context [@bool_decide ?P ?d] =>
      first [ rewrite (@bd_true P d) by (first [assumption | reflexivity | congruence])
            | rewrite (@bd_false P d) by (first [assumption | congruence | intuition discriminate]) ]
  end.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "every_inst_distinct_tar_reg_copy_prop_aux" *)
Theorem every_inst_distinct_tar_reg_copy_prop_aux : forall (p : prog a) cs,
  every_inst distinct_tar_reg p -> every_inst distinct_tar_reg (FST (copy_prop_prog p cs)).
Proof.
  cp_start. all: intros; cbn [every_inst] in *; bsplit; eauto.
  all: try (match goal with |- context [copy_prop_inst ?i ?c] =>
    unfold copy_prop_inst; unfold distinct_tar_reg in *; repeat (case_split; inv_eqs); inv_eqs;
    cbn [FST every_inst] in *; bsplit; bd_hyps; bd_goal; auto end).
  all: unfold distinct_tar_reg in *; bd_hyps; bd_goal; auto;
    apply negb_true_iff, N.eqb_neq; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "every_inst_distinct_tar_reg_copy_prop" *)
Theorem every_inst_distinct_tar_reg_copy_prop : forall (p : prog a),
  every_inst distinct_tar_reg p -> every_inst distinct_tar_reg (copy_prop p).
Proof. intros; apply every_inst_distinct_tar_reg_copy_prop_aux; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "full_inst_ok_less_copy_prop_aux" *)
Theorem full_inst_ok_less_copy_prop_aux : forall ac (p : prog a) cs,
  full_inst_ok_less ac p -> full_inst_ok_less ac (FST (copy_prop_prog p cs)).
Proof.
  intros ac; cp_start. all: intros; cbn [full_inst_ok_less] in *; bsplit; eauto.
  all: try (match goal with |- context [copy_prop_inst ?i ?c] =>
    unfold copy_prop_inst; repeat (case_split; inv_eqs); inv_eqs;
    cbn [FST full_inst_ok_less lookup_eq_imm] in *; unfold inst_ok_less in *; auto end).
  all: try (match goal with r : reg_imm a |- context [lookup_eq_imm _ ?r] =>
              destruct r; cbn [lookup_eq_imm] in *; auto end; fail).
  all: try (match goal with |- context [implb ?x _] => destruct x end; cbn [implb andb] in *;
            auto; bsplit; auto; apply negb_true_iff, N.eqb_neq; congruence).
  all: unfold copy_prop_share; revert H; repeat (case_split; inv_eqs); inv_eqs;
    cbn [exp_to_addr] in *; try discriminate; auto.
  all: intros; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "full_inst_ok_less_copy_prop" *)
Theorem full_inst_ok_less_copy_prop : forall ac (p : prog a),
  full_inst_ok_less ac p -> full_inst_ok_less ac (copy_prop p).
Proof. intros; apply full_inst_ok_less_copy_prop_aux; auto. Qed.

Lemma lookup_eq_na cs v : na_inv cs -> is_alloc_var v = false -> lookup_eq cs v = v.
Proof.
  intros H Hv; unfold lookup_eq; rewrite H; [reflexivity|]. rewrite Hv; discriminate.
Qed.

Lemma MAP_lookup_eq_na cs (l : list N) :
  na_inv cs -> (forall x, In x l -> is_alloc_var x = false) -> MAP (lookup_eq cs) l = l.
Proof.
  intros H Hl; induction l as [|x l IH]; [reflexivity|]; cbn [MAP map].
  rewrite lookup_eq_na, IH; auto; [intros; apply Hl; right; auto|apply Hl; left; auto].
Qed.

Lemma even_not_alloc k : is_alloc_var (2 * k) = false.
Proof. unfold is_alloc_var; apply N.eqb_neq; intros Hm; lia. Qed.

Lemma copy_prop_every_stack_var : forall P (p : prog a) cs,
  every_stack_var P p -> every_stack_var P (FST (copy_prop_prog p cs)).
Proof. intros P; cp_start. all: cp_shape; intros; cbn [every_stack_var] in *; bsplit; eauto. Qed.

Lemma copy_prop_call_arg_convention : forall (p : prog a) cs,
  na_inv cs -> call_arg_convention p -> call_arg_convention (FST (copy_prop_prog p cs)).
Proof.
  intros p; induction p using prog_nested_ind; intros cs Hi; cbn [copy_prop_prog];
    repeat (case_split; inv_eqs); inv_eqs; cp_ih; cbn [FST];
    intros; cbn [call_arg_convention] in *; bsplit;
    eauto using na_inv_copy_prop_prog, na_inv_empty.
  - (* Inst *)
    unfold copy_prop_inst; unfold inst_arg_convention in *;
      repeat (case_split; inv_eqs); inv_eqs; cbn [FST call_arg_convention lookup_eq_imm] in *;
      unfold inst_arg_convention in *; bsplit; auto;
      repeat match goal with H : (_ =? _) = true |- _ => apply N.eqb_eq in H; subst end;
      rewrite ?lookup_eq_na by (auto; reflexivity); try reflexivity; try congruence.
  - (* Raise *)
    apply N.eqb_eq in H; subst; rewrite lookup_eq_na by (auto; reflexivity); reflexivity.
  - (* Return *)
    bd_hyps. rewrite MAP_lookup_eq_na; auto.
    + apply bool_decide_spec; exact H.
    + intros x Hx; rewrite H in Hx; apply In_GENLIST_iff in Hx as (i & _ & ->); apply even_not_alloc.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "pre_alloc_conventions_copy_prop_aux" *)
Theorem pre_alloc_conventions_copy_prop_aux : forall (p : prog a) cs,
  (forall x, ~ is_alloc_var x -> lookup x (to_eq cs) = None) ->
  pre_alloc_conventions p -> pre_alloc_conventions (FST (copy_prop_prog p cs)).
Proof.
  intros p cs Hi H; unfold pre_alloc_conventions in *; bsplit;
    [apply copy_prop_every_stack_var|apply copy_prop_call_arg_convention]; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "pre_alloc_conventions_copy_prop" *)
Theorem pre_alloc_conventions_copy_prop : forall (p : prog a),
  pre_alloc_conventions p -> pre_alloc_conventions (copy_prop p).
Proof. intros p H; apply pre_alloc_conventions_copy_prop_aux; auto; apply na_inv_empty. Qed.

End Copy.

(** ** three_to_two_reg_prog *)

Section ThreeToTwo.
Context {a : N}.

Ltac t2_start :=
  let p := fresh "p" in
  intros p; induction p using prog_nested_ind; cbn [three_to_two_reg];
  repeat (case_split; inv_eqs); inv_eqs.

Lemma three_to_two_reg_labels : forall (p : prog a),
  extract_labels p = extract_labels (three_to_two_reg p).
Proof. t2_start. all: cbn [extract_labels] in *; try reflexivity; congruence. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "three_to_two_reg_prog_lab_pres" *)
Theorem three_to_two_reg_prog_lab_pres : forall b (prog : prog a),
  extract_labels prog = extract_labels (three_to_two_reg_prog b prog).
Proof. intros [] prog; [apply three_to_two_reg_labels|reflexivity]. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "three_to_two_reg_prog_not_created_subprogs" *)
Theorem three_to_two_reg_prog_not_created_subprogs : forall P b (prog : prog a),
  not_created_subprogs P prog -> not_created_subprogs P (three_to_two_reg_prog b prog).
Proof.
  intros P [] prog; [|auto]; unfold three_to_two_reg_prog; revert prog.
  t2_start. all: intros; cbn [not_created_subprogs] in *; intuition eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "three_to_two_reg_prog_two_reg_inst" *)
Theorem three_to_two_reg_prog_two_reg_inst : forall (b : bool) (prog : prog a),
  b -> every_inst two_reg_inst (three_to_two_reg_prog b prog).
Proof.
  intros [] prog Hb; [|discriminate Hb]; unfold three_to_two_reg_prog; clear Hb; revert prog.
  t2_start. all: cbn [every_inst two_reg_inst] in *; unfold two_reg_inst; bsplit; eauto;
    apply N.eqb_refl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "three_to_two_reg_prog_wf_cutsets" *)
Theorem three_to_two_reg_prog_wf_cutsets : forall b (prog : prog a),
  wf_cutsets prog -> wf_cutsets (three_to_two_reg_prog b prog).
Proof.
  intros [] prog; [|auto]; unfold three_to_two_reg_prog; revert prog.
  t2_start. all: intros; cbn [wf_cutsets] in *; bsplit; eauto.
Qed.

Lemma three_to_two_reg_esv : forall P (prog : prog a),
  every_stack_var P prog -> every_stack_var P (three_to_two_reg prog).
Proof. intros P; t2_start. all: intros; cbn [every_stack_var] in *; bsplit; eauto. Qed.

Lemma three_to_two_reg_cac : forall (prog : prog a),
  call_arg_convention prog -> call_arg_convention (three_to_two_reg prog).
Proof.
  t2_start. all: intros; cbn [call_arg_convention] in *; unfold inst_arg_convention in *;
    bsplit; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "three_to_two_reg_prog_pre_alloc_conventions" *)
Theorem three_to_two_reg_prog_pre_alloc_conventions : forall b (prog : prog a),
  pre_alloc_conventions prog -> pre_alloc_conventions (three_to_two_reg_prog b prog).
Proof.
  intros [] prog; [|auto]; unfold three_to_two_reg_prog, pre_alloc_conventions; intros H.
  bsplit; [apply three_to_two_reg_esv|apply three_to_two_reg_cac]; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "three_to_two_reg_prog_flat_exp_conventions" *)
Theorem three_to_two_reg_prog_flat_exp_conventions : forall b (prog : prog a),
  flat_exp_conventions prog -> flat_exp_conventions (three_to_two_reg_prog b prog).
Proof.
  intros [] prog; [|auto]; unfold three_to_two_reg_prog; revert prog.
  t2_start. all: intros; cbn [flat_exp_conventions] in *; bsplit; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "three_to_two_reg_prog_full_inst_ok_less" *)
Theorem three_to_two_reg_prog_full_inst_ok_less : forall c b (prog : prog a),
  full_inst_ok_less c prog -> full_inst_ok_less c (three_to_two_reg_prog b prog).
Proof.
  intros c [] prog; [|auto]; unfold three_to_two_reg_prog; revert prog.
  t2_start. all: intros; cbn [full_inst_ok_less] in *; unfold inst_ok_less in *; bsplit; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_three_to_two_reg_prog" *)
Theorem word_get_code_labels_three_to_two_reg_prog : forall b (ps : prog a),
  get_code_labels (three_to_two_reg_prog b ps) = get_code_labels ps.
Proof.
  intros [] ps; [|reflexivity]; unfold three_to_two_reg_prog; revert ps.
  t2_start. all: cbn [get_code_labels] in *; try congruence; set_eq.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_three_to_two_reg_prog" *)
Theorem word_good_handlers_three_to_two_reg_prog : forall n b (ps : prog a),
  good_handlers n (three_to_two_reg_prog b ps) = good_handlers n ps.
Proof.
  intros n [] ps; [|reflexivity]; unfold three_to_two_reg_prog; revert ps.
  t2_start. all: cbn [good_handlers] in *; try reflexivity; congruence.
Qed.

End ThreeToTwo.

(** ** remove_unreach *)

Section Unreach.
Context {a : N}.

Lemma dest_Seq_Move_cases : forall (p : prog a) n l rest,
  dest_Seq_Move p = Some (n, (l, rest)) ->
  (p = Move n l /\ rest = Skip) \/ p = Seq (Move n l) rest.
Proof.
  intros p n l rest H; unfold dest_Seq_Move in H; repeat (case_split; inv_eqs); inv_eqs;
    try discriminate; auto.
Qed.

(** Galette-only: the possible results of [SimpSeq]. *)
Lemma SimpSeq_cases : forall (p1 p2 : prog a),
  SimpSeq p1 p2 = Seq p1 p2 \/ SimpSeq p1 p2 = p1 \/ SimpSeq p1 p2 = p2 \/
  exists n l n2 l2 rest,
    p1 = Move n l /\ ((p2 = Move n2 l2 /\ rest = Skip) \/ p2 = Seq (Move n2 l2) rest) /\
    (SimpSeq p1 p2 = Move (MAX n n2) (word_unreach.merge_moves l l2) \/
     SimpSeq p1 p2 = Seq (Move (MAX n n2) (word_unreach.merge_moves l l2)) rest).
Proof.
  intros p1 p2; unfold SimpSeq.
  destruct p2; try (left; reflexivity); try (right; left; reflexivity).
  all: destruct p1; try (left; reflexivity); try (right; left; reflexivity);
    try (right; right; left; reflexivity).
  all: try (destruct (dest_Seq_Move _) as [[n2 [l2 rest]]|] eqn:D;
            [|left; reflexivity];
            apply dest_Seq_Move_cases in D;
            right; right; right; do 5 eexists; split; [reflexivity|]; split; [exact D|];
            destruct rest; auto).
Qed.

Ltac simpseq_cases p1 p2 :=
  destruct (SimpSeq_cases p1 p2) as
    [->|[->|[->|(? & ? & ? & ? & ? & -> & [[-> ->]| ->] & [->| ->])]]].

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_dest_Seq_Move" *)
Theorem word_get_code_labels_dest_Seq_Move : forall (p : prog a) x y z,
  dest_Seq_Move p = Some (x, (y, z)) -> get_code_labels z = get_code_labels p.
Proof.
  intros p x y z H; apply dest_Seq_Move_cases in H as [[-> ->]| ->]; cbn; [reflexivity|set_eq].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_SimpSeq" *)
Theorem word_get_code_labels_SimpSeq : forall (p q : prog a),
  get_code_labels (SimpSeq p q) SUBSET get_code_labels p UNION get_code_labels q.
Proof. intros p q; simpseq_cases p q; cbn [get_code_labels]; sets. Qed.

Ltac sar_inst lem :=
  repeat match goal with
  | |- context [SimpSeq ?x ?y] => pose_new (lem x y)
  | IH : forall qs : prog a, _ |- context [Seq_assoc_right ?q ?x] =>
      lazymatch type of IH with
      | context [Seq_assoc_right q _] => pose_new (IH x)
      end
  end.

Ltac sar_start :=
  let p := fresh "p" in
  intros p; induction p using prog_nested_ind; intros qs;
  try match goal with
      | |- context [Seq_assoc_right (Call ?r _ _ ?h) _] =>
          destruct r as [[? [? [? [? ?]]]]|]; [destruct h as [[? [? [? ?]]]|]|]
      end;
  cbn [Seq_assoc_right] in *.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_Seq_assoc_right" *)
Theorem word_get_code_labels_Seq_assoc_right : forall (ps qs : prog a),
  get_code_labels (Seq_assoc_right ps qs) SUBSET get_code_labels ps UNION get_code_labels qs.
Proof.
  sar_start; sar_inst word_get_code_labels_SimpSeq.
  all: cbn [get_code_labels] in *; sets.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_remove_unreach" *)
Theorem word_get_code_labels_remove_unreach : forall (ps : prog a),
  get_code_labels (remove_unreach ps) SUBSET get_code_labels ps.
Proof.
  intros ps; unfold remove_unreach; pose proof (word_get_code_labels_Seq_assoc_right ps Skip).
  cbn [get_code_labels] in *; sets.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_SimpSeq" *)
Theorem word_good_handlers_SimpSeq : forall n (ps qs : prog a),
  good_handlers n ps /\ good_handlers n qs -> good_handlers n (SimpSeq ps qs).
Proof. intros n ps qs [H1 H2]; simpseq_cases ps qs; cbn [good_handlers] in *; bsplit; auto. Qed.

Ltac sar_prop lem :=
  sar_start; intros; try (apply lem; split).

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_Seq_assoc_right" *)
Theorem word_good_handlers_Seq_assoc_right : forall n (ps qs : prog a),
  good_handlers n ps /\ good_handlers n qs -> good_handlers n (Seq_assoc_right ps qs).
Proof.
  intros n; sar_prop word_good_handlers_SimpSeq.
  all: cbn [good_handlers] in *; bsplit; eauto 6.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_remove_unreach" *)
Theorem word_good_handlers_remove_unreach : forall n (ps : prog a),
  good_handlers n ps -> good_handlers n (remove_unreach ps).
Proof.
  intros n ps H; unfold remove_unreach; apply word_good_handlers_Seq_assoc_right; split;
    [exact H|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "SimpSeq_not_created_subprogs" *)
Theorem SimpSeq_not_created_subprogs : forall P (ps qs : prog a),
  not_created_subprogs P ps /\ not_created_subprogs P qs ->
  not_created_subprogs P (SimpSeq ps qs).
Proof.
  intros P ps qs [H1 H2]; simpseq_cases ps qs; cbn [not_created_subprogs] in *; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "Seq_assoc_right_not_created_subprogs" *)
Theorem Seq_assoc_right_not_created_subprogs : forall P (ps qs : prog a),
  not_created_subprogs P ps /\ not_created_subprogs P qs ->
  not_created_subprogs P (Seq_assoc_right ps qs).
Proof.
  intros P; sar_prop SimpSeq_not_created_subprogs.
  all: cbn [not_created_subprogs] in *; intuition eauto 6.
  all: match goal with
       | IH : forall qs, _ -> not_created_subprogs _ (Seq_assoc_right ?q qs)
         |- not_created_subprogs _ (Seq_assoc_right ?q _) =>
           apply IH; cbn [not_created_subprogs]; tauto
       end.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "remove_unreach_not_created_subprogs" *)
Theorem remove_unreach_not_created_subprogs : forall P (prog : prog a),
  not_created_subprogs P prog -> not_created_subprogs P (remove_unreach prog).
Proof.
  intros P prog H; unfold remove_unreach; apply Seq_assoc_right_not_created_subprogs;
    split; [exact H|exact Logic.I].
Qed.

(** Galette-only: subsequences of label lists. *)
Inductive subseq {A} : list A -> list A -> Prop :=
| subseq_nil : subseq [] []
| subseq_cons x l1 l2 : subseq l1 l2 -> subseq (x :: l1) (x :: l2)
| subseq_skip x l1 l2 : subseq l1 l2 -> subseq l1 (x :: l2).

Lemma subseq_refl {A} (l : list A) : subseq l l.
Proof. induction l; constructor; auto. Qed.

Lemma subseq_nil_l {A} (l : list A) : subseq [] l.
Proof. induction l; constructor; auto. Qed.

Lemma subseq_app {A} (l1 l2 m1 m2 : list A) :
  subseq l1 l2 -> subseq m1 m2 -> subseq (l1 ++ m1) (l2 ++ m2).
Proof. intros H1 H2; induction H1; cbn; try constructor; auto. Qed.

Lemma subseq_trans {A} (l1 l2 l3 : list A) : subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros H1 H2; revert l1 H1; induction H2; intros l0 H1.
  - exact H1.
  - inversion H1; subst; constructor; auto.
  - constructor; auto.
Qed.

Lemma subseq_app_l {A} (l1 l2 : list A) : subseq l1 (l1 ++ l2).
Proof. rewrite <- (app_nil_r l1) at 1; apply subseq_app; [apply subseq_refl|apply subseq_nil_l]. Qed.

Lemma subseq_app_r {A} (l1 l2 : list A) : subseq l2 (l1 ++ l2).
Proof. apply (subseq_app [] l1 l2 l2); [apply subseq_nil_l|apply subseq_refl]. Qed.

Lemma subseq_In {A} (l1 l2 : list A) x : subseq l1 l2 -> In x l1 -> In x l2.
Proof. induction 1; cbn; intuition. Qed.

Lemma subseq_NoDup {A} (l1 l2 : list A) : subseq l1 l2 -> NoDup l2 -> NoDup l1.
Proof.
  induction 1; intros Hd; [constructor|inversion Hd; subst|inversion Hd; subst; auto].
  constructor; auto. intros Hx; apply H2, (subseq_In _ _ _ H Hx).
Qed.

Ltac subseq_solve :=
  repeat first
    [ apply subseq_refl
    | apply subseq_nil_l
    | apply subseq_app
    | apply subseq_cons
    | assumption ].

Lemma SimpSeq_subseq : forall (p1 p2 : prog a),
  subseq (extract_labels (SimpSeq p1 p2)) (extract_labels p1 ++ extract_labels p2).
Proof.
  intros p1 p2; simpseq_cases p1 p2; cbn [extract_labels app];
    first [apply subseq_refl|apply subseq_app_l|apply subseq_app_r|apply subseq_nil_l].
Qed.

Lemma Seq_assoc_right_subseq : forall (p1 p2 : prog a),
  subseq (extract_labels (Seq_assoc_right p1 p2)) (extract_labels p1 ++ extract_labels p2).
Proof.
  sar_start.
  all: try (eapply subseq_trans; [apply SimpSeq_subseq|]); cbn [extract_labels app];
    rewrite ?app_nil_r, ?app_assoc; try apply subseq_nil_l; try apply subseq_refl.
  all: repeat match goal with
         | IH : forall qs, subseq (extract_labels (Seq_assoc_right ?q qs)) _
           |- context [Seq_assoc_right ?q Skip] =>
             let T := fresh "T" in pose proof (IH Skip) as T; cbn [extract_labels] in T;
             rewrite app_nil_r in T; clear IH
         end.
  all: try (subseq_solve; fail).
  (* Seq *)
  rewrite <- app_assoc. eapply subseq_trans; [apply IHp1|].
  apply subseq_app; [apply subseq_refl|apply IHp2].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_SimpSeq" *)
Theorem extract_labels_SimpSeq : forall (p1 p2 : prog a),
  set (extract_labels (SimpSeq p1 p2)) SUBSET set (extract_labels (Seq p1 p2)).
Proof.
  intros p1 p2 x Hx; rewrite IN_set in *; cbn [extract_labels].
  eapply subseq_In; [apply SimpSeq_subseq|exact Hx].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_Seq_assoc_right_lemma" *)
Theorem extract_labels_Seq_assoc_right_lemma : forall (p1 p2 : prog a),
  set (extract_labels (Seq_assoc_right p1 p2)) SUBSET
  set (extract_labels p1) UNION set (extract_labels p2).
Proof.
  intros p1 p2 x Hx; rewrite IN_set in Hx; unfold pred_set.IN, pred_set.UNION; rewrite !IN_set.
  apply in_app_or; eapply subseq_In; [apply Seq_assoc_right_subseq|exact Hx].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_remove_unreach" *)
Theorem extract_labels_remove_unreach : forall (p : prog a),
  set (extract_labels (remove_unreach p)) SUBSET set (extract_labels p).
Proof.
  intros p x Hx; rewrite IN_set in *; unfold remove_unreach in Hx.
  eapply subseq_In in Hx; [|apply Seq_assoc_right_subseq]; cbn [extract_labels] in Hx.
  rewrite app_nil_r in Hx; exact Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "MEM_extract_labels_Seq_assoc_right_lemma" *)
Theorem MEM_extract_labels_Seq_assoc_right_lemma : forall (p1 p2 : prog a) x,
  MEM x (extract_labels (Seq_assoc_right p1 p2)) ->
  MEM x (extract_labels p1) \/ MEM x (extract_labels p2).
Proof.
  intros p1 p2 x H; unfold is_true in *; rewrite !MEM_In in *.
  apply in_app_or; eapply subseq_In; [apply Seq_assoc_right_subseq|exact H].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "helper" *)
Theorem helper : forall (p1 p2 : prog a) x,
  ~ (MEM x (extract_labels p1) \/ MEM x (extract_labels p2)) ->
  ~ MEM x (extract_labels (Seq_assoc_right p1 p2)).
Proof. intros p1 p2 x H1 H2; apply H1, MEM_extract_labels_Seq_assoc_right_lemma, H2. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma" *)
Theorem ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma : forall (p1 p2 : prog a),
  ALL_DISTINCT (extract_labels p1 ++ extract_labels p2) ->
  ALL_DISTINCT (extract_labels (Seq_assoc_right p1 p2)).
Proof.
  intros p1 p2; unfold is_true; rewrite !ALL_DISTINCT_NoDup_list.
  apply subseq_NoDup, Seq_assoc_right_subseq.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "ALL_DISTINCT_extract_labels_remove_unreach" *)
Theorem ALL_DISTINCT_extract_labels_remove_unreach : forall (p : prog a),
  ALL_DISTINCT (extract_labels p) -> ALL_DISTINCT (extract_labels (remove_unreach p)).
Proof.
  intros p H; unfold remove_unreach; apply ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma.
  cbn [extract_labels]; rewrite app_nil_r; exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "labels_rel_remove_unreach" *)
Theorem labels_rel_remove_unreach : forall (q : prog a),
  labels_rel (extract_labels q) (extract_labels (remove_unreach q)).
Proof.
  intros q; split; [apply ALL_DISTINCT_extract_labels_remove_unreach|].
  apply extract_labels_remove_unreach.
Qed.

(** Galette-only: curried forms for the boolean conventions. *)
Tactic Notation "simpseq_bool" reference(f) :=
  let p1 := fresh "p1" in let p2 := fresh "p2" in let H1 := fresh "H1" in let H2 := fresh "H2" in
  intros p1 p2 H1 H2; simpseq_cases p1 p2; cbn [f] in *; bsplit; auto.

Tactic Notation "sar_bool" constr(lem) reference(f) :=
  sar_start; intros; try (apply lem; [|assumption]); cbn [f] in *; bsplit; eauto 6.

Lemma cac_SimpSeq : forall (p1 p2 : prog a),
  call_arg_convention p1 -> call_arg_convention p2 -> call_arg_convention (SimpSeq p1 p2).
Proof. simpseq_bool call_arg_convention. Qed.

Lemma cac_SAR : forall (p1 p2 : prog a),
  call_arg_convention p1 -> call_arg_convention p2 ->
  call_arg_convention (Seq_assoc_right p1 p2).
Proof. sar_bool cac_SimpSeq call_arg_convention. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "call_arg_convention_Seq_assoc_right_lemma" *)
Theorem call_arg_convention_Seq_assoc_right_lemma : forall (p1 p2 : prog a),
  call_arg_convention p1 /\ call_arg_convention p2 ->
  call_arg_convention (Seq_assoc_right p1 p2).
Proof. intros p1 p2 [H1 H2]; apply cac_SAR; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "call_arg_convention_remove_unreach" *)
Theorem call_arg_convention_remove_unreach : forall (p : prog a),
  call_arg_convention p -> call_arg_convention (remove_unreach p).
Proof. intros p H; apply cac_SAR; auto. Qed.

Lemma esv_SimpSeq : forall P (p1 p2 : prog a),
  every_stack_var P p1 -> every_stack_var P p2 -> every_stack_var P (SimpSeq p1 p2).
Proof. intros P; simpseq_bool every_stack_var. Qed.

Lemma esv_SAR : forall P (p1 p2 : prog a),
  every_stack_var P p1 -> every_stack_var P p2 -> every_stack_var P (Seq_assoc_right p1 p2).
Proof. intros P; sar_bool (esv_SimpSeq P) every_stack_var. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "every_stack_var_is_stack_var_Seq_assoc_right_lemma" *)
Theorem every_stack_var_is_stack_var_Seq_assoc_right_lemma : forall (p1 p2 : prog a),
  every_stack_var is_stack_var p1 /\ every_stack_var is_stack_var p2 ->
  every_stack_var is_stack_var (Seq_assoc_right p1 p2).
Proof. intros p1 p2 [H1 H2]; apply esv_SAR; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "every_stack_var_is_stack_var_remove_unreach" *)
Theorem every_stack_var_is_stack_var_remove_unreach : forall (p : prog a),
  every_stack_var is_stack_var p -> every_stack_var is_stack_var (remove_unreach p).
Proof. intros p H; apply esv_SAR; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "pre_alloc_conventions_remove_unreach" *)
Theorem pre_alloc_conventions_remove_unreach : forall (p : prog a),
  pre_alloc_conventions p -> pre_alloc_conventions (remove_unreach p).
Proof.
  intros p H; unfold pre_alloc_conventions in *; bsplit;
    [apply every_stack_var_is_stack_var_remove_unreach|apply call_arg_convention_remove_unreach];
    auto.
Qed.

Lemma fiol_SimpSeq : forall c (p1 p2 : prog a),
  full_inst_ok_less c p1 -> full_inst_ok_less c p2 -> full_inst_ok_less c (SimpSeq p1 p2).
Proof. intros c; simpseq_bool full_inst_ok_less. Qed.

Lemma fiol_SAR : forall c (p1 p2 : prog a),
  full_inst_ok_less c p1 -> full_inst_ok_less c p2 ->
  full_inst_ok_less c (Seq_assoc_right p1 p2).
Proof. intros c; sar_bool (fiol_SimpSeq c) full_inst_ok_less. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "full_inst_ok_less_Seq_assoc_right_lemma" *)
Theorem full_inst_ok_less_Seq_assoc_right_lemma : forall ac (p1 p2 : prog a),
  full_inst_ok_less ac p1 /\ full_inst_ok_less ac p2 ->
  full_inst_ok_less ac (Seq_assoc_right p1 p2).
Proof. intros ac p1 p2 [H1 H2]; apply fiol_SAR; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "full_inst_ok_less_remove_unreach" *)
Theorem full_inst_ok_less_remove_unreach : forall ac (p : prog a),
  full_inst_ok_less ac p -> full_inst_ok_less ac (remove_unreach p).
Proof. intros ac p H; apply fiol_SAR; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "wf_cutsets_SimpSeq" *)
Theorem wf_cutsets_SimpSeq : forall (p1 p2 : prog a),
  wf_cutsets p1 /\ wf_cutsets p2 -> wf_cutsets (SimpSeq p1 p2).
Proof.
  intros p1 p2 [H1 H2]; revert H1 H2; revert p1 p2; simpseq_bool wf_cutsets.
Qed.

Lemma wf_SAR : forall (p1 p2 : prog a),
  wf_cutsets p1 -> wf_cutsets p2 -> wf_cutsets (Seq_assoc_right p1 p2).
Proof.
  sar_start; intros; try (apply wf_cutsets_SimpSeq; split; [|assumption]);
    cbn [wf_cutsets] in *; bsplit; eauto 6.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "wf_cutsets_Seq_assoc_right_lemma" *)
Theorem wf_cutsets_Seq_assoc_right_lemma : forall (p1 p2 : prog a),
  wf_cutsets p1 /\ wf_cutsets p2 -> wf_cutsets (Seq_assoc_right p1 p2).
Proof. intros p1 p2 [H1 H2]; apply wf_SAR; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "wf_cutsets_remove_unreach" *)
Theorem wf_cutsets_remove_unreach : forall (p : prog a),
  wf_cutsets p -> wf_cutsets (remove_unreach p).
Proof. intros p H; apply wf_SAR; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "every_inst_SimpSeq" *)
Theorem every_inst_SimpSeq : forall P (p1 p2 : prog a),
  every_inst P p1 /\ every_inst P p2 -> every_inst P (SimpSeq p1 p2).
Proof.
  intros P p1 p2 [H1 H2]; revert H1 H2; revert p1 p2; simpseq_bool every_inst.
Qed.

Lemma ei_SAR : forall P (p1 p2 : prog a),
  every_inst P p1 -> every_inst P p2 -> every_inst P (Seq_assoc_right p1 p2).
Proof.
  intros P; sar_start; intros; try (apply every_inst_SimpSeq; split; [|assumption]);
    cbn [every_inst] in *; bsplit; eauto 6.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "every_inst_Seq_assoc_right_lemma" *)
Theorem every_inst_Seq_assoc_right_lemma : forall P (p1 p2 : prog a),
  every_inst P p1 /\ every_inst P p2 -> every_inst P (Seq_assoc_right p1 p2).
Proof. intros P p1 p2 [H1 H2]; apply ei_SAR; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "every_inst_remove_unreach" *)
Theorem every_inst_remove_unreach : forall P (p : prog a),
  every_inst P p -> every_inst P (remove_unreach p).
Proof. intros P p H; apply ei_SAR; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "flat_exp_conventions_SimpSeq" *)
Theorem flat_exp_conventions_SimpSeq : forall (p1 p2 : prog a),
  flat_exp_conventions p1 /\ flat_exp_conventions p2 -> flat_exp_conventions (SimpSeq p1 p2).
Proof.
  intros p1 p2 [H1 H2]; revert H1 H2; revert p1 p2; simpseq_bool flat_exp_conventions.
Qed.

Lemma flat_SAR : forall (p1 p2 : prog a),
  flat_exp_conventions p1 -> flat_exp_conventions p2 ->
  flat_exp_conventions (Seq_assoc_right p1 p2).
Proof.
  sar_start; intros; try (apply flat_exp_conventions_SimpSeq; split; [|assumption]);
    cbn [flat_exp_conventions] in *; bsplit; eauto 6.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "flat_exp_conventions_Seq_assoc_right_lemma" *)
Theorem flat_exp_conventions_Seq_assoc_right_lemma : forall (p1 p2 : prog a),
  flat_exp_conventions p1 /\ flat_exp_conventions p2 ->
  flat_exp_conventions (Seq_assoc_right p1 p2).
Proof. intros p1 p2 [H1 H2]; apply flat_SAR; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "flat_exp_conventions_remove_unreach" *)
Theorem flat_exp_conventions_remove_unreach : forall (p : prog a),
  flat_exp_conventions p -> flat_exp_conventions (remove_unreach p).
Proof. intros p H; apply flat_SAR; auto. Qed.

End Unreach.

(** ** word_alloc *)

Section Alloc.
Context {a : N}.

(** Galette-only: [word_alloc] either keeps the program or recolours it. *)
Lemma word_alloc_cases : forall fc (c : asm_config a) alg k (prog : prog a) col_opt,
  word_alloc fc c alg k prog col_opt = prog \/
  exists f, word_alloc fc c alg k prog col_opt = apply_colour f prog.
Proof.
  intros; unfold word_alloc, oracle_colour_ok; repeat (case_split; inv_eqs); inv_eqs; eauto.
Qed.

Ltac ac_start :=
  let p := fresh "p" in
  intros p; induction p using prog_nested_ind; cbn [apply_colour];
  repeat (case_split; inv_eqs); inv_eqs.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "apply_colour_lab_pres" *)
Theorem apply_colour_lab_pres : forall col (prog : prog a),
  extract_labels prog = extract_labels (apply_colour col prog).
Proof. intros col; ac_start. all: cbn [extract_labels] in *; try reflexivity; congruence. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_alloc_lab_pres" *)
Theorem word_alloc_lab_pres : forall fc (c : asm_config a) alg k (prog : prog a) col_opt,
  extract_labels prog = extract_labels (word_alloc fc c alg k prog col_opt).
Proof.
  intros; destruct (word_alloc_cases fc c alg k prog col_opt) as [->|[f ->]];
    [reflexivity|apply apply_colour_lab_pres].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_alloc_flat_exp_conventions_lem" *)
Theorem word_alloc_flat_exp_conventions_lem : forall f (prog : prog a),
  flat_exp_conventions prog -> flat_exp_conventions (apply_colour f prog).
Proof.
  intros f; ac_start. all: intros; cbn [flat_exp_conventions apply_colour_exp MAP] in *;
    bsplit; eauto.
  all: match goal with H : _ = true |- _ => revert H end; destruct e; cbn [apply_colour_exp MAP];
    intros H; repeat (case_split; inv_eqs; cbn [MAP apply_colour_exp] in * );
    try discriminate; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_alloc_flat_exp_conventions" *)
Theorem word_alloc_flat_exp_conventions : forall fc (c : asm_config a) alg k (prog : prog a) col_opt,
  flat_exp_conventions prog -> flat_exp_conventions (word_alloc fc c alg k prog col_opt).
Proof.
  intros fc c alg k prog col_opt H; destruct (word_alloc_cases fc c alg k prog col_opt) as [->|[f ->]];
    [exact H|apply word_alloc_flat_exp_conventions_lem, H].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_alloc_two_reg_inst_lem" *)
Theorem word_alloc_two_reg_inst_lem : forall f (prog : prog a),
  every_inst two_reg_inst prog -> every_inst two_reg_inst (apply_colour f prog).
Proof.
  intros f; ac_start. all: intros; cbn [every_inst] in *; bsplit; eauto.
  all: unfold apply_colour_inst, two_reg_inst in *; repeat (case_split; inv_eqs); inv_eqs;
    try discriminate; auto;
    repeat match goal with H : Arith _ = Arith _ |- _ => injection H as; subst end;
    repeat match goal with H : (_ =? _) = true |- _ => apply N.eqb_eq in H; subst end;
    apply N.eqb_refl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_alloc_two_reg_inst" *)
Theorem word_alloc_two_reg_inst : forall fc (c : asm_config a) alg k (prog : prog a) col_opt,
  every_inst two_reg_inst prog -> every_inst two_reg_inst (word_alloc fc c alg k prog col_opt).
Proof.
  intros fc c alg k prog col_opt H; destruct (word_alloc_cases fc c alg k prog col_opt) as [->|[f ->]];
    [exact H|apply word_alloc_two_reg_inst_lem, H].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "apply_colour_not_created_subprogs" *)
Theorem apply_colour_not_created_subprogs : forall P f (prog : prog a),
  not_created_subprogs P prog -> not_created_subprogs P (apply_colour f prog).
Proof. intros P f; ac_start. all: intros; cbn [not_created_subprogs] in *; intuition eauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_alloc_not_created_subprogs" *)
Theorem word_alloc_not_created_subprogs : forall P n (c : asm_config a) a0 r (prog : prog a) cl,
  not_created_subprogs P prog -> not_created_subprogs P (word_alloc n c a0 r prog cl).
Proof.
  intros P n c a0 r prog cl H; destruct (word_alloc_cases n c a0 r prog cl) as [->|[f ->]];
    [exact H|apply apply_colour_not_created_subprogs, H].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_apply_colour" *)
Theorem word_get_code_labels_apply_colour : forall col (ps : prog a),
  get_code_labels (apply_colour col ps) = get_code_labels ps.
Proof. intros col; ac_start. all: cbn [get_code_labels] in *; congruence. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_apply_colour" *)
Theorem word_good_handlers_apply_colour : forall n col (ps : prog a),
  good_handlers n (apply_colour col ps) = good_handlers n ps.
Proof. intros n col; ac_start. all: cbn [good_handlers] in *; congruence. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_word_alloc" *)
Theorem word_get_code_labels_word_alloc : forall fc (c : asm_config a) alg k (prog : prog a) col_opt,
  get_code_labels (word_alloc fc c alg k prog col_opt) = get_code_labels prog.
Proof.
  intros; destruct (word_alloc_cases fc c alg k prog col_opt) as [->|[f ->]];
    [reflexivity|apply word_get_code_labels_apply_colour].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_word_alloc" *)
Theorem word_good_handlers_word_alloc : forall n fc (c : asm_config a) alg k (prog : prog a) col_opt,
  good_handlers n (word_alloc fc c alg k prog col_opt) = good_handlers n prog.
Proof.
  intros; destruct (word_alloc_cases fc c alg k prog col_opt) as [->|[f ->]];
    [reflexivity|apply word_good_handlers_apply_colour].
Qed.

End Alloc.

(** ** remove_must_terminate *)

Section RMT.
Context {a : N}.

Ltac rmt_start :=
  let p := fresh "p" in
  intros p; induction p using prog_nested_ind; cbn [remove_must_terminate];
  repeat (case_split; inv_eqs); inv_eqs.

Ltac rmt_bool :=
  intros; cbn [flat_exp_conventions full_inst_ok_less every_inst every_var every_stack_var
               call_arg_convention] in *; bsplit; eauto.

Lemma rmt_flat : forall (p : prog a),
  flat_exp_conventions p -> flat_exp_conventions (remove_must_terminate p).
Proof. rmt_start. all: rmt_bool. Qed.

Lemma rmt_fiol : forall c (p : prog a),
  full_inst_ok_less c p -> full_inst_ok_less c (remove_must_terminate p).
Proof. intros c; rmt_start. all: rmt_bool. Qed.

Lemma rmt_every_inst : forall P (p : prog a),
  every_inst P p -> every_inst P (remove_must_terminate p).
Proof. intros P; rmt_start. all: rmt_bool. Qed.

Lemma rmt_every_var : forall P (p : prog a),
  every_var P p -> every_var P (remove_must_terminate p).
Proof. intros P; rmt_start. all: rmt_bool. Qed.

Lemma rmt_esv : forall P (p : prog a),
  every_stack_var P p -> every_stack_var P (remove_must_terminate p).
Proof. intros P; rmt_start. all: rmt_bool. Qed.

Lemma rmt_cac : forall (p : prog a),
  call_arg_convention p -> call_arg_convention (remove_must_terminate p).
Proof. rmt_start. all: rmt_bool. Qed.

Lemma rmt_labels : forall (p : prog a),
  extract_labels p = extract_labels (remove_must_terminate p).
Proof. rmt_start. all: cbn [extract_labels] in *; try reflexivity; congruence. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "remove_must_terminate_conventions" *)
Theorem remove_must_terminate_conventions : forall P (p : prog a) c k,
  let comp := remove_must_terminate p in
  (flat_exp_conventions p -> flat_exp_conventions comp) /\
  (full_inst_ok_less c p -> full_inst_ok_less c comp) /\
  (post_alloc_conventions k p -> post_alloc_conventions k comp) /\
  (every_inst P p -> every_inst P comp) /\
  (extract_labels p = extract_labels comp).
Proof.
  intros P p c k comp; subst comp; unfold post_alloc_conventions; repeat split; intros.
  - apply rmt_flat; auto.
  - apply rmt_fiol; auto.
  - bsplit; [apply rmt_every_var|apply rmt_esv|apply rmt_cac]; auto.
  - apply rmt_every_inst; auto.
  - apply rmt_labels.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_remove_must_terminate" *)
Theorem word_get_code_labels_remove_must_terminate : forall (ps : prog a),
  get_code_labels (remove_must_terminate ps) = get_code_labels ps.
Proof. rmt_start. all: cbn [get_code_labels] in *; congruence. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_remove_must_terminate" *)
Theorem word_good_handlers_remove_must_terminate : forall n (ps : prog a),
  good_handlers n (remove_must_terminate ps) = good_handlers n ps.
Proof. intros n; rmt_start. all: cbn [good_handlers] in *; congruence. Qed.

End RMT.

(** ** word_to_word *)

Section W2W.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "compile_single_not_created_subprogs" *)
Theorem compile_single_not_created_subprogs : forall P two_reg_arith reg_count alg
    (c : asm_config a) (prog_opt : (N * (N * prog a)) * option (num_map N)),
  not_created_subprogs P (SND (SND (FST prog_opt))) ->
  not_created_subprogs P (SND (SND (compile_single two_reg_arith reg_count alg c prog_opt))).
Proof.
  intros P t rc alg c [[n [m p]] o] H; cbn [FST SND] in H; unfold compile_single; cbn [SND].
  apply word_alloc_not_created_subprogs, remove_dead_prog_not_created_subprogs,
    remove_unreach_not_created_subprogs, three_to_two_reg_prog_not_created_subprogs,
    copy_prop_not_created_subprogs, word_common_subexp_elim_not_created_subprogs,
    remove_dead_prog_not_created_subprogs, full_ssa_cc_trans_not_created_subprogs,
    inst_select_not_created_subprogs, compile_exp_not_created_subprogs, H.
Qed.

(** Galette-only: what [full_compile_single] does to one table entry. *)
Lemma full_compile_single_entry : forall t rc alg (c : asm_config a) n m (pp : prog a) o,
  exists pp', full_compile_single t rc alg c ((n, (m, pp)), o) = (n, (m, pp')) /\
    (forall k, good_handlers k pp -> good_handlers k pp') /\
    get_code_labels pp' SUBSET get_code_labels pp.
Proof.
  intros; unfold full_compile_single, compile_single; eexists; split; [reflexivity|]; split.
  - intros k H.
    rewrite word_good_handlers_remove_must_terminate, word_good_handlers_word_alloc,
      word_good_handlers_remove_dead_prog.
    apply word_good_handlers_remove_unreach.
    rewrite word_good_handlers_three_to_two_reg_prog, word_good_handlers_copy_prop,
      word_good_handlers_word_common_subexp_elim, word_good_handlers_remove_dead_prog,
      word_good_handlers_full_ssa_cc_trans, word_good_handlers_inst_select.
    apply word_good_handlers_word_simp, H.
  - rewrite word_get_code_labels_remove_must_terminate, word_get_code_labels_word_alloc.
    eapply SUBSET_TRANS; split; [apply word_get_code_labels_remove_dead_prog|].
    eapply SUBSET_TRANS; split; [apply word_get_code_labels_remove_unreach|].
    rewrite word_get_code_labels_three_to_two_reg_prog, word_get_code_labels_copy_prop.
    eapply SUBSET_TRANS; split; [apply word_get_code_labels_word_common_subexp_elim|].
    eapply SUBSET_TRANS; split; [apply word_get_code_labels_remove_dead_prog|].
    rewrite word_get_code_labels_full_ssa_cc_trans, word_get_code_labels_inst_select.
    apply word_get_code_labels_word_simp.
Qed.

Lemma In_ZIP_l {A B} (l1 : list A) (l2 : list B) x y : In (x, y) (ZIP (l1, l2)) -> In x l1.
Proof.
  revert l2; induction l1 as [|h t IH]; intros [|h2 t2] H; cbn in H; try contradiction.
  destruct H as [H|H]; [injection H as -> ->; left; reflexivity|right; eapply IH; eauto].
Qed.

Lemma In_ZIP_r {A B} (l1 : list A) (l2 : list B) x :
  LENGTH l1 = LENGTH l2 -> In x l1 -> exists y, In (x, y) (ZIP (l1, l2)).
Proof.
  revert l2; induction l1 as [|h t IH]; intros [|h2 t2] Hl Hx; cbn in *; try contradiction.
  - rewrite !LENGTH_length in Hl; cbn in Hl; lia.
  - destruct Hx as [->|Hx]; [exists h2; left; reflexivity|].
    destruct (IH t2) as [y Hy]; [rewrite !LENGTH_length in *; cbn in Hl; lia|exact Hx|].
    exists y; right; exact Hy.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_word_to_word_incr_helper" *)
Theorem word_good_handlers_word_to_word_incr_helper : forall tra reg_count1 ralg
    (asm_c : asm_config a) (progs : list (N * (N * prog a))) oracles,
  LENGTH progs = LENGTH oracles ->
  EVERY (fun '(n, (m, pp)) => good_handlers n pp) progs ->
  EVERY (fun '(n, (m, pp)) => good_handlers n pp)
    (MAP (full_compile_single tra reg_count1 ralg asm_c) (ZIP (progs, oracles))).
Proof.
  intros tra rc ralg asm_c progs oracles _ H; unfold is_true in *; rewrite EVERY_Forall in *.
  rewrite Forall_forall in *. intros x Hx; apply in_map_iff in Hx as [[[n [m pp]] o] [<- Hx]].
  destruct (full_compile_single_entry tra rc ralg asm_c n m pp o) as [pp' [-> [Hg _]]].
  apply Hg. apply (H (n, (m, pp))). eapply In_ZIP_l; eauto.
Qed.

Lemma ZIP_MAP_NONE {A B} (l : list A) :
  ZIP (l, MAP (fun _ => @None B) l) = MAP (fun p => (p, None)) l.
Proof. induction l as [|h t IH]; cbn; [reflexivity|]; cbn in IH; rewrite IH; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_word_to_word_incr" *)
Theorem word_good_handlers_word_to_word_incr : forall tra reg_count1 ralg
    (asm_c : asm_config a) (progs : list (N * (N * prog a))),
  EVERY (fun '(n, (m, pp)) => good_handlers n pp) progs ->
  EVERY (fun '(n, (m, pp)) => good_handlers n pp)
    (MAP (fun p => full_compile_single tra reg_count1 ralg asm_c (p, None)) progs).
Proof.
  intros tra rc ralg asm_c progs H.
  pose proof (word_good_handlers_word_to_word_incr_helper tra rc ralg asm_c progs
    (MAP (fun _ => None) progs)) as T.
  rewrite ZIP_MAP_NONE, map_map in T; apply T; auto.
  rewrite !LENGTH_length, length_map; reflexivity.
Qed.

Lemma next_n_oracle_length n col :
  LENGTH (FST (next_n_oracle n col)) = n.
Proof.
  unfold next_n_oracle; destruct (n <=? LENGTH col) eqn:E; cbn [FST].
  - rewrite LENGTH_length in *. apply N.leb_le in E.
    rewrite TAKE_firstn, length_firstn; lia.
  - apply LENGTH_REPLICATE.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_word_to_word" *)
Theorem word_good_handlers_word_to_word : forall wc (ac : asm_config a)
    (progs : list (N * (N * prog a))),
  EVERY (fun '(n, (m, pp)) => good_handlers n pp) progs ->
  EVERY (fun '(n, (m, pp)) => good_handlers n pp) (SND (compile wc ac progs)).
Proof.
  intros wc ac progs H; unfold compile.
  destruct (next_n_oracle (LENGTH progs) (col_oracle wc)) as [no col] eqn:E; cbn [SND].
  apply word_good_handlers_word_to_word_incr_helper; auto.
  pose proof (next_n_oracle_length (LENGTH progs) (col_oracle wc)) as L; rewrite E in L.
  symmetry; exact L.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_code_labels_word_to_word_incr_helper" *)
Theorem word_good_code_labels_word_to_word_incr_helper : forall tra reg_count1 ralg
    (asm_c : asm_config a) (progs : list (N * (N * prog a))) elabs oracles,
  LENGTH progs = LENGTH oracles ->
  good_code_labels progs elabs ->
  good_code_labels (MAP (full_compile_single tra reg_count1 ralg asm_c) (ZIP (progs, oracles)))
    elabs.
Proof.
  intros tra rc ralg asm_c progs elabs oracles Hl [He Hs]; split.
  - apply word_good_handlers_word_to_word_incr_helper; auto.
  - intros x Hx. apply IN_BIGUNION in Hx as [st [Hx Hst]].
    rewrite IN_set in Hst. apply in_map_iff in Hst as [e' [<- He']].
    apply in_map_iff in He' as [[[n [m pp]] o] [<- Hz]].
    destruct (full_compile_single_entry tra rc ralg asm_c n m pp o) as [pp' [Ef [_ Hc]]].
    rewrite Ef in Hx. cbn in Hx.
    assert (Hold : x IN BIGUNION (set (MAP (fun '(n, (m, pp)) => get_code_labels pp) progs))).
    { apply IN_BIGUNION; exists (get_code_labels pp); split; [apply Hc, Hx|].
      rewrite IN_set; apply in_map_iff; exists (n, (m, pp)); split; [reflexivity|].
      eapply In_ZIP_l; eauto. }
    apply Hs in Hold. unfold pred_set.IN, pred_set.UNION in *.
    destruct Hold as [Hold|Hold]; [left|right; exact Hold].
    rewrite IN_set in *. apply in_map_iff in Hold as [ent [<- Hent]].
    destruct (In_ZIP_r progs oracles ent Hl Hent) as [o2 Ho2].
    destruct ent as [n2 [m2 pp2]].
    destruct (full_compile_single_entry tra rc ralg asm_c n2 m2 pp2 o2) as [pp2' [Ef2 _]].
    apply in_map_iff; exists (n2, (m2, pp2')); split; [reflexivity|].
    apply in_map_iff; exists ((n2, (m2, pp2)), o2); split; [exact Ef2|exact Ho2].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_code_labels_word_to_word_incr" *)
Theorem word_good_code_labels_word_to_word_incr : forall tra reg_count1 ralg
    (asm_c : asm_config a) (progs : list (N * (N * prog a))) elabs,
  good_code_labels progs elabs ->
  good_code_labels
    (MAP (fun p => full_compile_single tra reg_count1 ralg asm_c (p, None)) progs) elabs.
Proof.
  intros tra rc ralg asm_c progs elabs H.
  pose proof (word_good_code_labels_word_to_word_incr_helper tra rc ralg asm_c progs elabs
    (MAP (fun _ => None) progs)) as T.
  rewrite ZIP_MAP_NONE, map_map in T; apply T; auto.
  rewrite !LENGTH_length, length_map; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_code_labels_word_to_word" *)
Theorem word_good_code_labels_word_to_word : forall wc (ac : asm_config a)
    (progs : list (N * (N * prog a))) elabs,
  good_code_labels progs elabs -> good_code_labels (SND (compile wc ac progs)) elabs.
Proof.
  intros wc ac progs elabs H; unfold compile.
  destruct (next_n_oracle (LENGTH progs) (col_oracle wc)) as [no col] eqn:E; cbn [SND].
  apply word_good_code_labels_word_to_word_incr_helper; auto.
  pose proof (next_n_oracle_length (LENGTH progs) (col_oracle wc)) as L; rewrite E in L.
  symmetry; exact L.
Qed.

End W2W.
