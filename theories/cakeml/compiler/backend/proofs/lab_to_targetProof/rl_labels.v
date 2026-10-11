(** * CakeML [lab_to_targetProof]: syntactic properties of [remove_labels] (4)

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml] (HOL
    lines 4990-5418): referenced labels exist ([labs_exist],
    [zero_labs_acc_exist_eq]), the label domain of [compute_labels_alt],
    labels at even positions ([even_labels]) and [all_enc_ok] from its
    light check.

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v].
    - [line_labs_exist] and [sec_labs_exist] (used under [EVERY]) are
      [bool]-valued, the quantified condition being decided classically
      ([⌜_⌝]); HOL's overload [all_labs_exist] is an [Abbreviation].
    - [even_labels], [lines_even_labels] and [even_labels_strong] are
      [Prop]-valued; [even_labels] and [even_labels_strong] recurse on the
      sections, then on the lines, and HOL's equations are the tagged
      [_def] theorems.
    - HOL's boolean equivalences between [bool]-valued predicates
      ([line_similar_line_labs_exist], [code_similar_all_labs_exist],
      [all_labs_exist_pad_code], [upd_lab_len_all_labs_exist]) are stated
      as equalities of booleans.
    - [all_enc_ok_light] (HOL overload, a section-local abbreviation in
      [lab_to_target.v]) is written out as [EVERY (sec_ok_light c)].
    - HOL's [local] theorems ([all_enc_ok_split], [all_enc_ok_even],
      [all_enc_ok_lab_lookup_even]) are ported as ordinary theorems.
    - Not ported: the ML bindings [line_labs_exist_ind], [even_labels_ind]
      and the evaluation snippets inside HOL comments ([val tm], [val th],
      [val tm2]). *)

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
  basic bytes rl_syntax rl_invariants rl_nop.
Import backendProps (restrict_zero, restrict_nonzero).
Open Scope N_scope.

Ltac set_unfold :=
  cbv [pred_set.IN pred_set.UNION pred_set.INSERT pred_set.EMPTY pred_set.SUBSET
       pred_set.IMAGE restrict_zero restrict_nonzero] in *.

(** ** Invariant: referenced labels exist *)

Section LabsExist.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_labs_exist_def" *)
Definition line_labs_exist (labs : spt (spt N)) (l : line a) : bool :=
  match l with
  | LabAsm a0 _ _ _ =>
      ⌜forall n1 n2, (n1, n2) IN labs_of a0 -> lab_lookup n1 n2 labs <> NONE⌝
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_labs_exist_def" *)
Definition sec_labs_exist (labs : spt (spt N)) (s : sec a) : bool :=
  match s with Section_ _ ls => EVERY (line_labs_exist labs) ls end.

End LabsExist.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_labs_exist" *)
Abbreviation all_labs_exist labs code := (EVERY (sec_labs_exist labs) code).

Section ZeroLabs.
Context {a : N}.

Lemma IMAGE_FST_restrict_zero_single (n1 n2 x : N) :
  x IN IMAGE FST (restrict_zero ((n1, n2) INSERT {})) <-> x = n1 /\ n2 = 0.
Proof.
  rewrite IN_IMAGE. split.
  - intros ([y1 y2] & -> & Hy). set_unfold. destruct Hy as [[Hy|[]] Hz].
    injection Hy as -> ->. cbn in *. auto.
  - intros [-> ->]. exists (n1, 0). split; [reflexivity|]. set_unfold. cbn. auto.
Qed.

Lemma IMAGE_FST_restrict_zero_empty (x : N) :
  x IN IMAGE FST (restrict_zero ({} : N * N -> Prop)) <-> False.
Proof.
  rewrite IN_IMAGE. split; [|intros []]. intros ([y1 y2] & _ & Hy). set_unfold. destruct Hy as [[] _].
Qed.

Lemma zero_labs_single (n1 n2 : N) acc x :
  x IN domain (if n2 =? 0 then insert n1 tt acc else acc) <->
  x IN IMAGE FST (restrict_zero ((n1, n2) INSERT {})) \/ x IN domain acc.
Proof.
  rewrite IMAGE_FST_restrict_zero_single.
  destruct (N.eqb_spec n2 0) as [->|Hn].
  - set_unfold. rewrite domain_insert. tauto.
  - tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "zero_labs_acc_of_eq_zero_labs_of" *)
Theorem zero_labs_acc_of_eq_zero_labs_of : forall (l : asm_with_lab a) acc,
  domain (zero_labs_acc_of l acc) = IMAGE FST (restrict_zero (labs_of l)) UNION domain acc.
Proof.
  intros l acc. apply EXTENSION. intros x. rewrite IN_UNION.
  destruct l as [[n1 n2]|c r ri [n1 n2]|v|r [n1 n2]|s| |]; cbn [zero_labs_acc_of labs_of];
    try apply zero_labs_single; rewrite IMAGE_FST_restrict_zero_empty; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_get_zero_labs_acc_eq_line_get_zero_labels" *)
Theorem line_get_zero_labs_acc_eq_line_get_zero_labels : forall (l : line a) acc,
  domain (line_get_zero_labs_acc l acc) =
  IMAGE FST (restrict_zero (line_get_labels l)) UNION domain acc.
Proof.
  intros [k1 k2 l|b bytes l|x w bytes l] acc; cbn [line_get_zero_labs_acc line_get_labels];
    [| |apply zero_labs_acc_of_eq_zero_labs_of];
    apply EXTENSION; intros y; rewrite IN_UNION, IMAGE_FST_restrict_zero_empty; tauto.
Qed.

Lemma IMAGE_FST_restrict_zero_UNION (s t : N * N -> Prop) :
  IMAGE FST (restrict_zero (s UNION t)) =
  IMAGE FST (restrict_zero s) UNION IMAGE FST (restrict_zero t).
Proof.
  apply EXTENSION. intros x. rewrite IN_UNION, !IN_IMAGE. split.
  - intros (y & -> & Hy). set_unfold. destruct Hy as [[Hy|Hy] Hz]; [left|right]; exists y; auto.
  - intros [(y & -> & Hy)|(y & -> & Hy)]; exists y; set_unfold; split; try reflexivity;
      destruct Hy; auto.
Qed.

Lemma BIGUNION_IMAGE_nil {A B} (f : A -> B -> Prop) : BIGUNION (IMAGE f (set [])) = {}.
Proof. cbn [LIST_TO_SET]. rewrite IMAGE_EMPTY. apply BIGUNION_EMPTY. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_get_zero_labs_acc_eq_sec_get_zero_labels" *)
Theorem sec_get_zero_labs_acc_eq_sec_get_zero_labels : forall (sec : sec a) acc,
  domain (sec_get_zero_labs_acc sec acc) =
  IMAGE FST (restrict_zero (sec_get_labels sec)) UNION domain acc.
Proof.
  intros [k lines] acc. cbn [sec_get_zero_labs_acc sec_get_labels].
  induction lines as [|l lines IH].
  - cbn [FOLDR fold_right]. rewrite BIGUNION_IMAGE_nil.
    apply EXTENSION. intros y. rewrite IN_UNION, IMAGE_FST_restrict_zero_empty. tauto.
  - change (FOLDR line_get_zero_labs_acc acc (l :: lines)) with
      (line_get_zero_labs_acc l (FOLDR line_get_zero_labs_acc acc lines)).
    rewrite line_get_zero_labs_acc_eq_line_get_zero_labels, IH, BIGUNION_IMAGE_cons,
      IMAGE_FST_restrict_zero_UNION, UNION_ASSOC. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "get_zero_labs_acc_eq_get_zero_labels" *)
Theorem get_zero_labs_acc_eq_get_zero_labels : forall (code : list (sec a)) acc,
  domain (FOLDR sec_get_zero_labs_acc acc code) =
  IMAGE FST (restrict_zero (get_labels code)) UNION domain acc.
Proof.
  intros code acc. induction code as [|sec code IH].
  - cbn [FOLDR fold_right]. unfold get_labels. rewrite BIGUNION_IMAGE_nil.
    apply EXTENSION. intros y. rewrite IN_UNION, IMAGE_FST_restrict_zero_empty. tauto.
  - change (FOLDR sec_get_zero_labs_acc acc (sec :: code)) with
      (sec_get_zero_labs_acc sec (FOLDR sec_get_zero_labs_acc acc code)).
    rewrite sec_get_zero_labs_acc_eq_sec_get_zero_labels, IH, get_labels_cons,
      IMAGE_FST_restrict_zero_UNION, UNION_ASSOC. reflexivity.
Qed.

Lemma domain_LN {X} : domain (@LN X) = {}.
Proof. apply EXTENSION. intros x. split; [|intros []]. intros H. apply domain_lookup in H as [v Hv]. discriminate. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "zero_labs_acc_exist_eq" *)
Theorem zero_labs_acc_exist_eq : forall (labs : spt (spt N)) (code : list (sec a)),
  zero_labs_acc_exist labs code <-> restrict_zero (get_labels code) SUBSET labs_domain labs.
Proof.
  intros labs code. unfold zero_labs_acc_exist. unfold is_true. rewrite EVERY_Forall, List.Forall_forall.
  assert (Hd : forall n, (exists v, lookup n (get_zero_labs_acc code) = SOME v) <->
                          n IN IMAGE FST (restrict_zero (get_labels code))).
  { intros n. rewrite <- domain_lookup. unfold get_zero_labs_acc.
    change (domain (FOLDR sec_get_zero_labs_acc LN code) n) with
      (n IN domain (FOLDR sec_get_zero_labs_acc LN code)).
    rewrite get_zero_labs_acc_eq_get_zero_labels, domain_LN, IN_UNION. split; [|tauto].
    intros [H|[]]. exact H. }
  split.
  - intros H [n1 n2] Hin. assert (Hn : n1 IN IMAGE FST (restrict_zero (get_labels code))).
    { apply IN_IMAGE. exists (n1, n2). split; [reflexivity|exact Hin]. }
    apply Hd in Hn as [v Hv]. apply ALOOKUP_toAList_In in Hv. specialize (H _ Hv). cbn in H.
    set_unfold. destruct Hin as [_ Hz]. cbn in Hz. subst n2.
    unfold labs_domain. exists n1, 0. split; [reflexivity|]. unfold lab_lookup.
    destruct (lookup n1 labs) as [l|]; [|discriminate]. destruct (lookup 0 l); [discriminate|discriminate].
  - intros H [n v] Hin. apply ALOOKUP_toAList_In in Hin.
    assert (Hn : n IN IMAGE FST (restrict_zero (get_labels code))) by (apply Hd; eauto).
    apply IN_IMAGE in Hn as ([n1 n2] & -> & Hr). specialize (H _ Hr).
    set_unfold. destruct Hr as [_ Hz]. cbn in Hz |- *. subst n2.
    destruct H as (m1 & m2 & E & Hl). injection E as <- <-. unfold lab_lookup in Hl.
    destruct (lookup n1 labs) as [l|]; [|contradiction]. destruct (lookup 0 l); [reflexivity|contradiction].
Qed.

End ZeroLabs.



(** ** Preservation of [labs_exist] *)

Section LabsExistPres.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_line_labs_exist" *)
Theorem line_similar_line_labs_exist : forall labs (l1 l2 : line a),
  line_similar l1 l2 -> (line_labs_exist labs l1 = line_labs_exist labs l2).
Proof.
  intros labs [k1 k2 l|b bytes l|x w bytes l] [k1' k2' l'|b' bytes' l'|x' w' bytes' l'] H;
    cbn in H; try contradiction; try reflexivity.
  subst x'. reflexivity.
Qed.

Lemma LIST_REL_EVERY_eq {X} (P Q : X -> bool) (R : X -> X -> Prop) l1 l2 :
  (forall x y, R x y -> P x = Q y) -> LIST_REL R l1 l2 -> EVERY P l1 = EVERY Q l2.
Proof.
  intros HR H. induction H as [|x y l1 l2 Hxy _ IH]; [reflexivity|].
  cbn [EVERY]. rewrite (HR _ _ Hxy), IH. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_all_labs_exist" *)
Theorem code_similar_all_labs_exist : forall labs (c1 c2 : list (sec a)),
  code_similar c1 c2 -> (all_labs_exist labs c1 = all_labs_exist labs c2).
Proof.
  intros labs c1; induction c1 as [|[k1 l1] c1 IH]; intros [|[k2 l2] c2] H; cbn in H; try contradiction.
  - reflexivity.
  - destruct H as (Hc & Hl & ->). cbn [EVERY sec_labs_exist]. rewrite (IH _ Hc).
    rewrite (LIST_REL_EVERY_eq _ _ _ _ _ (line_similar_line_labs_exist labs) Hl). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_labs_exist_pad_code" *)
Theorem all_labs_exist_pad_code : forall labs nop (code : list (sec a)),
  all_labs_exist labs (pad_code nop code) = all_labs_exist labs code.
Proof.
  intros labs nop code. symmetry. apply code_similar_all_labs_exist.
  apply code_similar_pad_code, code_similar_refl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_line_labs_exist" *)
Theorem enc_lines_again_line_labs_exist : forall labs' labs ffis pos enc (lines : list (line a))
    acc ok res ok',
  enc_lines_again labs ffis pos enc lines (acc, ok) = (res, ok') /\
  EVERY (line_labs_exist labs') acc /\
  EVERY (line_labs_exist labs') lines ->
  EVERY (line_labs_exist labs') res.
Proof.
  intros labs' labs ffis pos enc lines. revert pos.
  induction lines as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos acc ok res ok' (H & Ha & Hl);
    cbn [enc_lines_again] in H; cbn [EVERY] in Hl.
  - injection H as <- _. rewrite EVERY_rev. exact Ha.
  - eapply IH; split; [exact H|split; [|exact Hl]]. cbn [EVERY]. rewrite Ha. reflexivity.
  - eapply IH; split; [exact H|split; [|exact Hl]]. cbn [EVERY]. rewrite Ha. reflexivity.
  - apply Bool.andb_true_iff in Hl as [Hx Hl].
    cbv zeta in H. destruct (decide _);
      (eapply IH; split; [exact H|split; [|exact Hl]]; cbn [EVERY]; rewrite Ha, Bool.andb_true_r;
       exact Hx).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_secs_again_all_labs_exist" *)
Theorem enc_secs_again_all_labs_exist : forall labs' pos ffis labs enc (ls res : list (sec a)) ok,
  enc_secs_again pos ffis labs enc ls = (res, ok) /\ all_labs_exist labs' ls ->
  all_labs_exist labs' res.
Proof.
  intros labs' pos ffis labs enc ls; revert pos.
  induction ls as [|[k lines] rest IH]; intros pos res ok (H & Hok); cbn [enc_secs_again] in H.
  - injection H as <- _. reflexivity.
  - destruct (enc_lines_again ffis labs pos enc lines ([], true)) as [lines1 [pos1 ok1]] eqn:E1.
    destruct (enc_secs_again pos1 ffis labs enc rest) as [rest1 ok2] eqn:E2.
    injection H as <- _. cbn in Hok |- *. apply Bool.andb_true_iff in Hok as [H1 H2].
    apply Bool.andb_true_iff. split; [|exact (IH _ _ _ (conj E2 H2))].
    exact (enc_lines_again_line_labs_exist labs' _ _ _ _ _ [] true _ _ (conj E1 (conj eq_refl H1))).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "upd_lab_len_all_labs_exist" *)
Theorem upd_lab_len_all_labs_exist : forall labs pos (code : list (sec a)),
  all_labs_exist labs (upd_lab_len pos code) = all_labs_exist labs code.
Proof.
  intros labs pos code. apply code_similar_all_labs_exist.
  apply code_similar_upd_lab_len, code_similar_refl.
Qed.

(** ** Establishing [labs_exist] *)

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_line_get_code_labels" *)
Theorem line_similar_line_get_code_labels : forall (l1 l2 : line a),
  line_similar l1 l2 -> line_get_code_labels l1 = line_get_code_labels l2.
Proof.
  intros [k1 k2 l|b bytes l|x w bytes l] [k1' k2' l'|b' bytes' l'|x' w' bytes' l'] H;
    cbn in H; try contradiction; try reflexivity.
  destruct H as [-> ->]. reflexivity.
Qed.

Lemma LIST_REL_BIGUNION_IMAGE {X Y} (f : X -> Y -> Prop) (R : X -> X -> Prop) l1 l2 :
  (forall x y, R x y -> f x = f y) -> LIST_REL R l1 l2 ->
  BIGUNION (IMAGE f (set l1)) = BIGUNION (IMAGE f (set l2)).
Proof.
  intros HR H. induction H as [|x y l1 l2 Hxy _ IH].
  - reflexivity.
  - rewrite !BIGUNION_IMAGE_cons, (HR _ _ Hxy), IH. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_get_code_labels" *)
Theorem code_similar_get_code_labels : forall (c1 c2 : list (sec a)),
  code_similar c1 c2 -> get_code_labels c1 = get_code_labels c2.
Proof.
  intros c1; induction c1 as [|[k1 l1] c1 IH]; intros [|[k2 l2] c2] H; cbn in H; try contradiction.
  - reflexivity.
  - destruct H as (Hc & Hl & ->). rewrite !get_code_labels_cons, (IH _ Hc).
    cbn [sec_get_code_labels].
    rewrite (LIST_REL_BIGUNION_IMAGE _ _ _ _ line_similar_line_get_code_labels Hl). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_labs_exist_get_labels" *)
Theorem line_labs_exist_get_labels : forall labs (line : line a),
  line_labs_exist labs line <-> line_get_labels line SUBSET labs_domain labs.
Proof.
  intros labs [k1 k2 l|b bytes l|x w bytes l]; cbn [line_labs_exist line_get_labels].
  - split; [intros _ y []|reflexivity].
  - split; [intros _ y []|reflexivity].
  - unfold is_true. rewrite bool_decide_spec. split.
    + intros H [n1 n2] Hin. exists n1, n2. split; [reflexivity|]. apply H, Hin.
    + intros H n1 n2 Hin. destruct (H _ Hin) as (m1 & m2 & E & Hl). injection E as -> ->. exact Hl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_labs_exist_get_labels" *)
Theorem sec_labs_exist_get_labels : forall labs (sec : sec a),
  sec_labs_exist labs sec <-> sec_get_labels sec SUBSET labs_domain labs.
Proof.
  intros labs [k lines]. cbn [sec_labs_exist sec_get_labels].
  unfold is_true. rewrite EVERY_Forall, List.Forall_forall. split.
  - intros H x Hx. apply IN_BIGUNION_IMAGE_set in Hx as (y & Hy & Hx).
    exact (proj1 (line_labs_exist_get_labels labs y) (H _ Hy) _ Hx).
  - intros H y Hy. apply line_labs_exist_get_labels. intros x Hx. apply H.
    apply IN_BIGUNION_IMAGE_set. eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_labs_exist_get_labels" *)
Theorem all_labs_exist_get_labels : forall labs (code : list (sec a)),
  all_labs_exist labs code <-> get_labels code SUBSET labs_domain labs.
Proof.
  intros labs code. unfold is_true. rewrite EVERY_Forall, List.Forall_forall. unfold get_labels. split.
  - intros H x Hx. apply IN_BIGUNION_IMAGE_set in Hx as (y & Hy & Hx).
    exact (proj1 (sec_labs_exist_get_labels labs y) (H _ Hy) _ Hx).
  - intros H y Hy. apply sec_labs_exist_get_labels. intros x Hx. apply H.
    apply IN_BIGUNION_IMAGE_set. eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_line_get_labels" *)
Theorem line_similar_line_get_labels : forall (l1 l2 : line a),
  line_similar l1 l2 -> line_get_labels l1 = line_get_labels l2.
Proof.
  intros [k1 k2 l|b bytes l|x w bytes l] [k1' k2' l'|b' bytes' l'|x' w' bytes' l'] H;
    cbn in H; try contradiction; try reflexivity.
  subst x'. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_get_labels" *)
Theorem code_similar_get_labels : forall (c1 c2 : list (sec a)),
  code_similar c1 c2 -> get_labels c1 = get_labels c2.
Proof.
  intros c1; induction c1 as [|[k1 l1] c1 IH]; intros [|[k2 l2] c2] H; cbn in H; try contradiction.
  - reflexivity.
  - destruct H as (Hc & Hl & ->). rewrite !get_labels_cons, (IH _ Hc).
    cbn [sec_get_labels].
    rewrite (LIST_REL_BIGUNION_IMAGE _ _ _ _ line_similar_line_get_labels Hl). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "get_labels_upd_lab_len" *)
Theorem get_labels_upd_lab_len : forall pos (code : list (sec a)),
  get_labels (upd_lab_len pos code) = get_labels code.
Proof.
  intros pos code. apply code_similar_get_labels.
  apply code_similar_upd_lab_len, code_similar_refl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "section_labels_line_get_code_labels" *)
Theorem section_labels_line_get_code_labels : forall pos (lines : list (line a)) aux new_pos labs,
  section_labels pos lines aux = (new_pos, labs) ->
  0 INSERT set (MAP FST labs) =
  0 INSERT (set (MAP FST aux) UNION BIGUNION (IMAGE line_get_code_labels (set lines))).
Proof.
  intros pos lines; revert pos.
  induction lines as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos aux new_pos labs H;
    cbn [section_labels] in H.
  - injection H as <- <-. apply EXTENSION. intros y.
    rewrite BIGUNION_IMAGE_nil, !IN_INSERT, IN_UNION. split; [tauto|]. intros [?|[?|[]]]; auto.
  - apply EXTENSION. intros y. rewrite BIGUNION_IMAGE_cons.
    destruct (N.eqb_spec k2 0) as [->|Hk].
    + rewrite (IH _ _ _ _ H), !IN_INSERT, !IN_UNION. cbn [line_get_code_labels].
      rewrite IN_SING. tauto.
    + rewrite (IH _ _ _ _ H), !IN_INSERT, !IN_UNION. cbn [line_get_code_labels MAP map].
      rewrite IN_SING, !IN_set. cbn [In FST fst].
      split; [intros [?|[[?|?]|?]]|intros [?|[?|[?|?]]]]; subst; tauto.
  - apply EXTENSION. intros y. rewrite BIGUNION_IMAGE_cons, (IH _ _ _ _ H), !IN_INSERT, !IN_UNION.
    cbn [line_get_code_labels]. pose proof (NOT_IN_EMPTY y). tauto.
  - apply EXTENSION. intros y. rewrite BIGUNION_IMAGE_cons, (IH _ _ _ _ H), !IN_INSERT, !IN_UNION.
    cbn [line_get_code_labels]. pose proof (NOT_IN_EMPTY y). tauto.
Qed.

Lemma prop_eq_iff (P Q : Prop) : P = Q -> (P <-> Q).
Proof. intros ->. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "labs_domain_compute_labels_alt" *)
Theorem labs_domain_compute_labels_alt : forall pos (code : list (sec a)) labs,
  ALL_DISTINCT (MAP Section_num code) /\
  DISJOINT (domain labs) (set (MAP Section_num code)) ->
  labs_domain (compute_labels_alt pos code labs) =
  get_code_labels code UNION labs_domain labs.
Proof.
  intros pos code; revert pos. induction code as [|[k lines] rest IH]; intros pos labs [Hd Hj].
  - cbn [compute_labels_alt]. rewrite get_code_labels_nil. apply EXTENSION. intros y.
    rewrite IN_UNION. split; [tauto|]. intros [[]|H]; exact H.
  - cbn [compute_labels_alt]. destruct (section_labels pos lines []) as [new_pos sec_labs] eqn:Es.
    cbn [MAP map Section_num ALL_DISTINCT] in Hd. apply Bool.andb_true_iff in Hd as [Hk Hd].
    apply Bool.negb_true_iff in Hk.
    rewrite IN_DISJOINT in Hj. cbn [MAP map Section_num LIST_TO_SET] in Hj.
    assert (Hkl : k NOTIN domain labs).
    { intros Hin. apply Hj. exists k. split; [exact Hin|]. apply IN_INSERT. auto. }
    rewrite IH.
    2:{ split; [exact Hd|]. apply IN_DISJOINT. intros (x & Hx1 & Hx2).
        rewrite domain_insert in Hx1. destruct Hx1 as [->|Hx1].
        - apply IN_set in Hx2. apply MEM_In in Hx2. rewrite Hx2 in Hk. discriminate.
        - apply Hj. exists x. split; [exact Hx1|]. apply IN_INSERT. auto. }
    rewrite labs_domain_insert by exact Hkl.
    pose proof (section_labels_line_get_code_labels _ _ _ _ _ Es) as Hs.
    apply EXTENSION. intros [n1 n2]. rewrite get_code_labels_cons, !IN_UNION.
    cbn [sec_get_code_labels]. rewrite IN_INSERT, !IN_IMAGE, domain_fromAList.
    assert (Hn2 : (n2 = 0 \/ In n2 (MAP FST sec_labs)) <->
                  (n2 = 0 \/ n2 IN BIGUNION (IMAGE line_get_code_labels (set lines)))).
    { pose proof (f_equal (fun s => s n2) Hs) as E. cbn beta in E. apply prop_eq_iff in E.
      change ((0 INSERT set (MAP FST sec_labs)) n2) with (n2 IN (0 INSERT set (MAP FST sec_labs))) in E.
      change ((0 INSERT (set (MAP FST []) UNION BIGUNION (IMAGE line_get_code_labels (set lines)))) n2)
        with (n2 IN (0 INSERT (set (MAP FST ([] : list (N * N))) UNION
                                BIGUNION (IMAGE line_get_code_labels (set lines))))) in E.
      rewrite !IN_INSERT, IN_UNION, IN_set, IN_set in E. cbn [MAP map In] in E. rewrite E. tauto. }
    split.
    + intros [Hc|[(y & E & Hy)|Hl]]; [tauto| |tauto]. injection E as -> ->.
      left. left. change (is_true (MEM y (MAP fst ((0, pos) :: sec_labs)))) in Hy. apply MEM_In in Hy.
      cbn [MAP map In fst] in Hy.
      assert (Hy' : y = 0 \/ In y (MAP FST sec_labs)) by (destruct Hy; auto).
      apply Hn2 in Hy'. destruct Hy' as [->|Hy']; [left; reflexivity|right; exists y; auto].
    + intros [[[E|(y & E & Hy)]|Hc]|Hl]; [| |tauto|tauto].
      * right. left. injection E as -> ->. exists 0. split; [reflexivity|].
        change (is_true (MEM 0 (MAP fst ((0, pos) :: sec_labs)))). apply MEM_In. left. reflexivity.
      * right. left. injection E as -> ->. exists y. split; [reflexivity|].
        change (is_true (MEM y (MAP fst ((0, pos) :: sec_labs)))). apply MEM_In.
        assert (Hy' : y = 0 \/ y IN BIGUNION (IMAGE line_get_code_labels (set lines))) by auto.
        apply Hn2 in Hy'. cbn [MAP map In fst]. destruct Hy'; auto.
Qed.

End LabsExistPres.

(** ** Invariant: labels aligned at even positions *)

Section EvenLabels.
Context {a : N}.

(** HOL [even_labels]: recursion on the sections, then on the lines. *)
Fixpoint even_labels (pos : N) (l : list (sec a)) : Prop :=
  match l with
  | [] => True
  | Section_ k ys :: ls =>
      (fix go (pos : N) (ys : list (line a)) : Prop :=
         match ys with
         | [] => even_labels pos ls
         | y :: ys => (is_Label y -> EVEN pos) /\ go (pos + line_len y) ys
         end) pos ys
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "even_labels_def" *)
Theorem even_labels_def : forall pos k (y : line a) ys ls,
  (even_labels pos [] <-> True) /\
  (even_labels pos (Section_ k [] :: ls) <-> even_labels pos ls) /\
  (even_labels pos (Section_ k (y :: ys) :: ls) <->
     (is_Label y -> EVEN pos) /\ even_labels (pos + line_len y) (Section_ k ys :: ls)).
Proof. intros; repeat match goal with |- _ /\ _ => split end; split; intro Hx; exact Hx. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_even_labels_def" *)
Fixpoint lines_even_labels (pos : N) (l : list (line a)) : Prop :=
  match l with
  | [] => True
  | y :: ys => (is_Label y -> EVEN pos) /\ lines_even_labels (pos + line_len y) ys
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "even_labels_alt" *)
Theorem even_labels_alt : forall pos k (ls : list (line a)) ss,
  (even_labels pos [] <-> True) /\
  (even_labels pos (Section_ k ls :: ss) <->
     lines_even_labels pos ls /\ even_labels (pos + SUM (MAP line_len ls)) ss).
Proof.
  intros pos k ls ss. split; [tauto|]. revert pos.
  induction ls as [|y ys IH]; intros pos.
  - cbn. rewrite N.add_0_r. tauto.
  - change (even_labels pos (Section_ k (y :: ys) :: ss)) with
      ((is_Label y -> EVEN pos) /\ even_labels (pos + line_len y) (Section_ k ys :: ss)).
    rewrite IH. cbn [lines_even_labels MAP map SUM]. rewrite N.add_assoc. tauto.
Qed.

(** HOL [even_labels_strong]: recursion on the sections, then on the lines. *)
Fixpoint even_labels_strong (pos : N) (l : list (sec a)) : Prop :=
  match l with
  | [] => True
  | Section_ k ys :: ls =>
      (fix go (pos : N) (ys : list (line a)) : Prop :=
         match ys with
         | [] => EVEN pos /\ even_labels_strong pos ls
         | y :: ys => (is_Label y -> EVEN pos) /\ go (pos + line_len y) ys
         end) pos ys
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "even_labels_strong_def" *)
Theorem even_labels_strong_def : forall pos k (y : line a) ys ls,
  (even_labels_strong pos [] <-> True) /\
  (even_labels_strong pos (Section_ k [] :: ls) <-> EVEN pos /\ even_labels_strong pos ls) /\
  (even_labels_strong pos (Section_ k (y :: ys) :: ls) <->
     (is_Label y -> EVEN pos) /\ even_labels_strong (pos + line_len y) (Section_ k ys :: ls)).
Proof. intros; repeat match goal with |- _ /\ _ => split end; split; intro Hx; exact Hx. Qed.

Lemma even_labels_strong_alt pos k (ls : list (line a)) ss :
  even_labels_strong pos (Section_ k ls :: ss) <->
  lines_even_labels pos ls /\ EVEN (pos + SUM (MAP line_len ls)) /\
  even_labels_strong (pos + SUM (MAP line_len ls)) ss.
Proof.
  revert pos. induction ls as [|y ys IH]; intros pos.
  - cbn. rewrite N.add_0_r. tauto.
  - change (even_labels_strong pos (Section_ k (y :: ys) :: ss)) with
      ((is_Label y -> EVEN pos) /\ even_labels_strong (pos + line_len y) (Section_ k ys :: ss)).
    rewrite IH. cbn [lines_even_labels MAP map SUM]. rewrite N.add_assoc. tauto.
Qed.

Lemma lines_even_labels_ends pos (ls : list (line a)) :
  lines_even_labels pos ls -> EVERY label_zero ls -> negb (NULL ls) -> is_Label (LAST ls) ->
  EVEN (pos + SUM (MAP line_len ls)).
Proof.
  revert pos. induction ls as [|x [|y t] IH]; intros pos He Hz Hn Hl; [discriminate| |].
  - cbn [LAST] in Hl. cbn [lines_even_labels] in He. cbn [EVERY] in Hz.
    destruct x as [k1 k2 l| |]; try discriminate. cbn [label_zero] in Hz.
    rewrite Bool.andb_true_r in Hz. apply N.eqb_eq in Hz. subst l.
    cbn [MAP map SUM line_len]. rewrite !N.add_0_r. apply (proj1 He), Hl.
  - change (LAST (x :: y :: t)) with (LAST (y :: t)) in Hl.
    cbn [lines_even_labels] in He. cbn [EVERY] in Hz. apply Bool.andb_true_iff in Hz as [_ Hz].
    cbn [MAP map SUM]. rewrite N.add_assoc. apply IH; [exact (proj2 He)|exact Hz|reflexivity|exact Hl].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "even_labels_ends_imp_strong" *)
Theorem even_labels_ends_imp_strong : forall pos (code : list (sec a)),
  even_labels pos code /\
  EVERY sec_ends_with_label code /\
  EVERY sec_label_zero code ->
  even_labels_strong pos code.
Proof.
  intros pos code; revert pos. induction code as [|[k ls] code IH]; intros pos (He & Hs & Hz); [exact Logic.I|].
  apply even_labels_alt in He as [He1 He2]. apply even_labels_strong_alt.
  cbn [EVERY sec_ends_with_label sec_label_zero] in Hs, Hz.
  apply Bool.andb_true_iff in Hs as [Hs Hs']. apply Bool.andb_true_iff in Hs as [Hn Hl].
  apply Bool.andb_true_iff in Hz as [Hz Hz'].
  split; [exact He1|split; [exact (lines_even_labels_ends _ _ He1 Hz Hn Hl)|]].
  apply IH. auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "ALOOKUP_section_labels_ignore" *)
Theorem ALOOKUP_section_labels_ignore : forall n2 pos (lines : list (line a)) acc,
  ~ MEM n2 (MAP SND (extract_labels lines)) ->
  ALOOKUP (SND (section_labels pos lines acc)) n2 = ALOOKUP acc n2.
Proof.
  intros n2 pos lines; revert pos.
  induction lines as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos acc Hm;
    cbn [section_labels]; [reflexivity| | |]; cbn [extract_labels] in Hm; try (apply IH; exact Hm).
  unfold is_true in Hm. rewrite MEM_In in Hm. cbn [MAP map SND snd In] in Hm.
  assert (Hk : k2 <> n2) by (intros ->; apply Hm; left; reflexivity).
  assert (Hm' : ~ MEM n2 (MAP SND (extract_labels xs))).
  { unfold is_true. rewrite MEM_In. intros H. apply Hm. right. exact H. }
  destruct (k2 =? 0); rewrite IH by exact Hm'; [reflexivity|].
  cbn [ALOOKUP]. destruct (decide (k2 = n2)); [contradiction|reflexivity].
Qed.

End EvenLabels.

(** ** [all_enc_ok] from the light check *)

Section EncOkLight.
Context {a : N}.

Lemma line_ok_line_length (c : asm_config a) labs ffis pos (y : line a) :
  line_ok c labs ffis pos y -> line_length y = line_len y.
Proof.
  destruct y as [k1 k2 l|b bytes l|x w bytes l]; cbn [line_ok line_length line_len].
  - intros [_ ->]. reflexivity.
  - intros (_ & -> & _). reflexivity.
  - destruct x as [[l1 l2]|cc r ri [l1 l2]|v|r [l1 l2]|s| |]; cbn [get_label]; cbv zeta;
      try (intros (_ & -> & _); reflexivity); try contradiction;
      (destruct (lab_lookup l1 l2 labs); [intros (_ & -> & _); reflexivity|contradiction]).
Qed.

Lemma lines_ok_SUM (c : asm_config a) labs ffis pos (ls : list (line a)) :
  lines_ok c labs ffis pos ls -> SUM (MAP line_length ls) = SUM (MAP line_len ls).
Proof.
  revert pos. induction ls as [|y ys IH]; intros pos H; [reflexivity|].
  destruct H as [H1 H2]. cbn [MAP map SUM]. rewrite (line_ok_line_length _ _ _ _ _ H1), (IH _ H2).
  reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_ok_section_lab_lookup_even" *)
Theorem lines_ok_section_lab_lookup_even : forall (c : asm_config a) labs ffis l2 x pos
    (lines : list (line a)) acc,
  lines_ok c labs ffis pos lines /\
  (forall l2 x, ALOOKUP acc l2 = SOME x -> EVEN x) /\
  ALOOKUP (SND (section_labels pos lines acc)) l2 = SOME x ->
  EVEN x.
Proof.
  intros c labs ffis l2 x pos lines; revert pos.
  induction lines as [|y xs IH]; intros pos acc (Hok & Hacc & Hl).
  - exact (Hacc _ _ Hl).
  - destruct Hok as [Hy Hok]. pose proof (line_ok_line_length _ _ _ _ _ Hy) as Hlen.
    rewrite Hlen in Hok.
    destruct y as [k1 k2 l|b bytes l|x0 w bytes l]; cbn [section_labels] in Hl; cbn [line_len] in Hok.
    + destruct Hy as [Hev ->]. destruct (k2 =? 0).
      * exact (IH _ _ (conj Hok (conj Hacc Hl))).
      * apply (IH (pos + 0) ((k2, pos + 0) :: acc)). split; [exact Hok|split; [|exact Hl]]. intros l2' x' Hx'. cbn [ALOOKUP] in Hx'.
        destruct (decide (k2 = l2')); [injection Hx' as <-; rewrite N.add_0_r; exact Hev|].
        exact (Hacc _ _ Hx').
    + exact (IH _ _ (conj Hok (conj Hacc Hl))).
    + exact (IH _ _ (conj Hok (conj Hacc Hl))).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_ok_split" *)
Theorem all_enc_ok_split : forall (c : asm_config a) labs ffis pos k (lines : list (line a)) xs,
  all_enc_ok c labs ffis pos (Section_ k lines :: xs) ->
  all_enc_ok c labs ffis pos [Section_ k lines] /\
  all_enc_ok c labs ffis (pos + sec_length lines 0) xs.
Proof.
  intros c labs ffis pos k lines xs H. apply all_enc_ok_cons in H as (H1 & H2 & H3).
  rewrite sec_length_sum_line_len, N.add_0_r, <- (lines_ok_SUM _ _ _ _ _ H3).
  split; [|exact H1]. apply all_enc_ok_cons. split; [exact Logic.I|]. auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_ok_even" *)
Theorem all_enc_ok_even : forall (c : asm_config a) labs ffis k (lines : list (line a)) pos,
  all_enc_ok c labs ffis pos [Section_ k lines] ->
  EVEN (sec_length lines pos).
Proof.
  intros c labs ffis k lines pos H. apply all_enc_ok_cons in H as (_ & H2 & H3).
  rewrite sec_length_sum_line_len, <- (lines_ok_SUM _ _ _ _ _ H3), N.add_comm. exact H2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_ok_lab_lookup_even" *)
Theorem all_enc_ok_lab_lookup_even : forall (c : asm_config a) labs ffis pos
    (sec_list : list (sec a)) l1 l2 acc x,
  all_enc_ok c labs ffis pos sec_list /\
  lab_lookup l1 l2 (compute_labels_alt pos sec_list acc) = SOME x /\
  (forall x, lab_lookup l1 l2 acc = SOME x -> EVEN x) /\
  EVEN pos ->
  EVEN x.
Proof.
  intros c labs ffis pos sec_list l1 l2; revert pos.
  induction sec_list as [|[k lines] rest IH]; intros pos acc x (Hok & Hl & Hacc & Hev).
  - exact (Hacc _ Hl).
  - cbn [compute_labels_alt] in Hl.
    destruct (section_labels pos lines []) as [new_pos sec_labs] eqn:Es.
    pose proof (all_enc_ok_split _ _ _ _ _ _ _ Hok) as [Hok1 Hok2].
    pose proof (all_enc_ok_even _ _ _ _ _ _ Hok1) as Hev'.
    pose proof (section_labels_sec_length pos lines []) as Hp. rewrite Es in Hp. cbn [FST fst] in Hp.
    assert (Hnp : new_pos = pos + sec_length lines 0).
    { rewrite Hp, !sec_length_sum_line_len. lia. }
    apply (IH new_pos (insert k (fromAList ((0, pos) :: sec_labs)) acc)).
    split; [rewrite Hnp; exact Hok2|split; [exact Hl|split; [|rewrite Hp; exact Hev']]].
    intros x' Hx'. unfold lab_lookup in Hx'. rewrite lookup_insert in Hx'.
    destruct (decide (l1 = k)) as [->|Hne]; [|exact (Hacc _ Hx')].
    rewrite lookup_fromAList in Hx'. cbn [ALOOKUP] in Hx'.
    destruct (decide (0 = l2)); [injection Hx' as <-; exact Hev|].
    apply all_enc_ok_cons in Hok as (_ & _ & Hlines).
    apply (lines_ok_section_lab_lookup_even c labs ffis l2 x' pos lines []).
    split; [exact Hlines|split; [intros ? ? Hn; discriminate Hn|]]. rewrite Es. exact Hx'.
Qed.

Lemma line_length_ok_line_length (y : line a) : line_length_ok y -> line_length y = line_len y.
Proof.
  unfold line_length_ok, is_true. rewrite N.eqb_eq.
  destruct y as [k1 k2 l|b bytes l|x w bytes l]; cbn [line_bytes line_length line_len]; intros H;
    [|exact H|exact H].
  cbn in H. subst l. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_ok_pre_light_imp_line_ok" *)
Theorem line_ok_pre_light_imp_line_ok : forall (c : asm_config a) labs ffis pos (line : line a),
  line_ok_pre c line /\
  line_enc_with_nop (encode c) labs ffis pos line /\
  line_offset_ok labs ffis pos line /\
  line_labs_exist labs line /\
  line_ok_light c line /\ (is_Label line -> EVEN pos) ->
  line_ok c labs ffis pos line.
Proof.
  intros c labs ffis pos [k1 k2 l|b bytes l|x w bytes l] (Hpre & Henc & Hoff & Hex & Hlight & Hev).
  - cbn [line_enc_with_nop] in Henc. split; [apply Hev; reflexivity|exact Henc].
  - cbn [line_enc_with_nop] in Henc. cbn [line_ok_pre] in Hpre. destruct Henc as [He Hl].
    split; [exact He|split; [exact Hl|exact Hpre]].
  - cbn [line_offset_ok] in Hoff. subst w. cbn [line_labs_exist] in Hex.
    destruct x as [[l1 l2]|cc r ri [l1 l2]|v|r [l1 l2]|s| |];
      cbn [line_ok_light get_jump_offset get_label lab_inst] in Hlight;
      cbn [line_enc_with_nop] in Henc; cbn [line_ok get_label lab_inst]; cbv zeta.
    + apply bool_decide_spec in Hex. cbn [labs_of] in Hex.
      specialize (Hex l1 l2 ltac:(apply IN_INSERT; left; reflexivity)).
      destruct (lab_lookup l1 l2 labs) as [t|] eqn:El; [|contradiction].
      apply lab_lookup_IMP in El. rewrite El in Henc, Hlight. destruct Henc as [He Hl].
      split; [exact He|split; [exact Hl|exact Hlight]].
    + apply bool_decide_spec in Hex. cbn [labs_of] in Hex.
      specialize (Hex l1 l2 ltac:(apply IN_INSERT; left; reflexivity)).
      destruct (lab_lookup l1 l2 labs) as [t|] eqn:El; [|contradiction].
      apply lab_lookup_IMP in El. rewrite El in Henc, Hlight. destruct Henc as [He Hl].
      split; [exact He|split; [exact Hl|exact Hlight]].
    + discriminate Hlight.
    + apply bool_decide_spec in Hex. cbn [labs_of] in Hex.
      specialize (Hex l1 l2 ltac:(apply IN_INSERT; left; reflexivity)).
      destruct (lab_lookup l1 l2 labs) as [t|] eqn:El; [|contradiction].
      apply lab_lookup_IMP in El. rewrite El in Henc, Hlight. destruct Henc as [He Hl].
      split; [exact He|split; [exact Hl|exact Hlight]].
    + destruct Henc as [He Hl]. rewrite WORD_SUB_LZERO, (N.add_comm 3 (get_ffi_index _ _)) in *.
      split; [exact He|split; [exact Hl|exact Hlight]].
    + destruct Henc as [He Hl]. rewrite WORD_SUB_LZERO in *.
      split; [exact He|split; [exact Hl|exact Hlight]].
    + destruct Henc as [He Hl]. rewrite WORD_SUB_LZERO in *.
      split; [exact He|split; [exact Hl|exact Hlight]].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_ok_pre_light_imp_all_enc_ok" *)
Theorem all_enc_ok_pre_light_imp_all_enc_ok : forall (c : asm_config a) labs ffis pos
    (code : list (sec a)),
  all_enc_with_nop (encode c) labs ffis pos code /\
  all_enc_ok_pre c code /\
  EVERY (sec_ok_light c) code /\
  even_labels_strong pos code /\
  all_labs_exist labs code /\
  offset_ok labs ffis pos code ->
  all_enc_ok c labs ffis pos code.
Proof.
  intros c labs ffis pos code; revert pos.
  induction code as [|[k lines] rest IH]; intros pos; [intros; exact Logic.I|].
  revert pos. induction lines as [|y ys IHl]; intros pos (H1 & H2 & H3 & H4 & H5 & H6).
  - cbn [EVERY sec_ok_pre sec_ok_light sec_labs_exist andb] in H2, H3, H5.
    cbn [offset_ok lines_offset_ok MAP map SUM] in H6. rewrite N.add_0_r in H6.
    destruct H4 as [Hev H4]. split; [exact Hev|].
    apply IH. repeat split; try assumption. exact (proj2 H6).
  - destruct H1 as [Hy H1]. destruct H4 as [Hly H4].
    cbn [EVERY sec_ok_pre sec_ok_light sec_labs_exist] in H2, H3, H5.
    apply Bool.andb_true_iff in H2 as [H2 H2r]. apply Bool.andb_true_iff in H2 as [H2y H2].
    apply Bool.andb_true_iff in H3 as [H3 H3r]. apply Bool.andb_true_iff in H3 as [H3y H3].
    apply Bool.andb_true_iff in H5 as [H5 H5r]. apply Bool.andb_true_iff in H5 as [H5y H5].
    cbn [offset_ok lines_offset_ok MAP map SUM] in H6. destruct H6 as [[H6y H6] H6r].
    pose proof (line_length_ok_line_length _ (line_enc_with_nop_length_ok _ _ _ _ _ Hy)) as Hlen.
    split.
    + apply line_ok_pre_light_imp_line_ok. repeat split; assumption.
    + rewrite Hlen. rewrite Hlen in H1. apply IHl. split; [exact H1|].
      split; [cbn [EVERY sec_ok_pre]; rewrite H2, H2r; reflexivity|].
      split; [cbn [EVERY sec_ok_light]; rewrite H3, H3r; reflexivity|].
      split; [exact H4|].
      split; [cbn [EVERY sec_labs_exist]; rewrite H5, H5r; reflexivity|].
      cbn [offset_ok]. rewrite N.add_assoc in H6r. split; assumption.
Qed.

End EncOkLight.
