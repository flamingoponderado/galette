(** * CakeML [reg_allocProof]: the bijection and the graph functions

    Part of the [reg_allocProofScript] counterpart: the bijection built by
    [mk_bij] ([list_remap], [mk_bij_aux]) and the graph-manipulating
    functions ([sorted_insert], [insert_edge], [list_insert_edge],
    [clique_insert_edge], [extend_clique]).

    HOL's [list_remap_bij] and [mk_bij_aux_bij] are anonymous ([val ... =
    Q.prove]); they are ported untagged.  [markerTheory.Abbrev] wrappers
    are omitted.  HOL [$>] on [num] is [fun x y => y <? x]. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.coretypes Require Import pair.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From Galette.cakeml.compiler.backend.reg_alloc.proofs.reg_allocProof Require Import
  check_clash_tree ra_state colouring.
Open Scope N_scope.
Open Scope monad_scope.

Lemma In_MAP_FST_toAList {A} (t : spt A) k : In k (MAP fst (toAList t)) <-> k IN domain t.
Proof.
  pose proof (f_equal (fun P => P k) (set_MAP_FST_toAList_domain t)) as H; cbv beta in H.
  unfold pred_set.IN; rewrite <- H; symmetry; apply MEM_In.
Qed.

Lemma set_MAP_FST_toAList {A} (t : spt A) : set (MAP fst (toAList t)) = domain t.
Proof. apply EXTENSION; intros k; rewrite IN_set; apply In_MAP_FST_toAList. Qed.

(** ** The bijection *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "list_remap_domain" *)
Theorem list_remap_domain : forall ls ta fa n ta' fa' n',
  list_remap ls (ta, (fa, n)) = (ta', (fa', n')) ->
  domain ta' = domain ta UNION set ls.
Proof.
  induction ls as [|x xs IH]; intros ta fa n ta' fa' n' H; cbn [list_remap] in H.
  - inversion H; subst; apply set_ext; intros z; unfold_sets; cbn [LIST_TO_SET]; tauto.
  - destruct (lookup x ta) as [v|] eqn:E; apply IH in H; rewrite H; apply set_ext; intros z.
    + assert (domain ta x) by (apply domain_lookup; eauto).
      unfold_sets; cbn [LIST_TO_SET]; intuition (subst; auto).
    + rewrite domain_insert; unfold_sets; cbn [LIST_TO_SET]; tauto.
Qed.

(** HOL's anonymous [list_remap_bij]. *)
Lemma list_remap_bij : forall ls ta fa n ta' fa' n',
  list_remap ls (ta, (fa, n)) = (ta', (fa', n')) /\
  sp_inverts ta fa /\ sp_inverts fa ta /\ domain fa = count n ->
  sp_inverts ta' fa' /\ sp_inverts fa' ta' /\ domain fa' = count n'.
Proof.
  induction ls as [|x xs IH]; intros ta fa n ta' fa' n' (H & H1 & H2 & H3); cbn [list_remap] in H.
  - inversion H; subst; auto.
  - destruct (lookup x ta) as [v|] eqn:E; eapply IH; (split; [exact H|]); [auto|].
    assert (Hx : x NOTIN domain ta) by (unfold pred_set.IN; rewrite domain_lookup; intros [? ?]; congruence).
    assert (Hn : n NOTIN domain fa) by (rewrite H3; unfold pred_set.IN, count; lia).
    split; [apply sp_inverts_insert; auto|split; [apply sp_inverts_insert; auto|]].
    rewrite domain_insert, H3; apply set_ext; intros z; unfold_sets; unfold count; lia.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "mk_bij_aux_domain" *)
Theorem mk_bij_aux_domain : forall ct ta fa n ta' fa' n',
  mk_bij_aux ct (ta, (fa, n)) = (ta', (fa', n')) ->
  domain ta' = domain ta UNION (fun x => in_clash_tree ct x).
Proof.
  induction ct as [w r|t|topt t1 IH1 t2 IH2|t1 IH1 t2 IH2]; intros ta fa n ta' fa' n' H;
    cbn [mk_bij_aux in_clash_tree] in *.
  - destruct (list_remap r (ta, (fa, n))) as [ta1 [fa1 n1]] eqn:E1.
    apply list_remap_domain in E1, H. rewrite H, E1.
    apply EXTENSION; intros z; rewrite !IN_UNION, !IN_set; unfold pred_set.IN; rewrite <- !MEM_In; tauto.
  - apply list_remap_domain in H; rewrite H, set_MAP_FST_toAList; reflexivity.
  - destruct (mk_bij_aux t1 (ta, (fa, n))) as [ta1 [fa1 n1]] eqn:E1.
    destruct (mk_bij_aux t2 (ta1, (fa1, n1))) as [ta2 [fa2 n2]] eqn:E2.
    apply IH1 in E1; apply IH2 in E2.
    destruct topt as [ts|].
    + apply list_remap_domain in H; rewrite H, set_MAP_FST_toAList, E2, E1.
      apply set_ext; intros z; unfold_sets; tauto.
    + inversion H; subst. rewrite E2, E1. apply set_ext; intros z; unfold_sets; tauto.
  - destruct (mk_bij_aux t2 (ta, (fa, n))) as [ta1 [fa1 n1]] eqn:E1.
    apply IH2 in E1; apply IH1 in H. rewrite H, E1. apply set_ext; intros z; unfold_sets; tauto.
Qed.

(** HOL's anonymous [mk_bij_aux_bij]. *)
Lemma mk_bij_aux_bij : forall ct ta fa n ta' fa' n',
  mk_bij_aux ct (ta, (fa, n)) = (ta', (fa', n')) /\
  sp_inverts ta fa /\ sp_inverts fa ta /\ domain fa = count n ->
  sp_inverts ta' fa' /\ sp_inverts fa' ta' /\ domain fa' = count n'.
Proof.
  induction ct as [w r|t|topt t1 IH1 t2 IH2|t1 IH1 t2 IH2]; intros ta fa n ta' fa' n' (H & Hi);
    cbn [mk_bij_aux] in H.
  - destruct (list_remap r (ta, (fa, n))) as [ta1 [fa1 n1]] eqn:E1.
    eapply list_remap_bij; split; [exact H|]. eapply list_remap_bij; eauto.
  - eapply list_remap_bij; eauto.
  - destruct (mk_bij_aux t1 (ta, (fa, n))) as [ta1 [fa1 n1]] eqn:E1.
    destruct (mk_bij_aux t2 (ta1, (fa1, n1))) as [ta2 [fa2 n2]] eqn:E2.
    pose proof (IH1 _ _ _ _ _ _ (conj E1 Hi)) as Hi1.
    pose proof (IH2 _ _ _ _ _ _ (conj E2 Hi1)) as Hi2.
    destruct topt as [ts|]; [eapply list_remap_bij; eauto|inversion H; subst; exact Hi2].
  - destruct (mk_bij_aux t2 (ta, (fa, n))) as [ta1 [fa1 n1]] eqn:E1.
    eapply IH1; split; [exact H|]. eapply IH2; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "list_remap_wf" *)
Theorem list_remap_wf : forall l ta fa n ta' fa' n',
  list_remap l (ta, (fa, n)) = (ta', (fa', n')) /\ wf ta /\ wf fa -> wf ta' /\ wf fa'.
Proof.
  induction l as [|x xs IH]; intros ta fa n ta' fa' n' (H & W1 & W2); cbn [list_remap] in H.
  - inversion H; subst; auto.
  - destruct (lookup x ta); eapply IH; (split; [exact H|]); auto.
    split; apply wf_insert; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "mk_bij_aux_wf" *)
Theorem mk_bij_aux_wf : forall ct ta fa n ta' fa' n',
  mk_bij_aux ct (ta, (fa, n)) = (ta', (fa', n')) /\ wf ta /\ wf fa -> wf ta' /\ wf fa'.
Proof.
  induction ct as [w r|t|topt t1 IH1 t2 IH2|t1 IH1 t2 IH2]; intros ta fa n ta' fa' n' (H & W);
    cbn [mk_bij_aux] in H.
  - destruct (list_remap r (ta, (fa, n))) as [ta1 [fa1 n1]] eqn:E1.
    eapply list_remap_wf; split; [exact H|]. eapply list_remap_wf; eauto.
  - eapply list_remap_wf; eauto.
  - destruct (mk_bij_aux t1 (ta, (fa, n))) as [ta1 [fa1 n1]] eqn:E1.
    destruct (mk_bij_aux t2 (ta1, (fa1, n1))) as [ta2 [fa2 n2]] eqn:E2.
    pose proof (IH1 _ _ _ _ _ _ (conj E1 W)) as W1.
    pose proof (IH2 _ _ _ _ _ _ (conj E2 W1)) as W2.
    destruct topt as [ts|]; [eapply list_remap_wf; eauto|inversion H; subst; exact W2].
  - destruct (mk_bij_aux t2 (ta, (fa, n))) as [ta1 [fa1 n1]] eqn:E1.
    eapply IH1; split; [exact H|]. eapply IH2; eauto.
Qed.

(** ** Cliques and subgraphs *)

(** The list represents a clique. *)
(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "is_clique_def" *)
Definition is_clique (ls : list N) (adjls : list (list N)) : Prop :=
  forall x y, MEM x ls /\ MEM y ls /\ x <> y -> has_edge adjls x y.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "is_subgraph_def" *)
Definition is_subgraph (g h : list (list N)) : Prop :=
  forall x y, has_edge g x y -> has_edge h x y.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "is_subgraph_refl" *)
Theorem is_subgraph_refl : forall s, is_subgraph s s.
Proof. intros s x y H; exact H. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "is_subgraph_trans" *)
Theorem is_subgraph_trans : forall s s' s'',
  is_subgraph s s' /\ is_subgraph s' s'' -> is_subgraph s s''.
Proof. intros s s' s'' [H1 H2] x y H; apply H2, H1, H. Qed.

(** ** Sorted adjacency lists *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "GT_TRANS" *)
Theorem GT_TRANS : forall a b c : N, a > b /\ b > c -> a > c.
Proof. intros; lia. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "GT_sorted_eq" *)
Theorem GT_sorted_eq : forall x L,
  SORTED (fun x y => y <? x) (x :: L) <->
  SORTED (fun x y => y <? x) L /\ (forall y, MEM y L -> x > y).
Proof.
  intros x L; revert x; induction L as [|y L IH]; intros x.
  - split; [intros _; split; [reflexivity|intros y Hy; discriminate]|intros _; reflexivity].
  - cbn [SORTED]; rewrite andb_iff, ltb_iff. fold (SORTED (fun x y => y <? x) (y :: L)).
    rewrite (IH y). split.
    + intros (Hyx & HL & Hy). split; [split; assumption|].
      intros z Hz; cbn [MEM] in Hz; apply orb_iff in Hz as [Hz|Hz];
        [apply bool_decide_iff in Hz; subst; lia|specialize (Hy z Hz); lia].
    + intros ((HL & Hy) & Hx). split; [|split; [exact HL|exact Hy]].
      specialize (Hx y); cbn [MEM] in Hx; enough (x > y) by lia; apply Hx, orb_iff; left; apply bool_decide_iff; reflexivity.
Qed.

Lemma SORTED_gt_cons x L :
  is_true (SORTED (fun x y => y <? x) (x :: L)) <->
  is_true (SORTED (fun x y => y <? x) L) /\ (forall y, In y L -> y < x).
Proof.
  rewrite GT_sorted_eq; split; intros [H1 H2]; split; auto; intros y Hy;
    [apply MEM_In in Hy|apply MEM_In in Hy]; specialize (H2 y Hy); lia.
Qed.

Lemma SORTED_gt_app l1 l2 :
  is_true (SORTED (fun x y => y <? x) (l1 ++ l2)) <->
  is_true (SORTED (fun x y => y <? x) l1) /\ is_true (SORTED (fun x y => y <? x) l2) /\
  (forall a b, In a l1 -> In b l2 -> b < a).
Proof.
  induction l1 as [|x l1 IH]; cbn [app].
  - split; [intros H; split; [reflexivity|split; [exact H|intros a b []]]|tauto].
  - rewrite !SORTED_gt_cons, IH. split.
    + intros ((H1 & H2 & H3) & H4). split; [split; [exact H1|]|split; [exact H2|]].
      * intros y Hy; apply H4, in_or_app; left; exact Hy.
      * intros a b [<-|Ha] Hb; [apply H4, in_or_app; right; exact Hb|apply H3; assumption].
    + intros ((H1 & H4) & H2 & H3). split; [split; [exact H1|split; [exact H2|]]|].
      * intros a b Ha Hb; apply H3; [right|]; assumption.
      * intros y Hy; apply in_app_or in Hy as [Hy|Hy]; [apply H4, Hy|apply H3; [left; reflexivity|exact Hy]].
Qed.

Fixpoint ins (x : N) (l : list N) : list N :=
  match l with
  | [] => [x]
  | y :: ys => if x =? y then y :: ys else if y <? x then x :: y :: ys else y :: ins x ys
  end.

Lemma sorted_insert_ins x ls : forall acc, sorted_insert x acc ls = REVERSE acc ++ ins x ls.
Proof.
  induction ls as [|y ys IH]; intros acc; cbn [sorted_insert ins]; [reflexivity|].
  destruct (x =? y); [reflexivity|]. destruct (y <? x); [reflexivity|].
  rewrite IH; cbn [REVERSE rev]; rewrite <- app_assoc; reflexivity.
Qed.

Lemma ins_correct x ls :
  is_true (SORTED (fun x y => y <? x) ls) ->
  is_true (SORTED (fun x y => y <? x) (ins x ls)) /\ (forall z, In z (ins x ls) <-> x = z \/ In z ls).
Proof.
  induction ls as [|y ys IH]; intros Hs; cbn [ins].
  - split; [reflexivity|intros z; cbn [In]; tauto].
  - apply SORTED_gt_cons in Hs as [Hs Hy].
    destruct (N.eqb_spec x y) as [->|Hxy].
    + split; [apply SORTED_gt_cons; auto|intros z; cbn [In]; intuition].
    + destruct (N.ltb_spec y x) as [Hlt|Hge].
      * split; [|intros z; cbn [In]; tauto].
        apply SORTED_gt_cons; split; [apply SORTED_gt_cons; auto|].
        intros z [<-|Hz]; [exact Hlt|specialize (Hy z Hz); lia].
      * destruct (IH Hs) as [Hs' Hm]. split.
        -- apply SORTED_gt_cons; split; [exact Hs'|]. intros z Hz; apply Hm in Hz as [<-|Hz]; [lia|auto].
        -- intros z; cbn [In]; rewrite Hm; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "sorted_insert_correct_lem" *)
Theorem sorted_insert_correct_lem : forall x ls acc,
  SORTED (fun x y => y <? x) ls /\
  SORTED (fun x y => y <? x) (REVERSE acc) /\
  SORTED (fun x y => y <? x) (REVERSE acc ++ ls) /\
  EVERY (fun y => x <? y) acc ->
  hide (SORTED (fun x y => y <? x) (sorted_insert x acc ls) /\
        forall z, MEM z (sorted_insert x acc ls) <-> x = z \/ MEM z ls \/ MEM z acc).
Proof.
  intros x ls acc (H1 & H2 & H3 & H4). unfold hide. rewrite sorted_insert_ins.
  destruct (ins_correct x ls H1) as [Hs Hm].
  apply SORTED_gt_app in H3 as (_ & _ & H3). rewrite EVERY_iff in H4. split.
  - apply SORTED_gt_app; split; [exact H2|split; [exact Hs|]].
    intros a b Ha Hb; apply Hm in Hb as [<-|Hb]; [|apply H3; assumption].
    apply in_rev in Ha; apply ltb_iff, H4, Ha.
  - intros z; rewrite !MEM_iff, in_app_iff, Hm, <- in_rev; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "sorted_insert_correct" *)
Theorem sorted_insert_correct : forall x ls,
  SORTED (fun x y => y <? x) ls ->
  SORTED (fun x y => y <? x) (sorted_insert x [] ls) /\
  forall z, MEM z (sorted_insert x [] ls) <-> x = z \/ MEM z ls.
Proof.
  intros x ls H. pose proof (sorted_insert_correct_lem x ls []) as Hl.
  unfold hide in Hl; destruct Hl as [Hs Hm]; [repeat split; auto|].
  split; [exact Hs|intros z; rewrite Hm; cbn [MEM]; intuition discriminate].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "sorted_mem_correct" *)
Theorem sorted_mem_correct : forall x ls,
  SORTED (fun x y => y <? x) ls -> (sorted_mem x ls <-> MEM x ls).
Proof.
  intros x; induction ls as [|y ys IH]; intros Hs; cbn [sorted_mem MEM]; [tauto|].
  apply SORTED_gt_cons in Hs as [Hs Hy]. rewrite orb_iff, bool_decide_iff.
  destruct (N.eqb_spec x y) as [->|Hxy]; [split; auto|].
  destruct (N.ltb_spec y x) as [Hlt|Hge].
  - split; [discriminate|intros [?|Hm]; [congruence|]]. apply MEM_In, Hy in Hm; lia.
  - rewrite IH by exact Hs; tauto.
Qed.

(** ** Adding edges *)

Lemma MEM_sorted_insert x l z :
  is_true (SORTED (fun x y => y <? x) l) ->
  (In z (sorted_insert x [] l) <-> x = z \/ In z l).
Proof. intros H; rewrite <- !MEM_In; apply (sorted_insert_correct x l H). Qed.

Lemma SORTED_sorted_insert x l :
  is_true (SORTED (fun x y => y <? x) l) -> is_true (SORTED (fun x y => y <? x) (sorted_insert x [] l)).
Proof. intros H; apply (sorted_insert_correct x l H). Qed.

Lemma good_ra_state_with_adj_ls s A :
  good_ra_state s -> LENGTH A = s.(dim) ->
  (forall i v, i < LENGTH A -> In v (EL i A) -> v < s.(dim)) ->
  (forall i, i < LENGTH A -> is_true (SORTED (fun x y => y <? x) (EL i A))) ->
  undirected A -> good_ra_state (with_adj_ls s A).
Proof.
  intros (L1 & L2 & L3 & L4 & L5 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & Hu) HL HB HS HU.
  unfold good_ra_state; rs. do 6 (split; [assumption|]).
  split; [|split; [|do 5 (split; [assumption|]); exact HU]].
  - apply EVERY_iff; intros l Hl; apply In_EL in Hl as (i & Hi & ->).
    apply EVERY_iff; intros v Hv; apply ltb_iff; eapply HB; eauto.
  - apply EVERY_iff; intros l Hl; apply In_EL in Hl as (i & Hi & ->); apply HS, Hi.
Qed.

Lemma good_adj_facts s :
  good_ra_state s ->
  (forall i v, i < LENGTH s.(adj_ls) -> In v (EL i s.(adj_ls)) -> v < s.(dim)) /\
  (forall i, i < LENGTH s.(adj_ls) -> is_true (SORTED (fun x y => y <? x) (EL i s.(adj_ls)))).
Proof.
  intros Hg; pose proof Hg as (L1 & L2 & L3 & L4 & L5 & B1 & B2 & B3 & _). split.
  - intros i v Hi Hv; eapply good_bound_adj; eauto; lia.
  - intros i Hi; rewrite EVERY_iff in B3; apply B3, EL_In, Hi.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "insert_edge_succeeds" *)
Theorem insert_edge_succeeds : forall s x y,
  good_ra_state s /\ y < s.(dim) /\ x < s.(dim) ->
  exists s',
    insert_edge x y s = (M_success tt, s') /\
    good_ra_state s' /\
    s' = with_adj_ls s s'.(adj_ls) /\
    forall a b, has_edge s'.(adj_ls) a b <->
      (a = x /\ b = y) \/ (a = y /\ b = x) \/ has_edge s.(adj_ls) a b.
Proof.
  intros s x y (Hg & Hy & Hx).
  pose proof Hg as (L1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hu).
  destruct (good_adj_facts s Hg) as [HB HS].
  unfold insert_edge.
  mstep' (adj_ls_sub_ok x s ltac:(lia)). mstep' (adj_ls_sub_ok y s ltac:(lia)).
  mstep (update_adj_ls_ok x (sorted_insert y [] (EL x (adj_ls s))) s ltac:(lia)). rs.
  rewrite (update_adj_ls_ok y _ _) by (rs; rewrite LENGTH_LUPDATE; lia). rs.
  eexists; split; [reflexivity|]. rs.
  set (A := adj_ls s) in *.
  set (A2 := LUPDATE (sorted_insert x [] (EL y A)) y (LUPDATE (sorted_insert y [] (EL x A)) x A)).
  assert (Hlen : LENGTH A2 = LENGTH A) by (subst A2; rewrite !LENGTH_LUPDATE; reflexivity).
  assert (HEL : forall a, a < LENGTH A -> EL a A2 =
    if decide (a = y) then sorted_insert x [] (EL y A)
    else if decide (a = x) then sorted_insert y [] (EL x A) else EL a A).
  { intros a Ha; subst A2; rewrite !EL_LUPDATE, LENGTH_LUPDATE.
    destruct (decide (y = a /\ a < LENGTH A)) as [[<- _]|Hd1];
      [destruct (decide (y = y)); [reflexivity|congruence]|].
    destruct (decide (a = y)) as [->|]; [exfalso; apply Hd1; auto|].
    destruct (decide (x = a /\ a < LENGTH A)) as [[<- _]|Hd2];
      [destruct (decide (x = x)); [reflexivity|congruence]|].
    destruct (decide (a = x)) as [->|]; [exfalso; apply Hd2; auto|reflexivity]. }
  assert (Hedge : forall a b, has_edge A2 a b <-> (a = x /\ b = y) \/ (a = y /\ b = x) \/ has_edge A a b).
  { intros a b; unfold has_edge; rewrite Hlen, !MEM_iff. split.
    - intros (Ha & Hb & Hm). rewrite HEL in Hm by exact Ha.
      destruct (decide (a = y)) as [->|Hay].
      + apply MEM_sorted_insert in Hm as [<-|Hm]; [tauto|right; right; auto|apply HS; lia].
      + destruct (decide (a = x)) as [->|Hax].
        * apply MEM_sorted_insert in Hm as [<-|Hm]; [tauto|right; right; auto|apply HS; lia].
        * right; right; auto.
    - intros [[-> ->]|[[-> ->]|(Ha & Hb & Hm)]]; (split; [lia|split; [lia|]]); rewrite HEL by lia.
      + destruct (decide (x = y)) as [->|]; [apply MEM_sorted_insert; [apply HS; lia|left; reflexivity]|].
        destruct (decide (x = x)); [|congruence]. apply MEM_sorted_insert; [apply HS; lia|left; reflexivity].
      + destruct (decide (y = y)); [|congruence]. apply MEM_sorted_insert; [apply HS; lia|left; reflexivity].
      + destruct (decide (a = y)) as [->|]; [apply MEM_sorted_insert; [apply HS; lia|right; exact Hm]|].
        destruct (decide (a = x)) as [->|]; [apply MEM_sorted_insert; [apply HS; lia|right; exact Hm]|exact Hm]. }
  split; [|split; [reflexivity|exact Hedge]].
  change (good_ra_state (with_adj_ls s A2)).
  apply good_ra_state_with_adj_ls; [exact Hg|lia| | |].
  - intros i v Hi Hv; rewrite Hlen in Hi; rewrite HEL in Hv by exact Hi.
    destruct (decide (i = y)) as [->|]; [apply MEM_sorted_insert in Hv as [<-|Hv]; [lia|eapply HB; eauto|apply HS; lia]|].
    destruct (decide (i = x)) as [->|]; [apply MEM_sorted_insert in Hv as [<-|Hv]; [lia|eapply HB; eauto|apply HS; lia]|].
    eapply HB; eauto.
  - intros i Hi; rewrite Hlen in Hi; rewrite HEL by exact Hi.
    destruct (decide (i = y)) as [->|]; [apply SORTED_sorted_insert, HS; lia|].
    destruct (decide (i = x)) as [->|]; [apply SORTED_sorted_insert, HS; lia|apply HS; exact Hi].
  - intros a b H; apply Hedge in H; apply Hedge.
    destruct H as [[-> ->]|[[-> ->]|H]]; [tauto|tauto|right; right; apply Hu, H].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "list_insert_edge_succeeds" *)
Theorem list_insert_edge_succeeds : forall ys x s,
  good_ra_state s /\ x < s.(dim) /\ EVERY (fun y => y <? s.(dim)) ys ->
  exists s',
    list_insert_edge x ys s = (M_success tt, s') /\
    good_ra_state s' /\
    s' = with_adj_ls s s'.(adj_ls) /\
    forall a b, has_edge s'.(adj_ls) a b <->
      (a = x /\ MEM b ys) \/ (b = x /\ MEM a ys) \/ has_edge s.(adj_ls) a b.
Proof.
  induction ys as [|y ys IH]; intros x s (Hg & Hx & Hys); cbn [list_insert_edge].
  - exists s; split; [reflexivity|split; [exact Hg|split; [destruct s; reflexivity|]]].
    intros a b; cbn [MEM]; intuition discriminate.
  - cbn [EVERY] in Hys; apply andb_iff in Hys as [Hy Hys]; apply ltb_iff in Hy.
    destruct (insert_edge_succeeds s x y (conj Hg (conj Hy Hx))) as (s1 & E1 & Hg1 & Hw1 & He1).
    mstep E1. wsubst Hw1. rs.
    destruct (IH x (with_adj_ls s t)) as (s2 & E2 & Hg2 & Hw2 & He2); [rs; auto|].
    rewrite E2. wsubst Hw2. rs.
    exists (with_adj_ls s t0); split; [reflexivity|split; [exact Hg2|split; [reflexivity|]]].
    intros a b; rs; rewrite He2, He1; cbn [MEM]; rewrite !orb_iff, !bool_decide_iff.
    intuition (subst; auto).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "clique_insert_edge_succeeds" *)
Theorem clique_insert_edge_succeeds : forall ls s,
  good_ra_state s /\ EVERY (fun y => y <? s.(dim)) ls ->
  exists s',
    clique_insert_edge ls s = (M_success tt, s') /\
    good_ra_state s' /\
    s' = with_adj_ls s s'.(adj_ls) /\
    is_clique ls s'.(adj_ls) /\
    is_subgraph s.(adj_ls) s'.(adj_ls).
Proof.
  induction ls as [|x xs IH]; intros s (Hg & Hev); cbn [clique_insert_edge].
  - exists s; split; [reflexivity|split; [exact Hg|split; [destruct s; reflexivity|]]].
    split; [intros a b (Ha & _); discriminate|apply is_subgraph_refl].
  - cbn [EVERY] in Hev; apply andb_iff in Hev as [Hx Hev]; apply ltb_iff in Hx.
    destruct (list_insert_edge_succeeds xs x s (conj Hg (conj Hx Hev))) as (s1 & E1 & Hg1 & Hw1 & He1).
    mstep E1. wsubst Hw1. rs.
    destruct (IH (with_adj_ls s t)) as (s2 & E2 & Hg2 & Hw2 & Hc2 & Hs2); [rs; auto|].
    rewrite E2. wsubst Hw2. rs.
    exists (with_adj_ls s t0); split; [reflexivity|split; [exact Hg2|split; [reflexivity|]]].
    split.
    + intros a b (Ha & Hb & Hab). cbn [MEM] in Ha, Hb; apply orb_iff in Ha, Hb.
      rewrite !bool_decide_iff in Ha, Hb.
      destruct Ha as [->|Ha], Hb as [->|Hb]; [congruence| | |apply Hc2; auto].
      * apply Hs2, He1; left; auto.
      * apply Hs2, He1; right; left; auto.
    + intros a b H; apply Hs2, He1; right; right; exact H.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "extend_clique_succeeds" *)
Theorem extend_clique_succeeds : forall ls cli s,
  good_ra_state s /\ is_clique cli s.(adj_ls) /\ EVERY (fun y => y <? s.(dim)) ls /\
  ALL_DISTINCT cli /\ EVERY (fun y => y <? s.(dim)) cli ->
  exists cli' s',
    extend_clique ls cli s = (M_success cli', s') /\
    good_ra_state s' /\
    ALL_DISTINCT cli' /\
    s' = with_adj_ls s s'.(adj_ls) /\
    set cli' = set (cli ++ ls) /\
    is_clique cli' s'.(adj_ls) /\
    is_subgraph s.(adj_ls) s'.(adj_ls).
Proof.
  induction ls as [|x xs IH]; intros cli s (Hg & Hc & Hls & Hd & Hcli); cbn [extend_clique].
  - exists cli, s; split; [reflexivity|split; [exact Hg|split; [exact Hd|split; [destruct s; reflexivity|]]]].
    rewrite app_nil_r; split; [reflexivity|split; [exact Hc|apply is_subgraph_refl]].
  - cbn [EVERY] in Hls; apply andb_iff in Hls as [Hx Hls]; apply ltb_iff in Hx.
    destruct (MEM x cli) eqn:Em.
    + destruct (IH cli s) as (cli' & s' & E & H1 & H2 & H3 & H4 & H5 & H6); [auto|].
      exists cli', s'; split; [exact E|split; [exact H1|split; [exact H2|split; [exact H3|]]]].
      split; [|split; [exact H5|exact H6]]. rewrite H4.
      apply EXTENSION; intros z; rewrite !IN_set, !in_app_iff; cbn [In].
      apply MEM_In in Em; intuition (subst; auto).
    + destruct (list_insert_edge_succeeds cli x s (conj Hg (conj Hx Hcli))) as (s1 & E1 & Hg1 & Hw1 & He1).
      mstep E1. wsubst Hw1. rs.
      destruct (IH (x :: cli) (with_adj_ls s t)) as (cli' & s2 & E2 & Hg2 & Hd2 & Hw2 & Hset & Hc2 & Hs2).
      { rs. split; [exact Hg1|split; [|split; [exact Hls|split]]].
        - intros a b (Ha & Hb & Hab); apply He1. cbn [MEM] in Ha, Hb; apply orb_iff in Ha, Hb.
          rewrite !bool_decide_iff in Ha, Hb.
          destruct Ha as [->|Ha], Hb as [->|Hb]; [congruence|tauto|tauto|].
          right; right; apply Hc; auto.
        - cbn [ALL_DISTINCT]; rewrite Em; exact Hd.
        - cbn [EVERY]; apply andb_iff; split; [apply ltb_iff; exact Hx|exact Hcli]. }
      rewrite E2. wsubst Hw2. rs.
      exists cli', (with_adj_ls s t0); split; [reflexivity|split; [exact Hg2|split; [exact Hd2|split; [reflexivity|]]]].
      split; [|split; [exact Hc2|]].
      * rewrite Hset; apply EXTENSION; intros z; rewrite !IN_set, !in_app_iff; cbn [In]; tauto.
      * intros a b H; apply Hs2, He1; right; right; exact H.
Qed.
