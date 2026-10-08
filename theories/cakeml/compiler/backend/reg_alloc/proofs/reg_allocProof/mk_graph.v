(** * CakeML [reg_allocProof]: [mk_graph] and the clash-tree check

    Part of the [reg_allocProofScript] counterpart: [mk_graph] succeeds and
    any colouring of the graph it builds passes [check_clash_tree].

    HOL's local [domain_difference] is [sptree]'s [domain_difference] and
    is not ported again.  HOL [{x | P x}] is [fun x => P x]; HOL [g o f] is
    [g ∘ f]. *)

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
  check_clash_tree ra_state colouring graph.
Open Scope N_scope.
Open Scope monad_scope.

(** ** Helpers (Galette infrastructure) *)

Ltac ret := rewrite ?(bind_ok _ _ _ _ _ (return_eq _ _)); cbv beta.

Lemma EVERY_lt_iff l d : is_true (EVERY (fun y => y <? d) l) <-> (forall y, In y l -> y < d).
Proof. rewrite EVERY_iff; split; intros H y Hy; apply ltb_iff, H, Hy. Qed.

Lemma set_eq_iff {A} (l1 l2 : list A) : set l1 = set l2 <-> (forall z, In z l1 <-> In z l2).
Proof. rewrite EXTENSION; split; intros H z; specialize (H z); rewrite ?IN_set in *; exact H. Qed.

Lemma INJ_mono {A B} (f : A -> B) (S S' : A -> Prop) T :
  INJ f S T -> (forall x, S' x -> S x) -> INJ f S' T.
Proof. intros H Hs; apply (INJ_less f S); split; [exact H|intros x; apply Hs]. Qed.

Lemma NoDup_map_inj {A B} (f : A -> B) l :
  NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup (List.map f l).
Proof.
  induction l as [|x l IH]; intros Hd Hi; cbn [List.map]; [constructor|].
  inversion Hd as [|? ? Hx Hd']; subst. constructor.
  - intros Hin; apply in_map_iff in Hin as (y & Hy & Hyl).
    assert (y = x) by (apply Hi; [right|left|]; auto). subst; contradiction.
  - apply IH; [exact Hd'|intros a b Ha Hb; apply Hi; right; assumption].
Qed.

Lemma NoDup_map_inv_inj {A B} (f : A -> B) l :
  NoDup (List.map f l) -> forall x y, In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|z l IH]; intros Hd x y Hx Hy E; [destruct Hx|].
  cbn [List.map] in Hd; inversion Hd as [|? ? Hz Hd']; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; auto.
  - exfalso; apply Hz; rewrite E; apply in_map, Hy.
  - exfalso; apply Hz; rewrite <- E; apply in_map, Hx.
Qed.

Lemma check_col_Some {A} f (t : num_map A) a b :
  check_col f t = Some (a, b) ->
  a = t /\ b = fromAList (MAP (fun x => (x, tt)) (MAP (fun x => f (FST x)) (toAList t))) /\
  is_true (ALL_DISTINCT (MAP (fun x => f (FST x)) (toAList t))).
Proof. unfold check_col; destruct (ALL_DISTINCT _) eqn:E; [intros [= <- <-]; auto|discriminate]. Qed.

Lemma domain_fromAList_unit (l : list N) :
  domain (fromAList (MAP (fun x => (x, tt)) l)) = set l.
Proof.
  rewrite domain_fromAList; apply EXTENSION; intros z; rewrite IN_set; unfold pred_set.IN.
  rewrite MEM_iff, List.map_map, List.map_id; reflexivity.
Qed.

Lemma MAP_FST_toAList_eq {A} (f : N -> N) (t : num_map A) :
  MAP (fun x => f (FST x)) (toAList t) = MAP f (MAP fst (toAList t)).
Proof. rewrite List.map_map; reflexivity. Qed.

(** ** Colourings *)

(** The colouring of the graph needed for [check_clash_tree]; it is
    generated from the node tags. *)
(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "colouring_satisfactory_def" *)
Definition colouring_satisfactory (col : N -> N) (adjls : list (list N)) : Prop :=
  forall x, x < LENGTH adjls ->
    forall y, y < LENGTH adjls /\ MEM y (EL x adjls) -> col x = col y -> x = y.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "INJ_COMPOSE_IMAGE" *)
Theorem INJ_COMPOSE_IMAGE : forall {A B C} (f : A -> B) (g : B -> C) a b u,
  INJ f a b /\ INJ g (IMAGE f a) u -> INJ (g ∘ f) a u.
Proof.
  intros A B C f g a b u [H1 H2]; apply (INJ_COMPOSE f g a (IMAGE f a) u); split; [|exact H2].
  apply (INJ_IMAGE f a b H1).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "colouring_satisfactory_cliques" *)
Theorem colouring_satisfactory_cliques : forall ls g (f : N -> N),
  ALL_DISTINCT ls /\ EVERY (fun x => x <? LENGTH g) ls /\
  colouring_satisfactory f g /\ is_clique ls g ->
  ALL_DISTINCT (MAP f ls).
Proof.
  intros ls g f (Hd & Hev & Hc & Hcl). apply ALL_DISTINCT_iff in Hd; apply ALL_DISTINCT_iff.
  rewrite EVERY_lt_iff in Hev. apply NoDup_map_inj; [exact Hd|].
  intros x y Hx Hy E. destruct (N.eq_dec x y) as [|Hxy]; [assumption|].
  destruct (Hcl x y) as (Hxl & Hyl & Hm); [rewrite !MEM_iff; auto|].
  apply (Hc x Hxl y); auto.
Qed.

Lemma colsat_inj col adj l :
  colouring_satisfactory col adj -> is_clique l adj -> NoDup l ->
  (forall y, In y l -> y < LENGTH adj) -> INJ col (set l) UNIV.
Proof.
  intros Hc Hcl Hd Hb. split; [intros; exact I|].
  intros x y [Hx Hy]; rewrite IN_set in Hx, Hy.
  apply NoDup_map_inv_inj with (l := l); auto. apply ALL_DISTINCT_iff.
  apply (colouring_satisfactory_cliques l adj col).
  refine (conj _ (conj _ (conj Hc Hcl))); [apply ALL_DISTINCT_iff, Hd|apply EVERY_lt_iff, Hb].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "domain_eq_IMAGE" *)
Theorem domain_eq_IMAGE : forall {A} `{EqDecision A} (s : num_map A), domain s = IMAGE FST (set (toAList s)).
Proof.
  intros A EA s; apply EXTENSION; intros k; rewrite IN_IMAGE. unfold pred_set.IN; rewrite domain_lookup.
  split.
  - intros [v Hv]; exists (k, v); split; [reflexivity|]. apply IN_set, MEM_In, MEM_toAList, Hv.
  - intros ([k' v] & -> & H). exists v. apply MEM_toAList, MEM_In, IN_set, H.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "is_clique_FILTER" *)
Theorem is_clique_FILTER : forall P G ls, is_clique ls G -> is_clique (FILTER P ls) G.
Proof.
  intros P G ls H x y (Hx & Hy & Hxy); apply H; rewrite !MEM_iff in *.
  apply filter_In in Hx, Hy; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "is_clique_subgraph" *)
Theorem is_clique_subgraph : forall ls s s',
  is_clique ls s /\ is_subgraph s s' -> is_clique ls s'.
Proof. intros ls s s' [H1 H2] x y H; apply H2, H1, H. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "domain_numset_list_delete" *)
Theorem domain_numset_list_delete : forall {A} l (live : num_map A),
  domain (numset_list_delete l live) = domain live DIFF set l.
Proof.
  intros A l; induction l as [|x xs IH]; intros live; cbn [numset_list_delete].
  - apply EXTENSION; intros z; rewrite IN_DIFF, IN_set; cbn [In]; tauto.
  - rewrite IH, domain_delete; apply EXTENSION; intros z; rewrite !IN_DIFF, !IN_set; cbn [In].
    unfold pred_set.IN; split; [intros [[? ?] ?]; split; [auto|intros [?|?]; [congruence|auto]]|intros [? Hn]; split; [split; [auto|intros ->; apply Hn; left; reflexivity]|intros ?; apply Hn; right; auto]].
Qed.

(** ** [mk_graph] succeeds *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "mk_graph_succeeds" *)
Theorem mk_graph_succeeds : forall ct ta liveout s,
  good_ra_state s /\
  (forall x, in_clash_tree ct x -> ta x < s.(dim)) /\
  INJ ta (fun x => in_clash_tree ct x) (count (LENGTH s.(adj_ls))) /\
  is_clique liveout s.(adj_ls) /\
  ALL_DISTINCT liveout /\
  EVERY (fun y => y <? s.(dim)) liveout ->
  exists livein s',
    mk_graph ta ct liveout s = (M_success livein, s') /\
    good_ra_state s' /\
    is_clique livein s'.(adj_ls) /\
    s' = with_adj_ls s s'.(adj_ls) /\
    EVERY (fun y => y <? s.(dim)) livein /\
    ALL_DISTINCT livein /\
    set livein SUBSET set liveout UNION IMAGE ta (fun x => in_clash_tree ct x) /\
    is_subgraph s.(adj_ls) s'.(adj_ls).
Proof.
  induction ct as [w r|t|topt c1 IH1 c2 IH2|c1 IH1 c2 IH2];
    intros ta liveout s (Hg & Hta & Hinj & Hc & Hd & Hev); cbn [mk_graph in_clash_tree] in *.
  - (* Delta *)
    ret.
    destruct (extend_clique_succeeds (MAP ta w) liveout s) as (cli1 & s1 & E1 & Hg1 & Hd1 & Hw1 & Hset1 & Hc1 & Hs1).
    { split; [exact Hg|split; [exact Hc|split; [|split; [exact Hd|exact Hev]]]].
      apply EVERY_lt_iff; intros y Hy; apply in_map_iff in Hy as (x & <- & Hx).
      apply Hta; left; apply MEM_In, Hx. }
    mstep' E1. ret. wsubst Hw1. rs.
    set (live2 := FILTER (fun x => negb (MEM x (MAP ta w))) cli1).
    assert (Hcli1 : forall z, In z cli1 -> In z liveout \/ In z (MAP ta w)).
    { intros z Hz; apply set_eq_iff with (z := z) in Hset1; rewrite in_app_iff in Hset1; tauto. }
    rewrite EVERY_lt_iff in Hev.
    assert (Hb1 : forall z, In z cli1 -> z < dim s).
    { intros z Hz; destruct (Hcli1 z Hz) as [Hz'|Hz']; [auto|].
      apply in_map_iff in Hz' as (x & <- & Hx); apply Hta; left; apply MEM_In, Hx. }
    destruct (extend_clique_succeeds (MAP ta r) live2 (with_adj_ls s t)) as (cli2 & s2 & E2 & Hg2 & Hd2 & Hw2 & Hset2 & Hc2 & Hs2).
    { rs. split; [exact Hg1|split; [apply is_clique_FILTER, Hc1|split; [|split]]].
      - apply EVERY_lt_iff; intros y Hy; apply in_map_iff in Hy as (x & <- & Hx).
        apply Hta; right; apply MEM_In, Hx.
      - apply ALL_DISTINCT_iff, NoDup_filter, ALL_DISTINCT_iff, Hd1.
      - apply EVERY_lt_iff; intros y Hy; apply filter_In in Hy as [Hy _]; auto. }
    mstep' E2. wsubst Hw2. rs.
    exists cli2, (with_adj_ls s t0); split; [reflexivity|]. rs.
    split; [exact Hg2|split; [exact Hc2|split; [reflexivity|split; [|split; [exact Hd2|split]]]]].
    + apply EVERY_lt_iff; intros y Hy. apply set_eq_iff with (z := y) in Hset2.
      apply Hset2, in_app_iff in Hy as [Hy|Hy]; [apply filter_In in Hy as [Hy _]; auto|].
      apply in_map_iff in Hy as (x & <- & Hx); apply Hta; right; apply MEM_In, Hx.
    + intros z Hz; unfold pred_set.IN in Hz; apply IN_set in Hz.
      apply set_eq_iff with (z := z) in Hset2. apply Hset2, in_app_iff in Hz.
      rewrite IN_UNION, IN_set, IN_IMAGE.
      destruct Hz as [Hz|Hz].
      * apply filter_In in Hz as [Hz Hn]. destruct (Hcli1 z Hz) as [Hz'|Hz']; [left; exact Hz'|].
        apply MEM_In in Hz'; rewrite Hz' in Hn; discriminate.
      * apply in_map_iff in Hz as (x & <- & Hx); right; exists x; split; [reflexivity|].
        unfold pred_set.IN; right; apply MEM_In, Hx.
    + apply (is_subgraph_trans _ t); split; assumption.
  - (* Set *)
    ret.
    set (ls := MAP ta (MAP fst (toAList t))).
    assert (Hb : forall y, In y ls -> y < dim s).
    { intros y Hy; apply in_map_iff in Hy as (x & <- & Hx); apply Hta, In_MAP_FST_toAList, Hx. }
    destruct (clique_insert_edge_succeeds ls s) as (s1 & E1 & Hg1 & Hw1 & Hc1 & Hs1).
    { split; [exact Hg|apply EVERY_lt_iff, Hb]. }
    mstep' E1. wsubst Hw1. rs.
    exists ls, (with_adj_ls s t0); split; [reflexivity|]. rs.
    split; [exact Hg1|split; [exact Hc1|split; [reflexivity|split; [apply EVERY_lt_iff, Hb|split; [|split]]]]].
    + apply ALL_DISTINCT_iff, NoDup_map_inj.
      * apply ALL_DISTINCT_iff. apply ALL_DISTINCT_MAP_FST_toAList.
      * intros x y Hx Hy E; apply (proj2 Hinj); [split; apply In_MAP_FST_toAList; assumption|exact E].
    + intros z Hz; unfold pred_set.IN in Hz; apply IN_set in Hz.
      apply in_map_iff in Hz as (x & <- & Hx). right; exists x; split; [reflexivity|].
      apply In_MAP_FST_toAList, Hx.
    + exact Hs1.
  - (* Branch *)
    destruct (IH1 ta liveout s) as (l1 & s1 & E1 & Hg1 & Hc1 & Hw1 & Hev1 & Hd1 & Hsub1 & Hs1).
    { split; [exact Hg|split; [intros; apply Hta; tauto|split; [apply (INJ_mono _ _ _ _ Hinj); tauto|split; [exact Hc|split; [exact Hd|exact Hev]]]]]. }
    mstep' E1. wsubst Hw1. rs.
    pose proof Hg as (L1 & _). pose proof Hg1 as (L1' & _). rs.
    destruct (IH2 ta liveout (with_adj_ls s t)) as (l2 & s2 & E2 & Hg2 & Hc2 & Hw2 & Hev2 & Hd2 & Hsub2 & Hs2).
    { rs. split; [exact Hg1|split; [intros; apply Hta; tauto|split; [|split; [|split; assumption]]]].
      - rewrite L1'; rewrite <- L1. apply (INJ_mono _ _ _ _ Hinj); tauto.
      - apply (is_clique_subgraph _ (adj_ls s)); split; assumption. }
    mstep' E2. wsubst Hw2. rs.
    destruct topt as [ts|].
    + ret. set (ls := MAP ta (MAP fst (toAList ts))).
      assert (Hb : forall y, In y ls -> y < dim s).
      { intros y Hy; apply in_map_iff in Hy as (x & <- & Hx); apply Hta. right; right; apply In_MAP_FST_toAList, Hx. }
      destruct (clique_insert_edge_succeeds ls (with_adj_ls s t0)) as (s3 & E3 & Hg3 & Hw3 & Hc3 & Hs3).
      { rs; split; [exact Hg2|apply EVERY_lt_iff, Hb]. }
      mstep' E3. wsubst Hw3. rs.
      exists ls, (with_adj_ls s t1); split; [reflexivity|]. rs.
      split; [exact Hg3|split; [exact Hc3|split; [reflexivity|split; [apply EVERY_lt_iff, Hb|split; [|split]]]]].
      * apply ALL_DISTINCT_iff, NoDup_map_inj; [apply ALL_DISTINCT_iff, ALL_DISTINCT_MAP_FST_toAList|].
        intros x y Hx Hy E; apply (proj2 Hinj); [split; unfold pred_set.IN; right; right; apply In_MAP_FST_toAList; assumption|exact E].
      * intros z Hz; unfold pred_set.IN in Hz; apply IN_set in Hz.
        apply in_map_iff in Hz as (x & <- & Hx). right; exists x; split; [reflexivity|].
        unfold pred_set.IN; right; right; apply In_MAP_FST_toAList, Hx.
      * apply (is_subgraph_trans _ t); split; [exact Hs1|]. apply (is_subgraph_trans _ t0); split; assumption.
    + ret.
      rewrite EVERY_lt_iff in Hev1, Hev2.
      destruct (extend_clique_succeeds l1 l2 (with_adj_ls s t0)) as (cli & s3 & E3 & Hg3 & Hd3 & Hw3 & Hset3 & Hc3 & Hs3).
      { rs. split; [exact Hg2|split; [exact Hc2|split; [apply EVERY_lt_iff; exact Hev1|split; [exact Hd2|apply EVERY_lt_iff; exact Hev2]]]]. }
      mstep' E3. ret. wsubst Hw3. rs.
      exists cli, (with_adj_ls s t1); split; [reflexivity|]. rs.
      split; [exact Hg3|split; [exact Hc3|split; [reflexivity|split; [|split; [exact Hd3|split]]]]].
      * apply EVERY_lt_iff; intros y Hy; apply set_eq_iff with (z := y) in Hset3.
        apply Hset3, in_app_iff in Hy as [Hy|Hy]; auto.
      * intros z Hz; unfold pred_set.IN in Hz; apply IN_set in Hz.
        apply set_eq_iff with (z := z) in Hset3; apply Hset3, in_app_iff in Hz.
        destruct Hz as [Hz|Hz]; [specialize (Hsub2 z)|specialize (Hsub1 z)];
          unfold pred_set.IN, pred_set.SUBSET, pred_set.UNION, IMAGE in *; cbv beta in *;
          rewrite ?IN_set in *; (destruct (Hsub2 ltac:(apply IN_set; exact Hz)) as [H|(x & -> & Hx)] ||
                                  destruct (Hsub1 ltac:(apply IN_set; exact Hz)) as [H|(x & -> & Hx)]);
          [left; exact H|right; exists x; split; [reflexivity|unfold pred_set.IN in *; tauto]|
           left; exact H|right; exists x; split; [reflexivity|unfold pred_set.IN in *; tauto]].
      * apply (is_subgraph_trans _ t); split; [exact Hs1|]. apply (is_subgraph_trans _ t0); split; assumption.
  - (* Seq *)
    destruct (IH2 ta liveout s) as (l2 & s2 & E2 & Hg2 & Hc2 & Hw2 & Hev2 & Hd2 & Hsub2 & Hs2).
    { split; [exact Hg|split; [intros; apply Hta; tauto|split; [apply (INJ_mono _ _ _ _ Hinj); tauto|split; [exact Hc|split; [exact Hd|exact Hev]]]]]. }
    mstep' E2. wsubst Hw2. rs.
    pose proof Hg as (L1 & _). pose proof Hg2 as (L1' & _). rs.
    destruct (IH1 ta l2 (with_adj_ls s t)) as (l1 & s1 & E1 & Hg1 & Hc1 & Hw1 & Hev1 & Hd1 & Hsub1 & Hs1).
    { rs. split; [exact Hg2|split; [intros; apply Hta; tauto|split; [|split; [exact Hc2|split; assumption]]]].
      rewrite L1', <- L1. apply (INJ_mono _ _ _ _ Hinj); tauto. }
    rewrite E1. wsubst Hw1. rs.
    exists l1, (with_adj_ls s t0); split; [reflexivity|]. rs.
    split; [exact Hg1|split; [exact Hc1|split; [reflexivity|split; [exact Hev1|split; [exact Hd1|split]]]]].
    + intros z Hz. specialize (Hsub1 z Hz).
      unfold pred_set.IN, pred_set.UNION, IMAGE in *; cbv beta in *.
      destruct Hsub1 as [Hz'|(x & -> & Hx)]; [|right; exists x; split; [reflexivity|unfold pred_set.IN in *; tauto]].
      specialize (Hsub2 z Hz'); unfold pred_set.IN, pred_set.UNION, IMAGE in Hsub2; cbv beta in Hsub2.
      destruct Hsub2 as [H|(x & -> & Hx)]; [left; exact H|right; exists x; split; [reflexivity|unfold pred_set.IN in *; tauto]].
    + apply (is_subgraph_trans _ t); split; assumption.
Qed.

(** ** Checking a colouring *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "colouring_satisfactory_subgraph" *)
Theorem colouring_satisfactory_subgraph : forall f g h,
  colouring_satisfactory f h /\ is_subgraph g h -> colouring_satisfactory f g.
Proof.
  intros f g h [Hc Hs] x Hx y [Hy Hm] E.
  destruct (Hs x y (conj Hx (conj Hy Hm))) as (Hx' & Hy' & Hm').
  exact (Hc x Hx' y (conj Hy' Hm') E).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "ALL_DISTINCT_set_INJ" *)
Theorem ALL_DISTINCT_set_INJ : forall {A} `{EqDecision A} (ls : list A) (col : A -> N),
  ALL_DISTINCT (MAP col ls) -> INJ col (set ls) UNIV.
Proof.
  intros A EA ls col H; split; [intros; exact I|].
  intros x y [Hx Hy]; rewrite IN_set in Hx, Hy.
  apply ALL_DISTINCT_iff in H. exact (NoDup_map_inv_inj col ls H x y Hx Hy).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "IMAGE_DIFF" *)
Theorem IMAGE_DIFF : forall {A B} (f : A -> B) s t,
  INJ f (s UNION t) UNIV -> IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t.
Proof.
  intros A B f s t [_ Hi]; apply EXTENSION; intros z; rewrite IN_DIFF, !IN_IMAGE; split.
  - intros (x & -> & Hx); rewrite IN_DIFF in Hx; split; [exists x; tauto|].
    intros (y & E & Hy). apply (proj2 Hx). rewrite (Hi x y); [exact Hy| |exact E].
    rewrite !IN_UNION; tauto.
  - intros [(x & -> & Hx) Hn]; exists x; split; [reflexivity|]. rewrite IN_DIFF; split; [exact Hx|].
    intros Ht; apply Hn; exists x; split; [reflexivity|exact Ht].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "set_FILTER" *)
Theorem set_FILTER : forall {A} (P : A -> bool) live,
  set (FILTER P live) = set live DIFF (fun x => ~ P x).
Proof.
  intros A P live; apply EXTENSION; intros z; rewrite IN_DIFF, !IN_set, filter_In.
  unfold pred_set.IN, is_true; split; [intros [? ?]; split; [auto|tauto]|].
  intros [H1 H2]; split; [exact H1|destruct (P z); [reflexivity|exfalso; apply H2; discriminate]].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "MEM_MAP_IMAGE" *)
Theorem MEM_MAP_IMAGE : forall {A B} `{EqDecision B} (f : A -> B) l,
  (fun x => is_true (MEM x (MAP f l))) = IMAGE f (set l).
Proof.
  intros A B EB f l; apply EXTENSION; intros z; rewrite IN_IMAGE; unfold pred_set.IN at 1.
  rewrite MEM_iff, in_map_iff; split; intros (x & H1 & H2); exists x; rewrite ?IN_set in *; auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "UNION_DIFF_3" *)
Theorem UNION_DIFF_3 : forall {A} (s t : A -> Prop), s DIFF t UNION t = s UNION t.
Proof.
  intros A s t; apply EXTENSION; intros z; rewrite !IN_UNION, IN_DIFF.
  destruct (classic (z IN t)); tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "check_clash_tree_domain" *)
Theorem check_clash_tree_domain : forall ct f live flive live' flive',
  check_clash_tree f ct live flive = Some (live', flive') ->
  domain live' SUBSET domain live UNION (fun x => in_clash_tree ct x).
Proof.
  induction ct as [w r|t|topt c1 IH1 c2 IH2|c1 IH1 c2 IH2]; intros f live flive live' flive' H;
    cbn [check_clash_tree in_clash_tree] in *; intros z Hz.
  - destruct (check_partial_col f w live flive) as [p|]; [|discriminate].
    pose proof (check_partial_col_domain _ _ _ _ _ H) as Hd; cbn [FST] in Hd.
    rewrite Hd, IN_UNION, domain_numset_list_delete, IN_DIFF, IN_set in Hz.
    rewrite IN_UNION; unfold pred_set.IN at 2; rewrite !MEM_iff; tauto.
  - apply check_col_Some in H as (-> & _). rewrite IN_UNION; right; exact Hz.
  - destruct (check_clash_tree f c1 live flive) as [[o1 fo1]|] eqn:C1; [|discriminate].
    destruct (check_clash_tree f c2 live flive) as [[o2 fo2]|] eqn:C2; [|discriminate].
    pose proof (IH1 _ _ _ _ _ C1) as D1; pose proof (IH2 _ _ _ _ _ C2) as D2.
    destruct topt as [ts|].
    + apply check_col_Some in H as (-> & _). rewrite IN_UNION; right; unfold pred_set.IN; tauto.
    + pose proof (check_partial_col_domain _ _ _ _ _ H) as Hd; cbn [FST] in Hd.
      rewrite Hd, IN_UNION, IN_set, In_MAP_FST_toAList, domain_difference in Hz.
      destruct Hz as [[Hz _]|Hz]; [apply D2 in Hz|apply D1 in Hz];
        rewrite IN_UNION in *; unfold pred_set.IN in *; tauto.
  - destruct (check_clash_tree f c2 live flive) as [[o2 fo2]|] eqn:C2; [|discriminate].
    apply IH1 in H; apply IH2 in C2. apply H in Hz. rewrite IN_UNION in Hz.
    destruct Hz as [Hz|Hz]; [apply C2 in Hz|]; rewrite IN_UNION in *; unfold pred_set.IN in *; tauto.
Qed.

Lemma set_In {A} (l : list A) x : set l x <-> In x l.
Proof. apply IN_set. Qed.

Ltac ssimp := unfold pred_set.UNION, pred_set.DIFF, pred_set.IN; cbv beta;
  rewrite ?set_In, ?MEM_iff.
Ltac ssimp_in H := unfold pred_set.UNION, pred_set.DIFF, pred_set.IN in H; cbv beta in H;
  rewrite ?set_In, ?MEM_iff in H.

Ltac hstep E H := first [rewrite (bind_ok _ _ _ _ _ E) in H | rewrite (ibind_ok _ _ _ _ _ E) in H]; cbv beta in H.
Ltac hret H := rewrite ?(bind_ok _ _ _ _ _ (return_eq _ _)) in H; cbv beta in H.

Lemma IMAGE_eq_set {A B} (f : A -> B) S l :
  IMAGE f S = set l <-> (forall z, In z l <-> exists x, z = f x /\ S x).
Proof.
  rewrite EXTENSION; split; intros H z; specialize (H z); rewrite ?IN_set, ?IN_IMAGE in *;
    unfold pred_set.IN in *; rewrite H; reflexivity.
Qed.

Lemma good_dim_len s : good_ra_state s -> LENGTH s.(adj_ls) = s.(dim).
Proof. intros (L1 & _); exact L1. Qed.

(** Facts about [check_col] on a set whose image is a clique. *)
Lemma check_col_clique (col ta : N -> N) (t : num_set) adj :
  colouring_satisfactory col adj ->
  is_clique (MAP ta (MAP fst (toAList t))) adj ->
  (forall x, x IN domain t -> ta x < LENGTH adj) ->
  (forall x y, x IN domain t -> y IN domain t -> ta x = ta y -> x = y) ->
  exists flivein,
    check_col (col ∘ ta) t = Some (t, flivein) /\
    IMAGE ta (domain t) = set (MAP ta (MAP fst (toAList t))) /\
    domain flivein = IMAGE (col ∘ ta) (domain t).
Proof.
  intros Hc Hcl Hb Hi.
  assert (Hd : NoDup (MAP ta (MAP fst (toAList t)))).
  { apply NoDup_map_inj; [apply ALL_DISTINCT_iff, ALL_DISTINCT_MAP_FST_toAList|].
    intros x y Hx Hy; apply Hi; apply In_MAP_FST_toAList; assumption. }
  assert (Hb' : forall y, In y (MAP ta (MAP fst (toAList t))) -> y < LENGTH adj).
  { intros y Hy; apply in_map_iff in Hy as (x & <- & Hx); apply Hb, In_MAP_FST_toAList, Hx. }
  pose proof (colsat_inj col adj _ Hc Hcl Hd Hb') as Hci.
  assert (Hdist : is_true (ALL_DISTINCT (MAP (fun x => (col ∘ ta) (FST x)) (toAList t)))).
  { rewrite (MAP_FST_toAList_eq (col ∘ ta)); apply ALL_DISTINCT_iff, NoDup_map_inj.
    - apply ALL_DISTINCT_iff, ALL_DISTINCT_MAP_FST_toAList.
    - intros x y Hx Hy E. apply Hi; [apply In_MAP_FST_toAList, Hx|apply In_MAP_FST_toAList, Hy|].
      apply (proj2 Hci); [split; apply IN_set, in_map; assumption|exact E]. }
  unfold check_col; rewrite Hdist. eexists; split; [reflexivity|split].
  - apply IMAGE_eq_set; intros z; rewrite in_map_iff; split;
      intros (x & H1 & H2); exists x; split; auto; rewrite In_MAP_FST_toAList in *; auto.
  - rewrite domain_fromAList_unit, (MAP_FST_toAList_eq (fun k => col (ta k))), LIST_TO_SET_MAP, set_MAP_FST_toAList. reflexivity.
Qed.

(** The correctness theorem for [mk_graph]. *)
(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "mk_graph_check_clash_tree" *)
Theorem mk_graph_check_clash_tree : forall ct ta livelist s livelist' s' col live flive,
  mk_graph ta ct livelist s = (M_success livelist', s') /\
  colouring_satisfactory col s'.(adj_ls) /\
  INJ ta ((fun x => in_clash_tree ct x) UNION domain live) (count (LENGTH s.(adj_ls))) /\
  IMAGE ta (domain live) = set livelist /\
  ALL_DISTINCT livelist /\
  EVERY (fun y => y <? s.(dim)) livelist /\
  is_clique livelist s.(adj_ls) /\
  good_ra_state s /\
  domain flive = IMAGE (col ∘ ta) (domain live) ->
  exists livein flivein,
    check_clash_tree (col ∘ ta) ct live flive = Some (livein, flivein) /\
    IMAGE ta (domain livein) = set livelist' /\
    domain flivein = IMAGE (col ∘ ta) (domain livein).
Proof.
  induction ct as [w r|t|topt c1 IH1 c2 IH2|c1 IH1 c2 IH2];
    intros ta livelist s livelist' s' col live flive (H & Hcol & Hinj & Him & Hd & Hev & Hc & Hg & Hfl);
    pose proof (good_dim_len s Hg) as L1;
    match type of Hinj with INJ _ ?S _ =>
      assert (Hta : forall x, S x -> ta x < dim s) by
        (intros x Hx; rewrite <- L1; apply (proj1 Hinj); exact Hx) end;
    cbn [mk_graph check_clash_tree in_clash_tree] in *.
  - (* Delta *)
    hret H.
    destruct (extend_clique_succeeds (MAP ta w) livelist s) as (cli1 & s1 & E1 & Hg1 & Hd1 & Hw1 & Hset1 & Hc1 & Hs1).
    { split; [exact Hg|split; [exact Hc|split; [|split; [exact Hd|exact Hev]]]].
      apply EVERY_lt_iff; intros y Hy; apply in_map_iff in Hy as (x & <- & Hx).
      apply Hta; left; left; apply MEM_In, Hx. }
    hstep E1 H. hret H. wsubst Hw1. rs.
    set (live2 := FILTER (fun x => negb (MEM x (MAP ta w))) cli1) in *.
    rewrite set_eq_iff in Hset1. rewrite EVERY_lt_iff in Hev.
    assert (Hb1 : forall z, In z cli1 -> z < dim s).
    { intros z Hz; apply Hset1, in_app_iff in Hz as [Hz|Hz]; [auto|].
      apply in_map_iff in Hz as (x & <- & Hx); apply Hta; left; left; apply MEM_In, Hx. }
    destruct (extend_clique_succeeds (MAP ta r) live2 (with_adj_ls s t)) as (cli2 & s2 & E2 & Hg2 & Hd2 & Hw2 & Hset2 & Hc2 & Hs2).
    { rs. split; [exact Hg1|split; [apply is_clique_FILTER, Hc1|split; [|split]]].
      - apply EVERY_lt_iff; intros y Hy; apply in_map_iff in Hy as (x & <- & Hx).
        apply Hta; left; right; apply MEM_In, Hx.
      - apply ALL_DISTINCT_iff, NoDup_filter, ALL_DISTINCT_iff, Hd1.
      - apply EVERY_lt_iff; intros y Hy; apply filter_In in Hy as [Hy _]; auto. }
    hstep E2 H. wsubst Hw2. rs. injection H as <- <-. rs.
    rewrite set_eq_iff in Hset2.
    pose proof (good_dim_len _ Hg2) as L2; rs.
    assert (Hb2 : forall z, In z cli2 -> z < LENGTH t0).
    { intros z Hz; rewrite L2; apply Hset2, in_app_iff in Hz as [Hz|Hz];
        [apply filter_In in Hz as [Hz _]; auto|].
      apply in_map_iff in Hz as (x & <- & Hx); apply Hta; left; right; apply MEM_In, Hx. }
    assert (Hci2 : INJ col (set cli2) UNIV) by (apply (colsat_inj col t0); auto; apply ALL_DISTINCT_iff, Hd2).
    assert (Hci1 : INJ col (set cli1) UNIV).
    { apply (colsat_inj col t0); [exact Hcol|apply (is_clique_subgraph _ t); split; assumption|
        apply ALL_DISTINCT_iff, Hd1|intros z Hz; rewrite L2; auto]. }
    rewrite IMAGE_eq_set in Him.
    assert (Hinj1 : INJ (col ∘ ta) (set w UNION domain live) UNIV).
    { apply (INJ_COMPOSE_IMAGE ta col _ (count (LENGTH (adj_ls s)))); split.
      - apply (INJ_mono _ _ _ _ Hinj); intros x; ssimp; tauto.
      - apply (INJ_mono _ _ _ _ Hci1); intros z (x & -> & Hx). apply IN_set, Hset1, in_app_iff.
        ssimp_in Hx. destruct Hx as [Hx|Hx].
        + right; apply in_map, Hx.
        + left; apply Him; exists x; split; [reflexivity|exact Hx]. }
    destruct (check_partial_col_success w live flive (col ∘ ta) (conj Hfl Hinj1)) as (li1 & fli1 & C1 & _).
    rewrite C1.
    assert (Hnot : forall x, x IN domain live -> ~ In x w -> ~ In (ta x) (MAP ta w)).
    { intros x Hx Hxw Hin; apply in_map_iff in Hin as (y & E & Hy). apply Hxw.
      replace x with y; [exact Hy|]. apply (proj2 Hinj); [|exact E].
      unfold pred_set.UNION, pred_set.IN; split; [left; left; apply MEM_In, Hy|right; exact Hx]. }
    assert (Hset : forall z, In z cli2 <-> exists x, z = ta x /\ (In x r \/ (x IN domain live /\ ~ In x w))).
    { intros z; rewrite Hset2, in_app_iff; split.
      - intros [Hz|Hz].
        + apply filter_In in Hz as [Hz Hn]. apply Hset1, in_app_iff in Hz as [Hz|Hz].
          * apply Him in Hz as (x & -> & Hx). exists x; split; [reflexivity|right; split; [exact Hx|]].
            intros Hxw; rewrite (proj2 (MEM_In _ _) (in_map ta _ _ Hxw)) in Hn; discriminate.
          * rewrite (proj2 (MEM_In _ _) Hz) in Hn; discriminate.
        + apply in_map_iff in Hz as (x & <- & Hx); exists x; split; [reflexivity|left; exact Hx].
      - intros (x & -> & [Hx|[Hx Hxw]]); [right; apply in_map, Hx|left].
        apply filter_In; split; [apply Hset1, in_app_iff; left; apply Him; exists x; split; [reflexivity|exact Hx]|].
        destruct (MEM (ta x) (MAP ta w)) eqn:Em; [|reflexivity].
        exfalso; apply (Hnot x Hx Hxw), MEM_In, Em. }
    assert (Hinj2 : INJ (col ∘ ta) (set r UNION domain (numset_list_delete w live)) UNIV).
    { rewrite domain_numset_list_delete.
      apply (INJ_COMPOSE_IMAGE ta col _ (count (LENGTH (adj_ls s)))); split.
      - apply (INJ_mono _ _ _ _ Hinj); intros x; ssimp; tauto.
      - apply (INJ_mono _ _ _ _ Hci2); intros z (x & -> & Hx). apply IN_set, Hset; exists x; split; [reflexivity|].
        ssimp_in Hx. tauto. }
    assert (Hfl2 : domain (numset_list_delete (MAP (col ∘ ta) w) flive) =
                   IMAGE (col ∘ ta) (domain (numset_list_delete w live))).
    { rewrite !domain_numset_list_delete, Hfl, LIST_TO_SET_MAP, IMAGE_DIFF; [reflexivity|].
      apply (INJ_mono _ _ _ _ Hinj1); intros x; unfold pred_set.UNION, pred_set.IN in *; tauto. }
    destruct (check_partial_col_success r _ _ (col ∘ ta) (conj Hfl2 Hinj2)) as (li2 & fli2 & C2 & Hfd2).
    exists li2, fli2; split; [exact C2|split; [|exact Hfd2]].
    pose proof (check_partial_col_domain _ _ _ _ _ C2) as Hdom; cbn [FST] in Hdom.
    apply IMAGE_eq_set; intros z; rewrite Hset, Hdom, domain_numset_list_delete.
    ssimp; split; intros (x & -> & Hx); exists x; (split; [reflexivity|]); ssimp_in Hx; ssimp; tauto.
  - (* Set *)
    hret H.
    destruct (clique_insert_edge_succeeds (MAP ta (MAP fst (toAList t))) s) as (s1 & E1 & Hg1 & Hw1 & Hc1 & Hs1).
    { split; [exact Hg|]. apply EVERY_lt_iff; intros y Hy; apply in_map_iff in Hy as (x & <- & Hx).
      apply Hta; left; apply In_MAP_FST_toAList, Hx. }
        hstep E1 H. wsubst Hw1. rs. injection H as <- <-. rs.
    pose proof (good_dim_len _ Hg1) as L2; rs.
    destruct (check_col_clique col ta t t0 Hcol Hc1) as (fl & C & Hi1 & Hi2).
    + intros x Hx; rewrite L2; apply Hta; left; exact Hx.
    + intros x y Hx Hy; apply (proj2 Hinj); unfold pred_set.UNION, pred_set.IN in *; tauto.
    + exists t, fl; auto.
  - (* Branch *)
    assert (Hinj1 : INJ ta (fun x => in_clash_tree c1 x) (count (LENGTH (adj_ls s))))
      by (apply (INJ_mono _ _ _ _ Hinj); intros x; unfold pred_set.UNION, pred_set.IN in *; tauto).
    destruct (mk_graph_succeeds c1 ta livelist s) as (l1 & s1 & E1 & Hg1 & Hc1 & Hw1 & Hev1 & Hd1 & Hsub1 & Hs1).
    { split; [exact Hg|split; [intros x Hx; apply Hta; unfold pred_set.UNION, pred_set.IN in *; tauto|split; [exact Hinj1|split; [exact Hc|split; [exact Hd|exact Hev]]]]]. }
    hstep E1 H. wsubst Hw1. rs.
    pose proof (good_dim_len _ Hg1) as L1'; rs.
    assert (Hinj2 : INJ ta (fun x => in_clash_tree c2 x) (count (LENGTH t)))
      by (rewrite L1', <- L1; apply (INJ_mono _ _ _ _ Hinj); intros x; unfold pred_set.UNION, pred_set.IN in *; tauto).
    destruct (mk_graph_succeeds c2 ta livelist (with_adj_ls s t)) as (l2 & s2 & E2 & Hg2 & Hc2 & Hw2 & Hev2 & Hd2 & Hsub2 & Hs2).
    { rs. split; [exact Hg1|split; [intros x Hx; apply Hta; unfold pred_set.UNION, pred_set.IN in *; tauto|split; [exact Hinj2|split; [|split; [exact Hd|exact Hev]]]]].
      apply (is_clique_subgraph _ (adj_ls s)); split; assumption. }
    hstep E2 H. wsubst Hw2. rs.
    pose proof (good_dim_len _ Hg2) as L2'; rs.
    (* the final graph *)
    assert (Hfinal : exists cli t1, livelist' = cli /\ s' = with_adj_ls s t1 /\ is_subgraph t0 t1 /\
               is_clique cli t1 /\ ALL_DISTINCT cli /\ good_ra_state (with_adj_ls s t1) /\
               match topt with
               | None => set cli = set (l2 ++ l1)
               | Some ts => cli = MAP ta (MAP fst (toAList ts))
               end).
    { destruct topt as [ts|].
      - hret H.
        destruct (clique_insert_edge_succeeds (MAP ta (MAP fst (toAList ts))) (with_adj_ls s t0)) as (s3 & E3 & Hg3 & Hw3 & Hc3 & Hs3).
        { rs. split; [exact Hg2|]. apply EVERY_lt_iff; intros y Hy; apply in_map_iff in Hy as (x & <- & Hx).
          apply Hta; left; right; right; apply In_MAP_FST_toAList, Hx. }
        hstep E3 H. wsubst Hw3. rs. injection H as <- <-.
        exists (MAP ta (MAP fst (toAList ts))), t1.
        split; [reflexivity|split; [reflexivity|split; [exact Hs3|split; [exact Hc3|split; [|split; [exact Hg3|reflexivity]]]]]].
        apply ALL_DISTINCT_iff, NoDup_map_inj; [apply ALL_DISTINCT_iff, ALL_DISTINCT_MAP_FST_toAList|].
        intros x y Hx Hy E; apply (proj2 Hinj); [|exact E].
        unfold pred_set.UNION, pred_set.IN; rewrite !In_MAP_FST_toAList in *; unfold pred_set.IN in *; tauto.
      - hret H.
        destruct (extend_clique_succeeds l1 l2 (with_adj_ls s t0)) as (cli & s3 & E3 & Hg3 & Hd3 & Hw3 & Hset3 & Hc3 & Hs3).
        { rs. split; [exact Hg2|split; [exact Hc2|split; [exact Hev1|split; [exact Hd2|exact Hev2]]]]. }
        hstep E3 H. hret H. wsubst Hw3. rs. injection H as <- <-.
        exists cli, t1.
        split; [reflexivity|split; [reflexivity|split; [exact Hs3|split; [exact Hc3|split; [exact Hd3|split; [exact Hg3|exact Hset3]]]]]]. }
    destruct Hfinal as (cli & t1 & -> & -> & Hs3 & Hc3 & Hd3 & Hg3 & Hcase). rs.
    assert (Hcol2 : colouring_satisfactory col t0) by (apply (colouring_satisfactory_subgraph _ _ t1); auto).
    assert (Hcol1 : colouring_satisfactory col t)
      by (apply (colouring_satisfactory_subgraph _ _ t0); auto).
    destruct (IH1 ta livelist s l1 (with_adj_ls s t) col live flive) as (li1 & fli1 & C1 & Him1 & Hfd1).
    { rs. repeat (split; [solve [auto]|]). split; [|split; [exact Him|split; [exact Hd|split; [exact Hev|split; [exact Hc|split; [exact Hg|exact Hfl]]]]]].
      apply (INJ_mono _ _ _ _ Hinj); intros x; unfold pred_set.UNION, pred_set.IN in *; tauto. }
    destruct (IH2 ta livelist (with_adj_ls s t) l2 (with_adj_ls s t0) col live flive) as (li2 & fli2 & C2 & Him2 & Hfd2).
    { rs. split; [exact E2|split; [exact Hcol2|split; [|split; [exact Him|split; [exact Hd|split; [exact Hev|split; [|split; [exact Hg1|exact Hfl]]]]]]]].
      - rewrite L1', <- L1; apply (INJ_mono _ _ _ _ Hinj); intros x; unfold pred_set.UNION, pred_set.IN in *; tauto.
      - apply (is_clique_subgraph _ (adj_ls s)); split; assumption. }
    rewrite C1, C2.
    pose proof (good_dim_len _ Hg3) as L3; rs.
    destruct topt as [ts|].
    + subst cli. destruct (check_col_clique col ta ts t1 Hcol Hc3) as (fl & C & Hi1 & Hi2).
      * intros x Hx; rewrite L3; apply Hta; left; right; right; exact Hx.
      * intros x y Hx Hy; apply (proj2 Hinj); unfold pred_set.UNION, pred_set.IN in *; tauto.
      * exists ts, fl; auto.
    + pose proof (check_clash_tree_domain _ _ _ _ _ _ C1) as D1.
      pose proof (check_clash_tree_domain _ _ _ _ _ _ C2) as D2.
      rewrite set_eq_iff in Hcase. rewrite IMAGE_eq_set in Him1, Him2.
      assert (HinjU : INJ (col ∘ ta) (set (MAP fst (toAList (difference li2 li1))) UNION domain li1) UNIV).
      { rewrite set_MAP_FST_toAList, domain_difference.
        apply (INJ_COMPOSE_IMAGE ta col _ (count (LENGTH (adj_ls s)))); split.
        - apply (INJ_mono _ _ _ _ Hinj); intros x Hx.
          unfold pred_set.UNION, pred_set.IN in Hx; destruct Hx as [[Hx _]|Hx];
            [specialize (D2 x Hx)|specialize (D1 x Hx)]; unfold pred_set.UNION, pred_set.IN in *; tauto.
        - apply (INJ_mono col (set cli)).
          + apply (colsat_inj col t1); auto; [apply ALL_DISTINCT_iff, Hd3|].
            intros z Hz; rewrite L3; apply Hcase, in_app_iff in Hz as [Hz|Hz]; [apply (proj1 (EVERY_lt_iff _ _) Hev2)|apply (proj1 (EVERY_lt_iff _ _) Hev1)]; exact Hz.
          + intros z (x & -> & Hx). apply IN_set, Hcase, in_app_iff.
            unfold pred_set.UNION, pred_set.IN in Hx; destruct Hx as [[Hx _]|Hx];
              [left; apply Him2|right; apply Him1]; exists x; auto. }
      destruct (check_partial_col_success _ li1 fli1 (col ∘ ta) (conj Hfd1 HinjU)) as (li & fli & C & Hfd).
      exists li, fli; split; [exact C|split; [|exact Hfd]].
      pose proof (check_partial_col_domain _ _ _ _ _ C) as Hdom; cbn [FST] in Hdom.
      rewrite Hdom, set_MAP_FST_toAList, domain_difference.
      apply IMAGE_eq_set; intros z; rewrite Hcase, in_app_iff, Him1, Him2.
      unfold pred_set.UNION, pred_set.IN; split.
      * intros [(x & -> & Hx)|(x & -> & Hx)]; exists x; split; auto.
        destruct (classic (domain li1 x)); tauto.
      * intros (x & -> & [[Hx _]|Hx]); [left|right]; exists x; auto.
  - (* Seq *)
    assert (Hinj2 : INJ ta (fun x => in_clash_tree c2 x) (count (LENGTH (adj_ls s))))
      by (apply (INJ_mono _ _ _ _ Hinj); intros x; unfold pred_set.UNION, pred_set.IN in *; tauto).
    destruct (mk_graph_succeeds c2 ta livelist s) as (l2 & s2 & E2 & Hg2 & Hc2 & Hw2 & Hev2 & Hd2 & Hsub2 & Hs2).
    { split; [exact Hg|split; [intros x Hx; apply Hta; unfold pred_set.UNION, pred_set.IN in *; tauto|split; [exact Hinj2|split; [exact Hc|split; [exact Hd|exact Hev]]]]]. }
    hstep E2 H. wsubst Hw2. rs.
    pose proof (good_dim_len _ Hg2) as L2'; rs.
    assert (Hinj1 : INJ ta (fun x => in_clash_tree c1 x) (count (LENGTH t)))
      by (rewrite L2', <- L1; apply (INJ_mono _ _ _ _ Hinj); intros x; unfold pred_set.UNION, pred_set.IN in *; tauto).
    destruct (mk_graph_succeeds c1 ta l2 (with_adj_ls s t)) as (l1 & s1 & E1 & Hg1 & Hc1 & Hw1 & Hev1 & Hd1 & Hsub1 & Hs1).
    { rs. split; [exact Hg2|split; [intros x Hx; apply Hta; unfold pred_set.UNION, pred_set.IN in *; tauto|split; [exact Hinj1|split; [exact Hc2|split; [exact Hd2|exact Hev2]]]]]. }
    rewrite E1 in H. injection H as <- <-. wsubst Hw1. rs.
    destruct (IH2 ta livelist s l2 (with_adj_ls s t) col live flive) as (li2 & fli2 & C2 & Him2 & Hfd2).
    { rs. split; [exact E2|split; [apply (colouring_satisfactory_subgraph _ _ t0); auto|]].
      split; [|split; [exact Him|split; [exact Hd|split; [exact Hev|split; [exact Hc|split; [exact Hg|exact Hfl]]]]]].
      apply (INJ_mono _ _ _ _ Hinj); intros x; unfold pred_set.UNION, pred_set.IN in *; tauto. }
    pose proof (check_clash_tree_domain _ _ _ _ _ _ C2) as D2.
    destruct (IH1 ta l2 (with_adj_ls s t) l1 (with_adj_ls s t0) col li2 fli2) as (li & fli & C & Him1 & Hfd).
    { rs. split; [exact E1|split; [exact Hcol|split; [|split; [exact Him2|split; [exact Hd2|split; [exact Hev2|split; [exact Hc2|split; [exact Hg2|exact Hfd2]]]]]]]].
      rewrite L2', <- L1; apply (INJ_mono _ _ _ _ Hinj); intros x Hx.
      unfold pred_set.UNION, pred_set.IN in Hx; destruct Hx as [Hx|Hx]; [|specialize (D2 x Hx)];
        unfold pred_set.UNION, pred_set.IN in *; tauto. }
    rewrite C2. exists li, fli; auto.
Qed.
