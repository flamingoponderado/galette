(** * CakeML [linear_scanProof]: live trees, intervals and their checks

    Part of the [linear_scanProofScript] counterpart: the theorems about
    [numset_list_insert]/[numset_list_delete], [check_partial_col],
    [check_live_tree], [get_live_tree], [check_number_property],
    [get_intervals] and [check_intervals] (HOL lines 1-2018). *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc linear_scan.
From Galette.cakeml.compiler.backend.reg_alloc.proofs.reg_allocProof Require Import check_clash_tree.
Open Scope N_scope.

(** ** Local helpers (Galette infrastructure, untagged) *)

Lemma INJ_UNIV {A B} (f : A -> B) s :
  INJ f s UNIV <-> (forall x y, x IN s -> y IN s -> f x = f y -> x = y).
Proof.
  unfold INJ; split.
  - intros [_ H] x y Hx Hy; apply H; auto.
  - intros H; split; [intros; exact I|intros x y [Hx Hy]; apply H; auto].
Qed.

Lemma INJ_sub {A B} (f : A -> B) s t :
  INJ f t UNIV -> (forall x, x IN s -> x IN t) -> INJ f s UNIV.
Proof. rewrite !INJ_UNIV; intros H Hs x y Hx Hy; apply H; auto. Qed.

Lemma dom_unit (x : N) (t : num_set) : x IN domain t <-> lookup x t = Some tt.
Proof.
  unfold pred_set.IN; rewrite domain_lookup; split; [intros [[] H]; exact H|eauto].
Qed.

Lemma dom_lookup {A} (x : N) (t : num_map A) : x IN domain t <-> exists v, lookup x t = Some v.
Proof. unfold pred_set.IN; apply domain_lookup. Qed.

Lemma notdom_lookup {A} (x : N) (t : num_map A) : ~ x IN domain t <-> lookup x t = None.
Proof. unfold pred_set.IN; rewrite lookup_NONE_domain; tauto. Qed.

Lemma lookup_unit_cases' (x : N) (t : num_set) :
  lookup x t = None \/ lookup x t = Some tt.
Proof. destruct (lookup x t) as [[]|]; auto. Qed.

Lemma IN_set_cons {A} (x h : A) l : x IN set (h :: l) <-> x = h \/ x IN set l.
Proof. reflexivity. Qed.

Lemma MEM_IN_set {A} `{EqDecision A} (x : A) l : MEM x l = true <-> x IN set l.
Proof. rewrite MEM_In, IN_set; reflexivity. Qed.

Lemma In_toAList {A} (t : num_map A) k v : In (k, v) (toAList t) <-> lookup k t = Some v.
Proof.
  unfold toAList; rewrite In_foldi, lrnext_0; cbn [In]; split.
  - intros [[]|[n [-> H]]]; replace (0 + 1 * n) with n by lia; exact H.
  - intros H; right; exists k; split; [lia|exact H].
Qed.

Lemma NoDup_map_inj {A B} (f : A -> B) l :
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (List.map f l).
Proof.
  induction l as [|h l IH]; intros Hi Hd; cbn [List.map]; constructor.
  - inversion Hd; subst. intros Hm; apply in_map_iff in Hm as (y & E & Hy).
    assert (y = h) as -> by (apply Hi; cbn; auto). contradiction.
  - inversion Hd; subst; apply IH; auto; intros; apply Hi; cbn; auto.
Qed.

Ltac set_ext_tac := apply set_ext; intros ?; unfold_sets.

(** ** Basic lemmas *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "set_MAP_FST_toAList_eq_domain" *)
Theorem set_MAP_FST_toAList_eq_domain : forall {A} (s : num_map A),
  set (MAP FST (toAList s)) = domain s.
Proof.
  intros A s; apply set_ext; intros x; change (x IN set (MAP FST (toAList s)) <-> x IN domain s).
  rewrite IN_set, dom_lookup, in_map_iff; split.
  - intros [[k v] [<- H]]; exists v; apply In_toAList, H.
  - intros [v H]; exists (x, v); split; [reflexivity|apply In_toAList, H].
Qed.

Lemma IN_set_MAP_FST_toAList {A} (s : num_map A) x :
  x IN set (MAP FST (toAList s)) <-> x IN domain s.
Proof. rewrite set_MAP_FST_toAList_eq_domain; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "numset_list_insert_FOLDL" *)
Theorem numset_list_insert_FOLDL : forall l live,
  numset_list_insert l live = FOLDL (fun live x => insert x tt live) live l.
Proof. induction l as [|h l IH]; intros live; cbn; auto. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "numset_list_insert_nottailrec_FOLDR" *)
Theorem numset_list_insert_nottailrec_FOLDR : forall l live,
  numset_list_insert_nottailrec l live = FOLDR (fun x live => insert x tt live) live l.
Proof. induction l as [|h l IH]; intros live; cbn; congruence. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "both_numset_list_insert_equal" *)
Theorem both_numset_list_insert_equal : forall l live,
  numset_list_insert l live = numset_list_insert_nottailrec (REVERSE l) live.
Proof.
  intros l live; rewrite numset_list_insert_FOLDL, numset_list_insert_nottailrec_FOLDR,
    FOLDL_fold_left, FOLDR_fold_right, fold_left_rev_right.
  reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "domain_numset_list_insert" *)
Theorem domain_numset_list_insert : forall l s,
  domain (numset_list_insert l s) = set l UNION domain s.
Proof.
  induction l as [|h l IH]; intros s; cbn [numset_list_insert].
  - set_ext_tac; cbn [LIST_TO_SET]; tauto.
  - rewrite IH, domain_insert; set_ext_tac; cbn [LIST_TO_SET]; tauto.
Qed.

Lemma IN_domain_numset_list_insert l s x :
  x IN domain (numset_list_insert l s) <-> x IN set l \/ x IN domain s.
Proof. rewrite domain_numset_list_insert; reflexivity. Qed.

(** "why breaking encapsulation like this? To get rid of the assumption [wf s]" *)
(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "lookup_insert_id" *)
Theorem lookup_insert_id : forall x (y : unit) s, lookup x s = Some tt -> s = insert x tt s.
Proof. intros x y s H; symmetry; apply insert_unchanged, H. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "numset_list_insert_FILTER" *)
Theorem numset_list_insert_FILTER : forall l live,
  numset_list_insert (FILTER (fun x => bool_decide (lookup x live = None)) l) live =
  numset_list_insert l live.
Proof.
  intros l live0.
  assert (G : forall live, (forall x, lookup x live0 = Some tt -> lookup x live = Some tt) ->
    numset_list_insert (FILTER (fun x => bool_decide (lookup x live0 = None)) l) live =
    numset_list_insert l live).
  { induction l as [|h l IH]; intros live Hl; [reflexivity|].
    cbn [FILTER numset_list_insert filter].
    destruct (lookup_unit_cases' h live0) as [E|E].
    - rewrite (proj2 (bool_decide_spec _) E); cbn [numset_list_insert].
      apply IH; intros x Hx; rewrite lookup_insert; destruct (decide (x = h)); auto.
    - assert (bool_decide (lookup h live0 = None) = false) as ->.
      { destruct (bool_decide _) eqn:B; [apply bool_decide_spec in B; congruence|reflexivity]. }
      rewrite (insert_unchanged live h tt (Hl _ E)); apply IH, Hl. }
  apply G; auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "domain_numset_list_delete" *)
Theorem domain_numset_list_delete : forall {A} l (s : num_map A),
  domain (numset_list_delete l s) = domain s DIFF set l.
Proof.
  intros A; induction l as [|h l IH]; intros s; cbn [numset_list_delete].
  - set_ext_tac; cbn [LIST_TO_SET]; tauto.
  - rewrite IH, domain_delete; set_ext_tac; cbn [LIST_TO_SET]; tauto.
Qed.

Lemma IN_domain_numset_list_delete {A} l (s : num_map A) x :
  x IN domain (numset_list_delete l s) <-> x IN domain s /\ ~ x IN set l.
Proof. rewrite domain_numset_list_delete; reflexivity. Qed.

(** ** [check_partial_col] *)

Lemma check_partial_col_cons f h l live flive :
  check_partial_col f (h :: l) live flive =
  match lookup h live with
  | Some _ => check_partial_col f l live flive
  | None => match lookup (f h) flive with
            | None => check_partial_col f l (insert h tt live) (insert (f h) tt flive)
            | Some _ => None
            end
  end.
Proof. cbn; destruct (lookup h live) as [[]|]; [|destruct (lookup (f h) flive) as [[]|]]; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_partial_col_success_INJ_lemma" *)
Theorem check_partial_col_success_INJ_lemma : forall l live flive f live' flive',
  domain flive = IMAGE f (domain live) /\
  INJ f (domain live) UNIV /\
  check_partial_col f l live flive = Some (live', flive') ->
  INJ f (set l UNION domain live) UNIV.
Proof.
  induction l as [|h l IH]; intros live flive f live' flive' (Hd & Hinj & Hc).
  - eapply INJ_sub; [exact Hinj|]; intros x; unfold_sets; cbn [LIST_TO_SET]; tauto.
  - rewrite check_partial_col_cons in Hc.
    destruct (lookup h live) as [u|] eqn:Eh.
    + eapply INJ_sub; [eapply IH; eauto|].
      intros x; unfold_sets; cbn [LIST_TO_SET]; intros [[->|Hx]|Hx]; auto.
      right; apply domain_lookup; eauto.
    + destruct (lookup (f h) flive) as [u|] eqn:Efh; [discriminate|].
      assert (Hinj2 : INJ f (domain (insert h tt live)) UNIV).
      { rewrite INJ_UNIV in *; rewrite domain_insert; unfold_sets.
        assert (Hn : forall y, domain live y -> f y <> f h).
        { intros y Hy E. assert (Hin : f h IN domain flive) by (rewrite Hd; exists y; split; auto).
          apply notdom_lookup in Efh; contradiction. }
        intros x y [->|Hx] [->|Hy] E; auto.
        - exfalso; apply (Hn y Hy); auto.
        - exfalso; apply (Hn x Hx); auto. }
      assert (Hd2 : domain (insert (f h) tt flive) = IMAGE f (domain (insert h tt live))).
      { rewrite !domain_insert, Hd; set_ext_tac; split.
        - intros [->|(y & -> & Hy)]; eauto.
        - intros (y & -> & [->|Hy]); eauto. }
      eapply INJ_sub; [eapply IH; eauto|].
      rewrite domain_insert; intros x; unfold_sets; cbn [LIST_TO_SET]; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_partial_col_success_INJ" *)
Theorem check_partial_col_success_INJ : forall l live flive f live' flive',
  domain flive = IMAGE f (domain live) /\
  INJ f (domain live) UNIV /\
  check_partial_col f l live flive = Some (live', flive') ->
  INJ f (set l UNION domain live) UNIV /\
  INJ f (domain live') UNIV.
Proof.
  intros l live flive f live' flive' H.
  pose proof (check_partial_col_success_INJ_lemma _ _ _ _ _ _ H) as Hi; split; [exact Hi|].
  destruct H as (_ & _ & Hc). apply check_partial_col_domain in Hc; cbn [FST] in Hc.
  rewrite Hc; exact Hi.
Qed.

Lemma check_partial_col_INJ_out l live flive f live' flive' :
  domain flive = IMAGE f (domain live) -> INJ f (domain live) UNIV ->
  check_partial_col f l live flive = Some (live', flive') -> INJ f (domain live') UNIV.
Proof. intros; eapply check_partial_col_success_INJ; eauto. Qed.

Lemma check_partial_col_INJ_in l live flive f live' flive' :
  domain flive = IMAGE f (domain live) -> INJ f (domain live) UNIV ->
  check_partial_col f l live flive = Some (live', flive') -> INJ f (set l UNION domain live) UNIV.
Proof. intros; eapply check_partial_col_success_INJ; eauto. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_partial_col_input_monotone" *)
Theorem check_partial_col_input_monotone : forall f live1 flive1 live2 flive2 l v,
  IMAGE f (domain live1) = domain flive1 /\ IMAGE f (domain live2) = domain flive2 ->
  domain live1 SUBSET domain live2 ->
  INJ f (domain live2) UNIV ->
  check_partial_col f l live2 flive2 = Some v ->
  exists livein1 flivein1, check_partial_col f l live1 flive1 = Some (livein1, flivein1).
Proof.
  intros f live1 flive1 live2 flive2 l [v1 v2] [H1 H2] Hs Hinj Hc.
  destruct (check_partial_col_success_INJ l live2 flive2 f v1 v2 (conj (eq_sym H2) (conj Hinj Hc))) as [Hi _].
  destruct (check_partial_col_success l live1 flive1 f) as (a & b & Ha & _).
  - split; [symmetry; exact H1|]. eapply INJ_sub; [exact Hi|].
    intros x; unfold pred_set.SUBSET in Hs; unfold_sets; specialize (Hs x); unfold pred_set.IN in Hs; tauto.
  - eauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "numset_list_delete_IMAGE" *)
Theorem numset_list_delete_IMAGE : forall f l live flive v,
  domain flive = IMAGE f (domain live) ->
  INJ f (domain live) UNIV ->
  check_partial_col f l live flive = Some v ->
  domain (numset_list_delete (MAP f l) flive) = IMAGE f (domain (numset_list_delete l live)).
Proof.
  intros f l live flive [v1 v2] Hd Hinj Hc.
  destruct (check_partial_col_success_INJ l live flive f v1 v2 (conj Hd (conj Hinj Hc))) as [Hi _].
  rewrite INJ_UNIV in Hi.
  rewrite !domain_numset_list_delete, Hd, LIST_TO_SET_MAP. set_ext_tac; split.
  - intros [(y & -> & Hy) Hn]. exists y; split; [reflexivity|]. split; [exact Hy|].
    intros Hm; apply Hn; exists y; auto.
  - intros (y & -> & Hy & Hn). split; [eauto|].
    intros (z & Ez & Hz). apply Hn.
    assert (z = y) as ->; [|exact Hz].
    apply Hi; [left; exact Hz|right; exact Hy|auto].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_partial_col_IMAGE" *)
Theorem check_partial_col_IMAGE : forall f l live flive live' flive',
  domain flive = IMAGE f (domain live) ->
  check_partial_col f l live flive = Some (live', flive') ->
  domain flive' = IMAGE f (domain live').
Proof.
  intros f; induction l as [|h l IH]; intros live flive live' flive' Hd Hc.
  - cbn in Hc; congruence.
  - rewrite check_partial_col_cons in Hc.
    destruct (lookup h live); [eauto|].
    destruct (lookup (f h) flive); [discriminate|].
    eapply IH; [|exact Hc].
    rewrite !domain_insert, Hd; set_ext_tac; split.
    + intros [->|(y & -> & Hy)]; eauto.
    + intros (y & -> & [->|Hy]); eauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "branch_domain" *)
Theorem branch_domain : forall (live1 : num_set) (live2 : num_set),
  set (MAP FST (toAList (difference live2 live1))) UNION domain live1 =
  domain live1 UNION domain live2.
Proof.
  intros live1 live2; rewrite set_MAP_FST_toAList_eq_domain, domain_difference.
  set_ext_tac; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_partial_col_branch_domain" *)
Theorem check_partial_col_branch_domain : forall (live1 : num_set) (live2 : num_set) flive1 liveout fliveout f,
  check_partial_col f (MAP FST (toAList (difference live2 live1))) live1 flive1 =
    Some (liveout, fliveout) ->
  domain liveout = domain live1 UNION domain live2.
Proof.
  intros live1 live2 flive1 liveout fliveout f H.
  apply check_partial_col_domain in H; cbn [FST] in H; rewrite H; apply branch_domain.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_partial_col_branch_comm" *)
Theorem check_partial_col_branch_comm : forall f live1 flive1 live2 flive2 a b,
  INJ f (domain live1) UNIV ->
  domain flive1 = IMAGE f (domain live1) /\ domain flive2 = IMAGE f (domain live2) ->
  check_partial_col f (MAP FST (toAList (difference live2 live1))) live1 flive1 = Some (a, b) ->
  exists c d, check_partial_col f (MAP FST (toAList (difference live1 live2))) live2 flive2 = Some (c, d).
Proof.
  intros f live1 flive1 live2 flive2 a b Hinj [H1 H2] Hc.
  destruct (check_partial_col_success_INJ _ _ _ _ _ _ (conj H1 (conj Hinj Hc))) as [Hi _].
  rewrite branch_domain in Hi.
  destruct (check_partial_col_success (MAP FST (toAList (difference live1 live2))) live2 flive2 f)
    as (c & d & Hcd & _); [|eauto].
  split; [exact H2|]. rewrite branch_domain.
  eapply INJ_sub; [exact Hi|]; intros x; unfold_sets; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_partial_col_list_monotone" *)
Theorem check_partial_col_list_monotone : forall f live flive (s1 : num_set) (s2 : num_set) a b,
  domain flive = IMAGE f (domain live) ->
  INJ f (domain live) UNIV ->
  domain s1 SUBSET domain s2 ->
  check_partial_col f (MAP FST (toAList s2)) live flive = Some (a, b) ->
  exists c d, check_partial_col f (MAP FST (toAList s1)) live flive = Some (c, d).
Proof.
  intros f live flive s1 s2 a b Hd Hinj Hs Hc.
  destruct (check_partial_col_success_INJ _ _ _ _ _ _ (conj Hd (conj Hinj Hc))) as [Hi _].
  destruct (check_partial_col_success (MAP FST (toAList s1)) live flive f) as (c & d & H & _); [|eauto].
  split; [exact Hd|]. eapply INJ_sub; [exact Hi|].
  intros x; rewrite !IN_UNION, !IN_set_MAP_FST_toAList. specialize (Hs x). tauto.
Qed.

(** ** [check_live_tree], [check_col], [check_clash_tree] *)

Ltac inv_opt :=
  repeat match goal with
  | H : Some _ = Some _ |- _ => inversion H; subst; try clear H
  | H : (_, _) = (_, _) |- _ => inversion H; subst; try clear H
  | H : None = Some _ |- _ => discriminate H
  | H : Some _ = None |- _ => discriminate H
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_live_tree_success" *)
Theorem check_live_tree_success : forall lt live flive live' flive' f,
  domain flive = IMAGE f (domain live) /\
  INJ f (domain live) UNIV /\
  check_live_tree f lt live flive = Some (live', flive') ->
  domain flive' = IMAGE f (domain live') /\
  INJ f (domain live') UNIV.
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros live flive live' flive' f (Hd & Hinj & Hc); cbn [check_live_tree] in Hc.
  - destruct (check_partial_col f l live flive) as [v|] eqn:E; [|discriminate]. inv_opt.
    split; [eapply numset_list_delete_IMAGE; eauto|].
    eapply INJ_sub; [exact Hinj|]. intros x; rewrite IN_domain_numset_list_delete; tauto.
  - split; [eapply check_partial_col_IMAGE; eauto|].
    eapply check_partial_col_INJ_out; eauto.
  - destruct (check_live_tree f lt1 live flive) as [[l1 fl1]|] eqn:E1; [|discriminate].
    destruct (check_live_tree f lt2 live flive) as [[l2 fl2]|] eqn:E2; [|discriminate].
    destruct (IH1 _ _ _ _ _ (conj Hd (conj Hinj E1))) as [Hd1 Hi1].
    split; [eapply check_partial_col_IMAGE; eauto|].
    eapply check_partial_col_INJ_out; eauto.
  - destruct (check_live_tree f lt2 live flive) as [[l2 fl2]|] eqn:E2; [|discriminate].
    destruct (IH2 _ _ _ _ _ (conj Hd (conj Hinj E2))) as [Hd2 Hi2].
    eapply IH1; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "ALL_DISTINCT_INJ_MAP" *)
Theorem ALL_DISTINCT_INJ_MAP : forall {A B} `{EqDecision B} (f : A -> B) l,
  ALL_DISTINCT (MAP f l) -> INJ f (set l) UNIV.
Proof.
  intros A B EB f l H; unfold is_true in H; rewrite ALL_DISTINCT_NoDup in H.
  rewrite INJ_UNIV; intros x y Hx Hy E; rewrite IN_set in Hx, Hy.
  induction l as [|h l IH]; [destruct Hx|]. cbn [MAP List.map] in H; inversion H as [|? ? Hn Hd]; subst.
  destruct Hx as [->|Hx], Hy as [->|Hy]; auto.
  - exfalso; apply Hn; rewrite E; apply in_map, Hy.
  - exfalso; apply Hn; rewrite <- E; apply in_map, Hx.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_col_output" *)
Theorem check_col_output : forall {A} f (live : num_map A) live' flive',
  check_col f live = Some (live', flive') ->
  domain flive' = IMAGE f (domain live') /\
  INJ f (domain live') UNIV.
Proof.
  intros A f live live' flive'; unfold check_col.
  destruct (ALL_DISTINCT (MAP (fun x => f (FST x)) (toAList live))) eqn:E; [|discriminate].
  intros H; inv_opt. split.
  - rewrite domain_fromAList, List.map_map; cbn [fst].
    apply set_ext; intros x; cbv beta; unfold is_true.
    rewrite MEM_In, in_map_iff; unfold_sets. split.
    + intros (y & <- & Hy). apply in_map_iff in Hy as ([k v] & <- & Hk).
      exists k; split; [reflexivity|]. apply domain_lookup; exists v; apply In_toAList, Hk.
    + intros (k & -> & Hk). apply domain_lookup in Hk as [v Hv]. exists (f k); split; [reflexivity|].
      apply in_map_iff; exists (k, v); split; [reflexivity|apply In_toAList, Hv].
  - rewrite <- set_MAP_FST_toAList_eq_domain. apply ALL_DISTINCT_INJ_MAP.
    rewrite List.map_map; exact E.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_col_success" *)
Theorem check_col_success : forall {A} f (live : num_map A),
  INJ f (domain live) UNIV ->
  exists flive, check_col f live = Some (live, flive).
Proof.
  intros A f live Hinj; unfold check_col.
  assert (ALL_DISTINCT (MAP (fun x => f (FST x)) (toAList live)) = true) as ->; [|eauto].
  rewrite ALL_DISTINCT_NoDup, <- List.map_map. apply NoDup_map_inj.
  2:{ pose proof (ALL_DISTINCT_MAP_FST_toAList live) as D; unfold is_true in D; rewrite ALL_DISTINCT_NoDup in D; exact D. }
  intros x y Hx Hy E. rewrite INJ_UNIV in Hinj; apply Hinj; auto.
  - apply IN_set_MAP_FST_toAList, IN_set, Hx.
  - apply IN_set_MAP_FST_toAList, IN_set, Hy.
Qed.

Lemma INJ_SUBSET_UNIV {A B} (f : A -> B) s t : INJ f t UNIV -> s SUBSET t -> INJ f s UNIV.
Proof. intros H S; eapply INJ_sub; [exact H|exact S]. Qed.

Lemma IN_domain_LN {A} x : x IN domain (@LN A) <-> False.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_clash_tree_output" *)
Theorem check_clash_tree_output : forall f ct live flive livein flivein,
  domain flive = IMAGE f (domain live) /\
  INJ f (domain live) UNIV /\
  check_clash_tree f ct live flive = Some (livein, flivein) ->
  domain flivein = IMAGE f (domain livein) /\
  INJ f (domain livein) UNIV.
Proof.
  intros f ct; induction ct as [w r|s|o c1 IH1 c2 IH2|c1 IH1 c2 IH2];
    intros live flive livein flivein (Hd & Hinj & Hc); cbn [check_clash_tree] in Hc.
  - destruct (check_partial_col f w live flive) as [v|] eqn:E; [|discriminate].
    pose proof (numset_list_delete_IMAGE f w live flive v Hd Hinj E) as Hd'.
    assert (Hi' : INJ f (domain (numset_list_delete w live)) UNIV).
    { eapply INJ_sub; [exact Hinj|]; intros x; rewrite IN_domain_numset_list_delete; tauto. }
    split; [eapply check_partial_col_IMAGE; eauto|eapply check_partial_col_INJ_out; eauto].
  - eapply check_col_output; eauto.
  - destruct (check_clash_tree f c1 live flive) as [[t1 ft1]|] eqn:E1; [|discriminate].
    destruct (check_clash_tree f c2 live flive) as [[t2 ft2]|] eqn:E2; [|discriminate].
    destruct o as [t|].
    + eapply check_col_output; eauto.
    + destruct (IH1 _ _ _ _ (conj Hd (conj Hinj E1))) as [Hd1 Hi1].
      split; [eapply check_partial_col_IMAGE; eauto|eapply check_partial_col_INJ_out; eauto].
  - destruct (check_clash_tree f c2 live flive) as [[t2 ft2]|] eqn:E2; [|discriminate].
    destruct (IH2 _ _ _ _ (conj Hd (conj Hinj E2))) as [Hd2 Hi2].
    eapply IH1; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_live_tree_correct_lemma" *)
Theorem get_live_tree_correct_lemma : forall f live flive live' flive' ct livein' flivein',
  IMAGE f (domain live) = domain flive /\ IMAGE f (domain live') = domain flive' ->
  INJ f (domain live') UNIV ->
  domain live SUBSET domain live' ->
  check_live_tree f (get_live_tree ct) live' flive' = Some (livein', flivein') ->
  exists livein flivein, check_clash_tree f ct live flive = Some (livein, flivein) /\
    domain livein SUBSET domain livein'.
Proof.
  intros f live flive live' flive' ct; revert live flive live' flive'.
  induction ct as [w r|s|o c1 IH1 c2 IH2|c1 IH1 c2 IH2];
    intros live flive live' flive' livein' flivein' [H1 H2] Hinj Hsub Hc;
    assert (Hinjl : INJ f (domain live) UNIV) by (eapply INJ_SUBSET_UNIV; eauto);
    cbn [get_live_tree check_live_tree] in Hc; cbn [check_clash_tree].
  - destruct (check_partial_col f w live' flive') as [v'|] eqn:Ew'; [|discriminate].
    destruct (check_partial_col_input_monotone f live flive live' flive' w v' (conj H1 H2) Hsub Hinj Ew')
      as (a & b & Ew). rewrite Ew.
    pose proof (numset_list_delete_IMAGE f w live flive (a, b) (eq_sym H1) Hinjl Ew) as HI1.
    pose proof (numset_list_delete_IMAGE f w live' flive' v' (eq_sym H2) Hinj Ew') as HI2.
    assert (Hinj2 : INJ f (domain (numset_list_delete w live')) UNIV).
    { eapply INJ_sub; [exact Hinj|]; intros x; rewrite IN_domain_numset_list_delete; tauto. }
    assert (Hsub2 : domain (numset_list_delete w live) SUBSET domain (numset_list_delete w live')).
    { intros x; rewrite !IN_domain_numset_list_delete; specialize (Hsub x); tauto. }
    destruct (check_partial_col_input_monotone f _ _ _ _ r _ (conj (eq_sym HI1) (eq_sym HI2)) Hsub2 Hinj2 Hc)
      as (c & d & Er).
    exists c, d; split; [exact Er|].
    apply check_partial_col_domain in Er; apply check_partial_col_domain in Hc; cbn [FST] in Er, Hc.
    rewrite Er, Hc; intros x; rewrite !IN_UNION. specialize (Hsub2 x); tauto.
  - pose proof (check_partial_col_INJ_in _ _ _ _ _ _ (eq_sym H2) Hinj Hc) as Hi.
    destruct (check_col_success f s) as [fs Hs].
    { eapply INJ_sub; [exact Hi|]; intros x Hx; left; apply IN_set_MAP_FST_toAList, Hx. }
    rewrite Hs; exists s, fs; split; [reflexivity|].
    apply check_partial_col_domain in Hc; cbn [FST] in Hc; rewrite Hc.
    intros x Hx; left; apply IN_set_MAP_FST_toAList, Hx.
  - assert (Hgen : forall (o' : option num_set) lt', check_live_tree f
          (match o' with Some cs => Seq (Reads (MAP FST (toAList cs))) lt' | None => lt' end) live' flive'
          = Some (livein', flivein') -> exists a b, check_live_tree f lt' live' flive' = Some (a, b)).
    { intros [cs|] lt' H; [|eauto]. cbn [check_live_tree] in H.
      destruct (check_live_tree f lt' live' flive') as [[a b]|]; [eauto|discriminate]. }
    destruct (Hgen o _ Hc) as (lm0 & flm0 & EB0); cbn [check_live_tree] in EB0.
    destruct (check_live_tree f (get_live_tree c1) live' flive') as [[l1' fl1']|] eqn:E1; [|discriminate].
    destruct (check_live_tree f (get_live_tree c2) live' flive') as [[l2' fl2']|] eqn:E2; [|discriminate].
    destruct (IH1 live flive live' flive' l1' fl1' (conj H1 H2) Hinj Hsub E1) as (t1 & ft1 & Ec1 & S1).
    destruct (IH2 live flive live' flive' l2' fl2' (conj H1 H2) Hinj Hsub E2) as (t2 & ft2 & Ec2 & S2).
    rewrite Ec1, Ec2.
    destruct (check_live_tree_success _ _ _ _ _ _ (conj (eq_sym H2) (conj Hinj E1))) as [Hd1' Hi1'].
    destruct o as [cut|].
    + cbn [check_live_tree] in Hc; rewrite E1, E2, EB0 in Hc.
      rename lm0 into lm, flm0 into flm, EB0 into Em.
      assert (EB : check_live_tree f (Branch (get_live_tree c1) (get_live_tree c2)) live' flive' = Some (lm, flm))
        by (cbn [check_live_tree]; rewrite E1, E2; exact Em).
      destruct (check_live_tree_success _ _ _ _ _ _ (conj (eq_sym H2) (conj Hinj EB))) as [Hdm Him].
      pose proof (check_partial_col_INJ_in _ _ _ _ _ _ Hdm Him Hc) as Hi.
      destruct (check_col_success f cut) as [fc Hcut].
      { eapply INJ_sub; [exact Hi|]; intros x Hx; left; apply IN_set_MAP_FST_toAList, Hx. }
      rewrite Hcut; exists cut, fc; split; [reflexivity|].
      apply check_partial_col_domain in Hc; cbn [FST] in Hc; rewrite Hc.
      intros x Hx; left; apply IN_set_MAP_FST_toAList, Hx.
    + cbn [check_live_tree] in Hc; rewrite E1, E2 in Hc.
      pose proof (check_partial_col_INJ_in _ _ _ _ _ _ Hd1' Hi1' Hc) as Hi.
      rewrite branch_domain in Hi.
      destruct (check_clash_tree_output f c1 live flive t1 ft1 (conj (eq_sym H1) (conj Hinjl Ec1))) as [Hdt1 _].
      destruct (check_partial_col_success (MAP FST (toAList (difference t2 t1))) t1 ft1 f) as (a & b & Eab & _).
      { split; [exact Hdt1|]. rewrite branch_domain. eapply INJ_sub; [exact Hi|].
        intros x; rewrite !IN_UNION; specialize (S1 x); specialize (S2 x); tauto. }
      rewrite Eab; exists a, b; split; [reflexivity|].
      rewrite (check_partial_col_branch_domain _ _ _ _ _ _ Eab), (check_partial_col_branch_domain _ _ _ _ _ _ Hc).
      intros x; rewrite !IN_UNION; specialize (S1 x); specialize (S2 x); tauto.
  - destruct (check_live_tree f (get_live_tree c2) live' flive') as [[l2' fl2']|] eqn:E2; [|discriminate].
    destruct (IH2 live flive live' flive' l2' fl2' (conj H1 H2) Hinj Hsub E2) as (t2 & ft2 & Ec2 & S2).
    destruct (check_live_tree_success _ _ _ _ _ _ (conj (eq_sym H2) (conj Hinj E2))) as [Hd2' Hi2'].
    destruct (check_clash_tree_output f c2 live flive t2 ft2 (conj (eq_sym H1) (conj Hinjl Ec2))) as [Hdt2 _].
    rewrite Ec2. eapply (IH1 t2 ft2 l2' fl2'); eauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_live_tree_correct" *)
Theorem get_live_tree_correct : forall f live flive ct livein flivein,
  IMAGE f (domain live) = domain flive ->
  INJ f (domain live) UNIV ->
  check_live_tree f (get_live_tree ct) live flive = Some (livein, flivein) ->
  exists livein' flivein', check_clash_tree f ct live flive = Some (livein', flivein').
Proof.
  intros f live flive ct livein flivein H1 H2 H3.
  destruct (get_live_tree_correct_lemma f live flive live flive ct livein flivein (conj H1 H1) H2
    (fun x H => H) H3) as (a & b & E & _); eauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_live_tree_correct_LN" *)
Theorem get_live_tree_correct_LN : forall f ct livein flivein,
  check_live_tree f (get_live_tree ct) LN LN = Some (livein, flivein) ->
  exists livein' flivein', check_clash_tree f ct LN LN = Some (livein', flivein').
Proof.
  intros f ct livein flivein H; eapply get_live_tree_correct; [| |exact H].
  - apply set_ext; intros x; unfold_sets; cbn [domain]; split; [intros (? & _ & [])|intros []].
  - rewrite INJ_UNIV; intros x y [].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_partial_col_numset_list_insert" *)
Theorem check_partial_col_numset_list_insert : forall f l live flive liveout fliveout,
  check_partial_col f l live flive = Some (liveout, fliveout) ->
  liveout = numset_list_insert l live.
Proof.
  intros f; induction l as [|h l IH]; intros live flive liveout fliveout Hc.
  - cbn in *; congruence.
  - rewrite check_partial_col_cons in Hc; cbn [numset_list_insert].
    destruct (lookup_unit_cases' h live) as [E|E]; rewrite E in Hc.
    + destruct (lookup (f h) flive); [discriminate|]. eapply IH; eauto.
    + rewrite <- (lookup_insert_id h tt live E). eapply IH; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_live_tree_eq_get_live_backward" *)
Theorem check_live_tree_eq_get_live_backward : forall f lt live flive liveout fliveout,
  check_live_tree f lt live flive = Some (liveout, fliveout) ->
  liveout = get_live_backward lt live.
Proof.
  intros f; induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros live flive liveout fliveout Hc; cbn [check_live_tree get_live_backward] in *.
  - destruct (check_partial_col f l live flive); [congruence|discriminate].
  - eapply check_partial_col_numset_list_insert; eauto.
  - destruct (check_live_tree f lt1 live flive) as [[l1 fl1]|] eqn:E1; [|discriminate].
    destruct (check_live_tree f lt2 live flive) as [[l2 fl2]|] eqn:E2; [|discriminate].
    rewrite <- (IH1 _ _ _ _ E1), <- (IH2 _ _ _ _ E2).
    eapply check_partial_col_numset_list_insert; eauto.
  - destruct (check_live_tree f lt2 live flive) as [[l2 fl2]|] eqn:E2; [|discriminate].
    rewrite <- (IH2 _ _ _ _ E2). eapply IH1; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "fix_domination_fixes_domination" *)
Theorem fix_domination_fixes_domination : forall lt,
  domain (get_live_backward (fix_domination lt) LN) = EMPTY.
Proof.
  intros lt; unfold fix_domination.
  destruct (bool_decide (get_live_backward lt LN = LN)) eqn:E.
  - apply bool_decide_spec in E; rewrite E; reflexivity.
  - cbn [get_live_backward]. rewrite domain_numset_list_delete, set_MAP_FST_toAList_eq_domain.
    set_ext_tac; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "fix_domination_check_live_tree" *)
Theorem fix_domination_check_live_tree : forall f lt liveout fliveout,
  check_live_tree f (fix_domination lt) LN LN = Some (liveout, fliveout) ->
  exists liveout' fliveout', check_live_tree f lt LN LN = Some (liveout', fliveout').
Proof.
  intros f lt liveout fliveout; unfold fix_domination.
  destruct (bool_decide _); [eauto|].
  cbn [check_live_tree]. destruct (check_live_tree f lt LN LN) as [[a b]|]; [eauto|discriminate].
Qed.

(** ** Number properties *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "size_of_live_tree_positive" *)
Theorem size_of_live_tree_positive : forall lt, (0 <= size_of_live_tree lt)%Z.
Proof. induction lt; cbn [size_of_live_tree]; lia. Qed.

Ltac bsplit' :=
  unfold is_true in *;
  repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_prop in H; destruct H
  | |- (_ && _) = true => apply andb_true_intro; split
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_number_property_strong_monotone_weak" *)
Theorem check_number_property_strong_monotone_weak : forall (P Q : Z -> num_set -> bool) lt n live,
  (forall n' live', P n' live' -> Q n' live') /\
  check_number_property_strong P lt n live ->
  check_number_property_strong Q lt n live.
Proof.
  intros P Q; induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2]; intros n live [HPQ H];
    cbn [check_number_property_strong] in *; bsplit'; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_number_property_strong_monotone" *)
Theorem check_number_property_strong_monotone : forall (P Q : Z -> num_set -> bool) lt n live,
  (forall n' live', (n - size_of_live_tree lt <= n')%Z /\ P n' live' -> Q n' live') /\
  check_number_property_strong P lt n live ->
  check_number_property_strong Q lt n live.
Proof.
  intros P Q; induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2]; intros n live [HPQ H];
    cbn [check_number_property_strong size_of_live_tree] in *; bsplit';
    try (apply HPQ; split; [lia|assumption]);
    pose proof (size_of_live_tree_positive lt1); pose proof (size_of_live_tree_positive lt2);
    try (apply HPQ; split; [lia|assumption]);
    first [eapply IH1|eapply IH2]; (split; [|eassumption]);
    intros n' l' [Hn HP]; apply HPQ; (split; [lia|exact HP]).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_number_property_strong_end" *)
Theorem check_number_property_strong_end : forall (P : Z -> num_set -> bool) lt n live,
  check_number_property_strong P lt n live ->
  P (n - size_of_live_tree lt)%Z (get_live_backward lt live).
Proof.
  intros P; induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2]; intros n live H;
    cbn [check_number_property_strong size_of_live_tree get_live_backward] in *; bsplit'; auto.
  specialize (IH1 _ _ H). replace (n - (size_of_live_tree lt1 + size_of_live_tree lt2))%Z
    with (n - size_of_live_tree lt2 - size_of_live_tree lt1)%Z by lia. exact IH1.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_number_property_monotone_weak" *)
Theorem check_number_property_monotone_weak : forall (P Q : Z -> num_set -> bool) lt n live,
  (forall n' live', P n' live' -> Q n' live') /\
  check_number_property P lt n live ->
  check_number_property Q lt n live.
Proof.
  intros P Q; induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2]; intros n live [HPQ H];
    cbn [check_number_property] in *; bsplit'; eauto.
Qed.

(** ** [numset_list_add_if] *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "lookup_numset_list_add_if" *)
Theorem lookup_numset_list_add_if : forall r l v s P,
  lookup r (numset_list_add_if l v s P) =
    if MEM r l then
      match lookup r s with
      | Some vr => if P v vr then Some v else Some vr
      | None => Some v
      end
    else lookup r s.
Proof.
  intros r l; induction l as [|h l IH]; intros v s P; [reflexivity|].
  cbn [numset_list_add_if MEM].
  destruct (lookup h s) as [x|] eqn:Eh; [destruct (P v x) eqn:EP|]; rewrite ?IH, ?lookup_insert;
    destruct (decide (r = h)) as [->|Hne];
    rewrite ?(proj2 (bool_decide_spec (h = h)) eq_refl), ?Eh; cbn [orb];
    try (assert (bool_decide (r = h) = false) as -> by
           (destruct (bool_decide (r = h)) eqn:B; [apply bool_decide_spec in B; contradiction|reflexivity]);
         cbn [orb]);
    try (destruct (MEM h l)); try (destruct (MEM r l)); rewrite ?Eh, ?EP; try reflexivity;
    try (destruct (P v v); reflexivity).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "lookup_numset_list_add_if_lt" *)
Theorem lookup_numset_list_add_if_lt : forall r l v s,
  lookup r (numset_list_add_if_lt l v s) =
    if MEM r l then
      match lookup r s with
      | Some vr => if (v <=? vr)%Z then Some v else Some vr
      | None => Some v
      end
    else lookup r s.
Proof. intros; unfold numset_list_add_if_lt; apply lookup_numset_list_add_if. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "lookup_numset_list_add_if_gt" *)
Theorem lookup_numset_list_add_if_gt : forall r l v s,
  lookup r (numset_list_add_if_gt l v s) =
    if MEM r l then
      match lookup r s with
      | Some vr => if (vr <=? v)%Z then Some v else Some vr
      | None => Some v
      end
    else lookup r s.
Proof. intros; unfold numset_list_add_if_gt; apply lookup_numset_list_add_if. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "domain_numset_list_add_if" *)
Theorem domain_numset_list_add_if : forall l v s P,
  domain (numset_list_add_if l v s P) = set l UNION domain s.
Proof.
  intros l v s P; apply set_ext; intros x.
  change (x IN domain (numset_list_add_if l v s P) <-> x IN (set l UNION domain s)).
  rewrite IN_UNION, !dom_lookup, lookup_numset_list_add_if, <- MEM_IN_set.
  destruct (MEM x l); [|split; [intros; right; auto|intros [[=]|H]; exact H]].
  split; [left; reflexivity|intros _].
  destruct (lookup x s) as [vr|]; [destruct (P v vr)|]; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "domain_numset_list_add_if_lt" *)
Theorem domain_numset_list_add_if_lt : forall l v s,
  domain (numset_list_add_if_lt l v s) = set l UNION domain s.
Proof. intros; apply domain_numset_list_add_if. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "domain_numset_list_add_if_gt" *)
Theorem domain_numset_list_add_if_gt : forall l v s,
  domain (numset_list_add_if_gt l v s) = set l UNION domain s.
Proof. intros; apply domain_numset_list_add_if. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "lookup_numset_list_delete" *)
Theorem lookup_numset_list_delete : forall {A} l (s : num_map A) x,
  lookup x (numset_list_delete l s) = if MEM x l then None else lookup x s.
Proof.
  intros A; induction l as [|h l IH]; intros s x; [reflexivity|].
  cbn [numset_list_delete MEM]; rewrite IH, lookup_delete.
  destruct (decide (x = h)) as [->|Hne].
  - rewrite (proj2 (bool_decide_spec (h = h)) eq_refl); cbn [orb]; destruct (MEM h l); reflexivity.
  - assert (bool_decide (x = h) = false) as ->
      by (destruct (bool_decide (x = h)) eqn:B; [apply bool_decide_spec in B; contradiction|reflexivity]).
    reflexivity.
Qed.

(** ** [get_intervals] *)

Ltac dlk :=
  repeat match goal with
  | H : context [match lookup ?r ?t with Some _ => _ | None => _ end] |- _ =>
      let E := fresh "L" in destruct (lookup r t) eqn:E
  | |- context [match lookup ?r ?t with Some _ => _ | None => _ end] =>
      let E := fresh "L" in destruct (lookup r t) eqn:E
  end.

Ltac ddec :=
  repeat match goal with
  | H : context [if decide ?P then _ else _] |- _ => destruct (decide P)
  | |- context [if decide ?P then _ else _] => destruct (decide P)
  | H : context [if MEM ?x ?l then _ else _] |- _ => let E := fresh "M" in destruct (MEM x l) eqn:E
  | |- context [if MEM ?x ?l then _ else _] => let E := fresh "M" in destruct (MEM x l) eqn:E
  | H : context [if Z.leb ?a ?b then _ else _] |- _ => let E := fresh "Z" in destruct (Z.leb_spec a b) as [E|E]
  | |- context [if Z.leb ?a ?b then _ else _] => let E := fresh "Z" in destruct (Z.leb_spec a b) as [E|E]
  end.

Ltac spec_lk :=
  repeat match goal with
  | B : forall r v, lookup r ?t = Some v -> _, L : lookup ?r0 ?t = Some ?v0 |- _ =>
      let T := type of (B r0 v0 L) in
      lazymatch goal with
      | _ : T |- _ => fail
      | _ => pose proof (B r0 v0 L)
      end
  | E : forall r v1 v2, lookup r ?t1 = Some v1 /\ lookup r ?t2 = Some v2 -> _,
    L1 : lookup ?r0 ?t1 = Some ?a, L2 : lookup ?r0 ?t2 = Some ?b |- _ =>
      let T := type of (E r0 a b (conj L1 L2)) in
      lazymatch goal with
      | _ : T |- _ => fail
      | _ => pose proof (E r0 a b (conj L1 L2))
      end
  end.

Lemma MEM_keys {A} r (s : num_map A) : MEM r (MAP FST (toAList s)) = true <-> r IN domain s.
Proof. rewrite MEM_IN_set; apply IN_set_MAP_FST_toAList. Qed.


(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_nout" *)
Theorem get_intervals_nout : forall lt n_in beg_in end_in n_out beg_out end_out,
  (n_out, (beg_out, end_out)) = get_intervals lt n_in beg_in end_in ->
  n_out = (n_in - size_of_live_tree lt)%Z.
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2]; intros n_in beg_in end_in n_out beg_out end_out H;
    cbn [get_intervals size_of_live_tree] in *; [inv_opt; lia|inv_opt; lia| |];
    destruct (get_intervals lt2 n_in beg_in end_in) as [n2 [b2 e2]] eqn:E2;
    rewrite (IH1 _ _ _ _ _ _ H), (IH2 _ _ _ _ _ _ (eq_sym E2)); lia.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_withlive_nout" *)
Theorem get_intervals_withlive_nout : forall lt n_in beg_in end_in n_out beg_out end_out live,
  (n_out, (beg_out, end_out)) = get_intervals_withlive lt n_in beg_in end_in live ->
  n_out = (n_in - size_of_live_tree lt)%Z.
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2]; intros n_in beg_in end_in n_out beg_out end_out live H;
    cbn [get_intervals_withlive size_of_live_tree] in *; [inv_opt; lia|inv_opt; lia| |].
  - destruct (get_intervals_withlive lt2 n_in beg_in end_in live) as [n2 [b2 e2]] eqn:E2.
    destruct (get_intervals_withlive lt1 n2 (difference b2 live) e2 live) as [n1 [b1 e1]] eqn:E1.
    inv_opt. rewrite (IH1 _ _ _ _ _ _ _ (eq_sym E1)), (IH2 _ _ _ _ _ _ _ (eq_sym E2)); lia.
  - destruct (get_intervals_withlive lt2 n_in beg_in end_in live) as [n2 [b2 e2]] eqn:E2.
    destruct (get_intervals_withlive lt1 n2 b2 e2 (get_live_backward lt2 live)) as [n1 [b1 e1]] eqn:E1.
    inv_opt. rewrite (IH1 _ _ _ _ _ _ _ (eq_sym E1)), (IH2 _ _ _ _ _ _ _ (eq_sym E2)); lia.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_intend_augment" *)
Theorem get_intervals_intend_augment : forall lt n_in beg_in end_in n_out beg_out end_out,
  (n_out, (beg_out, end_out)) = get_intervals lt n_in beg_in end_in ->
  forall r v, lookup r end_in = Some v -> exists v', lookup r end_out = Some v' /\ (v <= v')%Z.
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2]; intros n_in beg_in end_in n_out beg_out end_out H r v Hv;
    cbn [get_intervals] in *.
  1,2: inv_opt; rewrite lookup_numset_list_add_if_gt, Hv; ddec; eexists; split; try reflexivity; lia.
  all: destruct (get_intervals lt2 n_in beg_in end_in) as [n2 [b2 e2]] eqn:E2;
    destruct (IH2 _ _ _ _ _ _ (eq_sym E2) r v Hv) as (v1 & Hv1 & Le1);
    destruct (IH1 _ _ _ _ _ _ H r v1 Hv1) as (v2 & Hv2 & Le2); exists v2; split; [exact Hv2|lia].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_number_property_intend" *)
Theorem check_number_property_intend : forall end_out lt n_in live_in,
  check_number_property (fun n (live : num_set) =>
    ⌜forall r, r IN domain live -> exists v, lookup r end_out = Some v /\ (n + 1 <= v)%Z⌝) lt n_in live_in ->
  forall r, r IN domain (get_live_backward lt live_in) ->
    exists v, lookup r end_out = Some v /\ (n_in - size_of_live_tree lt <= v)%Z.
Proof.
  intros end_out; induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2]; intros n_in live_in H r Hr;
    cbn [check_number_property get_live_backward size_of_live_tree] in *; bsplit'.
  1,2: apply bool_decide_spec in H; destruct (H r Hr) as (v & Hv & Le); exists v; split; [exact Hv|lia].
  - pose proof (size_of_live_tree_positive lt1); pose proof (size_of_live_tree_positive lt2).
    rewrite domain_numset_list_insert, branch_domain, IN_UNION in Hr. destruct Hr as [Hr|Hr].
    + destruct (IH1 _ _ H r Hr) as (v & Hv & Le); exists v; split; [exact Hv|lia].
    + destruct (IH2 _ _ H0 r Hr) as (v & Hv & Le); exists v; split; [exact Hv|lia].
  - destruct (IH1 _ _ H r Hr) as (v & Hv & Le); exists v; split; [exact Hv|lia].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_live_less_end" *)
Theorem get_intervals_live_less_end : forall lt n_in beg_in end_in live_in n_out beg_out end_out,
  (n_out, (beg_out, end_out)) = get_intervals lt n_in beg_in end_in /\
  (forall r, r IN domain live_in -> exists v, lookup r end_in = Some v /\ (n_in <= v)%Z) ->
  check_number_property (fun n (live : num_set) =>
    ⌜forall r, r IN domain live -> exists v, lookup r end_out = Some v /\ (n + 1 <= v)%Z⌝) lt n_in live_in.
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros n_in beg_in end_in live_in n_out beg_out end_out [H Hl];
    cbn [get_intervals check_number_property] in *.
  - inv_opt. apply bool_decide_spec; intros r Hr. rewrite IN_domain_numset_list_delete in Hr; destruct Hr as [Hr Hn].
    destruct (Hl r Hr) as (v & Hv & Le). rewrite lookup_numset_list_add_if_gt.
    assert (MEM r l = false) as -> by (destruct (MEM r l) eqn:M; [apply MEM_IN_set in M; contradiction|reflexivity]).
    exists v; split; [exact Hv|lia].
  - inv_opt. apply bool_decide_spec; intros r Hr. rewrite IN_domain_numset_list_insert in Hr.
    rewrite lookup_numset_list_add_if_gt. destruct (MEM r l) eqn:M.
    + dlk; ddec; eexists; split; try reflexivity; lia.
    + destruct Hr as [Hr|Hr]; [apply MEM_IN_set in Hr; congruence|].
      destruct (Hl r Hr) as (v & Hv & Le); exists v; split; [exact Hv|lia].
  - destruct (get_intervals lt2 n_in beg_in end_in) as [n2 [b2 e2]] eqn:E2.
    pose proof (get_intervals_nout _ _ _ _ _ _ _ (eq_sym E2)) as Hn2.
    pose proof (size_of_live_tree_positive lt1); pose proof (size_of_live_tree_positive lt2).
    bsplit'.
    + subst n2. eapply IH1; split; [exact H|]. intros r Hr.
      destruct (Hl r Hr) as (v & Hv & Le).
      destruct (get_intervals_intend_augment _ _ _ _ _ _ _ (eq_sym E2) r v Hv) as (v' & Hv' & Le').
      exists v'; split; [exact Hv'|lia].
    + refine (check_number_property_monotone_weak _ _ _ _ _ (conj _ (IH2 _ _ _ _ _ _ _ (conj (eq_sym E2) Hl)))).
      intros n' l' Hp; apply bool_decide_spec; apply bool_decide_spec in Hp; intros r Hr.
      destruct (Hp r Hr) as (v & Hv & Le).
      destruct (get_intervals_intend_augment _ _ _ _ _ _ _ H r v Hv) as (v' & Hv' & Le').
      exists v'; split; [exact Hv'|lia].
  - destruct (get_intervals lt2 n_in beg_in end_in) as [n2 [b2 e2]] eqn:E2.
    pose proof (get_intervals_nout _ _ _ _ _ _ _ (eq_sym E2)) as Hn2.
    assert (C2 := IH2 _ _ _ _ _ _ _ (conj (eq_sym E2) Hl)).
    bsplit'.
    + subst n2. eapply IH1; split; [exact H|].
      intros r Hr; destruct (check_number_property_intend _ _ _ _ C2 r Hr) as (v & Hv & Le).
      exists v; split; [exact Hv|lia].
    + refine (check_number_property_monotone_weak _ _ _ _ _ (conj _ C2)).
      intros n' l' Hp; apply bool_decide_spec; apply bool_decide_spec in Hp; intros r Hr.
      destruct (Hp r Hr) as (v & Hv & Le).
      destruct (get_intervals_intend_augment _ _ _ _ _ _ _ H r v Hv) as (v' & Hv' & Le').
      exists v'; split; [exact Hv'|lia].
Qed.

Tactic Notation "gwl_destr" hyp(H) "as" ident(n2) ident(b2) ident(e2) ident(E2)
    ident(n1) ident(b1) ident(e1) ident(E1) :=
  cbn [get_intervals_withlive get_live_backward] in H;
  lazymatch type of H with
  | context [get_intervals_withlive ?lt2 ?n ?b ?e ?lv] =>
      destruct (get_intervals_withlive lt2 n b e lv) as [n2 [b2 e2]] eqn:E2;
      lazymatch type of H with
      | context [get_intervals_withlive ?lt1 ?n' ?b' ?e' ?lv'] =>
          destruct (get_intervals_withlive lt1 n' b' e' lv') as [n1 [b1 e1]] eqn:E1;
          symmetry in E1, E2; inv_opt
      end
  end.

Tactic Notation "gi_destr" hyp(H) "as" ident(n2) ident(b2) ident(e2) ident(E2) :=
  cbn [get_intervals] in H;
  lazymatch type of H with
  | context [get_intervals ?lt2 ?n ?b ?e] =>
      destruct (get_intervals lt2 n b e) as [n2 [b2 e2]] eqn:E2; symmetry in E2
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_withlive_intbeg_reduce" *)
Theorem get_intervals_withlive_intbeg_reduce : forall lt n_in beg_in end_in n_out beg_out end_out live,
  (n_out, (beg_out, end_out)) = get_intervals_withlive lt n_in beg_in end_in live /\
  (forall r v, lookup r beg_in = Some v -> (n_in <= v)%Z) ->
  (forall r, (match lookup r beg_out with None => n_out | Some x => x end <=
              match lookup r beg_in with None => n_in | Some x => x end)%Z) /\
  (forall r v, lookup r beg_out = Some v -> (n_out <= v)%Z).
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros n_in beg_in end_in n_out beg_out end_out live [H Hb].
  - cbn [get_intervals_withlive] in H; inv_opt. split.
    + intros r; rewrite lookup_numset_list_add_if_lt; ddec; dlk; ddec;
        try (specialize (Hb r _ L)); try (specialize (Hb r _ L0)); lia.
    + intros r v; rewrite lookup_numset_list_add_if_lt; ddec; dlk; ddec; intros E; inv_opt;
        try (specialize (Hb r _ L)); try (specialize (Hb r _ E)); lia.
  - cbn [get_intervals_withlive] in H; inv_opt. split.
    + intros r; rewrite lookup_numset_list_delete; ddec; dlk; try (specialize (Hb r _ L)); lia.
    + intros r v; rewrite lookup_numset_list_delete; ddec; intros E; [discriminate|].
      specialize (Hb r _ E); lia.
  - gwl_destr H as n2 b2 e2 E2 n1 b1 e1 E1.
    pose proof (get_intervals_withlive_nout _ _ _ _ _ _ _ _ E2) as N2.
    pose proof (get_intervals_withlive_nout _ _ _ _ _ _ _ _ E1) as N1.
    pose proof (size_of_live_tree_positive lt1); pose proof (size_of_live_tree_positive lt2).
    destruct (IH2 _ _ _ _ _ _ _ (conj E2 Hb)) as [R2 B2].
    assert (Bd : forall r v, lookup r (difference b2 live) = Some v -> (n2 <= v)%Z).
    { intros r v; rewrite lookup_difference; ddec; [apply B2|discriminate]. }
    destruct (IH1 _ _ _ _ _ _ _ (conj E1 Bd)) as [R1 B1].
    split.
    + intros r; specialize (R1 r); specialize (R2 r); rewrite lookup_difference in *; ddec; dlk;
        try (specialize (Hb r _ L)); try (specialize (Hb r _ L0)); try (specialize (Hb r _ L1)); lia.
    + intros r v; rewrite lookup_difference; ddec; [apply B1|discriminate].
  - gwl_destr H as n2 b2 e2 E2 n1 b1 e1 E1.
    pose proof (get_intervals_withlive_nout _ _ _ _ _ _ _ _ E2) as N2.
    pose proof (get_intervals_withlive_nout _ _ _ _ _ _ _ _ E1) as N1.
    pose proof (size_of_live_tree_positive lt1); pose proof (size_of_live_tree_positive lt2).
    destruct (IH2 _ _ _ _ _ _ _ (conj E2 Hb)) as [R2 B2].
    destruct (IH1 _ _ _ _ _ _ _ (conj E1 B2)) as [R1 B1].
    split; [|exact B1].
    intros r; specialize (R1 r); specialize (R2 r); dlk; lia.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_withlive_intbeg_nout" *)
Theorem get_intervals_withlive_intbeg_nout : forall lt n_in beg_in end_in n_out beg_out end_out live,
  (n_out, (beg_out, end_out)) = get_intervals_withlive lt n_in beg_in end_in live /\
  (forall r v, lookup r beg_in = Some v -> (n_in <= v)%Z) ->
  (forall r v, lookup r beg_out = Some v -> (n_out <= v)%Z).
Proof. intros; eapply get_intervals_withlive_intbeg_reduce; eauto. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_intbeg_nout" *)
Theorem get_intervals_intbeg_nout : forall lt n_in beg_in end_in n_out beg_out end_out,
  (n_out, (beg_out, end_out)) = get_intervals lt n_in beg_in end_in /\
  (forall r v, lookup r beg_in = Some v -> (n_in <= v)%Z) ->
  (forall r v, lookup r beg_out = Some v -> (n_out <= v)%Z).
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros n_in beg_in end_in n_out beg_out end_out [H Hb] r v Hv.
  - cbn [get_intervals] in H; inv_opt. rewrite lookup_numset_list_add_if_lt in Hv; ddec; dlk; ddec; inv_opt;
      try (specialize (Hb r _ L)); try (specialize (Hb r _ Hv)); lia.
  - cbn [get_intervals] in H; inv_opt. specialize (Hb r _ Hv); lia.
  - gi_destr H as n2 b2 e2 E2. eapply IH1; [split; [exact H|]|exact Hv]. eapply IH2; split; [exact E2|exact Hb].
  - gi_destr H as n2 b2 e2 E2. eapply IH1; [split; [exact H|]|exact Hv]. eapply IH2; split; [exact E2|exact Hb].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_withlive_live_intbeg" *)
Theorem get_intervals_withlive_live_intbeg : forall lt n_in beg_in end_in live n_out beg_out end_out,
  (n_out, (beg_out, end_out)) = get_intervals_withlive lt n_in beg_in end_in live /\
  (forall r, r IN domain live -> r NOTIN domain beg_in) ->
  (forall r, r IN domain (get_live_backward lt live) -> r NOTIN domain beg_out).
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros n_in beg_in end_in live n_out beg_out end_out [H Hb] r Hr.
  - cbn [get_intervals_withlive get_live_backward] in *; inv_opt.
    rewrite IN_domain_numset_list_delete in Hr; destruct Hr as [Hr Hn].
    rewrite domain_numset_list_add_if_lt, IN_UNION; intros [?|?]; [contradiction|exact (Hb r Hr H)].
  - cbn [get_intervals_withlive get_live_backward] in *; inv_opt.
    rewrite IN_domain_numset_list_insert in Hr; rewrite IN_domain_numset_list_delete.
    intros [Hd Hn]; destruct Hr as [Hr|Hr]; [contradiction|exact (Hb r Hr Hd)].
  - gwl_destr H as n2 b2 e2 E2 n1 b1 e1 E1. cbn [get_live_backward] in Hr.
    rewrite domain_numset_list_insert, branch_domain in Hr.
    rewrite domain_difference; unfold_sets. intros [_ Hn]; apply Hn. rewrite domain_union. exact Hr.
  - gwl_destr H as n2 b2 e2 E2 n1 b1 e1 E1. cbn [get_live_backward] in Hr.
    eapply IH1; [split; [exact E1|]|exact Hr]. eapply IH2; split; [exact E2|exact Hb].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_withlive_beg_less_live" *)
Theorem get_intervals_withlive_beg_less_live : forall lt n_in beg_in end_in live_in n_out beg_out end_out,
  (n_out, (beg_out, end_out)) = get_intervals_withlive lt n_in beg_in end_in live_in /\
  (forall r v, lookup r beg_in = Some v -> (n_in <= v)%Z) /\
  (forall r, r IN domain live_in -> r NOTIN domain beg_in) ->
  check_number_property_strong (fun n (live : num_set) =>
    ⌜forall r, r IN domain live -> (match lookup r beg_out with None => n_out | Some x => x end <= n)%Z⌝)
    lt n_in live_in.
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros n_in beg_in end_in live_in n_out beg_out end_out (H & Hb & Hl).
  - cbn [get_intervals_withlive check_number_property_strong] in *; inv_opt.
    apply bool_decide_spec; intros r Hr. rewrite IN_domain_numset_list_delete in Hr; destruct Hr as [Hr Hn].
    rewrite lookup_numset_list_add_if_lt.
    assert (MEM r l = false) as -> by (destruct (MEM r l) eqn:M; [apply MEM_IN_set in M; contradiction|reflexivity]).
    pose proof (Hl r Hr) as Hn'; rewrite notdom_lookup in Hn'; rewrite Hn'; lia.
  - cbn [get_intervals_withlive check_number_property_strong] in *; inv_opt.
    apply bool_decide_spec; intros r Hr. rewrite IN_domain_numset_list_insert in Hr.
    rewrite lookup_numset_list_delete. destruct (MEM r l) eqn:M; [lia|].
    destruct Hr as [Hr|Hr]; [apply MEM_IN_set in Hr; congruence|].
    pose proof (Hl r Hr) as Hn'; rewrite notdom_lookup in Hn'; rewrite Hn'; lia.
  - gwl_destr H as n2 b2 e2 E2 n1 b1 e1 E1. cbn [check_number_property_strong get_live_backward size_of_live_tree].
    pose proof (get_intervals_withlive_nout _ _ _ _ _ _ _ _ E2) as N2.
    pose proof (get_intervals_withlive_nout _ _ _ _ _ _ _ _ E1) as N1.
    pose proof (size_of_live_tree_positive lt1); pose proof (size_of_live_tree_positive lt2).
    pose proof (IH2 _ _ _ _ _ _ _ (conj E2 (conj Hb Hl))) as C2.
    pose proof (get_intervals_withlive_intbeg_nout _ _ _ _ _ _ _ _ (conj E2 Hb)) as B2.
    assert (Bd : forall r v, lookup r (difference b2 live_in) = Some v -> (n2 <= v)%Z).
    { intros r v; rewrite lookup_difference; ddec; [apply B2|discriminate]. }
    assert (Ld : forall r, r IN domain live_in -> r NOTIN domain (difference b2 live_in)).
    { intros r Hr; rewrite domain_difference; unfold_sets; tauto. }
    pose proof (IH1 _ _ _ _ _ _ _ (conj E1 (conj Bd Ld))) as C1.
    destruct (get_intervals_withlive_intbeg_reduce _ _ _ _ _ _ _ _ (conj E1 Bd)) as [R1 _].
    set (U := union (get_live_backward lt1 live_in) (get_live_backward lt2 live_in)) in *.
    bsplit'.
    + subst n2. refine (check_number_property_strong_monotone _ _ _ _ _ (conj _ C1)).
      intros n' l' [Hn' Hp]; apply bool_decide_spec; apply bool_decide_spec in Hp; intros r Hr.
      specialize (Hp r Hr). rewrite lookup_difference; ddec; dlk; lia.
    + refine (check_number_property_strong_monotone _ _ _ _ _ (conj _ C2)).
      intros n' l' [Hn' Hp]; apply bool_decide_spec; apply bool_decide_spec in Hp; intros r Hr.
      specialize (Hp r Hr); specialize (R1 r). rewrite lookup_difference in *; ddec; dlk; lia.
    + apply bool_decide_spec; intros r Hr.
      rewrite domain_numset_list_insert, branch_domain in Hr.
      rewrite lookup_difference; ddec.
      * exfalso. assert (r IN domain U) by (unfold U; rewrite domain_union; exact Hr).
        apply notdom_lookup in e; contradiction.
      * lia.
  - gwl_destr H as n2 b2 e2 E2 n1 b1 e1 E1. cbn [check_number_property_strong get_live_backward size_of_live_tree].
    pose proof (get_intervals_withlive_nout _ _ _ _ _ _ _ _ E2) as N2.
    pose proof (get_intervals_withlive_nout _ _ _ _ _ _ _ _ E1) as N1.
    pose proof (size_of_live_tree_positive lt1); pose proof (size_of_live_tree_positive lt2).
    pose proof (IH2 _ _ _ _ _ _ _ (conj E2 (conj Hb Hl))) as C2.
    pose proof (get_intervals_withlive_intbeg_nout _ _ _ _ _ _ _ _ (conj E2 Hb)) as B2.
    pose proof (get_intervals_withlive_live_intbeg _ _ _ _ _ _ _ _ (conj E2 Hl)) as L2.
    pose proof (IH1 _ _ _ _ _ _ _ (conj E1 (conj B2 L2))) as C1.
    destruct (get_intervals_withlive_intbeg_reduce _ _ _ _ _ _ _ _ (conj E1 B2)) as [R1 _].
    bsplit'.
    + subst n2; exact C1.
    + refine (check_number_property_strong_monotone _ _ _ _ _ (conj _ C2)).
      intros n' l' [Hn' Hp]; apply bool_decide_spec; apply bool_decide_spec in Hp; intros r Hr.
      specialize (Hp r Hr); specialize (R1 r). dlk; lia.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_withlive_n_eq_get_intervals_n" *)
Theorem get_intervals_withlive_n_eq_get_intervals_n : forall lt n beg end_ beg' end_' n1 beg1 end1 n2 beg2 end2 live,
  (n1, (beg1, end1)) = get_intervals lt n beg end_ /\
  (n2, (beg2, end2)) = get_intervals_withlive lt n beg' end_' live ->
  n1 = n2.
Proof.
  intros lt n beg end_ beg' end_' n1 beg1 end1 n2 beg2 end2 live [H1 H2].
  rewrite (get_intervals_nout _ _ _ _ _ _ _ H1), (get_intervals_withlive_nout _ _ _ _ _ _ _ _ H2); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_withlive_end_eq_get_intervals_end" *)
Theorem get_intervals_withlive_end_eq_get_intervals_end : forall lt n beg beg' end_ n1 beg1 end1 n2 beg2 end2 live,
  (n1, (beg1, end1)) = get_intervals lt n beg end_ /\
  (n2, (beg2, end2)) = get_intervals_withlive lt n beg' end_ live ->
  end1 = end2.
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros n beg beg' end_ n1 beg1 end1 n2 beg2 end2 live [H1 H2].
  1,2: cbn [get_intervals get_intervals_withlive] in *; inv_opt; reflexivity.
  all: gi_destr H1 as m2 c2 d2 F2; gwl_destr H2 as k2 g2 h2 E2 k1 g1 h1 E1;
    pose proof (get_intervals_withlive_n_eq_get_intervals_n _ _ _ _ _ _ _ _ _ _ _ _ _ (conj F2 E2)) as Nn;
    pose proof (IH2 _ _ _ _ _ _ _ _ _ _ _ (conj F2 E2)) as Ee; subst;
    eapply IH1; split; [exact H1|exact E1].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_withlive_beg_eq_get_intervals_beg_when_some" *)
Theorem get_intervals_withlive_beg_eq_get_intervals_beg_when_some :
  forall lt n beg beg' end_ n1 beg1 end1 n2 beg2 end2 live,
  (n1, (beg1, end1)) = get_intervals lt n beg end_ /\
  (n2, (beg2, end2)) = get_intervals_withlive lt n beg' end_ live /\
  (forall r v, lookup r beg = Some v -> (n <= v)%Z) /\
  (forall r v, lookup r beg' = Some v -> (n <= v)%Z) /\
  (forall r v1 v2, lookup r beg = Some v1 /\ lookup r beg' = Some v2 -> v1 = v2) ->
  forall r v1 v2, lookup r beg1 = Some v1 /\ lookup r beg2 = Some v2 -> v1 = v2.
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros n beg beg' end_ n1 beg1 end1 n2 beg2 end2 live (H1 & H2 & B & B' & Eq) r v1 v2 [Hv1 Hv2].
  - cbn [get_intervals get_intervals_withlive] in *; inv_opt.
    rewrite lookup_numset_list_add_if_lt in *. ddec; dlk; ddec; inv_opt; spec_lk; lia.
  - cbn [get_intervals get_intervals_withlive] in *; inv_opt.
    rewrite lookup_numset_list_delete in Hv2; ddec; [discriminate|]. eapply Eq; eauto.
  - gi_destr H1 as m2 c2 d2 F2; gwl_destr H2 as k2 g2 h2 E2 k1 g1 h1 E1.
    pose proof (get_intervals_withlive_n_eq_get_intervals_n _ _ _ _ _ _ _ _ _ _ _ _ _ (conj F2 E2)) as Nn.
    pose proof (get_intervals_withlive_end_eq_get_intervals_end _ _ _ _ _ _ _ _ _ _ _ _ (conj F2 E2)) as Ee.
    subst k2 h2.
    pose proof (get_intervals_intbeg_nout _ _ _ _ _ _ _ (conj F2 B)) as Bc.
    pose proof (get_intervals_withlive_intbeg_nout _ _ _ _ _ _ _ _ (conj E2 B')) as Bg.
    assert (Eq2 := IH2 _ _ _ _ _ _ _ _ _ _ _ (conj F2 (conj E2 (conj B (conj B' Eq))))).
    assert (Bd : forall r v, lookup r (difference g2 live) = Some v -> (m2 <= v)%Z).
    { intros r' v; rewrite lookup_difference; ddec; [apply Bg|discriminate]. }
    assert (Eqd : forall r v1 v2, lookup r c2 = Some v1 /\ lookup r (difference g2 live) = Some v2 -> v1 = v2).
    { intros r' w1 w2 [A1 A2]; rewrite lookup_difference in A2; ddec; [|discriminate]. eauto. }
    rewrite lookup_difference in Hv2; ddec; [|discriminate].
    eapply (IH1 _ _ _ _ _ _ _ _ _ _ _ (conj H1 (conj E1 (conj Bc (conj Bd Eqd))))); eauto.
  - gi_destr H1 as m2 c2 d2 F2; gwl_destr H2 as k2 g2 h2 E2 k1 g1 h1 E1.
    pose proof (get_intervals_withlive_n_eq_get_intervals_n _ _ _ _ _ _ _ _ _ _ _ _ _ (conj F2 E2)) as Nn.
    pose proof (get_intervals_withlive_end_eq_get_intervals_end _ _ _ _ _ _ _ _ _ _ _ _ (conj F2 E2)) as Ee.
    subst k2 h2.
    pose proof (get_intervals_intbeg_nout _ _ _ _ _ _ _ (conj F2 B)) as Bc.
    pose proof (get_intervals_withlive_intbeg_nout _ _ _ _ _ _ _ _ (conj E2 B')) as Bg.
    assert (Eq2 := IH2 _ _ _ _ _ _ _ _ _ _ _ (conj F2 (conj E2 (conj B (conj B' Eq))))).
    eapply (IH1 _ _ _ _ _ _ _ _ _ _ _ (conj H1 (conj E1 (conj Bc (conj Bg Eq2))))); eauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_withlive_beg_subset_get_intervals_beg" *)
Theorem get_intervals_withlive_beg_subset_get_intervals_beg :
  forall lt n beg_in1 beg_in2 end_ n1 beg_out1 end1 n2 beg_out2 end2 live,
  (n1, (beg_out1, end1)) = get_intervals_withlive lt n beg_in1 end_ live /\
  (n2, (beg_out2, end2)) = get_intervals lt n beg_in2 end_ /\
  domain beg_in1 SUBSET domain beg_in2 ->
  domain beg_out1 SUBSET domain beg_out2.
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros n beg_in1 beg_in2 end_ n1 beg_out1 end1 n2 beg_out2 end2 live (H1 & H2 & S); intros x.
  - cbn [get_intervals get_intervals_withlive] in *; inv_opt.
    rewrite !domain_numset_list_add_if_lt, !IN_UNION; specialize (S x); tauto.
  - cbn [get_intervals get_intervals_withlive] in *; inv_opt.
    rewrite IN_domain_numset_list_delete; specialize (S x); tauto.
  - gi_destr H2 as m2 c2 d2 F2; gwl_destr H1 as k2 g2 h2 E2 k1 g1 h1 E1.
    pose proof (get_intervals_withlive_n_eq_get_intervals_n _ _ _ _ _ _ _ _ _ _ _ _ _ (conj F2 E2)) as Nn.
    pose proof (get_intervals_withlive_end_eq_get_intervals_end _ _ _ _ _ _ _ _ _ _ _ _ (conj F2 E2)) as Ee.
    subst k2 h2.
    pose proof (IH2 _ _ _ _ _ _ _ _ _ _ _ (conj E2 (conj F2 S))) as S2.
    assert (Sd : domain (difference g2 live) SUBSET domain c2).
    { intros y; rewrite domain_difference; unfold_sets; specialize (S2 y); unfold pred_set.IN in S2; tauto. }
    pose proof (IH1 _ _ _ _ _ _ _ _ _ _ _ (conj E1 (conj H2 Sd))) as S1.
    rewrite domain_difference; unfold_sets; specialize (S1 x); unfold pred_set.IN in S1; tauto.
  - gi_destr H2 as m2 c2 d2 F2; gwl_destr H1 as k2 g2 h2 E2 k1 g1 h1 E1.
    pose proof (get_intervals_withlive_n_eq_get_intervals_n _ _ _ _ _ _ _ _ _ _ _ _ _ (conj F2 E2)) as Nn.
    pose proof (get_intervals_withlive_end_eq_get_intervals_end _ _ _ _ _ _ _ _ _ _ _ _ (conj F2 E2)) as Ee.
    subst k2 h2.
    pose proof (IH2 _ _ _ _ _ _ _ _ _ _ _ (conj E2 (conj F2 S))) as S2.
    exact (IH1 _ _ _ _ _ _ _ _ _ _ _ (conj E1 (conj H2 S2)) x).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_beg_subset_registers" *)
Theorem get_intervals_beg_subset_registers : forall lt n_in beg_in end_in n_out beg_out end_out,
  (n_out, (beg_out, end_out)) = get_intervals lt n_in beg_in end_in ->
  domain beg_out SUBSET (domain beg_in UNION live_tree_registers lt).
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros n_in beg_in end_in n_out beg_out end_out H x; cbn [live_tree_registers].
  - cbn [get_intervals] in H; inv_opt. rewrite domain_numset_list_add_if_lt, !IN_UNION; tauto.
  - cbn [get_intervals] in H; inv_opt. rewrite !IN_UNION; tauto.
  - gi_destr H as n2 b2 e2 E2. intros Hx.
    pose proof (IH1 _ _ _ _ _ _ H x Hx) as A; rewrite IN_UNION in A; destruct A as [A|A].
    + pose proof (IH2 _ _ _ _ _ _ E2 x A) as B; rewrite !IN_UNION in *; tauto.
    + rewrite !IN_UNION; tauto.
  - gi_destr H as n2 b2 e2 E2. intros Hx.
    pose proof (IH1 _ _ _ _ _ _ H x Hx) as A; rewrite IN_UNION in A; destruct A as [A|A].
    + pose proof (IH2 _ _ _ _ _ _ E2 x A) as B; rewrite !IN_UNION in *; tauto.
    + rewrite !IN_UNION; tauto.
Qed.

(** "This theorem looks like lipschitz continuity: it says something like f(x+y) <= f(x)+y" *)
(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_withlive_beg_lipschitz" *)
Theorem get_intervals_withlive_beg_lipschitz :
  forall lt n1 beg1 end1 live n2 beg2 end2 (s : num_map Z) nout1 begout1 endout1 nout2 begout2 endout2,
  (nout1, (begout1, endout1)) = get_intervals_withlive lt n1 beg1 end1 live /\
  (nout2, (begout2, endout2)) = get_intervals_withlive lt n2 beg2 end2 live /\
  domain beg2 SUBSET domain beg1 UNION domain s ->
  domain begout2 SUBSET domain begout1 UNION domain s.
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros n1 beg1 end1 live n2 beg2 end2 s nout1 begout1 endout1 nout2 begout2 endout2 (H1 & H2 & S) x.
  - cbn [get_intervals_withlive] in *; inv_opt.
    rewrite !domain_numset_list_add_if_lt, !IN_UNION; specialize (S x); rewrite IN_UNION in S; tauto.
  - cbn [get_intervals_withlive] in *; inv_opt.
    rewrite !IN_UNION, !IN_domain_numset_list_delete; specialize (S x); rewrite IN_UNION in S; tauto.
  - gwl_destr H1 as k2 g2 h2 E2 k1 g1 h1 E1. gwl_destr H2 as k2' g2' h2' E2' k1' g1' h1' E1'.
    pose proof (IH2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ (conj E2 (conj E2' S))) as S2.
    assert (Sd : domain (difference g2' live) SUBSET domain (difference g2 live) UNION domain s).
    { intros y; rewrite !domain_difference, IN_UNION; specialize (S2 y);
        rewrite IN_UNION in S2; unfold_sets; tauto. }
    pose proof (IH1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ (conj E1 (conj E1' Sd)) x) as S1.
    rewrite !IN_UNION, !domain_difference in *; unfold_sets; tauto.
  - gwl_destr H1 as k2 g2 h2 E2 k1 g1 h1 E1. gwl_destr H2 as k2' g2' h2' E2' k1' g1' h1' E1'.
    pose proof (IH2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ (conj E2 (conj E2' S))) as S2.
    exact (IH1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ (conj E1 (conj E1' S2)) x).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_withlive_registers_subset_beg" *)
Theorem get_intervals_withlive_registers_subset_beg :
  forall lt n_in beg_in end_in n_out beg_out end_out live_in,
  domain end_in SUBSET domain beg_in UNION domain live_in /\
  (n_out, (beg_out, end_out)) = get_intervals_withlive lt n_in beg_in end_in live_in ->
  domain end_out SUBSET domain beg_out UNION domain (get_live_backward lt live_in).
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros n_in beg_in end_in n_out beg_out end_out live_in [S H]; intros x.
  - cbn [get_intervals_withlive get_live_backward] in *; inv_opt.
    rewrite domain_numset_list_add_if_lt, domain_numset_list_add_if_gt, !IN_UNION, IN_domain_numset_list_delete.
    specialize (S x); rewrite IN_UNION in S; tauto.
  - cbn [get_intervals_withlive get_live_backward] in *; inv_opt.
    rewrite domain_numset_list_add_if_gt, !IN_UNION, IN_domain_numset_list_delete, IN_domain_numset_list_insert.
    specialize (S x); rewrite IN_UNION in S; tauto.
  - gwl_destr H as n2 b2 e2 E2 n1 b1 e1 E1. cbn [get_live_backward].
    pose proof (IH2 _ _ _ _ _ _ _ (conj S E2)) as S2.
    set (lt_ := sptree.map (fun _ => 0%Z) (get_live_backward lt2 live_in)).
    assert (Dlt : domain lt_ = domain (get_live_backward lt2 live_in)) by apply domain_map.
    destruct (get_intervals_withlive lt1 n2 (union (difference b2 live_in) lt_) e2 live_in)
      as [n1' [b1' e1']] eqn:E1'. symmetry in E1'.
    destruct (get_intervals lt1 n2 LN e2) as [m [c d]] eqn:G; symmetry in G.
    pose proof (get_intervals_withlive_end_eq_get_intervals_end _ _ _ _ _ _ _ _ _ _ _ _ (conj G E1)) as X1.
    pose proof (get_intervals_withlive_end_eq_get_intervals_end _ _ _ _ _ _ _ _ _ _ _ _ (conj G E1')) as X2.
    subst e1' d.
    assert (S3 : domain e2 SUBSET domain (union (difference b2 live_in) lt_) UNION domain live_in).
    { intros y Hy; specialize (S2 y Hy). rewrite domain_union, domain_difference, Dlt.
      rewrite IN_UNION in S2 |- *; unfold_sets; tauto. }
    pose proof (IH1 _ _ _ _ _ _ _ (conj S3 E1')) as S1.
    assert (L : domain b1' SUBSET domain b1 UNION domain lt_).
    { eapply (get_intervals_withlive_beg_lipschitz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (conj E1 (conj E1' _))).
      Unshelve. intros y; rewrite domain_union, IN_UNION; unfold_sets; tauto. }
    intros Hx. specialize (S1 x Hx). rewrite IN_UNION in S1.
    rewrite IN_UNION, domain_difference, domain_numset_list_insert, branch_domain, domain_union.
    destruct S1 as [S1|S1].
    + specialize (L x S1); rewrite IN_UNION, Dlt in L; unfold_sets; tauto.
    + unfold_sets; tauto.
  - gwl_destr H as n2 b2 e2 E2 n1 b1 e1 E1. cbn [get_live_backward].
    pose proof (IH2 _ _ _ _ _ _ _ (conj S E2)) as S2.
    exact (IH1 _ _ _ _ _ _ _ (conj S2 E1) x).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_withlive_live_tree_registers_subset_endout" *)
Theorem get_intervals_withlive_live_tree_registers_subset_endout :
  forall lt n_in beg_in end_in live_in n_out beg_out end_out,
  (n_out, (beg_out, end_out)) = get_intervals_withlive lt n_in beg_in end_in live_in ->
  domain end_in UNION live_tree_registers lt SUBSET domain end_out.
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros n_in beg_in end_in live_in n_out beg_out end_out H; intros x; cbn [live_tree_registers].
  1,2: cbn [get_intervals_withlive] in *; inv_opt; rewrite domain_numset_list_add_if_gt, !IN_UNION; tauto.
  all: gwl_destr H as n2 b2 e2 E2 n1 b1 e1 E1;
    pose proof (IH2 _ _ _ _ _ _ _ E2) as S2; pose proof (IH1 _ _ _ _ _ _ _ E1) as S1;
    rewrite !IN_UNION; intros Hx; apply S1; rewrite IN_UNION;
    destruct Hx as [Hx|[Hx|Hx]]; [left; apply S2; rewrite IN_UNION; auto|right; exact Hx|];
    left; apply S2; rewrite IN_UNION; auto.
Qed.

Lemma IN_domain_LN' {A} x : x IN domain (@LN A) -> False.
Proof. intros []. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_domain_eq_live_tree_registers" *)
Theorem get_intervals_domain_eq_live_tree_registers : forall lt n beg end_,
  (n, (beg, end_)) = get_intervals (fix_domination lt) 0 LN LN ->
  domain beg = live_tree_registers (fix_domination lt) /\
  domain end_ = live_tree_registers (fix_domination lt).
Proof.
  intros lt n beg end_ H.
  pose proof (fix_domination_fixes_domination lt) as Fd.
  set (lt' := fix_domination lt) in *.
  destruct (get_intervals_withlive lt' 0 LN LN LN) as [n' [beg' end']] eqn:E; symmetry in E.
  pose proof (get_intervals_withlive_end_eq_get_intervals_end _ _ _ _ _ _ _ _ _ _ _ _ (conj H E)) as X; subst end'.
  pose proof (get_intervals_withlive_live_tree_registers_subset_endout _ _ _ _ _ _ _ _ E) as S1.
  assert (S0 : domain (@LN Z) SUBSET domain (@LN Z) UNION domain (@LN unit)) by (intros x []).
  pose proof (get_intervals_withlive_registers_subset_beg _ _ _ _ _ _ _ _ (conj S0 E)) as S2.
  assert (S0' : domain (@LN Z) SUBSET domain (@LN Z)) by (intros x []).
  pose proof (get_intervals_withlive_beg_subset_get_intervals_beg _ _ _ _ _ _ _ _ _ _ _ _ (conj E (conj H S0'))) as S3.
  pose proof (get_intervals_beg_subset_registers _ _ _ _ _ _ _ H) as S4.
  rewrite Fd in S2.
  assert (A : forall x, x IN domain end_ -> x IN live_tree_registers lt').
  { intros x Hx. specialize (S2 x Hx); rewrite IN_UNION in S2; destruct S2 as [S2|[]].
    specialize (S4 x (S3 x S2)); rewrite IN_UNION in S4; destruct S4 as [[]|S4]; exact S4. }
  split; apply set_ext; intros x; split.
  - intros Hx; specialize (S4 x Hx); rewrite IN_UNION in S4; destruct S4 as [[]|S4]; exact S4.
  - intros Hx. apply S3. specialize (S2 x (S1 x ltac:(rewrite IN_UNION; auto))).
    rewrite IN_UNION in S2; destruct S2 as [S2|[]]; exact S2.
  - apply A.
  - intros Hx; apply S1; rewrite IN_UNION; auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_withlive_domain_eq_live_tree_registers" *)
Theorem get_intervals_withlive_domain_eq_live_tree_registers : forall lt n beg end_,
  (n, (beg, end_)) = get_intervals_withlive (fix_domination lt) 0 LN LN LN ->
  domain beg = live_tree_registers (fix_domination lt) /\
  domain end_ = live_tree_registers (fix_domination lt).
Proof.
  intros lt n beg end_ E.
  pose proof (fix_domination_fixes_domination lt) as Fd.
  set (lt' := fix_domination lt) in *.
  destruct (get_intervals lt' 0 LN LN) as [n' [beg' end']] eqn:H; symmetry in H.
  pose proof (get_intervals_withlive_end_eq_get_intervals_end _ _ _ _ _ _ _ _ _ _ _ _ (conj H E)) as X; subst end'.
  pose proof (get_intervals_withlive_live_tree_registers_subset_endout _ _ _ _ _ _ _ _ E) as S1.
  assert (S0 : domain (@LN Z) SUBSET domain (@LN Z) UNION domain (@LN unit)) by (intros x []).
  pose proof (get_intervals_withlive_registers_subset_beg _ _ _ _ _ _ _ _ (conj S0 E)) as S2.
  assert (S0' : domain (@LN Z) SUBSET domain (@LN Z)) by (intros x []).
  pose proof (get_intervals_withlive_beg_subset_get_intervals_beg _ _ _ _ _ _ _ _ _ _ _ _ (conj E (conj H S0'))) as S3.
  pose proof (get_intervals_beg_subset_registers _ _ _ _ _ _ _ H) as S4.
  rewrite Fd in S2.
  assert (A : forall x, x IN domain beg -> x IN live_tree_registers lt').
  { intros x Hx. specialize (S4 x (S3 x Hx)); rewrite IN_UNION in S4; destruct S4 as [[]|S4]; exact S4. }
  split; apply set_ext; intros x; split.
  - apply A.
  - intros Hx. specialize (S2 x (S1 x ltac:(rewrite IN_UNION; auto))).
    rewrite IN_UNION in S2; destruct S2 as [S2|[]]; exact S2.
  - intros Hx. specialize (S2 x Hx); rewrite IN_UNION in S2; destruct S2 as [S2|[]]. apply A, S2.
  - intros Hx; apply S1; rewrite IN_UNION; auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_withlive_beg_eq_get_intervals_beg" *)
Theorem get_intervals_withlive_beg_eq_get_intervals_beg : forall lt n beg end_ n' beg' end_',
  (n, (beg, end_)) = get_intervals_withlive (fix_domination lt) 0 LN LN LN /\
  (n', (beg', end_')) = get_intervals (fix_domination lt) 0 LN LN ->
  forall (r : N), lookup r beg = lookup r beg'.
Proof.
  intros lt n beg end_ n' beg' end_' [E H] r.
  destruct (get_intervals_withlive_domain_eq_live_tree_registers _ _ _ _ E) as [D1 _].
  destruct (get_intervals_domain_eq_live_tree_registers _ _ _ _ H) as [D2 _].
  assert (B0 : forall r (v : Z), lookup r (@LN Z) = Some v -> (0 <= v)%Z) by (intros ? ? X; discriminate X).
  assert (Q0 : forall r (v1 v2 : Z), lookup r (@LN Z) = Some v1 /\ lookup r (@LN Z) = Some v2 -> v1 = v2)
    by (intros ? ? ? [X _]; discriminate X).
  pose proof (get_intervals_withlive_beg_eq_get_intervals_beg_when_some _ _ _ _ _ _ _ _ _ _ _ _
    (conj H (conj E (conj B0 (conj B0 Q0))))) as W.
  rewrite <- D2 in D1.
  assert (Hd : r IN domain beg <-> r IN domain beg') by (rewrite D1; reflexivity).
  rewrite !dom_lookup in Hd.
  destruct (lookup r beg) as [a|] eqn:A, (lookup r beg') as [b|] eqn:B.
  - f_equal; symmetry; exact (W r b a (conj B A)).
  - exfalso; destruct (proj1 Hd (ex_intro _ a eq_refl)) as [? X]; discriminate X.
  - exfalso; destruct (proj2 Hd (ex_intro _ b eq_refl)) as [? X]; discriminate X.
  - reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_end_increase" *)
Theorem get_intervals_end_increase : forall lt n_in beg_in end_in n_out beg_out end_out,
  (n_out, (beg_out, end_out)) = get_intervals lt n_in beg_in end_in ->
  domain end_in SUBSET domain end_out.
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros n_in beg_in end_in n_out beg_out end_out H x Hx.
  1,2: cbn [get_intervals] in *; inv_opt; rewrite domain_numset_list_add_if_gt, IN_UNION; auto.
  all: gi_destr H as n2 b2 e2 E2; eapply IH1; [exact H|]; eapply IH2; [exact E2|exact Hx].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_number_property_subset_endout" *)
Theorem check_number_property_subset_endout : forall lt n_in beg_in end_in live_in n_out beg_out end_out,
  (n_out, (beg_out, end_out)) = get_intervals lt n_in beg_in end_in /\
  domain live_in SUBSET domain end_in ->
  check_number_property_strong (fun n (live : num_set) => ⌜domain live SUBSET domain end_out⌝) lt n_in live_in.
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros n_in beg_in end_in live_in n_out beg_out end_out [H S];
    cbn [check_number_property_strong].
  - cbn [get_intervals] in H; inv_opt. apply bool_decide_spec; intros x.
    rewrite IN_domain_numset_list_delete, domain_numset_list_add_if_gt, IN_UNION.
    specialize (S x); tauto.
  - cbn [get_intervals] in H; inv_opt. apply bool_decide_spec; intros x.
    rewrite IN_domain_numset_list_insert, domain_numset_list_add_if_gt, IN_UNION.
    specialize (S x); tauto.
  - gi_destr H as n2 b2 e2 E2.
    pose proof (get_intervals_nout _ _ _ _ _ _ _ E2) as N2.
    pose proof (get_intervals_end_increase _ _ _ _ _ _ _ E2) as I2.
    pose proof (get_intervals_end_increase _ _ _ _ _ _ _ H) as I1.
    pose proof (IH2 _ _ _ _ _ _ _ (conj E2 S)) as C2.
    assert (C2' : check_number_property_strong (fun n (live : num_set) => ⌜domain live SUBSET domain end_out⌝) lt2 n_in live_in).
    { refine (check_number_property_strong_monotone_weak _ _ _ _ _ (conj _ C2)).
      intros n' l' Hp; apply bool_decide_spec; apply bool_decide_spec in Hp; intros x Hx; apply I1, Hp, Hx. }
    assert (S' : domain live_in SUBSET domain e2) by (intros x Hx; apply I2, S, Hx).
    pose proof (IH1 _ _ _ _ _ _ _ (conj H S')) as C1. subst n2.
    bsplit'; [exact C1|exact C2'|].
    apply bool_decide_spec. cbn [get_live_backward]. intros x.
    rewrite domain_numset_list_insert, branch_domain, IN_UNION.
    pose proof (check_number_property_strong_end _ _ _ _ C1) as F1.
    pose proof (check_number_property_strong_end _ _ _ _ C2') as F2.
    apply bool_decide_spec in F1, F2. intros [Hx|Hx]; [apply F1, Hx|apply F2, Hx].
  - gi_destr H as n2 b2 e2 E2.
    pose proof (get_intervals_nout _ _ _ _ _ _ _ E2) as N2.
    pose proof (get_intervals_end_increase _ _ _ _ _ _ _ H) as I1.
    pose proof (IH2 _ _ _ _ _ _ _ (conj E2 S)) as C2.
    pose proof (check_number_property_strong_end _ _ _ _ C2) as F2; apply bool_decide_spec in F2.
    pose proof (IH1 _ _ _ _ _ _ _ (conj H F2)) as C1. subst n2.
    bsplit'; [exact C1|].
    refine (check_number_property_strong_monotone_weak _ _ _ _ _ (conj _ C2)).
    intros n' l' Hp; apply bool_decide_spec; apply bool_decide_spec in Hp; intros x Hx; apply I1, Hp, Hx.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_beg_less_live" *)
Theorem get_intervals_beg_less_live : forall lt (live_in : num_set) n_out beg_out end_out,
  (n_out, (beg_out, end_out)) = get_intervals (fix_domination lt) 0 LN LN ->
  check_number_property_strong (fun n (live : num_set) =>
    ⌜forall r, r IN domain live -> (match lookup r beg_out with None => n_out | Some x => x end <= n)%Z⌝)
    (fix_domination lt) 0 LN.
Proof.
  intros lt live_in n_out beg_out end_out H.
  destruct (get_intervals_withlive (fix_domination lt) 0 LN LN LN) as [n' [beg' end']] eqn:E; symmetry in E.
  assert (B0 : forall r (v : Z), lookup r (@LN Z) = Some v -> (0 <= v)%Z) by (intros ? ? X; discriminate X).
  assert (L0 : forall r, r IN domain (@LN unit) -> r NOTIN domain (@LN Z)) by (intros ? []).
  pose proof (get_intervals_withlive_beg_less_live _ _ _ _ _ _ _ _ (conj E (conj B0 L0))) as C.
  pose proof (get_intervals_withlive_beg_eq_get_intervals_beg _ _ _ _ _ _ _ (conj E H)) as Eq.
  pose proof (get_intervals_withlive_n_eq_get_intervals_n _ _ _ _ _ _ _ _ _ _ _ _ _ (conj H E)) as Nn; subst n'.
  refine (check_number_property_strong_monotone_weak _ _ _ _ _ (conj _ C)).
  intros n0 l0 Hp; apply bool_decide_spec; apply bool_decide_spec in Hp; intros r Hr.
  rewrite <- Eq; apply Hp, Hr.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_intbeg_reduce" *)
Theorem get_intervals_intbeg_reduce : forall lt n_in beg_in end_in n_out beg_out end_out (live : num_set),
  (n_out, (beg_out, end_out)) = get_intervals lt n_in beg_in end_in /\
  (forall r v, lookup r beg_in = Some v -> (n_in <= v)%Z) ->
  (forall r, (match lookup r beg_out with None => n_out | Some x => x end <=
              match lookup r beg_in with None => n_in | Some x => x end)%Z) /\
  (forall r v, lookup r beg_out = Some v -> (n_out <= v)%Z).
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros n_in beg_in end_in n_out beg_out end_out live [H Hb].
  - cbn [get_intervals] in H; inv_opt. split.
    + intros r; rewrite lookup_numset_list_add_if_lt; ddec; dlk; ddec; spec_lk; lia.
    + intros r v; rewrite lookup_numset_list_add_if_lt; ddec; dlk; ddec; intros E; inv_opt; spec_lk; lia.
  - cbn [get_intervals] in H; inv_opt. split.
    + intros r; dlk; lia.
    + intros r v E; spec_lk; lia.
  - gi_destr H as n2 b2 e2 E2.
    pose proof (get_intervals_nout _ _ _ _ _ _ _ E2) as N2.
    pose proof (get_intervals_nout _ _ _ _ _ _ _ H) as N1.
    pose proof (size_of_live_tree_positive lt1); pose proof (size_of_live_tree_positive lt2).
    destruct (IH2 _ _ _ _ _ _ live (conj E2 Hb)) as [R2 B2].
    destruct (IH1 _ _ _ _ _ _ live (conj H B2)) as [R1 B1].
    split; [|exact B1]. intros r; specialize (R1 r); specialize (R2 r); dlk; lia.
  - gi_destr H as n2 b2 e2 E2.
    pose proof (get_intervals_nout _ _ _ _ _ _ _ E2) as N2.
    pose proof (get_intervals_nout _ _ _ _ _ _ _ H) as N1.
    pose proof (size_of_live_tree_positive lt1); pose proof (size_of_live_tree_positive lt2).
    destruct (IH2 _ _ _ _ _ _ live (conj E2 Hb)) as [R2 B2].
    destruct (IH1 _ _ _ _ _ _ live (conj H B2)) as [R1 B1].
    split; [|exact B1]. intros r; specialize (R1 r); specialize (R2 r); dlk; lia.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_startlive_prop_monotone" *)
Theorem check_startlive_prop_monotone : forall lt beg ndef end_ beg' ndef' end_' n_in,
  (forall r, (match lookup r beg' with None => ndef' | Some x => x end <=
              match lookup r beg with None => ndef | Some x => x end)%Z) /\
  (forall r v, lookup r end_ = Some v -> (exists v', lookup r end_' = Some v' /\ (v <= v')%Z)) /\
  check_startlive_prop lt n_in beg end_ ndef ->
  check_startlive_prop lt n_in beg' end_' ndef'.
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros beg ndef end_ beg' ndef' end_' n_in (R & A & C); cbn [check_startlive_prop] in *.
  - intros r Hr. destruct (C r Hr) as [C1 (v & Hv & Le)].
    destruct (A r v Hv) as (v' & Hv' & Le'). specialize (R r).
    split; [lia|exists v'; split; [exact Hv'|lia]].
  - exact I.
  - destruct C as [C1 C2]; split; [eapply IH1|eapply IH2]; eauto.
  - destruct C as [C1 C2]; split; [eapply IH1|eapply IH2]; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_startlive_prop_augment_ndef" *)
Theorem check_startlive_prop_augment_ndef : forall lt n_in beg_out end_out ndef ndef',
  check_startlive_prop lt n_in beg_out end_out ndef /\
  (ndef <= ndef')%Z /\
  (ndef' <= n_in - size_of_live_tree lt)%Z ->
  check_startlive_prop lt n_in beg_out end_out ndef'.
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros n_in beg_out end_out ndef ndef' (C & L1 & L2); cbn [check_startlive_prop size_of_live_tree] in *.
  - intros r Hr. destruct (C r Hr) as [C1 C2]. split; [|exact C2]. dlk; lia.
  - exact I.
  - pose proof (size_of_live_tree_positive lt1); pose proof (size_of_live_tree_positive lt2).
    destruct C as [C1 C2]; split; [eapply IH1|eapply IH2]; (split; [eassumption|split; lia]).
  - pose proof (size_of_live_tree_positive lt1); pose proof (size_of_live_tree_positive lt2).
    destruct C as [C1 C2]; split; [eapply IH1|eapply IH2]; (split; [eassumption|split; lia]).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_check_startlive_prop" *)
Theorem get_intervals_check_startlive_prop : forall lt n_in beg_in end_in n_out beg_out end_out,
  (n_out, (beg_out, end_out)) = get_intervals lt n_in beg_in end_in /\
  (forall r v, lookup r beg_in = Some v -> (n_in <= v)%Z) ->
  check_startlive_prop lt n_in beg_out end_out n_out.
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros n_in beg_in end_in n_out beg_out end_out [H Hb]; cbn [check_startlive_prop].
  - cbn [get_intervals] in H; inv_opt. intros r Hr.
    rewrite lookup_numset_list_add_if_lt, lookup_numset_list_add_if_gt. unfold is_true in Hr; rewrite !Hr.
    split; [dlk; ddec; spec_lk; lia|dlk; ddec; eexists; split; try reflexivity; lia].
  - exact I.
  - gi_destr H as n2 b2 e2 E2.
    pose proof (get_intervals_nout _ _ _ _ _ _ _ E2) as N2.
    pose proof (IH2 _ _ _ _ _ _ (conj E2 Hb)) as C2.
    destruct (get_intervals_intbeg_reduce _ _ _ _ _ _ _ LN (conj E2 Hb)) as [_ B2].
    pose proof (IH1 _ _ _ _ _ _ (conj H B2)) as C1.
    pose proof (get_intervals_intend_augment _ _ _ _ _ _ _ H) as A1.
    destruct (get_intervals_intbeg_reduce _ _ _ _ _ _ _ LN (conj H B2)) as [R1 _].
    subst n2. split; [exact C1|]. eapply check_startlive_prop_monotone; eauto.
  - gi_destr H as n2 b2 e2 E2.
    pose proof (get_intervals_nout _ _ _ _ _ _ _ E2) as N2.
    pose proof (IH2 _ _ _ _ _ _ (conj E2 Hb)) as C2.
    destruct (get_intervals_intbeg_reduce _ _ _ _ _ _ _ LN (conj E2 Hb)) as [_ B2].
    pose proof (IH1 _ _ _ _ _ _ (conj H B2)) as C1.
    pose proof (get_intervals_intend_augment _ _ _ _ _ _ _ H) as A1.
    destruct (get_intervals_intbeg_reduce _ _ _ _ _ _ _ LN (conj H B2)) as [R1 _].
    subst n2. split; [exact C1|]. eapply check_startlive_prop_monotone; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "exists_point_inside_interval_interval_intersect" *)
Theorem exists_point_inside_interval_interval_intersect : forall l1 r1 l2 r2 v,
  point_inside_interval (l1, r1) v /\ point_inside_interval (l2, r2) v ->
  interval_intersect (l1, r1) (l2, r2).
Proof.
  unfold point_inside_interval, interval_intersect, is_true; intros l1 r1 l2 r2 v [H1 H2].
  rewrite !andb_true_iff, !Z.leb_le in *; lia.
Qed.

Lemma pt_mk (x : N) (beg end_ : num_map Z) vb ve m :
  lookup x beg = Some vb -> lookup x end_ = Some ve -> (vb <= m)%Z -> (m <= ve)%Z ->
  point_inside_interval (THE (lookup x beg), THE (lookup x end_)) m.
Proof.
  intros -> -> H1 H2; cbn [THE]; unfold point_inside_interval, is_true.
  rewrite andb_true_iff, !Z.leb_le; lia.
Qed.

Lemma points_INJ f (beg end_ : num_map Z) (s : N -> Prop) m :
  check_intervals f beg end_ ->
  (forall x, x IN s -> x IN domain beg /\ point_inside_interval (THE (lookup x beg), THE (lookup x end_)) m) ->
  INJ f s UNIV.
Proof.
  intros Ci Hp; rewrite INJ_UNIV; intros x y Hx Hy E.
  destruct (Hp x Hx) as [Dx Px], (Hp y Hy) as [Dy Py].
  apply Ci; split; [exact Dx|split; [exact Dy|split; [|exact E]]].
  eapply exists_point_inside_interval_interval_intersect; split; [exact Px|exact Py].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_intervals_check_live_tree_lemma" *)
Theorem check_intervals_check_live_tree_lemma : forall lt n_in beg_out end_out f live flive n_out,
  check_startlive_prop lt n_in beg_out end_out (n_in - size_of_live_tree lt)%Z /\
  check_number_property_strong (fun n (live' : num_set) =>
    ⌜forall r, r IN domain live' -> (match lookup r beg_out with None => n_out | Some x => x end <= n)%Z⌝)
    lt n_in live /\
  check_number_property (fun n (live' : num_set) =>
    ⌜forall r, r IN domain live' -> exists v, lookup r end_out = Some v /\ (n + 1 <= v)%Z⌝) lt n_in live /\
  check_number_property_strong (fun n (live' : num_set) => ⌜domain live' SUBSET domain end_out⌝) lt n_in live /\
  domain beg_out = domain end_out /\
  live_tree_registers lt SUBSET domain end_out /\
  check_intervals f beg_out end_out /\
  domain flive = IMAGE f (domain live) /\
  INJ f (domain live) UNIV ->
  exists liveout fliveout, check_live_tree f lt live flive = Some (liveout, fliveout).
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2];
    intros n_in beg_out end_out f live flive n_out (C & Pb & Pe & Ps & Dbe & Rg & Ci & Hd & Hinj);
    cbn [check_startlive_prop check_number_property_strong check_number_property live_tree_registers
         size_of_live_tree check_live_tree] in *.
  - apply bool_decide_spec in Pb, Pe, Ps.
    assert (Hp : forall x, x IN (set l UNION domain live) ->
      x IN domain beg_out /\ point_inside_interval (THE (lookup x beg_out), THE (lookup x end_out)) n_in).
    { intros x Hx. rewrite IN_UNION in Hx.
      destruct (classic (x IN set l)) as [Hl|Hl].
      - assert (Db : x IN domain beg_out) by (rewrite Dbe; apply Rg, Hl).
        split; [exact Db|]. pose proof Db as Db'; apply dom_lookup in Db' as [vb Hvb].
        destruct (C x (proj2 (MEM_IN_set x l) Hl)) as [C1 (ve & Hve & Le)]. rewrite Hvb in C1.
        eapply pt_mk; eauto; lia.
      - destruct Hx as [Hx|Hx]; [contradiction|].
        assert (Hd' : x IN domain (numset_list_delete l live)) by (rewrite IN_domain_numset_list_delete; auto).
        assert (Db : x IN domain beg_out) by (rewrite Dbe; apply Ps, Hd').
        split; [exact Db|]. pose proof Db as Db'; apply dom_lookup in Db' as [vb Hvb].
        specialize (Pb x Hd'); rewrite Hvb in Pb. destruct (Pe x Hd') as (ve & Hve & Le).
        eapply pt_mk; eauto; lia. }
    destruct (check_partial_col_success l live flive f) as (a & b & E & _).
    { split; [exact Hd|]. eapply points_INJ; eauto. }
    rewrite E; eauto.
  - apply bool_decide_spec in Pb, Pe, Ps.
    assert (Hp : forall x, x IN (set l UNION domain live) ->
      x IN domain beg_out /\ point_inside_interval (THE (lookup x beg_out), THE (lookup x end_out)) n_in).
    { intros x Hx. assert (Hd' : x IN domain (numset_list_insert l live)) by (rewrite domain_numset_list_insert; exact Hx).
      assert (Db : x IN domain beg_out) by (rewrite Dbe; apply Ps, Hd').
      split; [exact Db|]. pose proof Db as Db'; apply dom_lookup in Db' as [vb Hvb].
      specialize (Pb x Hd'); rewrite Hvb in Pb. destruct (Pe x Hd') as (ve & Hve & Le).
      eapply pt_mk; eauto; lia. }
    destruct (check_partial_col_success l live flive f) as (a & b & E & _).
    { split; [exact Hd|]. eapply points_INJ; eauto. }
    rewrite E; eauto.
  - unfold is_true in Pb, Pe, Ps.
    apply andb_prop in Pb as [Pb Pb1]; apply andb_prop in Pb as [Pb Pb0].
    apply andb_prop in Ps as [Ps Ps1]; apply andb_prop in Ps as [Ps Ps0].
    apply andb_prop in Pe as [Pe Pe0].
    destruct C as [C1 C2].
    pose proof (size_of_live_tree_positive lt1); pose proof (size_of_live_tree_positive lt2).
    assert (C2' : check_startlive_prop lt2 n_in beg_out end_out (n_in - size_of_live_tree lt2)%Z).
    { eapply check_startlive_prop_augment_ndef; split; [exact C2|split; lia]. }
    assert (C1' : check_startlive_prop lt1 (n_in - size_of_live_tree lt2)%Z beg_out end_out
                    (n_in - size_of_live_tree lt2 - size_of_live_tree lt1)%Z).
    { replace (n_in - size_of_live_tree lt2 - size_of_live_tree lt1)%Z
        with (n_in - (size_of_live_tree lt1 + size_of_live_tree lt2))%Z by lia. exact C1. }
    assert (Rg1 : live_tree_registers lt1 SUBSET domain end_out) by (intros x Hx; apply Rg; rewrite IN_UNION; auto).
    assert (Rg2 : live_tree_registers lt2 SUBSET domain end_out) by (intros x Hx; apply Rg; rewrite IN_UNION; auto).
    destruct (IH2 _ _ _ f live flive n_out (conj C2' (conj Pb0 (conj Pe0 (conj Ps0 (conj Dbe (conj Rg2 (conj Ci (conj Hd Hinj))))))))) as (l2 & fl2 & E2).
    destruct (IH1 _ _ _ f live flive n_out (conj C1' (conj Pb (conj Pe (conj Ps (conj Dbe (conj Rg1 (conj Ci (conj Hd Hinj))))))))) as (l1 & fl1 & E1).
    rewrite E1, E2.
    pose proof (check_live_tree_eq_get_live_backward _ _ _ _ _ _ E1) as G1.
    pose proof (check_live_tree_eq_get_live_backward _ _ _ _ _ _ E2) as G2.
    destruct (check_live_tree_success _ _ _ _ _ _ (conj Hd (conj Hinj E1))) as [Hd1 _].
    apply bool_decide_spec in Pb1, Ps1.
    cbn [get_live_backward] in Pb1, Ps1.
    assert (Hp : forall x, x IN (domain l1 UNION domain l2) ->
      x IN domain beg_out /\ point_inside_interval (THE (lookup x beg_out), THE (lookup x end_out))
        (n_in - (size_of_live_tree lt1 + size_of_live_tree lt2))%Z).
    { intros x Hx.
      assert (Hd' : x IN domain (numset_list_insert (MAP FST (toAList (difference (get_live_backward lt2 live)
                      (get_live_backward lt1 live)))) (get_live_backward lt1 live)))
        by (rewrite domain_numset_list_insert, branch_domain; subst; exact Hx).
      assert (Db : x IN domain beg_out) by (rewrite Dbe; apply Ps1, Hd').
      split; [exact Db|]. pose proof Db as Db'; apply dom_lookup in Db' as [vb Hvb].
      specialize (Pb1 x Hd'); rewrite Hvb in Pb1.
      rewrite IN_UNION in Hx; destruct Hx as [Hx|Hx]; subst.
      - destruct (check_number_property_intend _ _ _ _ Pe x Hx) as (ve & Hve & Le).
        eapply pt_mk; eauto; lia.
      - destruct (check_number_property_intend _ _ _ _ Pe0 x Hx) as (ve & Hve & Le).
        eapply pt_mk; eauto; lia. }
    destruct (check_partial_col_success (MAP FST (toAList (difference l2 l1))) l1 fl1 f) as (a & b & E & _).
    { split; [exact Hd1|]. rewrite branch_domain. eapply points_INJ; eauto. }
    rewrite E; eauto.
  - unfold is_true in Pb, Pe, Ps.
    apply andb_prop in Pb as [Pb Pb0]; apply andb_prop in Ps as [Ps Ps0]; apply andb_prop in Pe as [Pe Pe0].
    destruct C as [C1 C2].
    pose proof (size_of_live_tree_positive lt1); pose proof (size_of_live_tree_positive lt2).
    assert (C2' : check_startlive_prop lt2 n_in beg_out end_out (n_in - size_of_live_tree lt2)%Z).
    { eapply check_startlive_prop_augment_ndef; split; [exact C2|split; lia]. }
    assert (C1' : check_startlive_prop lt1 (n_in - size_of_live_tree lt2)%Z beg_out end_out
                    (n_in - size_of_live_tree lt2 - size_of_live_tree lt1)%Z).
    { replace (n_in - size_of_live_tree lt2 - size_of_live_tree lt1)%Z
        with (n_in - (size_of_live_tree lt1 + size_of_live_tree lt2))%Z by lia. exact C1. }
    assert (Rg1 : live_tree_registers lt1 SUBSET domain end_out) by (intros x Hx; apply Rg; rewrite IN_UNION; auto).
    assert (Rg2 : live_tree_registers lt2 SUBSET domain end_out) by (intros x Hx; apply Rg; rewrite IN_UNION; auto).
    destruct (IH2 _ _ _ f live flive n_out (conj C2' (conj Pb0 (conj Pe0 (conj Ps0 (conj Dbe (conj Rg2 (conj Ci (conj Hd Hinj))))))))) as (l2 & fl2 & E2).
    rewrite E2.
    pose proof (check_live_tree_eq_get_live_backward _ _ _ _ _ _ E2) as G2.
    destruct (check_live_tree_success _ _ _ _ _ _ (conj Hd (conj Hinj E2))) as [Hd2 Hi2].
    subst l2.
    exact (IH1 _ _ _ f _ fl2 n_out (conj C1' (conj Pb (conj Pe (conj Ps (conj Dbe (conj Rg1 (conj Ci (conj Hd2 Hi2))))))))).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_intervals_check_live_tree" *)
Theorem check_intervals_check_live_tree : forall lt n_out beg_out end_out f,
  (n_out, (beg_out, end_out)) = get_intervals (fix_domination lt) 0 LN LN /\
  check_intervals f beg_out end_out ->
  exists liveout fliveout, check_live_tree f (fix_domination lt) LN LN = Some (liveout, fliveout).
Proof.
  intros lt n_out beg_out end_out f [H Ci].
  assert (B0 : forall r (v : Z), lookup r (@LN Z) = Some v -> (0 <= v)%Z) by (intros ? ? X; discriminate X).
  pose proof (get_intervals_check_startlive_prop _ _ _ _ _ _ _ (conj H B0)) as C.
  rewrite (get_intervals_nout _ _ _ _ _ _ _ H) in C.
  pose proof (get_intervals_beg_less_live _ LN _ _ _ H) as Pb.
  pose proof (get_intervals_live_less_end _ _ _ _ LN _ _ _ (conj H (fun r (X : r IN domain (@LN unit)) => False_ind _ X))) as Pe.
  pose proof (check_number_property_subset_endout _ _ _ _ LN _ _ _ (conj H (fun r (X : r IN domain (@LN unit)) => False_ind _ X))) as Ps.
  destruct (get_intervals_domain_eq_live_tree_registers _ _ _ _ H) as [D1 D2].
  eapply (check_intervals_check_live_tree_lemma _ 0%Z beg_out end_out f LN LN n_out).
  repeat split; try assumption.
  - rewrite D1, D2; reflexivity.
  - rewrite D2; intros x Hx; exact Hx.
  - apply set_ext; intros x; unfold_sets; cbn [domain]; split; [intros []|intros (? & _ & [])].
  - intros x y [[] _].
Qed.

Lemma ap_union {A} (a b : num_map A) x : domain (union a b) x <-> domain a x \/ domain b x.
Proof. rewrite domain_union; reflexivity. Qed.
Lemma ap_insert l (t : num_set) x : domain (numset_list_insert l t) x <-> set l x \/ domain t x.
Proof. rewrite domain_numset_list_insert; reflexivity. Qed.
Lemma ap_delete {A} l (t : num_map A) x : domain (numset_list_delete l t) x <-> domain t x /\ ~ set l x.
Proof. rewrite domain_numset_list_delete; reflexivity. Qed.
Lemma ap_difference {A B} (a : num_map A) (b : num_map B) x : domain (difference a b) x <-> domain a x /\ ~ domain b x.
Proof. rewrite domain_difference; reflexivity. Qed.
Lemma ap_keys {A} (t : num_map A) x : set (MAP FST (toAList t)) x <-> domain t x.
Proof. rewrite set_MAP_FST_toAList_eq_domain; reflexivity. Qed.

Ltac dom_ext :=
  apply set_ext; intros ?; unfold pred_set.IN in *;
  repeat first [rewrite ap_union | rewrite ap_insert | rewrite ap_delete | rewrite ap_difference | rewrite ap_keys].

Tactic Notation "aux_destr" hyp(H) "as" ident(n2) ident(b2) ident(e2) ident(l2) ident(E2)
    ident(n1) ident(b1) ident(e1) ident(l1) ident(E1) :=
  cbn [get_intervals_ct_aux] in H;
  lazymatch type of H with
  | context [get_intervals_ct_aux ?c2 ?n ?b ?e ?lv] =>
      destruct (get_intervals_ct_aux c2 n b e lv) as [n2 [b2 [e2 l2]]] eqn:E2;
      lazymatch type of H with
      | context [get_intervals_ct_aux ?c1 ?n' ?b' ?e' ?lv'] =>
          destruct (get_intervals_ct_aux c1 n' b' e' lv') as [n1 [b1 [e1 l1]]] eqn:E1;
          symmetry in E1, E2
      end
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_ct_aux_live" *)
Theorem get_intervals_ct_aux_live :
  forall ct n_in beg_in end_in live_in live_in' n_out beg_out end_out live_out,
  domain live_in = domain live_in' /\
  (n_out, (beg_out, (end_out, live_out))) = get_intervals_ct_aux ct n_in beg_in end_in live_in ->
  domain live_out = domain (get_live_backward (get_live_tree ct) live_in').
Proof.
  induction ct as [w r|s|o c1 IH1 c2 IH2|c1 IH1 c2 IH2];
    intros n_in beg_in end_in live_in live_in' n_out beg_out end_out live_out [D H];
    cbn [get_live_tree get_live_backward].
  - cbn [get_intervals_ct_aux] in H; inv_opt.
    rewrite !domain_numset_list_insert, !domain_numset_list_delete, D; reflexivity.
  - cbn [get_intervals_ct_aux] in H; inv_opt.
    rewrite domain_union, domain_numset_list_insert, set_MAP_FST_toAList_eq_domain, D; reflexivity.
  - aux_destr H as n2 b2 e2 l2 E2 n1 b1 e1 l1 E1.
    pose proof (IH2 _ _ _ _ _ _ _ _ _ (conj D E2)) as D2.
    pose proof (IH1 _ _ _ _ _ _ _ _ _ (conj D E1)) as D1.
    destruct o as [cut|]; inv_opt; cbn [get_live_backward]; dom_ext; rewrite ?D1, ?D2;
      destruct (classic (domain (get_live_backward (get_live_tree c1) live_in') x)); tauto.
  - aux_destr H as n2 b2 e2 l2 E2 n1 b1 e1 l1 E1. inv_opt.
    pose proof (IH2 _ _ _ _ _ _ _ _ _ (conj D E2)) as D2.
    exact (IH1 _ _ _ _ _ _ _ _ _ (conj D2 E1)).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_ct_aux_int" *)
Theorem get_intervals_ct_aux_int :
  forall ct n_in beg_in end_in live_in n_out beg_out end_out live_out,
  (n_out, (beg_out, (end_out, live_out))) = get_intervals_ct_aux ct n_in beg_in end_in live_in ->
  (n_out, (beg_out, end_out)) = get_intervals (get_live_tree ct) n_in beg_in end_in.
Proof.
  induction ct as [w r|s|o c1 IH1 c2 IH2|c1 IH1 c2 IH2];
    intros n_in beg_in end_in live_in n_out beg_out end_out live_out H;
    cbn [get_live_tree get_intervals].
  - cbn [get_intervals_ct_aux] in H; inv_opt. f_equal; lia.
  - cbn [get_intervals_ct_aux] in H; inv_opt. reflexivity.
  - aux_destr H as n2 b2 e2 l2 E2 n1 b1 e1 l1 E1.
    destruct o as [cut|]; cbn [get_intervals];
      rewrite <- (IH2 _ _ _ _ _ _ _ _ E2), <- (IH1 _ _ _ _ _ _ _ _ E1); inv_opt; reflexivity.
  - aux_destr H as n2 b2 e2 l2 E2 n1 b1 e1 l1 E1. inv_opt.
    rewrite <- (IH2 _ _ _ _ _ _ _ _ E2). exact (IH1 _ _ _ _ _ _ _ _ E1).
Qed.

Lemma MEM_keys_eq {A B} (s : num_map A) (t : num_map B) r :
  domain s = domain t -> MEM r (MAP FST (toAList s)) = MEM r (MAP FST (toAList t)).
Proof.
  intros D. destruct (MEM r (MAP FST (toAList s))) eqn:E1, (MEM r (MAP FST (toAList t))) eqn:E2; auto.
  - apply MEM_keys in E1; rewrite D in E1; apply MEM_keys in E1; congruence.
  - apply MEM_keys in E2; rewrite <- D in E2; apply MEM_keys in E2; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_ct_eq" *)
Theorem get_intervals_ct_eq : forall ct int_beg1 int_beg2 int_end1 int_end2 n1 n2,
  (n1, (int_beg1, int_end1)) = get_intervals_ct ct /\
  (n2, (int_beg2, int_end2)) = get_intervals (fix_domination (get_live_tree ct)) 0 LN LN ->
  (forall r, lookup r int_beg1 = lookup r int_beg2) /\
  (forall r, lookup r int_end1 = lookup r int_end2).
Proof.
  intros ct int_beg1 int_beg2 int_end1 int_end2 n1 n2 [H1 H2].
  unfold get_intervals_ct in H1.
  destruct (get_intervals_ct_aux ct 0 LN LN LN) as [n [b [e live]]] eqn:E; symmetry in E.
  pose proof (get_intervals_ct_aux_int _ _ _ _ _ _ _ _ _ E) as I.
  pose proof (get_intervals_ct_aux_live _ _ _ _ _ LN _ _ _ _ (conj eq_refl E)) as D.
  inv_opt. unfold fix_domination in H2.
  destruct (bool_decide (get_live_backward (get_live_tree ct) LN = LN)) eqn:B.
  - apply bool_decide_spec in B. rewrite B in D. rewrite <- I in H2; inv_opt.
    assert (Mf : forall r, MEM r (MAP FST (toAList live)) = false).
    { intros r; destruct (MEM r (MAP FST (toAList live))) eqn:M; [|reflexivity].
      apply MEM_keys in M; rewrite D in M; destruct M. }
    split; intros r; rewrite ?lookup_numset_list_add_if_lt, ?lookup_numset_list_add_if_gt, Mf; reflexivity.
  - cbn [get_intervals] in H2. rewrite <- I in H2; cbn in H2; inv_opt.
    split; intros r; rewrite ?lookup_numset_list_add_if_lt, ?lookup_numset_list_add_if_gt, (MEM_keys_eq _ _ r D);
      reflexivity.
Qed.
