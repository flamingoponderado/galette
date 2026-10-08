(** * CakeML [reg_allocProof]: forced edges, tags, colour extraction and
    the injectivity of [check_clash_tree]

    Part of the [reg_allocProofScript] counterpart.

    [reg_allocScript]'s theorem [convention_partitions] is not yet in
    [reg_alloc.v]; an untagged copy ([convention_partitions_copy]) is proved
    here. *)

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
  check_clash_tree ra_state colouring graph mk_graph.
Open Scope N_scope.
Open Scope monad_scope.

(** [reg_allocScript]'s [convention_partitions] (untagged copy). *)
Lemma convention_partitions_copy : forall n,
  (is_stack_var n <-> ~ is_phy_var n /\ ~ is_alloc_var n) /\
  (is_phy_var n <-> ~ is_stack_var n /\ ~ is_alloc_var n) /\
  (is_alloc_var n <-> ~ is_phy_var n /\ ~ is_stack_var n).
Proof.
  intros n; unfold is_stack_var, is_phy_var, is_alloc_var, is_true; rewrite !N.eqb_eq.
  assert (H2 : n MOD 2 = (n MOD 4) MOD 2) by lia.
  assert (H4 : n MOD 4 < 4) by (apply N.mod_lt; lia).
  rewrite H2; destruct (n MOD 4) as [|p] eqn:E; [cbn; intuition discriminate|].
  destruct p as [[p|p|]|[p|p|]|]; cbn in *; try lia; intuition discriminate.
Qed.

(** ** Forced edges *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "extend_graph_succeeds" *)
Theorem extend_graph_succeeds : forall (forced : list (N * N)) f s,
  good_ra_state s /\ EVERY (fun '(x, y) => (f x <? s.(dim)) && (f y <? s.(dim))) forced ->
  exists s',
    extend_graph f forced s = (M_success tt, s') /\
    good_ra_state s' /\
    s' = with_adj_ls s s'.(adj_ls) /\
    forall a b, has_edge s'.(adj_ls) a b <->
      (exists x y, f x = a /\ f y = b /\ MEM (y, x) forced) \/
      (exists x y, f x = a /\ f y = b /\ MEM (x, y) forced) \/
      has_edge s.(adj_ls) a b.
Proof.
  induction forced as [|[x y] xs IH]; intros f s (Hg & Hev); cbn [extend_graph].
  - exists s; split; [reflexivity|split; [exact Hg|split; [destruct s; reflexivity|]]].
    intros a b; split; [tauto|intros [(? & ? & _ & _ & H)|[(? & ? & _ & _ & H)|H]]; [discriminate|discriminate|exact H]].
  - cbn [EVERY] in Hev; apply andb_iff in Hev as [Hxy Hev]; apply andb_iff in Hxy as [Hx Hy].
    apply ltb_iff in Hx, Hy.
    destruct (insert_edge_succeeds s (f x) (f y) (conj Hg (conj Hy Hx))) as (s1 & E1 & Hg1 & Hw1 & He1).
    mstep E1. wsubst Hw1. rs.
    destruct (IH f (with_adj_ls s t)) as (s2 & E2 & Hg2 & Hw2 & He2); [rs; auto|].
    rewrite E2. wsubst Hw2. rs.
    exists (with_adj_ls s t0); split; [reflexivity|split; [exact Hg2|split; [reflexivity|]]].
    intros a b; rs; rewrite He2, He1. cbn [MEM]. split.
    + intros [(p & q & <- & <- & Hm)|[(p & q & <- & <- & Hm)|[[-> ->]|[[-> ->]|Hm]]]];
        [left; exists p, q; rewrite orb_iff; tauto|right; left; exists p, q; rewrite orb_iff; tauto
        |right; left; exists x, y; rewrite orb_iff, bool_decide_iff; tauto
        |left; exists y, x; rewrite orb_iff, bool_decide_iff; tauto|tauto].
    + intros [(p & q & <- & <- & Hm)|[(p & q & <- & <- & Hm)|Hm]]; [| |tauto];
        rewrite orb_iff, bool_decide_iff in Hm; destruct Hm as [Hm|Hm].
      * injection Hm as -> ->; tauto.
      * left; exists p, q; tauto.
      * injection Hm as -> ->; tauto.
      * right; left; exists p, q; tauto.
Qed.

(** ** Tags *)

Definition mk_tag (fs : num_set) (v : N) : tag :=
  if v MOD 4 =? 1 then match lookup v fs with None => Atemp | Some tt => Stemp end
  else if v MOD 4 =? 3 then Stemp else Fixed (v DIV 2).

Lemma mk_tag_spec fs v :
  if is_phy_var v then mk_tag fs v = Fixed (v DIV 2)
  else if is_stack_var v then mk_tag fs v = Stemp
  else mk_tag fs v = Atemp \/ mk_tag fs v = Stemp.
Proof.
  pose proof (convention_partitions_copy v) as (P1 & P2 & P3).
  unfold mk_tag. destruct (is_phy_var v) eqn:Ep.
  - destruct (proj1 P2 eq_refl) as [Hs Ha].
    unfold is_alloc_var, is_stack_var, is_true in Ha, Hs. destruct (v MOD 4 =? 1); [exfalso; apply Ha; reflexivity|].
    destruct (v MOD 4 =? 3); [exfalso; apply Hs; reflexivity|reflexivity].
  - destruct (is_stack_var v) eqn:Es.
    + unfold is_stack_var in Es; apply N.eqb_eq in Es; rewrite Es; reflexivity.
    + assert (Ha : is_alloc_var v) by (apply P3; split; intros H; discriminate H).
      unfold is_alloc_var in Ha; apply N.eqb_eq in Ha; rewrite Ha; cbn.
      destruct (lookup v fs) as [[]|]; auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "mk_tags_st_ex_FOREACH_lem" *)
Theorem mk_tags_st_ex_FOREACH_lem : forall fs ls s fa,
  good_ra_state s /\ EVERY (fun v => v <? s.(dim)) ls ->
  exists s',
    st_ex_FOREACH ls
      (fun i =>
         if fa i MOD 4 =? 1 then
           match lookup (fa i) fs with
           | None => update_node_tag i Atemp
           | Some tt => update_node_tag i Stemp
           end
         else if fa i MOD 4 =? 3 then update_node_tag i Stemp
         else update_node_tag i (Fixed (fa i DIV 2))) s = (M_success tt, s') /\
    good_ra_state s' /\
    s' = with_node_tag s s'.(node_tag) /\
    (forall x, x < s.(dim) ->
       if MEM x ls then
         (if is_phy_var (fa x) then EL x s'.(node_tag) = Fixed (fa x DIV 2)
          else if is_stack_var (fa x) then EL x s'.(node_tag) = Stemp
          else EL x s'.(node_tag) = Atemp \/ EL x s'.(node_tag) = Stemp)
       else EL x s'.(node_tag) = EL x s.(node_tag)).
Proof.
  intros fs; induction ls as [|h ls IH]; intros s fa (Hg & Hev); cbn [st_ex_FOREACH].
  - exists s; split; [reflexivity|split; [exact Hg|split; [destruct s; reflexivity|]]].
    intros x _; reflexivity.
  - cbn [EVERY] in Hev; apply andb_iff in Hev as [Hh Hev]; apply ltb_iff in Hh.
    pose proof Hg as (_ & L2 & _).
    assert (Hu : (if fa h MOD 4 =? 1 then
           match lookup (fa h) fs with
           | None => update_node_tag h Atemp
           | Some tt => update_node_tag h Stemp
           end
         else if fa h MOD 4 =? 3 then update_node_tag h Stemp
         else update_node_tag h (Fixed (fa h DIV 2))) s = update_node_tag h (mk_tag fs (fa h)) s).
    { unfold mk_tag; destruct (fa h MOD 4 =? 1); [destruct (lookup (fa h) fs) as [[]|]|destruct (fa h MOD 4 =? 3)]; reflexivity. }
    unfold st_ex_ignore_bind at 1; rewrite Hu, (update_node_tag_ok h _ s ltac:(lia)).
    fold (st_ex_FOREACH ls (fun i =>
         if fa i MOD 4 =? 1 then
           match lookup (fa i) fs with
           | None => update_node_tag i Atemp
           | Some tt => update_node_tag i Stemp
           end
         else if fa i MOD 4 =? 3 then update_node_tag i Stemp
         else update_node_tag i (Fixed (fa i DIV 2)))).
    destruct (IH (with_node_tag s (LUPDATE (mk_tag fs (fa h)) h (node_tag s))) fa) as (s2 & E2 & Hg2 & Hw2 & Hm2).
    { split; [apply good_ra_state_with_node_tag; [exact Hg|rewrite LENGTH_LUPDATE; exact L2]|rs; exact Hev]. }
    rewrite E2. wsubst Hw2. rs.
    exists (with_node_tag s t); split; [reflexivity|split; [exact Hg2|split; [reflexivity|]]].
    intros x Hx; rs. specialize (Hm2 x Hx). cbn [MEM].
    destruct (MEM x ls) eqn:Em.
    + rewrite orb_true_r; exact Hm2.
    + rewrite orb_false_r. rewrite Hm2, EL_LUPDATE.
      destruct (N.eq_dec x h) as [->|Hne].
      * rewrite (proj2 (bool_decide_spec (h = h)) eq_refl).
        destruct (decide (h = h /\ h < LENGTH (node_tag s))) as [_|Hd]; [apply mk_tag_spec|].
        exfalso; apply Hd; split; [reflexivity|lia].
      * assert (Hb : bool_decide (x = h) = false) by (unfold bool_decide; destruct (decide _); [congruence|reflexivity]).
        rewrite Hb. destruct (decide (h = x /\ _)) as [[? _]|]; [congruence|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "mk_tags_succeeds" *)
Theorem mk_tags_succeeds : forall s n fs fa,
  good_ra_state s /\ n = s.(dim) ->
  exists s',
    mk_tags n fs fa s = (M_success tt, s') /\
    good_ra_state s' /\
    s' = with_node_tag s s'.(node_tag) /\
    forall x y, x < n /\ y = fa x ->
      if is_phy_var y then EL x s'.(node_tag) = Fixed (y DIV 2)
      else if is_stack_var y then EL x s'.(node_tag) = Stemp
      else EL x s'.(node_tag) = Atemp \/ EL x s'.(node_tag) = Stemp.
Proof.
  intros s n fs fa (Hg & ->). unfold mk_tags. ret.
  destruct (mk_tags_st_ex_FOREACH_lem fs (GENLIST (fun x => x) (dim s)) s fa) as (s' & E & Hg' & Hw & Hm).
  { split; [exact Hg|]. apply EVERY_lt_iff; intros y Hy; apply In_GENLIST in Hy as (i & Hi & ->); exact Hi. }
  exists s'; split; [exact E|split; [exact Hg'|split; [exact Hw|]]].
  intros x y [Hx ->]. specialize (Hm x Hx).
  assert (Hmem : MEM x (GENLIST (fun x => x) (dim s)) = true) by (apply MEM_In, In_GENLIST; exists x; split; [lia|reflexivity]).
  rewrite Hmem in Hm; exact Hm.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "TWOxDIV2" *)
Theorem TWOxDIV2 : forall x, 2 * x DIV 2 = x.
Proof. intros x; rewrite N.mul_comm, N.div_mul by lia; reflexivity. Qed.

(** ** Extracting the colouring *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "extract_color_st_ex_MAP_lem" *)
Theorem extract_color_st_ex_MAP_lem : forall (ls : list (N * N)) s,
  EVERY (fun '(k, v) => v <? LENGTH s.(node_tag)) ls ->
  st_ex_MAP (fun '(k, v) => t <- node_tag_sub v ;; st_ex_return (k, extract_tag t)) ls s =
  (M_success (MAP (fun '(k, v) => (k, extract_tag (EL v s.(node_tag)))) ls), s).
Proof.
  induction ls as [|[k v] ls IH]; intros s H; [reflexivity|].
  cbn [EVERY] in H; apply andb_iff in H as [Hv H]; apply ltb_iff in Hv.
  cbn [st_ex_MAP]. unfold st_ex_bind at 1. cbv beta iota. rewrite (bind_ok _ _ _ _ _ (node_tag_sub_ok v s Hv)).
  cbv beta. cbn [st_ex_return]. mstep' (IH s H). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "extract_color_succeeds" *)
Theorem extract_color_succeeds : forall s ta,
  good_ra_state s /\ (forall x y, lookup x ta = Some y -> y < s.(dim)) /\ wf ta ->
  extract_color ta s = (M_success (sptree.map (fun v => extract_tag (EL v s.(node_tag))) ta), s).
Proof.
  intros s ta (Hg & Hb & Hw). pose proof Hg as (_ & L2 & _).
  unfold extract_color. ret.
  assert (Hev : EVERY (fun '(k, v) => v <? LENGTH s.(node_tag)) (toAList ta)).
  { apply EVERY_iff; intros [k v] Hk; apply ltb_iff; rewrite L2.
    apply (Hb k), MEM_toAList, MEM_In, Hk. }
  mstep' (extract_color_st_ex_MAP_lem (toAList ta) s Hev). cbn [st_ex_return]. f_equal; f_equal.
  rewrite <- (fromAList_toAList ta Hw) at 2. rewrite map_fromAList. reflexivity.
Qed.

(** ** [check_clash_tree] only depends on the colouring of its variables *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "no_clash_colouring_satisfactory" *)
Theorem no_clash_colouring_satisfactory : forall adjls node_tag,
  no_clash adjls node_tag /\ LENGTH adjls = LENGTH node_tag /\
  EVERY (fun n => bool_decide (n <> Stemp /\ n <> Atemp)) node_tag ->
  colouring_satisfactory
    (fun f => if f <? LENGTH node_tag then extract_tag (EL f node_tag) else 0) adjls.
Proof.
  intros adjls tags (Hnc & HL & Hev) x Hx y [Hy Hm].
  rewrite <- HL. apply N.ltb_lt in Hx as Hx', Hy as Hy'. rewrite Hx', Hy'.
  specialize (Hnc x y (conj Hx (conj Hy Hm))).
  rewrite EVERY_iff in Hev.
  pose proof (Hev _ (EL_In x tags ltac:(lia))) as Ex; pose proof (Hev _ (EL_In y tags ltac:(lia))) as Ey.
  apply bool_decide_iff in Ex, Ey.
  destruct (EL x tags), (EL y tags); tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "check_partial_col_same_dom" *)
Theorem check_partial_col_same_dom : forall ls f g t ft,
  (forall x, MEM x ls -> f x = g x) ->
  check_partial_col f ls t ft = check_partial_col g ls t ft.
Proof.
  induction ls as [|x xs IH]; intros f g t ft H; cbn [check_partial_col]; [reflexivity|].
  assert (Hx : f x = g x) by (apply H; cbn [MEM]; apply orb_iff; left; apply bool_decide_iff; reflexivity).
  assert (Hxs : forall y, MEM y xs -> f y = g y) by (intros y Hy; apply H; cbn [MEM]; apply orb_iff; right; exact Hy).
  rewrite Hx. destruct (lookup x t) as [[]|]; [apply IH, Hxs|].
  destruct (lookup (g x) ft) as [[]|]; [reflexivity|apply IH, Hxs].
Qed.

Lemma MAP_FST_toAList_ext {A} (f g : N -> N) (t : num_map A) :
  (forall x, x IN domain t -> f x = g x) ->
  MAP (fun x => f (FST x)) (toAList t) = MAP (fun x => g (FST x)) (toAList t).
Proof.
  intros H; apply map_ext_in; intros [k v] Hk; cbn [FST]; apply H.
  apply In_MAP_FST_toAList, in_map_iff; exists (k, v); auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "check_clash_tree_same_dom" *)
Theorem check_clash_tree_same_dom : forall ct f g live flive,
  (forall x, in_clash_tree ct x \/ x IN domain live -> f x = g x) ->
  check_clash_tree f ct live flive = check_clash_tree g ct live flive.
Proof.
  induction ct as [w r|t|topt c1 IH1 c2 IH2|c1 IH1 c2 IH2]; intros f g live flive H;
    cbn [check_clash_tree in_clash_tree] in *.
  - rewrite (check_partial_col_same_dom w f g) by (intros; apply H; tauto).
    destruct (check_partial_col g w live flive); [|reflexivity].
    rewrite (map_ext_in f g w) by (intros x Hx; apply H; left; left; apply MEM_In, Hx).
    apply check_partial_col_same_dom; intros; apply H; tauto.
  - unfold check_col; rewrite (MAP_FST_toAList_ext f g) by (intros; apply H; tauto); reflexivity.
  - rewrite (IH1 f g live flive) by (intros; apply H; tauto).
    rewrite (IH2 f g live flive) by (intros; apply H; tauto).
    destruct (check_clash_tree g c1 live flive) as [[o1 fo1]|] eqn:C1; [|reflexivity].
    destruct (check_clash_tree g c2 live flive) as [[o2 fo2]|] eqn:C2; [|reflexivity].
    destruct topt as [ts|].
    + unfold check_col; rewrite (MAP_FST_toAList_ext f g) by (intros; apply H; tauto); reflexivity.
    + apply check_partial_col_same_dom; intros x Hx. apply MEM_In, In_MAP_FST_toAList in Hx.
      rewrite domain_difference in Hx; destruct Hx as [Hx _].
      apply (check_clash_tree_domain _ _ _ _ _ _ C2) in Hx.
      apply H; unfold pred_set.UNION, pred_set.IN in *; tauto.
  - rewrite (IH2 f g live flive) by (intros; apply H; tauto).
    destruct (check_clash_tree g c2 live flive) as [[o2 fo2]|] eqn:C2; [|reflexivity].
    apply IH1; intros x [Hx|Hx]; [apply H; tauto|].
    apply (check_clash_tree_domain _ _ _ _ _ _ C2) in Hx.
    apply H; unfold pred_set.UNION, pred_set.IN in *; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "opt_split" *)
Theorem opt_split : forall a : option unit, a <> None <-> a = Some tt.
Proof. intros [[]|]; split; congruence. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "INJ_IMG_lookup" *)
Theorem INJ_IMG_lookup : forall (g : N -> N) (gt ft : num_set) x,
  INJ g UNIV UNIV /\ domain gt = IMAGE g (domain ft) -> lookup (g x) gt = lookup x ft.
Proof.
  intros g gt ft x [[_ Hi] Hd].
  pose proof (f_equal (fun P => P (g x)) Hd) as E; cbv beta in E.
  destruct (lookup x ft) as [[]|] eqn:Ex.
  - assert (Hin : domain gt (g x)).
    { rewrite E; exists x; split; [reflexivity|]. unfold pred_set.IN; apply domain_lookup; eauto. }
    apply domain_lookup in Hin as [[] Hv]; exact Hv.
  - destruct (lookup (g x) gt) as [[]|] eqn:Eg; [|reflexivity]. exfalso.
    assert (Hin : domain gt (g x)) by (apply domain_lookup; eauto).
    rewrite E in Hin; destruct Hin as (y & Ey & Hy).
    assert (x = y) by (apply Hi; [split; exact I|exact Ey]). subst y.
    unfold pred_set.IN in Hy; apply domain_lookup in Hy as [? ?]; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "check_partial_col_INJ" *)
Theorem check_partial_col_INJ : forall (f g : N -> N) ls t ft gt,
  INJ g UNIV UNIV /\ domain gt = IMAGE g (domain ft) ->
  match check_partial_col f ls t ft with
  | None => check_partial_col (g ∘ f) ls t gt = None
  | Some (tt_, ftt) =>
      exists gtt, check_partial_col (g ∘ f) ls t gt = Some (tt_, gtt) /\
                  domain gtt = IMAGE g (domain ftt)
  end.
Proof.
  intros f g; induction ls as [|x xs IH]; intros t ft gt [Hg Hd]; cbn [check_partial_col].
  - exists gt; auto.
  - destruct (lookup x t) as [[]|]; [apply IH; auto|].
    cbv beta; rewrite (INJ_IMG_lookup g gt ft (f x) (conj Hg Hd)).
    destruct (lookup (f x) ft) as [[]|]; [reflexivity|].
    apply IH; split; [exact Hg|]. rewrite !domain_insert, Hd.
    apply EXTENSION; intros z; rewrite IN_IMAGE; unfold pred_set.IN, IMAGE; cbv beta.
    split; [intros [->|(y & -> & Hy)]; [exists (f x); auto|exists y; auto]|].
    intros (y & -> & [->|Hy]); [left; reflexivity|right; exists y; auto].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "check_col_INJ" *)
Theorem check_col_INJ : forall (f g : N -> N) (s : num_set),
  INJ g UNIV UNIV ->
  match check_col f s with
  | None => check_col (g ∘ f) s = None
  | Some (t, ft) =>
      exists gt, check_col (g ∘ f) s = Some (t, gt) /\ domain gt = IMAGE g (domain ft)
  end.
Proof.
  intros f g s [_ Hi]. unfold check_col.
  rewrite (MAP_FST_toAList_eq (g ∘ f)), (MAP_FST_toAList_eq f).
  set (ls := MAP f (MAP fst (toAList s))).
  replace (MAP (g ∘ f) (MAP fst (toAList s))) with (MAP g ls) by (subst ls; rewrite List.map_map; reflexivity).
  assert (Hiff : ALL_DISTINCT ls = ALL_DISTINCT (MAP g ls)).
  { apply eq_true_iff_eq; change (is_true (ALL_DISTINCT ls) <-> is_true (ALL_DISTINCT (MAP g ls))); rewrite !ALL_DISTINCT_iff; split.
    - intros Hd; apply NoDup_map_inj; [exact Hd|intros x y _ _ E; apply Hi; [split; exact I|exact E]].
    - apply NoDup_map_inv. }
  rewrite <- Hiff. destruct (ALL_DISTINCT ls); [|reflexivity].
  eexists; split; [reflexivity|]. rewrite !domain_fromAList_unit, LIST_TO_SET_MAP; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "check_clash_tree_INJ" *)
Theorem check_clash_tree_INJ : forall ct (f g : N -> N) live flive glive,
  INJ g UNIV UNIV /\ domain glive = IMAGE g (domain flive) ->
  match check_clash_tree f ct live flive with
  | None => check_clash_tree (g ∘ f) ct live glive = None
  | Some (liveout, fliveout) =>
      exists gliveout,
        check_clash_tree (g ∘ f) ct live glive = Some (liveout, gliveout) /\
        domain gliveout = IMAGE g (domain fliveout)
  end.
Proof.
  induction ct as [w r|t|topt c1 IH1 c2 IH2|c1 IH1 c2 IH2]; intros f g live flive glive [Hg Hd];
    cbn [check_clash_tree].
  - pose proof (check_partial_col_INJ f g w live flive glive (conj Hg Hd)) as H1.
    destruct (check_partial_col f w live flive) as [[l1 fl1]|]; [|rewrite H1; reflexivity].
    destruct H1 as (gl1 & -> & _).
    replace (MAP (g ∘ f) w) with (MAP g (MAP f w)) by (rewrite List.map_map; reflexivity).
    apply check_partial_col_INJ; split; [exact Hg|].
    rewrite !domain_numset_list_delete, Hd, LIST_TO_SET_MAP, IMAGE_DIFF; [reflexivity|].
    apply INJ_SUBSET_UNIV, Hg.
  - apply check_col_INJ, Hg.
  - pose proof (IH1 f g live flive glive (conj Hg Hd)) as H1.
    destruct (check_clash_tree f c1 live flive) as [[o1 fo1]|]; [|rewrite H1; reflexivity].
    destruct H1 as (go1 & -> & Hd1).
    pose proof (IH2 f g live flive glive (conj Hg Hd)) as H2.
    destruct (check_clash_tree f c2 live flive) as [[o2 fo2]|]; [|rewrite H2; reflexivity].
    destruct H2 as (go2 & -> & Hd2).
    destruct topt as [ts|]; [apply check_col_INJ, Hg|].
    apply check_partial_col_INJ; split; assumption.
  - pose proof (IH2 f g live flive glive (conj Hg Hd)) as H2.
    destruct (check_clash_tree f c2 live flive) as [[o2 fo2]|]; [|rewrite H2; reflexivity].
    destruct H2 as (go2 & -> & Hd2).
    apply IH1; split; assumption.
Qed.
