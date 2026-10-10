(** * CakeML [linear_scanProof]: the renaming bijection and the top-level theorem

    Part of the [linear_scanProofScript] counterpart (HOL lines 4997-6230):
    the bijection invariants, the monadic interval computation, the
    renaming of clash trees and [linear_scan_reg_alloc_correct].

    Statement conventions: HOL [st.bij] is [bij st]; HOL sets are
    predicates ([pred_set]); HOL [s with f := v] is a record update
    ([with_int_beg]/[with_int_end], Galette-only); HOL [EVERY] over [Prop]
    predicates uses [⌜P⌝]; HOL's free variables ([bijdom], [appbij], ...)
    are quantified explicitly.  HOL's local [LENGTH_toAList] is
    [LENGTH_toAList'] ([sptree] already has [LENGTH_toAList]). *)

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
From Galette.cakeml.compiler.backend.reg_alloc.proofs.linear_scanProof Require Import intervals allocator.
Open Scope N_scope.
Open Scope monad_scope.

(** ** The bijection *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "good_bijection_state_def" *)
Definition good_bijection_state (st : bijection_state) (regset : N -> Prop) : Prop :=
  regset = domain st.(bij) /\
  (sp_inverts st.(bij) st.(invbij) /\ sp_inverts st.(invbij) st.(bij)) /\
  ((forall r, r IN regset -> (is_stack_var r <-> is_stack_var (the 0 (lookup r st.(bij))))) /\
   (forall r, r IN regset -> (is_alloc_var r <-> is_alloc_var (the 0 (lookup r st.(bij))))) /\
   (forall r, r IN regset /\ is_phy_var r -> r = the 0 (lookup r st.(bij)))) /\
  (forall r, r IN domain st.(invbij) /\ is_stack_var r -> r < st.(nstack)) /\
  (forall r, r IN domain st.(invbij) /\ is_alloc_var r -> r < st.(nalloc)) /\
  (is_stack_var st.(nstack) /\ is_alloc_var st.(nalloc)) /\
  (forall r, the 0 (lookup r st.(bij)) <= st.(nmax)).

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "convention_partitions_or" *)
Theorem convention_partitions_or : forall r,
  (is_phy_var r /\ ~ is_stack_var r /\ ~ is_alloc_var r) \/
  (~ is_phy_var r /\ is_stack_var r /\ ~ is_alloc_var r) \/
  (~ is_phy_var r /\ ~ is_stack_var r /\ is_alloc_var r).
Proof.
  intros r. pose proof (convention_partitions' r) as (H1 & H2 & H3).
  destruct (is_phy_var r) eqn:Ep, (is_stack_var r) eqn:Es, (is_alloc_var r) eqn:Ea; unfold is_true in *;
    intuition (try congruence).
Qed.

Lemma dom_iff {A} (x : N) (t : num_map A) : x IN domain t <-> lookup x t <> None.
Proof.
  unfold pred_set.IN. rewrite domain_lookup. destruct (lookup x t); split; intros H;
    [eauto; discriminate|eauto|destruct H; discriminate|congruence].
Qed.

Ltac bd_simp :=
  repeat match goal with
         | |- context [@bool_decide (?u = ?v) ?d] =>
             first [ replace (@bool_decide (u = v) d) with false
                       by (symmetry; apply Bool.not_true_iff_false; intros Hbd; apply bool_decide_spec in Hbd; discriminate)
                   | replace (@bool_decide (u = v) d) with true by (symmetry; apply bool_decide_spec; reflexivity) ]
         end.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "find_bijection_invariants" *)
Theorem find_bijection_invariants : forall st r regset,
  good_bijection_state st regset ->
  good_bijection_state (find_bijection_step st r) (r INSERT regset).
Proof.
  intros st r regset (Hd & [Hi1 Hi2] & (Hs & Ha & Hp) & Hns & Hna & [Hsn Han] & Hmx). subst regset.
  unfold find_bijection_step.
  destruct (lookup r (bij st)) as [v|] eqn:El.
  { bd_simp. cbn [negb].
    assert (E : r INSERT domain (bij st) = domain (bij st)).
    { apply set_ext; intros x. unfold pred_set.INSERT, pred_set.IN. split; [|tauto]. intros [->|H]; [|exact H].
      apply domain_lookup; eauto. }
    rewrite E. exact (conj eq_refl (conj (conj Hi1 Hi2) (conj (conj Hs (conj Ha Hp)) (conj Hns (conj Hna (conj (conj Hsn Han) Hmx)))))). }
  bd_simp. cbn [negb].
  assert (Hrn : r NOTIN domain (bij st)) by (rewrite dom_iff; tauto).
  assert (Hdi : forall x, r INSERT domain (bij st) = domain (insert r x (bij st))).
  { intros x. rewrite domain_insert. reflexivity. }
  pose proof (convention_partitions_or r) as Hc.
  destruct (is_phy_var r) eqn:Ep.
  - (* physical *)
    assert (Hri : r NOTIN domain (invbij st)).
    { rewrite dom_iff. destruct (lookup r (invbij st)) as [fr|] eqn:Ef; [|tauto]. intros _.
      pose proof (Hi2 _ _ Ef) as Hb. assert (Hfr : fr IN domain (bij st)) by (apply domain_lookup; eauto).
      pose proof (convention_partitions_or fr) as Hcf. pose proof (convention_partitions' r) as (_ & Hpr & _).
      assert (Hrp : is_true (is_phy_var r)) by exact Ep. apply Hpr in Hrp as [Hrs Hra].
      destruct Hcf as [(Hf1 & _ & _)|[(_ & Hf2 & _)|(_ & _ & Hf3)]].
      - pose proof (Hp fr (conj Hfr Hf1)) as Ef'. rewrite Hb in Ef'. cbn in Ef'. subst fr. congruence.
      - apply Hrs. pose proof (proj1 (Hs fr Hfr) Hf2) as X. rewrite Hb in X. exact X.
      - apply Hra. pose proof (proj1 (Ha fr Hfr) Hf3) as X. rewrite Hb in X. exact X. }
    unfold good_bijection_state; cbn [bij invbij nstack nalloc nmax].
    split; [apply Hdi|]. split; [split; apply sp_inverts_insert; tauto|].
    split; [split; [|split]|].
    + intros x Hx; unfold pred_set.INSERT, pred_set.IN in Hx. rewrite lookup_insert. destruct (decide (x = r)) as [->|Hne]; [cbn; tauto|].
      apply Hs. destruct Hx as [Hx|Hx]; [congruence|exact Hx].
    + intros x Hx; unfold pred_set.INSERT, pred_set.IN in Hx. rewrite lookup_insert. destruct (decide (x = r)) as [->|Hne]; [cbn; tauto|].
      apply Ha. destruct Hx as [Hx|Hx]; [congruence|exact Hx].
    + intros x [Hx Hxp]; unfold pred_set.INSERT, pred_set.IN in Hx. rewrite lookup_insert. destruct (decide (x = r)) as [->|Hne]; [reflexivity|].
      apply Hp. split; [|exact Hxp]. destruct Hx as [Hx|Hx]; [congruence|exact Hx].
    + split; [|split; [|split; [split; assumption|]]].
      * intros x [Hx Hxs]. unfold pred_set.IN in Hx; rewrite domain_insert in Hx. destruct Hx as [->|Hx]; [|apply Hns; auto].
        exfalso. pose proof (convention_partitions' r) as (Hsx & _). apply Hsx in Hxs as [Hx _]. apply Hx, Ep.
      * intros x [Hx Hxa]. unfold pred_set.IN in Hx; rewrite domain_insert in Hx. destruct Hx as [->|Hx]; [|apply Hna; auto].
        exfalso. pose proof (convention_partitions' r) as (_ & _ & Hax). apply Hax in Hxa as [Hx _]. apply Hx, Ep.
      * intros x. rewrite lookup_insert. destruct (decide (x = r)) as [->|]; cbn [the]; [|specialize (Hmx x)]; rewrite MAX_max; lia.
  - destruct (is_stack_var r) eqn:Es.
    + (* stack *)
      assert (Hri : nstack st NOTIN domain (invbij st)) by (intros H; pose proof (Hns _ (conj H Hsn)); lia).
      unfold good_bijection_state; cbn [bij invbij nstack nalloc nmax].
      split; [apply Hdi|]. split; [split; apply sp_inverts_insert; tauto|].
      split; [split; [|split]|].
      * intros x Hx; unfold pred_set.INSERT, pred_set.IN in Hx. rewrite lookup_insert. destruct (decide (x = r)) as [->|Hne]; [cbn; split; intros _; [exact Hsn|exact Es]|].
        apply Hs. destruct Hx as [Hx|Hx]; [congruence|exact Hx].
      * intros x Hx; unfold pred_set.INSERT, pred_set.IN in Hx. rewrite lookup_insert. destruct (decide (x = r)) as [->|Hne].
        -- cbn [the]. pose proof (convention_partitions' r) as (Hs1 & _). pose proof (convention_partitions' (nstack st)) as (Hs2 & _).
           assert (A1 : is_true (is_stack_var r)) by exact Es. apply Hs1 in A1. apply Hs2 in Hsn. tauto.
        -- apply Ha. destruct Hx as [Hx|Hx]; [congruence|exact Hx].
      * intros x [Hx Hxp]; unfold pred_set.INSERT, pred_set.IN in Hx. rewrite lookup_insert. destruct (decide (x = r)) as [->|Hne]; [rewrite Ep in Hxp; discriminate|].
        apply Hp. split; [|exact Hxp]. destruct Hx as [Hx|Hx]; [congruence|exact Hx].
      * split; [|split; [|split; [split|]]].
        -- intros x [Hx Hxs]. unfold pred_set.IN in Hx; rewrite domain_insert in Hx. destruct Hx as [->|Hx]; [lia|].
           pose proof (Hns _ (conj Hx Hxs)); lia.
        -- intros x [Hx Hxa]. unfold pred_set.IN in Hx; rewrite domain_insert in Hx. destruct Hx as [->|Hx]; [|apply Hna; auto].
           exfalso. pose proof (convention_partitions' (nstack st)) as (Hs2 & _). apply Hs2 in Hsn. tauto.
        -- unfold is_stack_var in *. unfold is_true in *. apply N.eqb_eq in Hsn. apply N.eqb_eq.
           replace (nstack st + 4) with (nstack st + 1 * 4) by lia. rewrite N.Div0.mod_add. exact Hsn.
        -- exact Han.
        -- intros x. rewrite lookup_insert. destruct (decide (x = r)) as [->|]; cbn [the]; [|specialize (Hmx x)]; rewrite MAX_max; lia.
    + (* alloc *)
      assert (Hra : is_true (is_alloc_var r)).
      { destruct Hc as [(H & _)|[(_ & H & _)|(_ & _ & H)]]; [exfalso; revert H; rewrite ?Ep; intros H; discriminate H|exfalso; revert H; rewrite ?Es; intros H; discriminate H|exact H]. }
      assert (Hri : nalloc st NOTIN domain (invbij st)) by (intros H; pose proof (Hna _ (conj H Han)); lia).
      unfold good_bijection_state; cbn [bij invbij nstack nalloc nmax].
      split; [apply Hdi|]. split; [split; apply sp_inverts_insert; tauto|].
      split; [split; [|split]|].
      * intros x Hx; unfold pred_set.INSERT, pred_set.IN in Hx. rewrite lookup_insert. destruct (decide (x = r)) as [->|Hne].
        -- cbn [the]. pose proof (convention_partitions' (nalloc st)) as (_ & _ & Hs2).
           apply Hs2 in Han. rewrite Es. split; [discriminate|tauto].
        -- apply Hs. destruct Hx as [Hx|Hx]; [congruence|exact Hx].
      * intros x Hx; unfold pred_set.INSERT, pred_set.IN in Hx. rewrite lookup_insert. destruct (decide (x = r)) as [->|Hne]; [cbn; tauto|].
        apply Ha. destruct Hx as [Hx|Hx]; [congruence|exact Hx].
      * intros x [Hx Hxp]; unfold pred_set.INSERT, pred_set.IN in Hx. rewrite lookup_insert. destruct (decide (x = r)) as [->|Hne]; [rewrite Ep in Hxp; discriminate|].
        apply Hp. split; [|exact Hxp]. destruct Hx as [Hx|Hx]; [congruence|exact Hx].
      * split; [|split; [|split; [split|]]].
        -- intros x [Hx Hxs]. unfold pred_set.IN in Hx; rewrite domain_insert in Hx. destruct Hx as [->|Hx]; [|apply Hns; auto].
           exfalso. pose proof (convention_partitions' (nalloc st)) as (_ & _ & Hs2). apply Hs2 in Han. tauto.
        -- intros x [Hx Hxa]. unfold pred_set.IN in Hx; rewrite domain_insert in Hx. destruct Hx as [->|Hx]; [lia|].
           pose proof (Hna _ (conj Hx Hxa)); lia.
        -- exact Hsn.
        -- unfold is_alloc_var in *. unfold is_true in *. apply N.eqb_eq in Han. apply N.eqb_eq.
           replace (nalloc st + 4) with (nalloc st + 1 * 4) by lia. rewrite N.Div0.mod_add. exact Han.
        -- intros x. rewrite lookup_insert. destruct (decide (x = r)) as [->|]; cbn [the]; [|specialize (Hmx x)]; rewrite MAX_max; lia.
Qed.

Lemma set_eq_iff (s t : N -> Prop) : (forall x, s x <-> t x) -> s = t.
Proof. apply set_ext. Qed.

Ltac sets := unfold pred_set.UNION, pred_set.INSERT, pred_set.IN in *.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "FOLDL_find_bijection_invariants" *)
Theorem FOLDL_find_bijection_invariants : forall st l regset,
  good_bijection_state st regset ->
  good_bijection_state (FOLDL find_bijection_step st l) (set l UNION regset).
Proof.
  intros st l; revert st; induction l as [|h l IH]; intros st regset H; cbn [FOLDL].
  - replace (set [] UNION regset) with regset; [exact H|]. apply set_eq_iff; intros x; sets; cbn; tauto.
  - replace (set (h :: l) UNION regset) with (set l UNION (h INSERT regset)).
    + apply IH, find_bijection_invariants, H.
    + apply set_eq_iff; intros x; sets; cbn [LIST_TO_SET]; tauto.
Qed.

Lemma FOLDR_find_bijection_invariants st l regset :
  good_bijection_state st regset ->
  good_bijection_state (FOLDR (fun r acc => find_bijection_step acc r) st l) (set l UNION regset).
Proof.
  revert regset; induction l as [|h l IH]; intros regset H; cbn [FOLDR].
  - replace (set [] UNION regset) with regset; [exact H|]. apply set_eq_iff; intros x; sets; cbn; tauto.
  - replace (set (h :: l) UNION regset) with (h INSERT (set l UNION regset)).
    + apply find_bijection_invariants, IH, H.
    + apply set_eq_iff; intros x; sets; cbn [LIST_TO_SET]; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "foldi_find_bijection_invariants" *)
Theorem foldi_find_bijection_invariants : forall st (s : num_map unit) regset,
  good_bijection_state st regset ->
  good_bijection_state (foldi (fun r v acc => find_bijection_step acc r) 0 st s) (domain s UNION regset).
Proof.
  intros st s regset H. rewrite foldi_FOLDR_toAList.
  replace (FOLDR (fun p acc => find_bijection_step acc (fst p)) st (toAList s))
    with (FOLDR (fun r acc => find_bijection_step acc r) st (MAP fst (toAList s)))
    by (induction (toAList s) as [|[k v] t IHt]; cbn; [reflexivity|rewrite IHt; reflexivity]).
  rewrite <- set_MAP_FST_toAList_eq_domain. apply FOLDR_find_bijection_invariants, H.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "in_clash_tree_set_eq" *)
Theorem in_clash_tree_set_eq :
  (forall w r, in_clash_tree (Delta w r) = set w UNION set r) /\
  (forall names, in_clash_tree (Set_ names) = domain names) /\
  (forall name_opt t1 t2,
    in_clash_tree (reg_alloc.Branch name_opt t1 t2) =
    match name_opt with
    | SOME names => domain names UNION in_clash_tree t1 UNION in_clash_tree t2
    | NONE => in_clash_tree t1 UNION in_clash_tree t2
    end) /\
  (forall t1 t2, in_clash_tree (reg_alloc.Seq t1 t2) = in_clash_tree t1 UNION in_clash_tree t2).
Proof.
  repeat split; intros; apply set_eq_iff; intros x; cbn [in_clash_tree]; sets.
  - rewrite !MEM_set. reflexivity.
  - destruct name_opt; cbv beta; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "find_bijection_clash_tree_invariants" *)
Theorem find_bijection_clash_tree_invariants : forall st ct regset,
  good_bijection_state st regset ->
  good_bijection_state (find_bijection_clash_tree st ct) (in_clash_tree ct UNION regset).
Proof.
  intros st ct; revert st; induction ct as [w r|names|[names|] t1 IH1 t2 IH2|t1 IH1 t2 IH2];
    intros st regset H; cbn [find_bijection_clash_tree]; destruct in_clash_tree_set_eq as (E1 & E2 & E3 & E4).
  - rewrite E1. replace (set w UNION set r UNION regset) with (set w UNION (set r UNION regset)).
    + apply FOLDL_find_bijection_invariants, FOLDL_find_bijection_invariants, H.
    + apply set_eq_iff; intros x; sets; tauto.
  - rewrite E2. apply foldi_find_bijection_invariants, H.
  - rewrite E3. replace (domain names UNION in_clash_tree t1 UNION in_clash_tree t2 UNION regset)
      with (domain names UNION (in_clash_tree t2 UNION (in_clash_tree t1 UNION regset))).
    + apply foldi_find_bijection_invariants, IH2, IH1, H.
    + apply set_eq_iff; intros x; sets; tauto.
  - rewrite E3. replace (in_clash_tree t1 UNION in_clash_tree t2 UNION regset)
      with (in_clash_tree t2 UNION (in_clash_tree t1 UNION regset)).
    + apply IH2, IH1, H.
    + apply set_eq_iff; intros x; sets; tauto.
  - rewrite E4. replace (in_clash_tree t1 UNION in_clash_tree t2 UNION regset)
      with (in_clash_tree t2 UNION (in_clash_tree t1 UNION regset)).
    + apply IH2, IH1, H.
    + apply set_eq_iff; intros x; sets; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "find_bijection_init_invariants" *)
Theorem find_bijection_init_invariants : good_bijection_state find_bijection_init {}.
Proof.
  assert (Hl : forall r, lookup r (@LN N) = None) by (intros r; destruct r; reflexivity).
  assert (Hd : forall r, ~ r IN domain (@LN N)) by (intros r H; apply dom_iff in H; apply H, Hl).
  unfold good_bijection_state, find_bijection_init; cbn [bij invbij nstack nalloc nmax].
  split; [apply set_eq_iff; intros x; split; [intros []|intros H; exact (Hd x H)]|].
  split; [split; intros m fm E; rewrite Hl in E; discriminate|].
  split; [split; [|split]; intros x Hx; exfalso; try destruct Hx as [Hx _]; exact Hx|].
  split; [intros x [Hx _]; exfalso; exact (Hd x Hx)|].
  split; [intros x [Hx _]; exfalso; exact (Hd x Hx)|].
  split; [split; reflexivity|].
  intros r. rewrite Hl. cbn. lia.
Qed.

(** ** The monadic interval computation *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "sptree_eq_list_def" *)
Definition sptree_eq_list (s : num_map Z) (l : list Z) : Prop :=
  forall i, i < LENGTH l ->
    ((0 < EL i l)%Z <-> lookup i s = None) /\ ((EL i l <= 0)%Z <-> lookup i s = Some (EL i l)).

(** Galette-only: HOL's [sth with int_beg := x] and [sth with int_end := x]. *)
Definition with_int_beg (sth : linear_scan_hidden_state) x : linear_scan_hidden_state :=
  {| colors := sth.(colors); int_beg := x; int_end := sth.(int_end);
     sorted_regs := sth.(sorted_regs); sorted_moves := sth.(sorted_moves) |}.
Definition with_int_end (sth : linear_scan_hidden_state) x : linear_scan_hidden_state :=
  {| colors := sth.(colors); int_beg := sth.(int_beg); int_end := x;
     sorted_regs := sth.(sorted_regs); sorted_moves := sth.(sorted_moves) |}.

Lemma sptree_eq_list_update s l r v :
  sptree_eq_list s l -> (v <= 0)%Z -> r < LENGTH l -> sptree_eq_list (insert r v s) (LUPDATE v r l).
Proof.
  intros H Hv Hr i Hi. rewrite LENGTH_LUPDATE in Hi. rewrite EL_LUPDATE, lookup_insert.
  destruct (decide (i = r)) as [->|Hne].
  - rewrite N.eqb_refl. destruct (N.ltb_spec r (LENGTH l)); [|lia]. cbn [andb].
    split; split; intros X; try lia; try discriminate; try reflexivity.
  - destruct (N.eqb_spec i r); [contradiction|]. cbn [andb]. apply H, Hi.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "numset_list_add_if_lt_monad_correct" *)
Theorem numset_list_add_if_lt_monad_correct : forall int_beg0 sth l v,
  (v <= 0)%Z /\ sptree_eq_list int_beg0 sth.(int_beg) /\
  EVERY (fun r => r <? LENGTH sth.(int_beg)) l ->
  exists sthout, numset_list_add_if_lt_monad l v sth = (M_success tt, sthout) /\
    sptree_eq_list (numset_list_add_if_lt l v int_beg0) sthout.(int_beg) /\
    sthout = with_int_beg sth sthout.(int_beg) /\
    LENGTH sthout.(int_beg) = LENGTH sth.(int_beg).
Proof.
  intros int_beg0 sth l; revert int_beg0 sth; induction l as [|r l IH]; intros s0 sth v (Hv & Hs & He).
  - exists sth. split; [reflexivity|split; [exact Hs|split; [destruct sth; reflexivity|reflexivity]]].
  - cbn [EVERY] in He. unfold is_true in He. apply andb_prop in He as [Hr He]. apply N.ltb_lt in Hr.
    cbn [numset_list_add_if_lt_monad]. msimp. rewrite int_beg_sub_eqn. destruct (N.ltb_spec r (LENGTH (int_beg sth))); [|lia].
    cbv beta iota. unfold numset_list_add_if_lt. cbn [numset_list_add_if]. fold (numset_list_add_if_lt l v).
    destruct (Hs r Hr) as [H1 H2].
    set (sth1 := {| colors := colors sth; int_beg := LUPDATE v r (int_beg sth); int_end := int_end sth;
                    sorted_regs := sorted_regs sth; sorted_moves := sorted_moves sth |}).
    assert (U : forall s, sptree_eq_list s (int_beg sth) ->
              (exists sthout, numset_list_add_if_lt_monad l v sth1 = (M_success tt, sthout) /\
                 sptree_eq_list (numset_list_add_if_lt l v (insert r v s)) (int_beg sthout) /\
                 sthout = with_int_beg sth (int_beg sthout) /\ LENGTH (int_beg sthout) = LENGTH (int_beg sth))).
    { intros s Hss. destruct (IH (insert r v s) sth1 v) as (so & E & Hso & Eso & Lso).
      { split; [exact Hv|split; [apply sptree_eq_list_update; auto|]].
        cbn [int_beg sth1]. rewrite LENGTH_LUPDATE. exact He. }
      exists so. split; [exact E|split; [exact Hso|split]].
      - rewrite Eso at 1. reflexivity.
      - rewrite Lso. cbn [int_beg sth1]. apply LENGTH_LUPDATE. }
    destruct (Z.ltb_spec 0 (EL r (int_beg sth))) as [Hp|Hp].
    + rewrite update_int_beg_eqn. destruct (N.ltb_spec r (LENGTH (int_beg sth))); [|lia]. cbv beta iota.
      rewrite (proj1 H1 Hp). fold sth1. apply U, Hs.
    + rewrite (proj1 H2 Hp). cbn [Z.leb]. destruct (Z.leb_spec v (EL r (int_beg sth))) as [Hle|Hgt].
      * rewrite update_int_beg_eqn. destruct (N.ltb_spec r (LENGTH (int_beg sth))); [|lia]. cbv beta iota.
        fold sth1. apply U, Hs.
      * apply (IH s0 sth v). split; [exact Hv|split; [exact Hs|exact He]].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "numset_list_add_if_gt_monad_correct" *)
Theorem numset_list_add_if_gt_monad_correct : forall int_end0 sth l v,
  (v <= 0)%Z /\ sptree_eq_list int_end0 sth.(int_end) /\
  EVERY (fun r => r <? LENGTH sth.(int_end)) l ->
  exists sthout, numset_list_add_if_gt_monad l v sth = (M_success tt, sthout) /\
    sptree_eq_list (numset_list_add_if_gt l v int_end0) sthout.(int_end) /\
    sthout = with_int_end sth sthout.(int_end) /\
    LENGTH sthout.(int_end) = LENGTH sth.(int_end).
Proof.
  intros int_end0 sth l; revert int_end0 sth; induction l as [|r l IH]; intros s0 sth v (Hv & Hs & He).
  - exists sth. split; [reflexivity|split; [exact Hs|split; [destruct sth; reflexivity|reflexivity]]].
  - cbn [EVERY] in He. unfold is_true in He. apply andb_prop in He as [Hr He]. apply N.ltb_lt in Hr.
    cbn [numset_list_add_if_gt_monad]. msimp. rewrite int_end_sub_eqn. destruct (N.ltb_spec r (LENGTH (int_end sth))); [|lia].
    cbv beta iota. unfold numset_list_add_if_gt. cbn [numset_list_add_if]. fold (numset_list_add_if_gt l v).
    destruct (Hs r Hr) as [H1 H2].
    set (sth1 := {| colors := colors sth; int_beg := int_beg sth; int_end := LUPDATE v r (int_end sth);
                    sorted_regs := sorted_regs sth; sorted_moves := sorted_moves sth |}).
    assert (U : forall s, sptree_eq_list s (int_end sth) ->
              (exists sthout, numset_list_add_if_gt_monad l v sth1 = (M_success tt, sthout) /\
                 sptree_eq_list (numset_list_add_if_gt l v (insert r v s)) (int_end sthout) /\
                 sthout = with_int_end sth (int_end sthout) /\ LENGTH (int_end sthout) = LENGTH (int_end sth))).
    { intros s Hss. destruct (IH (insert r v s) sth1 v) as (so & E & Hso & Eso & Lso).
      { split; [exact Hv|split; [apply sptree_eq_list_update; auto|]].
        cbn [int_end sth1]. rewrite LENGTH_LUPDATE. exact He. }
      exists so. split; [exact E|split; [exact Hso|split]].
      - rewrite Eso at 1. reflexivity.
      - rewrite Lso. cbn [int_end sth1]. apply LENGTH_LUPDATE. }
    destruct (Z.ltb_spec 0 (EL r (int_end sth))) as [Hp|Hp].
    + rewrite update_int_end_eqn. destruct (N.ltb_spec r (LENGTH (int_end sth))); [|lia]. cbv beta iota.
      rewrite (proj1 H1 Hp). fold sth1. apply U, Hs.
    + rewrite (proj1 H2 Hp). cbn [Z.leb]. destruct (Z.leb_spec (EL r (int_end sth)) v) as [Hle|Hgt].
      * rewrite update_int_end_eqn. destruct (N.ltb_spec r (LENGTH (int_end sth))); [|lia]. cbv beta iota.
        fold sth1. apply U, Hs.
      * apply (IH s0 sth v). split; [exact Hv|split; [exact Hs|exact He]].
Qed.

Lemma EVERY_lt_iff (l : list N) n : is_true (EVERY (fun r => r <? n) l) <-> forall r, In r l -> r < n.
Proof. rewrite EVERY_iff. split; intros H r Hr; [apply N.ltb_lt, H, Hr|apply N.ltb_lt, H, Hr]. Qed.

Lemma In_MAP_FST_toAList {A} (s : num_map A) r : In r (MAP fst (toAList s)) <-> r IN domain s.
Proof. rewrite <- IN_set. change (MAP fst (toAList s)) with (MAP FST (toAList s)). rewrite set_MAP_FST_toAList_eq_domain. reflexivity. Qed.

Lemma with_ie_ib_eq (s sth : linear_scan_hidden_state) :
  colors s = colors sth -> sorted_regs s = sorted_regs sth -> sorted_moves s = sorted_moves sth ->
  s = with_int_end (with_int_beg sth (int_beg s)) (int_end s).
Proof. destruct s, sth; cbn; intros -> -> ->; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_ct_monad_aux_correct" *)
Theorem get_intervals_ct_monad_aux_correct : forall ct sth live n int_beg0 int_end0 nout int_begout int_endout liveout,
  (n <= 0)%Z /\
  sptree_eq_list int_beg0 sth.(int_beg) /\
  sptree_eq_list int_end0 sth.(int_end) /\
  get_intervals_ct_aux ct n int_beg0 int_end0 live = (nout, (int_begout, (int_endout, liveout))) /\
  LENGTH sth.(int_end) = LENGTH sth.(int_beg) /\
  (forall r, in_clash_tree ct r -> r < LENGTH sth.(int_beg)) /\
  (forall r, r IN domain live -> r < LENGTH sth.(int_beg)) ->
  exists sthout, get_intervals_ct_monad_aux ct n live sth = (M_success (nout, liveout), sthout) /\
    sptree_eq_list int_begout sthout.(int_beg) /\
    sptree_eq_list int_endout sthout.(int_end) /\
    LENGTH sthout.(int_beg) = LENGTH sth.(int_beg) /\
    LENGTH sthout.(int_end) = LENGTH sth.(int_end) /\
    (forall r, r IN domain liveout -> r < LENGTH sth.(int_beg)) /\
    sthout = with_int_end (with_int_beg sth sthout.(int_beg)) sthout.(int_end) /\
    (nout <= 0)%Z.
Proof.
  induction ct as [wr rd|cutset|optcutset ct1 IH1 ct2 IH2|ct1 IH1 ct2 IH2];
    intros sth live n ib ie nout ibo ieo lo (Hn & Hb & He & Eg & Hl & Hct & Hlive); cbn [get_intervals_ct_aux] in Eg.
  - injection Eg as <- <- <- <-. cbn [get_intervals_ct_monad_aux]. msimp.
    cbn [in_clash_tree] in Hct.
    assert (Hw : forall r, In r wr -> r < LENGTH (int_beg sth)) by (intros r Hr; apply Hct; left; apply MEM_iff, Hr).
    assert (Hr : forall r, In r rd -> r < LENGTH (int_beg sth)) by (intros r Hr; apply Hct; right; apply MEM_iff, Hr).
    destruct (numset_list_add_if_lt_monad_correct ib sth wr n) as (s1 & E1 & B1 & Q1 & L1).
    { split; [exact Hn|split; [exact Hb|apply EVERY_lt_iff, Hw]]. }
    rewrite E1. cbv beta iota.
    destruct (numset_list_add_if_gt_monad_correct ie s1 wr n) as (s2 & E2 & B2 & Q2 & L2).
    { split; [exact Hn|split; [rewrite Q1; exact He|]]. apply EVERY_lt_iff. rewrite Q1; cbn; rewrite Hl; exact Hw. }
    rewrite E2. cbv beta iota.
    destruct (numset_list_add_if_gt_monad_correct (numset_list_add_if_gt wr n ie) s2 rd (n - 1)%Z) as (s3 & E3 & B3 & Q3 & L3).
    { split; [lia|split; [exact B2|]]. apply EVERY_lt_iff. rewrite L2, Q1; cbn; rewrite Hl; exact Hr. }
    rewrite E3. cbv beta iota. exists s3.
    assert (Eb3 : int_beg s3 = int_beg s1) by (rewrite Q3, Q2; reflexivity).
    split; [reflexivity|]. split; [rewrite Eb3; exact B1|]. split; [exact B3|].
    split; [rewrite Eb3; exact L1|]. split; [rewrite L3, L2, Q1; reflexivity|]. split.
    + intros r Hr'. rewrite domain_numset_list_insert in Hr'. destruct Hr' as [Hr'|Hr']; [apply Hr, IN_set, Hr'|].
      rewrite domain_numset_list_delete in Hr'. destruct Hr' as [Hr' _]. apply Hlive, Hr'.
    + split; [|lia]. apply with_ie_ib_eq; rewrite Q3; cbn; rewrite Q2; cbn; rewrite Q1; reflexivity.
  - injection Eg as <- <- <- <-. cbn [get_intervals_ct_monad_aux]. msimp.
    cbn [in_clash_tree] in Hct.
    destruct (numset_list_add_if_gt_monad_correct ie sth (MAP fst (toAList cutset)) n) as (s1 & E1 & B1 & Q1 & L1).
    { split; [exact Hn|split; [exact He|]]. apply EVERY_lt_iff. rewrite Hl. intros r Hr; apply Hct, In_MAP_FST_toAList, Hr. }
    rewrite E1. cbv beta iota. exists s1.
    split; [reflexivity|]. split; [rewrite Q1; exact Hb|]. split; [exact B1|].
    split; [rewrite Q1; reflexivity|]. split; [exact L1|]. split.
    + intros r Hr'. unfold pred_set.IN in Hr'. rewrite domain_union in Hr'. destruct Hr' as [Hr'|Hr']; [apply Hct, Hr'|apply Hlive, Hr'].
    + split; [|lia]. apply with_ie_ib_eq; rewrite Q1; reflexivity.
  - destruct (get_intervals_ct_aux ct2 n ib ie live) as [n2 [ib2 [ie2 l2]]] eqn:G2.
    destruct (get_intervals_ct_aux ct1 n2 ib2 ie2 live) as [n1 [ib1 [ie1 l1]]] eqn:G1.
    cbn [in_clash_tree] in Hct.
    destruct (IH2 sth live n ib ie n2 ib2 ie2 l2) as (s2 & E2 & B2 & C2 & LB2 & LE2 & D2 & Q2 & N2).
    { split; [exact Hn|split; [exact Hb|split; [exact He|split; [exact G2|split; [exact Hl|split; [|exact Hlive]]]]]].
      intros r Hr; apply Hct; right; left; exact Hr. }
    destruct (IH1 s2 live n2 ib2 ie2 n1 ib1 ie1 l1) as (s1 & E1 & B1 & C1 & LB1 & LE1 & D1 & Q1 & N1).
    { split; [exact N2|split; [exact B2|split; [exact C2|split; [exact G1|split; [rewrite LE2, LB2; exact Hl|split]]]]].
      - intros r Hr; rewrite LB2. apply Hct; left; exact Hr.
      - intros r Hr; rewrite LB2. apply Hlive, Hr. }
    cbn [get_intervals_ct_monad_aux]. msimp. rewrite E2. cbv beta iota. rewrite E1. cbv beta iota.
    destruct optcutset as [cutset|].
    + injection Eg as <- <- <- <-.
      destruct (numset_list_add_if_gt_monad_correct ie1 s1 (MAP fst (toAList cutset)) n1) as (s0 & E0 & B0 & Q0 & L0).
      { split; [exact N1|split; [exact C1|]]. apply EVERY_lt_iff. rewrite LE1, LE2, Hl. intros r Hr; apply Hct; right; right; apply In_MAP_FST_toAList, Hr. }
      msimp. rewrite E0. cbv beta iota. exists s0.
      split; [reflexivity|]. split; [rewrite Q0; exact B1|]. split; [exact B0|].
      split; [rewrite Q0; cbn; rewrite LB1; exact LB2|]. split; [rewrite L0, LE1; exact LE2|]. split.
      * intros r Hr'. unfold pred_set.IN in Hr'. rewrite !domain_union in Hr'.
        destruct Hr' as [Hr'|[Hr'|Hr']]; [apply Hct; right; right; exact Hr'|rewrite <- LB2; apply D1, Hr'|apply D2, Hr'].
      * split; [|lia]. apply with_ie_ib_eq; rewrite Q0; cbn; rewrite Q1; cbn; rewrite Q2; reflexivity.
    + injection Eg as <- <- <- <-. exists s1.
      split; [reflexivity|]. split; [exact B1|]. split; [exact C1|].
      split; [rewrite LB1; exact LB2|]. split; [rewrite LE1; exact LE2|]. split.
      * intros r Hr'. unfold pred_set.IN in Hr'. rewrite domain_union in Hr'.
        destruct Hr' as [Hr'|Hr']; [rewrite <- LB2; apply D1, Hr'|apply D2, Hr'].
      * split; [|exact N1]. apply with_ie_ib_eq; rewrite Q1; cbn; rewrite Q2; reflexivity.
  - destruct (get_intervals_ct_aux ct2 n ib ie live) as [n2 [ib2 [ie2 l2]]] eqn:G2.
    cbn [in_clash_tree] in Hct.
    destruct (IH2 sth live n ib ie n2 ib2 ie2 l2) as (s2 & E2 & B2 & C2 & LB2 & LE2 & D2 & Q2 & N2).
    { split; [exact Hn|split; [exact Hb|split; [exact He|split; [exact G2|split; [exact Hl|split; [|exact Hlive]]]]]].
      intros r Hr; apply Hct; right; exact Hr. }
    destruct (IH1 s2 l2 n2 ib2 ie2 nout ibo ieo lo) as (s1 & E1 & B1 & C1 & LB1 & LE1 & D1 & Q1 & N1).
    { split; [exact N2|split; [exact B2|split; [exact C2|split; [exact Eg|split; [rewrite LE2, LB2; exact Hl|split]]]]].
      - intros r Hr; rewrite LB2. apply Hct; left; exact Hr.
      - intros r Hr; rewrite LB2. apply D2, Hr. }
    cbn [get_intervals_ct_monad_aux]. msimp. rewrite E2. cbv beta iota. rewrite E1. exists s1.
    split; [reflexivity|]. split; [exact B1|]. split; [exact C1|].
    split; [rewrite LB1; exact LB2|]. split; [rewrite LE1; exact LE2|]. split.
    + intros r Hr'. rewrite <- LB2. apply D1, Hr'.
    + split; [|exact N1]. apply with_ie_ib_eq; rewrite Q1; cbn; rewrite Q2; reflexivity.
Qed.

Lemma sptree_eq_list_LN (l : list Z) :
  (forall i, i < LENGTH l -> (0 < EL i l)%Z) -> sptree_eq_list LN l.
Proof.
  intros H i Hi. assert (E : lookup i (@LN Z) = None) by (destruct i; reflexivity). rewrite E.
  specialize (H i Hi). split; split; intros X; try lia; try reflexivity; discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_ct_monad_correct" *)
Theorem get_intervals_ct_monad_correct : forall ct sth n int_beg0 int_end0,
  (forall i, i < LENGTH sth.(int_beg) -> (0 < EL i sth.(int_beg))%Z) /\
  (forall i, i < LENGTH sth.(int_end) -> (0 < EL i sth.(int_end))%Z) /\
  get_intervals_ct ct = (n, (int_beg0, int_end0)) /\
  LENGTH sth.(int_end) = LENGTH sth.(int_beg) /\
  (forall r, in_clash_tree ct r -> r < LENGTH sth.(int_beg)) ->
  exists sthout, get_intervals_ct_monad ct sth = (M_success n, sthout) /\
    sptree_eq_list int_beg0 sthout.(int_beg) /\
    sptree_eq_list int_end0 sthout.(int_end) /\
    LENGTH sthout.(int_beg) = LENGTH sth.(int_beg) /\
    LENGTH sthout.(int_end) = LENGTH sth.(int_end) /\
    sthout = with_int_end (with_int_beg sth sthout.(int_beg)) sthout.(int_end).
Proof.
  intros ct sth n ib ie (Hpb & Hpe & Eg & Hl & Hct). unfold get_intervals_ct in Eg.
  destruct (get_intervals_ct_aux ct 0%Z LN LN LN) as [n1 [ib1 [ie1 live]]] eqn:G.
  injection Eg as <- <- <-.
  destruct (get_intervals_ct_monad_aux_correct ct sth LN 0%Z LN LN n1 ib1 ie1 live)
    as (s1 & E1 & B1 & C1 & LB1 & LE1 & D1 & Q1 & N1).
  { split; [lia|split; [apply sptree_eq_list_LN, Hpb|split; [apply sptree_eq_list_LN, Hpe|]]].
    split; [exact G|split; [exact Hl|split; [exact Hct|]]].
    intros r Hr. exfalso. apply dom_iff in Hr. apply Hr. destruct r; reflexivity. }
  unfold get_intervals_ct_monad. msimp. rewrite E1. cbv beta iota.
  destruct (numset_list_add_if_lt_monad_correct ib1 s1 (MAP fst (toAList live)) n1) as (s2 & E2 & B2 & Q2 & L2).
  { split; [exact N1|split; [exact B1|]]. apply EVERY_lt_iff. rewrite LB1. intros r Hr; apply D1, In_MAP_FST_toAList, Hr. }
  rewrite E2. cbv beta iota.
  destruct (numset_list_add_if_gt_monad_correct ie1 s2 (MAP fst (toAList live)) n1) as (s3 & E3 & B3 & Q3 & L3).
  { split; [exact N1|split; [rewrite Q2; exact C1|]]. apply EVERY_lt_iff. rewrite Q2; cbn [int_end with_int_beg].
    rewrite LE1, Hl. intros r Hr; apply D1, In_MAP_FST_toAList, Hr. }
  rewrite E3. cbv beta iota. exists s3.
  assert (Eb : int_beg s3 = int_beg s2) by (rewrite Q3; reflexivity).
  split; [reflexivity|]. split; [rewrite Eb; exact B2|]. split; [exact B3|].
  split; [rewrite Eb, L2; exact LB1|]. split; [rewrite L3, Q2; cbn; exact LE1|].
  apply with_ie_ib_eq; rewrite Q3; cbn; rewrite Q2; cbn; rewrite Q1; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "in_clash_tree_eq_live_tree_registers" *)
Theorem in_clash_tree_eq_live_tree_registers : forall ct r,
  in_clash_tree ct r <-> r IN live_tree_registers (get_live_tree ct).
Proof.
  induction ct as [wr rd|cutset|[cutset|] t1 IH1 t2 IH2|t1 IH1 t2 IH2]; intros r;
    cbn [in_clash_tree get_live_tree live_tree_registers]; sets.
  - rewrite !MEM_set. unfold pred_set.IN. tauto.
  - rewrite <- set_MAP_FST_toAList_eq_domain. reflexivity.
  - unfold pred_set.IN in *. rewrite IH1, IH2. change (MAP fst (toAList cutset)) with (MAP FST (toAList cutset)).
    rewrite set_MAP_FST_toAList_eq_domain. tauto.
  - unfold pred_set.IN in *. rewrite IH1, IH2. tauto.
  - unfold pred_set.IN in *. rewrite IH1, IH2. tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_live_backward_in_live_tree_registers" *)
Theorem get_live_backward_in_live_tree_registers : forall lt live,
  domain (get_live_backward lt live) SUBSET domain live UNION live_tree_registers lt.
Proof.
  unfold pred_set.SUBSET. induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2]; intros live x Hx;
    cbn [get_live_backward live_tree_registers] in *; sets.
  - rewrite domain_numset_list_delete in Hx. unfold pred_set.DIFF, pred_set.IN in Hx. tauto.
  - unfold pred_set.IN in Hx. rewrite domain_numset_list_insert in Hx. sets. tauto.
  - unfold pred_set.IN in Hx. rewrite domain_numset_list_insert in Hx.
    change (MAP fst (toAList (difference (get_live_backward lt2 live) (get_live_backward lt1 live))))
      with (MAP FST (toAList (difference (get_live_backward lt2 live) (get_live_backward lt1 live)))) in Hx.
    rewrite branch_domain in Hx. sets. unfold pred_set.IN in *.
    destruct Hx as [Hx|Hx]; [apply IH1 in Hx|apply IH2 in Hx]; sets; unfold pred_set.IN in *; tauto.
  - apply IH1 in Hx. sets. unfold pred_set.IN in *. destruct Hx as [Hx|Hx]; [apply IH2 in Hx; sets; unfold pred_set.IN in *|]; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "fix_domination_live_tree_registers" *)
Theorem fix_domination_live_tree_registers : forall lt,
  live_tree_registers (fix_domination lt) = live_tree_registers lt.
Proof.
  intros lt. unfold fix_domination. destruct (bool_decide _); [reflexivity|].
  cbn [live_tree_registers]. apply set_eq_iff; intros x; sets. split; [|tauto]. intros [Hx|Hx]; [|exact Hx].
  change (MAP fst (toAList (get_live_backward lt LN))) with (MAP FST (toAList (get_live_backward lt LN))) in Hx.
  unfold pred_set.IN in Hx. rewrite set_MAP_FST_toAList_eq_domain in Hx.
  pose proof (get_live_backward_in_live_tree_registers lt LN x Hx) as H. sets. unfold pred_set.IN in H.
  destruct H as [H|H]; [|exact H]. exfalso. apply dom_iff in H. apply H. destruct x; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_beg_less_end" *)
Theorem get_intervals_beg_less_end : forall lt n_in beg_in end_in n_out beg_out end_out,
  (forall r, r IN domain beg_in -> (the 0%Z (lookup r beg_in) <= the 0%Z (lookup r end_in))%Z) /\
  domain beg_in SUBSET domain end_in /\
  (n_out, (beg_out, end_out)) = get_intervals lt n_in beg_in end_in ->
  (forall r, r IN domain beg_out -> (the 0%Z (lookup r beg_out) <= the 0%Z (lookup r end_out))%Z) /\
  domain beg_out SUBSET domain end_out.
Proof.
  induction lt as [l|l|lt1 IH1 lt2 IH2|lt1 IH1 lt2 IH2]; intros n bi ei no bo eo (Hle & Hsub & Eg);
    cbn [get_intervals] in Eg.
  - injection Eg as -> -> ->. split.
    + intros r Hr. rewrite lookup_numset_list_add_if_lt, lookup_numset_list_add_if_gt.
      destruct (MEM r l) eqn:Em.
      * destruct (lookup r bi) as [b|] eqn:Eb.
        -- assert (Hd : r IN domain bi) by (apply dom_iff; congruence).
           specialize (Hle r Hd). pose proof (Hsub r Hd) as He. apply dom_iff in He.
           rewrite Eb in Hle. destruct (lookup r ei) as [e|]; [|congruence]. cbn in Hle.
           destruct (Z.leb_spec n b), (Z.leb_spec e n); cbn; lia.
        -- destruct (lookup r ei) as [e|]; [destruct (Z.leb_spec e n)|]; cbn; lia.
      * unfold pred_set.IN in Hr. rewrite domain_numset_list_add_if_lt in Hr. sets. unfold pred_set.IN in Hr.
        destruct Hr as [Hr|Hr]; [apply MEM_set in Hr; congruence|]. apply Hle, Hr.
    + intros x Hx. unfold pred_set.IN in *. rewrite domain_numset_list_add_if_lt in Hx. rewrite domain_numset_list_add_if_gt.
      sets. unfold pred_set.IN in *. destruct Hx as [Hx|Hx]; [left; exact Hx|right; apply Hsub, Hx].
  - injection Eg as -> -> ->. split.
    + intros r Hr. rewrite lookup_numset_list_add_if_gt. specialize (Hle r Hr).
      pose proof (Hsub r Hr) as He. apply dom_iff in He.
      destruct (MEM r l); [|exact Hle]. destruct (lookup r ei) as [e|]; [|congruence]. cbn in Hle.
      destruct (Z.leb_spec e n); cbn; lia.
    + intros x Hx. unfold pred_set.IN in *. rewrite domain_numset_list_add_if_gt. sets. unfold pred_set.IN in *.
      right; apply Hsub, Hx.
  - destruct (get_intervals lt2 n bi ei) as [n2 [b2 e2]] eqn:G2.
    destruct (IH2 n bi ei n2 b2 e2) as [H1 H2]; [split; [exact Hle|split; [exact Hsub|symmetry; exact G2]]|].
    apply (IH1 n2 b2 e2 no bo eo). split; [exact H1|split; [exact H2|exact Eg]].
  - destruct (get_intervals lt2 n bi ei) as [n2 [b2 e2]] eqn:G2.
    destruct (IH2 n bi ei n2 b2 e2) as [H1 H2]; [split; [exact Hle|split; [exact Hsub|symmetry; exact G2]]|].
    apply (IH1 n2 b2 e2 no bo eo). split; [exact H1|split; [exact H2|exact Eg]].
Qed.

(** ** Renaming clash trees *)

Lemma NoDup_map_inj_in {A B} (g : A -> B) l x y :
  NoDup (List.map g l) -> In x l -> In y l -> g x = g y -> x = y.
Proof.
  induction l as [|h l IH]; [intros _ []|]. cbn [List.map]. intros Hn Hx Hy E. inversion Hn as [|? ? Hh Hl]; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; auto.
  - exfalso; apply Hh. rewrite E. apply in_map, Hy.
  - exfalso; apply Hh. rewrite <- E. apply in_map, Hx.
Qed.

Lemma NoDup_map_of_inj {A B} (g : A -> B) l :
  NoDup l -> (forall x y, In x l -> In y l -> g x = g y -> x = y) -> NoDup (List.map g l).
Proof.
  induction l as [|h l IH]; intros Hn Hi; cbn [List.map]; [constructor|]. inversion Hn as [|? ? Hh Hl]; subst.
  constructor.
  - intros Hm. apply in_map_iff in Hm as (z & E & Hz). assert (z = h) by (apply Hi; [right; exact Hz|left; reflexivity|exact E]). subst. contradiction.
  - apply IH; [exact Hl|]. intros x y Hx Hy; apply Hi; right; assumption.
Qed.

Lemma keys_NoDup {A} (t : num_map A) : NoDup (MAP fst (toAList t)).
Proof. apply ALL_DISTINCT_NoDup_list, ALL_DISTINCT_MAP_FST_toAList. Qed.

Lemma domain_insert_keys (g : N -> N) (s : num_set) :
  domain (foldi (fun r _ acc => insert (g r) tt acc) 0 LN s) = IMAGE g (domain s).
Proof.
  rewrite foldi_FOLDR_toAList. rewrite <- (set_MAP_FST_toAList_eq_domain s).
  change (MAP FST (toAList s)) with (MAP fst (toAList s)).
  induction (toAList s) as [|[k v] t IH]; cbn [FOLDR MAP fst LIST_TO_SET].
  - apply set_eq_iff; intros x; split; [intros H; apply dom_iff in H; exfalso; apply H; destruct x; reflexivity|].
    intros (y & _ & []).
  - rewrite domain_insert, IH. apply set_eq_iff; intros x; unfold IMAGE, pred_set.IN; split.
    + intros [->|(y & -> & Hy)]; [exists k; split; [reflexivity|left; reflexivity]|exists y; split; [reflexivity|right; exact Hy]].
    + intros (y & -> & [->|Hy]); [left; reflexivity|right; exists y; split; [reflexivity|exact Hy]].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_col_apply_bijection" *)
Theorem check_col_apply_bijection : forall (bijdom bijcodom : N -> Prop) (appbij appinvbij : N -> N)
    (cutset : num_set) livein flivein f,
  (forall r, r IN bijdom -> appbij r IN bijcodom /\ appinvbij (appbij r) = r) /\
  (forall r, r IN bijcodom -> appinvbij r IN bijdom /\ appbij (appinvbij r) = r) /\
  domain cutset SUBSET bijdom /\
  check_col f (foldi (fun r _ acc => insert (appbij r) tt acc) 0 LN cutset) = SOME (livein, flivein) ->
  exists livein' flivein', check_col (fun r => f (appbij r)) cutset = SOME (livein', flivein') /\
    domain livein' = IMAGE appinvbij (domain livein).
Proof.
  intros bijdom bijcodom appbij appinvbij cutset livein flivein f (Hb & Hc & Hs & Hk).
  set (T := foldi (fun r _ acc => insert (appbij r) tt acc) 0 LN cutset) in *.
  assert (HT : domain T = IMAGE appbij (domain cutset)) by apply domain_insert_keys.
  unfold check_col in *. destruct (ALL_DISTINCT (MAP (fun x => f (FST x)) (toAList T))) eqn:Ed; [|discriminate].
  injection Hk as <- _.
  assert (Hinj : forall x y, x IN domain T -> y IN domain T -> f x = f y -> x = y).
  { intros x y Hx Hy E. apply ALL_DISTINCT_NoDup_list in Ed.
    rewrite <- (List.map_map fst f) in Ed.
    apply (NoDup_map_inj_in f (MAP fst (toAList T))); auto; apply In_MAP_FST_toAList; auto. }
  destruct (ALL_DISTINCT (MAP (fun x => f (appbij (FST x))) (toAList cutset))) eqn:Ed2.
  - eexists _, _. split; [reflexivity|].
    rewrite HT. apply set_eq_iff; intros x; unfold IMAGE, pred_set.IN; split.
    + intros Hx. exists (appbij x). split; [symmetry; apply (Hb x), Hs, Hx|exists x; split; [reflexivity|exact Hx]].
    + intros (y & -> & (z & -> & Hz)). rewrite (proj2 (Hb z (Hs z Hz))). exact Hz.
  - exfalso. apply Bool.not_true_iff_false in Ed2. apply Ed2, ALL_DISTINCT_NoDup_list.
    rewrite <- (List.map_map fst (fun r => f (appbij r))). apply NoDup_map_of_inj; [apply keys_NoDup|].
    intros x y Hx Hy E. apply In_MAP_FST_toAList in Hx, Hy.
    assert (Hx' : appbij x IN domain T) by (rewrite HT; exists x; split; [reflexivity|exact Hx]).
    assert (Hy' : appbij y IN domain T) by (rewrite HT; exists y; split; [reflexivity|exact Hy]).
    pose proof (Hinj _ _ Hx' Hy' E) as E2.
    rewrite <- (proj2 (Hb x (Hs x Hx))), <- (proj2 (Hb y (Hs y Hy))), E2. reflexivity.
Qed.

Lemma lookup_unit_cases (t : num_set) x : {lookup x t = Some tt /\ x IN domain t} + {lookup x t = None /\ ~ x IN domain t}.
Proof.
  destruct (lookup x t) as [[]|] eqn:E; [left|right]; split; auto; [apply dom_unit, E|rewrite dom_iff; tauto].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_partial_col_apply_bijection" *)
Theorem check_partial_col_apply_bijection : forall (bijdom bijcodom : N -> Prop) (appbij appinvbij : N -> N) f
    l (live flive live' flive' livein flivein : num_set),
  (forall r, r IN bijdom -> appbij r IN bijcodom /\ appinvbij (appbij r) = r) /\
  (forall r, r IN bijcodom -> appinvbij r IN bijdom /\ appbij (appinvbij r) = r) /\
  set l SUBSET bijdom /\
  domain live SUBSET bijcodom /\
  domain flive = IMAGE f (domain live) /\
  domain flive' = IMAGE (f ∘ appbij) (domain live') /\
  domain live' = IMAGE appinvbij (domain live) /\
  INJ f (domain live) UNIV /\
  check_partial_col f (MAP appbij l) live flive = SOME (livein, flivein) ->
  exists livein' flivein', check_partial_col (fun r => f (appbij r)) l live' flive' = SOME (livein', flivein') /\
    domain livein' = IMAGE appinvbij (domain livein).
Proof.
  intros bijdom bijcodom appbij appinvbij f l. induction l as [|h l IH];
    intros live flive live' flive' livein flivein (Hb & Hc & Hl & Hlv & Hf & Hf' & Hl' & Hi & Hk); cbn [MAP check_partial_col] in *.
  - injection Hk as <- <-. eexists _, _. split; [reflexivity|exact Hl'].
  - assert (Hh : h IN bijdom) by (apply Hl; left; reflexivity).
    assert (Hl2 : set l SUBSET bijdom) by (intros x Hx; apply Hl; right; exact Hx).
    assert (Hmem : appbij h IN domain live <-> h IN domain live').
    { rewrite Hl'. unfold IMAGE, pred_set.IN at 2. split.
      - intros H. exists (appbij h). split; [symmetry; apply (Hb h Hh)|exact H].
      - intros (y & -> & Hy). rewrite (proj2 (Hc y (Hlv y Hy))). exact Hy. }
    assert (Hff : domain flive' = domain flive).
    { rewrite Hf', Hf, Hl'. apply set_eq_iff; intros x; unfold IMAGE, pred_set.IN; split.
      - intros (y & -> & (z & -> & Hz)). exists z. split; [|exact Hz]. cbv beta. rewrite (proj2 (Hc z (Hlv z Hz))). reflexivity.
      - intros (y & -> & Hy). exists (appinvbij y). split; [cbv beta; rewrite (proj2 (Hc y (Hlv y Hy))); reflexivity|].
        exists y. split; [reflexivity|exact Hy]. }
    destruct (lookup_unit_cases live (appbij h)) as [[E1 D1]|[E1 D1]].
    + rewrite E1 in Hk. destruct (lookup_unit_cases live' h) as [[E2 _]|[_ D2]]; [|exfalso; apply D2, Hmem, D1].
      rewrite E2. apply (IH live flive live' flive' livein flivein).
      exact (conj Hb (conj Hc (conj Hl2 (conj Hlv (conj Hf (conj Hf' (conj Hl' (conj Hi Hk)))))))).
    + rewrite E1 in Hk. destruct (lookup_unit_cases live' h) as [[_ D2]|[E2 _]]; [exfalso; apply D1, Hmem, D2|].
      rewrite E2.
      destruct (lookup_unit_cases flive (f (appbij h))) as [[E3 _]|[E3 D3]]; [rewrite E3 in Hk; discriminate|].
      rewrite E3 in Hk.
      destruct (lookup_unit_cases flive' (f (appbij h))) as [[_ D4]|[E4 _]]; [exfalso; apply D3; rewrite <- Hff; exact D4|].
      rewrite E4.
      apply (IH (insert (appbij h) tt live) (insert (f (appbij h)) tt flive) (insert h tt live') (insert (f (appbij h)) tt flive')
               livein flivein).
      split; [exact Hb|split; [exact Hc|split; [exact Hl2|]]].
      split; [intros x Hx; unfold pred_set.IN in Hx; rewrite domain_insert in Hx; destruct Hx as [->|Hx]; [apply (Hb h Hh)|apply Hlv, Hx]|].
      split; [rewrite !domain_insert, Hf; apply set_eq_iff; intros x; unfold IMAGE, pred_set.IN; split;
              [intros [->|(y & -> & Hy)]; [exists (appbij h); split; [reflexivity|left; reflexivity]|exists y; split; [reflexivity|right; exact Hy]]
              |intros (y & -> & [->|Hy]); [left; reflexivity|right; exists y; split; [reflexivity|exact Hy]]]|].
      split; [rewrite !domain_insert, Hf'; apply set_eq_iff; intros x; unfold IMAGE, pred_set.IN; split;
              [intros [->|(y & -> & Hy)]; [exists h; split; [reflexivity|left; reflexivity]|exists y; split; [reflexivity|right; exact Hy]]
              |intros (y & -> & [->|Hy]); [left; reflexivity|right; exists y; split; [reflexivity|exact Hy]]]|].
      split; [rewrite !domain_insert, Hl'; apply set_eq_iff; intros x; unfold IMAGE, pred_set.IN; split;
              [intros [->|(y & -> & Hy)]; [exists (appbij h); split; [symmetry; apply (Hb h Hh)|left; reflexivity]|exists y; split; [reflexivity|right; exact Hy]]
              |intros (y & -> & [->|Hy]); [left; apply (Hb h Hh)|right; exists y; split; [reflexivity|exact Hy]]]|].
      split; [|exact Hk].
      rewrite INJ_UNIV in *. intros x y Hx Hy E. unfold pred_set.IN in Hx, Hy. rewrite domain_insert in Hx, Hy.
      destruct Hx as [->|Hx], Hy as [->|Hy]; auto.
      * exfalso. apply D3. rewrite Hf. exists y. split; [exact E|exact Hy].
      * exfalso. apply D3. rewrite Hf. exists x. split; [symmetry; exact E|exact Hx].
Qed.

Lemma check_col_fst {A} f (t : num_map A) v : check_col f t = SOME v -> FST v = t.
Proof. unfold check_col. destruct (ALL_DISTINCT _); [intros [= <-]; reflexivity|discriminate]. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_clash_tree_output_subset" *)
Theorem check_clash_tree_output_subset : forall f ct live flive livein flivein,
  check_clash_tree f ct live flive = SOME (livein, flivein) ->
  domain livein SUBSET domain live UNION in_clash_tree ct.
Proof.
  intros f ct; induction ct as [w r|t|topt t1 IH1 t2 IH2|t1 IH1 t2 IH2]; intros live flive livein flivein Hk x Hx;
    cbn [check_clash_tree in_clash_tree] in *; sets; unfold pred_set.IN in *.
  - destruct (check_partial_col f w live flive) as [v|]; [|discriminate].
    pose proof (check_partial_col_domain _ _ _ _ _ Hk) as D. cbn [FST] in D. rewrite D in Hx.
    sets. unfold pred_set.IN in Hx. rewrite domain_numset_list_delete in Hx. unfold pred_set.DIFF, pred_set.IN in Hx.
    destruct Hx as [Hx|[Hx _]]; [right; right; apply MEM_set, Hx|left; exact Hx].
  - pose proof (check_col_fst _ _ _ Hk) as E. cbn [FST] in E. subst. right; exact Hx.
  - destruct (check_clash_tree f t1 live flive) as [[o1 fo1]|] eqn:C1; [|discriminate].
    destruct (check_clash_tree f t2 live flive) as [[o2 fo2]|] eqn:C2; [|discriminate].
    pose proof (IH1 _ _ _ _ C1) as S1. pose proof (IH2 _ _ _ _ C2) as S2. unfold pred_set.SUBSET in S1, S2.
    destruct topt as [t|].
    + pose proof (check_col_fst _ _ _ Hk) as E. cbn [FST] in E. subst. right; right; right; exact Hx.
    + pose proof (check_partial_col_domain _ _ _ _ _ Hk) as D. cbn [FST] in D. rewrite D in Hx.
      change (MAP fst (toAList (difference o2 o1))) with (MAP FST (toAList (difference o2 o1))) in Hx.
      rewrite branch_domain in Hx. sets. unfold pred_set.IN in Hx.
      destruct Hx as [Hx|Hx]; [apply S1 in Hx|apply S2 in Hx]; sets; unfold pred_set.IN in Hx; tauto.
  - destruct (check_clash_tree f t2 live flive) as [[o2 fo2]|] eqn:C2; [|discriminate].
    pose proof (IH1 _ _ _ _ Hk x Hx) as S1. sets. unfold pred_set.IN in S1.
    destruct S1 as [S1|S1]; [|tauto]. pose proof (IH2 _ _ _ _ C2 x S1) as S2. sets. unfold pred_set.IN in S2. tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "domain_apply_bij_set" *)
Theorem domain_apply_bij_set : forall (s : num_set) bij,
  domain (foldi (fun r _ acc => insert (the 0 (lookup r bij)) tt acc) 0 LN s) =
  IMAGE (fun r => the 0 (lookup r bij)) (domain s).
Proof. intros s bij. apply domain_insert_keys. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "in_clash_tree_apply_bij" *)
Theorem in_clash_tree_apply_bij : forall bij ct,
  in_clash_tree ct SUBSET domain bij ->
  in_clash_tree (apply_bij_on_clash_tree ct bij) = IMAGE (fun r => the 0 (lookup r bij)) (in_clash_tree ct).
Proof.
  intros bij ct; induction ct as [w r|t|topt t1 IH1 t2 IH2|t1 IH1 t2 IH2]; intros Hs;
    cbn [apply_bij_on_clash_tree in_clash_tree] in *; apply set_eq_iff; intros x.
  - unfold IMAGE, pred_set.IN. rewrite !MEM_iff, !in_map_iff. split.
    + intros [(y & <- & Hy)|(y & <- & Hy)]; exists y; (split; [reflexivity|]); [left|right]; apply MEM_iff, Hy.
    + intros (y & -> & [Hy|Hy]); [left|right]; exists y; (split; [reflexivity|]); apply MEM_iff, Hy.
  - unfold pred_set.IN. rewrite domain_apply_bij_set. reflexivity.
  - assert (S1 : in_clash_tree t1 SUBSET domain bij) by (intros y Hy; apply Hs; left; exact Hy).
    assert (S2 : in_clash_tree t2 SUBSET domain bij) by (intros y Hy; apply Hs; right; left; exact Hy).
    rewrite (IH1 S1), (IH2 S2). destruct topt as [t|]; cbn [OPTION_MAP]; unfold IMAGE, pred_set.IN.
    + rewrite domain_apply_bij_set. unfold IMAGE, pred_set.IN. split.
      * intros [(y & -> & Hy)|[(y & -> & Hy)|(y & -> & Hy)]]; exists y; split; auto.
      * intros (y & -> & [Hy|[Hy|Hy]]); [left|right; left|right; right]; exists y; split; auto.
    + split.
      * intros [(y & -> & Hy)|[(y & -> & Hy)|[]]]; exists y; split; auto.
      * intros (y & -> & [Hy|[Hy|[]]]); [left|right; left]; exists y; split; auto.
  - assert (S1 : in_clash_tree t1 SUBSET domain bij) by (intros y Hy; apply Hs; left; exact Hy).
    assert (S2 : in_clash_tree t2 SUBSET domain bij) by (intros y Hy; apply Hs; right; exact Hy).
    rewrite (IH1 S1), (IH2 S2). unfold IMAGE, pred_set.IN. split.
    + intros [(y & -> & Hy)|(y & -> & Hy)]; exists y; split; auto.
    + intros (y & -> & [Hy|Hy]); [left|right]; exists y; split; auto.
Qed.

Lemma delete_image (g : N -> N) l (D : N -> Prop) (F : num_set) :
  domain F = IMAGE g D -> INJ g (set l UNION D) UNIV ->
  domain (numset_list_delete (MAP g l) F) = IMAGE g (D DIFF set l).
Proof.
  intros HF Hi. rewrite INJ_UNIV in Hi. rewrite domain_numset_list_delete, HF.
  apply set_eq_iff; intros x; unfold IMAGE, pred_set.DIFF, pred_set.IN; split.
  - intros ((y & -> & Hy) & Hn). exists y. split; [reflexivity|split; [exact Hy|]].
    intros Hyl. apply Hn. apply IN_set, in_map, IN_set, Hyl.
  - intros (y & -> & Hy & Hn). split; [exists y; split; [reflexivity|exact Hy]|].
    intros Hm. apply IN_set, in_map_iff in Hm as (z & E & Hz). apply IN_set in Hz.
    assert (z = y) by (apply Hi; [sets; left; exact Hz|sets; right; exact Hy|exact E]). subst. contradiction.
Qed.

Section BijApply.
Variables (bij invbij : num_map N).
Hypotheses (Hi1 : sp_inverts bij invbij) (Hi2 : sp_inverts invbij bij).
Local Abbreviation ab := (fun r => the 0 (lookup r bij)).
Local Abbreviation ai := (fun r => the 0 (lookup r invbij)).

Lemma Fab r : r IN domain bij -> ab r IN domain invbij /\ ai (ab r) = r.
Proof.
  intros H. apply dom_lookup in H as [v Hv]. cbv beta. rewrite Hv. cbn [the].
  pose proof (Hi1 _ _ Hv) as Hw. rewrite Hw. split; [apply dom_lookup; eauto|reflexivity].
Qed.

Lemma Fai r : r IN domain invbij -> ai r IN domain bij /\ ab (ai r) = r.
Proof.
  intros H. apply dom_lookup in H as [v Hv]. cbv beta. rewrite Hv. cbn [the].
  pose proof (Hi2 _ _ Hv) as Hw. rewrite Hw. split; [apply dom_lookup; eauto|reflexivity].
Qed.

Lemma inj_comp (f : N -> N) (live : num_set) (live' : num_set) :
  domain live SUBSET domain invbij -> domain live' = IMAGE ai (domain live) ->
  INJ f (domain live) UNIV -> INJ (fun r => f (ab r)) (domain live') UNIV.
Proof.
  intros Hs Hl Hi. rewrite INJ_UNIV in *. intros x y Hx Hy E. rewrite Hl in Hx, Hy.
  destruct Hx as (x' & -> & Hx), Hy as (y' & -> & Hy).
  rewrite (proj2 (Fai x' (Hs x' Hx))), (proj2 (Fai y' (Hs y' Hy))) in E.
  assert (x' = y') by (apply Hi; auto). subst. reflexivity.
Qed.

Lemma subset_codom (f : N -> N) ct (live flive livein flivein : num_set) :
  in_clash_tree ct SUBSET domain bij -> domain live SUBSET domain invbij ->
  check_clash_tree f (apply_bij_on_clash_tree ct bij) live flive = SOME (livein, flivein) ->
  domain livein SUBSET domain invbij.
Proof.
  intros Hct Hl Hk x Hx. apply check_clash_tree_output_subset in Hk. apply Hk in Hx. sets. unfold pred_set.IN in Hx.
  destruct Hx as [Hx|Hx]; [apply Hl, Hx|]. rewrite in_clash_tree_apply_bij in Hx by exact Hct.
  destruct Hx as (y & -> & Hy). apply (Fab y), Hct, Hy.
Qed.

End BijApply.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_clash_tree_apply_bijection" *)
Theorem check_clash_tree_apply_bijection : forall bij invbij f ct (live flive live' flive' livein flivein : num_set),
  sp_inverts bij invbij /\
  sp_inverts invbij bij /\
  in_clash_tree ct SUBSET domain bij /\
  domain live SUBSET domain invbij /\
  domain flive = IMAGE f (domain live) /\
  domain flive' = IMAGE (fun r => f (the 0 (lookup r bij))) (domain live') /\
  domain live' = IMAGE (fun r => the 0 (lookup r invbij)) (domain live) /\
  INJ f (domain live) UNIV /\
  check_clash_tree f (apply_bij_on_clash_tree ct bij) live flive = SOME (livein, flivein) ->
  exists livein' flivein', check_clash_tree (fun r => f (the 0 (lookup r bij))) ct live' flive' = SOME (livein', flivein') /\
    domain livein' = IMAGE (fun r => the 0 (lookup r invbij)) (domain livein).
Proof.
  intros bij invbij f ct. induction ct as [w r|t|topt t1 IH1 t2 IH2|t1 IH1 t2 IH2];
    intros live flive live' flive' livein flivein (Hi1 & Hi2 & Hct & Hlv & Hf & Hf' & Hl' & Hinj & Hk);
    cbn [apply_bij_on_clash_tree check_clash_tree] in Hk |- *.
  - (* Delta *)
    set (ab := fun r => the 0 (lookup r bij)) in *. set (ai := fun r => the 0 (lookup r invbij)) in *.
    assert (Fb : forall x, x IN domain bij -> ab x IN domain invbij /\ ai (ab x) = x) by (intros x Hx; apply (Fab bij invbij Hi1 x Hx)).
    assert (Fi : forall x, x IN domain invbij -> ai x IN domain bij /\ ab (ai x) = x) by (intros x Hx; apply (Fai bij invbij Hi2 x Hx)).
    assert (Hw : set w SUBSET domain bij) by (intros x Hx; apply Hct; left; apply MEM_set, Hx).
    assert (Hr : set r SUBSET domain bij) by (intros x Hx; apply Hct; right; apply MEM_set, Hx).
    destruct (check_partial_col f (MAP ab w) live flive) as [[v1 fv1]|] eqn:C1; [|discriminate].
    destruct (check_partial_col_apply_bijection (domain bij) (domain invbij) ab ai f w live flive live' flive' v1 fv1)
      as (w1 & fw1 & T1 & _).
    { repeat (split; [eassumption|]). exact C1. }
    match goal with |- context [check_partial_col ?g w live' flive'] =>
      replace (check_partial_col g w live' flive') with (Some (w1, fw1)) by (rewrite <- T1; reflexivity) end.
    cbv beta iota.
    pose proof (check_partial_col_success_INJ_lemma (MAP ab w) live flive f v1 fv1 (conj Hf (conj Hinj C1))) as Hu.
    rewrite INJ_UNIV in Hu.
    apply (check_partial_col_apply_bijection (domain bij) (domain invbij) ab ai f r
             (numset_list_delete (MAP ab w) live) (numset_list_delete (MAP f (MAP ab w)) flive)
             (numset_list_delete w live') (numset_list_delete (MAP (fun r => f (ab r)) w) flive') livein flivein).
    split; [exact Fb|split; [exact Fi|split; [exact Hr|]]].
    split; [intros x Hx; unfold pred_set.IN in Hx; rewrite domain_numset_list_delete in Hx; apply Hlv, Hx|].
    split; [rewrite (domain_numset_list_delete (MAP ab w) live); apply delete_image; [exact Hf|rewrite INJ_UNIV; exact Hu]|].
    split.
    { rewrite !domain_numset_list_delete. rewrite Hf'. apply set_eq_iff; intros x; unfold IMAGE, pred_set.DIFF, pred_set.IN; split.
      - intros ((y & -> & Hy) & Hn). exists y. split; [reflexivity|split; [exact Hy|]].
        intros Hyw. apply Hn. apply IN_set, (in_map (fun r => f (ab r))), IN_set, Hyw.
      - intros (y & -> & Hy & Hn). split; [exists y; split; [reflexivity|exact Hy]|].
        intros Hm. apply IN_set, in_map_iff in Hm as (z & E & Hz). apply IN_set in Hz.
        rewrite Hl' in Hy. destruct Hy as (y' & -> & Hy').
        assert (Ey : ab (ai y') = y') by (apply Fi, Hlv, Hy').
        rewrite Ey in E.
        assert (E2 : ab z = y') by (apply Hu; [sets; left; apply IN_set, in_map, IN_set, Hz|sets; right; exact Hy'|exact E]).
        apply Hn. rewrite <- E2. rewrite (proj2 (Fb z (Hw z Hz))). exact Hz. }
    split.
    { rewrite !domain_numset_list_delete, Hl'. apply set_eq_iff; intros x; unfold IMAGE, pred_set.DIFF, pred_set.IN; split.
      - intros ((y & -> & Hy) & Hn). exists y. split; [reflexivity|split; [exact Hy|]].
        intros Hm. apply IN_set, in_map_iff in Hm as (z & E & Hz). apply IN_set in Hz. apply Hn.
        rewrite <- E, (proj2 (Fb z (Hw z Hz))). exact Hz.
      - intros (y & -> & Hy & Hn). split; [exists y; split; [reflexivity|exact Hy]|].
        intros Hz. apply Hn. apply IN_set, in_map_iff. exists (ai y). split; [apply Fi, Hlv, Hy|apply IN_set, Hz]. }
    split; [rewrite INJ_UNIV in *; intros x y Hx Hy; unfold pred_set.IN in Hx, Hy; rewrite domain_numset_list_delete in Hx, Hy;
            apply Hinj; [apply Hx|apply Hy]|].
    exact Hk.
  - destruct (check_col_apply_bijection (domain bij) (domain invbij) (fun r => the 0 (lookup r bij))
                (fun r => the 0 (lookup r invbij)) t livein flivein f) as (l' & fl' & E & D).
    { split; [intros x Hx; apply (Fab bij invbij Hi1 x Hx)|split; [intros x Hx; apply (Fai bij invbij Hi2 x Hx)|]].
      split; [intros x Hx; apply Hct, Hx|exact Hk]. }
    exists l', fl'. split; [exact E|exact D].
  - (* Branch *)
    set (ab := fun r => the 0 (lookup r bij)) in *. set (ai := fun r => the 0 (lookup r invbij)) in *.
    assert (Fb : forall x, x IN domain bij -> ab x IN domain invbij /\ ai (ab x) = x) by (intros x Hx; apply (Fab bij invbij Hi1 x Hx)).
    assert (Fi : forall x, x IN domain invbij -> ai x IN domain bij /\ ab (ai x) = x) by (intros x Hx; apply (Fai bij invbij Hi2 x Hx)).
    assert (S1 : in_clash_tree t1 SUBSET domain bij) by (intros y Hy; apply Hct; left; exact Hy).
    assert (S2 : in_clash_tree t2 SUBSET domain bij) by (intros y Hy; apply Hct; right; left; exact Hy).
    destruct (check_clash_tree f (apply_bij_on_clash_tree t1 bij) live flive) as [[o1 fo1]|] eqn:C1; [|discriminate].
    destruct (check_clash_tree f (apply_bij_on_clash_tree t2 bij) live flive) as [[o2 fo2]|] eqn:C2; [|discriminate].
    destruct (IH1 live flive live' flive' o1 fo1) as (l1 & fl1 & T1 & D1).
    { repeat (split; [eassumption|]). exact C1. }
    destruct (IH2 live flive live' flive' o2 fo2) as (l2 & fl2 & T2 & D2).
    { repeat (split; [eassumption|]). exact C2. }
    match goal with |- context [check_clash_tree ?g t1 live' flive'] =>
      replace (check_clash_tree g t1 live' flive') with (Some (l1, fl1)) by (rewrite <- T1; reflexivity) end.
    match goal with |- context [check_clash_tree ?g t2 live' flive'] =>
      replace (check_clash_tree g t2 live' flive') with (Some (l2, fl2)) by (rewrite <- T2; reflexivity) end.
    cbv beta iota.
    destruct topt as [t|]; cbn [OPTION_MAP] in Hk.
    + destruct (check_col_apply_bijection (domain bij) (domain invbij) ab ai t livein flivein f) as (l' & fl' & E & D).
      { split; [exact Fb|split; [exact Fi|split; [intros x Hx; apply Hct; right; right; exact Hx|exact Hk]]]. }
      exists l', fl'. split; [exact E|exact D].
    + assert (Hinj' : INJ (fun r => f (ab r)) (domain live') UNIV) by (eapply inj_comp; eassumption).
      destruct (check_clash_tree_output f _ live flive o1 fo1 (conj Hf (conj Hinj C1))) as [Ho1 Hio1].
      destruct (check_clash_tree_output (fun r => f (ab r)) t1 live' flive' l1 fl1 (conj Hf' (conj Hinj' T1))) as [Hl1 Hil1].
      assert (Sb1 : domain o1 SUBSET domain invbij) by (eapply subset_codom; [exact Hi1|exact S1|exact Hlv|exact C1]).
      assert (Sb2 : domain o2 SUBSET domain invbij) by (eapply subset_codom; [exact Hi1|exact S2|exact Hlv|exact C2]).
      set (L := MAP fst (toAList (difference l2 l1))).
      assert (HL : forall x, In x L <-> x IN domain l2 /\ ~ x IN domain l1).
      { intros x. unfold L. rewrite In_MAP_FST_toAList. unfold pred_set.IN. rewrite domain_difference. reflexivity. }
      assert (HsetL : set (MAP ab L) UNION domain o1 = domain o1 UNION domain o2).
      { apply set_eq_iff; intros x. unfold pred_set.UNION. rewrite IN_set. split.
        - intros [Hx|Hx]; [|left; exact Hx]. apply in_map_iff in Hx as (y & <- & Hy). apply HL in Hy as [Hy2 Hy1].
          rewrite D2 in Hy2. destruct Hy2 as (z & -> & Hz). right. rewrite (proj2 (Fi z (Sb2 z Hz))). exact Hz.
        - intros [Hx|Hx]; [right; exact Hx|]. destruct (classic (x IN domain o1)) as [H1|H1]; [right; exact H1|left].
          apply in_map_iff. exists (ai x). split; [apply Fi, Sb2, Hx|]. apply HL. split.
          + rewrite D2. exists x. split; [reflexivity|exact Hx].
          + rewrite D1. intros (z & E & Hz). apply H1. rewrite <- (proj2 (Fi x (Sb2 x Hx))), E, (proj2 (Fi z (Sb1 z Hz))). exact Hz. }
      pose proof (check_partial_col_success_INJ_lemma _ o1 fo1 f livein flivein (conj Ho1 (conj Hio1 Hk))) as Hu.
      change (MAP fst (toAList (difference o2 o1))) with (MAP FST (toAList (difference o2 o1))) in Hu.
      rewrite branch_domain in Hu.
      destruct (check_partial_col_success (MAP ab L) o1 fo1 f) as (br & fbr & Eb & _).
      { split; [exact Ho1|]. rewrite HsetL. exact Hu. }
      assert (Dbr : domain br = domain livein).
      { pose proof (check_partial_col_domain _ _ _ _ _ Eb) as X. pose proof (check_partial_col_domain _ _ _ _ _ Hk) as Y.
        cbn [FST] in X, Y. rewrite X, Y, HsetL. change (MAP fst (toAList (difference o2 o1))) with (MAP FST (toAList (difference o2 o1))).
        symmetry; apply branch_domain. }
      destruct (check_partial_col_apply_bijection (domain bij) (domain invbij) ab ai f L o1 fo1 l1 fl1 br fbr)
        as (l' & fl' & E & D).
      { split; [exact Fb|split; [exact Fi|]]. split.
        - intros x Hx. apply IN_set, HL in Hx as [Hx _]. rewrite D2 in Hx. destruct Hx as (z & -> & Hz). apply Fi, Sb2, Hz.
        - split; [exact Sb1|split; [exact Ho1|split; [exact Hl1|split; [exact D1|split; [exact Hio1|exact Eb]]]]]. }
      exists l', fl'. split; [exact E|]. rewrite D, Dbr. reflexivity.
  - (* Seq *)
    set (ab := fun r => the 0 (lookup r bij)) in *. set (ai := fun r => the 0 (lookup r invbij)) in *.
    assert (S1 : in_clash_tree t1 SUBSET domain bij) by (intros y Hy; apply Hct; left; exact Hy).
    assert (S2 : in_clash_tree t2 SUBSET domain bij) by (intros y Hy; apply Hct; right; exact Hy).
    destruct (check_clash_tree f (apply_bij_on_clash_tree t2 bij) live flive) as [[o2 fo2]|] eqn:C2; [|discriminate].
    destruct (IH2 live flive live' flive' o2 fo2) as (l2 & fl2 & T2 & D2).
    { repeat (split; [eassumption|]). exact C2. }
    match goal with |- context [check_clash_tree ?g t2 live' flive'] =>
      replace (check_clash_tree g t2 live' flive') with (Some (l2, fl2)) by (rewrite <- T2; reflexivity) end.
    cbv beta iota.
    assert (Hinj' : INJ (fun r => f (ab r)) (domain live') UNIV) by (eapply inj_comp; eassumption).
    destruct (check_clash_tree_output f _ live flive o2 fo2 (conj Hf (conj Hinj C2))) as [Ho2 Hio2].
    destruct (check_clash_tree_output (fun r => f (ab r)) t2 live' flive' l2 fl2 (conj Hf' (conj Hinj' T2))) as [Hl2 Hil2].
    assert (Sb2 : domain o2 SUBSET domain invbij) by (eapply subset_codom; [exact Hi1|exact S2|exact Hlv|exact C2]).
    apply (IH1 o2 fo2 l2 fl2 livein flivein).
    repeat (split; [eassumption|]). exact Hk.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "extract_coloration_output" *)
Theorem extract_coloration_output : forall bij invbij sth l acc,
  sp_inverts bij invbij /\
  sp_inverts invbij bij /\
  EVERY (fun r => ⌜r IN domain invbij⌝) l /\
  EVERY (fun r => r <? LENGTH sth.(colors)) l ->
  exists col, extract_coloration invbij l acc sth = (M_success col, sth) /\
    (forall r, r IN domain bij ->
      if MEM (the 0 (lookup r bij)) l then
        lookup r col = SOME (EL (the 0 (lookup r bij)) sth.(colors))
      else
        lookup r col = lookup r acc) /\
    domain col SUBSET domain bij UNION domain acc.
Proof.
  intros bij invbij sth l; induction l as [|h l IH]; intros acc (Hi1 & Hi2 & Hd & Hl).
  - exists acc. split; [reflexivity|]. split; [intros r _; reflexivity|]. intros x Hx; sets; right; exact Hx.
  - cbn [EVERY] in Hd, Hl. unfold is_true in Hd, Hl. apply andb_prop in Hd as [Hh Hd]. apply andb_prop in Hl as [Hhl Hl].
    apply bool_decide_spec in Hh. apply N.ltb_lt in Hhl.
    cbn [extract_coloration]. msimp. rewrite colors_sub_eqn. destruct (N.ltb_spec h (LENGTH (colors sth))); [|lia].
    cbv beta iota.
    destruct (IH (insert (the 0 (lookup h invbij)) (EL h (colors sth)) acc)) as (col & E & H1 & H2);
      [split; [exact Hi1|split; [exact Hi2|split; [exact Hd|exact Hl]]]|].
    exists col. split; [exact E|]. split.
    + intros r Hr. pose proof (H1 r Hr) as X. destruct (Fab bij invbij Hi1 r Hr) as [_ Er]. cbv beta in Er.
      destruct (MEM (the 0 (lookup r bij)) (h :: l)) eqn:Em; destruct (MEM (the 0 (lookup r bij)) l) eqn:Em'.
      * exact X.
      * rewrite X, lookup_insert. apply MEM_iff in Em. destruct Em as [Eh|Em]; [|apply MEM_iff in Em; congruence].
        rewrite Eh, Er. destruct (decide (r = r)); [reflexivity|congruence].
      * exfalso. apply Bool.not_true_iff_false in Em. apply Em, MEM_iff. right. apply MEM_iff, Em'.
      * rewrite X, lookup_insert. destruct (decide (r = the 0 (lookup h invbij))) as [Eq|]; [|reflexivity].
        exfalso. apply Bool.not_true_iff_false in Em. apply Em, MEM_iff. left.
        rewrite Eq. symmetry. apply (Fai bij invbij Hi2 h Hh).
    + intros x Hx. apply H2 in Hx. sets. unfold pred_set.IN in *. destruct Hx as [Hx|Hx]; [left; exact Hx|].
      rewrite domain_insert in Hx. destruct Hx as [->|Hx]; [left; apply (Fai bij invbij Hi2 h Hh)|right; exact Hx].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "LENGTH_toAList" *)
Theorem LENGTH_toAList' : forall {A} (s : num_map A), LENGTH (toAList s) = size s.
Proof. intros A s. apply LENGTH_toAList. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_col_equal_col" *)
Theorem check_col_equal_col : forall {A} (s : num_map A) f1 f2,
  (forall r, r IN domain s -> f1 r = f2 r) ->
  check_col f1 s = check_col f2 s.
Proof.
  intros A s f1 f2 H. unfold check_col.
  replace (MAP (fun x => f1 (FST x)) (toAList s)) with (MAP (fun x => f2 (FST x)) (toAList s)); [reflexivity|].
  symmetry. apply map_ext_in. intros [k v] Hk. cbn. apply H. apply In_MAP_FST_toAList.
  apply (in_map fst) in Hk. exact Hk.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_partial_col_equal_col" *)
Theorem check_partial_col_equal_col : forall l live flive f1 f2,
  (forall r, MEM r l -> f1 r = f2 r) ->
  check_partial_col f1 l live flive = check_partial_col f2 l live flive.
Proof.
  induction l as [|h l IH]; intros live flive f1 f2 H; cbn [check_partial_col]; [reflexivity|].
  assert (Hh : f1 h = f2 h) by (apply H, MEM_iff; left; reflexivity).
  assert (Hl : forall r, MEM r l -> f1 r = f2 r) by (intros r Hr; apply H, MEM_iff; right; apply MEM_iff, Hr).
  rewrite Hh. destruct (lookup h live) as [[]|]; [apply IH, Hl|]. destruct (lookup (f2 h) flive) as [[]|]; [reflexivity|].
  apply IH, Hl.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "check_clash_tree_equal_col" *)
Theorem check_clash_tree_equal_col : forall f1 f2 ct live flive,
  (forall r, r IN in_clash_tree ct -> f1 r = f2 r) /\
  (forall r, r IN domain live -> f1 r = f2 r) ->
  check_clash_tree f1 ct live flive = check_clash_tree f2 ct live flive.
Proof.
  intros f1 f2 ct; induction ct as [w r|t|topt t1 IH1 t2 IH2|t1 IH1 t2 IH2]; intros live flive [Hc Hl];
    cbn [check_clash_tree].
  - assert (Hw : forall x, MEM x w -> f1 x = f2 x) by (intros x Hx; apply Hc; left; exact Hx).
    assert (Hr : forall x, MEM x r -> f1 x = f2 x) by (intros x Hx; apply Hc; right; exact Hx).
    rewrite (check_partial_col_equal_col w live flive f1 f2 Hw).
    destruct (check_partial_col f2 w live flive); [|reflexivity].
    replace (MAP f1 w) with (MAP f2 w) by (symmetry; apply map_ext_in; intros x Hx; apply Hw, MEM_iff, Hx).
    apply check_partial_col_equal_col, Hr.
  - apply check_col_equal_col. intros x Hx; apply Hc, Hx.
  - rewrite (IH1 live flive) by (split; [intros x Hx; apply Hc; left; exact Hx|exact Hl]).
    rewrite (IH2 live flive) by (split; [intros x Hx; apply Hc; right; left; exact Hx|exact Hl]).
    destruct (check_clash_tree f2 t1 live flive) as [[o1 fo1]|] eqn:C1; [|reflexivity].
    destruct (check_clash_tree f2 t2 live flive) as [[o2 fo2]|] eqn:C2; [|reflexivity].
    destruct topt as [t|].
    + apply check_col_equal_col. intros x Hx; apply Hc; right; right; exact Hx.
    + apply check_partial_col_equal_col. intros x Hx. apply MEM_iff, In_MAP_FST_toAList in Hx.
      unfold pred_set.IN in Hx. rewrite domain_difference in Hx. destruct Hx as [Hx _].
      pose proof (check_clash_tree_output_subset f2 t2 live flive o2 fo2 C2 x Hx) as S. sets. unfold pred_set.IN in S.
      destruct S as [S|S]; [apply Hl, S|apply Hc; right; left; exact S].
  - rewrite (IH2 live flive) by (split; [intros x Hx; apply Hc; right; exact Hx|exact Hl]).
    destruct (check_clash_tree f2 t2 live flive) as [[o2 fo2]|] eqn:C2; [|reflexivity].
    apply IH1. split; [intros x Hx; apply Hc; left; exact Hx|].
    intros x Hx. pose proof (check_clash_tree_output_subset f2 t2 live flive o2 fo2 C2 x Hx) as S. sets. unfold pred_set.IN in S.
    destruct S as [S|S]; [apply Hl, S|apply Hc; right; exact S].
Qed.
