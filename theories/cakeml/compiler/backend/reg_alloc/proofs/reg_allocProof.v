(** * CakeML [reg_allocProof]: correctness of the graph-colouring allocator

    A port of [compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml].
    The script is split along its own sections into
    [reg_allocProof/check_clash_tree.v] (clash trees, also used by
    [linear_scanProof]), [ra_state.v] (state invariants, array lemmas),
    [colouring.v] (the colouring steps and oracles), [graph.v] (the
    bijection and the graph functions), [mk_graph.v] ([mk_graph] and the
    clash-tree check), [conventions.v] (forced edges, tags, colour
    extraction, injectivity of [check_clash_tree]) and [heuristics.v] (the
    heuristic steps); this file holds the top-level theorems.

    HOL applies [EVERY] to non-computable predicates here; they are written
    [⌜P⌝] ([Classical.v]).

    Not ported: [case_eq_thms] (a list of HOL [case_eq] rewrite theorems,
    proof infrastructure with no Rocq counterpart) and HOL's local
    [domain_difference] (the same as [sptreeTheory.domain_difference]). *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.coretypes Require Import pair.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From Galette.cakeml.compiler.backend.reg_alloc.proofs.reg_allocProof Require Export
  check_clash_tree ra_state colouring graph mk_graph conventions heuristics.
Open Scope N_scope.
Open Scope monad_scope.

Lemma domain_LN_empty {A} x : ~ x IN domain (@LN A).
Proof. unfold pred_set.IN; cbn; tauto. Qed.

(** The top-most correctness theorem. *)
(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "do_reg_alloc_correct" *)
Theorem do_reg_alloc_correct : forall alg scost k moves ct forced fs st ta fa n,
  mk_bij ct = (ta, (fa, n)) ->
  st.(adj_ls) = REPLICATE n [] ->
  st.(node_tag) = REPLICATE n Atemp ->
  st.(degrees) = REPLICATE n 0 ->
  st.(dim) = n ->
  st.(simp_wl) = [] ->
  st.(spill_wl) = [] ->
  st.(freeze_wl) = [] ->
  st.(avail_moves_wl) = [] ->
  st.(unavail_moves_wl) = [] ->
  st.(coalesced) = REPLICATE n 0 ->
  st.(move_related) = REPLICATE n false ->
  EVERY (fun '(x, y) => ⌜in_clash_tree ct x /\ in_clash_tree ct y⌝) forced ->
  exists spcol st' livein flivein,
    do_reg_alloc alg scost k moves ct forced fs (ta, (fa, n)) st = (M_success spcol, st') /\
    check_clash_tree (sp_default spcol) ct LN LN = Some (livein, flivein) /\
    (forall x, in_clash_tree ct x ->
       x IN domain spcol /\
       (if is_phy_var x then sp_default spcol x = x DIV 2
        else if is_stack_var x then k <= sp_default spcol x
        else True)) /\
    (forall x, x IN domain spcol -> in_clash_tree ct x) /\
    EVERY (fun '(x, y) => ⌜sp_default spcol x = sp_default spcol y -> x = y⌝) forced.
Proof.
  intros alg scost k moves ct forced fs st ta fa n Hbij Ha Ht Hd Hdim Hs1 Hs2 Hs3 Hs4 Hs5 Hc Hm Hforced.
  unfold mk_bij in Hbij.
  destruct (mk_bij_aux ct (LN, (LN, 0))) as [ta' [fa' n']] eqn:Eb; injection Hbij as -> -> ->.
  pose proof (mk_bij_aux_domain _ _ _ _ _ _ _ Eb) as Hdom.
  destruct (mk_bij_aux_bij ct LN LN 0 ta fa n) as (Hi1 & Hi2 & Hdfa).
  { split; [exact Eb|split; [intros m fm H; discriminate|split; [intros m fm H; discriminate|]]].
    apply EXTENSION; intros z; split; [intros []|unfold pred_set.IN, count; lia]. }
  destruct (mk_bij_aux_wf ct LN LN 0 ta fa n) as [Wta Wfa]; [split; [exact Eb|split; reflexivity]|].
  assert (Hdom' : forall x, x IN domain ta <-> in_clash_tree ct x).
  { intros x; rewrite Hdom, IN_UNION; pose proof (domain_LN_empty (A:=N) x); unfold pred_set.IN at 2; tauto. }
  assert (Hcount : forall v, v IN domain fa <-> v < n) by (intros v; rewrite Hdfa; reflexivity).
  (* the bijection *)
  assert (Hta : forall x, in_clash_tree ct x -> exists v, lookup x ta = Some v /\ lookup v fa = Some x /\ v < n /\
                 sp_default ta x = v /\ sp_default fa v = x).
  { intros x Hx. apply Hdom', domain_lookup in Hx as [v Hv]. pose proof (Hi1 x v Hv) as Hv'.
    exists v; split; [exact Hv|split; [exact Hv'|split; [|unfold sp_default; rewrite Hv, Hv'; auto]]].
    apply Hcount, domain_lookup; eauto. }
  assert (Hfa : forall v, v < n -> exists x, lookup v fa = Some x /\ lookup x ta = Some v /\ in_clash_tree ct x).
  { intros v Hv. apply Hcount, domain_lookup in Hv as [x Hx]. pose proof (Hi2 v x Hx) as Hx'.
    exists x; split; [exact Hx|split; [exact Hx'|apply Hdom', domain_lookup; eauto]]. }
  (* the initial state *)
  assert (Hg0 : good_ra_state st).
  { unfold good_ra_state; rewrite Ha, Ht, Hd, Hdim, Hs1, Hs2, Hs3, Hs4, Hs5, Hc, Hm, !LENGTH_REPLICATE.
    do 5 (split; [reflexivity|]).
    split; [apply EVERY_lt_iff; intros v Hv; pose proof (In_REPLICATE _ _ _ Hv); subst v;
            destruct (N.eq_dec n 0) as [->|]; [destruct Hv|lia]|].
    split; [apply EVERY_iff; intros l Hl; apply In_REPLICATE in Hl; subst; reflexivity|].
    split; [apply EVERY_iff; intros l Hl; apply In_REPLICATE in Hl; subst; reflexivity|].
    do 5 (split; [reflexivity|]).
    intros x y (Hx & Hy & Hmem). rewrite LENGTH_REPLICATE in Hx.
    rewrite EL_REPLICATE in Hmem by exact Hx. discriminate. }
  subst n.
  (* mk_graph *)
  destruct (mk_graph_succeeds ct (sp_default ta) [] st) as (l1 & s1 & E1 & Hg1 & Hc1 & Hw1 & _ & _ & _ & Hsub1).
  { split; [exact Hg0|split; [|split; [|split; [intros x y (Hx & _); discriminate|split; reflexivity]]]].
    - intros x Hx; destruct (Hta x Hx) as (v & _ & _ & Hv & -> & _); exact Hv.
    - split.
      + intros x Hx; destruct (Hta x Hx) as (v & _ & _ & Hv & -> & _). unfold pred_set.IN, count.
        rewrite Ha, LENGTH_REPLICATE; lia.
      + intros x y [Hx Hy] E; destruct (Hta x Hx) as (v & Lx & Fx & _ & Dx & _), (Hta y Hy) as (w & Ly & Fy & _ & Dy & _).
        rewrite Dx, Dy in E; subst w; congruence. }
  wsubst Hw1. rs.
  (* extend_graph *)
  destruct (extend_graph_succeeds forced (sp_default ta) (with_adj_ls st t)) as (s2 & E2 & Hg2 & Hw2 & He2).
  { split; [exact Hg1|]. rs. rewrite EVERY_iff in Hforced. apply EVERY_iff; intros [x y] Hin.
    specialize (Hforced _ Hin); cbv beta iota in Hforced; apply bool_decide_iff in Hforced as [Hx Hy].
    destruct (Hta x Hx) as (v & _ & _ & Hv & -> & _), (Hta y Hy) as (w & _ & _ & Hw & -> & _).
    apply andb_iff; split; apply ltb_iff; assumption. }
  wsubst Hw2. rs.
  (* mk_tags *)
  destruct (mk_tags_succeeds (with_adj_ls (with_adj_ls st t) t0) (dim st) fs (sp_default fa)) as (s3 & E3 & Hg3 & Hw3 & Htag).
  { split; [exact Hg2|reflexivity]. }
  wsubst Hw3. rs.
  assert (Hinit : init_ra_state ct forced fs (ta, (fa, dim st)) st =
                  (M_success tt, with_node_tag (with_adj_ls (with_adj_ls st t) t0) t1)).
  { unfold init_ra_state; cbv iota beta. mstep E1. mstep E2. exact E3. }
  unfold do_reg_alloc; cbv iota beta. mstep Hinit. ret.
  set (s3 := with_node_tag (with_adj_ls (with_adj_ls st t) t0) t1) in *.
  (* filtering the moves *)
  destruct (st_ex_FILTER_full_consistency_ok k (MAP (update_move (sp_default ta)) moves) [] s3 Hg3) as (mv & E4 & Hmv).
  mstep' E4.
  destruct (do_alloc1_success s3 (if bool_decide (alg = Simple) then [] else mv) scost k) as (ls & s4 & E5 & Hg4 & Hsub4 & D4 & T4).
  { split; [exact Hg3|]. destruct (bool_decide (alg = Simple)); [reflexivity|].
    apply EVERY_moves_iff; intros p x y Hin. rewrite EVERY_iff in Hmv; specialize (Hmv _ Hin); cbv beta iota in Hmv.
    apply orb_iff in Hmv as [Hmv|Hmv]; [apply andb_iff in Hmv as [? ?]; split; apply ltb_iff; assumption|discriminate]. }
  mstep' E5. ret.
  (* no_clash after the allocation heuristics *)
  assert (Hnc4 : no_clash (adj_ls s4) (node_tag s4)).
  { intros x y (Hx & Hy & _). pose proof Hg4 as (L1 & L2 & _). rewrite T4. subst s3; rs.
    rewrite L1, D4 in Hx, Hy; rs.
    pose proof (Htag x _ (conj Hx eq_refl)) as Tx. pose proof (Htag y _ (conj Hy eq_refl)) as Ty.
    destruct (Hfa x Hx) as (a & Fa & _ & _). destruct (Hfa y Hy) as (b & Fb & _ & _).
    assert (Sa : sp_default fa x = a) by (unfold sp_default; rewrite Fa; reflexivity).
    assert (Sb : sp_default fa y = b) by (unfold sp_default; rewrite Fb; reflexivity).
    rewrite Sa in Tx; rewrite Sb in Ty.
    destruct (is_phy_var a) eqn:Pa; [|destruct (is_stack_var a); [rewrite Tx; exact I|destruct Tx as [-> | ->]; exact I]].
    destruct (is_phy_var b) eqn:Pb; [|destruct (is_stack_var b); [rewrite Ty; destruct (EL x t1); exact I|destruct Ty as [-> | ->]; destruct (EL x t1); exact I]].
    rewrite Tx, Ty. intros E.
    assert (a = b).
    { unfold is_phy_var in Pa, Pb; apply N.eqb_eq in Pa, Pb.
      rewrite (N.div_mod a 2), (N.div_mod b 2) by lia. rewrite Pa, Pb, E; reflexivity. }
    subst b. pose proof (Hi2 _ _ Fa) as Ha'. pose proof (Hi2 _ _ Fb) as Hb'. congruence. }
  (* assigning the colours *)
  set (mvs := resort_moves (moves_to_sp (MAP (update_move (sp_default ta)) moves) LN)).
  destruct (assign_Atemps_correct k ls (biased_pref mvs) s4) as (s5 & E6 & Hnc5 & Hg5 & Hw5 & Hna5 & Hun5).
  { split; [exact Hg4|split; [apply good_pref_biased_pref|exact Hnc4]]. }
  mstep E6. wsubst Hw5. rs.
  destruct (assign_Stemps_correct (with_node_tag s4 t2) k (neg_biased_pref k mvs)) as (s6 & E7 & Hnc6 & Hg6 & Hw6 & Hst6).
  { split; [exact Hg5|split; [exact Hnc5|apply good_neg_pref_neg_biased_pref]]. }
  mstep E7. wsubst Hw6. rs.
  set (s6 := with_node_tag (with_node_tag s4 t2) t3) in *.
  pose proof Hg6 as (L1' & L2' & _). subst s6; rs.
  assert (Hdim4 : dim s4 = dim st) by (rewrite D4; subst s3; rs; reflexivity).
  pose proof (extract_color_succeeds (with_node_tag (with_node_tag s4 t2) t3) ta) as E8.
  assert (HB : forall x y, lookup x ta = Some y -> y < dim (with_node_tag (with_node_tag s4 t2) t3)).
  { rs. intros x y Hxy. pose proof (Hi1 x y Hxy) as Hyx. rewrite Hdim4; apply Hcount, domain_lookup; eauto. }
  specialize (E8 (conj Hg6 (conj HB Wta))).
  mstep' E8.
  set (spcol := sptree.map (fun v => extract_tag (EL v t3)) ta).
  (* all tags are fixed now *)
  assert (Hfix : forall v, v < dim st -> exists c, EL v t3 = Fixed c).
  { intros v Hv. rewrite EVERY_iff in Hna5.
    assert (Hv2 : v < LENGTH t2) by (pose proof Hg5 as (_ & L2'' & _); rs; lia).
    pose proof (Hna5 _ (EL_In v t2 Hv2)) as Hn; apply bool_decide_iff in Hn.
    specialize (Hst6 v Hv2); apply ifdec in Hst6.
    destruct (decide (EL v t2 = Stemp)) as [E|E]; [destruct (proj1 Hst6 E) as (c & Hc' & _); eauto|].
    rewrite (proj2 Hst6 E). destruct (EL v t2); [eauto|congruence|congruence]. }
  set (col := fun f => if f <? LENGTH t3 then extract_tag (EL f t3) else 0).
  assert (Hcol : colouring_satisfactory col (adj_ls s4)).
  { apply no_clash_colouring_satisfactory; split; [exact Hnc6|split; [lia|]].
    apply EVERY_iff; intros tg Htg; apply In_EL in Htg as (v & Hv & ->). apply bool_decide_iff.
    destruct (Hfix v ltac:(lia)) as (c & ->); split; discriminate. }
  destruct (mk_graph_check_clash_tree ct (sp_default ta) [] st l1 (with_adj_ls st t) col LN LN) as (livein & flivein & C & _ & _).
  { split; [exact E1|split; [|split; [|split; [|split; [reflexivity|split; [reflexivity|split; [intros x y (Hx & _); discriminate|split; [exact Hg0|]]]]]]]].
    - apply (colouring_satisfactory_subgraph _ _ (adj_ls s4)); split; [exact Hcol|]. rs.
      intros a b Hab; apply Hsub4; subst s3; rs. apply He2; right; right; exact Hab.
    - split.
      + intros x Hx; rewrite IN_UNION in Hx; destruct Hx as [Hx|Hx]; [|destruct (domain_LN_empty x Hx)].
        destruct (Hta x Hx) as (v & _ & _ & Hv & -> & _). unfold pred_set.IN, count. rewrite Ha, LENGTH_REPLICATE; lia.
      + intros x y [Hx Hy] E. rewrite IN_UNION in Hx, Hy.
        destruct Hx as [Hx|Hx]; [|destruct (domain_LN_empty x Hx)]. destruct Hy as [Hy|Hy]; [|destruct (domain_LN_empty y Hy)].
        destruct (Hta x Hx) as (v & Lx & Fx & _ & Dx & _), (Hta y Hy) as (w & Ly & Fy & _ & Dy & _).
        rewrite Dx, Dy in E; subst w; congruence.
    - apply EXTENSION; intros z; split; [intros (x & _ & Hx); destruct (domain_LN_empty x Hx)|intros []].
    - apply EXTENSION; intros z; split; [intros []|intros (x & _ & Hx); destruct (domain_LN_empty x Hx)]. }
  exists spcol, (with_node_tag (with_node_tag s4 t2) t3), livein, flivein. split; [reflexivity|].
  (* the colour of a variable *)
  assert (Hspc : forall x, in_clash_tree ct x -> exists v, lookup x ta = Some v /\ lookup v fa = Some x /\ v < dim st /\
                  sp_default spcol x = extract_tag (EL v t3) /\ x IN domain spcol).
  { intros x Hx; destruct (Hta x Hx) as (v & Lx & Fx & Hv & _ & _).
    exists v; split; [exact Lx|split; [exact Fx|split; [exact Hv|]]].
    unfold sp_default, spcol; rewrite lookup_map, Lx; split; [reflexivity|].
    unfold pred_set.IN; rewrite domain_map; apply domain_lookup; eauto. }
  split; [|split; [|split]].
  - rewrite <- C. apply check_clash_tree_same_dom. intros x [Hx|Hx]; [|destruct (domain_LN_empty x Hx)].
    destruct (Hspc x Hx) as (v & Lx & _ & Hv & -> & _). cbv beta. unfold col.
    replace (sp_default ta x) with v by (unfold sp_default; rewrite Lx; reflexivity). destruct (N.ltb_spec v (LENGTH t3)); [reflexivity|lia].
  - intros x Hx; destruct (Hspc x Hx) as (v & Lx & Fx & Hv & Sx & Dx). split; [exact Dx|rewrite Sx].
    assert (Hfv : sp_default fa v = x) by (unfold sp_default; rewrite Fx; reflexivity).
    pose proof (Htag v _ (conj Hv eq_refl)) as Tv. rewrite Hfv in Tv.
    assert (Hv2 : v < LENGTH t2) by (pose proof Hg5 as (_ & L2'' & _); rs; lia).
    specialize (Hst6 v Hv2); apply ifdec in Hst6.
    pose proof Hg3 as (_ & L2s3 & _). subst s3; rs.
    assert (Hv3 : v < LENGTH t1) by lia.
    pose proof (Hun5 v) as Hu5. rewrite T4 in Hu5. rs.
    destruct (is_phy_var x).
    + assert (F5 : EL v t2 = Fixed (x DIV 2)) by (rewrite Hu5; [exact Tv|rewrite Tv; split; [exact Hv3|discriminate]]).
      rewrite (proj2 Hst6) by (rewrite F5; discriminate). rewrite F5; reflexivity.
    + destruct (is_stack_var x); [|exact I].
      assert (F5 : EL v t2 = Stemp) by (rewrite Hu5; [exact Tv|rewrite Tv; split; [exact Hv3|discriminate]]).
      destruct (proj1 Hst6 F5) as (c & -> & Hkc). exact Hkc.
  - intros x Hx. unfold spcol, pred_set.IN in Hx. rewrite domain_map in Hx. apply Hdom', Hx.
  - apply EVERY_iff; intros [x y] Hin. apply bool_decide_iff. intros E.
    rewrite EVERY_iff in Hforced. pose proof (Hforced _ Hin) as Hf; cbv beta iota in Hf; apply bool_decide_iff in Hf as [Hx Hy].
    destruct (Hspc x Hx) as (v & Lx & Fx & Hv & Sx & _), (Hspc y Hy) as (w & Ly & Fy & Hw & Sy & _).
    rewrite Sx, Sy in E.
    enough (v = w) by (subst w; congruence).
    destruct (N.eq_dec v w) as [|Hvw]; [assumption|].
    assert (Hedge : has_edge (adj_ls s4) v w).
    { apply Hsub4; subst s3; rs. apply He2. right; left. exists x, y; split; [|split; [|apply MEM_iff, Hin]].
      - unfold sp_default; rewrite Lx; reflexivity.
      - unfold sp_default; rewrite Ly; reflexivity. }
    specialize (Hnc6 v w Hedge).
    destruct (Hfix v Hv) as (cv & Ev), (Hfix w Hw) as (cw & Ew). rewrite Ev, Ew in Hnc6, E.
    apply Hnc6; exact E.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "reg_alloc_correct" *)
Theorem reg_alloc_correct : forall alg scost k moves ct forced fs,
  EVERY (fun '(x, y) => ⌜in_clash_tree ct x /\ in_clash_tree ct y⌝) forced ->
  exists spcol livein flivein,
    reg_alloc alg scost k moves ct forced fs = M_success spcol /\
    check_clash_tree (sp_default spcol) ct LN LN = Some (livein, flivein) /\
    (forall x, in_clash_tree ct x ->
       x IN domain spcol /\
       (if is_phy_var x then sp_default spcol x = x DIV 2
        else if is_stack_var x then k <= sp_default spcol x
        else True)) /\
    (forall x, x IN domain spcol -> in_clash_tree ct x) /\
    EVERY (fun '(x, y) => ⌜sp_default spcol x = sp_default spcol y -> x = y⌝) forced.
Proof.
  intros alg scost k moves ct forced fs Hforced. unfold reg_alloc.
  destruct (mk_bij ct) as [ta [fa n]] eqn:Eb.
  unfold reg_alloc_aux, run_ira_state, run. cbv iota beta.
  destruct (do_reg_alloc_correct alg scost k moves ct forced fs
    (mk_ra_state (marray_replicate n []) (marray_replicate n Atemp) (marray_replicate n 0) n [] [] [] [] []
       (marray_replicate n 0) (marray_replicate n false) []) ta fa n Eb)
    as (spcol & st' & livein & flivein & E & H1 & H2 & H3 & H4); try reflexivity; [exact Hforced|].
  exists spcol, livein, flivein. cbn [ira_state_adj_ls ira_state_node_tag ira_state_degrees ira_state_dim
    ira_state_simp_wl ira_state_spill_wl ira_state_freeze_wl ira_state_avail_moves_wl ira_state_unavail_moves_wl
    ira_state_coalesced ira_state_move_related ira_state_stack FST SND fst snd].
  rewrite E; cbn [fst]. auto.
Qed.
