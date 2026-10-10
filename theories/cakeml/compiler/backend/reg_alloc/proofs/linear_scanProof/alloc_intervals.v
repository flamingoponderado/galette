(** * CakeML [linear_scanProof]: correctness of [linear_reg_alloc_intervals]

    Part of the [linear_scanProofScript] counterpart (HOL lines 4574-4996):
    [linear_reg_alloc_intervals_correct], the correctness of the monadic
    allocator on precomputed intervals.  HOL [EVERY] over boolean
    combinations is stated with [&&], [implb] and the boolean comparisons;
    HOL's [T] is [true]. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.relation Require Import relation.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc linear_scan.
From Galette.cakeml.compiler.backend.reg_alloc.proofs.reg_allocProof Require Import check_clash_tree.
From Galette.cakeml.compiler.backend.reg_alloc.proofs.linear_scanProof Require Import intervals allocator.
From Stdlib Require Import Permutation Sorting.Sorted.
Open Scope N_scope.
Open Scope monad_scope.

Lemma DROP_0' {A} (l : list A) : DROP 0 l = l.
Proof. destruct l; reflexivity. Qed.

Lemma SORTED_EL {A} `{Inhabited A} (R : A -> A -> Prop) (l : list A) :
  (forall i, i + 1 < LENGTH l -> R (EL i l) (EL (i + 1) l)) -> SORTED R l.
Proof.
  induction l as [|x [|y l] IH]; intros Hs; cbn [SORTED]; auto.
  split.
  - pose proof (Hs 0 ltac:(cbn [LENGTH]; lia)) as X. rewrite EL_cons in X. cbn [N.eqb] in X.
    rewrite EL_cons in X. cbn in X. exact X.
  - apply IH. intros i Hi. pose proof (Hs (i + 1) ltac:(cbn [LENGTH] in *; lia)) as X.
    rewrite (EL_cons (i + 1) x (y :: l)), (EL_cons (i + 1 + 1) x (y :: l)) in X.
    destruct (N.eqb_spec (i + 1) 0); [lia|]. destruct (N.eqb_spec (i + 1 + 1) 0); [lia|].
    replace (i + 1 - 1) with i in X by lia. replace (i + 1 + 1 - 1) with (i + 1) in X by lia. exact X.
Qed.

Lemma NoDup_map_inj {A B} (g : A -> B) l x y :
  NoDup (List.map g l) -> In x l -> In y l -> g x = g y -> x = y.
Proof.
  induction l as [|h l IH]; [intros _ []|]. cbn [List.map]. intros Hn Hx Hy E. inversion Hn as [|? ? Hh Hl]; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; auto.
  - exfalso; apply Hh. rewrite E. apply in_map, Hy.
  - exfalso; apply Hh. rewrite <- E. apply in_map, Hx.
Qed.

Lemma NoDup_map_of_inj' {A B} (g : A -> B) l :
  NoDup l -> (forall x y, In x l -> In y l -> g x = g y -> x = y) -> NoDup (List.map g l).
Proof.
  induction l as [|h l IH]; intros Hn Hi; cbn [List.map]; [constructor|]. inversion Hn as [|? ? Hh Hl]; subst.
  constructor.
  - intros Hm. apply in_map_iff in Hm as (z & E & Hz). assert (z = h) by (apply Hi; [right; exact Hz|left; reflexivity|exact E]).
    subst. contradiction.
  - apply IH; [exact Hl|]. intros x y Hx Hy; apply Hi; right; assumption.
Qed.

Lemma In_MEM {A} `{EqDecision A} (x : A) l : In x l -> is_true (MEM x l).
Proof. apply MEM_iff. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "linear_reg_alloc_intervals_correct" *)
Theorem linear_reg_alloc_intervals_correct : forall k forced moves reglist_unsorted sth,
  EVERY (fun '(r1, r2) => MEM r1 reglist_unsorted && MEM r2 reglist_unsorted) forced /\
  EVERY (fun '(r1, r2) => (r1 <? LENGTH sth.(colors)) && (r2 <? LENGTH sth.(colors))) (MAP SND moves) /\
  EVERY (fun r => r <? LENGTH sth.(colors)) reglist_unsorted /\
  EVERY (fun r => (EL r sth.(int_beg) <=? EL r sth.(int_end))%Z) reglist_unsorted /\
  ALL_DISTINCT reglist_unsorted /\
  EVERY (fun r => r <? LENGTH sth.(int_beg)) reglist_unsorted /\
  LENGTH sth.(colors) = LENGTH sth.(int_beg) /\
  LENGTH sth.(int_end) = LENGTH sth.(int_beg) /\
  LENGTH reglist_unsorted <= LENGTH sth.(sorted_regs) /\
  LENGTH moves <= LENGTH sth.(sorted_moves) ->
  exists sthout, linear_reg_alloc_intervals k forced moves reglist_unsorted sth = (M_success tt, sthout) /\
    (forall r1 r2, MEM r1 reglist_unsorted /\ MEM r2 reglist_unsorted /\
       interval_intersect (EL r1 sth.(int_beg), EL r1 sth.(int_end)) (EL r2 sth.(int_beg), EL r2 sth.(int_end)) /\
       EL r1 sthout.(colors) = EL r2 sthout.(colors) ->
       r1 = r2) /\
    EVERY (fun r =>
      if is_phy_var r then EL r sthout.(colors) =? r DIV 2
      else if is_stack_var r then k <=? EL r sthout.(colors)
      else true) reglist_unsorted /\
    EVERY (fun '(r1, r2) => implb (EL r1 sthout.(colors) =? EL r2 sthout.(colors)) (r1 =? r2)) forced /\
    LENGTH sthout.(colors) = LENGTH sth.(colors).
Proof.
  intros k forced moves rl sth (Hf & Hm & Hc & Hbe & Hd & Hb & Lc & Le & Lr & Lm).
  unfold linear_reg_alloc_intervals. cbv zeta. msimp.
  (* list_to_sorted_regs *)
  destruct (list_to_sorted_regs_correct rl 0 sth ltac:(lia)) as (s3 & E3 & L3 & Q3 & _ & T3).
  rewrite <- E3. cbv beta iota. rewrite DROP_0' in T3.
  assert (F3 : colors s3 = colors sth /\ int_beg s3 = int_beg sth /\ int_end s3 = int_end sth /\ sorted_moves s3 = sorted_moves sth)
    by (rewrite Q3; repeat split).
  assert (Hc' : forall r, In r rl -> r < LENGTH (colors sth)) by (intros r Hr; apply N.ltb_lt, (proj1 (EVERY_iff _ _) Hc r Hr)).
  assert (Hb' : forall r, In r rl -> r < LENGTH (int_beg sth)) by (intros r Hr; apply N.ltb_lt, (proj1 (EVERY_iff _ _) Hb r Hr)).
  (* sort_regs *)
  destruct (sort_regs_correct 0 (LENGTH rl) s3) as (s2 & E2 & Q2 & L2 & P2 & _ & S2).
  { split; [|split; lia]. intros i [_ Hi]. rewrite <- (EL_TAKE (LENGTH rl) i) by lia. rewrite T3, (proj1 (proj2 F3)).
    apply Hb', EL_In, Hi. }
  rewrite E2. cbv beta iota.
  rewrite sorted_regs_to_list_correct by lia. cbv beta iota. rewrite N.sub_0_r, DROP_0'.
  assert (F2 : colors s2 = colors sth /\ int_beg s2 = int_beg sth /\ int_end s2 = int_end sth /\ sorted_moves s2 = sorted_moves sth)
    by (rewrite Q2; cbn; exact F3).
  pose proof (proj2 (proj2 (proj2 F2))) as Fm2.
  set (reglist := TAKE (LENGTH rl) (sorted_regs s2)) in *.
  assert (Pr : Permutation rl reglist).
  { apply PERM_Permutation. rewrite <- T3 at 1. apply P2. lia. }
  (* moves *)
  destruct (list_to_sorted_moves_correct moves 0 s2) as (s1 & E1 & L1 & Q1 & _ & T1); [rewrite (proj2 (proj2 (proj2 F2))); lia|].
  rewrite <- E1. cbv beta iota. rewrite DROP_0' in T1.
  destruct (sort_moves_correct 0 (LENGTH moves) s1) as (s0 & E0 & Q0 & L0 & P0); [rewrite L1, (proj2 (proj2 (proj2 F2))); lia|].
  rewrite E0. cbv beta iota.
  rewrite sorted_moves_to_list_correct by (rewrite L0, L1, Fm2; lia). cbv beta iota. rewrite N.sub_0_r, DROP_0'.
  assert (F0 : colors s0 = colors sth /\ int_beg s0 = int_beg sth /\ int_end s0 = int_end sth)
    by (rewrite Q0; cbn; rewrite Q1; cbn; repeat split; apply F2).
  set (smoves := TAKE (LENGTH moves) (sorted_moves s0)) in *.
  assert (Pm : Permutation moves smoves).
  { apply PERM_Permutation. rewrite <- T1 at 1. apply P0. rewrite L1, Fm2; lia. }
  destruct F0 as (Fc0 & Fb0 & Fe0).
  (* edges *)
  assert (Hm' : forall a b, In (a, b) (MAP SND moves) -> a < LENGTH (colors sth) /\ b < LENGTH (colors sth)).
  { intros a b Hab. pose proof (proj1 (EVERY_iff _ _) Hm _ Hab) as X. cbv beta iota in X.
    unfold is_true in X. apply andb_prop in X as [X1 X2]. split; apply N.ltb_lt; assumption. }
  assert (Pms : Permutation (MAP SND moves) (MAP SND smoves)) by (apply Permutation_map, Pm).
  destruct (edges_to_adjlist_output (MAP SND smoves) s0) as (madj & Em & Fm).
  { apply EVERY_iff. intros [a b] Hab. apply (Permutation_in _ (Permutation_sym Pms)) in Hab.
    destruct (Hm' a b Hab) as [Ha Hb2]. rewrite Fb0, <- Lc. apply andb_true_intro; split; apply N.ltb_lt; assumption. }
  rewrite Em. cbv beta iota.
  assert (Hf' : forall a b, In (a, b) forced -> In a rl /\ In b rl).
  { intros a b Hab. pose proof (proj1 (EVERY_iff _ _) Hf _ Hab) as X. cbv beta iota in X.
    unfold is_true in X. apply andb_prop in X as [X1 X2]. split; apply MEM_iff; assumption. }
  destruct (edges_to_adjlist_output forced s0) as (fadj & Ef & Ff).
  { apply EVERY_iff. intros [a b] Hab. destruct (Hf' a b Hab) as [Ha Hb2].
    rewrite Fb0. apply andb_true_intro; split; apply N.ltb_lt; apply Hb'; assumption. }
  rewrite Ef. cbv beta iota.
  assert (Inr : forall r, In r rl <-> In r reglist) by (intros r; split; apply Permutation_in; [exact Pr|symmetry; exact Pr]).
  assert (NDr : NoDup reglist) by (apply (Permutation_NoDup Pr), ALL_DISTINCT_iff, Hd).
  (* pass 1 *)
  assert (Hfr : forall a b, In (a, b) forced -> In a reglist /\ In b reglist)
    by (intros a b Hab; destruct (Hf' a b Hab); split; apply Inr; assumption).
  assert (Hfs : forall r, forbidden_is_from_forced_sublist reglist forced (int_beg s0) r (the [] (lookup r fadj))).
  { apply forbidden_is_from_forced_take_sublist. split; [|exact Ff].
    apply EVERY_iff. intros [a b] Hab. destruct (Hfr a b Hab) as [Ha Hb2].
    apply andb_true_intro; split; apply MEM_iff; assumption. }
  assert (Hfa : forall r1 r2, In r2 (the [] (lookup r1 fadj)) -> In r2 reglist).
  { intros r1 r2 Hr2. apply In_MEM in Hr2. apply (Ff r1 r2) in Hr2 as (_ & Hm2 & _).
    destruct Hm2 as [Hm2|Hm2]; apply MEM_iff in Hm2; apply (Hfr _ _ Hm2). }
  assert (Hma : forall r1 r2, In r2 (the [] (lookup r1 madj)) -> r2 < LENGTH (colors sth)).
  { intros r1 r2 Hr2. apply In_MEM in Hr2. apply (Fm r1 r2) in Hr2 as (_ & Hm2 & _).
    destruct Hm2 as [Hm2|Hm2]; apply MEM_iff in Hm2; apply (Permutation_in _ (Permutation_sym Pms)) in Hm2;
      apply (Hm' _ _ Hm2). }
  assert (Hsrt : SORTED (intbeg_less (int_beg s0)) reglist).
  { apply SORTED_EL. intros i Hi. unfold intbeg_less. rewrite Fb0, <- (proj1 (proj2 F3)).
    unfold reglist in *. rewrite LENGTH_TAKE' in Hi. rewrite !EL_TAKE by lia. apply (S2 i (i + 1)). lia. }
  destruct (linear_reg_alloc_pass1_initial_state_invariants s0 reglist forced k tt) as (pos & G0 & Hpos).
  { rewrite Fc0, Fb0, Fe0, Lc, Le. split; reflexivity. }
  destruct (st_ex_FOLDL_linear_reg_alloc_step_passn_invariants reglist (linear_reg_alloc_pass1_initial_state k) s0 pos true
              madj fadj forced 0) as (st1 & sh1 & pos1 & E1' & G1 & L1' & B1 & En1 & U1 & Ph1 & M1).
  { split; [exact Hsrt|].
    split; [apply ALL_DISTINCT_iff, NDr|]. split; [exact G0|]. split; [exact Hpos|].
    split; [apply EVERY_iff; intros r Hr; apply N.ltb_lt; rewrite Fc0; apply Hc', Inr, Hr|].
    split; [exact Hfs|].
    split.
    { apply EVERY_iff. intros [a b] Hab. destruct (Hfr a b Hab) as [Ha Hb2].
      apply andb_true_intro; split; apply MEM_iff; assumption. }
    split; [intros r1; apply EVERY_iff; intros r2 Hr2; apply N.ltb_lt; rewrite Fc0; apply Hc', Inr, (Hfa r1 r2 Hr2)|].
    split; [intros r1; apply EVERY_iff; intros r2 Hr2; apply N.ltb_lt; rewrite Fc0; apply (Hma r1 r2 Hr2)|].
    apply EVERY_iff. intros r Hr. rewrite Fb0, Fe0. apply (proj1 (EVERY_iff _ _) Hbe), Inr, Hr. }
  rewrite <- E1'. cbv beta iota.
  apply gls_iff in G1.
  set (phy := FILTER is_phy_var reglist) in *.
  set (phyphy := FILTER (fun r => r <? 2 * k) phy) in *.
  set (stackphy := FILTER (fun r => 2 * k <=? r) phy) in *.
  assert (Inphy : forall r, In r phy <-> In r reglist /\ is_phy_var r = true) by (intros r; apply filter_In).
  assert (Inpp : forall r, In r phyphy <-> In r phy /\ r < 2 * k) by (intros r; unfold phyphy; rewrite filter_In, N.ltb_lt; reflexivity).
  assert (Insp : forall r, In r stackphy <-> In r phy /\ 2 * k <= r) by (intros r; unfold stackphy; rewrite filter_In, N.leb_le; reflexivity).
  assert (Hlen1 : forall r, In r reglist -> r < LENGTH (colors sh1)) by (intros r Hr; rewrite L1', Fc0; apply Hc', Inr, Hr).
  (* colours of physical registers after pass 1 are distinct *)
  assert (Dph1 : forall r1 r2, In r1 phy -> In r2 phy -> EL r1 (colors sh1) = EL r2 (colors sh1) -> r1 = r2).
  { intros r1 r2 H1 H2 E. apply (NoDup_map_inj (fun r => EL r (colors sh1)) (List.filter is_phy_var (REVERSE reglist)));
      [exact (g_phydistinct _ _ _ _ _ _ G1)| | |exact E]; apply filter_In; apply Inphy in H1, H2;
      (split; [apply in_rev; rewrite rev_involutive|]); try tauto; unfold REVERSE; rewrite <- in_rev; tauto. }
  (* register exchange, pass 1 *)
  destruct (apply_reg_exchange_correct phyphy sh1 k) as (sh2 & E2' & L2' & B2 & En2 & X2a & X2b & X2c & X2d & X2e).
  { split; [|split].
    - apply ALL_DISTINCT_iff. apply NoDup_map_of_inj'; [apply NoDup_filter, NoDup_filter, NDr|].
      intros x y Hx Hy E. apply Dph1; [apply Inpp, Hx|apply Inpp, Hy|exact E].
    - intros r Hr. apply MEM_iff, Inpp, proj1, Inphy in Hr. exact (proj2 Hr).
    - intros r Hr. apply MEM_iff, Inpp, proj1, Inphy in Hr. apply Hlen1, Hr. }
  rewrite <- E2'. cbv beta iota.
  (* stacklist *)
  pose proof (st_ex_FILTER_good_stack reglist sh2 k) as Fg. unfold st_ex_bind, st_ex_return in Fg. cbv beta iota zeta in Fg.
  rewrite Fg by (apply EVERY_iff; intros r Hr; apply N.ltb_lt; rewrite L2'; apply Hlen1, Hr). cbv beta iota.
  set (stacklist := FILTER (fun r => is_stack_var r || (k <=? EL r (colors sh2))) reglist) in *.
  assert (Ins : forall r, In r stacklist <-> In r reglist /\ (is_stack_var r = true \/ k <= EL r (colors sh2))).
  { intros r. unfold stacklist. rewrite filter_In, Bool.orb_true_iff, N.leb_le. reflexivity. }
  match goal with |- context [map (FILTER ?Q) fadj] => set (Qf := Q) in * end.
  assert (HQ : forall r, Qf r = true <-> In r stacklist).
  { intros r. unfold Qf. destruct (bool_decide _) eqn:B; cbn [negb].
    - apply bool_decide_spec in B. split; [discriminate|]. intros Hr. apply MEM_iff in Hr.
      apply lookup_fromAList_MAP_not_NONE in Hr. contradiction.
    - split; [intros _|reflexivity]. apply MEM_iff, lookup_fromAList_MAP_not_NONE. intros E.
      apply Bool.not_true_iff_false in B. apply B, bool_decide_spec, E. }
  set (forced' := FILTER (fun '(r1, r2) => MEM r1 stacklist && MEM r2 stacklist) forced).
  assert (Inf' : forall a b, In (a, b) forced' <-> In (a, b) forced /\ In a stacklist /\ In b stacklist).
  { intros a b. unfold forced'. rewrite filter_In, Bool.andb_true_iff.
    split; intros (H & H1 & H2); (split; [exact H|]); split; apply MEM_iff; assumption. }
  assert (Lk : forall {B} (g : list N -> list B) (t : num_map (list N)) r, the [] (lookup r (map g t)) = the [] (OPTION_MAP g (lookup r t)) )
    by (intros B g t0 r; rewrite lookup_map; reflexivity).
  destruct (linear_reg_alloc_pass2_initial_state_invariants sh2 stacklist forced' k (LENGTH stacklist) tt) as (pos2 & G20 & Hpos2).
  { rewrite L2', B2, En2, B1, En1, L1', Fc0, Fb0, Fe0, Lc, Le. split; reflexivity. }
  assert (Fb2 : int_beg sh2 = int_beg s0) by (rewrite B2, B1; reflexivity).
  assert (Fe2 : int_end sh2 = int_end s0) by (rewrite En2, En1; reflexivity).
  assert (Lc2 : LENGTH (colors sh2) = LENGTH (colors sth)) by (rewrite L2', L1', Fc0; reflexivity).
  assert (Ins' : forall r, In r stacklist -> In r reglist) by (intros r Hr; apply Ins, Hr).
  destruct (st_ex_FOLDL_linear_reg_alloc_step_passn_invariants stacklist
              (linear_reg_alloc_pass2_initial_state k (LENGTH stacklist)) sh2 pos2 false
              (map (FILTER Qf) madj) (map (FILTER Qf) fadj) forced' k)
    as (st3 & sh3 & pos3 & E3' & G3 & L3' & B3 & En3 & U3 & _ & M3).
  { split; [rewrite Fb2; apply SORTED_filter; [apply intbeg_less_transitive|exact Hsrt]|].
    split; [apply ALL_DISTINCT_iff, NoDup_filter, NDr|]. split; [exact G20|]. split; [exact Hpos2|].
    split; [apply EVERY_iff; intros r Hr; apply N.ltb_lt; rewrite Lc2; apply Hc', Inr, Ins', Hr|].
    split.
    { intros r reg2. rewrite Lk. specialize (Hfs r reg2). rewrite Fb2.
      split.
      - intros (Hne & Hm2 & Hlex). assert (Hm2' : (In (reg2, r) forced' \/ In (r, reg2) forced')) by
          (destruct Hm2 as [Hm2|Hm2]; apply MEM_iff in Hm2; [left|right]; exact Hm2).
        assert (Hboth : In r stacklist /\ In reg2 stacklist) by (destruct Hm2' as [X|X]; apply Inf' in X; tauto).
        destruct (proj1 Hfs) as [X1 X2].
        { split; [exact Hne|split; [|exact Hlex]]. destruct Hm2' as [X|X]; apply Inf' in X; [left|right]; apply MEM_iff; tauto. }
        split; [|apply MEM_iff; tauto].
        apply MEM_iff. destruct (lookup r fadj) as [lr|]; cbn [OPTION_MAP the] in *; [|apply MEM_iff in X1; destruct X1].
        apply filter_In. split; [apply MEM_iff, X1|apply HQ; tauto].
      - intros [X1 X2]. apply MEM_iff in X1, X2.
        assert (X1' : In reg2 (the [] (lookup r fadj)) /\ Qf reg2 = true).
        { destruct (lookup r fadj) as [lr|]; cbn [OPTION_MAP the] in *; [|destruct X1]. apply filter_In, X1. }
        destruct X1' as [X1' Qr2]. apply HQ in Qr2.
        destruct (proj2 Hfs) as (Hne & Hm2 & Hlex); [split; apply MEM_iff; [exact X1'|apply Ins', X2]|].
        split; [exact Hne|split; [|exact Hlex]].
        destruct Hm2 as [Hm2|Hm2]; apply MEM_iff in Hm2; [left|right]; apply MEM_iff, Inf'; tauto. }
    split.
    { apply EVERY_iff. intros [a b] Hab. apply Inf' in Hab as (_ & Ha & Hb2).
      apply andb_true_intro; split; apply MEM_iff; assumption. }
    split.
    { intros r1. apply EVERY_iff. intros r2 Hr2. rewrite Lk in Hr2. apply N.ltb_lt. rewrite Lc2.
      destruct (lookup r1 fadj) as [lr|] eqn:El; cbn [OPTION_MAP the] in Hr2; [|destruct Hr2].
      apply filter_In in Hr2 as [Hr2 _]. apply Hc', Inr, (Hfa r1 r2). rewrite El. exact Hr2. }
    split.
    { intros r1. apply EVERY_iff. intros r2 Hr2. rewrite Lk in Hr2. apply N.ltb_lt. rewrite Lc2.
      destruct (lookup r1 madj) as [lr|] eqn:El; cbn [OPTION_MAP the] in Hr2; [|destruct Hr2].
      apply filter_In in Hr2 as [Hr2 _]. apply (Hma r1 r2). rewrite El. exact Hr2. }
    apply EVERY_iff. intros r Hr. rewrite Fb2, Fe2, Fb0, Fe0. apply (proj1 (EVERY_iff _ _) Hbe), Inr, Ins', Hr. }
  rewrite <- E3'. cbv beta iota.
  apply gls_iff in G3.
  assert (InR : forall (l : list N) r, In r (REVERSE l) <-> In r l) by (intros l r; unfold REVERSE; rewrite <- in_rev; reflexivity).
  assert (U3' : forall r, ~ In r stacklist -> EL r (colors sh3) = EL r (colors sh2))
    by (intros r Hr; apply U3; intros X; apply Hr, MEM_iff, X).
  assert (Mk3 : forall r, In r stacklist -> k <= EL r (colors sh3))
    by (intros r Hr; apply (g_mincol_l _ _ _ _ _ _ G3), InR, Hr).
  assert (Lt3 : forall r, In r reglist -> ~ In r stacklist -> EL r (colors sh3) < k).
  { intros r Hr Hn. rewrite U3' by exact Hn. destruct (N.lt_ge_cases (EL r (colors sh2)) k) as [X|X]; [exact X|].
    exfalso. apply Hn, Ins. split; [exact Hr|right; exact X]. }
  assert (Lc3 : LENGTH (colors sh3) = LENGTH (colors sth)) by (rewrite L3'; exact Lc2).
  assert (Hlen3 : forall r, In r reglist -> r < LENGTH (colors sh3)) by (intros r Hr; rewrite Lc3; apply Hc', Inr, Hr).
  assert (Hlen1' : forall r, In r reglist -> r < LENGTH (colors sh1)) by (intros r Hr; apply Hlen1, Hr).
  (* injectivity of the colours after pass 2 on the registers of pass 1 *)
  assert (Eq3 : forall r1 r2, In r1 reglist -> In r2 reglist -> EL r1 (colors sh3) = EL r2 (colors sh3) ->
            (In r1 stacklist /\ In r2 stacklist) \/
            (~ In r1 stacklist /\ ~ In r2 stacklist /\ EL r1 (colors sh1) = EL r2 (colors sh1))).
  { intros r1 r2 H1 H2 E. destruct (classic (In r1 stacklist)) as [S1|S1], (classic (In r2 stacklist)) as [S2'|S2'].
    - left; split; assumption.
    - exfalso. pose proof (Mk3 r1 S1). pose proof (Lt3 r2 H2 S2'). lia.
    - exfalso. pose proof (Mk3 r2 S2'). pose proof (Lt3 r1 H1 S1). lia.
    - right. split; [exact S1|split; [exact S2'|]]. rewrite !U3' in E by assumption.
      apply X2a; [split; apply Hlen1; assumption|exact E]. }
  assert (Inj3 : forall r1 r2, In r1 phy -> In r2 phy -> EL r1 (colors sh3) = EL r2 (colors sh3) -> r1 = r2).
  { intros r1 r2 H1 H2 E. pose proof H1 as H1'. pose proof H2 as H2'. apply Inphy in H1', H2'.
    destruct (Eq3 r1 r2 (proj1 H1') (proj1 H2') E) as [[S1 S2']|(_ & _ & Ec1)].
    - apply (NoDup_map_inj (fun r => EL r (colors sh3)) (List.filter is_phy_var (REVERSE stacklist)));
        [exact (g_phydistinct _ _ _ _ _ _ G3)| | |exact E]; apply filter_In; (split; [apply InR; assumption|tauto]).
    - apply Dph1; assumption. }
  (* the physical registers on the stack end up in the stack list *)
  assert (Kst : forall r, In r stackphy -> In r stacklist).
  { intros r Hr. apply Insp in Hr as [Hp H2k]. pose proof Hp as Hp'. apply Inphy in Hp' as [Hrl Hph].
    apply Ins. split; [exact Hrl|right].
    apply X2d.
    - intros r' Hr'. apply MEM_iff, Inpp in Hr' as [_ X]. apply lt_div_2. exact X.
    - split; [apply Hlen1, Hrl|split].
      + assert (M1' : colormax st1 = k) by (rewrite M1; reflexivity).
        rewrite <- M1'. apply (Ph1 eq_refl r). split; [apply MEM_iff, InR, Hrl|split; [exact Hph|]]. rewrite M1'. exact H2k.
      + intros r' Hr' E. apply MEM_iff, Inpp in Hr' as [Hr'p Hr'k]. assert (r = r') by (apply Dph1; assumption). lia. }
  (* register exchange, pass 2 *)
  destruct (apply_reg_exchange_correct stackphy sh3 k) as (sh4 & E4 & L4 & B4 & En4 & X4a & X4b & X4c & X4d & X4e).
  { split; [|split].
    - apply ALL_DISTINCT_iff. apply NoDup_map_of_inj'; [apply NoDup_filter, NoDup_filter, NDr|].
      intros x y Hx Hy E. apply Inj3; [apply Insp, Hx|apply Insp, Hy|exact E].
    - intros r Hr. apply MEM_iff, Insp, proj1, Inphy in Hr. exact (proj2 Hr).
    - intros r Hr. apply MEM_iff, Insp, proj1, Inphy in Hr. apply Hlen3, Hr. }
  assert (Kst2 : forall r, is_true (MEM r stackphy) -> k <= EL r (colors sh3) /\ k <= r DIV 2).
  { intros r Hr. apply MEM_iff in Hr. split; [apply Mk3, Kst, Hr|]. apply Insp in Hr as [_ X]. apply le_div_2, X. }
  exists sh4. split; [symmetry; exact E4|].
  assert (Bsth : int_beg sh3 = int_beg sth /\ int_end sh3 = int_end sth) by (rewrite B3, En3, Fb2, Fe2, Fb0, Fe0; split; reflexivity).
  assert (Bsth1 : int_beg sh1 = int_beg sth /\ int_end sh1 = int_end sth) by (rewrite B1, En1, Fb0, Fe0; split; reflexivity).
  split.
  { intros r1 r2 (H1 & H2 & Hi & E). apply MEM_iff, Inr in H1, H2.
    apply X4a in E; [|split; apply Hlen3; assumption].
    destruct (Eq3 r1 r2 H1 H2 E) as [[S1 S2']|(_ & _ & Ec1)].
    - apply (g_inj _ _ _ _ _ _ G3); [apply InR; exact S1|apply InR; exact S2'| |exact E].
      rewrite (proj1 Bsth), (proj2 Bsth). exact Hi.
    - apply (g_inj _ _ _ _ _ _ G1); [apply InR; exact H1|apply InR; exact H2| |exact Ec1].
      rewrite (proj1 Bsth1), (proj2 Bsth1). exact Hi. }
  split.
  { apply EVERY_iff. intros r Hr. apply Inr in Hr.
    destruct (is_phy_var r) eqn:Ep.
    - apply N.eqb_eq. destruct (N.lt_ge_cases r (2 * k)) as [Hk|Hk].
      + assert (Hpp : In r phyphy) by (apply Inpp; split; [apply Inphy; split; assumption|exact Hk]).
        pose proof (X2b r (proj2 (MEM_iff _ _) Hpp)) as D2.
        assert (Hns : ~ In r stacklist).
        { intros X. apply Ins in X as [_ [X|X]].
          - pose proof (convention_partitions' r) as (Cs & _). apply Cs in X as [X _]. apply X, Ep.
          - rewrite D2 in X. apply lt_div_2 in Hk. lia. }
        assert (D3 : EL r (colors sh3) = r DIV 2) by (rewrite U3' by exact Hns; exact D2).
        rewrite X4e; [exact D3|exact Kst2|]. split; [apply Hlen3, Hr|]. rewrite D3. apply lt_div_2, Hk.
      + apply X4b, MEM_iff, Insp. split; [apply Inphy; split; assumption|exact Hk].
    - destruct (is_stack_var r) eqn:Es; [|reflexivity]. apply N.leb_le.
      assert (Hs : In r stacklist) by (apply Ins; split; [exact Hr|left; exact Es]).
      apply (X4c (fun r' Hr' => conj (fun _ => proj2 (Kst2 r' Hr')) (fun _ => proj1 (Kst2 r' Hr')))).
      + apply Hlen3, Hr.
      + apply Mk3, Hs. }
  split.
  { apply EVERY_iff. intros [r1 r2] Hp. cbv beta iota. apply implb_iff. intros E. apply N.eqb_eq in E. apply N.eqb_eq.
    destruct (Hfr r1 r2 Hp) as [H1 H2].
    apply X4a in E; [|split; apply Hlen3; assumption].
    destruct (Eq3 r1 r2 H1 H2 E) as [[S1 S2']|(_ & _ & Ec1)].
    - apply (g_forced _ _ _ _ _ _ G3); [apply Inf'; tauto|apply InR; exact S1|apply InR; exact S2'|exact E].
    - apply (g_forced _ _ _ _ _ _ G1); [exact Hp|apply InR; exact H1|apply InR; exact H2|exact Ec1]. }
  rewrite L4. exact Lc3.
Qed.
