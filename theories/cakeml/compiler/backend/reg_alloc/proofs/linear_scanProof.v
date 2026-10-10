(** * CakeML [linear_scanProof]: correctness of the linear-scan allocator

    A port of [compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml],
    split along the script into [linear_scanProof/intervals.v] (live trees,
    intervals, HOL lines 1-2018), [allocator.v] (the monadic allocator and
    its invariants, HOL lines 2020-4573), [alloc_intervals.v]
    ([linear_reg_alloc_intervals_correct]) and [renaming.v] (the renaming
    bijection and clash-tree checks); this file holds the top-level
    theorems [linear_reg_alloc_without_renaming_correct] and
    [linear_scan_reg_alloc_correct].

    HOL's free variables ([sth], [reglist_unsorted]) are quantified
    explicitly; HOL [EVERY] over [Prop] predicates uses [⌜P⌝];
    HOL's [do m1; m2 od] is [m1 ;; m2]. *)

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
From Galette.cakeml.compiler.backend.reg_alloc.proofs.linear_scanProof Require Export
  intervals allocator alloc_intervals renaming.
From Stdlib Require Import Permutation.
Open Scope N_scope.
Open Scope monad_scope.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "linear_reg_alloc_without_renaming_correct" *)
Theorem linear_reg_alloc_without_renaming_correct : forall k moves ct forced sth reglist_unsorted,
  (forall i, i < LENGTH sth.(int_beg) -> (0 < EL i sth.(int_beg))%Z) /\
  (forall i, i < LENGTH sth.(int_end) -> (0 < EL i sth.(int_end))%Z) /\
  LENGTH sth.(int_end) = LENGTH sth.(int_beg) /\
  (forall r, MEM r reglist_unsorted <-> in_clash_tree ct r) /\
  (forall r, in_clash_tree ct r -> r < LENGTH sth.(int_beg)) /\
  EVERY (fun '(r1, r2) => ⌜in_clash_tree ct r1 /\ in_clash_tree ct r2⌝) forced /\
  EVERY (fun '(r1, r2) => (r1 <? LENGTH sth.(colors)) && (r2 <? LENGTH sth.(colors))) (MAP SND moves) /\
  LENGTH reglist_unsorted <= LENGTH sth.(sorted_regs) /\
  LENGTH moves <= LENGTH sth.(sorted_moves) /\
  LENGTH sth.(colors) = LENGTH sth.(int_beg) /\
  LENGTH sth.(int_end) = LENGTH sth.(int_beg) /\
  ALL_DISTINCT reglist_unsorted ->
  exists sthout livein flivein,
    (get_intervals_ct_monad ct ;; linear_reg_alloc_intervals k forced moves reglist_unsorted) sth =
      (M_success tt, sthout) /\
    check_clash_tree (fun r => EL r sthout.(colors)) ct LN LN = SOME (livein, flivein) /\
    (forall r, in_clash_tree ct r ->
      if is_phy_var r then EL r sthout.(colors) = r DIV 2
      else if is_stack_var r then k <= EL r sthout.(colors)
      else True) /\
    EVERY (fun '(r1, r2) => ⌜EL r1 sthout.(colors) = EL r2 sthout.(colors) -> r1 = r2⌝) forced /\
    LENGTH sthout.(colors) = LENGTH sth.(colors).
Proof.
  intros k moves ct forced sth rl (Hpb & Hpe & Lbe & Hrl & Hct & Hf & Hm & Lr & Lm & Lc & _ & Hd).
  destruct (get_intervals_ct ct) as [n [ib ie]] eqn:Gc.
  destruct (get_intervals_ct_monad_correct ct sth n ib ie) as (si & Ei & Bi & Ci & LBi & LEi & Qi).
  { repeat (split; [eassumption|]). exact Hct. }
  assert (Fi : colors si = colors sth /\ sorted_regs si = sorted_regs sth /\ sorted_moves si = sorted_moves sth)
    by (rewrite Qi; repeat split).
  destruct Fi as (Fci & Fri & Fmi).
  destruct (get_intervals (fix_domination (get_live_tree ct)) 0%Z LN LN) as [n' [ib' ie']] eqn:Gl.
  destruct (get_intervals_ct_eq ct ib ib' ie ie' n n') as [Eb Ee]; [split; [symmetry; exact Gc|symmetry; exact Gl]|].
  destruct (get_intervals_beg_less_end (fix_domination (get_live_tree ct)) 0%Z LN LN n' ib' ie') as [Hbe Hsub].
  { split; [intros r Hr; exfalso; apply dom_iff in Hr; apply Hr; destruct r; reflexivity|].
    split; [intros r Hr; exact Hr|symmetry; exact Gl]. }
  destruct (get_intervals_domain_eq_live_tree_registers (get_live_tree ct) n' ib' ie') as [Db De];
    [symmetry; exact Gl|].
  rewrite fix_domination_live_tree_registers in Db, De.
  assert (Hdom : forall r, r IN domain ib' <-> in_clash_tree ct r).
  { intros r. rewrite Db, in_clash_tree_eq_live_tree_registers. reflexivity. }
  assert (Hdome : forall r, r IN domain ie' <-> in_clash_tree ct r).
  { intros r. rewrite De, in_clash_tree_eq_live_tree_registers. reflexivity. }
  assert (Lk : forall r, in_clash_tree ct r ->
            lookup r ib' = SOME (EL r (int_beg si)) /\ lookup r ie' = SOME (EL r (int_end si))).
  { intros r Hr. pose proof (Hct r Hr) as Hlt. split.
    - destruct (Bi r ltac:(rewrite LBi; exact Hlt)) as [B1 B2]. rewrite <- Eb.
      apply B2. destruct (Z.le_gt_cases (EL r (int_beg si)) 0) as [X|X]; [exact X|].
      exfalso. apply (proj1 B1) in X. rewrite Eb in X. apply (proj2 (Hdom r)) in Hr. apply dom_iff in Hr. contradiction.
    - destruct (Ci r ltac:(rewrite LEi, Lbe; exact Hlt)) as [B1 B2]. rewrite <- Ee.
      apply B2. destruct (Z.le_gt_cases (EL r (int_end si)) 0) as [X|X]; [exact X|].
      exfalso. apply (proj1 B1) in X. rewrite Ee in X. apply (proj2 (Hdome r)) in Hr. apply dom_iff in Hr. contradiction. }
  destruct (linear_reg_alloc_intervals_correct k forced moves rl si) as (so & Eo & Inj & Phy & Frc & Lo).
  { split.
    { apply EVERY_iff. intros [a b] Hab. pose proof (proj1 (EVERY_iff _ _) Hf _ Hab) as X. cbv beta iota in X.
      apply bool_decide_spec in X as [Xa Xb]. apply andb_true_intro; split; apply Hrl; assumption. }
    split; [rewrite Fci; exact Hm|].
    split; [apply EVERY_iff; intros r Hr; apply N.ltb_lt; rewrite Fci, Lc; apply Hct, Hrl, MEM_iff, Hr|].
    split.
    { apply EVERY_iff. intros r Hr. apply MEM_iff, Hrl in Hr. destruct (Lk r Hr) as [L1 L2].
      apply Z.leb_le. apply (proj2 (Hdom r)) in Hr. pose proof (Hbe r Hr) as X. rewrite L1, L2 in X. exact X. }
    split; [exact Hd|].
    split; [apply EVERY_iff; intros r Hr; apply N.ltb_lt; rewrite LBi; apply Hct, Hrl, MEM_iff, Hr|].
    split; [rewrite Fci, LBi; exact Lc|]. split; [rewrite LEi, LBi; exact Lbe|].
    split; [rewrite Fri; exact Lr|rewrite Fmi; exact Lm]. }
  assert (Ci' : check_intervals (fun r => EL r (colors so)) ib' ie').
  { intros r1 r2 (H1 & H2 & Hi & E). apply Hdom in H1, H2. apply Inj.
    split; [apply Hrl, H1|split; [apply Hrl, H2|split; [|exact E]]].
    destruct (Lk r1 H1) as [A1 A2], (Lk r2 H2) as [A3 A4]. rewrite A1, A2, A3, A4 in Hi. exact Hi. }
  destruct (check_intervals_check_live_tree (get_live_tree ct) n' ib' ie' (fun r => EL r (colors so)))
    as (lo & flo & Clo); [split; [symmetry; exact Gl|exact Ci']|].
  destruct (fix_domination_check_live_tree _ _ _ _ Clo) as (lo' & flo' & Clo').
  destruct (get_live_tree_correct_LN _ _ _ _ Clo') as (livein & flivein & Cct).
  exists so, livein, flivein.
  split; [unfold st_ex_ignore_bind; rewrite Ei; exact Eo|].
  split; [exact Cct|].
  split.
  { intros r Hr. pose proof (proj1 (EVERY_iff _ _) Phy r (proj1 (MEM_iff _ _) (proj2 (Hrl r) Hr))) as X.
    cbv beta in X. destruct (is_phy_var r); [apply N.eqb_eq, X|].
    destruct (is_stack_var r); [apply N.leb_le, X|exact I]. }
  split; [|rewrite Lo, Fci; reflexivity].
  apply EVERY_iff. intros [a b] Hab. pose proof (proj1 (EVERY_iff _ _) Frc _ Hab) as X. cbv beta iota in X.
  apply bool_decide_spec. intros E. unfold is_true in X. rewrite implb_iff in X. apply N.eqb_eq, X, N.eqb_eq, E.
Qed.

Lemma EL_REPLICATE' {A} `{Inhabited A} n (x : A) i : i < n -> EL i (REPLICATE n x) = x.
Proof.
  revert i; induction n as [|n IH] using N.peano_ind; intros i Hi; [lia|].
  rewrite (proj2 (REPLICATE_thm n x)), EL_cons. destruct (N.eqb_spec i 0); [reflexivity|]. apply IH; lia.
Qed.

Lemma In_MAP_SND_toAList (t : num_map N) v : In v (MAP snd (toAList t)) <-> exists k, lookup k t = SOME v.
Proof.
  rewrite <- MEM_iff. change (MAP snd (toAList t)) with (MAP SND (toAList t)). unfold is_true.
  split.
  - intros H. apply MEM_iff, in_map_iff in H as ([k v'] & <- & Hk). exists k. apply MEM_toAList. apply MEM_iff, Hk.
  - intros [k Hk]. apply MEM_iff, in_map_iff. exists (k, v). split; [reflexivity|]. apply MEM_iff, MEM_toAList, Hk.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "linear_scan_reg_alloc_correct" *)
Theorem linear_scan_reg_alloc_correct : forall k moves ct forced,
  EVERY (fun '(r1, r2) => ⌜in_clash_tree ct r1 /\ in_clash_tree ct r2⌝) forced ->
  exists col livein flivein,
    linear_scan_reg_alloc k moves ct forced = M_success col /\
    check_clash_tree (sp_default col) ct LN LN = Some (livein, flivein) /\
    (forall r, in_clash_tree ct r ->
       r IN domain col /\
       (if is_phy_var r then sp_default col r = r DIV 2
        else if is_stack_var r then k <= sp_default col r
        else True)) /\
    (forall r, r IN domain col -> in_clash_tree ct r) /\
    EVERY (fun '(r1, r2) => ⌜sp_default col r1 = sp_default col r2 -> r1 = r2⌝) forced.
Proof.
  intros k moves ct forced Hf.
  unfold linear_scan_reg_alloc, run_linear_reg_alloc_intervals, run_i_linear_scan_hidden_state, run,
    linear_reg_alloc_and_extract_coloration. cbv zeta. cbn [FST SND i_linear_scan_hidden_state_colors
    i_linear_scan_hidden_state_int_beg i_linear_scan_hidden_state_int_end i_linear_scan_hidden_state_sorted_regs
    i_linear_scan_hidden_state_sorted_moves]. unfold marray_replicate.
  set (bs := find_bijection_clash_tree find_bijection_init ct).
  pose proof (find_bijection_clash_tree_invariants find_bijection_init ct {} find_bijection_init_invariants) as G.
  fold bs in G. destruct G as (Gd & [Gi1 Gi2] & (Gs & Ga & Gp) & _ & _ & _ & Gmx).
  assert (Hdom : forall r, r IN domain (bij bs) <-> in_clash_tree ct r).
  { intros r. rewrite <- Gd. unfold pred_set.UNION, pred_set.IN, EMPTY. tauto. }
  set (ab := fun r => the 0 (lookup r (bij bs))) in *.
  set (ct' := apply_bij_on_clash_tree ct (bij bs)).
  assert (Sct : in_clash_tree ct SUBSET domain (bij bs)) by (intros r Hr; apply Hdom, Hr).
  pose proof (in_clash_tree_apply_bij (bij bs) ct Sct) as Ict. fold ct' in Ict.
  set (forced' := MAP (fun '(r1, r2) => (the 0 (lookup r1 (bij bs)), the 0 (lookup r2 (bij bs)))) forced).
  set (moves' := MAP (fun '(p, (r1, r2)) => (p, (the 0 (lookup r1 (bij bs)), the 0 (lookup r2 (bij bs))))) moves).
  set (rl := MAP snd (toAList (bij bs))).
  set (sth := {| colors := REPLICATE (nmax bs + 1) 0; int_beg := REPLICATE (nmax bs + 1) 1%Z;
                 int_end := REPLICATE (nmax bs + 1) 1%Z; sorted_regs := REPLICATE (nmax bs + 1) 0;
                 sorted_moves := REPLICATE (LENGTH moves') (0, (0, 0)) |}).
  assert (Fab' : forall r, r IN domain (bij bs) -> lookup r (bij bs) = SOME (ab r) /\ lookup (ab r) (invbij bs) = SOME r).
  { intros r Hr. apply dom_lookup in Hr as [v Hv]. unfold ab. rewrite Hv. cbn [the]. split; [reflexivity|exact (Gi1 _ _ Hv)]. }
  assert (Inrl : forall v, In v rl <-> exists r, in_clash_tree ct r /\ v = ab r).
  { intros v. unfold rl. rewrite In_MAP_SND_toAList. split.
    - intros [r Hr]. exists r. split; [apply Hdom, dom_lookup; eauto|]. unfold ab. rewrite Hr. reflexivity.
    - intros (r & Hr & ->). exists r. apply (Fab' r), Hdom, Hr. }
  assert (NDrl : NoDup rl).
  { unfold rl. apply NoDup_map_of_inj.
    - apply (NoDup_map_inv fst). apply keys_NoDup.
    - intros [k1 v1] [k2 v2] H1 H2 E. cbn in E. subst v2.
      assert (L1 : lookup k1 (bij bs) = SOME v1) by (apply MEM_toAList, MEM_iff, H1).
      assert (L2 : lookup k2 (bij bs) = SOME v1) by (apply MEM_toAList, MEM_iff, H2).
      pose proof (Gi1 _ _ L1) as X1. pose proof (Gi1 _ _ L2) as X2. rewrite X1 in X2. injection X2 as ->. reflexivity. }
  assert (Hab_le : forall r, ab r <= nmax bs) by (intros r; apply Gmx).
  assert (Ict' : forall v, in_clash_tree ct' v <-> exists r, in_clash_tree ct r /\ v = ab r).
  { intros v. rewrite Ict. unfold IMAGE, pred_set.IN. split; intros (r & H1 & H2); exists r; auto. }
  assert (Hf2 : forall a b, In (a, b) forced -> in_clash_tree ct a /\ in_clash_tree ct b).
  { intros a b Hab. pose proof (proj1 (EVERY_iff _ _) Hf _ Hab) as X. cbv beta iota in X. apply bool_decide_spec in X. exact X. }
  destruct (linear_reg_alloc_without_renaming_correct k moves' ct' forced' sth rl)
    as (so & livein & flivein & Em & Ck & Ph & Fr & Lo).
  { unfold sth; cbn [colors int_beg int_end sorted_regs sorted_moves]. rewrite !LENGTH_REPLICATE.
    split; [intros i Hi; rewrite EL_REPLICATE' by exact Hi; lia|].
    split; [intros i Hi; rewrite EL_REPLICATE' by exact Hi; lia|].
    split; [reflexivity|].
    split; [intros r; rewrite MEM_iff, Inrl, Ict'; reflexivity|].
    split; [intros r Hr; apply Ict' in Hr as (x & _ & ->); specialize (Hab_le x); lia|].
    split.
    { apply EVERY_iff. intros [a b] Hab. unfold forced' in Hab. apply in_map_iff in Hab as ([x y] & E & Hxy).
      injection E as <- <-. apply bool_decide_spec. destruct (Hf2 x y Hxy) as [Hx Hy].
      split; apply Ict'; eexists; split; [exact Hx|reflexivity|exact Hy|reflexivity]. }
    split.
    { apply EVERY_iff. intros [a b] Hab. unfold moves' in Hab. rewrite List.map_map in Hab.
      apply in_map_iff in Hab as ([p [x y]] & E & _). cbn in E. injection E as <- <-.
      apply andb_true_intro; split; apply N.ltb_lt;
        [specialize (Hab_le x)|specialize (Hab_le y)]; unfold ab in Hab_le; lia. }
    split.
    { (* the registers are distinct and below [nmax + 1] *)
      rewrite LENGTH_length.
      assert (I : incl rl (List.map N.of_nat (seq 0 (N.to_nat (nmax bs + 1))))).
      { intros v Hv. apply Inrl in Hv as (r & _ & ->). apply in_map_iff. exists (N.to_nat (ab r)).
        split; [lia|]. apply in_seq. specialize (Hab_le r). lia. }
      pose proof (NoDup_incl_length NDrl I) as X. rewrite length_map, length_seq in X.
      lia. }
    split; [unfold moves'; rewrite LENGTH_MAP; lia|].
    split; [reflexivity|]. split; [reflexivity|]. apply ALL_DISTINCT_iff, NDrl. }
  assert (Lso : LENGTH (colors so) = nmax bs + 1) by (rewrite Lo; unfold sth; cbn; apply LENGTH_REPLICATE).
  destruct (extract_coloration_output (bij bs) (invbij bs) so rl LN) as (col & Ex & Hcol & Dcol).
  { split; [exact Gi1|split; [exact Gi2|split]].
    - apply EVERY_iff. intros v Hv. apply bool_decide_spec. apply Inrl in Hv as (r & Hr & ->).
      apply dom_lookup. exists r. apply (Fab' r), Hdom, Hr.
    - apply EVERY_iff. intros v Hv. apply N.ltb_lt. rewrite Lso. apply Inrl in Hv as (r & _ & ->).
      specialize (Hab_le r). lia. }
  assert (Hsp : forall r, in_clash_tree ct r -> lookup r col = SOME (EL (ab r) (colors so))).
  { intros r Hr. pose proof (Hcol r (proj2 (Hdom r) Hr)) as X.
    assert (Hm : MEM (the 0 (lookup r (bij bs))) rl = true) by (apply MEM_iff, Inrl; exists r; split; [exact Hr|reflexivity]).
    rewrite Hm in X. exact X. }
  assert (Hsp' : forall r, in_clash_tree ct r -> sp_default col r = EL (ab r) (colors so))
    by (intros r Hr; unfold sp_default; rewrite (Hsp r Hr); reflexivity).
  assert (HLN : forall r, ~ r IN domain (@LN unit)) by (intros r H; apply dom_iff in H; apply H; destruct r; reflexivity).
  destruct (check_clash_tree_apply_bijection (bij bs) (invbij bs) (fun r => EL r (colors so)) ct LN LN LN LN livein flivein)
    as (l' & fl' & Ck' & _).
  { split; [exact Gi1|split; [exact Gi2|split; [exact Sct|]]].
    split; [intros x Hx; exfalso; exact (HLN x Hx)|].
    split; [apply set_eq_iff; intros x; split; [intros Hx; exfalso; exact (HLN x Hx)|intros (y & _ & Hy); exfalso; exact (HLN y Hy)]|].
    split; [apply set_eq_iff; intros x; split; [intros Hx; exfalso; exact (HLN x Hx)|intros (y & _ & Hy); exfalso; exact (HLN y Hy)]|].
    split; [apply set_eq_iff; intros x; split; [intros Hx; exfalso; exact (HLN x Hx)|intros (y & _ & Hy); exfalso; exact (HLN y Hy)]|].
    split; [rewrite INJ_UNIV; intros x y Hx; exfalso; exact (HLN x Hx)|exact Ck]. }
  exists col, l', fl'.
  split.
  { unfold st_ex_ignore_bind in *. destruct (get_intervals_ct_monad ct' sth) as [[x|e] s1]; [|discriminate].
    rewrite Em. rewrite Ex. reflexivity. }
  split.
  { rewrite (check_clash_tree_equal_col (sp_default col) (fun r => EL (ab r) (colors so)) ct LN LN); [exact Ck'|].
    split; [intros r Hr; apply Hsp', Hr|intros r Hr; exfalso; exact (HLN r Hr)]. }
  split.
  { intros r Hr. split; [apply dom_lookup; exists (EL (ab r) (colors so)); apply Hsp, Hr|].
    rewrite (Hsp' r Hr).
    assert (Hr' : in_clash_tree ct' (ab r)) by (apply Ict'; exists r; split; [exact Hr|reflexivity]).
    pose proof (Ph (ab r) Hr') as X.
    assert (Hrr : r IN in_clash_tree ct UNION {}) by (left; exact Hr).
    destruct (is_phy_var r) eqn:Ep.
    - assert (Eab : r = ab r) by (apply Gp; split; [exact Hrr|exact Ep]).
      rewrite <- Eab in X. rewrite Ep in X. rewrite <- Eab. exact X.
    - destruct (is_stack_var r) eqn:Es; [|exact I].
      assert (Es' : is_true (is_stack_var (ab r))) by (apply (Gs r Hrr), Es).
      pose proof (convention_partitions' (ab r)) as (C1 & _). apply C1 in Es' as [Np _].
      destruct (is_phy_var (ab r)) eqn:Ep'; [exfalso; apply Np; reflexivity|].
      assert (Es2 : is_stack_var (ab r) = true) by (apply (Gs r Hrr), Es). rewrite Es2 in X. exact X. }
  split.
  { intros r Hr. apply Dcol in Hr. unfold pred_set.UNION, pred_set.IN in Hr.
    destruct Hr as [Hr|Hr]; [apply Hdom, Hr|exfalso; exact (HLN r Hr)]. }
  apply EVERY_iff. intros [r1 r2] Hp. apply bool_decide_spec. intros E.
  destruct (Hf2 r1 r2 Hp) as [H1 H2]. rewrite (Hsp' r1 H1), (Hsp' r2 H2) in E.
  assert (Hp' : In (ab r1, ab r2) forced') by (apply in_map_iff; exists (r1, r2); split; [reflexivity|exact Hp]).
  pose proof (proj1 (EVERY_iff _ _) Fr _ Hp') as X. cbv beta iota in X. apply bool_decide_spec in X.
  specialize (X E).
  destruct (Fab' r1 (proj2 (Hdom r1) H1)) as [_ I1]. destruct (Fab' r2 (proj2 (Hdom r2) H2)) as [_ I2].
  rewrite X in I1. rewrite I1 in I2. injection I2 as ->. reflexivity.
Qed.
