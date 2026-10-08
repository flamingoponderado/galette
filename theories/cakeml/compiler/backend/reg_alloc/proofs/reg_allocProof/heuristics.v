(** * CakeML [reg_allocProof]: the heuristic steps

    Part of the [reg_allocProofScript] counterpart: every heuristic step of
    the allocator ([do_simplify], [do_coalesce], [do_prefreeze],
    [do_freeze], [do_spill], [do_step], [rpt_do_step], [do_alloc1])
    succeeds and preserves the state invariant.

    HOL states some of these lemmas with a vacuous existential ([∃s' b.]
    where [b] does not occur, or [?ts fs.] where [fs] does not occur) or a
    vacuous universal; the unused variables are omitted here. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.coretypes Require Import pair.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.sort Require Import sorting.
From Galette.cakeml.basis.pure Require Import mllist.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From Galette.cakeml.compiler.backend.reg_alloc.proofs.reg_allocProof Require Import
  check_clash_tree ra_state colouring graph mk_graph.
Open Scope N_scope.
Open Scope monad_scope.

(** ** Helpers (Galette infrastructure) *)

Definition with_simp_wl (s : ra_state) v : ra_state :=
  mk_ra_state s.(adj_ls) s.(node_tag) s.(degrees) s.(dim) v s.(spill_wl) s.(freeze_wl)
    s.(avail_moves_wl) s.(unavail_moves_wl) s.(coalesced) s.(move_related) s.(stack).
Definition with_spill_wl (s : ra_state) v : ra_state :=
  mk_ra_state s.(adj_ls) s.(node_tag) s.(degrees) s.(dim) s.(simp_wl) v s.(freeze_wl)
    s.(avail_moves_wl) s.(unavail_moves_wl) s.(coalesced) s.(move_related) s.(stack).
Definition with_freeze_wl (s : ra_state) v : ra_state :=
  mk_ra_state s.(adj_ls) s.(node_tag) s.(degrees) s.(dim) s.(simp_wl) s.(spill_wl) v
    s.(avail_moves_wl) s.(unavail_moves_wl) s.(coalesced) s.(move_related) s.(stack).

Lemma set_simp_wl_eq {E} x s : @set_simp_wl E x s = (M_success tt, with_simp_wl s x). Proof. reflexivity. Qed.
Lemma set_spill_wl_eq {E} x s : @set_spill_wl E x s = (M_success tt, with_spill_wl s x). Proof. reflexivity. Qed.
Lemma set_freeze_wl_eq {E} x s : @set_freeze_wl E x s = (M_success tt, with_freeze_wl s x). Proof. reflexivity. Qed.
Lemma set_stack_eq {E} x s : @set_stack E x s = (M_success tt, with_stack s x). Proof. reflexivity. Qed.
Lemma set_avail_moves_wl_eq {E} x s : @set_avail_moves_wl E x s = (M_success tt, with_avail_moves_wl s x).
Proof. reflexivity. Qed.
Lemma set_unavail_moves_wl_eq {E} x s : @set_unavail_moves_wl E x s = (M_success tt, with_unavail_moves_wl s x).
Proof. reflexivity. Qed.

Ltac rs2 := rs; cbn [with_simp_wl with_spill_wl with_freeze_wl
  adj_ls node_tag degrees dim simp_wl spill_wl freeze_wl avail_moves_wl unavail_moves_wl
  coalesced move_related stack] in *.

Ltac ms := cbv beta iota zeta.

(** Unpacked [good_ra_state]. *)
Ltac good_destr H :=
  let L1 := fresh "L1" in let L2 := fresh "L2" in let L3 := fresh "L3" in
  let L4 := fresh "L4" in let L5 := fresh "L5" in let B1 := fresh "B1" in
  let B2 := fresh "B2" in let B3 := fresh "B3" in let B4 := fresh "B4" in
  let B5 := fresh "B5" in let B6 := fresh "B6" in let B7 := fresh "B7" in
  let B8 := fresh "B8" in let Hu := fresh "Hu" in
  pose proof H as (L1 & L2 & L3 & L4 & L5 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & Hu).

Lemma st_ex_MAP_pure {A B} (f : A -> RA B) l s :
  (forall x, In x l -> exists y, f x s = (M_success y, s)) ->
  exists ys, st_ex_MAP f l s = (M_success ys, s).
Proof.
  induction l as [|x l IH]; intros H; cbn [st_ex_MAP]; [eexists; reflexivity|].
  destruct (H x (or_introl eq_refl)) as [y Hy]. mstep Hy; cbv beta.
  destruct IH as [ys Hys]; [intros; apply H; right; assumption|]. mstep Hys; cbv beta.
  eexists; reflexivity.
Qed.

Lemma st_ex_PARTITION_pure {A} (P : A -> RA bool) l s : forall lss lss',
  (forall x, In x l -> exists b, P x s = (M_success b, s)) ->
  exists ts fs, st_ex_PARTITION P l lss lss' s = (M_success (ts, fs), s) /\
    (forall x, In x ts -> In x lss \/ In x l) /\ (forall x, In x fs -> In x lss' \/ In x l).
Proof.
  induction l as [|x l IH]; intros lss lss' H; cbn [st_ex_PARTITION].
  - exists lss, lss'; split; [reflexivity|split; intros; left; assumption].
  - destruct (H x (or_introl eq_refl)) as [b Hb]. mstep Hb; cbv beta.
    destruct b; [destruct (IH (x :: lss) lss') as (ts & fs & E & H1 & H2)|destruct (IH lss (x :: lss')) as (ts & fs & E & H1 & H2)];
      try (intros; apply H; right; assumption);
      exists ts, fs; (split; [exact E|]); split; intros y Hy;
      [destruct (H1 y Hy) as [[<-|?]|?]|destruct (H2 y Hy) as [?|?]|destruct (H1 y Hy) as [?|?]|destruct (H2 y Hy) as [[<-|?]|?]];
      cbn [In]; tauto.
Qed.

Lemma st_ex_FILTER_pure {A} (P : A -> RA bool) (Q : A -> Prop) l s : forall acc,
  (forall x, In x l -> exists b, P x s = (M_success b, s) /\ (b = true -> Q x)) ->
  exists ts, st_ex_FILTER P l acc s = (M_success ts, s) /\
    (forall x, In x ts -> (Q x /\ In x l) \/ In x acc).
Proof.
  induction l as [|x l IH]; intros acc H; cbn [st_ex_FILTER].
  - exists acc; split; [reflexivity|intros; right; assumption].
  - destruct (H x (or_introl eq_refl)) as (b & Hb & HQ). mstep Hb; cbv beta.
    destruct b; [destruct (IH (x :: acc)) as (ts & E & H1)|destruct (IH acc) as (ts & E & H1)];
      try (intros; apply H; right; assumption);
      exists ts; (split; [exact E|]); intros y Hy; destruct (H1 y Hy) as [[? ?]|Hy'];
      cbn [In] in *; try tauto.
    destruct Hy' as [<-|?]; [left; split; [apply HQ; reflexivity|left; reflexivity]|tauto].
Qed.

Lemma In_PART {A} (P : A -> bool) l : forall l1 l2 x,
  (In x (fst (PART P l l1 l2)) -> In x l1 \/ In x l) /\
  (In x (snd (PART P l l1 l2)) -> In x l2 \/ In x l).
Proof.
  induction l as [|y l IH]; intros l1 l2 x; cbn [PART]; [cbn; tauto|].
  destruct (P y); [destruct (IH (y :: l1) l2 x)|destruct (IH l1 (y :: l2) x)]; cbn [In] in *; tauto.
Qed.

Lemma In_PARTITION {A} (P : A -> bool) l a b x :
  PARTITION P l = (a, b) -> (In x a -> In x l) /\ (In x b -> In x l).
Proof.
  unfold PARTITION; intros E. destruct (In_PART P l [] [] x) as [H1 H2]. rewrite E in H1, H2; cbn in *.
  split; intros Hx; [destruct (H1 Hx)|destruct (H2 Hx)]; tauto.
Qed.

(** ** Simplification *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "is_not_coalesced_succeeds" *)
Theorem is_not_coalesced_succeeds : forall s n,
  good_ra_state s /\ n < s.(dim) -> exists b, is_not_coalesced n s = (M_success b, s).
Proof.
  intros s n [Hg Hn]; good_destr Hg. unfold is_not_coalesced.
  mstep' (coalesced_sub_ok n s ltac:(lia)). eexists; reflexivity.
Qed.

Lemma split_degree_ok s k v : good_ra_state s -> exists b, split_degree s.(dim) k v s = (M_success b, s).
Proof.
  intros Hg; good_destr Hg. unfold split_degree. destruct (N.ltb_spec v (dim s)) as [Hv|Hv]; [|eexists; reflexivity].
  mstep' (degrees_sub_ok v s ltac:(lia)).
  destruct (is_not_coalesced_succeeds s v (conj Hg Hv)) as [b Hb]. mstep' Hb. eexists; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "st_ex_PARTITION_split_degree" *)
Theorem st_ex_PARTITION_split_degree : forall atemps k lss lss' s,
  good_ra_state s ->
  exists ts fs,
    st_ex_PARTITION (split_degree s.(dim) k) atemps lss lss' s = (M_success (ts, fs), s) /\
    EVERY (fun x => MEM x lss || MEM x atemps) ts /\
    EVERY (fun x => MEM x lss' || MEM x atemps) fs.
Proof.
  intros atemps k lss lss' s Hg.
  destruct (st_ex_PARTITION_pure (split_degree s.(dim) k) atemps s lss lss') as (ts & fs & E & H1 & H2).
  { intros x _; apply split_degree_ok, Hg. }
  exists ts, fs; split; [exact E|]; split; apply EVERY_iff; intros x Hx; apply orb_iff; rewrite !MEM_iff; auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "st_ex_PARTITION_move_related_sub" *)
Theorem st_ex_PARTITION_move_related_sub : forall atemps lss lss' s,
  EVERY (fun x => x <? LENGTH s.(move_related)) atemps ->
  exists ts fs,
    st_ex_PARTITION move_related_sub atemps lss lss' s = (M_success (ts, fs), s) /\
    EVERY (fun x => MEM x lss || MEM x atemps) ts /\
    EVERY (fun x => MEM x lss' || MEM x atemps) fs.
Proof.
  intros atemps lss lss' s Hev. rewrite EVERY_lt_iff in Hev.
  destruct (st_ex_PARTITION_pure move_related_sub atemps s lss lss') as (ts & fs & E & H1 & H2).
  { intros x Hx; eexists; apply move_related_sub_ok, Hev, Hx. }
  exists ts, fs; split; [exact E|]; split; apply EVERY_iff; intros x Hx; apply orb_iff; rewrite !MEM_iff; auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "dec_deg_success" *)
Theorem dec_deg_success : forall ls s,
  EVERY (fun v => v <? s.(dim)) ls /\ good_ra_state s ->
  exists d, st_ex_FOREACH ls dec_deg s = (M_success tt, with_degrees s d) /\
    LENGTH d = LENGTH s.(degrees).
Proof.
  induction ls as [|x ls IH]; intros s [Hev Hg]; cbn [st_ex_FOREACH].
  - exists (degrees s); split; [destruct s; reflexivity|reflexivity].
  - cbn [EVERY] in Hev; apply andb_iff in Hev as [Hx Hev]; apply ltb_iff in Hx. good_destr Hg.
    unfold st_ex_ignore_bind at 1, dec_deg. rewrite (bind_ok _ _ _ _ _ (degrees_sub_ok x s ltac:(lia))). cbv beta.
    rewrite (update_degrees_ok x _ s ltac:(lia)). fold (@st_ex_FOREACH ra_state N unit state_exn ls dec_deg).
    destruct (IH (with_degrees s (LUPDATE (EL x (degrees s) - 1) x (degrees s)))) as (d & E & Hl).
    { rs; split; [exact Hev|]. unfold good_ra_state; rs. rewrite LENGTH_LUPDATE. tauto. }
    exists d; split; [exact E|]. rewrite Hl; rs; apply LENGTH_LUPDATE.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "dec_degree_success" *)
Theorem dec_degree_success : forall ls s,
  good_ra_state s ->
  exists d, st_ex_FOREACH ls dec_degree s = (M_success tt, with_degrees s d) /\
    LENGTH d = LENGTH s.(degrees).
Proof.
  induction ls as [|x ls IH]; intros s Hg; cbn [st_ex_FOREACH].
  - exists (degrees s); split; [destruct s; reflexivity|reflexivity].
  - good_destr Hg.
    assert (Hx1 : exists d, dec_degree x s = (M_success tt, with_degrees s d) /\ LENGTH d = LENGTH (degrees s)).
    { unfold dec_degree. mstep' (get_dim_eq (E:=state_exn) s).
      destruct (N.ltb_spec x (dim s)) as [Hx|Hx].
      - mstep' (adj_ls_sub_ok x s ltac:(lia)). apply dec_deg_success; split; [|exact Hg].
        apply EVERY_lt_iff; intros y Hy; eapply good_bound_adj; eauto.
      - exists (degrees s); split; [destruct s; reflexivity|reflexivity]. }
    destruct Hx1 as (d & E & Hl). mstep E.
    destruct (IH (with_degrees s d)) as (d' & E' & Hl').
    { unfold good_ra_state; rs. rewrite Hl. tauto. }
    exists d'; split; [rewrite E'; destruct s; reflexivity|]. rewrite Hl'; rs; exact Hl.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "MEM_smerge" *)
Theorem MEM_smerge : forall {A} `{EqDecision A} (x : N * A) xs ys,
  MEM x (smerge xs ys) <-> MEM x xs \/ MEM x ys.
Proof.
  intros A EA x xs ys; rewrite !MEM_iff; revert ys.
  induction xs as [|[p m] xs IH]; intros ys; cbn [smerge]; [cbn; tauto|].
  induction ys as [|[p' m'] ys IHy]; [cbn [In]; tauto|].
  destruct (p' <=? p); cbn [In].
  - rewrite IH; cbn [In]; tauto.
  - rewrite IHy; cbn [In]; tauto.
Qed.

Lemma sort_moves_In {A} (x : N * A) l : In x (sort_moves l) <-> In x l.
Proof.
  unfold sort_moves; split; apply Permutation.Permutation_in;
    [symmetry|]; apply sort_Permutation.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "revive_moves_success" *)
Theorem revive_moves_success : forall s ls,
  EVERY (fun x => x <? LENGTH s.(adj_ls)) ls ->
  exists s',
    revive_moves ls s = (M_success tt, s') /\
    s' = with_unavail_moves_wl (with_avail_moves_wl s s'.(avail_moves_wl)) s'.(unavail_moves_wl) /\
    EVERY (fun x => MEM x (s.(avail_moves_wl) ++ s.(unavail_moves_wl))) s'.(avail_moves_wl) /\
    EVERY (fun x => MEM x (s.(avail_moves_wl) ++ s.(unavail_moves_wl))) s'.(unavail_moves_wl).
Proof.
  intros s ls Hev. unfold revive_moves.
  mstep' (st_ex_MAP_adj_ls_sub ls s Hev).
  mstep' (get_unavail_moves_wl_eq (E:=state_exn) s). mstep' (get_avail_moves_wl_eq (E:=state_exn) s).
  match goal with |- context [PARTITION ?P ?l] => destruct (PARTITION P l) as [rv un] eqn:EP end.
  ms. unfold st_ex_ignore_bind; rewrite set_avail_moves_wl_eq; ms. rewrite set_unavail_moves_wl_eq.
  eexists; split; [reflexivity|]. rs. split; [destruct s; reflexivity|].
  split; apply EVERY_iff; intros x Hx; apply MEM_iff; apply in_app_iff.
  - apply MEM_iff, MEM_smerge in Hx as [Hx|Hx]; rewrite MEM_iff in Hx; [|left; exact Hx].
    apply (proj1 (sort_moves_In x rv)) in Hx. right; exact (proj1 (In_PARTITION _ _ _ _ x EP) Hx).
  - right; exact (proj2 (In_PARTITION _ _ _ _ x EP) Hx).
Qed.

(** Preservation of the invariant by field updates. *)
Lemma good_with_degrees s d : good_ra_state s -> LENGTH d = s.(dim) -> good_ra_state (with_degrees s d).
Proof. unfold good_ra_state; rs; tauto. Qed.
Lemma good_with_move_related s d : good_ra_state s -> LENGTH d = s.(dim) -> good_ra_state (with_move_related s d).
Proof. unfold good_ra_state; rs; tauto. Qed.
Lemma good_with_stack s d : good_ra_state s -> good_ra_state (with_stack s d).
Proof. unfold good_ra_state; rs; tauto. Qed.
Lemma good_with_coalesced s d : good_ra_state s -> LENGTH d = s.(dim) ->
  EVERY (fun v => v <? s.(dim)) d -> good_ra_state (with_coalesced s d).
Proof. unfold good_ra_state; rs; tauto. Qed.
Lemma good_with_simp_wl s d : good_ra_state s -> EVERY (fun v => v <? s.(dim)) d -> good_ra_state (with_simp_wl s d).
Proof. unfold good_ra_state; rs2; tauto. Qed.
Lemma good_with_spill_wl s d : good_ra_state s -> EVERY (fun v => v <? s.(dim)) d -> good_ra_state (with_spill_wl s d).
Proof. unfold good_ra_state; rs2; tauto. Qed.
Lemma good_with_freeze_wl s d : good_ra_state s -> EVERY (fun v => v <? s.(dim)) d -> good_ra_state (with_freeze_wl s d).
Proof. unfold good_ra_state; rs2; tauto. Qed.
Lemma good_with_avail s d : good_ra_state s ->
  EVERY (fun '(p, (x, y)) => (x <? s.(dim)) && (y <? s.(dim))) d -> good_ra_state (with_avail_moves_wl s d).
Proof. unfold good_ra_state; rs; tauto. Qed.
Lemma good_with_unavail s d : good_ra_state s ->
  EVERY (fun '(p, (x, y)) => (x <? s.(dim)) && (y <? s.(dim))) d -> good_ra_state (with_unavail_moves_wl s d).
Proof. unfold good_ra_state; rs; tauto. Qed.

Lemma add_simp_wl_eq ls s : add_simp_wl ls s = (M_success tt, with_simp_wl s (ls ++ s.(simp_wl))).
Proof. reflexivity. Qed.
Lemma add_spill_wl_eq ls s : add_spill_wl ls s = (M_success tt, with_spill_wl s (ls ++ s.(spill_wl))).
Proof. reflexivity. Qed.
Lemma add_freeze_wl_eq ls s : add_freeze_wl ls s = (M_success tt, with_freeze_wl s (ls ++ s.(freeze_wl))).
Proof. reflexivity. Qed.
Lemma add_unavail_moves_wl_eq ls s :
  add_unavail_moves_wl ls s = (M_success tt, with_unavail_moves_wl s (ls ++ s.(unavail_moves_wl))).
Proof. reflexivity. Qed.

Lemma EVERY_moves_iff d (l : list (N * (N * N))) :
  is_true (EVERY (fun '(p, (x, y)) => (x <? d) && (y <? d)) l) <->
  (forall p x y, In (p, (x, y)) l -> x < d /\ y < d).
Proof.
  rewrite EVERY_iff; split.
  - intros H p x y Hin; specialize (H _ Hin); cbv beta iota in H; apply andb_iff in H as [H1 H2].
    split; apply ltb_iff; assumption.
  - intros H [p [x y]] Hin; apply andb_iff; split; apply ltb_iff; apply (H p x y Hin).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "unspill_success" *)
Theorem unspill_success : forall k s,
  good_ra_state s ->
  exists s',
    unspill k s = (M_success tt, s') /\
    good_ra_state s' /\
    is_subgraph s.(adj_ls) s'.(adj_ls) /\
    s.(dim) = s'.(dim) /\
    s.(node_tag) = s'.(node_tag).
Proof.
  intros k s Hg. good_destr Hg. unfold unspill.
  mstep' (get_dim_eq (E:=state_exn) s). mstep' (get_spill_wl_eq (E:=state_exn) s).
  destruct (st_ex_PARTITION_split_degree (spill_wl s) k [] [] s Hg) as (ts & fs & E1 & H1 & H2).
  mstep' E1. rewrite EVERY_iff in H1, H2.
  assert (Hts : forall x, In x ts -> x < dim s).
  { intros x Hx; specialize (H1 x Hx); apply orb_iff in H1 as [H1|H1]; [discriminate|].
    apply MEM_iff in H1; rewrite EVERY_lt_iff in B5; auto. }
  assert (Hfs : forall x, In x fs -> x < dim s).
  { intros x Hx; specialize (H2 x Hx); apply orb_iff in H2 as [H2|H2]; [discriminate|].
    apply MEM_iff in H2; rewrite EVERY_lt_iff in B5; auto. }
  destruct (revive_moves_success s ts) as (s1 & E2 & Hw & Ha & Hun).
  { apply EVERY_lt_iff; intros x Hx; rewrite L1; auto. }
  mstep' E2.
  remember (avail_moves_wl s1) as av eqn:Hav; remember (unavail_moves_wl s1) as uv eqn:Huv; subst s1; rs.
  destruct (st_ex_PARTITION_move_related_sub ts [] [] (with_unavail_moves_wl (with_avail_moves_wl s av) uv))
    as (tf & tsimp & E3 & H3 & H4).
  { rs; apply EVERY_lt_iff; intros x Hx; rewrite L5; auto. }
  mstep' E3. rewrite EVERY_iff in H3, H4.
  set (s2 := with_unavail_moves_wl (with_avail_moves_wl s av) uv) in *.
  mstep' (set_spill_wl_eq (E:=state_exn) fs s2). mstep' (add_simp_wl_eq tsimp (with_spill_wl s2 fs)).
  rewrite add_freeze_wl_eq. subst s2. rs2.
  eexists; split; [reflexivity|]. rs2.
  split; [|split; [apply is_subgraph_refl|split; reflexivity]].
  apply good_with_freeze_wl; [apply good_with_simp_wl; [apply good_with_spill_wl|]|]; rs2.
  - apply good_with_unavail; [apply good_with_avail|]; rs; auto.
    + apply EVERY_moves_iff; intros p x y Hin. rewrite EVERY_iff in Ha.
      specialize (Ha _ Hin); apply MEM_iff, in_app_iff in Ha.
      rewrite EVERY_moves_iff in B7, B8; destruct Ha; eauto.
    + apply EVERY_moves_iff; intros p x y Hin. rewrite EVERY_iff in Hun.
      specialize (Hun _ Hin); apply MEM_iff, in_app_iff in Hun.
      rewrite EVERY_moves_iff in B7, B8; destruct Hun; eauto.
  - apply EVERY_lt_iff, Hfs.
  - apply EVERY_lt_iff; intros x Hx; apply in_app_iff in Hx as [Hx|Hx].
    + specialize (H4 x Hx); apply orb_iff in H4 as [H4|H4]; [discriminate|]. apply MEM_iff in H4; auto.
    + rewrite EVERY_lt_iff in B4; auto.
  - apply EVERY_lt_iff; intros x Hx; apply in_app_iff in Hx as [Hx|Hx].
    + specialize (H3 x Hx); apply orb_iff in H3 as [H3|H3]; [discriminate|]. apply MEM_iff in H3; auto.
    + rewrite EVERY_lt_iff in B6; auto.
Qed.

Lemma push_stack_ok s x :
  good_ra_state s -> x < s.(dim) ->
  push_stack x s = (M_success tt, with_stack (with_move_related (with_degrees s (LUPDATE 0 x s.(degrees)))
                                  (LUPDATE false x s.(move_related))) (x :: s.(stack))).
Proof.
  intros Hg Hx; good_destr Hg. unfold push_stack.
  mstep' (get_stack_eq (E:=state_exn) s). mstep' (update_degrees_ok x 0 s ltac:(lia)).
  rs. mstep' (update_move_related_ok x false (with_degrees s (LUPDATE 0 x (degrees s))) ltac:(rs; lia)).
  reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "push_stack_success" *)
Theorem push_stack_success : forall ls s,
  EVERY (fun x => x <? s.(dim)) ls /\ good_ra_state s ->
  exists d mr st,
    st_ex_FOREACH ls push_stack s =
      (M_success tt, with_stack (with_move_related (with_degrees s d) mr) st) /\
    LENGTH d = LENGTH s.(degrees) /\ LENGTH mr = LENGTH s.(move_related).
Proof.
  induction ls as [|x ls IH]; intros s [Hev Hg]; cbn [st_ex_FOREACH].
  - exists (degrees s), (move_related s), (stack s); split; [destruct s; reflexivity|split; reflexivity].
  - cbn [EVERY] in Hev; apply andb_iff in Hev as [Hx Hev]; apply ltb_iff in Hx. good_destr Hg.
    mstep (push_stack_ok s x Hg Hx). rs.
    destruct (IH (with_stack (with_move_related (with_degrees s (LUPDATE 0 x (degrees s)))
                (LUPDATE false x (move_related s))) (x :: stack s))) as (d & mr & st & E & Hd & Hm).
    { rs; split; [exact Hev|]. apply good_with_stack, good_with_move_related; [apply good_with_degrees|]; rs;
        rewrite ?LENGTH_LUPDATE; auto. }
    exists d, mr, st; rs; rewrite E, Hd, Hm, !LENGTH_LUPDATE; split; [|split; reflexivity].
    destruct s; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "do_simplify_success" *)
Theorem do_simplify_success : forall k s,
  good_ra_state s ->
  exists s' b,
    do_simplify k s = (M_success b, s') /\
    good_ra_state s' /\
    is_subgraph s.(adj_ls) s'.(adj_ls) /\
    s.(dim) = s'.(dim) /\
    s.(node_tag) = s'.(node_tag).
Proof.
  intros k s Hg. good_destr Hg. unfold do_simplify.
  mstep' (get_simp_wl_eq (E:=state_exn) s).
  destruct (NULL (simp_wl s)).
  - exists s, false; split; [reflexivity|split; [exact Hg|split; [apply is_subgraph_refl|split; reflexivity]]].
  - destruct (dec_degree_success (simp_wl s) s Hg) as (d & E1 & Hl1). mstep' E1.
    destruct (push_stack_success (simp_wl s) (with_degrees s d)) as (d2 & mr & st & E2 & Hl2 & Hm2).
    { rs; split; [exact B4|apply good_with_degrees; [exact Hg|lia]]. }
    mstep' E2. rs. mstep' (set_simp_wl_eq (E:=state_exn) [] (with_stack (with_move_related (with_degrees (with_degrees s d) d2) mr) st)).
    destruct (unspill_success k (with_simp_wl (with_stack (with_move_related (with_degrees (with_degrees s d) d2) mr) st) []))
      as (s3 & E3 & Hg3 & Hs3 & Hd3 & Ht3).
    { apply good_with_simp_wl; [|reflexivity].
      apply good_with_stack, good_with_move_related; [apply good_with_degrees; [apply good_with_degrees; [exact Hg|lia]|]|]; rs; lia. }
    mstep' E3. rs2. exists s3, true; split; [reflexivity|split; [exact Hg3|split; [exact Hs3|split; assumption]]].
Qed.

(** ** Coalescing *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "st_ex_FILTER_is_not_coalesced" *)
Theorem st_ex_FILTER_is_not_coalesced : forall ls acc s,
  EVERY (fun x => x <? LENGTH s.(coalesced)) ls /\ EVERY (fun x => x <? LENGTH s.(coalesced)) acc ->
  exists ts, st_ex_FILTER is_not_coalesced ls acc s = (M_success ts, s) /\
    EVERY (fun x => x <? LENGTH s.(coalesced)) ts.
Proof.
  intros ls acc s [H1 H2]. rewrite EVERY_lt_iff in H1, H2.
  destruct (st_ex_FILTER_pure is_not_coalesced (fun _ => True) ls s acc) as (ts & E & Hts).
  { intros x Hx; unfold is_not_coalesced. eexists; split; [mstep' (coalesced_sub_ok x s (H1 x Hx)); reflexivity|auto]. }
  exists ts; split; [exact E|]. apply EVERY_lt_iff; intros x Hx; destruct (Hts x Hx) as [[_ ?]|?]; auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "consistency_ok_success" *)
Theorem consistency_ok_success : forall x y s,
  good_ra_state s /\ x < s.(dim) /\ y < s.(dim) ->
  exists b, consistency_ok x y s = (M_success b, s) /\ (b = true -> x < s.(dim) /\ y < s.(dim)).
Proof.
  intros x y s (Hg & Hx & Hy). good_destr Hg. unfold consistency_ok.
  destruct (x =? y); [eexists; split; [reflexivity|auto]|].
  mstep' (adj_ls_sub_ok y s ltac:(lia)). destruct (sorted_mem x _); [eexists; split; [reflexivity|auto]|].
  mstep' (is_Fixed_ok x s ltac:(lia)). mstep' (is_Fixed_ok y s ltac:(lia)).
  mstep' (move_related_sub_ok x s ltac:(lia)). mstep' (move_related_sub_ok y s ltac:(lia)).
  eexists; split; [reflexivity|auto].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "st_ex_FILTER_consistency_ok" *)
Theorem st_ex_FILTER_consistency_ok : forall (ls acc : list (N * (N * N))) s,
  good_ra_state s /\ EVERY (fun '(p, (x, y)) => (x <? s.(dim)) && (y <? s.(dim))) ls ->
  exists ts,
    st_ex_FILTER (fun '(_, (x, y)) => consistency_ok x y) ls acc s = (M_success ts, s) /\
    EVERY (fun '(p, (x, y)) => (x <? s.(dim)) && (y <? s.(dim)) || MEM (p, (x, y)) acc) ts.
Proof.
  intros ls acc s [Hg Hev]. rewrite EVERY_moves_iff in Hev.
  destruct (st_ex_FILTER_pure (fun '(_, (x, y)) => consistency_ok x y)
              (fun '(p, (x, y)) => x < s.(dim) /\ y < s.(dim)) ls s acc) as (ts & E & Hts).
  { intros [p [x y]] Hin. destruct (Hev p x y Hin) as [Hx Hy].
    destruct (consistency_ok_success x y s (conj Hg (conj Hx Hy))) as (b & Eb & Hb).
    exists b; split; [exact Eb|intros; split; assumption]. }
  exists ts; split; [exact E|]. apply EVERY_iff; intros [p [x y]] Hin.
  apply orb_iff; destruct (Hts _ Hin) as [[[Hx Hy] _]|H]; [left; apply andb_iff; split; apply ltb_iff; assumption|].
  right; apply MEM_iff, H.
Qed.

Lemma considered_var_ok k x s : x < LENGTH s.(node_tag) -> exists b, considered_var k x s = (M_success b, s).
Proof.
  intros Hx; unfold considered_var. mstep' (is_Atemp_ok x s Hx). mstep' (is_Fixed_k_ok k x s Hx).
  eexists; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "st_ex_FILTER_considered_var" *)
Theorem st_ex_FILTER_considered_var : forall k ls acc s,
  EVERY (fun x => x <? LENGTH s.(node_tag)) ls /\ EVERY (fun x => x <? LENGTH s.(node_tag)) acc ->
  exists ts, st_ex_FILTER (considered_var k) ls acc s = (M_success ts, s) /\
    EVERY (fun x => x <? LENGTH s.(node_tag)) ts.
Proof.
  intros k ls acc s [H1 H2]. rewrite EVERY_lt_iff in H1, H2.
  destruct (st_ex_FILTER_pure (considered_var k) (fun _ => True) ls s acc) as (ts & E & Hts).
  { intros x Hx; destruct (considered_var_ok k x s (H1 x Hx)) as [b Hb]; exists b; auto. }
  exists ts; split; [exact E|]. apply EVERY_lt_iff; intros x Hx; destruct (Hts x Hx) as [[_ ?]|?]; auto.
Qed.

(** HOL's anonymous [st_ex_MAP_deg_or_inf]. *)
Lemma st_ex_MAP_deg_or_inf : forall k ls s,
  good_ra_state s /\ EVERY (fun x => x <? s.(dim)) ls ->
  exists degs, st_ex_MAP (deg_or_inf k) ls s = (M_success degs, s).
Proof.
  intros k ls s [Hg Hev]; good_destr Hg; rewrite EVERY_lt_iff in Hev. apply st_ex_MAP_pure.
  intros x Hx; specialize (Hev x Hx); unfold deg_or_inf. mstep' (is_Fixed_k_ok k x s ltac:(lia)).
  destruct (match EL x (node_tag s) with Fixed n => n <? k | _ => false end);
    [eexists; reflexivity|eexists; apply degrees_sub_ok; lia].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "bg_ok_success" *)
Theorem bg_ok_success : forall s x y k,
  good_ra_state s /\ x < s.(dim) /\ y < s.(dim) ->
  exists opt, bg_ok k x y s = (M_success opt, s) /\
    match opt with
    | None => True
    | Some (case1, case2) => EVERY (fun v => v <? s.(dim)) case1 /\ EVERY (fun v => v <? s.(dim)) case2
    end.
Proof.
  intros s x y k (Hg & Hx & Hy). good_destr Hg. unfold bg_ok.
  mstep' (adj_ls_sub_ok x s ltac:(lia)). mstep' (adj_ls_sub_ok y s ltac:(lia)).
  match goal with |- context [PARTITION ?P ?l] => destruct (PARTITION P l) as [c1 c2] eqn:EP end. ms.
  assert (Hc1 : forall v, In v c1 -> v < dim s) by
    (intros v Hv; apply (proj1 (In_PARTITION _ _ _ _ v EP)) in Hv; eapply good_bound_adj; eauto).
  assert (Hc2 : forall v, In v c2 -> v < dim s) by
    (intros v Hv; apply (proj2 (In_PARTITION _ _ _ _ v EP)) in Hv; eapply good_bound_adj; eauto).
  assert (Hf : forall l, (forall v, In v l -> v < dim s) ->
     exists ts, st_ex_FILTER (considered_var k) l [] s = (M_success ts, s) /\ forall v, In v ts -> v < dim s).
  { intros l Hl. destruct (st_ex_FILTER_considered_var k l [] s) as (ts & E & Hts).
    { split; [apply EVERY_lt_iff; intros; rewrite L2; auto|reflexivity]. }
    exists ts; split; [exact E|]. rewrite EVERY_lt_iff in Hts; intros v Hv; rewrite <- L2; auto. }
  destruct (Hf c1 Hc1) as (ts1 & E1 & H1). mstep' E1.
  destruct (Hf c2 Hc2) as (ts2 & E2 & H2). mstep' E2.
  destruct (st_ex_MAP_deg_or_inf k ts2 s (conj Hg (proj2 (EVERY_lt_iff _ _) H2))) as (d2 & Ed2). mstep' Ed2. ms.
  destruct (_ =? 0).
  - eexists; split; [reflexivity|split; apply EVERY_lt_iff; assumption].
  - destruct (Hf (FILTER (fun v => negb (sorted_mem v (EL y (adj_ls s)))) (EL x (adj_ls s)))) as (ts3 & E3 & H3).
    { intros v Hv; apply filter_In in Hv as [Hv _]; exact (good_bound_adj s x v Hg Hx Hv). }
    mstep' E3.
    destruct (st_ex_MAP_deg_or_inf (k + 1) ts1 s (conj Hg (proj2 (EVERY_lt_iff _ _) H1))) as (d1 & Ed1). mstep' Ed1.
    destruct (st_ex_MAP_deg_or_inf k ts3 s (conj Hg (proj2 (EVERY_lt_iff _ _) H3))) as (d3 & Ed3). mstep' Ed3.
    ret. destruct (_ <? k); [eexists; split; [reflexivity|split; apply EVERY_lt_iff; assumption]|].
    eexists; split; [reflexivity|exact I].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "coalesce_parent_success" *)
Theorem coalesce_parent_success : forall x s,
  x < s.(dim) /\ good_ra_state s ->
  exists y s' coal,
    coalesce_parent x s = (M_success y, s') /\
    y < s.(dim) /\ good_ra_state s' /\ s' = with_coalesced s coal.
Proof.
  intros x; induction x as [x IH] using (well_founded_induction N.lt_wf_0); intros s [Hx Hg].
  good_destr Hg. rewrite coalesce_parent_def.
  mstep' (coalesced_sub_ok x s ltac:(lia)).
  assert (Hc : EL x (coalesced s) < dim s) by (rewrite EVERY_lt_iff in B1; apply B1, EL_In; lia).
  mstep' (is_Fixed_ok (EL x (coalesced s)) s ltac:(lia)).
  destruct (match EL (EL x (coalesced s)) (node_tag s) with Fixed _ => true | _ => false end).
  - exists (EL x (coalesced s)), s, (coalesced s); split; [reflexivity|split; [exact Hc|split; [exact Hg|destruct s; reflexivity]]].
  - destruct (N.leb_spec x (EL x (coalesced s))) as [Hle|Hlt].
    + exists x, s, (coalesced s); split; [reflexivity|split; [exact Hx|split; [exact Hg|destruct s; reflexivity]]].
    + destruct (IH (EL x (coalesced s)) Hlt s (conj Hc Hg)) as (y & s1 & c1 & E1 & Hy & Hg1 & ->).
      mstep' E1. pose proof Hg1 as (_ & _ & _ & L4' & _ & B1' & _). rs.
      mstep' (update_coalesced_ok x y (with_coalesced s c1) ltac:(rs; lia)). rs.
      exists y, (with_coalesced (with_coalesced s c1) (LUPDATE y x c1)), (LUPDATE y x c1).
      split; [reflexivity|split; [exact Hy|split; [|reflexivity]]].
      apply good_with_coalesced; [exact Hg1|rs; rewrite LENGTH_LUPDATE; lia|rs].
      apply EVERY_LUPDATE; [apply ltb_iff; exact Hy|exact B1'].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "canonize_move_success" *)
Theorem canonize_move_success : forall s x y,
  x < s.(dim) /\ y < s.(dim) /\ good_ra_state s ->
  exists x2 y2, canonize_move x y s = (M_success (x2, y2), s) /\ x2 < s.(dim) /\ y2 < s.(dim).
Proof.
  intros s x y (Hx & Hy & Hg). good_destr Hg. unfold canonize_move.
  mstep' (is_Fixed_ok x s ltac:(lia)). mstep' (is_Fixed_ok y s ltac:(lia)).
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    eexists _, _; (split; [reflexivity|]); auto.
Qed.

Lemma with_coalesced_twice s a b : with_coalesced (with_coalesced s a) b = with_coalesced s b.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "st_ex_FIRST_consistency_ok_bg_ok" *)
Theorem st_ex_FIRST_consistency_ok_bg_ok : forall k ls acc s,
  good_ra_state s /\
  EVERY (fun '(p, (x, y)) => (x <? s.(dim)) && (y <? s.(dim))) ls /\
  EVERY (fun '(p, (x, y)) => (x <? s.(dim)) && (y <? s.(dim))) acc ->
  exists ores ys s' coal,
    st_ex_FIRST consistency_ok (bg_ok k) ls acc s = (M_success (ores, ys), s') /\
    good_ra_state s' /\
    s' = with_coalesced s coal /\
    EVERY (fun '(p, (x, y)) => (x <? s.(dim)) && (y <? s.(dim))) ys /\
    match ores with
    | Some ((x, y), ((case1, case2), rest)) =>
        x < s.(dim) /\ y < s.(dim) /\
        EVERY (fun v => v <? s.(dim)) case1 /\ EVERY (fun v => v <? s.(dim)) case2 /\
        EVERY (fun '(p, (x, y)) => (x <? s.(dim)) && (y <? s.(dim))) rest
    | None => True
    end.
Proof.
  intros k; induction ls as [|[p [x y]] ms IH]; intros acc s (Hg & Hls & Hacc); cbn [st_ex_FIRST].
  - exists None, acc, s, (coalesced s); split; [reflexivity|split; [exact Hg|split; [destruct s; reflexivity|split; [exact Hacc|exact I]]]].
  - cbn [EVERY] in Hls; apply andb_iff in Hls as [Hxy Hls]; apply andb_iff in Hxy as [Hx Hy]; apply ltb_iff in Hx, Hy.
    destruct (coalesce_parent_success x s (conj Hx Hg)) as (x' & s1 & c1 & E1 & Hx' & Hg1 & ->). mstep' E1.
    destruct (coalesce_parent_success y (with_coalesced s c1) (conj Hy Hg1)) as (y' & s2 & c2 & E2 & Hy' & Hg2 & ->).
    mstep' E2. rs. rewrite with_coalesced_twice in *.
    destruct (consistency_ok_success x' y' (with_coalesced s c2) ltac:(rs; auto)) as (b & Eb & _). mstep' Eb.
    destruct b; cbn [negb].
    + destruct (canonize_move_success (with_coalesced s c2) x' y' ltac:(rs; auto)) as (x2 & y2 & Ec & Hx2 & Hy2).
      mstep' Ec. rs.
      destruct (bg_ok_success (with_coalesced s c2) x2 y2 k ltac:(rs; auto)) as (opt & Eo & Ho).
      mstep' Eo. rs. destruct opt as [[c1' c2']|].
      * exists (Some ((x2, y2), ((c1', c2'), ms))), acc, (with_coalesced s c2), c2.
        split; [reflexivity|split; [exact Hg2|split; [reflexivity|split; [exact Hacc|]]]].
        destruct Ho; auto.
      * destruct (IH ((p, (x2, y2)) :: acc) (with_coalesced s c2)) as (ores & ys & s' & coal & E & Hg' & -> & Hys & Hores).
        { rs. split; [exact Hg2|split; [exact Hls|]]. cbn [EVERY]; apply andb_iff; split; [apply andb_iff; split; apply ltb_iff; assumption|exact Hacc]. }
        rs. exists ores, ys, (with_coalesced s coal), coal. rewrite E. auto.
    + destruct (IH acc (with_coalesced s c2)) as (ores & ys & s' & coal & E & Hg' & -> & Hys & Hores).
      { rs. auto. }
      rs. exists ores, ys, (with_coalesced s coal), coal. rewrite E. auto.
Qed.

Definition hok (s s' : ra_state) : Prop :=
  good_ra_state s' /\ is_subgraph s.(adj_ls) s'.(adj_ls) /\ s.(dim) = s'.(dim) /\ s.(node_tag) = s'.(node_tag).

Lemma hok_trans s1 s2 s3 : hok s1 s2 -> hok s2 s3 -> hok s1 s3.
Proof.
  intros (G2 & S2 & D2 & T2) (G3 & S3 & D3 & T3); split; [exact G3|split; [|split; congruence]].
  apply (is_subgraph_trans _ (adj_ls s2)); split; assumption.
Qed.

Lemma hok_refl s : good_ra_state s -> hok s s.
Proof. intros Hg; split; [exact Hg|split; [apply is_subgraph_refl|split; reflexivity]]. Qed.

Lemma hok_same s s' : good_ra_state s' -> s.(adj_ls) = s'.(adj_ls) -> s.(dim) = s'.(dim) ->
  s.(node_tag) = s'.(node_tag) -> hok s s'.
Proof. intros G A D T; split; [exact G|split; [rewrite A; apply is_subgraph_refl|split; assumption]]. Qed.

Lemma dec_degree_ok s x : good_ra_state s ->
  exists d, dec_degree x s = (M_success tt, with_degrees s d) /\ LENGTH d = LENGTH (degrees s).
Proof.
  intros Hg; good_destr Hg. unfold dec_degree. mstep' (get_dim_eq (E:=state_exn) s).
  destruct (N.ltb_spec x (dim s)) as [Hx|Hx].
  - mstep' (adj_ls_sub_ok x s ltac:(lia)). apply dec_deg_success; split; [|exact Hg].
    apply EVERY_lt_iff; intros y Hy; eapply good_bound_adj; eauto.
  - exists (degrees s); split; [destruct s; reflexivity|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "do_coalesce_real_success" *)
Theorem do_coalesce_real_success : forall x y case1 case2 s,
  y < s.(dim) /\ x < s.(dim) /\
  EVERY (fun v => v <? s.(dim)) case1 /\ EVERY (fun v => v <? s.(dim)) case2 /\
  good_ra_state s ->
  exists s',
    do_coalesce_real x y case1 case2 s = (M_success tt, s') /\
    good_ra_state s' /\
    is_subgraph s.(adj_ls) s'.(adj_ls) /\
    s.(dim) = s'.(dim) /\
    s.(node_tag) = s'.(node_tag).
Proof.
  intros x y case1 case2 s (Hy & Hx & Hc1 & Hc2 & Hg). good_destr Hg. unfold do_coalesce_real.
  mstep' (update_coalesced_ok y x s ltac:(lia)). set (s1 := with_coalesced s (LUPDATE x y (coalesced s))).
  assert (Hg1 : good_ra_state s1).
  { apply good_with_coalesced; [exact Hg|rewrite LENGTH_LUPDATE; lia|apply EVERY_LUPDATE; [apply ltb_iff; exact Hx|exact B1]]. }
  mstep' (is_Fixed_ok x s1 ltac:(subst s1; rs; lia)).
  assert (Hs2 : exists s2, (if match EL x (node_tag s1) with Fixed _ => true | _ => false end
                           then st_ex_return tt else inc_deg x (LENGTH case2)) s1 = (M_success tt, s2) /\ hok s1 s2).
  { destruct (match EL x (node_tag s1) with Fixed _ => true | _ => false end).
    - exists s1; split; [reflexivity|apply hok_refl, Hg1].
    - unfold inc_deg. mstep' (degrees_sub_ok x s1 ltac:(subst s1; rs; lia)).
      rewrite (update_degrees_ok x _ s1 ltac:(subst s1; rs; lia)). eexists; split; [reflexivity|].
      apply hok_same; subst s1; rs; try reflexivity. apply good_with_degrees; [exact Hg1|rs; rewrite LENGTH_LUPDATE; lia]. }
  destruct Hs2 as (s2 & E2 & Hok2). mstep' E2.
  pose proof Hok2 as (Hg2 & _ & D2 & T2). subst s1; rs.
  destruct (list_insert_edge_succeeds case2 x s2) as (s3 & E3 & Hg3 & Hw3 & He3).
  { split; [exact Hg2|split; [lia|rewrite <- D2; exact Hc2]]. }
  mstep' E3. wsubst Hw3. rs.
  destruct (dec_deg_success case1 (with_adj_ls s2 t)) as (d & E4 & Hl4).
  { rs; split; [rewrite <- D2; exact Hc1|exact Hg3]. }
  mstep' E4. rs.
  assert (Hg4 : good_ra_state (with_degrees (with_adj_ls s2 t) d)).
  { pose proof Hg3 as (_ & _ & L3' & _); apply good_with_degrees; [exact Hg3|rs; lia]. }
  rewrite (push_stack_ok _ y Hg4 ltac:(rs; lia)).
  eexists; split; [reflexivity|].
  assert (Hok : hok s2 (with_stack (with_move_related (with_degrees (with_degrees (with_adj_ls s2 t) d)
       (LUPDATE 0 y (degrees (with_degrees (with_adj_ls s2 t) d))))
     (LUPDATE false y (move_related (with_degrees (with_adj_ls s2 t) d))))
    (y :: stack (with_degrees (with_adj_ls s2 t) d)))).
  { split; [|split; [rs; intros a b H; apply He3; tauto|rs; split; reflexivity]].
    pose proof Hg4 as (_ & _ & L3' & _ & L5' & _). rs.
    apply good_with_stack, good_with_move_related; [apply good_with_degrees; [exact Hg4|]|]; rs;
      rewrite LENGTH_LUPDATE; lia. }
  destruct (hok_trans _ _ _ Hok2 Hok) as (G & S & D & T). rs.
  split; [exact G|split; [exact S|split; assumption]].
Qed.

Lemma respill_ok k x s : good_ra_state s -> x < s.(dim) ->
  exists s', respill k x s = (M_success tt, s') /\ hok s s'.
Proof.
  intros Hg Hx; good_destr Hg. unfold respill. mstep' (degrees_sub_ok x s ltac:(lia)).
  destruct (_ <? k); [eexists; split; [reflexivity|apply hok_refl, Hg]|].
  mstep' (get_freeze_wl_eq (E:=state_exn) s). destruct (MEM x (freeze_wl s)) eqn:Em;
    [|eexists; split; [reflexivity|apply hok_refl, Hg]].
  mstep' (add_spill_wl_eq [x] s). rewrite set_freeze_wl_eq. eexists; split; [reflexivity|].
  apply hok_same; rs2; try reflexivity.
  apply good_with_freeze_wl; [apply good_with_spill_wl; [exact Hg|]|]; rs2.
  - apply EVERY_lt_iff; intros v Hv; apply in_app_iff in Hv as [[<-|[]]|Hv]; [exact Hx|].
    rewrite EVERY_lt_iff in B5; auto.
  - apply EVERY_lt_iff; intros v Hv; apply filter_In in Hv as [Hv _]. rewrite EVERY_lt_iff in B6; auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "do_coalesce_success" *)
Theorem do_coalesce_success : forall k s,
  good_ra_state s ->
  exists s' b,
    do_coalesce k s = (M_success b, s') /\
    good_ra_state s' /\
    is_subgraph s.(adj_ls) s'.(adj_ls) /\
    s.(dim) = s'.(dim) /\
    s.(node_tag) = s'.(node_tag).
Proof.
  intros k s Hg. good_destr Hg. unfold do_coalesce.
  mstep' (get_avail_moves_wl_eq (E:=state_exn) s).
  destruct (st_ex_FIRST_consistency_ok_bg_ok k (avail_moves_wl s) [] s) as (ores & ys & s1 & coal & E1 & Hg1 & -> & Hys & Hores).
  { split; [exact Hg|split; [exact B7|reflexivity]]. }
  mstep' E1. rs. mstep' (add_unavail_moves_wl_eq ys (with_coalesced s coal)). rs.
  set (s2 := with_unavail_moves_wl (with_coalesced s coal) (ys ++ unavail_moves_wl s)).
  assert (Hok2 : hok s s2).
  { apply hok_same; subst s2; rs; try reflexivity. apply good_with_unavail; [exact Hg1|]. rs.
    apply EVERY_moves_iff; intros p a b Hin; apply in_app_iff in Hin as [Hin|Hin];
      [rewrite EVERY_moves_iff in Hys|rewrite EVERY_moves_iff in B8]; eauto. }
  destruct ores as [[[x y] [[case1 case2] ms]]|].
  - destruct Hores as (Hx & Hy & Hc1 & Hc2 & Hms).
    mstep' (set_avail_moves_wl_eq (E:=state_exn) ms s2).
    assert (Hok3 : hok s (with_avail_moves_wl s2 ms)).
    { apply (hok_trans _ s2); [exact Hok2|]. apply hok_same; rs; try reflexivity.
      apply good_with_avail; [exact (proj1 Hok2)|subst s2; rs; exact Hms]. }
    pose proof Hok3 as (G3 & _ & D3 & _).
    destruct (do_coalesce_real_success x y case1 case2 (with_avail_moves_wl s2 ms)) as (s4 & E4 & G4 & S4 & D4 & T4).
    { rewrite <- D3; auto. }
    mstep' E4.
    destruct (unspill_success k s4 G4) as (s5 & E5 & G5 & S5 & D5 & T5). mstep' E5.
    destruct (respill_ok k x s5 G5 ltac:(lia)) as (s6 & E6 & Hok6). mstep' E6.
    exists s6, true; split; [reflexivity|].
    assert (Hok : hok s s6).
    { apply (hok_trans _ _ _ Hok3), (hok_trans _ s4); [split; auto|].
      apply (hok_trans _ s5); [split; auto|exact Hok6]. }
    destruct Hok as (? & ? & ? & ?); auto.
  - mstep' (set_avail_moves_wl_eq (E:=state_exn) [] s2). exists (with_avail_moves_wl s2 []), false.
    split; [reflexivity|].
    assert (Hok : hok s (with_avail_moves_wl s2 [])).
    { apply (hok_trans _ s2); [exact Hok2|]. apply hok_same; rs; try reflexivity.
      apply good_with_avail; [exact (proj1 Hok2)|reflexivity]. }
    destruct Hok as (? & ? & ? & ?); auto.
Qed.

(** ** Freezing *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "st_ex_FOREACH_update_move_related" *)
Theorem st_ex_FOREACH_update_move_related : forall ls s b,
  EVERY (fun v => v <? LENGTH s.(move_related)) ls ->
  exists lss,
    st_ex_FOREACH ls (fun x => update_move_related x b) s = (M_success tt, with_move_related s lss) /\
    LENGTH lss = LENGTH s.(move_related).
Proof.
  induction ls as [|x ls IH]; intros s b Hev; cbn [st_ex_FOREACH].
  - exists (move_related s); split; [destruct s; reflexivity|reflexivity].
  - cbn [EVERY] in Hev; apply andb_iff in Hev as [Hx Hev]; apply ltb_iff in Hx.
    mstep (update_move_related_ok x b s Hx). rs.
    destruct (IH (with_move_related s (LUPDATE b x (move_related s))) b) as (lss & E & Hl).
    { rs; rewrite LENGTH_LUPDATE; exact Hev. }
    exists lss; split; [rewrite E; reflexivity|]. rewrite Hl; rs; apply LENGTH_LUPDATE.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "reset_move_related_success" *)
Theorem reset_move_related_success : forall ls s,
  good_ra_state s /\ EVERY (fun '(p, (x, y)) => (x <? s.(dim)) && (y <? s.(dim))) ls ->
  exists mv, reset_move_related ls s = (M_success tt, with_move_related s mv) /\ LENGTH mv = s.(dim).
Proof.
  intros ls s [Hg Hev]. good_destr Hg. unfold reset_move_related.
  mstep' (get_dim_eq (E:=state_exn) s).
  destruct (st_ex_FOREACH_update_move_related (COUNT_LIST (dim s)) s false) as (lss & E1 & Hl1).
  { apply EVERY_lt_iff; intros v Hv; apply In_COUNT_LIST in Hv; lia. }
  mstep E1. rewrite EVERY_moves_iff in Hev.
  assert (H : forall (l : list (N * (N * N))) (s0 : ra_state) mv0, (forall p x y, In (p, (x, y)) l -> x < dim s /\ y < dim s) ->
     LENGTH mv0 = dim s -> LENGTH (node_tag s0) = dim s ->
     exists mv, st_ex_FOREACH l (fun '(_, (x, y)) =>
        bx <- is_Fixed x ;; by_ <- is_Fixed y ;;
        update_move_related x (negb bx) ;; update_move_related y (negb by_)) (with_move_related s0 mv0) =
      (M_success tt, with_move_related s0 mv) /\ LENGTH mv = dim s).
  { clear -L2. intros l; induction l as [|[p [x y]] l IH]; intros s0 mv0 Hb Hm Ht; cbn [st_ex_FOREACH].
    - exists mv0; split; [reflexivity|exact Hm].
    - destruct (Hb p x y (or_introl eq_refl)) as [Hx Hy].
      set (bx := match EL x (node_tag s0) with Fixed _ => true | _ => false end).
      set (by_ := match EL y (node_tag s0) with Fixed _ => true | _ => false end).
      match goal with |- context [st_ex_ignore_bind ?m _ (with_move_related s0 mv0)] =>
        assert (Hstep : m (with_move_related s0 mv0) =
          (M_success tt, with_move_related s0 (LUPDATE (negb by_) y (LUPDATE (negb bx) x mv0)))) end.
      { cbv beta iota.
        rewrite (bind_ok _ _ _ _ _ (is_Fixed_ok x (with_move_related s0 mv0) ltac:(rs; lia))). cbv beta.
        rewrite (bind_ok _ _ _ _ _ (is_Fixed_ok y (with_move_related s0 mv0) ltac:(rs; lia))). cbv beta.
        rewrite (ibind_ok _ _ _ _ _ (update_move_related_ok x _ (with_move_related s0 mv0) ltac:(rs; lia))). rs.
        rewrite (update_move_related_ok y _ _) by (rs; rewrite LENGTH_LUPDATE; lia). reflexivity. }
      mstep Hstep.
      destruct (IH s0 (LUPDATE (negb by_) y (LUPDATE (negb bx) x mv0))) as (mv & E & Hl).
      + intros p' x' y' Hin; apply (Hb p' x' y'); right; exact Hin.
      + rewrite !LENGTH_LUPDATE; exact Hm.
      + exact Ht.
      + exists mv; split; [|exact Hl]. exact E. }
  destruct (H ls s lss Hev ltac:(lia) L2) as (mv & E & Hl).
  exists mv; split; [rewrite E; reflexivity|exact Hl].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "do_prefreeze_success" *)
Theorem do_prefreeze_success : forall k s,
  good_ra_state s ->
  exists s' b,
    do_prefreeze k s = (M_success b, s') /\
    good_ra_state s' /\
    is_subgraph s.(adj_ls) s'.(adj_ls) /\
    s.(dim) = s'.(dim) /\
    s.(node_tag) = s'.(node_tag).
Proof.
  intros k s Hg. good_destr Hg. unfold do_prefreeze.
  mstep' (get_freeze_wl_eq (E:=state_exn) s).
  destruct (st_ex_FILTER_is_not_coalesced (freeze_wl s) [] s) as (ts1 & E1 & H1).
  { split; [rewrite L4; exact B6|reflexivity]. }
  mstep' E1. mstep' (get_spill_wl_eq (E:=state_exn) s).
  destruct (st_ex_FILTER_is_not_coalesced (spill_wl s) [] s) as (ts2 & E2 & H2).
  { split; [rewrite L4; exact B5|reflexivity]. }
  mstep' E2. mstep' (set_spill_wl_eq (E:=state_exn) ts2 s). rs2.
  mstep' (get_unavail_moves_wl_eq (E:=state_exn) (with_spill_wl s ts2)). rs2.
  assert (Hg1 : good_ra_state (with_spill_wl s ts2)) by (apply good_with_spill_wl; [exact Hg|rewrite <- L4; exact H2]).
  destruct (st_ex_FILTER_consistency_ok (unavail_moves_wl s) [] (with_spill_wl s ts2)) as (ts3 & E3 & H3).
  { rs2; split; [exact Hg1|exact B8]. }
  mstep' E3. rs2.
  destruct (reset_move_related_success ts3 (with_spill_wl s ts2)) as (mv & E4 & Hl4).
  { split; [exact Hg1|]. rs2. apply EVERY_moves_iff; intros p x y Hin; rewrite EVERY_iff in H3.
    specialize (H3 _ Hin); cbv beta iota in H3; apply orb_iff in H3 as [H3|H3]; [|discriminate].
    apply andb_iff in H3 as [? ?]; split; apply ltb_iff; assumption. }
  mstep' E4. rs2.
  set (s3 := with_move_related (with_spill_wl s ts2) mv).
  mstep' (set_unavail_moves_wl_eq (E:=state_exn) ts3 s3).
  destruct (st_ex_PARTITION_move_related_sub ts1 [] [] (with_unavail_moves_wl s3 ts3)) as (tf & tsimp & E5 & H5 & H6).
  { subst s3; rs2; rewrite Hl4, <- L4; exact H1. }
  mstep' E5. mstep' (add_simp_wl_eq tsimp (with_unavail_moves_wl s3 ts3)).
  mstep' (set_freeze_wl_eq (E:=state_exn) tf (with_simp_wl (with_unavail_moves_wl s3 ts3)
     (tsimp ++ simp_wl (with_unavail_moves_wl s3 ts3)))).
  rewrite EVERY_iff in H5, H6. rewrite EVERY_lt_iff in H1, H2.
  set (s4 := with_freeze_wl (with_simp_wl (with_unavail_moves_wl s3 ts3) (tsimp ++ simp_wl (with_unavail_moves_wl s3 ts3))) tf).
  assert (Hg4 : good_ra_state s4).
  { subst s4 s3. apply good_with_freeze_wl; [apply good_with_simp_wl; [apply good_with_unavail;
      [apply good_with_move_related; [exact Hg1|rs2; exact Hl4]|]|]|]; rs2.
    - apply EVERY_moves_iff; intros p x y Hin; rewrite EVERY_iff in H3.
      specialize (H3 _ Hin); cbv beta iota in H3; apply orb_iff in H3 as [H3|H3]; [|discriminate].
      apply andb_iff in H3 as [? ?]; split; apply ltb_iff; assumption.
    - apply EVERY_lt_iff; intros x Hx; apply in_app_iff in Hx as [Hx|Hx].
      + specialize (H6 x Hx); apply orb_iff in H6 as [H6|H6]; [discriminate|apply MEM_iff in H6]. rewrite <- L4; auto.
      + rewrite EVERY_lt_iff in B4; auto.
    - apply EVERY_lt_iff; intros x Hx.
      specialize (H5 x Hx); apply orb_iff in H5 as [H5|H5]; [discriminate|apply MEM_iff in H5]. rs2; rewrite <- L4; auto. }
  destruct (do_simplify_success k s4 Hg4) as (s5 & b & E6 & G5 & S5 & D5 & T5).
  exists s5, b; split; [exact E6|split; [exact G5|]]. subst s4 s3; rs2. auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "do_freeze_success" *)
Theorem do_freeze_success : forall k s,
  good_ra_state s ->
  exists s' b,
    do_freeze k s = (M_success b, s') /\
    good_ra_state s' /\
    is_subgraph s.(adj_ls) s'.(adj_ls) /\
    s.(dim) = s'.(dim) /\
    s.(node_tag) = s'.(node_tag).
Proof.
  intros k s Hg. good_destr Hg. unfold do_freeze.
  mstep' (get_freeze_wl_eq (E:=state_exn) s).
  destruct (freeze_wl s) as [|x xs] eqn:Ef.
  - exists s, false; split; [reflexivity|split; [exact Hg|split; [apply is_subgraph_refl|split; reflexivity]]].
  - cbn [EVERY] in B6; apply andb_iff in B6 as [Hx Hxs]; apply ltb_iff in Hx.
    destruct (dec_degree_ok s x Hg) as (d & E1 & Hl1). mstep' E1.
    assert (Hg1 : good_ra_state (with_degrees s d)) by (apply good_with_degrees; [exact Hg|lia]).
    mstep' (push_stack_ok (with_degrees s d) x Hg1 ltac:(rs; lia)). rs.
    set (s2 := with_stack (with_move_related (with_degrees (with_degrees s d) (LUPDATE 0 x d))
                 (LUPDATE false x (move_related s))) (x :: stack s)).
    mstep' (set_freeze_wl_eq (E:=state_exn) xs s2).
    assert (Hg3 : good_ra_state (with_freeze_wl s2 xs)).
    { subst s2; apply good_with_freeze_wl; [apply good_with_stack, good_with_move_related;
        [apply good_with_degrees; [exact Hg1|]|]|]; rs2; rewrite ?LENGTH_LUPDATE; auto; lia. }
    destruct (unspill_success k (with_freeze_wl s2 xs) Hg3) as (s4 & E4 & G4 & S4 & D4 & T4). mstep' E4.
    exists s4, true; split; [reflexivity|]. subst s2; rs2. auto.
Qed.

(** ** Spilling *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "st_ex_list_MIN_cost_success" *)
Theorem st_ex_list_MIN_cost_success : forall scost ls s k v acc,
  good_ra_state s /\ EVERY (fun v => v <? s.(dim)) acc /\ k < s.(dim) ->
  exists x y,
    st_ex_list_MIN_cost scost ls s.(dim) k v acc s = (M_success (x, y), s) /\
    x < s.(dim) /\ EVERY (fun v => v <? s.(dim)) y.
Proof.
  intros scost; induction ls as [|h ls IH]; intros s k v acc (Hg & Hacc & Hk); cbn [st_ex_list_MIN_cost].
  - exists k, acc; auto.
  - good_destr Hg. destruct (N.ltb_spec h (dim s)) as [Hh|Hh]; [|apply IH; auto].
    mstep' (degrees_sub_ok h s ltac:(lia)). ret.
    destruct (_ <? v); apply IH; (split; [exact Hg|split; [|lia]]); cbn [EVERY];
      apply andb_iff; split; auto; apply ltb_iff; lia.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "st_ex_list_MAX_deg_success" *)
Theorem st_ex_list_MAX_deg_success : forall ls s k v acc,
  good_ra_state s /\ EVERY (fun v => v <? s.(dim)) acc /\ k < s.(dim) ->
  exists x y,
    st_ex_list_MAX_deg ls s.(dim) k v acc s = (M_success (x, y), s) /\
    x < s.(dim) /\ EVERY (fun v => v <? s.(dim)) y.
Proof.
  induction ls as [|h ls IH]; intros s k v acc (Hg & Hacc & Hk); cbn [st_ex_list_MAX_deg].
  - exists k, acc; auto.
  - good_destr Hg. destruct (N.ltb_spec h (dim s)) as [Hh|Hh]; [|apply IH; auto].
    mstep' (degrees_sub_ok h s ltac:(lia)).
    destruct (_ <? _); apply IH; (split; [exact Hg|split; [|lia]]); cbn [EVERY];
      apply andb_iff; split; auto; apply ltb_iff; lia.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "do_spill_success" *)
Theorem do_spill_success : forall scost k s,
  good_ra_state s ->
  exists s' b,
    do_spill scost k s = (M_success b, s') /\
    good_ra_state s' /\
    is_subgraph s.(adj_ls) s'.(adj_ls) /\
    s.(dim) = s'.(dim) /\
    s.(node_tag) = s'.(node_tag).
Proof.
  intros scost k s Hg. good_destr Hg. unfold do_spill.
  mstep' (get_spill_wl_eq (E:=state_exn) s). mstep' (get_dim_eq (E:=state_exn) s).
  destruct (spill_wl s) as [|x xs] eqn:Es.
  - exists s, false; split; [reflexivity|split; [exact Hg|split; [apply is_subgraph_refl|split; reflexivity]]].
  - cbn [EVERY] in B5; apply andb_iff in B5 as [Hx Hxs]; apply ltb_iff in Hx.
    mstep' (degrees_sub_ok x s ltac:(lia)).
    assert (Hsel : exists y ys, (match scost with
        | None => st_ex_list_MAX_deg xs (dim s) x (EL x (degrees s)) []
        | Some scost0 => st_ex_list_MIN_cost scost0 xs (dim s) x
                           (safe_div (lookup_any x scost0 0) (EL x (degrees s))) []
        end) s = (M_success (y, ys), s) /\ y < dim s /\ EVERY (fun v => v <? dim s) ys).
    { destruct scost as [sc|]; [apply st_ex_list_MIN_cost_success|apply st_ex_list_MAX_deg_success]; auto. }
    destruct Hsel as (y & ys & E1 & Hy & Hys). mstep' E1.
    destruct (dec_degree_ok s y Hg) as (d & E2 & Hl2). mstep' E2.
    assert (Hg1 : good_ra_state (with_degrees s d)) by (apply good_with_degrees; [exact Hg|lia]).
    mstep' (push_stack_ok (with_degrees s d) y Hg1 ltac:(rs; lia)). rs.
    set (s2 := with_stack (with_move_related (with_degrees (with_degrees s d) (LUPDATE 0 y d))
                 (LUPDATE false y (move_related s))) (y :: stack s)).
    mstep' (set_spill_wl_eq (E:=state_exn) ys s2).
    assert (Hg3 : good_ra_state (with_spill_wl s2 ys)).
    { subst s2; apply good_with_spill_wl; [apply good_with_stack, good_with_move_related;
        [apply good_with_degrees; [exact Hg1|]|]|]; rs2; rewrite ?LENGTH_LUPDATE; auto; lia. }
    destruct (unspill_success k (with_spill_wl s2 ys) Hg3) as (s4 & E4 & G4 & S4 & D4 & T4). mstep' E4.
    exists s4, true; split; [reflexivity|]. subst s2; rs2. auto.
Qed.

(** ** The main loop *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "do_step_success" *)
Theorem do_step_success : forall scost k s,
  good_ra_state s ->
  exists b s',
    do_step scost k s = (M_success b, s') /\
    good_ra_state s' /\
    is_subgraph s.(adj_ls) s'.(adj_ls) /\
    s.(dim) = s'.(dim) /\
    s.(node_tag) = s'.(node_tag).
Proof.
  intros scost k s Hg. unfold do_step.
  destruct (do_simplify_success k s Hg) as (s1 & b1 & E1 & G1 & S1 & D1 & T1). mstep' E1.
  destruct b1; [exists true, s1; auto|].
  destruct (do_coalesce_success k s1 G1) as (s2 & b2 & E2 & G2 & S2 & D2 & T2). mstep' E2.
  assert (H12 : hok s s2) by (apply (hok_trans _ s1); split; auto).
  destruct b2; [exists true, s2; exact (conj eq_refl H12)|].
  destruct (do_prefreeze_success k s2 G2) as (s3 & b3 & E3 & G3 & S3 & D3 & T3). mstep' E3.
  assert (H13 : hok s s3) by (apply (hok_trans _ s2); [exact H12|split; auto]).
  destruct b3; [exists true, s3; exact (conj eq_refl H13)|].
  destruct (do_freeze_success k s3 G3) as (s4 & b4 & E4 & G4 & S4 & D4 & T4). mstep' E4.
  assert (H14 : hok s s4) by (apply (hok_trans _ s3); [exact H13|split; auto]).
  destruct b4; [exists true, s4; exact (conj eq_refl H14)|].
  destruct (do_spill_success scost k s4 G4) as (s5 & b5 & E5 & G5 & S5 & D5 & T5). mstep' E5.
  assert (H15 : hok s s5) by (apply (hok_trans _ s4); [exact H14|split; auto]).
  exists b5, s5; exact (conj eq_refl H15).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "rpt_do_step_success" *)
Theorem rpt_do_step_success : forall scost n s k,
  good_ra_state s ->
  exists s',
    rpt_do_step scost k n s = (M_success tt, s') /\
    good_ra_state s' /\
    is_subgraph s.(adj_ls) s'.(adj_ls) /\
    s.(dim) = s'.(dim) /\
    s.(node_tag) = s'.(node_tag).
Proof.
  intros scost n; induction n as [|n IH] using N.peano_ind; intros s k Hg.
  - rewrite (proj1 (rpt_do_step_def scost k 0)). exists s; split; [reflexivity|].
    exact (hok_refl s Hg).
  - rewrite (proj2 (rpt_do_step_def scost k n)).
    destruct (do_step_success scost k s Hg) as (b & s1 & E1 & G1 & S1 & D1 & T1). mstep' E1.
    destruct b.
    + destruct (IH s1 k G1) as (s2 & E2 & G2 & S2 & D2 & T2). exists s2; split; [exact E2|].
      exact (hok_trans _ s1 _ (conj G1 (conj S1 (conj D1 T1))) (conj G2 (conj S2 (conj D2 T2)))).
    + exists s1; split; [reflexivity|]. exact (conj G1 (conj S1 (conj D1 T1))).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "full_consistency_ok_success" *)
Theorem full_consistency_ok_success : forall k x y s,
  good_ra_state s ->
  exists b, full_consistency_ok k x y s = (M_success b, s) /\ (b = true -> x < s.(dim) /\ y < s.(dim)).
Proof.
  intros k x y s Hg. good_destr Hg. unfold full_consistency_ok.
  destruct (x =? y); [eexists; split; [reflexivity|discriminate]|].
  mstep' (get_dim_eq (E:=state_exn) s).
  destruct (N.leb_spec (dim s) x), (N.leb_spec (dim s) y); cbn [orb];
    try (eexists; split; [reflexivity|discriminate]).
  mstep' (adj_ls_sub_ok y s ltac:(lia)). destruct (sorted_mem x _); [eexists; split; [reflexivity|discriminate]|].
  mstep' (is_Fixed_k_ok k x s ltac:(lia)). mstep' (is_Fixed_k_ok k y s ltac:(lia)).
  mstep' (is_Atemp_ok x s ltac:(lia)). mstep' (is_Atemp_ok y s ltac:(lia)).
  eexists; split; [reflexivity|intros; split; lia].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "st_ex_FILTER_full_consistency_ok" *)
Theorem st_ex_FILTER_full_consistency_ok : forall k (ls acc : list (N * (N * N))) s,
  good_ra_state s ->
  exists ts,
    st_ex_FILTER (fun '(_, (x, y)) => full_consistency_ok k x y) ls acc s = (M_success ts, s) /\
    EVERY (fun '(p, (x, y)) => (x <? s.(dim)) && (y <? s.(dim)) || MEM (p, (x, y)) acc) ts.
Proof.
  intros k ls acc s Hg.
  destruct (st_ex_FILTER_pure (fun '(_, (x, y)) => full_consistency_ok k x y)
              (fun '(p, (x, y)) => x < s.(dim) /\ y < s.(dim)) ls s acc) as (ts & E & Hts).
  { intros [p [x y]] _. destruct (full_consistency_ok_success k x y s Hg) as (b & Eb & Hb).
    exists b; split; [exact Eb|exact Hb]. }
  exists ts; split; [exact E|]. apply EVERY_iff; intros [p [x y]] Hin.
  apply orb_iff; destruct (Hts _ Hin) as [[[Hx Hy] _]|H]; [left; apply andb_iff; split; apply ltb_iff; assumption|].
  right; apply MEM_iff, H.
Qed.

Lemma init_degrees_ok k s : good_ra_state s -> forall (l : list N) dd,
  (forall i, In i l -> i < s.(dim)) -> LENGTH dd = s.(dim) ->
  exists dd',
    st_ex_FOREACH l (fun i =>
      adjls <- adj_ls_sub i ;;
      fills <- st_ex_FILTER (fun v => considered_var k v) adjls [] ;;
      update_degrees i (LENGTH fills)) (with_degrees s dd) = (M_success tt, with_degrees s dd') /\
    LENGTH dd' = s.(dim).
Proof.
  intros Hg; good_destr Hg. induction l as [|i l IH]; intros dd Hl Hdd; cbn [st_ex_FOREACH].
  - exists dd; split; [reflexivity|exact Hdd].
  - assert (Hi : i < dim s) by (apply Hl; left; reflexivity).
    unfold st_ex_ignore_bind at 1.
    rewrite (bind_ok _ _ _ _ _ (adj_ls_sub_ok i (with_degrees s dd) ltac:(rs; lia))). cbv beta. rs.
    destruct (st_ex_FILTER_considered_var k (EL i (adj_ls s)) [] (with_degrees s dd)) as (ts & E & _).
    { rs; split; [apply EVERY_lt_iff; intros y Hy; rewrite L2; eapply good_bound_adj; eauto|reflexivity]. }
    assert (E' : st_ex_FILTER (fun v => considered_var k v) (EL i (adj_ls s)) [] (with_degrees s dd) =
                 (M_success ts, with_degrees s dd)) by exact E.
    rewrite (bind_ok _ _ _ _ _ E'). cbv beta.
    rewrite (update_degrees_ok i (LENGTH ts) (with_degrees s dd) ltac:(rs; lia)). rs. cbv beta iota.
    destruct (IH (LUPDATE (LENGTH ts) i dd)) as (dd' & E2 & H2).
    + intros j Hj; apply Hl; right; exact Hj.
    + rewrite LENGTH_LUPDATE; exact Hdd.
    + exists dd'; split; [exact E2|exact H2].
Qed.

Lemma init_coalesced_ok (s : ra_state) : forall (l : list N) cc,
  (forall i, In i l -> i < LENGTH cc) ->
  exists cc', st_ex_FOREACH l do_upd_coalesce (with_coalesced s cc) = (M_success tt, with_coalesced s cc') /\
    LENGTH cc' = LENGTH cc /\ (forall v, In v cc' -> In v cc \/ In v l).
Proof.
  induction l as [|i l IH]; intros cc Hl; cbn [st_ex_FOREACH].
  - exists cc; split; [reflexivity|split; [reflexivity|tauto]].
  - unfold do_upd_coalesce. mstep (update_coalesced_ok i (0 + i) (with_coalesced s cc) ltac:(rs; apply Hl; left; reflexivity)). rs.
    destruct (IH (LUPDATE (0 + i) i cc)) as (cc' & E & H1 & H2).
    + intros j Hj; rewrite LENGTH_LUPDATE; apply Hl; right; exact Hj.
    + exists cc'; split; [exact E|split; [rewrite H1; apply LENGTH_LUPDATE|]].
      intros v Hv; destruct (H2 v Hv) as [Hv'|Hv']; [|right; right; exact Hv'].
      apply In_LUPDATE in Hv' as [->|Hv']; [right; left; lia|left; exact Hv'].
Qed.

Lemma init_alloc1_heu_ok moves k s :
  good_ra_state s -> EVERY (fun '(p, (x, y)) => (x <? s.(dim)) && (y <? s.(dim))) moves ->
  exists l s', init_alloc1_heu moves s.(dim) k s = (M_success l, s') /\ good_ra_state s' /\
    s'.(adj_ls) = s.(adj_ls) /\ s'.(dim) = s.(dim) /\ s'.(node_tag) = s.(node_tag).
Proof.
  intros Hg Hmv. good_destr Hg. unfold init_alloc1_heu. ret.
  assert (Hds : forall i, In i (COUNT_LIST (dim s)) -> i < dim s) by (intros i Hi; apply In_COUNT_LIST, Hi).
  destruct (st_ex_FILTER_pure is_Atemp (fun _ => True) (COUNT_LIST (dim s)) s []) as (allocs & E1 & H1).
  { intros x Hx; eexists; split; [apply is_Atemp_ok; rewrite L2; auto|auto]. }
  mstep' E1.
  assert (Hal : forall x, In x allocs -> x < dim s) by (intros x Hx; destruct (H1 x Hx) as [[_ ?]|[]]; auto).
  destruct (init_degrees_ok k s Hg (COUNT_LIST (dim s)) (degrees s) Hds L3) as (dd & E2 & Hdd).
  replace (with_degrees s (degrees s)) with s in E2 by (destruct s; reflexivity).
  mstep' E2.
  destruct (init_coalesced_ok (with_degrees s dd) (COUNT_LIST (dim s)) (coalesced s)) as (cc & E3 & Hcc & Hccv).
  { intros i Hi; rewrite L4; auto. }
  replace (with_coalesced (with_degrees s dd) (coalesced s)) with (with_degrees s dd) in E3 by (destruct s; reflexivity).
  mstep' E3.
  set (s3 := with_coalesced (with_degrees s dd) cc).
  assert (Hg3 : good_ra_state s3).
  { subst s3; apply good_with_coalesced; [apply good_with_degrees; [exact Hg|exact Hdd]|rs; lia|rs].
    apply EVERY_lt_iff; intros v Hv; destruct (Hccv v Hv) as [Hv'|Hv']; [rewrite EVERY_lt_iff in B1|]; auto. }
  mstep' (set_avail_moves_wl_eq (E:=state_exn) (sort_moves moves) s3).
  assert (Hg4 : good_ra_state (with_avail_moves_wl s3 (sort_moves moves))).
  { apply good_with_avail; [exact Hg3|]. subst s3; rs.
    apply EVERY_moves_iff; intros p x y Hin. apply (proj1 (sort_moves_In _ _)) in Hin.
    rewrite EVERY_moves_iff in Hmv; eauto. }
  destruct (reset_move_related_success moves (with_avail_moves_wl s3 (sort_moves moves))) as (mv & E4 & Hmv4).
  { split; [exact Hg4|subst s3; rs; exact Hmv]. }
  mstep' E4.
  set (s4 := with_move_related (with_avail_moves_wl s3 (sort_moves moves)) mv).
  assert (Hg5 : good_ra_state s4) by (apply good_with_move_related; [exact Hg4|exact Hmv4]).
  destruct (st_ex_PARTITION_split_degree allocs k [] [] s4 Hg5) as (ltk & gtk & E5 & H5a & H5b).
  replace (dim s4) with (dim s) in E5 by reflexivity.
  mstep' E5.
  destruct (st_ex_PARTITION_move_related_sub ltk [] [] s4) as (tf & tsimp & E6 & H6a & H6b).
  { apply EVERY_lt_iff; intros x Hx; rewrite EVERY_iff in H5a; specialize (H5a x Hx).
    apply orb_iff in H5a as [H5a|H5a]; [discriminate|apply MEM_iff in H5a].
    subst s4 s3; rs; rewrite Hmv4; auto. }
  mstep' E6.
  mstep' (set_spill_wl_eq (E:=state_exn) gtk s4).
  mstep' (set_simp_wl_eq (E:=state_exn) tsimp (with_spill_wl s4 gtk)).
  mstep' (set_freeze_wl_eq (E:=state_exn) tf (with_simp_wl (with_spill_wl s4 gtk) tsimp)).
  rewrite EVERY_iff in H5a, H5b, H6a, H6b.
  assert (Hltk : forall x, In x ltk -> x < dim s).
  { intros x Hx; specialize (H5a x Hx); apply orb_iff in H5a as [H5a|H5a]; [discriminate|apply MEM_iff in H5a]; auto. }
  eexists _, _; split; [reflexivity|]. subst s4 s3; rs2. split; [|auto].
  apply good_with_freeze_wl; [apply good_with_simp_wl; [apply good_with_spill_wl; [exact Hg5|]|]|]; rs2;
    apply EVERY_lt_iff; intros x Hx.
  - specialize (H5b x Hx); apply orb_iff in H5b as [H5b|H5b]; [discriminate|apply MEM_iff in H5b]; auto.
  - specialize (H6b x Hx); apply orb_iff in H6b as [H6b|H6b]; [discriminate|apply MEM_iff in H6b]; auto.
  - specialize (H6a x Hx); apply orb_iff in H6a as [H6a|H6a]; [discriminate|apply MEM_iff in H6a]; auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "do_alloc1_success" *)
Theorem do_alloc1_success : forall s moves scost k,
  good_ra_state s /\ EVERY (fun '(p, (x, y)) => (x <? s.(dim)) && (y <? s.(dim))) moves ->
  exists ls s',
    do_alloc1 moves scost k s = (M_success ls, s') /\
    good_ra_state s' /\
    is_subgraph s.(adj_ls) s'.(adj_ls) /\
    s'.(dim) = s.(dim) /\
    s'.(node_tag) = s.(node_tag).
Proof.
  intros s moves scost k [Hg Hmv]. unfold do_alloc1.
  mstep' (get_dim_eq (E:=state_exn) s).
  destruct (init_alloc1_heu_ok moves k s Hg Hmv) as (l & s1 & E1 & G1 & A1 & D1 & T1). mstep' E1.
  destruct (rpt_do_step_success scost l s1 k G1) as (s2 & E2 & G2 & S2 & D2 & T2). mstep' E2.
  mstep' (get_stack_eq (E:=state_exn) s2).
  eexists _, s2; split; [reflexivity|split; [exact G2|split; [rewrite <- A1; exact S2|split; congruence]]].
Qed.
