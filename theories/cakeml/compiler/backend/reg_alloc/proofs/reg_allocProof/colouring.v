(** * CakeML [reg_allocProof]: the colouring steps

    Part of the [reg_allocProofScript] counterpart: correctness of
    [remove_colours], [assign_Atemps], [assign_Stemps] and of the
    preference oracles [biased_pref] / [neg_biased_pref].

    HOL wraps some conclusions in [markerTheory.Abbrev] (the identity, a
    proof-engineering marker); it is omitted here.  HOL [if P then A else B]
    on a proposition [P] is [if decide P then A else B]. *)

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
From Galette.cakeml.compiler.backend.reg_alloc.proofs.reg_allocProof Require Import ra_state.
From Stdlib Require Import Sorted.
Open Scope N_scope.
Open Scope monad_scope.

(** ** Proof helpers (Galette infrastructure) *)

Lemma ifdec {P} `{Decision P} (A B : Prop) :
  (if decide P then A else B) <-> (P -> A) /\ (~ P -> B).
Proof. destruct (decide P); tauto. Qed.

(** Replace [s1] by [with_f s t] given [H : s1 = with_f s s1.(f)]. *)
Ltac wsubst H :=
  match type of H with
  | ?s1 = ?w ?s (?proj ?s1) =>
      let t := fresh "t" in let Ht := fresh "Ht" in
      remember (proj s1) as t eqn:Ht; subst s1; clear Ht
  end.

Ltac mstep' H := mstep H; cbv beta.

Lemma good_bound_adj s x y :
  good_ra_state s -> x < s.(dim) -> In y (EL x s.(adj_ls)) -> y < s.(dim).
Proof.
  intros (L1 & _ & _ & _ & _ & _ & Ha & _) Hx Hy.
  rewrite EVERY_iff in Ha. specialize (Ha (EL x s.(adj_ls)) (EL_In x s.(adj_ls) ltac:(lia))).
  rewrite EVERY_iff in Ha; apply ltb_iff, Ha, Hy.
Qed.

Lemma good_ra_state_with_node_tag s t :
  good_ra_state s -> LENGTH t = s.(dim) -> good_ra_state (with_node_tag s t).
Proof. unfold good_ra_state; rs; tauto. Qed.

Lemma is_Fixed_ok x s : x < LENGTH s.(node_tag) ->
  is_Fixed x s = (M_success (match EL x s.(node_tag) with Fixed _ => true | _ => false end), s).
Proof. intros H; unfold is_Fixed; mstep' (node_tag_sub_ok x s H); reflexivity. Qed.

Lemma is_Atemp_ok x s : x < LENGTH s.(node_tag) ->
  is_Atemp x s = (M_success (bool_decide (EL x s.(node_tag) = Atemp)), s).
Proof. intros H; unfold is_Atemp; mstep' (node_tag_sub_ok x s H); reflexivity. Qed.

Lemma is_Fixed_k_ok k x s : x < LENGTH s.(node_tag) ->
  is_Fixed_k k x s = (M_success (match EL x s.(node_tag) with Fixed n => n <? k | _ => false end), s).
Proof. intros H; unfold is_Fixed_k; mstep' (node_tag_sub_ok x s H); reflexivity. Qed.

(** ** [remove_colours] *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "remove_colours_frame" *)
Theorem remove_colours_frame : forall adjs ks s res s',
  remove_colours adjs ks s = (res, s') -> s = s'.
Proof.
  induction adjs as [|x xs IH]; intros ks s res s' H; destruct ks as [|k ks];
    cbn [remove_colours] in H; try (unfold st_ex_return in H; congruence).
  unfold st_ex_bind at 1 in H; rewrite node_tag_sub_eqn in H.
  destruct (x <? LENGTH s.(node_tag)); [|congruence].
  unfold st_ex_bind in H.
  destruct (EL x s.(node_tag)) eqn:Et;
    match type of H with context [remove_colours xs ?k' s] =>
      destruct (remove_colours xs k' s) as [[r|e] s1] eqn:E end;
    inversion H; subst; eapply IH; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "remove_colours_success" *)
Theorem remove_colours_success : forall adjs ks s ls s',
  remove_colours adjs ks s = (M_success ls, s') ->
  set ls SUBSET set ks /\
  (forall n, MEM n adjs /\ n < LENGTH s'.(node_tag) ->
     match EL n s.(node_tag) with Fixed c => ~ MEM c ls | _ => True end).
Proof.
  induction adjs as [|x xs IH]; intros ks s ls s' H; destruct ks as [|k ks];
    cbn [remove_colours] in H.
  - inversion H; subst; split; [intros z Hz; exact Hz|intros n [Hn _]; discriminate].
  - inversion H; subst; split; [intros z Hz; exact Hz|intros n [Hn _]; discriminate].
  - inversion H; subst; split; [intros z Hz; exact Hz|].
    intros n _; destruct (EL n s'.(node_tag)); auto; discriminate.
  - unfold st_ex_bind at 1 in H; rewrite node_tag_sub_eqn in H.
    destruct (x <? LENGTH s.(node_tag)); [|congruence].
    unfold st_ex_bind in H.
    destruct (EL x s.(node_tag)) eqn:Et;
      match type of H with context [remove_colours xs ?k' s] =>
        destruct (remove_colours xs k' s) as [[r|e] s1] eqn:E end;
      inversion H; subst; clear H;
      pose proof (remove_colours_frame _ _ _ _ _ E) as <-;
      destruct (IH _ _ _ _ E) as [Hsub Hcol]; (split; [|intros m [Hm Hml]]).
    + intros z Hz; apply Hsub, IN_set in Hz; apply IN_set.
      apply filter_In in Hz; tauto.
    + cbn [MEM] in Hm; apply orb_iff in Hm as [Hm|Hm].
      * apply bool_decide_spec in Hm; subst m; rewrite Et.
        intros Hc; apply MEM_In, IN_set, Hsub in Hc; unfold pred_set.IN in Hc.
        apply IN_set, filter_In in Hc as [_ Hc]; rewrite N.eqb_refl in Hc; discriminate.
      * apply Hcol; split; assumption.
    + exact Hsub.
    + cbn [MEM] in Hm; apply orb_iff in Hm as [Hm|Hm].
      * apply bool_decide_spec in Hm; subst m; rewrite Et; exact I.
      * apply Hcol; split; assumption.
    + exact Hsub.
    + cbn [MEM] in Hm; apply orb_iff in Hm as [Hm|Hm].
      * apply bool_decide_spec in Hm; subst m; rewrite Et; exact I.
      * apply Hcol; split; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "no_clash_LUPDATE_Stemp" *)
Theorem no_clash_LUPDATE_Stemp : forall adjls tags n,
  no_clash adjls tags -> no_clash adjls (LUPDATE Stemp n tags).
Proof.
  unfold no_clash; intros adjls tags n H x y Hxy; specialize (H x y Hxy).
  rewrite !EL_LUPDATE; repeat destruct (decide _); cbn; auto;
    destruct (EL x tags); auto; destruct (EL y tags); auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "no_clash_LUPDATE_Fixed" *)
Theorem no_clash_LUPDATE_Fixed : forall adjls tags n x,
  undirected adjls /\
  EVERY (fun ls => EVERY (fun v => v <? LENGTH tags) ls) adjls /\
  n < LENGTH adjls /\
  (forall m, MEM m (EL n adjls) /\ m < LENGTH tags -> EL m tags <> Fixed x) /\
  no_clash adjls tags ->
  no_clash adjls (LUPDATE (Fixed x) n tags).
Proof.
  intros adjls tags n x (Hu & Hb & Hn & Hm & Hc) a b Hab.
  assert (Hbd : forall p q, has_edge adjls p q -> q < LENGTH tags).
  { intros p q (Hp & _ & Hq). rewrite EVERY_iff in Hb.
    specialize (Hb _ (EL_In _ _ Hp)); rewrite EVERY_iff in Hb; apply ltb_iff, Hb, MEM_In, Hq. }
  pose proof (Hc a b Hab) as Hc'.
  rewrite !EL_LUPDATE; destruct (decide (n = a /\ a < LENGTH tags)) as [[<- Ha]|Ha];
    destruct (decide (n = b /\ b < LENGTH tags)) as [[<- Hb']|Hb'].
  - auto.
  - destruct (EL b tags) eqn:E; auto. intros <-. exfalso; apply (Hm b); [|exact E].
    split; [exact (proj2 (proj2 Hab))|exact (Hbd _ _ Hab)].
  - destruct (EL a tags) eqn:E; auto. intros ->. exfalso; apply (Hm a); [|exact E].
    pose proof (Hu _ _ Hab) as Hba. split; [exact (proj2 (proj2 Hba))|exact (Hbd _ _ Hba)].
  - exact Hc'.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "remove_colours_succeeds" *)
Theorem remove_colours_succeeds : forall adj ks s,
  EVERY (fun v => v <? LENGTH s.(node_tag)) adj ->
  exists ls, remove_colours adj ks s = (M_success ls, s).
Proof.
  induction adj as [|x xs IH]; intros ks s H; destruct ks as [|k ks]; cbn [remove_colours];
    try (eexists; reflexivity).
  cbn [EVERY] in H; apply andb_iff in H as [Hx H]; apply ltb_iff in Hx.
  mstep' (node_tag_sub_ok _ _ Hx).
  destruct (EL x s.(node_tag));
    match goal with |- context [remove_colours xs ?k'] =>
      destruct (IH k' s H) as [r Hr]; mstep' Hr; eexists; reflexivity end.
Qed.

(** ** [assign_Atemps] *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "assign_Atemp_tag_correct" *)
Theorem assign_Atemp_tag_correct : forall s pref n ks,
  good_ra_state s /\ no_clash s.(adj_ls) s.(node_tag) /\ good_pref pref /\ n < s.(dim) ->
  exists s',
    assign_Atemp_tag ks pref n s = (M_success tt, s') /\
    (forall m,
       if decide (n = m /\ EL n s.(node_tag) = Atemp)
       then EL n s'.(node_tag) <> Atemp
       else EL m s'.(node_tag) = EL m s.(node_tag)) /\
    no_clash s'.(adj_ls) s'.(node_tag) /\
    good_ra_state s' /\
    s' = with_node_tag s s'.(node_tag).
Proof.
  intros s pref n ks (Hg & Hnc & Hp & Hn).
  pose proof Hg as (L1 & L2 & L3 & L4 & L5 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & Hu).
  unfold assign_Atemp_tag. mstep' (node_tag_sub_ok n s ltac:(lia)).
  destruct (EL n s.(node_tag)) eqn:Et.
  1,3: exists s; split; [reflexivity|]; split;
    [intros m; destruct (decide _) as [[_ ?]|]; [discriminate|reflexivity]|];
    split; [exact Hnc|split; [exact Hg|destruct s; reflexivity]].
  mstep' (adj_ls_sub_ok n s ltac:(lia)).
  assert (Hev : EVERY (fun v => v <? LENGTH s.(node_tag)) (EL n s.(adj_ls))).
  { apply EVERY_iff; intros y Hy; apply ltb_iff; rewrite L2; eapply good_bound_adj; eauto. }
  destruct (remove_colours_succeeds _ ks _ Hev) as [ls Hls]. mstep' Hls.
  destruct (remove_colours_success _ _ _ _ _ Hls) as [Hsub Hcol].
  assert (Hfix : forall c, (forall c', MEM c' ls -> c' = c -> False) -> False -> True) by auto.
  destruct ls as [|h t].
  - rewrite (update_node_tag_ok n Stemp s ltac:(lia)).
    eexists; split; [reflexivity|]; rs. split; [|split; [|split]].
    + intros m; rewrite !EL_LUPDATE. destruct (decide (n = m /\ Atemp = Atemp)) as [[<- _]|Hd].
      * destruct (decide _) as [_|Hd]; [discriminate|exfalso; apply Hd; split; [reflexivity|lia]].
      * destruct (decide (n = m /\ m < LENGTH (node_tag s))) as [[<- _]|]; [exfalso; apply Hd; auto|reflexivity].
    + apply no_clash_LUPDATE_Stemp, Hnc.
    + apply good_ra_state_with_node_tag; [exact Hg|rewrite LENGTH_LUPDATE; exact L2].
    + reflexivity.
  - destruct (Hp n (h :: t) s Hg) as [res [Hres Hmem]]. mstep' Hres.
    set (c := match res with None => h | Some y => y end).
    assert (Hc : MEM c (h :: t)).
    { subst c; destruct res as [y|]; [exact Hmem|cbn [MEM]; apply orb_iff; left; apply bool_decide_spec; reflexivity]. }
    assert (Hupd : (match res with None => update_node_tag n (Fixed h) | Some y => update_node_tag n (Fixed y) end) s
                   = update_node_tag n (Fixed c) s) by (subst c; destruct res; reflexivity).
    rewrite Hupd, (update_node_tag_ok n (Fixed c) s ltac:(lia)).
    eexists; split; [reflexivity|]; rs. split; [|split; [|split]].
    + intros m; rewrite !EL_LUPDATE. destruct (decide (n = m /\ Atemp = Atemp)) as [[<- _]|Hd].
      * destruct (decide _) as [_|Hd]; [discriminate|exfalso; apply Hd; split; [reflexivity|lia]].
      * destruct (decide (n = m /\ m < LENGTH (node_tag s))) as [[<- _]|]; [exfalso; apply Hd; auto|reflexivity].
    + apply no_clash_LUPDATE_Fixed; split; [exact Hu|split; [|split; [lia|split; [|exact Hnc]]]].
      * rewrite L2; exact B2.
      * intros m [Hm Hml] Em. specialize (Hcol m (conj Hm Hml)). rewrite Em in Hcol. exact (Hcol Hc).
    + apply good_ra_state_with_node_tag; [exact Hg|rewrite LENGTH_LUPDATE; exact L2].
    + reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "assign_Atemps_FOREACH_lem" *)
Theorem assign_Atemps_FOREACH_lem : forall ls s ks prefs,
  good_ra_state s /\ no_clash s.(adj_ls) s.(node_tag) /\ good_pref prefs /\
  EVERY (fun v => v <? s.(dim)) ls ->
  exists s',
    st_ex_FOREACH ls (assign_Atemp_tag ks prefs) s = (M_success tt, s') /\
    no_clash s'.(adj_ls) s'.(node_tag) /\
    good_ra_state s' /\
    s' = with_node_tag s s'.(node_tag) /\
    (forall m,
       if decide (MEM m ls /\ EL m s.(node_tag) = Atemp)
       then EL m s'.(node_tag) <> Atemp
       else EL m s'.(node_tag) = EL m s.(node_tag)).
Proof.
  induction ls as [|h ls IH]; intros s ks prefs (Hg & Hnc & Hp & Hev); cbn [st_ex_FOREACH].
  - exists s; split; [reflexivity|]; split; [exact Hnc|split; [exact Hg|split; [destruct s; reflexivity|]]].
    intros m; destruct (decide _) as [[Hm _]|]; [discriminate|reflexivity].
  - cbn [EVERY] in Hev; apply andb_iff in Hev as [Hh Hev]; apply ltb_iff in Hh.
    destruct (assign_Atemp_tag_correct s prefs h ks (conj Hg (conj Hnc (conj Hp Hh))))
      as (s1 & E1 & Hm1 & Hnc1 & Hg1 & Hw1).
    mstep E1. wsubst Hw1. rs.
    destruct (IH (with_node_tag s t) ks prefs) as (s2 & E2 & Hnc2 & Hg2 & Hw2 & Hm2).
    { split; [exact Hg1|split; [exact Hnc1|split; [exact Hp|exact Hev]]]. }
    rs. rewrite E2. wsubst Hw2. rs.
    exists (with_node_tag s t0); split; [reflexivity|]; rs.
    split; [exact Hnc2|split; [exact Hg2|split; [reflexivity|]]].
    intros m; specialize (Hm1 m); specialize (Hm2 m); apply ifdec in Hm1, Hm2; apply ifdec.
    cbn [MEM]. rewrite orb_iff, bool_decide_iff.
    destruct (N.eq_dec m h) as [->|Hmh].
    + destruct (decide (EL h (node_tag s) = Atemp)) as [Ea|Ea].
      * assert (Hne : EL h t <> Atemp) by (apply (proj1 Hm1); auto).
        split; [intros _; rewrite (proj2 Hm2) by tauto; exact Hne|tauto].
      * assert (Heq : EL h t = EL h (node_tag s)) by (apply (proj2 Hm1); tauto).
        split; [tauto|intros _]. rewrite (proj2 Hm2) by (rewrite Heq; tauto). exact Heq.
    + assert (Heq : EL m t = EL m (node_tag s)) by (apply (proj2 Hm1); intros [? _]; congruence).
      rewrite Heq in Hm2. split.
      * intros [[?|Hm] Ha]; [congruence|]. apply (proj1 Hm2); auto.
      * intros Hn; apply (proj2 Hm2); tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "assign_Atemps_correct" *)
Theorem assign_Atemps_correct : forall k ls prefs s,
  good_ra_state s /\ good_pref prefs /\ no_clash s.(adj_ls) s.(node_tag) ->
  exists s',
    assign_Atemps k ls prefs s = (M_success tt, s') /\
    no_clash s'.(adj_ls) s'.(node_tag) /\
    good_ra_state s' /\
    s' = with_node_tag s s'.(node_tag) /\
    EVERY (fun n => bool_decide (n <> Atemp)) s'.(node_tag) /\
    (forall m, m < LENGTH s.(node_tag) /\ EL m s.(node_tag) <> Atemp ->
       EL m s'.(node_tag) = EL m s.(node_tag)).
Proof.
  intros k ls prefs s (Hg & Hp & Hnc). unfold assign_Atemps.
  mstep' (get_dim_eq (E:=state_exn) s). rewrite !(bind_ok _ _ _ _ _ (return_eq _ _)). cbv beta.
  set (lsf := FILTER (fun n => n <? dim s) ls). set (ks := GENLIST (fun x => x) k).
  destruct (assign_Atemps_FOREACH_lem lsf s ks prefs) as (s1 & E1 & Hnc1 & Hg1 & Hw1 & Hm1).
  { split; [exact Hg|split; [exact Hnc|split; [exact Hp|]]].
    apply EVERY_iff; intros x Hx; apply filter_In in Hx; tauto. }
  mstep E1. wsubst Hw1. rs.
  set (lsg := GENLIST (fun x => x) (dim s)).
  destruct (assign_Atemps_FOREACH_lem lsg (with_node_tag s t) ks prefs) as (s2 & E2 & Hnc2 & Hg2 & Hw2 & Hm2).
  { split; [exact Hg1|split; [exact Hnc1|split; [exact Hp|]]].
    rs; apply EVERY_iff; intros x Hx; apply In_GENLIST in Hx as (i & Hi & ->); apply ltb_iff; exact Hi. }
  rewrite E2. wsubst Hw2. rs.
  pose proof Hg as (L1 & L2 & _). pose proof Hg1 as (_ & L2' & _). pose proof Hg2 as (_ & L2'' & _). rs.
  exists (with_node_tag s t0); split; [reflexivity|]; rs.
  split; [exact Hnc2|split; [exact Hg2|split; [reflexivity|split]]].
  - apply EVERY_iff; intros x Hx; apply bool_decide_spec; intros ->.
    apply In_EL in Hx as (m & Hm & Hx).
    specialize (Hm2 m); apply ifdec in Hm2.
    assert (Hmem : MEM m lsg) by (apply MEM_In, In_GENLIST; exists m; split; [lia|reflexivity]).
    destruct (decide (EL m t = Atemp)) as [Ea|Ea].
    + exact (proj1 Hm2 (conj Hmem Ea) (eq_sym Hx)).
    + apply Ea; rewrite <- (proj2 Hm2) by tauto; symmetry; exact Hx.
  - intros m [Hm Hna]. specialize (Hm1 m); specialize (Hm2 m); apply ifdec in Hm1, Hm2.
    assert (E1' : EL m t = EL m (node_tag s)) by (apply (proj2 Hm1); tauto).
    rewrite <- E1'; apply (proj2 Hm2); rewrite E1'; tauto.
Qed.

(** ** [assign_Stemps] *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "SORTED_HEAD_LT" *)
Theorem SORTED_HEAD_LT : forall col h ls,
  col < h /\ SORTED (fun x y => x <=? y) (h :: ls) -> ~ MEM col ls.
Proof.
  intros col h ls; revert h; induction ls as [|y ls IH]; intros h [Hlt Hs]; [discriminate|].
  cbn [SORTED] in Hs; apply andb_iff in Hs as [Hhy Hs]; apply leb_iff in Hhy.
  cbn [MEM]; rewrite orb_iff, bool_decide_iff; intros [->|Hm]; [lia|].
  apply (IH y); [split; [lia|exact Hs]|exact Hm].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "unbound_colour_correct" *)
Theorem unbound_colour_correct : forall ls k (k' : N),
  SORTED (fun x y => x <=? y) ls ->
  k <= unbound_colour k ls /\ ~ MEM (unbound_colour k ls) ls.
Proof.
  induction ls as [|h ls IH]; intros k k' Hs; cbn [unbound_colour]; [split; [lia|discriminate]|].
  assert (Hs' : is_true (SORTED (fun x y => x <=? y) ls)) by (destruct ls; cbn [SORTED] in *;
    [reflexivity|apply andb_iff in Hs; tauto]).
  destruct (N.ltb_spec k h) as [Hkh|Hkh].
  - split; [lia|]. cbn [MEM]; rewrite orb_iff, bool_decide_iff; intros [Hm|Hm]; [lia|].
    exact (SORTED_HEAD_LT k h ls (conj Hkh Hs) Hm).
  - destruct (N.eqb_spec h k) as [->|Hhk].
    + destruct (IH (k + 1) k' Hs') as [H1 H2]. split; [lia|].
      cbn [MEM]; rewrite orb_iff, bool_decide_iff; intros [Hm|Hm]; [lia|exact (H2 Hm)].
    + destruct (IH k k' Hs') as [H1 H2]. split; [lia|].
      cbn [MEM]; rewrite orb_iff, bool_decide_iff; intros [Hm|Hm]; [|exact (H2 Hm)].
      (* h < k and the result is at least k *)
      lia.
Qed.

(** A good negated preference oracle only inspects the state and selects an
    element [>= k] not in the input list. *)
(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "good_neg_pref_def" *)
Definition good_neg_pref (k : N) (pref : N -> list N -> RA (option N)) : Prop :=
  forall n bads s, good_ra_state s ->
    exists res, pref n bads s = (M_success res, s) /\
      match res with None => True | Some c => ~ MEM c bads /\ k <= c end.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "assign_Stemp_tag_correct" *)
Theorem assign_Stemp_tag_correct : forall s n k prefs,
  good_ra_state s /\ no_clash s.(adj_ls) s.(node_tag) /\ n < s.(dim) /\ good_neg_pref k prefs ->
  exists s',
    assign_Stemp_tag k prefs n s = (M_success tt, s') /\
    (forall m,
       if decide (n = m /\ EL n s.(node_tag) = Stemp)
       then exists k', EL n s'.(node_tag) = Fixed k' /\ k <= k'
       else EL m s'.(node_tag) = EL m s.(node_tag)) /\
    no_clash s'.(adj_ls) s'.(node_tag) /\
    good_ra_state s' /\
    s' = with_node_tag s s'.(node_tag).
Proof.
  intros s n k prefs (Hg & Hnc & Hn & Hp).
  pose proof Hg as (L1 & L2 & L3 & L4 & L5 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & Hu).
  unfold assign_Stemp_tag. mstep' (node_tag_sub_ok n s ltac:(lia)).
  destruct (EL n s.(node_tag)) eqn:Et.
  1,2: exists s; split; [reflexivity|]; split;
    [intros m; destruct (decide _) as [[_ ?]|]; [discriminate|reflexivity]|];
    split; [exact Hnc|split; [exact Hg|destruct s; reflexivity]].
  mstep' (adj_ls_sub_ok n s ltac:(lia)).
  assert (Hev : EVERY (fun v => v <? LENGTH s.(node_tag)) (EL n s.(adj_ls))).
  { apply EVERY_iff; intros y Hy; apply ltb_iff; rewrite L2; eapply good_bound_adj; eauto. }
  mstep' (st_ex_MAP_node_tag_sub _ _ Hev).
  set (bads := mllist.sort (fun x y => x <=? y) (MAP tag_col (MAP (fun i => EL i (node_tag s)) (EL n (adj_ls s))))).
  assert (Hsorted : is_true (SORTED (fun x y => x <=? y) bads)).
  { apply sort_SORTED; intros x y; destruct (N.leb_spec x y); [left; reflexivity|right; apply N.leb_le; lia]. }
  destruct (Hp n bads s Hg) as [res [Hres Hr]]. mstep' Hres.
  set (c := match res with None => unbound_colour k bads | Some y => y end).
  assert (Hc : ~ MEM c bads /\ k <= c).
  { subst c; destruct res as [y|]; [exact Hr|]. pose proof (unbound_colour_correct bads k 0 Hsorted); tauto. }
  assert (Hupd : (match res with None => update_node_tag n (Fixed (unbound_colour k bads))
                  | Some y => update_node_tag n (Fixed y) end) s
                 = update_node_tag n (Fixed c) s) by (subst c; destruct res; reflexivity).
  rewrite Hupd, (update_node_tag_ok n (Fixed c) s ltac:(lia)).
  eexists; split; [reflexivity|]; rs. split; [|split; [|split]].
  - intros m; rewrite !EL_LUPDATE. destruct (decide (n = m /\ Stemp = Stemp)) as [[<- _]|Hd].
    + destruct (decide _) as [_|Hd]; [exists c; split; [reflexivity|tauto]|].
      exfalso; apply Hd; split; [reflexivity|lia].
    + destruct (decide (n = m /\ m < LENGTH (node_tag s))) as [[<- _]|]; [exfalso; apply Hd; auto|reflexivity].
  - apply no_clash_LUPDATE_Fixed; split; [exact Hu|split; [|split; [lia|split; [|exact Hnc]]]].
    + rewrite L2; exact B2.
    + intros m [Hm Hml] Em. apply (proj1 Hc).
      subst bads; apply sort_MEM, MEM_In, in_map_iff. exists (Fixed c); split; [reflexivity|].
      apply in_map_iff; exists m; split; [exact Em|apply MEM_In, Hm].
  - apply good_ra_state_with_node_tag; [exact Hg|rewrite LENGTH_LUPDATE; exact L2].
  - reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "assign_Stemps_FOREACH_lem" *)
Theorem assign_Stemps_FOREACH_lem : forall prefs ls s k,
  good_ra_state s /\ no_clash s.(adj_ls) s.(node_tag) /\
  EVERY (fun v => v <? s.(dim)) ls /\ good_neg_pref k prefs ->
  exists s',
    st_ex_FOREACH ls (assign_Stemp_tag k prefs) s = (M_success tt, s') /\
    no_clash s'.(adj_ls) s'.(node_tag) /\
    good_ra_state s' /\
    (forall m,
       if decide (MEM m ls /\ EL m s.(node_tag) = Stemp)
       then exists k', EL m s'.(node_tag) = Fixed k' /\ k <= k'
       else EL m s'.(node_tag) = EL m s.(node_tag)) /\
    s' = with_node_tag s s'.(node_tag).
Proof.
  intros prefs; induction ls as [|h ls IH]; intros s k (Hg & Hnc & Hev & Hp); cbn [st_ex_FOREACH].
  - exists s; split; [reflexivity|]; split; [exact Hnc|split; [exact Hg|split; [|destruct s; reflexivity]]].
    intros m; destruct (decide _) as [[Hm _]|]; [discriminate|reflexivity].
  - cbn [EVERY] in Hev; apply andb_iff in Hev as [Hh Hev]; apply ltb_iff in Hh.
    destruct (assign_Stemp_tag_correct s h k prefs (conj Hg (conj Hnc (conj Hh Hp))))
      as (s1 & E1 & Hm1 & Hnc1 & Hg1 & Hw1).
    mstep E1. wsubst Hw1. rs.
    destruct (IH (with_node_tag s t) k) as (s2 & E2 & Hnc2 & Hg2 & Hm2 & Hw2).
    { split; [exact Hg1|split; [exact Hnc1|split; [exact Hev|exact Hp]]]. }
    rs. rewrite E2. wsubst Hw2. rs.
    exists (with_node_tag s t0); split; [reflexivity|]; rs.
    split; [exact Hnc2|split; [exact Hg2|split; [|reflexivity]]].
    intros m; specialize (Hm1 m); specialize (Hm2 m); apply ifdec in Hm1, Hm2; apply ifdec.
    cbn [MEM]. rewrite orb_iff, bool_decide_iff.
    destruct (N.eq_dec m h) as [->|Hmh].
    + destruct (decide (EL h (node_tag s) = Stemp)) as [Ea|Ea].
      * destruct (proj1 Hm1 (conj eq_refl Ea)) as (k' & Hk' & Hkk).
        split; [intros _|tauto]. exists k'; split; [|exact Hkk].
        rewrite (proj2 Hm2) by (rewrite Hk'; intros [_ ?]; discriminate). exact Hk'.
      * assert (Heq : EL h t = EL h (node_tag s)) by (apply (proj2 Hm1); tauto).
        split; [tauto|intros _]. rewrite (proj2 Hm2) by (rewrite Heq; tauto). exact Heq.
    + assert (Heq : EL m t = EL m (node_tag s)) by (apply (proj2 Hm1); intros [? _]; congruence).
      rewrite Heq in Hm2. split.
      * intros [[?|Hm] Ha]; [congruence|]. apply (proj1 Hm2); auto.
      * intros Hn; apply (proj2 Hm2); tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "assign_Stemps_correct" *)
Theorem assign_Stemps_correct : forall s k prefs,
  good_ra_state s /\ no_clash s.(adj_ls) s.(node_tag) /\ good_neg_pref k prefs ->
  exists s',
    assign_Stemps k prefs s = (M_success tt, s') /\
    no_clash s'.(adj_ls) s'.(node_tag) /\
    good_ra_state s' /\
    s' = with_node_tag s s'.(node_tag) /\
    (forall m, m < LENGTH s.(node_tag) ->
       if decide (EL m s.(node_tag) = Stemp)
       then exists k', EL m s'.(node_tag) = Fixed k' /\ k <= k'
       else EL m s'.(node_tag) = EL m s.(node_tag)).
Proof.
  intros s k prefs (Hg & Hnc & Hp). unfold assign_Stemps.
  mstep' (get_dim_eq (E:=state_exn) s). rewrite !(bind_ok _ _ _ _ _ (return_eq _ _)). cbv beta.
  set (ls := GENLIST (fun x => x) (dim s)).
  destruct (assign_Stemps_FOREACH_lem prefs ls s k) as (s1 & E1 & Hnc1 & Hg1 & Hm1 & Hw1).
  { split; [exact Hg|split; [exact Hnc|split; [|exact Hp]]].
    apply EVERY_iff; intros x Hx; apply In_GENLIST in Hx as (i & Hi & ->); apply ltb_iff; exact Hi. }
  exists s1; split; [exact E1|split; [exact Hnc1|split; [exact Hg1|split; [exact Hw1|]]]].
  intros m Hm; specialize (Hm1 m); apply ifdec in Hm1; apply ifdec.
  pose proof Hg as (_ & L2 & _).
  assert (Hmem : MEM m ls) by (apply MEM_In, In_GENLIST; exists m; split; [lia|reflexivity]).
  split; intros H; [apply (proj1 Hm1)|apply (proj2 Hm1)]; tauto.
Qed.

(** ** The preference oracles *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "first_match_col_correct" *)
Theorem first_match_col_correct : forall x ks s,
  exists res, first_match_col ks x s = (res, s) /\
    match res with
    | M_failure v => v = Subscript
    | M_success (Some k) => is_true (MEM k ks)
    | _ => True
    end.
Proof.
  induction x as [|h x IH]; intros ks s; cbn [first_match_col]; [eexists; split; [reflexivity|exact I]|].
  unfold st_ex_bind at 1; rewrite node_tag_sub_eqn.
  destruct (h <? LENGTH (node_tag s)); [|eexists; split; [reflexivity|reflexivity]].
  destruct (EL h (node_tag s)) as [m| |]; try apply IH.
  destruct (MEM m ks) eqn:E; [eexists; split; [reflexivity|exact E]|apply IH].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "coalesce_root_success" *)
Theorem coalesce_root_success : forall n s,
  good_ra_state s /\ n < s.(dim) -> exists v, coalesce_root n s = (M_success v, s).
Proof.
  intros n; induction n as [n IH] using (well_founded_induction N.lt_wf_0); intros s [Hg Hn].
  pose proof Hg as (L1 & L2 & L3 & L4 & L5 & B1 & _).
  rewrite coalesce_root_def. mstep' (coalesced_sub_ok n s ltac:(lia)).
  assert (Hc : EL n (coalesced s) < dim s).
  { rewrite EVERY_iff in B1; apply ltb_iff, B1, EL_In; lia. }
  mstep' (is_Fixed_ok (EL n (coalesced s)) s ltac:(lia)).
  destruct (match EL (EL n (coalesced s)) (node_tag s) with Fixed _ => true | _ => false end).
  - eexists; reflexivity.
  - destruct (N.leb_spec n (EL n (coalesced s))); [eexists; reflexivity|].
    apply IH; [lia|split; assumption].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "good_pref_biased_pref" *)
Theorem good_pref_biased_pref : forall t, good_pref (biased_pref t).
Proof.
  intros t n ks s Hg. unfold biased_pref; mstep' (get_dim_eq (E:=state_exn) s).
  destruct (N.ltb_spec n (dim s)) as [Hn|Hn]; [|eexists; split; [reflexivity|exact I]].
  destruct (coalesce_root_success n s (conj Hg Hn)) as [v Hv]. mstep' Hv.
  destruct (first_match_col_correct (v :: match lookup n t with None => [] | Some vs => vs end) ks s)
    as [res [Hres Hr]].
  unfold handle_Subscript. rewrite Hres.
  destruct res as [[k|]|e]; [eexists; split; [reflexivity|exact Hr]|eexists; split; [reflexivity|exact I]|].
  subst e; eexists; split; [reflexivity|exact I].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "neg_first_match_col_correct" *)
Theorem neg_first_match_col_correct : forall k x ks s,
  exists res, neg_first_match_col k ks x s = (res, s) /\
    match res with
    | M_failure v => v = Subscript
    | M_success (Some c) => ~ MEM c ks /\ k <= c
    | _ => True
    end.
Proof.
  intros k; induction x as [|h x IH]; intros ks s; cbn [neg_first_match_col];
    [eexists; split; [reflexivity|exact I]|].
  unfold st_ex_bind at 1; rewrite node_tag_sub_eqn.
  destruct (h <? LENGTH (node_tag s)); [|eexists; split; [reflexivity|reflexivity]].
  destruct (EL h (node_tag s)) as [m| |]; try apply IH.
  destruct (MEM m ks || (m <? k)) eqn:E; [apply IH|].
  apply orb_false_iff in E as [E1 E2]. eexists; split; [reflexivity|].
  split; [rewrite E1; discriminate|apply N.ltb_ge, E2].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "good_neg_pref_neg_biased_pref" *)
Theorem good_neg_pref_neg_biased_pref : forall k t, good_neg_pref k (neg_biased_pref k t).
Proof.
  intros k t n bads s Hg. unfold neg_biased_pref; mstep' (get_dim_eq (E:=state_exn) s).
  destruct (N.ltb_spec n (dim s)) as [Hn|Hn]; [|eexists; split; [reflexivity|exact I]].
  destruct (neg_first_match_col_correct k (match lookup n t with None => [] | Some vs => vs end) bads s)
    as [res [Hres Hr]].
  unfold handle_Subscript. rewrite Hres.
  destruct res as [[c|]|e]; [eexists; split; [reflexivity|exact Hr]|eexists; split; [reflexivity|exact I]|].
  subst e; eexists; split; [reflexivity|exact I].
Qed.
