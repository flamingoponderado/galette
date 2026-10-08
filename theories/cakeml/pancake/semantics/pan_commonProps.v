(** * CakeML Pancake [pan_commonProps]: common properties for the Pancake ILs

    Port of [cakeml/pancake/semantics/pan_commonPropsScript.sml] (the part
    used by the Pancake proofs ported so far; see the list at the end of
    this header).

    Carrier notes: HOL's [MEM] is the boolean [MEM]; list indices are [N]
    ([EL], [TAKE], [DROP], [LENGTH]); [set] is [LIST_TO_SET].

    Not yet ported (not needed by [panProps]/[pan_simpProof]):
    [opt_mmap_some_eq_zip_flookup], [opt_mmap_disj_zip_flookup],
    [genlist_distinct_max], [genlist_distinct_max'], [mem_genlist_add_suc_val],
    [update_eq_zip_map_flookup], [map_flookup_fupdate_zip_not_mem],
    [fm_multi_update], [zero_not_mem_genlist_offset], [fm_empty_zip_alist],
    [fm_empty_zip_flookup], [fm_empty_zip_flookup_el],
    [all_distinct_flookup_all_distinct], [no_overlap_flookup_distinct],
    [fupdate_flookup_zip_elim], [not_mem_fst_zip_flookup_empty],
    [fm_zip_append_take_drop], [max_set_MAX_LIST], [MAX_LIST_add_not_mem],
    the [subspt_*] lemmas, [max_set_count_length], [MAX_LIST_i_genlist],
    [lookup_some_el], [max_foldr_lt], [fm_update_diff_vars],
    [fmap_to_alist_eq_fm], [MAP3_MAP2]. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist.
From Galette.cakeml.pancake Require Import pan_common.
Open Scope N_scope.
Local Open Scope fmap_scope.

(** ** Galette-only list helpers (bridging [N]-indexed HOL list operations
    and [Stdlib.List]). *)
Section Helpers.
Context {A : Type}.

Lemma EL_cons_pos `{Inhabited A} (n : N) (x : A) l :
  0 < n -> EL n (x :: l) = EL (n - 1) l.
Proof.
  intros Hn; replace n with (N.succ (n - 1)) at 1 by lia; rewrite EL_SUC; reflexivity.
Qed.

Lemma EL_cons_0 `{Inhabited A} (x : A) l : EL 0 (x :: l) = x.
Proof. reflexivity. Qed.

Lemma LENGTH_cons (x : A) l : LENGTH (x :: l) = LENGTH l + 1.
Proof. rewrite !LENGTH_length; cbn [length]; lia. Qed.

Lemma MEM_true_iff `{EqDecision A} (x : A) l : MEM x l = true <-> In x l.
Proof. apply MEM_In. Qed.

End Helpers.

Section Props.
Context {A B : Type}.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "ctxt_max_def" *)
Definition ctxt_max {K C} (n : N) (fm : fmap K (C * list N)) : Prop :=
  0 <= n /\
  (forall v a xs, FLOOKUP fm v = SOME (a, xs) -> forall x, is_true (MEM x xs) -> x <= n).

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "no_overlap_def" *)
Definition no_overlap {K C D} `{EqDecision D} (fm : fmap K (C * list D)) : Prop :=
  (forall x a xs, FLOOKUP fm x = SOME (a, xs) -> is_true (ALL_DISTINCT xs)) /\
  (forall x y a b xs ys,
     FLOOKUP fm x = SOME (a, xs) /\
     FLOOKUP fm y = SOME (b, ys) /\
     ~ DISJOINT (set xs) (set ys) -> x = y).

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "opt_mmap_eq_some" *)
Theorem opt_mmap_eq_some : forall (xs : list A) (f : A -> option B) ys,
  OPT_MMAP f xs = SOME ys <-> MAP f xs = MAP SOME ys.
Proof.
  induction xs as [|x xs IH]; intros f ys; cbn.
  - destruct ys; cbn; split; congruence.
  - destruct (f x) as [y|] eqn:Ef; cbn.
    + destruct (OPT_MMAP f xs) as [zs|] eqn:Eo; cbn.
      * split; intros H.
        -- injection H as <-; cbn; f_equal; apply IH; exact Eo.
        -- destruct ys as [|y' ys]; cbn in H; [discriminate|].
           injection H as -> H; apply IH in H; congruence.
      * split; intros H; [discriminate|].
        destruct ys as [|y' ys]; cbn in H; [discriminate|].
        injection H as _ H; apply IH in H; congruence.
    + split; intros H; [discriminate|].
      destruct ys; cbn in H; discriminate.
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "map_append_eq_drop" *)
Theorem map_append_eq_drop : forall (xs : list A) (ys zs : list B) f,
  MAP f xs = ys ++ zs -> MAP f (DROP (LENGTH ys) xs) = zs.
Proof.
  intros xs ys zs f H; rewrite DROP_skipn, LENGTH_length, Nat2N.id.
  revert xs H; induction ys as [|y ys IH]; intros xs H; [exact H|].
  destruct xs as [|x xs]; cbn in H; [discriminate|]. injection H as _ H.
  cbn [length skipn]; apply IH, H.
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "opt_mmap_mem_func" *)
Theorem opt_mmap_mem_func : forall (l : list A) (f : A -> option B) n g `{EqDecision A},
  OPT_MMAP f l = SOME n /\ is_true (MEM g l) -> exists m, f g = SOME m.
Proof.
  induction l as [|x l IH]; intros f n g ? [H Hm]; [discriminate|].
  cbn in H, Hm. destruct (f x) as [y|] eqn:Ef; [|discriminate]; cbn in H.
  destruct (OPT_MMAP f l) as [ys|] eqn:Eo; [|discriminate].
  destruct (decide (g = x)) as [->|Hne]; [eauto|].
  unfold is_true in Hm; apply Bool.orb_true_iff in Hm as [Hm|Hm].
  - apply bool_decide_spec in Hm; congruence.
  - eapply IH; eauto.
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "opt_mmap_mem_defined" *)
Theorem opt_mmap_mem_defined : forall (l : list A) (f : A -> option B) m e n
    `{EqDecision A} `{EqDecision B},
  OPT_MMAP f l = SOME m /\ is_true (MEM e l) /\ f e = SOME n -> is_true (MEM n m).
Proof.
  induction l as [|x l IH]; intros f m e n ? ? [H [Hm He]]; [discriminate|].
  cbn in H, Hm. destruct (f x) as [y|] eqn:Ef; [|discriminate]; cbn in H.
  destruct (OPT_MMAP f l) as [ys|] eqn:Eo; [|discriminate]; cbn in H.
  injection H as <-. unfold is_true in *; cbn.
  apply Bool.orb_true_iff in Hm as [Hm|Hm].
  - apply bool_decide_spec in Hm; subst; rewrite Ef in He; injection He as ->.
    apply Bool.orb_true_iff; left; apply bool_decide_spec; reflexivity.
  - apply Bool.orb_true_iff; right; eapply IH; eauto.
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "opt_mmap_el" *)
Theorem opt_mmap_el : forall (l : list A) (f : A -> option B) x n
    `{Inhabited A} `{Inhabited B},
  OPT_MMAP f l = SOME x /\ n < LENGTH l -> f (EL n l) = SOME (EL n x).
Proof.
  induction l as [|y l IH]; intros f x n ? ? [H Hn]; [cbn in Hn; lia|].
  cbn in H. destruct (f y) as [z|] eqn:Ef; [|discriminate]; cbn in H.
  destruct (OPT_MMAP f l) as [zs|] eqn:Eo; [|discriminate]; cbn in H.
  injection H as <-.
  destruct (N.eq_dec n 0) as [->|Hn0].
  - rewrite !EL_cons_0; exact Ef.
  - rewrite !EL_cons_pos by lia. apply IH; split; [exact Eo|].
    rewrite LENGTH_cons in Hn; lia.
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "opt_mmap_length_eq" *)
Theorem opt_mmap_length_eq : forall (l : list A) (f : A -> option B) n,
  OPT_MMAP f l = SOME n -> LENGTH l = LENGTH n.
Proof.
  induction l as [|y l IH]; intros f n H; cbn in H.
  - injection H as <-; reflexivity.
  - destruct (f y) as [z|]; [|discriminate]; cbn in H.
    destruct (OPT_MMAP f l) as [zs|] eqn:Eo; [|discriminate]; cbn in H.
    injection H as <-. rewrite !LENGTH_cons, (IH f zs Eo); reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "opt_mmap_opt_map" *)
Theorem opt_mmap_opt_map : forall {C} (l : list A) (f : A -> option B) n (g : B -> C),
  OPT_MMAP f l = SOME n -> OPT_MMAP (fun a => OPTION_MAP g (f a)) l = SOME (MAP g n).
Proof.
  intros C; induction l as [|y l IH]; intros f n g H; cbn in H.
  - injection H as <-; reflexivity.
  - destruct (f y) as [z|] eqn:Ef; [|discriminate]; cbn in H.
    destruct (OPT_MMAP f l) as [zs|] eqn:Eo; [|discriminate]; cbn in H.
    injection H as <-. cbn. rewrite Ef; cbn. rewrite (IH f zs g Eo); reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "map_the_some_cancel" *)
Theorem map_the_some_cancel : forall `{Inhabited A} (xs : list A), MAP (THE ∘ SOME) xs = xs.
Proof. intros ?; induction xs as [|x xs IH]; cbn in *; [reflexivity|]; rewrite IH; reflexivity. Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "map_some_the_map" *)
Theorem map_some_the_map : forall `{Inhabited B} (xs : list A) (ys : list B) f,
  MAP f xs = MAP SOME ys -> MAP (fun n => THE (f n)) xs = ys.
Proof.
  intros Hinh; induction xs as [|x xs IH]; intros ys f H; destruct ys as [|y ys]; cbn in *;
    try discriminate; [reflexivity|].
  injection H as H1 H2; rewrite H1, (IH ys f H2); reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "set_eq_membership" *)
Theorem set_eq_membership : forall (a b : A -> Prop) x, a = b /\ x IN a -> x IN b.
Proof. intros a b x [-> H]; exact H. Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "el_reduc_tl" *)
Theorem el_reduc_tl : forall (l : list A) n `{Inhabited A},
  0 < n /\ n < LENGTH l -> EL n l = EL (n - 1) (TL l).
Proof.
  intros l n ? [H0 H1]; destruct l as [|x l]; [cbn in H1; lia|].
  rewrite EL_cons_pos by lia; reflexivity.
Qed.

End Props.

Section ListProps.
Context {A : Type} {HdecA : EqDecision A}.

Lemma ALL_DISTINCT_NoDup (l : list A) : is_true (ALL_DISTINCT l) <-> NoDup l.
Proof.
  unfold is_true; induction l as [|x l IH]; cbn.
  - split; [constructor|reflexivity].
  - rewrite Bool.andb_true_iff, IH, Bool.negb_true_iff.
    split.
    + intros [Hm Hn]; constructor; [|exact Hn].
      intros Hi; apply MEM_In in Hi; congruence.
    + intros Hn; inversion Hn as [|? ? Hni Hnd]; subst; split; [|exact Hnd].
      destruct (MEM x l) eqn:E; [|reflexivity]. apply MEM_In in E; tauto.
Qed.

Lemma DISJOINT_set_iff (xs ys : list A) :
  DISJOINT (set xs) (set ys) <-> (forall x, In x xs -> ~ In x ys).
Proof.
  unfold DISJOINT; split.
  - intros H x Hx Hy.
    assert (Hc : pred_set.INTER (set xs) (set ys) x) by (split; apply IN_set; assumption).
    rewrite H in Hc; exact Hc.
  - intros H; apply functional_extensionality; intros x; apply propositional_extensionality.
    split; [|intros []].
    intros [Hx Hy]; apply (H x); apply IN_set; assumption.
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "distinct_lists_eq_disjoint" *)
Theorem distinct_lists_eq_disjoint : forall xs ys : list A,
  is_true (distinct_lists xs ys) <-> DISJOINT (set xs) (set ys).
Proof.
  intros xs ys; rewrite DISJOINT_set_iff; unfold distinct_lists, is_true.
  rewrite EVERY_Forall, Forall_forall; split; intros H x Hx; specialize (H x Hx).
  - rewrite Bool.negb_true_iff in H; intros Hy; apply MEM_In in Hy; congruence.
  - rewrite Bool.negb_true_iff; destruct (MEM x ys) eqn:E; [|reflexivity].
    apply MEM_In in E; tauto.
Qed.

Lemma distinct_lists_iff (xs ys : list A) :
  is_true (distinct_lists xs ys) <-> (forall x, In x xs -> ~ In x ys).
Proof. rewrite distinct_lists_eq_disjoint; apply DISJOINT_set_iff. Qed.

Lemma NoDup_app_disj (xs ys : list A) :
  NoDup (xs ++ ys) -> forall x, In x xs -> ~ In x ys.
Proof.
  induction xs as [|z xs IH]; intros H x Hx; [destruct Hx|].
  cbn in H; inversion H as [|? ? Hn Hd]; subst.
  destruct Hx as [<-|Hx]; [intros Hy; apply Hn, in_or_app; right; exact Hy|].
  apply IH; assumption.
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "distinct_lists_append" *)
Theorem distinct_lists_append : forall xs ys : list A,
  is_true (ALL_DISTINCT (xs ++ ys)) -> is_true (distinct_lists xs ys).
Proof.
  intros xs ys H; apply ALL_DISTINCT_NoDup in H; apply distinct_lists_iff.
  apply NoDup_app_disj, H.
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "distinct_lists_commutes" *)
Theorem distinct_lists_commutes : forall xs ys : list A,
  distinct_lists xs ys = distinct_lists ys xs.
Proof.
  intros xs ys; apply Bool.eq_true_iff_eq; fold (is_true (distinct_lists xs ys)) (is_true (distinct_lists ys xs)).
  rewrite !distinct_lists_iff; split; intros H x H1 H2; exact (H x H2 H1).
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "distinct_lists_cons" *)
Theorem distinct_lists_cons : forall ns xs ys zs : list A,
  is_true (distinct_lists (ns ++ xs) (ys ++ zs)) -> is_true (distinct_lists xs zs).
Proof.
  intros ns xs ys zs; rewrite !distinct_lists_iff; intros H x H1 H2.
  apply (H x); apply in_or_app; right; assumption.
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "distinct_lists_simp_cons" *)
Theorem distinct_lists_simp_cons : forall (xs : list A) y ys,
  is_true (distinct_lists xs (y :: ys)) -> is_true (distinct_lists xs ys).
Proof.
  intros xs y ys; rewrite !distinct_lists_iff; intros H x H1 H2.
  apply (H x H1); right; exact H2.
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "distinct_lists_append_intro" *)
Theorem distinct_lists_append_intro : forall xs ys zs : list A,
  is_true (distinct_lists xs ys) /\ is_true (distinct_lists xs zs) ->
  is_true (distinct_lists xs (ys ++ zs)).
Proof.
  intros xs ys zs; rewrite !distinct_lists_iff; intros [H1 H2] x Hx Hy.
  apply in_app_or in Hy as [Hy|Hy]; [exact (H1 x Hx Hy)|exact (H2 x Hx Hy)].
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "distinct_lists_append_right_elim" *)
Theorem distinct_lists_append_right_elim : forall xs ys zs : list A,
  is_true (distinct_lists xs (ys ++ zs)) ->
  is_true (distinct_lists xs ys) /\ is_true (distinct_lists xs zs).
Proof.
  intros xs ys zs; rewrite !distinct_lists_iff; intros H; split; intros x Hx Hy;
    apply (H x Hx), in_or_app; tauto.
Qed.

Lemma In_firstn (x : A) n l : In x (firstn n l) -> In x l.
Proof. intros H; rewrite <- (firstn_skipn n l); apply in_or_app; left; exact H. Qed.

Lemma In_skipn (x : A) n l : In x (skipn n l) -> In x l.
Proof. intros H; rewrite <- (firstn_skipn n l); apply in_or_app; right; exact H. Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "all_distinct_take" *)
Theorem all_distinct_take : forall (ns : list A) n,
  is_true (ALL_DISTINCT ns) /\ n <= LENGTH ns -> is_true (ALL_DISTINCT (TAKE n ns)).
Proof.
  intros ns n [H _]; rewrite ALL_DISTINCT_NoDup in *; rewrite TAKE_firstn.
  rewrite <- (firstn_skipn (N.to_nat n) ns) in H; eapply NoDup_app_remove_r; exact H.
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "all_distinct_drop" *)
Theorem all_distinct_drop : forall (ns : list A) n,
  is_true (ALL_DISTINCT ns) /\ n <= LENGTH ns -> is_true (ALL_DISTINCT (DROP n ns)).
Proof.
  intros ns n [H _]; rewrite ALL_DISTINCT_NoDup in *; rewrite DROP_skipn.
  rewrite <- (firstn_skipn (N.to_nat n) ns) in H; eapply NoDup_app_remove_l; exact H.
Qed.

Lemma skipn_add_firstn_disj (n m p : nat) (ns : list A) :
  NoDup ns -> forall x, In x (firstn n ns) -> ~ In x (firstn p (skipn (n + m) ns)).
Proof.
  intros H x H1 H2.
  rewrite <- (firstn_skipn n ns) in H.
  apply In_firstn in H2. rewrite Nat.add_comm, <- skipn_skipn in H2. apply In_skipn in H2.
  exact (NoDup_app_disj _ _ H x H1 H2).
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "disjoint_take_drop_sum" *)
Theorem disjoint_take_drop_sum : forall n m p (ns : list A),
  is_true (ALL_DISTINCT ns) ->
  DISJOINT (set (TAKE n ns)) (set (TAKE p (DROP (n + m) ns))).
Proof.
  intros n m p ns H; apply ALL_DISTINCT_NoDup in H; apply DISJOINT_set_iff.
  rewrite !TAKE_firstn, DROP_skipn, N2Nat.inj_add. apply skipn_add_firstn_disj, H.
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "disjoint_drop_take_sum" *)
Theorem disjoint_drop_take_sum : forall n m p (ns : list A),
  is_true (ALL_DISTINCT ns) ->
  DISJOINT (set (TAKE p (DROP (n + m) ns))) (set (TAKE n ns)).
Proof.
  intros n m p ns H; apply ALL_DISTINCT_NoDup in H; apply DISJOINT_set_iff.
  rewrite !TAKE_firstn, DROP_skipn, N2Nat.inj_add. intros x H1 H2.
  exact (skipn_add_firstn_disj _ _ _ ns H x H2 H1).
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "all_distinct_take_frop_disjoint" *)
Theorem all_distinct_take_frop_disjoint : forall (ns : list A) n,
  is_true (ALL_DISTINCT ns) /\ n <= LENGTH ns ->
  DISJOINT (set (TAKE n ns)) (set (DROP n ns)).
Proof.
  intros ns n [H _]; apply ALL_DISTINCT_NoDup in H; apply DISJOINT_set_iff.
  rewrite TAKE_firstn, DROP_skipn; apply NoDup_app_disj.
  rewrite firstn_skipn; exact H.
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "disjoint_not_mem_el" *)
Theorem disjoint_not_mem_el : forall (xs ys : list A) n `{Inhabited A},
  DISJOINT (set xs) (set ys) /\ n < LENGTH xs -> ~ is_true (MEM (EL n xs) ys).
Proof.
  intros xs ys n ? [H Hn]; rewrite DISJOINT_set_iff in H; unfold is_true; rewrite MEM_In.
  apply H; rewrite EL_nth by exact Hn; apply nth_In; rewrite LENGTH_length in Hn; lia.
Qed.

End ListProps.

Section FmapProps.
Context {K V : Type} {HdecK : EqDecision K}.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "flookup_fupdate_zip_not_mem" *)
Theorem flookup_fupdate_zip_not_mem : forall (xs : list K) (ys : list V) f n,
  LENGTH xs = LENGTH ys /\ ~ is_true (MEM n xs) ->
  FLOOKUP (f |++ ZIP (xs, ys)) n = FLOOKUP f n.
Proof.
  intros xs ys f n [Hl Hn]; apply FLOOKUP_FUPDATE_LIST_notin.
  intros Hi; apply Hn; unfold is_true; rewrite MEM_In.
  clear Hn Hl; revert ys Hi; induction xs as [|x xs IH]; intros [|y ys] Hi; cbn in *; try tauto.
  destruct Hi as [->|Hi]; [left; reflexivity|right; exact (IH ys Hi)].
Qed.

Lemma In_map_fst_ZIP (xs : list K) (ys : list V) k :
  In k (map fst (ZIP (xs, ys))) -> In k xs.
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys] Hi; cbn in *; try tauto.
  destruct Hi as [->|Hi]; [left; reflexivity|right; exact (IH ys Hi)].
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "update_eq_zip_flookup" *)
Theorem update_eq_zip_flookup : forall (xs : list K) (f : fmap K V) ys n
    `{Inhabited K} `{Inhabited V},
  is_true (ALL_DISTINCT xs) /\ LENGTH xs = LENGTH ys /\ n < LENGTH xs ->
  FLOOKUP (f |++ ZIP (xs, ys)) (EL n xs) = SOME (EL n ys).
Proof.
  induction xs as [|x xs IH]; intros f ys n ? ? [Hd [Hl Hn]]; [cbn in Hn; lia|].
  destruct ys as [|y ys]; [rewrite !LENGTH_length in Hl; cbn [length] in Hl; lia|].
  rewrite !LENGTH_cons in Hn. rewrite (LENGTH_cons x xs), (LENGTH_cons y ys) in Hl. cbn in Hd; unfold is_true in Hd.
  apply Bool.andb_true_iff in Hd as [Hm Hd].
  change (FLOOKUP ((f |+ (x, y)) |++ ZIP (xs, ys)) (EL n (x :: xs)) = SOME (EL n (y :: ys))).
  destruct (N.eq_dec n 0) as [->|Hn0].
  - rewrite !EL_cons_0. rewrite FLOOKUP_FUPDATE_LIST_notin.
    + rewrite FLOOKUP_UPDATE; destruct (decide (x = x)); [reflexivity|congruence].
    + intros Hi; apply In_map_fst_ZIP, MEM_In in Hi; rewrite Hi in Hm; discriminate.
  - rewrite !EL_cons_pos by lia. apply IH; split; [exact Hd|split; lia].
Qed.

(*! HOL "cakeml/pancake/semantics/pan_commonPropsScript.sml" "domsub_commutes_fupdate" *)
Theorem domsub_commutes_fupdate : forall (xs : list K) (ys : list V) fm x,
  ~ is_true (MEM x xs) /\ LENGTH xs = LENGTH ys ->
  (fm |++ ZIP (xs, ys)) \\ x = (fm \\ x) |++ ZIP (xs, ys).
Proof.
  intros xs ys fm x [Hm _]; apply fmap_ext; intros k.
  rewrite DOMSUB_FLOOKUP_THM. destruct (decide (x = k)) as [<-|Hne].
  - rewrite FLOOKUP_FUPDATE_LIST_notin; [rewrite DOMSUB_FLOOKUP_THM; destruct (decide (x = x)); congruence|].
    intros Hi; apply In_map_fst_ZIP, MEM_In in Hi; exact (Hm Hi).
  - destruct (in_dec (fun a b => decide (a = b)) k (map fst (ZIP (xs, ys)))) as [Hi|Hi].
    + apply FLOOKUP_FUPDATE_LIST_in, Hi.
    + rewrite !FLOOKUP_FUPDATE_LIST_notin by exact Hi.
      rewrite DOMSUB_FLOOKUP_THM; destruct (decide (x = k)); congruence.
Qed.

End FmapProps.
