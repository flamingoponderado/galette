(** * HOL4 [alist]: association lists and finite maps

    [ALOOKUP] is computable (keys compared with [EqDecision]).
    [alist_to_fmap al] is the finite map whose lookup function is
    [ALOOKUP al]; HOL's defining equation (a [FOLDR] of updates) is the
    theorem [alist_to_fmap_def].

    [fmap_to_alist] is not executable.  HOL defines it through
    [SET_TO_LIST (FDOM s)], i.e. with a choice-determined key order; here it
    is a chosen duplicate-free list with the same bindings, whose order is
    likewise unspecified.  HOL theorems that depend on HOL's particular
    order (e.g. [MAP_values_fmap_to_alist]) are not ported.

    HOL [MEM] is [list]'s boolean [MEM]; a statement with [MEM (k,v) l]
    therefore needs [EqDecision] on the values as well.  Sets are [pred_set]'s. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.finite_maps Require Import finite_map.
Open Scope N_scope.

Section Alookup.
Context {K V : Type} `{EqDecision K}.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_def" *)
Fixpoint ALOOKUP (l : list (K * V)) (q : K) : option V :=
  match l with
  | [] => NONE
  | (x, y) :: t => if decide (x = q) then SOME y else ALOOKUP t q
  end.

Lemma ALOOKUP_finite (l : list (K * V)) :
  exists ks : list K, forall k, ALOOKUP l k <> None -> In k ks.
Proof.
  exists (map fst l); intros k; induction l as [|[x y] t IH]; cbn; [tauto|].
  destruct (decide (x = k)); [left; assumption|right; apply IH; assumption].
Qed.

(** HOL [alist_to_fmap] ([alist_to_fmap_def] below). *)
Definition alist_to_fmap (s : list (K * V)) : fmap K V := mk_fmap (ALOOKUP s) (ALOOKUP_finite s).

(** HOL [fmap_to_alist] (see the header); not executable. *)
Definition fmap_to_alist (s : fmap K V) : list (K * V) :=
  select (fun al => NoDup (map fst al) /\ forall k v, In (k, v) al <-> FLOOKUP s k = Some v).

Lemma bindings_of_spec (s : fmap K V) (ks : list K) :
  NoDup ks ->
  let al := flat_map (fun k => match FLOOKUP s k with Some v => [(k, v)] | None => [] end) ks in
  NoDup (map fst al) /\ forall k v, In (k, v) al <-> In k ks /\ FLOOKUP s k = Some v.
Proof.
  induction 1 as [|a ks Ha Hks IH]; cbn; [split; [constructor|tauto]|].
  destruct IH as [IH1 IH2].
  destruct (FLOOKUP s a) as [w|] eqn:E; cbn; split.
  - constructor; [|exact IH1].
    rewrite in_map_iff; intros [[k v] [Hk Hin]]; cbn in Hk; subst k.
    apply IH2 in Hin; tauto.
  - intros k v; rewrite IH2; split.
    + intros [h|h]; [injection h as <- <-; auto|tauto].
    + intros [[<-|h] h']; [left; congruence|right; auto].
  - exact IH1.
  - intros k v; rewrite IH2; split; [tauto|intros [[<-|h] h']; [congruence|auto]].
Qed.

Lemma fmap_to_alist_spec (s : fmap K V) :
  NoDup (map fst (fmap_to_alist s)) /\
  forall k v, In (k, v) (fmap_to_alist s) <-> FLOOKUP s k = Some v.
Proof.
  unfold fmap_to_alist; match goal with |- context [select ?P] => apply (select_spec P) end.
  destruct (FLOOKUP_finite s) as [l Hl].
  set (ks := nodup (fun x y => decide (x = y)) l).
  destruct (bindings_of_spec s ks (NoDup_nodup _ l)) as [h1 h2].
  eexists; split; [exact h1|intros k v; rewrite h2; split; [tauto|intros E; split; [|exact E]]].
  apply nodup_In, Hl; rewrite E; discriminate.
Qed.

Lemma ALL_DISTINCT_iff {A} `{EqDecision A} (l : list A) : is_true (ALL_DISTINCT l) <-> NoDup l.
Proof.
  unfold is_true; induction l as [|h t IH]; cbn; [split; [constructor|reflexivity]|].
  rewrite andb_true_iff, negb_true_iff, IH; split.
  - intros [h1 h2]; constructor; [|exact h2].
    rewrite <- MEM_iff; unfold is_true; rewrite h1; discriminate.
  - intros h'; inversion h' as [|? ? h1 h2]; subst; split; [|exact h2].
    destruct (MEM h t) eqn:E; [|reflexivity]; exfalso; apply h1, MEM_iff; exact E.
Qed.

Lemma bool_decide_eq_true_2 (P : Prop) `{Decision P} : P -> bool_decide P = true.
Proof. intros; apply bool_decide_spec; assumption. Qed.

Lemma bool_decide_eq_false_2 (P : Prop) `{Decision P} : ~ P -> bool_decide P = false.
Proof. intros h; unfold bool_decide; destruct (decide P); tauto. Qed.

Lemma ALOOKUP_In l k v : ALOOKUP l k = Some v -> In (k, v) l.
Proof.
  induction l as [|[x y] t IH]; cbn; [discriminate|].
  destruct (decide (x = k)) as [<-|n]; [intros [= <-]; left; reflexivity|right; auto].
Qed.

Lemma ALOOKUP_None_iff l x : ALOOKUP l x = None <-> ~ In x (map fst l).
Proof.
  induction l as [|[a b] t IH]; cbn; [tauto|].
  destruct (decide (a = x)); [split; [discriminate|tauto]|rewrite IH; intuition].
Qed.

Lemma ALOOKUP_NoDup_In l k v : NoDup (map fst l) -> In (k, v) l -> ALOOKUP l k = Some v.
Proof.
  induction l as [|[a b] t IH]; cbn; [tauto|]; intros hd hin.
  inversion hd as [|? ? hnot hd']; subst; destruct hin as [h|h].
  - injection h as -> ->; destruct (decide (k = k)); [reflexivity|tauto].
  - destruct (decide (a = k)) as [->|n]; [|auto].
    exfalso; apply hnot; apply in_map_iff; exists (k, v); auto.
Qed.

Lemma ALOOKUP_app l1 l2 k :
  ALOOKUP (l1 ++ l2) k = match ALOOKUP l1 k with Some v => Some v | None => ALOOKUP l2 k end.
Proof.
  induction l1 as [|[a b] t IH]; cbn; [reflexivity|]; destruct (decide (a = k)); auto.
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "alist_to_fmap_thm" *)
Theorem alist_to_fmap_thm : forall k v (t : list (K * V)),
  (alist_to_fmap [] = FEMPTY) /\ (alist_to_fmap ((k, v) :: t) = alist_to_fmap t |+ (k, v)).
Proof. intros; split; apply fmap_ext; intros; reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "alist_to_fmap_def" *)
Theorem alist_to_fmap_def : forall s : list (K * V),
  alist_to_fmap s = FOLDR (fun '(k, v) f => f |+ (k, v)) FEMPTY s.
Proof.
  induction s as [|[k v] t IH]; [apply fmap_ext; intros; reflexivity|].
  cbn [FOLDR]; rewrite <- IH; apply (alist_to_fmap_thm k v t).
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_EQ_FLOOKUP" *)
Theorem ALOOKUP_EQ_FLOOKUP : forall (al : list (K * V)) fm,
  (FLOOKUP (alist_to_fmap al) = ALOOKUP al) /\ (ALOOKUP (fmap_to_alist fm) = FLOOKUP fm).
Proof.
  intros al fm; split; [reflexivity|]; apply functional_extensionality; intros k.
  destruct (fmap_to_alist_spec fm) as [h1 h2].
  destruct (FLOOKUP fm k) as [v|] eqn:E.
  - apply ALOOKUP_NoDup_In; [exact h1|apply h2, E].
  - apply ALOOKUP_None_iff; rewrite in_map_iff; intros [[a b] [<- h]]; apply h2 in h; cbn in *; congruence.
Qed.

Lemma FLOOKUP_alist_to_fmap (al : list (K * V)) k : FLOOKUP (alist_to_fmap al) k = ALOOKUP al k.
Proof. reflexivity. Qed.

Lemma ALOOKUP_fmap_to_alist (fm : fmap K V) k : ALOOKUP (fmap_to_alist fm) k = FLOOKUP fm k.
Proof. rewrite (proj2 (ALOOKUP_EQ_FLOOKUP [] fm)); reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "fmap_to_alist_FEMPTY" *)
Theorem fmap_to_alist_FEMPTY : fmap_to_alist (FEMPTY : fmap K V) = [].
Proof.
  destruct (fmap_to_alist_spec (FEMPTY : fmap K V)) as [_ h].
  destruct (fmap_to_alist FEMPTY) as [|[k v] t]; [reflexivity|].
  exfalso; specialize (h k v); cbn in h; destruct h as [h _]; discriminate (h (or_introl eq_refl)).
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_NONE" *)
Theorem ALOOKUP_NONE : forall (l : list (K * V)) x, (ALOOKUP l x = NONE) <-> ~ MEM x (MAP FST l).
Proof. intros; rewrite ALOOKUP_None_iff, MEM_iff; reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_TABULATE" *)
Theorem ALOOKUP_TABULATE : forall x l (f : K -> V),
  MEM x l -> ALOOKUP (MAP (fun k => (k, f k)) l) x = SOME (f x).
Proof.
  intros x l f h; rewrite MEM_iff in h; induction l as [|a t IH]; [destruct h|cbn].
  destruct (decide (a = x)) as [->|n]; [reflexivity|apply IH; destruct h; [congruence|auto]].
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "fmap_to_alist_to_fmap" *)
Theorem fmap_to_alist_to_fmap : forall fm : fmap K V, alist_to_fmap (fmap_to_alist fm) = fm.
Proof. intros; apply fmap_ext; intros k; apply ALOOKUP_fmap_to_alist. Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "MEM_pair_fmap_to_alist_FLOOKUP" *)
Theorem MEM_pair_fmap_to_alist_FLOOKUP `{EqDecision V} : forall x y (fm : fmap K V),
  MEM (x, y) (fmap_to_alist fm) <-> (FLOOKUP fm x = SOME y).
Proof. intros; rewrite MEM_iff; apply fmap_to_alist_spec. Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "MEM_fmap_to_alist_FLOOKUP" *)
Theorem MEM_fmap_to_alist_FLOOKUP `{EqDecision V} : forall p (fm : fmap K V),
  MEM p (fmap_to_alist fm) <-> (FLOOKUP fm (FST p) = SOME (SND p)).
Proof. intros [x y] fm; apply MEM_pair_fmap_to_alist_FLOOKUP. Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "MEM_fmap_to_alist" *)
Theorem MEM_fmap_to_alist `{EqDecision V} `{Inhabited V} : forall x y (fm : fmap K V),
  MEM (x, y) (fmap_to_alist fm) <-> x IN FDOM fm /\ (FAPPLY fm x = y).
Proof. intros; rewrite MEM_pair_fmap_to_alist_FLOOKUP; apply flookup_thm. Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ALL_DISTINCT_fmap_to_alist_keys" *)
Theorem ALL_DISTINCT_fmap_to_alist_keys : forall fm : fmap K V,
  ALL_DISTINCT (MAP FST (fmap_to_alist fm)).
Proof. intros; apply ALL_DISTINCT_iff, fmap_to_alist_spec. Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "set_MAP_FST_fmap_to_alist" *)
Theorem set_MAP_FST_fmap_to_alist : forall fm : fmap K V,
  set (MAP FST (fmap_to_alist fm)) = FDOM fm.
Proof.
  intros fm; apply functional_extensionality; intros k; apply propositional_extensionality.
  change (k IN set (MAP FST (fmap_to_alist fm)) <-> FDOM fm k).
  rewrite IN_set, in_map_iff; unfold FDOM; destruct (fmap_to_alist_spec fm) as [_ h]; split.
  - intros [[a b] [<- hi]]; apply h in hi; cbn; rewrite hi; discriminate.
  - destruct (FLOOKUP fm k) as [v|] eqn:E; [intros _|tauto].
    exists (k, v); split; [reflexivity|apply h, E].
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "fmap_to_alist_inj" *)
Theorem fmap_to_alist_inj : forall f1 f2 : fmap K V, (fmap_to_alist f1 = fmap_to_alist f2) -> (f1 = f2).
Proof.
  intros f1 f2 E; rewrite <- (fmap_to_alist_to_fmap f1), <- (fmap_to_alist_to_fmap f2), E; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_MEM" *)
Theorem ALOOKUP_MEM `{EqDecision V} : forall (al : list (K * V)) k v,
  (ALOOKUP al k = SOME v) -> MEM (k, v) al.
Proof. intros; apply MEM_iff, ALOOKUP_In; assumption. Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_FAILS" *)
Theorem ALOOKUP_FAILS `{EqDecision V} : forall (l : list (K * V)) x,
  (ALOOKUP l x = NONE) <-> forall k v, MEM (k, v) l -> k <> x.
Proof.
  intros l x; rewrite ALOOKUP_None_iff; split.
  - intros h k v hm ->; apply h, in_map_iff; exists (x, v); rewrite <- MEM_iff; auto.
  - intros h hi; apply in_map_iff in hi as [[a b] [ha hi]]; cbn in ha; subst a.
    apply (h x b); [apply MEM_iff, hi|reflexivity].
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_ALL_DISTINCT_MEM" *)
Theorem ALOOKUP_ALL_DISTINCT_MEM `{EqDecision V} : forall (al : list (K * V)) k v,
  ALL_DISTINCT (MAP FST al) /\ MEM (k, v) al -> (ALOOKUP al k = SOME v).
Proof.
  intros al k v [h1 h2]; apply ALOOKUP_NoDup_In; [apply ALL_DISTINCT_iff, h1|apply MEM_iff, h2].
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_SOME_FAPPLY_alist_to_fmap" *)
Theorem ALOOKUP_SOME_FAPPLY_alist_to_fmap `{Inhabited V} : forall (al : list (K * V)) k v,
  (ALOOKUP al k = SOME v) -> (FAPPLY (alist_to_fmap al) k = v).
Proof. intros al k v E; unfold FAPPLY; rewrite FLOOKUP_alist_to_fmap, E; reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "alist_to_fmap_FAPPLY_MEM" *)
Theorem alist_to_fmap_FAPPLY_MEM `{EqDecision V} `{Inhabited V} : forall (al : list (K * V)) z,
  z IN FDOM (alist_to_fmap al) -> MEM (z, FAPPLY (alist_to_fmap al) z) al.
Proof.
  intros al z h; unfold_sets; unfold FDOM in h; rewrite FLOOKUP_alist_to_fmap in h.
  destruct (ALOOKUP al z) as [v|] eqn:E; [|tauto].
  rewrite (ALOOKUP_SOME_FAPPLY_alist_to_fmap al z v E); apply ALOOKUP_MEM, E.
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "FDOM_alist_to_fmap" *)
Theorem FDOM_alist_to_fmap : forall al : list (K * V),
  FDOM (alist_to_fmap al) = set (MAP FST al).
Proof.
  intros al; apply functional_extensionality; intros k; apply propositional_extensionality.
  change (FDOM (alist_to_fmap al) k <-> k IN set (MAP FST al)).
  rewrite IN_set; unfold FDOM; rewrite FLOOKUP_alist_to_fmap.
  pose proof (ALOOKUP_None_iff al k) as h.
  destruct (in_dec (fun x y => decide (x = y)) k (map fst al)) as [i|n].
  - split; [intros _; exact i|intros _ E; apply h in E; tauto].
  - split; [intros E; exfalso; apply E, h, n|intros i; tauto].
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_APPEND" *)
Theorem ALOOKUP_APPEND : forall (l1 l2 : list (K * V)) k,
  ALOOKUP (l1 ++ l2) k = match ALOOKUP l1 k with SOME v => SOME v | NONE => ALOOKUP l2 k end.
Proof. exact ALOOKUP_app. Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_prefix" *)
Theorem ALOOKUP_prefix : forall (ls : list (K * V)) k ls2 v,
  ((ALOOKUP ls k = SOME v) -> (ALOOKUP (ls ++ ls2) k = SOME v)) /\
  ((ALOOKUP ls k = NONE) -> (ALOOKUP (ls ++ ls2) k = ALOOKUP ls2 k)).
Proof. intros; rewrite ALOOKUP_app; split; intros ->; reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "alist_to_fmap_APPEND" *)
Theorem alist_to_fmap_APPEND : forall l1 l2 : list (K * V),
  alist_to_fmap (l1 ++ l2) = FUNION (alist_to_fmap l1) (alist_to_fmap l2).
Proof. intros; apply fmap_ext; intros k; rewrite FLOOKUP_FUNION; apply ALOOKUP_app. Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "alist_to_fmap_prefix" *)
Theorem alist_to_fmap_prefix : forall ls l1 l2 : list (K * V),
  (alist_to_fmap l1 = alist_to_fmap l2) -> (alist_to_fmap (ls ++ l1) = alist_to_fmap (ls ++ l2)).
Proof. intros ls l1 l2 E; rewrite !alist_to_fmap_APPEND, E; reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_APPEND_same" *)
Theorem ALOOKUP_APPEND_same : forall l1 l2 l : list (K * V),
  (ALOOKUP l1 = ALOOKUP l2) -> (ALOOKUP (l1 ++ l) = ALOOKUP (l2 ++ l)).
Proof.
  intros l1 l2 l E; apply functional_extensionality; intros k; rewrite !ALOOKUP_app, E; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_ALL_DISTINCT_EL" *)
Theorem ALOOKUP_ALL_DISTINCT_EL `{Inhabited K} `{Inhabited V} : forall (ls : list (K * V)) n,
  n < LENGTH ls /\ ALL_DISTINCT (MAP FST ls) ->
  (ALOOKUP ls (FST (EL n ls)) = SOME (SND (EL n ls))).
Proof.
  intros ls n [h1 h2]; apply ALL_DISTINCT_iff in h2; rewrite EL_nth by exact h1.
  destruct (nth (N.to_nat n) ls ARB) as [k v] eqn:E; cbn; apply ALOOKUP_NoDup_In; [exact h2|].
  rewrite <- E; apply nth_In; rewrite LENGTH_length in h1; lia.
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_FILTER" *)
Theorem ALOOKUP_FILTER : forall (P : K -> bool) (ls : list (K * V)) x,
  ALOOKUP (FILTER (fun '(k, v) => P k) ls) x = if P x then ALOOKUP ls x else NONE.
Proof.
  intros P ls x; induction ls as [|[a b] t IH]; cbn; [destruct (P x); reflexivity|].
  destruct (P a) eqn:Ea; cbn.
  - destruct (decide (a = x)) as [->|n]; [rewrite Ea; reflexivity|exact IH].
  - destruct (decide (a = x)) as [->|n]; [rewrite IH, Ea; reflexivity|exact IH].
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "alookup_filter" *)
Theorem alookup_filter : forall {T} (f : T) (l : list (K * V)) x,
  ALOOKUP l x = ALOOKUP (FILTER (fun '(x', y) => bool_decide (x = x')) l) x.
Proof.
  intros T f l x; induction l as [|[a b] t IH]; cbn; [reflexivity|].
  destruct (decide (a = x)) as [->|n].
  - unfold bool_decide; destruct (decide (x = x)); [|tauto]; cbn; destruct (decide (x = x)); [reflexivity|tauto].
  - unfold bool_decide; destruct (decide (x = a)); [congruence|exact IH].
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_IN_FRANGE" *)
Theorem ALOOKUP_IN_FRANGE : forall (ls : list (K * V)) k v,
  (ALOOKUP ls k = SOME v) -> v IN FRANGE (alist_to_fmap ls).
Proof. intros ls k v E; exists k; exact E. Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "IN_FRANGE_alist_to_fmap_suff" *)
Theorem IN_FRANGE_alist_to_fmap_suff `{EqDecision V} : forall (P : V -> Prop) (ls : list (K * V)),
  (forall v, MEM v (MAP SND ls) -> P v) -> (forall v, v IN FRANGE (alist_to_fmap ls) -> P v).
Proof.
  intros P ls h v [k E]; apply h, MEM_iff, in_map_iff; exists (k, v); split; [reflexivity|].
  apply ALOOKUP_In, E.
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "alookup_distinct_reverse" *)
Theorem alookup_distinct_reverse : forall (l : list (K * V)) k,
  ALL_DISTINCT (MAP FST l) -> (ALOOKUP (REVERSE l) k = ALOOKUP l k).
Proof.
  intros l k h; apply ALL_DISTINCT_iff in h.
  destruct (ALOOKUP l k) as [v|] eqn:E.
  - apply ALOOKUP_NoDup_In; [rewrite map_rev; apply NoDup_rev, h|apply in_rev; rewrite rev_involutive; apply ALOOKUP_In, E].
  - apply ALOOKUP_None_iff; apply ALOOKUP_None_iff in E; rewrite map_rev, <- in_rev; exact E.
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "flookup_fupdate_list" *)
Theorem flookup_fupdate_list : forall (l : list (K * V)) k m,
  FLOOKUP (m |++ l) k =
  match ALOOKUP (REVERSE l) k with SOME v => SOME v | NONE => FLOOKUP m k end.
Proof.
  induction l as [|[a b] t IH]; intros k m; [reflexivity|].
  change (FLOOKUP ((m |+ (a, b)) |++ t) k =
    match ALOOKUP (REVERSE t ++ [(a, b)]) k with SOME v => SOME v | NONE => FLOOKUP m k end).
  rewrite IH, ALOOKUP_app; destruct (ALOOKUP (REVERSE t) k); [reflexivity|].
  rewrite FLOOKUP_UPDATE; cbn; destruct (decide (a = k)); reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "FLOOKUP_FUPDATE_LIST" *)
Theorem FLOOKUP_FUPDATE_LIST : forall (xs : list (K * V)) k m,
  FLOOKUP (m |++ xs) k =
  match ALOOKUP (REVERSE xs) k with NONE => FLOOKUP m k | SOME x => SOME x end.
Proof. intros; rewrite flookup_fupdate_list; destruct (ALOOKUP (REVERSE xs) k); reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME" *)
Theorem FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME : forall (ls : list (K * V)) k v fm,
  (ALOOKUP ls k = SOME v) -> (FLOOKUP (fm |++ (REVERSE ls)) k = SOME v).
Proof. intros ls k v fm E; rewrite flookup_fupdate_list, rev_involutive, E; reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "FLOOKUP_FUPDATE_LIST_ALOOKUP_NONE" *)
Theorem FLOOKUP_FUPDATE_LIST_ALOOKUP_NONE : forall (ls : list (K * V)) k fm,
  (ALOOKUP ls k = NONE) -> (FLOOKUP (fm |++ (REVERSE ls)) k = FLOOKUP fm k).
Proof. intros ls k fm E; rewrite flookup_fupdate_list, rev_involutive, E; reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "FUNION_alist_to_fmap" *)
Theorem FUNION_alist_to_fmap : forall (ls : list (K * V)) fm,
  FUNION (alist_to_fmap ls) fm = fm |++ (REVERSE ls).
Proof.
  intros; apply fmap_ext; intros k; rewrite FLOOKUP_FUNION, flookup_fupdate_list, rev_involutive.
  reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "FUPDATE_LIST_EQ_APPEND_REVERSE" *)
Theorem FUPDATE_LIST_EQ_APPEND_REVERSE : forall (ls : list (K * V)) fm,
  fm |++ ls = alist_to_fmap (REVERSE ls ++ fmap_to_alist fm).
Proof.
  intros; apply fmap_ext; intros k; rewrite flookup_fupdate_list, FLOOKUP_alist_to_fmap,
    ALOOKUP_app, ALOOKUP_fmap_to_alist; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "fupdate_list_funion" *)
Theorem fupdate_list_funion : forall (m : fmap K V) l, m |++ l = FUNION (FEMPTY |++ l) m.
Proof.
  intros; apply fmap_ext; intros k; rewrite FLOOKUP_FUNION, !flookup_fupdate_list.
  destruct (ALOOKUP (REVERSE l) k); reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "mem_to_flookup" *)
Theorem mem_to_flookup `{EqDecision V} : forall x y (l : list (K * V)),
  ALL_DISTINCT (MAP FST l) /\ MEM (x, y) l -> (FLOOKUP (FEMPTY |++ l) x = SOME y).
Proof.
  intros x y l [h1 h2]; rewrite flookup_fupdate_list, alookup_distinct_reverse by exact h1.
  rewrite (ALOOKUP_ALL_DISTINCT_MEM l x y) by (split; assumption); reflexivity.
Qed.

(** HOL [alist_range]. *)
(*! HOL "HOL/src/finite_maps/alistScript.sml" "alist_range_def" *)
Definition alist_range (m : list (K * V)) : V -> Prop := fun v => exists k, ALOOKUP m k = SOME v.

(** ** [AFUPDKEY] and [ADELKEY] *)

(*! HOL "HOL/src/finite_maps/alistScript.sml" "AFUPDKEY_def" *)
Fixpoint AFUPDKEY (k : K) (f : V -> V) (l : list (K * V)) : list (K * V) :=
  match l with
  | [] => []
  | (k', v) :: rest => if decide (k = k') then (k, f v) :: rest else (k', v) :: AFUPDKEY k f rest
  end.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "AFUPDKEY_ALOOKUP" *)
Theorem AFUPDKEY_ALOOKUP : forall k2 f (al : list (K * V)) k1,
  ALOOKUP (AFUPDKEY k2 f al) k1 =
  match ALOOKUP al k1 with NONE => NONE | SOME v => if decide (k1 = k2) then SOME (f v) else SOME v end.
Proof.
  intros k2 f al k1; induction al as [|[a b] t IH]; cbn; [reflexivity|].
  destruct (decide (k2 = a)) as [<-|n]; cbn.
  - destruct (decide (k2 = k1)) as [<-|n']; [destruct (decide (k2 = k2)); [reflexivity|tauto]|].
    destruct (decide (k1 = k2)); [congruence|].
    destruct (ALOOKUP t k1) eqn:E; [|reflexivity].
    destruct (decide (k1 = k2)); [congruence|reflexivity].
  - destruct (decide (a = k1)) as [<-|n']; [|exact IH].
    destruct (decide (a = k2)); [congruence|reflexivity].
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "MAP_FST_AFUPDKEY" *)
Theorem MAP_FST_AFUPDKEY : forall f k (alist : list (K * V)), MAP FST (AFUPDKEY f k alist) = MAP FST alist.
Proof.
  intros f k alist; induction alist as [|[a b] t IH]; cbn; [reflexivity|].
  destruct (decide (f = a)) as [<-|]; cbn; congruence.
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "LENGTH_AFUPDKEY" *)
Theorem LENGTH_AFUPDKEY : forall k f (ls : list (K * V)), LENGTH (AFUPDKEY k f ls) = LENGTH ls.
Proof.
  intros k f ls; induction ls as [|[a b] t IH]; cbn; [reflexivity|].
  destruct (decide (k = a)); cbn; congruence.
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "AFUPDKEY_unchanged" *)
Theorem AFUPDKEY_unchanged : forall k f (alist : list (K * V)),
  (forall v, (ALOOKUP alist k = SOME v) -> (f v = v)) -> (AFUPDKEY k f alist = alist).
Proof.
  intros k f alist; induction alist as [|[a b] t IH]; intros h; cbn in *; [reflexivity|].
  destruct (decide (k = a)) as [<-|n].
  - rewrite h; [reflexivity|destruct (decide (k = k)); [reflexivity|tauto]].
  - f_equal; apply IH; intros v E; apply h; destruct (decide (a = k)); [congruence|exact E].
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "AFUPDKEY_eq" *)
Theorem AFUPDKEY_eq : forall k f1 (l : list (K * V)) f2,
  (forall v, (ALOOKUP l k = SOME v) -> (f1 v = f2 v)) -> (AFUPDKEY k f1 l = AFUPDKEY k f2 l).
Proof.
  intros k f1 l f2; induction l as [|[a b] t IH]; intros h; cbn in *; [reflexivity|].
  destruct (decide (k = a)) as [<-|n].
  - rewrite h; [reflexivity|destruct (decide (k = k)); [reflexivity|tauto]].
  - f_equal; apply IH; intros v E; apply h; destruct (decide (a = k)); [congruence|exact E].
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "AFUPDKEY_o" *)
Theorem AFUPDKEY_o : forall k f1 f2 (al : list (K * V)),
  AFUPDKEY k f1 (AFUPDKEY k f2 al) = AFUPDKEY k (f1 ∘ f2) al.
Proof.
  intros k f1 f2 al; induction al as [|[a b] t IH]; cbn; [reflexivity|].
  destruct (decide (k = a)) as [<-|n]; cbn.
  - destruct (decide (k = k)); [reflexivity|tauto].
  - destruct (decide (k = a)); [congruence|rewrite IH; reflexivity].
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "AFUPDKEY_I" *)
Theorem AFUPDKEY_I : forall n, AFUPDKEY n (I : V -> V) = I.
Proof.
  intros n; apply functional_extensionality; intros l; unfold I at 2.
  apply AFUPDKEY_unchanged; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "AFUPDKEY_comm" *)
Theorem AFUPDKEY_comm : forall k1 k2 f1 f2 (l : list (K * V)),
  k1 <> k2 -> (AFUPDKEY k2 f2 (AFUPDKEY k1 f1 l) = AFUPDKEY k1 f1 (AFUPDKEY k2 f2 l)).
Proof.
  intros k1 k2 f1 f2 l hk; induction l as [|[a b] t IH]; cbn; [reflexivity|].
  destruct (decide (k1 = a)) as [<-|n1], (decide (k2 = k1)) as [|n2]; try congruence; cbn.
  - destruct (decide (k2 = k1)); [congruence|]; destruct (decide (k1 = k1)); [reflexivity|tauto].
  - destruct (decide (k2 = a)) as [<-|n3]; cbn.
    + destruct (decide (k1 = k2)); [congruence|]; destruct (decide (k2 = k2)); [reflexivity|tauto].
    + destruct (decide (k1 = a)); [congruence|]; destruct (decide (k2 = a)); [congruence|].
      rewrite IH; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ADELKEY_def" *)
Definition ADELKEY (k : K) (alist : list (K * V)) : list (K * V) :=
  FILTER (fun p => bool_decide (FST p <> k)) alist.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_ADELKEY" *)
Theorem ALOOKUP_ADELKEY : forall k1 k2 (al : list (K * V)),
  ALOOKUP (ADELKEY k1 al) k2 = if decide (k1 = k2) then NONE else ALOOKUP al k2.
Proof.
  intros k1 k2 al; unfold ADELKEY; induction al as [|[a b] t IH]; cbn [filter ALOOKUP fst].
  - destruct (decide (k1 = k2)); reflexivity.
  - destruct (decide (a = k1)) as [->|n].
    + rewrite (bool_decide_eq_false_2 (k1 <> k1)) by tauto; rewrite IH.
      destruct (decide (k1 = k2)); reflexivity.
    + rewrite (bool_decide_eq_true_2 (a <> k1)) by exact n; cbn [ALOOKUP].
      destruct (decide (a = k2)) as [<-|n']; [|exact IH].
      destruct (decide (k1 = a)); [congruence|reflexivity].
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "MEM_ADELKEY" *)
Theorem MEM_ADELKEY `{EqDecision V} : forall k1 v k2 (al : list (K * V)),
  MEM (k1, v) (ADELKEY k2 al) <-> k1 <> k2 /\ MEM (k1, v) al.
Proof.
  intros; unfold ADELKEY; rewrite !MEM_iff, filter_In, bool_decide_spec; cbn; tauto.
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ADELKEY_AFUPDKEY_same" *)
Theorem ADELKEY_AFUPDKEY_same : forall fd f (ls : list (K * V)),
  ADELKEY fd (AFUPDKEY fd f ls) = ADELKEY fd ls.
Proof.
  intros fd f ls; unfold ADELKEY; induction ls as [|[a b] t IH]; cbn [AFUPDKEY]; [reflexivity|].
  destruct (decide (fd = a)) as [<-|n]; cbn [filter fst].
  - rewrite (bool_decide_eq_false_2 (fd <> fd)) by tauto; reflexivity.
  - rewrite (bool_decide_eq_true_2 (a <> fd)) by congruence; rewrite IH; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ADELKEY_unchanged" *)
Theorem ADELKEY_unchanged : forall x (ls : list (K * V)),
  ((ADELKEY x ls = ls) <-> ~ MEM x (MAP FST ls)).
Proof.
  intros x ls; rewrite MEM_iff; unfold ADELKEY; induction ls as [|[a b] t IH];
    cbn [filter fst map In]; [tauto|].
  destruct (decide (a = x)) as [->|n].
  - rewrite (bool_decide_eq_false_2 (x <> x)) by tauto.
    split; [intros E; exfalso|intros h; exfalso; apply h; left; reflexivity].
    assert (hl := f_equal (@length _) E); cbn in hl.
    pose proof (filter_length_le (fun p => bool_decide (FST p <> x)) t); lia.
  - rewrite (bool_decide_eq_true_2 (a <> x)) by exact n.
    split; [intros E; injection E as E; apply IH in E; tauto|intros h; f_equal; apply IH; tauto].
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ADELKEY_AFUPDKEY" *)
Theorem ADELKEY_AFUPDKEY : forall (ls : list (K * V)) f x y,
  x <> y -> (ADELKEY x (AFUPDKEY y f ls) = (AFUPDKEY y f (ADELKEY x ls))).
Proof.
  intros ls f x y hxy; unfold ADELKEY; induction ls as [|[a b] t IH]; cbn [AFUPDKEY]; [reflexivity|].
  destruct (decide (y = a)) as [<-|n]; cbn [filter fst].
  - rewrite (bool_decide_eq_true_2 (y <> x)) by congruence; cbn [AFUPDKEY].
    destruct (decide (y = y)); [reflexivity|tauto].
  - destruct (decide (a = x)) as [->|n'].
    + rewrite (bool_decide_eq_false_2 (x <> x)) by tauto; exact IH.
    + rewrite (bool_decide_eq_true_2 (a <> x)) by exact n'; cbn [AFUPDKEY].
      destruct (decide (y = a)); [congruence|]; rewrite IH; reflexivity.
Qed.

End Alookup.

Section Values.
Context {K V W : Type} `{EqDecision K}.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_MAP" *)
Theorem ALOOKUP_MAP : forall (f : V -> W) (al : list (K * V)),
  ALOOKUP (MAP (fun '(x, y) => (x, f y)) al) = OPTION_MAP f ∘ ALOOKUP al.
Proof.
  intros f al; apply functional_extensionality; intros k.
  induction al as [|[a b] t IH]; cbn; [reflexivity|]; destruct (decide (a = k)); auto.
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_MAP_2" *)
Theorem ALOOKUP_MAP_2 : forall (f : K -> V -> W) (al : list (K * V)) x,
  ALOOKUP (MAP (fun '(x, y) => (x, f x y)) al) x = OPTION_MAP (f x) (ALOOKUP al x).
Proof.
  intros f al x; induction al as [|[a b] t IH]; cbn; [reflexivity|].
  destruct (decide (a = x)) as [->|]; auto.
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "alist_to_fmap_MAP_values" *)
Theorem alist_to_fmap_MAP_values : forall (f : V -> W) (al : list (K * V)),
  alist_to_fmap (MAP (fun '(k, v) => (k, f v)) al) = o_f f (alist_to_fmap al).
Proof.
  intros f al; apply fmap_ext; intros k; rewrite FLOOKUP_alist_to_fmap, ALOOKUP_MAP.
  cbn; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_ZIP_MAP_SND" *)
Theorem ALOOKUP_ZIP_MAP_SND : forall {T} (l1 : list K) (l2 : list V) (k : T) (f : V -> W),
  (LENGTH l1 = LENGTH l2) ->
  (ALOOKUP (ZIP (l1, MAP f l2)) = OPTION_MAP f ∘ ALOOKUP (ZIP (l1, l2))).
Proof.
  intros T l1 l2 k f hl; apply functional_extensionality; intros q.
  rewrite !LENGTH_length in hl; apply N2Nat.inj_iff in hl; rewrite !Nat2N.id in hl.
  revert l2 hl; induction l1 as [|a t IH]; intros [|b l2] hl; cbn in *; try discriminate; [reflexivity|].
  destruct (decide (a = q)); [reflexivity|apply IH; congruence].
Qed.

End Values.
