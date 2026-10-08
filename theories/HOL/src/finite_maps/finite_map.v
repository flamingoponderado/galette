(** * HOL4 [finite_map]: finite maps ['a |-> 'b]

    HOL defines ['a |-> 'b] abstractly (a type of representations
    ['a -> 'b + one] closed under update) and characterises its operations
    by theorems.  Galette's carrier [fmap K V] is a lookup function together
    with a (proof-irrelevant) finiteness witness; two maps with the same
    lookup function are equal ([fmap_ext]).  [FLOOKUP] is the record field.

    Executable operations ([FEMPTY], [FUPDATE] [|+], [FUPDATE_LIST] [|++],
    [fdomsub] [\\], [FUNION] [⊌], [o_f], [f_o_f], [FMAP_MAP2]) compute on the
    lookup function and extract to OCaml closures; key comparisons use
    [EqDecision K].  Operations whose HOL argument is an arbitrary set
    ([DRESTRICT], [FDIFF], [FUN_FMAP]) and the set/predicate-valued ones
    ([FDOM], [FRANGE], [SUBMAP] [⊑], [FEVERY], [fmap_rel]) are not
    executable.  [FAPPLY f k] (HOL [f ' k]) is [THE (FLOOKUP f k)], i.e. [ARB]
    outside the domain, and needs [Inhabited V].

    HOL's characterising theorems are proved and tagged.

    Sets are [pred_set]'s ([A -> Prop] with HOL's operations and
    notations).  HOL [if x IN FDOM f] is [if decide (x IN FDOM f)]
    (computable, [FDOM_IN_dec]); [if x IN s] for an arbitrary set is
    [if classical_dec (x IN s)]. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.num.theories Require Import While.
Open Scope N_scope.

Lemma MEM_iff {A} `{EqDecision A} (x : A) l : is_true (MEM x l) <-> In x l.
Proof. exact (MEM_In x l). Qed.

(** ** The carrier *)

Record fmap (K V : Type) : Type := mk_fmap {
  FLOOKUP : K -> option V;
  FLOOKUP_finite : exists l : list K, forall k, FLOOKUP k <> None -> In k l
}.
Arguments mk_fmap {K V} _ _.
Arguments FLOOKUP {K V} _ _.
Arguments FLOOKUP_finite {K V} _.

Lemma fmap_ext {K V} (f g : fmap K V) :
  (forall k, FLOOKUP f k = FLOOKUP g k) -> f = g.
Proof.
  destruct f as [f Hf], g as [g Hg]; cbn; intros E.
  assert (f = g) as <- by (apply functional_extensionality; exact E).
  f_equal; apply proof_irrelevance.
Qed.

Lemma fmap_ext_iff {K V} (f g : fmap K V) :
  f = g <-> (forall k, FLOOKUP f k = FLOOKUP g k).
Proof. split; [intros ->; reflexivity|apply fmap_ext]. Qed.

Declare Scope fmap_scope.
Open Scope fmap_scope.

Section Defs.
Context {K V W : Type}.

Lemma FEMPTY_finite : exists l : list K, forall k, (fun _ : K => @None V) k <> None -> In k l.
Proof. exists []; intros k H; exfalso; apply H; reflexivity. Qed.

(** HOL [FEMPTY] ([FEMPTY_DEF] is stated over the representation). *)
Definition FEMPTY : fmap K V := mk_fmap (fun _ => None) FEMPTY_finite.

(** HOL [FDOM] ([FDOM_DEF] is stated over the representation). *)
Definition FDOM (f : fmap K V) : K -> Prop := fun k => FLOOKUP f k <> None.

#[global] Instance FDOM_dec (f : fmap K V) (k : K) : Decision (FDOM f k).
Proof.
  unfold_sets; unfold FDOM; destruct (FLOOKUP f k); [left; discriminate|right; tauto].
Defined.

#[global] Instance FDOM_IN_dec (f : fmap K V) (k : K) : Decision (k IN FDOM f) := FDOM_dec f k.

(** HOL [FAPPLY] ([f ' k]); [FAPPLY_DEF] is stated over the representation.
    Outside the domain HOL's value is unspecified; here it is [ARB]. *)
Definition FAPPLY `{Inhabited V} (f : fmap K V) (k : K) : V := THE (FLOOKUP f k).

Section Upd.
Context `{EqDecision K}.

Lemma FUPDATE_finite (f : fmap K V) (p : K * V) :
  exists l : list K, forall k,
    (fun a => if decide (fst p = a) then Some (snd p) else FLOOKUP f a) k <> None -> In k l.
Proof.
  destruct (FLOOKUP_finite f) as [l Hl]; exists (fst p :: l); intros k; cbn.
  destruct (decide (fst p = k)); [left; assumption|right; apply Hl; assumption].
Qed.

(** HOL [FUPDATE] ([f |+ (k,v)]); [FUPDATE_DEF] is stated over the
    representation. *)
Definition FUPDATE (f : fmap K V) (p : K * V) : fmap K V :=
  mk_fmap (fun a => if decide (fst p = a) then Some (snd p) else FLOOKUP f a)
    (FUPDATE_finite f p).

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_LIST" *)
Definition FUPDATE_LIST : fmap K V -> list (K * V) -> fmap K V := FOLDL FUPDATE.

Lemma fdomsub_finite (f : fmap K V) (k0 : K) :
  exists l : list K, forall k,
    (fun a => if decide (a = k0) then None else FLOOKUP f a) k <> None -> In k l.
Proof.
  destruct (FLOOKUP_finite f) as [l Hl]; exists l; intros k; cbn.
  destruct (decide (k = k0)); [tauto|apply Hl].
Qed.

(** HOL [fdomsub] ([fm \\ k]), defined in HOL as [DRESTRICT fm (COMPL {k})]
    (theorem [fmap_domsub] below). *)
Definition fdomsub (f : fmap K V) (k0 : K) : fmap K V :=
  mk_fmap (fun a => if decide (a = k0) then None else FLOOKUP f a) (fdomsub_finite f k0).

End Upd.

Lemma FUNION_finite (f g : fmap K V) :
  exists l : list K, forall k,
    (fun a => match FLOOKUP f a with Some v => Some v | None => FLOOKUP g a end) k <> None ->
    In k l.
Proof.
  destruct (FLOOKUP_finite f) as [l1 H1], (FLOOKUP_finite g) as [l2 H2].
  exists (l1 ++ l2); intros k; cbn; rewrite in_app_iff.
  destruct (FLOOKUP f k) eqn:E; intros H.
  - left; apply H1; rewrite E; discriminate.
  - right; apply H2; exact H.
Qed.

(** HOL [FUNION] (specified by [FUNION_DEF]). *)
Definition FUNION (f g : fmap K V) : fmap K V :=
  mk_fmap (fun a => match FLOOKUP f a with Some v => Some v | None => FLOOKUP g a end)
    (FUNION_finite f g).

Lemma DRESTRICT_finite (f : fmap K V) (r : K -> Prop) :
  exists l : list K, forall k,
    (fun a => if classical_dec (r a) then FLOOKUP f a else None) k <> None -> In k l.
Proof.
  destruct (FLOOKUP_finite f) as [l Hl]; exists l; intros k; cbn.
  destruct (classical_dec (r k)); [apply Hl|tauto].
Qed.

(** HOL [DRESTRICT] (specified by [DRESTRICT_DEF]); not executable. *)
Definition DRESTRICT (f : fmap K V) (r : K -> Prop) : fmap K V :=
  mk_fmap (fun a => if classical_dec (r a) then FLOOKUP f a else None) (DRESTRICT_finite f r).

(** HOL [FRANGE] ([FRANGE_DEF] below). *)
Definition FRANGE (f : fmap K V) : V -> Prop := fun v => exists k, FLOOKUP f k = Some v.

(** HOL [SUBMAP] ([SUBMAP_DEF] below). *)
Definition SUBMAP (f g : fmap K V) : Prop :=
  forall k v, FLOOKUP f k = Some v -> FLOOKUP g k = Some v.

(** HOL [FEVERY] ([FEVERY_DEF] below).  The predicate is a [Prop]. *)
Definition FEVERY (P : K * V -> Prop) (f : fmap K V) : Prop :=
  forall k v, FLOOKUP f k = Some v -> P (k, v).

Lemma o_f_finite (f : V -> W) (g : fmap K V) :
  exists l : list K, forall k, (fun a => OPTION_MAP f (FLOOKUP g a)) k <> None -> In k l.
Proof.
  destruct (FLOOKUP_finite g) as [l Hl]; exists l; intros k; cbn.
  destruct (FLOOKUP g k) eqn:E; cbn; intros H; [apply Hl; rewrite E; discriminate|tauto].
Qed.

(** HOL [o_f] (infix in HOL, prefix here; specified by [o_f_DEF]). *)
Definition o_f (f : V -> W) (g : fmap K V) : fmap K W :=
  mk_fmap (fun a => OPTION_MAP f (FLOOKUP g a)) (o_f_finite f g).

Lemma FMAP_MAP2_finite (f : K * V -> W) (m : fmap K V) :
  exists l : list K, forall k,
    (fun a => OPTION_MAP (fun v => f (a, v)) (FLOOKUP m a)) k <> None -> In k l.
Proof.
  destruct (FLOOKUP_finite m) as [l Hl]; exists l; intros k; cbn.
  destruct (FLOOKUP m k) eqn:E; cbn; intros H; [apply Hl; rewrite E; discriminate|tauto].
Qed.

(** HOL [FMAP_MAP2] ([FMAP_MAP2_def] below). *)
Definition FMAP_MAP2 (f : K * V -> W) (m : fmap K V) : fmap K W :=
  mk_fmap (fun a => OPTION_MAP (fun v => f (a, v)) (FLOOKUP m a)) (FMAP_MAP2_finite f m).

Lemma FUN_FMAP_finite (f : K -> V) (P : K -> Prop) :
  (exists l : list K, forall x, P x -> In x l) ->
  exists l : list K, forall k,
    (fun a => if classical_dec (P a) then Some (f a) else None) k <> None -> In k l.
Proof.
  intros [l Hl]; exists l; intros k; cbn.
  destruct (classical_dec (P k)); [intros _; apply Hl; assumption|tauto].
Qed.

(** HOL [FUN_FMAP] (specified by [FUN_FMAP_DEF] for finite [P]); not
    executable.  For an infinite [P] HOL leaves the value unspecified; here
    it is [FEMPTY]. *)
Definition FUN_FMAP (f : K -> V) (P : K -> Prop) : fmap K V :=
  match classical_dec (exists l : list K, forall x, P x -> In x l) with
  | left H => mk_fmap (fun a => if classical_dec (P a) then Some (f a) else None)
                (FUN_FMAP_finite f P H)
  | right _ => FEMPTY
  end.

(** HOL [fmap_rel] ([fmap_rel_def] below). *)
Definition fmap_rel (R : V -> W -> Prop) (f1 : fmap K V) (f2 : fmap K W) : Prop :=
  forall k, OPTREL R (FLOOKUP f1 k) (FLOOKUP f2 k).

End Defs.

Section Defs2.
Context {A B C : Type}.

Lemma f_o_f_finite (f : fmap B C) (g : fmap A B) :
  exists l : list A, forall k,
    (fun a => match FLOOKUP g a with Some b => FLOOKUP f b | None => None end) k <> None ->
    In k l.
Proof.
  destruct (FLOOKUP_finite g) as [l Hl]; exists l; intros k; cbn.
  destruct (FLOOKUP g k) eqn:E; intros H; [apply Hl; rewrite E; discriminate|tauto].
Qed.

(** HOL [f_o_f] (infix in HOL, prefix here; specified by [f_o_f_DEF]). *)
Definition f_o_f (f : fmap B C) (g : fmap A B) : fmap A C :=
  mk_fmap (fun a => match FLOOKUP g a with Some b => FLOOKUP f b | None => None end)
    (f_o_f_finite f g).

End Defs2.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDIFF_def" *)
Definition FDIFF {K V} (f1 : fmap K V) (s : K -> Prop) : fmap K V :=
  DRESTRICT f1 (COMPL s).

Arguments FEMPTY {K V}.

Notation "f ' k" := (FAPPLY f k) (at level 9, k at level 9) : fmap_scope.
Infix "|+" := FUPDATE (at level 45, left associativity) : fmap_scope.
Infix "|++" := FUPDATE_LIST (at level 50, left associativity) : fmap_scope.
Infix "\\" := fdomsub (at level 45, left associativity) : fmap_scope.
Infix "⊌" := FUNION (at level 50, left associativity) : fmap_scope.
Infix "⊑" := SUBMAP (at level 70, no associativity) : fmap_scope.

(** ** Computation rules for [FLOOKUP] *)

Section Lookup.
Context {K V W : Type}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FLOOKUP_EMPTY" *)
Theorem FLOOKUP_EMPTY : forall k : K, FLOOKUP (FEMPTY : fmap K V) k = NONE.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FLOOKUP_UPDATE" *)
Theorem FLOOKUP_UPDATE `{EqDecision K} : forall (fm : fmap K V) k1 v k2,
  FLOOKUP (fm |+ (k1, v)) k2 = if decide (k1 = k2) then SOME v else FLOOKUP fm k2.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FLOOKUP_FUNION" *)
Theorem FLOOKUP_FUNION : forall (f1 f2 : fmap K V) k,
  FLOOKUP (FUNION f1 f2) k =
  match FLOOKUP f1 k with NONE => FLOOKUP f2 k | SOME v => SOME v end.
Proof. intros; cbn; destruct (FLOOKUP f1 k); reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FLOOKUP_DRESTRICT" *)
Theorem FLOOKUP_DRESTRICT : forall (fm : fmap K V) s k,
  FLOOKUP (DRESTRICT fm s) k = if classical_dec (k IN s) then FLOOKUP fm k else NONE.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DOMSUB_FLOOKUP_THM" *)
Theorem DOMSUB_FLOOKUP_THM `{EqDecision K} : forall (fm : fmap K V) k1 k2,
  FLOOKUP (fm \\ k1) k2 = if decide (k1 = k2) then NONE else FLOOKUP fm k2.
Proof.
  intros; cbn; destruct (decide (k2 = k1)), (decide (k1 = k2)); congruence.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FLOOKUP_o_f" *)
Theorem FLOOKUP_o_f : forall (f : V -> W) (fm : fmap K V) k,
  FLOOKUP (o_f f fm) k = match FLOOKUP fm k with NONE => NONE | SOME v => SOME (f v) end.
Proof. intros; cbn; destruct (FLOOKUP fm k); reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FLOOKUP_FMAP_MAP2" *)
Theorem FLOOKUP_FMAP_MAP2 : forall (f : K * V -> W) m k,
  FLOOKUP (FMAP_MAP2 f m) k = OPTION_MAP (fun v => f (k, v)) (FLOOKUP m k).
Proof. reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FLOOKUP_FDIFF" 3494 *)
Theorem FLOOKUP_FDIFF : forall (fm : fmap K V) s k,
  FLOOKUP (FDIFF fm s) k = if classical_dec (k IN s) then NONE else FLOOKUP fm k.
Proof.
  intros; unfold FDIFF; cbn; do 2 destruct (classical_dec _); unfold_sets; tauto.
Qed.

Lemma FLOOKUP_f_o_f {A B C} (f : fmap B C) (g : fmap A B) k :
  FLOOKUP (f_o_f f g) k = match FLOOKUP g k with SOME b => FLOOKUP f b | NONE => NONE end.
Proof. reflexivity. Qed.

End Lookup.

(** Normalisation tactic used by the proofs below (Galette infrastructure). *)
Ltac fm_lookup :=
  repeat first
    [ rewrite FLOOKUP_UPDATE in *
    | rewrite FLOOKUP_FUNION in *
    | rewrite DOMSUB_FLOOKUP_THM in *
    | rewrite FLOOKUP_FDIFF in *
    | rewrite FLOOKUP_DRESTRICT in *
    | rewrite FLOOKUP_o_f in *
    | rewrite FLOOKUP_FMAP_MAP2 in *
    | rewrite FLOOKUP_f_o_f in *
    | rewrite FLOOKUP_EMPTY in * ].

Ltac fm_finish :=
  try congruence; try tauto;
  try solve [intuition (try discriminate; try congruence)];
  try solve [firstorder congruence].

Ltac fm_cases :=
  repeat (match goal with
  | |- context [decide ?P] => destruct (decide P)
  | H : context [decide ?P] |- _ => destruct (decide P)
  | |- context [classical_dec ?P] => destruct (classical_dec P)
  | H : context [classical_dec ?P] |- _ => destruct (classical_dec P)
  | |- context [match FLOOKUP ?f ?k with _ => _ end] =>
      let E := fresh "E" in destruct (FLOOKUP f k) eqn:E
  | H : context [match FLOOKUP ?f ?k with _ => _ end] |- _ =>
      let E := fresh "E" in destruct (FLOOKUP f k) eqn:E
  | H : context [FLOOKUP ?f ?k <> None] |- _ =>
      let E := fresh "E" in destruct (FLOOKUP f k) eqn:E
  | |- context [FLOOKUP ?f ?k <> None] =>
      let E := fresh "E" in destruct (FLOOKUP f k) eqn:E
  end; unfold_sets); subst; cbn in *; fm_finish.

Ltac fm_auto := unfold_sets; unfold FDOM, FAPPLY, FRANGE, SUBMAP, FEVERY in *; fm_lookup; unfold THE, option_map in *; fm_cases.

(** ** Basic theorems: [FEMPTY], [FUPDATE], [FAPPLY], [FDOM] *)

Section Basic.
Context {K V : Type} `{EqDecision K} `{Inhabited V}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FLOOKUP_DEF" *)
Theorem FLOOKUP_DEF : forall (f : fmap K V) x,
  FLOOKUP f x = if decide (x IN FDOM f) then SOME (f ' x) else NONE.
Proof.
  intros; unfold FAPPLY; destruct (decide (x IN FDOM f)) as [h|h]; unfold_sets; unfold FDOM in h;
    destruct (FLOOKUP f x); cbn; congruence || tauto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FAPPLY_FUPDATE" *)
Theorem FAPPLY_FUPDATE : forall (f : fmap K V) x y, FAPPLY (FUPDATE f (x, y)) x = y.
Proof. intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "NOT_EQ_FAPPLY" *)
Theorem NOT_EQ_FAPPLY : forall (f : fmap K V) a x y,
  ~ (a = x) -> FAPPLY (FUPDATE f (x, y)) a = FAPPLY f a.
Proof. intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_COMMUTES" *)
Theorem FUPDATE_COMMUTES : forall (f : fmap K V) a b c d,
  ~ (a = c) -> FUPDATE (FUPDATE f (a, b)) (c, d) = FUPDATE (FUPDATE f (c, d)) (a, b).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_EQ" *)
Theorem FUPDATE_EQ : forall (f : fmap K V) a b c,
  FUPDATE (FUPDATE f (a, b)) (a, c) = FUPDATE f (a, c).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDOM_FEMPTY" *)
Theorem FDOM_FEMPTY : FDOM (FEMPTY : fmap K V) = {}.
Proof. apply functional_extensionality; intros; apply propositional_extensionality; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDOM_FUPDATE" *)
Theorem FDOM_FUPDATE : forall (f : fmap K V) a b,
  FDOM (FUPDATE f (a, b)) = a INSERT FDOM f.
Proof.
  intros; apply functional_extensionality; intros; apply propositional_extensionality; fm_auto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FAPPLY_FUPDATE_THM" *)
Theorem FAPPLY_FUPDATE_THM : forall (f : fmap K V) a b x,
  FAPPLY (FUPDATE f (a, b)) x = if decide (x = a) then b else FAPPLY f x.
Proof. intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "NOT_EQ_FEMPTY_FUPDATE" *)
Theorem NOT_EQ_FEMPTY_FUPDATE : forall (f : fmap K V) a b, ~ (FEMPTY = FUPDATE f (a, b)).
Proof.
  intros f a b E; assert (h := f_equal (fun g => FLOOKUP g a) E); cbn in h; fm_cases.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDOM_EQ_FDOM_FUPDATE" *)
Theorem FDOM_EQ_FDOM_FUPDATE : forall (f : fmap K V) x,
  x IN FDOM f -> forall y, FDOM (FUPDATE f (x, y)) = FDOM f.
Proof.
  intros; rewrite FDOM_FUPDATE; apply ABSORPTION_RWT; assumption.
Qed.

End Basic.

(** Domain finiteness (HOL [FDOM_FINITE] needs pred_set's [FINITE]). *)
Lemma FDOM_finite {K V} (f : fmap K V) : exists l : list K, forall k, k IN FDOM f -> In k l.
Proof. exact (FLOOKUP_finite f). Qed.

(** ** Induction *)

Section Induct.
Context {K V : Type} `{EqDecision K}.

Lemma fmap_FEMPTY_iff (f : fmap K V) : f = FEMPTY <-> forall k, FLOOKUP f k = None.
Proof. rewrite fmap_ext_iff; reflexivity. Qed.

Lemma fmap_decomp (f : fmap K V) k v :
  FLOOKUP f k = Some v -> f = FUPDATE (f \\ k) (k, v).
Proof. intros E; apply fmap_ext; intros a; fm_auto. Qed.

Lemma fmap_list_induct (P : fmap K V -> Prop) :
  P FEMPTY ->
  (forall f, P f -> forall x y, ~ x IN FDOM f -> P (FUPDATE f (x, y))) ->
  forall l f, (forall k, k IN FDOM f -> In k l) -> P f.
Proof.
  intros H0 HS l; induction l as [|a l IH]; intros f Hf.
  - replace f with (@FEMPTY K V); [exact H0|].
    apply fmap_ext; intros k; cbn; destruct (FLOOKUP f k) eqn:E; [|reflexivity].
    destruct (Hf k); unfold_sets; unfold FDOM; congruence.
  - destruct (FLOOKUP f a) as [v|] eqn:Ea.
    + rewrite (fmap_decomp f a v Ea); apply HS.
      * apply IH; intros k Hk; unfold_sets; unfold FDOM in Hk; fm_lookup; fm_cases;
        destruct (Hf k); unfold_sets; unfold FDOM; congruence.
      * fm_auto.
    + apply IH; intros k Hk; destruct (Hf k Hk); [subst; unfold_sets; unfold FDOM in Hk; congruence|auto].
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_INDUCT" *)
Theorem fmap_INDUCT : forall P : fmap K V -> Prop,
  P FEMPTY /\ (forall f, P f -> forall x y, ~ x IN FDOM f -> P (FUPDATE f (x, y))) ->
  forall f, P f.
Proof.
  intros P [H0 HS] f; destruct (FLOOKUP_finite f) as [l Hl].
  exact (fmap_list_induct P H0 HS l f Hl).
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_SIMPLE_INDUCT" *)
Theorem fmap_SIMPLE_INDUCT : forall P : fmap K V -> Prop,
  P FEMPTY /\ (forall f, P f -> forall x y, P (FUPDATE f (x, y))) -> forall f, P f.
Proof. intros P [H0 HS]; apply fmap_INDUCT; split; auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_CASES" *)
Theorem fmap_CASES : forall f : fmap K V, f = FEMPTY \/ exists g x y, f = FUPDATE g (x, y).
Proof.
  apply fmap_INDUCT; split; [left; reflexivity|]; intros f _ x y _; right; eauto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_cases_NOTIN" *)
Theorem fmap_cases_NOTIN : forall fm : fmap K V,
  fm = FEMPTY \/ exists k v fm0, ~ k IN FDOM fm0 /\ fm = FUPDATE fm0 (k, v).
Proof.
  apply fmap_INDUCT; split; [left; reflexivity|]; intros f _ x y Hx; right; eauto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FM_PULL_APART" *)
Theorem FM_PULL_APART : forall (fm : fmap K V) k,
  k IN FDOM fm -> exists fm0 v, fm = FUPDATE fm0 (k, v) /\ ~ k IN FDOM fm0.
Proof.
  intros fm k Hk; unfold_sets; unfold FDOM in Hk; destruct (FLOOKUP fm k) as [v|] eqn:E; [|tauto].
  exists (fm \\ k), v; split; [apply fmap_decomp; exact E|fm_auto].
Qed.

End Induct.

(** ** Equality *)

Section Eq.
Context {K V : Type} `{Inhabited V}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDOM_EQ_EMPTY" *)
Theorem FDOM_EQ_EMPTY : forall f : fmap K V, (FDOM f = {}) <-> (f = FEMPTY).
Proof.
  intros f; rewrite fmap_ext_iff; split.
  - intros E k; cbn; assert (h := f_equal (fun s => s k) E); cbn in h; unfold_sets; unfold FDOM in h.
    destruct (FLOOKUP f k); [|reflexivity]; exfalso; rewrite <- h; discriminate.
  - intros E; apply functional_extensionality; intros k; apply propositional_extensionality.
    unfold_sets; unfold FDOM; rewrite E; cbn; tauto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDOM_F_FEMPTY1" *)
Theorem FDOM_F_FEMPTY1 : forall f : fmap K V, (forall a, ~ a IN FDOM f) <-> (f = FEMPTY).
Proof.
  intros f; rewrite fmap_ext_iff; unfold_sets; unfold FDOM; cbn; split; intros E a; specialize (E a).
  - destruct (FLOOKUP f a); [exfalso; apply E; discriminate|reflexivity].
  - rewrite E; tauto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "NOT_FDOM_FAPPLY_FEMPTY" *)
Theorem NOT_FDOM_FAPPLY_FEMPTY : forall (f : fmap K V) x,
  ~ x IN FDOM f -> FAPPLY f x = FAPPLY FEMPTY x.
Proof. intros; fm_auto. Qed.

Lemma FLOOKUP_FAPPLY (f : fmap K V) x : x IN FDOM f -> FLOOKUP f x = SOME (f ' x).
Proof. intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_EQ_THM" *)
Theorem fmap_EQ_THM : forall f g : fmap K V,
  (FDOM f = FDOM g) /\ (forall x, x IN FDOM f -> FAPPLY f x = FAPPLY g x) <-> (f = g).
Proof.
  intros f g; split; [|intros ->; split; auto].
  intros [Hd Ha]; apply fmap_ext; intros k.
  assert (hk := f_equal (fun s => s k) Hd); cbn in hk; unfold_sets; unfold FDOM in hk.
  specialize (Ha k); unfold FDOM, FAPPLY in Ha.
  destruct (FLOOKUP f k) eqn:E1, (FLOOKUP g k) eqn:E2; cbn in *.
  - f_equal; apply Ha; discriminate.
  - exfalso; assert (h : Some v <> None) by discriminate; rewrite hk in h; apply h; reflexivity.
  - exfalso; assert (h : Some v <> None) by discriminate; rewrite <- hk in h; apply h; reflexivity.
  - reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_EQ" *)
Theorem fmap_EQ : forall f g : fmap K V,
  (FDOM f = FDOM g) /\ (FAPPLY f = FAPPLY g) <-> (f = g).
Proof.
  intros f g; rewrite <- fmap_EQ_THM; split; intros [Hd Ha]; split; auto.
  - intros x _; rewrite Ha; reflexivity.
  - apply functional_extensionality; intros x.
    destruct (decide (x IN FDOM f)) as [h|h]; [auto|].
    assert (h' : ~ FDOM g x) by (rewrite <- Hd; exact h).
    rewrite (NOT_FDOM_FAPPLY_FEMPTY f x h), (NOT_FDOM_FAPPLY_FEMPTY g x h'); reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_EXT" *)
Theorem fmap_EXT : forall f g : fmap K V,
  (f = g) <-> (FDOM f = FDOM g) /\ (forall x, x IN FDOM f -> FAPPLY f x = FAPPLY g x).
Proof. intros; rewrite fmap_EQ_THM; reflexivity. Qed.

End Eq.

Section Eq2.
Context {K V : Type}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FLOOKUP_EXT" *)
Theorem FLOOKUP_EXT : forall f1 f2 : fmap K V, (f1 = f2) <-> (FLOOKUP f1 = FLOOKUP f2).
Proof.
  intros; rewrite fmap_ext_iff; split; [apply functional_extensionality|].
  intros E k; rewrite E; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_eq_flookup" *)
Theorem fmap_eq_flookup : forall f1 f2 : fmap K V,
  (f1 = f2) <-> (forall x, FLOOKUP f1 x = FLOOKUP f2 x).
Proof. intros; apply fmap_ext_iff. Qed.

End Eq2.

Ltac set_ext := apply functional_extensionality; intro; apply propositional_extensionality.

(** ** Submaps *)

Section Submap.
Context {K V : Type}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_DEF" *)
Theorem SUBMAP_DEF `{Inhabited V} : forall f g : fmap K V,
  SUBMAP f g <-> forall x, x IN FDOM f -> x IN FDOM g /\ FAPPLY f x = FAPPLY g x.
Proof.
  intros f g; split.
  - intros Hs x Hx; unfold_sets; unfold FDOM in Hx; destruct (FLOOKUP f x) eqn:E; [|tauto].
    pose proof (Hs _ _ E); fm_auto.
  - intros Hs x v E; destruct (Hs x) as [h1 h2]; [fm_auto|]; fm_auto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_FEMPTY" *)
Theorem SUBMAP_FEMPTY : forall f : fmap K V, FEMPTY ⊑ f.
Proof. intros f k v E; discriminate. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_REFL" *)
Theorem SUBMAP_REFL : forall f : fmap K V, f ⊑ f.
Proof. intros f k v E; exact E. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_ANTISYM" *)
Theorem SUBMAP_ANTISYM : forall f g : fmap K V, (f ⊑ g /\ g ⊑ f) <-> (f = g).
Proof.
  intros f g; split; [|intros ->; split; apply SUBMAP_REFL].
  intros [h1 h2]; apply fmap_ext; intros k.
  destruct (FLOOKUP f k) eqn:E1, (FLOOKUP g k) eqn:E2; auto.
  - rewrite (h1 _ _ E1) in E2; exact E2.
  - rewrite (h1 _ _ E1) in E2; discriminate.
  - rewrite (h2 _ _ E2) in E1; discriminate.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_TRANS" *)
Theorem SUBMAP_TRANS : forall f g h : fmap K V, f ⊑ g /\ g ⊑ h -> f ⊑ h.
Proof. intros f g h [h1 h2] k v E; auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FLOOKUP_SUBMAP" *)
Theorem FLOOKUP_SUBMAP : forall (f g : fmap K V) k v,
  f ⊑ g /\ FLOOKUP f k = SOME v -> FLOOKUP g k = SOME v.
Proof. intros f g k v [h E]; auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_FLOOKUP_EQN" *)
Theorem SUBMAP_FLOOKUP_EQN : forall f g : fmap K V,
  f ⊑ g <-> forall x y, FLOOKUP f x = SOME y -> FLOOKUP g x = SOME y.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "EQ_FDOM_SUBMAP" *)
Theorem EQ_FDOM_SUBMAP : forall f g : fmap K V, (f = g) <-> f ⊑ g /\ FDOM f = FDOM g.
Proof.
  intros f g; split; [intros ->; split; [apply SUBMAP_REFL|reflexivity]|].
  intros [h1 h2]; apply fmap_ext; intros k.
  assert (hk := f_equal (fun s => s k) h2); cbn in hk; unfold_sets; unfold FDOM in hk.
  destruct (FLOOKUP f k) eqn:E1; [symmetry; apply h1; exact E1|].
  destruct (FLOOKUP g k) eqn:E2; [|reflexivity].
  exfalso; assert (h : Some v <> None) by discriminate; rewrite <- hk in h; apply h; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_FDOM_SUBSET" *)
Theorem SUBMAP_FDOM_SUBSET : forall f1 f2 : fmap K V,
  f1 ⊑ f2 -> FDOM f1 SUBSET FDOM f2.
Proof.
  intros f1 f2 h y; unfold_sets; unfold FDOM; destruct (FLOOKUP f1 y) eqn:E; [|tauto].
  rewrite (h _ _ E); discriminate.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FEMPTY_SUBMAP" *)
Theorem FEMPTY_SUBMAP : forall h : fmap K V, h ⊑ FEMPTY <-> (h = FEMPTY).
Proof.
  intros h; split; [|intros ->; apply SUBMAP_REFL].
  intros Hs; apply fmap_ext; intros k; cbn; destruct (FLOOKUP h k) eqn:E; auto.
  apply Hs in E; discriminate.
Qed.

Context `{EqDecision K}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_FUPDATE_FLOOKUP" *)
Theorem SUBMAP_FUPDATE_FLOOKUP : forall (f : fmap K V) x y,
  f ⊑ (f |+ (x, y)) <-> (FLOOKUP f x = NONE) \/ (FLOOKUP f x = SOME y).
Proof.
  intros f x y; split.
  - intros h; destruct (FLOOKUP f x) eqn:E; auto; right; rewrite <- E.
    specialize (h _ _ E); fm_auto.
  - intros h k v E; fm_auto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_FUPDATE_EXTENDED" *)
Theorem SUBMAP_FUPDATE_EXTENDED : forall (k : K) (f : fmap K V) v,
  ~ k IN FDOM f -> f ⊑ f |+ (k, v).
Proof. intros k f v h; apply SUBMAP_FUPDATE_FLOOKUP; left; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_FUPDATE_EQN" *)
Theorem SUBMAP_FUPDATE_EQN `{Inhabited V} : forall (f : fmap K V) x y,
  f ⊑ f |+ (x, y) <-> ~ x IN FDOM f \/ (FAPPLY f x = y) /\ x IN FDOM f.
Proof.
  intros f x y; rewrite SUBMAP_FUPDATE_FLOOKUP; fm_auto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_mono_FUPDATE" *)
Theorem SUBMAP_mono_FUPDATE : forall (f g : fmap K V) x y,
  f \\ x ⊑ g \\ x -> f |+ (x, y) ⊑ g |+ (x, y).
Proof. intros f g x y h k v E; specialize (h k v); fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_DOMSUB_gen" *)
Theorem SUBMAP_DOMSUB_gen : forall (f g : fmap K V) k, f \\ k ⊑ g <-> f \\ k ⊑ g \\ k.
Proof. intros f g k; split; intros h a v E; specialize (h a v); fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DOMSUB_SUBMAP" *)
Theorem DOMSUB_SUBMAP : forall (f g : fmap K V) x, f ⊑ g /\ ~ x IN FDOM f -> f ⊑ g \\ x.
Proof. intros f g x [h Hx] a v E; specialize (h a v); fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_DOMSUB" *)
Theorem SUBMAP_DOMSUB : forall (f : fmap K V) k, (f \\ k) ⊑ f.
Proof. intros f k a v E; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_FUPDATE" *)
Theorem SUBMAP_FUPDATE `{Inhabited V} : forall (f g : fmap K V) x y,
  (f |+ (x, y)) ⊑ g <-> x IN FDOM g /\ FAPPLY g x = y /\ (f \\ x) ⊑ (g \\ x).
Proof.
  intros f g x y; split.
  - intros h; pose proof (h x y) as hx; fm_lookup; fm_cases.
    specialize (hx eq_refl); split; [|split]; [fm_auto|fm_auto|].
    intros a v E; specialize (h a v); fm_auto.
  - intros (h1 & h2 & h3) a v E; specialize (h3 a v); fm_auto.
Qed.

End Submap.

(** ** Domain restriction *)

Section Drestrict.
Context {K V : Type}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DRESTRICT_DEF" *)
Theorem DRESTRICT_DEF `{Inhabited V} : forall (f : fmap K V) r,
  (FDOM (DRESTRICT f r) = FDOM f INTER r) /\
  (forall x, FAPPLY (DRESTRICT f r) x =
             if classical_dec (x IN FDOM f INTER r) then FAPPLY f x else FAPPLY FEMPTY x).
Proof. intros; split; [set_ext|intros]; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DRESTRICT_FEMPTY" *)
Theorem DRESTRICT_FEMPTY : forall r, DRESTRICT (FEMPTY : fmap K V) r = FEMPTY.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDOM_DRESTRICT" *)
Theorem FDOM_DRESTRICT : forall (f : fmap K V) r (x : K),
  FDOM (DRESTRICT f r) = FDOM f INTER r.
Proof. intros; set_ext; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DRESTRICT_SUBMAP" *)
Theorem DRESTRICT_SUBMAP : forall (f : fmap K V) r, (DRESTRICT f r) ⊑ f.
Proof. intros f r k v E; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_DRESTRICT" *)
Theorem SUBMAP_DRESTRICT : forall (f : fmap K V) P, DRESTRICT f P ⊑ f.
Proof. exact DRESTRICT_SUBMAP. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DRESTRICT_DRESTRICT" *)
Theorem DRESTRICT_DRESTRICT : forall (f : fmap K V) P Q,
  DRESTRICT (DRESTRICT f P) Q = DRESTRICT f (P INTER Q).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DRESTRICT_IS_FEMPTY" *)
Theorem DRESTRICT_IS_FEMPTY : forall f : fmap K V, DRESTRICT f {} = FEMPTY.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DRESTRICT_UNIV" *)
Theorem DRESTRICT_UNIV : forall f : fmap K V, DRESTRICT f UNIV = f.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DRESTRICT_EQ_FEMPTY" *)
Theorem DRESTRICT_EQ_FEMPTY : forall (m : fmap K V) s,
  DISJOINT s (FDOM m) <-> DRESTRICT m s = FEMPTY.
Proof.
  intros m s; rewrite DISJOINT_iff, fmap_ext_iff; split; intros h y; specialize (h y); fm_auto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_DRESTRICT_MONOTONE" *)
Theorem SUBMAP_DRESTRICT_MONOTONE : forall (f1 f2 : fmap K V) s1 s2,
  f1 ⊑ f2 /\ s1 SUBSET s2 -> DRESTRICT f1 s1 ⊑ DRESTRICT f2 s2.
Proof. intros f1 f2 s1 s2 [h1 h2] k v E; specialize (h1 k v); specialize (h2 k); fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DRESTRICT_SUBMAP_gen" *)
Theorem DRESTRICT_SUBMAP_gen : forall (f g : fmap K V) P, f ⊑ g -> DRESTRICT f P ⊑ g.
Proof. intros f g P h k v E; specialize (h k v); fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DRESTRICT_SUBSET_SUBMAP" *)
Theorem DRESTRICT_SUBSET_SUBMAP : forall s1 s2 (f : fmap K V),
  s1 SUBSET s2 -> DRESTRICT f s1 ⊑ DRESTRICT f s2.
Proof. intros s1 s2 f h k v E; specialize (h k); fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DRESTRICT_FDOM" *)
Theorem DRESTRICT_FDOM : forall f : fmap K V, DRESTRICT f (FDOM f) = f.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DRESTRICT_IDEMPOT" *)
Theorem DRESTRICT_IDEMPOT : forall (s : fmap K V) vs,
  DRESTRICT (DRESTRICT s vs) vs = DRESTRICT s vs.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DRESTRICT_FUNION_SAME" *)
Theorem DRESTRICT_FUNION_SAME : forall (fm : fmap K V) s, FUNION (DRESTRICT fm s) fm = fm.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DRESTRICT_FUNION" *)
Theorem DRESTRICT_FUNION : forall (h : fmap K V) s1 s2,
  FUNION (DRESTRICT h s1) (DRESTRICT h s2) = DRESTRICT h (s1 UNION s2).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DRESTRICTED_FUNION" *)
Theorem DRESTRICTED_FUNION : forall (f1 f2 : fmap K V) s,
  DRESTRICT (FUNION f1 f2) s =
  FUNION (DRESTRICT f1 s) (DRESTRICT f2 (s DIFF FDOM f1)).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

Context `{EqDecision K}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DRESTRICT_FUPDATE" *)
Theorem DRESTRICT_FUPDATE : forall (f : fmap K V) r x y,
  DRESTRICT (FUPDATE f (x, y)) r =
  if classical_dec (x IN r) then FUPDATE (DRESTRICT f r) (x, y) else DRESTRICT f r.
Proof.
  intros; destruct (classical_dec (x IN r)); apply fmap_ext; intros; fm_auto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "STRONG_DRESTRICT_FUPDATE" *)
Theorem STRONG_DRESTRICT_FUPDATE : forall (f : fmap K V) r x y,
  x IN r -> DRESTRICT (FUPDATE f (x, y)) r = FUPDATE (DRESTRICT f (r DELETE x)) (x, y).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "NOT_FDOM_DRESTRICT" *)
Theorem NOT_FDOM_DRESTRICT : forall (f : fmap K V) x,
  ~ x IN FDOM f -> DRESTRICT f (COMPL (x INSERT {})) = f.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_DRESTRICT" *)
Theorem FUPDATE_DRESTRICT : forall (f : fmap K V) x y,
  FUPDATE f (x, y) = FUPDATE (DRESTRICT f (COMPL (x INSERT {}))) (x, y).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

End Drestrict.

(** ** Union *)

Section Funion.
Context {K V : Type}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUNION_DEF" *)
Theorem FUNION_DEF `{Inhabited V} : forall f g : fmap K V,
  (FDOM (FUNION f g) = FDOM f UNION FDOM g) /\
  (forall x, FAPPLY (FUNION f g) x = if decide (x IN FDOM f) then FAPPLY f x else FAPPLY g x).
Proof. intros; split; [set_ext|intros]; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDOM_FUNION" *)
Theorem FDOM_FUNION : forall f g : fmap K V,
  FDOM (FUNION f g) = FDOM f UNION FDOM g.
Proof. intros; set_ext; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUNION_FEMPTY_1" *)
Theorem FUNION_FEMPTY_1 : forall g : fmap K V, FUNION FEMPTY g = g.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUNION_FEMPTY_2" *)
Theorem FUNION_FEMPTY_2 : forall f : fmap K V, FUNION f FEMPTY = f.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUNION_IDEMPOT" *)
Theorem FUNION_IDEMPOT : forall fm : fmap K V, FUNION fm fm = fm.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUNION_ASSOC" *)
Theorem FUNION_ASSOC : forall f g h : fmap K V,
  (FUNION f (FUNION g h)) = (FUNION (FUNION f g) h).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUNION_COMM" *)
Theorem FUNION_COMM : forall f g : fmap K V,
  DISJOINT (FDOM f) (FDOM g) -> (FUNION f g) = (FUNION g f).
Proof. intros f g h; rewrite DISJOINT_iff in h; apply fmap_ext; intros k; specialize (h k); fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUNION_EQ_FEMPTY" *)
Theorem FUNION_EQ_FEMPTY : forall h1 h2 : fmap K V,
  (FUNION h1 h2 = FEMPTY) <-> ((h1 = FEMPTY) /\ (h2 = FEMPTY)).
Proof.
  intros; rewrite !fmap_ext_iff; split; [intros h; split; intros k; specialize (h k)|
    intros [a b] k; specialize (a k); specialize (b k)]; fm_auto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_FUNION" *)
Theorem SUBMAP_FUNION : forall f1 f2 f3 : fmap K V,
  f1 ⊑ f2 \/ (DISJOINT (FDOM f1) (FDOM f2) /\ f1 ⊑ f3) -> f1 ⊑ FUNION f2 f3.
Proof.
  intros f1 f2 f3 [h|[hd h]] k v E; specialize (h k v E).
  - fm_auto.
  - rewrite DISJOINT_iff in hd; specialize (hd k); fm_auto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_FUNION_ID" *)
Theorem SUBMAP_FUNION_ID :
  (forall f1 f2 : fmap K V, f1 ⊑ FUNION f1 f2) /\
  (forall f1 f2 : fmap K V, DISJOINT (FDOM f1) (FDOM f2) -> f2 ⊑ (FUNION f1 f2)).
Proof.
  split; intros; apply SUBMAP_FUNION; [left; apply SUBMAP_REFL|right].
  split; [apply DISJOINT_SYM, H|apply SUBMAP_REFL].
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_FUNION_ABSORPTION" *)
Theorem SUBMAP_FUNION_ABSORPTION : forall f g : fmap K V, f ⊑ g <-> (FUNION f g = g).
Proof.
  intros f g; rewrite fmap_ext_iff; split.
  - intros h k; pose proof (h k); fm_auto.
  - intros h k v E; specialize (h k); fm_auto.
Qed.

Context `{EqDecision K}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUNION_FUPDATE_1" *)
Theorem FUNION_FUPDATE_1 : forall (f g : fmap K V) x y,
  FUNION (FUPDATE f (x, y)) g = FUPDATE (FUNION f g) (x, y).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUNION_FUPDATE_2" *)
Theorem FUNION_FUPDATE_2 : forall (f g : fmap K V) x y,
  FUNION f (FUPDATE g (x, y)) =
  if decide (x IN FDOM f) then FUNION f g else FUPDATE (FUNION f g) (x, y).
Proof.
  intros; destruct (decide (x IN FDOM f)) as [h|h]; apply fmap_ext; intros; fm_auto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DOMSUB_FUNION" *)
Theorem DOMSUB_FUNION : forall (f g : fmap K V) k, (FUNION f g) \\ k = FUNION (f \\ k) (g \\ k).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_EQ_FUNION" *)
Theorem FUPDATE_EQ_FUNION : forall (fm : fmap K V) kv, fm |+ kv = FUNION (FEMPTY |+ kv) fm.
Proof. intros fm [k v]; apply fmap_ext; intros; fm_auto. Qed.

End Funion.

(** ** [FEVERY] *)

Section Fevery.
Context {K V : Type}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FEVERY_DEF" *)
Theorem FEVERY_DEF `{Inhabited V} : forall P (f : fmap K V),
  FEVERY P f <-> forall x, x IN FDOM f -> P (x, FAPPLY f x).
Proof.
  intros P f; split.
  - intros h x Hx; unfold_sets; unfold FDOM in Hx; destruct (FLOOKUP f x) eqn:E; [|tauto].
    unfold FAPPLY; rewrite E; apply h; exact E.
  - intros h x v E; specialize (h x); unfold_sets; unfold FDOM, FAPPLY in h; cbv beta in h; rewrite E in h.
    apply h; discriminate.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FEVERY_FEMPTY" *)
Theorem FEVERY_FEMPTY : forall P : K * V -> Prop, FEVERY P FEMPTY.
Proof. intros P k v E; discriminate. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FEVERY_FLOOKUP" *)
Theorem FEVERY_FLOOKUP : forall P (f : fmap K V) k v,
  FEVERY P f /\ (FLOOKUP f k = SOME v) -> P (k, v).
Proof. intros P f k v [h E]; exact (h k v E). Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FEVERY_ALL_FLOOKUP" *)
Theorem FEVERY_ALL_FLOOKUP : forall P (f : fmap K V),
  FEVERY P f <-> forall k v, (FLOOKUP f k = SOME v) -> P (k, v).
Proof. reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FEVERY_SUBMAP" *)
Theorem FEVERY_SUBMAP : forall P (fm fm0 : fmap K V), FEVERY P fm /\ fm0 ⊑ fm -> FEVERY P fm0.
Proof. intros P fm fm0 [h1 h2] k v E; apply h1, h2, E. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fevery_funion" *)
Theorem fevery_funion : forall P (m1 m2 : fmap K V),
  FEVERY P m1 /\ FEVERY P m2 -> FEVERY P (FUNION m1 m2).
Proof. intros P m1 m2 [h1 h2] k v E; specialize (h1 k); specialize (h2 k); fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DISJOINT_FEVERY_FUNION" *)
Theorem DISJOINT_FEVERY_FUNION : forall (m1 m2 : fmap K V) P,
  DISJOINT (FDOM m1) (FDOM m2) ->
  (FEVERY P (FUNION m1 m2) <-> FEVERY P m1 /\ FEVERY P m2).
Proof.
  intros m1 m2 P hd; rewrite DISJOINT_iff in hd; split; [|apply fevery_funion].
  intros h; split; intros k v E; specialize (h k v); specialize (hd k); fm_auto.
Qed.

Context `{EqDecision K}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FEVERY_FUPDATE" *)
Theorem FEVERY_FUPDATE : forall P (f : fmap K V) x y,
  FEVERY P (FUPDATE f (x, y)) <-> P (x, y) /\ FEVERY P (DRESTRICT f (COMPL (x INSERT {}))).
Proof.
  intros P f x y; split.
  - intros h; split; [apply h; fm_auto|intros k v E; apply h; fm_auto].
  - intros [h1 h2] k v E; specialize (h2 k v); fm_auto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FEVERY_STRENGTHEN_THM" *)
Theorem FEVERY_STRENGTHEN_THM : forall P (f : fmap K V) x y,
  FEVERY P FEMPTY /\ ((FEVERY P f /\ P (x, y)) -> FEVERY P (f |+ (x, y))).
Proof.
  intros; split; [apply FEVERY_FEMPTY|intros [h1 h2] k v E; specialize (h1 k v); fm_auto].
Qed.

End Fevery.

(** ** [o_f] and [f_o_f] *)

Section Of.
Context {A B C : Type}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "o_f_DEF" *)
Theorem o_f_DEF `{Inhabited B} `{Inhabited C} : forall (f : B -> C) (g : fmap A B),
  (FDOM (o_f f g) = FDOM g) /\
  (forall x, x IN FDOM (o_f f g) -> FAPPLY (o_f f g) x = f (FAPPLY g x)).
Proof. intros; split; [set_ext|intros]; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "o_f_FDOM" *)
Theorem o_f_FDOM : forall (f : B -> C) (g : fmap A B), FDOM g = FDOM (o_f f g).
Proof. intros; set_ext; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDOM_o_f" *)
Theorem FDOM_o_f : forall (f : B -> C) (g : fmap A B), FDOM (o_f f g) = FDOM g.
Proof. intros; symmetry; apply o_f_FDOM. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "o_f_FAPPLY" *)
Theorem o_f_FAPPLY `{Inhabited B} `{Inhabited C} : forall (f : B -> C) (g : fmap A B) x,
  x IN FDOM g -> FAPPLY (o_f f g) x = f (FAPPLY g x).
Proof. intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "o_f_FEMPTY" *)
Theorem o_f_FEMPTY : forall f : B -> C, o_f f (FEMPTY : fmap A B) = FEMPTY.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "o_f_id" *)
Theorem o_f_id : forall m : fmap A B, o_f (fun x => x) m = m.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FEVERY_o_f" *)
Theorem FEVERY_o_f : forall (m : fmap A B) P (f : B -> C),
  FEVERY P (o_f f m) <-> FEVERY (fun x => P (FST x, f (SND x))) m.
Proof.
  intros m P f; split; intros h k v E.
  - apply (h k (f v)); fm_auto.
  - rewrite FLOOKUP_o_f in E; destruct (FLOOKUP m k) eqn:E'; [|discriminate].
    injection E as <-; exact (h k b E').
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "o_f_o_f" *)
Theorem o_f_o_f : forall {D} (f : C -> D) (g : B -> C) (h : fmap A B),
  (o_f f (o_f g h)) = o_f (f ∘ g) h.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "o_f_FUNION" *)
Theorem o_f_FUNION : forall (f : B -> C) (f1 f2 : fmap A B),
  o_f f (FUNION f1 f2) = FUNION (o_f f f1) (o_f f f2).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

Context `{EqDecision A}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "o_f_DOMSUB" *)
Theorem o_f_DOMSUB : forall (g : B -> C) (fm : fmap A B) k, (o_f g fm) \\ k = o_f g (fm \\ k).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "o_f_FUPDATE" *)
Theorem o_f_FUPDATE : forall (f : B -> C) (fm : fmap A B) k v,
  o_f f (fm |+ (k, v)) = (o_f f fm) |+ (k, f v).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

End Of.

Section Fof.
Context {A B C : Type}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "f_o_f_DEF" *)
Theorem f_o_f_DEF `{Inhabited B} `{Inhabited C} : forall (f : fmap B C) (g : fmap A B),
  (FDOM (f_o_f f g) = FDOM g INTER (fun x => FAPPLY g x IN FDOM f)) /\
  (forall x, x IN FDOM (f_o_f f g) -> FAPPLY (f_o_f f g) x = FAPPLY f (FAPPLY g x)).
Proof. intros; split; [set_ext|intros]; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "f_o_f_FEMPTY_1" *)
Theorem f_o_f_FEMPTY_1 : forall f : fmap A B, f_o_f (FEMPTY : fmap B C) f = FEMPTY.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "f_o_f_FEMPTY_2" *)
Theorem f_o_f_FEMPTY_2 : forall f : fmap B C, f_o_f f (FEMPTY : fmap A B) = FEMPTY.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

End Fof.

(** ** Range *)

Section Frange.
Context {K V : Type}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FRANGE_DEF" *)
Theorem FRANGE_DEF `{Inhabited V} : forall f : fmap K V,
  FRANGE f = (fun y => exists x, x IN FDOM f /\ FAPPLY f x = y).
Proof.
  intros f; set_ext; split.
  - intros [k E]; exists k; fm_auto.
  - intros [k [h1 h2]]; exists k; fm_auto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "IN_FRANGE" *)
Theorem IN_FRANGE `{Inhabited V} : forall (f : fmap K V) v,
  v IN FRANGE f <-> exists k, k IN FDOM f /\ FAPPLY f k = v.
Proof. intros; rewrite FRANGE_DEF; reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FRANGE_FLOOKUP" *)
Theorem FRANGE_FLOOKUP : forall (f : fmap K V) v, v IN FRANGE f <-> exists k, FLOOKUP f k = SOME v.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "IN_FRANGE_FLOOKUP" *)
Theorem IN_FRANGE_FLOOKUP : forall (f : fmap K V) v,
  v IN FRANGE f <-> exists k, FLOOKUP f k = SOME v.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FRANGE_FEMPTY" *)
Theorem FRANGE_FEMPTY : FRANGE (FEMPTY : fmap K V) = {}.
Proof. set_ext; unfold_sets; split; [intros [k E]; discriminate|tauto]. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_FRANGE" *)
Theorem SUBMAP_FRANGE : forall f g : fmap K V, f ⊑ g -> FRANGE f SUBSET FRANGE g.
Proof. intros f g h y [k E]; exists k; apply h, E. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "o_f_FRANGE" *)
Theorem o_f_FRANGE : forall {W} x (g : fmap K V) (f : V -> W), x IN FRANGE g -> f x IN FRANGE (o_f f g).
Proof. intros W x g f [k E]; exists k; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FRANGE_FUNION" *)
Theorem FRANGE_FUNION : forall fm1 fm2 : fmap K V,
  DISJOINT (FDOM fm1) (FDOM fm2) ->
  (FRANGE (FUNION fm1 fm2) = FRANGE fm1 UNION FRANGE fm2).
Proof.
  intros fm1 fm2 hd; rewrite DISJOINT_iff in hd; set_ext; split.
  - intros [k E]; rewrite FLOOKUP_FUNION in E; destruct (FLOOKUP fm1 k) eqn:E1.
    + left; exists k; congruence.
    + right; exists k; exact E.
  - intros [[k E]|[k E]]; exists k; specialize (hd k); fm_auto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FINITE_MAP_LOOKUP_RANGE" *)
Theorem FINITE_MAP_LOOKUP_RANGE `{Inhabited V} :
  (forall (f : fmap K V) x y, FLOOKUP f x = SOME y -> y IN FRANGE f) /\
  (forall (f : fmap K V) x, x IN FDOM f -> FAPPLY f x IN FRANGE f).
Proof. split; intros; [exists x; exact H0|exists x; fm_auto]. Qed.

Context `{EqDecision K}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FRANGE_FUPDATE" *)
Theorem FRANGE_FUPDATE : forall (f : fmap K V) x y,
  FRANGE (FUPDATE f (x, y)) = y INSERT FRANGE (DRESTRICT f (COMPL (x INSERT {}))).
Proof.
  intros; set_ext; split.
  - intros [k E]; fm_lookup; fm_cases; right; exists k; fm_auto.
  - intros [->|[k E]]; [exists x|exists k]; fm_auto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FRANGE_FUPDATE_DOMSUB" *)
Theorem FRANGE_FUPDATE_DOMSUB : forall (fm : fmap K V) k v,
  FRANGE (fm |+ (k, v)) = v INSERT FRANGE (fm \\ k).
Proof.
  intros; set_ext; split.
  - intros [a E]; fm_lookup; fm_cases; right; exists a; fm_auto.
  - intros [->|[a E]]; [exists k|exists a]; fm_auto.
Qed.

End Frange.

(** ** Domain subtraction [\\] *)

Section Domsub.
Context {K V : Type} `{EqDecision K}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_domsub" *)
Theorem fmap_domsub : forall (fm : fmap K V) k, fdomsub fm k = DRESTRICT fm (COMPL (k INSERT {})).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DOMSUB_FEMPTY" *)
Theorem DOMSUB_FEMPTY : forall k, (FEMPTY : fmap K V) \\ k = FEMPTY.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DOMSUB_FUPDATE" *)
Theorem DOMSUB_FUPDATE : forall (fm : fmap K V) k v, fm |+ (k, v) \\ k = fm \\ k.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DOMSUB_FUPDATE_NEQ" *)
Theorem DOMSUB_FUPDATE_NEQ : forall (fm : fmap K V) k1 k2 v,
  ~ (k1 = k2) -> (fm |+ (k1, v) \\ k2 = fm \\ k2 |+ (k1, v)).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DOMSUB_FUPDATE_THM" *)
Theorem DOMSUB_FUPDATE_THM : forall (fm : fmap K V) k1 k2 v,
  fm |+ (k1, v) \\ k2 = if decide (k1 = k2) then fm \\ k2 else (fm \\ k2) |+ (k1, v).
Proof. intros; destruct (decide (k1 = k2)); apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDOM_DOMSUB" *)
Theorem FDOM_DOMSUB : forall (fm : fmap K V) k, FDOM (fm \\ k) = FDOM fm DELETE k.
Proof. intros; set_ext; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DOMSUB_FLOOKUP" *)
Theorem DOMSUB_FLOOKUP : forall (fm : fmap K V) k, FLOOKUP (fm \\ k) k = NONE.
Proof. intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DOMSUB_FLOOKUP_NEQ" *)
Theorem DOMSUB_FLOOKUP_NEQ : forall (fm : fmap K V) k1 k2,
  ~ (k1 = k2) -> (FLOOKUP (fm \\ k1) k2 = FLOOKUP fm k2).
Proof. intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DOMSUB_IDEM" *)
Theorem DOMSUB_IDEM : forall (fm : fmap K V) k, (fm \\ k) \\ k = fm \\ k.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DOMSUB_COMMUTES" *)
Theorem DOMSUB_COMMUTES : forall (fm : fmap K V) k1 k2, fm \\ k1 \\ k2 = fm \\ k2 \\ k1.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DOMSUB_NOT_IN_DOM" *)
Theorem DOMSUB_NOT_IN_DOM : forall k (fm : fmap K V), ~ k IN FDOM fm -> (fm \\ k = fm).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DRESTRICT_DOMSUB" *)
Theorem DRESTRICT_DOMSUB : forall (f : fmap K V) s k,
  DRESTRICT f s \\ k = DRESTRICT f (s DELETE k).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_PURGE'" *)
Theorem FUPDATE_PURGE' : forall (f : fmap K V) x y, (f \\ x) |+ (x, y) = f |+ (x, y).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_PURGE" *)
Theorem FUPDATE_PURGE : forall (f : fmap K V) x y, f |+ (x, y) = (f \\ x) |+ (x, y).
Proof. intros; symmetry; apply FUPDATE_PURGE'. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPD11_SAME_KEY_AND_BASE" *)
Theorem FUPD11_SAME_KEY_AND_BASE : forall (f : fmap K V) k v1 v2,
  (f |+ (k, v1) = f |+ (k, v2)) <-> (v1 = v2).
Proof.
  intros; split; [|intros ->; reflexivity].
  intros E; assert (h := f_equal (fun g => FLOOKUP g k) E); cbn in h; fm_cases.
Qed.

Context `{Inhabited V}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DOMSUB_FAPPLY" *)
Theorem DOMSUB_FAPPLY : forall (fm : fmap K V) k, FAPPLY (fm \\ k) k = FAPPLY FEMPTY k.
Proof. intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DOMSUB_FAPPLY_NEQ" *)
Theorem DOMSUB_FAPPLY_NEQ : forall (fm : fmap K V) k1 k2,
  ~ (k1 = k2) -> (FAPPLY (fm \\ k1) k2 = FAPPLY fm k2).
Proof. intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DOMSUB_FAPPLY_THM" *)
Theorem DOMSUB_FAPPLY_THM : forall (fm : fmap K V) k1 k2,
  FAPPLY (fm \\ k1) k2 = if decide (k1 = k2) then FAPPLY FEMPTY k2 else FAPPLY fm k2.
Proof. intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_ELIM" *)
Theorem FUPDATE_ELIM : forall k v (f : fmap K V), (k IN FDOM f /\ FAPPLY f k = v) -> (f |+ (k, v) = f).
Proof. intros k v f [h1 h2]; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_SAME_APPLY" *)
Theorem FUPDATE_SAME_APPLY : forall x kv (fm1 fm2 : fmap K V),
  (x = FST kv) \/ (FAPPLY fm1 x = FAPPLY fm2 x) -> FAPPLY (fm1 |+ kv) x = FAPPLY (fm2 |+ kv) x.
Proof. intros x [k v] fm1 fm2 h; cbn in h; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "flookup_thm" *)
Theorem flookup_thm : forall (f : fmap K V) x v,
  ((FLOOKUP f x = NONE) <-> ~ x IN FDOM f) /\ ((FLOOKUP f x = SOME v) <-> x IN FDOM f /\ FAPPLY f x = v).
Proof. intros; split; fm_auto. Qed.

End Domsub.

(** ** Iterated update [|++] *)

Section FupdateList.
Context {K V : Type} `{EqDecision K}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_LIST_THM" *)
Theorem FUPDATE_LIST_THM : forall f : fmap K V,
  (f |++ [] = f) /\ (forall h t, f |++ (h :: t) = (FUPDATE f h) |++ t).
Proof. split; reflexivity. Qed.

Lemma FLOOKUP_FUPDATE_LIST_notin (l : list (K * V)) fm k :
  ~ In k (map fst l) -> FLOOKUP (fm |++ l) k = FLOOKUP fm k.
Proof.
  revert fm; induction l as [|[a b] t IH]; intros fm h; [reflexivity|].
  cbn in h; change (FLOOKUP ((fm |+ (a, b)) |++ t) k = FLOOKUP fm k).
  rewrite IH by tauto; fm_auto.
Qed.

Lemma FLOOKUP_FUPDATE_LIST_in (l : list (K * V)) fm1 fm2 k :
  In k (map fst l) -> FLOOKUP (fm1 |++ l) k = FLOOKUP (fm2 |++ l) k.
Proof.
  revert fm1 fm2; induction l as [|[a b] t IH]; intros fm1 fm2 h; [destruct h|].
  change (FLOOKUP ((fm1 |+ (a, b)) |++ t) k = FLOOKUP ((fm2 |+ (a, b)) |++ t) k).
  destruct (in_dec (fun x y => decide (x = y)) k (map fst t)) as [i|n]; [apply IH, i|].
  rewrite !FLOOKUP_FUPDATE_LIST_notin by exact n.
  cbn in h; destruct h as [<-|h]; [|tauto]; fm_auto.
Qed.

Lemma FDOM_FUPDATE_LIST_iff (kvl : list (K * V)) fm y :
  FDOM (fm |++ kvl) y <-> y IN FDOM fm \/ In y (map fst kvl).
Proof.
  destruct (in_dec (fun x y => decide (x = y)) y (map fst kvl)) as [i|n].
  - split; [tauto|intros _].
    revert fm; induction kvl as [|[a b] t IH]; intros fm; [destruct i|].
    change (FDOM ((fm |+ (a, b)) |++ t) y).
    destruct (in_dec (fun x y => decide (x = y)) y (map fst t)) as [i'|n']; [apply IH, i'|].
    unfold_sets; unfold FDOM; rewrite FLOOKUP_FUPDATE_LIST_notin by exact n'.
    cbn in i; destruct i as [<-|i]; [|tauto]; fm_auto.
  - unfold_sets; unfold FDOM; rewrite FLOOKUP_FUPDATE_LIST_notin by exact n; tauto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_LIST_APPLY_NOT_MEM" *)
Theorem FUPDATE_LIST_APPLY_NOT_MEM `{Inhabited V} : forall kvl (f : fmap K V) k,
  ~ MEM k (MAP FST kvl) -> FAPPLY (f |++ kvl) k = FAPPLY f k.
Proof.
  intros kvl f k h; rewrite MEM_iff in h; unfold FAPPLY.
  rewrite FLOOKUP_FUPDATE_LIST_notin by exact h; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_LIST_APPEND" *)
Theorem FUPDATE_LIST_APPEND : forall (fm : fmap K V) kvl1 kvl2,
  fm |++ (kvl1 ++ kvl2) = fm |++ kvl1 |++ kvl2.
Proof. intros; unfold FUPDATE_LIST; rewrite !FOLDL_fold_left, fold_left_app; reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_FUPDATE_LIST_COMMUTES" *)
Theorem FUPDATE_FUPDATE_LIST_COMMUTES : forall k kvl (fm : fmap K V) v,
  ~ MEM k (MAP FST kvl) -> (fm |+ (k, v) |++ kvl = (fm |++ kvl) |+ (k, v)).
Proof.
  intros k kvl fm v h; rewrite MEM_iff in h; apply fmap_ext; intros a.
  destruct (in_dec (fun x y => decide (x = y)) a (map fst kvl)) as [i|n].
  - assert (k <> a) by (intros ->; tauto).
    rewrite FLOOKUP_UPDATE; destruct (decide (k = a)); [tauto|].
    apply FLOOKUP_FUPDATE_LIST_in, i.
  - rewrite FLOOKUP_FUPDATE_LIST_notin by exact n; fm_lookup.
    rewrite FLOOKUP_FUPDATE_LIST_notin by exact n; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_FUPDATE_LIST_MEM" *)
Theorem FUPDATE_FUPDATE_LIST_MEM : forall k kvl (fm : fmap K V) v,
  MEM k (MAP FST kvl) -> (fm |+ (k, v) |++ kvl = fm |++ kvl).
Proof.
  intros k kvl fm v h; rewrite MEM_iff in h; apply fmap_ext; intros a.
  destruct (in_dec (fun x y => decide (x = y)) a (map fst kvl)) as [i|n].
  - apply FLOOKUP_FUPDATE_LIST_in, i.
  - rewrite !FLOOKUP_FUPDATE_LIST_notin by exact n; fm_auto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_LIST_SNOC" *)
Theorem FUPDATE_LIST_SNOC : forall xs x (fm : fmap K V), fm |++ SNOC x xs = (fm |++ xs) |+ x.
Proof. intros; rewrite SNOC_app, FUPDATE_LIST_APPEND; reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FOLDL_FUPDATE_LIST" *)
Theorem FOLDL_FUPDATE_LIST : forall {A} (f1 : A -> K) (f2 : A -> V) ls a,
  FOLDL (fun fm k => fm |+ (f1 k, f2 k)) a ls = a |++ MAP (fun k => (f1 k, f2 k)) ls.
Proof. intros A f1 f2 ls; induction ls as [|x t IH]; intros a; cbn; [reflexivity|apply IH]. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_EQ_FUPDATE_LIST" *)
Theorem FUPDATE_EQ_FUPDATE_LIST : forall (fm : fmap K V) kv, fm |+ kv = fm |++ [kv].
Proof. reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fupdate_list_foldl" *)
Theorem fupdate_list_foldl : forall (m : fmap K V) l,
  FOLDL (fun env '(k, v) => env |+ (k, v)) m l = m |++ l.
Proof. intros m l; revert m; induction l as [|[k v] t IH]; intros m; cbn; [reflexivity|apply IH]. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fupdate_list_foldr" *)
Theorem fupdate_list_foldr : forall (m : fmap K V) l,
  FOLDR (fun '(k, v) env => env |+ (k, v)) m l = m |++ REVERSE l.
Proof.
  intros m l; induction l as [|[k v] t IH]; [reflexivity|].
  cbn [FOLDR REVERSE rev]; rewrite FUPDATE_LIST_APPEND, IH; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDOM_FUPDATE_LIST" *)
Theorem FDOM_FUPDATE_LIST : forall kvl (fm : fmap K V),
  FDOM (fm |++ kvl) = FDOM fm UNION set (MAP FST kvl).
Proof. intros; apply EXTENSION; intros y; rewrite IN_UNION, IN_set; apply FDOM_FUPDATE_LIST_iff. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_LIST_EQ_FEMPTY" *)
Theorem FUPDATE_LIST_EQ_FEMPTY : forall (fm : fmap K V) ls,
  (fm |++ ls = FEMPTY) <-> (fm = FEMPTY) /\ (ls = []).
Proof.
  intros fm ls; split; [|intros [-> ->]; reflexivity].
  destruct ls as [|[k v] t]; [split; auto|intros E; exfalso].
  assert (h : FDOM (fm |++ ((k, v) :: t)) k) by (apply FDOM_FUPDATE_LIST_iff; right; left; reflexivity).
  rewrite E in h; apply h; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_LIST_CANCEL" *)
Theorem FUPDATE_LIST_CANCEL : forall ls1 (fm : fmap K V) ls2,
  (forall k, MEM k (MAP FST ls1) -> MEM k (MAP FST ls2)) ->
  (fm |++ ls1 |++ ls2 = fm |++ ls2).
Proof.
  intros ls1 fm ls2 h; apply fmap_ext; intros a; specialize (h a); rewrite !MEM_iff in h.
  destruct (in_dec (fun x y => decide (x = y)) a (map fst ls2)) as [i|n].
  - apply FLOOKUP_FUPDATE_LIST_in, i.
  - rewrite !FLOOKUP_FUPDATE_LIST_notin by tauto; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_LIST_APPEND_COMMUTES" *)
Theorem FUPDATE_LIST_APPEND_COMMUTES : forall l1 l2 (fm : fmap K V),
  DISJOINT (set (MAP FST l1)) (set (MAP FST l2)) ->
  (fm |++ l1 |++ l2 = fm |++ l2 |++ l1).
Proof.
  intros l1 l2 fm h; rewrite DISJOINT_iff in h; apply fmap_ext; intros a; specialize (h a);
    change (~ (a IN set (MAP FST l1) /\ a IN set (MAP FST l2))) in h; rewrite !IN_set in h.
  destruct (in_dec (fun x y => decide (x = y)) a (map fst l2)) as [i|n].
  - rewrite (FLOOKUP_FUPDATE_LIST_notin l1) by tauto.
    apply FLOOKUP_FUPDATE_LIST_in, i.
  - rewrite (FLOOKUP_FUPDATE_LIST_notin l2) by exact n.
    destruct (in_dec (fun x y => decide (x = y)) a (map fst l1)) as [i'|n'].
    + apply FLOOKUP_FUPDATE_LIST_in, i'.
    + rewrite !FLOOKUP_FUPDATE_LIST_notin by assumption; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_SAME_LIST_APPLY" *)
Theorem FUPDATE_SAME_LIST_APPLY `{Inhabited V} : forall kvl (fm1 fm2 : fmap K V) x,
  MEM x (MAP FST kvl) -> FAPPLY (fm1 |++ kvl) x = FAPPLY (fm2 |++ kvl) x.
Proof.
  intros kvl fm1 fm2 x h; rewrite MEM_iff in h; unfold FAPPLY.
  rewrite (FLOOKUP_FUPDATE_LIST_in kvl fm1 fm2) by exact h; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_LIST_ALL_DISTINCT_REVERSE" *)
Theorem FUPDATE_LIST_ALL_DISTINCT_REVERSE : forall ls : list (K * V),
  ALL_DISTINCT (MAP FST ls) -> forall fm, fm |++ (REVERSE ls) = fm |++ ls.
Proof.
  induction ls as [|[k v] t IH]; intros h fm; [reflexivity|].
  cbn in h; apply andb_prop in h as [h1 h2]; apply negb_true_iff in h1.
  cbn [REVERSE rev]; rewrite FUPDATE_LIST_APPEND, IH by exact h2.
  change ((fm |++ t) |++ [(k, v)] = (fm |+ (k, v)) |++ t).
  rewrite FUPDATE_FUPDATE_LIST_COMMUTES; [reflexivity|].
  rewrite h1; discriminate.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DOMSUB_FUPDATE_LIST" *)
Theorem DOMSUB_FUPDATE_LIST : forall l (m : fmap K V) x,
  (m |++ l) \\ x = (m \\ x) |++ (FILTER ((fun y => bool_decide (x <> y)) ∘ FST) l).
Proof.
  induction l as [|[k v] t IH]; intros m x; [reflexivity|].
  change (((m |+ (k, v)) |++ t) \\ x =
    (m \\ x) |++ (if bool_decide (x <> k) then (k, v) :: FILTER ((fun y => bool_decide (x <> y)) ∘ FST) t
                  else FILTER ((fun y => bool_decide (x <> y)) ∘ FST) t)).
  rewrite IH; destruct (bool_decide (x <> k)) eqn:E.
  - apply bool_decide_spec in E; rewrite DOMSUB_FUPDATE_NEQ by congruence; reflexivity.
  - assert (x = k) as ->.
    { destruct (decide (x = k)); [assumption|].
      exfalso; assert (bool_decide (x <> k) = true) by (apply bool_decide_spec; assumption); congruence. }
    rewrite DOMSUB_FUPDATE; reflexivity.
Qed.

End FupdateList.

(** ** [FUN_FMAP] and [FMAP_MAP2] *)

(** HOL [FUN_FMAP_DEF] and [FLOOKUP_FUN_FMAP] assume pred_set's [FINITE P];
    here finiteness is given by a covering list. *)
Lemma FLOOKUP_FUN_FMAP_list {K V} (f : K -> V) (P : K -> Prop) k :
  (exists l : list K, forall x, P x -> In x l) ->
  FLOOKUP (FUN_FMAP f P) k = if classical_dec (P k) then SOME (f k) else NONE.
Proof.
  intros h; unfold FUN_FMAP; destruct (classical_dec _) as [h'|n]; [reflexivity|tauto].
Qed.

Section FunFmap.
Context {K V W : Type}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FMAP_MAP2_def" *)
Theorem FMAP_MAP2_def `{Inhabited V} : forall (f : K * V -> W) (m : fmap K V),
  FMAP_MAP2 f m = FUN_FMAP (fun x => f (x, FAPPLY m x)) (FDOM m).
Proof.
  intros f m; apply fmap_ext; intros k.
  rewrite FLOOKUP_FUN_FMAP_list by apply FLOOKUP_finite; fm_auto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FMAP_MAP2_THM" *)
Theorem FMAP_MAP2_THM `{Inhabited V} `{Inhabited W} : forall (f : K * V -> W) (m : fmap K V),
  (FDOM (FMAP_MAP2 f m) = FDOM m) /\
  (forall x, x IN FDOM m -> FAPPLY (FMAP_MAP2 f m) x = f (x, FAPPLY m x)).
Proof. intros; split; [set_ext|intros]; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FMAP_MAP2_FEMPTY" *)
Theorem FMAP_MAP2_FEMPTY : forall f : K * V -> W, FMAP_MAP2 f FEMPTY = FEMPTY.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

Context `{EqDecision K}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FMAP_MAP2_FUPDATE" *)
Theorem FMAP_MAP2_FUPDATE : forall (f : K * V -> W) m x v,
  FMAP_MAP2 f (m |+ (x, v)) = (FMAP_MAP2 f m) |+ (x, f (x, v)).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DOMSUB_FMAP_MAP2" *)
Theorem DOMSUB_FMAP_MAP2 : forall (f : K * V -> W) m s,
  (FMAP_MAP2 f m) \\ s = FMAP_MAP2 f (m \\ s).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FMAP_MAP2_FUPDATE_LIST" *)
Theorem FMAP_MAP2_FUPDATE_LIST : forall l (m : fmap K V) (f : K * V -> W),
  FMAP_MAP2 f (m |++ l) = FMAP_MAP2 f m |++ MAP (fun '(k, v) => (k, f (k, v))) l.
Proof.
  induction l as [|[k v] t IH]; intros m f; [reflexivity|].
  change (FMAP_MAP2 f ((m |+ (k, v)) |++ t) = (FMAP_MAP2 f m |+ (k, f (k, v))) |++
    MAP (fun '(k, v) => (k, f (k, v))) t).
  rewrite IH, FMAP_MAP2_FUPDATE; reflexivity.
Qed.

End FunFmap.

(** ** [FDIFF] *)

Section Fdiff.
Context {K V W : Type}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDOM_FDIFF" *)
Theorem FDOM_FDIFF : forall x (refs : fmap K V) f2,
  x IN FDOM (FDIFF refs f2) <-> x IN FDOM refs /\ x NOTIN f2.
Proof. intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDIFF_FEMPTY" *)
Theorem FDIFF_FEMPTY : forall s, FDIFF (FEMPTY : fmap K V) s = FEMPTY.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDIFF_EMPTY" *)
Theorem FDIFF_EMPTY : forall f : fmap K V, FDIFF f {} = f.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDIFF_FDIFF" *)
Theorem FDIFF_FDIFF : forall (fm : fmap K V) s1 s2,
  FDIFF (FDIFF fm s1) s2 = FDIFF fm (s1 UNION s2).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDIFF_FUNION" *)
Theorem FDIFF_FUNION : forall (fm1 fm2 : fmap K V) s,
  FDIFF (FUNION fm1 fm2) s = FUNION (FDIFF fm1 s) (FDIFF fm2 s).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDIFF_BOUND" *)
Theorem FDIFF_BOUND : forall (f : fmap K V) p, FDIFF f p = FDIFF f (p INTER FDOM f).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDIFF_FMAP_MAP2" *)
Theorem FDIFF_FMAP_MAP2 : forall (f : K * V -> W) m s,
  FDIFF (FMAP_MAP2 f m) s = FMAP_MAP2 f (FDIFF m s).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

Context `{EqDecision K}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDIFF_FUPDATE" *)
Theorem FDIFF_FUPDATE : forall (fm : fmap K V) k v s,
  FDIFF (fm |+ (k, v)) s = if classical_dec (k IN s) then FDIFF fm s else (FDIFF fm s) |+ (k, v).
Proof. intros; destruct (classical_dec (k IN s)); apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDIFF_FDOMSUB" *)
Theorem FDIFF_FDOMSUB : forall (f : fmap K V) x p, FDIFF (f \\ x) p = FDIFF f p \\ x.
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDIFF_FDOMSUB_INSERT" *)
Theorem FDIFF_FDOMSUB_INSERT : forall (f : fmap K V) x p,
  FDIFF (f \\ x) p = FDIFF f (x INSERT p).
Proof. intros; apply fmap_ext; intros; fm_auto. Qed.

End Fdiff.

(** ** [fmap_rel] *)

Section FmapRel.
Context {K V W : Type}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_rel_OPTREL_FLOOKUP" *)
Theorem fmap_rel_OPTREL_FLOOKUP : forall (R : V -> W -> Prop) (f1 : fmap K V) f2,
  fmap_rel R f1 f2 <-> forall k, OPTREL R (FLOOKUP f1 k) (FLOOKUP f2 k).
Proof. reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_rel_def" *)
Theorem fmap_rel_def `{Inhabited V} `{Inhabited W} : forall (R : V -> W -> Prop) (f1 : fmap K V) f2,
  fmap_rel R f1 f2 <-> FDOM f2 = FDOM f1 /\ (forall x, x IN FDOM f1 -> R (FAPPLY f1 x) (FAPPLY f2 x)).
Proof.
  intros R f1 f2; unfold fmap_rel, OPTREL; split.
  - intros h; split.
    + apply EXTENSION; intros x; specialize (h x); unfold_sets; unfold FDOM;
        destruct h as [[-> ->]|(a & b & -> & -> & _)]; split; intros; congruence.
    + intros x hx; specialize (h x); unfold_sets; unfold FDOM, FAPPLY, THE in *.
      destruct h as [[e _]|(a & b & -> & -> & hab)]; [contradiction|exact hab].
  - intros [hd h] k; specialize (h k); assert (hk := f_equal (fun s => s k) hd); cbn in hk.
    unfold_sets; unfold FDOM, FAPPLY, THE in *; cbv beta in *.
    destruct (FLOOKUP f1 k) eqn:E1, (FLOOKUP f2 k) eqn:E2.
    + right; exists v, w; split; [reflexivity|split; [reflexivity|apply h; discriminate]].
    + exfalso; assert (q : Some v <> None) by discriminate; rewrite <- hk in q; apply q; reflexivity.
    + exfalso; assert (q : Some w <> None) by discriminate; rewrite hk in q; apply q; reflexivity.
    + left; split; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_rel_FLOOKUP_imp" *)
Theorem fmap_rel_FLOOKUP_imp : forall (R : V -> W -> Prop) (f1 : fmap K V) f2,
  fmap_rel R f1 f2 ->
  (forall k, FLOOKUP f1 k = NONE -> FLOOKUP f2 k = NONE) /\
  (forall k v1, FLOOKUP f1 k = SOME v1 -> exists v2, FLOOKUP f2 k = SOME v2 /\ R v1 v2).
Proof.
  intros R f1 f2 h; split.
  - intros k E; specialize (h k); unfold OPTREL in h; rewrite E in h.
    destruct h as [[_ h]|(x & y & h1 & _ & _)]; [exact h|discriminate].
  - intros k v1 E; specialize (h k); unfold OPTREL in h; rewrite E in h.
    destruct h as [[h _]|(x & y & h1 & h2 & h3)]; [discriminate|].
    injection h1 as <-; eauto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_rel_FEMPTY" *)
Theorem fmap_rel_FEMPTY : forall (R : V -> W -> Prop) (f2 : fmap K W) (f1 : fmap K V),
  (fmap_rel R FEMPTY f2 <-> f2 = FEMPTY) /\ (fmap_rel R f1 FEMPTY <-> f1 = FEMPTY).
Proof.
  intros R f2 f1; rewrite !fmap_ext_iff; unfold fmap_rel, OPTREL; split; split;
    intros h k; specialize (h k); cbn in *; firstorder congruence.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_rel_mono" *)
Theorem fmap_rel_mono : forall (R1 R2 : V -> W -> Prop) (f1 : fmap K V) f2,
  (forall x y, R1 x y -> R2 x y) -> fmap_rel R1 f1 f2 -> fmap_rel R2 f1 f2.
Proof. intros R1 R2 f1 f2 hR h k; specialize (h k); unfold OPTREL in *; firstorder. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_rel_FUNION_rels" *)
Theorem fmap_rel_FUNION_rels : forall (R : V -> W -> Prop) f1 f2 (f3 : fmap K V) f4,
  fmap_rel R f1 f2 /\ fmap_rel R f3 f4 -> fmap_rel R (FUNION f1 f3) (FUNION f2 f4).
Proof.
  intros R f1 f2 f3 f4 [h1 h2] k; specialize (h1 k); specialize (h2 k); unfold OPTREL in *.
  rewrite !FLOOKUP_FUNION; destruct h1 as [[-> ->]|(x & y & -> & -> & h)]; auto.
  right; eauto.
Qed.

Context `{EqDecision K}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_rel_FUPDATE_same" *)
Theorem fmap_rel_FUPDATE_same : forall (R : V -> W -> Prop) (f1 : fmap K V) f2 v1 v2 k,
  fmap_rel R f1 f2 /\ R v1 v2 -> fmap_rel R (f1 |+ (k, v1)) (f2 |+ (k, v2)).
Proof.
  intros R f1 f2 v1 v2 k [h hv] a; rewrite !FLOOKUP_UPDATE; destruct (decide (k = a)); auto.
  right; eauto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_rel_FUPDATE_I" *)
Theorem fmap_rel_FUPDATE_I : forall (R : V -> W -> Prop) (f1 : fmap K V) f2 k v1 v2,
  fmap_rel R (f1 \\ k) (f2 \\ k) /\ R v1 v2 -> fmap_rel R (f1 |+ (k, v1)) (f2 |+ (k, v2)).
Proof.
  intros R f1 f2 k v1 v2 [h hv] a; specialize (h a); rewrite !DOMSUB_FLOOKUP_THM in h.
  rewrite !FLOOKUP_UPDATE; destruct (decide (k = a)); auto; right; eauto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_rel_FUPDATE_EQN" *)
Theorem fmap_rel_FUPDATE_EQN : forall (R : V -> W -> Prop) (f1 : fmap K V) f2 k v1 v2,
  fmap_rel R (f1 \\ k) (f2 \\ k) /\ R v1 v2 <-> fmap_rel R (f1 |+ (k, v1)) (f2 |+ (k, v2)).
Proof.
  intros R f1 f2 k v1 v2; split; [apply fmap_rel_FUPDATE_I|intros h].
  split.
  - intros a; pose proof (h a) as ha; rewrite !FLOOKUP_UPDATE in ha.
    rewrite !DOMSUB_FLOOKUP_THM; destruct (decide (k = a)); [left; auto|exact ha].
  - specialize (h k); rewrite !FLOOKUP_UPDATE in h; destruct (decide (k = k)); [|tauto].
    unfold OPTREL in h; destruct h as [[h _]|(x & y & h1 & h2 & h3)]; [discriminate|congruence].
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_rel_FUPDATE_LIST_same" *)
Theorem fmap_rel_FUPDATE_LIST_same : forall (R : V -> W -> Prop) ls1 ls2 (f1 : fmap K V) f2,
  fmap_rel R f1 f2 /\ (MAP FST ls1 = MAP FST ls2) /\ (LIST_REL R (MAP SND ls1) (MAP SND ls2)) ->
  fmap_rel R (f1 |++ ls1) (f2 |++ ls2).
Proof.
  intros R ls1; induction ls1 as [|[k1 v1] t1 IH]; intros [|[k2 v2] t2] f1 f2 (h1 & h2 & h3);
    try discriminate; [exact h1|].
  cbn in h2, h3; injection h2 as -> h2; inversion h3; subst.
  apply (IH t2 (f1 |+ (k2, v1)) (f2 |+ (k2, v2))); split; [|split]; auto.
  apply fmap_rel_FUPDATE_same; auto.
Qed.

End FmapRel.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_rel_refl" *)
Theorem fmap_rel_refl {K V} : forall (R : V -> V -> Prop) (x : fmap K V),
  (forall x, R x x) -> fmap_rel R x x.
Proof.
  intros R x h k; unfold OPTREL; destruct (FLOOKUP x k); [right; eauto|left; auto].
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_rel_trans" *)
Theorem fmap_rel_trans {K V} : forall R : V -> V -> Prop,
  (forall x y z, R x y /\ R y z -> R x z) ->
  forall x y z : fmap K V, fmap_rel R x y /\ fmap_rel R y z -> fmap_rel R x z.
Proof.
  intros R hR x y z [h1 h2] k; specialize (h1 k); specialize (h2 k); unfold OPTREL in *.
  destruct h1 as [[e1 e2]|(a & b & e1 & e2 & hab)];
    destruct h2 as [[e3 e4]|(c & d & e3 & e4 & hcd)]; rewrite ?e1, ?e4; try congruence.
  - left; split; reflexivity.
  - right; exists a, d; rewrite e2 in e3; injection e3 as <-; eauto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "fmap_rel_sym" *)
Theorem fmap_rel_sym {K V} : forall R : V -> V -> Prop,
  (forall x y, R x y -> R y x) ->
  forall x y : fmap K V, fmap_rel R x y -> fmap_rel R y x.
Proof.
  intros R hR x y h k; specialize (h k); unfold OPTREL in *.
  destruct h as [[-> ->]|(a & b & -> & -> & hab)]; [left; auto|right; exists b, a; auto].
Qed.

(** ** Collected [FLOOKUP] characterisations *)

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "TO_FLOOKUP" *)
Theorem TO_FLOOKUP {K V} `{Inhabited V} : forall x (m : fmap K V) y m' P,
  (x IN FDOM m <-> FLOOKUP m x <> NONE) /\
  (y IN FRANGE m <-> exists k, FLOOKUP m k = SOME y) /\
  (FLOOKUP m x <> NONE -> FAPPLY m x = THE (FLOOKUP m x)) /\
  (m = m' <-> FLOOKUP m = FLOOKUP m') /\
  (m ⊑ m' <-> forall k v, FLOOKUP m k = SOME v -> FLOOKUP m' k = SOME v) /\
  (FEVERY P m <-> forall k v, FLOOKUP m k = SOME v -> P (k, v)).
Proof.
  intros; split; [reflexivity|split; [reflexivity|split; [reflexivity|split]]].
  - apply FLOOKUP_EXT.
  - split; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "NUM_NOT_IN_FDOM" *)
Theorem NUM_NOT_IN_FDOM {A} : forall f : fmap num A, exists x, x NOTIN FDOM f.
Proof.
  intros f; destruct (FLOOKUP_finite f) as [l Hl].
  assert (hm : forall y, In y l -> y <= fold_right N.max 0 l).
  { clear Hl; induction l as [|a t IH]; cbn; [tauto|intros y [<-|h]; [lia|specialize (IH y h); lia]]. }
  exists (N.succ (fold_right N.max 0 l)); intros h; specialize (hm _ (Hl _ h)); lia.
Qed.

(** ** Finiteness and cardinality of the domain *)

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDOM_FINITE" *)
Theorem FDOM_FINITE {K V} : forall fm : fmap K V, FINITE (FDOM fm).
Proof. intros fm; apply (proj2 (FINITE_list _)), FLOOKUP_finite. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FCARD_DEF" *)
Definition FCARD {K V} (fm : fmap K V) : num := CARD (FDOM fm).

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FCARD_FEMPTY" *)
Theorem FCARD_FEMPTY {K V} : FCARD (FEMPTY : fmap K V) = 0.
Proof. unfold FCARD; rewrite FDOM_FEMPTY; apply CARD_EMPTY. Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FCARD_FUPDATE" *)
Theorem FCARD_FUPDATE {K V} `{EqDecision K} : forall (fm : fmap K V) a b,
  FCARD (FUPDATE fm (a, b)) = if decide (a IN FDOM fm) then FCARD fm else 1 + FCARD fm.
Proof.
  intros fm a b; unfold FCARD; rewrite FDOM_FUPDATE, CARD_INSERT by apply FDOM_FINITE.
  destruct (classical_dec _), (decide _); try contradiction; lia.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FCARD_0_FEMPTY" *)
Theorem FCARD_0_FEMPTY {K V} : forall f : fmap K V, (FCARD f = 0) <-> (f = FEMPTY).
Proof.
  intros f; unfold FCARD; rewrite (CARD_EQ_0 _ (FDOM_FINITE f)).
  pose proof (@FDOM_EQ_EMPTY K V) as h; split.
  - intros e; destruct (classic (f = FEMPTY)) as [->|n]; [reflexivity|exfalso].
    assert (hn : exists k, k IN FDOM f).
    { apply NNPP; intros hk; apply n, fmap_ext; intros k; cbn.
      destruct (FLOOKUP f k) eqn:E; [|reflexivity]; exfalso; apply hk; exists k; unfold_sets; unfold FDOM; congruence. }
    destruct hn as [k hk]; rewrite e in hk; exact hk.
  - intros ->; apply FDOM_FEMPTY.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "LEAST_NOTIN_FDOM" *)
Theorem LEAST_NOTIN_FDOM {A} : forall refs : fmap num A,
  LEAST (fun ptr => ptr NOTIN FDOM refs) NOTIN FDOM refs.
Proof.
  intros refs; destruct (NUM_NOT_IN_FDOM refs) as [x hx].
  exact (LEAST_INTRO (fun ptr => ptr NOTIN FDOM refs) x hx).
Qed.

(** ** [FUN_FMAP] *)

Section FunFmap2.
Context {K V : Type}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FLOOKUP_FUN_FMAP" *)
Theorem FLOOKUP_FUN_FMAP : forall (f : K -> V) P k,
  FINITE P -> (FLOOKUP (FUN_FMAP f P) k = if classical_dec (k IN P) then SOME (f k) else NONE).
Proof. intros f P k h; exact (FLOOKUP_FUN_FMAP_list f P k (proj1 (FINITE_list P) h)). Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUN_FMAP_DEF" *)
Theorem FUN_FMAP_DEF `{Inhabited V} : forall (f : K -> V) P,
  FINITE P -> (FDOM (FUN_FMAP f P) = P) /\ (forall x, x IN P -> (FAPPLY (FUN_FMAP f P) x = f x)).
Proof.
  intros f P h; split.
  - apply EXTENSION; intros x; unfold_sets; unfold FDOM; rewrite (FLOOKUP_FUN_FMAP f P x h).
    destruct (classical_dec _); unfold_sets; split; intros; congruence || tauto.
  - intros x hx; unfold FAPPLY; rewrite (FLOOKUP_FUN_FMAP f P x h).
    destruct (classical_dec _); [reflexivity|contradiction].
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FDOM_FMAP" *)
Theorem FDOM_FMAP : forall (f : K -> V) s, FINITE s -> (FDOM (FUN_FMAP f s) = s).
Proof.
  intros f s h; apply EXTENSION; intros x; unfold_sets; unfold FDOM; rewrite (FLOOKUP_FUN_FMAP f s x h).
  destruct (classical_dec _); unfold_sets; split; intros; congruence || tauto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FUN_FMAP_EMPTY" *)
Theorem FUN_FMAP_EMPTY : forall f : K -> V, FUN_FMAP f {} = FEMPTY.
Proof.
  intros f; apply fmap_ext; intros k; rewrite FLOOKUP_FUN_FMAP by apply FINITE_EMPTY.
  destruct (classical_dec _) as [[]|_]; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FRANGE_FMAP" *)
Theorem FRANGE_FMAP : forall (f : K -> V) P, FINITE P -> (FRANGE (FUN_FMAP f P) = IMAGE f P).
Proof.
  intros f P h; apply EXTENSION; intros y; rewrite IN_IMAGE; unfold_sets; unfold FRANGE; split.
  - intros [k E]; rewrite (FLOOKUP_FUN_FMAP f P k h) in E; destruct (classical_dec _); [|discriminate].
    injection E as <-; eauto.
  - intros [x [-> hx]]; exists x; rewrite (FLOOKUP_FUN_FMAP f P x h).
    destruct (classical_dec _); [reflexivity|contradiction].
Qed.

End FunFmap2.

(** ** [MAP_KEYS]

    HOL introduces [MAP_KEYS] by [new_specification] ([MAP_KEYS_def]); the
    Galette definition looks up the chosen preimage of a key (HOL's [some]),
    and the specification is proved.  Not executable. *)
Section MapKeys.
Context {K1 K2 V : Type} `{Inhabited K1}.

Lemma MAP_KEYS_finite (f : K1 -> K2) (fm : fmap K1 V) :
  exists l : list K2, forall k,
    (fun k => if classical_dec (exists x, k = f x /\ x IN FDOM fm)
              then FLOOKUP fm (select (fun x => k = f x /\ x IN FDOM fm)) else None) k <> None ->
    In k l.
Proof.
  destruct (FLOOKUP_finite fm) as [l Hl]; exists (List.map f l); intros k; cbn.
  destruct (classical_dec _) as [[x [-> Hx]]|]; [|tauto]. intros _. apply in_map, Hl, Hx.
Qed.

Definition MAP_KEYS (f : K1 -> K2) (fm : fmap K1 V) : fmap K2 V :=
  mk_fmap (fun k => if classical_dec (exists x, k = f x /\ x IN FDOM fm)
                    then FLOOKUP fm (select (fun x => k = f x /\ x IN FDOM fm)) else None)
    (MAP_KEYS_finite f fm).

Lemma FLOOKUP_MAP_KEYS_INJ_gen (f : K1 -> K2) (fm : fmap K1 V) D x :
  INJ f D UNIV -> (forall y, y IN FDOM fm -> y IN D) -> x IN D ->
  FLOOKUP (MAP_KEYS f fm) (f x) = FLOOKUP fm x.
Proof.
  intros [_ HI] HD Hx; cbn. destruct (classical_dec _) as [Ex|Nx].
  - destruct (select_spec _ Ex) as [E Hy].
    set (y := select _) in *.
    replace y with x; [reflexivity|]. apply HI; [split; [exact Hx|apply HD, Hy]|exact E].
  - destruct (FLOOKUP fm x) eqn:F; [|reflexivity].
    exfalso; apply Nx; exists x; split; [reflexivity|]. change (FLOOKUP fm x <> None); rewrite F; discriminate.
Qed.

Lemma FLOOKUP_MAP_KEYS_none (f : K1 -> K2) (fm : fmap K1 V) k :
  (forall x, x IN FDOM fm -> k <> f x) -> FLOOKUP (MAP_KEYS f fm) k = None.
Proof.
  intros N; cbn; destruct (classical_dec _) as [[x [E Hx]]|]; [|reflexivity].
  exfalso; exact (N x Hx E).
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "MAP_KEYS_def" *)
Theorem MAP_KEYS_def `{Inhabited V} : forall (f : K1 -> K2) (fm : fmap K1 V),
  (FDOM (MAP_KEYS f fm) = IMAGE f (FDOM fm)) /\
  (INJ f (FDOM fm) UNIV -> forall x, x IN FDOM fm -> FAPPLY (MAP_KEYS f fm) (f x) = FAPPLY fm x).
Proof.
  intros f fm; split.
  - apply functional_extensionality; intros k; apply propositional_extensionality.
    unfold FDOM, IMAGE; cbn. destruct (classical_dec _) as [Ex|Nx].
    + split; [intros _; destruct Ex as [x [E Hx]]; exists x; split; assumption|].
      intros _; exact (proj2 (select_spec _ Ex)).
    + split; [tauto|]. intros [x [E Hx]]; exfalso; apply Nx; exists x; split; assumption.
  - intros HI x Hx; unfold FAPPLY.
    rewrite (FLOOKUP_MAP_KEYS_INJ_gen f fm (FDOM fm) x HI); auto.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "MAP_KEYS_FEMPTY" *)
Theorem MAP_KEYS_FEMPTY : forall f : K1 -> K2, MAP_KEYS f (FEMPTY : fmap K1 V) = FEMPTY.
Proof.
  intros f; apply fmap_ext; intros k; apply FLOOKUP_MAP_KEYS_none.
  intros x Hx; exfalso; apply Hx; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FLOOKUP_MAP_KEYS" *)
Theorem FLOOKUP_MAP_KEYS : forall (f : K1 -> K2) (m : fmap K1 V) k,
  INJ f (FDOM m) UNIV ->
  FLOOKUP (MAP_KEYS f m) k = OPTION_BIND (some (fun x => k = f x /\ x IN FDOM m)) (FLOOKUP m).
Proof.
  intros f m k _; cbn; unfold some; destruct (classical_dec _); reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "FLOOKUP_MAP_KEYS_MAPPED" *)
Theorem FLOOKUP_MAP_KEYS_MAPPED : forall (f : K1 -> K2) (m : fmap K1 V) k,
  INJ f UNIV UNIV -> FLOOKUP (MAP_KEYS f m) (f k) = FLOOKUP m k.
Proof.
  intros f m k HI; apply (FLOOKUP_MAP_KEYS_INJ_gen f m UNIV k HI); intros; exact I.
Qed.

Lemma FLOOKUP_MAP_KEYS_cases (f : K1 -> K2) (m : fmap K1 V) k :
  INJ f UNIV UNIV ->
  (exists x, k = f x /\ FLOOKUP (MAP_KEYS f m) k = FLOOKUP m x) \/
  ((forall x, k <> f x) /\ FLOOKUP (MAP_KEYS f m) k = None).
Proof.
  intros HI; destruct (classical_dec (exists x, k = f x)) as [[x ->]|N].
  - left; exists x; split; [reflexivity|apply FLOOKUP_MAP_KEYS_MAPPED, HI].
  - right; split; [intros x E; apply N; exists x; exact E|].
    apply FLOOKUP_MAP_KEYS_none; intros x _ E; apply N; exists x; exact E.
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DRESTRICT_MAP_KEYS_IMAGE" *)
Theorem DRESTRICT_MAP_KEYS_IMAGE : forall (f : K1 -> K2) (fm : fmap K1 V) s,
  INJ f UNIV UNIV -> DRESTRICT (MAP_KEYS f fm) (IMAGE f s) = MAP_KEYS f (DRESTRICT fm s).
Proof.
  intros f fm s HI; apply fmap_ext; intros k.
  rewrite FLOOKUP_DRESTRICT.
  destruct (FLOOKUP_MAP_KEYS_cases f fm k HI) as [[x [-> E]]|[N E]].
  - rewrite E, FLOOKUP_MAP_KEYS_MAPPED, FLOOKUP_DRESTRICT by exact HI.
    destruct (classical_dec (f x IN IMAGE f s)) as [[y [Ey Hy]]|Ny];
      destruct (classical_dec (x IN s)) as [Hx|Nx]; try reflexivity.
    + destruct HI as [_ HI]. exfalso; apply Nx.
      rewrite (HI x y); [exact Hy|split; exact I|exact Ey].
    + exfalso; apply Ny; exists x; split; [reflexivity|exact Hx].
  - rewrite (FLOOKUP_MAP_KEYS_none f (DRESTRICT fm s) k) by (intros x _; apply N).
    destruct (classical_dec _) as [[y [Ey _]]|]; [exfalso; exact (N y Ey)|reflexivity].
Qed.

Context `{EqDecision K1} `{EqDecision K2}.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "MAP_KEYS_FUPDATE" *)
Theorem MAP_KEYS_FUPDATE : forall (f : K1 -> K2) (fm : fmap K1 V) k v,
  INJ f (k INSERT FDOM fm) UNIV ->
  MAP_KEYS f (fm |+ (k, v)) = (MAP_KEYS f fm) |+ (f k, v).
Proof.
  intros f fm k v HI; apply fmap_ext; intros k2.
  rewrite FLOOKUP_UPDATE.
  assert (HD1 : forall y, y IN FDOM (fm |+ (k, v)) -> y IN (k INSERT FDOM fm)).
  { intros y Hy; change (FLOOKUP (fm |+ (k, v)) y <> None) in Hy; change (y = k \/ FLOOKUP fm y <> None); cbn in Hy.
    destruct (decide (k = y)) as [->|]; [left; reflexivity|right; exact Hy]. }
  assert (HD2 : forall y, y IN FDOM fm -> y IN (k INSERT FDOM fm)) by (intros y Hy; right; exact Hy).
  destruct (classical_dec (exists x, x IN (k INSERT FDOM fm) /\ k2 = f x)) as [[x [Hx ->]]|N].
  - rewrite (FLOOKUP_MAP_KEYS_INJ_gen f _ _ x HI HD1 Hx), FLOOKUP_UPDATE.
    destruct (decide (f k = f x)) as [E|E].
    + destruct HI as [_ HI]. rewrite (HI k x); [|split; [left; reflexivity|exact Hx]|exact E].
      destruct (decide (x = x)); [reflexivity|contradiction].
    + destruct (decide (k = x)) as [->|]; [contradiction|].
      rewrite (FLOOKUP_MAP_KEYS_INJ_gen f _ _ x HI HD2 Hx); reflexivity.
  - rewrite FLOOKUP_MAP_KEYS_none by (intros x Hx E; apply N; exists x; split; [apply HD1, Hx|exact E]).
    destruct (decide (f k = k2)) as [E|E].
    + exfalso; apply N; exists k; split; [left; reflexivity|symmetry; exact E].
    + symmetry; apply FLOOKUP_MAP_KEYS_none.
      intros x Hx E'; apply N; exists x; split; [apply HD2, Hx|exact E'].
Qed.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "DOMSUB_MAP_KEYS" *)
Theorem DOMSUB_MAP_KEYS : forall (f : K1 -> K2) (fm : fmap K1 V) s,
  BIJ f UNIV UNIV -> (MAP_KEYS f fm) \\ (f s) = MAP_KEYS f (fm \\ s).
Proof.
  intros f fm s [HI _]; apply fmap_ext; intros k.
  rewrite DOMSUB_FLOOKUP_THM.
  destruct (FLOOKUP_MAP_KEYS_cases f fm k HI) as [[x [-> E]]|[N E]].
  - rewrite E, FLOOKUP_MAP_KEYS_MAPPED, DOMSUB_FLOOKUP_THM by exact HI.
    destruct (decide (f s = f x)) as [E2|E2]; destruct (decide (s = x)) as [E3|Ne]; try reflexivity.
    + destruct HI as [_ HI]. exfalso; apply Ne, HI; [split; exact I|exact E2].
    + subst; contradiction.
  - rewrite (FLOOKUP_MAP_KEYS_none f (fm \\ s) k) by (intros x _; apply N).
    destruct (decide _); [reflexivity|exact E].
Qed.

End MapKeys.

(*! HOL "HOL/src/finite_maps/finite_mapScript.sml" "MAP_KEYS_BIJ_LINV" *)
Theorem MAP_KEYS_BIJ_LINV : forall {V} (f : num -> num) (t : fmap num V),
  BIJ f UNIV UNIV -> MAP_KEYS f (MAP_KEYS (LINV f UNIV) t) = t.
Proof.
  intros V f t HB; apply fmap_ext; intros k.
  pose proof (BIJ_LINV_INV f UNIV UNIV HB k I) as Ek.
  pose proof (BIJ_LINV_BIJ f UNIV UNIV HB) as [HIg _].
  rewrite <- Ek at 1. rewrite FLOOKUP_MAP_KEYS_MAPPED by (destruct HB; assumption).
  rewrite FLOOKUP_MAP_KEYS_MAPPED by exact HIg. reflexivity.
Qed.
