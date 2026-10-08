(** * CakeML [parmove]: correctness of the parallel-move compiler

    Part of the [parmoveScript] counterpart: the inductive relations [step]
    (HOL [▷]) and [dstep] (HOL [↪]) and the theorems of the script (the
    definitions are in [parmove.v]).

    Galette-local (untagged) infrastructure, documented where it is used:
    - HOL's [▷*] is [RTC step] and [↪*] is [RTC dstep] ([RTC] from
      [relation.v]).
    - HOL's [PERM] is not ported; [parsem_perm] is stated with Rocq's
      [Permutation] and therefore left untagged.
    - HOL's local overload [NoRead μ dn] is written out as
      [~ MEM dn (MAP SND μ)].
    - HOL's composition [f o g] is written as [fun x => f (g x)].
    - [EqDecision] instances are required on every type whose equality the
      definitions decide (the carrier convention of AGENTS.md). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.relation Require Import relation.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.backend.reg_alloc Require Import parmove.
From Stdlib Require Import Permutation.
Open Scope N_scope.

(** ** Local infrastructure *)


Lemma MEM_iff {X} `{EqDecision X} (x : X) l : is_true (MEM x l) <-> In x l.
Proof. apply MEM_In. Qed.

Lemma ALL_DISTINCT_iff {X} `{EqDecision X} (l : list X) : ALL_DISTINCT l = true <-> NoDup l.
Proof.
  unfold is_true; induction l as [|x l IH]; cbn [ALL_DISTINCT].
  - split; [constructor|reflexivity].
  - rewrite andb_true_iff, negb_true_iff, IH, NoDup_cons_iff, <- not_true_iff_false, MEM_In.
    reflexivity.
Qed.

Lemma windmill_iff {X} `{EqDecision X} (l : list (X * X)) : windmill l = true <-> NoDup (map fst l).
Proof. unfold windmill; apply ALL_DISTINCT_iff. Qed.

Lemma EVERY_iff {X} (P : X -> bool) l : is_true (EVERY P l) <-> forall x, In x l -> is_true (P x).
Proof. unfold is_true; rewrite EVERY_Forall, Forall_forall; reflexivity. Qed.

Lemma NoDup_map_inj_on {X Y} (f : X -> Y) l :
  NoDup l -> (forall a b, In a l -> In b l -> f a = f b -> a = b) -> NoDup (map f l).
Proof.
  induction l as [|x l IH]; intros Hn Hi; cbn [map]; [constructor|].
  apply NoDup_cons_iff in Hn as [Hx Hn]; constructor.
  - intros Hin; apply in_map_iff in Hin as (y & Hy & Hin).
    assert (y = x) as -> by (apply Hi; cbn; auto). contradiction.
  - apply IH; auto; intros; apply Hi; cbn; auto.
Qed.

Lemma ZIP_cons {X Y} (x : X) (y : Y) l1 l2 : ZIP (x :: l1, y :: l2) = (x, y) :: ZIP (l1, l2).
Proof. reflexivity. Qed.

Lemma FRONT_cons2 {X} (a b : X) l : FRONT (a :: b :: l) = a :: FRONT (b :: l).
Proof. reflexivity. Qed.

Lemma LAST_cons2 {X} `{Inhabited X} (a b : X) l : LAST (a :: b :: l) = LAST (b :: l).
Proof. reflexivity. Qed.

Lemma FRONT_snoc {X} (l : list X) x : FRONT (l ++ [x]) = l.
Proof.
  induction l as [|y l IH]; [reflexivity|].
  destruct l as [|z l]; [reflexivity|].
  change ((y :: z :: l) ++ [x]) with (y :: z :: (l ++ [x])); rewrite FRONT_cons2.
  change (z :: l ++ [x]) with ((z :: l) ++ [x]); rewrite IH; reflexivity.
Qed.

Lemma LAST_snoc {X} `{Inhabited X} (l : list X) x : LAST (l ++ [x]) = x.
Proof.
  induction l as [|y l IH]; [reflexivity|].
  destruct l as [|z l]; [reflexivity|].
  change ((y :: z :: l) ++ [x]) with (y :: z :: (l ++ [x])); rewrite LAST_cons2.
  change (z :: l ++ [x]) with ((z :: l) ++ [x]); rewrite IH; reflexivity.
Qed.

Lemma snoc_cases {X} (l : list X) : l = [] \/ exists l' x, l = l' ++ [x].
Proof.
  destruct l as [|y l] using rev_ind; [auto|right; eauto].
Qed.

Lemma SNOC_eq {X} (x : X) l : SNOC x l = l ++ [x].
Proof. induction l as [|y l IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Section UpdateList.
Context {A B : Type} `{EA : EqDecision A}.

Lemma UL_cons (f : A -> B) a b l : UPDATE_LIST f ((a, b) :: l) = UPDATE_LIST ((a =+ b) f) l.
Proof. reflexivity. Qed.

Lemma UL_out l : forall (f : A -> B) z, ~ In z (map fst l) -> UPDATE_LIST f l z = f z.
Proof.
  induction l as [|[a b] l IH]; intros f z H; [reflexivity|].
  rewrite UL_cons, IH by (cbn in H; tauto).
  unfold UPDATE; destruct (decide (a = z)); [subst; cbn in H; tauto|reflexivity].
Qed.

Lemma UL_ext l : forall (f g : A -> B) z, In z (map fst l) -> UPDATE_LIST f l z = UPDATE_LIST g l z.
Proof.
  induction l as [|[a b] l IH]; intros f g z H; [destruct H|].
  rewrite !UL_cons.
  destruct (in_dec (fun x y => decide (x = y)) z (map fst l)) as [Hin|Hin]; [apply IH, Hin|].
  rewrite !UL_out by exact Hin. cbn in H; destruct H as [<-|]; [|contradiction].
  unfold UPDATE; destruct (decide (a = a)); congruence.
Qed.

Lemma UL_in l : forall (f : A -> B) z v, NoDup (map fst l) -> In (z, v) l -> UPDATE_LIST f l z = v.
Proof.
  induction l as [|[a b] l IH]; intros f z v Hn H; [destruct H|].
  cbn [map fst] in Hn; apply NoDup_cons_iff in Hn as [Ha Hn].
  rewrite UL_cons. destruct H as [[= -> ->]|H].
  - rewrite UL_out by exact Ha. unfold UPDATE; destruct (decide (z = z)); congruence.
  - apply IH; auto.
Qed.

End UpdateList.

Section ParsemHelpers.
Context {A : Type} `{EA : EqDecision A}.

Lemma keys_map {B} (g : A * A -> B) (μ : list (A * A)) :
  map fst (map (fun p => (fst p, g p)) μ) = map fst μ.
Proof. induction μ as [|x μ IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma parsem_eq {B} (μ : list (A * A)) (ρ : A -> B) :
  parsem μ ρ = UPDATE_LIST ρ (map (fun p => (fst p, ρ (snd p))) μ).
Proof.
  unfold parsem; f_equal; induction μ as [|[a b] μ IH]; [reflexivity|].
  cbn [map]; rewrite ZIP_cons, IH; reflexivity.
Qed.

Lemma parsem_out {B} (μ : list (A * A)) (ρ : A -> B) z :
  ~ In z (map fst μ) -> parsem μ ρ z = ρ z.
Proof. intros H; rewrite parsem_eq; apply UL_out; rewrite keys_map; exact H. Qed.

Lemma parsem_in {B} (μ : list (A * A)) (ρ : A -> B) z y :
  NoDup (map fst μ) -> In (z, y) μ -> parsem μ ρ z = ρ y.
Proof.
  intros Hn H; rewrite parsem_eq; apply UL_in; [rewrite keys_map; exact Hn|].
  apply (in_map (fun p => (fst p, ρ (snd p)))) in H; exact H.
Qed.

Lemma parsem_perm_gen {B} (l1 l2 : list (A * A)) (ρ : A -> B) :
  NoDup (map fst l1) -> Permutation l1 l2 -> parsem l1 ρ = parsem l2 ρ.
Proof.
  intros Hn Hp; apply functional_extensionality; intros z.
  assert (Hn2 : NoDup (map fst l2)) by (eapply Permutation_NoDup; [apply Permutation_map, Hp|exact Hn]).
  destruct (in_dec (fun x y => decide (x = y)) z (map fst l1)) as [Hin|Hin].
  - apply in_map_iff in Hin as ([z' y] & <- & Hin).
    rewrite (parsem_in _ _ _ y Hn Hin), (parsem_in _ _ _ y Hn2); [reflexivity|].
    eapply Permutation_in; eauto.
  - rewrite !parsem_out; [reflexivity| |exact Hin].
    intros H; apply Hin; eapply Permutation_in; [apply Permutation_map, Permutation_sym, Hp|exact H].
Qed.

End ParsemHelpers.

Section Generic.
Context {A : Type} `{EA : EqDecision A}.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "windmill_cons" *)
Theorem windmill_cons : forall (x : A * A) ls,
  windmill (x :: ls) <-> ~ MEM (FST x) (MAP FST ls) /\ windmill ls.
Proof.
  intros x ls; unfold windmill; cbn [map ALL_DISTINCT]; unfold is_true.
  rewrite andb_true_iff, negb_true_iff, <- not_true_iff_false; reflexivity.
Qed.

Section Paths.
Context `{IA : Inhabited A}.

Lemma path_cons2 (c b' b a : A) p :
  is_true (path ((c, b') :: (b, a) :: p)) <-> b = b' /\ is_true (path ((b, a) :: p)).
Proof. cbn [path]; unfold is_true; rewrite andb_true_iff, bool_decide_spec; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "path_change_start" *)
Theorem path_change_start : forall (y : list (A * A)) z x,
  path (SNOC x y) /\ FST x = FST z -> path (SNOC z y).
Proof.
  induction y as [|[c b'] y IH]; intros [z1 z2] [x1 x2] [Hp Hf]; cbn [FST fst] in Hf; [reflexivity|].
  destruct y as [|[b a] y].
  - cbn [SNOC] in *; apply path_cons2 in Hp as [-> _]; apply path_cons2; subst; split; reflexivity.
  - cbn [SNOC] in *; apply path_cons2 in Hp as [-> Hp]; apply path_cons2; split; [reflexivity|].
    apply (IH (z1, z2) (x1, x2)); cbn [SNOC]; split; [exact Hp|exact Hf].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "path_tail" *)
Theorem path_tail : forall (t : list (A * A)) h, path (h :: t) -> path t.
Proof.
  intros [|[b a] t] [c b'] H; [reflexivity|]; apply path_cons2 in H; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "path_imp_mem" *)
Theorem path_imp_mem : forall (x : A * A) y, path (x :: y) -> ~ NULL y -> MEM (SND x) (MAP FST y).
Proof.
  intros [c b'] [|[b a] y] Hp Hn; [exfalso; apply Hn; reflexivity|].
  apply path_cons2 in Hp as [-> _]; apply MEM_iff; cbn; auto.
Qed.

Lemma path_snd (x : list (A * A)) : path x ->
  forall y, In y (map snd x) -> y = SND (LAST x) \/ In y (map fst (TL x)).
Proof.
  induction x as [|[c b'] x IH]; intros Hp y Hy; [destruct Hy|].
  destruct x as [|[b a] x].
  - cbn in Hy; destruct Hy as [<-|[]]; left; reflexivity.
  - apply path_cons2 in Hp as [-> Hp]. cbn [map snd] in Hy. destruct Hy as [<-|Hy].
    + right; cbn [In TL map fst]; tauto.
    + destruct (IH Hp y Hy) as [E|E].
      * left; rewrite E; reflexivity.
      * right; cbn [TL map fst] in *; cbn [In]; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "path_imp_mem2" *)
Theorem path_imp_mem2 : forall (x : list (A * A)), path x ->
  forall y, MEM y (MAP SND x) /\ y <> SND (LAST x) -> MEM y (MAP FST x).
Proof.
  intros x Hp y [Hm Hne]; apply MEM_iff in Hm; apply MEM_iff.
  destruct (path_snd x Hp y Hm) as [E|E]; [contradiction|].
  destruct x; cbn in *; auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "NoRead_path" *)
Theorem NoRead_path : forall (σ : list (A * A)),
  path σ /\ windmill σ /\ LENGTH σ >= 2 /\ FST (HD σ) <> SND (LAST σ) ->
  ~ MEM (FST (HD σ)) (MAP SND (TL σ)).
Proof.
  intros [|h [|h2 t]] (Hp & Hw & Hl & Hne); cbn [LENGTH] in Hl; try lia.
  cbn [HD TL]; intros Hm; apply MEM_iff in Hm.
  apply path_tail in Hp.
  destruct (path_snd _ Hp _ Hm) as [E|E].
  - apply Hne; exact E.
  - apply windmill_iff in Hw; cbn [map] in Hw; apply NoDup_cons_iff in Hw as [Hw _].
    apply Hw; cbn [TL] in E; cbn; auto.
Qed.

End Paths.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parsem_nil" *)
Theorem parsem_nil : forall {B}, @parsem A _ B [] = combin.I.
Proof. intros B; apply functional_extensionality; intros ρ; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parsem_cons" *)
Theorem parsem_cons : forall (x : A) μ y {B} (ρ : A -> B),
  ~ MEM x (MAP FST μ) -> parsem ((x, y) :: μ) ρ = (x =+ ρ y) (parsem μ ρ).
Proof.
  intros x μ y B ρ Hx; rewrite MEM_iff in Hx; apply functional_extensionality; intros z.
  rewrite !parsem_eq; cbn [map fst snd]; rewrite UL_cons.
  unfold UPDATE at 2; destruct (decide (x = z)) as [<-|Hne].
  - rewrite UL_out by (rewrite keys_map; exact Hx). unfold UPDATE; destruct (decide (x = x)); congruence.
  - destruct (in_dec (fun a b => decide (a = b)) z (map fst μ)) as [Hin|Hin].
    + apply UL_ext; rewrite keys_map; exact Hin.
    + rewrite !UL_out by (rewrite keys_map; exact Hin). unfold UPDATE; destruct (decide (x = z)); congruence.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "independence" *)
Theorem independence : forall {B} μ1 (s d : A) μ2 μ,
  windmill μ /\ μ = μ1 ++ [(d, s)] ++ μ2 ->
  @parsem A _ B μ = parsem ([(d, s)] ++ μ1 ++ μ2).
Proof.
  intros B μ1 s d μ2 μ [Hw ->]; apply functional_extensionality; intros ρ.
  apply parsem_perm_gen; [apply windmill_iff, Hw|].
  cbn [app]; apply Permutation_sym, Permutation_middle.
Qed.

(** HOL's [parsem_perm], with Rocq's [Permutation] for HOL's [PERM] (not
    ported); hence untagged. *)
Theorem parsem_perm : forall {B} (l1 l2 : list (A * A)),
  windmill l1 /\ Permutation l1 l2 -> @parsem A _ B l1 = parsem l2.
Proof.
  intros B l1 l2 [Hw Hp]; apply functional_extensionality; intros ρ.
  apply parsem_perm_gen; [apply windmill_iff, Hw|exact Hp].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parsem_untouched" *)
Theorem parsem_untouched : forall {B} (ρ : A -> B) μ x,
  windmill μ /\ ~ MEM x (MAP FST μ) -> parsem μ ρ x = ρ x.
Proof. intros B ρ μ x [_ H]; rewrite MEM_iff in H; apply parsem_out, H. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parsem_change_env" *)
Theorem parsem_change_env : forall (x : A) μ {B} (ρ1 ρ2 : A -> B),
  (~ MEM x (MAP FST μ) -> ρ1 x = ρ2 x) /\
  MAP (fun p => ρ1 (SND p)) μ = MAP (fun p => ρ2 (SND p)) μ ->
  parsem μ ρ1 x = parsem μ ρ2 x.
Proof.
  intros x μ B ρ1 ρ2 [H1 H2]; rewrite !parsem_eq.
  assert (E : map (fun p => (fst p, ρ1 (snd p))) μ = map (fun p => (fst p, ρ2 (snd p))) μ).
  { clear H1; induction μ as [|p μ IH]; [reflexivity|]; cbn in H2 |- *.
    injection H2 as E1 E2; rewrite E1, IH; auto. }
  rewrite E.
  destruct (in_dec (fun a b => decide (a = b)) x (map fst μ)) as [Hin|Hin].
  - apply UL_ext; rewrite keys_map; exact Hin.
  - rewrite !UL_out by (rewrite keys_map; exact Hin). apply H1; rewrite MEM_iff; exact Hin.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parsem_NoRead" *)
Theorem parsem_NoRead : forall μ (x : A) y {B} (ρ : A -> B),
  ~ MEM x (MAP SND μ) -> parsem ((x, y) :: μ) ρ = parsem μ ((x =+ ρ y) ρ).
Proof.
  intros μ x y B ρ Hx; rewrite MEM_iff in Hx; rewrite !parsem_eq; cbn [map fst snd].
  rewrite UL_cons; f_equal; apply map_ext_in; intros [a b] Hin; cbn [fst snd].
  unfold UPDATE; destruct (decide (x = b)) as [<-|]; [|reflexivity].
  exfalso; apply Hx, (in_map snd _ _ Hin).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parsem_MAP_INJ" *)
Theorem parsem_MAP_INJ : forall {B C} `{EqDecision B} (f : A -> B) (r : B -> C) ms,
  windmill ms /\ INJ f (set (MAP FST ms ++ MAP SND ms)) UNIV ->
  forall x, MEM x (MAP FST ms) -> parsem (MAP (f ## f) ms) r (f x) = parsem ms (fun y => r (f y)) x.
Proof.
  intros B C EB f r ms [Hw [_ Hi]] x Hx; apply MEM_iff in Hx; apply windmill_iff in Hw.
  apply in_map_iff in Hx as ([x' y] & <- & Hin); cbn [fst].
  rewrite (parsem_in _ _ _ y Hw Hin).
  apply parsem_in.
  - rewrite map_map. replace (map (fun p => fst ((f ## f) p)) ms) with (map f (map fst ms))
      by (rewrite map_map; reflexivity).
    apply NoDup_map_inj_on; [exact Hw|].
    intros a b Ha Hb E; apply Hi; [|exact E].
    split; apply IN_set, in_or_app; left; assumption.
  - apply (in_map (f ## f)) in Hin; exact Hin.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "seqsem_append" *)
Theorem seqsem_append : forall {B} (l1 l2 : list (A * A)),
  @seqsem A _ B (l1 ++ l2) = fun ρ => seqsem l2 (seqsem l1 ρ).
Proof.
  intros B l1 l2; apply functional_extensionality; intros ρ; revert ρ.
  induction l1 as [|[d s] l1 IH]; intros ρ; [reflexivity|]; cbn [app seqsem]; apply IH.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "seqsem_move_unchanged" *)
Theorem seqsem_move_unchanged : forall (k : A) ms {B} (r : A -> B),
  ~ MEM k (MAP FST ms) -> seqsem ms r k = r k.
Proof.
  intros k ms B r H; rewrite MEM_iff in H; revert r H; induction ms as [|[d s] ms IH]; intros r H; [reflexivity|].
  cbn [seqsem]; rewrite IH by (cbn in H; tauto).
  unfold UPDATE; destruct (decide (d = k)); [subst; cbn in H; tauto|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "sem_init" *)
Theorem sem_init : forall (μ : list (A * A)) {B}, @sem A _ B (μ, ([], [])) = parsem μ.
Proof.
  intros μ B; apply functional_extensionality; intros ρ; unfold sem.
  rewrite app_nil_r; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "sem_final" *)
Theorem sem_final : forall (τ : list (A * A)) {B}, @sem A _ B ([], ([], τ)) = seqsem (REVERSE τ).
Proof. intros τ B; apply functional_extensionality; intros ρ; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "eqenv_sym" *)
Theorem eqenv_sym : forall {B} (p1 p2 : option A -> B), eqenv p1 p2 -> eqenv p2 p1.
Proof. unfold eqenv; intros B p1 p2 H r Hr; symmetry; auto. Qed.

End Generic.

(** ** The non-deterministic and deterministic step relations *)

(** Solves [Permutation l r] where both sides are built from the same
    lists and elements with [++] and [::]. *)
Ltac perm_solve :=
  apply (Permutation_count_occ (fun a b => decide (a = b))); intros ?x;
  repeat progress (rewrite ?map_app, ?count_occ_app; cbn [count_occ map fst]);
  repeat match goal with |- context [if decide (?a = ?b) then _ else _] =>
    destruct (decide (a = b)) end; lia.

Lemma NoDup_perm {X} (l l' : list X) : Permutation l l' -> NoDup l -> NoDup l'.
Proof. intros; eapply Permutation_NoDup; eauto. Qed.

Lemma NoDup_perm_cons {X} (l l' : list X) a : Permutation l (a :: l') -> NoDup l -> NoDup l'.
Proof. intros Hp Hn; apply (NoDup_perm _ _ Hp) in Hn; inversion Hn; auto. Qed.

Lemma EVERY_MAP_iff {X Y} (P : Y -> bool) (f : X -> Y) l :
  EVERY P (map f l) = true <-> forall x, In x l -> P (f x) = true.
Proof.
  rewrite EVERY_Forall, Forall_forall; split.
  - intros H x Hx; apply H, in_map, Hx.
  - intros H y Hy; apply in_map_iff in Hy as (x & <- & Hx); auto.
Qed.

Section Steps.
Context {A : Type} `{EA : EqDecision A}.

Local Abbreviation mv := (option A * option A)%type.
Local Abbreviation st := (@pstate A).

(** HOL [▷]. *)
(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "step_rules" *)
Inductive step : st -> st -> Prop :=
| step_1 (μ1 : list mv) r μ2 σ τ :
    step (μ1 ++ [(r, r)] ++ μ2, (σ, τ)) (μ1 ++ μ2, (σ, τ))
| step_2 (μ1 : list mv) d s μ2 τ :
    step (μ1 ++ [(d, s)] ++ μ2, ([], τ)) (μ1 ++ μ2, ([(d, s)], τ))
| step_3 (μ1 : list mv) r d μ2 s σ τ :
    step (μ1 ++ [(r, d)] ++ μ2, ([(d, s)] ++ σ, τ)) (μ1 ++ μ2, ([(r, d); (d, s)] ++ σ, τ))
| step_4 (μ : list mv) σ d s τ :
    step (μ, (σ ++ [(d, s)], τ)) (μ, (σ ++ [(d, None)], [(None, s)] ++ τ))
| step_5 (μ : list mv) dn s0 sn σ d0 τ :
    ~ MEM dn (MAP SND μ) -> dn <> s0 ->
    step (μ, ([(dn, sn)] ++ σ ++ [(d0, s0)], τ)) (μ, (σ ++ [(d0, s0)], [(dn, sn)] ++ τ))
| step_6 (μ : list mv) d s τ :
    ~ MEM d (MAP SND μ) ->
    step (μ, ([(d, s)], τ)) (μ, ([], [(d, s)] ++ τ)).

(** HOL [↪]. *)
(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "dstep_rules" *)
Inductive dstep : st -> st -> Prop :=
| dstep_1 (r : option A) μ τ :
    dstep ([(r, r)] ++ μ, ([], τ)) (μ, ([], τ))
| dstep_2 (s d : option A) μ τ :
    s <> d -> dstep ([(d, s)] ++ μ, ([], τ)) (μ, ([(d, s)], τ))
| dstep_3 (μ1 : list mv) d r μ2 s σ τ :
    ~ MEM d (MAP SND μ1) ->
    dstep (μ1 ++ [(r, d)] ++ μ2, ([(d, s)] ++ σ, τ)) (μ1 ++ μ2, ([(r, d); (d, s)] ++ σ, τ))
| dstep_4 (μ : list mv) r s σ d τ :
    ~ MEM r (MAP SND μ) ->
    dstep (μ, ([(r, s)] ++ σ ++ [(d, r)], τ)) (μ, (σ ++ [(d, None)], [(r, s); (None, r)] ++ τ))
| dstep_5 (μ : list mv) dn s0 sn σ d0 τ :
    ~ MEM dn (MAP SND μ) -> dn <> s0 ->
    dstep (μ, ([(dn, sn)] ++ σ ++ [(d0, s0)], τ)) (μ, (σ ++ [(d0, s0)], [(dn, sn)] ++ τ))
| dstep_6 (μ : list mv) d s τ :
    ~ MEM d (MAP SND μ) ->
    dstep (μ, ([(d, s)], τ)) (μ, ([], [(d, s)] ++ τ)).

Lemma wf_iff (μ σ τ : list mv) :
  is_true (wf (μ, (σ, τ))) <->
  NoDup (map fst (μ ++ σ)) /\
  (forall p, In p μ -> is_true (IS_SOME (fst p))) /\
  (forall p, In p μ -> is_true (IS_SOME (snd p))) /\
  (σ <> [] -> forall p, In p (FRONT σ) -> is_true (IS_SOME (snd p))) /\
  (forall p, In p σ -> is_true (IS_SOME (fst p))) /\
  is_true (path σ).
Proof.
  unfold wf, is_true, windmill; rewrite !andb_true_iff, ALL_DISTINCT_iff, !EVERY_MAP_iff.
  assert (E : implb (negb (NULL σ)) (EVERY IS_SOME (MAP SND (FRONT σ))) = true <->
              (σ <> [] -> forall p, In p (FRONT σ) -> IS_SOME (snd p) = true)).
  { destruct σ; cbn [NULL negb implb]; [split; [congruence|auto]|].
    rewrite EVERY_MAP_iff; split; auto; intros H; apply H; discriminate. }
  rewrite E; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "wf_init" *)
Theorem wf_init : forall μ : list mv,
  windmill μ /\ EVERY IS_SOME (MAP FST μ) /\ EVERY IS_SOME (MAP SND μ) -> wf (μ, ([], [])).
Proof.
  intros μ (H1 & H2 & H3); unfold wf; rewrite app_nil_r, H1, H2, H3; reflexivity.
Qed.

Ltac in_tac := intros ?p ?Hp; repeat match goal with H : forall q, In q _ -> _ |- _ => apply H end;
  rewrite ?in_app_iff in *; cbn [In] in *; tauto.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "wf_step" *)
Theorem wf_step : forall s1 s2 : st, step s1 s2 -> wf s1 -> wf s2.
Proof.
  intros s1 s2 Hs; destruct Hs; rewrite !wf_iff;
    intros (Hn & Hfm & Hsm & Hfr & Hfs & Hp); rewrite ?map_app in Hn |- *; cbn [map app fst] in Hn |- *.
  - (* 1 *)
    split; [rewrite <- ?app_assoc in *; cbn [app] in *; eapply NoDup_remove_1; exact Hn|].
    repeat split; auto; intros p Hp'; [apply Hfm|apply Hsm]; rewrite !in_app_iff in *; cbn [In]; tauto.
  - (* 2 *)
    split; [eapply NoDup_perm; [|exact Hn]; perm_solve|].
    split; [intros p Hp'; apply Hfm; rewrite !in_app_iff in *; cbn [In]; tauto|].
    split; [intros p Hp'; apply Hsm; rewrite !in_app_iff in *; cbn [In]; tauto|].
    split; [intros _ p []|].
    split; [intros p [<-|[]]; apply (Hfm (d, s)); rewrite !in_app_iff; cbn; tauto|reflexivity].
  - (* 3 *)
    split; [eapply NoDup_perm; [|exact Hn]; perm_solve|].
    split; [intros p Hp'; apply Hfm; rewrite !in_app_iff in *; cbn [In]; tauto|].
    split; [intros p Hp'; apply Hsm; rewrite !in_app_iff in *; cbn [In]; tauto|].
    split.
    { intros _ p Hp'; rewrite FRONT_cons2 in Hp'; destruct Hp' as [<-|Hp'].
      - apply (Hsm (r, d)); rewrite !in_app_iff; cbn; tauto.
      - apply Hfr; [discriminate|exact Hp']. }
    split; [intros p [<-|Hp']; [apply (Hfm (r, d)); rewrite !in_app_iff; cbn; tauto|apply Hfs, Hp']|].
    apply path_cons2; split; [reflexivity|exact Hp].
  - (* 4 *)
    split; [exact Hn|]. split; [exact Hfm|]. split; [exact Hsm|].
    split; [intros _; rewrite FRONT_snoc; rewrite FRONT_snoc in Hfr; apply Hfr; destruct σ; discriminate|].
    split; [intros p Hp'; rewrite in_app_iff in Hp'; destruct Hp' as [Hp'|[<-|[]]]; [apply Hfs, in_or_app; auto|apply (Hfs (d, s)), in_or_app; right; left; reflexivity]|].
    rewrite <- SNOC_eq in Hp |- *; eapply path_change_start; split; [exact Hp|reflexivity].
  - (* 5 *)
    split; [rewrite <- ?app_assoc in *; cbn [app] in *;
            refine (NoDup_perm_cons _ _ dn _ Hn); perm_solve|].
    split; [exact Hfm|]. split; [exact Hsm|].
    split; [intros _ p Hp'; rewrite FRONT_snoc in Hp'; apply Hfr; [discriminate|];
            rewrite app_assoc, FRONT_snoc; apply in_or_app; right; exact Hp'|].
    split; [intros p Hp'; apply Hfs; right; exact Hp'|].
    eapply path_tail; exact Hp.
  - (* 6 *)
    split; [rewrite app_nil_r; eapply NoDup_app_remove_r; exact Hn|]. repeat split; auto; first [intros _ ? [] | intros ? [] | reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "wf_steps" *)
Theorem wf_steps : forall s1 s2 : st, wf s1 /\ RTC step s1 s2 -> wf s2.
Proof. apply RTC_lifts_invariants; intros x y [Hx Hs]; eapply wf_step; eauto. Qed.

End Steps.

Lemma splitAtPki_first {X B} (l : list X) : forall (P : N -> X -> bool) (k : list X -> list X -> B),
  (forall i j x, P i x = P j x) ->
  exists t1 t2, l = t1 ++ t2 /\ splitAtPki P k l = k t1 t2 /\
    (forall x, In x t1 -> P 0 x = false) /\
    match t2 with [] => True | h :: _ => P 0 h = true end.
Proof.
  induction l as [|h t IH]; intros P k HP; cbn [splitAtPki].
  - exists [], []; repeat split; auto; intros x [].
  - destruct (P 0 h) eqn:Eh.
    + exists [], (h :: t); repeat split; auto; intros x [].
    + destruct (IH (fun i => P (SUC i)) (fun p s => k (h :: p) s)) as (t1 & t2 & -> & E & H1 & H2);
        [intros; apply HP|].
      exists (h :: t1), t2; split; [reflexivity|]; split; [exact E|]; split.
      * intros x [<-|Hx]; [exact Eh|rewrite (HP 0 (SUC 0)); apply H1, Hx].
      * destruct t2; [trivial|rewrite (HP 0 (SUC 0)); exact H2].
Qed.

Section Steps2.
Context {A : Type} `{EA : EqDecision A}.

Local Abbreviation mv := (option A * option A)%type.
Local Abbreviation st := (@pstate A).

Lemma seqsem_snoc {B} (τ : list mv) d s (ρ : option A -> B) :
  seqsem (REVERSE ([(d, s)] ++ τ)) ρ = (d =+ seqsem (REVERSE τ) ρ s) (seqsem (REVERSE τ) ρ).
Proof. cbn [app rev]; rewrite seqsem_append; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "step_sem" *)
Theorem step_sem : forall {B} (s1 s2 : st), step s1 s2 -> wf s1 ->
  forall ρ : option A -> B, eqenv (sem s1 ρ) (sem s2 ρ).
Proof.
  intros B s1 s2 Hs; destruct Hs; rewrite !wf_iff;
    intros (Hn & Hfm & Hsm & Hfr & Hfs & Hp) ρ; unfold sem; cbv beta iota.
  - (* 1 *)
    set (ρ' := seqsem (REVERSE τ) ρ); intros z _.
    assert (Hn' : NoDup (map fst ((r, r) :: (μ1 ++ μ2) ++ σ))).
    { eapply NoDup_perm; [|exact Hn]; perm_solve. }
    rewrite (parsem_perm_gen _ ((r, r) :: (μ1 ++ μ2) ++ σ)); [|exact Hn|perm_solve].
    cbn [map fst] in Hn'; apply NoDup_cons_iff in Hn' as [Hr _].
    rewrite parsem_cons by (rewrite MEM_iff; exact Hr).
    unfold UPDATE; destruct (decide (r = z)) as [<-|]; [|reflexivity].
    symmetry; apply parsem_out, Hr.
  - (* 2 *)
    rewrite (parsem_perm_gen _ ((μ1 ++ μ2) ++ [(d, s)])); [intros z _; reflexivity|exact Hn|perm_solve].
  - (* 3 *)
    rewrite (parsem_perm_gen _ ((μ1 ++ μ2) ++ [(r, d); (d, s)] ++ σ)); [intros z _; reflexivity|exact Hn|perm_solve].
  - (* 4 *)
    rewrite seqsem_snoc; set (ρ' := seqsem (REVERSE τ) ρ); intros z Hz.
    assert (Hk : map fst (μ ++ σ ++ [(d, None)]) = map fst (μ ++ σ ++ [(d, s)]))
      by (rewrite !map_app; reflexivity).
    assert (Hfr' : forall p, In p σ -> is_true (IS_SOME (snd p))).
    { intros p Hp'; apply Hfr; [destruct σ; discriminate|]; rewrite FRONT_snoc; exact Hp'. }
    destruct (in_dec (fun a b => decide (a = b)) z (map fst (μ ++ σ ++ [(d, s)]))) as [Hin|Hin].
    + apply in_map_iff in Hin as ([z' y] & Ez & Hin); cbn [fst] in Ez; subst z'.
      rewrite (parsem_in _ _ _ y Hn Hin).
      apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|[[= <- <-]|[]]]].
      * rewrite (parsem_in _ _ _ y); [|rewrite Hk; exact Hn|apply in_or_app; left; exact Hin].
        unfold UPDATE; destruct (decide (None = y)) as [<-|]; [|reflexivity].
        specialize (Hsm _ Hin); discriminate.
      * rewrite (parsem_in _ _ _ y); [|rewrite Hk; exact Hn|apply in_or_app; right; apply in_or_app; left; exact Hin].
        unfold UPDATE; destruct (decide (None = y)) as [<-|]; [|reflexivity].
        specialize (Hfr' _ Hin); discriminate.
      * rewrite (parsem_in _ _ _ None); [|rewrite Hk; exact Hn|apply in_or_app; right; apply in_or_app; right; left; reflexivity].
        unfold UPDATE; destruct (decide (None = None)); congruence.
    + rewrite !parsem_out; [| rewrite Hk; exact Hin | exact Hin].
      unfold UPDATE; destruct (decide (None = z)) as [<-|]; [discriminate|reflexivity].
  - (* 5 *)
    rewrite seqsem_snoc; set (ρ' := seqsem (REVERSE τ) ρ).
    rewrite (parsem_perm_gen _ ((dn, sn) :: μ ++ σ ++ [(d0, s0)])); [|exact Hn|perm_solve].
    rewrite parsem_NoRead; [intros z _; reflexivity|].
    rewrite MEM_iff, map_app, in_app_iff; intros [Hm|Hm]; [apply H; rewrite MEM_iff; exact Hm|].
    refine (NoRead_path ((dn, sn) :: σ ++ [(d0, s0)]) _ _).
    + split; [exact Hp|]. split; [apply windmill_iff; rewrite map_app in Hn; eapply NoDup_app_remove_l; exact Hn|].
      split; [cbn [LENGTH]; rewrite LENGTH_app; cbn [LENGTH]; lia|].
      rewrite app_comm_cons, LAST_snoc; exact H0.
    + apply MEM_iff; exact Hm.
  - (* 6 *)
    rewrite seqsem_snoc; set (ρ' := seqsem (REVERSE τ) ρ).
    rewrite (parsem_perm_gen _ ((d, s) :: μ ++ [])); [|exact Hn|perm_solve].
    rewrite parsem_NoRead; [intros z _; reflexivity|].
    rewrite app_nil_r; exact H.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "steps_sem" *)
Theorem steps_sem : forall {B} (s1 s2 : st), RTC step s1 s2 /\ wf s1 ->
  forall ρ : option A -> B, eqenv (sem s1 ρ) (sem s2 ρ).
Proof.
  intros B s1 s2 [H Hw]; induction H as [x|x y z Hxy Hyz IH]; intros ρ r Hr; [reflexivity|].
  rewrite (step_sem _ _ Hxy Hw ρ r Hr); apply IH; [eapply wf_step; eauto|exact Hr].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "steps_correct" *)
Theorem steps_correct : forall {B} (μ τ : list mv),
  windmill μ /\ EVERY IS_SOME (MAP FST μ) /\ EVERY IS_SOME (MAP SND μ) /\
  RTC step (μ, ([], [])) ([], ([], τ)) ->
  forall ρ : option A -> B, eqenv (parsem μ ρ) (seqsem (REVERSE τ) ρ).
Proof.
  intros B μ τ (H1 & H2 & H3 & H4) ρ.
  rewrite <- sem_init, <- sem_final; apply steps_sem; split; [exact H4|].
  apply wf_init; auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "dstep_step" *)
Theorem dstep_step : forall s1 s2 : st, dstep s1 s2 -> wf s1 -> RTC step s1 s2.
Proof.
  intros s1 s2 Hs Hw; destruct Hs.
  - apply RTC_SINGLE; exact (step_1 [] r μ [] τ).
  - apply RTC_SINGLE; exact (step_2 [] d s μ τ).
  - apply RTC_SINGLE; exact (step_3 μ1 r d μ2 s σ τ).
  - apply wf_iff in Hw as (_ & _ & _ & _ & Hfs & _).
    assert (Hr : r <> None).
    { intros ->; specialize (Hfs (None, s) (or_introl eq_refl)); discriminate. }
    eapply rtc_step; [exact (step_4 μ ([(r, s)] ++ σ) d r τ)|].
    apply RTC_SINGLE; exact (step_5 μ r None s σ d ([(None, r)] ++ τ) H Hr).
  - apply RTC_SINGLE; exact (step_5 μ dn s0 sn σ d0 τ H H0).
  - apply RTC_SINGLE; exact (step_6 μ d s τ H).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "dsteps_steps" *)
Theorem dsteps_steps : forall s1 s2 : st, RTC dstep s1 s2 -> wf s1 -> RTC step s1 s2.
Proof.
  intros s1 s2 H; induction H as [x|x y z Hxy Hyz IH]; intros Hw; [apply rtc_refl|].
  pose proof (dstep_step _ _ Hxy Hw) as H1.
  apply (fun H2 => RTC_RTC _ _ _ H1 _ H2), IH, (wf_steps x); split; assumption.
Qed.

Lemma NoRead_of_split (t1 : list mv) d :
  (forall x, In x t1 -> bool_decide (SND x = d) = false) -> ~ MEM d (MAP SND t1).
Proof.
  intros H Hm; apply MEM_iff, in_map_iff in Hm as (x & Ex & Hx).
  specialize (H x Hx); rewrite (proj2 (bool_decide_spec _) Ex) in H; discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "fstep_dstep" *)
Theorem fstep_dstep : forall s : st, (forall τ, s <> ([], ([], τ))) -> dstep s (fstep s).
Proof.
  intros [μ [σ τ]] Hs; destruct σ as [|[d s] b].
  - destruct μ as [|[d s] t]; [exfalso; apply (Hs τ); reflexivity|].
    unfold fstep; cbv beta iota.
    destruct (bool_decide (s = d)) eqn:E.
    + apply bool_decide_spec in E; subst; exact (dstep_1 d t τ).
    + apply (dstep_2 s d t τ); intros Esd; apply (proj2 (bool_decide_spec _)) in Esd; congruence.
  - assert (Hgen : forall t : list mv, dstep (t, ((d, s) :: b, τ)) (fstep (t, ((d, s) :: b, τ)))).
    2: exact (Hgen μ).
    intros t; replace (fstep (t, ((d, s) :: b, τ))) with
      (splitAtPki (fun i (p : mv) => bool_decide (SND p = d))
        (fun t1 rt2 =>
           match rt2 with
           | rd :: t2 => (t1 ++ t2, (rd :: (d, s) :: b, τ))
           | [] =>
               if NULL b then (t, ([], (d, s) :: τ))
               else
                 let '(b', (d', s')) := (FRONT b, LAST b) in
                 if bool_decide (s' = d) then (t, (SNOC (d', None) b', (d, s) :: (None, d) :: τ))
                 else (t, (b, (d, s) :: τ))
           end) t) by (destruct t as [|[] t]; reflexivity).
    match goal with |- dstep _ (splitAtPki ?P ?k ?l) =>
      destruct (splitAtPki_first l P k (fun _ _ _ => eq_refl)) as (t1 & t2 & Ht & E & H1 & H2);
      rewrite E end.
    apply NoRead_of_split in H1.
    destruct t2 as [|[r d1] t2].
    + rewrite app_nil_r in Ht; subst t1. destruct (snoc_cases b) as [->|(b' & [d' s'] & ->)].
      * exact (dstep_6 t d s τ H1).
      * replace (NULL (b' ++ [(d', s')])) with false by (destruct b'; reflexivity).
        rewrite FRONT_snoc, LAST_snoc; cbv beta iota.
        destruct (bool_decide (s' = d)) eqn:E2.
        -- apply bool_decide_spec in E2; subst s'; rewrite SNOC_eq.
           exact (dstep_4 t d s b' d' τ H1).
        -- apply (dstep_5 t d s' s b' d' τ H1); intros Ed; subst; rewrite (proj2 (bool_decide_spec _) eq_refl) in E2; discriminate.
    + apply bool_decide_spec in H2; cbn [SND snd] in H2; subst d1 t.
      exact (dstep_3 t1 d r t2 s b τ H1).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "pmov_dsteps" *)
Theorem pmov_dsteps : forall s : st, RTC dstep s (pmov s).
Proof.
  intros s; induction s as [s IH] using (well_founded_induction pmov_wf).
  destruct s as [[|m μ] [[|x σ] τ]]; rewrite pmov_def; cbv beta iota; [apply rtc_refl|..];
    (eapply rtc_step; [apply fstep_dstep; intros ? [=]|apply IH, fstep_dec; reflexivity]).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "pmov_final" *)
Theorem pmov_final : forall s : st, exists τ, pmov s = ([], ([], τ)).
Proof.
  intros s; induction s as [s IH] using (well_founded_induction pmov_wf).
  destruct s as [[|m μ] [[|x σ] τ]]; rewrite pmov_def; cbv beta iota; [eauto|..];
    (apply IH, fstep_dec; reflexivity).
Qed.

Lemma init_wf (xs : list (A * A)) :
  windmill xs -> wf (MAP (fun '(x, y) => (Some x, Some y)) xs, ([], [])).
Proof.
  intros Hw; apply wf_init; split; [|split].
  - apply windmill_iff in Hw; apply windmill_iff.
    replace (map fst (map (fun '(x, y) => (Some x, Some y)) xs)) with (map (@Some A) (map fst xs))
      by (rewrite !map_map; apply map_ext; intros []; reflexivity).
    apply NoDup_map_inj_on; [exact Hw|intros a b _ _ [=]; auto].
  - apply EVERY_MAP_iff; intros p Hp; apply in_map_iff in Hp as ([a b] & <- & _); reflexivity.
  - apply EVERY_MAP_iff; intros p Hp; apply in_map_iff in Hp as ([a b] & <- & _); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parmove_correct" *)
Theorem parmove_correct : forall (xs : list (A * A)), windmill xs ->
  forall {B} (ρ : option A -> B),
    eqenv (seqsem (parmove xs) ρ) (parsem (MAP (fun '(x, y) => (Some x, Some y)) xs) ρ).
Proof.
  intros xs Hw B ρ; unfold parmove.
  set (μ := MAP (fun '(x, y) => (Some x, Some y)) xs).
  destruct (pmov_final (μ, ([], []))) as [τ Hτ].
  pose proof (pmov_dsteps (μ, ([], []))) as Hd; rewrite Hτ in Hd |- *; cbn [SND snd].
  pose proof (init_wf xs Hw) as Hwf.
  apply dsteps_steps in Hd; [|exact Hwf].
  apply eqenv_sym; apply wf_iff in Hwf as (Hn & Hfm & Hsm & _).
  apply steps_correct; repeat split; [apply windmill_iff; rewrite app_nil_r in Hn; exact Hn
    |apply EVERY_MAP_iff; intros; apply Hfm; auto|apply EVERY_MAP_iff; intros; apply Hsm; auto|exact Hd].
Qed.

(** ** The compiler does not invent new moves *)

Ltac list_in_tac :=
  repeat progress (rewrite ?map_app, ?in_app_iff in *; cbn [map fst snd In app] in * );
  intuition congruence.

Lemma dstep_fst_sub (s1 s2 : st) : dstep s1 s2 -> forall x,
  In (Some x) (map fst (FST s2 ++ FST (SND s2) ++ SND (SND s2))) ->
  In (Some x) (map fst (FST s1 ++ FST (SND s1) ++ SND (SND s1))).
Proof. intros H x Hx; destruct H; cbn [FST SND fst snd] in *; list_in_tac. Qed.

Lemma dstep_snd_sub (s1 s2 : st) : dstep s1 s2 -> forall x,
  In (Some x) (map snd (FST s2 ++ FST (SND s2) ++ SND (SND s2))) ->
  In (Some x) (map snd (FST s1 ++ FST (SND s1) ++ SND (SND s1))).
Proof. intros H x Hx; destruct H; cbn [FST SND fst snd] in *; list_in_tac. Qed.

Lemma dsteps_sub (g : mv -> option A) (s1 s2 : st) :
  (forall s1 s2 : st, dstep s1 s2 -> forall x,
     In (Some x) (map g (FST s2 ++ FST (SND s2) ++ SND (SND s2))) ->
     In (Some x) (map g (FST s1 ++ FST (SND s1) ++ SND (SND s1)))) ->
  RTC dstep s1 s2 -> forall x,
  In (Some x) (map g (FST s2 ++ FST (SND s2) ++ SND (SND s2))) ->
  In (Some x) (map g (FST s1 ++ FST (SND s1) ++ SND (SND s1))).
Proof. intros Hg H; induction H; eauto. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "MEM_MAP_FST_SND_SND_pmov" *)
Theorem MEM_MAP_FST_SND_SND_pmov : forall (p : st) x,
  MEM (Some x) (MAP FST (SND (SND (pmov p)))) ->
  MEM (Some x) (MAP FST (FST p ++ FST (SND p) ++ SND (SND p))).
Proof.
  intros p x H; apply MEM_iff in H; apply MEM_iff.
  apply (dsteps_sub fst p (pmov p) dstep_fst_sub (pmov_dsteps p)).
  destruct (pmov_final p) as [τ E]; rewrite E in H |- *; exact H.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "MEM_MAP_SND_SND_SND_pmov" *)
Theorem MEM_MAP_SND_SND_SND_pmov : forall (p : st) x,
  MEM (Some x) (MAP SND (SND (SND (pmov p)))) ->
  MEM (Some x) (MAP SND (FST p ++ FST (SND p) ++ SND (SND p))).
Proof.
  intros p x H; apply MEM_iff in H; apply MEM_iff.
  apply (dsteps_sub snd p (pmov p) dstep_snd_sub (pmov_dsteps p)).
  destruct (pmov_final p) as [τ E]; rewrite E in H |- *; exact H.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "MEM_MAP_FST_parmove" *)
Theorem MEM_MAP_FST_parmove : forall (x : A) mvs,
  MEM (Some x) (MAP FST (parmove mvs)) -> MEM x (MAP FST mvs).
Proof.
  intros x mvs H; unfold parmove in H.
  apply MEM_iff in H; rewrite map_rev, <- in_rev in H; apply MEM_iff in H.
  apply MEM_MAP_FST_SND_SND_pmov, MEM_iff in H; cbn [FST SND fst snd] in H.
  rewrite !app_nil_r, map_map, in_map_iff in H; destruct H as ([a b] & [= ->] & Hin).
  apply MEM_iff, in_map_iff; exists (x, b); auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "MEM_MAP_SND_parmove" *)
Theorem MEM_MAP_SND_parmove : forall (x : A) mvs,
  MEM (Some x) (MAP SND (parmove mvs)) -> MEM x (MAP SND mvs).
Proof.
  intros x mvs H; unfold parmove in H.
  apply MEM_iff in H; rewrite map_rev, <- in_rev in H; apply MEM_iff in H.
  apply MEM_MAP_SND_SND_SND_pmov, MEM_iff in H; cbn [FST SND fst snd] in H.
  rewrite !app_nil_r, map_map, in_map_iff in H; destruct H as ([a b] & [= ->] & Hin).
  apply MEM_iff, in_map_iff; exists (a, x); auto.
Qed.

(** ** The compiler does not use uninitialised temporaries *)

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "not_use_temp_before_assign_append" *)
Theorem not_use_temp_before_assign_append : forall l1 l2 : list mv,
  not_use_temp_before_assign (l1 ++ l2) <->
  not_use_temp_before_assign l1 /\
  (EVERY IS_SOME (MAP FST l1) -> not_use_temp_before_assign l2).
Proof.
  induction l1 as [|[d [s|]] l1 IH]; intros l2; cbn [app map EVERY].
  - split; [intros H; split; auto|intros [_ H]; apply H; reflexivity].
  - destruct d as [d|]; cbn [not_use_temp_before_assign FST fst IS_SOME andb].
    + apply IH.
    + split; [intros _; split; [reflexivity|discriminate]|reflexivity].
  - destruct d; cbn [not_use_temp_before_assign]; split; [discriminate|intros [H _]; exact H|discriminate|intros [H _]; exact H].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "not_use_temp_before_assign_insert" *)
Theorem not_use_temp_before_assign_insert : forall (x y : A) (l1 l2 : list mv),
  not_use_temp_before_assign (l1 ++ l2) ->
  not_use_temp_before_assign (l1 ++ [(Some x, Some y)] ++ l2).
Proof.
  intros x y l1 l2; rewrite !not_use_temp_before_assign_append; intros [H1 H2]; split; [exact H1|].
  intros H; split; [reflexivity|intros _; exact (H2 H)].
Qed.

Lemma find_index_shift {X} `{EqDecision X} (y : X) l : forall n,
  find_index y l (n + 1) = option_map (fun i => i + 1) (find_index y l n).
Proof.
  induction l as [|x l IH]; intros n; cbn [find_index]; [reflexivity|].
  destruct (decide (x = y)); [reflexivity|apply IH].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "not_use_temp_before_assign_thm" *)
Theorem not_use_temp_before_assign_thm : forall ls : list mv,
  not_use_temp_before_assign ls <->
  (forall i, find_index None (MAP SND ls) 0 = Some i ->
     exists j, find_index None (MAP FST ls) 0 = Some j /\ j < i).
Proof.
  induction ls as [|[d s] ls IH]; cbn [map find_index FST SND fst snd].
  - split; [discriminate|reflexivity].
  - destruct s as [s|]; [destruct d as [d|]|].
    + cbn [not_use_temp_before_assign]; rewrite IH.
      destruct (decide (Some s = None)) as [|_]; [discriminate|].
      destruct (decide (Some d = None)) as [|_]; [discriminate|].
      replace 1 with (0 + 1) by reflexivity; rewrite !find_index_shift.
      split.
      * intros H i Hi; destruct (find_index None (MAP SND ls) 0) as [i'|] eqn:E; [|discriminate].
        cbn in Hi; injection Hi as <-. destruct (H i' eq_refl) as (j & Hj & Hlt).
        exists (j + 1); rewrite Hj; split; [reflexivity|lia].
      * intros H i Hi; specialize (H (i + 1)); rewrite Hi in H; destruct (H eq_refl) as (j & Hj & Hlt).
        destruct (find_index None (MAP FST ls) 0) as [j'|]; [|discriminate].
        cbn in Hj; injection Hj as <-; exists j'; split; [reflexivity|lia].
    + cbn [not_use_temp_before_assign]; split; [|reflexivity]; intros _ i Hi.
      destruct (decide (Some s = None)) as [|_]; [discriminate|].
      destruct (decide (@None A = None)) as [_|]; [|congruence].
      exists 0; split; [reflexivity|].
      replace 1 with (0 + 1) in Hi by reflexivity; rewrite find_index_shift in Hi.
      destruct (find_index None (MAP SND ls) 0); cbn in Hi; [injection Hi as <-; lia|discriminate].
    + cbn [not_use_temp_before_assign]; split; [destruct d; discriminate|].
      destruct (decide (@None A = None)) as [_|]; [|congruence].
      intros H; destruct (H 0 eq_refl) as (j & _ & Hj); lia.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "step_not_use_temp_before_assign" *)
Theorem step_not_use_temp_before_assign : forall s1 s2 : st, step s1 s2 ->
  wf s1 /\ not_use_temp_before_assign (REVERSE (FST (SND s1) ++ SND (SND s1))) ->
  not_use_temp_before_assign (REVERSE (FST (SND s2) ++ SND (SND s2))).
Proof.
  intros s1 s2 Hs; destruct Hs; rewrite wf_iff; intros [(Hn & Hfm & Hsm & Hfr & Hfs & Hp) Hu];
    cbn [FST SND fst snd] in *.
  - exact Hu.
  - assert (Hd := Hfm (d, s)); assert (Hs := Hsm (d, s)); cbn [fst snd] in *.
    destruct d as [d|]; [|discriminate Hd; apply in_or_app; right; left; reflexivity].
    destruct s as [s|]; [|discriminate Hs; apply in_or_app; right; left; reflexivity].
    cbn [app rev]; apply not_use_temp_before_assign_append; split; [exact Hu|reflexivity].
  - assert (Hd := Hsm (r, d)); assert (Hr := Hfm (r, d)); cbn [fst snd] in *.
    destruct d as [d|]; [|discriminate Hd; apply in_or_app; right; left; reflexivity].
    destruct r as [r|]; [|discriminate Hr; apply in_or_app; right; left; reflexivity].
    cbn [app rev] in *.
    apply not_use_temp_before_assign_append; split; [|reflexivity].
    exact Hu.
  - rewrite !rev_app_distr in *; cbn [rev app] in *; rewrite <- !app_assoc in *; cbn [app] in *.
    apply not_use_temp_before_assign_append in Hu as [H1 H2].
    apply not_use_temp_before_assign_append; split; [exact H1|]; intros He; specialize (H2 He).
    destruct s; [reflexivity|destruct d; discriminate].
  - assert (Hdn := Hfs (dn, sn) (or_introl eq_refl)).
    assert (Hsn : is_true (IS_SOME (snd (dn, sn)))).
    { apply Hfr; [discriminate|]. rewrite app_assoc, FRONT_snoc; left; reflexivity. }
    cbn [fst snd] in *.
    destruct dn as [dn|]; [|discriminate]. destruct sn as [sn|]; [|discriminate].
    rewrite !rev_app_distr in *; cbn [rev app] in *; rewrite <- !app_assoc in *; cbn [app] in *.
    apply (not_use_temp_before_assign_insert dn sn (REVERSE τ) ((d0, s0) :: REVERSE σ)).
    rewrite app_comm_cons, app_assoc in Hu; apply not_use_temp_before_assign_append in Hu as [Hu _].
    exact Hu.
  - exact Hu.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "steps_not_use_temp_before_assign" *)
Theorem steps_not_use_temp_before_assign : forall s1 s2 : st,
  (fun s1 : st => wf s1 /\ not_use_temp_before_assign (REVERSE (FST (SND s1) ++ SND (SND s1)))) s1 /\
  RTC step s1 s2 ->
  (fun s1 : st => wf s1 /\ not_use_temp_before_assign (REVERSE (FST (SND s1) ++ SND (SND s1)))) s2.
Proof.
  apply RTC_lifts_invariants; intros x y [Hx Hs]; split;
    [eapply wf_step; [exact Hs|apply Hx]|eapply step_not_use_temp_before_assign; eauto].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "pmov_not_use_temp_before_assign" *)
Theorem pmov_not_use_temp_before_assign : forall (p : st) {C} (i : C),
  wf p /\ not_use_temp_before_assign (REVERSE (FST (SND p) ++ SND (SND p))) ->
  not_use_temp_before_assign (REVERSE (FST (SND (pmov p)) ++ SND (SND (pmov p)))).
Proof.
  intros p C i [Hw H].
  apply (steps_not_use_temp_before_assign p (pmov p)); split; [split; assumption|].
  apply dsteps_steps; [apply pmov_dsteps|exact Hw].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parmove_not_use_temp_before_assign" *)
Theorem parmove_not_use_temp_before_assign : forall mvs : list (A * A), windmill mvs ->
  match find_index None (MAP SND (parmove mvs)) 0 with
  | None => True
  | Some i =>
      match find_index None (MAP FST (parmove mvs)) 0 with
      | None => False
      | Some j => ~ (i <= j)
      end
  end.
Proof.
  intros mvs Hw.
  assert (H : not_use_temp_before_assign (parmove mvs)).
  { unfold parmove.
    set (p := (MAP (fun '(x, y) => (Some x, Some y)) mvs, ([], [])) : st).
    destruct (pmov_final p) as [τ E].
    pose proof (pmov_not_use_temp_before_assign p tt) as Hp; rewrite E in Hp |- *; apply Hp.
    split; [apply init_wf, Hw|reflexivity]. }
  pose proof (proj1 (not_use_temp_before_assign_thm (parmove mvs)) H) as H'; clear H; rename H' into H.
  destruct (find_index None (MAP SND (parmove mvs)) 0) as [i|]; [|exact Logic.I].
  destruct (H i eq_refl) as (j & -> & Hj); lia.
Qed.

(** ** The compiler preserves all-distinct variables *)

Lemma NoDup_perm_sub {X} (l1 l l2 : list X) : Permutation l1 (l ++ l2) -> NoDup l1 -> NoDup l2.
Proof. intros Hp Hn; eapply NoDup_app_remove_l, NoDup_perm; eauto. Qed.

Lemma IS_SOME_None {X} : @IS_SOME X None = false.
Proof. reflexivity. Qed.

Ltac filt_norm :=
  repeat progress (rewrite ?map_app, ?filter_app in *; cbn [map fst snd filter app] in * );
  rewrite ?IS_SOME_None in *; cbn iota in *;
  repeat match goal with |- context [if IS_SOME ?a then _ else _] => destruct (IS_SOME a) end.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "ALL_DISTINCT_step" *)
Theorem ALL_DISTINCT_step : forall s1 s2 : st, step s1 s2 ->
  ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST s1 ++ FST (SND s1) ++ SND (SND s1)))) ->
  ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST s2 ++ FST (SND s2) ++ SND (SND s2)))).
Proof.
  intros s1 s2 Hs H; apply ALL_DISTINCT_iff in H; apply ALL_DISTINCT_iff.
  destruct Hs; cbn [FST SND fst snd] in *.
  - refine (NoDup_perm_sub _ (FILTER IS_SOME [r]) _ _ H); filt_norm; perm_solve.
  - refine (NoDup_perm_sub _ [] _ _ H); filt_norm; perm_solve.
  - refine (NoDup_perm_sub _ [] _ _ H); filt_norm; perm_solve.
  - refine (NoDup_perm_sub _ [] _ _ H); filt_norm; perm_solve.
  - refine (NoDup_perm_sub _ [] _ _ H); filt_norm; perm_solve.
  - refine (NoDup_perm_sub _ [] _ _ H); filt_norm; perm_solve.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "ALL_DISTINCT_steps" *)
Theorem ALL_DISTINCT_steps : forall s1 s2 : st,
  (fun s1 : st => ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST s1 ++ FST (SND s1) ++ SND (SND s1))))) s1 /\
  RTC step s1 s2 ->
  (fun s1 : st => ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST s1 ++ FST (SND s1) ++ SND (SND s1))))) s2.
Proof. apply RTC_lifts_invariants; intros x y [Hx Hs]; eapply ALL_DISTINCT_step; eauto. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "ALL_DISTINCT_pmov" *)
Theorem ALL_DISTINCT_pmov : forall p : st,
  wf p /\ ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST p ++ FST (SND p) ++ SND (SND p)))) ->
  ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST (pmov p) ++ FST (SND (pmov p)) ++ SND (SND (pmov p))))).
Proof.
  intros p [Hw H]; apply (ALL_DISTINCT_steps p (pmov p)); split; [exact H|].
  apply dsteps_steps; [apply pmov_dsteps|exact Hw].
Qed.

Lemma filter_rev {X} (f : X -> bool) l : filter f (rev l) = rev (filter f l).
Proof.
  induction l as [|x l IH]; [reflexivity|]; cbn [rev filter].
  rewrite filter_app, IH; cbn [filter]; destruct (f x); [reflexivity|apply app_nil_r].
Qed.

Lemma filter_all {X} (f : X -> bool) l : (forall x, In x l -> f x = true) -> filter f l = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]; cbn [filter].
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity|intros; apply H; right; auto].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "ALL_DISTINCT_parmove" *)
Theorem ALL_DISTINCT_parmove : forall mvs : list (A * A),
  ALL_DISTINCT (MAP FST mvs) -> ALL_DISTINCT (FILTER IS_SOME (MAP FST (parmove mvs))).
Proof.
  intros mvs Hd; unfold parmove.
  set (p := (MAP (fun '(x, y) => (Some x, Some y)) mvs, ([], [])) : st).
  assert (Hw : wf p) by (apply init_wf, Hd).
  destruct (pmov_final p) as [τ E].
  pose proof (ALL_DISTINCT_pmov p) as H; rewrite E in H |- *; cbn [FST SND fst snd app] in *.
  apply ALL_DISTINCT_iff; rewrite map_rev, filter_rev; apply NoDup_rev, ALL_DISTINCT_iff, H.
  split; [exact Hw|]. apply ALL_DISTINCT_iff.
  apply wf_iff in Hw as (Hn & Hfm & _); cbn [app] in *; rewrite app_nil_r in *.
  rewrite filter_all; [exact Hn|].
  intros x Hx; apply in_map_iff in Hx as (q & <- & Hq); apply Hfm, Hq.
Qed.

(** ** The compiler retains all non-trivial moves *)

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "step_preserves_moves" *)
Theorem step_preserves_moves : forall s1 s2 : st, step s1 s2 ->
  forall x, (exists y, MEM (x, y) (state_to_list s1) /\ x <> y) ->
            (exists y, MEM (x, y) (state_to_list s2) /\ x <> y).
Proof.
  intros s1 s2 Hs x (y & Hm & Hne); apply MEM_iff in Hm; unfold state_to_list in *.
  destruct Hs; cbn [FST SND fst snd] in *; rewrite ?in_app_iff in Hm; cbn [In] in Hm;
    rewrite ?in_app_iff in Hm; cbn [In] in Hm.
  4: { destruct Hm as [[Hm|[Hm|[Hm|[]]]]|Hm].
       - exists y; split; [apply MEM_iff; rewrite !in_app_iff; tauto|exact Hne].
       - exists y; split; [apply MEM_iff; rewrite !in_app_iff; tauto|exact Hne].
       - injection Hm as -> ->. destruct x as [x|].
         + exists None; split; [apply MEM_iff; rewrite !in_app_iff; cbn; tauto|discriminate].
         + exists y; split; [apply MEM_iff; rewrite !in_app_iff; cbn; tauto|exact Hne].
       - exists y; split; [apply MEM_iff; rewrite !in_app_iff; cbn; tauto|exact Hne]. }
  all: exists y; split; [apply MEM_iff; repeat (rewrite ?in_app_iff; cbn [In app]); intuition congruence|exact Hne].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "steps_preserves_moves" *)
Theorem steps_preserves_moves : forall x (s1 s2 : st),
  (fun s1 : st => exists y, MEM (x, y) (state_to_list s1) /\ x <> y) s1 /\ RTC step s1 s2 ->
  (fun s1 : st => exists y, MEM (x, y) (state_to_list s1) /\ x <> y) s2.
Proof. intros x; apply RTC_lifts_invariants; intros a b [Ha Hs]; eapply step_preserves_moves; eauto. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "pmov_preserves_moves" *)
Theorem pmov_preserves_moves : forall x y (p : st),
  wf p /\ MEM (x, y) (state_to_list p) /\ x <> y -> MEM x (MAP FST (state_to_list (pmov p))).
Proof.
  intros x y p (Hw & Hm & Hne).
  destruct (steps_preserves_moves x p (pmov p)) as (y' & Hm' & _).
  - split; [eauto|apply dsteps_steps; [apply pmov_dsteps|exact Hw]].
  - apply MEM_iff in Hm'; apply MEM_iff, in_map_iff; exists (x, y'); auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parmove_preserves_moves" *)
Theorem parmove_preserves_moves : forall (moves : list (A * A)) x y,
  windmill moves /\ MEM (x, y) moves /\ x <> y -> MEM (Some x) (MAP FST (parmove moves)).
Proof.
  intros moves x y (Hw & Hm & Hne); unfold parmove.
  set (p := (MAP (fun '(x, y) => (Some x, Some y)) moves, ([], [])) : st).
  destruct (pmov_final p) as [τ E].
  pose proof (pmov_preserves_moves (Some x) (Some y) p) as H; rewrite E in H |- *.
  apply MEM_iff; rewrite map_rev, <- in_rev; apply MEM_iff, H.
  split; [apply init_wf, Hw|]. split; [|congruence].
  apply MEM_iff in Hm; apply MEM_iff; unfold state_to_list; cbn [FST SND fst snd app].
  rewrite !app_nil_r; apply (in_map (fun '(x, y) => (Some x, Some y)) _ _ Hm).
Qed.

End Steps2.

(** ** Mapping an injective function over compiled moves *)

(** The continuation of [fstep]'s [splitAtPki] call. *)
Definition fstep_k {X} `{EqDecision X} (t : list (option X * option X)) (d s : option X)
    (b l : list (option X * option X)) :
    list (option X * option X) -> list (option X * option X) -> @pstate X :=
  fun t1 rt2 =>
    match rt2 with
    | rd :: t2 => (t1 ++ t2, (rd :: (d, s) :: b, l))
    | [] =>
        if NULL b then (t, ([], (d, s) :: l))
        else
          let '(b', (d', s')) := (FRONT b, LAST b) in
          if bool_decide (s' = d) then (t, (SNOC (d', None) b', (d, s) :: (None, d) :: l))
          else (t, (b, (d, s) :: l))
    end.

Lemma fstep_sigma {X} `{EqDecision X} (t : list (option X * option X)) d s b l :
  fstep (t, ((d, s) :: b, l)) =
  splitAtPki (fun i p => bool_decide (SND p = d)) (fstep_k t d s b l) t.
Proof. destruct t as [|[] t]; reflexivity. Qed.

Lemma splitAtPki_unique {X B} (t1 : list X) : forall t2 (P : N -> X -> bool) (k : list X -> list X -> B),
  (forall i j x, P i x = P j x) ->
  (forall x, In x t1 -> P 0 x = false) ->
  match t2 with [] => True | h :: _ => P 0 h = true end ->
  splitAtPki P k (t1 ++ t2) = k t1 t2.
Proof.
  induction t1 as [|x t1 IH]; intros t2 P k HP H1 H2; cbn [app splitAtPki].
  - destruct t2 as [|h t2]; [reflexivity|]; cbn [splitAtPki]; rewrite H2; reflexivity.
  - rewrite (H1 x (or_introl eq_refl)).
    apply (IH t2 (fun i => P (SUC i)) (fun p s => k (x :: p) s)).
    + intros; apply HP.
    + intros y Hy; rewrite (HP _ 0); apply H1; right; exact Hy.
    + destruct t2; [trivial|rewrite (HP _ 0); exact H2].
Qed.

Lemma pmov_step {X} `{EqDecision X} (p : @pstate X) : parmove.pmov_final p = false -> pmov p = pmov (fstep p).
Proof. destruct p as [[|m μ] [[|x σ] τ]]; try discriminate; intros _; rewrite pmov_def; reflexivity. Qed.

Lemma pmov_nil {X} `{EqDecision X} (τ : list (option X * option X)) : pmov ([], ([], τ)) = ([], ([], τ)).
Proof. rewrite pmov_def; reflexivity. Qed.

Lemma bool_decide_inj {X Y} (f : X -> Y) `{EqDecision X} `{EqDecision Y} x y :
  (f x = f y -> x = y) -> bool_decide (f x = f y) = bool_decide (x = y).
Proof.
  intros Hf; unfold bool_decide; destruct (decide (f x = f y)), (decide (x = y)); subst; auto; tauto.
Qed.

Section MapInj.
Context {A : Type} `{EA : EqDecision A}.

Local Abbreviation mv := (option A * option A)%type.
Local Abbreviation st := (@pstate A).

Ltac list_in_tac :=
  repeat progress (rewrite ?map_app, ?in_app_iff in *; cbn [map fst snd In app] in * );
  intuition congruence.

Lemma step_ls_sub (s1 s2 : st) : step s1 s2 -> forall z,
  In z (map fst (state_to_list s2) ++ map snd (state_to_list s2)) ->
  z = None \/ In z (map fst (state_to_list s1) ++ map snd (state_to_list s1)).
Proof. intros H z Hz; destruct H; unfold state_to_list in *; cbn [FST SND fst snd] in *; list_in_tac. Qed.

Lemma inj_on_state_iff {B} (f : option A -> option B) (p : st) :
  inj_on_state f p <->
  (forall x y, In x (map fst (state_to_list p) ++ map snd (state_to_list p)) ->
               In y (map fst (state_to_list p) ++ map snd (state_to_list p)) -> f x = f y -> x = y) /\
  (forall x, f x = None <-> x = None).
Proof.
  unfold inj_on_state; cbv zeta; split; intros [H1 H2]; split; auto; intros x y Hx Hy.
  - apply H1; apply MEM_iff; assumption.
  - apply MEM_iff in Hx, Hy; auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "step_inj_on_state" *)
Theorem step_inj_on_state : forall {B} (f : option A -> option B) (s1 s2 : st),
  step s1 s2 -> inj_on_state f s1 -> inj_on_state f s2.
Proof.
  intros B f s1 s2 Hs; rewrite !inj_on_state_iff; intros [Hi Hn]; split; [|exact Hn].
  intros x y Hx Hy E.
  destruct (step_ls_sub _ _ Hs x Hx) as [->|Hx'], (step_ls_sub _ _ Hs y Hy) as [->|Hy'].
  - reflexivity.
  - symmetry; apply Hn; rewrite <- E; apply Hn; reflexivity.
  - apply Hn; rewrite E; apply Hn; reflexivity.
  - apply Hi; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "steps_inj_on_state" *)
Theorem steps_inj_on_state : forall {B} (f : option A -> option B) (s1 s2 : st),
  inj_on_state f s1 /\ RTC step s1 s2 -> inj_on_state f s2.
Proof. intros B f; apply RTC_lifts_invariants; intros x y [Hx Hs]; eapply step_inj_on_state; eauto. Qed.

Ltac in_ls :=
  repeat match goal with H : In (?a, ?b) ?l |- _ =>
    pose proof (in_map fst _ _ H); pose proof (in_map snd _ _ H); clear H end;
  cbn [fst snd] in *; rewrite ?in_app_iff; cbn [In]; rewrite ?in_app_iff; intuition congruence.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "step_MAP_INJ" *)
Theorem step_MAP_INJ : forall {B} `{EqDecision B} (f : option A -> option B) (s1 s2 : st),
  step s1 s2 -> inj_on_state f s1 -> step (map_state f s1) (map_state f s2).
Proof.
  intros B EB f s1 s2 Hs Hinj; apply inj_on_state_iff in Hinj as [Hi Hn].
  assert (fN : f None = None) by (apply Hn; reflexivity).
  destruct Hs; unfold map_state, state_to_list in *; cbn [fst snd FST SND] in *;
    rewrite ?map_app in *; cbn [map fst snd] in *.
  - apply step_1.
  - apply step_2.
  - apply step_3.
  - rewrite fN; apply step_4.
  - apply step_5.
    + intros Hm; apply MEM_iff, in_map_iff in Hm as (q & Eq & Hq).
      apply in_map_iff in Hq as ([a b] & <- & Hab); cbn [fst snd] in Eq.
      apply Hi in Eq; [subst b; apply H, MEM_iff, (in_map snd _ _ Hab)|in_ls|in_ls].
    + intros E; apply Hi in E; [contradiction|in_ls|in_ls].
  - apply step_6.
    intros Hm; apply MEM_iff, in_map_iff in Hm as (q & Eq & Hq).
    apply in_map_iff in Hq as ([a b] & <- & Hab); cbn [fst snd] in Eq.
    apply Hi in Eq; [subst b; apply H, MEM_iff, (in_map snd _ _ Hab)|in_ls|in_ls].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "steps_MAP_INJ" *)
Theorem steps_MAP_INJ : forall {B} `{EqDecision B} (f : option A -> option B) (s1 s2 : st),
  RTC step s1 s2 -> inj_on_state f s1 -> RTC step (map_state f s1) (map_state f s2).
Proof.
  intros B EB f s1 s2 H; induction H as [x|x y z Hxy Hyz IH]; intros Hi; [apply rtc_refl|].
  eapply rtc_step; [apply step_MAP_INJ; eauto|apply IH; eapply step_inj_on_state; eauto].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "fstep_MAP_INJ" *)
Theorem fstep_MAP_INJ : forall {B} `{EqDecision B} (f : option A -> option B) (p : st),
  inj_on_state f p -> fstep (map_state f p) = map_state f (fstep p).
Proof.
  intros B EB f [μ [σ τ]] Hinj; apply inj_on_state_iff in Hinj as [Hi Hn].
  assert (fN : f None = None) by (apply Hn; reflexivity).
  set (LS := map fst (state_to_list (μ, (σ, τ))) ++ map snd (state_to_list (μ, (σ, τ)))) in Hi.
  assert (HLS : forall a b, In (a, b) (μ ++ σ ++ τ) -> In a LS /\ In b LS).
  { intros a b Hab; unfold LS, state_to_list; cbn [FST SND fst snd]; rewrite <- app_assoc.
    split; apply in_or_app; [left; apply (in_map fst _ _ Hab)|right; apply (in_map snd _ _ Hab)]. }
  destruct σ as [|[d s] b].
  - destruct μ as [|[d s] t]; [reflexivity|].
    assert (Hds := HLS d s (or_introl eq_refl)).
    unfold map_state; cbn [fst snd map fstep].
    rewrite (bool_decide_inj f s d) by (apply Hi; tauto).
    destruct (bool_decide (s = d)); reflexivity.
  - assert (Hds := HLS d s (ltac:(apply in_or_app; right; left; reflexivity))).
    change (map_state f (μ, ((d, s) :: b, τ))) with
      (map (f ## f) μ, ((f d, f s) :: map (f ## f) b, map (f ## f) τ)).
    rewrite !fstep_sigma.
    destruct (splitAtPki_first μ (fun i (p : mv) => bool_decide (SND p = d)) (fstep_k μ d s b τ)
      (fun _ _ _ => eq_refl)) as (t1 & t2 & Ht & E & H1 & H2).
    rewrite E.
    assert (Hm : map (f ## f) μ = map (f ## f) t1 ++ map (f ## f) t2) by (rewrite Ht, map_app; reflexivity).
    rewrite Hm at 2.
    rewrite (splitAtPki_unique (map (f ## f) t1) (map (f ## f) t2)); [| reflexivity | |].
    + subst μ; unfold fstep_k; destruct t2 as [|rd t2].
      * rewrite !map_app; cbn [map].
        destruct (snoc_cases b) as [->|(b' & [d' s'] & ->)]; [unfold map_state; cbn [fst snd map NULL]; rewrite ?map_app; reflexivity|].
        rewrite map_app; cbn [map].
        repeat match goal with |- context [NULL (?l ++ [?x])] => replace (NULL (l ++ [x])) with false by (destruct l; reflexivity) end.
        rewrite !FRONT_snoc, !LAST_snoc; cbv beta iota.
        assert (Hs' := HLS d' s' ltac:(rewrite !in_app_iff; cbn [In]; rewrite !in_app_iff; cbn [In]; intuition congruence)).
        cbn [PAIR_MAP FST SND fst snd].
        rewrite (bool_decide_inj f s' d) by (apply Hi; tauto).
        destruct (bool_decide (s' = d)); unfold map_state; cbn [fst snd map];
          rewrite ?SNOC_eq, ?map_app; cbn [map PAIR_MAP fst snd]; rewrite ?fN, ?map_app; reflexivity.
      * unfold map_state; cbn [fst snd map]; rewrite !map_app; reflexivity.
    + intros x Hx; apply in_map_iff in Hx as ([a e] & <- & Hae).
      specialize (H1 _ Hae); cbn [PAIR_MAP FST SND fst snd] in *.
      assert (Hae' := HLS a e ltac:(subst μ; rewrite !in_app_iff; tauto)).
      rewrite (bool_decide_inj f e d) by (apply Hi; tauto); exact H1.
    + destruct t2 as [|[a e] t2]; [trivial|]; cbn [map PAIR_MAP FST SND fst snd] in *.
      assert (Hae' := HLS a e ltac:(subst μ; rewrite !in_app_iff; cbn; tauto)).
      rewrite (bool_decide_inj f e d) by (apply Hi; tauto); exact H2.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "pmov_MAP_INJ" *)
Theorem pmov_MAP_INJ : forall {B} `{EqDecision B} (f : option A -> option B) (p : st),
  wf p /\ inj_on_state f p -> pmov (map_state f p) = map_state f (pmov p).
Proof.
  intros B EB f p; induction p as [p IH] using (well_founded_induction pmov_wf); intros [Hw Hi].
  destruct (parmove.pmov_final p) eqn:Ef.
  - destruct p as [[|m μ] [[|x σ] τ]]; try discriminate Ef.
    unfold map_state; cbn [fst snd map]; rewrite !pmov_nil; reflexivity.
  - assert (Hnf : forall τ, p <> ([], ([], τ))) by (intros τ ->; discriminate).
    assert (Hst : RTC step p (fstep p)) by (apply dsteps_steps; [apply RTC_SINGLE, fstep_dstep, Hnf|exact Hw]).
    rewrite (pmov_step p Ef), (pmov_step (map_state f p)).
    + rewrite fstep_MAP_INJ by exact Hi. apply IH; [apply fstep_dec, Ef|].
      split; [apply (wf_steps p); auto|apply (steps_inj_on_state f p); auto].
    + destruct p as [[|m μ] [[|x σ] τ]]; try discriminate Ef; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parmove_MAP_INJ" *)
Theorem parmove_MAP_INJ : forall {B} `{EqDecision B} (f : A -> B) (ls : list (A * A)),
  (let ls1 := MAP FST ls ++ MAP SND ls in
   forall x y, MEM x ls1 /\ MEM y ls1 /\ f x = f y -> x = y) /\
  windmill ls ->
  parmove (MAP (f ## f) ls) = MAP (OPTION_MAP f ## OPTION_MAP f) (parmove ls).
Proof.
  intros B EB f ls [Hinj Hw]; cbv zeta in Hinj; unfold parmove.
  set (p := (MAP (fun '(x, y) => (Some x, Some y)) ls, ([], [])) : st).
  assert (Ep : (MAP (fun '(x, y) => (Some x, Some y)) (MAP (f ## f) ls),
                (([] : list (option B * option B)), ([] : list (option B * option B))))
               = map_state (OPTION_MAP f) p).
  { unfold map_state, p; cbn [fst snd map]; f_equal; rewrite !map_map; apply map_ext; intros [a b]; reflexivity. }
  rewrite Ep.
  assert (Hmem : forall a b, In (a, b) ls -> is_true (MEM a (MAP FST ls ++ MAP SND ls)) /\
                                            is_true (MEM b (MAP FST ls ++ MAP SND ls))).
  { intros a b Hab; split; apply MEM_iff, in_or_app; [left; apply (in_map fst _ _ Hab)|right; apply (in_map snd _ _ Hab)]. }
  assert (Hi : inj_on_state (OPTION_MAP f) p).
  { apply inj_on_state_iff; unfold p, state_to_list; cbn [FST SND fst snd app]; rewrite !app_nil_r; split.
    - intros x y Hx Hy E; rewrite in_app_iff, !map_map, !in_map_iff in Hx, Hy.
      destruct Hx as [([a b] & <- & Ha)|([a b] & <- & Ha)], Hy as [([c e] & <- & Hc)|([c e] & <- & Hc)];
        cbn in E |- *; injection E as E; f_equal; apply Hinj;
        destruct (Hmem _ _ Ha), (Hmem _ _ Hc); auto.
    - intros [x|]; cbn; split; congruence. }
  rewrite pmov_MAP_INJ by (split; [apply init_wf, Hw|exact Hi]).
  destruct (pmov_final p) as [τ E]; rewrite E.
  unfold map_state; cbn [fst snd]. rewrite map_rev; f_equal; apply map_ext; intros [a b]; reflexivity.
Qed.

End MapInj.

