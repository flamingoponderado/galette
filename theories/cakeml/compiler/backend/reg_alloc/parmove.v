(** * CakeML [parmove]: compiling parallel moves

    A port of the definitions of [compiler/backend/reg_alloc/parmoveScript.sml]
    (Rideau, Serpette, Leroy: "Tilting at windmills with Coq").  Not ported
    yet: the inductive relations [step] and [dstep] and the theorems.

    A state is HOL's triple [(μ, σ, τ)], i.e. the right-nested
    [(μ, (σ, τ))]; registers are [option A] ([NONE] is the temporary).
    Boolean HOL definitions used in code ([windmill], [path], [wf],
    [not_use_temp_before_assign]) are [bool]; [eqenv] and [inj_on_state] are
    [Prop].

    [pmov] terminates by HOL's measure [2 * LENGTH μ + LENGTH σ]; it is
    defined with [Fix] and HOL's equation is the tagged [pmov_def].
    [listTheory.splitAtPki] is not in [list.v] yet; it is defined locally
    (untagged) with HOL's equations. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.cakeml.misc Require Import misc.
From Stdlib Require Import Wellfounded.Inverse_Image.
Open Scope N_scope.

(** [listTheory]'s [splitAtPki] (HOL's [splitAtPki_def]; untagged copy). *)
Fixpoint splitAtPki {A B} (P : N -> A -> bool) (k : list A -> list A -> B) (l : list A) : B :=
  match l with
  | [] => k [] []
  | h :: t => if P 0 h then k [] (h :: t) else splitAtPki (fun i => P (SUC i)) (fun p s => k (h :: p) s) t
  end.

Lemma splitAtPki_split {A B} (l : list A) : forall (P : N -> A -> bool) (k : list A -> list A -> B),
  exists t1 t2, l = t1 ++ t2 /\ splitAtPki P k l = k t1 t2 /\
    (t2 = [] \/ exists h t2', t2 = h :: t2').
Proof.
  induction l as [|h t IH]; intros P k; cbn [splitAtPki].
  - exists [], []; auto.
  - destruct (P 0 h).
    + exists [], (h :: t); split; [reflexivity|split; [reflexivity|right; eauto]].
    + destruct (IH (fun i => P (SUC i)) (fun p s => k (h :: p) s)) as (t1 & t2 & -> & E & H).
      exists (h :: t1), t2; auto.
Qed.

Section Parmove.
Context {A : Type} `{EqDecision A} `{Inhabited A}.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "windmill_def" *)
Definition windmill {X} `{EqDecision X} (moves : list (X * X)) : bool := ALL_DISTINCT (MAP FST moves).

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "path_def" *)
Fixpoint path {X} `{EqDecision X} (l : list (X * X)) : bool :=
  match l with
  | [] => true
  | [_] => true
  | (c, b') :: ((b, a) :: p) as rest => bool_decide (b = b') && path rest
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "wf_def" *)
Definition wf (st : list (option A * option A) * (list (option A * option A) * list (option A * option A)))
    : bool :=
  let '(μ, (σ, τ)) := st in
  windmill (μ ++ σ) &&
  EVERY IS_SOME (MAP FST μ) &&
  EVERY IS_SOME (MAP SND μ) &&
  implb (negb (NULL σ)) (EVERY IS_SOME (MAP SND (FRONT σ))) &&
  EVERY IS_SOME (MAP FST σ) &&
  path σ.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parsem_def" *)
Definition parsem {B} (μ : list (A * A)) (ρ : A -> B) : A -> B :=
  UPDATE_LIST ρ (ZIP (MAP FST μ, MAP (fun x => ρ (SND x)) μ)).

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "seqsem_def" *)
Fixpoint seqsem {B} (τ : list (A * A)) (ρ : A -> B) : A -> B :=
  match τ with
  | [] => ρ
  | (d, s) :: τ => seqsem τ (UPDATE d (ρ s) ρ)
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "sem_def" *)
Definition sem {B} (st : list (A * A) * (list (A * A) * list (A * A))) (ρ : A -> B) : A -> B :=
  let '(μ, (σ, τ)) := st in parsem (μ ++ σ) (seqsem (REVERSE τ) ρ).

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "eqenv_def" *)
Definition eqenv {B} (ρ1 ρ2 : option A -> B) : Prop := forall r, IS_SOME r -> ρ1 r = ρ2 r.

Definition pstate : Type :=
  list (option A * option A) * (list (option A * option A) * list (option A * option A)).

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "fstep_def" *)
Definition fstep (st : pstate) : pstate :=
  match st with
  | ([], ([], _)) => st
  | ((d, s) :: t, ([], l)) =>
      if bool_decide (s = d) then (t, ([], l)) else (t, ([(d, s)], l))
  | (t, ((d, s) :: b, l)) =>
      splitAtPki (fun i p => bool_decide (SND p = d))
        (fun t1 rt2 =>
           match rt2 with
           | rd :: t2 => (t1 ++ t2, (rd :: (d, s) :: b, l))
           | [] =>
               if NULL b then (t, ([], (d, s) :: l))
               else
                 let '(b', (d', s')) := (FRONT b, LAST b) in
                 if bool_decide (s' = d) then (t, (SNOC (d', None) b', (d, s) :: (None, d) :: l))
                 else (t, (b, (d, s) :: l))
           end)
        t
  end.

Definition pmov_meas (st : pstate) : N :=
  let '(μ, (σ, τ)) := st in 2 * LENGTH μ + LENGTH σ.

Definition pmov_final (st : pstate) : bool :=
  match st with ([], ([], _)) => true | _ => false end.

Lemma LENGTH_FRONT_lt {B} `{Inhabited B} (b : list B) : NULL b = false -> LENGTH (FRONT b) < LENGTH b.
Proof.
  induction b as [|x b IH]; [discriminate|]; intros _.
  destruct b as [|y b]; cbn [FRONT LENGTH]; [lia|].
  specialize (IH eq_refl); cbn [FRONT LENGTH] in *; lia.
Qed.

Lemma LENGTH_SNOC {B} (x : B) l : LENGTH (SNOC x l) = LENGTH l + 1.
Proof. induction l as [|y l IH]; cbn [SNOC LENGTH]; lia. Qed.

Lemma LENGTH_app {B} (l1 l2 : list B) : LENGTH (l1 ++ l2) = LENGTH l1 + LENGTH l2.
Proof. induction l1 as [|y l IH]; cbn [app LENGTH]; lia. Qed.

Lemma fstep_dec (st : pstate) : pmov_final st = false -> pmov_meas (fstep st) < pmov_meas st.
Proof.
  destruct st as [μ [σ τ]]; intros Hf.
  destruct σ as [|[d s] b].
  - destruct μ as [|[d s] t]; [discriminate|]; cbn [fstep].
    destruct (bool_decide (s = d)); cbn [pmov_meas LENGTH]; lia.
  - cbn [fstep]. destruct μ as [|[m1 m2] μ'].
    + cbn [splitAtPki]. destruct (NULL b) eqn:Eb; [cbn [pmov_meas LENGTH]; lia|].
      pose proof (LENGTH_FRONT_lt b Eb).
      destruct (LAST b) as [d' s']; destruct (bool_decide (s' = d));
        cbn [pmov_meas LENGTH]; rewrite ?LENGTH_SNOC; lia.
    + set (μ := (m1, m2) :: μ') in *.
      destruct (splitAtPki_split μ (fun i p => bool_decide (SND p = d))
        (fun t1 rt2 => match rt2 with
           | rd :: t2 => (t1 ++ t2, (rd :: (d, s) :: b, τ))
           | [] => if NULL b then (μ, ([], (d, s) :: τ))
                   else let '(b', (d', s')) := (FRONT b, LAST b) in
                        if bool_decide (s' = d) then (μ, (SNOC (d', None) b', (d, s) :: (None, d) :: τ))
                        else (μ, (b, (d, s) :: τ)) end)) as (t1 & t2 & Et & -> & [->|(h & t2' & ->)]).
      * destruct (NULL b) eqn:Eb; [cbn [pmov_meas LENGTH]; lia|].
        pose proof (LENGTH_FRONT_lt b Eb).
        destruct (LAST b) as [d' s']; destruct (bool_decide (s' = d));
          cbn [pmov_meas LENGTH]; rewrite ?LENGTH_SNOC; lia.
      * rewrite Et; cbn [pmov_meas LENGTH]; rewrite !LENGTH_app; cbn [LENGTH]; lia.
Qed.

Definition pmov_wf : well_founded (fun a b => pmov_meas a < pmov_meas b) :=
  Acc_intro_generator 32 (wf_inverse_image pstate N N.lt pmov_meas N.lt_wf_0).
#[global] Opaque pmov_wf.

Definition pmov_F (st : pstate) (rec : forall st', pmov_meas st' < pmov_meas st -> pstate) : pstate :=
  match Sumbool.sumbool_of_bool (pmov_final st) with
  | left _ => st
  | right H => rec (fstep st) (fstep_dec st H)
  end.

(** HOL [pmov] (see [pmov_def]). *)
Definition pmov (s : pstate) : pstate := Fix pmov_wf (fun _ => pstate) pmov_F s.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "pmov_def" *)
Theorem pmov_def : forall s,
  pmov s = match s with ([], ([], _)) => s | _ => pmov (fstep s) end.
Proof.
  intros s; unfold pmov at 1; rewrite Fix_eq.
  - unfold pmov_F; destruct (Sumbool.sumbool_of_bool (pmov_final s)) as [E|E].
    + destruct s as [[|m μ] [[|x σ] τ]]; try discriminate; reflexivity.
    + destruct s as [[|m μ] [[|x σ] τ]]; try discriminate; reflexivity.
  - intros x f g Hfg; unfold pmov_F; destruct (Sumbool.sumbool_of_bool _); [reflexivity|apply Hfg].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parmove_def" *)
Definition parmove (xs : list (A * A)) : list (option A * option A) :=
  REVERSE (SND (SND (pmov (MAP (fun '(x, y) => (Some x, Some y)) xs, ([], []))))).

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "not_use_temp_before_assign_def" *)
Fixpoint not_use_temp_before_assign (l : list (option A * option A)) : bool :=
  match l with
  | [] => true
  | (_, None) :: _ => false
  | (None, _) :: _ => true
  | (_, _) :: ls => not_use_temp_before_assign ls
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "state_to_list_def" *)
Definition state_to_list {B} (p : list B * (list B * list B)) : list B :=
  APPEND (FST p) (FST (SND p)) ++ SND (SND p).

(** HOL's [f ## g] (pairTheory [PAIR_MAP]) is written out. *)
(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "map_state_def" *)
Definition map_state {B C} (f : B -> C) :
    list (B * B) * (list (B * B) * list (B * B)) -> list (C * C) * (list (C * C) * list (C * C)) :=
  let m := MAP (fun p : B * B => (f (fst p), f (snd p))) in
  fun p => (m (fst p), (m (fst (snd p)), m (snd (snd p)))).

(*! HOL "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "inj_on_state_def" *)
Definition inj_on_state {B} (f : option A -> option B)
    (p : list (option A * option A) * (list (option A * option A) * list (option A * option A)))
    : Prop :=
  let ls0 := state_to_list p in
  let ls := MAP FST ls0 ++ MAP SND ls0 in
  (forall x y, MEM x ls -> MEM y ls -> f x = f y -> x = y) /\
  (forall x, f x = None <-> x = None).

End Parmove.
