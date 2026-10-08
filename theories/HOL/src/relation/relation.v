(** * HOL4 [relation] (the part used so far) *)

From Galette Require Import Base.

(*! HOL "HOL/src/relation/relationScript.sml" "transitive_def" *)
Definition transitive {A} (R : A -> A -> Prop) : Prop :=
  forall x y z, R x y /\ R y z -> R x z.

(*! HOL "HOL/src/relation/relationScript.sml" "reflexive_def" *)
Definition reflexive {A} (R : A -> A -> Prop) : Prop := forall x, R x x.

(*! HOL "HOL/src/relation/relationScript.sml" "irreflexive_def" *)
Definition irreflexive {A} (R : A -> A -> Prop) : Prop := forall x, ~ R x x.

(** Reflexive-transitive closure (HOL [R^*]). *)
(*! HOL "HOL/src/relation/relationScript.sml" "RTC" *)
Inductive RTC {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| rtc_refl : forall x, RTC R x x
| rtc_step : forall x y z, R x y -> RTC R y z -> RTC R x z.

(*! HOL "HOL/src/relation/relationScript.sml" "RTC_INDUCT" *)
Theorem RTC_INDUCT : forall {A} (R : A -> A -> Prop) (P : A -> A -> Prop),
  (forall x, P x x) /\ (forall x y z, R x y /\ P y z -> P x z) ->
  forall x y, RTC R x y -> P x y.
Proof.
  intros A R P [Hr Hs] x y H; induction H; [apply Hr|eapply Hs; eauto].
Qed.

(*! HOL "HOL/src/relation/relationScript.sml" "RTC_RULES" *)
Theorem RTC_RULES : forall {A} (R : A -> A -> Prop),
  (forall x, RTC R x x) /\ (forall x y z, R x y /\ RTC R y z -> RTC R x z).
Proof. intros A R; split; [apply rtc_refl|intros x y z [H1 H2]; eapply rtc_step; eauto]. Qed.

(*! HOL "HOL/src/relation/relationScript.sml" "RTC_REFL" *)
Theorem RTC_REFL : forall {A} (R : A -> A -> Prop) x, RTC R x x.
Proof. intros; apply rtc_refl. Qed.

(*! HOL "HOL/src/relation/relationScript.sml" "RTC_SINGLE" *)
Theorem RTC_SINGLE : forall {A} (R : A -> A -> Prop) x y, R x y -> RTC R x y.
Proof. intros; eapply rtc_step; [eassumption|apply rtc_refl]. Qed.

(*! HOL "HOL/src/relation/relationScript.sml" "RTC_STRONG_INDUCT" *)
Theorem RTC_STRONG_INDUCT : forall {A} (R : A -> A -> Prop) (P : A -> A -> Prop),
  (forall x, P x x) /\ (forall x y z, R x y /\ RTC R y z /\ P y z -> P x z) ->
  forall x y, RTC R x y -> P x y.
Proof.
  intros A R P [Hr Hs] x y H; induction H; [apply Hr|eapply Hs; eauto].
Qed.

(*! HOL "HOL/src/relation/relationScript.sml" "RTC_RTC" *)
Theorem RTC_RTC : forall {A} (R : A -> A -> Prop) x y,
  RTC R x y -> forall z, RTC R y z -> RTC R x z.
Proof. intros A R x y H; induction H; intros; [assumption|eapply rtc_step; eauto]. Qed.

(*! HOL "HOL/src/relation/relationScript.sml" "RTC_TRANSITIVE" *)
Theorem RTC_TRANSITIVE : forall {A} (R : A -> A -> Prop), transitive (RTC R).
Proof. intros A R x y z [H1 H2]; eapply RTC_RTC; eauto. Qed.

(*! HOL "HOL/src/relation/relationScript.sml" "RTC_TRANS" *)
Theorem RTC_TRANS : forall {A} (R : A -> A -> Prop) x y z,
  RTC R x y /\ RTC R y z -> RTC R x z.
Proof. intros A R x y z [H1 H2]; eapply RTC_RTC; eauto. Qed.

(*! HOL "HOL/src/relation/relationScript.sml" "RTC_REFLEXIVE" *)
Theorem RTC_REFLEXIVE : forall {A} (R : A -> A -> Prop), reflexive (RTC R).
Proof. intros A R x; apply rtc_refl. Qed.

(*! HOL "HOL/src/relation/relationScript.sml" "RTC_SUBSET" *)
Theorem RTC_SUBSET : forall {A} (R : A -> A -> Prop) x y, R x y -> RTC R x y.
Proof. exact @RTC_SINGLE. Qed.

(*! HOL "HOL/src/relation/relationScript.sml" "RTC_CASES1" *)
Theorem RTC_CASES1 : forall {A} (R : A -> A -> Prop) x y,
  RTC R x y <-> x = y \/ exists u, R x u /\ RTC R u y.
Proof.
  intros A R x y; split.
  - intros H; destruct H; [left; reflexivity|right; eauto].
  - intros [<-|(u & H1 & H2)]; [apply rtc_refl|eapply rtc_step; eauto].
Qed.

(*! HOL "HOL/src/relation/relationScript.sml" "RTC_CASES2" *)
Theorem RTC_CASES2 : forall {A} (R : A -> A -> Prop) x y,
  RTC R x y <-> x = y \/ exists u, RTC R x u /\ R u y.
Proof.
  intros A R x y; split.
  - intros H; induction H as [x|x y z Hxy Hyz IH]; [left; reflexivity|].
    right; destruct IH as [<-|(u & H1 & H2)].
    + exists x; split; [apply rtc_refl|assumption].
    + exists u; split; [eapply rtc_step; eauto|assumption].
  - intros [<-|(u & H1 & H2)]; [apply rtc_refl|].
    eapply RTC_RTC; [eassumption|apply RTC_SINGLE; assumption].
Qed.

(*! HOL "HOL/src/relation/relationScript.sml" "RTC_CASES_RTC_TWICE" *)
Theorem RTC_CASES_RTC_TWICE : forall {A} (R : A -> A -> Prop) x y,
  RTC R x y <-> exists u, RTC R x u /\ RTC R u y.
Proof.
  intros A R x y; split.
  - intros H; exists x; split; [apply rtc_refl|assumption].
  - intros (u & H1 & H2); eapply RTC_RTC; eauto.
Qed.

(*! HOL "HOL/src/relation/relationScript.sml" "RTC_MONOTONE" *)
Theorem RTC_MONOTONE : forall {A} (R Q : A -> A -> Prop) x y,
  (forall x y, R x y -> Q x y) -> RTC R x y -> RTC Q x y.
Proof. intros A R Q x y HQ H; induction H; [apply rtc_refl|eapply rtc_step; eauto]. Qed.

(*! HOL "HOL/src/relation/relationScript.sml" "RTC_lifts_invariants" *)
Theorem RTC_lifts_invariants : forall {A} (R : A -> A -> Prop) (P : A -> Prop),
  (forall x y, P x /\ R x y -> P y) -> forall x y, P x /\ RTC R x y -> P y.
Proof.
  intros A R P HP x y [Hx H]; induction H; [assumption|apply IHRTC; eapply HP; eauto].
Qed.
