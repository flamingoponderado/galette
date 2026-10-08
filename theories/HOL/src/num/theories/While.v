(** * HOL4 [While]: [LEAST]

    HOL defines [LEAST P = WHILE ($~ o P) SUC 0], a loop whose value is
    unspecified when [P] holds nowhere.  Here [LEAST P] is chosen by Hilbert
    choice as the least [n] with [P n]; it is not executable.  [WHILE] itself
    is not ported, so [LEAST_DEF] is not tagged; HOL's characterising
    theorems are.  HOL's binder [LEAST n. P n] is written [LEAST (fun n => P n)]. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
Open Scope N_scope.

(** HOL [LEAST]. *)
Definition LEAST (P : num -> Prop) : num :=
  select (fun n => P n /\ forall m, m < n -> ~ P m).

Lemma LEAST_exists (P : num -> Prop) x : P x -> exists n, P n /\ forall m, m < n -> ~ P m.
Proof.
  intros hx; apply NNPP; intros hn.
  assert (H : forall n, ~ P n).
  { intros n; induction n as [n IH] using (well_founded_ind N.lt_wf_0).
    intros hp; apply hn; exists n; split; [exact hp|intros m hm; apply IH, hm]. }
  exact (H x hx).
Qed.

Lemma LEAST_spec (P : num -> Prop) x : P x -> P (LEAST P) /\ forall m, m < LEAST P -> ~ P m.
Proof. intros hx; exact (select_spec (fun n => P n /\ forall m, m < n -> ~ P m) (LEAST_exists P x hx)). Qed.

Lemma LEAST_unique (P : num -> Prop) n : P n -> (forall m, m < n -> ~ P m) -> LEAST P = n.
Proof.
  intros hn hm; destruct (LEAST_spec P n hn) as [h1 h2].
  destruct (N.lt_trichotomy (LEAST P) n) as [h|[h|h]]; [exfalso; exact (hm _ h h1)|exact h|].
  exfalso; exact (h2 _ h hn).
Qed.

(*! HOL "HOL/src/num/theories/WhileScript.sml" "LEAST_INTRO" *)
Theorem LEAST_INTRO : forall (P : num -> Prop) x, P x -> P (LEAST P).
Proof. intros P x hx; apply (LEAST_spec P x hx). Qed.

(*! HOL "HOL/src/num/theories/WhileScript.sml" "LESS_LEAST" *)
Theorem LESS_LEAST : forall (P : num -> Prop) m, m < LEAST P -> ~ P m.
Proof. intros P m hm hp; exact (proj2 (LEAST_spec P m hp) m hm hp). Qed.

(*! HOL "HOL/src/num/theories/WhileScript.sml" "FULL_LEAST_INTRO" *)
Theorem FULL_LEAST_INTRO : forall (P : num -> Prop) x, P x -> P (LEAST P) /\ LEAST P <= x.
Proof.
  intros P x hx; split; [apply (LEAST_INTRO P x hx)|].
  apply N.nlt_ge; intros h; exact (LESS_LEAST P x h hx).
Qed.

(*! HOL "HOL/src/num/theories/WhileScript.sml" "LEAST_ELIM" *)
Theorem LEAST_ELIM : forall (Q P : num -> Prop),
  (exists n, P n) /\ (forall n, (forall m, m < n -> ~ P m) /\ P n -> Q n) -> Q (LEAST P).
Proof.
  intros Q P [[x hx] h]; apply h; split; [apply LESS_LEAST|apply (LEAST_INTRO P x hx)].
Qed.

(*! HOL "HOL/src/num/theories/WhileScript.sml" "LEAST_EXISTS" *)
Theorem LEAST_EXISTS : forall p : num -> Prop,
  (exists n, p n) <-> (p (LEAST p) /\ forall n, n < LEAST p -> ~ p n).
Proof.
  intros p; split; [intros [x hx]; split; [apply (LEAST_INTRO p x hx)|apply LESS_LEAST]|].
  intros [h _]; eauto.
Qed.

(*! HOL "HOL/src/num/theories/WhileScript.sml" "LEAST_EXISTS_IMP" *)
Theorem LEAST_EXISTS_IMP : forall p : num -> Prop,
  (exists n, p n) -> (p (LEAST p) /\ forall n, n < LEAST p -> ~ p n).
Proof. intros p; apply LEAST_EXISTS. Qed.

(*! HOL "HOL/src/num/theories/WhileScript.sml" "LEAST_EQ" *)
Theorem LEAST_EQ : forall x,
  (LEAST (fun n => n = x) = x) /\ (LEAST (fun n => x = n) = x).
Proof. intros x; split; apply LEAST_unique; auto; intros m hm e; subst; lia. Qed.

(*! HOL "HOL/src/num/theories/WhileScript.sml" "LEAST_T" *)
Theorem LEAST_T : LEAST (fun x => True) = 0.
Proof. apply LEAST_unique; [exact I|intros m hm; lia]. Qed.

(*! HOL "HOL/src/num/theories/WhileScript.sml" "LEAST_LESS_EQ" *)
Theorem LEAST_LESS_EQ : forall y, LEAST (fun x => y <= x) = y.
Proof. intros y; apply LEAST_unique; [lia|intros m hm h; lia]. Qed.
