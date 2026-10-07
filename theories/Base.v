(** * Galette base: the HOL logic inside Rocq

    Galette-specific infrastructure (no HOL original).  HOL4 is a classical
    higher-order logic with extensionality and Hilbert choice; every HOL type
    is inhabited.  The port therefore works in Rocq extended with exactly the
    corresponding standard axioms, listed here and nowhere else:

    - excluded middle and Hilbert's epsilon ([ClassicalEpsilon]),
    - functional and propositional extensionality,
    - proof irrelevance (a consequence of the above, imported for convenience).

    Conventions (see AGENTS.md):
    - HOL [bool] used computationally (in compiler code) is Rocq [bool]; a
      [bool] appearing in a theorem statement is read as a [Prop] through the
      [is_true] coercion.  HOL predicates defined by quantification are [Prop].
    - HOL [=] on a type used computationally is decided by [decide (x = y)]. *)

From Stdlib Require Export Bool PeanoNat ZArith List String Ascii.
From Stdlib Require Export Logic.ClassicalEpsilon Logic.FunctionalExtensionality
  Logic.PropExtensionality Logic.ProofIrrelevance.
From Stdlib Require Export Lia.
Export ListNotations.

Set Asymmetric Patterns.

(** HOL booleans as propositions. *)
Definition is_true (b : bool) : Prop := b = true.
Coercion is_true : bool >-> Sortclass.

Lemma is_true_true : is_true true.
Proof. reflexivity. Qed.
#[global] Hint Resolve is_true_true : core.

(** ** Decidable propositions

    [decide P] is the computational counterpart of a HOL boolean condition
    [P].  Instances are provided for equality on the carriers used by the
    compiler. *)
Class Decision (P : Prop) := decide : {P} + {~ P}.
Arguments decide P {_}.

Definition bool_decide (P : Prop) {d : Decision P} : bool :=
  if decide P then true else false.

Lemma bool_decide_spec (P : Prop) {d : Decision P} : bool_decide P = true <-> P.
Proof. unfold bool_decide; destruct (decide P); split; congruence || tauto. Qed.

Class EqDecision (A : Type) := eq_dec :: forall x y : A, Decision (x = y).
#[global] Hint Mode EqDecision ! : typeclass_instances.

#[global] Instance nat_eq_dec : EqDecision nat := Nat.eq_dec.
#[global] Instance Z_eq_dec : EqDecision Z := Z.eq_dec.
#[global] Instance bool_eq_dec : EqDecision bool := Bool.bool_dec.
#[global] Instance ascii_eq_dec : EqDecision ascii := Ascii.ascii_dec.
#[global] Instance string_eq_dec : EqDecision string := String.string_dec.
#[global] Instance unit_eq_dec : EqDecision unit.
Proof. intros [] []; left; reflexivity. Defined.

#[global] Instance prod_eq_dec {A B} `{EqDecision A} `{EqDecision B} :
  EqDecision (A * B).
Proof.
  intros [a b] [c d]; destruct (decide (a = c)) as [->|n];
    [destruct (decide (b = d)) as [->|m]|]; [left; reflexivity|right|right];
    congruence.
Defined.

#[global] Instance option_eq_dec {A} `{EqDecision A} : EqDecision (option A).
Proof.
  intros [a|] [b|]; try (right; discriminate); try (left; reflexivity).
  destruct (decide (a = b)) as [->|n]; [left; reflexivity|right; congruence].
Defined.

#[global] Instance list_eq_dec {A} `{EqDecision A} : EqDecision (list A) :=
  fun l1 l2 => list_eq_dec (fun x y => decide (x = y)) l1 l2.

#[global] Instance not_dec P `{Decision P} : Decision (~ P).
Proof. destruct (decide P); [right|left]; tauto. Defined.
#[global] Instance and_dec P Q `{Decision P} `{Decision Q} : Decision (P /\ Q).
Proof. destruct (decide P); destruct (decide Q); [left|right|right|right]; tauto. Defined.
#[global] Instance or_dec P Q `{Decision P} `{Decision Q} : Decision (P \/ Q).
Proof. destruct (decide P); destruct (decide Q); [left|left|left|right]; tauto. Defined.
#[global] Instance is_true_dec (b : bool) : Decision (is_true b).
Proof. destruct b; [left; reflexivity|right; discriminate]. Defined.
#[global] Instance nat_lt_dec (m n : nat) : Decision (m < n) := lt_dec m n.
#[global] Instance nat_le_dec (m n : nat) : Decision (m <= n) := le_dec m n.

(** ** HOL's [ARB] and Hilbert choice [@]

    Every HOL type is inhabited; in Rocq this is the [inhabited] side
    condition, discharged by instances.  [ARB] is not computable: compiler code
    that reaches it is extracted to an OCaml exception (see extraction/). *)
Class Inhabited (A : Type) := inhabitant : A.
Arguments inhabitant : clear implicits.
Arguments inhabitant A {_}.

#[global] Instance nat_inhabited : Inhabited nat := 0.
#[global] Instance Z_inhabited : Inhabited Z := 0%Z.
#[global] Instance bool_inhabited : Inhabited bool := false.
#[global] Instance unit_inhabited : Inhabited unit := tt.
#[global] Instance list_inhabited {A} : Inhabited (list A) := [].
#[global] Instance option_inhabited {A} : Inhabited (option A) := None.
#[global] Instance prod_inhabited {A B} `{Inhabited A} `{Inhabited B} :
  Inhabited (A * B) := (inhabitant A, inhabitant B).
#[global] Instance fun_inhabited {A B} `{Inhabited B} : Inhabited (A -> B) :=
  fun _ => inhabitant B.
#[global] Instance string_inhabited : Inhabited string := EmptyString.
#[global] Instance ascii_inhabited : Inhabited ascii := Ascii.zero.

(** HOL [@x. P x]. *)
Definition select {A} `{Inhabited A} (P : A -> Prop) : A :=
  epsilon (inhabits (inhabitant A)) P.

Lemma select_spec {A} `{Inhabited A} (P : A -> Prop) :
  (exists x, P x) -> P (select P).
Proof. exact (epsilon_spec (inhabits (inhabitant A)) P). Qed.

(** HOL [ARB]: an unspecified value. *)
Definition ARB {A} `{Inhabited A} : A := select (fun _ => True).

(** Classical decision of an arbitrary proposition (HOL [if P then ...] for a
    non-computational [P]); not executable. *)
Definition classical_dec (P : Prop) : {P} + {~ P} :=
  match excluded_middle_informative P with left p => left p | right n => right n end.

(** HOL function composition [o] (printed [∘] by HOL's unicode mode). *)
Notation "f ∘ g" := (fun x => f (g x)) (at level 40, left associativity).
