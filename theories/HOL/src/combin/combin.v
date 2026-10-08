(** * HOL4 [combin]: combinators and function update *)

From Galette Require Import Base.

(*! HOL "HOL/src/combin/combinScript.sml" "K_DEF" *)
Definition K {A B} : A -> B -> A := fun x y => x.

(*! HOL "HOL/src/combin/combinScript.sml" "S_DEF" *)
Definition S {A B C} : (A -> B -> C) -> (A -> B) -> A -> C := fun f g x => f x (g x).

(** HOL [I = S K K]; extensionally the identity. *)
Definition I {A} (x : A) : A := x.

(*! HOL "HOL/src/combin/combinScript.sml" "C_DEF" *)
Definition C {A B C} : (A -> B -> C) -> B -> A -> C := fun f x y => f y x.

(*! HOL "HOL/src/combin/combinScript.sml" "W_DEF" *)
Definition W {A B} : (A -> A -> B) -> A -> B := fun f x => f x x.

(** HOL [UPDATE a b f], written [(a =+ b) f]. *)
(*! HOL "HOL/src/combin/combinScript.sml" "UPDATE_def" *)
Definition UPDATE {A B} `{EqDecision A} (a : A) (b : B) : (A -> B) -> A -> B :=
  fun f c => if decide (a = c) then b else f c.

Notation "( a =+ b )" := (UPDATE a b) : core_scope.

(*! HOL "HOL/src/combin/combinScript.sml" "APPLY_UPDATE_THM" *)
Theorem APPLY_UPDATE_THM : forall {A B} `{EqDecision A} (f : A -> B) a b c,
  (a =+ b) f c = if decide (a = c) then b else f c.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/combin/combinScript.sml" "UPDATE_COMMUTES" *)
Theorem UPDATE_COMMUTES : forall {A B} `{EqDecision A} (f : A -> B) a b c d,
  a <> b -> (a =+ c) ((b =+ d) f) = (b =+ d) ((a =+ c) f).
Proof.
  intros A B ? f a b c d Hab; apply functional_extensionality; intros x; unfold UPDATE.
  destruct (decide (a = x)), (decide (b = x)); congruence.
Qed.
