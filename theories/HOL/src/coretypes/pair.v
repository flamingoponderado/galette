(** * HOL4 [pair] *)

From Galette Require Import Base.

Abbreviation FST := fst.
Abbreviation SND := snd.

(*! HOL "HOL/src/coretypes/pairScript.sml" "FST" *)
Theorem FST_thm : forall {A B} (x : A) (y : B), FST (x, y) = x.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/coretypes/pairScript.sml" "SND" *)
Theorem SND_thm : forall {A B} (x : A) (y : B), SND (x, y) = y.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/coretypes/pairScript.sml" "CURRY_DEF" *)
Definition CURRY {A B C} (f : A * B -> C) (x : A) (y : B) : C := f (x, y).

(*! HOL "HOL/src/coretypes/pairScript.sml" "UNCURRY" *)
Definition UNCURRY {A B C} (f : A -> B -> C) (v : A * B) : C := f (FST v) (SND v).

(*! HOL "HOL/src/coretypes/pairScript.sml" "UNCURRY_DEF" *)
Theorem UNCURRY_DEF : forall {A B C} (f : A -> B -> C) x y, UNCURRY f (x, y) = f x y.
Proof. reflexivity. Qed.

(** HOL [f ## g] ([PAIR_MAP]). *)
(*! HOL "HOL/src/coretypes/pairScript.sml" "PAIR_MAP" *)
Definition PAIR_MAP {A B C D} (f : A -> C) (g : B -> D) (p : A * B) : C * D :=
  (f (FST p), g (SND p)).
Notation "f ## g" := (PAIR_MAP f g) (at level 40, left associativity).

(*! HOL "HOL/src/coretypes/pairScript.sml" "PAIR_MAP_THM" *)
Theorem PAIR_MAP_THM : forall {A B C D} (f : A -> C) (g : B -> D) x y,
  (f ## g) (x, y) = (f x, g y).
Proof. reflexivity. Qed.
