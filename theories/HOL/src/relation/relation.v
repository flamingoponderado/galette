(** * HOL4 [relation] (the part used so far) *)

From Galette Require Import Base.

(*! HOL "HOL/src/relation/relationScript.sml" "irreflexive_def" *)
Definition irreflexive {A} (R : A -> A -> Prop) : Prop := forall x, ~ R x x.
