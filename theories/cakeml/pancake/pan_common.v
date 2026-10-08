(** * Pancake [pan_common]: common definitions for the Pancake compiler

    Port of [cakeml/pancake/pan_commonScript.sml]. *)

From Galette Require Import Base.
From Galette.HOL.src.list.src Require Import list.
Open Scope N_scope.

(*! HOL "cakeml/pancake/pan_commonScript.sml" "distinct_lists_def" *)
Definition distinct_lists {A} `{EqDecision A} (xs ys : list A) : bool :=
  EVERY (fun x => negb (MEM x ys)) xs.
