(** * CakeML [misc]: [fromList2] (sptree with keys 0, 2, 4, ...) *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.finite_maps Require Import sptree.
Open Scope N_scope.

(*! HOL "cakeml/misc/miscScript.sml" "fromList2_def" *)
Definition fromList2 {A} (l : list A) : num_map A :=
  snd (FOLDL (fun '(i, t) a0 => (i + 2, insert i a0 t)) (0, LN) l).
