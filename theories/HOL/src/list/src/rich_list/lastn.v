(** * HOL4 [rich_list]: [LASTN] *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
Open Scope N_scope.

(*! HOL "HOL/src/list/src/rich_listScript.sml" "LASTN_def" *)
Definition LASTN {A} (n : N) (xs : list A) : list A := REVERSE (TAKE n (REVERSE xs)).
