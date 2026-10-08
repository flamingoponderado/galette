(** * HOL4 [sorting] (partial)

    Only the executable partition functions used by the compiler (the
    register allocator) are ported so far: [PART] and [PARTITION].  The
    remaining definitions ([PERM], [SORTED], [QSORT], ...) and the theory are
    not ported yet. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
Open Scope N_scope.

(*! HOL "HOL/src/sort/sortingScript.sml" "PART_DEF" *)
Fixpoint PART {A} (P : A -> bool) (l : list A) (l1 l2 : list A) : list A * list A :=
  match l with
  | [] => (l1, l2)
  | h :: rst => if P h then PART P rst (h :: l1) l2 else PART P rst l1 (h :: l2)
  end.

(*! HOL "HOL/src/sort/sortingScript.sml" "PARTITION_DEF" *)
Definition PARTITION {A} (P : A -> bool) (l : list A) : list A * list A := PART P l [] [].
