(** * CakeML [semanticsProps]: behaviours and refinement (partial)

    Partial port of [cakeml/semantics/proofs/semanticsPropsScript.sml]: the
    resource-limit extension of a set of behaviours and the refinement
    relations [implements] and [implements'], as used by the backend
    semantics proofs.  The theorems about the source semantics
    ([evaluate_prog_with_clock] ...) are not ported. *)

From Galette Require Import Base.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.cakeml.semantics.ffi Require Import ffi.
Open Scope N_scope.

(*! HOL "cakeml/semantics/proofs/semanticsPropsScript.sml" "extend_with_resource_limit_def" *)
Definition extend_with_resource_limit (behaviours : behaviour -> Prop) : behaviour -> Prop :=
  behaviours UNION
  (fun b => exists io_list, b = Terminate Resource_limit_hit io_list /\
     exists t l, Terminate t l IN behaviours /\ isPREFIX io_list l) UNION
  (fun b => exists io_list, b = Terminate Resource_limit_hit io_list /\
     exists ll, Diverge ll IN behaviours /\ LPREFIX (fromList io_list) ll).

(*! HOL "cakeml/semantics/proofs/semanticsPropsScript.sml" "extend_with_resource_limit'_def" *)
Definition extend_with_resource_limit' (precise : bool) (behaviours : behaviour -> Prop)
    : behaviour -> Prop :=
  if precise then behaviours else extend_with_resource_limit behaviours.

(*! HOL "cakeml/semantics/proofs/semanticsPropsScript.sml" "implements_def" *)
Definition implements (x y : behaviour -> Prop) : Prop :=
  (~ (Fail IN y) -> x SUBSET extend_with_resource_limit y).

(*! HOL "cakeml/semantics/proofs/semanticsPropsScript.sml" "implements'_def" *)
Definition implements' (precise : bool) (x y : behaviour -> Prop) : Prop :=
  Fail NOTIN y -> x SUBSET extend_with_resource_limit' precise y.
