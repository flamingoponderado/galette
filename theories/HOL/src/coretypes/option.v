(** * HOL4 [option] *)

From Galette Require Import Base.

Abbreviation NONE := None.
Abbreviation SOME := Some.
Abbreviation OPTION_MAP := option_map.

(*! HOL "HOL/src/coretypes/optionScript.sml" "OPTION_MAP_DEF" *)
Theorem OPTION_MAP_DEF : forall {A B} (f : A -> B) x,
  OPTION_MAP f (SOME x) = SOME (f x) /\ OPTION_MAP f NONE = NONE.
Proof. split; reflexivity. Qed.

Section Defs.
Context {A B C : Type}.

(*! HOL "HOL/src/coretypes/optionScript.sml" "IS_SOME_DEF" *)
Definition IS_SOME (o_ : option A) : bool := match o_ with Some _ => true | None => false end.

(*! HOL "HOL/src/coretypes/optionScript.sml" "IS_NONE_DEF" *)
Definition IS_NONE (o_ : option A) : bool := match o_ with Some _ => false | None => true end.

(** HOL [THE NONE] is unspecified. *)
(*! HOL "HOL/src/coretypes/optionScript.sml" "THE_DEF" *)
Definition THE `{Inhabited A} (o_ : option A) : A := match o_ with Some x => x | None => ARB end.

(*! HOL "HOL/src/coretypes/optionScript.sml" "OPTION_BIND_def" *)
Definition OPTION_BIND (m : option A) (f : A -> option B) : option B :=
  match m with None => None | Some x => f x end.

(*! HOL "HOL/src/coretypes/optionScript.sml" "OPTION_IGNORE_BIND_def" *)
Definition OPTION_IGNORE_BIND (m1 : option A) (m2 : option B) : option B :=
  OPTION_BIND m1 (fun _ => m2).

(*! HOL "HOL/src/coretypes/optionScript.sml" "OPTION_GUARD_def" *)
Definition OPTION_GUARD (b : bool) : option unit := if b then SOME tt else NONE.

(*! HOL "HOL/src/coretypes/optionScript.sml" "OPTION_CHOICE_def" *)
Definition OPTION_CHOICE (m1 m2 : option A) : option A :=
  match m1 with None => m2 | Some x => Some x end.

(*! HOL "HOL/src/coretypes/optionScript.sml" "OPTREL_def" *)
Definition OPTREL (R : A -> B -> Prop) (x : option A) (y : option B) : Prop :=
  (x = NONE /\ y = NONE) \/ (exists x0 y0, x = SOME x0 /\ y = SOME y0 /\ R x0 y0).

End Defs.

(*! HOL "HOL/src/coretypes/optionScript.sml" "OPTION_MAP2_DEF" *)
Definition OPTION_MAP2 {A B C} `{Inhabited A} `{Inhabited B} (f : A -> B -> C)
    (x : option A) (y : option B) : option C :=
  if IS_SOME x && IS_SOME y then SOME (f (THE x) (THE y)) else NONE.


(** HOL [some x. P x]: [SOME] of a chosen witness, or [NONE] if there is
    none.  Not computable. *)
(*! HOL "HOL/src/coretypes/optionScript.sml" "some_def" *)
Definition some {A} `{Inhabited A} (P : A -> Prop) : option A :=
  if classical_dec (exists x, P x) then SOME (select P) else NONE.
