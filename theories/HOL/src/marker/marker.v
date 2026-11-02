(** * HOL4 [marker]: tagging constants (the part used so far)

    Partial port of [HOL/src/marker/markerScript.sml]: [Abbrev], which HOL
    uses to protect abbreviation equations in theorem statements (e.g. in
    [arm8_targetProof]'s [lsl]).  HOL's [Abbrev : bool -> bool] is the
    identity on (statements as) propositions. *)

From Galette Require Import Base.

(*! HOL "HOL/src/marker/markerScript.sml" "Abbrev_def" *)
Definition Abbrev (x : Prop) : Prop := x.
