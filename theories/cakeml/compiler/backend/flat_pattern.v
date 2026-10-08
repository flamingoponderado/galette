(** * CakeML [flat_pattern]: pattern-compilation configuration

    Partial port of [cakeml/compiler/backend/flat_patternScript.sml]: the
    [config] record and [init_config].  The pattern compiler itself is not
    ported. *)

From Galette Require Import Base.
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/flat_patternScript.sml" "config" *)
Record config : Type := { pat_heuristic : N }.

(*! HOL "cakeml/compiler/backend/flat_patternScript.sml" "init_config_def" *)
Definition init_config (ph : N) : config := {| pat_heuristic := ph |}.

#[global] Instance config_inhabited : Inhabited config := init_config 0.
