(** * CakeML [flatLang]: the flatLang intermediate language

    Partial port of [cakeml/compiler/backend/flatLangScript.sml]: only the
    type abbreviations [ctor_id], [type_id], [type_group_id] (used by
    [source_to_flat]'s [environment]).  The syntax ([op], [pat], [exp],
    [dec]) and functions are not ported. *)

From Galette Require Import Base.
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/flatLangScript.sml" "ctor_id" *)
Abbreviation ctor_id := N.

(** [None] represents the exception type. *)
(*! HOL "cakeml/compiler/backend/flatLangScript.sml" "type_id" *)
Abbreviation type_id := (option N).

(*! HOL "cakeml/compiler/backend/flatLangScript.sml" "type_group_id" *)
Abbreviation type_group_id := (option (N * list (ctor_id * N))).
