(** * Pancake [news]: supported-feature queries

    Port of [cakeml/pancake/newsScript.sml].  HOL reads
    [cakeml/pancake/NEWS.md] at build time, keeps the lines
    [<sub>Feature enabled: `f`</sub>] / [<sub>Feature disabled: `f`</sub>],
    keeps for every feature only its first (most recent) line ([cleanFeatures])
    and splices the list of enabled features into [query_news_def].  The list
    below is that spliced list for the NEWS.md of the reference checkout; it
    must be regenerated when NEWS.md changes. *)

From Galette Require Import Base.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.basis.pure Require Import mlstring.
Open Scope hol_string_scope.

(*! HOL "cakeml/pancake/newsScript.sml" "query_news_def" *)
Definition query_news (s : mlstring) : bool :=
  MEM s (MAP strlit
    ["varshifts"; "exndecls"; "add_with_carry"; "structs"; "inline";
     "16bitshmem"; "shapedecls"; "shapechecks"; "globals"; "top";
     "staticchecks"; "annots"; "emptyblocks"; "st"; "biw"; "32bitshmem";
     "main_return"; "explore"; "mep"; "swcomp"; "andor"]).
