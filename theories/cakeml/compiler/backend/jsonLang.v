(** * CakeML [jsonLang]: JSON objects

    Port of [cakeml/compiler/backend/jsonLangScript.sml], restricted to
    [num_to_hex_digit], the only definition used by the compiler's text
    output ([presLang]'s [num_to_hex]; the [--explore] tap prints S-
    expressions, not JSON).  Not ported: the [obj] datatype, [concat_with],
    [printable], [n_rev_hex_digs], [encode_str], [json_to_mlstring] and
    their theorems. *)

From Galette Require Import Base.
From Galette.HOL.src.string Require Import string.
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/jsonLangScript.sml" "num_to_hex_digit_def" *)
Definition num_to_hex_digit (n : N) : list ascii :=
  if n <? 10 then [CHR (48 + n)] else
  if n <? 16 then [CHR (55 + n)] else [].
