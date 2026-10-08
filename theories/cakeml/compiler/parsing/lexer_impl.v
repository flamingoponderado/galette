(** * CakeML [lexer_impl]: the CakeML lexer (implementation)

    Partial port of [cakeml/compiler/parsing/lexer_implScript.sml]: only the
    number-parsing helpers used by the compiler's command-line parsing
    ([compilerScript]'s [parse_num]).  The CakeML lexer itself is not
    ported (only Pancake input is supported). *)

From Galette Require Import Base.
From Galette.HOL.src.string Require Import string ASCIInumbers.
Open Scope N_scope.

(*! HOL "cakeml/compiler/parsing/lexer_implScript.sml" "unhex_alt_def" *)
Definition unhex_alt (x : ascii) : N := if isHexDigit x then UNHEX x else 0.

(*! HOL "cakeml/compiler/parsing/lexer_implScript.sml" "num_from_dec_string_alt_def" *)
Definition num_from_dec_string_alt : string -> N := s2n 10 unhex_alt.

(*! HOL "cakeml/compiler/parsing/lexer_implScript.sml" "num_from_hex_string_alt_def" *)
Definition num_from_hex_string_alt : string -> N := s2n 16 unhex_alt.
