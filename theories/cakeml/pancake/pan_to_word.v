(** * Pancake [pan_to_word]: compiler from Pancake to wordLang

    Port of [cakeml/pancake/pan_to_wordScript.sml]. *)

From Galette Require Import Base.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.pancake Require panLang pan_simp pan_structs pan_globals pan_to_crep
  crep_to_loop loop_to_word.
Open Scope N_scope.
Open Scope hol_string_scope.

(*! HOL "cakeml/pancake/pan_to_wordScript.sml" "compile_prog_def" *)
Definition compile_prog {a : N} (arch : architecture) (prog : list (panLang.decl a))
    : list (N * (N * wordLang.prog a)) :=
  let prog := pan_simp.compile_prog prog in
  let prog := pan_structs.compile_top prog in
  let prog := pan_globals.compile_top prog (strlit "main") in
  let prog := pan_to_crep.compile_prog prog in
  let prog := crep_to_loop.compile_prog arch prog in
  loop_to_word.compile prog.
