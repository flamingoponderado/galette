(** * CakeML [clos_to_bvl]: closure-conversion configuration

    Partial port of [cakeml/compiler/backend/clos_to_bvlScript.sml]: the
    [config] record and [default_config].  The ClosLang-to-BVL compiler is
    not part of the Pancake pipeline and is not ported.  HOL's
    [(num, num # closLang$exp) alist] is [list (N * (N * closLang.exp))]. *)

From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import closLang clos_known.
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/clos_to_bvlScript.sml" "config" *)
Record config : Type := {
  next_loc : N;
  start : N;
  do_mti : bool;
  known_conf : option clos_known.config;
  do_call : bool;
  call_state : num_set * list (N * (N * closLang.exp));
  max_app : N
}.

(*! HOL "cakeml/compiler/backend/clos_to_bvlScript.sml" "default_config_def" *)
Definition default_config : config :=
  {| next_loc := 0;
     start := 1;
     do_mti := true;
     known_conf := Some (clos_known.default_config 10);
     do_call := true;
     call_state := (LN, []);
     max_app := 10 |}.

#[global] Instance config_inhabited : Inhabited config := default_config.
