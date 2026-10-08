(** * CakeML [clos_known]: closure-flow analysis configuration

    Partial port of [cakeml/compiler/backend/clos_knownScript.sml]: the
    datatype [val_approx], the [config] record and its constants
    [default_inline_factor], [default_max_body_size], [mk_config],
    [default_config].  The analysis itself ([merge], [known], [compile],
    ...) is not ported.  [val_approx]'s constructor [Int] shadows
    [closLang]'s [const_part] constructor ([closLang.Int]). *)

From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import closLang.
Open Scope N_scope.
Local Set Warnings "-register-all".

(*! HOL "cakeml/compiler/backend/clos_knownScript.sml" "val_approx" *)
Inductive val_approx : Type :=
| ClosNoInline : N -> N -> val_approx
| Clos : N -> N -> exp -> N -> val_approx
| Tuple : N -> list val_approx -> val_approx
| Int : Z -> val_approx
| Other : val_approx
| Impossible : val_approx.

#[global] Instance val_approx_inhabited : Inhabited val_approx := Other.

(*! HOL "cakeml/compiler/backend/clos_knownScript.sml" "config" *)
Record config : Type := {
  inline_max_body_size : N;
  inline_factor : N;
  initial_inline_factor : N;
  val_approx_spt : spt val_approx
}.

(*! HOL "cakeml/compiler/backend/clos_knownScript.sml" "default_inline_factor_def" *)
Definition default_inline_factor : N := 8.

(*! HOL "cakeml/compiler/backend/clos_knownScript.sml" "default_max_body_size_def" *)
Definition default_max_body_size (max_app inline_factor : N) : N :=
  (max_app + 1) * inline_factor.

(*! HOL "cakeml/compiler/backend/clos_knownScript.sml" "mk_config_def" *)
Definition mk_config (max_body_size inline_factor : N) : config :=
  {| inline_max_body_size := max_body_size;
     clos_known.inline_factor := inline_factor;
     initial_inline_factor := inline_factor;
     val_approx_spt := LN |}.

(*! HOL "cakeml/compiler/backend/clos_knownScript.sml" "default_config_def" *)
Definition default_config (max_app : N) : config :=
  mk_config (default_max_body_size max_app default_inline_factor)
    default_inline_factor.

#[global] Instance config_inhabited : Inhabited config := mk_config 0 0.
