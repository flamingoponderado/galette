(** * CakeML [source_to_flat]: source-to-flatLang configuration

    Partial port of [cakeml/compiler/backend/source_to_flatScript.sml]: the
    datatypes [var_name], [environment], [environment_generation_store],
    [environment_store], [next_indices], [config], and the constants
    [empty_env] and [empty_config].  The source compiler ([compile_exp],
    [compile_decs], [compile_prog], ...) is not ported.

    Field-name clashes within this module (HOL allows the same field name in
    several records): [environment_generation_store]'s [next]/[envs] are
    [environment_generation_store_next]/[environment_generation_store_envs],
    and [environment_store]'s [next] is [environment_store_next]; [config]
    keeps HOL's [next] and [envs]. *)

From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics Require Import ast namespace.
From Galette.cakeml.compiler.backend Require Import backend_common flatLang flat_pattern.
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/source_to_flatScript.sml" "var_name" *)
Inductive var_name : Type :=
| Glob : tra -> N -> var_name
| Local : tra -> mlstring -> var_name.

#[global] Instance var_name_eq_dec : EqDecision var_name.
Proof. intros x y; unfold Decision; decide equality; apply (decide (_ = _)). Defined.
#[global] Instance var_name_inhabited : Inhabited var_name := Glob tra_None 0.

(*! HOL "cakeml/compiler/backend/source_to_flatScript.sml" "environment" *)
Record environment : Type := {
  c : namespace modN conN (ctor_id * type_group_id);
  v : namespace modN varN var_name
}.

(** HOL's fields [next], [generation], [envs]; [next] and [envs] are
    prefixed (see the file header). *)
(*! HOL "cakeml/compiler/backend/source_to_flatScript.sml" "environment_generation_store" *)
Record environment_generation_store : Type := {
  environment_generation_store_next : N;
  generation : N;
  environment_generation_store_envs : num_map environment
}.

(** HOL's fields [next], [env_gens]; [next] is prefixed (see the file
    header). *)
(*! HOL "cakeml/compiler/backend/source_to_flatScript.sml" "environment_store" *)
Record environment_store : Type := {
  environment_store_next : N;
  env_gens : num_map (num_map environment)
}.

(*! HOL "cakeml/compiler/backend/source_to_flatScript.sml" "empty_env_def" *)
Definition empty_env : environment := {| v := nsEmpty; c := nsEmpty |}.

#[global] Instance environment_inhabited : Inhabited environment := empty_env.
#[global] Instance environment_generation_store_inhabited :
  Inhabited environment_generation_store :=
  {| environment_generation_store_next := 0; generation := 0;
     environment_generation_store_envs := LN |}.
#[global] Instance environment_store_inhabited : Inhabited environment_store :=
  {| environment_store_next := 0; env_gens := LN |}.

(*! HOL "cakeml/compiler/backend/source_to_flatScript.sml" "next_indices" *)
Record next_indices : Type := { vidx : N; tidx : N; eidx : N }.

#[global] Instance next_indices_inhabited : Inhabited next_indices :=
  {| vidx := 0; tidx := 0; eidx := 0 |}.

(*! HOL "cakeml/compiler/backend/source_to_flatScript.sml" "config" *)
Record config : Type := {
  next : next_indices;
  mod_env : environment;
  pattern_cfg : flat_pattern.config;
  envs : environment_store
}.

(*! HOL "cakeml/compiler/backend/source_to_flatScript.sml" "empty_config_def" *)
Definition empty_config : config :=
  {| next := {| vidx := 0; tidx := 0; eidx := 0 |};
     mod_env := empty_env;
     pattern_cfg := flat_pattern.init_config 0;
     envs := {| environment_store_next := 0; env_gens := LN |} |}.

#[global] Instance config_inhabited : Inhabited config := empty_config.
