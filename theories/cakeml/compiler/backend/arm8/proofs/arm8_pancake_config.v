(** * ARMv8 configuration for Pancake

    Flapjack-specific instantiation (no HOL original): the ARMv8
    configuration that Pancake compiles with, [pancake_backend_conf] of
    [arm8_backend_config], and the two configuration obligations it needs.

    Counterparts in Flapjack:
    [Flapjack/Compiler/Backend/Arm8Config/BackendConfig.lean]
    ([pancakeArm8BackendConfig]),
    [Flapjack/Compiler/Backend/Arm8Config/BackendProofL3.lean]
    ([arm8BackendConfigOkL3], [backendConfigOk_pancakeArm8BackendConfigL3]) and
    [Flapjack/Compiler/Backend/Arm8Config/ProofsL3.lean]
    ([arm8InitOkL3_pancake]).

    [pancake_backend_conf] changes only [data_conf.gc_kind], and neither
    [backend_config_ok] nor [mc_init_ok] reads that field, so both
    obligations follow from the [arm8_backend_config] ones by conversion. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.examples.l3_machine_code.arm8.model Require Import arm8.
From Galette.cakeml.compiler.backend Require Import backend.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem.
From Galette.cakeml.compiler.backend.proofs Require Import backendProof.
From Galette.cakeml.compiler.encoders.arm8 Require Import arm8_target.
From Galette.cakeml.compiler.backend.arm8 Require Import arm8_config.
From Galette.cakeml.compiler.backend.arm8.proofs Require Import arm8_configProof.
From Galette.cakeml.compiler Require Import compiler.
Open Scope N_scope.

(** Flapjack's [pancakeArm8BackendConfig]. *)
Definition pancake_arm8_backend_config : backend.config :=
  pancake_backend_conf arm8_backend_config.

(** [backend_config_ok] does not read [data_conf.gc_kind], which is the only
    field [pancake_backend_conf] changes. *)
Lemma arm8_backend_config_ok_pancake :
  backendProof.backend_config_ok arm8_config pancake_arm8_backend_config.
Proof.
  unfold pancake_arm8_backend_config, pancake_backend_conf, set_data_conf,
    backendProof.backend_config_ok.
  exact arm8_backend_config_ok.
Qed.

(** [mc_init_ok] reads only [stack_conf.reg_names] and [data_conf.be], both
    preserved by [pancake_backend_conf]. *)
Lemma arm8_init_ok_pancake
    (mc : targetSem.machine_config 64 arm8_state arm8_proj_type) :
  is_arm8_machine_config mc ->
  backendProof.mc_init_ok arm8_config pancake_arm8_backend_config mc.
Proof.
  intros H.
  unfold pancake_arm8_backend_config, pancake_backend_conf, set_data_conf.
  exact (arm8_init_ok mc H).
Qed.
