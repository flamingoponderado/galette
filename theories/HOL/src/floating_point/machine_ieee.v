(** * HOL4 [machine_ieee]: STAND-INS, not a port

    [HOL/src/floating-point/machine_ieeeScript.sml] defines the IEEE-754
    operations on bit-vector encodings ([fp32_add], [fp64_lessThan], ...)
    through [binary_ieee]'s real-valued semantics, which Galette has not
    ported.  This file provides Galette-only stand-ins with HOL's names and
    types so that the definitions that mention them ([asmSem]'s [fp_upd],
    the floating-point instructions of the L3 RISC-V model) can be written
    as in HOL:

    - the special values ([fp32_posInf], [fp64_negZero], ...) are the
      standard IEEE-754 bit patterns, i.e. the values HOL's definitions
      compute;
    - every other operation is [ARB] (an unspecified value of the right
      type): nothing can be proved about its result, and evaluation stops
      there.

    None of these declarations is tagged.  Replacing this file by a real
    port of [machine_ieee] (keeping the names and types) makes the
    declarations that use it fully faithful. *)

From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.floating_point Require Import binary_ieee.
Open Scope N_scope.

(** ** Special values (IEEE-754 encodings) *)

Definition fp32_posInf : word32 := n2w 0x7F800000.
Definition fp32_negInf : word32 := n2w 0xFF800000.
Definition fp32_posZero : word32 := n2w 0.
Definition fp32_negZero : word32 := n2w 0x80000000.
Definition fp64_posInf : word64 := n2w 0x7FF0000000000000.
Definition fp64_negInf : word64 := n2w 0xFFF0000000000000.
Definition fp64_posZero : word64 := n2w 0.
Definition fp64_negZero : word64 := n2w 0x8000000000000000.

(** ** Operations (unspecified stand-ins) *)

Section Ops.
Context {w : N}.

Definition fp_unop_arb : word w -> word w := fun _ => ARB.
Definition fp_pred_arb : word w -> bool := fun _ => ARB.
Definition fp_rel_arb : word w -> word w -> bool := fun _ _ => ARB.
Definition fp_rnd_unop_arb : rounding -> word w -> word w := fun _ _ => ARB.
Definition fp_rnd_binop_arb : rounding -> word w -> word w -> word w :=
  fun _ _ _ => ARB.
Definition fp_rnd_triop_arb : rounding -> word w -> word w -> word w -> word w :=
  fun _ _ _ _ => ARB.
Definition fp_compare_arb : word w -> word w -> float_compare := fun _ _ => ARB.
Definition fp_to_int_arb : rounding -> word w -> option Z := fun _ _ => ARB.
Definition int_to_fp_arb : rounding -> Z -> word w := fun _ _ => ARB.

End Ops.

Definition fp32_abs : word32 -> word32 := fp_unop_arb.
Definition fp32_negate : word32 -> word32 := fp_unop_arb.
Definition fp32_isNan : word32 -> bool := fp_pred_arb.
Definition fp32_isSignallingNan : word32 -> bool := fp_pred_arb.
Definition fp32_isNormal : word32 -> bool := fp_pred_arb.
Definition fp32_isSubnormal : word32 -> bool := fp_pred_arb.
Definition fp32_isZero : word32 -> bool := fp_pred_arb.
Definition fp32_isInfinite : word32 -> bool := fp_pred_arb.
Definition fp32_isFinite : word32 -> bool := fp_pred_arb.
Definition fp32_isIntegral : word32 -> bool := fp_pred_arb.
Definition fp32_equal : word32 -> word32 -> bool := fp_rel_arb.
Definition fp32_lessThan : word32 -> word32 -> bool := fp_rel_arb.
Definition fp32_lessEqual : word32 -> word32 -> bool := fp_rel_arb.
Definition fp32_greaterThan : word32 -> word32 -> bool := fp_rel_arb.
Definition fp32_greaterEqual : word32 -> word32 -> bool := fp_rel_arb.
Definition fp32_compare : word32 -> word32 -> float_compare := fp_compare_arb.
Definition fp32_sqrt : rounding -> word32 -> word32 := fp_rnd_unop_arb.
Definition fp32_roundToIntegral : rounding -> word32 -> word32 := fp_rnd_unop_arb.
Definition fp32_add : rounding -> word32 -> word32 -> word32 := fp_rnd_binop_arb.
Definition fp32_sub : rounding -> word32 -> word32 -> word32 := fp_rnd_binop_arb.
Definition fp32_mul : rounding -> word32 -> word32 -> word32 := fp_rnd_binop_arb.
Definition fp32_div : rounding -> word32 -> word32 -> word32 := fp_rnd_binop_arb.
Definition fp32_mul_add : rounding -> word32 -> word32 -> word32 -> word32 :=
  fp_rnd_triop_arb.
Definition fp32_mul_sub : rounding -> word32 -> word32 -> word32 -> word32 :=
  fp_rnd_triop_arb.
Definition fp32_to_int : rounding -> word32 -> option Z := fp_to_int_arb.
Definition int_to_fp32 : rounding -> Z -> word32 := int_to_fp_arb.

Definition fp64_abs : word64 -> word64 := fp_unop_arb.
Definition fp64_negate : word64 -> word64 := fp_unop_arb.
Definition fp64_isNan : word64 -> bool := fp_pred_arb.
Definition fp64_isSignallingNan : word64 -> bool := fp_pred_arb.
Definition fp64_isNormal : word64 -> bool := fp_pred_arb.
Definition fp64_isSubnormal : word64 -> bool := fp_pred_arb.
Definition fp64_isZero : word64 -> bool := fp_pred_arb.
Definition fp64_isInfinite : word64 -> bool := fp_pred_arb.
Definition fp64_isFinite : word64 -> bool := fp_pred_arb.
Definition fp64_isIntegral : word64 -> bool := fp_pred_arb.
Definition fp64_equal : word64 -> word64 -> bool := fp_rel_arb.
Definition fp64_lessThan : word64 -> word64 -> bool := fp_rel_arb.
Definition fp64_lessEqual : word64 -> word64 -> bool := fp_rel_arb.
Definition fp64_greaterThan : word64 -> word64 -> bool := fp_rel_arb.
Definition fp64_greaterEqual : word64 -> word64 -> bool := fp_rel_arb.
Definition fp64_compare : word64 -> word64 -> float_compare := fp_compare_arb.
Definition fp64_sqrt : rounding -> word64 -> word64 := fp_rnd_unop_arb.
Definition fp64_roundToIntegral : rounding -> word64 -> word64 := fp_rnd_unop_arb.
Definition fp64_add : rounding -> word64 -> word64 -> word64 := fp_rnd_binop_arb.
Definition fp64_sub : rounding -> word64 -> word64 -> word64 := fp_rnd_binop_arb.
Definition fp64_mul : rounding -> word64 -> word64 -> word64 := fp_rnd_binop_arb.
Definition fp64_div : rounding -> word64 -> word64 -> word64 := fp_rnd_binop_arb.
Definition fp64_mul_add : rounding -> word64 -> word64 -> word64 -> word64 :=
  fp_rnd_triop_arb.
Definition fp64_mul_sub : rounding -> word64 -> word64 -> word64 -> word64 :=
  fp_rnd_triop_arb.
Definition fp64_to_int : rounding -> word64 -> option Z := fp_to_int_arb.
Definition int_to_fp64 : rounding -> Z -> word64 := int_to_fp_arb.

(** Conversions. *)
Definition fp32_to_fp64 : word32 -> word64 := fun _ => ARB.
Definition fp64_to_fp32 : rounding -> word64 -> word32 := fun _ _ => ARB.
