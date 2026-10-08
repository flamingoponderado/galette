(** * HOL4 [binary_ieee]: IEEE-754 binary floating point (partial)

    Partial port of [HOL/src/floating-point/binary_ieeeScript.sml]: only the
    enumerations [rounding] and [float_compare], which appear in the
    signatures of the machine-level operations ([machine_ieee]) used by
    CakeML's [asmSem] and the L3 RISC-V model.  The [float] record, the
    real-valued semantics and the rounding functions are not ported. *)

From Galette Require Import Base.

(*! HOL "HOL/src/floating-point/binary_ieeeScript.sml" "rounding" *)
Inductive rounding : Type :=
| roundTiesToEven
| roundTowardPositive
| roundTowardNegative
| roundTowardZero.

#[global] Instance rounding_eq_dec : EqDecision rounding.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance rounding_inhabited : Inhabited rounding := roundTiesToEven.

(*! HOL "HOL/src/floating-point/binary_ieeeScript.sml" "float_compare" 755 *)
Inductive float_compare : Type := LT | EQ | GT | UN.

#[global] Instance float_compare_eq_dec : EqDecision float_compare.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance float_compare_inhabited : Inhabited float_compare := LT.
