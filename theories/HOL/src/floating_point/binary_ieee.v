(** * HOL4 [binary_ieee]: IEEE-754 binary floating point (partial)

    Partial port of [HOL/src/floating-point/binary_ieeeScript.sml]: the
    enumerations [rounding] and [float_compare], which appear in the
    signatures of the machine-level operations ([machine_ieee]) used by
    CakeML's [asmSem] and the L3 models, and the [flags] record with HOL's
    flag definitions ([clear_flags], [invalidop_flags], [dividezero_flags]).
    The [float] record, the real-valued semantics and the rounding
    functions are not ported.

    The [flags] fields carry the record-type prefix ([flags_InvalidOp], ...)
    because HOL's field selectors and updates are constants named
    [flags_<field>] and [flags_<field>_fupd], and the L3 generator emits
    those names. *)

From Galette Require Import Base.

(*! HOL "HOL/src/floating-point/binary_ieeeScript.sml" "flags" *)
Record flags : Type := {
  flags_DivideByZero : bool;
  flags_InvalidOp : bool;
  flags_Overflow : bool;
  flags_Precision : bool;
  flags_Underflow_BeforeRounding : bool;
  flags_Underflow_AfterRounding : bool
}.

#[global] Instance flags_eq_dec : EqDecision flags.
Proof. intros x y; unfold Decision; decide equality; decide equality. Defined.
#[global] Instance flags_inhabited : Inhabited flags :=
  {| flags_DivideByZero := false; flags_InvalidOp := false;
     flags_Overflow := false; flags_Precision := false;
     flags_Underflow_BeforeRounding := false;
     flags_Underflow_AfterRounding := false |}.

(** ** Record field updates (HOL [flags_<field>_fupd]) *)

Definition flags_DivideByZero_fupd (f : bool -> bool) (r : flags) : flags :=
  {| flags_DivideByZero := f (flags_DivideByZero r);
     flags_InvalidOp := flags_InvalidOp r;
     flags_Overflow := flags_Overflow r;
     flags_Precision := flags_Precision r;
     flags_Underflow_BeforeRounding := flags_Underflow_BeforeRounding r;
     flags_Underflow_AfterRounding := flags_Underflow_AfterRounding r |}.

Definition flags_InvalidOp_fupd (f : bool -> bool) (r : flags) : flags :=
  {| flags_DivideByZero := flags_DivideByZero r;
     flags_InvalidOp := f (flags_InvalidOp r);
     flags_Overflow := flags_Overflow r;
     flags_Precision := flags_Precision r;
     flags_Underflow_BeforeRounding := flags_Underflow_BeforeRounding r;
     flags_Underflow_AfterRounding := flags_Underflow_AfterRounding r |}.

Definition flags_Overflow_fupd (f : bool -> bool) (r : flags) : flags :=
  {| flags_DivideByZero := flags_DivideByZero r;
     flags_InvalidOp := flags_InvalidOp r;
     flags_Overflow := f (flags_Overflow r);
     flags_Precision := flags_Precision r;
     flags_Underflow_BeforeRounding := flags_Underflow_BeforeRounding r;
     flags_Underflow_AfterRounding := flags_Underflow_AfterRounding r |}.

Definition flags_Precision_fupd (f : bool -> bool) (r : flags) : flags :=
  {| flags_DivideByZero := flags_DivideByZero r;
     flags_InvalidOp := flags_InvalidOp r;
     flags_Overflow := flags_Overflow r;
     flags_Precision := f (flags_Precision r);
     flags_Underflow_BeforeRounding := flags_Underflow_BeforeRounding r;
     flags_Underflow_AfterRounding := flags_Underflow_AfterRounding r |}.

Definition flags_Underflow_BeforeRounding_fupd (f : bool -> bool) (r : flags) : flags :=
  {| flags_DivideByZero := flags_DivideByZero r;
     flags_InvalidOp := flags_InvalidOp r;
     flags_Overflow := flags_Overflow r;
     flags_Precision := flags_Precision r;
     flags_Underflow_BeforeRounding := f (flags_Underflow_BeforeRounding r);
     flags_Underflow_AfterRounding := flags_Underflow_AfterRounding r |}.

Definition flags_Underflow_AfterRounding_fupd (f : bool -> bool) (r : flags) : flags :=
  {| flags_DivideByZero := flags_DivideByZero r;
     flags_InvalidOp := flags_InvalidOp r;
     flags_Overflow := flags_Overflow r;
     flags_Precision := flags_Precision r;
     flags_Underflow_BeforeRounding := flags_Underflow_BeforeRounding r;
     flags_Underflow_AfterRounding := f (flags_Underflow_AfterRounding r) |}.

(*! HOL "HOL/src/floating-point/binary_ieeeScript.sml" "clear_flags_def" *)
Definition clear_flags : flags :=
  {| flags_DivideByZero := false; flags_InvalidOp := false;
     flags_Overflow := false; flags_Precision := false;
     flags_Underflow_BeforeRounding := false;
     flags_Underflow_AfterRounding := false |}.

(*! HOL "HOL/src/floating-point/binary_ieeeScript.sml" "invalidop_flags_def" *)
Definition invalidop_flags : flags :=
  flags_InvalidOp_fupd (fun _ => true) clear_flags.

(*! HOL "HOL/src/floating-point/binary_ieeeScript.sml" "dividezero_flags_def" *)
Definition dividezero_flags : flags :=
  flags_DivideByZero_fupd (fun _ => true) clear_flags.

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
