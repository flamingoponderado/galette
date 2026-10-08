(** * CakeML [fpSem]: floating-point operations

    Partial port of [cakeml/semantics/fpSemScript.sml]: only the operator
    datatypes [fp_cmp], [fp_uop], [fp_bop], [fp_top] (needed by closLang's
    [word_op]).  The semantic functions ([fp_cmp_def], [fp_uop_def], ...,
    over [machine_ieee]) are not ported. *)

From Galette Require Import Base.

(*! HOL "cakeml/semantics/fpSemScript.sml" "fp_cmp" 9 *)
Inductive fp_cmp : Type :=
  FP_Less | FP_LessEqual | FP_Greater | FP_GreaterEqual | FP_Equal.

#[global] Instance fp_cmp_eq_dec : EqDecision fp_cmp.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance fp_cmp_inhabited : Inhabited fp_cmp := FP_Less.

(*! HOL "cakeml/semantics/fpSemScript.sml" "fp_uop" *)
Inductive fp_uop : Type := FP_Abs | FP_Neg | FP_Sqrt.

#[global] Instance fp_uop_eq_dec : EqDecision fp_uop.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance fp_uop_inhabited : Inhabited fp_uop := FP_Abs.

(*! HOL "cakeml/semantics/fpSemScript.sml" "fp_bop" *)
Inductive fp_bop : Type := FP_Add | FP_Sub | FP_Mul | FP_Div.

#[global] Instance fp_bop_eq_dec : EqDecision fp_bop.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance fp_bop_inhabited : Inhabited fp_bop := FP_Add.

(*! HOL "cakeml/semantics/fpSemScript.sml" "fp_top" *)
Inductive fp_top : Type := FP_Fma.

#[global] Instance fp_top_eq_dec : EqDecision fp_top.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance fp_top_inhabited : Inhabited fp_top := FP_Fma.
