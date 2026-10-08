(** * CakeML [ast]: abstract syntax

    Port of [cakeml/semantics/astScript.sml].  Only the declarations needed
    so far by the compiler backend are ported. *)

From Galette Require Import Base.

(*! HOL "cakeml/semantics/astScript.sml" "shift" *)
Inductive shift : Type := Lsl | Lsr | Asr | Ror.

#[global] Instance shift_eq_dec : EqDecision shift.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance shift_inhabited : Inhabited shift := Lsl.
