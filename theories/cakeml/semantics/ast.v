(** * CakeML [ast]: abstract syntax

    Port of [cakeml/semantics/astScript.sml].  Only the declarations needed
    so far by the compiler backend are ported: [shift], the name
    abbreviations [modN]/[varN]/[conN], and the operator datatypes
    [word_size], [thunk_mode], [thunk_op], [opb], [test] used by closLang.
    Not ported: [lit], [arith], [prim_type], [op], [op_class], [ast_t],
    [pat], [exp], [dec] and the rest of the source syntax.

    [opb]'s constructors [Lt]/[Gt] shadow Rocq's [comparison] constructors
    in importing files ([Datatypes.Lt]/[Datatypes.Gt]); [test]'s [Equal]
    is shadowed by ASM's [cmp] constructor in files importing [asm]. *)

From Galette Require Import Base.
From Galette.cakeml.basis.pure Require Import mlstring.

(*! HOL "cakeml/semantics/astScript.sml" "shift" *)
Inductive shift : Type := Lsl | Lsr | Asr | Ror.

#[global] Instance shift_eq_dec : EqDecision shift.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance shift_inhabited : Inhabited shift := Lsl.

(** Module names. *)
(*! HOL "cakeml/semantics/astScript.sml" "modN" *)
Abbreviation modN := mlstring.

(** Variable names. *)
(*! HOL "cakeml/semantics/astScript.sml" "varN" *)
Abbreviation varN := mlstring.

(** Constructor names (from datatype definitions). *)
(*! HOL "cakeml/semantics/astScript.sml" "conN" *)
Abbreviation conN := mlstring.

(*! HOL "cakeml/semantics/astScript.sml" "word_size" *)
Inductive word_size : Type := W8 | W64.

#[global] Instance word_size_eq_dec : EqDecision word_size.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance word_size_inhabited : Inhabited word_size := W8.

(*! HOL "cakeml/semantics/astScript.sml" "thunk_mode" *)
Inductive thunk_mode : Type := Evaluated | NotEvaluated.

#[global] Instance thunk_mode_eq_dec : EqDecision thunk_mode.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance thunk_mode_inhabited : Inhabited thunk_mode := Evaluated.

(*! HOL "cakeml/semantics/astScript.sml" "thunk_op" *)
Inductive thunk_op : Type :=
| AllocThunk : thunk_mode -> thunk_op
| UpdateThunk : thunk_mode -> thunk_op
| ForceThunk : thunk_op.

#[global] Instance thunk_op_eq_dec : EqDecision thunk_op.
Proof. intros x y; unfold Decision; decide equality; apply thunk_mode_eq_dec. Defined.
#[global] Instance thunk_op_inhabited : Inhabited thunk_op := ForceThunk.

(*! HOL "cakeml/semantics/astScript.sml" "opb" *)
Inductive opb : Type := Lt | Gt | Leq | Geq.

#[global] Instance opb_eq_dec : EqDecision opb.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance opb_inhabited : Inhabited opb := Lt.

(*! HOL "cakeml/semantics/astScript.sml" "test" *)
Inductive test : Type :=
| Equal : test
| Compare : opb -> test
| AltCompare : opb -> test.

#[global] Instance test_eq_dec : EqDecision test.
Proof. intros x y; unfold Decision; decide equality; apply opb_eq_dec. Defined.
#[global] Instance test_inhabited : Inhabited test := Equal.
