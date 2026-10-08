(** * CakeML [bvl]: the BVL intermediate language (syntax)

    Partial port of [cakeml/compiler/backend/bvlScript.sml]: only the
    datatype [exp].  The overloads [mk_unit]/[mk_elem_at] and the
    functions/theorems on [exp] are not ported.  [exp]'s constructors
    shadow [closLang]'s of the same names; [op] is [closLang.op]. *)

From Galette Require Import Base.
From Galette.cakeml.compiler.backend Require Import closLang.
Open Scope N_scope.
Local Set Warnings "-register-all".

(*! HOL "cakeml/compiler/backend/bvlScript.sml" "exp" *)
Inductive exp : Type :=
| Var : N -> exp
| If : exp -> exp -> exp -> exp
| Let : list exp -> exp -> exp
| Raise : exp -> exp
| Handle : exp -> exp -> exp
| Tick : exp -> exp
| Call : N -> option N -> list exp -> exp
| Force : N -> N -> exp
| Op : closLang.op -> list exp -> exp.

#[global] Instance exp_inhabited : Inhabited exp := Var 0.
