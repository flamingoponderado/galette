(** * Classical decisions (Galette infrastructure, no HOL original)

    In HOL every proposition is a boolean.  A ported statement that applies a
    boolean combinator (e.g. [EVERY]) to a non-computable predicate writes
    [⌜P⌝], which is [bool_decide P] with the classical instance below.

    Compiler (executable) modules must not import this module: an executable
    definition that needed this instance would fail at run time.
    [scripts/check-hol-refs.py] does not check this; extraction tests do. *)

From Galette Require Import Base.

#[global] Instance classical_decision (P : Prop) : Decision P | 1000 :=
  classical_dec P.

Notation "⌜ P ⌝" := (bool_decide P) (format "⌜ P ⌝").
