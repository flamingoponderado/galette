(** * CakeML [ffi]: the foreign-function interface (names)

    Partial port of [cakeml/semantics/ffi/ffiScript.sml]: the datatypes
    naming FFI calls, used by the assembler ([lab_to_target]).  The FFI
    oracle, state and event types (semantics) are not ported yet. *)

From Galette Require Import Base.
From Galette.cakeml.basis.pure Require Import mlstring.

(*! HOL "cakeml/semantics/ffi/ffiScript.sml" "ffi_outcome" *)
Inductive ffi_outcome : Type := FFI_failed | FFI_diverged.

(*! HOL "cakeml/semantics/ffi/ffiScript.sml" "shmem_op" *)
Inductive shmem_op : Type := MappedRead | MappedWrite.

(*! HOL "cakeml/semantics/ffi/ffiScript.sml" "ffiname" *)
Inductive ffiname : Type :=
| ExtCall : mlstring -> ffiname
| SharedMem : shmem_op -> ffiname.

#[global] Instance ffi_outcome_eq_dec : EqDecision ffi_outcome.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance shmem_op_eq_dec : EqDecision shmem_op.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance ffiname_eq_dec : EqDecision ffiname.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.
#[global] Instance ffiname_inhabited : Inhabited ffiname := SharedMem MappedRead.
