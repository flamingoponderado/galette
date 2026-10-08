(** * CakeML [ffi]: the foreign-function interface

    The FFI oracle model: an oracle answers each call from its internal
    state (type parameter [ffi]); the semantics records I/O events and
    observable behaviours. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.cakeml.basis.pure Require Import mlstring.
Open Scope N_scope.

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

(*! HOL "cakeml/semantics/ffi/ffiScript.sml" "oracle_result" *)
Inductive oracle_result (ffi : Type) : Type :=
| Oracle_return : ffi -> list word8 -> oracle_result ffi
| Oracle_final : ffi_outcome -> oracle_result ffi.
Arguments Oracle_return {ffi} _ _.
Arguments Oracle_final {ffi} _.

(*! HOL "cakeml/semantics/ffi/ffiScript.sml" "oracle_function" *)
Definition oracle_function (ffi : Type) : Type :=
  ffi -> list word8 -> list word8 -> oracle_result ffi.

(*! HOL "cakeml/semantics/ffi/ffiScript.sml" "oracle" *)
Definition oracle (ffi : Type) : Type := ffiname -> oracle_function ffi.

(*! HOL "cakeml/semantics/ffi/ffiScript.sml" "io_event" *)
Inductive io_event : Type :=
| IO_event : ffiname -> list word8 -> list (word8 * word8) -> io_event.

(*! HOL "cakeml/semantics/ffi/ffiScript.sml" "final_event" *)
Inductive final_event : Type :=
| Final_event : ffiname -> list word8 -> list word8 -> ffi_outcome -> final_event.

#[global] Instance io_event_eq_dec : EqDecision io_event.
Proof. intros [a b c] [d e f]; unfold Decision; decide equality; apply decide; exact _. Defined.
#[global] Instance io_event_inhabited : Inhabited io_event := IO_event (inhabitant _) [] [].
#[global] Instance final_event_eq_dec : EqDecision final_event.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

(*! HOL "cakeml/semantics/ffi/ffiScript.sml" "ffi_state" *)
Record ffi_state (ffi : Type) : Type := mk_ffi_state {
  ffi_state_oracle : oracle ffi;
  ffi_state_ffi_state : ffi;
  io_events : list io_event
}.
Arguments mk_ffi_state {ffi} _ _ _.
Arguments ffi_state_oracle {ffi} _.
Arguments ffi_state_ffi_state {ffi} _.
Arguments io_events {ffi} _.
(** HOL's field names [oracle] and [ffi_state] clash with the type names
    [oracle] and [ffi_state] in Rocq's single namespace, so (per AGENTS.md)
    they are prefixed with the record name: [ffi_state_oracle],
    [ffi_state_ffi_state]; [io_events] keeps its name. *)

(*! HOL "cakeml/semantics/ffi/ffiScript.sml" "initial_ffi_state_def" *)
Definition initial_ffi_state {ffi} (oc : oracle ffi) (f : ffi) : ffi_state ffi :=
  mk_ffi_state oc f [].

(*! HOL "cakeml/semantics/ffi/ffiScript.sml" "ffi_result" *)
Inductive ffi_result (ffi : Type) : Type :=
| FFI_return : ffi_state ffi -> list word8 -> ffi_result ffi
| FFI_final : final_event -> ffi_result ffi.
Arguments FFI_return {ffi} _ _.
Arguments FFI_final {ffi} _.

(*! HOL "cakeml/semantics/ffi/ffiScript.sml" "call_FFI_def" *)
Definition call_FFI {ffi} (st : ffi_state ffi) (s : ffiname) (conf bytes : list word8)
    : ffi_result ffi :=
  if negb (bool_decide (s = ExtCall (strlit []))) then
    match ffi_state_oracle st s (ffi_state_ffi_state st) conf bytes with
    | Oracle_return ffi' bytes' =>
        if LENGTH bytes' =? LENGTH bytes then
          FFI_return
            (mk_ffi_state (ffi_state_oracle st) ffi'
               (io_events st ++ [IO_event s conf (ZIP (bytes, bytes'))]))
            bytes'
        else FFI_final (Final_event s conf bytes FFI_failed)
    | Oracle_final outcome => FFI_final (Final_event s conf bytes outcome)
    end
  else FFI_return st bytes.

(*! HOL "cakeml/semantics/ffi/ffiScript.sml" "outcome" *)
Inductive outcome : Type :=
| Success : outcome
| Resource_limit_hit : outcome
| FFI_outcome : final_event -> outcome.

(*! HOL "cakeml/semantics/ffi/ffiScript.sml" "behaviour" *)
Inductive behaviour : Type :=
| Diverge : llist io_event -> behaviour
| Terminate : outcome -> list io_event -> behaviour
| Fail : behaviour.

(*! HOL "cakeml/semantics/ffi/ffiScript.sml" "trace_oracle_def" *)
Definition trace_oracle (s : ffiname) (io_trace : llist io_event) (conf input : list word8)
    : oracle_result (llist io_event) :=
  match LHD io_trace with
  | None => Oracle_final FFI_failed
  | Some (IO_event s' conf' bytes2) =>
      if bool_decide (s = s') && bool_decide (MAP fst bytes2 = input)
         && bool_decide (conf = conf')
      then Oracle_return (THE (LTL io_trace)) (MAP snd bytes2)
      else Oracle_final FFI_failed
  end.
