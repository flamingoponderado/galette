(** * CakeML [evaluateProps]: properties of the operational semantics (partial)

    Partial port of [cakeml/semantics/proofs/evaluatePropsScript.sml]: only
    [call_FFI_LENGTH] and the FFI-step relation [call_FFI_rel], used by the
    backend proofs ([lab_to_targetProof]).  The theorems about the source semantics are
    not ported. *)

From Galette Require Import Base.
From Galette.HOL.src.list.src Require Import list.
From Galette.cakeml.semantics.ffi Require Import ffi.
Open Scope N_scope.

(*! HOL "cakeml/semantics/proofs/evaluatePropsScript.sml" "call_FFI_LENGTH" *)
Theorem call_FFI_LENGTH : forall {F} (st : ffi_state F) index conf x new_st new_bytes,
  call_FFI st index conf x = FFI_return new_st new_bytes ->
  LENGTH x = LENGTH new_bytes.
Proof.
  intros F st index conf x new_st new_bytes H; unfold call_FFI in H.
  destruct (negb _); [|injection H as _ <-; reflexivity].
  destruct (ffi_state_oracle st index _ conf x) as [f' b'|o]; [|discriminate H].
  destruct (LENGTH b' =? LENGTH x) eqn:E; [|discriminate H].
  injection H as _ <-. symmetry. apply N.eqb_eq, E.
Qed.

(*! HOL "cakeml/semantics/proofs/evaluatePropsScript.sml" "call_FFI_rel_def" *)
Definition call_FFI_rel {F} (s1 s2 : ffi_state F) : Prop :=
  exists n conf bytes t, call_FFI s1 n conf bytes = FFI_return s2 t.
