(** * HOL4 [arm8_step]: the ARMv8 step function used by CakeML

    Port of [HOL/examples/l3-machine-code/arm8/step/arm8_stepScript.sml]
    (partial): the next-state function [NextStateARM8] used by CakeML's
    ARMv8 target and the memory read helpers [mem_half], [mem_word],
    [mem_dword].

    Not ported: the theorems for the step evaluator [arm8_stepLib]
    ([NextStateARM8], [concat16], ..., [LoadCheck]), whose use in HOL is
    through ML automation. *)

From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.examples.l3_machine_code.arm8.model Require Import arm8.
Open Scope N_scope.
Local Open Scope word_scope.

(*! HOL "HOL/examples/l3-machine-code/arm8/step/arm8_stepScript.sml" "NextStateARM8_def" *)
Definition NextStateARM8 (s0 : arm8_state) : option arm8_state :=
  let s1 := Next s0 in
  if bool_decide (arm8_state_exception s1 = NoException) then Some s1 else None.

(*! HOL "HOL/examples/l3-machine-code/arm8/step/arm8_stepScript.sml" "mem_half_def" *)
Definition mem_half (m : word64 -> word8) (a : word64) : word16 :=
  (m (a + n2w 1) @@ m a : word16).

(*! HOL "HOL/examples/l3-machine-code/arm8/step/arm8_stepScript.sml" "mem_word_def" *)
Definition mem_word (m : word64 -> word8) (a : word64) : word32 :=
  (m (a + n2w 3) @@ (m (a + n2w 2) @@ (m (a + n2w 1) @@ m a : word16) : word 24) : word32).

(*! HOL "HOL/examples/l3-machine-code/arm8/step/arm8_stepScript.sml" "mem_dword_def" *)
Definition mem_dword (m : word64 -> word8) (a : word64) : word64 :=
  (m (a + n2w 7) @@ (m (a + n2w 6) @@ (m (a + n2w 5) @@ (m (a + n2w 4) @@
   (m (a + n2w 3) @@ (m (a + n2w 2) @@ (m (a + n2w 1) @@ m a : word16) : word 24) : word32)
   : word 40) : word 48) : word 56) : word64).
