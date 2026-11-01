(** * CakeML [arm8_target]: the ARMv8 (AArch64) target configuration

    Port of [cakeml/compiler/encoders/arm8/arm8_targetScript.sml]: the
    encoder of ASM instructions into ARMv8 machine code (through the L3
    model's instruction AST and its [Encode]), the target configuration
    [arm8_config] and the target record [arm8_target].

    HOL elaborates this script under [wordsLib.guess_lengths ()], which
    gives every [(h >< l)] extract with an otherwise unconstrained result the
    width [h + 1 - l]; where Rocq cannot infer such a width from the
    context it is written as an ascription.  [word_scope] is open, so the
    boolean connectives of HOL conditions are written in [%bool].  The ML
    values [temp], [off_min9], ..., [jump_max] are antiquoted into HOL's
    definitions as evaluated literals; here they are constants with the
    defining expression of the ML [val].

    L3's width-specialised constructors [AddSubImmediate@64], ... are
    [AddSubImmediate_64], ... (see the model,
    [theories/HOL/examples/l3_machine_code/arm8/model/arm8.v]), and the
    model's tuples are right-nested as in HOL.

    HOL leaves the cases [Add] and [Sub] of [bop_enc] unspecified; they are
    [ARB] here ([arm8_ast] never uses them).

    Not ported: the generated rewrites [arm8_config], [arm8_asm_ok]
    (theorems computed by [asmLib]) and the bootstrap-translation lemma
    [v2w_Ones]. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.n_bit Require Import words bitstring.
From Galette.HOL.src.integer Require Import integer_word.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.n_bit Require Import alignment.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.examples.l3_machine_code.arm8.model Require Import arm8.
From Galette.HOL.examples.l3_machine_code.arm8.step Require Import arm8_step.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.HOL.src.combin Require combin.
From Galette.HOL.examples.machine_code.hoare_triple Require set_sep.
From Galette.cakeml.compiler.encoders.asm Require asmProps asmSem.
Open Scope N_scope.
Local Open Scope word_scope.

(** ASM's constructors are imported after the model's names; the model's
    [Mem] (a function) is not used here. *)

(** ** The next-state function *)

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_next_def" *)
Definition arm8_next : arm8_state -> arm8_state := THE ∘ NextStateARM8.

(** ** Valid ARMv8 states *)

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_ok_def" *)
Definition arm8_ok (ms : arm8_state) : bool :=
  (bool_decide (ProcState_EL (arm8_state_PSTATE ms) = n2w 0) &&
   negb (SCTLRType_E0E (arm8_state_SCTLR_EL1 ms)) &&
   negb (SCTLRType_SA0 (arm8_state_SCTLR_EL1 ms)) &&
   negb (TCR_EL1_TBI1 (arm8_state_TCR_EL1 ms)) &&
   negb (TCR_EL1_TBI0 (arm8_state_TCR_EL1 ms)) &&
   bool_decide (arm8_state_exception ms = NoException) &&
   aligned 2 (arm8_state_PC ms))%bool.

(** ** Encode ASM instructions to ARM bytes *)

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_encode_fail_def" *)
Definition arm8_encode_fail : list instruction := [NoOperation].

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_encode_def" *)
Definition arm8_encode (i : instruction) : list word8 :=
  match Encode i with
  | ARM8 w => [(7 >< 0) w; (15 >< 8) w; (23 >< 16) w; (31 >< 24) w]
  | _ => [n2w 0; n2w 0; n2w 0; n2w 0]
  end.

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "bop_enc_def" *)
Definition bop_enc (b : binop) : LogicalOp :=
  match b with
  | And => LogicalOp_AND
  | Or => LogicalOp_ORR
  | Xor => LogicalOp_EOR
  | Add => ARB
  | Sub => ARB
  end.

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "cmp_cond_def" *)
Definition cmp_cond (c : cmp) : word4 :=
  match c with
  | Less => n2w 11
  | Lower => n2w 3
  | Equal => n2w 0
  | Test => n2w 0
  | NotLess => n2w 10
  | NotLower => n2w 2
  | NotEqual => n2w 1
  | NotTest => n2w 1
  end.

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_shv_def" *)
Definition arm8_shv (sh : shift) : ShiftType :=
  match sh with
  | Lsl => ShiftType_LSL
  | Lsr => ShiftType_LSR
  | Asr => ShiftType_ASR
  | Ror => ShiftType_ROR
  end.

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_enc_mov_imm_def" *)
Definition arm8_enc_mov_imm (i : word64) : option (word16 * word2) :=
  if bool_decide ((i && n2w 0xFFFFFFFFFFFF0000) = n2w 0) then
    Some ((15 >< 0) i, n2w 0)
  else if bool_decide ((i && n2w 0xFFFFFFFF0000FFFF) = n2w 0) then
    Some ((31 >< 16) i, n2w 1)
  else if bool_decide ((i && n2w 0xFFFF0000FFFFFFFF) = n2w 0) then
    Some ((47 >< 32) i, n2w 2)
  else if bool_decide ((i && n2w 0x0000FFFFFFFFFFFF) = n2w 0) then
    Some ((63 >< 48) i, n2w 3)
  else
    None.

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "temp" *)
Definition temp : word5 := n2w 26.

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_load_store_ast_def" *)
Definition arm8_load_store_ast (ls : MemOp) (r1 r2 : N) (a : word64) : list instruction :=
  let unsigned := negb (word_msb a) in
  if (negb (bool_decide (a = sw2sw ((8 >< 0) a : word 9))) &&
      implb unsigned
        (negb (bool_decide (a = w2w ((11 >< 0) (a >>> 3) : word12) << 3))))%bool then
    let '(b, c) := if unsigned then (a - n2w 0xFF, n2w 0xFF)
                   else (- a - n2w 0x100, - n2w 0x100) in
      [Data (AddSubImmediate_64 (n2w 1, (negb unsigned, (false, (b, (n2w r2, temp))))));
       LoadStore
         (LoadStoreImmediate_64
            (n2w 3, (false, (ls, (AccType_NORMAL, (false, (false, (false, (false, (false, (unsigned, (c,
             (temp, n2w r1)))))))))))))]
  else
    [LoadStore
       (LoadStoreImmediate_64
          (n2w 3, (false, (ls, (AccType_NORMAL, (false, (false, (false, (false, (false, (unsigned, (a,
           (n2w r2, n2w r1)))))))))))))].

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_load_store_ast32_def" *)
Definition arm8_load_store_ast32 (ls : MemOp) (r1 r2 : N) (a : word64) : list instruction :=
  let unsigned := negb (word_msb a) in
  if (negb (bool_decide (a = sw2sw ((8 >< 0) a : word 9))) &&
      implb unsigned
        (negb (bool_decide (a = w2w ((11 >< 0) (a >>> 2) : word12) << 2))))%bool then
    let '(b, c) := if unsigned then (a - n2w 0xFF, n2w 0xFF)
                   else (- a - n2w 0x100, - n2w 0x100) in
      [Data (AddSubImmediate_64 (n2w 1, (negb unsigned, (false, (b, (n2w r2, temp))))));
       LoadStore
         (LoadStoreImmediate_32
            (n2w 2, (true, (ls, (AccType_NORMAL, (false, (false, (false, (false, (false, (unsigned, (c,
             (temp, n2w r1)))))))))))))]
  else
    [LoadStore
       (LoadStoreImmediate_32
          (n2w 2, (true, (ls, (AccType_NORMAL, (false, (false, (false, (false, (false, (unsigned, (a,
           (n2w r2, n2w r1)))))))))))))].

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_load_store_ast16_def" *)
Definition arm8_load_store_ast16 (ls : MemOp) (r1 r2 : N) (a : word64) : list instruction :=
  let unsigned := negb (word_msb a) in
  if (negb (bool_decide (a = sw2sw ((8 >< 0) a : word 9))) &&
      implb unsigned
        (negb (bool_decide (a = w2w ((11 >< 0) (a >>> 1) : word12) << 1))))%bool then
    let '(b, c) := if unsigned then (a - n2w 0xFF, n2w 0xFF)
                   else (- a - n2w 0x100, - n2w 0x100) in
      [Data (AddSubImmediate_64 (n2w 1, (negb unsigned, (false, (b, (n2w r2, temp))))));
       LoadStore
         (LoadStoreImmediate_16
            (n2w 1, (true, (ls, (AccType_NORMAL, (false, (false, (false, (false, (false, (unsigned, (c,
             (temp, n2w r1)))))))))))))]
  else
    [LoadStore
       (LoadStoreImmediate_16
          (n2w 1, (true, (ls, (AccType_NORMAL, (false, (false, (false, (false, (false, (unsigned, (a,
           (n2w r2, n2w r1)))))))))))))].

(** HOL's clauses for [Inst (Arith (Binop bop r1 r2 (Reg r3)))] and for an
    immediate case on [bop] with a catch-all [x]; the order of the
    patterns is HOL's. *)
(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_ast_def" *)
Definition arm8_ast (x : asm 64) : list instruction :=
  match x with
  | Inst Skip => [NoOperation]
  | Inst (Const r i) =>
      match arm8_enc_mov_imm i with
      | Some (imm16, hw) =>
          [Data (MoveWide_64 (n2w 1, (MoveWideOp_Z, (hw, (imm16, n2w r)))))]
      | None =>
          match arm8_enc_mov_imm (¬ i) with
          | Some (imm16, hw) =>
              [Data (MoveWide_64 (n2w 1, (MoveWideOp_N, (hw, (imm16, n2w r)))))]
          | None =>
              if IS_SOME (EncodeBitMask i) then
                [Data (LogicalImmediate_64
                         (n2w 1, (LogicalOp_ORR, (false, (i, (n2w 0x1F, n2w r))))))]
              else
                [Data (MoveWide_64
                         (n2w 1, (MoveWideOp_K, (n2w 0, ((15 >< 0) i, n2w r)))));
                 Data (MoveWide_64
                         (n2w 1, (MoveWideOp_K, (n2w 1, ((31 >< 16) i, n2w r)))));
                 Data (MoveWide_64
                         (n2w 1, (MoveWideOp_K, (n2w 2, ((47 >< 32) i, n2w r)))));
                 Data (MoveWide_64
                         (n2w 1, (MoveWideOp_K, (n2w 3, ((63 >< 48) i, n2w r)))))]
          end
      end
  | Inst (Arith (Binop bop r1 r2 (Reg r3))) =>
      [Data
        match bop with
        | Add => AddSubShiftedRegister_64
                   (n2w 1, (false, (false, (ShiftType_LSL, (n2w r3, (n2w 0, (n2w r2, n2w r1)))))))
        | Sub => AddSubShiftedRegister_64
                   (n2w 1, (true, (false, (ShiftType_LSL, (n2w r3, (n2w 0, (n2w r2, n2w r1)))))))
        | x => LogicalShiftedRegister_64
                   (n2w 1, (bop_enc x, (false, (false, (ShiftType_LSL, (0,
                    (n2w r3, (n2w r2, n2w r1))))))))
        end]
  | Inst (Arith (Binop bop r1 r2 (Imm i))) =>
      [Data
        match bop with
        | Add => AddSubImmediate_64 (n2w 1, (false, (false, (i, (n2w r2, n2w r1)))))
        | Sub => AddSubImmediate_64 (n2w 1, (true, (false, (i, (n2w r2, n2w r1)))))
        | Xor => if bool_decide (i = - n2w 1) then
                   LogicalShiftedRegister_64
                     (n2w 1, (LogicalOp_ORR, (true, (false, (ShiftType_LSL, (0, (n2w r2, (n2w 31,
                      n2w r1))))))))
                 else
                   LogicalImmediate_64
                     (n2w 1, (LogicalOp_EOR, (false, (i, (n2w r2, n2w r1)))))
        | x => LogicalImmediate_64 (n2w 1, (bop_enc x, (false, (i, (n2w r2, n2w r1)))))
        end]
  | Inst (Arith (Shift sh r1 r2 (Imm i))) =>
      let n := w2n i in
      match sh with
      | Lsl => let i := (n2w n : word6) in
               let r := - i in let s := n2w 63 - i in
               match DecodeBitMasks (Mw:=64) (n2w 1, (s, (r, false))) with
               | Some (wmask, tmask) =>
                   [Data
                      (BitfieldMove_64
                         (n2w 1, (true, (false, (wmask, (tmask, (w2n r, (w2n s, (n2w r2,
                          n2w r1)))))))))]
               | None => arm8_encode_fail
               end
      | Ror => [Data (ExtractRegister_64 (n2w 1, (n2w n, (n2w r2, (n2w r2, n2w r1)))))]
      | x => match DecodeBitMasks (Mw:=64) (n2w 1, (n2w 63, (n2w n, false))) with
             | Some (wmask, tmask) =>
                 [Data
                   (BitfieldMove_64
                     (n2w 1, (true, (bool_decide (x = Asr), (wmask, (tmask, (n, (63, (n2w r2,
                      n2w r1)))))))))]
             | None => arm8_encode_fail
             end
      end
  | Inst (Arith (Shift sh r1 r2 (Reg r))) =>
      [Data (Shift_64 (n2w 1, (arm8_shv sh, (n2w r, (n2w r2, n2w r1)))))]
  | Inst (Arith (Div r1 r2 r3)) =>
      [Data (Division_64 (n2w 1, (false, (n2w r3, (n2w r2, n2w r1)))))]
  | Inst (Arith (LongMul r1 r2 r3 r4)) =>
      [Data (MultiplyHigh (false, (n2w r4, (n2w r3, n2w r1))));
       Data (MultiplyAddSub_64 (n2w 1, (false, (n2w r4, (n2w 31, (n2w r3, n2w r2))))))]
  | Inst (Arith (LongDiv _ _ _ _ _)) => arm8_encode_fail
  | Inst (Arith (AddCarry r1 r2 r3 r4)) =>
      [Data (AddSubImmediate_64 (n2w 1, (true, (true, (n2w 0, (n2w r4, n2w 0x1F))))));
       Data (ConditionalCompareImmediate_64
               (n2w 1, (false, (n2w 0, (n2w 0, ((false, (false, (true, false))), n2w r2))))));
       Data (AddSubCarry_64 (n2w 1, (false, (true, (n2w r3, (n2w r2, n2w r1))))));
       Data (MoveWide_64 (n2w 1, (MoveWideOp_Z, (n2w 0, (n2w 0, n2w r4)))));
       Data (AddSubCarry_64 (n2w 1, (false, (false, (n2w 31, (n2w r4, n2w r4))))))]
  | Inst (Arith (AddOverflow r1 r2 r3 r4)) =>
      [Data (AddSubShiftedRegister_64
               (n2w 1, (false, (true, (ShiftType_LSL, (n2w r3, (n2w 0, (n2w r2, n2w r1))))))));
       Data (ConditionalSelect_64 (n2w 1, (false, (true, (n2w 7, (n2w 31, (n2w 31, n2w r4)))))))]
  | Inst (Arith (SubOverflow r1 r2 r3 r4)) =>
      [Data (AddSubShiftedRegister_64
               (n2w 1, (true, (true, (ShiftType_LSL, (n2w r3, (n2w 0, (n2w r2, n2w r1))))))));
       Data (ConditionalSelect_64 (n2w 1, (false, (true, (n2w 7, (n2w 31, (n2w 31, n2w r4)))))))]
  | Inst (Mem Load r1 (Addr r2 a)) =>
      arm8_load_store_ast MemOp_LOAD r1 r2 a
  | Inst (Mem Load32 r1 (Addr r2 a)) =>
      arm8_load_store_ast32 MemOp_LOAD r1 r2 a
  | Inst (Mem Load16 r1 (Addr r2 a)) =>
      arm8_load_store_ast16 MemOp_LOAD r1 r2 a
  | Inst (Mem Load8 r1 (Addr r2 a)) =>
      [LoadStore
         (LoadStoreImmediate_8
            (n2w 0, (false, (MemOp_LOAD, (AccType_NORMAL, (false, (false, (false, (false, (false,
             (negb (word_msb a), (a, (n2w r2, n2w r1)))))))))))))]
  | Inst (Mem Store r1 (Addr r2 a)) =>
      arm8_load_store_ast MemOp_STORE r1 r2 a
  | Inst (Mem Store32 r1 (Addr r2 a)) =>
      arm8_load_store_ast32 MemOp_STORE r1 r2 a
  | Inst (Mem Store16 r1 (Addr r2 a)) =>
      arm8_load_store_ast16 MemOp_STORE r1 r2 a
  | Inst (Mem Store8 r1 (Addr r2 a)) =>
      [LoadStore
         (LoadStoreImmediate_8
            (n2w 0, (false, (MemOp_STORE, (AccType_NORMAL, (false, (false, (false, (false, (false,
             (negb (word_msb a), (a, (n2w r2, n2w r1)))))))))))))]
  | Inst (FP _) => arm8_encode_fail
  | Jump a =>
      [Branch (BranchImmediate (a, BranchType_JMP))]
  | JumpCmp cmp r1 (Reg r2) a =>
      [Data (if asmSem.is_test cmp then
               LogicalShiftedRegister_64
                 (n2w 1, (LogicalOp_AND, (false, (true, (ShiftType_LSL, (0,
                  (n2w r2, (n2w r1, n2w 0x1F))))))))
             else
               AddSubShiftedRegister_64
                 (n2w 1, (true, (true, (ShiftType_LSL, (n2w r2, (n2w 0, (n2w r1, n2w 0x1F))))))));
       Branch (BranchConditional (a - n2w 4, cmp_cond cmp))]
  | JumpCmp cmp r (Imm i) a =>
      [Data (if asmSem.is_test cmp then
               LogicalImmediate_64
                 (n2w 1, (LogicalOp_AND, (true, (i, (n2w r, n2w 0x1F)))))
             else
               AddSubImmediate_64 (n2w 1, (true, (true, (i, (n2w r, n2w 0x1F))))));
       Branch (BranchConditional (a - n2w 4, cmp_cond cmp))]
  | Call a =>
      [Branch (BranchImmediate (a, BranchType_CALL))]
  | JumpReg r =>
      [Branch (BranchRegister (n2w r, BranchType_JMP))]
  | Loc r i =>
      if ((sw2sw (INT_MINw : word20) <= i) && (i <= sw2sw (INT_MAXw : word20)))%bool
      then
        [Address (false, (i, n2w r))]
      else
        [Address (false, (n2w 0, n2w r));
         Data (MoveWide_64
                 (n2w 1, (MoveWideOp_K, (n2w 0, ((15 >< 0) i, temp)))));
         Data (MoveWide_64
                 (n2w 1, (MoveWideOp_K, (n2w 1, ((31 >< 16) i, temp)))));
         Data (MoveWide_64
                 (n2w 1, (MoveWideOp_K, (n2w 2, ((47 >< 32) i, temp)))));
         Data (MoveWide_64
                 (n2w 1, (MoveWideOp_K, (n2w 3, ((63 >< 48) i, temp)))));
         Data (AddSubShiftedRegister_64
                 (n2w 1, (false, (false, (ShiftType_LSL, (temp, (n2w 0, (n2w r, n2w r))))))))]
  end.

(** HOL marks [arm8_enc_def] [nocompute] (HOL evaluates it through
    [arm8_targetLib]); here it is directly executable. *)
(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_enc_def" *)
Definition arm8_enc : asm 64 -> list word8 :=
  combin.C LIST_BIND arm8_encode ∘ arm8_ast.

(** ** Configuration for ARMv8 *)

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "off_min9" *)
Definition off_min9 : word64 := sw2sw (INT_MINw : word 9).

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "off_max9" *)
Definition off_max9 : word64 := sw2sw (INT_MAXw : word 9).

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "off_max12" *)
Definition off_max12 : word64 := w2w (UINT_MAXw : word12).

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "off_min" *)
Definition off_min : word64 := - off_max12 + off_min9.

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "off_max" *)
Definition off_max : word64 := off_max12 + off_max9.

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "loc_min" *)
Definition loc_min : word64 := sw2sw (INT_MINw : word32).

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "loc_max" *)
Definition loc_max : word64 := sw2sw (INT_MAXw : word32).

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "cjump_min" *)
Definition cjump_min : word64 := sw2sw (INT_MINw : word21) + n2w 4.

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "cjump_max" *)
Definition cjump_max : word64 := sw2sw (INT_MAXw : word21) + n2w 4.

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "jump_min" *)
Definition jump_min : word64 := sw2sw (INT_MINw : word 28).

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "jump_max" *)
Definition jump_max : word64 := sw2sw (INT_MAXw : word 28).

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "valid_immediate_def" *)
Definition valid_immediate (c : binop + cmp) (i : word64) : bool :=
  if bool_decide (c IN (inl Add INSERT inl Sub INSERT
                        inr Less INSERT inr Lower INSERT inr Equal INSERT
                        inr NotLess INSERT inr NotLower INSERT inr NotEqual INSERT {})) then
    (bool_decide (word_and (¬ (n2w 0xFFF)) i = n2w 0) ||
     bool_decide (word_and (¬ (n2w 0xFFF000)) i = n2w 0))%bool
  else
    IS_SOME (EncodeBitMask i).

(** Register x18 is reserved on some platforms (e.g. Apple's); 26 is the
    encoder's temporary [temp]; 31 is the zero register / stack pointer. *)
(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_config_def" *)
Definition arm8_config : asm_config 64 := {|
  ISA := ARMv8;
  encode := arm8_enc;
  reg_count := 32;
  fp_reg_count := 0;
  avoid_regs := [18; 26; 31];
  link_reg := Some 30;
  two_reg_arith := false;
  big_endian := false;
  code_alignment := 2;
  valid_imm := valid_immediate;
  addr_offset := (off_min, off_max);
  hw_offset := (off_min, off_max);
  byte_offset := (off_min9, off_max12);
  jump_offset := (jump_min, jump_max);
  cjump_offset := (cjump_min, cjump_max);
  loc_offset := (loc_min, loc_max)
|}.

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_proj_def" *)
Definition arm8_proj (d : word64 -> Prop) (s : arm8_state) :
    ProcState * (SCTLRType * (TCR_EL1 * (exception * ((word5 -> word64) *
    ((word64 * word8 -> Prop) * word64))))) :=
  (arm8_state_PSTATE s, (arm8_state_SCTLR_EL1 s, (arm8_state_TCR_EL1 s,
   (arm8_state_exception s, (arm8_state_REG s,
   (set_sep.fun2set (arm8_state_MEM s, d), arm8_state_PC s)))))).

(** HOL's record literal leaves the field [get_fp_reg] unset (its value is
    that of [ARB]); here it is [ARB]. *)
(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_target_def" *)
Definition arm8_target :=
  asmProps.mk_target
    arm8_config
    arm8_next
    arm8_state_PC
    (fun s => arm8_state_REG s ∘ n2w)
    ARB
    arm8_state_MEM
    arm8_ok
    arm8_proj.

(** ** Lemmas used in bootstrap translation *)

(** [log2] recurses on [n DIV 2]; it is computed by [N.log2] and HOL's
    equation is the theorem [log2_def]. *)
Definition log2 (n : N) : N := if n <? 2 then 0 else N.log2 n.

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "log2_def" *)
Theorem log2_def : forall n, log2 n = (if n <? 2 then 0 else log2 (n DIV 2) + 1)%N.
Proof.
  intros n; unfold log2.
  destruct (N.ltb_spec n 2) as [Hn|Hn]; [reflexivity|].
  destruct (N.ltb_spec (n DIV 2) 2) as [Hd|Hd].
  - assert (n DIV 2 = 1)%N.
    { assert (1 <= n DIV 2)%N by (apply N.div_le_lower_bound; lia). lia. }
    assert (Hn' : (2 <= n < 4)%N) by (pose proof (N.div_mod n 2 ltac:(lia)); pose proof (N.mod_lt n 2 ltac:(lia)); lia).
    replace (N.log2 n) with 1; [reflexivity|].
    symmetry; apply N.log2_unique; [lia|]. cbn; lia.
  - rewrite <- N.div2_div, N.div2_spec, N.log2_shiftr.
    pose proof (N.log2_pos n ltac:(lia)). lia.
Qed.

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "LOG2_log2" *)
Theorem LOG2_log2 : forall n, (n <> 0)%N -> log2 n = LOG2 n.
Proof.
  intros n Hn; unfold log2, LOG2.
  destruct (N.ltb_spec n 2); [|reflexivity].
  replace n with 1 by lia. reflexivity.
Qed.

(*! HOL "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "hsb_compute" *)
Theorem hsb_compute : forall (w : word7),
  HighestSetBit w =
  if bool_decide (w = n2w 0) then (-1)%Z else w2i (n2w (log2 (w2n w)) : word7).
Proof.
  intros w; unfold HighestSetBit.
  destruct (bool_decide (w = n2w 0)) eqn:Hw; [reflexivity|].
  unfold word_log2. f_equal. f_equal. symmetry. apply LOG2_log2.
  intros H0. assert (Hz : w = n2w 0) by (apply word_eq_w2n; rewrite H0; reflexivity).
  assert (bool_decide (w = n2w 0) = true) by (apply bool_decide_spec; exact Hz). congruence.
Qed.
