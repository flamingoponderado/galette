(** * CakeML [riscv_target]: the RISC-V (RV64I) target configuration

    Port of [cakeml/compiler/encoders/riscv/riscv_targetScript.sml]: the
    encoder of ASM instructions into RISC-V machine code (through the L3
    model's instruction AST and its [Encode]) and the target configuration
    [riscv_config].

    HOL elaborates this script under [wordsLib.guess_lengths ()], which
    gives every [(h >< l)] extract with an otherwise unconstrained result the
    width [h + 1 - l]; where Rocq cannot infer such a width from the
    context it is written as an ascription.  [word_scope] is open, so the
    boolean connectives of HOL conditions are written in [%bool] and [num]
    arithmetic in [%N].  The ML values
    [min12], [max12], [min21], [max21], [min32] are antiquoted into HOL's
    definitions as evaluated literals; here they are constants with the
    defining expression of the ML [val].

    The target record [riscv_target] (with [riscv_next], [riscv_ok],
    [riscv_proj]) is at the end.  Not ported: the generated rewrites
    [riscv_config], [riscv_asm_ok] (theorems computed by [asmLib]). *)

From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.HOL.examples.l3_machine_code.riscv.model Require Import riscv.
From Galette.HOL.src.combin Require combin.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.n_bit Require Import alignment.
From Galette.HOL.examples.l3_machine_code.riscv.step Require Import riscv_step.
From Galette.HOL.examples.machine_code.hoare_triple Require set_sep.
From Galette.cakeml.compiler.encoders.asm Require asmProps.
Open Scope N_scope.
Local Open Scope word_scope.

(** ASM's [Load], [Store] and [Shift] are shadowed by the RISC-V instruction
    constructors of the same names, and ASM's constructor [Skip] by the
    model's function [Skip]; ASM's are written [asm.Load], [asm.Skip] etc. *)

(** ** Encoding RISC-V instructions to bytes *)

(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "riscv_encode_fail_def" *)
Definition riscv_encode_fail : list instruction :=
  [ArithI (ADDI (n2w 0, n2w 0, n2w 0))].

(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "riscv_encode_def" *)
Definition riscv_encode (i : instruction) : list word8 :=
  let w := Encode i in
  [(7 >< 0) w; (15 >< 8) w; (23 >< 16) w; (31 >< 24) w].

(** ** Instruction selection helpers

    HOL leaves the cases missing from [riscv_bop_i] ([Sub]), [riscv_sh] and
    [riscv_shv] ([Ror]) unspecified; they are [ARB] here.  [riscv_ast]
    never uses them. *)

(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "riscv_bop_r_def" *)
Definition riscv_bop_r (b : binop) : word5 * word5 * word5 -> ArithR_ty :=
  match b with
  | Add => ADD
  | Sub => SUB
  | And => AND
  | Or => OR
  | Xor => XOR
  end.

(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "riscv_bop_i_def" *)
Definition riscv_bop_i (b : binop) : word5 * word5 * word12 -> ArithI_ty :=
  match b with
  | Add => ADDI
  | And => ANDI
  | Or => ORI
  | Xor => XORI
  | Sub => ARB
  end.

(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "riscv_sh_def" *)
Definition riscv_sh (sh : shift) : word5 * word5 * word6 -> Shift_ty :=
  match sh with
  | Lsl => SLLI
  | Lsr => SRLI
  | Asr => SRAI
  | Ror => ARB
  end.

(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "riscv_shv_def" *)
Definition riscv_shv (sh : shift) : word5 * word5 * word5 -> Shift_ty :=
  match sh with
  | Lsl => SLL
  | Lsr => SRL
  | Asr => SRA
  | Ror => ARB
  end.

(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "riscv_memop_def" *)
Definition riscv_memop (m : memop) :
    (word5 * word5 * word12 -> Load_ty) + (word5 * word5 * word12 -> Store_ty) :=
  match m with
  | asm.Load => inl LD
  | Load32 => inl LWU
  | Load16 => inl LHU
  | Load8 => inl LBU
  | asm.Store => inr SD
  | Store32 => inr SW
  | Store16 => inr SH
  | Store8 => inr SB
  end.

(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "riscv_const32_def" *)
Definition riscv_const32 (r : word5) (i : word32) : list instruction :=
  if i ' 11 then
    [ArithI (LUI (r, ¬((31 >< 12) i)));
     ArithI (XORI (r, r, (11 >< 0) i))]
  else
    [ArithI (LUI (r, (31 >< 12) i));
     ArithI (ADDI (r, r, (11 >< 0) i))].

(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "min12" *)
Definition min12 : word64 := sw2sw (INT_MINw : word12).

(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "max12" *)
Definition max12 : word64 := sw2sw (INT_MAXw : word12).

(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "min21" *)
Definition min21 : word64 := sw2sw (INT_MINw : word21).

(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "max21" *)
Definition max21 : word64 := sw2sw (INT_MAXw : word21).

(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "min32" *)
Definition min32 : word64 := sw2sw (INT_MINw : word32).

(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "temp_reg" *)
Definition temp_reg : word5 := n2w 31.

(** ** Encoding ASM instructions *)

(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "riscv_ast_def" *)
Definition riscv_ast (x : asm 64) : list instruction :=
  match x with
  | Inst asm.Skip => [ArithI (ADDI (n2w 0, n2w 0, n2w 0))]
  | Inst (Const r i) =>
      let imm12 : word12 := (11 >< 0) i in
      if bool_decide (i = sw2sw imm12) then
        [ArithI (ORI (n2w r, n2w 0, imm12))]
      else if (bool_decide ((63 >< 32) i = (n2w 0 : word32)) && negb (i ' 31) ||
               bool_decide ((63 >< 32) i = (- n2w 1 : word32)) && i ' 31)%bool then
        riscv_const32 (n2w r) ((31 >< 0) i)
      else if i ' 31 then
        riscv_const32 temp_reg ((31 >< 0) i) ++
        riscv_const32 (n2w r) (¬((63 >< 32) i)) ++
        [Shift (SLLI (n2w r, n2w r, n2w 32));
         ArithR (XOR (n2w r, n2w r, temp_reg))]
      else
        riscv_const32 temp_reg ((31 >< 0) i) ++
        riscv_const32 (n2w r) ((63 >< 32) i) ++
        [Shift (SLLI (n2w r, n2w r, n2w 32));
         ArithR (OR (n2w r, n2w r, temp_reg))]
  | Inst (Arith (Binop bop r1 r2 (Reg r3))) =>
      [ArithR (riscv_bop_r bop (n2w r1, n2w r2, n2w r3))]
  | Inst (Arith (Binop Sub r1 r2 (Imm i))) =>
      [ArithI (ADDI (n2w r1, n2w r2, -(w2w i)))]
  | Inst (Arith (Binop bop r1 r2 (Imm i))) =>
      [ArithI (riscv_bop_i bop (n2w r1, n2w r2, w2w i))]
  | Inst (Arith (asm.Shift sh r1 r2 (Imm i))) =>
      let n := w2n i in
      if bool_decide (sh = Ror) then
        [Shift (SRLI (temp_reg, n2w r2, n2w n));
         Shift (SLLI (n2w r1, n2w r2, n2w (64 - n)%N));
         ArithR (OR (n2w r1, n2w r1, temp_reg))]
      else
        [Shift (riscv_sh sh (n2w r1, n2w r2, n2w n))]
  | Inst (Arith (asm.Shift sh r1 r2 (Reg r))) =>
      if bool_decide (sh = Ror) then
        [ArithI (ORI (temp_reg, n2w 0, n2w 64));
         ArithR (SUB (temp_reg, temp_reg, n2w r));
         Shift (SLL (temp_reg, n2w r2, temp_reg));
         Shift (SRL (n2w r1, n2w r2, n2w r));
         ArithR (OR (n2w r1, n2w r1, temp_reg))]
      else
        [Shift (riscv_shv sh (n2w r1, n2w r2, n2w r))]
  | Inst (Arith (Div r1 r2 r3)) =>
      [MulDiv (riscv.DIV (n2w r1, n2w r2, n2w r3))]
  | Inst (Arith (LongMul r1 r2 r3 r4)) =>
      [MulDiv (MULHU (n2w r1, n2w r3, n2w r4));
       MulDiv (MUL (n2w r2, n2w r3, n2w r4))]
  | Inst (Arith (LongDiv _ _ _ _ _)) => riscv_encode_fail
  | Inst (Arith (AddCarry r1 r2 r3 r4)) =>
      [ArithR (SLTU (temp_reg, n2w 0, n2w r4));
       ArithR (ADD (n2w r1, n2w r2, n2w r3));
       ArithR (SLTU (n2w r4, n2w r1, n2w r3));
       ArithR (ADD (n2w r1, n2w r1, temp_reg));
       ArithR (SLTU (temp_reg, n2w r1, temp_reg));
       ArithR (OR (n2w r4, n2w r4, temp_reg))]
  | Inst (Arith (AddOverflow r1 r2 r3 r4)) =>
      [ArithR (XOR (temp_reg, n2w r2, n2w r3));
       ArithI (XORI (temp_reg, temp_reg, - n2w 1));
       ArithR (ADD (n2w r1, n2w r2, n2w r3));
       ArithR (XOR (n2w r4, n2w r3, n2w r1));
       ArithR (AND (n2w r4, temp_reg, n2w r4));
       Shift (SRLI (n2w r4, n2w r4, n2w 63))]
  | Inst (Arith (SubOverflow r1 r2 r3 r4)) =>
      [ArithR (XOR (temp_reg, n2w r2, n2w r3));
       ArithR (SUB (n2w r1, n2w r2, n2w r3));
       ArithR (XOR (n2w r4, n2w r3, n2w r1));
       ArithI (XORI (n2w r4, n2w r4, - n2w 1));
       ArithR (AND (n2w r4, temp_reg, n2w r4));
       Shift (SRLI (n2w r4, n2w r4, n2w 63))]
  | Inst (Mem mop r1 (Addr r2 a)) =>
      match riscv_memop mop with
      | inl f => [Load (f (n2w r1, n2w r2, w2w a))]
      | inr f => [Store (f (n2w r2, n2w r1, w2w a))]
      end
  | Inst (FP _) => riscv_encode_fail
  | Jump a =>
      if ((min21 <= a) && (a <= max21))%bool then
        [Branch (JAL (n2w 0, w2w (a >>> 1)))]
      else
        let imm12 : word12 := (11 >< 0) a in
        [ArithI (AUIPC (temp_reg, (31 >< 12) (a - sw2sw imm12)));
         Branch (JALR (n2w 0, temp_reg, (11 >< 0) a))]
  | JumpCmp c r1 (Reg r2) a =>
      if ((- n2w 4092 <= a) && (a <= n2w 4095))%bool then
        let off12 : word12 := w2w (a >>> 1) in
        match c with
        | Equal => [Branch (BEQ (n2w r1, n2w r2, off12))]
        | Less => [Branch (BLT (n2w r1, n2w r2, off12))]
        | Lower => [Branch (BLTU (n2w r1, n2w r2, off12))]
        | Test => [ArithR (AND (temp_reg, n2w r1, n2w r2));
                   Branch (BEQ (temp_reg, n2w 0, off12 - n2w 2))]
        | NotEqual => [Branch (BNE (n2w r1, n2w r2, off12))]
        | NotLess => [Branch (BGE (n2w r1, n2w r2, off12))]
        | NotLower => [Branch (BGEU (n2w r1, n2w r2, off12))]
        | NotTest => [ArithR (AND (temp_reg, n2w r1, n2w r2));
                      Branch (BNE (temp_reg, n2w 0, off12 - n2w 2))]
        end
      else
        let off20 : word20 := w2w (a >>> 1) - n2w 2 in
        match c with
        | Equal => [Branch (BNE (n2w r1, n2w r2, n2w 4));
                    Branch (JAL (n2w 0, off20))]
        | Less => [Branch (BGE (n2w r1, n2w r2, n2w 4));
                   Branch (JAL (n2w 0, off20))]
        | Lower => [Branch (BGEU (n2w r1, n2w r2, n2w 4));
                    Branch (JAL (n2w 0, off20))]
        | Test => [ArithR (AND (temp_reg, n2w r1, n2w r2));
                   Branch (BNE (temp_reg, n2w 0, n2w 4));
                   Branch (JAL (n2w 0, off20 - n2w 2))]
        | NotEqual => [Branch (BEQ (n2w r1, n2w r2, n2w 4));
                       Branch (JAL (n2w 0, off20))]
        | NotLess => [Branch (BLT (n2w r1, n2w r2, n2w 4));
                      Branch (JAL (n2w 0, off20))]
        | NotLower => [Branch (BLTU (n2w r1, n2w r2, n2w 4));
                       Branch (JAL (n2w 0, off20))]
        | NotTest => [ArithR (AND (temp_reg, n2w r1, n2w r2));
                      Branch (BEQ (temp_reg, n2w 0, n2w 4));
                      Branch (JAL (n2w 0, off20 - n2w 2))]
        end
  | JumpCmp c r (Imm i) a =>
      if ((- n2w 4092 <= a) && (a <= n2w 4095))%bool then
        let off12 : word12 := w2w (a >>> 1) - n2w 2 in
        match c with
        | Equal => [ArithI (ORI (temp_reg, n2w 0, w2w i));
                    Branch (BEQ (n2w r, temp_reg, off12))]
        | Less => [ArithI (ORI (temp_reg, n2w 0, w2w i));
                   Branch (BLT (n2w r, temp_reg, off12))]
        | Lower => [ArithI (ORI (temp_reg, n2w 0, w2w i));
                    Branch (BLTU (n2w r, temp_reg, off12))]
        | Test => [ArithI (ANDI (temp_reg, n2w r, w2w i));
                   Branch (BEQ (temp_reg, n2w 0, off12))]
        | NotEqual => [ArithI (ORI (temp_reg, n2w 0, w2w i));
                       Branch (BNE (n2w r, temp_reg, off12))]
        | NotLess => [ArithI (ORI (temp_reg, n2w 0, w2w i));
                      Branch (BGE (n2w r, temp_reg, off12))]
        | NotLower => [ArithI (ORI (temp_reg, n2w 0, w2w i));
                       Branch (BGEU (n2w r, temp_reg, off12))]
        | NotTest => [ArithI (ANDI (temp_reg, n2w r, w2w i));
                      Branch (BNE (temp_reg, n2w 0, off12))]
        end
      else
        let off20 : word20 := w2w (a >>> 1) - n2w 4 in
        match c with
        | Equal => [ArithI (ORI (temp_reg, n2w 0, w2w i));
                    Branch (BNE (n2w r, temp_reg, n2w 4));
                    Branch (JAL (n2w 0, off20))]
        | Less => [ArithI (ORI (temp_reg, n2w 0, w2w i));
                   Branch (BGE (n2w r, temp_reg, n2w 4));
                   Branch (JAL (n2w 0, off20))]
        | Lower => [ArithI (ORI (temp_reg, n2w 0, w2w i));
                    Branch (BGEU (n2w r, temp_reg, n2w 4));
                    Branch (JAL (n2w 0, off20))]
        | Test => [ArithI (ANDI (temp_reg, n2w r, w2w i));
                   Branch (BNE (temp_reg, n2w 0, n2w 4));
                   Branch (JAL (n2w 0, off20))]
        | NotEqual => [ArithI (ORI (temp_reg, n2w 0, w2w i));
                       Branch (BEQ (n2w r, temp_reg, n2w 4));
                       Branch (JAL (n2w 0, off20))]
        | NotLess => [ArithI (ORI (temp_reg, n2w 0, w2w i));
                      Branch (BLT (n2w r, temp_reg, n2w 4));
                      Branch (JAL (n2w 0, off20))]
        | NotLower => [ArithI (ORI (temp_reg, n2w 0, w2w i));
                       Branch (BLTU (n2w r, temp_reg, n2w 4));
                       Branch (JAL (n2w 0, off20))]
        | NotTest => [ArithI (ANDI (temp_reg, n2w r, w2w i));
                      Branch (BEQ (temp_reg, n2w 0, n2w 4));
                      Branch (JAL (n2w 0, off20))]
        end
  | Call a =>
      if ((min21 <= a) && (a <= max21))%bool then
        [Branch (JAL (n2w 1, w2w (a >>> 1)))]
      else
        let imm12 : word12 := (11 >< 0) a in
        [ArithI (AUIPC (n2w 1, (31 >< 12) (a - sw2sw imm12)));
         Branch (JALR (n2w 1, n2w 1, (11 >< 0) a))]
  | JumpReg r => [Branch (JALR (n2w 0, n2w r, n2w 0))]
  | Loc r i =>
      let imm12 := (11 >< 0) i in
      [ArithI (AUIPC (n2w r, (31 >< 12) (i - sw2sw imm12)));
       ArithI (ADDI (n2w r, n2w r, imm12))]
  end.

(** HOL marks [riscv_enc_def] [nocompute] (HOL evaluates it through
    [riscv_targetLib]); here it is directly executable. *)
(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "riscv_enc_def" *)
Definition riscv_enc : asm 64 -> list word8 :=
  combin.C LIST_BIND riscv_encode ∘ riscv_ast.

(** ** Configuration for RISC-V *)

(** Calling conventions (https://riscv.org/specifications/, p109):
    0 - hardwired zero, 2 - stack pointer, 3 - global pointer,
    4 - thread pointer, 31 - used by the encoder above. *)
(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "riscv_config_def" *)
Definition riscv_config : asm_config 64 := {|
  ISA := RISC_V;
  encode := riscv_enc;
  big_endian := false;
  code_alignment := 2;
  link_reg := Some 1;
  avoid_regs := [0; 2; 3; 4; 31];
  reg_count := 32;
  fp_reg_count := 0;
  two_reg_arith := false;
  valid_imm := fun b i =>
    ((if bool_decide (b = inl Sub) then min12 < i else min12 <= i) &&
     (i <= max12))%bool;
  addr_offset := (min12, max12);
  hw_offset := (min12, max12);
  byte_offset := (min12, max12);
  jump_offset := (min32, n2w 0x7FFFF7FF);
  cjump_offset := (min21 + n2w 8, max21 + n2w 4);
  loc_offset := (min32, n2w 0x7FFFF7FF)
|}.

(** ** The RISC-V target *)

(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "riscv_next_def" *)
Definition riscv_next (s : riscv_state) : riscv_state := THE (NextRISCV s).

(** Valid RISC-V states: virtual memory is turned off and a 64-bit
    architecture (RV64I). *)
(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "riscv_ok_def" *)
Definition riscv_ok (ms : riscv_state) : bool :=
  (bool_decide (mstatus_VM (MachineCSR_mstatus (riscv_state_c_MCSR ms (riscv_state_procID ms)))
                = n2w 0) &&
   bool_decide (mcpuid_ArchBase (MachineCSR_mcpuid (riscv_state_c_MCSR ms (riscv_state_procID ms)))
                = n2w 2) &&
   bool_decide (riscv_state_c_NextFetch ms (riscv_state_procID ms) = None) &&
   bool_decide (riscv_state_exception ms = NoException) &&
   aligned 2 (riscv_state_c_PC ms (riscv_state_procID ms)))%bool.

(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "riscv_proj_def" *)
Definition riscv_proj (d : word64 -> Prop) (s : riscv_state) :
    word5 * word2 * option TransferControl * exception * (word5 -> word64) *
    (word64 * word8 -> Prop) * word64 :=
  (mstatus_VM (MachineCSR_mstatus (riscv_state_c_MCSR s (riscv_state_procID s))),
   mcpuid_ArchBase (MachineCSR_mcpuid (riscv_state_c_MCSR s (riscv_state_procID s))),
   riscv_state_c_NextFetch s (riscv_state_procID s),
   riscv_state_exception s,
   riscv_state_c_gpr s (riscv_state_procID s),
   set_sep.fun2set (riscv_state_MEM8 s, d),
   riscv_state_c_PC s (riscv_state_procID s)).

(** HOL's record literal leaves the field [get_fp_reg] unset (its value is
    that of [ARB]); here it is [ARB]. *)
(*! HOL "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "riscv_target_def" *)
Definition riscv_target :=
  asmProps.mk_target
    riscv_config
    riscv_next
    (fun s => riscv_state_c_PC s (riscv_state_procID s))
    (fun s => riscv_state_c_gpr s (riscv_state_procID s) ∘ n2w)
    ARB
    riscv_state_MEM8
    riscv_ok
    riscv_proj.
