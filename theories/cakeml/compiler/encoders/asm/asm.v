(** * CakeML [asm]: the target-independent assembly language

    Port of [cakeml/compiler/encoders/asm/asmScript.sml]: the syntax of ASM
    instructions, the target configuration record [asm_config], and the
    well-formedness predicates [asm_ok] etc. relative to a configuration.

    HOL's ['a word] type parameter is the width index [a : N] (an implicit
    argument of the constructors).  The HOL predicates here are boolean
    (the compiler evaluates [asm_ok], [offset_ok], [word_cmp]); HOL [==>] is
    [implb] and HOL [x IN {a; b; c}] on an explicit finite set is
    [MEM x [a; b; c]]. *)

From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words alignment.
From Galette.HOL.src.list.src Require Import list.
From Galette.cakeml.semantics Require Import ast.
Open Scope N_scope.

(** Equality on [N] (registers) is decided by [N.eq_dec]. *)

(** ** Syntax of ASM instructions *)

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "reg" *)
Abbreviation reg := N.

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "fp_reg" *)
Abbreviation fp_reg := N.

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "imm" *)
Abbreviation imm a := (word a).

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "reg_imm" *)
Inductive reg_imm (a : N) : Type :=
| Reg : reg -> reg_imm a
| Imm : imm a -> reg_imm a.
Arguments Reg {a} _.
Arguments Imm {a} _.

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "binop" *)
Inductive binop : Type := Add | Sub | And | Or | Xor.

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "cmp" *)
Inductive cmp : Type :=
  Equal | Lower | Less | Test | NotEqual | NotLower | NotLess | NotTest.

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "arith" *)
Inductive arith (a : N) : Type :=
| Binop : binop -> reg -> reg -> reg_imm a -> arith a
| Shift : shift -> reg -> reg -> reg_imm a -> arith a
| Div : reg -> reg -> reg -> arith a
| LongMul : reg -> reg -> reg -> reg -> arith a
| LongDiv : reg -> reg -> reg -> reg -> reg -> arith a
| AddCarry : reg -> reg -> reg -> reg -> arith a
| AddOverflow : reg -> reg -> reg -> reg -> arith a
| SubOverflow : reg -> reg -> reg -> reg -> arith a.
Arguments Binop {a} _ _ _ _.
Arguments Shift {a} _ _ _ _.
Arguments Div {a} _ _ _.
Arguments LongMul {a} _ _ _ _.
Arguments LongDiv {a} _ _ _ _ _.
Arguments AddCarry {a} _ _ _ _.
Arguments AddOverflow {a} _ _ _ _.
Arguments SubOverflow {a} _ _ _ _.

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "fp" *)
Inductive fp : Type :=
(* orderings *)
| FPLess : reg -> fp_reg -> fp_reg -> fp
| FPLessEqual : reg -> fp_reg -> fp_reg -> fp
| FPEqual : reg -> fp_reg -> fp_reg -> fp
(* unary ops *)
| FPAbs : fp_reg -> fp_reg -> fp
| FPNeg : fp_reg -> fp_reg -> fp
| FPSqrt : fp_reg -> fp_reg -> fp
(* binary ops *)
| FPAdd : fp_reg -> fp_reg -> fp_reg -> fp
| FPSub : fp_reg -> fp_reg -> fp_reg -> fp
| FPMul : fp_reg -> fp_reg -> fp_reg -> fp
| FPDiv : fp_reg -> fp_reg -> fp_reg -> fp
(* ternary ops *)
| FPFma : fp_reg -> fp_reg -> fp_reg -> fp
(* moves and converts *)
| FPMov : fp_reg -> fp_reg -> fp
| FPMovToReg : reg -> reg -> fp_reg -> fp
| FPMovFromReg : fp_reg -> reg -> reg -> fp
| FPToInt : fp_reg -> fp_reg -> fp
| FPFromInt : fp_reg -> fp_reg -> fp.

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "addr" *)
Inductive addr (a : N) : Type :=
| Addr : reg -> word a -> addr a.
Arguments Addr {a} _ _.

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "memop" *)
Inductive memop : Type :=
  Load | Load8 | Load16 | Load32 | Store | Store8 | Store16 | Store32.

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "inst" *)
Inductive inst (a : N) : Type :=
| Skip : inst a
| Const : reg -> word a -> inst a
| Arith : arith a -> inst a
| Mem : memop -> reg -> addr a -> inst a
| FP : fp -> inst a.
Arguments Skip {a}.
Arguments Const {a} _ _.
Arguments Arith {a} _.
Arguments Mem {a} _ _ _.
Arguments FP {a} _.

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "asm" *)
Inductive asm (a : N) : Type :=
| Inst : inst a -> asm a
| Jump : word a -> asm a
| JumpCmp : cmp -> reg -> reg_imm a -> word a -> asm a
| Call : word a -> asm a
| JumpReg : reg -> asm a
| Loc : reg -> word a -> asm a.
Arguments Inst {a} _.
Arguments Jump {a} _.
Arguments JumpCmp {a} _ _ _ _.
Arguments Call {a} _.
Arguments JumpReg {a} _.
Arguments Loc {a} _ _.

(** ** Target-specific configuration *)

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "architecture" *)
Inductive architecture : Type := ARMv7 | ARMv8 | MIPS | RISC_V | Ag32 | x86_64.

(** The fields of HOL's record [asm_config], in HOL's order; HOL's
    [c.reg_count] is [reg_count c]. *)
(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "asm_config" *)
Record asm_config (a : N) : Type := {
  ISA : architecture;
  encode : asm a -> list word8;
  big_endian : bool;
  code_alignment : N;
  link_reg : option N;
  avoid_regs : list N;
  reg_count : N;
  fp_reg_count : N;  (* set to 0 if float not available *)
  two_reg_arith : bool;
  valid_imm : binop + cmp -> word a -> bool;
  addr_offset : word a * word a;
  hw_offset : word a * word a;
  byte_offset : word a * word a;
  jump_offset : word a * word a;
  cjump_offset : word a * word a;
  loc_offset : word a * word a
}.
Arguments ISA {a} _.
Arguments encode {a} _.
Arguments big_endian {a} _.
Arguments code_alignment {a} _.
Arguments link_reg {a} _.
Arguments avoid_regs {a} _.
Arguments reg_count {a} _.
Arguments fp_reg_count {a} _.
Arguments two_reg_arith {a} _.
Arguments valid_imm {a} _.
Arguments addr_offset {a} _.
Arguments hw_offset {a} _.
Arguments byte_offset {a} _.
Arguments jump_offset {a} _.
Arguments cjump_offset {a} _.
Arguments loc_offset {a} _.

(** ** Decidable equality and inhabitants (Galette infrastructure) *)

#[global] Instance binop_eq_dec : EqDecision binop.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance cmp_eq_dec : EqDecision cmp.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance memop_eq_dec : EqDecision memop.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance architecture_eq_dec : EqDecision architecture.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance fp_eq_dec : EqDecision fp.
Proof. intros x y; unfold Decision; repeat decide equality. Defined.

Section EqDec.
Context {a : N}.
#[global] Instance reg_imm_eq_dec : EqDecision (reg_imm a).
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.
#[global] Instance arith_eq_dec : EqDecision (arith a).
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.
#[global] Instance addr_eq_dec : EqDecision (addr a).
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.
#[global] Instance inst_eq_dec : EqDecision (inst a).
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.
#[global] Instance asm_eq_dec : EqDecision (asm a).
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.
End EqDec.

#[global] Instance binop_inhabited : Inhabited binop := Add.
#[global] Instance cmp_inhabited : Inhabited cmp := Equal.
#[global] Instance memop_inhabited : Inhabited memop := Load.
#[global] Instance architecture_inhabited : Inhabited architecture := ARMv7.
#[global] Instance fp_inhabited : Inhabited fp := FPMov 0 0.
#[global] Instance reg_imm_inhabited {a} : Inhabited (reg_imm a) := Reg 0.
#[global] Instance arith_inhabited {a} : Inhabited (arith a) := Div 0 0 0.
#[global] Instance addr_inhabited {a} : Inhabited (addr a) := Addr 0 (n2w 0).
#[global] Instance inst_inhabited {a} : Inhabited (inst a) := Skip.
#[global] Instance asm_inhabited {a} : Inhabited (asm a) := Inst Skip.

(** ** Well-formedness relative to a configuration *)

Section Ok.
Context {a : N}.

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "reg_ok_def" *)
Definition reg_ok (r : N) (c : asm_config a) : bool :=
  (r <? reg_count c) && negb (MEM r (avoid_regs c)).

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "fp_reg_ok_def" *)
Definition fp_reg_ok (d : N) (c : asm_config a) : bool :=
  d <? fp_reg_count c.

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "reg_imm_ok_def" *)
Definition reg_imm_ok (b : binop + cmp) (ri : reg_imm a) (c : asm_config a) : bool :=
  match ri with
  | Reg r => reg_ok r c
  | Imm w =>
      (* Always permit Xor by -1 in order to provide 1's complement *)
      (bool_decide (b = inl Xor) && bool_decide (w = - n2w 1)%w) || valid_imm c b w
  end.

(** Requires register inequality for some architectures. *)
(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "arith_ok_def" *)
Definition arith_ok (x : arith a) (c : asm_config a) : bool :=
  match x with
  | Binop b r1 r2 ri =>
      (* note: register to register moves can be implmented with
               "Or" on "two_reg_arith" architectures. *)
      implb (two_reg_arith c)
        (bool_decide (r1 = r2) || bool_decide (b = Or) && bool_decide (ri = Reg r2)) &&
      reg_ok r1 c && reg_ok r2 c && reg_imm_ok (inl b) ri c
  | Shift l r1 r2 ri =>
      implb (two_reg_arith c) (bool_decide (r1 = r2)) &&
      reg_ok r1 c && reg_ok r2 c &&
      match ri with
      | Imm i => implb (bool_decide (i = n2w 0)) (bool_decide (l = Lsl)) &&
                 (w2n i <? dimindex a)
      | Reg r =>
          reg_ok r c &&
          implb (bool_decide (ISA c = x86_64)) (bool_decide (r = 1))
      end
  | Div r1 r2 r3 =>
      reg_ok r1 c && reg_ok r2 c && reg_ok r3 c &&
      MEM (ISA c) [ARMv8; MIPS; RISC_V]
  | LongMul r1 r2 r3 r4 =>
      reg_ok r1 c && reg_ok r2 c && reg_ok r3 c && reg_ok r4 c &&
      implb (bool_decide (ISA c = x86_64))
        (bool_decide (r1 = 2) && bool_decide (r2 = 0) && bool_decide (r3 = 0)) &&
      implb (bool_decide (ISA c = ARMv7)) (negb (bool_decide (r1 = r2))) &&
      implb (MEM (ISA c) [ARMv8; RISC_V; Ag32])
        (negb (bool_decide (r1 = r3)) && negb (bool_decide (r1 = r4)))
  | LongDiv r1 r2 r3 r4 r5 =>
      bool_decide (ISA c = x86_64) && bool_decide (r1 = 0) && bool_decide (r2 = 2) &&
      bool_decide (r3 = 2) && bool_decide (r4 = 0) &&
      reg_ok r5 c
  | AddCarry r1 r2 r3 r4 =>
      implb (two_reg_arith c) (bool_decide (r1 = r2)) &&
      reg_ok r1 c && reg_ok r2 c && reg_ok r3 c && reg_ok r4 c &&
      implb (bool_decide (ISA c = MIPS) || bool_decide (ISA c = RISC_V))
        (negb (bool_decide (r1 = r3)) && negb (bool_decide (r1 = r4)))
  | AddOverflow r1 r2 r3 r4 =>
      implb (two_reg_arith c) (bool_decide (r1 = r2)) &&
      reg_ok r1 c && reg_ok r2 c && reg_ok r3 c && reg_ok r4 c &&
      implb (bool_decide (ISA c = MIPS) || bool_decide (ISA c = RISC_V))
        (negb (bool_decide (r1 = r3)))
  | SubOverflow r1 r2 r3 r4 =>
      implb (two_reg_arith c) (bool_decide (r1 = r2)) &&
      reg_ok r1 c && reg_ok r2 c && reg_ok r3 c && reg_ok r4 c &&
      implb (bool_decide (ISA c = MIPS) || bool_decide (ISA c = RISC_V))
        (negb (bool_decide (r1 = r3)))
  end.

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "fp_ok_def" *)
Definition fp_ok (x : fp) (c : asm_config a) : bool :=
  match x with
  | FPLess r d1 d2 =>
      reg_ok r c && fp_reg_ok d1 c && fp_reg_ok d2 c
  | FPLessEqual r d1 d2 =>
      reg_ok r c && fp_reg_ok d1 c && fp_reg_ok d2 c
  | FPEqual r d1 d2 =>
      reg_ok r c && fp_reg_ok d1 c && fp_reg_ok d2 c
  | FPAbs d1 d2 =>
      implb (two_reg_arith c) (negb (bool_decide (d1 = d2))) &&
      fp_reg_ok d1 c && fp_reg_ok d2 c
  | FPNeg d1 d2 =>
      implb (two_reg_arith c) (negb (bool_decide (d1 = d2))) &&
      fp_reg_ok d1 c && fp_reg_ok d2 c
  | FPSqrt d1 d2 => fp_reg_ok d1 c && fp_reg_ok d2 c
  | FPAdd d1 d2 d3 =>
      implb (two_reg_arith c) (bool_decide (d1 = d2)) &&
      fp_reg_ok d1 c && fp_reg_ok d2 c && fp_reg_ok d3 c
  | FPSub d1 d2 d3 =>
      implb (two_reg_arith c) (bool_decide (d1 = d2)) &&
      fp_reg_ok d1 c && fp_reg_ok d2 c && fp_reg_ok d3 c
  | FPMul d1 d2 d3 =>
      implb (two_reg_arith c) (bool_decide (d1 = d2)) &&
      fp_reg_ok d1 c && fp_reg_ok d2 c && fp_reg_ok d3 c
  | FPDiv d1 d2 d3 =>
      implb (two_reg_arith c) (bool_decide (d1 = d2)) &&
      fp_reg_ok d1 c && fp_reg_ok d2 c && fp_reg_ok d3 c
  | FPFma d1 d2 d3 =>
      bool_decide (ISA c = ARMv7) &&
      (2 <? fp_reg_count c) &&
      fp_reg_ok d1 c && fp_reg_ok d2 c && fp_reg_ok d3 c
  | FPMov d1 d2 => fp_reg_ok d1 c && fp_reg_ok d2 c
  | FPMovToReg r1 r2 d =>
      reg_ok r1 c &&
      implb (bool_decide (dimindex a = 32)) (negb (bool_decide (r1 = r2)) && reg_ok r2 c) &&
      fp_reg_ok d c
  | FPMovFromReg d r1 r2 =>
      reg_ok r1 c &&
      implb (bool_decide (dimindex a = 32)) (negb (bool_decide (r1 = r2)) && reg_ok r2 c) &&
      fp_reg_ok d c
  | FPToInt r d => fp_reg_ok r c && fp_reg_ok d c
  | FPFromInt d r => fp_reg_ok r c && fp_reg_ok d c
  end.

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "cmp_ok_def" *)
Definition cmp_ok (cmp : cmp) (r : reg) (ri : reg_imm a) (c : asm_config a) : bool :=
  reg_ok r c && reg_imm_ok (inr cmp) ri c.

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "offset_ok_def" *)
Definition offset_ok (p : N) (offset : word a * word a) (w : word a) : bool :=
  let (min, max) := offset in (min <= w)%w && (w <= max)%w && aligned p w.

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "addr_offset_ok" *)
Definition addr_offset_ok (c : asm_config a) : word a -> bool :=
  offset_ok 0 (addr_offset c).

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "hw_offset_ok" *)
Definition hw_offset_ok (c : asm_config a) : word a -> bool :=
  offset_ok 0 (hw_offset c).

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "byte_offset_ok" *)
Definition byte_offset_ok (c : asm_config a) : word a -> bool :=
  offset_ok 0 (byte_offset c).

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "jump_offset_ok" *)
Definition jump_offset_ok (c : asm_config a) : word a -> bool :=
  offset_ok (code_alignment c) (jump_offset c).

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "cjump_offset_ok" *)
Definition cjump_offset_ok (c : asm_config a) : word a -> bool :=
  offset_ok (code_alignment c) (cjump_offset c).

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "loc_offset_ok" *)
Definition loc_offset_ok (c : asm_config a) : word a -> bool :=
  offset_ok (code_alignment c) (loc_offset c).

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "inst_ok_def" *)
Definition inst_ok (i : inst a) (c : asm_config a) : bool :=
  match i with
  | Skip => true
  | Const r w => reg_ok r c
  | Arith x => arith_ok x c
  | FP x => fp_ok x c
  | Mem m r1 (Addr r2 w) =>
      reg_ok r1 c && reg_ok r2 c &&
      (if MEM m [Load; Store; Load32; Store32] then
         addr_offset_ok c w
       else if MEM m [Load16; Store16] then
         hw_offset_ok c w && negb (bool_decide (ISA c = Ag32))
       else
         byte_offset_ok c w)
  end.

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "asm_ok_def" *)
Definition asm_ok (i : asm a) (c : asm_config a) : bool :=
  match i with
  | Inst i => inst_ok i c
  | Jump w => jump_offset_ok c w
  | JumpCmp cmp r ri w =>
      cjump_offset_ok c w && cmp_ok cmp r ri c
  | Call w =>
      match link_reg c with Some r => reg_ok r c | None => false end &&
      jump_offset_ok c w
  | JumpReg r => reg_ok r c
  | Loc r w => reg_ok r c && loc_offset_ok c w
  end.

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "word_cmp_def" *)
Definition word_cmp (c : cmp) (w1 w2 : word a) : bool :=
  match c with
  | Equal => bool_decide (w1 = w2)
  | Less => (w1 < w2)%w
  | Lower => (w1 <+ w2)%w
  | Test => bool_decide ((w1 && w2)%w = n2w 0)
  | NotEqual => negb (bool_decide (w1 = w2))
  | NotLess => negb (w1 < w2)%w
  | NotLower => negb (w1 <+ w2)%w
  | NotTest => negb (bool_decide ((w1 && w2)%w = n2w 0))
  end.

End Ok.

(*! HOL "cakeml/compiler/encoders/asm/asmScript.sml" "is_load_def" *)
Definition is_load (m : memop) : bool :=
  match m with
  | Load => true
  | Load8 => true
  | Load16 => true
  | Load32 => true
  | _ => false
  end.
