(** * Tests of the RISC-V encoder [riscv_enc] (Galette-only, no HOL original)

    Each example evaluates [riscv_enc] in the kernel ([vm_compute]) on one
    ASM instruction and compares the resulting bytes with the bytes the
    original CakeML compiler emits for that instruction.  The expected bytes
    were taken from the output of
    [cake --pancake --target=riscv] (the CakeML binary built from the HOL
    sources) on a small Pancake program, by disassembling its code section
    and matching each instruction (sequence) to the ASM instruction that
    [riscv_ast] encodes it from.  They cover all branches of the 64-bit
    constant loader, rotation by an immediate, [Loc], near forward and
    backward [Jump]s, near [JumpCmp] with register and immediate operands
    (including [Test]), [JumpReg], loads and stores with negative offsets,
    and register/immediate arithmetic. *)

From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.HOL.examples.l3_machine_code.riscv.model Require Import riscv.
From Galette.cakeml.compiler.encoders.riscv Require Import riscv_target.
Open Scope N_scope.

Local Definition w (n : N) : word64 := n2w n.
Local Definition nw (n : N) : word64 := (- n2w n)%w.

Example cake_const_big1 : map w2n (riscv_enc (Inst (Const 13 (n2w 0x123456789ABCDEF0)))) = [183; 47; 67; 101; 147; 207; 15; 239; 183; 86; 52; 18; 147; 198; 118; 152; 147; 150; 6; 2; 179; 198; 246; 1].
Proof. vm_compute. reflexivity. Qed.

Example cake_ror7 : map w2n (riscv_enc (Inst (Arith (asm.Shift Ror 13 13 (Imm (w 7)))))) = [147; 223; 118; 0; 147; 150; 150; 3; 179; 230; 246; 1].
Proof. vm_compute. reflexivity. Qed.

Example cake_const_big2 : map w2n (riscv_enc (Inst (Const 5 (n2w 0x7FFFFFFF00000001)))) = [183; 15; 0; 0; 147; 143; 31; 0; 183; 2; 0; 128; 147; 194; 242; 255; 147; 146; 2; 2; 179; 226; 242; 1].
Proof. vm_compute. reflexivity. Qed.

Example cake_const_negupper : map w2n (riscv_enc (Inst (Const 5 (n2w 0xFFFFFFFF12345678)))) = [183; 95; 52; 18; 147; 143; 143; 103; 183; 2; 0; 0; 147; 194; 242; 255; 147; 146; 2; 2; 179; 226; 242; 1].
Proof. vm_compute. reflexivity. Qed.

Example cake_const_fff8 : map w2n (riscv_enc (Inst (Const 5 (n2w 0xFFFFFFFFFFFFF8)))) = [183; 15; 0; 0; 147; 207; 143; 255; 183; 2; 0; 255; 147; 130; 2; 0; 147; 146; 2; 2; 179; 194; 242; 1].
Proof. vm_compute. reflexivity. Qed.

Example cake_bge : map w2n (riscv_enc (JumpCmp NotLess 10 (Reg 11) (w 12))) = [99; 86; 181; 0].
Proof. vm_compute. reflexivity. Qed.

Example cake_loc : map w2n (riscv_enc (Loc 1 (w 12))) = [151; 0; 0; 0; 147; 128; 192; 0].
Proof. vm_compute. reflexivity. Qed.

Example cake_jump_fwd : map w2n (riscv_enc (Jump (w 248))) = [111; 0; 128; 15].
Proof. vm_compute. reflexivity. Qed.

Example cake_jump_back : map w2n (riscv_enc (Jump (nw 776))) = [111; 240; 159; 207].
Proof. vm_compute. reflexivity. Qed.

Example cake_test_reg : map w2n (riscv_enc (JumpCmp Test 10 (Reg 10) (w 16))) = [179; 127; 165; 0; 99; 134; 15; 0].
Proof. vm_compute. reflexivity. Qed.

Example cake_less_imm : map w2n (riscv_enc (JumpCmp Less 10 (Imm (w 0)) (w 12))) = [147; 111; 0; 0; 99; 68; 245; 1].
Proof. vm_compute. reflexivity. Qed.

Example cake_ne_imm : map w2n (riscv_enc (JumpCmp NotEqual 10 (Imm (w 1)) (w 12))) = [147; 111; 16; 0; 99; 20; 245; 1].
Proof. vm_compute. reflexivity. Qed.

Example cake_test_imm : map w2n (riscv_enc (JumpCmp Test 10 (Imm (w 1)) (w 12))) = [147; 127; 21; 0; 99; 132; 15; 0].
Proof. vm_compute. reflexivity. Qed.

Example cake_bgeu : map w2n (riscv_enc (JumpCmp NotLower 24 (Reg 25) (w 12))) = [99; 118; 156; 1].
Proof. vm_compute. reflexivity. Qed.

Example cake_jump_back2 : map w2n (riscv_enc (Jump (nw 1212))) = [111; 240; 95; 180].
Proof. vm_compute. reflexivity. Qed.

Example cake_jumpreg : map w2n (riscv_enc (JumpReg 1)) = [103; 128; 0; 0].
Proof. vm_compute. reflexivity. Qed.

Example cake_sd : map w2n (riscv_enc (Inst (Mem asm.Store 10 (Addr 25 (nw 48))))) = [35; 184; 172; 252].
Proof. vm_compute. reflexivity. Qed.

Example cake_ld : map w2n (riscv_enc (Inst (Mem asm.Load 22 (Addr 25 (nw 56))))) = [3; 187; 140; 252].
Proof. vm_compute. reflexivity. Qed.

Example cake_add : map w2n (riscv_enc (Inst (Arith (Binop Add 13 10 (Reg 13))))) = [179; 6; 213; 0].
Proof. vm_compute. reflexivity. Qed.

Example cake_addi : map w2n (riscv_enc (Inst (Arith (Binop Add 10 12 (Imm (w 1)))))) = [19; 5; 22; 0].
Proof. vm_compute. reflexivity. Qed.

Example cake_or : map w2n (riscv_enc (Inst (Arith (Binop Or 1 13 (Reg 13))))) = [179; 224; 214; 0].
Proof. vm_compute. reflexivity. Qed.

Example cake_srli : map w2n (riscv_enc (Inst (Arith (asm.Shift Lsr 1 1 (Imm (w 4)))))) = [147; 208; 64; 0].
Proof. vm_compute. reflexivity. Qed.

Example cake_sub : map w2n (riscv_enc (Inst (Arith (Binop Sub 1 1 (Reg 11))))) = [179; 128; 176; 64].
Proof. vm_compute. reflexivity. Qed.

Example cake_ori : map w2n (riscv_enc (Inst (Const 5 (w 2040)))) = [147; 98; 128; 127].
Proof. vm_compute. reflexivity. Qed.

Example cake_bltu : map w2n (riscv_enc (JumpCmp Lower 12 (Reg 11) (w 16))) = [99; 104; 182; 0].
Proof. vm_compute. reflexivity. Qed.
