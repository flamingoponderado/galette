(** * Tests of the L3 RISC-V model and [NextRISCV] (Galette-only, no HOL original)

    Each example runs one instruction, given by its machine-code bytes, with
    [NextRISCV] (or the full model step [riscv.Next]) in the kernel
    ([vm_compute]) from a small RV64 state: virtual memory off
    ([mstatus.VM = 0]), [ArchBase = 2], PC 0, the bytes at address 0, and
    register [xr] holding [1000 * r + 8].  The expected register values and
    PCs were computed by hand from the RISC-V specification.  The byte
    sequences are those of [riscv_target/tests.v] (output of
    [cake --pancake --target=riscv]) and encodings by the model's [Encode]. *)

From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.examples.l3_machine_code.riscv.model Require Import riscv.
From Galette.HOL.examples.l3_machine_code.riscv.step Require Import riscv_step.
Open Scope N_scope.

Local Definition mcsr0 : MachineCSR :=
  MachineCSR_mcpuid_fupd (fun c => mcpuid_ArchBase_fupd (fun _ => n2w 2) c) (inhabitant _).

Local Definition mem_of (bytes : list N) (a : word64) : word8 :=
  n2w (nth (N.to_nat (w2n a)) bytes 0).

Local Definition st (bytes : list N) : riscv_state :=
  riscv_state_c_gpr_fupd
    (fun _ _ r => if bool_decide (r = n2w 0) then n2w 0 else n2w (1000 * w2n r + 8))
  (riscv_state_MEM8_fupd (fun _ => mem_of bytes)
  (riscv_state_exception_fupd (fun _ => NoException)
  (riscv_state_c_MCSR_fupd (fun _ _ => mcsr0) (inhabitant riscv_state)))).

Local Definition run1 (bytes : list N) := NextRISCV (st bytes).
Local Definition reg (o : option riscv_state) (r : N) : option N :=
  option_map (fun s => w2n (riscv_state_c_gpr s (riscv_state_procID s) (n2w r))) o.
Local Definition pc (o : option riscv_state) : option N :=
  option_map (fun s => w2n (riscv_state_c_PC s (riscv_state_procID s))) o.
Local Definition bytes_of (i : instruction) : list N :=
  map w2n (let w := Encode i in
           [(word_extract 7 0 w : word8); word_extract 15 8 w;
            word_extract 23 16 w; word_extract 31 24 w]).

(** addi x10, x12, 1 *)
Example addi : (reg (run1 [19;5;22;0]) 10, pc (run1 [19;5;22;0])) = (Some 12009, Some 4).
Proof. vm_compute. reflexivity. Qed.

(** add x13, x10, x13 *)
Example add : reg (run1 [179;6;213;0]) 13 = Some 23016.
Proof. vm_compute. reflexivity. Qed.

(** sub x1, x1, x11: 1008 - 11008 mod 2^64 *)
Example sub : reg (run1 [179;128;176;64]) 1 = Some (2 ^ 64 - 10000).
Proof. vm_compute. reflexivity. Qed.

(** srli x1, x1, 4 *)
Example srli : reg (run1 [147;208;64;0]) 1 = Some 63.
Proof. vm_compute. reflexivity. Qed.

(** srai x3, x31, 4 *)
Example srai : reg (run1 (bytes_of (Shift (SRAI (n2w 3, n2w 31, n2w 4))))) 3 = Some 1938.
Proof. vm_compute. reflexivity. Qed.

(** lui x5, 0x12345 *)
Example lui : reg (run1 (bytes_of (ArithI (LUI (n2w 5, n2w 0x12345))))) 5 = Some 0x12345000.
Proof. vm_compute. reflexivity. Qed.

(** mul x3, x4, x5; divu x3, x5, x4; remu x3, x5, x4 *)
Example mul : reg (run1 (bytes_of (MulDiv (MUL (n2w 3, n2w 4, n2w 5))))) 3 = Some (4008 * 5008).
Proof. vm_compute. reflexivity. Qed.
Example divu : reg (run1 (bytes_of (MulDiv (DIVU (n2w 3, n2w 5, n2w 4))))) 3 = Some 1.
Proof. vm_compute. reflexivity. Qed.
Example remu : reg (run1 (bytes_of (MulDiv (REMU (n2w 3, n2w 5, n2w 4))))) 3 = Some 1000.
Proof. vm_compute. reflexivity. Qed.

(** jal x0, 248; jalr x0, x1, 0 *)
Example jal : pc (run1 [111;0;128;15]) = Some 248.
Proof. vm_compute. reflexivity. Qed.
Example jalr : pc (run1 [103;128;0;0]) = Some 1008.
Proof. vm_compute. reflexivity. Qed.

(** branches: bge x10, x11 and bltu x12, x11 not taken; beq x0, x0, 16 taken *)
Example bge : pc (run1 [99;86;181;0]) = Some 4.
Proof. vm_compute. reflexivity. Qed.
Example bltu : pc (run1 [99;104;182;0]) = Some 4.
Proof. vm_compute. reflexivity. Qed.
Example beq : pc (run1 (bytes_of (Branch (BEQ (n2w 0, n2w 0, n2w 8))))) = Some 16.
Proof. vm_compute. reflexivity. Qed.

(** ld x22, -56(x25) reads zeros; sd x10, -48(x25) writes 10008 = 0x2718 at 24960 *)
Example ld : reg (run1 [3;187;140;252]) 22 = Some 0.
Proof. vm_compute. reflexivity. Qed.
Example sd :
  option_map (fun s => (w2n (riscv_state_MEM8 s (n2w 24960)), w2n (riscv_state_MEM8 s (n2w 24961))))
    (run1 [35;184;172;252]) = Some (0x18, 0x27).
Proof. vm_compute. reflexivity. Qed.

(** The full model step [Next] agrees on addi. *)
Example next_addi :
  (let s := riscv.Next (st [19;5;22;0]) in
   (w2n (riscv_state_c_gpr s (riscv_state_procID s) (n2w 10)),
    w2n (riscv_state_c_PC s (riscv_state_procID s)),
    bool_decide (riscv_state_exception s = NoException))) = (12009, 4, true).
Proof. vm_compute. reflexivity. Qed.
