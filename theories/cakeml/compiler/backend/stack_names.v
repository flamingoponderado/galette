(** * CakeML [stack_names]: renaming registers to fit the target

    Port of [cakeml/compiler/backend/stack_namesScript.sml].  HOL's overload
    [find_name] is [tlookup] ([misc.v]); it is an abbreviation here.  The
    [_pmatch] theorem is not ported.  HOL's [names_ok] is a boolean
    conjunction ([&&]). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import stackLang.
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/stack_namesScript.sml" "find_name" *)
Abbreviation find_name := tlookup.

Section StackNames.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/stack_namesScript.sml" "ri_find_name_def" *)
Definition ri_find_name (f : spt N) (ri : reg_imm a) : reg_imm a :=
  match ri with
  | Reg r => Reg (find_name f r)
  | Imm w => Imm w
  end.

(*! HOL "cakeml/compiler/backend/stack_namesScript.sml" "inst_find_name_def" *)
Definition inst_find_name (f : spt N) (i : inst a) : inst a :=
  match i with
  | asm.Skip => asm.Skip
  | asm.Const r w => asm.Const (find_name f r) w
  | Arith (Binop bop d r ri) =>
      Arith (Binop bop (find_name f d) (find_name f r) (ri_find_name f ri))
  | Arith (asm.Shift sop d r ri) =>
      Arith (asm.Shift sop (find_name f d) (find_name f r) (ri_find_name f ri))
  | Arith (Div r1 r2 r3) =>
      Arith (Div (find_name f r1) (find_name f r2) (find_name f r3))
  | Arith (AddCarry r1 r2 r3 r4) =>
      Arith (AddCarry (find_name f r1) (find_name f r2) (find_name f r3) (find_name f r4))
  | Arith (AddOverflow r1 r2 r3 r4) =>
      Arith (AddOverflow (find_name f r1) (find_name f r2) (find_name f r3) (find_name f r4))
  | Arith (SubOverflow r1 r2 r3 r4) =>
      Arith (SubOverflow (find_name f r1) (find_name f r2) (find_name f r3) (find_name f r4))
  | Arith (LongMul r1 r2 r3 r4) =>
      Arith (LongMul (find_name f r1) (find_name f r2) (find_name f r3) (find_name f r4))
  | Arith (LongDiv r1 r2 r3 r4 r5) =>
      Arith (LongDiv (find_name f r1) (find_name f r2) (find_name f r3) (find_name f r4)
                     (find_name f r5))
  | Mem mop r (Addr a0 w) => Mem mop (find_name f r) (Addr (find_name f a0) w)
  | FP (FPLess r f1 f2) => FP (FPLess (find_name f r) f1 f2)
  | FP (FPLessEqual r f1 f2) => FP (FPLessEqual (find_name f r) f1 f2)
  | FP (FPEqual r f1 f2) => FP (FPEqual (find_name f r) f1 f2)
  | FP (FPMovToReg r1 r2 d) => FP (FPMovToReg (find_name f r1) (find_name f r2) d)
  | FP (FPMovFromReg d r1 r2) => FP (FPMovFromReg d (find_name f r1) (find_name f r2))
  | i => i
  end.

(*! HOL "cakeml/compiler/backend/stack_namesScript.sml" "dest_find_name_def" *)
Definition dest_find_name (f : spt N) (d : N + N) : N + N :=
  match d with
  | inr r => inr (find_name f r)
  | x => x
  end.

(*! HOL "cakeml/compiler/backend/stack_namesScript.sml" "comp_def" *)
Fixpoint comp (f : spt N) (p : prog a) : prog a :=
  match p with
  | Halt r => Halt (find_name f r)
  | Raise r => Raise (find_name f r)
  | Break n => Break n
  | Continue n => Continue n
  | Return r => Return (find_name f r)
  | Inst i => Inst (inst_find_name f i)
  | LocValue i l1 l2 => LocValue (find_name f i) l1 l2
  | Seq p1 p2 => Seq (comp f p1) (comp f p2)
  | If c r ri p1 p2 =>
      If c (find_name f r) (ri_find_name f ri) (comp f p1) (comp f p2)
  | Loop p1 => Loop (comp f p1)
  | Call ret dest exc =>
      Call (match ret with
            | None => None
            | Some (p1, (lr, (l1, l2))) => Some (comp f p1, (find_name f lr, (l1, l2)))
            end)
           (dest_find_name f dest)
           (match exc with
            | None => None
            | Some (p2, (l1, l2)) => Some (comp f p2, (l1, l2))
            end)
  | Install r1 r2 r3 r4 r5 => Install (find_name f r1) (find_name f r2)
      (find_name f r3) (find_name f r4) (find_name f r5)
  | ShMemOp op r (Addr a0 w) => ShMemOp op (find_name f r) (Addr (find_name f a0) w)
  | CodeBufferWrite r1 r2 => CodeBufferWrite (find_name f r1) (find_name f r2)
  | FFI i r1 r2 r3 r4 r5 => FFI i (find_name f r1) (find_name f r2) (find_name f r3)
                                  (find_name f r4) (find_name f r5)
  | JumpLower r1 r2 dest => JumpLower (find_name f r1) (find_name f r2) dest
  | p => p
  end.

(*! HOL "cakeml/compiler/backend/stack_namesScript.sml" "prog_comp_def" *)
Definition prog_comp (f : spt N) (np : N * prog a) : N * prog a :=
  let '(n, p) := np in (n, comp f p).

(*! HOL "cakeml/compiler/backend/stack_namesScript.sml" "compile_def" *)
Definition compile (f : spt N) (prog0 : list (N * prog a)) : list (N * prog a) :=
  MAP (prog_comp f) prog0.

End StackNames.

(*! HOL "cakeml/compiler/backend/stack_namesScript.sml" "names_ok_def" *)
Definition names_ok (names : spt N) (reg_count : N) (avoid_regs : list N) : bool :=
  let xs := GENLIST (find_name names) (reg_count - LENGTH avoid_regs) in
  ALL_DISTINCT xs &&
  EVERY (fun x => (x <? reg_count) && negb (MEM x avoid_regs)) xs.
