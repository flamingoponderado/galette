(** * CakeML [wordConvs]: syntactic conventions on wordLang programs

    The predicates are [bool]-valued like [wordLang]'s [every_var] (they are
    computable); in theorem statements they are read as propositions.  HOL's
    set-membership tests on literal sets ([m IN {Load; Store; ...}]) are
    [MEM] on the corresponding lists. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From Galette.cakeml.compiler.backend Require Import wordLang.
Open Scope N_scope.

Section Defs.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_def" *)
Definition labels_rel (old_labs new_labs : list (N * N)) : Prop :=
  (is_true (ALL_DISTINCT old_labs) -> is_true (ALL_DISTINCT new_labs)) /\
  set new_labs SUBSET set old_labs.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "flat_exp_conventions_def" *)
Fixpoint flat_exp_conventions (p : prog a) : bool :=
  match p with
  | Assign v exp => false
  | Store exp num => false
  | Set_ store_name (Var r) => true
  | Set_ store_name _ => false
  | ShareInst op v (Var r) => true
  | ShareInst op v (Op asm.Add [Var r; Const c]) => true
  | ShareInst op v _ => false
  | Seq p1 p2 => flat_exp_conventions p1 && flat_exp_conventions p2
  | Loop names c exit_names => flat_exp_conventions c
  | If cmp r1 ri e2 e3 => flat_exp_conventions e2 && flat_exp_conventions e3
  | MustTerminate p => flat_exp_conventions p
  | Call ret dest args h =>
      match ret with
      | NONE => true
      | SOME (v, (cutset, (ret_handler, (l1, l2)))) => flat_exp_conventions ret_handler
      end &&
      match h with
      | NONE => true
      | SOME (v, (prog0, (l1, l2))) => flat_exp_conventions prog0
      end
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "inst_ok_less_def" *)
Definition inst_ok_less (c : asm_config a) (i : inst a) : bool :=
  match i with
  | Arith (Binop b r1 r2 (Imm w)) => valid_imm c (inl b) w
  | Arith (asm.Shift l r1 r2 (Imm i)) =>
      implb (bool_decide (i = n2w 0)) (bool_decide (l = Lsl)) && (w2n i <? dimindex a)
  | Arith (Div r1 r2 r3) => MEM (ISA c) [ARMv8; MIPS; RISC_V]
  | Arith (LongMul r1 r2 r3 r4) =>
      implb (bool_decide (ISA c = ARMv7)) (negb (r1 =? r2)) &&
      implb (bool_decide (ISA c = ARMv8) || bool_decide (ISA c = RISC_V) || bool_decide (ISA c = Ag32))
            (negb (r1 =? r3) && negb (r1 =? r4))
  | Arith (LongDiv r1 r2 r3 r4 r5) => bool_decide (ISA c = x86_64)
  | Arith (AddCarry r1 r2 r3 r4) =>
      implb (bool_decide (ISA c = MIPS) || bool_decide (ISA c = RISC_V))
            (negb (r1 =? r3) && negb (r1 =? r4))
  | Arith (AddOverflow r1 r2 r3 r4) =>
      implb (bool_decide (ISA c = MIPS) || bool_decide (ISA c = RISC_V)) (negb (r1 =? r3))
  | Arith (SubOverflow r1 r2 r3 r4) =>
      implb (bool_decide (ISA c = MIPS) || bool_decide (ISA c = RISC_V)) (negb (r1 =? r3))
  | Mem m r (Addr r' w) =>
      if MEM m [asm.Load; asm.Store; Load16; Store16; Load32; Store32]
      then addr_offset_ok c w
      else if MEM m [Load16; Store16]
      then hw_offset_ok c w
      else byte_offset_ok c w
  | FP (FPLess r d1 d2) => fp_reg_ok d1 c && fp_reg_ok d2 c
  | FP (FPLessEqual r d1 d2) => fp_reg_ok d1 c && fp_reg_ok d2 c
  | FP (FPEqual r d1 d2) => fp_reg_ok d1 c && fp_reg_ok d2 c
  | FP (FPAbs d1 d2) => implb (two_reg_arith c) (negb (d1 =? d2)) && fp_reg_ok d1 c && fp_reg_ok d2 c
  | FP (FPNeg d1 d2) => implb (two_reg_arith c) (negb (d1 =? d2)) && fp_reg_ok d1 c && fp_reg_ok d2 c
  | FP (FPSqrt d1 d2) => fp_reg_ok d1 c && fp_reg_ok d2 c
  | FP (FPAdd d1 d2 d3) =>
      implb (two_reg_arith c) (d1 =? d2) && fp_reg_ok d1 c && fp_reg_ok d2 c && fp_reg_ok d3 c
  | FP (FPSub d1 d2 d3) =>
      implb (two_reg_arith c) (d1 =? d2) && fp_reg_ok d1 c && fp_reg_ok d2 c && fp_reg_ok d3 c
  | FP (FPMul d1 d2 d3) =>
      implb (two_reg_arith c) (d1 =? d2) && fp_reg_ok d1 c && fp_reg_ok d2 c && fp_reg_ok d3 c
  | FP (FPDiv d1 d2 d3) =>
      implb (two_reg_arith c) (d1 =? d2) && fp_reg_ok d1 c && fp_reg_ok d2 c && fp_reg_ok d3 c
  | FP (FPFma d1 d2 d3) =>
      bool_decide (ISA c = ARMv7) && (2 <? fp_reg_count c) &&
      fp_reg_ok d1 c && fp_reg_ok d2 c && fp_reg_ok d3 c
  | FP (FPMov d1 d2) => fp_reg_ok d1 c && fp_reg_ok d2 c
  | FP (FPMovToReg r1 r2 d) => implb (dimindex a =? 32) (negb (r1 =? r2)) && fp_reg_ok d c
  | FP (FPMovFromReg d r1 r2) => implb (dimindex a =? 32) (negb (r1 =? r2)) && fp_reg_ok d c
  | FP (FPToInt d1 d2) => fp_reg_ok d1 c && fp_reg_ok d2 c
  | FP (FPFromInt d1 d2) => fp_reg_ok d1 c && fp_reg_ok d2 c
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "distinct_tar_reg_def" *)
Definition distinct_tar_reg (i : inst a) : bool :=
  match i with
  | Arith (Binop bop r1 r2 ri) => negb (bool_decide (ri = Reg r1))
  | Arith (asm.Shift l r1 r2 ri) => negb (bool_decide (ri = Reg r1))
  | Arith (AddCarry r1 r2 r3 r4) => negb (r1 =? r3) && negb (r1 =? r4)
  | Arith (AddOverflow r1 r2 r3 r4) => negb (r1 =? r3)
  | Arith (SubOverflow r1 r2 r3 r4) => negb (r1 =? r3)
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "two_reg_inst_def" *)
Definition two_reg_inst (i : inst a) : bool :=
  match i with
  | Arith (Binop bop r1 r2 ri) => r1 =? r2
  | Arith (asm.Shift l r1 r2 ri) => r1 =? r2
  | Arith (AddCarry r1 r2 r3 r4) => r1 =? r2
  | Arith (AddOverflow r1 r2 r3 r4) => r1 =? r2
  | Arith (SubOverflow r1 r2 r3 r4) => r1 =? r2
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "every_inst_def" *)
Fixpoint every_inst (P : inst a -> bool) (p : prog a) : bool :=
  match p with
  | Inst i => P i
  | Seq p1 p2 => every_inst P p1 && every_inst P p2
  | Loop names c exit_names => every_inst P c
  | If cmp r1 ri c1 c2 => every_inst P c1 && every_inst P c2
  | OpCurrHeap bop r1 r2 => P (Arith (Binop bop r1 r2 (Reg r2)))
  | MustTerminate p => every_inst P p
  | Call ret dest args handler =>
      match ret with
      | NONE => true
      | SOME (n, (names, (ret_handler, (l1, l2)))) =>
          every_inst P ret_handler &&
          match handler with
          | NONE => true
          | SOME (n, (h, (l1, l2))) => every_inst P h
          end
      end
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "full_inst_ok_less_def" *)
Fixpoint full_inst_ok_less (c : asm_config a) (p : prog a) : bool :=
  match p with
  | Inst i => inst_ok_less c i
  | Seq p1 p2 => full_inst_ok_less c p1 && full_inst_ok_less c p2
  | Loop names p exit_names => full_inst_ok_less c p
  | If cmp r1 ri c1 c2 => full_inst_ok_less c c1 && full_inst_ok_less c c2
  | MustTerminate p => full_inst_ok_less c p
  | Call ret dest args handler =>
      match ret with
      | NONE => true
      | SOME (n, (names, (ret_handler, (l1, l2)))) =>
          full_inst_ok_less c ret_handler &&
          match handler with
          | NONE => true
          | SOME (n, (h, (l1, l2))) => full_inst_ok_less c h
          end
      end
  | ShareInst op r ad =>
      match exp_to_addr ad with
      | SOME (Addr _ w) =>
          if MEM op [asm.Load; asm.Store; Load32; Store32]
          then addr_offset_ok c w
          else if MEM op [Load16; Store16]
          then hw_offset_ok c w
          else byte_offset_ok c w
      | NONE => false
      end
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "wf_names_def" *)
Definition wf_names {A B} (t : spt A * spt B) : bool := wf (FST t) && wf (SND t).

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "wf_cutsets_def" *)
Fixpoint wf_cutsets (p : prog a) : bool :=
  match p with
  | Alloc n s => wf_names s
  | Install _ _ _ _ s => wf_names s
  | Call ret dest args h =>
      match ret with
      | NONE => true
      | SOME (v, (cutset, (ret_handler, (l1, l2)))) =>
          wf_names cutset && wf_cutsets ret_handler &&
          match h with
          | NONE => true
          | SOME (v, (prog0, (l1, l2))) => wf_cutsets prog0
          end
      end
  | FFI x1 y1 x2 y2 z args => wf_names args
  | MustTerminate s => wf_cutsets s
  | Seq s1 s2 => wf_cutsets s1 && wf_cutsets s2
  | Loop names p exit_names => wf names && wf exit_names && wf_cutsets p
  | If cmp r1 ri e2 e3 => wf_cutsets e2 && wf_cutsets e3
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "inst_arg_convention_def" *)
Definition inst_arg_convention (i : inst a) : bool :=
  match i with
  | Arith (AddCarry r1 r2 r3 r4) => r4 =? 0
  | Arith (asm.Shift _ _ _ (Reg r)) => r =? 8
  | Arith (AddOverflow r1 r2 r3 r4) => r4 =? 0
  | Arith (SubOverflow r1 r2 r3 r4) => r4 =? 0
  | Arith (LongMul r1 r2 r3 r4) => (r1 =? 6) && (r2 =? 0) && (r3 =? 0) && (r4 =? 4)
  | Arith (LongDiv r1 r2 r3 r4 r5) => (r1 =? 0) && (r2 =? 6) && (r3 =? 6) && (r4 =? 0)
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "call_arg_convention_def" *)
Fixpoint call_arg_convention (p : prog a) : bool :=
  match p with
  | Inst i => inst_arg_convention i
  | Return x ys => bool_decide (ys = GENLIST (fun x => 2 * (x + 1)) (LENGTH ys))
  | Raise y => y =? 2
  | Install ptr len _ _ _ => (ptr =? 2) && (len =? 4)
  | FFI x ptr len ptr2 len2 args => (ptr =? 2) && (len =? 4) && (ptr2 =? 6) && (len2 =? 8)
  | Alloc n s => n =? 2
  | StoreConsts a0 b c d ws => (a0 =? 0) && (b =? 2) && (c =? 4) && (d =? 6)
  | Call ret dest args h =>
      match ret with
      | NONE => bool_decide (args = GENLIST (fun x => 2 * x) (LENGTH args))
      | SOME (vs, (cutset, (ret_handler, (l1, l2)))) =>
          bool_decide (args = GENLIST (fun x => 2 * (x + 1)) (LENGTH args)) &&
          bool_decide (vs = GENLIST (fun x => 2 * (x + 1)) (LENGTH vs)) &&
          call_arg_convention ret_handler &&
          match h with
          | NONE => true
          | SOME (v, (prog0, (l1, l2))) => (v =? 2) && call_arg_convention prog0
          end
      end
  | MustTerminate s1 => call_arg_convention s1
  | Seq s1 s2 => call_arg_convention s1 && call_arg_convention s2
  | Loop names p exit_names => call_arg_convention p
  | If cmp r1 ri e2 e3 => call_arg_convention e2 && call_arg_convention e3
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "pre_alloc_conventions_def" *)
Definition pre_alloc_conventions (p : prog a) : bool :=
  every_stack_var is_stack_var p && call_arg_convention p.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "post_alloc_conventions_def" *)
Definition post_alloc_conventions (k : N) (prog0 : prog a) : bool :=
  every_var is_phy_var prog0 && every_stack_var (fun x => 2 * k <=? x) prog0 &&
  call_arg_convention prog0.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "extract_labels_def" *)
Fixpoint extract_labels (p : prog a) : list (N * N) :=
  match p with
  | Call ret dest args h =>
      match ret with
      | NONE => []
      | SOME (v, (cutset, (ret_handler, (l1, l2)))) =>
          let ret_rest := extract_labels ret_handler in
          match h with
          | NONE => [(l1, l2)] ++ ret_rest
          | SOME (v, (prog0, (l1', l2'))) =>
              let h_rest := extract_labels prog0 in
              [(l1, l2); (l1', l2')] ++ ret_rest ++ h_rest
          end
      end
  | MustTerminate s1 => extract_labels s1
  | Seq s1 s2 => extract_labels s1 ++ extract_labels s2
  | Loop names p exit_names => extract_labels p
  | If cmp r1 ri e2 e3 => extract_labels e2 ++ extract_labels e3
  | _ => []
  end.

End Defs.
