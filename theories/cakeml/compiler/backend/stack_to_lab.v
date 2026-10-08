(** * CakeML [stack_to_lab]: from stackLang to labLang

    Port of [cakeml/compiler/backend/stack_to_labScript.sml].  The
    [_pmatch] theorem is not ported.

    - Unqualified [Call], [Halt], [LocValue], [Install], [Inst] are
      stackLang's (imported last); labLang's are written [labLang.X] and
      ASM's [asm.X].  HOL's local overload [Asm a] for [Asm (Asmi a)] is
      written out.  HOL's local overload [++] for [misc$Append] is written
      [Append] (HOL's [++] associates to the left).
    - HOL's tests [p1 = Skip] are written as pattern matches (same value).
    - The passes this script composes are referred to qualified
      ([stack_alloc.compile], ...), as HOL's ancestors are [qualified]. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.list.src.list Require Import extra.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.backend Require Import backend_common.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import labLang.
From Galette.cakeml.compiler.backend Require Import stackLang.
From Galette.cakeml.compiler.backend Require data_to_word bvl_to_bvi stack_alloc
  stack_remove stack_names stack_rawcall.
Open Scope N_scope.

Section StackToLab.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/stack_to_labScript.sml" "compile_jump_def" *)
Definition compile_jump (d : N + N) : line a :=
  match d with
  | inl n => LabAsm (labLang.Jump (Lab n 0)) (n2w 0) [] 0
  | inr r => Asm (Asmi (JumpReg r)) [] 0
  end.

(*! HOL "cakeml/compiler/backend/stack_to_labScript.sml" "negate_def" *)
Definition negate (c : cmp) : cmp :=
  match c with
  | Less => NotLess
  | Equal => NotEqual
  | Lower => NotLower
  | Test => NotTest
  | NotLess => Less
  | NotEqual => Equal
  | NotLower => Lower
  | NotTest => Test
  end.

(*! HOL "cakeml/compiler/backend/stack_to_labScript.sml" "find_lab_def" *)
Definition find_lab (n : N) (labs : list N) : N :=
  match oEL n labs with
  | None => 0
  | Some k => k
  end.

Definition is_Skip (p : prog a) : bool := match p with Skip => true | _ => false end.

(*! HOL "cakeml/compiler/backend/stack_to_labScript.sml" "flatten_def" *)
Fixpoint flatten (t : bool) (p : prog a) (n m : N) (conts breaks : list N)
    : app_list (line a) * (bool * N) :=
  match p with
  | Tick => (List [Asm (Asmi (asm.Inst asm.Skip)) [] 0], (false, m))
  | Inst i => (List [Asm (Asmi (asm.Inst i)) [] 0], (false, m))
  | Halt _ => (List [LabAsm labLang.Halt (n2w 0) [] 0], (true, m))
  | Seq p1 p2 =>
      let '(xs, (nr1, m)) := flatten false p1 n m conts breaks in
      let '(ys, (nr2, m)) := flatten false p2 n m conts breaks in
      if t then (Append (Append xs (List [Label n 1 0])) ys, (nr1 || nr2, m))
      else (Append xs ys, (nr1 || nr2, m))
  | If c r ri p1 p2 =>
      let '(xs, (nr1, m)) := flatten false p1 n m conts breaks in
      let '(ys, (nr2, m)) := flatten false p2 n m conts breaks in
      if is_Skip p1 && is_Skip p2 then (List [], (false, m))
      else if is_Skip p1 then
        (Append (Append (List [LabAsm (labLang.JumpCmp c r ri (Lab n m)) (n2w 0) [] 0]) ys)
                (List [Label n m 0]), (false, m + 1))
      else if is_Skip p2 then
        (Append (Append (List [LabAsm (labLang.JumpCmp (negate c) r ri (Lab n m)) (n2w 0) [] 0]) xs)
                (List [Label n m 0]), (false, m + 1))
      else if nr1 then
        (Append (Append (Append
           (List [LabAsm (labLang.JumpCmp (negate c) r ri (Lab n m)) (n2w 0) [] 0]) xs)
           (List [Label n m 0])) ys, (nr2, m + 1))
      else if nr2 then
        (Append (Append (Append
           (List [LabAsm (labLang.JumpCmp c r ri (Lab n m)) (n2w 0) [] 0]) ys)
           (List [Label n m 0])) xs, (nr1, m + 1))
      else
        (Append (Append (Append (Append
           (List [LabAsm (labLang.JumpCmp c r ri (Lab n m)) (n2w 0) [] 0]) ys)
           (List [LabAsm (labLang.Jump (Lab n (m + 1))) (n2w 0) [] 0; Label n m 0])) xs)
           (List [Label n (m + 1) 0]), (nr1 && nr2, m + 2))
  | Loop p1 =>
      let cont_lab := m in
      let break_lab := m + 1 in
      let '(xs, (_, m)) := flatten false p1 n (m + 2) (cont_lab :: conts) (break_lab :: breaks) in
      (Append (Append (List [Label n cont_lab 0]) xs)
         (List [LabAsm (labLang.Jump (Lab n cont_lab)) (n2w 0) [] 0;
                Label n break_lab 0]), (false, m))
  | Raise r => (List [Asm (Asmi (JumpReg r)) [] 0], (true, m))
  | Return r => (List [Asm (Asmi (JumpReg r)) [] 0], (true, m))
  | Break k => (List [LabAsm (labLang.Jump (Lab n (find_lab k breaks))) (n2w 0) [] 0], (true, m))
  | Continue k => (List [LabAsm (labLang.Jump (Lab n (find_lab k conts))) (n2w 0) [] 0], (true, m))
  | RawCall n => (List [LabAsm (labLang.Jump (Lab n 1)) (n2w 0) [] 0], (true, m))
  | Call None dest handler => (List [compile_jump dest], (true, m))
  | Call (Some (p1, (lr, (l1, l2)))) dest handler =>
      let '(xs, (nr1, m)) := flatten false p1 n m conts breaks in
      let prefix := Append (List [LabAsm (labLang.LocValue lr (Lab l1 l2)) (n2w 0) [] 0;
                                  compile_jump dest; Label l1 l2 0]) xs in
      match handler with
      | None => (prefix, (nr1, m))
      | Some (p2, (k1, k2)) =>
          let '(ys, (nr2, m)) := flatten false p2 n m conts breaks in
          (Append prefix
             (Append (Append (List [LabAsm (labLang.Jump (Lab n m)) (n2w 0) [] 0; Label k1 k2 0]) ys)
                     (List [Label n m 0])), (nr1 && nr2, m + 1))
      end
  | JumpLower r1 r2 target =>
      (List [LabAsm (labLang.JumpCmp Lower r1 (Reg r2) (Lab target 0)) (n2w 0) [] 0], (false, m))
  | FFI ffi_index _ _ _ _ lr =>
      (List [LabAsm (labLang.LocValue lr (Lab n m)) (n2w 0) [] 0;
             LabAsm (CallFFI ffi_index) (n2w 0) [] 0;
             Label n m 0], (false, m + 1))
  | LocValue i l1 l2 => (List [LabAsm (labLang.LocValue i (Lab l1 l2)) (n2w 0) [] 0], (false, m))
  | Install _ _ _ _ ret =>
      (List [LabAsm (labLang.LocValue ret (Lab n m)) (n2w 0) [] 0;
             LabAsm labLang.Install (n2w 0) [] 0;
             Label n m 0], (false, m + 1))
  | ShMemOp op r ad => (List [Asm (ShareMem op r ad) [] 0], (false, m))
  | CodeBufferWrite r1 r2 => (List [Asm (Cbw r1 r2) [] 0], (false, m))
  | _ => (List [], (false, m))
  end.

(*! HOL "cakeml/compiler/backend/stack_to_labScript.sml" "is_Seq_def" *)
Definition is_Seq (p : prog a) : bool := match p with Seq p1 p2 => true | _ => false end.

(*! HOL "cakeml/compiler/backend/stack_to_labScript.sml" "prog_to_section_def" *)
Definition prog_to_section (np : N * prog a) : sec a :=
  let '(n, p) := np in
  let '(lines, (_, m)) := flatten true p n (stack_alloc.next_lab p 2) [] [] in
  Section_ n (append (Append lines (List [Label n (if is_Seq p then m else 1) 0]))).

End StackToLab.

(*! HOL "cakeml/compiler/backend/stack_to_labScript.sml" "is_gen_gc_def" *)
Definition is_gen_gc (g : data_to_word.gc_kind_ty) : bool :=
  match g with data_to_word.Generational l => true | _ => false end.

(** The fields of HOL's record, in HOL's order. *)
(*! HOL "cakeml/compiler/backend/stack_to_labScript.sml" "config" *)
Record config : Type := {
  reg_names : num_map N;
  jump : bool;
  perf_calls : bool
}.

Section Compile.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/stack_to_labScript.sml" "compile_def" *)
Definition compile (stack_conf : config) (data_conf : data_to_word.config) (max_heap sp : N)
    (offset : word a * word a) (prog0 : list (N * prog a)) : list (sec a) :=
  let prog0 := stack_rawcall.compile prog0 in
  let prog0 := stack_alloc.compile data_conf prog0 in
  let prog0 := stack_remove.compile (jump stack_conf) offset
                 (is_gen_gc (data_to_word.gc_kind data_conf))
                 max_heap sp bvl_to_bvi.InitGlobals_location prog0 in
  let prog0 := stack_names.compile (reg_names stack_conf) prog0 in
  MAP prog_to_section prog0.

(*! HOL "cakeml/compiler/backend/stack_to_labScript.sml" "compile_no_stubs_def" *)
Definition compile_no_stubs (f : num_map N) (jump : bool) (offset : word a * word a) (sp : N)
    (prog0 : list (N * prog a)) : list (sec a) :=
  MAP prog_to_section
    (stack_names.compile f
      (MAP (stack_remove.prog_comp jump offset sp)
        (MAP stack_alloc.prog_comp prog0))).

End Compile.
