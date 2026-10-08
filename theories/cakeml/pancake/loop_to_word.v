(** * Pancake [loop_to_word]: compilation from loopLang to wordLang

    Port of [cakeml/pancake/loop_to_wordScript.sml].

    Both languages share constructor names; [wordLang] (and [asm]) are
    imported and the [loopLang] constructors are written qualified
    ([loopLang.Assign]).  HOL tuples nest to the right. *)

From Galette Require Import Base.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import stackLang wordLang.
From Galette.cakeml.pancake Require panLang loopLang.
Open Scope N_scope.

(*! HOL "cakeml/pancake/loop_to_wordScript.sml" "find_var_def" *)
Definition find_var (ctxt : num_map N) (v : N) : N :=
  match lookup v ctxt with
  | None => 0
  | Some n => n
  end.

Section Defs.
Context {a : N}.

(*! HOL "cakeml/pancake/loop_to_wordScript.sml" "find_reg_imm_def" *)
Definition find_reg_imm (ctxt : num_map N) (ri : reg_imm a) : reg_imm a :=
  match ri with
  | Imm w => Imm w
  | Reg n => Reg (find_var ctxt n)
  end.

(*! HOL "cakeml/pancake/loop_to_wordScript.sml" "comp_exp_def" *)
Fixpoint comp_exp (ctxt : num_map N) (e : loopLang.exp a) : wordLang.exp a :=
  match e with
  | loopLang.Const w => Const w
  | loopLang.Var n => Var (find_var ctxt n)
  | loopLang.Lookup m => Lookup (Temp m)
  | loopLang.BaseAddr => Lookup CurrHeap
  | loopLang.TopAddr =>
      Op Add [Lookup CurrHeap; Shift Lsl (Lookup HeapLength) (Const (n2w 1))]
  | loopLang.Load exp => Load (comp_exp ctxt exp)
  | loopLang.Shift s exp1 exp2 => Shift s (comp_exp ctxt exp1) (comp_exp ctxt exp2)
  | loopLang.Op op wexps =>
      let wexps := MAP (comp_exp ctxt) wexps in
      Op op wexps
  end.

End Defs.

(*! HOL "cakeml/pancake/loop_to_wordScript.sml" "toNumSet_def" *)
Fixpoint toNumSet (l : list N) : num_set :=
  match l with
  | [] => LN
  | n :: ns => insert n tt (toNumSet ns)
  end.

(*! HOL "cakeml/pancake/loop_to_wordScript.sml" "fromNumSet_def" *)
Definition fromNumSet (t : num_set) : list N := MAP FST (toAList t).

(*! HOL "cakeml/pancake/loop_to_wordScript.sml" "mk_new_cutset_def" *)
Definition mk_new_cutset (ctxt : num_map N) (l : num_set) : num_set :=
  insert 0 tt (toNumSet (MAP (find_var ctxt) (fromNumSet l))).

Section Comp.
Context {a : N}.

(*! HOL "cakeml/pancake/loop_to_wordScript.sml" "comp_def" *)
Fixpoint comp (ctxt : num_map N) (p : loopLang.prog a) (l : N * N) : wordLang.prog a * (N * N) :=
  match p with
  | loopLang.Skip => (Skip, l)
  | loopLang.Assign n e => (Assign (find_var ctxt n) (comp_exp ctxt e), l)
  | loopLang.Primitive lhss pop rhss =>
      match pop with
      | panLang.AddCarry =>
          if decide (LENGTH lhss = 2 /\ LENGTH rhss = 3) then
            let res := EL 0 lhss in
            let co := EL 1 lhss in
            let li := EL 0 rhss in
            let ri := EL 1 rhss in
            let ci := EL 2 rhss in
            let scratch_ci := 1 in
            let scratch_res := 3 in
            (Seq (Assign scratch_ci (Var (find_var ctxt ci)))
            (Seq (Inst (Arith (AddCarry scratch_res
                                        (find_var ctxt li)
                                        (find_var ctxt ri)
                                        scratch_ci)))
            (Seq (Assign (find_var ctxt co) (Var scratch_ci))
                 (Assign (find_var ctxt res) (Var scratch_res)))), l)
          else (Skip, l)
      end
  | loopLang.Arith arith =>
      match arith with
      | loopLang.LLongMul r1 r2 r3 r4 =>
          (Inst (Arith (LongMul (find_var ctxt r1) (find_var ctxt r2)
                          (find_var ctxt r3) (find_var ctxt r4))), l)
      | loopLang.LLongDiv r1 r2 r3 r4 r5 =>
          (Inst (Arith (LongDiv (find_var ctxt r1) (find_var ctxt r2)
                          (find_var ctxt r3) (find_var ctxt r4) (find_var ctxt r5))), l)
      | loopLang.LDiv r1 r2 r3 =>
          (Inst (Arith (Div (find_var ctxt r1) (find_var ctxt r2) (find_var ctxt r3))), l)
      end
  | loopLang.Store e v => (Store (comp_exp ctxt e) (find_var ctxt v), l)
  | loopLang.SetGlobal a0 e => (Set_ (Temp a0) (comp_exp ctxt e), l)
  | loopLang.Load32 a0 v =>
      (Inst (Mem asm.Load32 (find_var ctxt v) (Addr (find_var ctxt a0) (n2w 0))), l)
  | loopLang.LoadByte a0 v =>
      (Inst (Mem Load8 (find_var ctxt v) (Addr (find_var ctxt a0) (n2w 0))), l)
  | loopLang.Store32 a0 v =>
      (Inst (Mem Store32 (find_var ctxt v) (Addr (find_var ctxt a0) (n2w 0))), l)
  | loopLang.StoreByte a0 v =>
      (Inst (Mem Store8 (find_var ctxt v) (Addr (find_var ctxt a0) (n2w 0))), l)
  | loopLang.Seq p q =>
      let (wp, l) := comp ctxt p l in
      let (wq, l) := comp ctxt q l in
      (Seq wp wq, l)
  | loopLang.If c n ri p q l1 =>
      let (wp, l) := comp ctxt p l in
      let (wq, l) := comp ctxt q l in
      (Seq (If c (find_var ctxt n) (find_reg_imm ctxt ri) wp wq) Tick, l)
  | loopLang.Loop l1 body l2 =>
      let (wbody, l) := comp ctxt body l in
      (Seq Tick
         (Seq (Loop (mk_new_cutset ctxt l1) wbody (mk_new_cutset ctxt l2))
              Tick), l)
  | loopLang.Break n => (Break n, l)
  | loopLang.Continue n => (Continue n, l)
  | loopLang.Raise v => (Raise (find_var ctxt v), l)
  | loopLang.Return vs => (Return 0 (MAP (find_var ctxt) vs), l)
  | loopLang.Tick => (Tick, l)
  | loopLang.Mark p => comp ctxt p l
  | loopLang.Fail => (Skip, l)
  | loopLang.LocValue n m => (LocValue (find_var ctxt n) m, l)
  | loopLang.Call ret dest args handler =>
      let args := MAP (find_var ctxt) args in
      match ret with
      | None => (Call None dest (0 :: args) None, l)
      | Some (vs, live) =>
          let vs := MAP (find_var ctxt) vs in
          let live := mk_new_cutset ctxt live in
          let new_l := (FST l, SND l + 1) in
          match handler with
          | None => (Call (Some (vs, ((live, LN), (Skip, l)))) dest args None, new_l)
          | Some (n, (p1, (p2, _))) =>
              let (p1, l1) := comp ctxt p1 new_l in
              let (p2, l1) := comp ctxt p2 l1 in
              let new_l := (FST l1, SND l1 + 1) in
              (Seq (Call (Some (vs, ((live, LN), (p2, l)))) dest args
                      (Some (find_var ctxt n, (p1, l1)))) Tick, new_l)
          end
      end
  | loopLang.FFI f ptr1 len1 ptr2 len2 live =>
      let live := mk_new_cutset ctxt live in
      (FFI f (find_var ctxt ptr1) (find_var ctxt len1)
             (find_var ctxt ptr2) (find_var ctxt len2) (live, LN), l)
  | loopLang.ShMem memop n e => (ShareInst memop (find_var ctxt n) (comp_exp ctxt e), l)
  end.

End Comp.

(*! HOL "cakeml/pancake/loop_to_wordScript.sml" "make_ctxt_def" *)
Fixpoint make_ctxt (n : N) (l : list N) (acc : num_map N) : num_map N :=
  match l with
  | [] => acc
  | x :: xs => make_ctxt (n + 2) xs (insert x n acc)
  end.

Section Compile.
Context {a : N}.

(*! HOL "cakeml/pancake/loop_to_wordScript.sml" "comp_func_def" *)
Definition comp_func (name : N) (params : list N) (body : loopLang.prog a) : wordLang.prog a :=
  let vs := fromNumSet (difference (loopLang.acc_vars body LN) (toNumSet params)) in
  let ctxt := make_ctxt 2 (params ++ vs) LN in
  FST (comp ctxt body (name, 2)).

(*! HOL "cakeml/pancake/loop_to_wordScript.sml" "compile_prog_def" *)
Definition compile_prog (p : list (N * (list N * loopLang.prog a)))
    : list (N * (N * wordLang.prog a)) :=
  MAP (fun '(name, (params, body)) =>
         (name, (LENGTH params + 1, comp_func name params body))) p.

(*! HOL "cakeml/pancake/loop_to_wordScript.sml" "compile_def" *)
Definition compile (p : list (N * (list N * loopLang.prog a)))
    : list (N * (N * wordLang.prog a)) :=
  compile_prog p.

End Compile.
