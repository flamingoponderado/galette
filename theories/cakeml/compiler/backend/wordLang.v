(** * CakeML [wordLang]: the wordLang intermediate language (syntax)

    Port of [cakeml/compiler/backend/wordLangScript.sml].

    - HOL's type parameter ['a] is the width index [a] (implicit in the
      constructors, explicit in [exp a], [prog a]).
    - HOL tuples nest to the right: the [Call] arguments are
      [option (list N * (cutsets * (prog a * (N * N))))] and
      [option (N * (prog a * (N * N)))].
    - The constructors [Const] (of [exp]) and [Skip], [Inst], [Call] (of
      [prog]) shadow ASM's [inst]/[asm] constructors of the same names, and
      [prog]'s shadow stackLang's; ASM's are written [asm.Const],
      [asm.Skip], ... .  HOL's constructor [Set] is [Set_] ([Set] is a Rocq
      keyword).
    - The variable recursors [every_var_exp] etc. take a boolean predicate
      [P : N -> bool] (HOL's [P : num -> bool]).
    - Not ported: [MEM_IMP_exp_size] (about HOL's generated [exp_size]) and
      the term overload [shift] for [word_shift] (HOL's [shift] is also the
      type abbreviation for [ast$shift], ported here; use [word_shift]). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.coretypes Require Import pair.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.backend Require Import backend_common.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import stackLang.
Open Scope N_scope.
Local Set Warnings "-register-all".

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "shift" 12 *)
Abbreviation shift := ast.shift.

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "exp" *)
Inductive exp {a : N} : Type :=
| Const : word a -> exp
| Var : N -> exp
| Lookup : store_name -> exp
| Load : exp -> exp
| Op : binop -> list exp -> exp
| Shift : shift -> exp -> exp -> exp.
Arguments exp : clear implicits.

#[global] Instance exp_inhabited {a} : Inhabited (exp a) := Var 0.

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "ShiftN" *)
Abbreviation ShiftN sh e n := (Shift sh e (Const (n2w n))).

(** Non-GCed cutset, GCed cutset. *)
(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "cutsets" *)
Abbreviation cutsets := (num_set * num_set)%type.

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "prog" *)
Inductive prog {a : N} : Type :=
| Skip : prog
| Move : N -> list (N * N) -> prog
| Inst : inst a -> prog
| Assign : N -> exp a -> prog
| Get : N -> store_name -> prog
| Set_ : store_name -> exp a -> prog
| Store : exp a -> N -> prog
| MustTerminate : prog -> prog
| Call : option (list N * (cutsets * (prog * (N * N)))) ->
         option N -> list N -> option (N * (prog * (N * N))) -> prog
| Seq : prog -> prog -> prog
| If : cmp -> N -> reg_imm a -> prog -> prog -> prog
| Loop : num_set -> prog -> num_set -> prog
| Alloc : N -> cutsets -> prog
| StoreConsts : N -> N -> N -> N -> list (bool * word a) -> prog
| Raise : N -> prog
| Return : N -> list N -> prog
| Break : N -> prog
| Continue : N -> prog
| Tick : prog
| OpCurrHeap : binop -> N -> N -> prog
| LocValue : N -> N -> prog
| Install : N -> N -> N -> N -> cutsets -> prog
| CodeBufferWrite : N -> N -> prog
| DataBufferWrite : N -> N -> prog
| FFI : mlstring -> N -> N -> N -> N -> cutsets -> prog
| ShareInst : memop -> N -> exp a -> prog.
Arguments prog : clear implicits.

#[global] Instance prog_inhabited {a} : Inhabited (prog a) := Skip.

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "raise_stub_location_def" *)
Definition raise_stub_location : N := word_num_stubs - 2.

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "store_consts_stub_location_def" *)
Definition store_consts_stub_location : N := word_num_stubs - 1.

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "raise_stub_location_eq" *)
Theorem raise_stub_location_eq : raise_stub_location = 5.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "store_consts_stub_location_eq" *)
Theorem store_consts_stub_location_eq : store_consts_stub_location = 6.
Proof. reflexivity. Qed.

(** ** Recursors for variables *)

Section Vars.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "every_var_exp_def" *)
Fixpoint every_var_exp (P : N -> bool) (e : exp a) : bool :=
  match e with
  | Var num => P num
  | Load exp => every_var_exp P exp
  | Op wop ls => EVERY (every_var_exp P) ls
  | Shift sh e1 e2 => every_var_exp P e1 && every_var_exp P e2
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "every_var_imm_def" *)
Definition every_var_imm (P : N -> bool) (ri : reg_imm a) : bool :=
  match ri with
  | Reg r => P r
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "every_var_inst_def" *)
Definition every_var_inst (P : N -> bool) (i : inst a) : bool :=
  match i with
  | asm.Const reg w => P reg
  | Arith (Binop bop r1 r2 ri) => P r1 && P r2 && every_var_imm P ri
  | Arith (asm.Shift shift r1 r2 ri) => P r1 && P r2 && every_var_imm P ri
  | Arith (Div r1 r2 r3) => P r1 && P r2 && P r3
  | Arith (AddCarry r1 r2 r3 r4) => P r1 && P r2 && P r3 && P r4
  | Arith (AddOverflow r1 r2 r3 r4) => P r1 && P r2 && P r3 && P r4
  | Arith (SubOverflow r1 r2 r3 r4) => P r1 && P r2 && P r3 && P r4
  | Arith (LongMul r1 r2 r3 r4) => P r1 && P r2 && P r3 && P r4
  | Arith (LongDiv r1 r2 r3 r4 r5) => P r1 && P r2 && P r3 && P r4 && P r5
  | Mem asm.Load r (Addr a0 w) => P r && P a0
  | Mem asm.Store r (Addr a0 w) => P r && P a0
  | Mem Load32 r (Addr a0 w) => P r && P a0
  | Mem Store32 r (Addr a0 w) => P r && P a0
  | Mem Load8 r (Addr a0 w) => P r && P a0
  | Mem Store8 r (Addr a0 w) => P r && P a0
  | FP (FPLess r d1 d2) => P r
  | FP (FPLessEqual r d1 d2) => P r
  | FP (FPEqual r d1 d2) => P r
  | FP (FPMovToReg r1 r2 d) => if dimindex a =? 64 then P r1 else P r1 && P r2
  | FP (FPMovFromReg d r1 r2) => if dimindex a =? 64 then P r1 else P r1 && P r2
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "every_name_def" *)
Definition every_name (P : N -> bool) (t : cutsets) : bool :=
  EVERY P (MAP FST (toAList (FST t))) && EVERY P (MAP FST (toAList (SND t))).

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "every_var_def" *)
Fixpoint every_var (P : N -> bool) (p : prog a) : bool :=
  match p with
  | Skip => true
  | Move pri ls => EVERY P (MAP FST ls) && EVERY P (MAP SND ls)
  | Inst i => every_var_inst P i
  | Assign num exp => P num && every_var_exp P exp
  | Get num store => P num
  | Store exp num => P num && every_var_exp P exp
  | LocValue r _ => P r
  | Install r1 r2 r3 r4 names => P r1 && P r2 && P r3 && P r4 && every_name P names
  | CodeBufferWrite r1 r2 => P r1 && P r2
  | DataBufferWrite r1 r2 => P r1 && P r2
  | FFI ffi_index cptr clen ptr len names =>
      P cptr && P clen && P ptr && P len && every_name P names
  | MustTerminate s1 => every_var P s1
  | Call ret dest args h =>
      EVERY P args &&
      match ret with
      | None => true
      | Some (v, (cutset, (ret_handler, (l1, l2)))) =>
          EVERY P v && every_name P cutset && every_var P ret_handler &&
          match h with
          | None => true
          | Some (v, (prog, (l1, l2))) => P v && every_var P prog
          end
      end
  | Seq s1 s2 => every_var P s1 && every_var P s2
  | If cmp r1 ri e2 e3 => P r1 && every_var_imm P ri && every_var P e2 && every_var P e3
  | Alloc num numset => P num && every_name P numset
  | StoreConsts a0 b c d ws => P a0 && P b && P c && P d
  | Raise num => P num
  | Return num1 ns => P num1 && EVERY P ns
  | OpCurrHeap _ num1 num2 => P num1 && P num2
  | Tick => true
  | Set_ n exp => every_var_exp P exp
  | ShareInst op num exp => P num && every_var_exp P exp
  | Loop names body exit_names =>
      EVERY P (MAP FST (toAList names)) && every_var P body &&
      EVERY P (MAP FST (toAList exit_names))
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "every_stack_var_def" *)
Fixpoint every_stack_var (P : N -> bool) (p : prog a) : bool :=
  match p with
  | FFI ffi_index cptr clen ptr len names => every_name P names
  | Install _ _ _ _ names => every_name P names
  | Call ret dest args h =>
      match ret with
      | None => true
      | Some (v, (cutset, (ret_handler, (l1, l2)))) =>
          every_name P cutset && every_stack_var P ret_handler &&
          match h with
          | None => true
          | Some (v, (prog, (l1, l2))) => every_stack_var P prog
          end
      end
  | Alloc num numset => every_name P numset
  | MustTerminate s1 => every_stack_var P s1
  | Seq s1 s2 => every_stack_var P s1 && every_stack_var P s2
  | If cmp r1 ri e2 e3 => every_stack_var P e2 && every_stack_var P e3
  | Loop names body exit_names => every_stack_var P body
  | _ => true
  end.

(** ** The maximum variable *)

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "max_var_exp_def" *)
Fixpoint max_var_exp (e : exp a) : N :=
  match e with
  | Var num => num
  | Load exp => max_var_exp exp
  | Op wop ls => MAX_LIST (MAP max_var_exp ls)
  | Shift sh exp1 exp2 => MAX (max_var_exp exp1) (max_var_exp exp2)
  | _ => 0
  end.

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "max_var_inst_def" *)
Definition max_var_inst (i : inst a) : N :=
  match i with
  | asm.Skip => 0
  | asm.Const reg w => reg
  | Arith (Binop bop r1 r2 ri) =>
      match ri with Reg r => max3 r1 r2 r | _ => MAX r1 r2 end
  | Arith (asm.Shift shift r1 r2 n) =>
      match n with Reg r => max3 r1 r2 r | _ => MAX r1 r2 end
  | Arith (Div r1 r2 r3) => max3 r1 r2 r3
  | Arith (AddCarry r1 r2 r3 r4) => MAX (MAX r1 r2) (MAX r3 r4)
  | Arith (AddOverflow r1 r2 r3 r4) => MAX (MAX r1 r2) (MAX r3 r4)
  | Arith (SubOverflow r1 r2 r3 r4) => MAX (MAX r1 r2) (MAX r3 r4)
  | Arith (LongMul r1 r2 r3 r4) => MAX (MAX r1 r2) (MAX r3 r4)
  | Arith (LongDiv r1 r2 r3 r4 r5) => MAX (MAX (MAX r1 r2) (MAX r3 r4)) r5
  | Mem asm.Load r (Addr a0 w) => MAX a0 r
  | Mem asm.Store r (Addr a0 w) => MAX a0 r
  | Mem Load32 r (Addr a0 w) => MAX a0 r
  | Mem Store32 r (Addr a0 w) => MAX a0 r
  | Mem Load8 r (Addr a0 w) => MAX a0 r
  | Mem Store8 r (Addr a0 w) => MAX a0 r
  | FP (FPLess r f1 f2) => r
  | FP (FPLessEqual r f1 f2) => r
  | FP (FPEqual r f1 f2) => r
  | FP (FPMovToReg r1 r2 d) => if dimindex a =? 64 then r1 else MAX r1 r2
  | FP (FPMovFromReg d r1 r2) => if dimindex a =? 64 then r1 else MAX r1 r2
  | _ => 0
  end.

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "cutsets_max_def" *)
Definition cutsets_max (c : cutsets) : N :=
  MAX (MAX_LIST (MAP FST (toAList (FST c)))) (MAX_LIST (MAP FST (toAList (SND c)))).

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "max_var_def" *)
Fixpoint max_var (p : prog a) : N :=
  match p with
  | Skip => 0
  | Move pri ls => MAX_LIST (MAP FST ls ++ MAP SND ls)
  | Inst i => max_var_inst i
  | Assign num exp => MAX num (max_var_exp exp)
  | Get num store => num
  | Store exp num => MAX num (max_var_exp exp)
  | Call ret dest args h =>
      let n := MAX_LIST args in
      match ret with
      | None => n
      | Some (v, (cutset, (ret_handler, (l1, l2)))) =>
          let cutset_max := MAX n (cutsets_max cutset) in
          let ret_max := max3 (MAX_LIST v) cutset_max (max_var ret_handler) in
          match h with
          | None => ret_max
          | Some (v, (prog, (l1, l2))) => max3 v ret_max (max_var prog)
          end
      end
  | Seq s1 s2 => MAX (max_var s1) (max_var s2)
  | MustTerminate s1 => max_var s1
  | If cmp r1 ri e2 e3 =>
      let r := match ri with Reg r => MAX r r1 | _ => r1 end in
      max3 r (max_var e2) (max_var e3)
  | Alloc num numset => MAX num (cutsets_max numset)
  | StoreConsts a0 b c d ws => MAX_LIST [a0; b; c; d]
  | Install r1 r2 r3 r4 numset => MAX_LIST [r1; r2; r3; r4; cutsets_max numset]
  | CodeBufferWrite r1 r2 => MAX r1 r2
  | DataBufferWrite r1 r2 => MAX r1 r2
  | FFI ffi_index ptr1 len1 ptr2 len2 numset =>
      MAX_LIST [ptr1; len1; ptr2; len2; cutsets_max numset]
  | Raise num => num
  | OpCurrHeap _ num1 num2 => MAX num1 num2
  | Return num1 ns => MAX_LIST (num1 :: ns)
  | Tick => 0
  | LocValue r l1 => r
  | Set_ n exp => max_var_exp exp
  | ShareInst op num exp => MAX num (max_var_exp exp)
  | Loop names body exit_names =>
      max3 (MAX_LIST (MAP FST (toAList names))) (max_var body)
           (MAX_LIST (MAP FST (toAList exit_names)))
  | _ => 0
  end.

(** ** Word operations *)

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "word_op_def" *)
Definition word_op (op : binop) (ws : list (word a)) : option (word a) :=
  match op, ws with
  | And, ws => Some (FOLDR word_and (word_1comp (n2w 0)) ws)
  | asm.Add, ws => Some (FOLDR word_add (n2w 0) ws)
  | Or, ws => Some (FOLDR word_or (n2w 0) ws)
  | asm.Xor, ws => Some (FOLDR word_xor (n2w 0) ws)
  | asm.Sub, [w1; w2] => Some (word_sub w1 w2)
  | _, _ => None
  end.

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "word_sh_def" *)
Definition word_sh (sh : shift) (w : word a) (n : N) : option (word a) :=
  if negb (n =? 0) && (dimindex a <=? n) then None
  else match sh with
       | Lsl => Some (word_lsl w n)
       | Lsr => Some (word_lsr w n)
       | Asr => Some (word_asr w n)
       | Ror => Some (word_ror w n)
       end.

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "exp_to_addr_def" *)
Definition exp_to_addr (e : exp a) : option (addr a) :=
  match e with
  | Var ad => Some (Addr ad (n2w 0))
  | Op asm.Add [Var ad; Const offset] => Some (Addr ad offset)
  | _ => None
  end.

End Vars.

(*! HOL "cakeml/compiler/backend/wordLangScript.sml" "word_loc" *)
Inductive word_loc (a : N) : Type :=
| Word : word a -> word_loc a
| Loc : N -> N -> word_loc a.
Arguments Word {a} _.
Arguments Loc {a} _ _.

#[global] Instance word_loc_eq_dec {a} : EqDecision (word_loc a).
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.
#[global] Instance word_loc_inhabited {a} : Inhabited (word_loc a) := Loc 0 0.
