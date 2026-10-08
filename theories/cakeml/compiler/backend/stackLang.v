(** * CakeML [stackLang]: the stackLang intermediate language (syntax)

    Port of [cakeml/compiler/backend/stackLangScript.sml].

    The constructors of [prog] shadow ASM's [Skip], [Inst], [Call] (and are
    in turn shadowed by wordLang's); ASM's are written [asm.Skip] etc. where
    needed.  HOL's constructor [Set] is [Set_] ([Set] is a Rocq keyword).
    HOL's [Overload]s of instruction shapes are [Abbreviation]s (so
    they can be used in patterns too). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words byte.
From Galette.HOL.src.list.src Require Import list.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.backend Require Import backend_common.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
Open Scope N_scope.
Local Set Warnings "-register-all".

(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "store_name" *)
Inductive store_name : Type :=
| NextFree | EndOfHeap | TriggerGC | HeapLength | ProgStart | BitmapBase
| CurrHeap | OtherHeap | AllocSize | Globals | GlobReal | Handler | GenStart
| CodeBuffer | CodeBufferEnd | BitmapBuffer | BitmapBufferEnd
| Temp : word5 -> store_name.

#[global] Instance store_name_eq_dec : EqDecision store_name.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.
#[global] Instance store_name_inhabited : Inhabited store_name := NextFree.

(** HOL tuples nest to the right: HOL's [prog # num # num # num] is
    [prog * (N * (N * N))].  HOL's type parameter ['a] is the width index [a] (implicit in the
    constructors, explicit in [prog a]). *)
(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "prog" *)
Inductive prog {a : N} : Type :=
| Skip : prog
| Inst : inst a -> prog
| Get : N -> store_name -> prog
| Set_ : store_name -> N -> prog
| OpCurrHeap : binop -> N -> N -> prog
| Call : option (prog * (N * (N * N))) -> (N + N) -> option (prog * (N * N)) -> prog
| Seq : prog -> prog -> prog
| If : cmp -> N -> reg_imm a -> prog -> prog -> prog
| Loop : prog -> prog
| JumpLower : N -> N -> N -> prog
| Alloc : N -> prog
| StoreConsts : N -> N -> option N -> prog
| Raise : N -> prog
| Return : N -> prog
| Break : N -> prog
| Continue : N -> prog
| FFI : mlstring -> N -> N -> N -> N -> N -> prog
| Tick : prog
| LocValue : N -> N -> N -> prog
| Install : N -> N -> N -> N -> N -> prog
| ShMemOp : memop -> N -> addr a -> prog
| CodeBufferWrite : N -> N -> prog
| DataBufferWrite : N -> N -> prog
| RawCall : N -> prog
| StackAlloc : N -> prog
| StackFree : N -> prog
| StackStore : N -> N -> prog
| StackStoreAny : N -> N -> prog
| StackLoad : N -> N -> prog
| StackLoadAny : N -> N -> prog
| StackGetSize : N -> prog
| StackSetSize : N -> prog
| BitmapLoad : N -> N -> prog
| Halt : N -> prog.
Arguments prog : clear implicits.

#[global] Instance prog_inhabited {a} : Inhabited (prog a) := Skip.

(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "While" *)
Abbreviation While cmp r ri c := (Loop (If cmp r ri c (Break 0))).

(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "move" *)
Abbreviation move dest src := (Inst (Arith (Binop Or dest src (Reg src)))).
(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "sub_1_inst" *)
Abbreviation sub_1_inst r1 := (Inst (Arith (Binop Sub r1 r1 (Imm (n2w 1))))).
(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "sub_inst" *)
Abbreviation sub_inst r1 r2 := (Inst (Arith (Binop Sub r1 r1 (Reg r2)))).
(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "add_inst" *)
Abbreviation add_inst r1 r2 := (Inst (Arith (Binop Add r1 r1 (Reg r2)))).
(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "and_inst" *)
Abbreviation and_inst r1 r2 := (Inst (Arith (Binop And r1 r1 (Reg r2)))).
(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "xor_inst" *)
Abbreviation xor_inst r1 r2 := (Inst (Arith (Binop Xor r1 r1 (Reg r2)))).
(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "add_1_inst" *)
Abbreviation add_1_inst r1 := (Inst (Arith (Binop Add r1 r1 (Imm (n2w 1))))).
(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "or_inst" *)
Abbreviation or_inst r1 r2 := (Inst (Arith (Binop Or r1 r1 (Reg r2)))).
(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "add_bytes_in_word_inst" *)
Abbreviation add_bytes_in_word_inst r1 := (Inst (Arith (Binop Add r1 r1 (Imm bytes_in_word)))).
(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "div2_inst" *)
Abbreviation div2_inst r := (Inst (Arith (Shift Lsr r r (Imm (n2w 1))))).
(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "left_shift_inst" *)
Abbreviation left_shift_inst r v := (Inst (Arith (Shift Lsl r r (Imm (n2w v))))).
(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "right_shift_inst" *)
Abbreviation right_shift_inst r v := (Inst (Arith (Shift Lsr r r (Imm (n2w v))))).
(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "const_inst" *)
Abbreviation const_inst r w := (Inst (Const r w)).
(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "load_inst" *)
Abbreviation load_inst r a := (Inst (Mem Load r (Addr a (n2w 0)))).
(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "store_inst" *)
Abbreviation store_inst r a := (Inst (Mem Store r (Addr a (n2w 0)))).

(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "list_Seq_def" *)
Fixpoint list_Seq {a} (l : list (prog a)) : prog a :=
  match l with
  | [] => Skip
  | [x] => x
  | x :: ((y :: xs) as t) => Seq x (list_Seq t)
  end.

(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "gc_stub_location_def" *)
Definition gc_stub_location : N := stack_num_stubs - 1.

(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "store_consts_stub_location_def" *)
Definition store_consts_stub_location : N := gc_stub_location - 1.

(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "gc_stub_location_eq" *)
Theorem gc_stub_location_eq : gc_stub_location = 4.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/stackLangScript.sml" "store_consts_stub_location_eq" *)
Theorem store_consts_stub_location_eq : store_consts_stub_location = 3.
Proof. reflexivity. Qed.
