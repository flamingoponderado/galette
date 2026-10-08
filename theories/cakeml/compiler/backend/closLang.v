(** * CakeML [closLang]: the closLang intermediate language (syntax)

    Partial port of [cakeml/compiler/backend/closLangScript.sml]: the
    datatypes [const], [const_part], [int_op], [word_op], [block_op],
    [glob_op], [mem_op], [op] and [exp].  Not ported: the type
    abbreviations [clos_prog]/[clos_cc], the helper functions and
    theorems ([pure_op], [pure], [contains_App_SOME], [every_Fn_vs], ...).

    Constructor shadowing (HOL keeps them apart by theory): [block_op]'s
    [Cons] shadows [backend_common]'s [tra] constructor [Cons]
    (write [backend_common.Cons]); [int_op]'s [Add]/[Sub] shadow
    [backend_common]'s [opw] constructors; [block_op]'s [Equal] shadows
    [ast]'s [test] constructor ([ast.Equal]). *)

From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics Require Import ast fpSem.
From Galette.cakeml.compiler.backend Require Import backend_common.
Open Scope N_scope.
Local Set Warnings "-register-all".

(*! HOL "cakeml/compiler/backend/closLangScript.sml" "const" *)
Inductive const : Type :=
| ConstCons : N -> list const -> const
| ConstInt : Z -> const
| ConstStr : mlstring -> const
| ConstWord64 : word64 -> const.

#[global] Instance const_inhabited : Inhabited const := ConstInt 0.

(*! HOL "cakeml/compiler/backend/closLangScript.sml" "const_part" *)
Inductive const_part : Type :=
| Con : N -> list N -> const_part
| Int : Z -> const_part
| Str : mlstring -> const_part
| W64 : word64 -> const_part.

#[global] Instance const_part_eq_dec : EqDecision const_part.
Proof.
  intros x y; unfold Decision; decide equality;
    try apply (decide (_ = _)); apply word_eq_dec.
Defined.
#[global] Instance const_part_inhabited : Inhabited const_part := Int 0.

(*! HOL "cakeml/compiler/backend/closLangScript.sml" "int_op" *)
Inductive int_op : Type :=
| Const : Z -> int_op
| Add : int_op
| Sub : int_op
| Mult : int_op
| Div : int_op
| Mod : int_op
| Less : int_op
| LessEq : int_op
| Greater : int_op
| GreaterEq : int_op
| LessConstSmall : N -> int_op.

#[global] Instance int_op_eq_dec : EqDecision int_op.
Proof. intros x y; unfold Decision; decide equality; apply (decide (_ = _)). Defined.
#[global] Instance int_op_inhabited : Inhabited int_op := Add.

(*! HOL "cakeml/compiler/backend/closLangScript.sml" "word_op" *)
Inductive word_op : Type :=
| WordOpw : word_size -> opw -> word_op
| WordShift : word_size -> shift -> N -> word_op
| WordTest : word_size -> test -> word_op
| WordFromInt : word_op
| WordToInt : word_op
| WordFromWord : bool -> word_op
| FP_cmp : fp_cmp -> word_op
| FP_uop : fp_uop -> word_op
| FP_bop : fp_bop -> word_op
| FP_top : fp_top -> word_op.

#[global] Instance word_op_eq_dec : EqDecision word_op.
Proof. intros x y; unfold Decision; decide equality; apply (decide (_ = _)). Defined.
#[global] Instance word_op_inhabited : Inhabited word_op := WordFromInt.

(*! HOL "cakeml/compiler/backend/closLangScript.sml" "block_op" *)
Inductive block_op : Type :=
| Cons : N -> block_op
| ElemAt : N -> block_op
| TagLenEq : N -> N -> block_op
| LenEq : N -> block_op
| TagEq : N -> block_op
| LengthBlock : block_op
| BoolTest : test -> block_op
| BoolNot : block_op
| BoundsCheckBlock : block_op
| ConsExtend : N -> block_op
| FromList : N -> block_op
| ListAppend : block_op
| Constant : const -> block_op
| Equal : block_op
| EqualConst : const_part -> block_op
| Build : list const_part -> block_op.

#[global] Instance block_op_inhabited : Inhabited block_op := LengthBlock.

(*! HOL "cakeml/compiler/backend/closLangScript.sml" "glob_op" *)
Inductive glob_op : Type :=
| Global : N -> glob_op
| SetGlobal : N -> glob_op
| AllocGlobal : glob_op
| GlobalsPtr : glob_op
| SetGlobalsPtr : glob_op.

#[global] Instance glob_op_eq_dec : EqDecision glob_op.
Proof. intros x y; unfold Decision; decide equality; apply (decide (_ = _)). Defined.
#[global] Instance glob_op_inhabited : Inhabited glob_op := AllocGlobal.

(*! HOL "cakeml/compiler/backend/closLangScript.sml" "mem_op" *)
Inductive mem_op : Type :=
| Ref : mem_op
| Update : mem_op
| El : mem_op
| Length : mem_op
| LengthByte : mem_op
| RefByte : bool -> mem_op
| RefArray : mem_op
| DerefByte : mem_op
| UpdateByte : mem_op
| ConcatByteVec : mem_op
| CopyByte : bool -> mem_op
| FromListByte : mem_op
| ToListByte : mem_op
| LengthByteVec : mem_op
| DerefByteVec : mem_op
| StringCmp : bool -> opb -> mem_op
| XorByte : mem_op
| BoundsCheckArray : mem_op
| BoundsCheckByte : bool -> mem_op
| MutCons : N -> N -> mem_op
| UpdateCons : mem_op
| FinaliseCons : mem_op
| ConfigGC : mem_op.

#[global] Instance mem_op_eq_dec : EqDecision mem_op.
Proof. intros x y; unfold Decision; decide equality; apply (decide (_ = _)). Defined.
#[global] Instance mem_op_inhabited : Inhabited mem_op := Ref.

(*! HOL "cakeml/compiler/backend/closLangScript.sml" "op" *)
Inductive op : Type :=
| Label : N -> op
| FFI : mlstring -> op
| IntOp : int_op -> op
| WordOp : word_op -> op
| BlockOp : block_op -> op
| GlobOp : glob_op -> op
| MemOp : mem_op -> op
| Install : op
| ThunkOp : thunk_op -> op.

#[global] Instance op_inhabited : Inhabited op := Install.

(*! HOL "cakeml/compiler/backend/closLangScript.sml" "exp" *)
Inductive exp : Type :=
| Var : tra -> N -> exp
| If : tra -> exp -> exp -> exp -> exp
| Let : tra -> list exp -> exp -> exp
| Raise : tra -> exp -> exp
| Handle : tra -> exp -> exp -> exp
| Tick : tra -> exp -> exp
| Call : tra -> N -> N -> list exp -> exp
| App : tra -> option N -> exp -> list exp -> exp
| Fn : mlstring -> option N -> option (list N) -> N -> exp -> exp
| Letrec : list mlstring -> option N -> option (list N) -> list (N * exp) -> exp -> exp
| Op : tra -> op -> list exp -> exp.

#[global] Instance exp_inhabited : Inhabited exp := Var tra_None 0.
