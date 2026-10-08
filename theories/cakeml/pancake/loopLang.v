(** * Pancake [loopLang]: the loopLang intermediate language

    Port of [cakeml/pancake/loopLangScript.sml].

    HOL's ['a] word-width type variable is the width index [a : N].  HOL
    tuples nest to the right.  [panLang] is required but not imported; its
    [primop] is [panLang.primop].  The [asm] constructors [Const], [Load],
    [Load32], [Shift], [Skip], [Call], [Arith] are shadowed by this module's
    and are written qualified.

    Not ported: [MEM_IMP_exp_size] (about HOL's generated [exp_size], for
    termination only). *)

From Galette Require Import Base.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.pancake Require panLang.
Open Scope N_scope.
#[local] Set Warnings "-register-all".

(*! HOL "cakeml/pancake/loopLangScript.sml" "shift" *)
Abbreviation shift := ast.shift.

(*! HOL "cakeml/pancake/loopLangScript.sml" "exp" *)
Inductive exp (a : N) : Type :=
| Const : word a -> exp a
| Var : N -> exp a
| Lookup : word 5 -> exp a
| Load : exp a -> exp a
| Op : binop -> list (exp a) -> exp a
| Shift : shift -> exp a -> exp a -> exp a
| BaseAddr : exp a
| TopAddr : exp a.
Arguments Const {a} _.
Arguments Var {a} _.
Arguments Lookup {a} _.
Arguments Load {a} _.
Arguments Op {a} _ _.
Arguments Shift {a} _ _ _.
Arguments BaseAddr {a}.
Arguments TopAddr {a}.

(*! HOL "cakeml/pancake/loopLangScript.sml" "loop_arith" *)
Inductive loop_arith : Type :=
| LLongMul : N -> N -> N -> N -> loop_arith
| LLongDiv : N -> N -> N -> N -> N -> loop_arith
| LDiv : N -> N -> N -> loop_arith.

(*! HOL "cakeml/pancake/loopLangScript.sml" "prog" *)
Inductive prog (a : N) : Type :=
| Skip : prog a
| Assign : N -> exp a -> prog a
| Primitive : list N -> panLang.primop -> list N -> prog a
| Arith : loop_arith -> prog a
| Store : exp a -> N -> prog a
| SetGlobal : word 5 -> exp a -> prog a
| Load32 : N -> N -> prog a
| LoadByte : N -> N -> prog a
| Store32 : N -> N -> prog a
| StoreByte : N -> N -> prog a
| Seq : prog a -> prog a -> prog a
| If : cmp -> N -> reg_imm a -> prog a -> prog a -> num_set -> prog a
| Loop : num_set -> prog a -> num_set -> prog a
| Break : N -> prog a
| Continue : N -> prog a
| Raise : N -> prog a
| Return : list N -> prog a
| ShMem : memop -> N -> exp a -> prog a
| Tick : prog a
| Mark : prog a -> prog a
| Fail : prog a
| LocValue : N -> N -> prog a
| Call : option (list N * num_set) -> option N -> list N ->
         option (N * (prog a * (prog a * num_set))) -> prog a
| FFI : mlstring -> N -> N -> N -> N -> num_set -> prog a.
Arguments Skip {a}.
Arguments Assign {a} _ _.
Arguments Primitive {a} _ _ _.
Arguments Arith {a} _.
Arguments Store {a} _ _.
Arguments SetGlobal {a} _ _.
Arguments Load32 {a} _ _.
Arguments LoadByte {a} _ _.
Arguments Store32 {a} _ _.
Arguments StoreByte {a} _ _.
Arguments Seq {a} _ _.
Arguments If {a} _ _ _ _ _ _.
Arguments Loop {a} _ _ _.
Arguments Break {a} _.
Arguments Continue {a} _.
Arguments Raise {a} _.
Arguments Return {a} _.
Arguments ShMem {a} _ _ _.
Arguments Tick {a}.
Arguments Mark {a} _.
Arguments Fail {a}.
Arguments LocValue {a} _ _.
Arguments Call {a} _ _ _ _.
Arguments FFI {a} _ _ _ _ _ _.

#[global] Instance exp_inhabited {a} : Inhabited (exp a) := BaseAddr.
#[global] Instance prog_inhabited {a} : Inhabited (prog a) := Skip.

Section Defs.
Context {a : N}.

(*! HOL "cakeml/pancake/loopLangScript.sml" "nested_seq_def" *)
Fixpoint nested_seq (l : list (prog a)) : prog a :=
  match l with
  | [] => Skip
  | e :: es => Seq e (nested_seq es)
  end.

(*! HOL "cakeml/pancake/loopLangScript.sml" "locals_touched_def" *)
Fixpoint locals_touched (e : exp a) : list N :=
  match e with
  | Const w => []
  | Var v => [v]
  | Lookup name => []
  | Load addr => locals_touched addr
  | Op op wexps => FLAT (MAP locals_touched wexps)
  | Shift sh wexp1 wexp2 => locals_touched wexp1 ++ locals_touched wexp2
  | BaseAddr => []
  | TopAddr => []
  end.

(*! HOL "cakeml/pancake/loopLangScript.sml" "assigned_vars_def" *)
Fixpoint assigned_vars (p : prog a) : list N :=
  match p with
  | Skip => []
  | Assign n e => [n]
  | Primitive lhss pop rhss => lhss
  | Arith arith =>
      match arith with
      | LLongMul v1 v2 v3 v4 => [v1; v2]
      | LLongDiv v1 v2 v3 v4 v5 => [v1; v2]
      | LDiv v1 v2 v3 => [v1]
      end
  | Load32 n m => [m]
  | LoadByte n m => [m]
  | Seq p q => assigned_vars p ++ assigned_vars q
  | If cmp n r p q ns => assigned_vars p ++ assigned_vars q
  | LocValue n m => [n]
  | ShMem op n e => [n]
  | Mark p => assigned_vars p
  | Loop _ p _ => assigned_vars p
  | Call None _ _ _ => []
  | Call (Some (ns, _)) _ _ None => ns
  | Call (Some (ns, _)) _ _ (Some (m, (p, (q, _)))) =>
      ns ++ m :: assigned_vars p ++ assigned_vars q
  | _ => []
  end.

(*! HOL "cakeml/pancake/loopLangScript.sml" "acc_vars_def" *)
Fixpoint acc_vars (p : prog a) (l : num_set) : num_set :=
  match p with
  | Seq p1 p2 => acc_vars p1 (acc_vars p2 l)
  | Break _ => l
  | Continue _ => l
  | Loop l1 body l2 => acc_vars body l
  | If x1 x2 x3 p1 p2 l1 => acc_vars p1 (acc_vars p2 l)
  | Arith arith =>
      match arith with
      | LLongMul v1 v2 v3 v4 => insert v1 tt (insert v2 tt l)
      | LLongDiv v1 v2 v3 v4 v5 => insert v1 tt (insert v2 tt l)
      | LDiv v1 v2 v3 => insert v1 tt l
      end
  | Mark p1 => acc_vars p1 l
  | Tick => l
  | Skip => l
  | Fail => l
  | Raise v => l
  | Return v => l
  | Call ret dest args handler =>
      match ret with
      | None => l
      | Some (vs, live) =>
          let l := list_insert vs l in
          match handler with
          | None => l
          | Some (n, (p1, (p2, l1))) => acc_vars p1 (acc_vars p2 (insert n tt l))
          end
      end
  | LocValue n m => insert n tt l
  | Assign n exp => insert n tt l
  | Primitive lhss pop rhss => list_insert lhss l
  | ShMem op n exp => insert n tt l
  | Store exp n => l
  | SetGlobal w exp => l
  | Load32 n m => insert m tt l
  | LoadByte n m => insert m tt l
  | Store32 n m => l
  | StoreByte n m => l
  | FFI name n1 n2 n3 n4 live => l
  end.

End Defs.
