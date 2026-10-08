(** * Pancake [crepLang]: abstract syntax of Crepe

    Port of [cakeml/pancake/crepLangScript.sml].

    HOL's ['a] word-width type variable is the width index [a : N].  HOL
    tuples nest to the right.  [panLang] is required but not imported (its
    constructor names clash with this language's); its [primop] is
    [panLang.primop].  The [asm] constructors [Const], [Load], [Load32],
    [Shift], [Skip], [Call] are shadowed by this module's and are written
    qualified ([asm.Add] is not shadowed).

    [load_shape] and [load_globals] recurse on [SUC]; they are defined with
    [num_rec] and HOL's equations are the tagged [_def] theorems.

    Not ported: [MEM_IMP_exp_size] (about HOL's generated [exp_size], for
    termination only) and the overload [shift] (of
    [backend_common$word_shift], not ported yet). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words byte.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.pancake Require panLang.
Open Scope N_scope.
#[local] Set Warnings "-register-all".

(** ** Types *)

(*! HOL "cakeml/pancake/crepLangScript.sml" "shift" 17 *)
Abbreviation shift := ast.shift.

(*! HOL "cakeml/pancake/crepLangScript.sml" "varname" *)
Abbreviation varname := N.

(*! HOL "cakeml/pancake/crepLangScript.sml" "funname" *)
Abbreviation funname := mlstring.

(*! HOL "cakeml/pancake/crepLangScript.sml" "crepop" *)
Inductive crepop : Type := Mul.

(*! HOL "cakeml/pancake/crepLangScript.sml" "exp" *)
Inductive exp (a : N) : Type :=
| Const : word a -> exp a
| Var : varname -> exp a
| Load : exp a -> exp a
| Load32 : exp a -> exp a
| LoadByte : exp a -> exp a
| LoadGlob : word 5 -> exp a
| Op : binop -> list (exp a) -> exp a
| Crepop : crepop -> list (exp a) -> exp a
| Cmp : cmp -> exp a -> exp a -> exp a
| Shift : shift -> exp a -> exp a -> exp a
| BaseAddr : exp a
| TopAddr : exp a.
Arguments Const {a} _.
Arguments Var {a} _.
Arguments Load {a} _.
Arguments Load32 {a} _.
Arguments LoadByte {a} _.
Arguments LoadGlob {a} _.
Arguments Op {a} _ _.
Arguments Crepop {a} _ _.
Arguments Cmp {a} _ _ _.
Arguments Shift {a} _ _ _.
Arguments BaseAddr {a}.
Arguments TopAddr {a}.

(*! HOL "cakeml/pancake/crepLangScript.sml" "prog" *)
Inductive prog (a : N) : Type :=
| Skip : prog a
| Dec : varname -> exp a -> prog a -> prog a
| Assign : varname -> exp a -> prog a
| Primitive : list varname -> panLang.primop -> list varname -> prog a
| Store : exp a -> exp a -> prog a
| Store32 : exp a -> exp a -> prog a
| StoreByte : exp a -> exp a -> prog a
| StoreGlob : word 5 -> exp a -> prog a
| Seq : prog a -> prog a -> prog a
| If : exp a -> prog a -> prog a -> prog a
| While : exp a -> prog a -> prog a
| Break : N -> prog a
| Continue : N -> prog a
| Call : option (list varname * option (word a * prog a)) -> funname -> list (exp a) -> prog a
| ExtCall : funname -> varname -> varname -> varname -> varname -> prog a
| Raise : word a -> prog a
| Return : list (exp a) -> prog a
| ShMem : memop -> varname -> exp a -> prog a
| Tick : prog a.
Arguments Skip {a}.
Arguments Dec {a} _ _ _.
Arguments Assign {a} _ _.
Arguments Primitive {a} _ _ _.
Arguments Store {a} _ _.
Arguments Store32 {a} _ _.
Arguments StoreByte {a} _ _.
Arguments StoreGlob {a} _ _.
Arguments Seq {a} _ _.
Arguments If {a} _ _ _.
Arguments While {a} _ _.
Arguments Break {a} _.
Arguments Continue {a} _.
Arguments Call {a} _ _ _.
Arguments ExtCall {a} _ _ _ _ _.
Arguments Raise {a} _.
Arguments Return {a} _.
Arguments ShMem {a} _ _ _.
Arguments Tick {a}.

#[global] Instance crepop_eq_dec : EqDecision crepop.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance exp_inhabited {a} : Inhabited (exp a) := BaseAddr.
#[global] Instance prog_inhabited {a} : Inhabited (prog a) := Skip.

(** ** Functions *)

Section Defs.
Context {a : N}.

Definition load_shape (a0 : word a) (i : N) (e : exp a) : list (exp a) :=
  num_rec (fun _ => [])
    (fun _ r a0 =>
       if decide (a0 = n2w 0) then Load e :: r (word_add a0 bytes_in_word)
       else Load (Op Add [e; Const a0]) :: r (word_add a0 bytes_in_word))
    i a0.

(*! HOL "cakeml/pancake/crepLangScript.sml" "load_shape_def" *)
Theorem load_shape_def : forall (a0 : word a) (e : exp a) i,
  load_shape a0 0 e = [] /\
  load_shape a0 (SUC i) e =
    if decide (a0 = n2w 0) then Load e :: load_shape (word_add a0 bytes_in_word) i e
    else Load (Op Add [e; Const a0]) :: load_shape (word_add a0 bytes_in_word) i e.
Proof.
  intros; split; [reflexivity|]. unfold load_shape; rewrite num_rec_SUC; reflexivity.
Qed.

(*! HOL "cakeml/pancake/crepLangScript.sml" "nested_seq_def" *)
Fixpoint nested_seq (l : list (prog a)) : prog a :=
  match l with
  | [] => Skip
  | e :: es => Seq e (nested_seq es)
  end.

(*! HOL "cakeml/pancake/crepLangScript.sml" "stores_def" *)
Fixpoint stores (ad : exp a) (l : list (exp a)) (a0 : word a) : list (prog a) :=
  match l with
  | [] => []
  | e :: es =>
      if decide (a0 = n2w 0) then Store ad e :: stores ad es (word_add a0 bytes_in_word)
      else Store (Op Add [ad; Const a0]) e :: stores ad es (word_add a0 bytes_in_word)
  end.

(*! HOL "cakeml/pancake/crepLangScript.sml" "nested_decs_def" *)
Fixpoint nested_decs (ns : list varname) (es : list (exp a)) (p : prog a) : prog a :=
  match ns, es with
  | [], [] => p
  | n :: ns, e :: es => Dec n e (nested_decs ns es p)
  | [], _ => Skip
  | _, [] => Skip
  end.

(*! HOL "cakeml/pancake/crepLangScript.sml" "store_globals_def" *)
Fixpoint store_globals (ad : word 5) (l : list (exp a)) : list (prog a) :=
  match l with
  | [] => []
  | e :: es => StoreGlob ad e :: store_globals (word_add ad (n2w 1)) es
  end.

Definition load_globals (ad : word 5) (n : N) : list (exp a) :=
  num_rec (fun _ => []) (fun _ r ad => LoadGlob ad :: r (word_add ad (n2w 1))) n ad.

(*! HOL "cakeml/pancake/crepLangScript.sml" "load_globals_def" *)
Theorem load_globals_def : forall (ad : word 5) n,
  load_globals ad 0 = [] /\
  load_globals ad (SUC n) = LoadGlob ad :: load_globals (word_add ad (n2w 1)) n.
Proof.
  intros; split; [reflexivity|]. unfold load_globals; rewrite num_rec_SUC; reflexivity.
Qed.

(*! HOL "cakeml/pancake/crepLangScript.sml" "assign_ret_def" *)
Definition assign_ret (ns : list varname) : prog a :=
  nested_seq (MAP2 Assign ns (load_globals (n2w 0) (LENGTH ns))).

(** HOL's last clause is [var_cexp TopAddrl = []], a variable pattern
    (catch-all); it only matches [TopAddr]. *)
(*! HOL "cakeml/pancake/crepLangScript.sml" "var_cexp_def" *)
Fixpoint var_cexp (e : exp a) : list N :=
  match e with
  | Const w => []
  | Var v => [v]
  | Load e => var_cexp e
  | Load32 e => var_cexp e
  | LoadByte e => var_cexp e
  | LoadGlob ad => []
  | Op bop es => FLAT (MAP var_cexp es)
  | Crepop cop es => FLAT (MAP var_cexp es)
  | Cmp c e1 e2 => var_cexp e1 ++ var_cexp e2
  | Shift sh e1 e2 => var_cexp e1 ++ var_cexp e2
  | BaseAddr => []
  | _TopAddrl => []
  end.

(*! HOL "cakeml/pancake/crepLangScript.sml" "assigned_free_vars_def" *)
Fixpoint assigned_free_vars (p : prog a) : list N :=
  match p with
  | Skip => []
  | Dec n e p => FILTER (fun x => bool_decide (n <> x)) (assigned_free_vars p)
  | Assign n e => [n]
  | Primitive lhss pop rhss => lhss
  | Seq p p' => assigned_free_vars p ++ assigned_free_vars p'
  | If e p p' => assigned_free_vars p ++ assigned_free_vars p'
  | While e p => assigned_free_vars p
  | Call (Some (rts, Some (_, p))) e es => rts ++ assigned_free_vars p
  | Call (Some (rts, None)) e es => rts
  | ShMem op r ad => [r]
  | _ => []
  end.

(*! HOL "cakeml/pancake/crepLangScript.sml" "assigned_vars_def" *)
Fixpoint assigned_vars (p : prog a) : list N :=
  match p with
  | Skip => []
  | Dec n e p => n :: assigned_vars p
  | Assign n e => [n]
  | Primitive lhss pop rhss => lhss
  | Seq p p' => assigned_vars p ++ assigned_vars p'
  | If e p p' => assigned_vars p ++ assigned_vars p'
  | While e p => assigned_vars p
  | Call (Some (rts, Some (_, p))) e es => rts ++ assigned_vars p
  | Call (Some (rts, None)) e es => rts
  | ShMem op r ad => [r]
  | _ => []
  end.

(*! HOL "cakeml/pancake/crepLangScript.sml" "exps_def" *)
Fixpoint exps (e : exp a) : list (exp a) :=
  match e with
  | Const w => [Const w]
  | Var v => [Var v]
  | Load e => exps e
  | Load32 e => exps e
  | LoadByte e => exps e
  | LoadGlob ad => [LoadGlob ad]
  | Op bop es => FLAT (MAP exps es)
  | Crepop pop es => FLAT (MAP exps es)
  | Cmp c e1 e2 => exps e1 ++ exps e2
  | Shift sh e1 e2 => exps e1 ++ exps e2
  | BaseAddr => [BaseAddr]
  | TopAddr => [TopAddr]
  end.

End Defs.
