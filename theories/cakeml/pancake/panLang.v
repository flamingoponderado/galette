(** * Pancake [panLang]: abstract syntax of Pancake

    Port of [cakeml/pancake/panLangScript.sml].

    HOL's ['a] word-width type variable is the width index [a : N], an
    implicit argument of the constructors.  HOL tuples nest to the right
    ([eid # varname # prog] is [eid * (varname * prog a)]).

    Names: the [fun_decl] field [return] is a Rocq keyword and is named
    [fun_decl_return] (the record-prefixed form); all other names are HOL's.
    The constructors of [exp]/[prog] shadow the [asm] constructors of the
    same name ([Const], [Load], [Load32], [Shift], [Skip], [Call]); [asm]'s
    are written qualified ([asm.Load]).  Downstream languages
    ([crepLang], [loopLang]) reuse constructor names too and therefore
    [Require] this module without importing it.

    HOL definitions with missing patterns are completed by HOL with [ARB]
    right-hand sides; [global_var_exp] has such cases and they are [ARB]
    here too.

    Not ported: [MEM_IMP_shape_size] and [MEM_IMP_exp_size] (statements
    about HOL's generated [*_size] functions, used for HOL termination
    proofs only). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.finite_maps Require Import alist.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
Open Scope N_scope.
Open Scope hol_string_scope.
#[local] Set Warnings "-register-all".


(** A decision procedure for [o = None] that needs no equality on the
    contents (HOL tests [ALOOKUP ctxt nm = NONE]). *)
#[local] Instance option_None_dec {B} (o : option B) : Decision (o = None).
Proof. destruct o; [right; discriminate|left; reflexivity]. Defined.

(** ** Types *)

(*! HOL "cakeml/pancake/panLangScript.sml" "shift" *)
Abbreviation shift := ast.shift.

(*! HOL "cakeml/pancake/panLangScript.sml" "stcname" *)
Abbreviation stcname := mlstring.

(*! HOL "cakeml/pancake/panLangScript.sml" "fldname" *)
Abbreviation fldname := mlstring.

(*! HOL "cakeml/pancake/panLangScript.sml" "varname" *)
Abbreviation varname := mlstring.

(*! HOL "cakeml/pancake/panLangScript.sml" "funname" *)
Abbreviation funname := mlstring.

(*! HOL "cakeml/pancake/panLangScript.sml" "eid" *)
Abbreviation eid := mlstring.

(*! HOL "cakeml/pancake/panLangScript.sml" "decname" *)
Abbreviation decname := mlstring.

(*! HOL "cakeml/pancake/panLangScript.sml" "index" *)
Abbreviation index := N.

(*! HOL "cakeml/pancake/panLangScript.sml" "shape" *)
Inductive shape : Type :=
| One : shape
| Comb : list shape -> shape
| Named : stcname -> shape.

(*! HOL "cakeml/pancake/panLangScript.sml" "panop" *)
Inductive panop : Type := Mul.

(*! HOL "cakeml/pancake/panLangScript.sml" "varkind" *)
Inductive varkind : Type := Local | Global.

(*! HOL "cakeml/pancake/panLangScript.sml" "exp" *)
Inductive exp (a : N) : Type :=
| Const : word a -> exp a
| Var : varkind -> varname -> exp a
| RStruct : list (exp a) -> exp a
| RField : index -> exp a -> exp a
| NStruct : stcname -> list (fldname * exp a) -> exp a
| NField : fldname -> exp a -> exp a
| Load : shape -> exp a -> exp a
| Load32 : exp a -> exp a
| LoadByte : exp a -> exp a
| Op : binop -> list (exp a) -> exp a
| Panop : panop -> list (exp a) -> exp a
| Cmp : cmp -> exp a -> exp a -> exp a
| Shift : shift -> exp a -> exp a -> exp a
| BaseAddr : exp a
| TopAddr : exp a
| BytesInWord : exp a.
Arguments Const {a} _.
Arguments Var {a} _ _.
Arguments RStruct {a} _.
Arguments RField {a} _ _.
Arguments NStruct {a} _ _.
Arguments NField {a} _ _.
Arguments Load {a} _ _.
Arguments Load32 {a} _.
Arguments LoadByte {a} _.
Arguments Op {a} _ _.
Arguments Panop {a} _ _.
Arguments Cmp {a} _ _ _.
Arguments Shift {a} _ _ _.
Arguments BaseAddr {a}.
Arguments TopAddr {a}.
Arguments BytesInWord {a}.

(*! HOL "cakeml/pancake/panLangScript.sml" "opsize" *)
Inductive opsize : Type := Op8 | OpW | Op32 | Op16.

(*! HOL "cakeml/pancake/panLangScript.sml" "primop" *)
Inductive primop : Type := AddCarry.

(*! HOL "cakeml/pancake/panLangScript.sml" "prog" *)
Inductive prog (a : N) : Type :=
| Skip : prog a
| Dec : varname -> shape -> exp a -> prog a -> prog a
| Assign : varkind -> varname -> exp a -> prog a
| Primitive : varname -> primop -> list (exp a) -> prog a
| Store : exp a -> exp a -> prog a
| Store32 : exp a -> exp a -> prog a
| StoreByte : exp a -> exp a -> prog a
| Seq : prog a -> prog a -> prog a
| If : exp a -> prog a -> prog a -> prog a
| While : exp a -> prog a -> prog a
| Break : prog a
| Continue : prog a
| Call : option (option (varkind * varname) * option (eid * (varname * prog a))) ->
         funname -> list (exp a) -> prog a
| DecCall : varname -> shape -> funname -> list (exp a) -> prog a -> prog a
| ExtCall : funname -> exp a -> exp a -> exp a -> exp a -> prog a
| Raise : eid -> exp a -> prog a
| Return : exp a -> prog a
| ShMemLoad : opsize -> varkind -> varname -> exp a -> prog a
| ShMemStore : opsize -> exp a -> exp a -> prog a
| Tick : prog a
| Annot : mlstring -> mlstring -> prog a.
Arguments Skip {a}.
Arguments Dec {a} _ _ _ _.
Arguments Assign {a} _ _ _.
Arguments Primitive {a} _ _ _.
Arguments Store {a} _ _.
Arguments Store32 {a} _ _.
Arguments StoreByte {a} _ _.
Arguments Seq {a} _ _.
Arguments If {a} _ _ _.
Arguments While {a} _ _.
Arguments Break {a}.
Arguments Continue {a}.
Arguments Call {a} _ _ _.
Arguments DecCall {a} _ _ _ _ _.
Arguments ExtCall {a} _ _ _ _ _.
Arguments Raise {a} _ _.
Arguments Return {a} _.
Arguments ShMemLoad {a} _ _ _ _.
Arguments ShMemStore {a} _ _ _.
Arguments Tick {a}.
Arguments Annot {a} _ _.

(** HOL [fun_decl]; field [return] is [fun_decl_return] ([return] is a
    Rocq keyword). *)
(*! HOL "cakeml/pancake/panLangScript.sml" "fun_decl" *)
Record fun_decl (a : N) : Type := {
  name : mlstring;
  inline : bool;
  export : bool;
  params : list (varname * shape);
  body : prog a;
  fun_decl_return : shape
}.
Arguments name {a} _.
Arguments inline {a} _.
Arguments export {a} _.
Arguments params {a} _.
Arguments body {a} _.
Arguments fun_decl_return {a} _.

(*! HOL "cakeml/pancake/panLangScript.sml" "decl" *)
Inductive decl (a : N) : Type :=
| Function : fun_decl a -> decl a
| Decl : shape -> mlstring -> exp a -> decl a
| ExnDecl : eid -> shape -> decl a
| Name : stcname -> list (fldname * shape) -> decl a.
Arguments Function {a} _.
Arguments Decl {a} _ _ _.
Arguments ExnDecl {a} _ _.
Arguments Name {a} _ _.

(*! HOL "cakeml/pancake/panLangScript.sml" "struct_info" *)
Record struct_info : Type := {
  fields : list (fldname * shape);
  size : N
}.

#[global] Instance varkind_eq_dec : EqDecision varkind.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance opsize_eq_dec : EqDecision opsize.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance panop_eq_dec : EqDecision panop.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance primop_eq_dec : EqDecision primop.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance shape_inhabited : Inhabited shape := One.
#[global] Instance exp_inhabited {a} : Inhabited (exp a) := BaseAddr.
#[global] Instance prog_inhabited {a} : Inhabited (prog a) := Skip.

(*! HOL "cakeml/pancake/panLangScript.sml" "TailCall" *)
Abbreviation TailCall := (Call None).

(*! HOL "cakeml/pancake/panLangScript.sml" "AssignCall" *)
Abbreviation AssignCall s h := (Call (Some (Some s, h))).

(*! HOL "cakeml/pancake/panLangScript.sml" "StandAloneCall" *)
Abbreviation StandAloneCall h := (Call (Some (None, h))).

(** ** Shapes *)

(*! HOL "cakeml/pancake/panLangScript.sml" "is_wf_shape_def" *)
Fixpoint is_wf_shape {A} (ctxt : list (stcname * A)) (sh : shape) : bool :=
  match sh with
  | One => true
  | Comb shs => EVERY (is_wf_shape ctxt) shs
  | Named nm =>
      match ALOOKUP ctxt nm with
      | Some flds => true
      | None => false
      end
  end.

(*! HOL "cakeml/pancake/panLangScript.sml" "is_wf_flds_def" *)
Fixpoint is_wf_flds {A B} (ctxt : list (stcname * A)) (l : list (B * shape)) : bool :=
  match l with
  | [] => true
  | (fld, sh) :: flds => is_wf_shape ctxt sh && is_wf_flds ctxt flds
  end.

(*! HOL "cakeml/pancake/panLangScript.sml" "is_wf_ctxt_def" *)
Fixpoint is_wf_ctxt (l : list (stcname * struct_info)) : bool :=
  match l with
  | [] => true
  | (nm, info) :: ctxt' =>
      bool_decide (ALOOKUP ctxt' nm = None) && is_wf_flds ctxt' (fields info) &&
      is_wf_ctxt ctxt'
  end.

(*! HOL "cakeml/pancake/panLangScript.sml" "size_of_sh_with_ctxt_def" *)
Fixpoint size_of_sh_with_ctxt (ctxt : list (stcname * struct_info)) (sh : shape) : N :=
  match sh with
  | One => 1
  | Comb shapes => SUM (MAP (size_of_sh_with_ctxt ctxt) shapes)
  | Named name =>
      match ALOOKUP ctxt name with
      | Some info => size info
      | None => 1
      end
  end.

(*! HOL "cakeml/pancake/panLangScript.sml" "size_of_shape_def" *)
Fixpoint size_of_shape (sh : shape) : N :=
  match sh with
  | One => 1
  | Comb shapes => SUM (MAP size_of_shape shapes)
  | Named name => 1
  end.

(*! HOL "cakeml/pancake/panLangScript.sml" "shape_to_str_def" *)
Fixpoint shape_to_str (sh : shape) : mlstring :=
  match sh with
  | One => strlit "1"
  | Comb [] => strlit "{}"
  | Comb (x :: xs) =>
      concat (strlit "{" :: shape_to_str x ::
              MAP (fun x => strcat (strlit ",") x) (MAP shape_to_str xs) ++
              [strlit "}"])
  | Named nm => nm
  end.

(** HOL's mutual [shape_val]/[shape_vals]; [shape_vals] is the nested
    [fix] and also the top-level [shape_vals] below. *)
(*! HOL "cakeml/pancake/panLangScript.sml" "shape_val_def" *)
Fixpoint shape_val {a : N} (sh : shape) : exp a :=
  match sh with
  | One => Const (n2w 0)
  | Comb shapes =>
      RStruct ((fix shape_vals (l : list shape) : list (exp a) :=
                  match l with
                  | [] => []
                  | sh :: shs => shape_val sh :: shape_vals shs
                  end) shapes)
  | Named nm => Const (n2w 0)
  end.

Fixpoint shape_vals {a : N} (l : list shape) : list (exp a) :=
  match l with
  | [] => []
  | sh :: shs => shape_val sh :: shape_vals shs
  end.

Lemma shape_val_Comb {a : N} shapes : (shape_val (Comb shapes) : exp a) = RStruct (shape_vals shapes).
Proof. cbn; f_equal; induction shapes; cbn; congruence. Qed.

(** ** Programs *)

(*! HOL "cakeml/pancake/panLangScript.sml" "nested_seq_def" *)
Fixpoint nested_seq {a : N} (l : list (prog a)) : prog a :=
  match l with
  | [] => Skip
  | e :: es => Seq e (nested_seq es)
  end.

(*! HOL "cakeml/pancake/panLangScript.sml" "with_shape_def" *)
Fixpoint with_shape {A} (shs : list shape) (e : list A) : list (list A) :=
  match shs with
  | [] => []
  | sh :: shs => TAKE (size_of_shape sh) e :: with_shape shs (DROP (size_of_shape sh) e)
  end.

(*! HOL "cakeml/pancake/panLangScript.sml" "exp_ids_def" *)
Fixpoint exp_ids {a : N} (p : prog a) : list mlstring :=
  match p with
  | Skip => []
  | Raise e _ => [e]
  | Dec _ _ _ p => exp_ids p
  | Seq p q => exp_ids p ++ exp_ids q
  | If _ p q => exp_ids p ++ exp_ids q
  | While _ p => exp_ids p
  | Call (Some (_, Some (e, (_, ep)))) _ _ => e :: exp_ids ep
  | DecCall _ _ _ _ p => exp_ids p
  | _ => []
  end.

(*! HOL "cakeml/pancake/panLangScript.sml" "is_decl_def" *)
Definition is_decl {a : N} (d : decl a) : bool :=
  match d with Decl sh v e => true | _ => false end.

(*! HOL "cakeml/pancake/panLangScript.sml" "is_exn_decl_def" *)
Definition is_exn_decl {a : N} (d : decl a) : bool :=
  match d with ExnDecl eid sh => true | _ => false end.

(*! HOL "cakeml/pancake/panLangScript.sml" "is_name_def" *)
Definition is_name {a : N} (d : decl a) : bool :=
  match d with Name _ _ => true | _ => false end.

(*! HOL "cakeml/pancake/panLangScript.sml" "size_of_eids_def" *)
Definition size_of_eids {a : N} (prog : list (decl a)) : N :=
  LENGTH (FILTER is_exn_decl prog).

(** HOL [var_exp].  The [NStruct] clause [FLAT (MAP var_exp (MAP SND fes))]
    is computed as [FLAT (MAP (fun fe => var_exp (SND fe)) fes)] (so that
    the recursion is structural); HOL's equations are [var_exp_def]. *)
Fixpoint var_exp {a : N} (e : exp a) : list mlstring :=
  match e with
  | Const w => []
  | Var Local v => [v]
  | Var Global v => []
  | RStruct es => FLAT (MAP var_exp es)
  | RField i e => var_exp e
  | NStruct sn fes => FLAT (MAP (fun fe => var_exp (SND fe)) fes)
  | NField fld e => var_exp e
  | Load sh e => var_exp e
  | Load32 e => var_exp e
  | LoadByte e => var_exp e
  | Op bop es => FLAT (MAP var_exp es)
  | Panop op es => FLAT (MAP var_exp es)
  | Cmp c e1 e2 => var_exp e1 ++ var_exp e2
  | Shift sh e1 e2 => var_exp e1 ++ var_exp e2
  | BaseAddr => []
  | TopAddr => []
  | BytesInWord => []
  end.

(*! HOL "cakeml/pancake/panLangScript.sml" "var_exp_def" *)
Theorem var_exp_def : forall {a : N},
  (forall w : word a, var_exp (Const w) = []) /\
  (forall v, var_exp (Var Local v : exp a) = [v]) /\
  (forall v, var_exp (Var Global v : exp a) = []) /\
  (forall es : list (exp a), var_exp (RStruct es) = FLAT (MAP var_exp es)) /\
  (forall i (e : exp a), var_exp (RField i e) = var_exp e) /\
  (forall sn (fes : list (fldname * exp a)),
     var_exp (NStruct sn fes) = FLAT (MAP var_exp (MAP SND fes))) /\
  (forall fld (e : exp a), var_exp (NField fld e) = var_exp e) /\
  (forall sh (e : exp a), var_exp (Load sh e) = var_exp e) /\
  (forall e : exp a, var_exp (Load32 e) = var_exp e) /\
  (forall e : exp a, var_exp (LoadByte e) = var_exp e) /\
  (forall bop (es : list (exp a)), var_exp (Op bop es) = FLAT (MAP var_exp es)) /\
  (forall op (es : list (exp a)), var_exp (Panop op es) = FLAT (MAP var_exp es)) /\
  (forall c (e1 e2 : exp a), var_exp (Cmp c e1 e2) = var_exp e1 ++ var_exp e2) /\
  (forall sh (e1 e2 : exp a), var_exp (Shift sh e1 e2) = var_exp e1 ++ var_exp e2) /\
  var_exp (BaseAddr : exp a) = [] /\
  var_exp (TopAddr : exp a) = [] /\
  var_exp (BytesInWord : exp a) = [].
Proof.
  intros a; repeat split; intros; try reflexivity.
  cbn; rewrite map_map; reflexivity.
Qed.

(** HOL [global_var_exp]: HOL's definition has no clauses for [Load32],
    [BaseAddr], [TopAddr], [BytesInWord]; HOL's pattern completion makes
    them [ARB], as here. *)
(*! HOL "cakeml/pancake/panLangScript.sml" "global_var_exp_def" *)
Fixpoint global_var_exp {a : N} (e : exp a) : list mlstring :=
  match e with
  | Const w => []
  | Var Local v => []
  | Var Global v => [v]
  | RStruct es => FLAT (MAP global_var_exp es)
  | RField i e => global_var_exp e
  | NStruct sn fes => FLAT (MAP (global_var_exp ∘ SND) fes)
  | NField fld e => global_var_exp e
  | Load sh e => global_var_exp e
  | LoadByte e => global_var_exp e
  | Op bop es => FLAT (MAP global_var_exp es)
  | Panop op es => FLAT (MAP global_var_exp es)
  | Cmp c e1 e2 => global_var_exp e1 ++ global_var_exp e2
  | Shift sh e1 e2 => global_var_exp e1 ++ global_var_exp e2
  | _ => ARB
  end.

(*! HOL "cakeml/pancake/panLangScript.sml" "load_op_def" *)
Definition load_op (o_ : opsize) : memop :=
  match o_ with
  | Op8 => Load8
  | Op16 => Load16
  | OpW => asm.Load
  | Op32 => asm.Load32
  end.

(*! HOL "cakeml/pancake/panLangScript.sml" "store_op_def" *)
Definition store_op (o_ : opsize) : memop :=
  match o_ with
  | Op8 => Store8
  | Op16 => Store16
  | OpW => asm.Store
  | Op32 => asm.Store32
  end.

(*! HOL "cakeml/pancake/panLangScript.sml" "is_function_def" *)
Definition is_function {a : N} (d : decl a) : bool :=
  match d with Function _ => true | _ => false end.

(*! HOL "cakeml/pancake/panLangScript.sml" "functions_def" *)
Fixpoint functions {a : N} (l : list (decl a))
  : list (mlstring * (list (varname * shape) * (prog a * shape))) :=
  match l with
  | [] => []
  | Function fi :: fs => (name fi, (params fi, (body fi, fun_decl_return fi))) :: functions fs
  | Decl _ _ _ :: fs => functions fs
  | ExnDecl _ _ :: fs => functions fs
  | Name _ _ :: fs => functions fs
  end.

(*! HOL "cakeml/pancake/panLangScript.sml" "exceptions_def" *)
Fixpoint exceptions {a : N} (l : list (decl a)) : list (eid * shape) :=
  match l with
  | [] => []
  | Function fi :: fs => exceptions fs
  | Decl _ _ _ :: fs => exceptions fs
  | ExnDecl eid sh :: fs => (eid, sh) :: exceptions fs
  | Name _ _ :: fs => exceptions fs
  end.

(*! HOL "cakeml/pancake/panLangScript.sml" "fun_ids_def" *)
Fixpoint fun_ids {a : N} (p : prog a) : list funname :=
  match p with
  | Dec _ _ _ p => fun_ids p
  | Seq p q => fun_ids p ++ fun_ids q
  | If _ p q => fun_ids p ++ fun_ids q
  | While _ p => fun_ids p
  | Call (Some (_, Some (_, (_, ep)))) nm _ => nm :: fun_ids ep
  | Call _ nm _ => [nm]
  | DecCall _ _ nm _ p => nm :: fun_ids p
  | _ => []
  end.

(*! HOL "cakeml/pancake/panLangScript.sml" "free_var_ids_def" *)
Fixpoint free_var_ids {a : N} (p : prog a) : list varname :=
  match p with
  | Dec vn sh e p => var_exp e ++ FILTER (fun x => bool_decide (vn <> x)) (free_var_ids p)
  | Seq p q => free_var_ids p ++ free_var_ids q
  | If g p q => var_exp g ++ free_var_ids p ++ free_var_ids q
  | While g p => var_exp g ++ free_var_ids p
  | Assign vk v e => if decide (vk = Local) then v :: var_exp e else var_exp e
  | Primitive v pop es => v :: FLAT (MAP var_exp es)
  | Store e1 e2 => var_exp e1 ++ var_exp e2
  | Store32 e1 e2 => var_exp e1 ++ var_exp e2
  | StoreByte e1 e2 => var_exp e1 ++ var_exp e2
  | Raise eid e => var_exp e
  | Return e => var_exp e
  | ExtCall fn e1 e2 e3 e4 => var_exp e1 ++ var_exp e2 ++ var_exp e3 ++ var_exp e4
  | ShMemLoad os vk v e => if decide (vk = Local) then v :: var_exp e else var_exp e
  | ShMemStore os e1 e2 => var_exp e1 ++ var_exp e2
  | Call (Some (None, Some (_, (vn, ep)))) _ args =>
      vn :: free_var_ids ep ++ FLAT (MAP var_exp args)
  | Call (Some (Some (vk, vn), Some (_, (en, ep)))) _ args =>
      (if decide (vk = Local) then [vn] else []) ++ en :: free_var_ids ep ++
      FLAT (MAP var_exp args)
  | Call (Some (Some (vk, vn), None)) _ args =>
      (if decide (vk = Local) then [vn] else []) ++ FLAT (MAP var_exp args)
  | Call (Some (None, None)) _ args => FLAT (MAP var_exp args)
  | Call None _ args => FLAT (MAP var_exp args)
  | DecCall vn _ _ args p => vn :: free_var_ids p ++ FLAT (MAP var_exp args)
  | _ => []
  end.

(*! HOL "cakeml/pancake/panLangScript.sml" "inlinable_def" *)
Definition inlinable {a : N} (d : decl a) : bool :=
  match d with Function fi => inline fi | _ => false end.
