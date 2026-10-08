(** * Pancake [panPtreeConversion]: parse trees to the Pancake AST

    Port of [cakeml/pancake/parser/panPtreeConversionScript.sml].

    - The conversion functions are polymorphic in the word width [a]
      (HOL's ['a]).  HOL's option-monad [do]-notation is written with
      [OPTION_BIND]; [f ' x] is [OPTION_BIND x f], [lift] is [OPTION_MAP],
      [lift2] is [OPTION_MAP2], [++] on options is [OPTION_CHOICE].
    - [destLf]/[destTOK] are this script's own copies (HOL: "Copied from
      tokenUtilsTheory"); [destTOK] shadows [grammar]'s pair version.
    - HOL defines [conv_Shape], [conv_Exp] (mutually with [conv_ArgList],
      [conv_FieldList], [conv_Field], [conv_binaryExps], [conv_panops],
      [conv_shifts]) and [conv_Prog] by well-founded recursion on the parse
      tree size.  Here they are structural [Fixpoint]s: the list-processing
      helpers take the tree function as an argument (and are unfolded by the
      guard checker), and [conv_Prog]'s [ProgNT] case maps [conv_Prog] over
      all children before taking [LAST]/[butlast] of the results.  HOL's
      defining equations are the tagged [*_def] theorems.
    - [OPT_MMAP] ([listScript]) is not yet in [list.v]; a local copy is
      defined here (as in [crep_to_loop.v]).

    Not ported: the [list_size] lemmas ([list_size_butlast],
    [list_size_MEM]), which serve HOL's termination proofs only. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.integer Require Import integer_word.
From Galette.HOL.src.string Require Import string.
From Galette.HOL.src.sort Require Import ternaryComparisons.
From Galette.cakeml.basis.pure Require Import mlstring mlint.
From Galette.cakeml.basis.pure Require mlmap.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.pancake Require Import panLang.
From Galette.HOL.examples.formal_languages.context_free Require Import location grammar peg pegexec.
From Galette.cakeml.pancake.parser Require Import panLexer panPEG.
From Galette.HOL.src.list.src.list Require Import extra.
Open Scope N_scope.
Open Scope hol_string_scope.

#[local] Instance word_inhabited {a} : Inhabited (word a) := n2w 0.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "destLf_def" *)
Definition destLf {A B L} (t : parsetree A B L) : option (symbol A B) :=
  match t with Lf (x, _) => SOME x | _ => NONE end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "destTOK_def" *)
Definition destTOK {A B} (s : symbol A B) : option A :=
  match s with TOK t => SOME t | _ => NONE end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "tokcheck_def" *)
Definition tokcheck {A B L} `{EqDecision A} (pt : parsetree A B L) (expected : A) : bool :=
  match OPTION_BIND (destLf pt) destTOK with
  | SOME actual => bool_decide (actual = expected)
  | NONE => false
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "dest_annot_tok_def" *)
Definition dest_annot_tok {B L} (pt : parsetree token B L) : option string :=
  match OPTION_BIND (destLf pt) destTOK with
  | SOME (AnnotCommentT c) => SOME c
  | _ => NONE
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "kw_def" *)
Definition kw (k : keyword) : token := KeywordT k.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "isNT_def" *)
Definition isNT {B X L} `{EqDecision B} `{EqDecision X} (nodeNT : (B + X) * L) (ntm : B)
    : bool :=
  bool_decide (FST nodeNT = inl ntm).

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "argsNT_def" *)
Definition argsNT {A B L} `{EqDecision B} (t : parsetree A B L) (ntm : B)
    : option (list (parsetree A B L)) :=
  match t with
  | Lf _ => NONE
  | Nd nodeNT args => if decide (FST nodeNT = inl ntm) then SOME args else NONE
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "is_add_with_carry_def" *)
Definition is_add_with_carry (s : mlstring) : bool := bool_decide (s = strlit "__add_with_carry__").

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_int_def" *)
Definition conv_int {B L} (tree : parsetree token B L) : option Z :=
  match OPTION_BIND (destLf tree) destTOK with
  | SOME (IntT n) => SOME n
  | _ => NONE
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_nat_def" *)
Definition conv_nat {B L} (tree : parsetree token B L) : option N :=
  match conv_int tree with
  | SOME n => if (n >=? 0)%Z then SOME (Z.to_N n) else NONE
  | _ => NONE
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_const_def" *)
Definition conv_const {a B L} (t : parsetree token B L) : option (exp a) :=
  OPTION_MAP (fun i => Const (i2w i)) (conv_int t).

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_ident_def" *)
Definition conv_ident {B L} (tree : parsetree token B L) : option mlstring :=
  match OPTION_BIND (destLf tree) destTOK with
  | SOME (IdentT s) => SOME (implode s)
  | _ => NONE
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_ffi_ident_def" *)
Definition conv_ffi_ident {B L} (tree : parsetree token B L) : option mlstring :=
  match OPTION_BIND (destLf tree) destTOK with
  | SOME (ForeignIdent s) => SOME (implode s)
  | _ => NONE
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_var_def" *)
Definition conv_var {a B L} (t : parsetree token B L) : option (exp a) := OPTION_MAP (Var Global) (conv_ident t).

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "binaryExps_def" *)
Definition binaryExps : list pancakeNT := [EOrNT; EXorNT; EAndNT; EAddNT].

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "panExps_def" *)
Definition panExps : list pancakeNT := [EMulNT].

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "isSubOp_def" *)
Definition isSubOp {a} (e : exp a) : bool :=
  match e with Op Sub [e1; e2] => true | _ => false end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_binop_def" *)
Fixpoint conv_binop {L} (t : parsetree token pancakeNT L) : option binop :=
  match t with
  | Nd nodeNT args =>
      if isNT nodeNT AddOpsNT then
        match args with [leaf] => conv_binop leaf | _ => NONE end
      else NONE
  | leaf =>
      if tokcheck leaf PlusT then SOME Add
      else if tokcheck leaf MinusT then SOME Sub
      else if tokcheck leaf AndT then SOME And
      else if tokcheck leaf OrT then SOME Or
      else if tokcheck leaf XorT then SOME Xor
      else NONE
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_panop_def" *)
Fixpoint conv_panop {L} (t : parsetree token pancakeNT L) : option panop :=
  match t with
  | Nd nodeNT args =>
      if isNT nodeNT MulOpsNT then
        match args with [leaf] => conv_panop leaf | _ => NONE end
      else NONE
  | leaf => if tokcheck leaf StarT then SOME Mul else NONE
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_shift_def" *)
Fixpoint conv_shift {L} (t : parsetree token pancakeNT L) : option shift :=
  match t with
  | Nd nodeNT args =>
      if isNT nodeNT ShiftOpsNT then
        match args with [leaf] => conv_shift leaf | _ => NONE end
      else NONE
  | leaf =>
      if tokcheck leaf LslT then SOME Lsl
      else if tokcheck leaf LsrT then SOME Lsr
      else if tokcheck leaf AsrT then SOME Asr
      else if tokcheck leaf RorT then SOME Ror
      else NONE
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_cmp_def" *)
Fixpoint conv_cmp {L} (t : parsetree token pancakeNT L) : option (cmp * bool) :=
  match t with
  | Nd nodeNT args =>
      if isNT nodeNT CmpOpsNT || isNT nodeNT EqOpsNT then
        match args with [leaf] => conv_cmp leaf | _ => NONE end
      else NONE
  | leaf =>
      if tokcheck leaf EqT then SOME (asm.Equal, false)
      else if tokcheck leaf NeqT then SOME (NotEqual, false)
      else if tokcheck leaf LessT then SOME (Less, false)
      else if tokcheck leaf GeqT then SOME (NotLess, false)
      else if tokcheck leaf GreaterT then SOME (Less, true)
      else if tokcheck leaf LeqT then SOME (NotLess, true)
      else if tokcheck leaf LowerT then SOME (Lower, false)
      else if tokcheck leaf HigherT then SOME (Lower, true)
      else if tokcheck leaf HigheqT then SOME (NotLower, false)
      else if tokcheck leaf LoweqT then SOME (NotLower, true)
      else NONE
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_default_shape_def" *)
Definition conv_default_shape {B L} (tree : parsetree token B L) : option shape :=
  match OPTION_BIND (destLf tree) destTOK with
  | SOME DefaultShT => SOME One
  | _ => NONE
  end.

Fixpoint conv_Shape {L} (tree : parsetree token pancakeNT L) : option shape :=
  match conv_default_shape tree with
  | SOME s => SOME s
  | _ =>
    match conv_int tree with
    | SOME n =>
        if (n <? 1)%Z then NONE
        else if decide (n = 1%Z) then SOME One
        else SOME (Comb (REPLICATE (Z.to_N n) One))
    | NONE =>
        match conv_ident tree with
        | SOME id => SOME (Named id)
        | NONE =>
            match tree with
            | Nd nodeNT ts =>
                if decide (FST nodeNT = inl ShapeCombNT)
                then OPTION_MAP Comb (OPT_MMAP conv_Shape ts)
                else NONE
            | Lf _ => NONE
            end
        end
    end
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_Shape_def" *)
Theorem conv_Shape_def {L} : forall (tree : parsetree token pancakeNT L),
  conv_Shape tree =
  match conv_default_shape tree with
  | SOME s => SOME s
  | _ =>
    match conv_int tree with
    | SOME n =>
        if (n <? 1)%Z then NONE
        else if decide (n = 1%Z) then SOME One
        else SOME (Comb (REPLICATE (Z.to_N n) One))
    | NONE =>
        match conv_ident tree with
        | SOME id => SOME (Named id)
        | NONE =>
            match argsNT tree ShapeCombNT with
            | SOME ts => OPTION_MAP Comb (OPT_MMAP conv_Shape ts)
            | _ => NONE
            end
        end
    end
  end.
Proof.
  intros tree; destruct tree as [p|p l]; [reflexivity|].
  cbn [conv_Shape]; unfold argsNT.
  destruct (conv_default_shape _); [reflexivity|].
  destruct (conv_int _); [reflexivity|].
  destruct (conv_ident _); [reflexivity|].
  destruct (decide _); reflexivity.
Qed.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_params_def" *)
Fixpoint conv_params {L} (as_ : list (parsetree token pancakeNT L)) : option (list (mlstring * shape)) :=
  match as_ with
  | s :: t :: ps =>
      match conv_Shape s with
      | SOME sh =>
          match conv_ident t with
          | SOME v => OPTION_MAP (cons (v, sh)) (conv_params ps)
          | _ => NONE
          end
      | _ => NONE
      end
  | [] => SOME []
  | _ => NONE
  end.

(** ** Expressions *)

Section ExpHelpers.
Context {a : N} {L : Type}.
Variable conv_Exp : parsetree token pancakeNT L -> option (exp a).

(** HOL [conv_ArgList], given [conv_Exp]. *)
Definition conv_ArgList_with (tree : parsetree token pancakeNT L) : option (list (exp a)) :=
  if tokcheck tree NotT then SOME []
  else
    match tree with
    | Nd nodeNT args =>
        if decide (FST nodeNT = inl ArgListNT) then
          match args with t :: ts => OPT_MMAP conv_Exp (t :: ts) | _ => NONE end
        else NONE
    | Lf _ => NONE
    end.

(** HOL [conv_Field], given [conv_Exp]. *)
Definition conv_Field_with (tree : parsetree token pancakeNT L) : option (mlstring * exp a) :=
  match tree with
  | Nd nodeNT args =>
      if decide (FST nodeNT = inl NmdFieldNT) then
        match args with
        | [t1; t2] =>
            OPTION_BIND (conv_ident t1) (fun fld =>
            OPTION_BIND (conv_Exp t2) (fun exp => SOME (fld, exp)))
        | _ => NONE
        end
      else NONE
  | Lf _ => NONE
  end.

(** HOL [conv_FieldList], given [conv_Exp]. *)
Definition conv_FieldList_with (tree : parsetree token pancakeNT L) : option (list (mlstring * exp a)) :=
  match tree with
  | Nd nodeNT args =>
      if decide (FST nodeNT = inl NmdFieldListNT) then
        match args with t :: ts => OPT_MMAP conv_Field_with (t :: ts) | _ => NONE end
      else NONE
  | Lf _ => NONE
  end.

(** HOL [conv_binaryExps], given [conv_Exp]. *)
Fixpoint conv_binaryExps_with (l : list (parsetree token pancakeNT L)) (res : exp a) {struct l} : option (exp a) :=
  match l with
  | [] => SOME res
  | t1 :: t2 :: ts =>
      OPTION_BIND (conv_binop t1) (fun op =>
      OPTION_BIND (conv_Exp t2) (fun e =>
      match res with
      | Op bop es =>
          if bool_decide (bop <> op) || isSubOp res then
            conv_binaryExps_with ts (Op op [res; e])
          else conv_binaryExps_with ts (Op bop (APPEND es [e]))
      | e' => conv_binaryExps_with ts (Op op [e'; e])
      end))
  | _ => NONE
  end.

(** HOL [conv_panops], given [conv_Exp]. *)
Fixpoint conv_panops_with (l : list (parsetree token pancakeNT L)) (res : exp a) {struct l} : option (exp a) :=
  match l with
  | [] => SOME res
  | t1 :: t2 :: ts =>
      OPTION_BIND (conv_panop t1) (fun op =>
      OPTION_BIND (conv_Exp t2) (fun e =>
      match res with
      | Panop bop es => conv_panops_with ts (Panop op [res; e])
      | e' => conv_panops_with ts (Panop op [e'; e])
      end))
  | _ => NONE
  end.

(** HOL [conv_shifts], given [conv_Exp]. *)
Fixpoint conv_shifts_with (l : list (parsetree token pancakeNT L)) (res : exp a) {struct l} : option (exp a) :=
  match l with
  | [] => SOME res
  | t1 :: t2 :: ts =>
      OPTION_BIND (conv_shift t1) (fun op =>
      OPTION_BIND (conv_Exp t2) (fun e =>
      conv_shifts_with ts (Shift op res e)))
  | _ => NONE
  end.

End ExpHelpers.

Fixpoint conv_Exp {a L} (t : parsetree token pancakeNT L) {struct t} : option (exp a) :=
  match t with
  | Nd nodeNT args =>
    if isNT nodeNT EFieldNT then
      match args with
      | [] => NONE
      | [t] => conv_Exp t
      | t :: ts => FOLDL (fun e t =>
                         match conv_nat t with
                         | SOME n => OPTION_MAP2 RField (SOME n) e
                         | NONE => match conv_ident t with
                                   | SOME i => OPTION_MAP2 NField (SOME i) e
                                   | NONE => NONE
                                   end
                         end) (conv_Exp t) ts
      end
    else if isNT nodeNT RawStructNT then
      match args with
      | [ts] => OPTION_BIND (conv_ArgList_with conv_Exp ts) (fun es => SOME (RStruct es))
      | _ => NONE
      end
    else if isNT nodeNT NmdStructNT then
      match args with
      | [t1; t2] =>
          OPTION_BIND (conv_ident t1) (fun nm =>
          OPTION_BIND (conv_FieldList_with conv_Exp t2) (fun flds => SOME (NStruct nm flds)))
      | _ => NONE
      end
    else if isNT nodeNT ENotNT then
      match args with
      | [t] => conv_Exp t
      | [_; t] => OPTION_MAP (Cmp asm.Equal (Const (n2w 0))) (conv_Exp t)
      | _ => NONE
      end
    else if isNT nodeNT ELoadByteNT then
      match args with [t] => OPTION_MAP LoadByte (conv_Exp t) | _ => NONE end
    else if isNT nodeNT ELoad32NT then
      match args with [t] => OPTION_MAP Load32 (conv_Exp t) | _ => NONE end
    else if isNT nodeNT ELoadNT then
      match args with
      | [t1; t2] =>
          OPTION_BIND (conv_Shape t1) (fun s =>
          OPTION_BIND (conv_Exp t2) (fun e => SOME (Load s e)))
      | _ => NONE
      end
    else if isNT nodeNT ECmpNT || isNT nodeNT EEqNT then
      match args with
      | [e] => conv_Exp e
      | [e1; op; e2] =>
          OPTION_BIND (conv_Exp e1) (fun e1' =>
          OPTION_BIND (conv_cmp op) (fun '(op', b) =>
          OPTION_BIND (conv_Exp e2) (fun e2' =>
          SOME (if b then Cmp op' e2' e1' else Cmp op' e1' e2'))))
      | _ => NONE
      end
    else if isNT nodeNT ExpNT then
      match args with
      | [e] => conv_Exp e
      | e1 :: args' =>
          OPTION_BIND (OPT_MMAP conv_Exp (e1 :: args')) (fun es =>
          SOME (Cmp NotEqual (Const (n2w 0)) (Op Or es)))
      | _ => NONE
      end
    else if isNT nodeNT EBoolAndNT then
      match args with
      | [e] => conv_Exp e
      | e1 :: args' =>
          OPTION_BIND (OPT_MMAP conv_Exp (e1 :: args')) (fun es =>
          SOME (Op And (MAP (fun e => Cmp NotEqual (Const (n2w 0)) e) es)))
      | _ => NONE
      end
    else if isNT nodeNT EShiftNT then
      match args with
      | e :: es => OPTION_BIND (conv_Exp e) (conv_shifts_with conv_Exp es)
      | _ => NONE
      end
    else if EXISTS (isNT nodeNT) binaryExps then
      match args with
      | [] => NONE
      | e :: es => OPTION_BIND (conv_Exp e) (conv_binaryExps_with conv_Exp es)
      end
    else if EXISTS (isNT nodeNT) panExps then
      match args with
      | [] => NONE
      | e :: es => OPTION_BIND (conv_Exp e) (conv_panops_with conv_Exp es)
      end
    else NONE
  | leaf =>
    if tokcheck leaf (kw BaseK) then SOME BaseAddr
    else if tokcheck leaf (kw TopK) then SOME TopAddr
    else if tokcheck leaf (kw BiwK) then SOME BytesInWord
    else if tokcheck leaf (kw TrueK) then SOME (Const (n2w 1))
    else if tokcheck leaf (kw FalseK) then SOME (Const (n2w 0))
    else OPTION_CHOICE (conv_const leaf) (conv_var leaf)
  end.

Definition conv_ArgList {a L} : parsetree token pancakeNT L -> option (list (exp a)) := conv_ArgList_with conv_Exp.
Definition conv_FieldList {a L} : parsetree token pancakeNT L -> option (list (mlstring * exp a)) :=
  conv_FieldList_with conv_Exp.
Definition conv_Field {a L} : parsetree token pancakeNT L -> option (mlstring * exp a) := conv_Field_with conv_Exp.
Definition conv_binaryExps {a L} : list (parsetree token pancakeNT L) -> exp a -> option (exp a) :=
  conv_binaryExps_with conv_Exp.
Definition conv_panops {a L} : list (parsetree token pancakeNT L) -> exp a -> option (exp a) := conv_panops_with conv_Exp.
Definition conv_shifts {a L} : list (parsetree token pancakeNT L) -> exp a -> option (exp a) := conv_shifts_with conv_Exp.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_Exp_def" *)
Theorem conv_Exp_def {a L} :
  (forall tree, @conv_ArgList a L tree =
     if tokcheck tree NotT then SOME []
     else match argsNT tree ArgListNT with
          | SOME (t :: ts) => OPT_MMAP conv_Exp (t :: ts)
          | _ => NONE
          end) /\
  (forall tree, @conv_FieldList a L tree =
     match argsNT tree NmdFieldListNT with
     | SOME (t :: ts) => OPT_MMAP conv_Field (t :: ts)
     | _ => NONE
     end) /\
  (forall tree, @conv_Field a L tree =
     match argsNT tree NmdFieldNT with
     | SOME [t1; t2] =>
         OPTION_BIND (conv_ident t1) (fun fld =>
         OPTION_BIND (conv_Exp t2) (fun exp => SOME (fld, exp)))
     | _ => NONE
     end) /\
  (forall nodeNT args, @conv_Exp a L (Nd nodeNT args) =
    if isNT nodeNT EFieldNT then
      match args with
      | [] => NONE
      | [t] => conv_Exp t
      | t :: ts => FOLDL (fun e t =>
                         match conv_nat t with
                         | SOME n => OPTION_MAP2 RField (SOME n) e
                         | NONE => match conv_ident t with
                                   | SOME i => OPTION_MAP2 NField (SOME i) e
                                   | NONE => NONE
                                   end
                         end) (conv_Exp t) ts
      end
    else if isNT nodeNT RawStructNT then
      match args with
      | [ts] => OPTION_BIND (conv_ArgList ts) (fun es => SOME (RStruct es))
      | _ => NONE
      end
    else if isNT nodeNT NmdStructNT then
      match args with
      | [t1; t2] =>
          OPTION_BIND (conv_ident t1) (fun nm =>
          OPTION_BIND (conv_FieldList t2) (fun flds => SOME (NStruct nm flds)))
      | _ => NONE
      end
    else if isNT nodeNT ENotNT then
      match args with
      | [t] => conv_Exp t
      | [_; t] => OPTION_MAP (Cmp asm.Equal (Const (n2w 0))) (conv_Exp t)
      | _ => NONE
      end
    else if isNT nodeNT ELoadByteNT then
      match args with [t] => OPTION_MAP LoadByte (conv_Exp t) | _ => NONE end
    else if isNT nodeNT ELoad32NT then
      match args with [t] => OPTION_MAP Load32 (conv_Exp t) | _ => NONE end
    else if isNT nodeNT ELoadNT then
      match args with
      | [t1; t2] =>
          OPTION_BIND (conv_Shape t1) (fun s =>
          OPTION_BIND (conv_Exp t2) (fun e => SOME (Load s e)))
      | _ => NONE
      end
    else if isNT nodeNT ECmpNT || isNT nodeNT EEqNT then
      match args with
      | [e] => conv_Exp e
      | [e1; op; e2] =>
          OPTION_BIND (conv_Exp e1) (fun e1' =>
          OPTION_BIND (conv_cmp op) (fun '(op', b) =>
          OPTION_BIND (conv_Exp e2) (fun e2' =>
          SOME (if b then Cmp op' e2' e1' else Cmp op' e1' e2'))))
      | _ => NONE
      end
    else if isNT nodeNT ExpNT then
      match args with
      | [e] => conv_Exp e
      | e1 :: args' =>
          OPTION_BIND (OPT_MMAP conv_Exp (e1 :: args')) (fun es =>
          SOME (Cmp NotEqual (Const (n2w 0)) (Op Or es)))
      | _ => NONE
      end
    else if isNT nodeNT EBoolAndNT then
      match args with
      | [e] => conv_Exp e
      | e1 :: args' =>
          OPTION_BIND (OPT_MMAP conv_Exp (e1 :: args')) (fun es =>
          SOME (Op And (MAP (fun e => Cmp NotEqual (Const (n2w 0)) e) es)))
      | _ => NONE
      end
    else if isNT nodeNT EShiftNT then
      match args with
      | e :: es => OPTION_BIND (conv_Exp e) (conv_shifts es)
      | _ => NONE
      end
    else if EXISTS (isNT nodeNT) binaryExps then
      match args with
      | [] => NONE
      | e :: es => OPTION_BIND (conv_Exp e) (conv_binaryExps es)
      end
    else if EXISTS (isNT nodeNT) panExps then
      match args with
      | [] => NONE
      | e :: es => OPTION_BIND (conv_Exp e) (conv_panops es)
      end
    else NONE) /\
  (forall l, @conv_Exp a L (Lf l) =
    let leaf := Lf l in
    if tokcheck leaf (kw BaseK) then SOME BaseAddr
    else if tokcheck leaf (kw TopK) then SOME TopAddr
    else if tokcheck leaf (kw BiwK) then SOME BytesInWord
    else if tokcheck leaf (kw TrueK) then SOME (Const (n2w 1))
    else if tokcheck leaf (kw FalseK) then SOME (Const (n2w 0))
    else OPTION_CHOICE (conv_const leaf) (conv_var leaf)) /\
  (forall e, @conv_binaryExps a L [] e = SOME e) /\
  (forall t1 t2 ts res, @conv_binaryExps a L (t1 :: t2 :: ts) res =
      OPTION_BIND (conv_binop t1) (fun op =>
      OPTION_BIND (conv_Exp t2) (fun e =>
      match res with
      | Op bop es =>
          if bool_decide (bop <> op) || isSubOp res then conv_binaryExps ts (Op op [res; e])
          else conv_binaryExps ts (Op bop (APPEND es [e]))
      | e' => conv_binaryExps ts (Op op [e'; e])
      end))) /\
  (forall t e, @conv_binaryExps a L [t] e = NONE) /\
  (forall e, @conv_panops a L [] e = SOME e) /\
  (forall t1 t2 ts res, @conv_panops a L (t1 :: t2 :: ts) res =
      OPTION_BIND (conv_panop t1) (fun op =>
      OPTION_BIND (conv_Exp t2) (fun e =>
      match res with
      | Panop bop es => conv_panops ts (Panop op [res; e])
      | e' => conv_panops ts (Panop op [e'; e])
      end))) /\
  (forall t e, @conv_panops a L [t] e = NONE) /\
  (forall e, @conv_shifts a L [] e = SOME e) /\
  (forall t1 t2 ts res, @conv_shifts a L (t1 :: t2 :: ts) res =
      OPTION_BIND (conv_shift t1) (fun op =>
      OPTION_BIND (conv_Exp t2) (fun e => conv_shifts ts (Shift op res e)))) /\
  (forall t e, @conv_shifts a L [t] e = NONE).
Proof.
  repeat split; intros; try reflexivity; destruct tree as [p|p l]; try reflexivity;
    unfold argsNT, conv_ArgList, conv_ArgList_with, conv_FieldList, conv_FieldList_with,
      conv_Field, conv_Field_with;
    repeat match goal with |- context [decide ?P] => destruct (decide P) end;
    reflexivity.
Qed.

(** ** Statements *)

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_NonRecStmt_def" *)
Definition conv_NonRecStmt {a L} (t : parsetree token pancakeNT L) : option (prog a) :=
  match t with
  | Nd nodeNT args =>
    if isNT nodeNT AssignNT then
      match args with
      | [dst; src] => OPTION_MAP2 (Assign Global) (conv_ident dst) (conv_Exp src)
      | _ => NONE
      end
    else if isNT nodeNT StoreNT then
      match args with
      | [dst; src] => OPTION_MAP2 Store (conv_Exp dst) (conv_Exp src)
      | _ => NONE
      end
    else if isNT nodeNT StoreByteNT then
      match args with
      | [dst; src] => OPTION_MAP2 StoreByte (conv_Exp dst) (conv_Exp src)
      | _ => NONE
      end
    else if isNT nodeNT Store32NT then
      match args with
      | [dst; src] => OPTION_MAP2 Store32 (conv_Exp dst) (conv_Exp src)
      | _ => NONE
      end
    else if isNT nodeNT SharedLoadNT then
      match args with
      | [v; e] => OPTION_MAP2 (ShMemLoad OpW Global) (conv_ident v) (conv_Exp e)
      | _ => NONE
      end
    else if isNT nodeNT SharedLoadByteNT then
      match args with
      | [v; e] => OPTION_MAP2 (ShMemLoad Op8 Global) (conv_ident v) (conv_Exp e)
      | _ => NONE
      end
    else if isNT nodeNT SharedLoad16NT then
      match args with
      | [v; e] => OPTION_MAP2 (ShMemLoad Op16 Global) (conv_ident v) (conv_Exp e)
      | _ => NONE
      end
    else if isNT nodeNT SharedLoad32NT then
      match args with
      | [v; e] => OPTION_MAP2 (ShMemLoad Op32 Global) (conv_ident v) (conv_Exp e)
      | _ => NONE
      end
    else if isNT nodeNT SharedStoreNT then
      match args with
      | [v; e] => OPTION_MAP2 (ShMemStore OpW) (conv_Exp v) (conv_Exp e)
      | _ => NONE
      end
    else if isNT nodeNT SharedStoreByteNT then
      match args with
      | [v; e] => OPTION_MAP2 (ShMemStore Op8) (conv_Exp v) (conv_Exp e)
      | _ => NONE
      end
    else if isNT nodeNT SharedStore16NT then
      match args with
      | [v; e] => OPTION_MAP2 (ShMemStore Op16) (conv_Exp v) (conv_Exp e)
      | _ => NONE
      end
    else if isNT nodeNT SharedStore32NT then
      match args with
      | [v; e] => OPTION_MAP2 (ShMemStore Op32) (conv_Exp v) (conv_Exp e)
      | _ => NONE
      end
    else if isNT nodeNT ExtCallNT then
      match args with
      | [name; ptr; clen; array; alen] =>
          OPTION_BIND (conv_ffi_ident name) (fun name' =>
          OPTION_BIND (conv_Exp ptr) (fun ptr' =>
          OPTION_BIND (conv_Exp clen) (fun clen' =>
          OPTION_BIND (conv_Exp array) (fun array' =>
          OPTION_BIND (conv_Exp alen) (fun alen' =>
          SOME (ExtCall name' ptr' clen' array' alen'))))))
      | _ => NONE
      end
    else if isNT nodeNT ThrowNT then
      match args with
      | [id; e] =>
          OPTION_BIND (conv_ident id) (fun eid =>
          OPTION_BIND (conv_Exp e) (fun e' => SOME (Raise eid e')))
      | _ => NONE
      end
    else if isNT nodeNT ReturnNT then
      match args with
      | [e] => OPTION_MAP Return (conv_Exp e)
      | _ => NONE
      end
    else NONE
  | leaf =>
    if tokcheck leaf (kw SkipK) then SOME Skip
    else if tokcheck leaf (kw BrK) then SOME Break
    else if tokcheck leaf (kw ContK) then SOME Continue
    else if tokcheck leaf (kw TicK) then SOME Tick
    else match dest_annot_tok leaf with
         | SOME c => SOME (Annot (strlit "@") (implode c))
         | NONE => NONE
         end
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "butlast_def" *)
Fixpoint butlast {A} (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => if NULL xs then [] else x :: butlast xs
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "butlast_length" *)
Theorem butlast_length : forall {A} (xs : list A), LENGTH (butlast xs) = LENGTH xs - 1.
Proof.
  intros A xs; induction xs as [|x xs IH]; [reflexivity|].
  destruct xs as [|y ys]; [reflexivity|].
  change (butlast (x :: y :: ys)) with (x :: butlast (y :: ys)).
  change (LENGTH (x :: butlast (y :: ys))) with (SUC (LENGTH (butlast (y :: ys)))).
  rewrite IH; cbn [LENGTH]; lia.
Qed.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "butlast_tl" *)
Theorem butlast_tl : forall {A} (xs : list A), butlast (TL xs) = TL (butlast xs).
Proof.
  intros A [|x [|y ys]]; reflexivity.
Qed.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "butlast_append" *)
Theorem butlast_append : forall {A} (xs ys : list A),
  butlast (xs ++ ys) = if NULL ys then butlast xs else xs ++ butlast ys.
Proof.
  intros A xs ys; induction xs as [|x xs IH].
  - destruct ys; reflexivity.
  - cbn [app butlast]; rewrite IH.
    destruct ys as [|y ys]; cbn [NULL]; [rewrite app_nil_r; reflexivity|].
    destruct xs; reflexivity.
Qed.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "parsetree_locs_def" *)
Definition parsetree_locs {A B} (tree : parsetree A B locs) : locn * locn :=
  match tree with
  | Nd (_, Locs p1 p2) _ => (p1, p2)
  | Lf (_, Locs p1 p2) => (p1, p2)
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "posn_string_def" *)
Definition posn_string (l : locn) : mlstring :=
  match l with
  | POSN lnum cnum => strcat (strcat (num_to_str lnum) (strlit ":")) (num_to_str cnum)
  | EOFpt => strlit "EOF"
  | UNKNOWNpt => strlit "UNKNOWN"
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "locs_comment_def" *)
Definition locs_comment (p : locn * locn) : mlstring :=
  let (p1, p2) := p in
  concat [strlit "("; posn_string p1; strlit " "; posn_string p2; strlit ")"].

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "add_locs_annot_def" *)
Definition add_locs_annot {a A B} (ptree : parsetree A B locs) (prog : prog a) : panLang.prog a :=
  Seq (Annot (strlit "location") (locs_comment (parsetree_locs ptree))) prog.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_Dec_def" *)
Definition conv_Dec {a} (t : ptree) : option (shape * (mlstring * exp a)) :=
  match t with
  | Nd nodeNT args =>
    if isNT nodeNT DecNT then
      match args with
      | [sh; id; e] =>
          OPTION_BIND (conv_Shape sh) (fun sh =>
          OPTION_BIND (conv_ident id) (fun v =>
          OPTION_BIND (conv_Exp e) (fun e' => SOME (sh, (v, e')))))
      | _ => NONE
      end
    else NONE
  | _ => NONE
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_GlobalDec_def" *)
Definition conv_GlobalDec {a} (t : ptree) : option (shape * (mlstring * exp a)) :=
  match t with
  | Nd nodeNT args =>
    if isNT nodeNT GlobalDecNT then
      match args with
      | [sh; id; e] =>
          OPTION_BIND (conv_Shape sh) (fun sh =>
          OPTION_BIND (conv_ident id) (fun v =>
          OPTION_BIND (conv_Exp e) (fun e' => SOME (sh, (v, e')))))
      | _ => NONE
      end
    else NONE
  | _ => NONE
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_ExnDec_def" *)
Definition conv_ExnDec {L} (tree : parsetree token pancakeNT L) : option (mlstring * shape) :=
  match argsNT tree ExnDecNT with
  | SOME [id; sh] =>
      OPTION_BIND (conv_ident id) (fun eid =>
      OPTION_BIND (conv_Shape sh) (fun sh' => SOME (eid, sh')))
  | _ => NONE
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_DecCall_def" *)
Definition conv_DecCall {a} (t : ptree)
    : option (shape * (mlstring * (mlstring * list (exp a)))) :=
  match t with
  | Nd nodeNT args =>
    if isNT nodeNT DecCallNT then
      match args with
      | s :: i :: e :: ts =>
          OPTION_BIND (conv_Shape s) (fun s' =>
          OPTION_BIND (conv_ident i) (fun i' =>
          OPTION_BIND (conv_ident e) (fun e' =>
          OPTION_BIND (match ts with [] => SOME [] | args :: _ => conv_ArgList args end)
            (fun args' => SOME (s', (i', (e', args')))))))
      | _ => NONE
      end
    else NONE
  | _ => NONE
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_Ret_def" *)
Definition conv_Ret {L} (tree : parsetree token pancakeNT L) : option (option (option (varkind * mlstring))) :=
  if tokcheck tree (kw RetK) then SOME NONE
  else if tokcheck tree NotT then SOME (SOME NONE)
  else
    match argsNT tree RetNT with
    | SOME [id] => OPTION_BIND (conv_ident id) (fun var => SOME (SOME (SOME (Global, var))))
    | _ => NONE
    end.

(** The [ProgNT] case: HOL's
    [FOLDR (λt' p. lift2 Seq t' p) (conv_Prog (LAST ts))
       (MAP conv_Prog (t::butlast ts))], computed from the converted
    children [rs = MAP conv_Prog (t::ts)]. *)
Definition conv_ProgNT_seq {a} (rs : list (option (prog a))) : option (prog a) :=
  FOLDR (fun t' p => OPTION_MAP2 Seq t' p) (LAST rs) (butlast rs).

Fixpoint conv_Prog {a} (t : ptree) {struct t} : option (prog a) :=
  match t with
  | Nd nodeNT args =>
    let nd := Nd nodeNT args in
    if isNT nodeNT DecNT then
      match args with
      | [d; p] =>
          OPTION_BIND (conv_Dec d) (fun '(sh, (v, e')) =>
          OPTION_BIND (conv_Prog p) (fun p' =>
          SOME (add_locs_annot nd (Dec v sh e' p'))))
      | _ => NONE
      end
    else if isNT nodeNT IfNT then
      match args with
      | [e; p1; p2] =>
          OPTION_BIND (conv_Exp e) (fun e' =>
          OPTION_BIND (conv_Prog p1) (fun p1' =>
          OPTION_BIND (conv_Prog p2) (fun p2' =>
          SOME (add_locs_annot nd (If e' p1' p2')))))
      | _ => NONE
      end
    else if isNT nodeNT WhileNT then
      match args with
      | [e; p] =>
          OPTION_BIND (conv_Exp e) (fun e' =>
          OPTION_BIND (conv_Prog p) (fun p' =>
          SOME (add_locs_annot nd (While e' p'))))
      | _ => NONE
      end
    else if isNT nodeNT DecCallNT then
      match args with
      | [dec; p] =>
          OPTION_BIND (conv_DecCall dec) (fun '(s', (i', (e', args'))) =>
          OPTION_BIND (conv_Prog p) (fun p' =>
          if is_add_with_carry e'
          then SOME (add_locs_annot nd
                       (Dec i' s' (shape_val s') (Seq (Primitive i' AddCarry args') p')))
          else SOME (add_locs_annot nd (DecCall i' s' e' args' p'))))
      | _ => NONE
      end
    else if isNT nodeNT HandleNT then
      match args with
      | [ret; f; ts; eid; id; p] =>
          OPTION_BIND (conv_Ret ret) (fun r' =>
          OPTION_BIND r' (fun r'' =>
          OPTION_BIND (conv_ident f) (fun fname =>
          OPTION_BIND (conv_ArgList ts) (fun args =>
          OPTION_BIND (conv_ident eid) (fun ename =>
          OPTION_BIND (conv_ident id) (fun evar =>
          OPTION_BIND (conv_Prog p) (fun prog =>
          SOME (add_locs_annot nd
                  (Call (SOME (r'', SOME (ename, (evar, prog)))) fname args)))))))))
      | _ => NONE
      end
    else if isNT nodeNT CallNT then
      match args with
      | [r; e; args] =>
          OPTION_BIND (conv_Ret r) (fun r' =>
          OPTION_BIND (conv_ident e) (fun e' =>
          OPTION_BIND (conv_ArgList args) (fun args' =>
          if is_add_with_carry e' then
            match r' with
            | SOME (SOME (_, vn)) => SOME (add_locs_annot nd (Primitive vn AddCarry args'))
            | _ => NONE
            end
          else
            SOME (add_locs_annot nd (Call (OPTION_MAP (fun x => (x, NONE)) r') e' args')))))
      | _ => NONE
      end
    else if isNT nodeNT ProgNT then
      match args with
      | t :: ts =>
          if negb (NULL ts) then conv_ProgNT_seq (MAP conv_Prog (t :: ts))
          else conv_Prog t
      | _ => NONE
      end
    else OPTION_MAP (add_locs_annot nd) (conv_NonRecStmt (Nd nodeNT args))
  | leaf => OPTION_MAP (add_locs_annot leaf) (conv_NonRecStmt leaf)
  end.

Lemma LAST_MAP {A B} `{Inhabited A} `{Inhabited B} (f : A -> B) x l :
  LAST (MAP f (x :: l)) = f (LAST (x :: l)).
Proof. revert x; induction l as [|y l IH]; intros x; [reflexivity|]; apply IH. Qed.

Lemma butlast_MAP {A B} (f : A -> B) l : butlast (MAP f l) = MAP f (butlast l).
Proof.
  induction l as [|x l IH]; [reflexivity|].
  destruct l as [|y l]; [reflexivity|]; cbn [MAP List.map butlast NULL] in *; rewrite <- IH; reflexivity.
Qed.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_Prog_def" *)
Theorem conv_Prog_def {a} :
  (forall nodeNT args, @conv_Prog a (Nd nodeNT args) =
    let nd := Nd nodeNT args in
    if isNT nodeNT DecNT then
      match args with
      | [d; p] =>
          OPTION_BIND (conv_Dec d) (fun '(sh, (v, e')) =>
          OPTION_BIND (conv_Prog p) (fun p' =>
          SOME (add_locs_annot nd (Dec v sh e' p'))))
      | _ => NONE
      end
    else if isNT nodeNT IfNT then
      match args with
      | [e; p1; p2] =>
          OPTION_BIND (conv_Exp e) (fun e' =>
          OPTION_BIND (conv_Prog p1) (fun p1' =>
          OPTION_BIND (conv_Prog p2) (fun p2' =>
          SOME (add_locs_annot nd (If e' p1' p2')))))
      | _ => NONE
      end
    else if isNT nodeNT WhileNT then
      match args with
      | [e; p] =>
          OPTION_BIND (conv_Exp e) (fun e' =>
          OPTION_BIND (conv_Prog p) (fun p' =>
          SOME (add_locs_annot nd (While e' p'))))
      | _ => NONE
      end
    else if isNT nodeNT DecCallNT then
      match args with
      | [dec; p] =>
          OPTION_BIND (conv_DecCall dec) (fun '(s', (i', (e', args'))) =>
          OPTION_BIND (conv_Prog p) (fun p' =>
          if is_add_with_carry e'
          then SOME (add_locs_annot nd
                       (Dec i' s' (shape_val s') (Seq (Primitive i' AddCarry args') p')))
          else SOME (add_locs_annot nd (DecCall i' s' e' args' p'))))
      | _ => NONE
      end
    else if isNT nodeNT HandleNT then
      match args with
      | [ret; f; ts; eid; id; p] =>
          OPTION_BIND (conv_Ret ret) (fun r' =>
          OPTION_BIND r' (fun r'' =>
          OPTION_BIND (conv_ident f) (fun fname =>
          OPTION_BIND (conv_ArgList ts) (fun args =>
          OPTION_BIND (conv_ident eid) (fun ename =>
          OPTION_BIND (conv_ident id) (fun evar =>
          OPTION_BIND (conv_Prog p) (fun prog =>
          SOME (add_locs_annot nd
                  (Call (SOME (r'', SOME (ename, (evar, prog)))) fname args)))))))))
      | _ => NONE
      end
    else if isNT nodeNT CallNT then
      match args with
      | [r; e; args] =>
          OPTION_BIND (conv_Ret r) (fun r' =>
          OPTION_BIND (conv_ident e) (fun e' =>
          OPTION_BIND (conv_ArgList args) (fun args' =>
          if is_add_with_carry e' then
            match r' with
            | SOME (SOME (_, vn)) => SOME (add_locs_annot nd (Primitive vn AddCarry args'))
            | _ => NONE
            end
          else
            SOME (add_locs_annot nd (Call (OPTION_MAP (fun x => (x, NONE)) r') e' args')))))
      | _ => NONE
      end
    else if isNT nodeNT ProgNT then
      match args with
      | t :: ts =>
          if negb (NULL ts)
          then FOLDR (fun t' p => OPTION_MAP2 Seq t' p) (conv_Prog (LAST ts))
                 (MAP conv_Prog (t :: butlast ts))
          else conv_Prog t
      | _ => NONE
      end
    else OPTION_MAP (add_locs_annot nd) (conv_NonRecStmt (Nd nodeNT args))) /\
  (forall l, @conv_Prog a (Lf l) = OPTION_MAP (add_locs_annot (Lf l)) (conv_NonRecStmt (Lf l))).
Proof.
  split; [|reflexivity].
  intros nodeNT args; cbn [conv_Prog].
  repeat match goal with |- (if ?b then _ else _) = (if ?b then _ else _) => destruct b; [reflexivity|] end.
  destruct (isNT nodeNT ProgNT); [|reflexivity].
  destruct args as [|t ts]; [reflexivity|].
  destruct (NULL ts) eqn:hn; [reflexivity|]; cbn [negb].
  destruct ts as [|t' ts]; [discriminate|].
  unfold conv_ProgNT_seq; rewrite LAST_MAP, butlast_MAP.
  reflexivity.
Qed.

(** ** Declarations *)

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_inline_def" *)
Definition conv_inline {B L} (tree : parsetree token B L) : option bool :=
  match OPTION_BIND (destLf tree) destTOK with
  | SOME (KeywordT InlineK) => SOME true
  | SOME NoinlineT => SOME false
  | _ => NONE
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_export_def" *)
Definition conv_export {B L} (tree : parsetree token B L) : option bool :=
  match OPTION_BIND (destLf tree) destTOK with
  | SOME (KeywordT ExportK) => SOME true
  | SOME StaticT => SOME false
  | _ => NONE
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_FieldNameList_def" *)
Definition conv_FieldNameList {L} (tree : parsetree token pancakeNT L) : option (list (mlstring * shape)) :=
  match argsNT tree FieldNameListNT with
  | SOME args => conv_params args
  | _ => NONE
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_StructName_def" *)
Definition conv_StructName (t : ptree) : option (mlstring * list (mlstring * shape)) :=
  match t with
  | Nd nodeNT args =>
    if isNT nodeNT StructNameNT then
      match args with
      | [id; flds] =>
          OPTION_BIND (conv_ident id) (fun nm =>
          OPTION_BIND (conv_FieldNameList flds) (fun flds' => SOME (nm, flds')))
      | _ => NONE
      end
    else NONE
  | _ => NONE
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_TopDec_def" *)
Definition conv_TopDec {a} (tree : ptree) : option (decl a) :=
  match argsNT tree FunNT with
  | SOME [i; e; sh; n; ps; c] =>
      match argsNT ps ParamListNT with
      | SOME args =>
          OPTION_BIND (conv_params args) (fun ps' =>
          OPTION_BIND (conv_Prog c) (fun body =>
          OPTION_BIND (conv_ident n) (fun n' =>
          OPTION_BIND (conv_inline i) (fun i' =>
          OPTION_BIND (conv_export e) (fun e' =>
          OPTION_BIND (conv_Shape sh) (fun sh' =>
          SOME (Function {| name := n'; inline := i'; export := e'; params := ps';
                            body := body; fun_decl_return := sh' |})))))))
      | _ => NONE
      end
  | _ =>
      match conv_GlobalDec tree with
      | SOME (sh, (v, e)) => SOME (Decl sh v e)
      | _ =>
          match conv_StructName tree with
          | SOME (nm, flds) => SOME (Name nm flds)
          | _ =>
              match conv_ExnDec tree with
              | SOME (eid, sh) => SOME (ExnDecl eid sh)
              | NONE => NONE
              end
          end
      end
  end.

Fixpoint conv_TopDecList {a} (tree : ptree) : option (list (decl a)) :=
  match tree with
  | Nd nodeNT args =>
      if decide (FST nodeNT = inl TopDecListNT) then
        match args with
        | [] => SOME []
        | [f; tree'] =>
            match dest_annot_tok f with
            | NONE =>
                match conv_TopDec f with
                | SOME f =>
                    match conv_TopDecList tree' with
                    | NONE => NONE
                    | SOME fs => SOME (f :: fs)
                    end
                | NONE => NONE
                end
            | SOME _ => conv_TopDecList tree'
            end
        | _ => NONE
        end
      else NONE
  | Lf _ => NONE
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "conv_TopDecList_def" *)
Theorem conv_TopDecList_def {a} : forall tree,
  @conv_TopDecList a tree =
  match argsNT tree TopDecListNT with
  | SOME [] => SOME []
  | SOME [f; tree'] =>
      match dest_annot_tok f with
      | NONE =>
          match conv_TopDec f with
          | SOME f =>
              match conv_TopDecList tree' with
              | NONE => NONE
              | SOME fs => SOME (f :: fs)
              end
          | NONE => NONE
          end
      | SOME _ => conv_TopDecList tree'
      end
  | _ => NONE
  end.
Proof.
  intros [|nodeNT args]; [reflexivity|]; cbn [conv_TopDecList argsNT].
  destruct (decide _); reflexivity.
Qed.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "parse_to_ast_def" *)
Definition parse_to_ast {a} (s : string) : option (prog a) :=
  match parse_statement (pancake_lex s) with
  | SOME e => conv_Prog e
  | _ => NONE
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "collect_globals_def" *)
Fixpoint collect_globals {a} (l : list (decl a)) : mlmap.map mlstring unit :=
  match l with
  | [] => mlmap.empty mlstring.compare
  | d :: ds =>
      match d with
      | Decl _ v _ => mlmap.insert (collect_globals ds) v tt
      | _ => collect_globals ds
      end
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "localise_exp_def" *)
Fixpoint localise_exp {a V} (ls : mlmap.map mlstring V) (e : exp a) {struct e} : exp a :=
  match e with
  | Var varkind varname =>
      match mlmap.lookup ls varname with
      | NONE => Var varkind varname
      | SOME _ => Var Local varname
      end
  | RStruct exps => RStruct (MAP (localise_exp ls) exps)
  | RField index exp => RField index (localise_exp ls exp)
  | NStruct nm flds => NStruct nm (MAP (fun '(fld, e) => (fld, localise_exp ls e)) flds)
  | NField fld exp => NField fld (localise_exp ls exp)
  | Load shape exp => Load shape (localise_exp ls exp)
  | LoadByte exp => LoadByte (localise_exp ls exp)
  | Op binop exps => Op binop (MAP (localise_exp ls) exps)
  | Panop panop exps => Panop panop (MAP (localise_exp ls) exps)
  | Cmp cmp exp1 exp2 => Cmp cmp (localise_exp ls exp1) (localise_exp ls exp2)
  | Shift shift exp1 exp2 => Shift shift (localise_exp ls exp1) (localise_exp ls exp2)
  | e => e
  end.

(** HOL's [localise_exps] (defined mutually with [localise_exp]). *)
Definition localise_exps {a V} (ls : mlmap.map mlstring V) (es : list (exp a)) : list (exp a) :=
  MAP (localise_exp ls) es.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "localise_prog_def" *)
Fixpoint localise_prog {a} (ls : mlmap.map mlstring unit) (p : prog a) {struct p} : prog a :=
  match p with
  | Dec varname shape exp prog =>
      Dec varname shape (localise_exp ls exp) (localise_prog (mlmap.insert ls varname tt) prog)
  | Assign varkind varname exp =>
      Assign (match mlmap.lookup ls varname with NONE => varkind | SOME _ => Local end)
        varname (localise_exp ls exp)
  | Primitive varname pop exps => Primitive varname pop (MAP (localise_exp ls) exps)
  | Store exp1 exp2 => Store (localise_exp ls exp1) (localise_exp ls exp2)
  | StoreByte exp1 exp2 => StoreByte (localise_exp ls exp1) (localise_exp ls exp2)
  | Seq prog1 prog2 => Seq (localise_prog ls prog1) (localise_prog ls prog2)
  | If exp prog1 prog2 => If (localise_exp ls exp) (localise_prog ls prog1) (localise_prog ls prog2)
  | While exp prog => While (localise_exp ls exp) (localise_prog ls prog)
  | Call call name exps =>
      Call (OPTION_MAP
              (fun '(x, y) =>
                 (OPTION_MAP (fun '(varkind, varname) =>
                    ((match mlmap.lookup ls varname with NONE => varkind | SOME _ => Local end),
                     varname)) x,
                  OPTION_MAP (fun '(x, (y, z)) => (x, (y, localise_prog (mlmap.insert ls y tt) z))) y))
              call)
        name (MAP (localise_exp ls) exps)
  | DecCall varname shape fname exps prog =>
      DecCall varname shape fname (MAP (localise_exp ls) exps)
        (localise_prog (mlmap.insert ls varname tt) prog)
  | ExtCall funname exp1 exp2 exp3 exp4 =>
      ExtCall funname (localise_exp ls exp1) (localise_exp ls exp2)
        (localise_exp ls exp3) (localise_exp ls exp4)
  | Raise eid exp => Raise eid (localise_exp ls exp)
  | Return exp => Return (localise_exp ls exp)
  | ShMemLoad opsize varkind varname exp =>
      ShMemLoad opsize (match mlmap.lookup ls varname with NONE => varkind | SOME _ => Local end)
        varname (localise_exp ls exp)
  | ShMemStore opsize exp1 exp2 => ShMemStore opsize (localise_exp ls exp1) (localise_exp ls exp2)
  | p => p
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "localise_topdec_def" *)
Definition localise_topdec {a} (ls : mlmap.map mlstring unit) (d : decl a) : decl a :=
  match d with
  | Decl sh v e => Decl sh v e
  | Name nm fld => Name nm fld
  | ExnDecl nm sh => ExnDecl nm sh
  | Function fi =>
      Function {| name := name fi; inline := inline fi; export := export fi;
                  params := params fi;
                  body := localise_prog (FOLDL (fun m p => mlmap.insert m p tt) ls
                                           (MAP FST (params fi))) (body fi);
                  fun_decl_return := fun_decl_return fi |}
  end.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "localise_topdecs_def" *)
Definition localise_topdecs {a} (decs : list (decl a)) : list (decl a) :=
  MAP (localise_topdec (mlmap.empty mlstring.compare)) decs.

(*! HOL "cakeml/pancake/parser/panPtreeConversionScript.sml" "parse_topdecs_to_ast_def" *)
Definition parse_topdecs_to_ast {a} (s : string) : list (decl a) + list (mlstring * locs) :=
  match safe_pancake_lex s with
  | inl toks =>
      match parse toks with
      | inl e =>
          match conv_TopDecList e with
          | SOME funs => inl (localise_topdecs funs)
          | NONE => inr [(strlit "Parse tree conversion failed", unknown_loc)]
          end
      | inr err => inr err
      end
  | inr err => inr err
  end.
