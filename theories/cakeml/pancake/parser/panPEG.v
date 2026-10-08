(** * Pancake [panPEG]: the Pancake grammar as a PEG

    Port of [cakeml/pancake/parser/panPEGScript.sml].

    The grammar's semantic values are parse-tree lists
    ([list (parsetree token pancakeNT locs)]) and its errors HOL strings.
    [rules] is HOL's [FEMPTY |++ [...]] ([FUPDATE_LIST] over a
    function-backed finite map).

    HOL proves the grammar well-formed ([PEG_wellformed]) by rewriting; here
    the proof runs the computable sufficient check [wfG_check] of [peg.v].

    [parse_statement] and [parse] call [peg_exec] in HOL, which is not
    executable in Rocq (see [pegexec.v]).  Here they call the executable
    interpreter [pancake_exec] (= [coreloop_acc] with the termination proof
    obtained from [PEG_wellformed]), and HOL's definitions are the tagged
    theorems [parse_statement_def]/[parse_def], proved for every input.

    Not ported: the ML-generated rewrite lists ([FDOM_pancake_peg],
    [pancake_peg_applied], [pancake_exec_thm], [pancake_wfpeg_thm],
    [pancake_wfpeg_FunNT_thm] and the [peg0_]/[peg1_] nonterminal
    lemmas), which are proof infrastructure for the HOL proof of
    [PEG_wellformed]. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.HOL.examples.formal_languages.context_free Require Import location grammar peg pegexec.
From Galette.cakeml.pancake.parser Require Import panLexer.
Open Scope N_scope.
Open Scope hol_string_scope.

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "pancakeNT" *)
Inductive pancakeNT : Type :=
  TopDecListNT | StructNameNT | FieldNameListNT
| FunNT | ProgNT | BlockNT | StmtNT | ExpNT
| DecNT | GlobalDecNT | AssignNT | StoreNT | StoreByteNT | Store32NT
| IfNT | WhileNT | CallNT | RetNT | HandleNT
| ExtCallNT | ThrowNT | ReturnNT
| DecCallNT | RetCallNT
| ArgListNT
| ParamListNT
| EBoolAndNT | EEqNT | ECmpNT
| ELoadNT | ELoadByteNT | ELoad32NT
| EXorNT | EOrNT | EAndNT
| EShiftNT | EAddNT | EMulNT | ENotNT | EFieldNT | EBaseNT
| RawStructNT | NmdStructNT | NmdFieldListNT | NmdFieldNT
| ShapedIdentNT | ShapeNT | ShapeCombNT
| EqOpsNT | CmpOpsNT | ShiftOpsNT | AddOpsNT | MulOpsNT
| SharedLoadNT | SharedLoadByteNT | SharedLoad16NT | SharedLoad32NT
| SharedStoreNT | SharedStoreByteNT | SharedStore16NT | SharedStore32NT
| ExnDecNT.

#[global] Instance pancakeNT_eq_dec : EqDecision pancakeNT.
Proof. intros x y; unfold Decision; decide equality. Defined.

(** The parse trees and PEG symbols of the Pancake grammar. *)
Abbreviation ptree := (parsetree token pancakeNT locs).
Abbreviation pansym := (pegsym token pancakeNT (list ptree) string).

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "mknt_def" *)
Definition mknt {A C E} (ntsym : pancakeNT) : pegsym A pancakeNT C E := nt (inl ntsym) I.

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "mkleaf_def" *)
Definition mkleaf {A B L} (t : A * L) : list (parsetree A B L) := [Lf (TOK (FST t), SND t)].

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "mknode_def" *)
Definition mknode {A B} (x : B) (ts : list (parsetree A B locs))
    : parsetree A B locs :=
  Nd (inl x, ptree_list_loc ts) ts.

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "mksubtree_def" *)
Definition mksubtree {A B} (x : B) (ts : list (parsetree A B locs))
    : list (parsetree A B locs) :=
  [mknode x ts].

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "consume_tok_def" *)
Definition consume_tok {B C E} (t : token) : pegsym token B (list C) E :=
  tok (fun x => bool_decide (t = x)) (fun t => []).

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "keep_tok_def" *)
Definition keep_tok {A B C E} `{EqDecision A} (t : A)
    : pegsym A B (list (parsetree A C locs)) E :=
  tok (fun x => bool_decide (t = x)) mkleaf.

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "consume_kw_def" *)
Definition consume_kw {B C E} (k : keyword) : pegsym token B (list C) E :=
  consume_tok (KeywordT k).

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "keep_kw_def" *)
Definition keep_kw {B C E} (k : keyword) : pegsym token B (list (parsetree token C locs)) E :=
  keep_tok (KeywordT k).

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "keep_ident_def" *)
Definition keep_ident {B C E} : pegsym token B (list (parsetree token C locs)) E :=
  tok (fun t => match t with IdentT _ => true | _ => false end) mkleaf.

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "keep_annot_def" *)
Definition keep_annot {B C E} : pegsym token B (list (parsetree token C locs)) E :=
  tok (fun t => match t with AnnotCommentT _ => true | _ => false end) mkleaf.

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "keep_ffi_ident_def" *)
Definition keep_ffi_ident {B C E} : pegsym token B (list (parsetree token C locs)) E :=
  tok (fun t => match t with ForeignIdent _ => true | _ => false end) mkleaf.

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "keep_int_def" *)
Definition keep_int {B C E} : pegsym token B (list (parsetree token C locs)) E :=
  tok (fun t => match t with IntT _ => true | _ => false end) mkleaf.

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "keep_nat_def" *)
Definition keep_nat {B C E} : pegsym token B (list (parsetree token C locs)) E :=
  tok (fun t => match t with IntT n => if (n >=? 0)%Z then true else false | _ => false end) mkleaf.

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "extract_sum_def" *)
Definition extract_sum {X} (s : X + X) : X := match s with inl x => x | inr x => x end.

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "choicel_def" *)
Fixpoint choicel {A B X E} (l : list (pegsym A B (list X) E)) : pegsym A B (list X) E :=
  match l with
  | [] => not (empty []) []
  | h :: t => choice h (choicel t) extract_sum
  end.

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "pegf_def" *)
Definition pegf {A B X E} (s : pegsym A B (list X) E) (f : list X -> list X)
    : pegsym A B (list X) E :=
  seq s (empty []) (fun l1 l2 => f l1).

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "seql_def" *)
Definition seql {A B X E} (l : list (pegsym A B (list X) E)) (f : list X -> list X)
    : pegsym A B (list X) E :=
  pegf (FOLDR (fun p acc => seq p acc (fun x y => x ++ y)) (empty []) l) f.

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "try_def" *)
Definition try {A B X E} (s : pegsym A B (list X) E) : pegsym A B (list X) E :=
  choicel [s; empty []].

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "try_default_def" *)
Definition try_default {A B T NT E} (s : pegsym A B (list (parsetree T NT locs)) E) (t : T)
    : pegsym A B (list (parsetree T NT locs)) E :=
  choicel [s; empty (mkleaf (t, unknown_loc))].

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "try_ProgNT_def" *)
Definition try_ProgNT {E} : pegsym token pancakeNT (list ptree) E :=
  choicel [
    seql [consume_tok RCurT; empty (mkleaf (KeywordT SkipK, unknown_loc))] (mksubtree ProgNT);
    mknt ProgNT
  ].

(** The rules of [pancake_peg], one definition per nonterminal (HOL writes
    them inline in the argument of [|++]). *)

Definition rule_TopDecListNT : pansym :=
  choicel [not (any (K (mksubtree TopDecListNT []))) (mksubtree TopDecListNT []);
    seql [mknt FunNT; mknt TopDecListNT] (mksubtree TopDecListNT);
    seql [mknt GlobalDecNT; mknt TopDecListNT] (mksubtree TopDecListNT);
    seql [mknt ExnDecNT; mknt TopDecListNT] (mksubtree TopDecListNT);
    seql [mknt StructNameNT; mknt TopDecListNT] (mksubtree TopDecListNT);
    seql [keep_annot; mknt TopDecListNT] (mksubtree TopDecListNT)].

Definition rule_StructNameNT : pansym :=
  seql [consume_kw NamedK;
    keep_ident;
    consume_tok LCurT;
    mknt FieldNameListNT;
    consume_tok RCurT]
    (mksubtree StructNameNT).

Definition rule_FieldNameListNT : pansym :=
  seql [mknt ShapedIdentNT;
    rpt (seql [consume_tok CommaT;
    mknt ShapedIdentNT] I)
    (fun l => FLAT l)]
    (mksubtree FieldNameListNT).

Definition rule_FunNT : pansym :=
  seql [try_default (keep_kw InlineK) NoinlineT;
    try_default (keep_kw ExportK) StaticT;
    consume_kw FunK;
    mknt ShapedIdentNT;
    consume_tok LParT;
    choicel
    [mknt ParamListNT;
    empty (mksubtree ParamListNT [])
    ];
    consume_tok RParT;
    consume_tok LCurT;
    try_ProgNT]
    (mksubtree FunNT).

Definition rule_ParamListNT : pansym :=
  seql [mknt ShapedIdentNT;
    rpt (seql [consume_tok CommaT;
    mknt ShapedIdentNT] I)
    (fun l => FLAT l)]
    (mksubtree ParamListNT).

Definition rule_ProgNT : pansym :=
  choicel [seql [mknt BlockNT; mknt ProgNT] (mksubtree ProgNT);
    seql [mknt DecCallNT; try_ProgNT] (mksubtree DecCallNT);
    seql [mknt DecNT; try_ProgNT] (mksubtree DecNT);
    seql [keep_annot; mknt ProgNT] (mksubtree ProgNT);
    seql [mknt StmtNT; consume_tok SemiT; mknt ProgNT] (mksubtree ProgNT);
    consume_tok RCurT
    ].

Definition rule_BlockNT : pansym :=
  choicel [mknt HandleNT;
    mknt IfNT;
    mknt WhileNT].

Definition rule_StmtNT : pansym :=
  choicel [keep_kw SkipK;
    mknt CallNT;
    mknt AssignNT; mknt StoreNT;
    mknt StoreByteNT;
    mknt Store32NT;
    mknt SharedLoadByteNT;
    mknt SharedLoad16NT;
    mknt SharedLoad32NT;
    mknt SharedLoadNT;
    mknt SharedStoreByteNT;
    mknt SharedStore16NT;
    mknt SharedStore32NT;
    mknt SharedStoreNT;
    keep_kw BrK; keep_kw ContK;
    mknt ExtCallNT;
    mknt ThrowNT; mknt RetCallNT; mknt ReturnNT;
    keep_kw TicK;
    seql [consume_tok LCurT; try_ProgNT] I
    ].

Definition rule_DecCallNT : pansym :=
  seql [consume_kw VarK; mknt ShapedIdentNT; consume_tok AssignT;
    keep_ident;
    consume_tok LParT; try (mknt ArgListNT);
    consume_tok RParT;consume_tok SemiT]
    (mksubtree DecCallNT).

Definition rule_DecNT : pansym :=
  seql [consume_kw VarK; mknt ShapedIdentNT;
    consume_tok AssignT; mknt ExpNT;
    consume_tok SemiT]
    (mksubtree DecNT).

Definition rule_GlobalDecNT : pansym :=
  seql [consume_kw VarK; mknt ShapedIdentNT;
    consume_tok AssignT; mknt ExpNT;
    consume_tok SemiT]
    (mksubtree GlobalDecNT).

Definition rule_ExnDecNT : pansym :=
  seql [consume_kw ExceptionK;
    keep_ident;
    consume_tok ColonT;
    mknt ShapeNT;
    consume_tok SemiT]
    (mksubtree ExnDecNT).

Definition rule_AssignNT : pansym :=
  seql [keep_ident; consume_tok AssignT;
    mknt ExpNT] (mksubtree AssignNT).

Definition rule_StoreNT : pansym :=
  seql [consume_kw StK; mknt ExpNT;
    consume_tok CommaT; mknt ExpNT]
    (mksubtree StoreNT).

Definition rule_StoreByteNT : pansym :=
  seql [consume_kw St8K; mknt ExpNT;
    consume_tok CommaT; mknt ExpNT]
    (mksubtree StoreByteNT).

Definition rule_Store32NT : pansym :=
  seql [consume_kw St32K; mknt ExpNT;
    consume_tok CommaT; mknt ExpNT]
    (mksubtree Store32NT).

Definition rule_IfNT : pansym :=
  seql [consume_kw IfK; mknt ExpNT; consume_tok LCurT;
    try_ProgNT;
    try_default (seql [consume_kw ElseK; consume_tok LCurT;
    try_ProgNT] I) (KeywordT SkipK)]
    (mksubtree IfNT).

Definition rule_WhileNT : pansym :=
  seql [consume_kw WhileK; mknt ExpNT;
    consume_tok LCurT; try_ProgNT] (mksubtree WhileNT).

Definition rule_CallNT : pansym :=
  seql [try_default (choicel [keep_kw RetK; mknt RetNT]) NotT;
    keep_ident;
    consume_tok LParT; try_default (mknt ArgListNT) NotT;
    consume_tok RParT]
    (mksubtree CallNT).

Definition rule_RetNT : pansym :=
  seql [keep_ident; consume_tok AssignT]
    (mksubtree RetNT).

Definition rule_HandleNT : pansym :=
  seql [consume_kw TryK;
    try_default (mknt RetNT) NotT;
    keep_ident;
    consume_tok LParT; try_default (mknt ArgListNT) NotT;
    consume_tok RParT;
    consume_kw CatchK;
    keep_ident;
    consume_tok ArrowT;
    keep_ident;
    consume_tok LCurT; try_ProgNT]
    (mksubtree HandleNT).

Definition rule_ExtCallNT : pansym :=
  seql [keep_ffi_ident;
    consume_tok LParT; mknt ExpNT;
    consume_tok CommaT; mknt ExpNT;
    consume_tok CommaT; mknt ExpNT;
    consume_tok CommaT; mknt ExpNT;
    consume_tok RParT]
    (mksubtree ExtCallNT).

Definition rule_ThrowNT : pansym :=
  seql [consume_kw ThrowK; keep_ident; mknt ExpNT]
    (mksubtree ThrowNT).

Definition rule_RetCallNT : pansym :=
  seql [consume_kw RetK;
    keep_ident;
    consume_tok LParT; try (mknt ArgListNT);
    consume_tok RParT]
    (mksubtree RetCallNT).

Definition rule_ReturnNT : pansym :=
  seql [consume_kw RetK; mknt ExpNT]
    (mksubtree ReturnNT).

Definition rule_ArgListNT : pansym :=
  seql [mknt ExpNT;
    rpt (seql [consume_tok CommaT;
    mknt ExpNT] I)
    (fun l => FLAT l)]
    (mksubtree ArgListNT).

Definition rule_ExpNT : pansym :=
  seql [mknt EBoolAndNT;
    rpt (seql [consume_tok BoolOrT; mknt EBoolAndNT] I)
    (fun l => FLAT l)]
    (mksubtree ExpNT).

Definition rule_EBoolAndNT : pansym :=
  seql [mknt EEqNT;
    rpt (seql [consume_tok BoolAndT; mknt EEqNT] I)
    (fun l => FLAT l)]
    (mksubtree EBoolAndNT).

Definition rule_EEqNT : pansym :=
  seql [mknt ECmpNT;
    try (seql [mknt EqOpsNT; mknt ECmpNT] I)]
    (mksubtree EEqNT).

Definition rule_ECmpNT : pansym :=
  seql [mknt ELoadNT;
    try (seql [mknt CmpOpsNT; mknt ELoadNT] I)]
    (mksubtree ECmpNT).

Definition rule_ELoadNT : pansym :=
  choicel [seql [consume_kw LdsK; mknt ShapeNT; mknt ELoadByteNT]
    (mksubtree ELoadNT);
    mknt ELoadByteNT].

Definition rule_ELoadByteNT : pansym :=
  choicel [seql [consume_kw Ld8K; mknt ELoad32NT]
    (mksubtree ELoadByteNT);
    mknt ELoad32NT].

Definition rule_ELoad32NT : pansym :=
  choicel [seql [consume_kw Ld32K; mknt EOrNT]
    (mksubtree ELoad32NT);
    mknt EOrNT].

Definition rule_EOrNT : pansym :=
  seql [mknt EXorNT;
    rpt (seql [keep_tok OrT; mknt EXorNT] I)
    (fun l => FLAT l)]
    (mksubtree EOrNT).

Definition rule_EXorNT : pansym :=
  seql [mknt EAndNT;
    rpt (seql [keep_tok XorT; mknt EAndNT] I)
    (fun l => FLAT l)]
    (mksubtree EXorNT).

Definition rule_EAndNT : pansym :=
  seql [mknt EShiftNT;
    rpt (seql [keep_tok AndT; mknt EShiftNT] I)
    (fun l => FLAT l)]
    (mksubtree EAndNT).

Definition rule_EShiftNT : pansym :=
  seql [mknt EAddNT;
    rpt (seql [mknt ShiftOpsNT; mknt EAddNT] I)
    (fun l => FLAT l)]
    (mksubtree EShiftNT).

Definition rule_EAddNT : pansym :=
  seql [mknt EMulNT;
    rpt (seql [mknt AddOpsNT; mknt EMulNT] I)
    (fun l => FLAT l)]
    (mksubtree EAddNT).

Definition rule_EMulNT : pansym :=
  seql [mknt ENotNT;
    rpt (seql [mknt MulOpsNT; mknt ENotNT] I) (fun l => FLAT l)]
    (mksubtree EMulNT).

Definition rule_ENotNT : pansym :=
  seql [try (keep_tok NotT); mknt EFieldNT]
    (mksubtree ENotNT).

Definition rule_EFieldNT : pansym :=
  seql [mknt EBaseNT;
    rpt (seql [consume_tok DotT;
    choicel [keep_nat; keep_ident]
    ] I)
    (fun l => FLAT l)]
    (mksubtree EFieldNT).

Definition rule_EBaseNT : pansym :=
  choicel [seql [consume_tok LParT;
    mknt ExpNT;
    consume_tok RParT] I;
    keep_kw TrueK; keep_kw FalseK;
    mknt RawStructNT; mknt NmdStructNT;
    keep_kw BaseK; keep_kw BiwK; keep_kw TopK;
    keep_int; keep_ident
    ].

Definition rule_RawStructNT : pansym :=
  seql [consume_tok LessT; mknt ArgListNT;
    consume_tok GreaterT]
    (mksubtree RawStructNT).

Definition rule_NmdStructNT : pansym :=
  seql [keep_ident; consume_tok LessT; mknt NmdFieldListNT;
    consume_tok GreaterT]
    (mksubtree NmdStructNT).

Definition rule_NmdFieldListNT : pansym :=
  seql [mknt NmdFieldNT;
    rpt (seql [consume_tok CommaT;
    mknt NmdFieldNT] I)
    (fun l => FLAT l)]
    (mksubtree NmdFieldListNT).

Definition rule_NmdFieldNT : pansym :=
  seql [keep_ident;
    consume_tok AssignT;
    mknt ExpNT]
    (mksubtree NmdFieldNT).

Definition rule_ShapedIdentNT : pansym :=
  choicel [seql [mknt ShapeNT;
    keep_ident] I;
    seql [empty (mkleaf (DefaultShT, unknown_loc));
    keep_ident] I
    ].

Definition rule_ShapeNT : pansym :=
  choicel [keep_int;
    seql [consume_tok LCurT;
    mknt ShapeCombNT;
    consume_tok RCurT] I;
    keep_ident
    ].

Definition rule_ShapeCombNT : pansym :=
  seql [mknt ShapeNT;
    rpt (seq (consume_tok CommaT)
    (mknt ShapeNT) (C K)) (fun l => FLAT l)]
    (mksubtree ShapeCombNT).

Definition rule_EqOpsNT : pansym :=
  choicel [keep_tok EqT; keep_tok NeqT].

Definition rule_CmpOpsNT : pansym :=
  choicel [keep_tok LessT; keep_tok GeqT; keep_tok GreaterT; keep_tok LeqT;
    keep_tok LowerT; keep_tok HigherT; keep_tok HigheqT; keep_tok LoweqT].

Definition rule_ShiftOpsNT : pansym :=
  choicel [keep_tok LslT; keep_tok LsrT;
    keep_tok AsrT; keep_tok RorT].

Definition rule_AddOpsNT : pansym :=
  choicel [keep_tok PlusT; keep_tok MinusT].

Definition rule_MulOpsNT : pansym :=
  keep_tok StarT.

Definition rule_SharedLoadNT : pansym :=
  seql [consume_tok NotT; consume_kw LdwK; keep_ident;
    consume_tok CommaT; mknt ExpNT]
    (mksubtree SharedLoadNT).

Definition rule_SharedLoadByteNT : pansym :=
  seql [consume_tok NotT; consume_kw Ld8K; keep_ident;
    consume_tok CommaT; mknt ExpNT]
    (mksubtree SharedLoadByteNT).

Definition rule_SharedLoad16NT : pansym :=
  seql [consume_tok NotT; consume_kw Ld16K; keep_ident;
    consume_tok CommaT; mknt ExpNT]
    (mksubtree SharedLoad16NT).

Definition rule_SharedLoad32NT : pansym :=
  seql [consume_tok NotT; consume_kw Ld32K; keep_ident;
    consume_tok CommaT; mknt ExpNT]
    (mksubtree SharedLoad32NT).

Definition rule_SharedStoreNT : pansym :=
  seql [consume_tok NotT; consume_kw StwK; mknt ExpNT;
    consume_tok CommaT; mknt ExpNT]
    (mksubtree SharedStoreNT).

Definition rule_SharedStoreByteNT : pansym :=
  seql [consume_tok NotT; consume_kw St8K; mknt ExpNT;
    consume_tok CommaT; mknt ExpNT]
    (mksubtree SharedStoreByteNT).

Definition rule_SharedStore16NT : pansym :=
  seql [consume_tok NotT; consume_kw St16K; mknt ExpNT;
    consume_tok CommaT; mknt ExpNT]
    (mksubtree SharedStore16NT).

Definition rule_SharedStore32NT : pansym :=
  seql [consume_tok NotT; consume_kw St32K; mknt ExpNT;
    consume_tok CommaT; mknt ExpNT]
    (mksubtree SharedStore32NT).

(** The rule list of [pancake_peg] (HOL's argument of [|++]). *)
Definition pancake_rules : list (inf pancakeNT * pansym) := [
  (inl TopDecListNT, rule_TopDecListNT);
  (inl StructNameNT, rule_StructNameNT);
  (inl FieldNameListNT, rule_FieldNameListNT);
  (inl FunNT, rule_FunNT);
  (inl ParamListNT, rule_ParamListNT);
  (inl ProgNT, rule_ProgNT);
  (inl BlockNT, rule_BlockNT);
  (inl StmtNT, rule_StmtNT);
  (inl DecCallNT, rule_DecCallNT);
  (inl DecNT, rule_DecNT);
  (inl GlobalDecNT, rule_GlobalDecNT);
  (inl ExnDecNT, rule_ExnDecNT);
  (inl AssignNT, rule_AssignNT);
  (inl StoreNT, rule_StoreNT);
  (inl StoreByteNT, rule_StoreByteNT);
  (inl Store32NT, rule_Store32NT);
  (inl IfNT, rule_IfNT);
  (inl WhileNT, rule_WhileNT);
  (inl CallNT, rule_CallNT);
  (inl RetNT, rule_RetNT);
  (inl HandleNT, rule_HandleNT);
  (inl ExtCallNT, rule_ExtCallNT);
  (inl ThrowNT, rule_ThrowNT);
  (inl RetCallNT, rule_RetCallNT);
  (inl ReturnNT, rule_ReturnNT);
  (inl ArgListNT, rule_ArgListNT);
  (inl ExpNT, rule_ExpNT);
  (inl EBoolAndNT, rule_EBoolAndNT);
  (inl EEqNT, rule_EEqNT);
  (inl ECmpNT, rule_ECmpNT);
  (inl ELoadNT, rule_ELoadNT);
  (inl ELoadByteNT, rule_ELoadByteNT);
  (inl ELoad32NT, rule_ELoad32NT);
  (inl EOrNT, rule_EOrNT);
  (inl EXorNT, rule_EXorNT);
  (inl EAndNT, rule_EAndNT);
  (inl EShiftNT, rule_EShiftNT);
  (inl EAddNT, rule_EAddNT);
  (inl EMulNT, rule_EMulNT);
  (inl ENotNT, rule_ENotNT);
  (inl EFieldNT, rule_EFieldNT);
  (inl EBaseNT, rule_EBaseNT);
  (inl RawStructNT, rule_RawStructNT);
  (inl NmdStructNT, rule_NmdStructNT);
  (inl NmdFieldListNT, rule_NmdFieldListNT);
  (inl NmdFieldNT, rule_NmdFieldNT);
  (inl ShapedIdentNT, rule_ShapedIdentNT);
  (inl ShapeNT, rule_ShapeNT);
  (inl ShapeCombNT, rule_ShapeCombNT);
  (inl EqOpsNT, rule_EqOpsNT);
  (inl CmpOpsNT, rule_CmpOpsNT);
  (inl ShiftOpsNT, rule_ShiftOpsNT);
  (inl AddOpsNT, rule_AddOpsNT);
  (inl MulOpsNT, rule_MulOpsNT);
  (inl SharedLoadNT, rule_SharedLoadNT);
  (inl SharedLoadByteNT, rule_SharedLoadByteNT);
  (inl SharedLoad16NT, rule_SharedLoad16NT);
  (inl SharedLoad32NT, rule_SharedLoad32NT);
  (inl SharedStoreNT, rule_SharedStoreNT);
  (inl SharedStoreByteNT, rule_SharedStoreByteNT);
  (inl SharedStore16NT, rule_SharedStore16NT);
  (inl SharedStore32NT, rule_SharedStore32NT)
].

(** Direct lookup of a rule (Galette): [pancake_lookup] agrees with
    [FLOOKUP pancake_peg.rules] ([pancake_lookup_eq]) and is what the
    executable parser uses. *)
Definition pancake_rule (n : pancakeNT) : pansym :=
  match n with
  | TopDecListNT => rule_TopDecListNT
  | StructNameNT => rule_StructNameNT
  | FieldNameListNT => rule_FieldNameListNT
  | FunNT => rule_FunNT
  | ParamListNT => rule_ParamListNT
  | ProgNT => rule_ProgNT
  | BlockNT => rule_BlockNT
  | StmtNT => rule_StmtNT
  | DecCallNT => rule_DecCallNT
  | DecNT => rule_DecNT
  | GlobalDecNT => rule_GlobalDecNT
  | ExnDecNT => rule_ExnDecNT
  | AssignNT => rule_AssignNT
  | StoreNT => rule_StoreNT
  | StoreByteNT => rule_StoreByteNT
  | Store32NT => rule_Store32NT
  | IfNT => rule_IfNT
  | WhileNT => rule_WhileNT
  | CallNT => rule_CallNT
  | RetNT => rule_RetNT
  | HandleNT => rule_HandleNT
  | ExtCallNT => rule_ExtCallNT
  | ThrowNT => rule_ThrowNT
  | RetCallNT => rule_RetCallNT
  | ReturnNT => rule_ReturnNT
  | ArgListNT => rule_ArgListNT
  | ExpNT => rule_ExpNT
  | EBoolAndNT => rule_EBoolAndNT
  | EEqNT => rule_EEqNT
  | ECmpNT => rule_ECmpNT
  | ELoadNT => rule_ELoadNT
  | ELoadByteNT => rule_ELoadByteNT
  | ELoad32NT => rule_ELoad32NT
  | EOrNT => rule_EOrNT
  | EXorNT => rule_EXorNT
  | EAndNT => rule_EAndNT
  | EShiftNT => rule_EShiftNT
  | EAddNT => rule_EAddNT
  | EMulNT => rule_EMulNT
  | ENotNT => rule_ENotNT
  | EFieldNT => rule_EFieldNT
  | EBaseNT => rule_EBaseNT
  | RawStructNT => rule_RawStructNT
  | NmdStructNT => rule_NmdStructNT
  | NmdFieldListNT => rule_NmdFieldListNT
  | NmdFieldNT => rule_NmdFieldNT
  | ShapedIdentNT => rule_ShapedIdentNT
  | ShapeNT => rule_ShapeNT
  | ShapeCombNT => rule_ShapeCombNT
  | EqOpsNT => rule_EqOpsNT
  | CmpOpsNT => rule_CmpOpsNT
  | ShiftOpsNT => rule_ShiftOpsNT
  | AddOpsNT => rule_AddOpsNT
  | MulOpsNT => rule_MulOpsNT
  | SharedLoadNT => rule_SharedLoadNT
  | SharedLoadByteNT => rule_SharedLoadByteNT
  | SharedLoad16NT => rule_SharedLoad16NT
  | SharedLoad32NT => rule_SharedLoad32NT
  | SharedStoreNT => rule_SharedStoreNT
  | SharedStoreByteNT => rule_SharedStoreByteNT
  | SharedStore16NT => rule_SharedStore16NT
  | SharedStore32NT => rule_SharedStore32NT
  end.

Definition pancake_lookup (n : inf pancakeNT) : option pansym :=
  match n with inl x => Some (pancake_rule x) | inr _ => None end.

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "pancake_peg_def" *)
Definition pancake_peg : peg token pancakeNT (list ptree) string := {|
  start := mknt TopDecListNT;
  anyEOF := "Didn't expect an EOF";
  tokFALSE := "Failed to see expected token";
  tokEOF := "Failed to see expected token; saw EOF instead";
  notFAIL := "Not combinator failed";
  rules := FUPDATE_LIST FEMPTY pancake_rules
|}.

(** ** Well-formedness *)

Lemma FLOOKUP_FUPDATE_LIST_range {K V} `{EqDecision K} (l : list (K * V)) fm k v :
  FLOOKUP (FUPDATE_LIST fm l) k = SOME v -> FLOOKUP fm k = SOME v \/ In v (MAP SND l).
Proof.
  revert fm; induction l as [|[a b] l IH]; intros fm h; [left; exact h|].
  destruct (IH _ h) as [h'|h']; [|right; right; exact h'].
  cbn in h'; destruct (decide (a = k)); [injection h' as ->; right; left; reflexivity|].
  left; exact h'.
Qed.

(** The nonterminals that never succeed without consuming input. *)
Definition pancake_nonnull : list (inf pancakeNT) :=
  MAP inl [StructNameNT; FieldNameListNT; FunNT; ProgNT; BlockNT; StmtNT; ExpNT;
           DecNT; GlobalDecNT; AssignNT; StoreNT; StoreByteNT; Store32NT;
           IfNT; WhileNT; CallNT; RetNT; HandleNT; ExtCallNT; ThrowNT; ReturnNT;
           DecCallNT; RetCallNT; ArgListNT; ParamListNT; EBoolAndNT; EEqNT; ECmpNT;
           ELoadNT; ELoadByteNT; ELoad32NT; EXorNT; EOrNT; EAndNT;
           EShiftNT; EAddNT; EMulNT; ENotNT; EFieldNT; EBaseNT;
           RawStructNT; NmdStructNT; NmdFieldListNT; NmdFieldNT;
           ShapedIdentNT; ShapeNT; ShapeCombNT;
           EqOpsNT; CmpOpsNT; ShiftOpsNT; AddOpsNT; MulOpsNT;
           SharedLoadNT; SharedLoadByteNT; SharedLoad16NT; SharedLoad32NT;
           SharedStoreNT; SharedStoreByteNT; SharedStore16NT; SharedStore32NT;
           ExnDecNT].

Lemma pancake_nn_ok : nn_ok pancake_peg pancake_nonnull = true.
Proof. vm_compute; reflexivity. Qed.

(** HOL's [topo_nts] followed by [ProgNT] and [TopDecListNT]: each
    nonterminal's rule calls only earlier ones before consuming input. *)
Definition pancake_wf_order : list (inf pancakeNT) :=
  MAP inl [MulOpsNT; AddOpsNT; ShiftOpsNT; CmpOpsNT; EqOpsNT; ShapeNT;
           ShapeCombNT; ShapedIdentNT; RawStructNT; NmdFieldNT; NmdFieldListNT; NmdStructNT;
           EBaseNT; EFieldNT; ENotNT; EMulNT; EAddNT; EShiftNT; EAndNT; EXorNT; EOrNT;
           ELoad32NT; ELoadByteNT; ELoadNT; ECmpNT; EEqNT; EBoolAndNT;
           ExpNT; ArgListNT; ReturnNT; ThrowNT; ExtCallNT;
           HandleNT; RetNT; RetCallNT; CallNT; WhileNT; IfNT; StoreByteNT; Store32NT;
           StoreNT; AssignNT;
           SharedLoadByteNT; SharedLoad16NT; SharedLoad32NT; SharedLoadNT;
           SharedStoreByteNT; SharedStore16NT; SharedStore32NT; SharedStoreNT; DecNT;
           DecCallNT; StmtNT; BlockNT; ParamListNT; GlobalDecNT; FunNT; FieldNameListNT;
           StructNameNT; ExnDecNT; ProgNT; TopDecListNT].

Lemma pancake_wf_order_ok : wf_order pancake_peg pancake_nonnull [] pancake_wf_order = true.
Proof. vm_compute; reflexivity. Qed.

Lemma pancake_wf_check :
  forallb (fun e => forallb (wfl pancake_nonnull pancake_wf_order) (subexprs_list e))
    (start pancake_peg :: MAP SND pancake_rules) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma pancake_rules_range k v :
  FLOOKUP (FUPDATE_LIST FEMPTY pancake_rules) k = SOME v -> In v (MAP SND pancake_rules).
Proof. intros h; apply FLOOKUP_FUPDATE_LIST_range in h as [h|h]; [discriminate|exact h]. Qed.

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "PEG_wellformed" *)
Theorem PEG_wellformed : wfG pancake_peg.
Proof.
  exact (wfG_check pancake_peg pancake_nonnull pancake_wf_order (MAP SND pancake_rules)
           pancake_nn_ok pancake_wf_order_ok pancake_rules_range pancake_wf_check).
Qed.

(** ** Parsing *)

Lemma pancake_nt_dom n : inl n IN FDOM (rules pancake_peg).
Proof. destruct n; unfold FDOM; unfold_sets; vm_compute; discriminate. Qed.

(** The executable interpreter run on a nonterminal of the Pancake grammar
    (Galette; see [pegexec.v]): it terminates on every input by
    [PEG_wellformed], and computes HOL's [peg_exec] ([pancake_exec_eq]). *)
Lemma pancake_lookup_eq : forall n, pancake_lookup n = FLOOKUP (rules pancake_peg) n.
Proof. intros [x|m]; [destruct x|]; vm_compute; reflexivity. Qed.

Definition pancake_exec (n : pancakeNT) (s : list (token * locs))
    : evalcase token pancakeNT (list ptree) string :=
  coreloop_acc pancake_lookup pancake_peg pancake_lookup_eq (EV (mknt n) s [] NONE [] done failed)
    (peg_exec_nt_Acc pancake_peg (inl n) I s PEG_wellformed (pancake_nt_dom n)).

Lemma pancake_exec_eq n s :
  pancake_exec n s = peg_exec pancake_peg (mknt n) s [] NONE [] done failed.
Proof. apply coreloop_acc_run. Qed.

Definition parse_statement (s : list (token * locs)) : option ptree :=
  match pancake_exec ProgNT s with
  | Result (Success [] [e] _) => SOME e
  | _ => NONE
  end.

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "parse_statement_def" *)
Theorem parse_statement_def : forall s,
  parse_statement s =
  match peg_exec pancake_peg (mknt ProgNT) s [] NONE [] done failed with
  | Result (Success [] [e] _) => SOME e
  | _ => NONE
  end.
Proof. intros s; unfold parse_statement; rewrite pancake_exec_eq; reflexivity. Qed.

Definition parse (s : list (token * locs)) : ptree + list (mlstring * locs) :=
  match pancake_exec TopDecListNT s with
  | Result (Success [] [e] _) => inl e
  | Result (Success toks _ _) => inr [(strlit "Parser could not consume all tokens", unknown_loc)]
  | Result (Failure loc msg) => inr [(implode msg, loc)]
  | Looped => inr [(strlit "PEG execution looped during parsing", unknown_loc)]
  | _ => inr [(strlit "Unknown error during parsing", unknown_loc)]
  end.

(*! HOL "cakeml/pancake/parser/panPEGScript.sml" "parse_def" *)
Theorem parse_def : forall s,
  parse s =
  match peg_exec pancake_peg (mknt TopDecListNT) s [] NONE [] done failed with
  | Result (Success [] [e] _) => inl e
  | Result (Success toks _ _) => inr [(strlit "Parser could not consume all tokens", unknown_loc)]
  | Result (Failure loc msg) => inr [(implode msg, loc)]
  | Looped => inr [(strlit "PEG execution looped during parsing", unknown_loc)]
  | _ => inr [(strlit "Unknown error during parsing", unknown_loc)]
  end.
Proof. intros s; unfold parse; rewrite pancake_exec_eq; reflexivity. Qed.
