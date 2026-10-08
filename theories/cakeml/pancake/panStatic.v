(** * Pancake [panStatic]: the static checker

    Port of [cakeml/pancake/panStaticScript.sml].  The checker runs in the
    [errorLogMonad]: a [static_result] is a result-or-error together with
    the list of warnings emitted ([WarningErr] messages, printed to stderr by
    the compiler); an error stops compilation.  All message strings are
    HOL's, byte for byte (HOL's ["\n"] is the character [NL] below).

    Names: HOL's [errorLogMonad$return] is [return_] (Rocq keyword).  The
    [context] field [scope] has the name of the type [scope] and is
    [context_scope]; the [prog_return] field [last] (also a [context] field)
    is [prog_return_last]; the [func_info] field [params] (also a
    [panLang$fun_decl] field) is [func_info_params] (AGENTS.md, record field
    clashes).  The [scoped_id] constructor [Var] shadows [panLang]'s exp
    constructor, which is written [panLang.Var].  HOL [ctxt with <| f := v |>]
    is [set_f ctxt v].

    Recursion:
    - [sh_bd_from_sh] is defined by structural recursion on the struct
      context (the [Named] case either recurses on the tail of the context
      or, when the head is the searched name, uses the tail for the fields),
      with a nested [fix] on the shape; HOL's equations (stated with
      [dropWhile] and [OPT_MMAP]) are the tagged [sh_bd_from_sh_def].
    - HOL's mutual [sh_bd_has_shape]/[sh_bd_has_shape_list],
      [sh_bd_eq_shapes]/[sh_bd_eq_shapes_list], [check_shape]/[check_shapes]
      and [static_check_exp]/[static_check_exps] are single [Fixpoint]s with
      nested [fix]es for the lists, followed by the list function; the HOL
      equations of each mutual pair are the tagged [_def] theorem.  In
      [static_check_exp], the [NStruct] case checks the field expressions
      with a [fix] over the field list itself (HOL checks
      [SND (UNZIP eflds)], not a structural subterm).
    - [static_check_prog], [static_check_progs], [static_check_decls] and
      [static_check_names] are structural, as in HOL.

    HOL's [static_check_exp ctxt BytesInWordB] clause has a variable pattern
    ([BytesInWordB] is not a constructor); being the last [exp] clause, it
    only matches the remaining constructor [BytesInWord], as here.

    Galette-local helpers (untagged; from scripts not yet ported or owned by
    other files): [dropWhile], [OPT_MMAP] ([listScript]), [LLOOKUP]
    ([listScript]'s [oEL], via [miscScript]'s overload), decidable equality
    on [panLang$shape] (HOL equality), and [NL]. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.finite_maps Require Import alist.
From Galette.HOL.src.sort Require Import ternaryComparisons.
From Galette.HOL.src.string Require Import string.
From Galette.HOL.src.monad.more_monads Require errorMonad.
From Galette.HOL.src.monad.more_monads Require Import errorLogMonad.
From Galette.cakeml.basis.pure Require Import mlstring mlint mllist.
From Galette.cakeml.basis.pure Require mlmap.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.pancake Require Import panLang.
From Galette.HOL.src.list.src.list Require Import extra.
Open Scope N_scope.
Open Scope hol_string_scope.
Open Scope errorLog_scope.
#[local] Set Warnings "-register-all".

(** ** Galette-local helpers *)

(** The newline character (HOL's ["\n"]). *)
#[local] Definition NL : ascii := "010"%char.

(** HOL [LLOOKUP l n] ([listScript]'s [oEL n l]; Galette-local until ported
    there). *)
#[local] Fixpoint LLOOKUP {A} (l : list A) (n : N) : option A :=
  match l with
  | [] => None
  | x :: xs => if decide (n = 0) then Some x else LLOOKUP xs (n - 1)
  end.

(** HOL equality on [shape] (Galette-local; [panLang] has no instance). *)
Fixpoint shape_eq_dec_f (x y : shape) {struct x} : Decision (x = y).
Proof.
  refine (match x, y with
    | One, One => left eq_refl
    | Comb xs, Comb ys =>
        match (fix go (xs ys : list shape) {struct xs} : Decision (xs = ys) :=
                 match xs, ys with
                 | [], [] => left eq_refl
                 | x :: xs', y :: ys' =>
                     match shape_eq_dec_f x y with
                     | left e1 => match go xs' ys' with left e2 => left _ | right n => right _ end
                     | right n => right _
                     end
                 | _, _ => right _
                 end) xs ys with
        | left e => left _
        | right n => right _
        end
    | Named a, Named b => match decide (a = b) with left e => left _ | right n => right _ end
    | _, _ => right _
    end); try congruence.
Defined.

#[local] Instance shape_eq_dec : EqDecision shape := shape_eq_dec_f.

(** ** Types *)

(*! HOL "cakeml/pancake/panStaticScript.sml" "staterr" *)
Inductive staterr : Type :=
| ScopeErr : mlstring -> staterr
| WarningErr : mlstring -> staterr
| GenErr : mlstring -> staterr
| ShapeErr : mlstring -> staterr.

#[global] Instance staterr_eq_dec : EqDecision staterr.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

(*! HOL "cakeml/pancake/panStaticScript.sml" "static_result" *)
Definition static_result (A : Type) : Type := M A staterr staterr.

(*! HOL "cakeml/pancake/panStaticScript.sml" "based" *)
Inductive based : Type := Based | NotBased | Trusted | NotTrusted.

#[global] Instance based_eq_dec : EqDecision based.
Proof. intros x y; unfold Decision; decide equality. Defined.

(*! HOL "cakeml/pancake/panStaticScript.sml" "shaped_based" *)
Inductive shaped_based : Type :=
| WordB : based -> shaped_based
| StructB : list shaped_based -> shaped_based
| NamedB : stcname -> list (fldname * shaped_based) -> shaped_based.

#[global] Instance shaped_based_inhabited : Inhabited shaped_based := WordB Based.

Fixpoint shaped_based_eq_dec_f (x y : shaped_based) {struct x} : Decision (x = y).
Proof.
  refine (match x, y with
    | WordB b, WordB b' => match decide (b = b') with left e => left _ | right n => right _ end
    | StructB xs, StructB ys =>
        match (fix go (xs ys : list shaped_based) {struct xs} : Decision (xs = ys) :=
                 match xs, ys with
                 | [], [] => left eq_refl
                 | x :: xs', y :: ys' =>
                     match shaped_based_eq_dec_f x y with
                     | left e1 => match go xs' ys' with left e2 => left _ | right n => right _ end
                     | right n => right _
                     end
                 | _, _ => right _
                 end) xs ys with
        | left e => left _
        | right n => right _
        end
    | NamedB a xs, NamedB b ys =>
        match decide (a = b) with
        | left e0 =>
            match (fix go (xs ys : list (fldname * shaped_based)) {struct xs}
                     : Decision (xs = ys) :=
                     match xs, ys with
                     | [], [] => left eq_refl
                     | (k, x) :: xs', (k', y) :: ys' =>
                         match decide (k = k') with
                         | left ek =>
                             match shaped_based_eq_dec_f x y with
                             | left e1 =>
                                 match go xs' ys' with left e2 => left _ | right n => right _ end
                             | right n => right _
                             end
                         | right n => right _
                         end
                     | _, _ => right _
                     end) xs ys with
            | left e => left _
            | right n => right _
            end
        | right n => right _
        end
    | _, _ => right _
    end); try congruence.
Defined.

#[global] Instance shaped_based_eq_dec : EqDecision shaped_based := shaped_based_eq_dec_f.

(*! HOL "cakeml/pancake/panStaticScript.sml" "reachable" *)
Inductive reachable : Type := IsReach | NotReach | WarnReach.

#[global] Instance reachable_eq_dec : EqDecision reachable.
Proof. intros x y; unfold Decision; decide equality. Defined.

(*! HOL "cakeml/pancake/panStaticScript.sml" "last_stmt" *)
Inductive last_stmt : Type :=
  RetLast | RaiseLast | TailLast | BreakLast | ContLast | CondExitLast | InvisLast | OtherLast.

#[global] Instance last_stmt_eq_dec : EqDecision last_stmt.
Proof. intros x y; unfold Decision; decide equality. Defined.

(** HOL [func_info]; field [params] is [func_info_params] (see the
    header). *)
(*! HOL "cakeml/pancake/panStaticScript.sml" "func_info" *)
Record func_info : Type := {
  ret_shape : shape;
  func_info_params : list (varname * shape)
}.

(*! HOL "cakeml/pancake/panStaticScript.sml" "local_info" *)
Record local_info : Type := {
  vsh_bd : shaped_based
}.

#[global] Instance local_info_inhabited : Inhabited local_info :=
  {| vsh_bd := inhabitant shaped_based |}.

(*! HOL "cakeml/pancake/panStaticScript.sml" "global_info" *)
Record global_info : Type := {
  vshape : shape
}.

(*! HOL "cakeml/pancake/panStaticScript.sml" "scope" *)
Inductive scope : Type :=
| FunScope : funname -> mlstring -> scope
| DeclScope : varname -> scope
| StcScope : stcname -> fldname -> scope
| TopLevel : scope.

(** HOL [context]; field [scope] is [context_scope] (see the header). *)
(*! HOL "cakeml/pancake/panStaticScript.sml" "context" *)
Record context : Type := {
  locals : mlmap.map varname local_info;
  globals : mlmap.map varname global_info;
  funcs : mlmap.map funname func_info;
  exns : mlmap.map eid shape;
  structs : list (stcname * struct_info);
  context_scope : scope;
  in_loop : bool;
  is_reachable : reachable;
  last : last_stmt;
  loc : mlstring
}.

Definition set_locals (c : context) (v : mlmap.map varname local_info) : context :=
  {| locals := v; globals := c.(globals); funcs := c.(funcs); exns := c.(exns);
     structs := c.(structs); context_scope := c.(context_scope); in_loop := c.(in_loop);
     is_reachable := c.(is_reachable); last := c.(last); loc := c.(loc) |}.
Definition set_context_scope (c : context) (v : scope) : context :=
  {| locals := c.(locals); globals := c.(globals); funcs := c.(funcs); exns := c.(exns);
     structs := c.(structs); context_scope := v; in_loop := c.(in_loop);
     is_reachable := c.(is_reachable); last := c.(last); loc := c.(loc) |}.
Definition set_in_loop (c : context) (v : bool) : context :=
  {| locals := c.(locals); globals := c.(globals); funcs := c.(funcs); exns := c.(exns);
     structs := c.(structs); context_scope := c.(context_scope); in_loop := v;
     is_reachable := c.(is_reachable); last := c.(last); loc := c.(loc) |}.
Definition set_is_reachable (c : context) (v : reachable) : context :=
  {| locals := c.(locals); globals := c.(globals); funcs := c.(funcs); exns := c.(exns);
     structs := c.(structs); context_scope := c.(context_scope); in_loop := c.(in_loop);
     is_reachable := v; last := c.(last); loc := c.(loc) |}.
Definition set_last (c : context) (v : last_stmt) : context :=
  {| locals := c.(locals); globals := c.(globals); funcs := c.(funcs); exns := c.(exns);
     structs := c.(structs); context_scope := c.(context_scope); in_loop := c.(in_loop);
     is_reachable := c.(is_reachable); last := v; loc := c.(loc) |}.
Definition set_loc (c : context) (v : mlstring) : context :=
  {| locals := c.(locals); globals := c.(globals); funcs := c.(funcs); exns := c.(exns);
     structs := c.(structs); context_scope := c.(context_scope); in_loop := c.(in_loop);
     is_reachable := c.(is_reachable); last := c.(last); loc := v |}.

(*! HOL "cakeml/pancake/panStaticScript.sml" "exp_return" *)
Record exp_return : Type := {
  sh_bd : shaped_based
}.

(*! HOL "cakeml/pancake/panStaticScript.sml" "exps_return" *)
Record exps_return : Type := {
  sh_bds : list shaped_based
}.

(** HOL [prog_return]; field [last] is [prog_return_last] (see the
    header). *)
(*! HOL "cakeml/pancake/panStaticScript.sml" "prog_return" *)
Record prog_return : Type := {
  exits_fun : bool;
  exits_loop : bool;
  prog_return_last : last_stmt;
  var_delta : mlmap.map varname local_info;
  curr_loc : mlstring
}.

(*! HOL "cakeml/pancake/panStaticScript.sml" "scoped_id" *)
Inductive scoped_id : Type := Var | Fun | Stc.

(** ** Functions for [based] and [shaped_based] *)

(** HOL [sh_bd_from_sh] (see the header and [sh_bd_from_sh_def]). *)
Fixpoint sh_bd_from_sh (sctxt : list (stcname * struct_info)) (b : based) (sh : shape)
    {struct sctxt} : option shaped_based :=
  (fix go (sh : shape) : option shaped_based :=
     match sh with
     | One => Some (WordB b)
     | Comb shs =>
         match OPT_MMAP go shs with
         | Some sbs => Some (StructB sbs)
         | None => None
         end
     | Named nm =>
         match sctxt with
         | [] => None
         | (n, info) :: sctxt' =>
             if decide (n = nm) then
               let '(field_nms, field_shs) := UNZIP (fields info) in
               match OPT_MMAP (sh_bd_from_sh sctxt' b) field_shs with
               | Some field_sbs => Some (NamedB n (ZIP (field_nms, field_sbs)))
               | None => None
               end
             else sh_bd_from_sh sctxt' b (Named nm)
         end
     end) sh.

(*! HOL "cakeml/pancake/panStaticScript.sml" "sh_bd_from_sh_def" *)
Theorem sh_bd_from_sh_def : forall sctxt b shs nm,
  sh_bd_from_sh sctxt b One = Some (WordB b) /\
  sh_bd_from_sh sctxt b (Comb shs) =
    (match OPT_MMAP (sh_bd_from_sh sctxt b) shs with
     | Some sbs => Some (StructB sbs)
     | None => None
     end) /\
  sh_bd_from_sh sctxt b (Named nm) =
    (match dropWhile (fun '(n, i) => bool_decide (~ (n = nm))) sctxt with
     | (nm, info) :: sctxt' =>
         let '(field_nms, field_shs) := UNZIP (fields info) in
         match OPT_MMAP (sh_bd_from_sh sctxt' b) field_shs with
         | Some field_sbs => Some (NamedB nm (ZIP (field_nms, field_sbs)))
         | None => None
         end
     | _ => None
     end).
Proof.
  intros sctxt b shs nm; split; [destruct sctxt; reflexivity|split].
  - destruct sctxt as [|[n info] sctxt]; reflexivity.
  - induction sctxt as [|[n info] sctxt IH]; [reflexivity|].
    cbn [sh_bd_from_sh dropWhile].
    unfold bool_decide; destruct (decide (~ (n = nm))) as [h|h];
      destruct (decide (n = nm)) as [e|ne]; try tauto.
    all: first [exact IH | subst n; reflexivity].
Qed.

(*! HOL "cakeml/pancake/panStaticScript.sml" "sh_bd_from_bd_def" *)
Fixpoint sh_bd_from_bd (b : based) (sb : shaped_based) : shaped_based :=
  match sb with
  | WordB b' => WordB b
  | StructB sbs => StructB (MAP (sh_bd_from_bd b) sbs)
  | NamedB nm flds => NamedB nm (MAP (fun '(nm, sb) => (nm, sh_bd_from_bd b sb)) flds)
  end.

(** HOL [sh_bd_has_shape] (with the nested [sh_bd_has_shape_list]); see
    [sh_bd_has_shape_def]. *)
Fixpoint sh_bd_has_shape (sh : shape) (sb : shaped_based) {struct sh} : bool :=
  match sh, sb with
  | One, WordB b => true
  | Comb shs, StructB sbs =>
      (fix sh_bd_has_shape_list (shs : list shape) (sbs : list shaped_based) : bool :=
         match shs, sbs with
         | [], [] => true
         | sh :: shs, [] => false
         | [], sb :: sbs => false
         | sh :: shs, sb :: sbs => sh_bd_has_shape sh sb && sh_bd_has_shape_list shs sbs
         end) shs sbs
  | Named nm, NamedB nm' flds => bool_decide (nm = nm')
  | _, _ => false
  end.

Fixpoint sh_bd_has_shape_list (shs : list shape) (sbs : list shaped_based) : bool :=
  match shs, sbs with
  | [], [] => true
  | sh :: shs, [] => false
  | [], sb :: sbs => false
  | sh :: shs, sb :: sbs => sh_bd_has_shape sh sb && sh_bd_has_shape_list shs sbs
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "sh_bd_has_shape_def" *)
Theorem sh_bd_has_shape_def : forall sh sb shs sbs,
  (sh_bd_has_shape sh sb =
    match sh, sb with
    | One, WordB b => true
    | Comb shs, StructB sbs => sh_bd_has_shape_list shs sbs
    | Named nm, NamedB nm' flds => bool_decide (nm = nm')
    | _, _ => false
    end) /\
  sh_bd_has_shape_list [] [] = true /\
  sh_bd_has_shape_list (sh :: shs) [] = false /\
  sh_bd_has_shape_list [] (sb :: sbs) = false /\
  sh_bd_has_shape_list (sh :: shs) (sb :: sbs) =
    (sh_bd_has_shape sh sb && sh_bd_has_shape_list shs sbs).
Proof.
  intros sh sb shs sbs; repeat split; try reflexivity; destruct sh, sb; reflexivity.
Qed.

(** HOL [sh_bd_eq_shapes] (with the nested [sh_bd_eq_shapes_list]); see
    [sh_bd_eq_shapes_def]. *)
Fixpoint sh_bd_eq_shapes (sb sh : shaped_based) {struct sb} : bool :=
  match sb, sh with
  | WordB b, WordB b' => true
  | StructB sbs, StructB sbs' =>
      (fix sh_bd_eq_shapes_list (sbs sbs' : list shaped_based) : bool :=
         match sbs, sbs' with
         | [], [] => true
         | sb :: sbs, [] => false
         | [], sb :: sbs => false
         | sb :: sbs, sb' :: sbs' => sh_bd_eq_shapes sb sb' && sh_bd_eq_shapes_list sbs sbs'
         end) sbs sbs'
  | NamedB nm flds, NamedB nm' flds' => bool_decide (nm = nm')
  | _, _ => false
  end.

Fixpoint sh_bd_eq_shapes_list (sbs sbs' : list shaped_based) : bool :=
  match sbs, sbs' with
  | [], [] => true
  | sb :: sbs, [] => false
  | [], sb :: sbs => false
  | sb :: sbs, sb' :: sbs' => sh_bd_eq_shapes sb sb' && sh_bd_eq_shapes_list sbs sbs'
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "sh_bd_eq_shapes_def" *)
Theorem sh_bd_eq_shapes_def : forall sb sh sbs sb' sbs',
  (sh_bd_eq_shapes sb sh =
    match sb, sh with
    | WordB b, WordB b' => true
    | StructB sbs, StructB sbs' => sh_bd_eq_shapes_list sbs sbs'
    | NamedB nm flds, NamedB nm' flds' => bool_decide (nm = nm')
    | _, _ => false
    end) /\
  sh_bd_eq_shapes_list [] [] = true /\
  sh_bd_eq_shapes_list (sb :: sbs) [] = false /\
  sh_bd_eq_shapes_list [] (sb :: sbs) = false /\
  sh_bd_eq_shapes_list (sb :: sbs) (sb' :: sbs') =
    (sh_bd_eq_shapes sb sb' && sh_bd_eq_shapes_list sbs sbs').
Proof.
  intros sb sh sbs sb' sbs'; repeat split; try reflexivity; destruct sb, sh; reflexivity.
Qed.

(*! HOL "cakeml/pancake/panStaticScript.sml" "index_sh_bd_def" *)
Definition index_sh_bd (i : N) (sb : shaped_based) : option shaped_based :=
  match sb with
  | WordB b => None
  | StructB sbs => LLOOKUP sbs i
  | NamedB nm flds => None
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "field_sh_bd_def" *)
Definition field_sh_bd (fld : fldname) (sb : shaped_based) : option shaped_based :=
  match sb with
  | WordB b => None
  | StructB sbs => None
  | NamedB nm flds => ALOOKUP flds fld
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "based_merge_def" *)
Definition based_merge (x y : based) : based :=
  match x, y with
  | Based, _ => Based
  | _, Based => Based
  | NotTrusted, _ => NotTrusted
  | _, NotTrusted => NotTrusted
  | Trusted, _ => Trusted
  | _, Trusted => Trusted
  | NotBased, NotBased => NotBased
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "sh_bd_branch_def" *)
Definition sh_bd_branch (x y : shaped_based) : shaped_based :=
  if decide (x = y) then x else sh_bd_from_bd NotTrusted x.

(*! HOL "cakeml/pancake/panStaticScript.sml" "branch_loc_inf_def" *)
Definition branch_loc_inf (vctxt x y : mlmap.map varname local_info)
    : mlmap.map varname local_info :=
  let x' :=
    mlmap.mapWithKey (fun k v => {|
        vsh_bd :=
          (if negb (mlmap.member k y) then
             match mlmap.lookup vctxt k with
             | Some v' => sh_bd_branch v.(vsh_bd) v'.(vsh_bd)
             | None => sh_bd_from_bd NotTrusted v.(vsh_bd)
             end
           else v.(vsh_bd))
      |}) x in
  let y' :=
    mlmap.mapWithKey (fun k v => {|
        vsh_bd :=
          (if negb (mlmap.member k x) then
             match mlmap.lookup vctxt k with
             | Some v' => sh_bd_branch v.(vsh_bd) v'.(vsh_bd)
             | None => sh_bd_from_bd NotTrusted v.(vsh_bd)
             end
           else v.(vsh_bd))
      |}) y in
  mlmap.unionWith (fun vx vy => {|
      vsh_bd := sh_bd_branch vx.(vsh_bd) vy.(vsh_bd)
    |}) x' y'.

(*! HOL "cakeml/pancake/panStaticScript.sml" "seq_loc_inf_def" *)
Definition seq_loc_inf (x y : mlmap.map varname local_info) : mlmap.map varname local_info :=
  mlmap.union y x.

(*! HOL "cakeml/pancake/panStaticScript.sml" "sh_bd_to_str_def" *)
Fixpoint sh_bd_to_str (sb : shaped_based) : mlstring :=
  match sb with
  | WordB b => strlit "1"
  | StructB [] => strlit "{}"
  | StructB (x :: xs) =>
      concat (strlit "{" :: sh_bd_to_str x ::
              MAP (fun x => (strlit "," ^ x)%mlstring) (MAP sh_bd_to_str xs) ++
              [strlit "}"])
  | NamedB nm flds => nm
  end.

(** ** Functions for [last_stmt] and [reachable] *)

(*! HOL "cakeml/pancake/panStaticScript.sml" "last_to_str_def" *)
Definition last_to_str (l : last_stmt) : mlstring :=
  match l with
  | RetLast => strlit "return"
  | RaiseLast => strlit "raise"
  | TailLast => strlit "tail call"
  | BreakLast => strlit "break"
  | ContLast => strlit "continue"
  | CondExitLast => strlit "exiting conditional"
  | _ => strlit ""
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "next_is_reachable_def" *)
Definition next_is_reachable (r : reachable) (x : last_stmt) : reachable :=
  match r with
  | IsReach => if decide (~ (x = InvisLast \/ x = OtherLast)) then WarnReach else IsReach
  | _ => r
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "next_now_unreachable_def" *)
Definition next_now_unreachable (r r' : reachable) : bool :=
  bool_decide (r = IsReach /\ ~ (r' = IsReach)).

(*! HOL "cakeml/pancake/panStaticScript.sml" "reached_warnable_def" *)
Definition reached_warnable {a : N} (s : prog a) (ctxt : context)
    : option last_stmt * context :=
  match s with
  | Seq prog1 prog2 => (None, ctxt)
  | Tick => (None, ctxt)
  | Annot str1 str2 => (None, ctxt)
  | _ =>
      if decide (ctxt.(is_reachable) = WarnReach) then
        (Some ctxt.(last), set_is_reachable ctxt NotReach)
      else (None, ctxt)
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "branch_last_stmt_def" *)
Definition branch_last_stmt (double_ret double_loop_exit : bool) : last_stmt :=
  if double_ret || double_loop_exit then CondExitLast else OtherLast.

(*! HOL "cakeml/pancake/panStaticScript.sml" "seq_last_stmt_def" *)
Definition seq_last_stmt (x y : last_stmt) : last_stmt :=
  if decide (y = InvisLast) then x else y.

(** ** Error message helpers *)

(*! HOL "cakeml/pancake/panStaticScript.sml" "get_scope_desc_def" *)
Definition get_scope_desc (scope : scope) : mlstring :=
  match scope with
  | FunScope fname desc => concat [strlit "function "; fname; desc]
  | DeclScope vname => concat [strlit "initialisation of global variable "; vname]
  | StcScope sname fld =>
      concat [strlit "declaration of field "; fld; strlit " in named struct "; sname]
  | TopLevel => strlit "top-level declaration"
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "get_scope_msg_def" *)
Definition get_scope_msg (id_type : scoped_id) (loc id : mlstring) (scope : scope)
    : mlstring :=
  let id_desc :=
    match id_type with
    | Var => strlit "variable "
    | Fun => strlit "function "
    | Stc => strlit "struct name "
    end in
  concat [loc; id_desc; id; strlit " is not in scope in "; get_scope_desc scope; strlit [NL]].

(*! HOL "cakeml/pancake/panStaticScript.sml" "primitive_idents_def" *)
Definition primitive_idents : list mlstring := [strlit "__add_with_carry__"].

(*! HOL "cakeml/pancake/panStaticScript.sml" "add_primitive_hint_def" *)
Definition add_primitive_hint (fname msg : mlstring) : mlstring :=
  if MEM fname primitive_idents
  then concat [msg;
         strlit "  note: "; fname;
         strlit " is a built-in primitive only available in ";
         strlit ("declaration or assignment RHS positions" ++ [NL])]
  else msg.

(*! HOL "cakeml/pancake/panStaticScript.sml" "get_redec_msg_def" *)
Definition get_redec_msg (id_type : scoped_id) (loc id : mlstring) (scope : scope)
    : mlstring :=
  let id_desc :=
    match id_type with
    | Var => strlit "variable "
    | Fun => strlit "function "
    | Stc => strlit "struct name "
    end in
  concat [loc; id_desc; id; strlit " is redeclared in "; get_scope_desc scope; strlit [NL]].

(*! HOL "cakeml/pancake/panStaticScript.sml" "get_memop_msg_def" *)
Definition get_memop_msg (is_local is_load is_untrust : bool) (loc : mlstring)
    (scope : scope) : mlstring :=
  let mem_type := if is_local then strlit "local " else strlit "shared " in
  let op_type := if is_load then strlit "load " else strlit "store " in
  let issue :=
    match is_local, is_untrust with
    | false, false => strlit "is "
    | false, true => strlit "may be "
    | true, false => strlit "is not "
    | true, true => strlit "may not be "
    end in
  concat [loc; mem_type; op_type; strlit "address "; issue;
          strlit "calculated from base in "; get_scope_desc scope; strlit [NL]].

(*! HOL "cakeml/pancake/panStaticScript.sml" "get_oparg_msg_def" *)
Definition get_oparg_msg (is_exact : bool) (n_expected n_given loc op : mlstring)
    (scope : scope) : mlstring :=
  let issue :=
    if is_exact then strlit " only accepts " else strlit " requires at least " in
  concat [loc; strlit "operation "; op; issue; n_expected; strlit " operands, ";
          n_given; strlit " provided in "; get_scope_desc scope; strlit [NL]].

(*! HOL "cakeml/pancake/panStaticScript.sml" "get_unreach_msg_def" *)
Definition get_unreach_msg (loc last : mlstring) (scope : scope) : mlstring :=
  concat [loc; strlit "unreachable statement(s) after "; last; strlit " in ";
          get_scope_desc scope; strlit [NL]].

(*! HOL "cakeml/pancake/panStaticScript.sml" "get_rogue_msg_def" *)
Definition get_rogue_msg (is_break : bool) (loc : mlstring) (scope : scope) : mlstring :=
  let stmt := if is_break then strlit "break " else strlit "continue " in
  concat [loc; stmt; strlit "statement outside loop in "; get_scope_desc scope; strlit [NL]].

(*! HOL "cakeml/pancake/panStaticScript.sml" "get_non_word_msg_def" *)
Definition get_non_word_msg (desc sh_str loc : mlstring) (scope : scope) : mlstring :=
  concat [loc; desc; strlit " has shape "; sh_str; strlit " instead of a word in ";
          get_scope_desc scope; strlit [NL]].

(*! HOL "cakeml/pancake/panStaticScript.sml" "get_shape_mismatch_msg_def" *)
Definition get_shape_mismatch_msg (desc sh_str_actual sh_str_expect loc : mlstring)
    (scope : scope) : mlstring :=
  concat [loc; desc; strlit " has shape "; sh_str_actual;
          strlit " instead of declared shape "; sh_str_expect; strlit " in ";
          get_scope_desc scope; strlit [NL]].

(*! HOL "cakeml/pancake/panStaticScript.sml" "get_implementation_err_msg_def" *)
Definition get_implementation_err_msg (desc loc : mlstring) (scope : scope) : mlstring :=
  concat [loc; desc; strlit " in "; get_scope_desc scope; strlit [NL];
          strlit ("this should never happen. please report to a compiler developer" ++ [NL])].

(** ** Misc functions *)

(*! HOL "cakeml/pancake/panStaticScript.sml" "first_repeat_def" *)
Fixpoint first_repeat {A} `{EqDecision A} (xs : list A) : option A :=
  match xs with
  | x1 :: ((x2 :: xs) as t) => if decide (x1 = x2) then Some x1 else first_repeat t
  | _ => None
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "binop_to_str_def" *)
Definition binop_to_str (op : binop) : mlstring :=
  match op with
  | Add => strlit "Add"
  | Sub => strlit "Sub"
  | And => strlit "And"
  | Or => strlit "Or"
  | Xor => strlit "Xor"
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "panop_to_str_def" *)
Definition panop_to_str (op : panop) : mlstring :=
  match op with Mul => strlit "Mul" end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "primop_to_str_def" *)
Definition primop_to_str (pop : primop) : mlstring :=
  match pop with AddCarry => strlit "AddCarry" end.

(** ** Static check helpers *)

(*! HOL "cakeml/pancake/panStaticScript.sml" "check_fun_name_def" *)
Definition check_fun_name (ctxt : context) (fname : funname) : static_result func_info :=
  match mlmap.lookup ctxt.(funcs) fname with
  | None => error (ScopeErr
      (add_primitive_hint fname (get_scope_msg Fun ctxt.(loc) fname ctxt.(context_scope))))
  | Some f => return_ f
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "check_global_var_def" *)
Definition check_global_var (ctxt : context) (vname : varname) : static_result global_info :=
  match mlmap.lookup ctxt.(globals) vname with
  | None => error (ScopeErr (get_scope_msg Var ctxt.(loc) vname ctxt.(context_scope)))
  | Some v => return_ v
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "check_local_var_def" *)
Definition check_local_var (ctxt : context) (vname : varname) : static_result local_info :=
  match mlmap.lookup ctxt.(locals) vname with
  | None => error (ScopeErr (get_scope_msg Var ctxt.(loc) vname ctxt.(context_scope)))
  | Some v => return_ v
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "check_redec_var_def" *)
Definition check_redec_var (ctxt : context) (vname : varname) : static_result unit :=
  match mlmap.lookup ctxt.(locals) vname, mlmap.lookup ctxt.(globals) vname with
  | None, None => return_ tt
  | _, _ => log (WarningErr (get_redec_msg Var ctxt.(loc) vname ctxt.(context_scope)))
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "check_export_params_def" *)
Fixpoint check_export_params (loc : mlstring) (scope : scope) (l : list (varname * shape))
    : static_result unit :=
  match l with
  | [] => return_ tt
  | (vname, shape) :: ps =>
      if decide (~ (shape = One)) then
        error (ShapeErr (get_non_word_msg
          (concat [strlit "exported function parameter "; vname])
          (shape_to_str shape) loc scope))
      else check_export_params loc scope ps
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "check_operands_def" *)
Fixpoint check_operands (ctxt : context) (op_str : mlstring) (l : list shaped_based)
    : static_result based :=
  match l with
  | [] => return_ NotBased
  | sb :: sbs =>
      match sb with
      | WordB b =>
          b' <- check_operands ctxt op_str sbs ;;
          return_ (based_merge b b')
      | _ => error (ShapeErr (get_non_word_msg
          (concat [strlit "operation "; op_str; strlit " operand"])
          (sh_bd_to_str sb) ctxt.(loc) ctxt.(context_scope)))
      end
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "check_primitive_args_def" *)
Definition check_primitive_args (ctxt : context) (pop : primop) (sh_bds : list shaped_based)
    : static_result shaped_based :=
  match pop with
  | AddCarry =>
      let op_str := primop_to_str AddCarry in
      let nargs := LENGTH sh_bds in
      (if decide (~ (nargs = 3))
       then error (GenErr (get_oparg_msg true (strlit "3")
              (num_to_str nargs) ctxt.(loc) op_str ctxt.(context_scope)))
       else return_ tt) ;;
      b <- check_operands ctxt op_str sh_bds ;;
      return_ (StructB [WordB b; WordB NotBased])
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "check_func_args_def" *)
Fixpoint check_func_args (ctxt : context) (fname : funname) (params : list (varname * shape))
    (sh_bds : list shaped_based) : static_result unit :=
  match params, sh_bds with
  | (p, s) :: ps, sb :: sbs =>
      if negb (sh_bd_has_shape s sb) then
        error (ShapeErr (get_shape_mismatch_msg (concat [
            strlit "value for argument "; p;
            strlit " given to function "; fname
          ]) (sh_bd_to_str sb) (shape_to_str s) ctxt.(loc) ctxt.(context_scope)))
      else check_func_args ctxt fname ps sbs
  | (p, s) :: ps, [] => error (GenErr (concat [
        ctxt.(loc); strlit "argument "; p;
        strlit " for call to function "; fname;
        strlit " is missing in ";
        get_scope_desc ctxt.(context_scope); strlit [NL]]))
  | [], sb :: sbs => error (GenErr (concat [
        ctxt.(loc); strlit "extra arguments given to function "; fname;
        strlit " in ";
        get_scope_desc ctxt.(context_scope); strlit [NL]]))
  | [], [] => return_ tt
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "check_struct_fields_def" *)
Fixpoint check_struct_fields (ctxt : context) (sname : stcname)
    (fields : list (fldname * shape)) (fsbs : list (fldname * shaped_based))
    : static_result unit :=
  match fields, fsbs with
  | (fld, sh) :: fss, fsbs =>
      sb <-
        match FILTER (fun '(fld', sb) => bool_decide (fld = fld')) fsbs with
        | [(fld, sb)] => return_ sb
        | [] => error (ShapeErr (concat [
            ctxt.(loc); strlit "missing field "; fld;
            strlit " in named struct "; sname;
            strlit " constant in ";
            get_scope_desc ctxt.(context_scope); strlit [NL]]))
        | _ => error (ShapeErr (concat [
            ctxt.(loc); strlit "multiple values for field "; fld;
            strlit " in named struct "; sname;
            strlit " constant in ";
            get_scope_desc ctxt.(context_scope); strlit [NL]]))
        end ;;
      if negb (sh_bd_has_shape sh sb) then
        error (ShapeErr (get_shape_mismatch_msg (concat [
            strlit "value for field "; fld;
            strlit " given to named struct "; sname
          ]) (sh_bd_to_str sb) (shape_to_str sh) ctxt.(loc) ctxt.(context_scope)))
      else check_struct_fields ctxt sname fss (ADELKEY fld fsbs)
  | [], fsb :: fsbs => error (GenErr (concat [
      ctxt.(loc); strlit "unexpected field "; FST fsb;
      strlit " given to named struct "; sname;
      strlit " in ";
      get_scope_desc ctxt.(context_scope); strlit [NL]]))
  | [], [] => return_ tt
  end.

(** HOL [check_shape] (with the nested [check_shapes]); see
    [check_shape_def]. *)
Fixpoint check_shape {A} (sctxt : list (stcname * A)) (loc : mlstring) (scope : scope)
    (sh : shape) {struct sh} : static_result unit :=
  match sh with
  | One => return_ tt
  | Comb shs =>
      (fix check_shapes (shs : list shape) : static_result unit :=
         match shs with
         | [] => return_ tt
         | sh :: shs =>
             check_shape sctxt loc scope sh ;;
             check_shapes shs
         end) shs
  | Named nm =>
      match ALOOKUP sctxt nm with
      | Some flds => return_ tt
      | None => error (ScopeErr (get_scope_msg Stc loc nm scope))
      end
  end.

Fixpoint check_shapes {A} (sctxt : list (stcname * A)) (loc : mlstring) (scope : scope)
    (shs : list shape) : static_result unit :=
  match shs with
  | [] => return_ tt
  | sh :: shs =>
      check_shape sctxt loc scope sh ;;
      check_shapes sctxt loc scope shs
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "check_shape_def" *)
Theorem check_shape_def {A} : forall (sctxt : list (stcname * A)) loc scope shs nm sh,
  check_shape sctxt loc scope One = return_ tt /\
  check_shape sctxt loc scope (Comb shs) = check_shapes sctxt loc scope shs /\
  check_shape sctxt loc scope (Named nm) =
    (match ALOOKUP sctxt nm with
     | Some flds => return_ tt
     | None => error (ScopeErr (get_scope_msg Stc loc nm scope))
     end) /\
  check_shapes sctxt loc scope [] = return_ tt /\
  check_shapes sctxt loc scope (sh :: shs) =
    (check_shape sctxt loc scope sh ;;
     check_shapes sctxt loc scope shs).
Proof.
  intros sctxt loc scope shs nm sh; repeat split; try reflexivity.
  induction shs as [|x shs IH]; [reflexivity|].
  cbn [check_shape check_shapes] in *; rewrite IH; reflexivity.
Qed.

(*! HOL "cakeml/pancake/panStaticScript.sml" "check_id_shapes_def" *)
Fixpoint check_id_shapes {A} (sctxt : list (stcname * A)) (loc : mlstring)
    (scope : scope) (l : list (mlstring * shape)) : static_result unit :=
  match l with
  | [] => return_ tt
  | (id, shape) :: ids =>
      scope' <-
        match scope with
        | FunScope fname _ =>
            return_ (FunScope fname (concat [strlit " parameter "; id]))
        | StcScope sname _ =>
            return_ (StcScope sname id)
        | _ => error (GenErr (get_implementation_err_msg
            (strlit "parameter or field found in unexpected scope")
            loc scope))
        end ;;
      check_shape sctxt loc scope' shape ;;
      check_id_shapes sctxt loc scope ids
  end.

(** ** Main static checking functions *)

(** HOL [static_check_exp] (with the nested [static_check_exps]); see the
    header and [static_check_exp_def]. *)
Fixpoint static_check_exp {a : N} (ctxt : context) (e : exp a) {struct e}
    : static_result exp_return :=
  match e with
  | Const num =>
      return_ {| sh_bd := WordB NotBased |}
  | panLang.Var Local vname =>
      vinf <- check_local_var ctxt vname ;;
      return_ {| sh_bd := vinf.(vsh_bd) |}
  | panLang.Var Global vname =>
      vinf <- check_global_var ctxt vname ;;
      match sh_bd_from_sh ctxt.(structs) Trusted vinf.(vshape) with
      | Some sb => return_ {| sh_bd := sb |}
      | None => error (ScopeErr (get_implementation_err_msg
          (strlit "static analysis failed to convert in-scope shape")
          ctxt.(loc) ctxt.(context_scope)))
      end
  | RStruct exps =>
      esret <-
        (fix static_check_exps (l : list (exp a)) : static_result exps_return :=
           match l with
           | [] => return_ {| sh_bds := [] |}
           | exp :: exps =>
               eret <- static_check_exp ctxt exp ;;
               esret <- static_check_exps exps ;;
               return_ {| sh_bds := eret.(sh_bd) :: esret.(sh_bds) |}
           end) exps ;;
      return_ {| sh_bd := StructB esret.(sh_bds) |}
  | RField index exp =>
      eret <- static_check_exp ctxt exp ;;
      match index_sh_bd index eret.(sh_bd) with
      | None => error (ShapeErr (concat [
          ctxt.(loc); strlit "expression shape "; sh_bd_to_str eret.(sh_bd);
          strlit " has no field at index "; num_to_str index;
          strlit " in "; get_scope_desc ctxt.(context_scope); strlit [NL]]))
      | Some sb => return_ {| sh_bd := sb |}
      end
  | NStruct name eflds =>
      sinfo <-
        match ALOOKUP ctxt.(structs) name with
        | Some info => return_ info
        | None => error (ScopeErr (get_scope_msg Stc ctxt.(loc) name ctxt.(context_scope)))
        end ;;
      let '(field_names, field_exps) := UNZIP eflds in
      esret <-
        (fix static_check_exps (l : list (fldname * exp a)) : static_result exps_return :=
           match l with
           | [] => return_ {| sh_bds := [] |}
           | (_, exp) :: exps =>
               eret <- static_check_exp ctxt exp ;;
               esret <- static_check_exps exps ;;
               return_ {| sh_bds := eret.(sh_bd) :: esret.(sh_bds) |}
           end) eflds ;;
      let field_sbs := ZIP (field_names, esret.(sh_bds)) in
      check_struct_fields ctxt name sinfo.(fields) field_sbs ;;
      return_ {| sh_bd := NamedB name field_sbs |}
  | NField field exp =>
      eret <- static_check_exp ctxt exp ;;
      match field_sh_bd field eret.(sh_bd) with
      | None => error (ShapeErr (concat [
          ctxt.(loc); strlit "expression shape "; sh_bd_to_str eret.(sh_bd);
          strlit " has no field "; field; strlit " in ";
          get_scope_desc ctxt.(context_scope); strlit [NL]]))
      | Some sb => return_ {| sh_bd := sb |}
      end
  | Load shape addr =>
      check_shape ctxt.(structs) ctxt.(loc) ctxt.(context_scope) shape ;;
      aret <- static_check_exp ctxt addr ;;
      match aret.(sh_bd) with
      | StructB _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "load address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | NamedB _ _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "load address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | WordB NotBased =>
          log (WarningErr (get_memop_msg true true false ctxt.(loc) ctxt.(context_scope)))
      | WordB NotTrusted =>
          log (WarningErr (get_memop_msg true true true ctxt.(loc) ctxt.(context_scope)))
      | _ => return_ tt
      end ;;
      match sh_bd_from_sh ctxt.(structs) Trusted shape with
      | Some sb => return_ {| sh_bd := sb |}
      | None => error (ScopeErr (get_implementation_err_msg
          (strlit "static analysis failed to convert in-scope shape")
          ctxt.(loc) ctxt.(context_scope)))
      end
  | Load32 addr =>
      aret <- static_check_exp ctxt addr ;;
      match aret.(sh_bd) with
      | StructB _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "load address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | NamedB _ _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "load address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | WordB NotBased =>
          log (WarningErr (get_memop_msg true true false ctxt.(loc) ctxt.(context_scope)))
      | WordB NotTrusted =>
          log (WarningErr (get_memop_msg true true true ctxt.(loc) ctxt.(context_scope)))
      | _ => return_ tt
      end ;;
      return_ {| sh_bd := WordB Trusted |}
  | LoadByte addr =>
      aret <- static_check_exp ctxt addr ;;
      match aret.(sh_bd) with
      | StructB _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "load address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | NamedB _ _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "load address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | WordB NotBased =>
          log (WarningErr (get_memop_msg true true false ctxt.(loc) ctxt.(context_scope)))
      | WordB NotTrusted =>
          log (WarningErr (get_memop_msg true true true ctxt.(loc) ctxt.(context_scope)))
      | _ => return_ tt
      end ;;
      return_ {| sh_bd := WordB Trusted |}
  | Op bop exps =>
      let op_str := binop_to_str bop in
      let nargs := LENGTH exps in
      match bop with
      | Sub =>
          if decide (~ (nargs = 2)) then
            error (GenErr (get_oparg_msg true (strlit "2") (num_to_str nargs)
              ctxt.(loc) op_str ctxt.(context_scope)))
          else return_ tt
      | _ =>
          if nargs <? 2 then
            error (GenErr (get_oparg_msg false (strlit "2") (num_to_str nargs)
              ctxt.(loc) op_str ctxt.(context_scope)))
          else return_ tt
      end ;;
      esret <-
        (fix static_check_exps (l : list (exp a)) : static_result exps_return :=
           match l with
           | [] => return_ {| sh_bds := [] |}
           | exp :: exps =>
               eret <- static_check_exp ctxt exp ;;
               esret <- static_check_exps exps ;;
               return_ {| sh_bds := eret.(sh_bd) :: esret.(sh_bds) |}
           end) exps ;;
      b <- check_operands ctxt op_str esret.(sh_bds) ;;
      return_ {| sh_bd := WordB b |}
  | Panop pop exps =>
      let op_str := panop_to_str pop in
      let nargs := LENGTH exps in
      match pop with
      | Mul =>
          if decide (~ (nargs = 2)) then
            error (GenErr (get_oparg_msg true (strlit "2") (num_to_str nargs)
              ctxt.(loc) op_str ctxt.(context_scope)))
          else return_ tt
      end ;;
      esret <-
        (fix static_check_exps (l : list (exp a)) : static_result exps_return :=
           match l with
           | [] => return_ {| sh_bds := [] |}
           | exp :: exps =>
               eret <- static_check_exp ctxt exp ;;
               esret <- static_check_exps exps ;;
               return_ {| sh_bds := eret.(sh_bd) :: esret.(sh_bds) |}
           end) exps ;;
      b <- check_operands ctxt op_str esret.(sh_bds) ;;
      return_ {| sh_bd := WordB b |}
  | Cmp cop exp1 exp2 =>
      eret1 <- static_check_exp ctxt exp1 ;;
      eret2 <- static_check_exp ctxt exp2 ;;
      (if negb (sh_bd_eq_shapes eret1.(sh_bd) eret2.(sh_bd)) then
         error (ShapeErr (concat [
             ctxt.(loc); strlit "comparison given operands of different shapes in ";
             get_scope_desc ctxt.(context_scope); strlit [NL]]))
       else return_ tt) ;;
      return_ {| sh_bd := WordB NotBased |}
  | Shift sop exp1 exp2 =>
      eret1 <- static_check_exp ctxt exp1 ;;
      eret2 <- static_check_exp ctxt exp2 ;;
      (if negb (sh_bd_has_shape One eret1.(sh_bd)) then
         error (ShapeErr (get_non_word_msg
           (strlit "shifted expression")
           (sh_bd_to_str eret1.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
       else if negb (sh_bd_has_shape One eret2.(sh_bd)) then
         error (ShapeErr (get_non_word_msg
           (strlit "shift expression")
           (sh_bd_to_str eret2.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
       else return_ tt) ;;
      return_ eret2
  | BaseAddr =>
      return_ {| sh_bd := WordB Based |}
  | TopAddr =>
      return_ {| sh_bd := WordB Based |}
  | BytesInWord =>
      return_ {| sh_bd := WordB NotBased |}
  end.

Fixpoint static_check_exps {a : N} (ctxt : context) (l : list (exp a))
    : static_result exps_return :=
  match l with
  | [] => return_ {| sh_bds := [] |}
  | exp :: exps =>
      eret <- static_check_exp ctxt exp ;;
      esret <- static_check_exps ctxt exps ;;
      return_ {| sh_bds := eret.(sh_bd) :: esret.(sh_bds) |}
  end.

(** Helpers for [static_check_exp_def]: the nested [fix]es of
    [static_check_exp] compute [static_check_exps]. *)
Lemma static_check_exps_unique {a : N} (ctxt : context)
    (F : list (exp a) -> static_result exps_return) :
  F [] = return_ {| sh_bds := [] |} ->
  (forall x l, F (x :: l) =
     (eret <- static_check_exp ctxt x ;;
      esret <- F l ;;
      return_ {| sh_bds := eret.(sh_bd) :: esret.(sh_bds) |})) ->
  forall l, F l = static_check_exps ctxt l.
Proof.
  intros H0 HS l; induction l as [|x l IH]; [exact H0|].
  rewrite HS, IH; reflexivity.
Qed.

Lemma static_check_exps_unique_fields {a : N} (ctxt : context)
    (F : list (fldname * exp a) -> static_result exps_return) :
  F [] = return_ {| sh_bds := [] |} ->
  (forall k x l, F ((k, x) :: l) =
     (eret <- static_check_exp ctxt x ;;
      esret <- F l ;;
      return_ {| sh_bds := eret.(sh_bd) :: esret.(sh_bds) |})) ->
  forall l, F l = static_check_exps ctxt (SND (UNZIP l)).
Proof.
  intros H0 HS l; induction l as [|[k x] l IH]; [exact H0|].
  rewrite HS, IH; reflexivity.
Qed.

(*! HOL "cakeml/pancake/panStaticScript.sml" "static_check_exp_def" *)
Theorem static_check_exp_def : forall {a : N} (ctxt : context),
  (forall num, static_check_exp ctxt (Const num : panLang.exp a) =
   (return_ {| sh_bd := WordB NotBased |})) /\
  (forall vname, static_check_exp ctxt (panLang.Var Local vname : panLang.exp a) =
   (vinf <- check_local_var ctxt vname ;;
      return_ {| sh_bd := vinf.(vsh_bd) |})) /\
  (forall vname, static_check_exp ctxt (panLang.Var Global vname : panLang.exp a) =
   (vinf <- check_global_var ctxt vname ;;
      match sh_bd_from_sh ctxt.(structs) Trusted vinf.(vshape) with
      | Some sb => return_ {| sh_bd := sb |}
      | None => error (ScopeErr (get_implementation_err_msg
          (strlit "static analysis failed to convert in-scope shape")
          ctxt.(loc) ctxt.(context_scope)))
      end)) /\
  (forall exps, static_check_exp ctxt (RStruct exps : panLang.exp a) =
   (esret <- static_check_exps ctxt exps ;;
      return_ {| sh_bd := StructB esret.(sh_bds) |})) /\
  (forall index exp, static_check_exp ctxt (RField index exp : panLang.exp a) =
   (eret <- static_check_exp ctxt exp ;;
      match index_sh_bd index eret.(sh_bd) with
      | None => error (ShapeErr (concat [
          ctxt.(loc); strlit "expression shape "; sh_bd_to_str eret.(sh_bd);
          strlit " has no field at index "; num_to_str index;
          strlit " in "; get_scope_desc ctxt.(context_scope); strlit [NL]]))
      | Some sb => return_ {| sh_bd := sb |}
      end)) /\
  (forall name eflds, static_check_exp ctxt (NStruct name eflds : panLang.exp a) =
   (sinfo <-
        match ALOOKUP ctxt.(structs) name with
        | Some info => return_ info
        | None => error (ScopeErr (get_scope_msg Stc ctxt.(loc) name ctxt.(context_scope)))
        end ;;
      let '(field_names, field_exps) := UNZIP eflds in
      esret <- static_check_exps ctxt field_exps ;;
      let field_sbs := ZIP (field_names, esret.(sh_bds)) in
      check_struct_fields ctxt name sinfo.(fields) field_sbs ;;
      return_ {| sh_bd := NamedB name field_sbs |})) /\
  (forall field exp, static_check_exp ctxt (NField field exp : panLang.exp a) =
   (eret <- static_check_exp ctxt exp ;;
      match field_sh_bd field eret.(sh_bd) with
      | None => error (ShapeErr (concat [
          ctxt.(loc); strlit "expression shape "; sh_bd_to_str eret.(sh_bd);
          strlit " has no field "; field; strlit " in ";
          get_scope_desc ctxt.(context_scope); strlit [NL]]))
      | Some sb => return_ {| sh_bd := sb |}
      end)) /\
  (forall shape addr, static_check_exp ctxt (Load shape addr : panLang.exp a) =
   (check_shape ctxt.(structs) ctxt.(loc) ctxt.(context_scope) shape ;;
      aret <- static_check_exp ctxt addr ;;
      match aret.(sh_bd) with
      | StructB _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "load address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | NamedB _ _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "load address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | WordB NotBased =>
          log (WarningErr (get_memop_msg true true false ctxt.(loc) ctxt.(context_scope)))
      | WordB NotTrusted =>
          log (WarningErr (get_memop_msg true true true ctxt.(loc) ctxt.(context_scope)))
      | _ => return_ tt
      end ;;
      match sh_bd_from_sh ctxt.(structs) Trusted shape with
      | Some sb => return_ {| sh_bd := sb |}
      | None => error (ScopeErr (get_implementation_err_msg
          (strlit "static analysis failed to convert in-scope shape")
          ctxt.(loc) ctxt.(context_scope)))
      end)) /\
  (forall addr, static_check_exp ctxt (Load32 addr : panLang.exp a) =
   (aret <- static_check_exp ctxt addr ;;
      match aret.(sh_bd) with
      | StructB _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "load address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | NamedB _ _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "load address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | WordB NotBased =>
          log (WarningErr (get_memop_msg true true false ctxt.(loc) ctxt.(context_scope)))
      | WordB NotTrusted =>
          log (WarningErr (get_memop_msg true true true ctxt.(loc) ctxt.(context_scope)))
      | _ => return_ tt
      end ;;
      return_ {| sh_bd := WordB Trusted |})) /\
  (forall addr, static_check_exp ctxt (LoadByte addr : panLang.exp a) =
   (aret <- static_check_exp ctxt addr ;;
      match aret.(sh_bd) with
      | StructB _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "load address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | NamedB _ _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "load address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | WordB NotBased =>
          log (WarningErr (get_memop_msg true true false ctxt.(loc) ctxt.(context_scope)))
      | WordB NotTrusted =>
          log (WarningErr (get_memop_msg true true true ctxt.(loc) ctxt.(context_scope)))
      | _ => return_ tt
      end ;;
      return_ {| sh_bd := WordB Trusted |})) /\
  (forall bop exps, static_check_exp ctxt (Op bop exps : panLang.exp a) =
   (let op_str := binop_to_str bop in
      let nargs := LENGTH exps in
      match bop with
      | Sub =>
          if decide (~ (nargs = 2)) then
            error (GenErr (get_oparg_msg true (strlit "2") (num_to_str nargs)
              ctxt.(loc) op_str ctxt.(context_scope)))
          else return_ tt
      | _ =>
          if nargs <? 2 then
            error (GenErr (get_oparg_msg false (strlit "2") (num_to_str nargs)
              ctxt.(loc) op_str ctxt.(context_scope)))
          else return_ tt
      end ;;
      esret <- static_check_exps ctxt exps ;;
      b <- check_operands ctxt op_str esret.(sh_bds) ;;
      return_ {| sh_bd := WordB b |})) /\
  (forall pop exps, static_check_exp ctxt (Panop pop exps : panLang.exp a) =
   (let op_str := panop_to_str pop in
      let nargs := LENGTH exps in
      match pop with
      | Mul =>
          if decide (~ (nargs = 2)) then
            error (GenErr (get_oparg_msg true (strlit "2") (num_to_str nargs)
              ctxt.(loc) op_str ctxt.(context_scope)))
          else return_ tt
      end ;;
      esret <- static_check_exps ctxt exps ;;
      b <- check_operands ctxt op_str esret.(sh_bds) ;;
      return_ {| sh_bd := WordB b |})) /\
  (forall cop exp1 exp2, static_check_exp ctxt (Cmp cop exp1 exp2 : panLang.exp a) =
   (eret1 <- static_check_exp ctxt exp1 ;;
      eret2 <- static_check_exp ctxt exp2 ;;
      (if negb (sh_bd_eq_shapes eret1.(sh_bd) eret2.(sh_bd)) then
         error (ShapeErr (concat [
             ctxt.(loc); strlit "comparison given operands of different shapes in ";
             get_scope_desc ctxt.(context_scope); strlit [NL]]))
       else return_ tt) ;;
      return_ {| sh_bd := WordB NotBased |})) /\
  (forall sop exp1 exp2, static_check_exp ctxt (Shift sop exp1 exp2 : panLang.exp a) =
   (eret1 <- static_check_exp ctxt exp1 ;;
      eret2 <- static_check_exp ctxt exp2 ;;
      (if negb (sh_bd_has_shape One eret1.(sh_bd)) then
         error (ShapeErr (get_non_word_msg
           (strlit "shifted expression")
           (sh_bd_to_str eret1.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
       else if negb (sh_bd_has_shape One eret2.(sh_bd)) then
         error (ShapeErr (get_non_word_msg
           (strlit "shift expression")
           (sh_bd_to_str eret2.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
       else return_ tt) ;;
      return_ eret2)) /\
  (static_check_exp ctxt (BaseAddr : panLang.exp a) =
   (return_ {| sh_bd := WordB Based |})) /\
  (static_check_exp ctxt (TopAddr : panLang.exp a) =
   (return_ {| sh_bd := WordB Based |})) /\
  (static_check_exp ctxt (BytesInWord : panLang.exp a) =
   (return_ {| sh_bd := WordB NotBased |})) /\
  static_check_exps ctxt ([] : list (panLang.exp a)) = return_ {| sh_bds := [] |} /\
  (forall exp exps, static_check_exps ctxt (exp :: exps : list (panLang.exp a)) =
   (eret <- static_check_exp ctxt exp ;;
    esret <- static_check_exps ctxt exps ;;
    return_ {| sh_bds := eret.(sh_bd) :: esret.(sh_bds) |})).
Proof.
  intros a ctxt; repeat split; intros; try reflexivity.
  all: cbn [static_check_exp].
  all: try (match goal with
            | |- context [?G ?l] =>
                let H := fresh in
                assert (H : G l = static_check_exps ctxt l)
                  by (apply static_check_exps_unique; reflexivity);
                rewrite H; reflexivity
            end).
  match goal with
  | |- context [?G eflds] =>
      let H := fresh in
      assert (H : G eflds = static_check_exps ctxt (SND (UNZIP eflds)))
        by (apply static_check_exps_unique_fields; reflexivity);
      rewrite H
  end.
  f_equal; apply functional_extensionality; intros sinfo.
  destruct (UNZIP eflds); reflexivity.
Qed.

(*! HOL "cakeml/pancake/panStaticScript.sml" "static_check_prog_def" *)
Fixpoint static_check_prog {a : N} (ctxt : context) (p : prog a) {struct p}
    : static_result prog_return :=
  match p with
  | Skip =>
      return_ {|
          exits_fun := false
        ; exits_loop := false
        ; prog_return_last := OtherLast
        ; var_delta := mlmap.empty mlstring.compare
        ; curr_loc := ctxt.(loc) |}
  | Dec vname shape exp prog =>
      check_redec_var ctxt vname ;;
      check_shape ctxt.(structs) ctxt.(loc) ctxt.(context_scope) shape ;;
      eret <- static_check_exp ctxt exp ;;
      (if negb (sh_bd_has_shape shape eret.(sh_bd)) then
         error (ShapeErr (get_shape_mismatch_msg (concat [
             strlit "expression to initialise local variable "; vname
           ]) (sh_bd_to_str eret.(sh_bd)) (shape_to_str shape)
           ctxt.(loc) ctxt.(context_scope)))
       else return_ tt) ;;
      let ctxt' := set_last (set_locals ctxt
                     (mlmap.insert ctxt.(locals) vname {| vsh_bd := eret.(sh_bd) |}))
                     OtherLast in
      pret <- static_check_prog ctxt' prog ;;
      return_ {|
          exits_fun := pret.(exits_fun)
        ; exits_loop := pret.(exits_loop)
        ; prog_return_last := pret.(prog_return_last)
        ; var_delta := mlmap.delete pret.(var_delta) vname
        ; curr_loc := pret.(curr_loc) |}
  | DecCall vname shape fname args prog =>
      check_redec_var ctxt vname ;;
      check_shape ctxt.(structs) ctxt.(loc) ctxt.(context_scope) shape ;;
      finf <- check_fun_name ctxt fname ;;
      esret <- static_check_exps ctxt args ;;
      check_func_args ctxt fname finf.(func_info_params) esret.(sh_bds) ;;
      (if decide (~ (shape = finf.(ret_shape))) then
         error (ShapeErr (get_shape_mismatch_msg (concat [
             strlit "result of function call "; fname;
             strlit " to initialise local variable "; vname
           ]) (shape_to_str finf.(ret_shape)) (shape_to_str shape)
           ctxt.(loc) ctxt.(context_scope)))
       else return_ tt) ;;
      sb <-
        match sh_bd_from_sh ctxt.(structs) Trusted shape with
        | Some sb => return_ sb
        | None => error (ScopeErr (get_implementation_err_msg
            (strlit "static analysis failed to convert in-scope shape")
            ctxt.(loc) ctxt.(context_scope)))
        end ;;
      let ctxt' := set_last (set_locals ctxt
                     (mlmap.insert ctxt.(locals) vname {| vsh_bd := sb |}))
                     OtherLast in
      pret <- static_check_prog ctxt' prog ;;
      return_ {|
          exits_fun := pret.(exits_fun)
        ; exits_loop := pret.(exits_loop)
        ; prog_return_last := pret.(prog_return_last)
        ; var_delta := mlmap.delete pret.(var_delta) vname
        ; curr_loc := pret.(curr_loc) |}
  | Assign Local vname exp =>
      vinf <- check_local_var ctxt vname ;;
      eret <- static_check_exp ctxt exp ;;
      (if negb (sh_bd_eq_shapes vinf.(vsh_bd) eret.(sh_bd)) then
         error (ShapeErr (get_shape_mismatch_msg (concat [
             strlit "expression assigned to local variable "; vname
           ]) (sh_bd_to_str eret.(sh_bd)) (sh_bd_to_str vinf.(vsh_bd))
           ctxt.(loc) ctxt.(context_scope)))
       else return_ tt) ;;
      return_ {|
          exits_fun := false
        ; exits_loop := false
        ; prog_return_last := OtherLast
        ; var_delta :=
            mlmap.singleton mlstring.compare vname {| vsh_bd := eret.(sh_bd) |}
        ; curr_loc := ctxt.(loc) |}
  | Assign Global vname exp =>
      vinf <- check_global_var ctxt vname ;;
      eret <- static_check_exp ctxt exp ;;
      (if negb (sh_bd_has_shape vinf.(vshape) eret.(sh_bd)) then
         error (ShapeErr (get_shape_mismatch_msg (concat [
             strlit "expression assigned to global variable "; vname
           ]) (sh_bd_to_str eret.(sh_bd)) (shape_to_str vinf.(vshape))
           ctxt.(loc) ctxt.(context_scope)))
       else return_ tt) ;;
      return_ {|
          exits_fun := false
        ; exits_loop := false
        ; prog_return_last := OtherLast
        ; var_delta := mlmap.empty mlstring.compare
        ; curr_loc := ctxt.(loc) |}
  | Call (Some (Some (Local, vname), hdl)) fname args =>
      vinf <- check_local_var ctxt vname ;;
      finf <- check_fun_name ctxt fname ;;
      esret <- static_check_exps ctxt args ;;
      check_func_args ctxt fname finf.(func_info_params) esret.(sh_bds) ;;
      (if negb (sh_bd_has_shape finf.(ret_shape) vinf.(vsh_bd)) then
         error (ShapeErr (get_shape_mismatch_msg (concat [
             strlit "result of function call "; fname;
             strlit " assigned to local variable "; vname
           ]) (shape_to_str finf.(ret_shape)) (sh_bd_to_str vinf.(vsh_bd))
           ctxt.(loc) ctxt.(context_scope)))
       else return_ tt) ;;
      match hdl with
      | None => return_ tt
      | Some (eid, (evar, prog)) =>
          sh <- match mlmap.lookup ctxt.(exns) eid with
                | None => error (ScopeErr (concat [
                            strlit "exception "; eid; strlit (" is not declared" ++ [NL])]))
                | Some sh => return_ sh
                end ;;
          evinf <- check_local_var ctxt evar ;;
          (if negb (sh_bd_has_shape sh evinf.(vsh_bd)) then
             error (ShapeErr (concat [
               strlit "handler variable "; evar;
               strlit " does not match shape of exception "; eid; strlit [NL]]))
           else return_ tt) ;;
          sb <-
            match sh_bd_from_sh ctxt.(structs) Trusted sh with
            | Some sb => return_ sb
            | None => error (ScopeErr (get_implementation_err_msg
                (strlit "static analysis failed to convert in-scope shape")
                ctxt.(loc) ctxt.(context_scope)))
            end ;;
          static_check_prog
            (set_locals ctxt (mlmap.insert ctxt.(locals) evar {| vsh_bd := sb |}))
            prog ;;
          return_ tt
      end ;;
      return_ {|
          exits_fun := false
        ; exits_loop := false
        ; prog_return_last := OtherLast
        ; var_delta :=
            mlmap.singleton mlstring.compare vname
              {| vsh_bd := sh_bd_from_bd Trusted vinf.(vsh_bd) |}
        ; curr_loc := ctxt.(loc) |}
  | Call (Some (Some (Global, vname), hdl)) fname args =>
      vinf <- check_global_var ctxt vname ;;
      finf <- check_fun_name ctxt fname ;;
      esret <- static_check_exps ctxt args ;;
      check_func_args ctxt fname finf.(func_info_params) esret.(sh_bds) ;;
      (if decide (~ (vinf.(vshape) = finf.(ret_shape))) then
         error (ShapeErr (get_shape_mismatch_msg (concat [
             strlit "result of function call "; fname;
             strlit " assigned to global variable "; vname
           ]) (shape_to_str finf.(ret_shape)) (shape_to_str vinf.(vshape))
           ctxt.(loc) ctxt.(context_scope)))
       else return_ tt) ;;
      match hdl with
      | None => return_ tt
      | Some (eid, (evar, prog)) =>
          evinf <- check_local_var ctxt evar ;;
          static_check_prog (set_locals ctxt
              (mlmap.insert ctxt.(locals) evar
                 {| vsh_bd := sh_bd_from_bd Trusted evinf.(vsh_bd) |})) prog ;;
          return_ tt
      end ;;
      return_ {|
          exits_fun := false
        ; exits_loop := false
        ; prog_return_last := OtherLast
        ; var_delta := mlmap.empty mlstring.compare
        ; curr_loc := ctxt.(loc) |}
  | Primitive vname pop es =>
      vinf <- check_local_var ctxt vname ;;
      esret <- static_check_exps ctxt es ;;
      res_sb <- check_primitive_args ctxt pop esret.(sh_bds) ;;
      (if negb (sh_bd_eq_shapes vinf.(vsh_bd) res_sb)
       then error (ShapeErr (get_shape_mismatch_msg (concat [
           strlit "result of primitive "; primop_to_str pop;
           strlit " assigned to local variable "; vname
         ]) (sh_bd_to_str res_sb) (sh_bd_to_str vinf.(vsh_bd))
         ctxt.(loc) ctxt.(context_scope)))
       else return_ tt) ;;
      return_ {| exits_fun := false
               ; exits_loop := false
               ; prog_return_last := OtherLast
               ; var_delta := mlmap.singleton mlstring.compare vname
                                {| vsh_bd := res_sb |}
               ; curr_loc := ctxt.(loc) |}
  | Return exp =>
      eret <- static_check_exp ctxt exp ;;
      finf <-
        match ctxt.(context_scope) with
        | FunScope fname _ => check_fun_name ctxt fname
        | _ => error (GenErr (get_implementation_err_msg
            (strlit "return found outside function scope")
            ctxt.(loc) ctxt.(context_scope)))
        end ;;
      (if negb (sh_bd_has_shape finf.(ret_shape) eret.(sh_bd)) then
         error (ShapeErr (get_shape_mismatch_msg
           (strlit "expression to return")
           (sh_bd_to_str eret.(sh_bd)) (shape_to_str finf.(ret_shape))
           ctxt.(loc) ctxt.(context_scope)))
       else return_ tt) ;;
      return_ {|
          exits_fun := true
        ; exits_loop := false
        ; prog_return_last := RetLast
        ; var_delta := mlmap.empty mlstring.compare
        ; curr_loc := ctxt.(loc) |}
  | Call None fname args =>
      caller_inf <-
        match ctxt.(context_scope) with
        | FunScope caller _ => check_fun_name ctxt caller
        | _ => error (GenErr (strlit "tail call found outside function scope"))
        end ;;
      callee_inf <- check_fun_name ctxt fname ;;
      esret <- static_check_exps ctxt args ;;
      (if decide (~ (caller_inf.(ret_shape) = callee_inf.(ret_shape))) then
         error (ShapeErr (get_shape_mismatch_msg (concat [
             strlit "result of function call "; fname;
             strlit " to return"
           ]) (shape_to_str callee_inf.(ret_shape))
           (shape_to_str caller_inf.(ret_shape))
           ctxt.(loc) ctxt.(context_scope)))
       else return_ tt) ;;
      check_func_args ctxt fname callee_inf.(func_info_params) esret.(sh_bds) ;;
      return_ {|
          exits_fun := true
        ; exits_loop := false
        ; prog_return_last := TailLast
        ; var_delta := mlmap.empty mlstring.compare
        ; curr_loc := ctxt.(loc) |}
  | Call (Some (None, hdl)) fname args =>
      finf <- check_fun_name ctxt fname ;;
      esret <- static_check_exps ctxt args ;;
      check_func_args ctxt fname finf.(func_info_params) esret.(sh_bds) ;;
      match hdl with
      | None => return_ tt
      | Some (eid, (evar, prog)) =>
          sh <- match mlmap.lookup ctxt.(exns) eid with
                | None => error (ScopeErr (concat [
                            strlit "exception "; eid; strlit (" is not declared" ++ [NL])]))
                | Some sh => return_ sh
                end ;;
          evinf <- check_local_var ctxt evar ;;
          (if negb (sh_bd_has_shape sh evinf.(vsh_bd)) then
             error (ShapeErr (concat [
               strlit "handler variable "; evar;
               strlit " does not match shape of exception "; eid; strlit [NL]]))
           else return_ tt) ;;
          sb <-
            match sh_bd_from_sh ctxt.(structs) Trusted sh with
            | Some sb => return_ sb
            | None => error (ScopeErr (get_implementation_err_msg
                (strlit "static analysis failed to convert in-scope shape")
                ctxt.(loc) ctxt.(context_scope)))
            end ;;
          static_check_prog
            (set_locals ctxt (mlmap.insert ctxt.(locals) evar {| vsh_bd := sb |}))
            prog ;;
          return_ tt
      end ;;
      return_ {|
          exits_fun := false
        ; exits_loop := false
        ; prog_return_last := OtherLast
        ; var_delta := mlmap.empty mlstring.compare
        ; curr_loc := ctxt.(loc) |}
  | ExtCall fname ptr1 len1 ptr2 len2 =>
      esret <- static_check_exps ctxt [ptr1; len1; ptr2; len2] ;;
      match FIND (fun sb => negb (sh_bd_has_shape One sb)) esret.(sh_bds) with
      | Some sb => error (ShapeErr (get_non_word_msg (concat [
          strlit "value for argument given to FFI "; fname
        ]) (sh_bd_to_str sb) ctxt.(loc) ctxt.(context_scope)))
      | None => return_ tt
      end ;;
      return_ {|
          exits_fun := false
        ; exits_loop := false
        ; prog_return_last := OtherLast
        ; var_delta := mlmap.empty mlstring.compare
        ; curr_loc := ctxt.(loc) |}
  | Seq prog1 prog2 =>
      let '(warn_p1, ctxt1) := reached_warnable prog1 ctxt in
      match warn_p1 with
      | Some ls =>
          log (WarningErr (get_unreach_msg ctxt1.(loc) (last_to_str ls) ctxt1.(context_scope)))
      | None => return_ tt
      end ;;
      pret1 <- static_check_prog ctxt1 prog1 ;;
      let next_r := next_is_reachable ctxt1.(is_reachable) pret1.(prog_return_last) in
      let ctxt2 :=
        set_loc (set_last (set_is_reachable (set_locals ctxt1
            (seq_loc_inf ctxt1.(locals) pret1.(var_delta)))
            next_r)
            (if next_now_unreachable ctxt1.(is_reachable) next_r
             then pret1.(prog_return_last)
             else ctxt1.(last)))
            pret1.(curr_loc) in
      let '(warn_p2, ctxt3) := reached_warnable prog2 ctxt2 in
      match warn_p2 with
      | Some ls =>
          log (WarningErr (get_unreach_msg ctxt3.(loc) (last_to_str ls) ctxt1.(context_scope)))
      | None => return_ tt
      end ;;
      pret2 <- static_check_prog ctxt3 prog2 ;;
      return_ {|
          exits_fun := (pret1.(exits_fun) || pret2.(exits_fun))
        ; exits_loop := (pret1.(exits_loop) || pret2.(exits_loop))
        ; prog_return_last := seq_last_stmt pret1.(prog_return_last) pret2.(prog_return_last)
        ; var_delta := seq_loc_inf pret1.(var_delta) pret2.(var_delta)
        ; curr_loc := pret2.(curr_loc) |}
  | If exp prog1 prog2 =>
      eret <- static_check_exp ctxt exp ;;
      (if negb (sh_bd_has_shape One eret.(sh_bd)) then
         error (ShapeErr (get_non_word_msg
           (strlit "if condition") (sh_bd_to_str eret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
       else return_ tt) ;;
      pret1 <- static_check_prog ctxt prog1 ;;
      pret2 <- static_check_prog (set_loc ctxt pret1.(curr_loc)) prog2 ;;
      let double_ret := (pret1.(exits_fun) && pret2.(exits_fun)) in
      let double_loop_exit := (pret1.(exits_loop) && pret2.(exits_loop)) in
      return_ {|
          exits_fun := double_ret
        ; exits_loop := double_loop_exit
        ; prog_return_last := branch_last_stmt double_ret double_loop_exit
        ; var_delta := branch_loc_inf ctxt.(locals) pret1.(var_delta) pret2.(var_delta)
        ; curr_loc := pret2.(curr_loc) |}
  | While exp prog =>
      eret <- static_check_exp ctxt exp ;;
      (if negb (sh_bd_has_shape One eret.(sh_bd)) then
         error (ShapeErr (get_non_word_msg
           (strlit "while condition") (sh_bd_to_str eret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
       else return_ tt) ;;
      pret <- static_check_prog (set_in_loop ctxt true) prog ;;
      return_ {|
          exits_fun := false
        ; exits_loop := false
        ; prog_return_last := OtherLast
        ; var_delta :=
            branch_loc_inf ctxt.(locals) pret.(var_delta) (mlmap.empty mlstring.compare)
        ; curr_loc := ctxt.(loc) |}
  | Break =>
      (if negb ctxt.(in_loop) then
         error (GenErr (get_rogue_msg true ctxt.(loc) ctxt.(context_scope)))
       else return_ tt) ;;
      return_ {|
          exits_fun := false
        ; exits_loop := true
        ; prog_return_last := BreakLast
        ; var_delta := mlmap.empty mlstring.compare
        ; curr_loc := ctxt.(loc) |}
  | Continue =>
      (if negb ctxt.(in_loop) then
         error (GenErr (get_rogue_msg false ctxt.(loc) ctxt.(context_scope)))
       else return_ tt) ;;
      return_ {|
          exits_fun := false
        ; exits_loop := true
        ; prog_return_last := ContLast
        ; var_delta := mlmap.empty mlstring.compare
        ; curr_loc := ctxt.(loc) |}
  | Raise eid exp =>
      sh <- match mlmap.lookup ctxt.(exns) eid with
            | None => error (ScopeErr (concat [
                        strlit "exception "; eid; strlit (" is not declared" ++ [NL])]))
            | Some sh => return_ sh
            end ;;
      eret <- static_check_exp ctxt exp ;;
      (if negb (sh_bd_has_shape sh eret.(sh_bd)) then
         error (ShapeErr (concat [
           strlit "raised exception "; eid;
           strlit (" has wrong value shape" ++ [NL])]))
       else return_ tt) ;;
      return_ {| exits_fun := true
               ; exits_loop := false
               ; prog_return_last := RaiseLast
               ; var_delta := mlmap.empty mlstring.compare
               ; curr_loc := ctxt.(loc) |}
  | Store addr exp =>
      aret <- static_check_exp ctxt addr ;;
      eret <- static_check_exp ctxt exp ;;
      match aret.(sh_bd) with
      | StructB _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "store address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | NamedB _ _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "store address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | WordB NotBased =>
          log (WarningErr (get_memop_msg true false false ctxt.(loc) ctxt.(context_scope)))
      | WordB NotTrusted =>
          log (WarningErr (get_memop_msg true false true ctxt.(loc) ctxt.(context_scope)))
      | _ => return_ tt
      end ;;
      return_ {|
          exits_fun := false
        ; exits_loop := false
        ; prog_return_last := OtherLast
        ; var_delta := mlmap.empty mlstring.compare
        ; curr_loc := ctxt.(loc) |}
  | Store32 addr exp =>
      aret <- static_check_exp ctxt addr ;;
      eret <- static_check_exp ctxt exp ;;
      match aret.(sh_bd) with
      | StructB _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "store address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | NamedB _ _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "store address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | WordB NotBased =>
          log (WarningErr (get_memop_msg true false false ctxt.(loc) ctxt.(context_scope)))
      | WordB NotTrusted =>
          log (WarningErr (get_memop_msg true false true ctxt.(loc) ctxt.(context_scope)))
      | _ => return_ tt
      end ;;
      (if negb (sh_bd_has_shape One eret.(sh_bd)) then
         error (ShapeErr (get_non_word_msg
           (strlit "store value") (sh_bd_to_str eret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
       else return_ tt) ;;
      return_ {|
          exits_fun := false
        ; exits_loop := false
        ; prog_return_last := OtherLast
        ; var_delta := mlmap.empty mlstring.compare
        ; curr_loc := ctxt.(loc) |}
  | StoreByte addr exp =>
      aret <- static_check_exp ctxt addr ;;
      eret <- static_check_exp ctxt exp ;;
      match aret.(sh_bd) with
      | StructB _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "store address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | NamedB _ _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "store address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | WordB NotBased =>
          log (WarningErr (get_memop_msg true false false ctxt.(loc) ctxt.(context_scope)))
      | WordB NotTrusted =>
          log (WarningErr (get_memop_msg true false true ctxt.(loc) ctxt.(context_scope)))
      | _ => return_ tt
      end ;;
      (if negb (sh_bd_has_shape One eret.(sh_bd)) then
         error (ShapeErr (get_non_word_msg
           (strlit "store value") (sh_bd_to_str eret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
       else return_ tt) ;;
      return_ {|
          exits_fun := false
        ; exits_loop := false
        ; prog_return_last := OtherLast
        ; var_delta := mlmap.empty mlstring.compare
        ; curr_loc := ctxt.(loc) |}
  | ShMemLoad mop Local vname addr =>
      vinf <- check_local_var ctxt vname ;;
      aret <- static_check_exp ctxt addr ;;
      match aret.(sh_bd) with
      | StructB _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "load address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | NamedB _ _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "load address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | WordB Based =>
          log (WarningErr (get_memop_msg false true false ctxt.(loc) ctxt.(context_scope)))
      | WordB NotTrusted =>
          log (WarningErr (get_memop_msg false true true ctxt.(loc) ctxt.(context_scope)))
      | _ => return_ tt
      end ;;
      (if negb (sh_bd_has_shape One vinf.(vsh_bd)) then
         error (ShapeErr (get_non_word_msg
           (strlit "load variable") (sh_bd_to_str vinf.(vsh_bd)) ctxt.(loc) ctxt.(context_scope)))
       else return_ tt) ;;
      return_ {|
          exits_fun := false
        ; exits_loop := false
        ; prog_return_last := OtherLast
        ; var_delta :=
            mlmap.singleton mlstring.compare vname
              {| vsh_bd := sh_bd_from_bd Trusted vinf.(vsh_bd) |}
        ; curr_loc := ctxt.(loc) |}
  | ShMemLoad mop Global vname addr =>
      vinf <- check_global_var ctxt vname ;;
      aret <- static_check_exp ctxt addr ;;
      match aret.(sh_bd) with
      | StructB _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "load address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | NamedB _ _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "load address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | WordB Based =>
          log (WarningErr (get_memop_msg false true false ctxt.(loc) ctxt.(context_scope)))
      | WordB NotTrusted =>
          log (WarningErr (get_memop_msg false true true ctxt.(loc) ctxt.(context_scope)))
      | _ => return_ tt
      end ;;
      (if decide (~ (One = vinf.(vshape))) then
         error (ShapeErr (get_non_word_msg
           (strlit "load variable") (shape_to_str vinf.(vshape)) ctxt.(loc) ctxt.(context_scope)))
       else return_ tt) ;;
      return_ {|
          exits_fun := false
        ; exits_loop := false
        ; prog_return_last := OtherLast
        ; var_delta := mlmap.empty mlstring.compare
        ; curr_loc := ctxt.(loc) |}
  | ShMemStore mop addr exp =>
      aret <- static_check_exp ctxt addr ;;
      eret <- static_check_exp ctxt exp ;;
      match aret.(sh_bd) with
      | StructB _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "store address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | NamedB _ _ =>
          error (ShapeErr (get_non_word_msg
            (strlit "store address") (sh_bd_to_str aret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
      | WordB Based =>
          log (WarningErr (get_memop_msg false false false ctxt.(loc) ctxt.(context_scope)))
      | WordB NotTrusted =>
          log (WarningErr (get_memop_msg false false true ctxt.(loc) ctxt.(context_scope)))
      | _ => return_ tt
      end ;;
      (if negb (sh_bd_has_shape One eret.(sh_bd)) then
         error (ShapeErr (get_non_word_msg
           (strlit "store value") (sh_bd_to_str eret.(sh_bd)) ctxt.(loc) ctxt.(context_scope)))
       else return_ tt) ;;
      return_ {|
          exits_fun := false
        ; exits_loop := false
        ; prog_return_last := OtherLast
        ; var_delta := mlmap.empty mlstring.compare
        ; curr_loc := ctxt.(loc) |}
  | Tick =>
      return_ {|
          exits_fun := false
        ; exits_loop := false
        ; prog_return_last := InvisLast
        ; var_delta := mlmap.empty mlstring.compare
        ; curr_loc := ctxt.(loc) |}
  | Annot tag str =>
      let loc :=
        if decide (tag = strlit "location") then
          concat [strlit "AT "; str; strlit ": "]
        else ctxt.(loc) in
      return_ {|
          exits_fun := false
        ; exits_loop := false
        ; prog_return_last := InvisLast
        ; var_delta := mlmap.empty mlstring.compare
        ; curr_loc := loc |}
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "static_check_progs_def" *)
Fixpoint static_check_progs {a : N} (fctxt : mlmap.map funname func_info)
    (gctxt : mlmap.map varname global_info) (sctxt : list (stcname * struct_info))
    (ectxt : mlmap.map eid shape) (l : list (decl a)) : static_result unit :=
  match l with
  | [] => return_ tt
  | Name _ _ :: decls => static_check_progs fctxt gctxt sctxt ectxt decls
  | ExnDecl _ _ :: decls => static_check_progs fctxt gctxt sctxt ectxt decls
  | Decl _ _ _ :: decls => static_check_progs fctxt gctxt sctxt ectxt decls
  | Function fi :: decls =>
      let '(param_names, param_shapes) := UNZIP fi.(params) in
      param_sbs <-
        match OPT_MMAP (sh_bd_from_sh sctxt Trusted) param_shapes with
        | Some sbs => return_ (ZIP (param_names, sbs))
        | None => error (ScopeErr (get_implementation_err_msg
            (strlit "static analysis failed to convert in-scope shape")
            (strlit "") (FunScope fi.(name) (strlit ""))))
        end ;;
      let ctxt := {| locals :=
                       FOLDL (fun m '(v, sb) => mlmap.insert m v {| vsh_bd := sb |})
                         (mlmap.empty mlstring.compare) param_sbs
                   ; globals := gctxt
                   ; exns := ectxt
                   ; funcs := fctxt
                   ; structs := sctxt
                   ; context_scope := FunScope fi.(name) (strlit "")
                   ; in_loop := false
                   ; is_reachable := IsReach
                   ; last := InvisLast
                   ; loc := strlit "" |} in
      prog_ret <- static_check_prog ctxt fi.(body) ;;
      (if negb prog_ret.(exits_fun) then
         error (GenErr (concat [
             strlit "branches missing return statement in ";
             get_scope_desc (FunScope fi.(name) (strlit "")); strlit [NL]]))
       else return_ tt) ;;
      static_check_progs fctxt gctxt sctxt ectxt decls
  end.

(** In HOL's non-[main] branch, [if fi.export then do ... od else
    check_id_shapes ...] is one statement of the [do] block ([;] separates
    statements), so the return-shape [check_shape] and the 32-word size check
    follow it for exported functions too (where they are no-ops, the return
    shape being [One]). *)
(*! HOL "cakeml/pancake/panStaticScript.sml" "static_check_decls_def" *)
Fixpoint static_check_decls {a : N} (fctxt : mlmap.map funname func_info)
    (gctxt : mlmap.map varname global_info) (sctxt : list (stcname * struct_info))
    (ectxt : mlmap.map eid shape) (l : list (decl a))
    : static_result (mlmap.map funname func_info *
                     (mlmap.map varname global_info * mlmap.map eid shape)) :=
  match l with
  | [] => return_ (fctxt, (gctxt, ectxt))
  | Name _ _ :: decls => static_check_decls fctxt gctxt sctxt ectxt decls
  | Decl shape vname exp :: decls =>
      let ctxt := {| locals := mlmap.empty mlstring.compare
                   ; globals := gctxt
                   ; exns := ectxt
                   ; funcs := mlmap.empty mlstring.compare
                   ; structs := sctxt
                   ; context_scope := DeclScope vname
                   ; in_loop := false
                   ; is_reachable := IsReach
                   ; last := InvisLast
                   ; loc := strlit "" |} in
      check_redec_var (set_context_scope ctxt TopLevel) vname ;;
      check_shape sctxt (strlit "") ctxt.(context_scope) shape ;;
      eret <- static_check_exp ctxt exp ;;
      (if negb (sh_bd_has_shape shape eret.(sh_bd)) then
         error (ShapeErr (get_shape_mismatch_msg (concat [
             strlit "expression to initialise global variable "; vname
           ]) (sh_bd_to_str eret.(sh_bd)) (shape_to_str shape)
           (strlit "") ctxt.(context_scope)))
       else return_ tt) ;;
      static_check_decls fctxt (mlmap.insert gctxt vname {| vshape := shape |})
        sctxt ectxt decls
  | ExnDecl eid sh :: decls =>
      (if mlmap.member eid ectxt then
         error (ScopeErr (concat [
           strlit "exception "; eid; strlit (" is redeclared" ++ [NL])]))
       else return_ tt) ;;
      static_check_decls fctxt gctxt sctxt (mlmap.insert ectxt eid sh) decls
  | Function fi :: decls =>
      (if mlmap.member fi.(name) fctxt then
         error (ScopeErr (get_redec_msg Fun (strlit "") fi.(name) TopLevel))
       else return_ tt) ;;
      (if decide (fi.(name) = strlit "main") then
         (if 0 <? LENGTH fi.(params) then
            error (GenErr (strlit ("main function has arguments" ++ [NL])))
          else return_ tt) ;;
         (if fi.(export) then
            error (GenErr (strlit ("main function is exported" ++ [NL])))
          else return_ tt) ;;
         (if decide (~ (fi.(fun_decl_return) = One)) then
            error (ShapeErr (get_non_word_msg
              (strlit "main function return") (shape_to_str fi.(fun_decl_return))
              (strlit "") (FunScope fi.(name) (strlit ""))))
          else return_ tt)
       else
         match first_repeat (sort mlstring_lt (MAP FST fi.(params))) with
         | Some pname => error (ScopeErr (concat [
             strlit "parameter "; pname; strlit " is redeclared in function ";
             fi.(name); strlit [NL]]))
         | None => return_ tt
         end ;;
         (if fi.(export) then
            (if 4 <? LENGTH fi.(params) then
               error (GenErr (concat [
                   strlit "exported function "; fi.(name);
                   strlit (" has more than 4 arguments" ++ [NL])]))
             else return_ tt) ;;
            check_export_params (strlit "")
              (FunScope fi.(name) (strlit "")) fi.(params) ;;
            (if decide (~ (fi.(fun_decl_return) = One)) then
               error (ShapeErr (get_non_word_msg
                 (strlit "exported function return") (shape_to_str fi.(fun_decl_return))
                 (strlit "") (FunScope fi.(name) (strlit ""))))
             else return_ tt)
          else
            check_id_shapes sctxt (strlit "")
              (FunScope fi.(name) (strlit "")) fi.(params)) ;;
         check_shape sctxt (strlit "")
           (FunScope fi.(name) (strlit " return")) fi.(fun_decl_return) ;;
         (if 32 <? size_of_sh_with_ctxt sctxt fi.(fun_decl_return) then
            error (ShapeErr (concat [
                strlit "function "; fi.(name);
                strlit (" returns a shape bigger than 32 words" ++ [NL])]))
          else return_ tt)) ;;
      static_check_decls
        (mlmap.insert fctxt fi.(name)
           {| ret_shape := fi.(fun_decl_return) ; func_info_params := fi.(params) |})
        gctxt sctxt ectxt decls
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "static_check_names_def" *)
Fixpoint static_check_names {a : N} (sctxt : list (stcname * struct_info))
    (l : list (decl a)) : static_result (list (stcname * struct_info)) :=
  match l with
  | [] => return_ sctxt
  | Name name flds :: decls =>
      match ALOOKUP sctxt name with
      | Some info =>
          error (ScopeErr (get_redec_msg Stc (strlit "") name TopLevel))
      | None => return_ tt
      end ;;
      match first_repeat (sort mlstring_lt (MAP FST flds)) with
      | Some fld => error (ScopeErr (concat [
          strlit "field "; fld; strlit " is redeclared in struct name ";
          name; strlit [NL]]))
      | None => return_ tt
      end ;;
      check_id_shapes sctxt (strlit "") (StcScope name (strlit "")) flds ;;
      let info := {| fields := flds
                   ; size := size_of_sh_with_ctxt sctxt (Comb (MAP SND flds)) |} in
      static_check_names ((name, info) :: sctxt) decls
  | _ :: decls => static_check_names sctxt decls
  end.

(*! HOL "cakeml/pancake/panStaticScript.sml" "static_check_def" *)
Definition static_check {a : N} (decls : list (decl a)) : static_result unit :=
  sctxt <- static_check_names [] decls ;;
  '(fctxt, (gctxt, ectxt)) <-
    static_check_decls (mlmap.empty mlstring.compare)
      (mlmap.empty mlstring.compare) sctxt (mlmap.empty mlstring.compare) decls ;;
  static_check_progs fctxt gctxt sctxt ectxt decls.
