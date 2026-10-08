(** * Pancake [pan_globals]: allocate globals at the end of the heap

    Port of [cakeml/pancake/pan_globalsScript.sml].

    HOL's ['a] word-width type variable is the width index [a : N].  HOL
    tuples nest to the right; HOL record updates are record constructions.

    [fresh_name] terminates in HOL by the measure
    [1 + MAX_SET (IMAGE strlen (set names)) - strlen name]; here it runs on
    a fuel of that many steps ([fresh_name_f]), and HOL's equation is the
    tagged [fresh_name_def] theorem. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words byte.
From Galette.HOL.src.string Require Import string.
From Galette.HOL.src.finite_maps Require Import alist.
From Galette.HOL.src.finite_maps Require finite_map.
Import -(notations) finite_map.

From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.pancake Require Import panLang.
Open Scope N_scope.
Open Scope hol_string_scope.

(*! HOL "cakeml/pancake/pan_globalsScript.sml" "context" *)
Record context (a : N) : Type := {
  globals : fmap varname (shape * word a);
  globals_size : word a;
  max_globals_size : word a
}.
Arguments globals {a} _.
Arguments globals_size {a} _.
Arguments max_globals_size {a} _.

Section Exp.
Context {a : N}.

(*! HOL "cakeml/pancake/pan_globalsScript.sml" "compile_exp_def" *)
Fixpoint compile_exp (ctxt : context a) (e : exp a) : exp a :=
  match e with
  | Var Local vname => Var Local vname
  | Var Global vname =>
      match FLOOKUP (globals ctxt) vname with
      | None => Const (n2w 0)
      | Some (sh, addr) => Load sh (Op Sub [TopAddr; Const addr])
      end
  | RStruct es => RStruct (MAP (compile_exp ctxt) es)
  | RField index e => RField index (compile_exp ctxt e)
  | NStruct nm flds => Const (n2w 0)
  | NField fld e => Const (n2w 0)
  | Load sh e => Load sh (compile_exp ctxt e)
  | LoadByte e => LoadByte (compile_exp ctxt e)
  | Load32 e => Load32 (compile_exp ctxt e)
  | Op bop es => Op bop (MAP (compile_exp ctxt) es)
  | Panop pop es => Panop pop (MAP (compile_exp ctxt) es)
  | Cmp cmp e e' => Cmp cmp (compile_exp ctxt e) (compile_exp ctxt e')
  | Shift sh e e' => Shift sh (compile_exp ctxt e) (compile_exp ctxt e')
  | TopAddr => Op Sub [TopAddr; Const (max_globals_size ctxt)]
  | e => e
  end.

End Exp.

(** ** Fresh names *)

(** The longest name length in [names] (HOL's
    [MAX_SET (IMAGE strlen (set names))]). *)
Definition max_strlen (names : list mlstring) : N :=
  FOLDR (fun s m => N.max (strlen s) m) 0 names.

Fixpoint fresh_name_f (fuel : nat) (name : mlstring) (names : list mlstring) : mlstring :=
  match fuel with
  | O => name
  | S fuel =>
      if MEM name names then fresh_name_f fuel (strcat name (strlit "'")) names
      else name
  end.

Definition fresh_name (name : mlstring) (names : list mlstring) : mlstring :=
  fresh_name_f (S (N.to_nat (1 + max_strlen names - strlen name))) name names.

Lemma MEM_strlen_le name names : MEM name names = true -> strlen name <= max_strlen names.
Proof.
  intros H; apply MEM_In in H; unfold max_strlen; induction names as [|n ns IH]; [destruct H|].
  cbn [FOLDR]; destruct H as [->|H]; [lia|specialize (IH H); lia].
Qed.

Lemma fresh_name_f_fuel : forall f1 f2 name names,
  (N.to_nat (1 + max_strlen names - strlen name) < f1)%nat ->
  (N.to_nat (1 + max_strlen names - strlen name) < f2)%nat ->
  fresh_name_f f1 name names = fresh_name_f f2 name names.
Proof.
  induction f1 as [|f1 IH]; intros [|f2] name names H1 H2; try lia.
  cbn [fresh_name_f]; destruct (MEM name names) eqn:E; [|reflexivity].
  apply MEM_strlen_le in E.
  apply IH; rewrite strlen_strcat; cbn [strlen LENGTH]; lia.
Qed.

(*! HOL "cakeml/pancake/pan_globalsScript.sml" "fresh_name_def" *)
Theorem fresh_name_def : forall name names,
  fresh_name name names =
  if MEM name names then fresh_name (strcat name (strlit "'")) names else name.
Proof.
  intros name names; unfold fresh_name at 1; cbn [fresh_name_f].
  destruct (MEM name names) eqn:E; [|reflexivity].
  apply MEM_strlen_le in E.
  apply fresh_name_f_fuel; rewrite strlen_strcat; cbn [strlen LENGTH]; lia.
Qed.

(** ** Programs *)

Section Defs.
Context {a : N}.

(*! HOL "cakeml/pancake/pan_globalsScript.sml" "compile_def" *)
Fixpoint compile (ctxt : context a) (p : prog a) : prog a :=
  match p with
  | Dec v s e p => Dec v s (compile_exp ctxt e) (compile ctxt p)
  | Assign vk v e =>
      match vk with
      | Global =>
          match FLOOKUP (globals ctxt) v with
          | None => Skip
          | Some (sh, addr) => Store (Op Sub [TopAddr; Const addr]) (compile_exp ctxt e)
          end
      | _ => Assign Local v (compile_exp ctxt e)
      end
  | Primitive v pop es => Primitive v pop (MAP (compile_exp ctxt) es)
  | Store ad v => Store (compile_exp ctxt ad) (compile_exp ctxt v)
  | Store32 ad v => Store32 (compile_exp ctxt ad) (compile_exp ctxt v)
  | StoreByte dest src => StoreByte (compile_exp ctxt dest) (compile_exp ctxt src)
  | Return rt => Return (compile_exp ctxt rt)
  | Raise eid excp => Raise eid (compile_exp ctxt excp)
  | Seq p p' => Seq (compile ctxt p) (compile ctxt p')
  | If e p p' => If (compile_exp ctxt e) (compile ctxt p) (compile ctxt p')
  | While e p => While (compile_exp ctxt e) (compile ctxt p)
  | Call rtyp e es =>
      let cexps := MAP (compile_exp ctxt) es in
      match rtyp with
      | None => Call None e cexps
      | Some (Some (Global, vn), hdl) =>
          match FLOOKUP (globals ctxt) vn with
          | None =>
              Call (Some (None,
                          match hdl with
                          | None => None
                          | Some (eid, (evar, p)) => Some (eid, (evar, compile ctxt p))
                          end))
                   e cexps
          | Some (sh, addr) =>
              match hdl with
              | None =>
                  DecCall (strlit "") sh e cexps
                    (Store (Op Sub [TopAddr; Const addr]) (Var Local (strlit "")))
              | Some (eid, (evar, p)) =>
                  let p' := compile ctxt p in
                  let names := evar :: free_var_ids p' ++ FLAT (MAP var_exp cexps) in
                  let vn' := fresh_name (strlit "") names in
                  let flag := fresh_name (strlit "vn'") (vn' :: names) in
                  Dec vn' sh (shape_val sh) (Dec flag One (Const (n2w 0))
                    (Seq (Call (Some (Some (Local, vn'),
                                      Some (eid, (evar, Seq p' (Assign Local flag (Const (n2w 1)))))))
                               e cexps)
                         (If (Var Local flag) Skip
                            (Store (Op Sub [TopAddr; Const addr]) (Var Local vn')))))
              end
          end
      | Some (tl, hdl) =>
          Call (Some (tl,
                      match hdl with
                      | None => None
                      | Some (eid, (evar, p)) => Some (eid, (evar, compile ctxt p))
                      end))
               e cexps
      end
  | DecCall v s e es p => DecCall v s e (MAP (compile_exp ctxt) es) (compile ctxt p)
  | ExtCall f ptr1 len1 ptr2 len2 =>
      ExtCall f (compile_exp ctxt ptr1) (compile_exp ctxt len1)
        (compile_exp ctxt ptr2) (compile_exp ctxt len2)
  | ShMemStore op r ad => ShMemStore op (compile_exp ctxt r) (compile_exp ctxt ad)
  | ShMemLoad op Local r ad => ShMemLoad op Local r (compile_exp ctxt ad)
  | ShMemLoad op Global r ad =>
      match FLOOKUP (globals ctxt) r with
      | Some (One, addr) =>
          let r' := strcat r (strlit "'") in
          Dec r One (compile_exp ctxt ad)
            (Dec r' One (Const (n2w 0))
               (Seq (ShMemLoad op Local r' (Var Local r))
                    (Store (Op Sub [TopAddr; Const addr]) (Var Local r'))))
      | _ => Skip
      end
  | p => p
  end.

(*! HOL "cakeml/pancake/pan_globalsScript.sml" "compile_decs_def" *)
Fixpoint compile_decs (ctxt : context a) (l : list (decl a))
    : list (prog a) * (list (decl a) * (list (decl a) * context a)) :=
  match l with
  | [] => ([], ([], ([], ctxt)))
  | Decl sh v e :: ds =>
      let s := word_add (globals_size ctxt) (word_mul bytes_in_word (n2w (size_of_shape sh))) in
      let ctxt' := {| globals := FUPDATE (globals ctxt) (v, (sh, s)); globals_size := s;
                      max_globals_size := max_globals_size ctxt |} in
      let '(decs, (funs, (exns, ctxt''))) := compile_decs ctxt' ds in
      (Store (Op Sub [TopAddr; Const s]) (compile_exp ctxt e) :: decs, (funs, (exns, ctxt'')))
  | Function fi :: ds =>
      let '(decs, (funs, (exns, ctxt''))) := compile_decs ctxt ds in
      (decs, (Function {| name := name fi; inline := inline fi; export := export fi;
                          params := params fi; body := compile ctxt (body fi);
                          fun_decl_return := fun_decl_return fi |} :: funs, (exns, ctxt'')))
  | ExnDecl eid sh :: ds =>
      let '(decs, (funs, (exns, ctxt''))) := compile_decs ctxt ds in
      (decs, (funs, (ExnDecl eid sh :: exns, ctxt'')))
  | Name nm flds :: ds => compile_decs ctxt ds
  end.

(*! HOL "cakeml/pancake/pan_globalsScript.sml" "resort_decls_def" *)
Definition resort_decls (decs : list (decl a)) : list (decl a) :=
  FILTER is_name decs ++ FILTER is_exn_decl decs ++ FILTER is_decl decs ++ FILTER is_function decs.

End Defs.

(*! HOL "cakeml/pancake/pan_globalsScript.sml" "fperm_name_def" *)
Definition fperm_name (f g h : mlstring) : mlstring :=
  if decide (f = h) then g
  else if decide (g = h) then f
  else h.

Section Fperm.
Context {a : N}.

(*! HOL "cakeml/pancake/pan_globalsScript.sml" "fperm_def" *)
Fixpoint fperm (f g : mlstring) (p : prog a) : prog a :=
  match p with
  | Dec v s e p => Dec v s e (fperm f g p)
  | Seq p p' => Seq (fperm f g p) (fperm f g p')
  | If e p p' => If e (fperm f g p) (fperm f g p')
  | While e p => While e (fperm f g p)
  | Call rtyp e es =>
      Call (match rtyp with
            | None => None
            | Some (tl, hdl) =>
                Some (tl, match hdl with
                          | None => None
                          | Some (eid, (evar, p)) => Some (eid, (evar, fperm f g p))
                          end)
            end)
           (fperm_name f g e) es
  | DecCall v s e es p => DecCall v s (fperm_name f g e) es (fperm f g p)
  | p => p
  end.

(*! HOL "cakeml/pancake/pan_globalsScript.sml" "fperm_decs_def" *)
Fixpoint fperm_decs (f g : mlstring) (l : list (decl a)) : list (decl a) :=
  match l with
  | [] => []
  | Function fi :: decs =>
      Function {| name := fperm_name f g (name fi); inline := inline fi; export := export fi;
                  params := params fi; body := fperm f g (body fi);
                  fun_decl_return := fun_decl_return fi |}
        :: fperm_decs f g decs
  | d :: decs => d :: fperm_decs f g decs
  end.

(*! HOL "cakeml/pancake/pan_globalsScript.sml" "new_main_name_def" *)
Definition new_main_name (decls : list (decl a)) : mlstring :=
  fresh_name (strlit "main") (MAP FST (functions decls)).

(*! HOL "cakeml/pancake/pan_globalsScript.sml" "dec_shapes_def" *)
Fixpoint dec_shapes (l : list (decl a)) : list shape :=
  match l with
  | Function _ :: ds => dec_shapes ds
  | Decl sh _ _ :: ds => sh :: dec_shapes ds
  | Name _ _ :: ds => dec_shapes ds
  | ExnDecl _ _ :: ds => dec_shapes ds
  | [] => []
  end.

(*! HOL "cakeml/pancake/pan_globalsScript.sml" "compile_top_def" *)
Definition compile_top (decs : list (decl a)) (start : mlstring) : list (decl a) :=
  match ALOOKUP (functions decs) start with
  | None => []
  | Some (args, (body, rshape)) =>
      let nds := resort_decls decs in
      let start' := new_main_name decs in
      let nds' := fperm_decs start start' nds in
      let '(decls, (funs, (exns, ctxt))) :=
        compile_decs
          {| globals := FEMPTY; globals_size := n2w 0;
             max_globals_size :=
               word_mul bytes_in_word (n2w (SUM (MAP size_of_shape (dec_shapes nds')))) |}
          nds' in
      let params := MAP (Var Local ∘ FST) args in
      let new_main := Function {| name := start; inline := false; export := false;
                                  panLang.params := args;
                                  panLang.body := Seq (nested_seq decls) (TailCall start' params);
                                  fun_decl_return := rshape |} in
      exns ++ new_main :: funs
  end.

End Fperm.
