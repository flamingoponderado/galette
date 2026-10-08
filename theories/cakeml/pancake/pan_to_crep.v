(** * Pancake [pan_to_crep]: compilation from panLang to crepLang

    Port of [cakeml/pancake/pan_to_crepScript.sml].

    [panLang] and [crepLang] share constructor names: [crepLang] is
    imported after [panLang], so unqualified constructors are crepLang's and
    panLang's are written [panLang.X].  [varname] is crepLang's ([N]);
    panLang's is [panLang.varname].  HOL tuples nest to the right; HOL
    record updates are record constructions.  HOL [I] is [combin.I].

    The [finite_map] notations clash with the [words] notation [w ' i];
    [finite_map] is imported without its notations.

    [oHD] and [MAP3] ([listScript]) are Galette-local copies until ported
    in [list.v]. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require combin.
From Galette.HOL.src.n_bit Require Import words byte.
From Galette.HOL.src.finite_maps Require Import alist.
From Galette.HOL.src.finite_maps Require finite_map.
Import -(notations) finite_map.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.pancake Require Import pan_common panLang crepLang crep_inline.
Open Scope N_scope.

(** HOL [oHD] (from [listScript]; Galette-local until ported there). *)
#[local] Definition oHD {A} (l : list A) : option A :=
  match l with [] => None | h :: _ => Some h end.

(** HOL [MAP3] (from [listScript]; Galette-local until ported there). *)
#[local] Fixpoint MAP3 {A B C D} (f : A -> B -> C -> D) (l1 : list A) (l2 : list B) (l3 : list C)
    : list D :=
  match l1, l2, l3 with
  | h1 :: t1, h2 :: t2, h3 :: t3 => f h1 h2 h3 :: MAP3 f t1 t2 t3
  | _, _, _ => []
  end.

(*! HOL "cakeml/pancake/pan_to_crepScript.sml" "context" *)
Record context (a : N) : Type := {
  vars : fmap panLang.varname (shape * list N);
  funcs : fmap panLang.funname (list (panLang.varname * shape) * shape);
  eids : fmap panLang.eid (word a);
  vmax : N
}.
Arguments vars {a} _.
Arguments funcs {a} _.
Arguments eids {a} _.
Arguments vmax {a} _.

Section Defs.
Context {a : N}.

(*! HOL "cakeml/pancake/pan_to_crepScript.sml" "cexp_heads_def" *)
Fixpoint cexp_heads {A} (l : list (list A)) : option (list A) :=
  match l with
  | [] => Some []
  | e :: es =>
      match e, cexp_heads es with
      | [], _ => None
      | _, None => None
      | x :: xs, Some ys => Some (x :: ys)
      end
  end.

(*! HOL "cakeml/pancake/pan_to_crepScript.sml" "comp_field_def" *)
Fixpoint comp_field (i : N) (shs : list shape) (es : list (exp a)) : list (exp a) * shape :=
  match shs with
  | [] => ([Const (n2w 0)], One)
  | sh :: shs =>
      if decide (i = 0) then (TAKE (size_of_shape sh) es, sh)
      else comp_field (i - 1) shs (DROP (size_of_shape sh) es)
  end.

(*! HOL "cakeml/pancake/pan_to_crepScript.sml" "compile_panop_def" *)
Definition compile_panop (op : panop) : crepop :=
  match op with panLang.Mul => crepLang.Mul end.

(*! HOL "cakeml/pancake/pan_to_crepScript.sml" "compile_exp_def" *)
Fixpoint compile_exp (ctxt : context a) (e : panLang.exp a) : list (exp a) * shape :=
  match e with
  | panLang.Const c => ([Const c], One)
  | panLang.Var Local vname =>
      match FLOOKUP (vars ctxt) vname with
      | Some (shape, ns) => (MAP Var ns, shape)
      | None => ([Const (n2w 0)], One)
      end
  | panLang.Var Global vname => ([Const (n2w 0)], One)
  | panLang.RStruct es =>
      let cexps := MAP (compile_exp ctxt) es in
      (FLAT (MAP FST cexps), Comb (MAP SND cexps))
  | panLang.RField index e =>
      let (cexp, shape) := compile_exp ctxt e in
      match shape with
      | Comb shapes => comp_field index shapes cexp
      | _ => ([Const (n2w 0)], One)
      end
  | panLang.NStruct nm flds => ([Const (n2w 0)], One)
  | panLang.NField fld e => ([Const (n2w 0)], One)
  | panLang.Load sh e =>
      let (cexp, shape) := compile_exp ctxt e in
      match cexp with
      | e :: es => (load_shape (n2w 0) (size_of_shape sh) e, sh)
      | _ => ([Const (n2w 0)], One)
      end
  | panLang.Load32 e =>
      let (cexp, shape) := compile_exp ctxt e in
      match cexp, shape with
      | e :: es, One => ([Load32 e], One)
      | _, _ => ([Const (n2w 0)], One)
      end
  | panLang.LoadByte e =>
      let (cexp, shape) := compile_exp ctxt e in
      match cexp, shape with
      | e :: es, One => ([LoadByte e], One)
      | _, _ => ([Const (n2w 0)], One)
      end
  | panLang.Op bop es =>
      let cexps := MAP FST (MAP (compile_exp ctxt) es) in
      match cexp_heads cexps with
      | Some es => ([Op bop es], One)
      | _ => ([Const (n2w 0)], One)
      end
  | panLang.Panop pop es =>
      let cexps := MAP FST (MAP (compile_exp ctxt) es) in
      match cexp_heads cexps with
      | Some es => ([Crepop (compile_panop pop) es], One)
      | _ => ([Const (n2w 0)], One)
      end
  | panLang.Cmp cmp e e' =>
      let ce := FST (compile_exp ctxt e) in
      let ce' := FST (compile_exp ctxt e') in
      match ce, ce' with
      | e :: es, e' :: es' => ([Cmp cmp e e'], One)
      | _, _ => ([Const (n2w 0)], One)
      end
  | panLang.Shift sh e e' =>
      let ce := FST (compile_exp ctxt e) in
      let ce' := FST (compile_exp ctxt e') in
      match ce, ce' with
      | e :: es, e' :: es' => ([Shift sh e e'], One)
      | _, _ => ([Const (n2w 0)], One)
      end
  | panLang.BaseAddr => ([BaseAddr], One)
  | panLang.TopAddr => ([TopAddr], One)
  | panLang.BytesInWord => ([Const bytes_in_word], One)
  end.

(*! HOL "cakeml/pancake/pan_to_crepScript.sml" "exp_hdl_def" *)
Definition exp_hdl {K S} (fm : fmap K (S * list N)) (v : K) : prog a :=
  match FLOOKUP fm v with
  | None => Skip
  | Some (vshp, ns) => nested_seq (MAP2 Assign ns (load_globals (n2w 0) (LENGTH ns)))
  end.

End Defs.

(*! HOL "cakeml/pancake/pan_to_crepScript.sml" "ret_var_def" *)
Definition ret_var {A} (sh : shape) (ns : list A) : option A :=
  match sh with
  | One => oHD ns
  | Comb sh => if decide (size_of_shape (Comb sh) = 1) then oHD ns else None
  | Named sh => None
  end.

Section Defs2.
Context {a : N}.

(*! HOL "cakeml/pancake/pan_to_crepScript.sml" "ret_hdl_def" *)
Definition ret_hdl (sh : shape) (ns : list N) : prog a :=
  match sh with
  | One => Skip
  | Comb sh => if decide (1 < size_of_shape (Comb sh)) then assign_ret ns else Skip
  | Named sh => Skip
  end.

End Defs2.

(*! HOL "cakeml/pancake/pan_to_crepScript.sml" "wrap_rt_def" *)
Definition wrap_rt {A} (n : option (shape * list A)) : option (shape * list A) :=
  match n with
  | None => None
  | Some (One, []) => None
  | m => m
  end.

Section Compile.
Context {a : N}.

(*! HOL "cakeml/pancake/pan_to_crepScript.sml" "compile_def" *)
Fixpoint compile (ctxt : context a) (p : panLang.prog a) : prog a :=
  match p with
  | panLang.Skip => Skip
  | panLang.Dec v s e p =>
      let (es, sh) := compile_exp ctxt e in
      let vmax := vmax ctxt in
      let nvars := GENLIST (fun x => vmax + SUC x) (size_of_shape sh) in
      let nctxt := {| vars := FUPDATE (vars ctxt) (v, (sh, nvars)); funcs := funcs ctxt;
                      eids := eids ctxt; vmax := pan_to_crep.vmax ctxt + size_of_shape sh |} in
      if decide (size_of_shape sh = LENGTH es)
      then nested_decs nvars es (compile nctxt p)
      else Skip
  | panLang.Assign Local v e =>
      let (es, sh) := compile_exp ctxt e in
      match FLOOKUP (vars ctxt) v with
      | Some (vshp, ns) =>
          if decide (LENGTH ns = LENGTH es)
          then if distinct_lists ns (FLAT (MAP var_cexp es))
               then nested_seq (MAP2 Assign ns es)
               else let vmax := vmax ctxt in
                    let temps := GENLIST (fun x => vmax + SUC x) (LENGTH ns) in
                    nested_decs temps es (nested_seq (MAP2 Assign ns (MAP Var temps)))
          else Skip
      | None => Skip
      end
  | panLang.Assign Global v e => Skip
  | panLang.Primitive v pop es =>
      let cexps := MAP (compile_exp ctxt) es in
      let ces := FLAT (MAP FST cexps) in
      match FLOOKUP (vars ctxt) v with
      | None => Skip
      | Some (vshp, ns) =>
          let vmax := vmax ctxt in
          let temps := GENLIST (fun x => vmax + SUC x) (LENGTH ces) in
          nested_decs temps ces (Primitive ns pop temps)
      end
  | panLang.Store ad v =>
      match compile_exp ctxt ad with
      | (e :: es', sh') =>
          let (es, sh) := compile_exp ctxt v in
          let adv := vmax ctxt + 1 in
          let temps := GENLIST (fun x => adv + SUC x) (size_of_shape sh) in
          if decide (size_of_shape sh = LENGTH es)
          then nested_decs (adv :: temps) (e :: es)
                 (nested_seq (stores (Var adv) (MAP Var temps) (n2w 0)))
          else Skip
      | (_, _) => Skip
      end
  | panLang.Store32 dest src =>
      match compile_exp ctxt dest, compile_exp ctxt src with
      | (ad :: ads, _), (e :: es, _) => Store32 ad e
      | _, _ => Skip
      end
  | panLang.StoreByte dest src =>
      match compile_exp ctxt dest, compile_exp ctxt src with
      | (ad :: ads, _), (e :: es, _) => StoreByte ad e
      | _, _ => Skip
      end
  | panLang.Return rt =>
      let (ces, sh) := compile_exp ctxt rt in
      if decide (size_of_shape sh = 0) then Return [] else Return ces
  | panLang.Raise eid excp =>
      match FLOOKUP (eids ctxt) eid with
      | Some n =>
          let (ces, sh) := compile_exp ctxt excp in
          let temps := GENLIST (fun x => vmax ctxt + SUC x) (size_of_shape sh) in
          if decide (size_of_shape sh = LENGTH ces)
          then Seq (nested_decs temps ces (nested_seq (store_globals (n2w 0) (MAP Var temps))))
                   (Raise n)
          else Skip
      | None => Skip
      end
  | panLang.Seq p p' => Seq (compile ctxt p) (compile ctxt p')
  | panLang.If e p p' =>
      match compile_exp ctxt e with
      | (ce :: ces, _) => If ce (compile ctxt p) (compile ctxt p')
      | _ => Skip
      end
  | panLang.While e p =>
      match compile_exp ctxt e with
      | (ce :: ces, _) => While ce (compile ctxt p)
      | _ => Skip
      end
  | panLang.Break => Break 0
  | panLang.Continue => Continue 0
  | panLang.Call rtyp ce es =>
      let cexps := MAP (compile_exp ctxt) es in
      let args := FLAT (MAP FST cexps) in
      match rtyp with
      | None => Call None ce args
      | Some (None, hdl) =>
          let rts :=
            match FLOOKUP (funcs ctxt) ce with
            | None => []
            | Some (args, rshape) => GENLIST (fun x => vmax ctxt + SUC x) (size_of_shape rshape)
            end in
          match hdl with
          | None => nested_decs rts (REPLICATE (LENGTH rts) (Const (n2w 0)))
                      (Call (Some (rts, None)) ce args)
          | Some (eid, (evar, p)) =>
              match FLOOKUP (eids ctxt) eid with
              | None => nested_decs rts (REPLICATE (LENGTH rts) (Const (n2w 0)))
                          (Call (Some (rts, None)) ce args)
              | Some neid =>
                  let comp_hdl := compile ctxt p in
                  let hndlr := Seq (exp_hdl (vars ctxt) evar) comp_hdl in
                  nested_decs rts (REPLICATE (LENGTH rts) (Const (n2w 0)))
                    (Call (Some (rts, Some (neid, hndlr))) ce args)
              end
          end
      | Some (Some (rk, rt), hdl) =>
          match wrap_rt (FLOOKUP (vars ctxt) rt) with
          | None =>
              match hdl with
              | None => Call None ce args
              | Some (eid, (evar, p)) =>
                  match FLOOKUP (eids ctxt) eid with
                  | None => Call None ce args
                  | Some neid =>
                      let comp_hdl := compile ctxt p in
                      let hndlr := Seq (exp_hdl (vars ctxt) evar) comp_hdl in
                      Call (Some ([], Some (neid, hndlr))) ce args
                  end
              end
          | Some (sh, ns) =>
              match hdl with
              | None => Call (Some (ns, None)) ce args
              | Some (eid, (evar, p)) =>
                  match FLOOKUP (eids ctxt) eid with
                  | None => Call (Some (ns, None)) ce args
                  | Some neid =>
                      let comp_hdl := compile ctxt p in
                      let hndlr := Seq (exp_hdl (vars ctxt) evar) comp_hdl in
                      Call (Some (ns, Some (neid, hndlr))) ce args
                  end
              end
          end
      end
  | panLang.DecCall v s ce es p =>
      let cexps := MAP (compile_exp ctxt) es in
      let args := FLAT (MAP FST cexps) in
      let vmax := vmax ctxt in
      let nvars := GENLIST (fun x => vmax + SUC x) (size_of_shape s) in
      let nctxt := {| vars := FUPDATE (vars ctxt) (v, (s, nvars)); funcs := funcs ctxt;
                      eids := eids ctxt; vmax := pan_to_crep.vmax ctxt + size_of_shape s |} in
      let ret_dec := nested_decs nvars (REPLICATE (LENGTH nvars) (Const (n2w 0))) in
      let p' := compile nctxt p in
      ret_dec (Seq (Call (Some (nvars, None)) ce args) p')
  | panLang.ExtCall f ptr1 len1 ptr2 len2 =>
      let (ptr1', sh1) := compile_exp ctxt ptr1 in
      let (len1', sh2) := compile_exp ctxt len1 in
      let (ptr2', sh3) := compile_exp ctxt ptr2 in
      let (len2', sh4) := compile_exp ctxt len2 in
      let n := FOLDR MAX 0 (FLAT (MAP var_cexp (FLAT [ptr1'; len1'; ptr2'; len2']))) in
      match (sh1, ptr1'), ((sh2, len1'), ((sh3, ptr2'), (sh4, len2'))) with
      | (One, pc :: pcs), ((One, lc :: lcs), ((One, pc' :: pcs'), (One, lc' :: lcs'))) =>
          Dec (n + 1) pc
            (Dec (n + 2) lc
               (Dec (n + 3) pc'
                  (Dec (n + 4) lc'
                     (crepLang.ExtCall f (n + 1) (n + 2) (n + 3) (n + 4)))))
      | _, _ => Skip
      end
  | panLang.ShMemStore op r ad =>
      match compile_exp ctxt r, compile_exp ctxt ad with
      | (e :: _, _), (a0 :: _, _) =>
          let n := FOLDR MAX 0 (var_cexp e) in
          Dec (n + 1) a0 (ShMem (store_op op) (n + 1) e)
      | _, _ => Skip
      end
  | panLang.ShMemLoad op Local r ad =>
      match compile_exp ctxt ad with
      | (a0 :: _, _) =>
          match FLOOKUP (vars ctxt) r with
          | Some (_, r' :: _) => ShMem (load_op op) r' a0
          | _ => Skip
          end
      | _ => Skip
      end
  | panLang.ShMemLoad op Global r ad => Skip
  | panLang.Tick => Tick
  | panLang.Annot _ _ => Skip
  end.

(*! HOL "cakeml/pancake/pan_to_crepScript.sml" "mk_ctxt_def" *)
Definition mk_ctxt (vmap : fmap panLang.varname (shape * list N))
    (fs : fmap panLang.funname (list (panLang.varname * shape) * shape)) (m : N)
    (es : fmap panLang.eid (word a)) : context a :=
  {| vars := vmap; funcs := fs; eids := es; vmax := m |}.

(*! HOL "cakeml/pancake/pan_to_crepScript.sml" "make_vmap_def" *)
Definition make_vmap {K} `{EqDecision K} (params : list (K * shape))
    : fmap K (shape * list N) :=
  let pvars := MAP FST params in
  let shs := MAP SND params in
  let ns := GENLIST combin.I (size_of_shape (Comb shs)) in
  let cvars := ZIP (shs, with_shape shs ns) in
  FUPDATE_LIST FEMPTY (ZIP (pvars, cvars)).

(*! HOL "cakeml/pancake/pan_to_crepScript.sml" "comp_func_def" *)
Definition comp_func (fs : fmap panLang.funname (list (panLang.varname * shape) * shape))
    (eids : fmap panLang.eid (word a)) (params : list (panLang.varname * shape))
    (body : panLang.prog a) : prog a :=
  let vmap := make_vmap params in
  let shapes := MAP SND params in
  let vmax := size_of_shape (Comb shapes) - 1 in
  compile (mk_ctxt vmap fs vmax eids) body.

(*! HOL "cakeml/pancake/pan_to_crepScript.sml" "get_eids_from_decls_def" *)
Definition get_eids_from_decls (decls : list (decl a)) : fmap panLang.eid (word a) :=
  let eids := MAP FST (exceptions decls) in
  let ns := GENLIST (fun x => (n2w x : word a)) (LENGTH eids) in
  let es := MAP2 (fun x y => (x, y)) eids ns in
  alist_to_fmap es.

(*! HOL "cakeml/pancake/pan_to_crepScript.sml" "make_funcs_def" *)
Definition make_funcs {A B C D} `{EqDecision A} (prog : list (A * (B * (C * D))))
    : fmap A (B * D) :=
  let fnames := MAP FST prog in
  let params := MAP (FST ∘ SND) prog in
  let returns := MAP (SND ∘ SND ∘ SND) prog in
  let fs := MAP3 (fun x y z => (x, (y, z))) fnames params returns in
  alist_to_fmap fs.

(*! HOL "cakeml/pancake/pan_to_crepScript.sml" "crep_vars_def" *)
Definition crep_vars {K} (params : list (K * shape)) : list N :=
  let shapes := MAP SND params in
  let len := size_of_shape (Comb shapes) in
  GENLIST combin.I len.

(*! HOL "cakeml/pancake/pan_to_crepScript.sml" "compile_to_crep_def" *)
Definition compile_to_crep (decls : list (decl a))
    : list (panLang.funname * (list N * prog a)) :=
  let prog := functions decls in
  let comp := comp_func (make_funcs prog) (get_eids_from_decls decls) in
  MAP (fun '(name, (params, (body, return_))) =>
         (name, (crep_vars params, comp params body))) prog.

(*! HOL "cakeml/pancake/pan_to_crepScript.sml" "compile_prog_def" *)
Definition compile_prog (prog : list (decl a)) : list (panLang.funname * (list N * crepLang.prog a)) :=
  let inl_fs_names := MAP FST (functions (FILTER inlinable prog)) in
  let to_crep := compile_to_crep prog in
  compile_inl_top inl_fs_names to_crep.

End Compile.
