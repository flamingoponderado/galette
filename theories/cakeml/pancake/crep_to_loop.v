(** * Pancake [crep_to_loop]: compilation from crepLang to loopLang

    Port of [cakeml/pancake/crep_to_loopScript.sml].

    [crepLang] and [loopLang] share constructor names: [loopLang] is
    imported after [crepLang], so unqualified constructors are loopLang's
    and crepLang's are written [crepLang.X].  HOL tuples nest to the right
    ([(p, le, tmp, l)] is [(p, (le, (tmp, l)))]); HOL record updates are
    record constructions.  The mutual [compile_exp]/[compile_exps] are a
    [Fixpoint] with a nested [fix]; the top-level [compile_exps] is equal
    to it and HOL's equations are the tagged [compile_exp_def] theorem.

    The [finite_map] notations clash with the [words] notation [w ' i];
    [finite_map] is imported without its notations.

    [OPT_MMAP] ([listScript]) and [MAPi] ([indexedListsScript]) are
    Galette-local copies until ported in their own files. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require combin.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.finite_maps Require Import sptree alist.
From Galette.HOL.src.finite_maps Require finite_map.
Import -(notations) finite_map.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.pancake Require Import crepLang loopLang.
From Galette.cakeml.pancake Require loop_live crep_arith.
Open Scope N_scope.

(** HOL [OPT_MMAP] (from [listScript]; Galette-local until ported there). *)
#[local] Fixpoint OPT_MMAP {A B} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | h0 :: t0 => OPTION_BIND (f h0) (fun h => OPTION_BIND (OPT_MMAP f t0) (fun t => Some (h :: t)))
  end.

(** HOL [MAPi] (from [indexedListsScript]; Galette-local until ported
    there): [MAPi f l = [f 0 x0; f 1 x1; ...]]. *)
#[local] Fixpoint MAPi_from {A B} (i : N) (f : N -> A -> B) (l : list A) : list B :=
  match l with
  | [] => []
  | h :: t => f i h :: MAPi_from (i + 1) f t
  end.
#[local] Definition MAPi {A B} (f : N -> A -> B) (l : list A) : list B := MAPi_from 0 f l.

(*! HOL "cakeml/pancake/crep_to_loopScript.sml" "context" *)
Record context : Type := {
  vars : fmap crepLang.varname N;
  funcs : fmap crepLang.funname (N * N);
  vmax : N;
  target : architecture
}.

(*! HOL "cakeml/pancake/crep_to_loopScript.sml" "find_var_def" *)
Definition find_var (ct : context) (v : N) : N :=
  match FLOOKUP (vars ct) v with
  | Some n => n
  | None => 0
  end.

(*! HOL "cakeml/pancake/crep_to_loopScript.sml" "find_lab_def" *)
Definition find_lab (ct : context) (f : mlstring) : N :=
  match FLOOKUP (funcs ct) f with
  | Some (n, _) => n
  | None => 0
  end.

Section Defs.
Context {a : N}.

(*! HOL "cakeml/pancake/crep_to_loopScript.sml" "prog_if_def" *)
Definition prog_if (cmp : cmp) (p q : list (prog a)) (e e' : exp a) (n m : N) (l : num_set)
    : list (prog a) :=
  p ++ q ++ [
    Assign n e; Assign m e';
    If cmp n (Reg m) (Assign n (Const (n2w 1))) (Assign n (Const (n2w 0))) (list_insert [n; m] l)].

(*! HOL "cakeml/pancake/crep_to_loopScript.sml" "compile_crepop_def" *)
Definition compile_crepop (op : crepop) (target : architecture) (x y tmp : N) (l : num_set)
    : list (prog a) * N :=
  match op with
  | crepLang.Mul =>
      if decide (target = ARMv7) then ([Arith (LLongMul tmp (tmp + 1) x y)], tmp + 1)
      else ([Arith (LLongMul tmp tmp x y)], tmp)
  end.

Fixpoint compile_exp (ctxt : context) (tmp : N) (l : num_set) (e : crepLang.exp a)
    : list (prog a) * (exp a * (N * num_set)) :=
  let compile_exps :=
    fix compile_exps (tmp : N) (l : num_set) (cps : list (crepLang.exp a))
        : list (prog a) * (list (exp a) * (N * num_set)) :=
      match cps with
      | [] => ([], ([], (tmp, l)))
      | e :: es =>
          let '(p, (le, (tmp, l))) := compile_exp ctxt tmp l e in
          let '(p1, (les, (tmp, l))) := compile_exps tmp l es in
          (p ++ p1, (le :: les, (tmp, l)))
      end in
  match e with
  | crepLang.BaseAddr => ([], (BaseAddr, (tmp, l)))
  | crepLang.TopAddr => ([], (TopAddr, (tmp, l)))
  | crepLang.Const c => ([], (Const c, (tmp, l)))
  | crepLang.Var v => ([], (Var (find_var ctxt v), (tmp, l)))
  | crepLang.Load ad =>
      let '(p, (le, (tmp, l))) := compile_exp ctxt tmp l ad in (p, (Load le, (tmp, l)))
  | crepLang.Load32 ad =>
      let '(p, (le, (tmp, l))) := compile_exp ctxt tmp l ad in
      (p ++ [Assign tmp le; Load32 tmp tmp], (Var tmp, (tmp + 1, insert tmp tt l)))
  | crepLang.LoadByte ad =>
      let '(p, (le, (tmp, l))) := compile_exp ctxt tmp l ad in
      (p ++ [Assign tmp le; LoadByte tmp tmp], (Var tmp, (tmp + 1, insert tmp tt l)))
  | crepLang.LoadGlob gadr => ([], (Lookup gadr, (tmp, l)))
  | crepLang.Op bop es =>
      let '(p, (les, (tmp, l))) := compile_exps tmp l es in
      (p, (Op bop les, (tmp, l)))
  | crepLang.Crepop cop es =>
      let tmp'' := tmp in
      let '(p, (les, (tmp, l))) := compile_exps tmp'' l es in
      let '(p', tmp') := compile_crepop cop (target ctxt) tmp (tmp + 1) (tmp + LENGTH les)
                           (list_insert (GENLIST (N.add tmp) (LENGTH les)) l) in
      (p ++ MAPi (fun n => Assign (tmp + n)) les ++ p',
       (Var tmp', (tmp' + 1, insert tmp' tt (list_insert (GENLIST (N.add tmp) (tmp' - tmp)) l))))
  | crepLang.Cmp cmp e e' =>
      let '(p, (le, (tmp, l))) := compile_exp ctxt tmp l e in
      let '(p', (le', (tmp', l))) := compile_exp ctxt tmp l e' in
      (prog_if cmp p p' le le' (tmp' + 1) (tmp' + 2) l,
       (Var (tmp' + 1), (tmp' + 3, list_insert [tmp' + 1; tmp' + 2] l)))
  | crepLang.Shift sh e e' =>
      let '(p, (le, (tmp, l))) := compile_exp ctxt tmp l e in
      let '(p', (le', (tmp', l))) := compile_exp ctxt tmp l e' in
      (p ++ p', (Shift sh le le', (tmp', l)))
  end.

Fixpoint compile_exps (ctxt : context) (tmp : N) (l : num_set) (cps : list (crepLang.exp a))
    : list (prog a) * (list (exp a) * (N * num_set)) :=
  match cps with
  | [] => ([], ([], (tmp, l)))
  | e :: es =>
      let '(p, (le, (tmp, l))) := compile_exp ctxt tmp l e in
      let '(p1, (les, (tmp, l))) := compile_exps ctxt tmp l es in
      (p ++ p1, (le :: les, (tmp, l)))
  end.

Lemma compile_exps_nested ctxt tmp l cps :
  (fix compile_exps (tmp : N) (l : num_set) (cps : list (crepLang.exp a))
       : list (prog a) * (list (exp a) * (N * num_set)) :=
     match cps with
     | [] => ([], ([], (tmp, l)))
     | e :: es =>
         let '(p, (le, (tmp, l))) := compile_exp ctxt tmp l e in
         let '(p1, (les, (tmp, l))) := compile_exps tmp l es in
         (p ++ p1, (le :: les, (tmp, l)))
     end) tmp l cps = compile_exps ctxt tmp l cps.
Proof.
  revert tmp l; induction cps as [|e es IH]; intros tmp l; [reflexivity|].
  cbn [compile_exps]; destruct (compile_exp ctxt tmp l e) as [p [le [tmp' l']]].
  rewrite IH; reflexivity.
Qed.

(** HOL [compile_exp_def] with [compile_exps] the top-level function. *)
(*! HOL "cakeml/pancake/crep_to_loopScript.sml" "compile_exp_def" *)
Theorem compile_exp_def :
  (forall ctxt tmp l, compile_exp ctxt tmp l crepLang.BaseAddr = ([], (BaseAddr, (tmp, l)))) /\
  (forall ctxt tmp l, compile_exp ctxt tmp l crepLang.TopAddr = ([], (TopAddr, (tmp, l)))) /\
  (forall ctxt tmp l c, compile_exp ctxt tmp l (crepLang.Const c) = ([], (Const c, (tmp, l)))) /\
  (forall ctxt tmp l v,
     compile_exp ctxt tmp l (crepLang.Var v) = ([], (Var (find_var ctxt v), (tmp, l)))) /\
  (forall ctxt tmp l ad, compile_exp ctxt tmp l (crepLang.Load ad) =
     let '(p, (le, (tmp, l))) := compile_exp ctxt tmp l ad in (p, (Load le, (tmp, l)))) /\
  (forall ctxt tmp l ad, compile_exp ctxt tmp l (crepLang.Load32 ad) =
     let '(p, (le, (tmp, l))) := compile_exp ctxt tmp l ad in
     (p ++ [Assign tmp le; Load32 tmp tmp], (Var tmp, (tmp + 1, insert tmp tt l)))) /\
  (forall ctxt tmp l ad, compile_exp ctxt tmp l (crepLang.LoadByte ad) =
     let '(p, (le, (tmp, l))) := compile_exp ctxt tmp l ad in
     (p ++ [Assign tmp le; LoadByte tmp tmp], (Var tmp, (tmp + 1, insert tmp tt l)))) /\
  (forall ctxt tmp l gadr,
     compile_exp ctxt tmp l (crepLang.LoadGlob gadr) = ([], (Lookup gadr, (tmp, l)))) /\
  (forall ctxt tmp l bop es, compile_exp ctxt tmp l (crepLang.Op bop es) =
     let '(p, (les, (tmp, l))) := compile_exps ctxt tmp l es in
     (p, (Op bop les, (tmp, l)))) /\
  (forall ctxt tmp'' l cop es, compile_exp ctxt tmp'' l (crepLang.Crepop cop es) =
     let '(p, (les, (tmp, l))) := compile_exps ctxt tmp'' l es in
     let '(p', tmp') := compile_crepop cop (target ctxt) tmp (tmp + 1) (tmp + LENGTH les)
                          (list_insert (GENLIST (N.add tmp) (LENGTH les)) l) in
     (p ++ MAPi (fun n => Assign (tmp + n)) les ++ p',
      (Var tmp', (tmp' + 1, insert tmp' tt (list_insert (GENLIST (N.add tmp) (tmp' - tmp)) l))))) /\
  (forall ctxt tmp l cmp e e', compile_exp ctxt tmp l (crepLang.Cmp cmp e e') =
     let '(p, (le, (tmp, l))) := compile_exp ctxt tmp l e in
     let '(p', (le', (tmp', l))) := compile_exp ctxt tmp l e' in
     (prog_if cmp p p' le le' (tmp' + 1) (tmp' + 2) l,
      (Var (tmp' + 1), (tmp' + 3, list_insert [tmp' + 1; tmp' + 2] l)))) /\
  (forall ctxt tmp l sh e e', compile_exp ctxt tmp l (crepLang.Shift sh e e') =
     let '(p, (le, (tmp, l))) := compile_exp ctxt tmp l e in
     let '(p', (le', (tmp', l))) := compile_exp ctxt tmp l e' in
     (p ++ p', (Shift sh le le', (tmp', l)))) /\
  (forall ctxt tmp l cps, compile_exps ctxt tmp l cps =
     match cps with
     | [] => ([], ([], (tmp, l)))
     | e :: es =>
         let '(p, (le, (tmp, l))) := compile_exp ctxt tmp l e in
         let '(p1, (les, (tmp, l))) := compile_exps ctxt tmp l es in
         (p ++ p1, (le :: les, (tmp, l)))
     end).
Proof.
  repeat split; try (intros; reflexivity).
  - intros; cbn [compile_exp]; rewrite compile_exps_nested; reflexivity.
  - intros; cbn [compile_exp]; rewrite compile_exps_nested; reflexivity.
  - intros ctxt tmp l [|e es]; reflexivity.
Qed.

(*! HOL "cakeml/pancake/crep_to_loopScript.sml" "gen_temps_def" *)
Definition gen_temps (n l : N) : list N := GENLIST (fun x => n + x) l.

(*! HOL "cakeml/pancake/crep_to_loopScript.sml" "rt_var_def" *)
Definition rt_var (fm : fmap N N) (v : option N) (n mx : N) : N :=
  match v with
  | None => n
  | Some v =>
      match FLOOKUP fm v with
      | None => mx + 1
      | Some m => m
      end
  end.

(*! HOL "cakeml/pancake/crep_to_loopScript.sml" "rt_vars_def" *)
Definition rt_vars (fm : fmap N N) (vs : list N) (mx : N) : list N :=
  match OPT_MMAP (FLOOKUP fm) vs with
  | None => [mx + 1]
  | Some m => m
  end.

(*! HOL "cakeml/pancake/crep_to_loopScript.sml" "compile_def" *)
Fixpoint compile (ctxt : context) (l : num_set) (prog : crepLang.prog a) : loopLang.prog a :=
  match prog with
  | crepLang.Skip => Skip
  | crepLang.Break n => Break n
  | crepLang.Continue n => Continue n
  | crepLang.Tick => Tick
  | crepLang.Return es =>
      let '(p, (les, (ntmp, nl))) := compile_exps ctxt (vmax ctxt + 1) l es in
      let ntmps := gen_temps ntmp (LENGTH les) in
      nested_seq (p ++ MAP2 Assign ntmps les ++ [Return ntmps])
  | crepLang.Raise eid =>
      Seq (Assign (vmax ctxt + 1) (Const eid)) (Raise (vmax ctxt + 1))
  | crepLang.ShMem op r ad =>
      match FLOOKUP (vars ctxt) r with
      | Some n =>
          let '(p, (le, (tmp, l))) := compile_exp ctxt (vmax ctxt + 1) l ad in
          nested_seq (p ++ [ShMem op n le])
      | None => Skip
      end
  | crepLang.Store dst src =>
      let '(p, (le, (tmp, l))) := compile_exp ctxt (vmax ctxt + 1) l dst in
      let '(p', (le', (tmp, l))) := compile_exp ctxt tmp l src in
      nested_seq (p ++ p' ++ [Assign tmp le'; Store le tmp])
  | crepLang.Store32 dst src =>
      let '(p, (le, (tmp, l))) := compile_exp ctxt (vmax ctxt + 1) l dst in
      let '(p', (le', (tmp, l))) := compile_exp ctxt tmp l src in
      nested_seq (p ++ p' ++ [Assign tmp le; Assign (tmp + 1) le'; Store32 tmp (tmp + 1)])
  | crepLang.StoreByte dst src =>
      let '(p, (le, (tmp, l))) := compile_exp ctxt (vmax ctxt + 1) l dst in
      let '(p', (le', (tmp, l))) := compile_exp ctxt tmp l src in
      nested_seq (p ++ p' ++ [Assign tmp le; Assign (tmp + 1) le'; StoreByte tmp (tmp + 1)])
  | crepLang.StoreGlob adr e =>
      let '(p, (le, (tmp, l))) := compile_exp ctxt (vmax ctxt + 1) l e in
      nested_seq (p ++ [SetGlobal adr le])
  | crepLang.Seq p q => Seq (compile ctxt l p) (compile ctxt l q)
  | crepLang.Assign v e =>
      match FLOOKUP (vars ctxt) v with
      | Some n =>
          let '(p, (le, (tmp, l))) := compile_exp ctxt (vmax ctxt + 1) l e in
          nested_seq (p ++ [Assign n le])
      | None => Skip
      end
  | crepLang.Primitive lhss pop rhss =>
      match OPT_MMAP (FLOOKUP (vars ctxt)) lhss, OPT_MMAP (FLOOKUP (vars ctxt)) rhss with
      | Some nlhss, Some nrhss => Primitive nlhss pop nrhss
      | _, _ => Skip
      end
  | crepLang.Dec v e prog =>
      let '(p, (le, (tmp, nl))) := compile_exp ctxt (vmax ctxt + 1) l e in
      let nctxt := {| vars := FUPDATE (vars ctxt) (v, tmp); funcs := funcs ctxt;
                      vmax := tmp; target := target ctxt |} in
      let fl := insert tmp tt l in
      let lp := compile nctxt fl prog in
      Seq (nested_seq p) (Seq (Assign tmp le) lp)
  | crepLang.If e p q =>
      let '(np, (le, (tmp, nl))) := compile_exp ctxt (vmax ctxt + 1) l e in
      let lp := compile ctxt l p in
      let lq := compile ctxt l q in
      nested_seq (np ++ [Assign tmp le; If NotEqual tmp (Imm (n2w 0)) lp lq l])
  | crepLang.While e p =>
      let '(np, (le, (tmp, nl))) := compile_exp ctxt (vmax ctxt + 1) l e in
      let lp := compile ctxt l p in
      Loop l (nested_seq (np ++ [
                Assign tmp le;
                If NotEqual tmp (Imm (n2w 0)) (Seq lp (Continue 0)) (Break 0) l]))
           l
  | crepLang.Call call_type e es =>
      let dest := find_lab ctxt e in
      let '(p, (les, (tmp, nl))) := compile_exps ctxt (vmax ctxt + 1) l es in
      let nargs := gen_temps tmp (LENGTH les) in
      let '(rt1, rt2) :=
        match call_type with
        | None => (None, None)
        | Some (rts, hdl) =>
            let rns := rt_vars (vars ctxt) rts (vmax ctxt + 1) in
            let en := vmax ctxt + 1 in
            let pe := match hdl with
                      | None => Raise en
                      | Some (eid, ep) =>
                          let cpe := compile ctxt l ep in
                          If NotEqual en (Imm eid) (Raise en) (Seq Tick cpe) l
                      end in
            (Some (rns, l), Some (en, (pe, (Skip, l))))
        end in
      nested_seq (p ++ MAP2 Assign nargs les ++ [Call rt1 (Some dest) nargs rt2])
  | crepLang.ExtCall f ptr1 len1 ptr2 len2 =>
      match FLOOKUP (vars ctxt) ptr1, FLOOKUP (vars ctxt) len1,
            FLOOKUP (vars ctxt) ptr2, FLOOKUP (vars ctxt) len2 with
      | Some pc, Some lc, Some pc', Some lc' => FFI f pc lc pc' lc' l
      | _, _, _, _ => Skip
      end
  end.

(*! HOL "cakeml/pancake/crep_to_loopScript.sml" "ocompile_def" *)
Definition ocompile (ctxt : context) (l : num_set) (p : crepLang.prog a) : loopLang.prog a :=
  (loop_live.optimise ∘ compile ctxt l) p.

End Defs.

(*! HOL "cakeml/pancake/crep_to_loopScript.sml" "mk_ctxt_def" *)
Definition mk_ctxt (target : architecture) (vmap : fmap N N) (fs : fmap mlstring (N * N))
    (vmax : N) : context :=
  {| vars := vmap; funcs := fs; vmax := vmax; target := target |}.

(*! HOL "cakeml/pancake/crep_to_loopScript.sml" "make_vmap_def" *)
Definition make_vmap (params : list N) : fmap N N :=
  FUPDATE_LIST FEMPTY (ZIP (params, GENLIST combin.I (LENGTH params))).

(*! HOL "cakeml/pancake/crep_to_loopScript.sml" "comp_func_def" *)
Definition comp_func {a : N} (target : architecture) (fs : fmap mlstring (N * N))
    (params : list N) (body : crepLang.prog a) : loopLang.prog a :=
  let vmap := make_vmap params in
  let vmax := LENGTH params - 1 in
  let l := list_to_num_set (GENLIST combin.I (LENGTH params)) in
  compile (mk_ctxt target vmap fs vmax) l body.

(*! HOL "cakeml/pancake/crep_to_loopScript.sml" "first_name_def" *)
Definition first_name : N := 64.

(*! HOL "cakeml/pancake/crep_to_loopScript.sml" "make_funcs_def" *)
Definition make_funcs {a : N} (prog : list (mlstring * (list N * crepLang.prog a)))
    : fmap mlstring (N * N) :=
  let fnames := MAP FST prog in
  let fnums := GENLIST (fun n => n + first_name) (LENGTH prog) in
  let lens := MAP (fun x => LENGTH (FST (SND x))) prog in
  let fnums_lens := MAP2 (fun x y => (x, y)) fnums lens in
  let fs := MAP2 (fun x y => (x, y)) fnames fnums_lens in
  alist_to_fmap fs.

(*! HOL "cakeml/pancake/crep_to_loopScript.sml" "compile_prog_def" *)
Definition compile_prog {a : N} (target : architecture)
    (prog : list (mlstring * (list N * crepLang.prog a)))
    : list (N * (list N * loopLang.prog a)) :=
  let fnums := GENLIST (fun n => n + first_name) (LENGTH prog) in
  let comp := comp_func target (make_funcs prog) in
  MAP2 (fun n '(name, (params, body)) =>
          (n, ((GENLIST combin.I ∘ LENGTH) params,
               loop_live.optimise (comp params (crep_arith.simp_prog body)))))
    fnums prog.
