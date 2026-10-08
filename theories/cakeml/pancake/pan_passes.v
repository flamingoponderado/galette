(** * Pancake [pan_passes]: the Pancake compiler with every intermediate program

    Port of [cakeml/pancake/pan_passesScript.sml]: [pan_to_target_all]
    (the compiler of [pan_to_target], also returning each intermediate
    program with a title), the display functions for panLang, crepLang and
    loopLang, [any_pan_prog_pp] and [pan_compile_tap], which the
    [--pancake --explore] compiler output uses.

    - [any_pan_prog]'s constructor [Cake] carries [backend_passes]'
      [any_prog], which is restricted to its [Word]/[Stack]/[Lab]
      constructors (see [backend_passes]); [any_pan_prog] and
      [any_pan_prog_pp] are therefore not tagged.
    - The languages ([panLang], [crepLang], [loopLang]) are required,
      not imported (their constructor names clash) and written qualified.
      [displayLang]'s constructors [String] and [List] shadow Rocq's and
      [misc]'s (the latter is written [misc.List]).
    - [pan_prog_to_display] (mutual with [pan_prog_to_display_handler]) is
      defined in HOL by well-founded recursion ([prog_size]), recursing on
      the elements of the flattened sequence [pan_seqs].  Here a structural
      [pan_prog_to_display_aux] returns, for a program [p], both its display
      and the displays of the elements of [append (pan_seqs p)]; HOL's
      equations are the tagged [pan_prog_to_display_def] theorem.  The same
      is done for [crep_prog_to_display] and [loop_prog_to_display].
    - Record updates use [backend]'s [set_*] helpers.

    Not ported: [compile_prog_eq_pan_to_target_all] and [compile_alt]
    (they need the backend's [from_word_0_thm]) and the local lemmas
    ([MAP2_MAP], [MAP_MAP2], [make_funcs_MAP], [MEM_append_*_seqs]). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.coretypes Require Import pair.
From Galette.HOL.src.combin Require combin.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.basis.pure Require Import mlstring mllist.
From Galette.cakeml.basis.pure Require mlsexp.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require wordLang word_to_stack stack_alloc stack_remove.
From Galette.cakeml.pancake Require panLang crepLang loopLang pan_simp pan_structs pan_globals
  pan_to_crep crep_inline crep_arith crep_to_loop loop_live loop_to_word.
From Galette.cakeml.compiler.backend Require Import backend backend_passes.
From Galette.cakeml.pancake Require Import pan_to_target.
From Galette.cakeml.compiler.backend Require Import presLang displayLang.
Open Scope N_scope.
Open Scope hol_string_scope.
Local Set Warnings "-register-all".

(** HOL's [any_pan_prog] with the restricted [any_prog] (see the header). *)
Inductive any_pan_prog (a : N) : Type :=
| Pan : list (panLang.decl a) -> any_pan_prog a
| Crep : list (mlstring * (list N * crepLang.prog a)) -> any_pan_prog a
| Loop : list (N * (list N * loopLang.prog a)) -> num_map mlstring -> any_pan_prog a
| Cake : any_prog a -> any_pan_prog a.
Arguments Pan {a} _.
Arguments Crep {a} _.
Arguments Loop {a} _ _.
Arguments Cake {a} _.

#[global] Instance any_pan_prog_inhabited {a} : Inhabited (any_pan_prog a) := Pan [].

(** ** The compiler with its intermediate programs *)

Section All.
Context {a : N}.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "pan_to_target_all_def" *)
Definition pan_to_target_all (asm_conf : asm_config a) (c : config) (prog : list (panLang.decl a))
    : list (mlstring * any_pan_prog a) * option (list word8 * (list (word a) * config)) :=
  let prog1 : list (panLang.decl a) :=
    match SPLITP (fun x => match x with
                           | panLang.Function fi => bool_decide (panLang.name fi = strlit "main")
                           | _ => false
                           end) prog with
    | ([], ys) => ys
    | (xs, []) => panLang.Function
                    {| panLang.name := strlit "main";
                       panLang.inline := false;
                       panLang.export := false;
                       panLang.params := [];
                       panLang.body := panLang.Return (panLang.Const (n2w 0));
                       panLang.fun_decl_return := panLang.One |}
                  :: xs
    | (xs, y :: ys) => y :: xs ++ ys
    end in
  let ps := [(strlit "initial pancake program", Pan prog1)] in
  let prog_a0 := pan_simp.compile_prog prog1 in
  let ps := ps ++ [(strlit "after pan_simp", Pan prog_a0)] in
  let prog_a1 := pan_structs.compile_top prog_a0 in
  let ps := ps ++ [(strlit "after pan_structs", Pan prog_a1)] in
  let prog_a := pan_globals.compile_top prog_a1 (strlit "main") in
  let ps := ps ++ [(strlit "after pan_globals", Pan prog_a)] in
  let prog_b0 := pan_to_crep.compile_to_crep prog_a in
  let ps := ps ++ [(strlit "after pan_to_crep", Crep prog_b0)] in
  let inl_fs_names := MAP FST (panLang.functions (FILTER panLang.inlinable prog_a)) in
  let prog_bi := crep_inline.compile_inl_top inl_fs_names prog_b0 in
  let ps := ps ++ [(strlit "after crep_inline", Crep prog_bi)] in
  let prog_b := MAP (fun '(n, (ps, e)) => (n, (ps, crep_arith.simp_prog e))) prog_bi in
  let ps := ps ++ [(strlit "after crep_arith", Crep prog_b)] in
  let fnums := GENLIST (fun n => n + crep_to_loop.first_name) (LENGTH prog_b) in
  let funcs := crep_to_loop.make_funcs prog_b in
  let target := ISA asm_conf in
  let comp := crep_to_loop.comp_func target funcs in
  let prog_b1 := MAP2 (fun n '(name, (params, body)) =>
                         (n, ((GENLIST combin.I ∘ LENGTH) params, comp params body)))
                      fnums prog_b in
  let prog_c := MAP (fun '(name, (params, body)) => (name, (params, loop_live.optimise body)))
                    prog_b1 in
  let prog2 := loop_to_word.compile_prog prog_c in
  let names : num_map mlstring :=
    fromAList (ZIP (sort N.ltb (MAP FST prog2),
                    strlit "generated_main" :: MAP FST (panLang.functions prog1))) in
  let names := union (fromAList (word_to_stack.stub_names tt ++
                                 stack_alloc.stub_names tt ++
                                 stack_remove.stub_names tt)) names in
  let ps := ps ++ [(strlit "after crep_to_loop", Loop prog_b1 names)] in
  let ps := ps ++ [(strlit "after loop_optimise", Loop prog_c names)] in
  let ps := ps ++ [(strlit "after loop_to_word", Cake (Word prog2 names))] in
  let c := set_exported (exports prog) c in
  let '(ps1, out) := from_word_0_all [] asm_conf c names prog2 in
  (ps ++ MAP (fun '(n, p) => (n, Cake p)) ps1, out).

End All.

(** ** panLang *)

(*! HOL "cakeml/pancake/pan_passesScript.sml" "opsize_to_display_def" *)
Definition opsize_to_display (s : panLang.opsize) : sExp :=
  match s with
  | panLang.Op8 => empty_item (strlit "byte")
  | panLang.Op16 => empty_item (strlit "word16")
  | panLang.OpW => empty_item (strlit "word")
  | panLang.Op32 => empty_item (strlit "word32")
  end.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "insert_es_def" *)
Definition insert_es (x : sExp) (xs : list sExp) : sExp :=
  match x with
  | String n => Item None n xs
  | x => x
  end.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "varkind_to_str_def" *)
Definition varkind_to_str (vk : panLang.varkind) : mlstring :=
  match vk with
  | panLang.Global => strlit "global"
  | panLang.Local => strlit "local"
  end.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "primop_to_display_def" *)
Definition primop_to_display (p : panLang.primop) : sExp :=
  match p with
  | panLang.AddCarry => String (strlit "AddCarry")
  end.

Section Pan.
Context {a : N}.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "pan_exp_to_display_def" *)
Fixpoint pan_exp_to_display (e : panLang.exp a) : sExp :=
  match e with
  | panLang.Const v => item_with_word (strlit "Const") v
  | panLang.Var vk n => Item None (strlit "Var") [String (varkind_to_str vk); String n]
  | panLang.BaseAddr => Item None (strlit "BaseAddr") []
  | panLang.TopAddr => Item None (strlit "TopAddr") []
  | panLang.BytesInWord => Item None (strlit "BytesInWord") []
  | panLang.Load shape exp2 =>
      Item None (strlit "MemLoad") [String (panLang.shape_to_str shape); pan_exp_to_display exp2]
  | panLang.Load32 exp2 => Item None (strlit "MemLoad32") [pan_exp_to_display exp2]
  | panLang.LoadByte exp2 => Item None (strlit "MemLoadByte") [pan_exp_to_display exp2]
  | panLang.RStruct xs => Item None (strlit "RawStruct") (MAP pan_exp_to_display xs)
  | panLang.NStruct nm fxs =>
      Item None (strlit "NamedStruct")
        (String nm :: MAP (fun '(f, x) =>
                             Tuple [String f; String (strlit ":="); pan_exp_to_display x]) fxs)
  | panLang.Cmp cmp x1 x2 =>
      insert_es (asm_cmp_to_display cmp) [pan_exp_to_display x1; pan_exp_to_display x2]
  | panLang.Op b xs => insert_es (asm_binop_to_display b) (MAP pan_exp_to_display xs)
  | panLang.Panop p xs =>
      match p with
      | panLang.Mul => Item None (strlit "Mul") (MAP pan_exp_to_display xs)
      end
  | panLang.RField n e => Item None (strlit "RawField") [num_to_display n; pan_exp_to_display e]
  | panLang.NField f e => Item None (strlit "NamedField") [String f; pan_exp_to_display e]
  | panLang.Shift sh e e' =>
      insert_es (shift_to_display sh) [pan_exp_to_display e; pan_exp_to_display e']
  end.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "dest_annot_def" *)
Definition dest_annot (p : panLang.prog a) : option (mlstring * mlstring) :=
  match p with
  | panLang.Annot k str => Some (k, str)
  | _ => None
  end.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "pan_seqs_def" *)
Fixpoint pan_seqs (z : panLang.prog a) : app_list (panLang.prog a) :=
  match z with
  | panLang.Seq x y =>
      match dest_annot x with
      | Some _ => misc.List [z]
      | _ => Append (pan_seqs x) (pan_seqs y)
      end
  | _ => misc.List [z]
  end.

(** [pan_prog_to_display_aux p] is the pair of [pan_prog_to_display p] and
    [MAP pan_prog_to_display (append (pan_seqs p))] (see the header). *)
Fixpoint pan_prog_to_display_aux (p : panLang.prog a) : sExp * list sExp :=
  let single (d : sExp) := (d, [d]) in
  match p with
  | panLang.Skip => single (empty_item (strlit "skip"))
  | panLang.ShMemLoad s vk v e =>
      single (Item None (strlit "shared_mem_load")
                [opsize_to_display s; String (varkind_to_str vk); String v;
                 pan_exp_to_display e])
  | panLang.ShMemStore s e1 e2 =>
      single (Item None (strlit "shared_mem_store")
                [opsize_to_display s; pan_exp_to_display e1; pan_exp_to_display e2])
  | panLang.ExtCall f e1 e2 e3 e4 =>
      single (Item None (strlit "ext_call")
                [String f; pan_exp_to_display e1; pan_exp_to_display e2;
                 pan_exp_to_display e3; pan_exp_to_display e4])
  | panLang.If e p1 p2 =>
      single (Item None (strlit "if")
                [pan_exp_to_display e;
                 fst (pan_prog_to_display_aux p1);
                 fst (pan_prog_to_display_aux p2)])
  | panLang.While e p =>
      single (Item None (strlit "while")
                [pan_exp_to_display e; fst (pan_prog_to_display_aux p)])
  | panLang.Dec n shape e p =>
      single (Item None (strlit "dec")
                [Tuple [String (strlit "local"); String (panLang.shape_to_str shape);
                        String n; String (strlit ":="); pan_exp_to_display e];
                 fst (pan_prog_to_display_aux p)])
  | panLang.Assign vk n exp =>
      single (Tuple [String (varkind_to_str vk); String n; String (strlit ":=");
                     pan_exp_to_display exp])
  | panLang.Primitive v pop es =>
      single (Tuple [String v; String (strlit ":=");
                     insert_es (primop_to_display pop) (MAP pan_exp_to_display es)])
  | panLang.Store e1 e2 =>
      single (Tuple [String (strlit "mem"); pan_exp_to_display e1;
                     String (strlit ":="); pan_exp_to_display e2])
  | panLang.Store32 e1 e2 =>
      single (Tuple [String (strlit "mem"); pan_exp_to_display e1;
                     String (strlit ":="); String (strlit "32bit"); pan_exp_to_display e2])
  | panLang.StoreByte e1 e2 =>
      single (Tuple [String (strlit "mem"); pan_exp_to_display e1;
                     String (strlit ":="); String (strlit "byte"); pan_exp_to_display e2])
  | panLang.Annot k str =>
      single (Item None (strlit "annot") [String (escape_str k); String (escape_str str)])
  | panLang.Tick => single (empty_item (strlit "tick"))
  | panLang.Break => single (empty_item (strlit "break"))
  | panLang.Continue => single (empty_item (strlit "continue"))
  | panLang.Return e => single (Item None (strlit "return") [pan_exp_to_display e])
  | panLang.Raise n e => single (Item None (strlit "raise") [String n; pan_exp_to_display e])
  | panLang.Seq prog1 prog2 =>
      let s1 := snd (pan_prog_to_display_aux prog1) in
      let s2 := snd (pan_prog_to_display_aux prog2) in
      let d := separate_lines (strlit "seq") (s1 ++ s2) in
      (d, match dest_annot prog1 with Some _ => [d] | None => s1 ++ s2 end)
  | panLang.Call ret_opt f args =>
      let handler (h : option (panLang.eid * (panLang.varname * panLang.prog a))) : sExp :=
        match h with
        | None => empty_item (strlit "no_handler")
        | Some (v1, (v2, p)) =>
            Item None (strlit "handler")
              [Tuple [String v1; String v2; fst (pan_prog_to_display_aux p)]]
        end in
      single
        match ret_opt with
        | None =>
            Item None (strlit "tail_call") [String f; Tuple (MAP pan_exp_to_display args)]
        | Some (None, h) =>
            Item None (strlit "call")
              [String f; Tuple (MAP pan_exp_to_display args); handler h]
        | Some (Some (vk, v), h) =>
            Tuple [String v; String (strlit ":=");
                   Item None (strlit "call")
                     [String f; Tuple (MAP pan_exp_to_display args); handler h]]
        end
  | panLang.DecCall v shape f args p =>
      single (Item None (strlit "dec")
                [Tuple [String (panLang.shape_to_str shape); String v; String (strlit ":=");
                        Item None (strlit "call")
                          [String f; Tuple (MAP pan_exp_to_display args)]];
                 fst (pan_prog_to_display_aux p)])
  end.

Definition pan_prog_to_display (p : panLang.prog a) : sExp := fst (pan_prog_to_display_aux p).

Definition pan_prog_to_display_handler
    (h : option (panLang.eid * (panLang.varname * panLang.prog a))) : sExp :=
  match h with
  | None => empty_item (strlit "no_handler")
  | Some (v1, (v2, p)) =>
      Item None (strlit "handler") [Tuple [String v1; String v2; pan_prog_to_display p]]
  end.

Lemma pan_prog_to_display_aux_snd : forall p,
  snd (pan_prog_to_display_aux p) = MAP pan_prog_to_display (append (pan_seqs p)).
Proof.
  induction p; try reflexivity.
  cbn [pan_prog_to_display_aux pan_seqs snd].
  destruct (dest_annot p1); [reflexivity|].
  rewrite IHp1, IHp2, (proj1 (append_thm _ _ [])), map_app; reflexivity.
Qed.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "pan_prog_to_display_def" *)
Theorem pan_prog_to_display_def :
  (pan_prog_to_display panLang.Skip = empty_item (strlit "skip")) /\
  (forall s vk v e, pan_prog_to_display (panLang.ShMemLoad s vk v e) =
     Item None (strlit "shared_mem_load")
       [opsize_to_display s; String (varkind_to_str vk); String v; pan_exp_to_display e]) /\
  (forall s e1 e2, pan_prog_to_display (panLang.ShMemStore s e1 e2) =
     Item None (strlit "shared_mem_store")
       [opsize_to_display s; pan_exp_to_display e1; pan_exp_to_display e2]) /\
  (forall f e1 e2 e3 e4, pan_prog_to_display (panLang.ExtCall f e1 e2 e3 e4) =
     Item None (strlit "ext_call")
       [String f; pan_exp_to_display e1; pan_exp_to_display e2;
        pan_exp_to_display e3; pan_exp_to_display e4]) /\
  (forall e p1 p2, pan_prog_to_display (panLang.If e p1 p2) =
     Item None (strlit "if")
       [pan_exp_to_display e; pan_prog_to_display p1; pan_prog_to_display p2]) /\
  (forall e p, pan_prog_to_display (panLang.While e p) =
     Item None (strlit "while") [pan_exp_to_display e; pan_prog_to_display p]) /\
  (forall n shape e p, pan_prog_to_display (panLang.Dec n shape e p) =
     Item None (strlit "dec")
       [Tuple [String (strlit "local"); String (panLang.shape_to_str shape);
               String n; String (strlit ":="); pan_exp_to_display e];
        pan_prog_to_display p]) /\
  (forall vk n exp, pan_prog_to_display (panLang.Assign vk n exp) =
     Tuple [String (varkind_to_str vk); String n; String (strlit ":=");
            pan_exp_to_display exp]) /\
  (forall v pop es, pan_prog_to_display (panLang.Primitive v pop es) =
     Tuple [String v; String (strlit ":=");
            insert_es (primop_to_display pop) (MAP pan_exp_to_display es)]) /\
  (forall e1 e2, pan_prog_to_display (panLang.Store e1 e2) =
     Tuple [String (strlit "mem"); pan_exp_to_display e1;
            String (strlit ":="); pan_exp_to_display e2]) /\
  (forall e1 e2, pan_prog_to_display (panLang.Store32 e1 e2) =
     Tuple [String (strlit "mem"); pan_exp_to_display e1;
            String (strlit ":="); String (strlit "32bit"); pan_exp_to_display e2]) /\
  (forall e1 e2, pan_prog_to_display (panLang.StoreByte e1 e2) =
     Tuple [String (strlit "mem"); pan_exp_to_display e1;
            String (strlit ":="); String (strlit "byte"); pan_exp_to_display e2]) /\
  (forall k str, pan_prog_to_display (panLang.Annot k str) =
     Item None (strlit "annot") [String (escape_str k); String (escape_str str)]) /\
  (pan_prog_to_display panLang.Tick = empty_item (strlit "tick")) /\
  (pan_prog_to_display panLang.Break = empty_item (strlit "break")) /\
  (pan_prog_to_display panLang.Continue = empty_item (strlit "continue")) /\
  (forall e, pan_prog_to_display (panLang.Return e) =
     Item None (strlit "return") [pan_exp_to_display e]) /\
  (forall n e, pan_prog_to_display (panLang.Raise n e) =
     Item None (strlit "raise") [String n; pan_exp_to_display e]) /\
  (forall prog1 prog2, pan_prog_to_display (panLang.Seq prog1 prog2) =
     let xs := append (Append (pan_seqs prog1) (pan_seqs prog2)) in
     separate_lines (strlit "seq") (MAP pan_prog_to_display xs)) /\
  (forall ret_opt f args, pan_prog_to_display (panLang.Call ret_opt f args) =
     match ret_opt with
     | None =>
         Item None (strlit "tail_call") [String f; Tuple (MAP pan_exp_to_display args)]
     | Some (None, handler) =>
         Item None (strlit "call")
           [String f; Tuple (MAP pan_exp_to_display args);
            pan_prog_to_display_handler handler]
     | Some (Some (vk, v), handler) =>
         Tuple [String v; String (strlit ":=");
                Item None (strlit "call")
                  [String f; Tuple (MAP pan_exp_to_display args);
                   pan_prog_to_display_handler handler]]
     end) /\
  (forall v shape f args p, pan_prog_to_display (panLang.DecCall v shape f args p) =
     Item None (strlit "dec")
       [Tuple [String (panLang.shape_to_str shape); String v; String (strlit ":=");
               Item None (strlit "call") [String f; Tuple (MAP pan_exp_to_display args)]];
        pan_prog_to_display p]) /\
  (pan_prog_to_display_handler None = empty_item (strlit "no_handler")) /\
  (forall v1 v2 p, pan_prog_to_display_handler (Some (v1, (v2, p))) =
     Item None (strlit "handler") [Tuple [String v1; String v2; pan_prog_to_display p]]).
Proof.
  repeat split; intros; try reflexivity.
  - unfold pan_prog_to_display at 1; cbn [pan_prog_to_display_aux fst].
    rewrite !pan_prog_to_display_aux_snd, (proj1 (append_thm _ _ [])), map_app.
    reflexivity.
Qed.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "pan_fun_to_display_def" *)
Definition pan_fun_to_display (decl : panLang.decl a) : sExp :=
  match decl with
  | panLang.Function fi =>
      Tuple [String (strlit "func"); String (panLang.shape_to_str (panLang.fun_decl_return fi));
             String (panLang.name fi);
             Tuple (MAP (fun '(s, shape) =>
                           Tuple [String s; String (strlit ":");
                                  String (panLang.shape_to_str shape)]) (panLang.params fi));
             pan_prog_to_display (panLang.body fi)]
  | panLang.Decl sh nm exp =>
      Tuple [String (strlit "global"); String (panLang.shape_to_str sh); String nm;
             String (strlit ":="); pan_exp_to_display exp]
  | panLang.Name nm flds =>
      Tuple [String (strlit "struct"); String nm;
             Tuple (MAP (fun '(fld, shape) =>
                           Tuple [String fld; String (strlit ":");
                                  String (panLang.shape_to_str shape)]) flds)]
  | panLang.ExnDecl nm sh =>
      Tuple [String (strlit "exception"); String nm; String (strlit ":");
             String (panLang.shape_to_str sh)]
  end.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "pan_to_strs_def" *)
Definition pan_to_strs (xs : list (panLang.decl a)) : app_list mlstring :=
  map_to_append
    (mlsexp.str_tree_to_strs double_newline ∘ display_to_str_tree ∘ pan_fun_to_display) xs.

End Pan.

(** ** crepLang *)

Section Crep.
Context {a : N}.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "crep_exp_to_display_def" *)
Fixpoint crep_exp_to_display (e : crepLang.exp a) : sExp :=
  match e with
  | crepLang.Const v => item_with_word (strlit "Const") v
  | crepLang.LoadGlob w => item_with_word (strlit "LoadGlob") w
  | crepLang.Var n => Item None (strlit "Var") [num_to_display n]
  | crepLang.BaseAddr => Item None (strlit "BaseAddr") []
  | crepLang.TopAddr => Item None (strlit "TopAddr") []
  | crepLang.Load exp2 => Item None (strlit "MemLoad") [crep_exp_to_display exp2]
  | crepLang.Load32 exp2 => Item None (strlit "MemLoad32") [crep_exp_to_display exp2]
  | crepLang.LoadByte exp2 => Item None (strlit "MemLoadByte") [crep_exp_to_display exp2]
  | crepLang.Cmp cmp x1 x2 =>
      insert_es (asm_cmp_to_display cmp) [crep_exp_to_display x1; crep_exp_to_display x2]
  | crepLang.Op b xs => insert_es (asm_binop_to_display b) (MAP crep_exp_to_display xs)
  | crepLang.Crepop p xs =>
      match p with
      | crepLang.Mul => Item None (strlit "Mul") (MAP crep_exp_to_display xs)
      end
  | crepLang.Shift sh e e' =>
      insert_es (shift_to_display sh) [crep_exp_to_display e; crep_exp_to_display e']
  end.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "crep_seqs_def" *)
Fixpoint crep_seqs (z : crepLang.prog a) : app_list (crepLang.prog a) :=
  match z with
  | crepLang.Seq x y => Append (crep_seqs x) (crep_seqs y)
  | _ => misc.List [z]
  end.

(** [crep_prog_to_display_aux p] is the pair of [crep_prog_to_display p]
    and [MAP crep_prog_to_display (append (crep_seqs p))]. *)
Fixpoint crep_prog_to_display_aux (p : crepLang.prog a) : sExp * list sExp :=
  let single (d : sExp) := (d, [d]) in
  match p with
  | crepLang.Skip => single (empty_item (strlit "skip"))
  | crepLang.ShMem mop v e =>
      let prefix :=
        match mop with
        | asm.Load => [String (strlit "load"); String (strlit "word")]
        | asm.Load8 => [String (strlit "load"); String (strlit "byte")]
        | asm.Load16 => [String (strlit "load"); String (strlit "word16")]
        | asm.Load32 => [String (strlit "load"); String (strlit "word32")]
        | asm.Store => [String (strlit "store"); String (strlit "word")]
        | asm.Store8 => [String (strlit "store"); String (strlit "byte")]
        | asm.Store16 => [String (strlit "store"); String (strlit "word16")]
        | asm.Store32 => [String (strlit "store"); String (strlit "word32")]
        end in
      single (Item None (strlit "shared_mem") (prefix ++ [num_to_display v; crep_exp_to_display e]))
  | crepLang.ExtCall f e1 e2 e3 e4 =>
      single (Item None (strlit "ext_call")
                [String f; num_to_display e1; num_to_display e2; num_to_display e3;
                 num_to_display e4])
  | crepLang.StoreGlob w e =>
      single (Item None (strlit "store_glob") [word_to_display w; crep_exp_to_display e])
  | crepLang.If e p1 p2 =>
      single (Item None (strlit "if")
                [crep_exp_to_display e; fst (crep_prog_to_display_aux p1);
                 fst (crep_prog_to_display_aux p2)])
  | crepLang.While e p =>
      single (Item None (strlit "while") [crep_exp_to_display e; fst (crep_prog_to_display_aux p)])
  | crepLang.Dec n e p =>
      single (Item None (strlit "dec")
                [Tuple [num_to_display n; String (strlit ":="); crep_exp_to_display e];
                 fst (crep_prog_to_display_aux p)])
  | crepLang.Assign n exp =>
      single (Tuple [num_to_display n; String (strlit ":="); crep_exp_to_display exp])
  | crepLang.Primitive lhss pop rhss =>
      single (Tuple [Tuple (MAP num_to_display lhss); String (strlit ":=");
                     insert_es (primop_to_display pop) (MAP num_to_display rhss)])
  | crepLang.Store e1 e2 =>
      single (Tuple [String (strlit "mem"); crep_exp_to_display e1;
                     String (strlit ":="); crep_exp_to_display e2])
  | crepLang.Store32 e1 e2 =>
      single (Tuple [String (strlit "mem"); crep_exp_to_display e1;
                     String (strlit ":="); String (strlit "32bit"); crep_exp_to_display e2])
  | crepLang.StoreByte e1 e2 =>
      single (Tuple [String (strlit "mem"); crep_exp_to_display e1;
                     String (strlit ":="); String (strlit "byte"); crep_exp_to_display e2])
  | crepLang.Tick => single (empty_item (strlit "tick"))
  | crepLang.Break n => single (item_with_num (strlit "break") n)
  | crepLang.Continue n => single (item_with_num (strlit "continue") n)
  | crepLang.Return es => single (Item None (strlit "return") (MAP crep_exp_to_display es))
  | crepLang.Raise w => single (item_with_word (strlit "raise") w)
  | crepLang.Seq prog1 prog2 =>
      let s := snd (crep_prog_to_display_aux prog1) ++ snd (crep_prog_to_display_aux prog2) in
      (separate_lines (strlit "seq") s, s)
  | crepLang.Call ret_opt f args =>
      let handler (h : option (word a * crepLang.prog a)) : sExp :=
        match h with
        | None => empty_item (strlit "no_handler")
        | Some (w, p) =>
            Item None (strlit "handler")
              [Tuple [word_to_display w; fst (crep_prog_to_display_aux p)]]
        end in
      single
        match ret_opt with
        | None =>
            Item None (strlit "tail_call") [String f; Tuple (MAP crep_exp_to_display args)]
        | Some ([], h) =>
            Item None (strlit "call")
              [String f; Tuple (MAP crep_exp_to_display args); handler h]
        | Some (vs, h) =>
            Tuple [Tuple (MAP num_to_display vs); String (strlit ":=");
                   Item None (strlit "call")
                     [String f; Tuple (MAP crep_exp_to_display args); handler h]]
        end
  end.

Definition crep_prog_to_display (p : crepLang.prog a) : sExp := fst (crep_prog_to_display_aux p).

Definition crep_prog_to_display_handler (h : option (word a * crepLang.prog a)) : sExp :=
  match h with
  | None => empty_item (strlit "no_handler")
  | Some (w, p) => Item None (strlit "handler") [Tuple [word_to_display w; crep_prog_to_display p]]
  end.

Lemma crep_prog_to_display_aux_snd : forall p,
  snd (crep_prog_to_display_aux p) = MAP crep_prog_to_display (append (crep_seqs p)).
Proof.
  induction p; try reflexivity.
  cbn [crep_prog_to_display_aux crep_seqs snd].
  rewrite IHp1, IHp2, (proj1 (append_thm _ _ [])), map_app; reflexivity.
Qed.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "crep_prog_to_display_def" *)
Theorem crep_prog_to_display_def :
  (crep_prog_to_display crepLang.Skip = empty_item (strlit "skip")) /\
  (forall mop v e, crep_prog_to_display (crepLang.ShMem mop v e) =
     let prefix :=
       match mop with
       | asm.Load => [String (strlit "load"); String (strlit "word")]
       | asm.Load8 => [String (strlit "load"); String (strlit "byte")]
       | asm.Load16 => [String (strlit "load"); String (strlit "word16")]
       | asm.Load32 => [String (strlit "load"); String (strlit "word32")]
       | asm.Store => [String (strlit "store"); String (strlit "word")]
       | asm.Store8 => [String (strlit "store"); String (strlit "byte")]
       | asm.Store16 => [String (strlit "store"); String (strlit "word16")]
       | asm.Store32 => [String (strlit "store"); String (strlit "word32")]
       end in
     Item None (strlit "shared_mem") (prefix ++ [num_to_display v; crep_exp_to_display e])) /\
  (forall f e1 e2 e3 e4, crep_prog_to_display (crepLang.ExtCall f e1 e2 e3 e4) =
     Item None (strlit "ext_call")
       [String f; num_to_display e1; num_to_display e2; num_to_display e3; num_to_display e4]) /\
  (forall w e, crep_prog_to_display (crepLang.StoreGlob w e) =
     Item None (strlit "store_glob") [word_to_display w; crep_exp_to_display e]) /\
  (forall e p1 p2, crep_prog_to_display (crepLang.If e p1 p2) =
     Item None (strlit "if")
       [crep_exp_to_display e; crep_prog_to_display p1; crep_prog_to_display p2]) /\
  (forall e p, crep_prog_to_display (crepLang.While e p) =
     Item None (strlit "while") [crep_exp_to_display e; crep_prog_to_display p]) /\
  (forall n e p, crep_prog_to_display (crepLang.Dec n e p) =
     Item None (strlit "dec")
       [Tuple [num_to_display n; String (strlit ":="); crep_exp_to_display e];
        crep_prog_to_display p]) /\
  (forall n exp, crep_prog_to_display (crepLang.Assign n exp) =
     Tuple [num_to_display n; String (strlit ":="); crep_exp_to_display exp]) /\
  (forall lhss pop rhss, crep_prog_to_display (crepLang.Primitive lhss pop rhss) =
     Tuple [Tuple (MAP num_to_display lhss); String (strlit ":=");
            insert_es (primop_to_display pop) (MAP num_to_display rhss)]) /\
  (forall e1 e2, crep_prog_to_display (crepLang.Store e1 e2) =
     Tuple [String (strlit "mem"); crep_exp_to_display e1;
            String (strlit ":="); crep_exp_to_display e2]) /\
  (forall e1 e2, crep_prog_to_display (crepLang.Store32 e1 e2) =
     Tuple [String (strlit "mem"); crep_exp_to_display e1;
            String (strlit ":="); String (strlit "32bit"); crep_exp_to_display e2]) /\
  (forall e1 e2, crep_prog_to_display (crepLang.StoreByte e1 e2) =
     Tuple [String (strlit "mem"); crep_exp_to_display e1;
            String (strlit ":="); String (strlit "byte"); crep_exp_to_display e2]) /\
  (crep_prog_to_display crepLang.Tick = empty_item (strlit "tick")) /\
  (forall n, crep_prog_to_display (crepLang.Break n) = item_with_num (strlit "break") n) /\
  (forall n, crep_prog_to_display (crepLang.Continue n) = item_with_num (strlit "continue") n) /\
  (forall es, crep_prog_to_display (crepLang.Return es) =
     Item None (strlit "return") (MAP crep_exp_to_display es)) /\
  (forall w, crep_prog_to_display (crepLang.Raise w) = item_with_word (strlit "raise") w) /\
  (forall prog1 prog2, crep_prog_to_display (crepLang.Seq prog1 prog2) =
     let xs := append (Append (crep_seqs prog1) (crep_seqs prog2)) in
     separate_lines (strlit "seq") (MAP crep_prog_to_display xs)) /\
  (forall ret_opt f args, crep_prog_to_display (crepLang.Call ret_opt f args) =
     match ret_opt with
     | None =>
         Item None (strlit "tail_call") [String f; Tuple (MAP crep_exp_to_display args)]
     | Some ([], handler) =>
         Item None (strlit "call")
           [String f; Tuple (MAP crep_exp_to_display args);
            crep_prog_to_display_handler handler]
     | Some (vs, handler) =>
         Tuple [Tuple (MAP num_to_display vs); String (strlit ":=");
                Item None (strlit "call")
                  [String f; Tuple (MAP crep_exp_to_display args);
                   crep_prog_to_display_handler handler]]
     end) /\
  (crep_prog_to_display_handler None = empty_item (strlit "no_handler")) /\
  (forall w p, crep_prog_to_display_handler (Some (w, p)) =
     Item None (strlit "handler") [Tuple [word_to_display w; crep_prog_to_display p]]).
Proof.
  repeat split; intros; try reflexivity.
  - unfold crep_prog_to_display at 1; cbn [crep_prog_to_display_aux fst].
    rewrite !crep_prog_to_display_aux_snd, (proj1 (append_thm _ _ [])), map_app.
    reflexivity.
  all: try (destruct ret_opt as [[[|v vs] [[w p]|]]|]; reflexivity).
Qed.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "crep_fun_to_display_def" *)
Definition crep_fun_to_display (f : mlstring * (list N * crepLang.prog a)) : sExp :=
  match f with
  | (nm, (args, body)) =>
      Tuple [String (strlit "func"); String nm; Tuple (MAP num_to_display args);
             crep_prog_to_display body]
  end.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "crep_to_strs_def" *)
Definition crep_to_strs (xs : list (mlstring * (list N * crepLang.prog a))) : app_list mlstring :=
  map_to_append
    (mlsexp.str_tree_to_strs double_newline ∘ display_to_str_tree ∘ crep_fun_to_display) xs.

End Crep.

(** ** loopLang *)

Section LoopL.
Context {a : N}.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "loop_exp_to_display_def" *)
Fixpoint loop_exp_to_display (e : loopLang.exp a) : sExp :=
  match e with
  | loopLang.Const v => item_with_word (strlit "Const") v
  | loopLang.Var n => item_with_num (strlit "Var") n
  | loopLang.BaseAddr => Item None (strlit "BaseAddr") []
  | loopLang.TopAddr => Item None (strlit "TopAddr") []
  | loopLang.Lookup st => item_with_word (strlit "Lookup") st
  | loopLang.Load exp2 => Item None (strlit "MemLoad") [loop_exp_to_display exp2]
  | loopLang.Op bop exs =>
      Item None (strlit "Op") (asm_binop_to_display bop :: MAP loop_exp_to_display exs)
  | loopLang.Shift sh exp exp' =>
      Item None (strlit "Shift")
        [shift_to_display sh; loop_exp_to_display exp; loop_exp_to_display exp']
  end.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "loop_seqs_def" *)
Fixpoint loop_seqs (z : loopLang.prog a) : app_list (loopLang.prog a) :=
  match z with
  | loopLang.Seq x y => Append (loop_seqs x) (loop_seqs y)
  | _ => misc.List [z]
  end.

(** [loop_prog_to_display_aux ns p] is the pair of [loop_prog_to_display ns p]
    and [MAP (loop_prog_to_display ns) (append (loop_seqs p))]. *)
Fixpoint loop_prog_to_display_aux (ns : num_map mlstring) (p : loopLang.prog a)
    : sExp * list sExp :=
  let single (d : sExp) := (d, [d]) in
  match p with
  | loopLang.Skip => single (empty_item (strlit "skip"))
  | loopLang.Arith a0 =>
      single
        match a0 with
        | loopLang.LLongMul n1 n2 n3 n4 => item_with_nums (strlit "long_mul") [n1; n2; n3; n4]
        | loopLang.LLongDiv n1 n2 n3 n4 n5 =>
            item_with_nums (strlit "long_div") [n1; n2; n3; n4; n5]
        | loopLang.LDiv n1 n2 n3 => item_with_nums (strlit "div") [n1; n2; n3]
        end
  | loopLang.Assign n exp =>
      single (Tuple [num_to_display n; String (strlit ":="); loop_exp_to_display exp])
  | loopLang.Primitive lhss pop rhss =>
      single (Tuple [Tuple (MAP num_to_display lhss); String (strlit ":=");
                     insert_es (primop_to_display pop) (MAP num_to_display rhss)])
  | loopLang.SetGlobal w exp =>
      single (Item None (strlit "set_global") [word_to_display w; loop_exp_to_display exp])
  | loopLang.Seq prog1 prog2 =>
      let s := snd (loop_prog_to_display_aux ns prog1) ++ snd (loop_prog_to_display_aux ns prog2) in
      (separate_lines (strlit "seq") s, s)
  | loopLang.FFI nm n1 n2 n3 n4 ms =>
      single (Item None (strlit "ffi")
                (string_imp nm :: MAP num_to_display [n1; n2; n3; n4] ++ [num_set_to_display ms]))
  | loopLang.Raise n => single (item_with_num (strlit "raise") n)
  | loopLang.Return ns0 => single (item_with_nums (strlit "return") ns0)
  | loopLang.Tick => single (empty_item (strlit "tick"))
  | loopLang.Break n => single (item_with_num (strlit "break") n)
  | loopLang.Continue n => single (item_with_num (strlit "continue") n)
  | loopLang.Fail => single (empty_item (strlit "fail"))
  | loopLang.Load32 n1 n2 => single (item_with_nums (strlit "load_32") [n1; n2])
  | loopLang.LoadByte n1 n2 => single (item_with_nums (strlit "load_byte") [n1; n2])
  | loopLang.Store32 n1 n2 => single (item_with_nums (strlit "store_32") [n1; n2])
  | loopLang.StoreByte n1 n2 => single (item_with_nums (strlit "store_byte") [n1; n2])
  | loopLang.LocValue n1 n2 =>
      single (Item None (strlit "loc_value") [String (attach_name ns (Some n1)); num_to_display n2])
  | loopLang.ShMem mop n e =>
      single (Tuple [String (strlit "share_mem"); asm_memop_to_display mop;
                     num_to_display n; loop_exp_to_display e])
  | loopLang.If cmp n reg p1 p2 ms =>
      single (Item None (strlit "if")
                [Tuple [asm_cmp_to_display cmp; num_to_display n; asm_reg_imm_to_display reg];
                 fst (loop_prog_to_display_aux ns p1); fst (loop_prog_to_display_aux ns p2);
                 num_set_to_display ms])
  | loopLang.Loop ms1 p ms2 =>
      single (Item None (strlit "loop")
                [num_set_to_display ms1; fst (loop_prog_to_display_aux ns p);
                 num_set_to_display ms2])
  | loopLang.Mark prog =>
      single (Item None (strlit "mark") [fst (loop_prog_to_display_aux ns prog)])
  | loopLang.Store exp n =>
      single (Tuple [String (strlit "mem"); loop_exp_to_display exp;
                     String (strlit ":="); num_to_display n])
  | loopLang.Call a0 b c d =>
      let handler (h : option (N * (loopLang.prog a * (loopLang.prog a * num_set)))) : sExp :=
        match h with
        | None => empty_item (strlit "no_handler")
        | Some (n1, (p1, (p2, ms))) =>
            Item None (strlit "handler")
              [Tuple [num_to_display n1; fst (loop_prog_to_display_aux ns p1);
                      fst (loop_prog_to_display_aux ns p2); num_set_to_display ms]]
        end in
      single
        match a0 with
        | None =>
            Item None (strlit "tail_call")
              [option_to_display (fun n => String (attach_name ns (Some n))) b;
               list_to_display num_to_display c]
        | Some (ns0, ms) =>
            Tuple [list_to_display num_to_display ns0;
                   String (strlit ":=");
                   Item None (strlit "call")
                     [option_to_display (fun n => String (attach_name ns (Some n))) b;
                      list_to_display num_to_display c;
                      num_set_to_display ms;
                      handler d]]
        end
  end.

Definition loop_prog_to_display (ns : num_map mlstring) (p : loopLang.prog a) : sExp :=
  fst (loop_prog_to_display_aux ns p).

Definition loop_prog_to_display_handler (ns : num_map mlstring)
    (h : option (N * (loopLang.prog a * (loopLang.prog a * num_set)))) : sExp :=
  match h with
  | None => empty_item (strlit "no_handler")
  | Some (n1, (p1, (p2, ms))) =>
      Item None (strlit "handler")
        [Tuple [num_to_display n1; loop_prog_to_display ns p1; loop_prog_to_display ns p2;
                num_set_to_display ms]]
  end.

Lemma loop_prog_to_display_aux_snd : forall ns p,
  snd (loop_prog_to_display_aux ns p) = MAP (loop_prog_to_display ns) (append (loop_seqs p)).
Proof.
  intros ns; induction p; try reflexivity.
  cbn [loop_prog_to_display_aux loop_seqs snd].
  rewrite IHp1, IHp2, (proj1 (append_thm _ _ [])), map_app; reflexivity.
Qed.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "loop_prog_to_display_def" *)
Theorem loop_prog_to_display_def :
  (forall ns, loop_prog_to_display ns loopLang.Skip = empty_item (strlit "skip")) /\
  (forall ns a0, loop_prog_to_display ns (loopLang.Arith a0) =
     match a0 with
     | loopLang.LLongMul n1 n2 n3 n4 => item_with_nums (strlit "long_mul") [n1; n2; n3; n4]
     | loopLang.LLongDiv n1 n2 n3 n4 n5 => item_with_nums (strlit "long_div") [n1; n2; n3; n4; n5]
     | loopLang.LDiv n1 n2 n3 => item_with_nums (strlit "div") [n1; n2; n3]
     end) /\
  (forall ns n exp, loop_prog_to_display ns (loopLang.Assign n exp) =
     Tuple [num_to_display n; String (strlit ":="); loop_exp_to_display exp]) /\
  (forall ns lhss pop rhss, loop_prog_to_display ns (loopLang.Primitive lhss pop rhss) =
     Tuple [Tuple (MAP num_to_display lhss); String (strlit ":=");
            insert_es (primop_to_display pop) (MAP num_to_display rhss)]) /\
  (forall ns w exp, loop_prog_to_display ns (loopLang.SetGlobal w exp) =
     Item None (strlit "set_global") [word_to_display w; loop_exp_to_display exp]) /\
  (forall ns prog1 prog2, loop_prog_to_display ns (loopLang.Seq prog1 prog2) =
     let xs := append (Append (loop_seqs prog1) (loop_seqs prog2)) in
     separate_lines (strlit "seq") (MAP (loop_prog_to_display ns) xs)) /\
  (forall ns nm n1 n2 n3 n4 ms, loop_prog_to_display ns (loopLang.FFI nm n1 n2 n3 n4 ms) =
     Item None (strlit "ffi")
       (string_imp nm :: MAP num_to_display [n1; n2; n3; n4] ++ [num_set_to_display ms])) /\
  (forall ns n, loop_prog_to_display ns (loopLang.Raise n) = item_with_num (strlit "raise") n) /\
  (forall ns ns0, loop_prog_to_display ns (loopLang.Return ns0) =
     item_with_nums (strlit "return") ns0) /\
  (forall ns, loop_prog_to_display ns loopLang.Tick = empty_item (strlit "tick")) /\
  (forall ns n, loop_prog_to_display ns (loopLang.Break n) = item_with_num (strlit "break") n) /\
  (forall ns n, loop_prog_to_display ns (loopLang.Continue n) =
     item_with_num (strlit "continue") n) /\
  (forall ns, loop_prog_to_display ns loopLang.Fail = empty_item (strlit "fail")) /\
  (forall ns n1 n2, loop_prog_to_display ns (loopLang.Load32 n1 n2) =
     item_with_nums (strlit "load_32") [n1; n2]) /\
  (forall ns n1 n2, loop_prog_to_display ns (loopLang.LoadByte n1 n2) =
     item_with_nums (strlit "load_byte") [n1; n2]) /\
  (forall ns n1 n2, loop_prog_to_display ns (loopLang.Store32 n1 n2) =
     item_with_nums (strlit "store_32") [n1; n2]) /\
  (forall ns n1 n2, loop_prog_to_display ns (loopLang.StoreByte n1 n2) =
     item_with_nums (strlit "store_byte") [n1; n2]) /\
  (forall ns n1 n2, loop_prog_to_display ns (loopLang.LocValue n1 n2) =
     Item None (strlit "loc_value") [String (attach_name ns (Some n1)); num_to_display n2]) /\
  (forall ns mop n e, loop_prog_to_display ns (loopLang.ShMem mop n e) =
     Tuple [String (strlit "share_mem"); asm_memop_to_display mop;
            num_to_display n; loop_exp_to_display e]) /\
  (forall ns cmp n reg p1 p2 ms, loop_prog_to_display ns (loopLang.If cmp n reg p1 p2 ms) =
     Item None (strlit "if")
       [Tuple [asm_cmp_to_display cmp; num_to_display n; asm_reg_imm_to_display reg];
        loop_prog_to_display ns p1; loop_prog_to_display ns p2; num_set_to_display ms]) /\
  (forall ns ms1 p ms2, loop_prog_to_display ns (loopLang.Loop ms1 p ms2) =
     Item None (strlit "loop")
       [num_set_to_display ms1; loop_prog_to_display ns p; num_set_to_display ms2]) /\
  (forall ns prog, loop_prog_to_display ns (loopLang.Mark prog) =
     Item None (strlit "mark") [loop_prog_to_display ns prog]) /\
  (forall ns exp n, loop_prog_to_display ns (loopLang.Store exp n) =
     Tuple [String (strlit "mem"); loop_exp_to_display exp;
            String (strlit ":="); num_to_display n]) /\
  (forall ns a0 b c d, loop_prog_to_display ns (loopLang.Call a0 b c d) =
     match a0 with
     | None =>
         Item None (strlit "tail_call")
           [option_to_display (fun n => String (attach_name ns (Some n))) b;
            list_to_display num_to_display c]
     | Some (ns0, ms) =>
         Tuple [list_to_display num_to_display ns0;
                String (strlit ":=");
                Item None (strlit "call")
                  [option_to_display (fun n => String (attach_name ns (Some n))) b;
                   list_to_display num_to_display c;
                   num_set_to_display ms;
                   loop_prog_to_display_handler ns d]]
     end) /\
  (forall ns, loop_prog_to_display_handler ns None = empty_item (strlit "no_handler")) /\
  (forall ns n1 p1 p2 ms, loop_prog_to_display_handler ns (Some (n1, (p1, (p2, ms)))) =
     Item None (strlit "handler")
       [Tuple [num_to_display n1; loop_prog_to_display ns p1; loop_prog_to_display ns p2;
               num_set_to_display ms]]).
Proof.
  repeat split; intros; try reflexivity.
  - unfold loop_prog_to_display at 1; cbn [loop_prog_to_display_aux fst].
    rewrite !loop_prog_to_display_aux_snd, (proj1 (append_thm _ _ [])), map_app.
    reflexivity.
  all: try (destruct a0 as [[ns0 ms]|]; [|reflexivity];
             destruct d as [[n1 [p1 [p2 ms']]]|]; reflexivity).
Qed.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "loop_fun_to_display_def" *)
Definition loop_fun_to_display (names : num_map mlstring)
    (f : N * (list N * loopLang.prog a)) : sExp :=
  match f with
  | (n, (args, body)) =>
      Tuple [String (strlit "func"); String (attach_name names (Some n));
             Tuple (MAP num_to_display args);
             loop_prog_to_display names body]
  end.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "loop_to_strs_def" *)
Definition loop_to_strs (names : num_map mlstring)
    (xs : list (N * (list N * loopLang.prog a))) : app_list mlstring :=
  map_to_append
    (mlsexp.str_tree_to_strs double_newline ∘ display_to_str_tree ∘ loop_fun_to_display names) xs.

End LoopL.

(** ** Printing and the tap *)

(** HOL's [any_pan_prog_pp] on the restricted [any_pan_prog] (untagged,
    see the header). *)
Definition any_pan_prog_pp {a : N} (x : any_pan_prog a) : app_list mlstring :=
  match x with
  | Pan p => pan_to_strs p
  | Crep p => crep_to_strs p
  | Loop p ns => loop_to_strs ns p
  | Cake p => any_prog_pp p
  end.

(*! HOL "cakeml/pancake/pan_passesScript.sml" "pan_compile_tap_def" *)
Definition pan_compile_tap {a : N} (asm_conf : asm_config a) (c : config)
    (p : list (panLang.decl a))
    : option (list word8 * (list (word a) * config)) * app_list mlstring :=
  if explore_flag (tap_conf c) then
    let '(ps, out) := pan_to_target_all asm_conf c p in
    (out, FOLDR (pp_with_title any_pan_prog_pp) Nil ps)
  else (compile_prog asm_conf c p, Nil).
