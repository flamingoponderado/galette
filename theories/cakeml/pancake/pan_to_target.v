(** * Pancake [pan_to_target]: compiler from Pancake to machine code

    Port of [cakeml/pancake/pan_to_targetScript.sml] ([exports],
    [compile_prog]).  Not ported: [compile_prog_eq] (a restatement through
    [from_word_0]). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.coretypes Require Import pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.basis.pure Require Import mlstring mllist.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require wordLang word_to_word word_to_stack stack_alloc
  stack_remove.
From Galette.cakeml.compiler.backend Require Import backend.
From Galette.cakeml.pancake Require Import panLang.
From Galette.cakeml.pancake Require pan_to_word.
Open Scope N_scope.
Open Scope hol_string_scope.

Section PanToTarget.
Context {a : N}.

(*! HOL "cakeml/pancake/pan_to_targetScript.sml" "exports_def" *)
Fixpoint exports (l : list (decl a)) : list mlstring :=
  match l with
  | Function fi :: ds => if export fi then name fi :: exports ds else exports ds
  | _ :: ds => exports ds
  | [] => []
  end.

(*! HOL "cakeml/pancake/pan_to_targetScript.sml" "compile_prog_def" *)
Definition compile_prog (asm_conf : asm_config a) (c : config) (prog : list (decl a))
    : option (list word8 * (list (word a) * config)) :=
  (* Ensure either user-written main or new main that does nothing is first in func list *)
  let prog1 : list (decl a) :=
    match SPLITP (fun x => match x with
                           | Function fi => bool_decide (name fi = strlit "main")
                           | _ => false
                           end) prog with
    | ([], ys) => ys
    | (xs, []) => Function
                    {| name := strlit "main";
                       inline := false;
                       export := false;
                       params := [];
                       body := Return (Const (n2w 0));
                       fun_decl_return := One |}
                  :: xs
    | (xs, y :: ys) => y :: xs ++ ys
    end in
  (* Compiler passes *)
  let prog2 := pan_to_word.compile_prog (ISA asm_conf) prog1 in
  let '(col, prog3) := word_to_word.compile (word_to_word_conf c) asm_conf prog2 in
  let c := set_word_to_word_conf (set_col_oracle col (word_to_word_conf c)) c in
  (* Add user functions to name mapping *)
  let names : num_map mlstring :=
    fromAList (ZIP (sort N.ltb (MAP FST prog2), (* func numbers *)
                    strlit "generated_main" ::
                    MAP FST (functions prog1) (* func names *))) in
  (* Add stubs to name mapping *)
  let names := union (fromAList (word_to_stack.stub_names tt ++
    stack_alloc.stub_names tt ++ stack_remove.stub_names tt)) names in
  (* Add exported functions to *)
  let c := set_exported (exports prog) c in
  from_word asm_conf c names prog3.

End PanToTarget.
