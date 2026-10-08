(** * CakeML [backend_passes]: the backend with every intermediate program

    Port of [cakeml/compiler/backend/backend_passesScript.sml], restricted
    to the part reached from Pancake: the lower backend from wordLang
    ([word_internal_all], [from_word_0_all], [from_word_all],
    [from_stack_all], [from_lab_all]), the printer [any_prog_pp] and
    [pp_with_title].  These are used by [pan_passes] for the compiler's
    [--explore] output.

    Deviation: HOL's datatype [any_prog] has the constructors [Source],
    [Flat], [Clos], [Bvl], [Bvi], [Data], [Word], [Stack], [Lab]; the first
    six carry programs of CakeML's source/flat/clos/bvl/bvi/data languages,
    which are not ported (they never occur on the Pancake path).  Here
    [any_prog] has only [Word], [Stack] and [Lab] (with HOL's argument
    types), so it and [any_prog_pp] are not tagged.

    The [*_all] functions are HOL's, but the configuration record updates
    use [backend]'s [set_*] helpers.  HOL's [x.f] on the [asm_config] is
    [f x].

    Not ported: [to_flat_all] ... [to_target_all], [from_data_all],
    [compile_tap] (the CakeML source pipeline) and the theorems
    ([to_*_thm], [from_*_thm], [number_of_passes], [compile_alt], ...). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require
  wordLang stackLang labLang word_simp word_inst word_alloc word_cse word_copy
  word_unreach word_remove word_to_word word_to_stack stack_rawcall stack_alloc
  stack_remove stack_names stack_to_lab lab_filter lab_to_target data_to_word
  bvl_to_bvi.
From Galette.cakeml.compiler.backend Require Import backend presLang.
Open Scope N_scope.
Open Scope hol_string_scope.

(** HOL's [any_prog] without the source ... data constructors (see the
    header). *)
Inductive any_prog (a : N) : Type :=
| Word : list (N * (N * wordLang.prog a)) -> num_map mlstring -> any_prog a
| Stack : list (N * stackLang.prog a) -> num_map mlstring -> any_prog a
| Lab : list (labLang.sec a) -> num_map mlstring -> any_prog a.
Arguments Word {a} _ _.
Arguments Stack {a} _ _.
Arguments Lab {a} _ _.

#[global] Instance any_prog_inhabited {a} : Inhabited (any_prog a) := Lab [] LN.

Section Passes.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/backend_passesScript.sml" "word_internal_all_def" *)
Definition word_internal_all (asm_conf : asm_config a) (ps : list (mlstring * any_prog a))
    (names : num_map mlstring) (p : list (N * (N * wordLang.prog a)))
    : list (N * (N * wordLang.prog a)) * list (mlstring * any_prog a) :=
  let two_reg_arith := two_reg_arith asm_conf in
  let p := MAP (fun '(name_num, (arg_count, prog)) =>
                  (name_num, (arg_count, word_simp.compile_exp prog))) p in
  let ps := ps ++ [(strlit "after word_simp", Word p names)] in
  let p := MAP (fun '(name_num, (arg_count, prog)) =>
                  (name_num, (arg_count,
                     word_inst.inst_select asm_conf (wordLang.max_var prog + 1) prog))) p in
  let ps := ps ++ [(strlit "after word_inst", Word p names)] in
  let p := MAP (fun '(name_num, (arg_count, prog)) =>
                  (name_num, (arg_count, word_alloc.full_ssa_cc_trans arg_count prog))) p in
  let ps := ps ++ [(strlit "after word_ssa", Word p names)] in
  let p := MAP (fun '(name_num, (arg_count, prog)) =>
                  (name_num, (arg_count, word_alloc.remove_dead_prog prog))) p in
  let ps := ps ++ [(strlit "after remove_dead in word_ssa", Word p names)] in
  let p := MAP (fun '(name_num, (arg_count, prog)) =>
                  (name_num, (arg_count, word_cse.word_common_subexp_elim prog))) p in
  let ps := ps ++ [(strlit "after word_cse", Word p names)] in
  let p := MAP (fun '(name_num, (arg_count, prog)) =>
                  (name_num, (arg_count, word_copy.copy_prop prog))) p in
  let ps := ps ++ [(strlit "after word_copy", Word p names)] in
  let p := MAP (fun '(name_num, (arg_count, prog)) =>
                  (name_num, (arg_count,
                     word_inst.three_to_two_reg_prog two_reg_arith prog))) p in
  let ps := ps ++ [(strlit "after three_to_two_reg from word_inst", Word p names)] in
  let p := MAP (fun '(name_num, (arg_count, prog)) =>
                  (name_num, (arg_count, word_unreach.remove_unreach prog))) p in
  let ps := ps ++ [(strlit "after word_unreach", Word p names)] in
  let p := MAP (fun '(name_num, (arg_count, prog)) =>
                  (name_num, (arg_count, word_alloc.remove_dead_prog prog))) p in
  let ps := ps ++ [(strlit "after remove_dead in word_alloc", Word p names)] in
  (p, ps).

(*! HOL "cakeml/compiler/backend/backend_passesScript.sml" "from_lab_all_def" *)
Definition from_lab_all (ps : list (mlstring * any_prog a)) (asm_conf : asm_config a)
    (c : config) (names : num_map mlstring) (p : labLang.prog a) (bm : list (word a))
    : list (mlstring * any_prog a) * option (list word8 * (list (word a) * config)) :=
  let p := lab_filter.filter_skip p in
  let ps := ps ++ [(strlit "after filter_skip", Lab p names)] in
  let p := lab_to_target.compile_lab asm_conf (lab_conf c) p in
  (ps, attach_bitmaps names c bm p).

(*! HOL "cakeml/compiler/backend/backend_passesScript.sml" "from_stack_all_def" *)
Definition from_stack_all (ps : list (mlstring * any_prog a)) (asm_conf : asm_config a)
    (c : config) (names : num_map mlstring) (p : list (N * stackLang.prog a))
    (bm : list (word a))
    : list (mlstring * any_prog a) * option (list word8 * (list (word a) * config)) :=
  let stack_conf := stack_conf c in
  let data_conf := data_conf c in
  let max_heap := 2 * data_to_word.max_heap_limit a (backend.data_conf c) - 1 in
  let sp := reg_count asm_conf - (LENGTH (avoid_regs asm_conf) + 3) in
  let offset := addr_offset asm_conf in
  let prog := stack_rawcall.compile p in
  let ps := ps ++ [(strlit "after stack_rawcall", Stack prog names)] in
  let prog := stack_alloc.compile data_conf prog in
  let ps := ps ++ [(strlit "after stack_alloc", Stack prog names)] in
  let prog := stack_remove.compile (stack_to_lab.jump stack_conf) offset
                (stack_to_lab.is_gen_gc (data_to_word.gc_kind data_conf))
                max_heap sp bvl_to_bvi.InitGlobals_location prog in
  let ps := ps ++ [(strlit "after stack_remove", Stack prog names)] in
  let prog := stack_names.compile (stack_to_lab.reg_names stack_conf) prog in
  let ps := ps ++ [(strlit "after stack_names", Stack prog names)] in
  let p := MAP stack_to_lab.prog_to_section prog in
  let ps := ps ++ [(strlit "after stack_to_lab", Lab p names)] in
  from_lab_all ps asm_conf c names p bm.

(*! HOL "cakeml/compiler/backend/backend_passesScript.sml" "from_word_all_def" *)
Definition from_word_all (ps : list (mlstring * any_prog a)) (asm_conf : asm_config a)
    (c : config) (names : num_map mlstring) (p : list (N * (N * wordLang.prog a)))
    : list (mlstring * any_prog a) * option (list word8 * (list (word a) * config)) :=
  let '(bm, (c', (fs, p))) :=
    word_to_stack.compile asm_conf (stack_to_lab.perf_calls (stack_conf c)) p in
  let ps := ps ++ [(strlit "after word_to_stack", Stack p names)] in
  let c := set_word_conf c' c in
  from_stack_all ps asm_conf c names p bm.

(*! HOL "cakeml/compiler/backend/backend_passesScript.sml" "from_word_0_all_def" *)
Definition from_word_0_all (ps : list (mlstring * any_prog a)) (asm_conf : asm_config a)
    (c : config) (names : num_map mlstring) (p : list (N * (N * wordLang.prog a)))
    : list (mlstring * any_prog a) * option (list word8 * (list (word a) * config)) :=
  let word_conf := word_to_word_conf c in
  let '(p, ps) := word_internal_all asm_conf ps names p in
  let reg_count := reg_count asm_conf - (5 + LENGTH (avoid_regs asm_conf)) in
  let alg := word_to_word.reg_alg word_conf in
  let '(n_oracles, col) := word_to_word.next_n_oracle (LENGTH p) (word_to_word.col_oracle word_conf) in
  let p := MAP (fun '((name_num, (arg_count, prog)), col_opt) =>
                  (name_num, (arg_count,
                    word_remove.remove_must_terminate
                      (word_alloc.word_alloc name_num asm_conf alg reg_count prog col_opt))))
               (ZIP (p, n_oracles)) in
  let ps := ps ++ [(strlit "after word_alloc (and remove_must_terminate)", Word p names)] in
  let c := set_word_to_word_conf (set_col_oracle col (word_to_word_conf c)) c in
  from_word_all ps asm_conf c names p.

End Passes.

(** HOL's [any_prog_pp] on the restricted [any_prog] (untagged, see the
    header). *)
Definition any_prog_pp {a : N} (p : any_prog a) : app_list mlstring :=
  match p with
  | Word p names => word_to_strs names p
  | Stack p names => stack_to_strs names p
  | Lab p names => lab_to_strs names p
  end.

(*! HOL "cakeml/compiler/backend/backend_passesScript.sml" "pp_with_title_def" *)
Definition pp_with_title {A} (pp : A -> app_list mlstring) (tp : mlstring * A)
    (acc : app_list mlstring) : app_list mlstring :=
  match tp with
  | (title, p) =>
      Append (misc.List [strlit "# "; title; strlit ["010"%char; "010"%char]])
        (Append (pp p) acc)
  end.
