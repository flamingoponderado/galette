(** * CakeML [word_to_word]: the wordLang-internal pass pipeline

    A port of [compiler/backend/word_to_wordScript.sml]: word_simp,
    inst_select, SSA, remove_dead, word_cse, copy_prop, three-to-two,
    remove_unreach, remove_dead, word_alloc, remove_must_terminate.
    HOL tuples nest to the right ([(name_num, arg_count, prog)] is
    [(name_num, (arg_count, prog))]).  Not ported: [compile_alt] (a
    restatement used for bootstrap translation). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.coretypes Require Import pair.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import wordLang word_alloc word_remove word_simp
  word_cse word_unreach word_copy word_inst.
Open Scope N_scope.
Open Scope hol_string_scope.

(*! HOL "cakeml/compiler/backend/word_to_wordScript.sml" "config" *)
Record config : Type := mk_config {
  reg_alg : N;
  col_oracle : list (option (num_map N))
}.

(*! HOL "cakeml/compiler/backend/word_to_wordScript.sml" "compile_single_def" *)
Definition compile_single {a} (two_reg_arith : bool) (reg_count alg : N) (c : asm_config a)
    (p : (N * (N * prog a)) * option (num_map N)) : N * (N * prog a) :=
  let '((name_num, (arg_count, prog)), col_opt) := p in
  let prog := word_simp.compile_exp prog in
  let maxv := max_var prog + 1 in
  let inst_prog := inst_select c maxv prog in
  let ssa_prog := full_ssa_cc_trans arg_count inst_prog in
  let rm_ssa_prog := remove_dead_prog ssa_prog in
  let cse_prog := word_common_subexp_elim rm_ssa_prog in
  let cp_prog := copy_prop cse_prog in
  let two_prog := three_to_two_reg_prog two_reg_arith cp_prog in
  let unreach_prog := remove_unreach two_prog in
  let rm_prog := remove_dead_prog unreach_prog in
  let reg_prog := word_alloc name_num c alg reg_count rm_prog col_opt in
  (name_num, (arg_count, reg_prog)).

(*! HOL "cakeml/compiler/backend/word_to_wordScript.sml" "full_compile_single_def" *)
Definition full_compile_single {a} (two_reg_arith : bool) (reg_count alg : N) (c : asm_config a)
    (p : (N * (N * prog a)) * option (num_map N)) : N * (N * prog a) :=
  let '(name_num, (arg_count, reg_prog)) := compile_single two_reg_arith reg_count alg c p in
  (name_num, (arg_count, remove_must_terminate reg_prog)).

(*! HOL "cakeml/compiler/backend/word_to_wordScript.sml" "next_n_oracle_def" *)
Definition next_n_oracle (n : N) (col : list (option (num_map N)))
    : list (option (num_map N)) * list (option (num_map N)) :=
  if n <=? LENGTH col then (TAKE n col, DROP n col)
  else (REPLICATE n None, []).

(*! HOL "cakeml/compiler/backend/word_to_wordScript.sml" "compile_def" *)
Definition compile {a} (word_conf : config) (asm_conf : asm_config a)
    (progs : list (N * (N * prog a)))
    : list (option (num_map N)) * list (N * (N * prog a)) :=
  let '(two_reg_arith, reg_count) :=
    (asm.two_reg_arith asm_conf, asm.reg_count asm_conf - (5 + LENGTH (avoid_regs asm_conf))) in
  let '(n_oracles, col) := next_n_oracle (LENGTH progs) word_conf.(col_oracle) in
  let progs := ZIP (progs, n_oracles) in
  (col, MAP (full_compile_single two_reg_arith reg_count word_conf.(reg_alg) asm_conf) progs).

(*! HOL "cakeml/compiler/backend/word_to_wordScript.sml" "full_compile_single_for_eval_def" *)
Definition full_compile_single_for_eval {a} (two_reg_arith : bool) (reg_count alg : N)
    (c : asm_config a) (p : (N * (N * prog a)) * option (num_map N)) : N * (N * prog a) :=
  let '((name_num, (arg_count, prog)), col_opt) := p in
  let prog := word_simp.compile_exp prog in
  let _ := empty_ffi (strlit "finished: word_simp") in
  let maxv := max_var prog + 1 in
  let inst_prog := inst_select c maxv prog in
  let _ := empty_ffi (strlit "finished: word_inst") in
  let ssa_prog := full_ssa_cc_trans arg_count inst_prog in
  let _ := empty_ffi (strlit "finished: word_ssa") in
  let rm_ssa_prog := remove_dead_prog ssa_prog in
  let _ := empty_ffi (strlit "finished: word_remove_dead after word_ssa") in
  let cse_prog := word_common_subexp_elim rm_ssa_prog in
  let _ := empty_ffi (strlit "finished: word_cse") in
  let cp_prog := copy_prop cse_prog in
  let _ := empty_ffi (strlit "finished: word_copy") in
  let two_prog := three_to_two_reg_prog two_reg_arith cp_prog in
  let _ := empty_ffi (strlit "finished: word_two_reg") in
  let unreach_prog := remove_unreach two_prog in
  let _ := empty_ffi (strlit "finished: word_unreach") in
  let rm_prog := remove_dead_prog unreach_prog in
  let _ := empty_ffi (strlit "finished: word_remove_dead") in
  let reg_prog := word_alloc name_num c alg reg_count rm_prog col_opt in
  let _ := empty_ffi (strlit "finished: word_alloc") in
  let rmt_prog := remove_must_terminate reg_prog in
  let _ := empty_ffi (strlit "finished: word_remove") in
  (name_num, (arg_count, rmt_prog)).

(*! HOL "cakeml/compiler/backend/word_to_wordScript.sml" "full_compile_single_for_eval_eq" *)
Theorem full_compile_single_for_eval_eq : forall {a} two_reg_arith reg_count alg (c : asm_config a) p,
  full_compile_single two_reg_arith reg_count alg c p =
  full_compile_single_for_eval two_reg_arith reg_count alg c p.
Proof. intros a t r al c [[n [ac p]] co]; reflexivity. Qed.
