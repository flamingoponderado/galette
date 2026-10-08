(** * CakeML [compiler]: the top-level compiler (Pancake path)

    Partial port of [cakeml/compiler/compilerScript.sml]: everything that
    the [cake] executable reaches for Pancake input ([--pancake]), on the
    RISC-V target.

    Ported (tagged when identical to HOL): [help_string], [compile_error],
    [find_next_newline], [safe_substring], [get_nth_line],
    [locs_to_string], [compile_pancake], [error_to_str], [is_error_msg],
    the command-line parsing ([parse_num] ... [extend_conf],
    [parse_top_config], [has_*_flag], [parse_pancake_feature]),
    [conf_ok_check], [format_compiler_result], [add_tap_output],
    [pancake_backend_conf], [compile_pancake_64].

    Deviations (untagged, documented at each declaration):
    - [parse_target_64]: HOL's selects one of the x64/arm8/mips/riscv
      backends (default x64).  Only RISC-V is ported, so the Galette version
      accepts [--target=riscv] only and reports every other choice
      (including the default) as a configuration error.
    - [full_compile_64] works on the basis library's file-system model
      ([add_stdout], [add_stderr], [fastForwardFD] over [IO_fs]), which is
      not ported.  [compiler_main] below follows the dispatch of the
      executable's [main] ([compiler64ProgScript.sml]) and of
      [full_compile_64] and returns the text written to stdout (as an
      [app_list]) and to stderr; the extracted OCaml driver
      ([extraction/galette_main.ml]) prints them and sets the exit code.
    - [current_build_info_str] is computed at HOL build time from [git],
      [poly] and the date; [current_build_info_str] here is Galette's own.

    Not ported (CakeML source language only): the compiler [config] record
    (inferencer configuration, ...), [print_option], [parse_sexp_input],
    [parse_cml_input], [compile], [compile_64], [compile_32],
    [parse_target_32], [compile_pancake_32], [full_compile_32].

    [find_next_newline] (termination measure [strlen s - n]) is defined
    with a fuel and [get_nth_line] (recursion on [k - 1]) with [num_rec];
    HOL's equations are the tagged [_def] theorems. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.coretypes Require Import pair option.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.string Require Import string.
From Galette.HOL.src.monad.more_monads Require errorMonad.
From Galette.HOL.examples.formal_languages.context_free Require Import location.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.basis.pure Require Import mlstring mlint.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From Galette.cakeml.compiler.parsing Require Import lexer_impl.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.encoders.riscv Require Import riscv_target.
From Galette.cakeml.compiler.backend Require
  clos_known clos_to_bvl bvl_to_bvi data_to_word word_to_word stack_to_lab lab_to_target.
From Galette.cakeml.compiler.backend Require Import backend_common presLang backend.
From Galette.cakeml.compiler.backend.riscv Require Import riscv_config export_riscv.
From Galette.cakeml.pancake Require panLang panStatic pan_passes.
From Galette.cakeml.pancake.parser Require panPtreeConversion.
From Galette.cakeml.pancake Require Import news.
Open Scope N_scope.
Open Scope hol_string_scope.
Open Scope mlstring_scope.

(** The newline character (HOL's [#"\n"]). *)
Definition NL : ascii := "010"%char.

(** ** Help and version text *)

(** HOL's [help_string_def]: the text of the [--help] string (from the SML
    quotation [help_string], without its first line break). *)
(*! HOL "cakeml/compiler/compilerScript.sml" "help_string_def" *)
Definition help_string : mlstring := strlit
"
Usage:  cake [OPTIONS] < input_file > output_file

The cake executable is usually invoked as shown above. The different
OPTIONS are described in the OPTIONS listing below.

One can also run the cake execuable as follows to print a listing of
the type of each top-level binding (including the bindings made in
the standard basis library).

Usage:  cake --types < input_file

One can invoke the cake executable to print this help message (--help)
or version information (--version) without an input_file:

Usage:  cake --version
Usage:  cake --help

OPTIONS:

  --repl        starts an interactive read-eval-print loop; all other
                flags are ignored, when the --repl flag is present

  --reg_alg=N   N is a natural number that specifies the register
                allocation algorithm to use:
                   0   - simple allocator, no spill heuristics
                   1   - simple allocator, spill heuristics
                   2   - IRC allocator, no spill heuristics (default)
                   3   - IRC allocator, spill heuristics
                   >=4 - linear scan allocator

  --gc=G        specifies garbage collector type; here G is one of:
                   none   - no garbage collector is used
                   simple - a non-generational Cheney (default)
                   genN   - a generational Cheney garbage collector is
                            used; the size of the nursery generation is
                            N machine words (example: --gc=gen5000)
                This option has no effect under --pancake; the Pancake
                compiler always uses gc=none.

  --target=T    specifies that compilation should produce code for target
                T, where T can be one of x64, arm8, mips, riscv for
                the 64-bit compiler; for the 32-bit compiler T can be
                one of arm7 and ag32.

  --sexp=B      B can be either true or false; here false means that the
                input will be parsed as normal CakeML concrete syntax;
                true means that the input is parsed as an s-expression.

  --print_sexp  causes the cake to print the given program in
                s-expression format; with this option, the compiler
                does not generate machine code.

  --exclude_prelude=B   here B can be either true or false; the default
                is false; setting this to true causes the compiler not
                to include the standard basis library.

  --skip_type_inference=B   here B can be either true or false; the
                default is false; true will make the compiler skip
                type inference. There are no gurantees of safety if
                the type inferencer is skipped.

  --explore     outputs intermediate forms of the compiled program

  --pancake     takes a pancake program as input

  --pancake_feature=T  here S can be any string denoting a Pancake feature tag.
                Prints true or false depending on whether this
                compiler binary supports feature T.
                Tags are documented in the NEWS.md in the pancake/
                subdirectory at code.cakeml.org

  --no_warn     silences pancake warning output

  --main_return=B   here B can be either true or false; the default is
                false; setting this to true causes the main function to
                return to caller instead of exit; this option is
                required to use multiple entry points with Pancake.

ADDITIONAL OPTIONS:

Optimisations can be configured using the following advanced options.

  --jump=B    true means conditional jumps to be used for out-of-stack checks
  --multi=B   true means clos_to_bvl phase is to use multi optimisation
  --known=B   true means clos_to_bvl phase is to use known optimisation
  --call=B    true means clos_to_bvl phase is to use call optimisation
  --tmc=B     true means tail-call modulo cons optimisations is used
  --tailrec=B true means attempts to turn functions into tail-rec form
  --inline_factor=N  threshold used by for ClosLang inliner in known pass
  --max_body_size=N  threshold used by for ClosLang inliner in known pass
  --max_app=N   max number of optimised curried applications in multi pass
  --inline_size=N  threshold used by for BVL inliner pass
  --exp_cut=N  threshold for when to cut large expression into subfunctions
  --split=B  true means main expression will be split at sequencing (;)
  --tag_bits=N  number of tag bits in every pointer
  --len_bits=N  number of length bits in every pointer
  --pad_bits=N  number of zero padding in every pointer
  --len_size=N  size of length field in heap object header cells
  --emit_empty_ffi=B  true emits debugging FFI calls for use with DEBUG_FFI
  --hash_size=N  size of the memoization table used by instruction encoder
  --perf_callgraph=B  unverified: emit C-stack shadowing so `perf record
                --call-graph fp` produces correct call graphs (x64 only)

".

(** HOL's [current_build_info_str] is computed when HOL builds the compiler
    (date, CakeML/HOL4/PolyML versions); Galette's is its own (untagged). *)
Definition current_build_info_str : mlstring :=
  strlit ("The CakeML compiler" ++ [NL] ++ [NL] ++ "Version details:" ++ [NL] ++
          "Galette: the Pancake compiler extracted from Rocq (RISC-V only)" ++ [NL]).

(** ** Errors *)

(*! HOL "cakeml/compiler/compilerScript.sml" "compile_error" *)
Inductive compile_error : Type :=
| ParseError : mlstring -> compile_error
| TypeError : mlstring -> compile_error
| AssembleError : compile_error
| ConfigError : mlstring -> compile_error
| StaticError : panStatic.staterr -> compile_error.

#[global] Instance compile_error_inhabited : Inhabited compile_error := AssembleError.

(** ** Source locations *)

Fixpoint find_next_newline_aux (fuel : nat) (n : N) (s : mlstring) : N :=
  match fuel with
  | O => n
  | S fuel =>
      if strlen s <=? n then n else
        if decide (strsub s n = NL) then n else
          find_next_newline_aux fuel (n + 1) s
  end.

(** HOL [find_next_newline] (see [find_next_newline_def]). *)
Definition find_next_newline (n : N) (s : mlstring) : N :=
  find_next_newline_aux (S (N.to_nat (strlen s - n))) n s.

Lemma find_next_newline_aux_fuel : forall f g n s,
  (N.to_nat (strlen s - n) < f)%nat -> (N.to_nat (strlen s - n) < g)%nat ->
  find_next_newline_aux f n s = find_next_newline_aux g n s.
Proof.
  induction f as [|f IH]; intros [|g] n s Hf Hg; try lia; cbn.
  destruct (strlen s <=? n) eqn:E; [reflexivity|].
  destruct (decide (strsub s n = NL)); [reflexivity|].
  apply N.leb_gt in E; apply IH; lia.
Qed.

(*! HOL "cakeml/compiler/compilerScript.sml" "find_next_newline_def" *)
Theorem find_next_newline_def : forall n s,
  find_next_newline n s =
    if strlen s <=? n then n else
      if decide (strsub s n = "010"%char) then n else
        find_next_newline (n + 1) s.
Proof.
  intros n s; unfold find_next_newline at 1; cbn [find_next_newline_aux].
  destruct (strlen s <=? n) eqn:E; [reflexivity|].
  change "010"%char with NL.
  destruct (decide (strsub s n = NL)); [reflexivity|].
  apply N.leb_gt in E; unfold find_next_newline; apply find_next_newline_aux_fuel; lia.
Qed.

(*! HOL "cakeml/compiler/compilerScript.sml" "safe_substring_def" *)
Definition safe_substring (s : mlstring) (n l : N) : mlstring :=
  let k := strlen s in
  if k <=? n then strlit "" else
    if n + l <=? k then
      substring s n l
    else substring s n (k - n).

(** HOL [get_nth_line] (see [get_nth_line_def]). *)
Definition get_nth_line (k : N) (s : mlstring) (n : N) : mlstring :=
  num_rec (fun n => let n1 := find_next_newline n s in safe_substring s n (n1 - n))
          (fun _ r n => r (find_next_newline n s + 1)) k n.

(*! HOL "cakeml/compiler/compilerScript.sml" "get_nth_line_def" *)
Theorem get_nth_line_def : forall k s n,
  get_nth_line k s n =
    if k =? 0 then
      let n1 := find_next_newline n s in
        safe_substring s n (n1 - n)
    else
      get_nth_line (k - 1) s (find_next_newline n s + 1).
Proof.
  intros k s n; unfold get_nth_line.
  destruct (k =? 0) eqn:E.
  - apply N.eqb_eq in E; subst; rewrite num_rec_0; reflexivity.
  - apply N.eqb_neq in E.
    replace k with (N.succ (k - 1)) at 1 by lia.
    rewrite num_rec_SUC; reflexivity.
Qed.

(*! HOL "cakeml/compiler/compilerScript.sml" "locs_to_string_def" *)
Definition locs_to_string (input : mlstring) (l : option locs) : mlstring :=
  match l with
  | None => implode "unknown location"
  | Some (Locs startl endl) =>
      match startl with
      | POSN r c =>
          let line := get_nth_line r input 0 in
          let len := strlen line in
          let stop :=
            match endl with POSN r1 c1 => if r1 =? r then c1 else len | _ => len end in
          let underline :=
            concat (REPLICATE c (strlit " ") ++ REPLICATE ((stop - c) + 1) (strlit [CHR 94])) in
          concat [strlit "line "; num_to_str (r + 1); strlit [NL; NL];
                  line; strlit [NL];
                  underline; strlit [NL]]
      | _ => implode "unknown location"
      end
  end.

(** ** Compiling Pancake *)

Section CompilePancake.
Context {a : N}.

(*! HOL "cakeml/compiler/compilerScript.sml" "compile_pancake_def" *)
Definition compile_pancake (asm_conf : asm_config a) (c : config) (input : string)
    : exc (list word8 * (list (word a) * config)) compile_error *
      (app_list mlstring * list compile_error) :=
  let _ := empty_ffi (strlit "finished: start up") in
  match panPtreeConversion.parse_topdecs_to_ast input with
  | inr errs =>
      (M_failure (ParseError (concat
         (MAP (fun '(msg, loc) => concat [msg; strlit " at ";
                                          locs_to_string (implode input) (Some loc); strlit [NL]])
              errs))), (Nil, []))
  | inl funs =>
      match panStatic.static_check funs with
      | (errorMonad.error e, warns) => (M_failure (StaticError e), (Nil, MAP StaticError warns))
      | (errorMonad.return_ tt, warns) =>
          let _ := empty_ffi (strlit "finished: lexing and parsing") in
          match pan_passes.pan_compile_tap asm_conf c funs with
          | (None, td) => (M_failure AssembleError, (td, MAP StaticError warns))
          | (Some (bytes, (data, c)), td) =>
              (M_success (bytes, (data, c)), (td, MAP StaticError warns))
          end
      end
  end.

End CompilePancake.

(** ** Printing errors *)

(*! HOL "cakeml/compiler/compilerScript.sml" "error_to_str_def" *)
Definition error_to_str (e : compile_error) : mlstring :=
  match e with
  | ParseError s =>
      concat [strlit ("### ERROR: parse error" ++ [NL]); s; strlit [NL]]
  | TypeError s =>
      (* if the first char in the message is a newline char then it isn't an error *)
      if (if strlen s =? 0 then true else
          if decide (strsub s 0 = NL) then false else true) then
        concat [strlit ("### ERROR: type error" ++ [NL]); s; strlit [NL]]
      else s
  | ConfigError s => concat [strlit ("### ERROR: config error" ++ [NL]); s; strlit [NL]]
  | AssembleError => strlit ("### ERROR: assembly error" ++ [NL])
  | StaticError e =>
      match e with
      | panStatic.ScopeErr s => concat [strlit ("### ERROR: scope error" ++ [NL]); s; strlit [NL]]
      | panStatic.WarningErr s => concat [strlit ("# WARNING:" ++ [NL]); s; strlit [NL]]
      | panStatic.GenErr s => concat [strlit ("### ERROR: static error" ++ [NL]); s; strlit [NL]]
      | panStatic.ShapeErr s => concat [strlit ("### ERROR: shape error" ++ [NL]); s; strlit [NL]]
      end
  end.

(*! HOL "cakeml/compiler/compilerScript.sml" "is_error_msg_def" *)
Definition is_error_msg (x : mlstring) : bool := isPrefix (strlit "###") x.

(** ** Command-line parsing *)

(*! HOL "cakeml/compiler/compilerScript.sml" "parse_num_def" *)
Definition parse_num (str : mlstring) : option N :=
  let str := explode str in
  if EVERY isDigit str
  then Some (num_from_dec_string_alt str)
  else None.

(*! HOL "cakeml/compiler/compilerScript.sml" "parse_bool_def" *)
Definition parse_bool (str : mlstring) : option bool :=
  if decide (str = strlit "true") then Some true
  else if decide (str = strlit "false") then Some false
  else None.

(*! HOL "cakeml/compiler/compilerScript.sml" "print_bool_def" *)
Definition print_bool (b : bool) : mlstring := if b then strlit "true" else strlit "false".

(*! HOL "cakeml/compiler/compilerScript.sml" "find_str_def" *)
Fixpoint find_str (flag : mlstring) (l : list mlstring) : option mlstring :=
  match l with
  | [] => None
  | x :: xs =>
      if isPrefix flag x then
        Some (extract x (strlen flag) None)
      else
        find_str flag xs
  end.

(*! HOL "cakeml/compiler/compilerScript.sml" "find_strs_def" *)
Fixpoint find_strs (flag : mlstring) (l : list mlstring) : list mlstring :=
  match l with
  | [] => []
  | x :: xs =>
      if isPrefix flag x then
        extract x (strlen flag) None :: find_strs flag xs
      else
        find_strs flag xs
  end.

(*! HOL "cakeml/compiler/compilerScript.sml" "find_bool_def" *)
Definition find_bool (flag : mlstring) (ls : list mlstring) (default : bool) : bool + mlstring :=
  match find_str flag ls with
  | None => inl default
  | Some rest =>
      match parse_bool rest with
      | Some b => inl b
      | None => inr (concat [strlit "Unable to parse as bool: "; rest; strlit " for flag: "; flag])
      end
  end.

(*! HOL "cakeml/compiler/compilerScript.sml" "find_num_def" *)
Definition find_num (flag : mlstring) (ls : list mlstring) (default : N) : N + mlstring :=
  match find_str flag ls with
  | None => inl default
  | Some rest =>
      match parse_num rest with
      | Some n => inl n
      | None => inr (concat [strlit "Unable to parse as num: "; rest; strlit " for flag: "; flag])
      end
  end.

(*! HOL "cakeml/compiler/compilerScript.sml" "get_err_str_def" *)
Definition get_err_str {A} (x : A + mlstring) : mlstring :=
  match x with
  | inl n => strlit ""
  | inr n => concat [n; strlit [NL]]
  end.

(*! HOL "cakeml/compiler/compilerScript.sml" "parse_num_list_def" *)
Fixpoint parse_num_list (l : list mlstring) : list N + mlstring :=
  match l with
  | [] => inl []
  | x :: xs =>
      match parse_num x with
      | None => inr (concat [strlit "Unable to parse as num: "; x])
      | Some n =>
          match parse_num_list xs with
          | inr s => inr s
          | inl ns => inl (n :: ns)
          end
      end
  end.

(*! HOL "cakeml/compiler/compilerScript.sml" "comma_tokens_def" *)
Fixpoint comma_tokens (acc : list mlstring) (xs : string) (l : string) : list mlstring :=
  match l with
  | [] => if NULL xs then acc else acc ++ [implode xs]
  | c :: cs =>
      if decide (c = ","%char) then
        comma_tokens (acc ++ if NULL xs then [] else [implode xs]) [] cs
      else
        comma_tokens acc (xs ++ [c]) cs
  end.

(*! HOL "cakeml/compiler/compilerScript.sml" "parse_nums_def" *)
Definition parse_nums (str : mlstring) : list N + mlstring :=
  parse_num_list (comma_tokens [] [] (explode str)).

(*! HOL "cakeml/compiler/compilerScript.sml" "parse_clos_conf_def" *)
Definition parse_clos_conf (ls : list mlstring) (clos : clos_to_bvl.config)
    : clos_to_bvl.config + mlstring :=
  let multi := find_bool (strlit "--multi=") ls (clos_to_bvl.do_mti clos) in
  let known := find_bool (strlit "--known=") ls (IS_SOME (clos_to_bvl.known_conf clos)) in
  let inline_factor := find_num (strlit "--inline_factor=") ls clos_known.default_inline_factor in
  let call := find_bool (strlit "--call=") ls (clos_to_bvl.do_call clos) in
  let maxapp := find_num (strlit "--max_app=") ls (clos_to_bvl.max_app clos) in
  match multi, known, inline_factor, call, maxapp with
  | inl m, inl k, inl i, inl c, inl n =>
      if k then
        (let max_body_size :=
           find_num (strlit "--max_body_size=") ls (clos_known.default_max_body_size n i) in
         match max_body_size with
         | inl x =>
             inl {| clos_to_bvl.next_loc := clos_to_bvl.next_loc clos;
                    clos_to_bvl.start := clos_to_bvl.start clos;
                    clos_to_bvl.do_mti := m;
                    clos_to_bvl.known_conf := Some (clos_known.mk_config x i);
                    clos_to_bvl.do_call := c;
                    clos_to_bvl.call_state := clos_to_bvl.call_state clos;
                    clos_to_bvl.max_app := n |}
         | _ => inr (concat [get_err_str max_body_size])
         end)
      else
        inl {| clos_to_bvl.next_loc := clos_to_bvl.next_loc clos;
               clos_to_bvl.start := clos_to_bvl.start clos;
               clos_to_bvl.do_mti := m;
               clos_to_bvl.known_conf := None;
               clos_to_bvl.do_call := c;
               clos_to_bvl.call_state := clos_to_bvl.call_state clos;
               clos_to_bvl.max_app := n |}
  | _, _, _, _, _ =>
      inr (concat [get_err_str multi;
                   get_err_str known;
                   get_err_str inline_factor;
                   get_err_str call;
                   get_err_str maxapp])
  end.

(*! HOL "cakeml/compiler/compilerScript.sml" "parse_bvl_conf_def" *)
Definition parse_bvl_conf (ls : list mlstring) (bvl : bvl_to_bvi.config)
    : bvl_to_bvi.config + mlstring :=
  let inlinesz := find_num (strlit "--inline_size=") ls (bvl_to_bvi.inline_size_limit bvl) in
  let expcut := find_num (strlit "--exp_cut=") ls (bvl_to_bvi.exp_cut bvl) in
  let tmc := find_bool (strlit "--tmc=") ls (bvl_to_bvi.do_tmc bvl) in
  let tailrec := find_bool (strlit "--tailrec=") ls (bvl_to_bvi.do_tailrec bvl) in
  let splitmain := find_bool (strlit "--split=") ls (bvl_to_bvi.split_main_at_seq bvl) in
  match inlinesz, expcut, splitmain, tmc, tailrec with
  | inl i, inl e, inl m, inl do_tmc, inl do_tailrec =>
      inl {| bvl_to_bvi.inline_size_limit := i;
             bvl_to_bvi.exp_cut := e;
             bvl_to_bvi.split_main_at_seq := m;
             bvl_to_bvi.next_name1 := bvl_to_bvi.next_name1 bvl;
             bvl_to_bvi.next_name2 := bvl_to_bvi.next_name2 bvl;
             bvl_to_bvi.next_name3 := bvl_to_bvi.next_name3 bvl;
             bvl_to_bvi.do_tailrec := do_tailrec;
             bvl_to_bvi.do_tmc := do_tmc;
             bvl_to_bvi.inlines := bvl_to_bvi.inlines bvl;
             bvl_to_bvi.bvi_inlines := bvl_to_bvi.bvi_inlines bvl |}
  | _, _, _, _, _ =>
      inr (concat [get_err_str inlinesz;
                   get_err_str expcut;
                   get_err_str splitmain;
                   get_err_str tmc;
                   get_err_str tailrec])
  end.

(*! HOL "cakeml/compiler/compilerScript.sml" "parse_wtw_conf_def" *)
Definition parse_wtw_conf (ls : list mlstring) (wtw : word_to_word.config)
    : word_to_word.config + mlstring :=
  let regalg := find_num (strlit "--reg_alg=") ls (word_to_word.reg_alg wtw) in
  match regalg with
  | inl r => inl {| word_to_word.reg_alg := r; word_to_word.col_oracle := word_to_word.col_oracle wtw |}
  | inr s => inr (get_err_str regalg)
  end.

(*! HOL "cakeml/compiler/compilerScript.sml" "parse_gc_def" *)
Definition parse_gc (ls : list mlstring) (default : data_to_word.gc_kind_ty)
    : data_to_word.gc_kind_ty + mlstring :=
  match find_str (strlit "--gc=") ls with
  | None => inl default
  | Some rest =>
      if decide (rest = strlit "none") then inl data_to_word.gc_kind_None
      else if decide (rest = strlit "simple") then inl data_to_word.Simple
      else if isPrefix (strlit "gen") rest then
        match parse_nums (extract rest (strlen (strlit "gen")) None) with
        | inl ls => inl (data_to_word.Generational ls)
        | inr s => inr (concat [strlit "Error parsing GenGC argument: "; s])
        end
      else inr (concat [strlit "Unrecognized GC option: "; rest])
  end.

(*! HOL "cakeml/compiler/compilerScript.sml" "parse_pancake_feature_def" *)
Definition parse_pancake_feature (ls : list mlstring) : option mlstring :=
  match find_str (strlit "--pancake_feature=") ls with
  | None => None
  | Some rest => Some rest
  end.

(** HOL's [conf_ok_check (:'a) c] (HOL's [shift (:'a)] is [word_shift]). *)
(*! HOL "cakeml/compiler/compilerScript.sml" "conf_ok_check_def" *)
Definition conf_ok_check (a : N) (c : data_to_word.config) : Prop :=
  data_to_word.shift_length c < dimindex a /\
  word_shift a <= data_to_word.shift_length c /\ data_to_word.len_size c <> 0 /\
  data_to_word.len_size c + 7 < dimindex a.

(*! HOL "cakeml/compiler/compilerScript.sml" "parse_data_conf_def" *)
Definition parse_data_conf (ls : list mlstring) (data : data_to_word.config)
    : data_to_word.config + mlstring :=
  let tag_bits := find_num (strlit "--tag_bits=") ls (data_to_word.tag_bits data) in
  let len_bits := find_num (strlit "--len_bits=") ls (data_to_word.len_bits data) in
  let pad_bits := find_num (strlit "--pad_bits=") ls (data_to_word.pad_bits data) in
  let len_size := find_num (strlit "--len_size=") ls (data_to_word.len_size data) in
  let empty_FFI := find_bool (strlit "--emit_empty_ffi=") ls (data_to_word.call_empty_ffi data) in
  let gc := parse_gc ls (data_to_word.gc_kind data) in
  match tag_bits, len_bits, pad_bits, len_size, gc, empty_FFI with
  | inl tb, inl lb, inl pb, inl ls, inl gc, inl empty_FFI =>
      (* TODO: check conf_ok here and raise error if violated *)
      inl {| data_to_word.tag_bits := tb;
             data_to_word.len_bits := lb;
             data_to_word.pad_bits := pb;
             data_to_word.len_size := ls;
             data_to_word.has_div := data_to_word.has_div data;
             data_to_word.has_longdiv := data_to_word.has_longdiv data;
             data_to_word.has_fp_ops := data_to_word.has_fp_ops data;
             data_to_word.has_fp_tern := data_to_word.has_fp_tern data;
             data_to_word.be := data_to_word.be data;
             data_to_word.call_empty_ffi := empty_FFI;
             data_to_word.gc_kind := gc |}
  | _, _, _, _, _, _ =>
      inr (concat [get_err_str tag_bits;
                   get_err_str len_bits;
                   get_err_str pad_bits;
                   get_err_str len_size;
                   get_err_str gc;
                   get_err_str empty_FFI])
  end.

(*! HOL "cakeml/compiler/compilerScript.sml" "parse_stack_conf_def" *)
Definition parse_stack_conf (ls : list mlstring) (stack : stack_to_lab.config)
    : stack_to_lab.config + mlstring :=
  let jump := find_bool (strlit "--jump=") ls (stack_to_lab.jump stack) in
  let perf := find_bool (strlit "--perf_callgraph=") ls (stack_to_lab.perf_calls stack) in
  match jump, perf with
  | inl j, inl p =>
      inl {| stack_to_lab.reg_names := stack_to_lab.reg_names stack;
             stack_to_lab.jump := j; stack_to_lab.perf_calls := p |}
  | inr s, _ => inr s
  | _, inr s => inr s
  end.

(*! HOL "cakeml/compiler/compilerScript.sml" "parse_tap_conf_def" *)
Definition parse_tap_conf (ls : list mlstring) (stack : tap_config) : tap_config + mlstring :=
  inl {| explore_flag := MEM (strlit "--explore") ls |}.

(*! HOL "cakeml/compiler/compilerScript.sml" "parse_lab_conf_def" *)
Definition parse_lab_conf (ls : list mlstring) (lab : lab_to_target.config)
    : lab_to_target.config + mlstring :=
  let hs := find_num (strlit "--hash_size=") ls (lab_to_target.hash_size lab) in
  match hs with
  | inl r =>
      inl {| lab_to_target.labels := lab_to_target.labels lab;
             lab_to_target.sec_pos_len := lab_to_target.sec_pos_len lab;
             lab_to_target.pos := lab_to_target.pos lab;
             lab_to_target.init_clock := lab_to_target.init_clock lab;
             lab_to_target.ffi_names := lab_to_target.ffi_names lab;
             lab_to_target.shmem_extra := lab_to_target.shmem_extra lab;
             lab_to_target.hash_size := r |}
  | inr s => inr s
  end.

(*! HOL "cakeml/compiler/compilerScript.sml" "extend_conf_def" *)
Definition extend_conf (ls : list mlstring) (conf : config) : config + mlstring :=
  let clos := parse_clos_conf ls (clos_conf conf) in
  let bvl := parse_bvl_conf ls (bvl_conf conf) in
  let wtw := parse_wtw_conf ls (word_to_word_conf conf) in
  let data := parse_data_conf ls (data_conf conf) in
  let stack := parse_stack_conf ls (stack_conf conf) in
  let tap := parse_tap_conf ls (tap_conf conf) in
  let lab := parse_lab_conf ls (lab_conf conf) in
  match clos, bvl, wtw, data, stack, tap, lab with
  | inl clos, inl bvl, inl wtw, inl data, inl stack, inl tap, inl lab =>
      inl {| source_conf := source_conf conf;
             clos_conf := clos;
             bvl_conf := bvl;
             data_conf := data;
             word_to_word_conf := wtw;
             word_conf := word_conf conf;
             stack_conf := stack;
             lab_conf := lab;
             symbols := symbols conf;
             tap_conf := tap;
             exported := exported conf |}
  | _, _, _, _, _, _, _ =>
      inr (concat [get_err_str clos;
                   get_err_str bvl;
                   get_err_str wtw;
                   get_err_str data;
                   get_err_str stack;
                   get_err_str tap;
                   get_err_str lab])
  end.

(** The type of the target-specific exporters ([riscv_export]). *)
Definition exporter : Type :=
  list mlstring -> list word8 -> list word64 -> list (mlstring * (N * N)) ->
  list mlstring -> bool -> bool -> app_list mlstring.

(** HOL [parse_target_64] (untagged, see the header): only the RISC-V
    branch is ported; every other choice, including the default ([x64]
    when no [--target=] is given), is a configuration error. *)
Definition parse_target_64 (ls : list mlstring)
    : (config * (exporter * asm_config 64)) + mlstring :=
  match find_str (strlit "--target=") ls with
  | None => inr (strlit "No --target= given: only --target=riscv is supported by Galette (CakeML's default is x64)")
  | Some rest =>
      if decide (rest = strlit "riscv") then inl (riscv_backend_config, (riscv_export, riscv_config))
      else if bool_decide (rest = strlit "x64") || bool_decide (rest = strlit "arm8") || bool_decide (rest = strlit "mips")
      then inr (concat [strlit "Unsupported 64-bit target option (Galette supports only riscv): "; rest])
      else inr (concat [strlit "Unrecognized 64-bit target option: "; rest])
  end.

(*! HOL "cakeml/compiler/compilerScript.sml" "parse_top_config_def" *)
Definition parse_top_config (ls : list mlstring)
    : (bool * (bool * (bool * (bool * (bool * (bool * bool)))))) + mlstring :=
  let sexp := find_bool (strlit "--sexp=") ls false in
  let prelude := find_bool (strlit "--exclude_prelude=") ls false in
  let typeinference := find_bool (strlit "--skip_type_inference=") ls false in
  let sexpprint := MEM (strlit "--print_sexp") ls in
  let onlyprinttypes := MEM (strlit "--types") ls in
  let nowarnings := MEM (strlit "--no_warn") ls in
  let mainreturn := find_bool (strlit "--main_return=") ls false in
  match sexp, prelude, typeinference, mainreturn with
  | inl sexp, inl prelude, inl typeinference, inl mainreturn =>
      inl (sexp, (prelude, (typeinference, (onlyprinttypes, (sexpprint, (mainreturn, nowarnings))))))
  | _, _, _, _ => inr (concat [
                   get_err_str sexp;
                   get_err_str prelude;
                   get_err_str typeinference;
                   get_err_str mainreturn])
  end.

(*! HOL "cakeml/compiler/compilerScript.sml" "has_version_flag_def" *)
Definition has_version_flag (ls : list mlstring) : bool := MEM (strlit "--version") ls.

(*! HOL "cakeml/compiler/compilerScript.sml" "has_help_flag_def" *)
Definition has_help_flag (ls : list mlstring) : bool := MEM (strlit "--help") ls.

(*! HOL "cakeml/compiler/compilerScript.sml" "has_pancake_flag_def" *)
Definition has_pancake_flag (ls : list mlstring) : bool := MEM (strlit "--pancake") ls.

(*! HOL "cakeml/compiler/compilerScript.sml" "format_compiler_result_def" *)
Definition format_compiler_result {a : N}
    (bytes_export : list ffiname -> list word8 -> list (word a) -> app_list mlstring)
    (r : exc (list word8 * (list (word a) * config)) compile_error)
    : app_list mlstring * mlstring :=
  match r with
  | M_failure err => (List [], error_to_str err)
  | M_success (bytes, (data, c)) =>
      (bytes_export (the [] (lab_to_target.ffi_names (lab_conf c))) bytes data, implode "")
  end.

(*! HOL "cakeml/compiler/compilerScript.sml" "add_tap_output_def" *)
Definition add_tap_output (td out : app_list mlstring) : app_list mlstring :=
  if decide (td = Nil) then out else td.

(*! HOL "cakeml/compiler/compilerScript.sml" "pancake_backend_conf_def" *)
Definition pancake_backend_conf (c : config) : config :=
  set_data_conf
    {| data_to_word.tag_bits := data_to_word.tag_bits (data_conf c);
       data_to_word.len_bits := data_to_word.len_bits (data_conf c);
       data_to_word.pad_bits := data_to_word.pad_bits (data_conf c);
       data_to_word.len_size := data_to_word.len_size (data_conf c);
       data_to_word.has_div := data_to_word.has_div (data_conf c);
       data_to_word.has_longdiv := data_to_word.has_longdiv (data_conf c);
       data_to_word.has_fp_ops := data_to_word.has_fp_ops (data_conf c);
       data_to_word.has_fp_tern := data_to_word.has_fp_tern (data_conf c);
       data_to_word.be := data_to_word.be (data_conf c);
       data_to_word.call_empty_ffi := data_to_word.call_empty_ffi (data_conf c);
       data_to_word.gc_kind := data_to_word.gc_kind_None |} c.

(** HOL's [compile_pancake_64]; tagged since its text is HOL's, but note
    that it calls the RISC-V-only [parse_target_64] above. *)
(*! HOL "cakeml/compiler/compilerScript.sml" "compile_pancake_64_def" *)
Definition compile_pancake_64 (cl : list mlstring) (input : string)
    : app_list mlstring * mlstring :=
  let confexp := parse_target_64 cl in
  match confexp with
  | inr err => (List [], error_to_str (ConfigError err))
  | inl (conf, (export, aconf)) =>
      let topconf := parse_top_config cl in
      match topconf with
      | inr err => (List [], error_to_str (ConfigError err))
      | inl (sexp, (prelude, (typeinfer, (onlyprinttypes, (sexpprint, (mainret, nowarn)))))) =>
          let ext_conf := extend_conf cl conf in
          match ext_conf with
          | inr err =>
              (List [], error_to_str (ConfigError (get_err_str ext_conf)))
          | inl ext_conf =>
              let ext_conf := pancake_backend_conf ext_conf in
              match compile_pancake aconf ext_conf input with
              | (M_failure err, (td, warns)) =>
                  (List [], concat (MAP error_to_str (err :: (if nowarn then [] else warns))))
              | (M_success (bytes, (data, c)), (td, warns)) =>
                  (add_tap_output td
                    (export (backend.ffinames_to_string_list
                      (the [] (lab_to_target.ffi_names (lab_conf c)))) bytes data (symbols c)
                      (exported c) mainret true),
                   concat (MAP error_to_str (if nowarn then [] else warns)))
              end
          end
      end
  end.

(** ** The executable's entry point (untagged, see the header)

    [compiler_main cl inp] is what [cake] writes to stdout (an [app_list],
    printed in order) and to stderr, following [full_compile_64] and the
    [main] function of [compiler64ProgScript.sml].  The CakeML (non-Pancake)
    compiler is not ported: without [--pancake] the result is a
    configuration error.  The caller exits with a nonzero code (after
    printing "Program exited with nonzero exit code.") when
    [is_error_msg] holds of the stderr text. *)
Definition compiler_main (cl : list mlstring) (inp : string) : app_list mlstring * mlstring :=
  if has_help_flag cl then
    (List [help_string], strlit "")
  else if has_version_flag cl then
    (List [current_build_info_str], strlit "")
  else
    match parse_pancake_feature cl with
    | Some rest => (List [print_bool (query_news rest)], strlit "")
    | None =>
        if has_pancake_flag cl then
          compile_pancake_64 cl inp
        else
          (List [], error_to_str (ConfigError
            (strlit "Galette compiles Pancake only: the --pancake flag is required")))
    end.
