(** * CakeML [backend]: the compiler backend configuration and lower passes

    Partial port of [cakeml/compiler/backend/backendScript.sml]: the
    [config] record, [attach_bitmaps], the lower part of the backend used by
    the Pancake compiler ([from_lab], [from_stack], [from_word],
    [from_word_0]), [ffinames_to_string_list], [set_oracle] and
    [prim_src_config] (as a value, see below).

    - HOL [c with f := v] is written with the [set_<f>] helpers below
      (Galette infrastructure) or by writing the record out.
    - [prim_src_config] is defined in HOL by running the source-to-flat
      compiler ([compile_decs]) on [prim_types_program]; that compiler (and
      CakeML's source language) is not ported.  Here [prim_src_config] is the
      evaluated value ([prim_src_config_eq] in HOL is [EVAL ``prim_src_config``];
      the value agrees with Flapjack's kernel-checked [primSrcConfig_eq]),
      built as HOL's [empty_config with <| next := ...; mod_env := ... |>];
      it is not tagged.  Only Pancake compilation is ported, where this field
      is carried along unused.
    - Not ported: the CakeML source pipeline ([compile], [to_flat] ...
      [to_target], [from_source] ... [from_data], [to_livesets*],
      [from_livesets], the incremental compiler [compile_inc_progs*],
      [prim_config], [backend_progs]) and all theorems. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics Require Import namespace.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require
  source_to_flat clos_to_bvl bvl_to_bvi data_to_word word_to_word word_to_stack
  stack_to_lab lab_to_target wordLang stackLang labLang.
From Galette.cakeml.compiler.backend Require Import presLang.
Open Scope N_scope.
Open Scope hol_string_scope.

(*! HOL "cakeml/compiler/backend/backendScript.sml" "config" *)
Record config : Type := {
  source_conf : source_to_flat.config;
  clos_conf : clos_to_bvl.config;
  bvl_conf : bvl_to_bvi.config;
  data_conf : data_to_word.config;
  word_to_word_conf : word_to_word.config;
  word_conf : word_to_stack.config;
  stack_conf : stack_to_lab.config;
  lab_conf : lab_to_target.config;
  symbols : list (mlstring * (N * N));
  tap_conf : tap_config;
  exported : list mlstring
}.

(** ** Record update helpers (Galette infrastructure) *)

Definition set_clos_conf (x : clos_to_bvl.config) (c : config) : config :=
  {| source_conf := source_conf c; clos_conf := x; bvl_conf := bvl_conf c;
     data_conf := data_conf c; word_to_word_conf := word_to_word_conf c;
     word_conf := word_conf c; stack_conf := stack_conf c; lab_conf := lab_conf c;
     symbols := symbols c; tap_conf := tap_conf c; exported := exported c |}.

Definition set_bvl_conf (x : bvl_to_bvi.config) (c : config) : config :=
  {| source_conf := source_conf c; clos_conf := clos_conf c; bvl_conf := x;
     data_conf := data_conf c; word_to_word_conf := word_to_word_conf c;
     word_conf := word_conf c; stack_conf := stack_conf c; lab_conf := lab_conf c;
     symbols := symbols c; tap_conf := tap_conf c; exported := exported c |}.

Definition set_data_conf (x : data_to_word.config) (c : config) : config :=
  {| source_conf := source_conf c; clos_conf := clos_conf c; bvl_conf := bvl_conf c;
     data_conf := x; word_to_word_conf := word_to_word_conf c;
     word_conf := word_conf c; stack_conf := stack_conf c; lab_conf := lab_conf c;
     symbols := symbols c; tap_conf := tap_conf c; exported := exported c |}.

Definition set_word_to_word_conf (x : word_to_word.config) (c : config) : config :=
  {| source_conf := source_conf c; clos_conf := clos_conf c; bvl_conf := bvl_conf c;
     data_conf := data_conf c; word_to_word_conf := x;
     word_conf := word_conf c; stack_conf := stack_conf c; lab_conf := lab_conf c;
     symbols := symbols c; tap_conf := tap_conf c; exported := exported c |}.

Definition set_word_conf (x : word_to_stack.config) (c : config) : config :=
  {| source_conf := source_conf c; clos_conf := clos_conf c; bvl_conf := bvl_conf c;
     data_conf := data_conf c; word_to_word_conf := word_to_word_conf c;
     word_conf := x; stack_conf := stack_conf c; lab_conf := lab_conf c;
     symbols := symbols c; tap_conf := tap_conf c; exported := exported c |}.

Definition set_stack_conf (x : stack_to_lab.config) (c : config) : config :=
  {| source_conf := source_conf c; clos_conf := clos_conf c; bvl_conf := bvl_conf c;
     data_conf := data_conf c; word_to_word_conf := word_to_word_conf c;
     word_conf := word_conf c; stack_conf := x; lab_conf := lab_conf c;
     symbols := symbols c; tap_conf := tap_conf c; exported := exported c |}.

Definition set_lab_conf (x : lab_to_target.config) (c : config) : config :=
  {| source_conf := source_conf c; clos_conf := clos_conf c; bvl_conf := bvl_conf c;
     data_conf := data_conf c; word_to_word_conf := word_to_word_conf c;
     word_conf := word_conf c; stack_conf := stack_conf c; lab_conf := x;
     symbols := symbols c; tap_conf := tap_conf c; exported := exported c |}.

Definition set_symbols (x : list (mlstring * (N * N))) (c : config) : config :=
  {| source_conf := source_conf c; clos_conf := clos_conf c; bvl_conf := bvl_conf c;
     data_conf := data_conf c; word_to_word_conf := word_to_word_conf c;
     word_conf := word_conf c; stack_conf := stack_conf c; lab_conf := lab_conf c;
     symbols := x; tap_conf := tap_conf c; exported := exported c |}.

Definition set_tap_conf (x : tap_config) (c : config) : config :=
  {| source_conf := source_conf c; clos_conf := clos_conf c; bvl_conf := bvl_conf c;
     data_conf := data_conf c; word_to_word_conf := word_to_word_conf c;
     word_conf := word_conf c; stack_conf := stack_conf c; lab_conf := lab_conf c;
     symbols := symbols c; tap_conf := x; exported := exported c |}.

Definition set_exported (x : list mlstring) (c : config) : config :=
  {| source_conf := source_conf c; clos_conf := clos_conf c; bvl_conf := bvl_conf c;
     data_conf := data_conf c; word_to_word_conf := word_to_word_conf c;
     word_conf := word_conf c; stack_conf := stack_conf c; lab_conf := lab_conf c;
     symbols := symbols c; tap_conf := tap_conf c; exported := x |}.

(** HOL [wc with col_oracle := col] on [word_to_word$config]. *)
Definition set_col_oracle (col : list (option (num_map N))) (wc : word_to_word.config)
    : word_to_word.config :=
  {| word_to_word.reg_alg := word_to_word.reg_alg wc; word_to_word.col_oracle := col |}.

(** ** Attaching the bitmaps and symbols *)

(*! HOL "cakeml/compiler/backend/backendScript.sml" "attach_bitmaps_def" *)
Definition attach_bitmaps {B C} (names : num_map mlstring) (c : config) (bm : C)
    (r : option (B * lab_to_target.config)) : option (B * (C * config)) :=
  match r with
  | Some (bytes, c') =>
      Some (bytes, (bm,
        set_symbols
          (MAP (fun '(n, (p, l)) => (lookup_any n names (strlit "NOTFOUND"), (p, l)))
               (lab_to_target.sec_pos_len c'))
          (set_lab_conf c' c)))
  | None => None
  end.

(** ** The lower backend *)

Section Lower.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/backendScript.sml" "from_lab_def" *)
Definition from_lab {C} (asm_conf : asm_config a) (c : config) (names : num_map mlstring)
    (p : labLang.prog a) (bm : C) : option (list word8 * (C * config)) :=
  attach_bitmaps names c bm
    (lab_to_target.compile asm_conf (lab_conf c) p).

(*! HOL "cakeml/compiler/backend/backendScript.sml" "from_stack_def" *)
Definition from_stack {C} (asm_conf : asm_config a) (c : config) (names : num_map mlstring)
    (p : list (N * stackLang.prog a)) (bm : C) : option (list word8 * (C * config)) :=
  let p := stack_to_lab.compile
    (stack_conf c) (data_conf c) (2 * data_to_word.max_heap_limit a (data_conf c) - 1)
    (reg_count asm_conf - (LENGTH (avoid_regs asm_conf) + 3))
    (addr_offset asm_conf) p in
  from_lab asm_conf c names (p : labLang.prog a) bm.

(*! HOL "cakeml/compiler/backend/backendScript.sml" "from_word_def" *)
Definition from_word (asm_conf : asm_config a) (c : config) (names : num_map mlstring)
    (p : list (N * (N * wordLang.prog a))) : option (list word8 * (list (word a) * config)) :=
  let '(bm, (c', (fs, p))) := word_to_stack.compile asm_conf (stack_to_lab.perf_calls (stack_conf c)) p in
  let c := set_word_conf c' c in
  from_stack asm_conf c names p bm.

(*! HOL "cakeml/compiler/backend/backendScript.sml" "from_word_0_def" *)
Definition from_word_0 (asm_conf : asm_config a) (c : config) (names : num_map mlstring)
    (p : list (N * (N * wordLang.prog a))) : option (list word8 * (list (word a) * config)) :=
  let '(col, prog) := word_to_word.compile (word_to_word_conf c) asm_conf p in
  let c := set_word_to_word_conf (set_col_oracle col (word_to_word_conf c)) c in
  from_word asm_conf c names prog.

End Lower.

(** ** FFI names *)

(*! HOL "cakeml/compiler/backend/backendScript.sml" "ffinames_to_string_list_def" *)
Fixpoint ffinames_to_string_list (l : list ffiname) : list mlstring :=
  match l with
  | [] => []
  | ExtCall s :: rest => s :: ffinames_to_string_list rest
  | SharedMem _ :: rest => ffinames_to_string_list rest
  end.

(*! HOL "cakeml/compiler/backend/backendScript.sml" "set_oracle_def" *)
Definition set_oracle (c : config) (oracle : list (option (num_map N))) : config :=
  set_word_to_word_conf (set_col_oracle oracle (word_to_word_conf c)) c.

(** ** [prim_src_config] (evaluated; see the header) *)

(** HOL [prim_src_config] after [EVAL] (untagged; see the header). *)
Definition prim_src_config : source_to_flat.config :=
  let c := source_to_flat.empty_config in
  {| source_to_flat.next := {| source_to_flat.vidx := 0; source_to_flat.tidx := 2;
                               source_to_flat.eidx := 4 |};
     source_to_flat.mod_env :=
       {| source_to_flat.c :=
            Bind [(strlit "::", (0, Some (1, [(0, 0); (0, 2)])));
                  (strlit "[]", (0, Some (1, [(0, 0); (0, 2)])));
                  (strlit "True", (1, Some (0, [(0, 0); (1, 0)])));
                  (strlit "False", (0, Some (0, [(0, 0); (1, 0)])));
                  (strlit "Subscript", (3, None));
                  (strlit "Div", (2, None));
                  (strlit "Chr", (1, None));
                  (strlit "Bind", (0, None))] [];
          source_to_flat.v := Bind [] [] |};
     source_to_flat.pattern_cfg := source_to_flat.pattern_cfg c;
     source_to_flat.envs := source_to_flat.envs c |}.
