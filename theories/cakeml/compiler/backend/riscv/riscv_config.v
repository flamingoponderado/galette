(** * CakeML [riscv_config]: the compiler configuration for RISC-V

    Port of [cakeml/compiler/backend/riscv/riscv_configScript.sml].

    HOL splices the [EVAL]uated [clos_to_bvl$default_config] and
    [bvl_to_bvi$default_config] into [riscv_backend_config_def]; here the
    constants themselves are used (they evaluate to the same values).  HOL's
    [riscv_names_def] is restated as the evaluated tree by a [compute]
    rebind of the same name; the definition here is the original
    composition of [insert]s. *)

From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.compiler.backend Require
  source_to_flat clos_to_bvl bvl_to_bvi data_to_word word_to_word word_to_stack
  stack_to_lab lab_to_target.
From Galette.cakeml.compiler.backend Require Import presLang backend.
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/riscv/riscv_configScript.sml" "riscv_names_def" 10 *)
Definition riscv_names : num_map N :=
  (insert 0 1 ∘
   insert 1 10 ∘
   insert 2 11 ∘
   insert 3 12 ∘
   insert 4 13 ∘
   insert 10 27 ∘
   insert 11 28 ∘
   insert 12 29 ∘
   insert 13 30 ∘
   insert 27 0 ∘
   insert 28 2 ∘
   insert 29 3 ∘
   insert 30 4) LN.

(*! HOL "cakeml/compiler/backend/riscv/riscv_configScript.sml" "riscv_backend_config_def" *)
Definition riscv_backend_config : config :=
  {| source_conf := prim_src_config;
     clos_conf := clos_to_bvl.default_config;
     bvl_conf := bvl_to_bvi.default_config;
     data_conf :=
       {| data_to_word.tag_bits := 4; data_to_word.len_bits := 4;
          data_to_word.pad_bits := 2; data_to_word.len_size := 32;
          data_to_word.has_div := true; data_to_word.has_longdiv := false;
          data_to_word.has_fp_ops := false; data_to_word.has_fp_tern := false;
          data_to_word.be := false; data_to_word.call_empty_ffi := false;
          data_to_word.gc_kind := data_to_word.Simple |};
     word_to_word_conf :=
       {| word_to_word.reg_alg := 3; word_to_word.col_oracle := [] |};
     word_conf :=
       {| word_to_stack.bitmaps_length := 0; word_to_stack.stack_frame_size := LN |};
     stack_conf :=
       {| stack_to_lab.jump := false; stack_to_lab.reg_names := riscv_names;
          stack_to_lab.perf_calls := false |};
     lab_conf :=
       {| lab_to_target.pos := 0; lab_to_target.ffi_names := None;
          lab_to_target.labels := LN; lab_to_target.sec_pos_len := [];
          lab_to_target.init_clock := 5; lab_to_target.hash_size := 104729;
          lab_to_target.shmem_extra := [] |};
     symbols := [];
     tap_conf := default_tap_config;
     exported := [] |}.
