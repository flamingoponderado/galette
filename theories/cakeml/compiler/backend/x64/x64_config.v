(** * CakeML [x64_config]: the compiler configuration for x86-64

    Port of [cakeml/compiler/backend/x64/x64_configScript.sml].

    HOL splices the [EVAL]uated [clos_to_bvl$default_config] and
    [bvl_to_bvi$default_config] into [x64_backend_config_def]; here the
    constants themselves are used (they evaluate to the same values).  HOL's
    [x64_names_def] is restated as the evaluated tree by a [compute] rebind of
    the same name; the definition here is the original composition of
    [insert]s.

    The machine-level halves of the x64 backend (the L3 x86-64 model,
    [x64_target] and [x64_encoder_correct]) are not ported yet; this file
    only fixes the compiler configuration, which does not depend on them.
    See [docs/PROGRESS.md]. *)

From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.compiler.backend Require
  source_to_flat clos_to_bvl bvl_to_bvi data_to_word word_to_word word_to_stack
  stack_to_lab lab_to_target.
From Galette.cakeml.compiler.backend Require Import presLang backend.
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/x64/x64_configScript.sml" "x64_names_def" 10 *)
Definition x64_names : num_map N :=
  (* 16 regs, must avoid 4 and 5, names:
       r0=rax, r1=rcx, r2=rdx, r3=rbx, r4=rsp, r5=rbp, r6=rsi,
       r7=rdi, r8=r8, r9, r10, r11, r12, r13, r14, r15
     The first six arguments are passed in registers. The first
     argument (1) is passed in rdi(r7), the second(2) in rsi(r6),
     the third(3) in rdx(r3), the fourth(4) in rcx(2), the fifth(5)
     in r8 and the sixth in r9.
     Callee-saved regs: r12-r15, rbx *)
  (insert 1 7 ∘  (* arg 1 *)
   insert 2 6 ∘  (* arg 2 *)
   insert 3 2 ∘
   insert 4 1 ∘
   insert 5 8 ∘
   insert 6 9 ∘
   insert 11 14 ∘
   insert 12 13 ∘
   insert 13 12 ∘
   (* the rest just ensures that the mapping is well-formed *)
   insert 7 3 ∘
   insert 8 15 ∘
   insert 9 11 ∘
   insert 14 4 ∘
   insert 15 5) LN.

(*! HOL "cakeml/compiler/backend/x64/x64_configScript.sml" "x64_backend_config_def" *)
Definition x64_backend_config : config :=
  {| source_conf := prim_src_config;
     clos_conf := clos_to_bvl.default_config;
     bvl_conf := bvl_to_bvi.default_config;
     data_conf :=
       {| data_to_word.tag_bits := 4; data_to_word.len_bits := 4;
          data_to_word.pad_bits := 2; data_to_word.len_size := 32;
          data_to_word.has_div := false; data_to_word.has_longdiv := true;
          data_to_word.has_fp_ops := true; data_to_word.has_fp_tern := false;
          data_to_word.be := false; data_to_word.call_empty_ffi := false;
          data_to_word.gc_kind := data_to_word.Simple |};
     word_to_word_conf :=
       {| word_to_word.reg_alg := 2; word_to_word.col_oracle := [] |};
     word_conf :=
       {| word_to_stack.bitmaps_length := 0; word_to_stack.stack_frame_size := LN |};
     stack_conf :=
       {| stack_to_lab.jump := true; stack_to_lab.reg_names := x64_names;
          stack_to_lab.perf_calls := false |};
     lab_conf :=
       {| lab_to_target.pos := 0; lab_to_target.ffi_names := None;
          lab_to_target.labels := LN; lab_to_target.sec_pos_len := [];
          lab_to_target.init_clock := 5; lab_to_target.hash_size := 104729;
          lab_to_target.shmem_extra := [] |};
     symbols := [];
     tap_conf := default_tap_config;
     exported := [] |}.
