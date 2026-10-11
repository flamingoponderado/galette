(** * CakeML [lab_to_targetProof]: correctness of [lab_to_target]

    A port of [compiler/backend/proofs/lab_to_targetProofScript.sml], split
    along the script's own sections:
    - [lab_to_targetProof/basic.v]: [sec_loc_to_pc], the nop-padded asm
      step, [code_similar], [line_ok], [all_enc_ok], [pos_val],
      [good_code], the shared-memory relations, [oracle_tie] and
      [state_rel] (HOL lines 1-1153);
    - [lab_to_targetProof/bytes.v]: the encoding of the fetched
      instruction in code memory and the FFI byte-array lemmas (HOL lines
      1154-1783);
    - [lab_to_targetProof/inst.v]: alignment facts and [Inst_lemma] (HOL
      lines 1784-2931);
    - [lab_to_targetProof/compile_lemmas.v]: alignment of [pos_val],
      [word_cmp_lemma], [list_add_if_fresh], [find_index], [has_io_name]
      (HOL lines 2932-3122);
    - [lab_to_targetProof/rl_syntax.v]: syntactic properties of
      [remove_labels]: annotated lengths, padding, [code_similar] and
      [sec_labels_ok] preservation (HOL lines 3123-3612);
    - [lab_to_targetProof/rl_invariants.v]: the invariants [encd0],
      [length_leq], [label_one], [encd], [length_ok], [label_zero],
      [aligned] (HOL lines 3613-4168);
    - [lab_to_targetProof/rl_nop.v]: the invariants [label_prefix_zero],
      [enc_with_nop], [lab_len_pos_ok], [offset_ok] (HOL lines
      4169-4989);
    - [lab_to_targetProof/rl_labels.v]: referenced labels exist, the
      label domain of [compute_labels_alt], [even_labels] and [all_enc_ok]
      from the light check (HOL lines 4990-5414);
    - [lab_to_targetProof/rl_compute.v]: sections ending with labels,
      [compute_labels_alt] under re-encoding and padding, the computed
      label positions, [all_enc_ok_pre] preservation and code alignment
      (HOL lines 5415-5921);
    - [lab_to_targetProof/rl_remove.v]: the loop invariant
      [remove_labels_loop_thm], [remove_labels_thm] and the label domain
      (HOL lines 5922-6268);
    - [lab_to_targetProof/code_props.v]: lengths of [prog_to_bytes],
      [loc_to_pc] and [pos_val] on appended code, bounds,
      [find_ffi_names_append] (HOL lines 6269-6569);
    - [lab_to_targetProof/pos_props.v]: FFI entry points versus executed
      instructions, monotonicity of [pos_val] (HOL lines 6570-6957);
    - [lab_to_targetProof/shmem.v]: [mmio_pcs_min_index], fetching on
      appended code, [get_shmem_info], [no_share_mem_inst], [no_install]
      and [oracle_tie] under shifted oracles (HOL lines 6958-7525);
    - [lab_to_targetProof/cc_setup.v], [cc_asm.v], [cc_jump.v], [cc_ffi.v],
      [cc_install.v], [cc_share.v], [compile_correct.v]: the theorem
      [compile_correct] and its cases (HOL lines 7526-9353);
    - [lab_to_targetProof/sem_machine.v]: [init_ok] and
      [machine_sem_EQ_sem] (HOL lines 9355-9590);
    - [lab_to_targetProof/init_defs.v]: [make_init], [compiler_oracle_ok],
      [mc_conf_ok] and [get_shmem_info] (HOL lines 9596-10133);
    - [lab_to_targetProof/init_state_rel.v]: [IMP_state_rel_make_init] and
      [semantics_make_init] (HOL lines 10134-10538);
    - [lab_to_targetProof/filter_skip.v]: [filter_skip] facts (HOL lines
      10540-11010);
    - [lab_to_targetProof/semantics_compile.v]: the main theorem
      [semantics_compile] (HOL lines 11011-11303).

    Conventions are described in the header of [lab_to_targetProof/basic.v]. *)

From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Export
  basic bytes inst compile_lemmas rl_syntax rl_invariants rl_nop rl_labels
  rl_compute rl_remove code_props
  pos_props shmem cc_setup cc_asm cc_jump cc_ffi cc_install cc_share compile_correct
  sem_machine init_defs init_state_rel filter_skip semantics_compile.
