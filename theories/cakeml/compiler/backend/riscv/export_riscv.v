(** * CakeML [export_riscv]: the RISC-V assembly file

    Port of [cakeml/compiler/backend/riscv/export_riscvScript.sml].

    HOL builds [riscv_export] from two SML-level terms that are spliced in by
    antiquotation: [ffi_code] (a [λret. ...] over the free variable
    [ffi_names], evaluated for [ret = T] and [ret = F]) and
    [entry_point_code] (an evaluated [List (MAP ...)]).  They are not HOL
    constants; here they are the (untagged) definitions [ffi_code] and
    [entry_point_code] with the same text, and [riscv_export] uses them where
    HOL splices them in.  See [export.v] for the string-literal conventions
    ([NL], [TAB]). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.compiler.backend Require Import export.
Open Scope N_scope.
Open Scope hol_string_scope.
Open Scope mlstring_scope.

(*! HOL "cakeml/compiler/backend/riscv/export_riscvScript.sml" "startup_def" *)
Definition startup (ret pk : bool) : app_list mlstring :=
  SmartAppend (List
    [strlit ("" ++ [NL]);
     strlit ("#### Start up code" ++ [NL]);
     strlit ("" ++ [NL]);
     strlit ("     .text" ++ [NL]);
     strlit ("     .p2align 3" ++ [NL]);
     strlit ("     .globl  cdecl(cml_main)" ++ [NL]);
     strlit ("     .globl  cdecl(cml_heap)" ++ [NL]);
     strlit ("     .globl  cdecl(cml_stack)" ++ [NL]);
     strlit ("     .globl  cdecl(cml_stackend)" ++ [NL]);
     strlit ("     .type   cml_main, function" ++ [NL]);
     strlit ("cdecl(cml_main):" ++ [NL]);
     strlit ("     la      a0,cake_main           # arg1: entry address" ++ [NL]);
     strlit ("     ld      a1,cdecl(cml_heap)     # arg2: first address of heap" ++ [NL])])
  (SmartAppend (List
    (if negb pk then
       [strlit ("     la      t3,cake_bitmaps" ++ [NL]);
        strlit ("     sd      t3, 0(a1)              # store bitmap pointer" ++ [NL])]
     else []))
  (SmartAppend (List
    [strlit ("     ld      a2,cdecl(cml_stack)    # arg3: first address of stack" ++ [NL]);
     strlit ("     ld      a3,cdecl(cml_stackend) # arg4: first address past the stack" ++ [NL])])
  (SmartAppend (List
    (if ret then
       [strlit ("     j       cml_enter" ++ [NL])]
     else
       [strlit ("     j       cake_main" ++ [NL])]))
  (List
    [strlit ("" ++ [NL])])))).

(*! HOL "cakeml/compiler/backend/riscv/export_riscvScript.sml" "ffi_asm_def" *)
Fixpoint ffi_asm (l : list mlstring) : app_list mlstring :=
  match l with
  | [] => Nil
  | ffi :: ffis =>
      SmartAppend (List [
        strlit "cake_ffi"; ffi; strlit (":" ++ [NL]);
        strlit "     tail cdecl(ffi"; ffi; strlit (")" ++ [NL]);
        strlit ("     .p2align 4" ++ [NL]);
        strlit ("" ++ [NL])]) (ffi_asm ffis)
  end.

(** HOL's SML value [ffi_code] (see the header). *)
Definition ffi_code (ffi_names : list mlstring) (ret : bool) : app_list mlstring :=
  SmartAppend
    (List (MAP (fun n => strlit (n ++ [NL]))
      ["#### CakeML FFI interface (each block is 16 bytes long)";
       "";
       "     .p2align 4";
       ""]))
    (SmartAppend
      (ffi_asm (REVERSE ffi_names))
      (List (MAP (fun n => strlit (n ++ [NL]))
        (["cake_clear:";
          "     tail cdecl(cml_exit)";
          "     .p2align 4";
          "";
          "cake_exit:"] ++
         (if ret then
            ["     j    cml_return"]
          else
            ["     tail cdecl(cml_exit)"]) ++
         ["     .p2align 4";
          "";
          "cake_main:";
          "";
          "#### Generated machine code follows";
          ""])))).

(** HOL's SML value [entry_point_code] (see the header). *)
Definition entry_point_code : app_list mlstring :=
  List (MAP (fun n => strlit (n ++ [NL]))
    [""; "";
     "cml_enter:";
     "     addi    sp, sp, -104";
     "     sd      ra, 0(sp)";
     "     sd      s11, 8(sp)";
     "     sd      s10, 16(sp)";
     "     sd      s9, 24(sp)";
     "     sd      s8, 32(sp)";
     "     sd      s7, 40(sp)";
     "     sd      s6, 48(sp)";
     "     sd      s5, 56(sp)";
     "     sd      s4, 64(sp)";
     "     sd      s3, 72(sp)";
     "     sd      s2, 80(sp)";
     "     sd      s1, 88(sp)";
     "     sd      s0, 96(sp)";
     "     j       cake_main";
     "     .p2align 4";
     ""; "";
     "cake_enter:";
     "     addi    sp, sp, -104";
     "     sd      ra, 0(sp)";
     "     sd      s11, 8(sp)";
     "     sd      s10, 16(sp)";
     "     sd      s9, 24(sp)";
     "     sd      s8, 32(sp)";
     "     sd      s7, 40(sp)";
     "     sd      s6, 48(sp)";
     "     sd      s5, 56(sp)";
     "     sd      s4, 64(sp)";
     "     sd      s3, 72(sp)";
     "     sd      s2, 80(sp)";
     "     sd      s1, 88(sp)";
     "     sd      s0, 96(sp)";
     "     la      t1, can_enter";
     "     ld      t2, 0(t1)";
     "     beq     t2, zero, cake_err3";
     "     sd      zero, 0(t1)";
     "     la      t1, ret_base";
     "     ld      s10, 0(t1)";
     "     la      t1, ret_stack";
     "     ld      s8, 0(t1)";
     "     la      t1, ret_stackend";
     "     ld      s9, 0(t1)";
     "     la      ra, cake_return";
     "     jr      t0";
     "     .p2align 4";
     ""; "";
     "cml_return:";
     "     la      t1, ret_base";
     "     sd      s10, 0(t1)";
     "     la      t1, ret_stack";
     "     sd      s8, 0(t1)";
     "     la      t1, ret_stackend";
     "     sd      s9, 0(t1)";
     "";
     "cake_return:";
     "     la      t1, can_enter";
     "     li      t2, 1";
     "     sd      t2, 0(t1)";
     "     ld      s0, 96(sp)";
     "     ld      s1, 88(sp)";
     "     ld      s2, 80(sp)";
     "     ld      s3, 72(sp)";
     "     ld      s4, 64(sp)";
     "     ld      s5, 56(sp)";
     "     ld      s6, 48(sp)";
     "     ld      s7, 40(sp)";
     "     ld      s8, 32(sp)";
     "     ld      s9, 24(sp)";
     "     ld      s10, 16(sp)";
     "     ld      s11, 8(sp)";
     "     ld      ra, 0(sp)";
     "     addi    sp, sp, 104";
     "     ret";
     "     .p2align 4";
     ""; "";
     "cake_err3:";
     "     li      a0, 3";
     "     j       cdecl(cml_err)";
     "     .p2align 4";
     ""]).

(*! HOL "cakeml/compiler/backend/riscv/export_riscvScript.sml" "export_func_def" *)
Definition export_func (appl : app_list mlstring) (q : mlstring * (mlstring * (N * N)))
    : app_list mlstring :=
  let '(name, (label, (start, len))) := q in
  SmartAppend appl (List
    [strlit ([NL] ++ "     .globl  cdecl("); name; strlit (")" ++ [NL]);
     strlit "     .type   "; name; strlit (", function" ++ [NL]);
     strlit "cdecl("; name; strlit ("):" ++ [NL]);
     strlit "     la      t0, "; name; strlit ("_jmp" ++ [NL]);
     strlit ("     j       cake_enter" ++ [NL]);
     name; strlit ("_jmp:" ++ [NL]);
     strlit "     j       "; label; strlit [NL]
    ]).

(*! HOL "cakeml/compiler/backend/riscv/export_riscvScript.sml" "export_funcs_def" *)
Definition export_funcs (lsyms : list (mlstring * (mlstring * (N * N)))) (exp : list mlstring)
    : app_list mlstring :=
  FOLDL export_func Nil (FILTER (fun x => MEM (fst x) exp) lsyms).

(*! HOL "cakeml/compiler/backend/riscv/export_riscvScript.sml" "riscv_export_def" *)
Definition riscv_export (ffi_names : list mlstring) (bytes : list word8) (data : list word64)
    (syms : list (mlstring * (N * N))) (exp : list mlstring) (ret pk : bool)
    : app_list mlstring :=
  let lsyms := get_sym_labels syms in
  SmartAppend
    (SmartAppend (List preamble)
    (SmartAppend (List (data_section ".quad" ret))
    (SmartAppend (split16 (words_line (strlit ([TAB] ++ ".quad ")) word_to_string) data)
    (SmartAppend (List data_buffer)
    (SmartAppend (startup ret pk) (ffi_code ffi_names ret))))))
    (SmartAppend (split16 (words_line (strlit ([TAB] ++ ".byte ")) byte_to_string) bytes)
    (SmartAppend (List code_buffer)
    (SmartAppend (emit_symbols lsyms)
    (if ret then
       SmartAppend entry_point_code (export_funcs lsyms exp)
     else List [])))).
