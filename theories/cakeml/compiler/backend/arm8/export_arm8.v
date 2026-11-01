(** * CakeML [export_arm8]: the ARMv8 assembly file

    Port of [cakeml/compiler/backend/arm8/export_arm8Script.sml].

    HOL builds [arm8_export] from two SML-level terms that are spliced in by
    antiquotation: [ffi_code] (a [λret. ...] over the free variable
    [ffi_names], evaluated for [ret = T] and [ret = F]) and
    [entry_point_code] (an evaluated [List (MAP ...)]).  They are not HOL
    constants; here they are the (untagged) definitions [ffi_code] and
    [entry_point_code] with the same text, and [arm8_export] uses them where
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

(*! HOL "cakeml/compiler/backend/arm8/export_arm8Script.sml" "startup_def" *)
Definition startup (ret pk : bool) : app_list mlstring :=
  SmartAppend (List
    [strlit ("" ++ [NL]);
     strlit ("/* Start up code */" ++ [NL]);
     strlit ("" ++ [NL]);
     strlit ("     .text" ++ [NL]);
     strlit ("     .p2align 3" ++ [NL]);
     strlit ("     .globl  cdecl(cml_main)" ++ [NL]);
     strlit ("     .globl  cdecl(cml_heap)" ++ [NL]);
     strlit ("     .globl  cdecl(cml_stack)" ++ [NL]);
     strlit ("     .globl  cdecl(cml_stackend)" ++ [NL]);
     strlit ("#ifndef __APPLE__" ++ [NL]);
     strlit ("     .type   cml_main, function" ++ [NL]);
     strlit ("#endif" ++ [NL]);
     strlit ("" ++ [NL]);
     strlit (".macro _ldrel reg sym" ++ [NL]);
     strlit ("#ifdef __APPLE__" ++ [NL]);
     strlit ("adrp \reg, \sym@PAGE" ++ [NL]);
     strlit ("add  \reg, \reg, \sym@PAGEOFF" ++ [NL]);
     strlit ("#else" ++ [NL]);
     strlit ("adrp \reg, \sym" ++ [NL]);
     strlit ("add  \reg, \reg, :lo12:\sym" ++ [NL]);
     strlit ("#endif" ++ [NL]);
     strlit (".endm" ++ [NL]);
     strlit ("" ++ [NL]);
     strlit ("cdecl(cml_main):" ++ [NL]);
     strlit ("     _ldrel x0, cake_main            /* arg1: entry address */" ++ [NL]);
     strlit ("     _ldrel x1, cdecl(cml_heap)      /* arg2: first address of heap */" ++ [NL]);
     strlit ("     ldr    x1,[x1]" ++ [NL])])
  (SmartAppend (List
    (if negb pk then
       [strlit ("     _ldrel x2, cake_bitmaps" ++ [NL]);
        strlit ("     str    x2,[x1]                  /* store bitmap pointer */" ++ [NL])]
     else []))
  (SmartAppend (List
    [strlit ("     _ldrel x2, cdecl(cml_stack)     /* arg3: first address of stack */" ++ [NL]);
     strlit ("     ldr    x2,[x2]" ++ [NL]);
     strlit ("     _ldrel x3, cdecl(cml_stackend)  /* arg4: first address past the stack */" ++ [NL]);
     strlit ("     ldr    x3,[x3]" ++ [NL])])
  (SmartAppend (List
    (if ret then
       [strlit ("     b      cml_enter" ++ [NL])]
     else
       [strlit ("     b      cake_main" ++ [NL])]))
  (List
    [strlit ("     .ltorg" ++ [NL]);
     strlit ("" ++ [NL])])))).

(*! HOL "cakeml/compiler/backend/arm8/export_arm8Script.sml" "ffi_asm_def" *)
Fixpoint ffi_asm (l : list mlstring) : app_list mlstring :=
  match l with
  | [] => Nil
  | ffi :: ffis =>
      SmartAppend (List [
        strlit "cake_ffi"; ffi; strlit (":" ++ [NL]);
        strlit "     b     cdecl(ffi"; ffi; strlit (")" ++ [NL]);
        strlit ("     .p2align 4" ++ [NL]);
        strlit ("" ++ [NL])]) (ffi_asm ffis)
  end.

(** HOL's SML value [ffi_code] (see the header). *)
Definition ffi_code (ffi_names : list mlstring) (ret : bool) : app_list mlstring :=
  SmartAppend
    (List (MAP (fun n => strlit (n ++ [NL]))
      ["/* CakeML FFI interface (each block is 16 bytes long) */";
       "";
       "     .p2align 4";
       ""]))
    (SmartAppend
      (ffi_asm (REVERSE ffi_names))
      (List (MAP (fun n => strlit (n ++ [NL]))
        (["cake_clear:";
          "     b   cdecl(cml_exit)";
          "     .p2align 4";
          "";
          "cake_exit:"] ++
         (if ret then
            ["     b   cml_return"]
          else
            ["     b   cdecl(cml_exit)"]) ++
         ["     .p2align 4";
          "";
          "cake_main:";
          "";
          "/* Generated machine code follows */";
          ""])))).

(** HOL's SML value [entry_point_code] (see the header). *)
Definition entry_point_code : app_list mlstring :=
  List (MAP (fun n => strlit (n ++ [NL]))
    ["";
     "";
     "cml_enter:";
     "     str    x30, [sp, #-32]!";
     "     str    x29, [sp, #-32]!";
     "     str    x28, [sp, #-32]!";
     "     str    x27, [sp, #-32]!";
     "     str    x26, [sp, #-32]!";
     "     str    x25, [sp, #-32]!";
     "     str    x24, [sp, #-32]!";
     "     str    x23, [sp, #-32]!";
     "     str    x22, [sp, #-32]!";
     "     str    x21, [sp, #-32]!";
     "     str    x20, [sp, #-32]!";
     "     str    x19, [sp, #-32]!";
     "     b      cake_main";
     "     .p2align 4";
     "";
     "";
     "cake_enter:";
     "     str    x30, [sp, #-32]!";
     "     str    x29, [sp, #-32]!";
     "     str    x28, [sp, #-32]!";
     "     str    x27, [sp, #-32]!";
     "     str    x26, [sp, #-32]!";
     "     str    x25, [sp, #-32]!";
     "     str    x24, [sp, #-32]!";
     "     str    x23, [sp, #-32]!";
     "     str    x22, [sp, #-32]!";
     "     str    x21, [sp, #-32]!";
     "     str    x20, [sp, #-32]!";
     "     str    x19, [sp, #-32]!";
     "     _ldrel x9, can_enter";
     "     ldr    x11, [x9]";
     "     cbz    x11, cake_err3";
     "     str    xzr, [x9]";
     "     _ldrel x9, ret_base";
     "     ldr    x28, [x9]";
     "     _ldrel x9, ret_stack";
     "     ldr    x25, [x9]";
     "     _ldrel x9, ret_stackend";
     "     ldr    x27, [x9]";
     "     _ldrel x30, cake_return";
     "     br     x10";
     "     .p2align 4";
     "";
     "";
     "cml_return:";
     "     _ldrel x9, ret_base";
     "     str    x28, [x9]";
     "     _ldrel x9, ret_stack";
     "     str    x25, [x9]";
     "     _ldrel x9, ret_stackend";
     "     str    x27, [x9]";
     "";
     "cake_return:";
     "     _ldrel x9, can_enter";
     "     mov    x11, #1";
     "     str    x11, [x9]";
     "     mov    x8, x0";
     "     ldr    x19, [sp], #32";
     "     ldr    x20, [sp], #32";
     "     ldr    x21, [sp], #32";
     "     ldr    x22, [sp], #32";
     "     ldr    x23, [sp], #32";
     "     ldr    x24, [sp], #32";
     "     ldr    x25, [sp], #32";
     "     ldr    x26, [sp], #32";
     "     ldr    x27, [sp], #32";
     "     ldr    x28, [sp], #32";
     "     ldr    x29, [sp], #32";
     "     ldr    x30, [sp], #32";
     "     ret";
     "     .p2align 4";
     "";
     "";
     "cake_err3:";
     "     mov    x0, #3";
     "     b      cdecl(cml_err)";
     "     .p2align 4";
     ""]).

(*! HOL "cakeml/compiler/backend/arm8/export_arm8Script.sml" "export_func_def" *)
Definition export_func (appl : app_list mlstring) (q : mlstring * (mlstring * (N * N)))
    : app_list mlstring :=
  let '(name, (label, (start, len))) := q in
  SmartAppend appl (List
    [strlit ([NL] ++ "    .globl cdecl("); name; strlit (")" ++ [NL]);
     strlit ("#ifndef __APPLE__" ++ [NL]);
     strlit "     .type   "; name; strlit (", function" ++ [NL]);
     strlit ("#endif" ++ [NL]);
     strlit "cdecl("; name; strlit ("):" ++ [NL]);
     strlit "     _ldrel x10, "; name; strlit ("_jmp" ++ [NL]);
     strlit ("     b      cake_enter" ++ [NL]);
     name; strlit ("_jmp:" ++ [NL]);
     strlit "     b      "; label; strlit [NL]
    ]).

(*! HOL "cakeml/compiler/backend/arm8/export_arm8Script.sml" "export_funcs_def" *)
Definition export_funcs (lsyms : list (mlstring * (mlstring * (N * N)))) (exp : list mlstring)
    : app_list mlstring :=
  FOLDL export_func Nil (FILTER (fun x => MEM (fst x) exp) lsyms).

(*! HOL "cakeml/compiler/backend/arm8/export_arm8Script.sml" "arm8_export_def" *)
Definition arm8_export (ffi_names : list mlstring) (bytes : list word8) (data : list word64)
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
