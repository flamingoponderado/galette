(** * CakeML [export_x64]: the x86-64 assembly file

    Port of [cakeml/compiler/backend/x64/export_x64Script.sml].

    HOL builds [ffi_code] and [windows_ffi_code] from SML-level terms that are
    spliced in by antiquotation: each is a [λret. ...] over the free variable
    [ffi_names], evaluated for [ret = T] and [ret = F].  They are not HOL
    constants; here they are the (untagged) definitions [ffi_code] and
    [windows_ffi_code] with the same text, taking [ffi_names] and [ret], and
    [x64_export] uses them where HOL splices them in.  [entry_point_code] is
    likewise an evaluated SML term, untagged.  See [export.v] for the
    string-literal conventions ([NL], [TAB]). *)

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

(*! HOL "cakeml/compiler/backend/x64/export_x64Script.sml" "startup_def" *)
Definition startup (ret pk : bool) : app_list mlstring :=
  SmartAppend (List
    [strlit ("" ++ [NL]);
     strlit ("/* Start up code */" ++ [NL]);
     strlit ("" ++ [NL]);
     strlit ("     .text" ++ [NL]);
     strlit ("     .p2align 12" ++ [NL]);
     strlit ("     .globl  cdecl(cake_text_begin)" ++ [NL]);
     strlit ("cdecl(cake_text_begin):" ++ [NL]);
     strlit ("     .globl  cdecl(cml_main)" ++ [NL]);
     strlit ("     .globl  cdecl(cml_heap)" ++ [NL]);
     strlit ("     .globl  cdecl(cml_stack)" ++ [NL]);
     strlit ("     .globl  cdecl(cml_stackend)" ++ [NL]);
     strlit ("#if defined(__APPLE__)" ++ [NL]);
     strlit ("" ++ [NL]);
     strlit ("#elif defined(__WIN32)" ++ [NL]);
     strlit ("     .func   cml_main" ++ [NL]);
     strlit ("#else" ++ [NL]);
     strlit ("     .type   cml_main, function" ++ [NL]);
     strlit ("#endif" ++ [NL]);
     strlit ("cdecl(cml_main):" ++ [NL]);
     strlit ("     pushq   %rbp                            # push base pointer" ++ [NL]);
     strlit ("     movq    %rsp, %rbp                      # save stack pointer" ++ [NL]);
     strlit ("     leaq    cake_main(%rip), %rdi           # arg1: entry address" ++ [NL]);
     strlit ("     movq    cdecl(cml_heap)(%rip), %rsi     # arg2: first address of heap" ++ [NL])])
  (SmartAppend (List
    (if negb pk then
       [strlit ("     leaq    cake_bitmaps(%rip), %rax" ++ [NL]);
        strlit ("     movq    %rax, 0(%rsi)                   # store bitmap pointer" ++ [NL]);
        strlit ("     leaq    cdecl(cake_bitmaps_buffer_begin)(%rip), %rax" ++ [NL]);
        strlit ("     movq    %rax, 8(%rsi)                   # store bitmap mutable start pointer" ++ [NL]);
        strlit ("     leaq    cdecl(cake_bitmaps_buffer_end)(%rip), %rax" ++ [NL]);
        strlit ("     movq    %rax, 16(%rsi)                  # store bitmap mutable end pointer" ++ [NL]);
        strlit ("     leaq    cdecl(cake_codebuffer_begin)(%rip), %rax" ++ [NL]);
        strlit ("     movq    %rax, 24(%rsi)                  # store code mutable start pointer" ++ [NL]);
        strlit ("     leaq    cdecl(cake_codebuffer_end)(%rip), %rax" ++ [NL]);
        strlit ("     movq    %rax, 32(%rsi)                  # store code mutable end pointer" ++ [NL])]
     else []))
  (SmartAppend (List
    [strlit ("     movq    cdecl(cml_stack)(%rip), %rdx    # arg3: first address of stack" ++ [NL]);
     strlit ("     movq    cdecl(cml_stackend)(%rip), %rcx # arg4: first address past the stack" ++ [NL])])
  (SmartAppend (List
    (if ret then
       [strlit ("     jmp     cml_enter" ++ [NL])]
     else
       [strlit ("     jmp     cake_main" ++ [NL])]))
  (List
    [strlit ("" ++ [NL]);
     strlit ("#if defined(__WIN32)" ++ [NL]);
     strlit ("     .endfunc" ++ [NL]);
     strlit ("#endif" ++ [NL])])))).

(*! HOL "cakeml/compiler/backend/x64/export_x64Script.sml" "ffi_asm_def" *)
Fixpoint ffi_asm (l : list mlstring) : app_list mlstring :=
  match l with
  | [] => Nil
  | ffi :: ffis =>
      SmartAppend (List [
        strlit "cake_ffi"; ffi; strlit (":" ++ [NL]);
        strlit ("     pushq   %rax" ++ [NL]);
        strlit "     jmp     wcdecl(ffi"; ffi; strlit (")" ++ [NL]);
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
          "     pushq   %rax";
          "     pushq   %rdi";
          "     callq   wcdecl(cml_clear)";
          "     popq    %rdi";
          "     ret";
          "     .p2align 4";
          "";
          "cake_exit:"] ++
         (if ret then
            ["     jmp     cml_return"]
          else
            ["     callq   cdecl(cml_exit)"]) ++
         ["     .p2align 4";
          "";
          "cake_main:";
          "";
          "/* Generated machine code follows */";
          ""])))).

(*! HOL "cakeml/compiler/backend/x64/export_x64Script.sml" "windows_ffi_asm_def" *)
Fixpoint windows_ffi_asm (l : list mlstring) : app_list mlstring :=
  match l with
  | [] => Nil
  | ffi :: ffis =>
      SmartAppend (List [
        strlit "windows_ffi"; ffi; strlit (":" ++ [NL]);
        strlit ("     movq    %rcx, %r9" ++ [NL]);
        strlit ("     movq    %rdx, %r8" ++ [NL]);
        strlit ("     movq    %rsi, %rdx" ++ [NL]);
        strlit ("     movq    %rdi, %rcx" ++ [NL]);
        strlit "     jmp     cdecl(ffi"; ffi; strlit (")" ++ [NL]);
        strlit ("" ++ [NL])]) (windows_ffi_asm ffis)
  end.

(** HOL's SML value [windows_ffi_code] (see the header). *)
Definition windows_ffi_code (ffi_names : list mlstring) (ret : bool) : app_list mlstring :=
  SmartAppend
    (List [strlit ([NL] ++ "/* Windows Compatibility for CakeML FFI interface */" ++ [NL] ++ [NL])])
    (SmartAppend
      (windows_ffi_asm (REVERSE ffi_names))
      (List (MAP (fun n => strlit (n ++ [NL]))
        (["windows_cml_clear:";
          "     movq    %rcx, %r9";
          "     movq    %rdx, %r8";
          "     movq    %rsi, %rdx";
          "     movq    %rdi, %rcx";
          "     jmp     cdecl(cml_clear)"] ++
         (if ret then
            []
          else
            ["windows_cml_exit:";
             "     movq    %rcx, %r9";
             "     movq    %rdx, %r8";
             "     movq    %rsi, %rdx";
             "     movq    %rdi, %rcx";
             "     callq   cdecl(cml_exit)"]))))).

(** HOL's SML value [entry_point_code] (see the header). *)
Definition entry_point_code : app_list mlstring :=
  List (MAP (fun n => strlit (n ++ [NL]))
    ["cml_enter:";
     "     sub     $0x30, %rsp";
     "     movq    %r12, -0x8(%rbp)";
     "     movq    %r13, -0x10(%rbp)";
     "     movq    %r14, -0x18(%rbp)";
     "     movq    %r15, -0x20(%rbp)";
     "     movq    %rbx, -0x28(%rbp)";
     "     jmp     cake_main";
     "";
     "windows_cake_enter:";
     "     movq    %rcx, %rdi";
     "     movq    %rdx, %rsi";
     "     movq    %r8, %rdx";
     "     movq    %r9, %rcx";
     "";
     "cake_enter:";
     "     pushq   %rbp";
     "     movq    %rsp, %rbp";
     "     sub     $0x30, %rsp";
     "     movq    %r12, -0x8(%rbp)";
     "     movq    %r13, -0x10(%rbp)";
     "     movq    %r14, -0x18(%rbp)";
     "     movq    %r15, -0x20(%rbp)";
     "     movq    %rbx, -0x28(%rbp)";
     "     movq    can_enter(%rip), %r11";
     "     cmp     $0, %r11";
     "     je      cake_err3";
     "     movq    $0, can_enter(%rip)";
     "     movq    ret_base(%rip), %r14";
     "     movq    ret_stack(%rip), %r12";
     "     movq    ret_stackend(%rip), %r13";
     "     lea     cake_return(%rip), %rax";
     "     jmp     *%r10";
     "     .p2align 4";
     "";
     "cml_return:";
     "     movq    %r14, ret_base(%rip)";
     "     movq    %r12, ret_stack(%rip)";
     "     movq    %r13, ret_stackend(%rip)";
     "";
     "cake_return:";
     "     movq    $1, can_enter(%rip)";
     "     mov     %edi, %eax";
     "     movq    -0x28(%rbp),%rbx";
     "     movq    -0x20(%rbp),%r15";
     "     movq    -0x18(%rbp),%r14";
     "     movq    -0x10(%rbp),%r13";
     "     movq    -0x8(%rbp),%r12";
     "     leave";
     "     ret";
     "     .p2align 4";
     "";
     "cake_err3:";
     "     pushq   %rax";
     "     movq    $3, %rdi";
     "     jmp     wcdecl(cml_err)";
     "     .p2align 4";
     "";
     "windows_cml_err:";
     "     movq    %rcx, %r9";
     "     movq    %rdx, %r8";
     "     movq    %rsi, %rdx";
     "     movq    %rdi, %rcx";
     "     jmp     cdecl(cml_err)";
     ""]).

(*! HOL "cakeml/compiler/backend/x64/export_x64Script.sml" "export_func_def" *)
Definition export_func (appl : app_list mlstring) (q : mlstring * (mlstring * (N * N)))
    : app_list mlstring :=
  let '(name, (label, (start, len))) := q in
  SmartAppend appl (List
    [strlit ([NL] ++ "    .globl cdecl("); name; strlit (")" ++ [NL]);
     strlit ("#if defined(__APPLE__)" ++ [NL]);
     strlit ("" ++ [NL]);
     strlit ("#elif defined(__WIN32)" ++ [NL]);
     strlit "     .func   cdecl("; name; strlit (")" ++ [NL]);
     strlit ("#else" ++ [NL]);
     strlit "     .type   cdecl("; name; strlit ("), function" ++ [NL]);
     strlit ("#endif" ++ [NL]);
     strlit "cdecl("; name; strlit ("):" ++ [NL]);
     strlit "     lea     "; name; strlit ("_jmp(%rip), %r10" ++ [NL]);
     strlit ("     jmp     wcml(cake_enter)" ++ [NL]);
     name; strlit ("_jmp:" ++ [NL]);
     strlit "     jmp     "; label; strlit [NL];
     strlit ("#if defined(__WIN32)" ++ [NL]);
     strlit ("     .endfunc" ++ [NL]);
     strlit ("#endif" ++ [NL])
    ]).

(*! HOL "cakeml/compiler/backend/x64/export_x64Script.sml" "export_funcs_def" *)
Definition export_funcs (lsyms : list (mlstring * (mlstring * (N * N)))) (exp : list mlstring)
    : app_list mlstring :=
  FOLDL export_func Nil (FILTER (fun x => MEM (fst x) exp) lsyms).

(*! HOL "cakeml/compiler/backend/x64/export_x64Script.sml" "x64_export_def" *)
Definition x64_export (ffi_names : list mlstring) (bytes : list word8) (data : list word64)
    (syms : list (mlstring * (N * N))) (exp : list mlstring) (ret pk : bool)
    : app_list mlstring :=
  let lsyms := get_sym_labels syms in
  SmartAppend
    (SmartAppend
      (SmartAppend (List preamble)
      (SmartAppend (List (data_section ".quad" ret))
      (SmartAppend (split16 (words_line (strlit ([TAB] ++ ".quad ")) word_to_string) data)
      (SmartAppend (List data_buffer)
      (SmartAppend (startup ret pk) (ffi_code ffi_names ret))))))
      (SmartAppend (split16 (words_line (strlit ([TAB] ++ ".byte ")) byte_to_string) bytes)
      (SmartAppend (List code_buffer)
      (emit_symbols lsyms))))
    (SmartAppend (windows_ffi_code ffi_names ret)
    (if ret then
       SmartAppend entry_point_code (export_funcs lsyms exp)
     else List [])).
