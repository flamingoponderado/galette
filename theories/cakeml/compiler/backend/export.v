(** * CakeML [export]: helpers for printing the generated assembly file

    Port of [cakeml/compiler/backend/exportScript.sml].

    String literals: HOL's ["...\n"] (with a newline character) is written
    [... ++ [NL]] with [NL] the newline character below, and HOL's [\t] is
    [TAB]; a backslash in a Rocq string literal is a plain backslash (HOL's
    ["\\"]), and a double quote is written [""].  [preamble] is HOL's
    evaluated form ([preamble_tm] is the [EVAL]uated [MAP]), stated here as
    the same [MAP] over the same lines.

    [split16] recurses on the length of the list (HOL's termination
    measure); it is defined with fuel [LENGTH xs] and HOL's equations are the
    tagged [split16_def] theorem.

    Not ported: [all_bytes_def], [all_bytes_eq] and [byte_to_string_eq] (an
    [mlvector] lookup table, an optimisation of [byte_to_string] for the
    translator). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.coretypes Require Import pair.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.basis.pure Require Import mlstring mlint.
Open Scope N_scope.
Open Scope hol_string_scope.
Open Scope mlstring_scope.

(** The newline and tab characters (HOL's [#"\n"], [#"\t"]). *)
Definition NL : ascii := "010"%char.
Definition TAB : ascii := "009"%char.

(** ** [split16] *)

Fixpoint split16_aux {A B} (f : list A -> app_list B) (fuel : nat) (xs : list A) : app_list B :=
  match xs with
  | [] => Nil
  | _ :: _ =>
      match fuel with
      | O => Nil
      | S fuel =>
          let xs1 := TAKE 16 xs in
          let xs2 := DROP 16 xs in
          SmartAppend (f xs1) (split16_aux f fuel xs2)
      end
  end.

(** HOL [split16] (see [split16_def]). *)
Definition split16 {A B} (f : list A -> app_list B) (xs : list A) : app_list B :=
  split16_aux f (length xs) xs.

Lemma split16_aux_fuel {A B} (f : list A -> app_list B) :
  forall n m xs, (length xs <= n)%nat -> (length xs <= m)%nat ->
    split16_aux f n xs = split16_aux f m xs.
Proof.
  induction n as [|n IH]; intros [|m] xs Hn Hm; destruct xs as [|x xs]; cbn in *;
    try reflexivity; try lia.
  f_equal; apply IH; rewrite DROP_skipn, length_skipn; cbn; lia.
Qed.

(*! HOL "cakeml/compiler/backend/exportScript.sml" "split16_def" *)
Theorem split16_def : forall {A B} (f : list A -> app_list B),
  split16 f [] = Nil /\
  (forall v2 v3,
     split16 f (v2 :: v3) =
       let xs := v2 :: v3 in
       let xs1 := TAKE 16 xs in
       let xs2 := DROP 16 xs in
       SmartAppend (f xs1) (split16 f xs2)).
Proof.
  intros A B f; split; [reflexivity|]; intros x xs; cbn zeta.
  unfold split16 at 1; cbn [length split16_aux]; f_equal.
  unfold split16; apply split16_aux_fuel; rewrite ?DROP_skipn, ?length_skipn; cbn [length]; lia.
Qed.

(** ** Fixed text *)

(*! HOL "cakeml/compiler/backend/exportScript.sml" "preamble_def" *)
Definition preamble : list mlstring :=
  MAP (fun n => strlit (n ++ [NL]))
    ["/* Preprocessor to get around Mac OS, Windows, and Linux differences in naming and calling conventions */";
     "";
     "#if defined(__APPLE__)";
     "# define cdecl(s) _##s";
     "#else";
     "# define cdecl(s) s";
     "#endif";
     "";
     "#if defined(__APPLE__)";
     "# define wcdecl(s) _##s";
     "#elif defined(__WIN32)";
     "# define wcdecl(s) windows_##s";
     "#else";
     "# define wcdecl(s) s";
     "#endif";
     "";
     "#if defined(__APPLE__)";
     "# define wcml(s) s";
     "#elif defined(__WIN32)";
     "# define wcml(s) windows_##s";
     "#else";
     "# define wcml(s) s";
     "#endif";
     "";
     "#if defined(__APPLE__)";
     ".macro _makesym name, base, len";
     ".set \name, cake_main+\base";
     ".endm";
     "# define makesym(name,base,len) _makesym name, base, len";
     "#elif defined(__WIN32)";
     ".macro _makesym name, base, len";
     ".set \name, cake_main+\base";
     ".endm";
     "# define makesym(name,base,len) _makesym name, base, len";
     "#else";
     ".macro _makesym name, base, len";
     ".local \name";
     ".set \name, cake_main+\base";
     ".size \name, \len";
     ".type \name, function";
     ".endm";
     "# define makesym(name,base,len) _makesym name, base, len";
     "#endif";
     "";
     "#define DATA_BUFFER_SIZE    65536";
     "#define CODE_BUFFER_SIZE  5242880";
     "";
     "     .file        ""cake.S""";
     ""].

(*! HOL "cakeml/compiler/backend/exportScript.sml" "data_section_def" *)
Definition data_section (word_directive : string) (ret : bool) : list mlstring :=
  MAP (fun n => strlit (n ++ [NL]))
    (["     .data";
      "     .p2align 3";
      "cdecl(cml_heap): " ++ word_directive ++ " 0";
      "cdecl(cml_stack): " ++ word_directive ++ " 0";
      "cdecl(cml_stackend): " ++ word_directive ++ " 0"] ++
     (if ret then
        ["ret_base: " ++ word_directive ++ " 0";
         "ret_stack: " ++ word_directive ++ " 0";
         "ret_stackend: " ++ word_directive ++ " 0";
         "can_enter: " ++ word_directive ++ " 0"]
      else []) ++
     ["     .p2align 3";
      "cake_bitmaps:"]).

(*! HOL "cakeml/compiler/backend/exportScript.sml" "data_buffer_def" *)
Definition data_buffer : list mlstring :=
  MAP (fun n => strlit (n ++ [NL]))
    ["     .globl cdecl(cake_bitmaps_buffer_begin)";
     "cdecl(cake_bitmaps_buffer_begin):";
     "#if defined(EVAL)";
     "     .space DATA_BUFFER_SIZE";
     "#endif";
     "     .globl cdecl(cake_bitmaps_buffer_end)";
     "cdecl(cake_bitmaps_buffer_end):"].

(*! HOL "cakeml/compiler/backend/exportScript.sml" "code_buffer_def" *)
Definition code_buffer : list mlstring :=
  MAP (fun n => strlit (n ++ [NL]))
    ["     .globl cdecl(cake_codebuffer_begin)";
     "cdecl(cake_codebuffer_begin):";
     "#if defined(EVAL)";
     "     .space CODE_BUFFER_SIZE";
     "#endif";
     "     .p2align 12";
     "     .globl cdecl(cake_codebuffer_end)";
     "cdecl(cake_codebuffer_end):";
     "     .space 4096"].

(*! HOL "cakeml/compiler/backend/exportScript.sml" "comm_strlit_def" *)
Definition comm_strlit : mlstring := strlit ",".

(*! HOL "cakeml/compiler/backend/exportScript.sml" "newl_strlit_def" *)
Definition newl_strlit : mlstring := strlit [NL].

(** ** Lines of words *)

(*! HOL "cakeml/compiler/backend/exportScript.sml" "comma_cat_def" *)
Fixpoint comma_cat {A} (f : A -> mlstring) (x : list A) : list mlstring :=
  match x with
  | [] => [newl_strlit]
  | [x] => [f x; newl_strlit]
  | x :: xs => f x :: comm_strlit :: comma_cat f xs
  end.

(*! HOL "cakeml/compiler/backend/exportScript.sml" "words_line_def" *)
Definition words_line {A} (word_directive : mlstring) (to_string : A -> mlstring)
    (ls : list A) : app_list mlstring :=
  List (word_directive :: comma_cat to_string ls).

(*! HOL "cakeml/compiler/backend/exportScript.sml" "word_to_string_def" *)
Definition word_to_string {a : N} (w : word a) : mlstring := num_to_str (w2n w).

(*! HOL "cakeml/compiler/backend/exportScript.sml" "byte_to_string_def" *)
Definition byte_to_string (b : word8) : mlstring :=
  strlit ("0x" ++ [EL (w2n b / 16) "0123456789ABCDEF"]
               ++ [EL (w2n b mod 16) "0123456789ABCDEF"]).

(** ** Symbols *)

(*! HOL "cakeml/compiler/backend/exportScript.sml" "escape_sym_char_def" *)
Definition escape_sym_char (ch : ascii) : mlstring :=
  let code := ORD ch in
  if ((97 <=? code) && (code <=? 122)) || ((65 <=? code) && (code <=? 90)) ||
     ((48 <=? code) && (code <=? 57)) || (code =? 95)
  then chr_to_str ch
  else strlit "$" ^ num_to_str code ^ strlit "_".

(*! HOL "cakeml/compiler/backend/exportScript.sml" "get_sym_label_def" *)
Definition get_sym_label (p : N * list (mlstring * (mlstring * (N * N))))
    (q : mlstring * (N * N)) : N * list (mlstring * (mlstring * (N * N))) :=
  let '(ix, appl) := p in
  let '(name, (start, len)) := q in
  let label :=
    strlit "cml_" ^ concat (MAP escape_sym_char (explode name)) ^
    strlit "_" ^ num_to_str ix in
  (ix + 1, appl ++ [(name, (label, (start, len)))]).

(*! HOL "cakeml/compiler/backend/exportScript.sml" "get_sym_labels_def" *)
Definition get_sym_labels (syms : list (mlstring * (N * N))) : list (mlstring * (mlstring * (N * N))) :=
  SND (FOLDL get_sym_label (0, []) syms).

(*! HOL "cakeml/compiler/backend/exportScript.sml" "emit_symbol_def" *)
Definition emit_symbol (appl : app_list mlstring) (q : mlstring * (mlstring * (N * N)))
    : app_list mlstring :=
  let '(name, (label, (start, len))) := q in
  Append appl (List
    [strlit "    makesym(" ^ label ^ strlit ", " ^ num_to_str start ^ strlit ", " ^
     num_to_str len ^ strlit (")" ++ [NL])]).

(*! HOL "cakeml/compiler/backend/exportScript.sml" "emit_symbols_def" *)
Definition emit_symbols (lsyms : list (mlstring * (mlstring * (N * N)))) : app_list mlstring :=
  FOLDL emit_symbol Nil lsyms.
