(** * CakeML [stack_alloc]: the garbage collector and allocation calls

    Port of [cakeml/compiler/backend/stack_allocScript.sml].  The [_pmatch]
    theorems (alternative presentations for HOL's translator) are not
    ported.  HOL's overload [shift (:'a)] is [word_shift a]; HOL's
    [conf.gc_kind] constructor [None] is [gc_kind_None] (see
    [data_to_word.v]). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words byte.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.backend Require Import backend_common.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import data_to_word.
From Galette.cakeml.compiler.backend Require Import stackLang.
Open Scope N_scope.
Open Scope hol_string_scope.

Section StackAlloc.
Context {a : N}.

Abbreviation sprog := (stackLang.prog a).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "memcpy_code_def" *)
Definition memcpy_code : sprog :=
  While NotEqual 0 (Imm (n2w 0))
    (list_Seq [load_inst 1 2;
               add_bytes_in_word_inst 2;
               sub_1_inst 0;
               store_inst 1 3;
               add_bytes_in_word_inst 3]).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "clear_top_inst_def" *)
Definition clear_top_inst (i n : N) : sprog :=
  Seq (left_shift_inst i (dimindex a - n - 1))
      (right_shift_inst i (dimindex a - n - 1)).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gc_move_code_def" *)
Definition word_gc_move_code (conf : data_to_word.config) : sprog :=
  If Test 5 (Imm (n2w 1)) Skip
    (list_Seq
      [move 0 5;
       Get 1 CurrHeap;
       right_shift_inst 0 (shift_length conf);
       left_shift_inst 0 (word_shift a);
       add_inst 0 1;
       load_inst 1 0;
       If Test 1 (Imm (n2w 3))
         (list_Seq [right_shift_inst 1 2;
                    left_shift_inst 1 (shift_length conf);
                    clear_top_inst 5 (small_shift_length conf - 1);
                    or_inst 5 1])
         (list_Seq [right_shift_inst 1 (dimindex a - len_size conf);
                    add_1_inst 1;
                    move 6 1;
                    move 2 0;
                    move 0 1;
                    memcpy_code;
                    move 0 6;
                    left_shift_inst 0 (word_shift a);
                    sub_inst 2 0;
                    move 0 4;
                    left_shift_inst 0 2;
                    store_inst 0 2;
                    move 1 4;
                    clear_top_inst 5 (small_shift_length conf - 1);
                    left_shift_inst 1 (shift_length conf);
                    or_inst 5 1;
                    add_inst 4 6])]).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gc_move_list_code_def" *)
Definition word_gc_move_list_code (conf : data_to_word.config) : sprog :=
  While NotEqual 7 (Imm (n2w 0))
    (list_Seq [load_inst 5 8;
               sub_1_inst 7;
               word_gc_move_code conf;
               store_inst 5 8;
               add_bytes_in_word_inst 8]).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gc_move_loop_code_def" *)
Definition word_gc_move_loop_code (conf : data_to_word.config) : sprog :=
  While NotEqual 3 (Reg 8)
   (list_Seq [load_inst 7 8;
              If Test 7 (Imm (n2w 4))
                (list_Seq [right_shift_inst 7 (dimindex a - len_size conf);
                           add_bytes_in_word_inst 8;
                           word_gc_move_list_code conf])
                (list_Seq [right_shift_inst 7 (dimindex a - len_size conf);
                           add_1_inst 7;
                           left_shift_inst 7 (word_shift a);
                           add_inst 8 7])]).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gc_move_bitmap_code_def" *)
Definition word_gc_move_bitmap_code (conf : data_to_word.config) : sprog :=
  While NotLower 7 (Imm (n2w 2))
   (If Test 7 (Imm (n2w 1))
      (list_Seq [right_shift_inst 7 1;
                 add_bytes_in_word_inst 8])
      (list_Seq [StackLoadAny 5 8;
                 right_shift_inst 7 1;
                 word_gc_move_code conf;
                 StackStoreAny 5 8;
                 add_bytes_in_word_inst 8])).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gc_move_bitmaps_code_def" *)
Definition word_gc_move_bitmaps_code (conf : data_to_word.config) : sprog :=
  While NotTest 0 (Reg 0)
    (list_Seq [BitmapLoad 7 9;
               word_gc_move_bitmap_code conf;
               BitmapLoad 0 9;
               add_1_inst 9;
               right_shift_inst 0 (dimindex a - 1)]).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gc_move_roots_bitmaps_code_def" *)
Definition word_gc_move_roots_bitmaps_code (conf : data_to_word.config) : sprog :=
  While NotTest 9 (Reg 9)
    (list_Seq [move 0 9;
               sub_1_inst 9;
               add_bytes_in_word_inst 8;
               word_gc_move_bitmaps_code conf;
               StackLoadAny 9 8]).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_move_code_def" *)
Definition word_gen_gc_move_code (conf : data_to_word.config) : sprog :=
  If Test 5 (Imm (n2w 1)) Skip
    (list_Seq
      [move 0 5;
       Get 1 CurrHeap;
       right_shift_inst 0 (shift_length conf);
       left_shift_inst 0 (word_shift a);
       add_inst 0 1;
       load_inst 1 0;
       If Test 1 (Imm (n2w 3))
         (list_Seq [right_shift_inst 1 2;
                    left_shift_inst 1 (shift_length conf);
                    clear_top_inst 5 (small_shift_length conf - 1);
                    or_inst 5 1])
         (list_Seq [move 6 1;
                    right_shift_inst 1 (dimindex a - len_size conf);
                    add_1_inst 1;
                    const_inst 2 (n2w 12);
                    and_inst 6 2;
                    If Equal 6 (Imm (n2w 8))
                      (list_Seq [
                        Set_ (Temp (n2w 0)) 3;
                        Set_ (Temp (n2w 1)) 4;
                        Get 3 (Temp (n2w 2));
                        Get 4 (Temp (n2w 3));
                        move 6 1;
                        left_shift_inst 1 (word_shift a);
                        sub_inst 4 6;
                        sub_inst 3 1;
                        Set_ (Temp (n2w 2)) 3;
                        Set_ (Temp (n2w 3)) 4;
                        move 2 0;
                        move 4 0;
                        move 0 6;
                        memcpy_code;
                        Get 0 (Temp (n2w 3));
                        left_shift_inst 0 2;
                        store_inst 0 4;
                        Get 1 (Temp (n2w 3));
                        clear_top_inst 5 (small_shift_length conf - 1);
                        left_shift_inst 1 (shift_length conf);
                        or_inst 5 1;
                        Get 3 (Temp (n2w 0));
                        Get 4 (Temp (n2w 1))])
                      (list_Seq [
                        move 6 1;
                        move 2 0;
                        move 0 1;
                        memcpy_code;
                        move 0 6;
                        left_shift_inst 0 (word_shift a);
                        sub_inst 2 0;
                        move 0 4;
                        left_shift_inst 0 2;
                        store_inst 0 2;
                        move 1 4;
                        clear_top_inst 5 (small_shift_length conf - 1);
                        left_shift_inst 1 (shift_length conf);
                        or_inst 5 1;
                        add_inst 4 6])])]).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_partial_move_code_def" *)
Definition word_gen_gc_partial_move_code (conf : data_to_word.config) : sprog :=
  If Test 5 (Imm (n2w 1)) Skip
    (list_Seq
      [move 0 5;
       Get 6 (Temp (n2w 0));
       right_shift_inst 0 (shift_length conf);
       left_shift_inst 0 (word_shift a);
       Get 1 (Temp (n2w 1));
       If Lower 0 (Reg 6) Skip
        (Seq (Get 6 (Temp (n2w 1)))
        (If NotLower 0 (Reg 1) Skip (list_Seq [
           Get 1 CurrHeap;
           add_inst 0 1;
           load_inst 1 0;
           If Test 1 (Imm (n2w 3))
             (list_Seq [right_shift_inst 1 2;
                        left_shift_inst 1 (shift_length conf);
                        clear_top_inst 5 (small_shift_length conf - 1);
                        or_inst 5 1])
             (list_Seq [move 6 1;
                        right_shift_inst 1 (dimindex a - len_size conf);
                        add_1_inst 1;
                        move 6 1;
                        move 2 0;
                        move 0 1;
                        memcpy_code;
                        move 0 6;
                        left_shift_inst 0 (word_shift a);
                        sub_inst 2 0;
                        move 0 4;
                        left_shift_inst 0 2;
                        store_inst 0 2;
                        move 1 4;
                        clear_top_inst 5 (small_shift_length conf - 1);
                        left_shift_inst 1 (shift_length conf);
                        or_inst 5 1;
                        add_inst 4 6])])))]).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_move_bitmap_code_def" *)
Definition word_gen_gc_move_bitmap_code (conf : data_to_word.config) : sprog :=
  While NotLower 7 (Imm (n2w 2))
   (If Test 7 (Imm (n2w 1))
      (list_Seq [right_shift_inst 7 1;
                 add_bytes_in_word_inst 8])
      (list_Seq [StackLoadAny 5 8;
                 right_shift_inst 7 1;
                 word_gen_gc_move_code conf;
                 StackStoreAny 5 8;
                 add_bytes_in_word_inst 8])).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_partial_move_bitmap_code_def" *)
Definition word_gen_gc_partial_move_bitmap_code (conf : data_to_word.config) : sprog :=
  While NotLower 7 (Imm (n2w 2))
   (If Test 7 (Imm (n2w 1))
      (list_Seq [right_shift_inst 7 1;
                 add_bytes_in_word_inst 8])
      (list_Seq [StackLoadAny 5 8;
                 right_shift_inst 7 1;
                 word_gen_gc_partial_move_code conf;
                 StackStoreAny 5 8;
                 add_bytes_in_word_inst 8])).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_move_bitmaps_code_def" *)
Definition word_gen_gc_move_bitmaps_code (conf : data_to_word.config) : sprog :=
  While NotTest 0 (Reg 0)
    (list_Seq [BitmapLoad 7 9;
               word_gen_gc_move_bitmap_code conf;
               BitmapLoad 0 9;
               add_1_inst 9;
               right_shift_inst 0 (dimindex a - 1)]).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_partial_move_bitmaps_code_def" *)
Definition word_gen_gc_partial_move_bitmaps_code (conf : data_to_word.config) : sprog :=
  While NotTest 0 (Reg 0)
    (list_Seq [BitmapLoad 7 9;
               word_gen_gc_partial_move_bitmap_code conf;
               BitmapLoad 0 9;
               add_1_inst 9;
               right_shift_inst 0 (dimindex a - 1)]).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_move_roots_bitmaps_code_def" *)
Definition word_gen_gc_move_roots_bitmaps_code (conf : data_to_word.config) : sprog :=
  While NotTest 9 (Reg 9)
    (list_Seq [move 0 9;
               sub_1_inst 9;
               add_bytes_in_word_inst 8;
               word_gen_gc_move_bitmaps_code conf;
               StackLoadAny 9 8]).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_partial_move_roots_bitmaps_code_def" *)
Definition word_gen_gc_partial_move_roots_bitmaps_code (conf : data_to_word.config) : sprog :=
  While NotTest 9 (Reg 9)
    (list_Seq [move 0 9;
               sub_1_inst 9;
               add_bytes_in_word_inst 8;
               word_gen_gc_partial_move_bitmaps_code conf;
               StackLoadAny 9 8]).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_move_list_code_def" *)
Definition word_gen_gc_move_list_code (conf : data_to_word.config) : sprog :=
  While NotEqual 7 (Imm (n2w 0))
    (list_Seq [load_inst 5 8;
               sub_1_inst 7;
               word_gen_gc_move_code conf;
               store_inst 5 8;
               add_bytes_in_word_inst 8]).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_partial_move_list_code_def" *)
Definition word_gen_gc_partial_move_list_code (conf : data_to_word.config) : sprog :=
  While NotEqual 7 (Imm (n2w 0))
    (list_Seq [load_inst 5 8;
               sub_1_inst 7;
               word_gen_gc_partial_move_code conf;
               store_inst 5 8;
               add_bytes_in_word_inst 8]).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_move_data_code_def" *)
Definition word_gen_gc_move_data_code (conf : data_to_word.config) : sprog :=
  While NotEqual 3 (Reg 8)
   (list_Seq [load_inst 7 8;
              If Test 7 (Imm (n2w 4))
                (list_Seq [right_shift_inst 7 (dimindex a - len_size conf);
                           add_bytes_in_word_inst 8;
                           word_gen_gc_move_list_code conf])
                (list_Seq [right_shift_inst 7 (dimindex a - len_size conf);
                           add_1_inst 7;
                           left_shift_inst 7 (word_shift a);
                           add_inst 8 7])]).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_partial_move_ref_list_code_def" *)
Definition word_gen_gc_partial_move_ref_list_code (conf : data_to_word.config) : sprog :=
  While NotEqual 9 (Reg 8)
   (list_Seq [load_inst 7 8;
              right_shift_inst 7 (dimindex a - len_size conf);
              add_bytes_in_word_inst 8;
              word_gen_gc_partial_move_list_code conf]).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_partial_move_data_code_def" *)
Definition word_gen_gc_partial_move_data_code (conf : data_to_word.config) : sprog :=
  While NotEqual 3 (Reg 8)
   (list_Seq [load_inst 7 8;
              If Test 7 (Imm (n2w 4))
                (list_Seq [right_shift_inst 7 (dimindex a - len_size conf);
                           add_bytes_in_word_inst 8;
                           word_gen_gc_partial_move_list_code conf])
                (list_Seq [right_shift_inst 7 (dimindex a - len_size conf);
                           add_1_inst 7;
                           left_shift_inst 7 (word_shift a);
                           add_inst 8 7])]).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_move_refs_code_def" *)
Definition word_gen_gc_move_refs_code (conf : data_to_word.config) : sprog :=
  While NotEqual 0 (Reg 8)
   (list_Seq [load_inst 7 8;
              right_shift_inst 7 (dimindex a - len_size conf);
              add_bytes_in_word_inst 8;
              word_gen_gc_move_list_code conf;
              Get 0 (Temp (n2w 4))]).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_move_loop_code_def" *)
Definition word_gen_gc_move_loop_code (conf : data_to_word.config) : sprog :=
  While NotTest 7 (Reg 7)
    (If Equal 1 (Reg 2)
       (list_Seq [word_gen_gc_move_data_code conf;
                  Get 5 (Temp (n2w 2));
                  Get 7 (Temp (n2w 4));
                  move 1 7;
                  move 2 5;
                  sub_inst 7 5])
       (list_Seq [move 0 1;
                  Set_ (Temp (n2w 6)) 8;
                  move 8 2;
                  Set_ (Temp (n2w 5)) 8;
                  word_gen_gc_move_refs_code conf;
                  move 7 8;
                  Get 1 (Temp (n2w 5));
                  Get 2 (Temp (n2w 5));
                  Set_ (Temp (n2w 4)) 2;
                  Get 2 (Temp (n2w 2));
                  move 3 3;
                  move 4 4;
                  move 7 1;
                  sub_inst 7 2;
                  Get 8 (Temp (n2w 6));
                  move 5 8;
                  sub_inst 5 3;
                  or_inst 7 5])).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gc_partial_or_full_def" *)
Definition word_gc_partial_or_full (gen_sizes : list N) (partial_code full_code : list sprog)
    : sprog :=
  match gen_sizes with
  | [] => list_Seq ([Get 8 TriggerGC; Get 7 EndOfHeap; sub_inst 7 8] ++ full_code)
  | _ => list_Seq
           [Get 8 TriggerGC;
            Get 7 EndOfHeap;
            sub_inst 7 8;
            If NotLower 7 (Reg 1)
              (list_Seq partial_code)
              (list_Seq full_code)]
  end.

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "SetNewTrigger_def" *)
Definition SetNewTrigger (endh ib : N) (gs : list N) : sprog :=
  list_Seq [const_inst 1 (get_gen_size gs : word a);
            Get 7 AllocSize;
            move 4 endh;
            sub_inst 4 ib;
            If Lower 1 (Reg 7)
              (If Lower 4 (Reg 7)
                 (Set_ TriggerGC endh)
                 (If Test 7 (Imm (if dimindex a =? 32 then n2w 3 else n2w 7))
                   (Seq (add_inst 7 ib) (Set_ TriggerGC 7))
                   (Set_ TriggerGC endh)))
              (If Lower 4 (Reg 1)
                 (Set_ TriggerGC endh)
                 (Seq (add_inst 1 ib) (Set_ TriggerGC 1)))].

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "word_gc_code_def" *)
Definition word_gc_code (conf : data_to_word.config) : sprog :=
  match gc_kind conf with
  | gc_kind_None =>
      list_Seq
        [Set_ AllocSize 1;
         Get 2 CurrHeap;
         Set_ NextFree 2;
         Set_ TriggerGC 2;
         Set_ EndOfHeap 2;
         If Test 1 (Reg 1) Skip (Seq (const_inst 1 (n2w 1)) (Halt 1))]
  | Simple =>
      list_Seq
        [Set_ AllocSize 1;
         Set_ NextFree 0;
         const_inst 1 (n2w 0);
         move 2 1;
         Get 3 OtherHeap;
         move 4 1;
         Get 5 Globals;
         move 6 1;
         move 8 1;
         word_gc_move_code conf;
         Set_ Globals 5;
         move 7 5;
         right_shift_inst 7 (shift_length conf);
         left_shift_inst 7 (word_shift a);
         Get 9 OtherHeap;
         add_inst 7 9;
         Set_ GlobReal 7;
         const_inst 7 (n2w 0);
         StackLoadAny 9 8;
         move 8 7;
         word_gc_move_roots_bitmaps_code conf;
         Get 8 OtherHeap;
         word_gc_move_loop_code conf;
         Get 0 CurrHeap;
         Get 1 OtherHeap;
         Get 2 HeapLength;
         add_inst 2 1;
         Set_ CurrHeap 1;
         Set_ OtherHeap 0;
         Get 0 NextFree;
         Set_ NextFree 8;
         Set_ EndOfHeap 2;
         Set_ TriggerGC 2;
         Get 1 AllocSize;
         sub_inst 2 8;
         If Lower 2 (Reg 1) (Seq (const_inst 1 (n2w 1)) (Halt 1)) Skip]
  | Generational gen_sizes =>
      word_gc_partial_or_full gen_sizes
        [Set_ AllocSize 1;
         Set_ NextFree 0;
         Get 4 GenStart;
         Get 5 EndOfHeap;
         Get 2 CurrHeap;
         Set_ (Temp (n2w 0)) 4;
         sub_inst 5 2;
         Set_ (Temp (n2w 1)) 5;
         Get 7 HeapLength;
         Get 5 Globals;
         Get 3 OtherHeap;
         right_shift_inst 4 (word_shift a);
         move 6 3;
         word_gen_gc_partial_move_code conf;
         Set_ Globals 5;
         move 8 5;
         right_shift_inst 8 (shift_length conf);
         left_shift_inst 8 (word_shift a);
         Get 9 CurrHeap;
         add_inst 8 9;
         Set_ GlobReal 8;
         const_inst 8 (n2w 0);
         StackLoadAny 9 8;
         word_gen_gc_partial_move_roots_bitmaps_code conf;
         Get 8 CurrHeap;
         Get 9 HeapLength;
         add_inst 9 8;
         Get 8 EndOfHeap;
         word_gen_gc_partial_move_ref_list_code conf;
         Get 8 OtherHeap;
         word_gen_gc_partial_move_data_code conf;
         Get 2 OtherHeap;
         move 0 3;
         sub_inst 0 2;
         right_shift_inst 0 (word_shift a);
         Get 3 GenStart;
         Get 1 CurrHeap;
         add_inst 3 1;
         memcpy_code;
         Get 0 NextFree;
         Set_ NextFree 3;
         Get 8 EndOfHeap;
         Get 2 TriggerGC;
         SetNewTrigger 8 3 gen_sizes;
         const_inst 1 (n2w 0);
         Set_ (Temp (n2w 0)) 1;
         Set_ (Temp (n2w 1)) 1;
         Get 1 AllocSize;
         sub_inst 8 3;
         Get 7 CurrHeap;
         sub_inst 3 7;
         Set_ GenStart 3]
        [Set_ AllocSize 1;
         Set_ NextFree 0;
         const_inst 1 (n2w 0);
         move 2 1;
         Get 3 OtherHeap;
         Get 4 HeapLength;
         add_inst 4 3;
         Set_ (Temp (n2w 0)) 4;
         Set_ (Temp (n2w 1)) 4;
         Set_ (Temp (n2w 2)) 4;
         Set_ (Temp (n2w 4)) 4;
         Set_ (Temp (n2w 5)) 4;
         Set_ (Temp (n2w 6)) 4;
         Get 4 HeapLength;
         right_shift_inst 4 (word_shift a);
         Set_ (Temp (n2w 3)) 4;
         move 4 1;
         Get 5 Globals;
         move 6 1;
         move 8 1;
         word_gen_gc_move_code conf;
         Set_ Globals 5;
         move 7 5;
         Get 9 OtherHeap;
         right_shift_inst 7 (shift_length conf);
         left_shift_inst 7 (word_shift a);
         add_inst 7 9;
         Set_ GlobReal 7;
         const_inst 7 (n2w 0);
         StackLoadAny 9 8;
         move 8 7;
         word_gen_gc_move_roots_bitmaps_code conf;
         Get 2 (Temp (n2w 2));
         Get 8 OtherHeap;
         move 7 3;
         sub_inst 7 8;
         Get 1 (Temp (n2w 6));
         move 6 2;
         sub_inst 6 1;
         or_inst 7 6;
         word_gen_gc_move_loop_code conf;
         Get 0 CurrHeap;
         Get 1 OtherHeap;
         Get 2 (Temp (n2w 2));
         Set_ CurrHeap 1;
         Set_ OtherHeap 0;
         Get 0 NextFree;
         Set_ NextFree 3;
         Set_ EndOfHeap 2;
         move 8 3;
         sub_inst 8 1;
         Set_ GenStart 8;
         SetNewTrigger 2 3 gen_sizes;
         const_inst 1 (n2w 0);
         Set_ (Temp (n2w 0)) 1;
         Set_ (Temp (n2w 1)) 1;
         Set_ (Temp (n2w 2)) 1;
         Set_ (Temp (n2w 3)) 1;
         Set_ (Temp (n2w 4)) 1;
         Set_ (Temp (n2w 5)) 1;
         Set_ (Temp (n2w 6)) 1;
         Get 1 AllocSize;
         Get 2 TriggerGC;
         sub_inst 2 3;
         If Lower 2 (Reg 1) (Seq (const_inst 1 (n2w 1)) (Halt 1)) Skip]
  end.

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "stubs_def" *)
Definition stubs (conf : data_to_word.config) : list (N * sprog) :=
  [(gc_stub_location, Seq (word_gc_code conf) (Return 0))].

(** ** The compiler *)

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "next_lab_def" *)
Fixpoint next_lab (p : sprog) (aux : N) : N :=
  match p with
  | Seq p1 p2 => next_lab p1 (next_lab p2 aux)
  | If _ _ _ p1 p2 => next_lab p1 (next_lab p2 aux)
  | Loop p => next_lab p aux
  | Call None _ None => aux
  | Call None _ (Some (_, (_, l2))) => MAX aux (l2 + 2)
  | Call (Some (p, (_, (_, l2)))) _ None => next_lab p (MAX aux (l2 + 2))
  | Call (Some (p, (_, (_, l2)))) _ (Some (p', (_, l3))) =>
      next_lab p (next_lab p' (MAX (MAX l2 l3 + 2) aux))
  | _ => aux
  end.

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "comp_def" *)
Fixpoint comp (n m : N) (p : sprog) : sprog * N :=
  match p with
  | Seq p1 p2 =>
      let '(q1, m) := comp n m p1 in
      let '(q2, m) := comp n m p2 in
      (Seq q1 q2, m)
  | If c r ri p1 p2 =>
      let '(q1, m) := comp n m p1 in
      let '(q2, m) := comp n m p2 in
      (If c r ri q1 q2, m)
  | Loop p1 =>
      let '(q1, m) := comp n m p1 in
      (Loop q1, m)
  | Call None dest exc => (Call None dest None, m)
  | Call (Some (p1, (lr, (l1, l2)))) dest exc =>
      let '(q1, m) := comp n m p1 in
      match exc with
      | None => (Call (Some (q1, (lr, (l1, l2)))) dest None, m)
      | Some (p2, (k1, k2)) =>
          let '(q2, m) := comp n m p2 in
          (Call (Some (q1, (lr, (l1, l2)))) dest (Some (q2, (k1, k2))), m)
      end
  | Alloc k => (Call (Some (Skip, (0, (n, m)))) (inl gc_stub_location) None, m + 1)
  | StoreConsts k1 k2 (Some loc) => (Call (Some (Skip, (0, (n, m)))) (inl loc) None, m + 1)
  | _ => (p, m)
  end.

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "prog_comp_def" *)
Definition prog_comp (np : N * sprog) : N * sprog :=
  let '(n, p) := np in (n, fst (comp n (next_lab p 2) p)).

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "compile_def" *)
Definition compile (c : data_to_word.config) (prog : list (N * sprog)) : list (N * sprog) :=
  stubs c ++ MAP prog_comp prog.

End StackAlloc.

(*! HOL "cakeml/compiler/backend/stack_allocScript.sml" "stub_names_def" *)
Definition stub_names (u : unit) : list (N * mlstring) := [(gc_stub_location, implode "_GC")].
