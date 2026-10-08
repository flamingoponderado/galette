(** * CakeML [labSem]: semantics of labLang

    Port of [cakeml/compiler/backend/semantics/labSemScript.sml].  Carrier
    notes:
    - [state] is a Rocq record with HOL's field names (types ['a], ['c],
      ['ffi] are [a : N], [c], [ffi_t]); HOL's [s with f := v] is
      [set_<f> v s] (helpers below).
    - HOL's functions [reg_imm] and [addr] have the names of ASM's types;
      the types are written [asm.reg_imm], [asm.addr] here.  HOL's overload
      [read_reg] is an [Abbreviation].
    - Constructor names: labLang's [Halt] (an instruction) is shadowed by
      targetSem's machine result [Halt] and written [labLang.Halt]; ASM's
      binops are written [asm.Add] etc.
    - Sets are [pred_set] sets ([_ -> Prop]); membership and equality on the
      abstract configuration type ['c] are decided classically.
    - FP: the [fp64_*] operations are the (unspecified, untagged) stand-ins
      of [machine_ieee.v]; [fpfma] is [fpSem.fpfma].
    - [asm_fetch_aux], [asm_code_length], [loc_to_pc], [get_lab_after]
      (HOL: recursion on the sections, then on the lines of the first
      section) are nested structural recursions; HOL's equations are the
      tagged [_def] theorems.
    - [evaluate] (HOL: well-founded recursion on the clock; every recursive
      call is at clock [s.clock - 1]) is a fuel-indexed recursion on the
      clock ([evaluate_f]); HOL's equation is the tagged [evaluate_def]. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.integer Require Import integer_word.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.HOL.src.floating_point Require Import binary_ieee machine_ieee.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.semantics Require fpSem.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.encoders.asm Require asmSem.
From Galette.cakeml.compiler.backend Require Import labLang.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend.semantics Require wordSem targetSem.
Import wordLang (word_loc, Word, Loc).
Import wordSem (buffer, buffer_flush, buffer_write, word_cmp, mem_load_byte_aux,
  mem_store_byte_aux, mem_load_32, mem_store_32, write_bytearray).
Import targetSem (machine_result(..), get_reg_value).
Import asmSem (word_shift).
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "word8_loc" *)
Inductive word8_loc : Type :=
| Byte : word8 -> word8_loc
| LocByte : N -> N -> N -> word8_loc.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "state" *)
Record state (a : N) (c : Type) (ffi_t : Type) : Type := mk_state {
  regs : N -> word_loc a;
  fp_regs : N -> word64;
  mem : word a -> word_loc a;
  mem_domain : word a -> Prop;
  shared_mem_domain : word a -> Prop;
  pc : N;
  be : bool;
  ffi : ffi_state ffi_t;
  io_regs : N -> ffiname -> N -> option (word a);
  cc_regs : N -> N -> option (word a);
  io_fp_regs : N -> N -> word64;
  cc_fp_regs : N -> N -> word64;
  code : labLang.prog a;
  compile : c -> labLang.prog a -> option (list word8 * c);
  compile_oracle : N -> c * labLang.prog a;
  code_buffer : buffer a 8;
  clock : N;
  failed : bool;
  ptr_reg : N;
  len_reg : N;
  ptr2_reg : N;
  len2_reg : N;
  link_reg : N
}.
Arguments mk_state {a c ffi_t}.
Arguments regs {a c ffi_t}. Arguments fp_regs {a c ffi_t}. Arguments mem {a c ffi_t}.
Arguments mem_domain {a c ffi_t}. Arguments shared_mem_domain {a c ffi_t}. Arguments pc {a c ffi_t}.
Arguments be {a c ffi_t}. Arguments ffi {a c ffi_t}. Arguments io_regs {a c ffi_t}.
Arguments cc_regs {a c ffi_t}. Arguments io_fp_regs {a c ffi_t}. Arguments cc_fp_regs {a c ffi_t}.
Arguments code {a c ffi_t}. Arguments compile {a c ffi_t}. Arguments compile_oracle {a c ffi_t}.
Arguments code_buffer {a c ffi_t}. Arguments clock {a c ffi_t}. Arguments failed {a c ffi_t}.
Arguments ptr_reg {a c ffi_t}. Arguments len_reg {a c ffi_t}. Arguments ptr2_reg {a c ffi_t}.
Arguments len2_reg {a c ffi_t}. Arguments link_reg {a c ffi_t}.

(** HOL [s with f := x] for each field. *)
Section Updates.
Context {a : N} {c ffi_t : Type}.
Definition set_regs x (s : state a c ffi_t) : state a c ffi_t := mk_state x s.(fp_regs) s.(mem) s.(mem_domain) s.(shared_mem_domain) s.(pc) s.(be) s.(ffi) s.(io_regs) s.(cc_regs) s.(io_fp_regs) s.(cc_fp_regs) s.(code) s.(compile) s.(compile_oracle) s.(code_buffer) s.(clock) s.(failed) s.(ptr_reg) s.(len_reg) s.(ptr2_reg) s.(len2_reg) s.(link_reg).
Definition set_fp_regs x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) x s.(mem) s.(mem_domain) s.(shared_mem_domain) s.(pc) s.(be) s.(ffi) s.(io_regs) s.(cc_regs) s.(io_fp_regs) s.(cc_fp_regs) s.(code) s.(compile) s.(compile_oracle) s.(code_buffer) s.(clock) s.(failed) s.(ptr_reg) s.(len_reg) s.(ptr2_reg) s.(len2_reg) s.(link_reg).
Definition set_mem x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) x s.(mem_domain) s.(shared_mem_domain) s.(pc) s.(be) s.(ffi) s.(io_regs) s.(cc_regs) s.(io_fp_regs) s.(cc_fp_regs) s.(code) s.(compile) s.(compile_oracle) s.(code_buffer) s.(clock) s.(failed) s.(ptr_reg) s.(len_reg) s.(ptr2_reg) s.(len2_reg) s.(link_reg).
Definition set_mem_domain x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(mem) x s.(shared_mem_domain) s.(pc) s.(be) s.(ffi) s.(io_regs) s.(cc_regs) s.(io_fp_regs) s.(cc_fp_regs) s.(code) s.(compile) s.(compile_oracle) s.(code_buffer) s.(clock) s.(failed) s.(ptr_reg) s.(len_reg) s.(ptr2_reg) s.(len2_reg) s.(link_reg).
Definition set_shared_mem_domain x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) x s.(pc) s.(be) s.(ffi) s.(io_regs) s.(cc_regs) s.(io_fp_regs) s.(cc_fp_regs) s.(code) s.(compile) s.(compile_oracle) s.(code_buffer) s.(clock) s.(failed) s.(ptr_reg) s.(len_reg) s.(ptr2_reg) s.(len2_reg) s.(link_reg).
Definition set_pc x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(shared_mem_domain) x s.(be) s.(ffi) s.(io_regs) s.(cc_regs) s.(io_fp_regs) s.(cc_fp_regs) s.(code) s.(compile) s.(compile_oracle) s.(code_buffer) s.(clock) s.(failed) s.(ptr_reg) s.(len_reg) s.(ptr2_reg) s.(len2_reg) s.(link_reg).
Definition set_be x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(shared_mem_domain) s.(pc) x s.(ffi) s.(io_regs) s.(cc_regs) s.(io_fp_regs) s.(cc_fp_regs) s.(code) s.(compile) s.(compile_oracle) s.(code_buffer) s.(clock) s.(failed) s.(ptr_reg) s.(len_reg) s.(ptr2_reg) s.(len2_reg) s.(link_reg).
Definition set_ffi x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(shared_mem_domain) s.(pc) s.(be) x s.(io_regs) s.(cc_regs) s.(io_fp_regs) s.(cc_fp_regs) s.(code) s.(compile) s.(compile_oracle) s.(code_buffer) s.(clock) s.(failed) s.(ptr_reg) s.(len_reg) s.(ptr2_reg) s.(len2_reg) s.(link_reg).
Definition set_io_regs x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(shared_mem_domain) s.(pc) s.(be) s.(ffi) x s.(cc_regs) s.(io_fp_regs) s.(cc_fp_regs) s.(code) s.(compile) s.(compile_oracle) s.(code_buffer) s.(clock) s.(failed) s.(ptr_reg) s.(len_reg) s.(ptr2_reg) s.(len2_reg) s.(link_reg).
Definition set_cc_regs x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(shared_mem_domain) s.(pc) s.(be) s.(ffi) s.(io_regs) x s.(io_fp_regs) s.(cc_fp_regs) s.(code) s.(compile) s.(compile_oracle) s.(code_buffer) s.(clock) s.(failed) s.(ptr_reg) s.(len_reg) s.(ptr2_reg) s.(len2_reg) s.(link_reg).
Definition set_io_fp_regs x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(shared_mem_domain) s.(pc) s.(be) s.(ffi) s.(io_regs) s.(cc_regs) x s.(cc_fp_regs) s.(code) s.(compile) s.(compile_oracle) s.(code_buffer) s.(clock) s.(failed) s.(ptr_reg) s.(len_reg) s.(ptr2_reg) s.(len2_reg) s.(link_reg).
Definition set_cc_fp_regs x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(shared_mem_domain) s.(pc) s.(be) s.(ffi) s.(io_regs) s.(cc_regs) s.(io_fp_regs) x s.(code) s.(compile) s.(compile_oracle) s.(code_buffer) s.(clock) s.(failed) s.(ptr_reg) s.(len_reg) s.(ptr2_reg) s.(len2_reg) s.(link_reg).
Definition set_code x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(shared_mem_domain) s.(pc) s.(be) s.(ffi) s.(io_regs) s.(cc_regs) s.(io_fp_regs) s.(cc_fp_regs) x s.(compile) s.(compile_oracle) s.(code_buffer) s.(clock) s.(failed) s.(ptr_reg) s.(len_reg) s.(ptr2_reg) s.(len2_reg) s.(link_reg).
Definition set_compile x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(shared_mem_domain) s.(pc) s.(be) s.(ffi) s.(io_regs) s.(cc_regs) s.(io_fp_regs) s.(cc_fp_regs) s.(code) x s.(compile_oracle) s.(code_buffer) s.(clock) s.(failed) s.(ptr_reg) s.(len_reg) s.(ptr2_reg) s.(len2_reg) s.(link_reg).
Definition set_compile_oracle x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(shared_mem_domain) s.(pc) s.(be) s.(ffi) s.(io_regs) s.(cc_regs) s.(io_fp_regs) s.(cc_fp_regs) s.(code) s.(compile) x s.(code_buffer) s.(clock) s.(failed) s.(ptr_reg) s.(len_reg) s.(ptr2_reg) s.(len2_reg) s.(link_reg).
Definition set_code_buffer x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(shared_mem_domain) s.(pc) s.(be) s.(ffi) s.(io_regs) s.(cc_regs) s.(io_fp_regs) s.(cc_fp_regs) s.(code) s.(compile) s.(compile_oracle) x s.(clock) s.(failed) s.(ptr_reg) s.(len_reg) s.(ptr2_reg) s.(len2_reg) s.(link_reg).
Definition set_clock x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(shared_mem_domain) s.(pc) s.(be) s.(ffi) s.(io_regs) s.(cc_regs) s.(io_fp_regs) s.(cc_fp_regs) s.(code) s.(compile) s.(compile_oracle) s.(code_buffer) x s.(failed) s.(ptr_reg) s.(len_reg) s.(ptr2_reg) s.(len2_reg) s.(link_reg).
Definition set_failed x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(shared_mem_domain) s.(pc) s.(be) s.(ffi) s.(io_regs) s.(cc_regs) s.(io_fp_regs) s.(cc_fp_regs) s.(code) s.(compile) s.(compile_oracle) s.(code_buffer) s.(clock) x s.(ptr_reg) s.(len_reg) s.(ptr2_reg) s.(len2_reg) s.(link_reg).
Definition set_ptr_reg x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(shared_mem_domain) s.(pc) s.(be) s.(ffi) s.(io_regs) s.(cc_regs) s.(io_fp_regs) s.(cc_fp_regs) s.(code) s.(compile) s.(compile_oracle) s.(code_buffer) s.(clock) s.(failed) x s.(len_reg) s.(ptr2_reg) s.(len2_reg) s.(link_reg).
Definition set_len_reg x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(shared_mem_domain) s.(pc) s.(be) s.(ffi) s.(io_regs) s.(cc_regs) s.(io_fp_regs) s.(cc_fp_regs) s.(code) s.(compile) s.(compile_oracle) s.(code_buffer) s.(clock) s.(failed) s.(ptr_reg) x s.(ptr2_reg) s.(len2_reg) s.(link_reg).
Definition set_ptr2_reg x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(shared_mem_domain) s.(pc) s.(be) s.(ffi) s.(io_regs) s.(cc_regs) s.(io_fp_regs) s.(cc_fp_regs) s.(code) s.(compile) s.(compile_oracle) s.(code_buffer) s.(clock) s.(failed) s.(ptr_reg) s.(len_reg) x s.(len2_reg) s.(link_reg).
Definition set_len2_reg x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(shared_mem_domain) s.(pc) s.(be) s.(ffi) s.(io_regs) s.(cc_regs) s.(io_fp_regs) s.(cc_fp_regs) s.(code) s.(compile) s.(compile_oracle) s.(code_buffer) s.(clock) s.(failed) s.(ptr_reg) s.(len_reg) s.(ptr2_reg) x s.(link_reg).
Definition set_link_reg x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(shared_mem_domain) s.(pc) s.(be) s.(ffi) s.(io_regs) s.(cc_regs) s.(io_fp_regs) s.(cc_fp_regs) s.(code) s.(compile) s.(compile_oracle) s.(code_buffer) s.(clock) s.(failed) s.(ptr_reg) s.(len_reg) s.(ptr2_reg) s.(len2_reg) x.
End Updates.

Section Fetch.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "is_Label_def" *)
Definition is_Label (l : line a) : bool :=
  match l with Label _ _ _ => true | _ => false end.

(** HOL [asm_fetch_aux]: recursion on the sections, then on the lines of
    the first section (nested structural recursion here). *)
Fixpoint asm_fetch_aux (pos : N) (secs : labLang.prog a) {struct secs} : option (line a) :=
  match secs with
  | [] => NONE
  | Section_ k lines :: xs =>
      (fix go (pos : N) (lines : list (line a)) {struct lines} : option (line a) :=
         match lines with
         | [] => asm_fetch_aux pos xs
         | y :: ys =>
             if is_Label y then go pos ys
             else if (pos =? 0)%N then SOME y
             else go (pos - 1) ys
         end) pos lines
  end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "asm_fetch_aux_def" *)
Theorem asm_fetch_aux_def :
  (forall pos, asm_fetch_aux pos [] = NONE) /\
  (forall pos k xs, asm_fetch_aux pos (Section_ k [] :: xs) = asm_fetch_aux pos xs) /\
  (forall pos k y ys xs,
     asm_fetch_aux pos (Section_ k (y :: ys) :: xs) =
     if is_Label y then asm_fetch_aux pos (Section_ k ys :: xs)
     else if (pos =? 0)%N then SOME y
     else asm_fetch_aux (pos - 1) (Section_ k ys :: xs)).
Proof. repeat split; reflexivity. Qed.

(** HOL [asm_code_length]: same recursion shape as [asm_fetch_aux]. *)
Fixpoint asm_code_length (secs : labLang.prog a) : N :=
  match secs with
  | [] => 0
  | Section_ k lines :: xs =>
      (fix go (lines : list (line a)) : N :=
         match lines with
         | [] => asm_code_length xs
         | y :: ys => go ys + (if is_Label y then 0 else 1)
         end) lines
  end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "asm_code_length_def" *)
Theorem asm_code_length_def :
  (asm_code_length [] = 0) /\
  (forall k xs, asm_code_length (Section_ k [] :: xs) = asm_code_length xs) /\
  (forall k y ys xs,
     asm_code_length (Section_ k (y :: ys) :: xs) =
     asm_code_length (Section_ k ys :: xs) + (if is_Label y then 0 else 1)).
Proof. repeat split; reflexivity. Qed.

(** HOL [loc_to_pc]: same recursion shape as [asm_fetch_aux]; HOL's
    [?k. z = Label n1 n2 k] is decided classically. *)
Fixpoint loc_to_pc (n1 n2 : N) (secs : labLang.prog a) {struct secs} : option N :=
  match secs with
  | [] => NONE
  | Section_ k xs :: ys =>
      (fix go (xs : list (line a)) {struct xs} : option N :=
         if andb (k =? n1) (n2 =? 0) then SOME 0 else
         match xs with
         | [] => loc_to_pc n1 n2 ys
         | z :: zs =>
             if andb ⌜exists k, z = Label n1 n2 k⌝ (negb (n2 =? 0)) then SOME 0 else
             if is_Label z then go zs
             else
               match go zs with
               | NONE => NONE
               | SOME pos => SOME (pos + 1)
               end
         end) xs
  end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "loc_to_pc_def" *)
Theorem loc_to_pc_def :
  (forall n1 n2, loc_to_pc n1 n2 [] = NONE) /\
  (forall n1 n2 k xs ys,
     loc_to_pc n1 n2 (Section_ k xs :: ys) =
     if andb (k =? n1) (n2 =? 0) then SOME 0 else
     match xs with
     | [] => loc_to_pc n1 n2 ys
     | z :: zs =>
         if andb ⌜exists k, z = Label n1 n2 k⌝ (negb (n2 =? 0)) then SOME 0 else
         if is_Label z then loc_to_pc n1 n2 (Section_ k zs :: ys)
         else
           match loc_to_pc n1 n2 (Section_ k zs :: ys) with
           | NONE => NONE
           | SOME pos => SOME (pos + 1)
           end
     end).
Proof. split; [reflexivity|]. intros n1 n2 k xs ys. destruct xs; reflexivity. Qed.

(** HOL [next_label]: same recursion shape as [asm_fetch_aux]. *)
Fixpoint next_label (secs : labLang.prog a) : option (word_loc a) :=
  match secs with
  | [] => NONE
  | Section_ k lines :: xs =>
      (fix go (lines : list (line a)) : option (word_loc a) :=
         match lines with
         | [] => next_label xs
         | Label n1 n2 _ :: ys => SOME (Loc n1 n2)
         | _ :: ys => go ys
         end) lines
  end.

(** HOL's equations; the overlapping last clause is stated, as HOL stores
    it, for the non-[Label] lines. *)
(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "next_label_def" *)
Theorem next_label_def :
  (next_label [] = NONE) /\
  (forall k xs, next_label (Section_ k [] :: xs) = next_label xs) /\
  (forall k n1 n2 l ys xs, next_label (Section_ k (Label n1 n2 l :: ys) :: xs) = SOME (Loc n1 n2)) /\
  (forall k v1 v2 v3 ys xs,
     next_label (Section_ k (Asm v1 v2 v3 :: ys) :: xs) = next_label (Section_ k ys :: xs)) /\
  (forall k v1 v2 v3 v4 ys xs,
     next_label (Section_ k (LabAsm v1 v2 v3 v4 :: ys) :: xs) = next_label (Section_ k ys :: xs)).
Proof. repeat split; reflexivity. Qed.

(** HOL [get_lab_after]: same recursion shape as [asm_fetch_aux]. *)
Fixpoint get_lab_after (pos : N) (secs : labLang.prog a) {struct secs} : option (word_loc a) :=
  match secs with
  | [] => NONE
  | Section_ k lines :: xs =>
      (fix go (pos : N) (lines : list (line a)) {struct lines} : option (word_loc a) :=
         match lines with
         | [] => get_lab_after pos xs
         | y :: ys =>
             if is_Label y then go pos ys
             else if (pos =? 0)%N then next_label (Section_ k ys :: xs)
             else go (pos - 1) ys
         end) pos lines
  end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "get_lab_after_def" *)
Theorem get_lab_after_def :
  (forall pos, get_lab_after pos [] = NONE) /\
  (forall pos k xs, get_lab_after pos (Section_ k [] :: xs) = get_lab_after pos xs) /\
  (forall pos k y ys xs,
     get_lab_after pos (Section_ k (y :: ys) :: xs) =
     if is_Label y then get_lab_after pos (Section_ k ys :: xs)
     else if (pos =? 0)%N then next_label (Section_ k ys :: xs)
     else get_lab_after (pos - 1) (Section_ k ys :: xs)).
Proof. repeat split; reflexivity. Qed.

End Fetch.

Section Ops.
Context {a : N} {c ffi_t : Type}.
Local Open Scope word_scope.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "asm_fetch_def" *)
Definition asm_fetch (s : state a c ffi_t) : option (line a) := asm_fetch_aux (pc s) (code s).

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "upd_pc_def" *)
Definition upd_pc (pc0 : N) (s : state a c ffi_t) : state a c ffi_t := set_pc pc0 s.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "upd_reg_def" *)
Definition upd_reg (r : N) (w : word_loc a) (s : state a c ffi_t) : state a c ffi_t :=
  set_regs ((r =+ w) (regs s)) s.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "upd_mem_def" *)
Definition upd_mem (ad : word a) (w : word_loc a) (s : state a c ffi_t) : state a c ffi_t :=
  set_mem ((ad =+ w) (mem s)) s.

End Ops.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "read_reg" *)
Abbreviation read_reg r s := (regs s r).

Section Ops2.
Context {a : N} {c ffi_t : Type}.
Local Open Scope word_scope.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "assert_def" *)
Definition assert (b : bool) (s : state a c ffi_t) : state a c ffi_t :=
  set_failed (orb (negb b) (failed s)) s.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "reg_imm_def" *)
Definition reg_imm (ri : asm.reg_imm a) (s : state a c ffi_t) : word_loc a :=
  match ri with
  | Reg r => read_reg r s
  | Imm w => Word w
  end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "binop_upd_def" *)
Definition binop_upd (r : N) (b : binop) (w1 w2 : word a) : state a c ffi_t -> state a c ffi_t :=
  match b with
  | asm.Add => upd_reg r (Word (w1 + w2))
  | asm.Sub => upd_reg r (Word (w1 - w2))
  | asm.And => upd_reg r (Word (word_and w1 w2))
  | asm.Or => upd_reg r (Word (word_or w1 w2))
  | asm.Xor => upd_reg r (Word (word_xor w1 w2))
  end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "arith_upd_def" *)
Definition arith_upd (x : arith a) (s : state a c ffi_t) : state a c ffi_t :=
  match x with
  | Binop b r1 r2 ri =>
      match read_reg r2 s, reg_imm ri s with
      | Word w1, Word w2 => binop_upd r1 b w1 w2 s
      | x, _ =>
          if andb (bool_decide (b = asm.Or)) (bool_decide (ri = Reg r2)) then upd_reg r1 x s
          else assert false s
      end
  | Shift l r1 r2 ri =>
      match read_reg r2 s, reg_imm ri s with
      | Word w1, Word w2 =>
          assert (w2n w2 <? dimindex a)%N (upd_reg r1 (Word (word_shift l w1 (w2n w2))) s)
      | _, _ => assert false s
      end
  | Div r1 r2 r3 =>
      match read_reg r3 s, read_reg r2 s with
      | Word q, Word w2 => assert (negb (bool_decide (q = n2w 0))) (upd_reg r1 (Word (word_quot w2 q)) s)
      | _, _ => assert false s
      end
  | AddCarry r1 r2 r3 r4 =>
      match read_reg r2 s, read_reg r3 s, read_reg r4 s with
      | Word w2, Word w3, Word w4 =>
          let r := (w2n w2 + w2n w3 + (if bool_decide (w4 = n2w 0) then 0 else 1))%N in
          upd_reg r4 (Word (if (dimword a <=? r)%N then n2w 1 else n2w 0))
            (upd_reg r1 (Word (n2w r)) s)
      | _, _, _ => assert false s
      end
  | LongMul r1 r2 r3 r4 =>
      match read_reg r3 s, read_reg r4 s with
      | Word w3, Word w4 =>
          let r := (w2n w3 * w2n w4)%N in
          upd_reg r2 (Word (n2w r)) (upd_reg r1 (Word (n2w (r DIV dimword a))) s)
      | _, _ => assert false s
      end
  | LongDiv r1 r2 r3 r4 r5 =>
      match read_reg r3 s, read_reg r4 s, read_reg r5 s with
      | Word w3, Word w4, Word w5 =>
          let n := (w2n w3 * dimword a + w2n w4)%N in
          let d := w2n w5 in
          let q := (n DIV d)%N in
          assert (andb (negb (d =? 0)%N) (q <? dimword a)%N)
            (upd_reg r1 (Word (n2w q)) (upd_reg r2 (Word (n2w (n MOD d))) s))
      | _, _, _ => assert false s
      end
  | AddOverflow r1 r2 r3 r4 =>
      match read_reg r2 s, read_reg r3 s with
      | Word w2, Word w3 =>
          upd_reg r4 (Word (if negb (Z.eqb (w2i (w2 + w3)) (w2i w2 + w2i w3)%Z) then n2w 1 else n2w 0))
            (upd_reg r1 (Word (w2 + w3)) s)
      | _, _ => assert false s
      end
  | SubOverflow r1 r2 r3 r4 =>
      match read_reg r2 s, read_reg r3 s with
      | Word w2, Word w3 =>
          upd_reg r4 (Word (if negb (Z.eqb (w2i (w2 - w3)) (w2i w2 - w2i w3)%Z) then n2w 1 else n2w 0))
            (upd_reg r1 (Word (w2 - w3)) s)
      | _, _ => assert false s
      end
  end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "upd_fp_reg_def" *)
Definition upd_fp_reg (r : N) (v : word64) (s : state a c ffi_t) : state a c ffi_t :=
  set_fp_regs ((r =+ v) (fp_regs s)) s.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "read_fp_reg_def" *)
Definition read_fp_reg (r : N) (s : state a c ffi_t) : word64 := fp_regs s r.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "fp_upd_def" *)
Definition fp_upd (f : fp) (s : state a c ffi_t) : state a c ffi_t :=
  match f with
  | FPLess r d1 d2 =>
      upd_reg r (Word (if fp64_lessThan (read_fp_reg d1 s) (read_fp_reg d2 s) then n2w 1 else n2w 0)) s
  | FPLessEqual r d1 d2 =>
      upd_reg r (Word (if fp64_lessEqual (read_fp_reg d1 s) (read_fp_reg d2 s) then n2w 1 else n2w 0)) s
  | FPEqual r d1 d2 =>
      upd_reg r (Word (if fp64_equal (read_fp_reg d1 s) (read_fp_reg d2 s) then n2w 1 else n2w 0)) s
  | FPMov d1 d2 => upd_fp_reg d1 (read_fp_reg d2 s) s
  | FPAbs d1 d2 => upd_fp_reg d1 (fp64_abs (read_fp_reg d2 s)) s
  | FPNeg d1 d2 => upd_fp_reg d1 (fp64_negate (read_fp_reg d2 s)) s
  | FPSqrt d1 d2 => upd_fp_reg d1 (fp64_sqrt roundTiesToEven (read_fp_reg d2 s)) s
  | FPAdd d1 d2 d3 =>
      upd_fp_reg d1 (fp64_add roundTiesToEven (read_fp_reg d2 s) (read_fp_reg d3 s)) s
  | FPSub d1 d2 d3 =>
      upd_fp_reg d1 (fp64_sub roundTiesToEven (read_fp_reg d2 s) (read_fp_reg d3 s)) s
  | FPMul d1 d2 d3 =>
      upd_fp_reg d1 (fp64_mul roundTiesToEven (read_fp_reg d2 s) (read_fp_reg d3 s)) s
  | FPDiv d1 d2 d3 =>
      upd_fp_reg d1 (fp64_div roundTiesToEven (read_fp_reg d2 s) (read_fp_reg d3 s)) s
  | FPFma d1 d2 d3 =>
      upd_fp_reg d1
        (fpSem.fpfma (read_fp_reg d1 s) (read_fp_reg d2 s) (read_fp_reg d3 s)) s
  | FPMovToReg r1 r2 d =>
      if (dimindex a =? 64)%N then upd_reg r1 (Word (w2w (read_fp_reg d s))) s
      else let v := read_fp_reg d s in
        upd_reg r2 (Word ((63 >< 32) v)) (upd_reg r1 (Word ((31 >< 0) v)) s)
  | FPMovFromReg d r1 r2 =>
      if (dimindex a =? 64)%N then
        match read_reg r1 s with
        | Word w1 => upd_fp_reg d (w2w w1) s
        | _ => assert false s
        end
      else
        match read_reg r1 s, read_reg r2 s with
        | Word w1, Word w2 => upd_fp_reg d (w2 @@ w1) s
        | _, _ => assert false s
        end
  | FPToInt d1 d2 =>
      match fp64_to_int roundTiesToEven (read_fp_reg d2 s) with
      | SOME i =>
          let w := (i2w i : word32) in
          (if (dimindex a =? 64)%N then upd_fp_reg d1 (w2w w)
           else let '(h, l) := if ODD d1 then (63, 32) else (31, 0) in
             upd_fp_reg (d1 DIV 2) (bit_field_insert h l w (read_fp_reg (d1 DIV 2) s)))
            (assert (Z.eqb (w2i w) i) s)
      | _ => assert false s
      end
  | FPFromInt d1 d2 =>
      let i := if (dimindex a =? 64)%N then w2i ((31 >< 0) (read_fp_reg d2 s) : word32)
               else let v := read_fp_reg (d2 DIV 2) s in
                 w2i (if ODD d2 then (63 >< 32) v else (31 >< 0) v : word a) in
      upd_fp_reg d1 (int_to_fp64 roundTiesToEven i) s
  end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "addr_def" *)
Definition addr (x : asm.addr a) (s : state a c ffi_t) : option (word a) :=
  match x with
  | Addr r offset =>
      match read_reg r s with
      | Word w => SOME (w + offset)
      | _ => NONE
      end
  end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "is_Loc_def" *)
Definition is_Loc (x : word_loc a) : bool :=
  match x with Loc _ _ => true | _ => false end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "mem_store_def" *)
Definition mem_store (r : N) (ad : asm.addr a) (s : state a c ffi_t) : state a c ffi_t :=
  match addr ad s with
  | NONE => assert false s
  | SOME w =>
      assert (andb ((w2n w MOD (dimindex a DIV 8)) =? 0)%N ⌜w IN mem_domain s⌝)
        (upd_mem w (read_reg r s) s)
  end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "mem_load_def" *)
Definition mem_load (r : N) (ad : asm.addr a) (s : state a c ffi_t) : state a c ffi_t :=
  match addr ad s with
  | NONE => assert false s
  | SOME w =>
      assert (andb ((w2n w MOD (dimindex a DIV 8)) =? 0)%N ⌜w IN mem_domain s⌝)
        (upd_reg r (mem s w) s)
  end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "mem_load32_def" *)
Definition mem_load32 (r : N) (ad : asm.addr a) (s : state a c ffi_t) : state a c ffi_t :=
  match addr ad s with
  | NONE => assert false s
  | SOME w =>
      match mem_load_32 (mem s) (mem_domain s) (be s) w with
      | SOME v => upd_reg r (Word (w2w v)) s
      | NONE => assert false s
      end
  end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "mem_store32_def" *)
Definition mem_store32 (r : N) (ad : asm.addr a) (s : state a c ffi_t) : state a c ffi_t :=
  match addr ad s with
  | NONE => assert false s
  | SOME w =>
      match read_reg r s with
      | Word b =>
          match mem_store_32 (mem s) (mem_domain s) (be s) w (w2w b) with
          | SOME m => set_mem m s
          | NONE => assert false s
          end
      | _ => assert false s
      end
  end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "mem_load_byte_def" *)
Definition mem_load_byte (r : N) (ad : asm.addr a) (s : state a c ffi_t) : state a c ffi_t :=
  match addr ad s with
  | NONE => assert false s
  | SOME w =>
      match mem_load_byte_aux (mem s) (mem_domain s) (be s) w with
      | SOME v => upd_reg r (Word (w2w v)) s
      | NONE => assert false s
      end
  end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "mem_store_byte_def" *)
Definition mem_store_byte (r : N) (ad : asm.addr a) (s : state a c ffi_t) : state a c ffi_t :=
  match addr ad s with
  | NONE => assert false s
  | SOME w =>
      match read_reg r s with
      | Word b =>
          match mem_store_byte_aux (mem s) (mem_domain s) (be s) w (w2w b) with
          | SOME m => set_mem m s
          | NONE => assert false s
          end
      | _ => assert false s
      end
  end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "mem_op_def" *)
Definition mem_op (m : memop) (r : N) (ad : asm.addr a) : state a c ffi_t -> state a c ffi_t :=
  match m with
  | Load => mem_load r ad
  | Store => mem_store r ad
  | Load32 => mem_load32 r ad
  | Store32 => mem_store32 r ad
  | Load8 => mem_load_byte r ad
  | Store8 => mem_store_byte r ad
  | Load16 => assert false
  | Store16 => assert false
  end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "asm_inst_def" *)
Definition asm_inst (i : asm.inst a) (s : state a c ffi_t) : state a c ffi_t :=
  match i with
  | asm.Skip => s
  | asm.Const r imm => upd_reg r (Word imm) s
  | Arith x => arith_upd x s
  | Mem m r ad => mem_op m r ad s
  | FP fp0 => fp_upd fp0 s
  end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "dec_clock_def" *)
Definition dec_clock (s : state a c ffi_t) : state a c ffi_t := set_clock (clock s - 1) s.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "inc_pc_def" *)
Definition inc_pc (s : state a c ffi_t) : state a c ffi_t := set_pc (pc s + 1) s.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "asm_fetch_IMP" *)
Theorem asm_fetch_IMP : forall (s : state a c ffi_t) x,
  asm_fetch s = SOME x -> (pc s < asm_code_length (code s))%N.
Proof.
  intros s x. unfold asm_fetch. generalize (pc s) as pos. generalize (code s) as secs.
  intros secs; induction secs as [|[k lines] xs IH]; intros pos H; [discriminate|].
  cbn [asm_fetch_aux asm_code_length] in *.
  revert pos H; induction lines as [|y ys IHl]; intros pos H.
  - apply IH in H; exact H.
  - destruct (is_Label y).
    + apply IHl in H; lia.
    + destruct (N.eqb_spec pos 0); [lia|].
      apply IHl in H; lia.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "lab_to_loc_def" *)
Definition lab_to_loc (l : lab) : word_loc a :=
  match l with Lab n1 n2 => Loc n1 n2 end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "get_pc_value_def" *)
Definition get_pc_value (l : lab) (s : state a c ffi_t) : option N :=
  match l with Lab n1 n2 => loc_to_pc n1 n2 (code s) end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "get_ret_Loc_def" *)
Definition get_ret_Loc (s : state a c ffi_t) : option (word_loc a) := get_lab_after (pc s) (code s).

End Ops2.

Section Consts.
Context {a : N} {c ffi_t : Type}.

Ltac consts_cbn :=
  cbn [asm_inst arith_upd binop_upd fp_upd mem_op mem_load mem_store mem_load32 mem_store32
       mem_load_byte mem_store_byte upd_reg upd_mem upd_fp_reg assert set_regs set_fp_regs
       set_mem set_failed pc code clock ffi io_regs io_fp_regs cc_regs cc_fp_regs ptr_reg
       len_reg ptr2_reg len2_reg link_reg].

Ltac consts_unfold :=
  consts_cbn;
  try unfold binop_upd; try unfold mem_op; try unfold fp_upd; try unfold arith_upd;
  try unfold mem_load; try unfold mem_store; try unfold mem_load32; try unfold mem_store32;
  try unfold mem_load_byte; try unfold mem_store_byte; try unfold addr;
  consts_cbn.

Ltac consts_tac :=
  consts_unfold;
  repeat first
    [ reflexivity
    | match goal with
      | |- context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta; consts_unfold
      end ].

Lemma asm_inst_pc_etc (i : asm.inst a) (s : state a c ffi_t) :
  pc (asm_inst i s) = pc s /\ code (asm_inst i s) = code s /\ clock (asm_inst i s) = clock s /\
  ffi (asm_inst i s) = ffi s /\ io_regs (asm_inst i s) = io_regs s /\
  io_fp_regs (asm_inst i s) = io_fp_regs s /\ cc_regs (asm_inst i s) = cc_regs s /\
  cc_fp_regs (asm_inst i s) = cc_fp_regs s /\ ptr_reg (asm_inst i s) = ptr_reg s /\
  len_reg (asm_inst i s) = len_reg s /\ ptr2_reg (asm_inst i s) = ptr2_reg s /\
  len2_reg (asm_inst i s) = len2_reg s /\ link_reg (asm_inst i s) = link_reg s.
Proof.
  destruct i as [| | x | m r ad | f]; [| | destruct x | destruct m | destruct f];
    repeat split; consts_tac.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "asm_inst_consts" *)
Theorem asm_inst_consts : forall (i : asm.inst a) (s : state a c ffi_t),
  pc (asm_inst i s) = pc s /\ code (asm_inst i s) = code s /\ clock (asm_inst i s) = clock s /\
  ffi (asm_inst i s) = ffi s /\ io_regs (asm_inst i s) = io_regs s /\
  io_fp_regs (asm_inst i s) = io_fp_regs s /\ cc_regs (asm_inst i s) = cc_regs s /\
  cc_fp_regs (asm_inst i s) = cc_fp_regs s /\ ptr_reg (asm_inst i s) = ptr_reg s /\
  len_reg (asm_inst i s) = len_reg s /\ ptr2_reg (asm_inst i s) = ptr2_reg s /\
  len2_reg (asm_inst i s) = len2_reg s /\ link_reg (asm_inst i s) = link_reg s.
Proof. exact asm_inst_pc_etc. Qed.

End Consts.

Section Share.
Context {a : N} {c ffi_t : Type}.
Local Open Scope word_scope.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "share_mem_load_def" *)
Definition share_mem_load (r : N) (ad : asm.addr a) (s : state a c ffi_t) (n : N)
    : option (ffi_result ffi_t * state a c ffi_t) :=
  match addr ad s with
  | NONE => NONE
  | SOME v =>
      if (if (n =? 0)%N
          then andb ((w2n v MOD (dimindex a DIV 8)) =? 0)%N ⌜v IN shared_mem_domain s⌝
          else ⌜byte_align v IN shared_mem_domain s⌝)
      then
        match call_FFI (ffi s) (SharedMem MappedRead) [n2w n] (word_to_bytes v false) with
        | FFI_final outcome => SOME (FFI_final outcome, s)
        | FFI_return new_ffi new_bytes =>
            SOME (FFI_return new_ffi new_bytes,
                  set_clock (clock s - 1) (set_pc (pc s + 1)
                    (set_regs ((r =+ Word (word_of_bytes false (n2w 0) new_bytes)) (regs s))
                      (set_ffi new_ffi s))))
        end
      else NONE
  end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "share_mem_store_def" *)
Definition share_mem_store (r : N) (ad : asm.addr a) (s : state a c ffi_t) (n : N)
    : option (ffi_result ffi_t * state a c ffi_t) :=
  match regs s r with
  | Word w =>
      match addr ad s with
      | NONE => NONE
      | SOME v =>
          if (if (n =? 0)%N
              then andb ((w2n v MOD (dimindex a DIV 8)) =? 0)%N ⌜v IN shared_mem_domain s⌝
              else ⌜byte_align v IN shared_mem_domain s⌝)
          then
            match call_FFI (ffi s) (SharedMem MappedWrite) [n2w n]
                    ((if (n =? 0)%N then word_to_bytes w false
                      else TAKE n (word_to_bytes w false)) ++ word_to_bytes v false) with
            | FFI_final outcome => SOME (FFI_final outcome, s)
            | FFI_return new_ffi new_bytes =>
                SOME (FFI_return new_ffi new_bytes, inc_pc (dec_clock (set_ffi new_ffi s)))
            end
          else NONE
      end
  | _ => NONE
  end.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "share_mem_op_def" *)
Definition share_mem_op (m : memop) (r : N) (ad : asm.addr a) (s : state a c ffi_t)
    : option (ffi_result ffi_t * state a c ffi_t) :=
  match m with
  | Load => share_mem_load r ad s 0
  | Load8 => share_mem_load r ad s 1
  | Load16 => share_mem_load r ad s 2
  | Store => share_mem_store r ad s 0
  | Store8 => share_mem_store r ad s 1
  | Store16 => share_mem_store r ad s 2
  | Load32 => share_mem_load r ad s 4
  | Store32 => share_mem_store r ad s 4
  end.

Lemma share_mem_op_clock m r ad (s s' : state a c ffi_t) x y :
  share_mem_op m r ad s = SOME (FFI_return x y, s') -> clock s' = (clock s - 1)%N.
Proof.
  destruct m; cbn [share_mem_op]; unfold share_mem_load, share_mem_store;
    intros H;
    repeat match type of H with
           | context [match ?z with _ => _ end] =>
               let E := fresh "E" in destruct z eqn:E; cbn beta iota zeta in H
           end; try discriminate;
    injection H as _ _ <-; reflexivity.
Qed.

End Share.

(** ** [evaluate]

    One step of HOL's [evaluate] is [evaluate_body rec s], with [rec] for
    the recursive calls (all at clock [clock s - 1]); [evaluate_f] iterates
    it with a fuel and [evaluate] uses a fuel above the clock.  HOL names
    the ASM instruction in [Asm (Asmi a) _ _] [a]; it is [a0] here. *)

Section Evaluate.
Context {a : N} {c ffi_t : Type}.
Local Open Scope word_scope.

Definition evaluate_body (rec : state a c ffi_t -> machine_result * state a c ffi_t)
    (s : state a c ffi_t) : machine_result * state a c ffi_t :=
  if (clock s =? 0)%N then (TimeOut, s) else
  match asm_fetch s with
  | SOME (Asm (Asmi a0) _ _) =>
      match a0 with
      | Inst i =>
          let s1 := asm_inst i s in
          if failed s1 then (Error, s)
          else rec (inc_pc (dec_clock s1))
      | JumpReg r =>
          match read_reg r s with
          | Loc n1 n2 =>
              match loc_to_pc n1 n2 (code s) with
              | NONE => (Error, s)
              | SOME p => rec (upd_pc p (dec_clock s))
              end
          | _ => (Error, s)
          end
      | _ => (Error, s)
      end
  | SOME (Asm (Cbw r1 r2) _ _) =>
      match read_reg r1 s, read_reg r2 s with
      | Word w1, Word w2 =>
          match buffer_write (code_buffer s) w1 (w2w w2) with
          | SOME new_cb => rec (inc_pc (dec_clock (set_code_buffer new_cb s)))
          | _ => (Error, s)
          end
      | _, _ => (Error, s)
      end
  | SOME (Asm (ShareMem m r ad) _ _) =>
      match share_mem_op m r ad s with
      | SOME (FFI_final outcome, s') => (Halt (FFI_outcome outcome), s')
      | SOME (FFI_return _ _, s') =>
          rec (set_io_fp_regs (shift_seq 1 (io_fp_regs s'))
                 (set_io_regs (shift_seq 1 (io_regs s')) s'))
      | NONE => (Error, s)
      end
  | SOME (LabAsm labLang.Halt _ _ _) =>
      match regs s (ptr_reg s) with
      | Word w => if bool_decide (w = n2w 0) then (Halt Success, s) else (Halt Resource_limit_hit, s)
      | _ => (Error, s)
      end
  | SOME (LabAsm (LocValue r lab0) _ _ _) =>
      if bool_decide (get_pc_value lab0 s = NONE) then (Error, s) else
        let s1 := upd_reg r (lab_to_loc lab0) s in
        rec (inc_pc (dec_clock s1))
  | SOME (LabAsm (Jump l) _ _ _) =>
      match get_pc_value l s with
      | NONE => (Error, s)
      | SOME p => rec (upd_pc p (dec_clock s))
      end
  | SOME (LabAsm (JumpCmp c0 r ri l) _ _ _) =>
      match word_cmp c0 (read_reg r s) (reg_imm ri s) with
      | NONE => (Error, s)
      | SOME false => rec (inc_pc (dec_clock s))
      | SOME true =>
          match get_pc_value l s with
          | NONE => (Error, s)
          | SOME p => rec (upd_pc p (dec_clock s))
          end
      end
  | SOME (LabAsm (Call l) _ _ _) =>
      match get_pc_value l s with
      | NONE => (Error, s)
      | SOME p =>
          match get_ret_Loc s with
          | NONE => (Error, s)
          | SOME k =>
              let s1 := upd_reg (link_reg s) k s in
              rec (upd_pc p (dec_clock s1))
          end
      end
  | SOME (LabAsm Install _ _ _) =>
      match regs s (ptr_reg s), regs s (len_reg s), regs s (link_reg s) with
      | Word w1, Word w2, Loc n1 n2 =>
          match buffer_flush (code_buffer s) w1 w2, loc_to_pc n1 n2 (code s) with
          | SOME (bytes, cb), SOME new_pc =>
              let '(cfg, prog0) := compile_oracle s 0 in
              let new_oracle := shift_seq 1 (compile_oracle s) in
              match compile s cfg prog0, prog0 with
              | SOME (bytes', cfg'), Section_ k _ :: _ =>
                  if andb (bool_decide (bytes = bytes')) ⌜FST (new_oracle 0) = cfg'⌝ then
                    rec (mk_state
                           ((ptr_reg s =+ Loc k 0)
                              (fun a0 => get_reg_value (cc_regs s 0 a0) (regs s a0) Word))
                           (fun n => cc_fp_regs s 0 n)
                           (mem s) (mem_domain s) (shared_mem_domain s) new_pc (be s) (ffi s)
                           (io_regs s) (shift_seq 1 (cc_regs s)) (io_fp_regs s)
                           (shift_seq 1 (cc_fp_regs s)) (code s ++ prog0) (compile s) new_oracle
                           cb (clock s - 1) (failed s) (ptr_reg s) (len_reg s) (ptr2_reg s)
                           (len2_reg s) (link_reg s))
                  else (Error, s)
              | _, _ => (Error, s)
              end
          | _, _ => (Error, s)
          end
      | _, _, _ => (Error, s)
      end
  | SOME (LabAsm (CallFFI ffi_index) _ _ _) =>
      match regs s (len_reg s), regs s (ptr_reg s), regs s (len2_reg s), regs s (ptr2_reg s),
            regs s (link_reg s) with
      | Word w, Word w2, Word w3, Word w4, Loc n1 n2 =>
          match read_bytearray w2 (w2n w) (mem_load_byte_aux (mem s) (mem_domain s) (be s)),
                read_bytearray w4 (w2n w3) (mem_load_byte_aux (mem s) (mem_domain s) (be s)),
                loc_to_pc n1 n2 (code s) with
          | SOME bytes, SOME bytes2, SOME new_pc =>
              match call_FFI (ffi s) (ExtCall ffi_index) bytes bytes2 with
              | FFI_final outcome => (Halt (FFI_outcome outcome), s)
              | FFI_return new_ffi new_bytes =>
                  let new_io_regs := shift_seq 1 (io_regs s) in
                  let new_io_fp_regs := shift_seq 1 (io_fp_regs s) in
                  let new_m := write_bytearray w4 new_bytes (mem s) (mem_domain s) (be s) in
                  rec (mk_state
                         (fun a0 => get_reg_value (io_regs s 0 (ExtCall ffi_index) a0) (regs s a0) Word)
                         (fun n => io_fp_regs s 0 n)
                         new_m (mem_domain s) (shared_mem_domain s) new_pc (be s) new_ffi
                         new_io_regs (cc_regs s) new_io_fp_regs (cc_fp_regs s) (code s)
                         (compile s) (compile_oracle s) (code_buffer s) (clock s - 1) (failed s)
                         (ptr_reg s) (len_reg s) (ptr2_reg s) (len2_reg s) (link_reg s))
              end
          | _, _, _ => (Error, s)
          end
      | _, _, _, _, _ => (Error, s)
      end
  | _ => (Error, s)
  end.

Fixpoint evaluate_f (n : nat) (s : state a c ffi_t) : machine_result * state a c ffi_t :=
  match n with
  | O => (TimeOut, s)
  | Datatypes.S n' => evaluate_body (evaluate_f n') s
  end.

(** HOL [evaluate]: run with a fuel above the clock. *)
Definition evaluate (s : state a c ffi_t) : machine_result * state a c ffi_t :=
  evaluate_f (Datatypes.S (N.to_nat (clock s))) s.

Lemma asm_inst_clock (i : asm.inst a) (s : state a c ffi_t) : clock (asm_inst i s) = clock s.
Proof. apply asm_inst_consts. Qed.

Ltac clock_lt :=
  repeat match goal with
         | H : (clock _ =? 0)%N = false |- _ => apply N.eqb_neq in H
         | H : share_mem_op _ _ _ _ = SOME (FFI_return _ _, _) |- _ =>
             apply share_mem_op_clock in H
         end;
  cbn [clock inc_pc dec_clock upd_pc upd_reg set_pc set_clock set_regs set_code_buffer
       set_io_regs set_io_fp_regs] in *;
  rewrite ?asm_inst_clock; lia.

Lemma evaluate_body_ext (rec1 rec2 : state a c ffi_t -> machine_result * state a c ffi_t) s :
  (forall s', (clock s' < clock s)%N -> rec1 s' = rec2 s') ->
  evaluate_body rec1 s = evaluate_body rec2 s.
Proof.
  intros Hrec. unfold evaluate_body.
  repeat first
    [ reflexivity
    | match goal with
      | |- context [rec1 ?s'] => rewrite (Hrec s') by clock_lt
      end
    | match goal with
      | |- context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
      end ].
Qed.

Lemma evaluate_f_fuel : forall n1 n2 (s : state a c ffi_t),
  (N.to_nat (clock s) < n1)%nat -> (N.to_nat (clock s) < n2)%nat ->
  evaluate_f n1 s = evaluate_f n2 s.
Proof.
  induction n1 as [|n1 IH]; intros n2 s H1 H2; [lia|].
  destruct n2 as [|n2]; [lia|]. cbn [evaluate_f].
  apply evaluate_body_ext. intros s' Hs. apply IH; lia.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "evaluate_def" *)
Theorem evaluate_def : forall s : state a c ffi_t,
  evaluate s =
    if (clock s =? 0)%N then (TimeOut, s) else
    match asm_fetch s with
    | SOME (Asm (Asmi a0) _ _) =>
        match a0 with
        | Inst i =>
            let s1 := asm_inst i s in
            if failed s1 then (Error, s)
            else evaluate (inc_pc (dec_clock s1))
        | JumpReg r =>
            match read_reg r s with
            | Loc n1 n2 =>
                match loc_to_pc n1 n2 (code s) with
                | NONE => (Error, s)
                | SOME p => evaluate (upd_pc p (dec_clock s))
                end
            | _ => (Error, s)
            end
        | _ => (Error, s)
        end
    | SOME (Asm (Cbw r1 r2) _ _) =>
        match read_reg r1 s, read_reg r2 s with
        | Word w1, Word w2 =>
            match buffer_write (code_buffer s) w1 (w2w w2) with
            | SOME new_cb => evaluate (inc_pc (dec_clock (set_code_buffer new_cb s)))
            | _ => (Error, s)
            end
        | _, _ => (Error, s)
        end
    | SOME (Asm (ShareMem m r ad) _ _) =>
        match share_mem_op m r ad s with
        | SOME (FFI_final outcome, s') => (Halt (FFI_outcome outcome), s')
        | SOME (FFI_return _ _, s') =>
            evaluate (set_io_fp_regs (shift_seq 1 (io_fp_regs s'))
                   (set_io_regs (shift_seq 1 (io_regs s')) s'))
        | NONE => (Error, s)
        end
    | SOME (LabAsm labLang.Halt _ _ _) =>
        match regs s (ptr_reg s) with
        | Word w => if bool_decide (w = n2w 0) then (Halt Success, s) else (Halt Resource_limit_hit, s)
        | _ => (Error, s)
        end
    | SOME (LabAsm (LocValue r lab0) _ _ _) =>
        if bool_decide (get_pc_value lab0 s = NONE) then (Error, s) else
          let s1 := upd_reg r (lab_to_loc lab0) s in
          evaluate (inc_pc (dec_clock s1))
    | SOME (LabAsm (Jump l) _ _ _) =>
        match get_pc_value l s with
        | NONE => (Error, s)
        | SOME p => evaluate (upd_pc p (dec_clock s))
        end
    | SOME (LabAsm (JumpCmp c0 r ri l) _ _ _) =>
        match word_cmp c0 (read_reg r s) (reg_imm ri s) with
        | NONE => (Error, s)
        | SOME false => evaluate (inc_pc (dec_clock s))
        | SOME true =>
            match get_pc_value l s with
            | NONE => (Error, s)
            | SOME p => evaluate (upd_pc p (dec_clock s))
            end
        end
    | SOME (LabAsm (Call l) _ _ _) =>
        match get_pc_value l s with
        | NONE => (Error, s)
        | SOME p =>
            match get_ret_Loc s with
            | NONE => (Error, s)
            | SOME k =>
                let s1 := upd_reg (link_reg s) k s in
                evaluate (upd_pc p (dec_clock s1))
            end
        end
    | SOME (LabAsm Install _ _ _) =>
        match regs s (ptr_reg s), regs s (len_reg s), regs s (link_reg s) with
        | Word w1, Word w2, Loc n1 n2 =>
            match buffer_flush (code_buffer s) w1 w2, loc_to_pc n1 n2 (code s) with
            | SOME (bytes, cb), SOME new_pc =>
                let '(cfg, prog0) := compile_oracle s 0 in
                let new_oracle := shift_seq 1 (compile_oracle s) in
                match compile s cfg prog0, prog0 with
                | SOME (bytes', cfg'), Section_ k _ :: _ =>
                    if andb (bool_decide (bytes = bytes')) ⌜FST (new_oracle 0) = cfg'⌝ then
                      evaluate (mk_state
                             ((ptr_reg s =+ Loc k 0)
                                (fun a0 => get_reg_value (cc_regs s 0 a0) (regs s a0) Word))
                             (fun n => cc_fp_regs s 0 n)
                             (mem s) (mem_domain s) (shared_mem_domain s) new_pc (be s) (ffi s)
                             (io_regs s) (shift_seq 1 (cc_regs s)) (io_fp_regs s)
                             (shift_seq 1 (cc_fp_regs s)) (code s ++ prog0) (compile s) new_oracle
                             cb (clock s - 1) (failed s) (ptr_reg s) (len_reg s) (ptr2_reg s)
                             (len2_reg s) (link_reg s))
                    else (Error, s)
                | _, _ => (Error, s)
                end
            | _, _ => (Error, s)
            end
        | _, _, _ => (Error, s)
        end
    | SOME (LabAsm (CallFFI ffi_index) _ _ _) =>
        match regs s (len_reg s), regs s (ptr_reg s), regs s (len2_reg s), regs s (ptr2_reg s),
              regs s (link_reg s) with
        | Word w, Word w2, Word w3, Word w4, Loc n1 n2 =>
            match read_bytearray w2 (w2n w) (mem_load_byte_aux (mem s) (mem_domain s) (be s)),
                  read_bytearray w4 (w2n w3) (mem_load_byte_aux (mem s) (mem_domain s) (be s)),
                  loc_to_pc n1 n2 (code s) with
            | SOME bytes, SOME bytes2, SOME new_pc =>
                match call_FFI (ffi s) (ExtCall ffi_index) bytes bytes2 with
                | FFI_final outcome => (Halt (FFI_outcome outcome), s)
                | FFI_return new_ffi new_bytes =>
                    let new_io_regs := shift_seq 1 (io_regs s) in
                    let new_io_fp_regs := shift_seq 1 (io_fp_regs s) in
                    let new_m := write_bytearray w4 new_bytes (mem s) (mem_domain s) (be s) in
                    evaluate (mk_state
                           (fun a0 => get_reg_value (io_regs s 0 (ExtCall ffi_index) a0) (regs s a0) Word)
                           (fun n => io_fp_regs s 0 n)
                           new_m (mem_domain s) (shared_mem_domain s) new_pc (be s) new_ffi
                           new_io_regs (cc_regs s) new_io_fp_regs (cc_fp_regs s) (code s)
                           (compile s) (compile_oracle s) (code_buffer s) (clock s - 1) (failed s)
                           (ptr_reg s) (len_reg s) (ptr2_reg s) (len2_reg s) (link_reg s))
                end
            | _, _, _ => (Error, s)
            end
        | _, _, _, _, _ => (Error, s)
        end
    | _ => (Error, s)
    end.
Proof.
  intros s. transitivity (evaluate_body evaluate s); [|reflexivity].
  unfold evaluate at 1. cbn [evaluate_f].
  apply evaluate_body_ext. intros s' Hs. unfold evaluate.
  apply evaluate_f_fuel; lia.
Qed.

End Evaluate.

(** ** Observable semantics *)
Section Semantics.
Context {a : N} {c ffi_t : Type}.

#[local] Instance behaviour_inhabited : Inhabited behaviour := Fail.

(*! HOL "cakeml/compiler/backend/semantics/labSemScript.sml" "semantics_def" *)
Definition semantics (s : state a c ffi_t) : behaviour :=
  if classical_dec (exists k, FST (evaluate (set_clock k s)) = Error) then Fail
  else
    match some (fun res => exists k t outcome,
             evaluate (set_clock k s) = (Halt outcome, t) /\
             res = Terminate outcome (io_events (ffi t))) with
    | SOME res => res
    | NONE =>
        Diverge (build_lprefix_lub
                   (IMAGE (fun k => fromList (io_events (ffi (SND (evaluate (set_clock k s))))))
                          UNIV))
    end.

End Semantics.
