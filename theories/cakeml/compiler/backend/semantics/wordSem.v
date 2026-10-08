(** * CakeML [wordSem]: the semantics of wordLang

    Port of [cakeml/compiler/backend/semantics/wordSemScript.sml].
    Carrier notes:
    - HOL's type parameters ['a] (word width), ['c] (compiler configuration)
      and ['ffi] are [a : N], [c : Type] and [ffi_t : Type]; [state a c ffi_t]
      is a Rocq record with HOL's fields in HOL's order.  HOL's
      [s with f := v] is [set_<f> v s] (helpers below).  Two field names
      clash with constants of this module and carry HOL's internal record
      prefix: the field [stack_size] is [state_stack_size] (the constant
      [stack_size] sums frame sizes), and the field [buffer] of the record
      [buffer] is [buffer_buffer].  The helper for the field [store] is
      [set_store_field] ([set_store] is HOL's [set_store_def]).
    - HOL tuples nest to the right ([a # b # c] is [a * (b * c)]).
    - Sets are [pred_set] predicates; the semantics is not executable, so
      classical decisions ([classical_dec], [⌜_⌝]) decide set membership,
      set equality and equality on the abstract configuration type [c].
    - [evaluate] (HOL: well-founded recursion on
      [(termdep, clock, prog_size)]) is defined with fuels, following
      [panSem]: [evaluate_body go lower deeper] is one step, with [go] for
      structurally smaller programs, [lower] for calls at a smaller clock and
      [deeper] for the [MustTerminate] call (smaller [termdep]).
      [evaluate_eqn] shows that [evaluate] is a fixed point of that step and
      HOL's equations are the tagged [evaluate_def] (HOL's rebound version,
      with [fix_clock] removed).

    - The floating-point instructions of [inst] use the [machine_ieee]
      stand-ins (unspecified values until [machine_ieee] is ported).

    Not ported (see the docstrings):
    - [mem_load_32_alt] (needs bit-blasting of [word_of_bytes]);
    - HOL's [evaluate_ind] (the recursion-induction principle; use
      well-founded induction on [eval_lt] instead).

    [fromList2] (HOL [miscScript]) and [LASTN] (HOL [rich_listScript]) are
    not yet in the shared libraries; local untagged copies are defined
    below. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.integer Require Import integer_word.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map sptree.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.src.floating_point Require Import binary_ieee machine_ieee.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.cakeml.basis.pure Require Import mlstring mllist.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang wordLang.
Open Scope N_scope.

(** Local copies of library definitions not yet ported in their own
    modules (HOL [miscScript]'s [fromList2_def], [rich_listScript]'s
    [LASTN_def]); untagged here, to be moved. *)
Definition fromList2 {A} (l : list A) : num_map A :=
  snd (FOLDL (fun '(i, t) a0 => (i + 2, insert i a0 t)) (0, LN) l).

Definition LASTN {A} (n : N) (xs : list A) : list A := REVERSE (TAKE n (REVERSE xs)).

(** ** Code and data buffers *)

(** The field [buffer] is [buffer_buffer] (HOL's internal name), since the
    record type is also called [buffer]. *)
(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "buffer" *)
Record buffer (a b : N) : Type := mk_buffer {
  position : word a;
  buffer_buffer : list (word b);
  space_left : N
}.
Arguments mk_buffer {a b}.
Arguments position {a b}.
Arguments buffer_buffer {a b}.
Arguments space_left {a b}.

Section Buffers.
Context {a b : N}.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "buffer_flush_def" *)
Definition buffer_flush (cb : buffer a b) (w1 w2 : word a)
    : option (list (word b) * buffer a b) :=
  if bool_decide (position cb = w1) &&
     bool_decide ((position cb + n2w (dimindex b DIV 8) * n2w (LENGTH (buffer_buffer cb)))%w = w2)
  then SOME (buffer_buffer cb, mk_buffer w2 [] (space_left cb))
  else NONE.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "buffer_write_def" *)
Definition buffer_write (cb : buffer a b) (w : word a) (b0 : word b) : option (buffer a b) :=
  if bool_decide ((position cb + n2w (dimindex b DIV 8) * n2w (LENGTH (buffer_buffer cb)))%w = w) &&
     (0 <? space_left cb)
  then SOME (mk_buffer (position cb) (buffer_buffer cb ++ [b0]) (space_left cb - 1))
  else NONE.

End Buffers.

(** ** Words and locations *)

Section WordLoc.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "is_fwd_ptr_def" *)
Definition is_fwd_ptr (x : word_loc a) : bool :=
  match x with
  | Word w => bool_decide ((w && n2w 3)%w = n2w 0)
  | _ => false
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "theWord_def" *)
Definition theWord (x : word_loc a) : word a :=
  match x with Word w => w | _ => ARB end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "isWord_def" *)
Definition isWord (x : word_loc a) : bool :=
  match x with Word w => true | _ => false end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "isWord_exists" *)
Theorem isWord_exists : forall (x : word_loc a), isWord x <-> exists w, x = Word w.
Proof.
  intros [w|l n]; cbn; split.
  - intros _; exists w; reflexivity.
  - intros _; reflexivity.
  - discriminate.
  - intros [w Hw]; discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "word_cmp_def" *)
Definition word_cmp (cmp0 : cmp) (x y : word_loc a) : option bool :=
  match cmp0, x, y with
  | Equal, Word w1, Word w2 => SOME (bool_decide (w1 = w2))
  | Less, Word w1, Word w2 => SOME (w1 < w2)%w
  | Lower, Word w1, Word w2 => SOME (w1 <+ w2)%w
  | Test, Word w1, Word w2 => SOME (bool_decide ((w1 && w2)%w = n2w 0))
  | Test, Loc _ n, Word w2 =>
      if negb (n =? 0) then NONE else if bool_decide (w2 = n2w 1) then SOME true else NONE
  | NotEqual, Word w1, Word w2 => SOME (negb (bool_decide (w1 = w2)))
  | NotLess, Word w1, Word w2 => SOME (negb (w1 < w2)%w)
  | NotLower, Word w1, Word w2 => SOME (negb (w1 <+ w2)%w)
  | NotTest, Word w1, Word w2 => SOME (negb (bool_decide ((w1 && w2)%w = n2w 0)))
  | NotTest, Loc _ n, Word w2 =>
      if negb (n =? 0) then NONE else if bool_decide (w2 = n2w 1) then SOME false else NONE
  | _, _, _ => NONE
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "mem_load_32_def" *)
Definition mem_load_32 (m : word a -> word_loc a) (dm : word a -> Prop) (be : bool)
    (w : word a) : option word32 :=
  if aligned 2 w then
    match m (byte_align w) with
    | Loc _ _ => NONE
    | Word v =>
        if classical_dec (byte_align w IN dm)
        then SOME (word_of_bytes be (n2w 0 : word32)
                     [get_byte w v be; get_byte (w + n2w 1)%w v be;
                      get_byte (w + n2w 2)%w v be; get_byte (w + n2w 3)%w v be])
        else NONE
    end
  else NONE.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "mem_store_32_def" *)
Definition mem_store_32 (m : word a -> word_loc a) (dm : word a -> Prop) (be : bool)
    (w : word a) (hw : word32) : option (word a -> word_loc a) :=
  if aligned 2 w then
    match m (byte_align w) with
    | Word v =>
        if classical_dec (byte_align w IN dm) then
          let v0 := set_byte w (get_byte (n2w 0 : word32) hw be) v be in
          let v1 := set_byte (w + n2w 1)%w (get_byte (n2w 1) hw be) v0 be in
          let v2 := set_byte (w + n2w 2)%w (get_byte (n2w 2) hw be) v1 be in
          let v3 := set_byte (w + n2w 3)%w (get_byte (n2w 3) hw be) v2 be in
          SOME ((byte_align w =+ Word v3) m)
        else NONE
    | _ => NONE
    end
  else NONE.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "mem_store_32_alt" *)
Theorem mem_store_32_alt : forall m dm be (w : word a) (hw : word32),
  mem_store_32 m dm be w hw =
  if aligned 2 w then
    match m (byte_align w) with
    | Word v =>
        if classical_dec (byte_align w IN dm) then
          if be then
            let v0 := set_byte w (w2w (hw >>> 24)%w) v be in
            let v1 := set_byte (w + n2w 1)%w (w2w (hw >>> 16)%w) v0 be in
            let v2 := set_byte (w + n2w 2)%w (w2w (hw >>> 8)%w) v1 be in
            let v3 := set_byte (w + n2w 3)%w (w2w hw) v2 be in
            SOME ((byte_align w =+ Word v3) m)
          else
            let v0 := set_byte w (w2w hw) v be in
            let v1 := set_byte (w + n2w 1)%w (w2w (hw >>> 8)%w) v0 be in
            let v2 := set_byte (w + n2w 2)%w (w2w (hw >>> 16)%w) v1 be in
            let v3 := set_byte (w + n2w 3)%w (w2w (hw >>> 24)%w) v2 be in
            SOME ((byte_align w =+ Word v3) m)
        else NONE
    | _ => NONE
    end
  else NONE.
Proof.
  intros m dm be w hw; unfold mem_store_32.
  destruct (aligned 2 w); [|reflexivity].
  destruct (m (byte_align w)) as [v|l n]; [|reflexivity].
  destruct (classical_dec _); [|reflexivity].
  assert (E0 : forall be', get_byte (n2w 0 : word32) hw be' =
                          w2w (hw >>> (if be' then 24 else 0))%w)
    by (intros []; reflexivity).
  assert (E1 : forall be', get_byte (n2w 1 : word32) hw be' =
                          w2w (hw >>> (if be' then 16 else 8))%w)
    by (intros []; reflexivity).
  assert (E2 : forall be', get_byte (n2w 2 : word32) hw be' =
                          w2w (hw >>> (if be' then 8 else 16))%w)
    by (intros []; reflexivity).
  assert (E3 : forall be', get_byte (n2w 3 : word32) hw be' =
                          w2w (hw >>> (if be' then 0 else 24))%w)
    by (intros []; reflexivity).
  assert (Z : (hw >>> 0)%w = hw).
  { apply word_eq_w2n. unfold word_lsr, word_bits, BITS, MOD_2EXP, DIV_2EXP.
    rewrite w2n_n2w. pose proof (w2n_lt hw) as Hlt. unfold dimword in *.
    rewrite N.pow_0_r, N.div_1_r.
    assert (Em : forall x, MIN x x = x) by (intros x; unfold MIN; destruct (x <? x); reflexivity).
    rewrite Em.
    replace (N.succ (dimindex 32 - 1) - 0) with (dimindex 32) by (unfold dimindex; lia).
    rewrite (N.mod_small (w2n hw)) by exact Hlt; apply N.mod_small, Hlt. }
  rewrite E0, E1, E2, E3.
  destruct be; cbn zeta; rewrite Z; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "mem_load_byte_aux_def" *)
Definition mem_load_byte_aux (m : word a -> word_loc a) (dm : word a -> Prop) (be : bool)
    (w : word a) : option word8 :=
  match m (byte_align w) with
  | Loc _ _ => NONE
  | Word v => if classical_dec (byte_align w IN dm) then SOME (get_byte w v be) else NONE
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "mem_store_byte_aux_def" *)
Definition mem_store_byte_aux (m : word a -> word_loc a) (dm : word a -> Prop) (be : bool)
    (w : word a) (b : word8) : option (word a -> word_loc a) :=
  match m (byte_align w) with
  | Word v =>
      if classical_dec (byte_align w IN dm)
      then SOME ((byte_align w =+ Word (set_byte w b v be)) m)
      else NONE
  | _ => NONE
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "write_bytearray_def" *)
Fixpoint write_bytearray (a0 : word a) (bs : list word8) (m : word a -> word_loc a)
    (dm : word a -> Prop) (be : bool) : word a -> word_loc a :=
  match bs with
  | [] => m
  | b :: bs =>
      match mem_store_byte_aux (write_bytearray (a0 + n2w 1)%w bs m dm be) dm be a0 b with
      | SOME m => m
      | NONE => m
      end
  end.

End WordLoc.

(** ** Stack frames and the state *)

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "stack_frame" *)
Inductive stack_frame (a : N) : Type :=
| StackFrame : option N -> list (N * word_loc a) -> list (N * word_loc a) ->
               option (N * (N * N)) -> stack_frame a.
Arguments StackFrame {a} _ _ _ _.

(** The abstract garbage collector: it is given the roots (the encoded
    stack), the memory, its domain and the store, and returns new roots,
    memory and store. *)
(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "gc_fun_type" *)
Abbreviation gc_fun_type a :=
  (list (word_loc a) * ((word a -> word_loc a) * ((word a -> Prop) * fmap store_name (word_loc a))) ->
   option (list (word_loc a) * ((word a -> word_loc a) * fmap store_name (word_loc a))))%type.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "gc_bij_ok_def" *)
Definition gc_bij_ok (seq' : N -> N -> N) : Prop := forall n, BIJ (seq' n) UNIV UNIV.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "state" *)
Record state (a : N) (c : Type) (ffi : Type) : Type := mk_state {
  locals : num_map (word_loc a);
  locals_size : option N;
  fp_regs : fmap N word64;
  store : fmap store_name (word_loc a);
  stack : list (stack_frame a);
  stack_limit : N;
  stack_max : option N;
  state_stack_size : num_map N;
  memory : word a -> word_loc a;
  mdomain : word a -> Prop;
  sh_mdomain : word a -> Prop;
  permute : N -> N -> N;
  compile : c -> list (N * (N * prog a)) -> option (list word8 * (list (word a) * c));
  compile_oracle : N -> c * list (N * (N * prog a));
  code_buffer : buffer a 8;
  data_buffer : buffer a a;
  gc_fun : gc_fun_type a;
  handler : N;
  clock : N;
  termdep : N;
  code : num_map (N * prog a);
  be : bool;
  ffi : ffi_state ffi
}.
Arguments mk_state {a c ffi}.
Arguments locals {a c ffi}. Arguments locals_size {a c ffi}. Arguments fp_regs {a c ffi}.
Arguments store {a c ffi}. Arguments stack {a c ffi}. Arguments stack_limit {a c ffi}.
Arguments stack_max {a c ffi}. Arguments state_stack_size {a c ffi}.
Arguments memory {a c ffi}. Arguments mdomain {a c ffi}. Arguments sh_mdomain {a c ffi}.
Arguments permute {a c ffi}. Arguments compile {a c ffi}. Arguments compile_oracle {a c ffi}.
Arguments code_buffer {a c ffi}. Arguments data_buffer {a c ffi}. Arguments gc_fun {a c ffi}.
Arguments handler {a c ffi}. Arguments clock {a c ffi}. Arguments termdep {a c ffi}.
Arguments code {a c ffi}. Arguments be {a c ffi}. Arguments ffi {a c ffi}.

(** HOL [s with f := x] for each field. *)
Section Updates.
Context {a : N} {c ffi_t : Type}.
Definition set_locals x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state x s.(locals_size) s.(fp_regs) s.(store) s.(stack) s.(stack_limit) s.(stack_max) s.(state_stack_size) s.(memory) s.(mdomain) s.(sh_mdomain) s.(permute) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(handler) s.(clock) s.(termdep) s.(code) s.(be) s.(ffi).
Definition set_locals_size x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) x s.(fp_regs) s.(store) s.(stack) s.(stack_limit) s.(stack_max) s.(state_stack_size) s.(memory) s.(mdomain) s.(sh_mdomain) s.(permute) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(handler) s.(clock) s.(termdep) s.(code) s.(be) s.(ffi).
Definition set_fp_regs x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) x s.(store) s.(stack) s.(stack_limit) s.(stack_max) s.(state_stack_size) s.(memory) s.(mdomain) s.(sh_mdomain) s.(permute) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(handler) s.(clock) s.(termdep) s.(code) s.(be) s.(ffi).
Definition set_store_field x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) s.(fp_regs) x s.(stack) s.(stack_limit) s.(stack_max) s.(state_stack_size) s.(memory) s.(mdomain) s.(sh_mdomain) s.(permute) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(handler) s.(clock) s.(termdep) s.(code) s.(be) s.(ffi).
Definition set_stack x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) s.(fp_regs) s.(store) x s.(stack_limit) s.(stack_max) s.(state_stack_size) s.(memory) s.(mdomain) s.(sh_mdomain) s.(permute) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(handler) s.(clock) s.(termdep) s.(code) s.(be) s.(ffi).
Definition set_stack_limit x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) s.(fp_regs) s.(store) s.(stack) x s.(stack_max) s.(state_stack_size) s.(memory) s.(mdomain) s.(sh_mdomain) s.(permute) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(handler) s.(clock) s.(termdep) s.(code) s.(be) s.(ffi).
Definition set_stack_max x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) s.(fp_regs) s.(store) s.(stack) s.(stack_limit) x s.(state_stack_size) s.(memory) s.(mdomain) s.(sh_mdomain) s.(permute) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(handler) s.(clock) s.(termdep) s.(code) s.(be) s.(ffi).
Definition set_stack_size x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) s.(fp_regs) s.(store) s.(stack) s.(stack_limit) s.(stack_max) x s.(memory) s.(mdomain) s.(sh_mdomain) s.(permute) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(handler) s.(clock) s.(termdep) s.(code) s.(be) s.(ffi).
Definition set_memory x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) s.(fp_regs) s.(store) s.(stack) s.(stack_limit) s.(stack_max) s.(state_stack_size) x s.(mdomain) s.(sh_mdomain) s.(permute) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(handler) s.(clock) s.(termdep) s.(code) s.(be) s.(ffi).
Definition set_mdomain x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) s.(fp_regs) s.(store) s.(stack) s.(stack_limit) s.(stack_max) s.(state_stack_size) s.(memory) x s.(sh_mdomain) s.(permute) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(handler) s.(clock) s.(termdep) s.(code) s.(be) s.(ffi).
Definition set_sh_mdomain x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) s.(fp_regs) s.(store) s.(stack) s.(stack_limit) s.(stack_max) s.(state_stack_size) s.(memory) s.(mdomain) x s.(permute) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(handler) s.(clock) s.(termdep) s.(code) s.(be) s.(ffi).
Definition set_permute x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) s.(fp_regs) s.(store) s.(stack) s.(stack_limit) s.(stack_max) s.(state_stack_size) s.(memory) s.(mdomain) s.(sh_mdomain) x s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(handler) s.(clock) s.(termdep) s.(code) s.(be) s.(ffi).
Definition set_compile x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) s.(fp_regs) s.(store) s.(stack) s.(stack_limit) s.(stack_max) s.(state_stack_size) s.(memory) s.(mdomain) s.(sh_mdomain) s.(permute) x s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(handler) s.(clock) s.(termdep) s.(code) s.(be) s.(ffi).
Definition set_compile_oracle x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) s.(fp_regs) s.(store) s.(stack) s.(stack_limit) s.(stack_max) s.(state_stack_size) s.(memory) s.(mdomain) s.(sh_mdomain) s.(permute) s.(compile) x s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(handler) s.(clock) s.(termdep) s.(code) s.(be) s.(ffi).
Definition set_code_buffer x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) s.(fp_regs) s.(store) s.(stack) s.(stack_limit) s.(stack_max) s.(state_stack_size) s.(memory) s.(mdomain) s.(sh_mdomain) s.(permute) s.(compile) s.(compile_oracle) x s.(data_buffer) s.(gc_fun) s.(handler) s.(clock) s.(termdep) s.(code) s.(be) s.(ffi).
Definition set_data_buffer x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) s.(fp_regs) s.(store) s.(stack) s.(stack_limit) s.(stack_max) s.(state_stack_size) s.(memory) s.(mdomain) s.(sh_mdomain) s.(permute) s.(compile) s.(compile_oracle) s.(code_buffer) x s.(gc_fun) s.(handler) s.(clock) s.(termdep) s.(code) s.(be) s.(ffi).
Definition set_gc_fun x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) s.(fp_regs) s.(store) s.(stack) s.(stack_limit) s.(stack_max) s.(state_stack_size) s.(memory) s.(mdomain) s.(sh_mdomain) s.(permute) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) x s.(handler) s.(clock) s.(termdep) s.(code) s.(be) s.(ffi).
Definition set_handler x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) s.(fp_regs) s.(store) s.(stack) s.(stack_limit) s.(stack_max) s.(state_stack_size) s.(memory) s.(mdomain) s.(sh_mdomain) s.(permute) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) x s.(clock) s.(termdep) s.(code) s.(be) s.(ffi).
Definition set_clock x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) s.(fp_regs) s.(store) s.(stack) s.(stack_limit) s.(stack_max) s.(state_stack_size) s.(memory) s.(mdomain) s.(sh_mdomain) s.(permute) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(handler) x s.(termdep) s.(code) s.(be) s.(ffi).
Definition set_termdep x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) s.(fp_regs) s.(store) s.(stack) s.(stack_limit) s.(stack_max) s.(state_stack_size) s.(memory) s.(mdomain) s.(sh_mdomain) s.(permute) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(handler) s.(clock) x s.(code) s.(be) s.(ffi).
Definition set_code x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) s.(fp_regs) s.(store) s.(stack) s.(stack_limit) s.(stack_max) s.(state_stack_size) s.(memory) s.(mdomain) s.(sh_mdomain) s.(permute) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(handler) s.(clock) s.(termdep) x s.(be) s.(ffi).
Definition set_be x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) s.(fp_regs) s.(store) s.(stack) s.(stack_limit) s.(stack_max) s.(state_stack_size) s.(memory) s.(mdomain) s.(sh_mdomain) s.(permute) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(handler) s.(clock) s.(termdep) s.(code) x s.(ffi).
Definition set_ffi x (s : state a c ffi_t) : state a c ffi_t :=
  mk_state s.(locals) s.(locals_size) s.(fp_regs) s.(store) s.(stack) s.(stack_limit) s.(stack_max) s.(state_stack_size) s.(memory) s.(mdomain) s.(sh_mdomain) s.(permute) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(handler) s.(clock) s.(termdep) s.(code) s.(be) x.
End Updates.

Section Frames.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "stack_size_frame_def" *)
Definition stack_size_frame (f : stack_frame a) : option N :=
  match f with
  | StackFrame n _ _ NONE => n
  | StackFrame n _ _ (SOME _) => OPTION_MAP (N.add 3) n
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "stack_size_def" *)
Definition stack_size : list (stack_frame a) -> option N :=
  FOLDR (OPTION_MAP2 N.add ∘ stack_size_frame) (SOME 1).

End Frames.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "state_component_equality" *)
Theorem state_component_equality : forall {a c ffi_t} (s1 s2 : state a c ffi_t),
  s1 = s2 <->
  locals s1 = locals s2 /\ locals_size s1 = locals_size s2 /\ fp_regs s1 = fp_regs s2 /\
  store s1 = store s2 /\ stack s1 = stack s2 /\ stack_limit s1 = stack_limit s2 /\
  stack_max s1 = stack_max s2 /\ state_stack_size s1 = state_stack_size s2 /\
  memory s1 = memory s2 /\ mdomain s1 = mdomain s2 /\ sh_mdomain s1 = sh_mdomain s2 /\
  permute s1 = permute s2 /\ compile s1 = compile s2 /\ compile_oracle s1 = compile_oracle s2 /\
  code_buffer s1 = code_buffer s2 /\ data_buffer s1 = data_buffer s2 /\
  gc_fun s1 = gc_fun s2 /\ handler s1 = handler s2 /\ clock s1 = clock s2 /\
  termdep s1 = termdep s2 /\ code s1 = code s2 /\ be s1 = be s2 /\ ffi s1 = ffi s2.
Proof.
  intros a c ffi_t [] []; cbn; split.
  - intros H; injection H; intros; subst; repeat split.
  - intros H; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "result" *)
Inductive result (w : N) : Type :=
| Result : word_loc w -> list (word_loc w) -> result w
| Exception : word_loc w -> word_loc w -> result w
| Break : N -> result w
| Continue : N -> result w
| TimeOut : result w
| NotEnoughSpace : result w
| FinalFFI : final_event -> result w
| Error : result w.
Arguments Result {w} _ _. Arguments Exception {w} _ _. Arguments Break {w} _.
Arguments Continue {w} _. Arguments TimeOut {w}. Arguments NotEnoughSpace {w}.
Arguments FinalFFI {w} _. Arguments Error {w}.

#[global] Instance result_eq_dec {w} : EqDecision (result w).
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.
#[global] Instance result_inhabited {w} : Inhabited (result w) := Error.

Section Basics.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "isResult_def" *)
Definition isResult (r : result a) : bool := match r with Result _ _ => true | _ => false end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "isException_def" *)
Definition isException (r : result a) : bool := match r with Exception _ _ => true | _ => false end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "dec_clock_def" *)
Definition dec_clock (s : state) : state := set_clock (clock s - 1) s.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "fix_clock_def" *)
Definition fix_clock {R} (old_s : state) (p : R * state) : R * state :=
  let '(res, new_s) := p in
  (res, set_termdep (termdep old_s)
          (set_clock (if clock old_s <? clock new_s then clock old_s else clock new_s) new_s)).

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "is_word_def" *)
Definition is_word (x : word_loc a) : bool := match x with Word w => true | _ => false end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "get_word_def" *)
Definition get_word (x : word_loc a) : word a := match x with Word w => w | _ => ARB end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "mem_store_def" *)
Definition mem_store (addr : word a) (w : word_loc a) (s : state) : option state :=
  if classical_dec (addr IN mdomain s) then SOME (set_memory ((addr =+ w) (memory s)) s)
  else NONE.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "mem_load_def" *)
Definition mem_load (addr : word a) (s : state) : option (word_loc a) :=
  if classical_dec (addr IN mdomain s) then SOME (memory s addr) else NONE.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "the_words_def" *)
Fixpoint the_words (ws : list (option (word_loc a))) : option (list (word a)) :=
  match ws with
  | [] => SOME []
  | w :: ws =>
      match w, the_words ws with
      | SOME (Word x), SOME xs => SOME (x :: xs)
      | _, _ => NONE
      end
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "get_var_def" *)
Definition get_var (v : N) (s : state) : option (word_loc a) := lookup v (locals s).

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "get_vars_def" *)
Fixpoint get_vars (vs : list N) (s : state) : option (list (word_loc a)) :=
  match vs with
  | [] => SOME []
  | v :: vs =>
      match get_var v s with
      | NONE => NONE
      | SOME x => match get_vars vs s with NONE => NONE | SOME xs => SOME (x :: xs) end
      end
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "set_var_def" *)
Definition set_var (v : N) (x : word_loc a) (s : state) : state :=
  set_locals (insert v x (locals s)) s.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "unset_var_def" *)
Definition unset_var (v : N) (s : state) : state := set_locals (delete v (locals s)) s.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "set_vars_def" *)
Definition set_vars (vs : list N) (xs : list (word_loc a)) (s : state) : state :=
  set_locals (alist_insert vs xs (locals s)) s.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "get_store_def" *)
Definition get_store (v : store_name) (s : state) : option (word_loc a) := FLOOKUP (store s) v.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "set_store_def" *)
Definition set_store (v : store_name) (x : word_loc a) (s : state) : state :=
  set_store_field (store s |+ (v, x)) s.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "word_exp_def" *)
Fixpoint word_exp (s : state) (e : exp a) {struct e} : option (word_loc a) :=
  match e with
  | Const w => SOME (Word w)
  | Var v => get_var v s
  | Lookup name => get_store name s
  | Load addr =>
      match word_exp s addr with
      | SOME (Word w) => mem_load w s
      | _ => NONE
      end
  | Op op wexps =>
      match the_words (MAP (word_exp s) wexps) with
      | SOME ws => OPTION_MAP Word (word_op op ws)
      | _ => NONE
      end
  | Shift sh wexp wexp1 =>
      match word_exp s wexp, word_exp s wexp1 with
      | SOME (Word w), SOME (Word w1) => OPTION_MAP Word (word_sh sh w (w2n w1))
      | _, _ => NONE
      end
  end.

(** Flushes the locals and (optionally) the store. *)
(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "flush_state_def" *)
Definition flush_state (b : bool) (s : state) : state :=
  if b then set_locals_size (SOME 0) (set_store_field FEMPTY (set_stack [] (set_locals LN s)))
  else set_locals_size (SOME 0) (set_locals LN s).

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "sh_mem_store_def" *)
Definition sh_mem_store (a0 w : word a) (s : state) : option (result a) * state :=
  if classical_dec (a0 IN sh_mdomain s) then
    match call_FFI (ffi s) (SharedMem MappedWrite) [n2w 0 : word8]
            (word_to_bytes w false ++ word_to_bytes a0 false) with
    | FFI_final outcome => (SOME (FinalFFI outcome), flush_state true s)
    | FFI_return new_ffi new_bytes => (NONE, set_ffi new_ffi s)
    end
  else (SOME Error, s).

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "sh_mem_load_def" *)
Definition sh_mem_load (a0 : word a) (s : state) : option (ffi_result ffi_t) :=
  if classical_dec (a0 IN sh_mdomain s) then
    SOME (call_FFI (ffi s) (SharedMem MappedRead) [n2w 0 : word8] (word_to_bytes a0 false))
  else NONE.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "sh_mem_store_byte_def" *)
Definition sh_mem_store_byte (a0 w : word a) (s : state) : option (result a) * state :=
  if classical_dec (byte_align a0 IN sh_mdomain s) then
    match call_FFI (ffi s) (SharedMem MappedWrite) [n2w 1 : word8]
            ([get_byte (n2w 0) w false] ++ word_to_bytes a0 false) with
    | FFI_final outcome => (SOME (FinalFFI outcome), flush_state true s)
    | FFI_return new_ffi new_bytes => (NONE, set_ffi new_ffi s)
    end
  else (SOME Error, s).

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "sh_mem_store16_def" *)
Definition sh_mem_store16 (a0 w : word a) (s : state) : option (result a) * state :=
  if classical_dec (byte_align a0 IN sh_mdomain s) then
    match call_FFI (ffi s) (SharedMem MappedWrite) [n2w 2 : word8]
            (TAKE 2 (word_to_bytes w false) ++ word_to_bytes a0 false) with
    | FFI_final outcome => (SOME (FinalFFI outcome), flush_state true s)
    | FFI_return new_ffi new_bytes => (NONE, set_ffi new_ffi s)
    end
  else (SOME Error, s).

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "sh_mem_store32_def" *)
Definition sh_mem_store32 (a0 w : word a) (s : state) : option (result a) * state :=
  if classical_dec (byte_align a0 IN sh_mdomain s) then
    match call_FFI (ffi s) (SharedMem MappedWrite) [n2w 4 : word8]
            (TAKE 4 (word_to_bytes w false) ++ word_to_bytes a0 false) with
    | FFI_final outcome => (SOME (FinalFFI outcome), flush_state true s)
    | FFI_return new_ffi new_bytes => (NONE, set_ffi new_ffi s)
    end
  else (SOME Error, s).

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "sh_mem_load_byte_def" *)
Definition sh_mem_load_byte (a0 : word a) (s : state) : option (ffi_result ffi_t) :=
  if classical_dec (byte_align a0 IN sh_mdomain s) then
    SOME (call_FFI (ffi s) (SharedMem MappedRead) [n2w 1 : word8] (word_to_bytes a0 false))
  else NONE.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "sh_mem_load16_def" *)
Definition sh_mem_load16 (a0 : word a) (s : state) : option (ffi_result ffi_t) :=
  if classical_dec (byte_align a0 IN sh_mdomain s) then
    SOME (call_FFI (ffi s) (SharedMem MappedRead) [n2w 2 : word8] (word_to_bytes a0 false))
  else NONE.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "sh_mem_load32_def" *)
Definition sh_mem_load32 (a0 : word a) (s : state) : option (ffi_result ffi_t) :=
  if classical_dec (byte_align a0 IN sh_mdomain s) then
    SOME (call_FFI (ffi s) (SharedMem MappedRead) [n2w 4 : word8] (word_to_bytes a0 false))
  else NONE.

(** Set a variable from the output of a shared-memory load. *)
(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "sh_mem_set_var_def" *)
Definition sh_mem_set_var (r : option (ffi_result ffi_t)) (v : N) (s : state)
    : option (result a) * state :=
  match r with
  | SOME (FFI_final outcome) => (SOME (FinalFFI outcome), flush_state true s)
  | SOME (FFI_return new_ffi new_bytes) =>
      (NONE, set_var v (Word (word_of_bytes false (n2w 0) new_bytes)) (set_ffi new_ffi s))
  | _ => (SOME Error, s)
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "share_inst_def" *)
Definition share_inst (op : memop) (v : N) (ad : word a) (s : state) : option (result a) * state :=
  match op with
  | asm.Load => sh_mem_set_var (sh_mem_load ad s) v s
  | Load8 => sh_mem_set_var (sh_mem_load_byte ad s) v s
  | Load16 => sh_mem_set_var (sh_mem_load16 ad s) v s
  | Load32 => sh_mem_set_var (sh_mem_load32 ad s) v s
  | asm.Store =>
      match get_var v s with SOME (Word v) => sh_mem_store ad v s | _ => (SOME Error, s) end
  | Store8 =>
      match get_var v s with SOME (Word v) => sh_mem_store_byte ad v s | _ => (SOME Error, s) end
  | Store16 =>
      match get_var v s with SOME (Word v) => sh_mem_store16 ad v s | _ => (SOME Error, s) end
  | Store32 =>
      match get_var v s with SOME (Word v) => sh_mem_store32 ad v s | _ => (SOME Error, s) end
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "call_env_def" *)
Definition call_env (args : list (word_loc a)) (size : option N) (s : state) : state :=
  set_stack_max (OPTION_MAP2 MAX (stack_max s) (OPTION_MAP2 N.add (stack_size (stack s)) size))
    (set_locals_size size (set_locals (fromList2 args) s)).

End Basics.

(** ** Environments on the stack *)

(** If [mover] is a permutation of the indices of [xs], rearrange [xs]
    with it; otherwise leave [xs] unchanged. *)
(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "list_rearrange_def" *)
Definition list_rearrange {A} `{Inhabited A} (mover : N -> N) (xs : list A) : list A :=
  if classical_dec (BIJ mover (count (LENGTH xs)) (count (LENGTH xs)))
  then GENLIST (fun i => EL (mover i) xs) (LENGTH xs)
  else xs.

Section Env.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(** Compare on keys; on equal keys compare the values, [Word]s before
    [Loc]s ([x <= y] on words is HOL's signed [word_le]). *)
(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "key_val_compare_def" *)
Definition key_val_compare (x y : N * word_loc a) : bool :=
  let '(a1, b) := x in
  let '(a1', b') := y in
  (a1' <? a1) ||
  ((a1 =? a1') &&
   match b with
   | Word x => match b' with Word y => word_le x y | _ => true end
   | Loc a2 b2 =>
       match b' with
       | Loc a2' b2' => (a2' <? a2) || ((a2 =? a2') && (b2' <=? b2))
       | _ => false
       end
   end).

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "env_to_list_def" *)
Definition env_to_list (env : num_map (word_loc a)) (bij_seq : N -> N -> N)
    : list (N * word_loc a) * (N -> N -> N) :=
  let mover := bij_seq 0 in
  let permute := fun n => bij_seq (n + 1) in
  let l := toAList env in
  let l := sort key_val_compare l in
  let l := list_rearrange mover l in
  (l, permute).

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "push_env_def" *)
Definition push_env (envs : num_map (word_loc a) * num_map (word_loc a))
    (h : option (N * (prog a * (N * N)))) (s : state) : state :=
  match h with
  | NONE =>
      let l0 := toAList (FST envs) in
      let '(l, perm) := env_to_list (SND envs) (permute s) in
      let stk := StackFrame (locals_size s) l0 l NONE :: stack s in
      set_permute perm (set_stack_max (OPTION_MAP2 MAX (stack_max s) (stack_size stk))
                          (set_stack stk s))
  | SOME (w, (h, (l1, l2))) =>
      let l0 := toAList (FST envs) in
      let '(l, perm) := env_to_list (SND envs) (permute s) in
      let hnd := SOME (handler s, (l1, l2)) in
      let stk := StackFrame (locals_size s) l0 l hnd :: stack s in
      set_handler (LENGTH (stack s))
        (set_permute perm (set_stack_max (OPTION_MAP2 MAX (stack_max s) (stack_size stk))
                             (set_stack stk s)))
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "pop_env_def" *)
Definition pop_env (s : state) : option state :=
  match stack s with
  | StackFrame m e0 e NONE :: xs =>
      SOME (set_locals_size m (set_stack xs (set_locals (union (fromAList e) (fromAList e0)) s)))
  | StackFrame m e0 e (SOME (n, _)) :: xs =>
      SOME (set_handler n (set_locals_size m
              (set_stack xs (set_locals (union (fromAList e) (fromAList e0)) s))))
  | _ => NONE
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "push_env_clock" *)
Theorem push_env_clock : forall env b (s : state), clock (push_env env b s) = clock s.
Proof.
  intros env [[w [h [l1 l2]]]|] s; unfold push_env;
    destruct (env_to_list _ _); reflexivity.
Qed.

Lemma push_env_termdep : forall env b (s : state), termdep (push_env env b s) = termdep s.
Proof.
  intros env [[w [h [l1 l2]]]|] s; unfold push_env;
    destruct (env_to_list _ _); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "pop_env_clock" *)
Theorem pop_env_clock : forall (s s1 : state), pop_env s = SOME s1 -> clock s1 = clock s.
Proof.
  intros s s1; unfold pop_env.
  destruct (stack s) as [|[m e0 e [[n x]|]] xs]; intros H; inversion H; reflexivity.
Qed.

Lemma pop_env_termdep : forall (s s1 : state), pop_env s = SOME s1 -> termdep s1 = termdep s.
Proof.
  intros s s1; unfold pop_env.
  destruct (stack s) as [|[m e0 e [[n x]|]] xs]; intros H; inversion H; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "jump_exc_def" *)
Definition jump_exc (s : state) : option (state * (N * N)) :=
  if handler s <? LENGTH (stack s) then
    match LASTN (handler s + 1) (stack s) with
    | StackFrame m e0 e (SOME (n, (l1, l2))) :: xs =>
        SOME (set_locals_size m (set_stack xs
                (set_locals (union (fromAList e) (fromAList e0)) (set_handler n s))),
              (l1, l2))
    | _ => NONE
    end
  else NONE.

Lemma jump_exc_clock : forall (s s1 : state) l,
  jump_exc s = SOME (s1, l) -> clock s1 = clock s /\ termdep s1 = termdep s.
Proof.
  intros s s1 l; unfold jump_exc.
  destruct (handler s <? LENGTH (stack s)); [|discriminate].
  destruct (LASTN _ _) as [|[m e0 e [[n [l1 l2]]|]] xs]; intros H; inversion H; subst;
    split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "cut_names_def" *)
Definition cut_names {A} (name_set : num_set) (env : num_map A) : option (num_map A) :=
  if classical_dec (domain name_set SUBSET domain env) then SOME (inter env name_set) else NONE.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "cut_envs_def" *)
Definition cut_envs {A} (name_sets : cutsets) (env : num_map A) : option (num_map A * num_map A) :=
  match cut_names (FST name_sets) env, cut_names (SND name_sets) env with
  | SOME e1, SOME e2 => SOME (e1, e2)
  | _, _ => NONE
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "cut_env_def" *)
Definition cut_env {A} (name_sets : cutsets) (env : num_map A) : option (num_map A) :=
  match cut_envs name_sets env with
  | SOME (e1, e2) => SOME (union e2 e1)
  | _ => NONE
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "cut_state_def" *)
Definition cut_state (names : cutsets) (s : state) : option state :=
  match cut_env names (locals s) with
  | NONE => NONE
  | SOME env => SOME (set_locals env s)
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "cut_state_opt_def" *)
Definition cut_state_opt (names : option cutsets) (s : state) : option state :=
  match names with
  | NONE => SOME s
  | SOME names => cut_state names s
  end.

Lemma cut_state_clock : forall names (s s1 : state),
  cut_state names s = SOME s1 -> clock s1 = clock s /\ termdep s1 = termdep s.
Proof.
  intros names s s1; unfold cut_state; destruct (cut_env _ _); intros H; inversion H;
    split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "find_code_def" *)
Definition find_code (p : option N) (args : list (word_loc a)) (code : num_map (N * prog a))
    (ssize : num_map N) : option (list (word_loc a) * (prog a * option N)) :=
  match p with
  | SOME p =>
      match lookup p code with
      | NONE => NONE
      | SOME (arity, exp) =>
          if LENGTH args =? arity then SOME (args, (exp, lookup p ssize)) else NONE
      end
  | NONE =>
      if bool_decide (args = []) then NONE else
        match LAST args with
        | Loc loc n =>
            if n =? 0 then
              match lookup loc code with
              | NONE => NONE
              | SOME (arity, exp) =>
                  if LENGTH args =? arity + 1
                  then SOME (FRONT args, (exp, lookup loc ssize))
                  else NONE
              end
            else NONE
        | _ => NONE
        end
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "enc_stack_def" *)
Fixpoint enc_stack (st : list (stack_frame a)) : list (word_loc a) :=
  match st with
  | [] => []
  | StackFrame n _ l handler :: st => MAP SND l ++ enc_stack st
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "dec_stack_def" *)
Fixpoint dec_stack (xs : list (word_loc a)) (st : list (stack_frame a))
    : option (list (stack_frame a)) :=
  match st with
  | [] => match xs with [] => SOME [] | _ => NONE end
  | StackFrame n l0 l handler :: st =>
      if LENGTH xs <? LENGTH l then NONE else
        match dec_stack (DROP (LENGTH l) xs) st with
        | NONE => NONE
        | SOME s => SOME (StackFrame n l0 (ZIP (MAP FST l, TAKE (LENGTH l) xs)) handler :: s)
        end
  end.

(** [gc] runs the garbage collector algorithm. *)
(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "gc_def" *)
Definition gc (s : state) : option state :=
  let wl_list := enc_stack (stack s) in
  match gc_fun s (wl_list, (memory s, (mdomain s, store s))) with
  | NONE => NONE
  | SOME (wl, (m, st)) =>
      match dec_stack wl (stack s) with
      | NONE => NONE
      | SOME stack => SOME (set_memory m (set_store_field st (set_stack stack s)))
      end
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "has_space_def" *)
Definition has_space (wl : word_loc a) (s : state) : option bool :=
  match wl, get_store NextFree s, get_store TriggerGC s with
  | Word w, SOME (Word n), SOME (Word l) => SOME (w2n w <=? w2n (l - n)%w)
  | _, _, _ => NONE
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "alloc_def" *)
Definition alloc (w : word a) (names : cutsets) (s : state) : option (result a) * state :=
  match cut_envs names (locals s) with
  | NONE => (SOME Error, flush_state true s)
  | SOME envs =>
      match gc (push_env envs (NONE : option (N * (prog a * (N * N))))
                  (set_store AllocSize (Word w) s)) with
      | NONE => (SOME Error, flush_state true s)
      | SOME s =>
          match pop_env s with
          | NONE => (SOME Error, flush_state true s)
          | SOME s =>
              match get_store AllocSize s with
              | NONE => (SOME Error, s)
              | SOME w =>
                  match has_space w s with
                  | NONE => (SOME Error, s)
                  | SOME true => (NONE, s)
                  | SOME false => (SOME NotEnoughSpace, flush_state true s)
                  end
              end
          end
      end
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "assign_def" *)
Definition assign (reg : N) (exp : exp a) (s : state) : option state :=
  match word_exp s exp with
  | NONE => NONE
  | SOME w => SOME (set_var reg w s)
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "get_fp_var_def" *)
Definition get_fp_var (v : N) (s : state) : option word64 := FLOOKUP (fp_regs s) v.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "set_fp_var_def" *)
Definition set_fp_var (v : N) (x : word64) (s : state) : state :=
  set_fp_regs (fp_regs s |+ (v, x)) s.

(** The floating-point operations ([fp64_*]) are the stand-ins of
    [machine_ieee] (see there); HOL's [fpSem$fpfma f1 f2 f3] is by definition
    [fp64_mul_add roundTiesToEven f2 f3 f1], written out because [fpfma] is
    not yet in [fpSem.v].  HOL's final catch-all [| _ => NONE] is redundant
    and omitted. *)
(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "inst_def" *)
Definition inst (i : inst a) (s : state) : option state :=
  match i with
  | asm.Skip => SOME s
  | asm.Const reg w => assign reg (Const w) s
  | Arith (Binop bop r1 r2 ri) =>
      assign r1 (Op bop [Var r2; match ri with Reg r3 => Var r3 | Imm w => Const w end]) s
  | Arith (asm.Shift sh r1 r2 ri) =>
      assign r1 (Shift sh (Var r2) (match ri with Reg r3 => Var r3 | Imm w => Const w end)) s
  | Arith (Div r1 r2 r3) =>
      let vs := get_vars [r3; r2] s in
      match vs with
      | SOME [Word q; Word w2] =>
          if negb (bool_decide (q = n2w 0)) then SOME (set_var r1 (Word (word_quot w2 q)) s)
          else NONE
      | _ => NONE
      end
  | Arith (AddCarry r1 r2 r3 r4) =>
      let vs := get_vars [r2; r3; r4] s in
      match vs with
      | SOME [Word l; Word r; Word c0] =>
          let '(res, co) := word_add_carry l r c0 in
          SOME (set_var r4 (Word co) (set_var r1 (Word res) s))
      | _ => NONE
      end
  | Arith (AddOverflow r1 r2 r3 r4) =>
      let vs := get_vars [r2; r3] s in
      match vs with
      | SOME [Word w2; Word w3] =>
          SOME (set_var r4 (Word (if negb (bool_decide (w2i (w2 + w3)%w = (w2i w2 + w2i w3)%Z))
                                  then n2w 1 else n2w 0))
                  (set_var r1 (Word (w2 + w3)%w) s))
      | _ => NONE
      end
  | Arith (SubOverflow r1 r2 r3 r4) =>
      let vs := get_vars [r2; r3] s in
      match vs with
      | SOME [Word w2; Word w3] =>
          SOME (set_var r4 (Word (if negb (bool_decide (w2i (w2 - w3)%w = (w2i w2 - w2i w3)%Z))
                                  then n2w 1 else n2w 0))
                  (set_var r1 (Word (w2 - w3)%w) s))
      | _ => NONE
      end
  | Arith (LongMul r1 r2 r3 r4) =>
      let vs := get_vars [r3; r4] s in
      match vs with
      | SOME [Word w3; Word w4] =>
          let r := w2n w3 * w2n w4 in
          SOME (set_var r2 (Word (n2w r)) (set_var r1 (Word (n2w (r DIV dimword a))) s))
      | _ => NONE
      end
  | Arith (LongDiv r1 r2 r3 r4 r5) =>
      let vs := get_vars [r3; r4; r5] s in
      match vs with
      | SOME [Word w3; Word w4; Word w5] =>
          let n := w2n w3 * dimword a + w2n w4 in
          let d := w2n w5 in
          let q := n DIV d in
          if negb (d =? 0) && (q <? dimword a) then
            SOME (set_var r1 (Word (n2w q)) (set_var r2 (Word (n2w (n MOD d))) s))
          else NONE
      | _ => NONE
      end
  | Mem asm.Load r (Addr a0 w) =>
      match word_exp s (Op asm.Add [Var a0; Const w]) with
      | SOME (Word w) =>
          match mem_load w s with
          | NONE => NONE
          | SOME w => SOME (set_var r w s)
          end
      | _ => NONE
      end
  | Mem Load8 r (Addr a0 w) =>
      match word_exp s (Op asm.Add [Var a0; Const w]) with
      | SOME (Word w) =>
          match mem_load_byte_aux (memory s) (mdomain s) (be s) w with
          | NONE => NONE
          | SOME w => SOME (set_var r (Word (w2w w)) s)
          end
      | _ => NONE
      end
  | Mem Load16 _ _ => NONE
  | Mem Load32 r (Addr a0 w) =>
      match word_exp s (Op asm.Add [Var a0; Const w]) with
      | SOME (Word w) =>
          match mem_load_32 (memory s) (mdomain s) (be s) w with
          | NONE => NONE
          | SOME w => SOME (set_var r (Word (w2w w)) s)
          end
      | _ => NONE
      end
  | Mem asm.Store r (Addr a0 w) =>
      match word_exp s (Op asm.Add [Var a0; Const w]), get_var r s with
      | SOME (Word a0), SOME w =>
          match mem_store a0 w s with
          | SOME s1 => SOME s1
          | NONE => NONE
          end
      | _, _ => NONE
      end
  | Mem Store8 r (Addr a0 w) =>
      match word_exp s (Op asm.Add [Var a0; Const w]), get_var r s with
      | SOME (Word a0), SOME (Word w) =>
          match mem_store_byte_aux (memory s) (mdomain s) (be s) a0 (w2w w) with
          | SOME new_m => SOME (set_memory new_m s)
          | NONE => NONE
          end
      | _, _ => NONE
      end
  | Mem Store16 _ _ => NONE
  | Mem Store32 r (Addr a0 w) =>
      match word_exp s (Op asm.Add [Var a0; Const w]), get_var r s with
      | SOME (Word a0), SOME (Word w) =>
          match mem_store_32 (memory s) (mdomain s) (be s) a0 (w2w w) with
          | SOME new_m => SOME (set_memory new_m s)
          | NONE => NONE
          end
      | _, _ => NONE
      end
  | FP (FPLess r d1 d2) =>
      match get_fp_var d1 s, get_fp_var d2 s with
      | SOME f1, SOME f2 =>
          SOME (set_var r (Word (if fp64_lessThan f1 f2 then n2w 1 else n2w 0)) s)
      | _, _ => NONE
      end
  | FP (FPLessEqual r d1 d2) =>
      match get_fp_var d1 s, get_fp_var d2 s with
      | SOME f1, SOME f2 =>
          SOME (set_var r (Word (if fp64_lessEqual f1 f2 then n2w 1 else n2w 0)) s)
      | _, _ => NONE
      end
  | FP (FPEqual r d1 d2) =>
      match get_fp_var d1 s, get_fp_var d2 s with
      | SOME f1, SOME f2 =>
          SOME (set_var r (Word (if fp64_equal f1 f2 then n2w 1 else n2w 0)) s)
      | _, _ => NONE
      end
  | FP (FPMov d1 d2) =>
      match get_fp_var d2 s with
      | SOME f => SOME (set_fp_var d1 f s)
      | _ => NONE
      end
  | FP (FPAbs d1 d2) =>
      match get_fp_var d2 s with
      | SOME f => SOME (set_fp_var d1 (fp64_abs f) s)
      | _ => NONE
      end
  | FP (FPNeg d1 d2) =>
      match get_fp_var d2 s with
      | SOME f => SOME (set_fp_var d1 (fp64_negate f) s)
      | _ => NONE
      end
  | FP (FPSqrt d1 d2) =>
      match get_fp_var d2 s with
      | SOME f => SOME (set_fp_var d1 (fp64_sqrt roundTiesToEven f) s)
      | _ => NONE
      end
  | FP (FPAdd d1 d2 d3) =>
      match get_fp_var d2 s, get_fp_var d3 s with
      | SOME f1, SOME f2 => SOME (set_fp_var d1 (fp64_add roundTiesToEven f1 f2) s)
      | _, _ => NONE
      end
  | FP (FPSub d1 d2 d3) =>
      match get_fp_var d2 s, get_fp_var d3 s with
      | SOME f1, SOME f2 => SOME (set_fp_var d1 (fp64_sub roundTiesToEven f1 f2) s)
      | _, _ => NONE
      end
  | FP (FPMul d1 d2 d3) =>
      match get_fp_var d2 s, get_fp_var d3 s with
      | SOME f1, SOME f2 => SOME (set_fp_var d1 (fp64_mul roundTiesToEven f1 f2) s)
      | _, _ => NONE
      end
  | FP (FPDiv d1 d2 d3) =>
      match get_fp_var d2 s, get_fp_var d3 s with
      | SOME f1, SOME f2 => SOME (set_fp_var d1 (fp64_div roundTiesToEven f1 f2) s)
      | _, _ => NONE
      end
  | FP (FPFma d1 d2 d3) =>
      match get_fp_var d1 s, get_fp_var d2 s, get_fp_var d3 s with
      | SOME f1, SOME f2, SOME f3 =>
          (* HOL: [fpSem$fpfma f1 f2 f3] *)
          SOME (set_fp_var d1 (fp64_mul_add roundTiesToEven f2 f3 f1) s)
      | _, _, _ => NONE
      end
  | FP (FPMovToReg r1 r2 d) =>
      match get_fp_var d s with
      | SOME v =>
          if dimindex a =? 64 then SOME (set_var r1 (Word (w2w v)) s)
          else SOME (set_var r2 (Word ((63 >< 32) v)%w) (set_var r1 (Word ((31 >< 0) v)%w) s))
      | _ => NONE
      end
  | FP (FPMovFromReg d r1 r2) =>
      if dimindex a =? 64 then
        match get_var r1 s with
        | SOME (Word w1) => SOME (set_fp_var d (w2w w1) s)
        | _ => NONE
        end
      else
        match get_var r1 s, get_var r2 s with
        | SOME (Word w1), SOME (Word w2) => SOME (set_fp_var d (word_concat w2 w1) s)
        | _, _ => NONE
        end
  | FP (FPToInt d1 d2) =>
      match get_fp_var d2 s with
      | NONE => NONE
      | SOME f =>
          match fp64_to_int roundTiesToEven f with
          | NONE => NONE
          | SOME i =>
              let w := (i2w i : word32) in
              if bool_decide (w2i w = i) then
                (if dimindex a =? 64 then SOME (set_fp_var d1 (w2w w) s)
                 else
                   match get_fp_var (d1 DIV 2) s with
                   | NONE => NONE
                   | SOME f =>
                       let '(h, l) := if ODD d1 then (63, 32) else (31, 0) in
                       SOME (set_fp_var (d1 DIV 2) (bit_field_insert h l w f) s)
                   end)
              else NONE
          end
      end
  | FP (FPFromInt d1 d2) =>
      if dimindex a =? 64 then
        match get_fp_var d2 s with
        | SOME f =>
            let i := w2i ((31 >< 0) f : word32)%w in
            SOME (set_fp_var d1 (int_to_fp64 roundTiesToEven i) s)
        | NONE => NONE
        end
      else
        match get_fp_var (d2 DIV 2) s with
        | SOME v =>
            let i := w2i (if ODD d2 then (63 >< 32) v else (31 >< 0) v : word a)%w in
            SOME (set_fp_var d1 (int_to_fp64 roundTiesToEven i) s)
        | NONE => NONE
        end
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "get_var_imm_def" *)
Definition get_var_imm (ri : reg_imm a) (s : state) : option (word_loc a) :=
  match ri with
  | Reg n => get_var n s
  | Imm w => SOME (Word w)
  end.

End Env.

Section Misc.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "add_ret_loc_def" *)
Definition add_ret_loc (ret : option (list N * (cutsets * (prog a * (N * N)))))
    (xs : list (word_loc a)) : list (word_loc a) :=
  match ret with
  | NONE => xs
  | SOME (n, (names, (ret_handler, (l1, l2)))) => Loc l1 l2 :: xs
  end.

(** Avoid case split. *)
(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "bad_dest_args_def" *)
Definition bad_dest_args (dest : option N) (args : list N) : bool :=
  bool_decide (dest = NONE) && bool_decide (args = []).

(** A number large enough for HOL's purposes (never computed). *)
(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "MustTerminate_limit_def" *)
Definition MustTerminate_limit (a : N) : N :=
  2 * dimword a +
  dimword a * dimword a +
  dimword a ** dimword a +
  dimword a ** (dimword a ** dimword a).

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "const_addresses_def" *)
Fixpoint const_addresses {B} (a0 : word a) (xs : list B) (d : word a -> Prop) : bool :=
  match xs with
  | [] => true
  | x :: xs => ⌜a0 IN d⌝ && const_addresses (a0 + bytes_in_word)%w xs d
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "const_writes_def" *)
Fixpoint const_writes (a0 : word a) (off : word a) (xs : list (bool * word a))
    (m : word a -> word_loc a) : word a -> word_loc a :=
  match xs with
  | [] => m
  | (b, x) :: xs =>
      const_writes (a0 + bytes_in_word)%w off xs
        ((a0 =+ Word (if b then (x + off)%w else x)) m)
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "STOP_def" *)
Definition STOP {A} (x : A) : A := x.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "bad_fun_return_def" *)
Definition bad_fun_return (r : option (result a)) : bool :=
  match r with
  | NONE => true
  | SOME (Break _) => true
  | SOME (Continue _) => true
  | _ => false
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "cont_loop_def" *)
Definition cont_loop (r : option (result a)) : bool :=
  match r with
  | NONE => true
  | SOME (Continue n) => n =? 0
  | _ => false
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "exit_loop_def" *)
Definition exit_loop (r : option (result a)) : option (result a) :=
  match r with
  | SOME (Break n) => SOME (Break (n - 1))
  | SOME (Continue n) => SOME (Continue (n - 1))
  | res => res
  end.

End Misc.

(** ** [evaluate] *)

Section Evaluate.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).
Local Abbreviation res := (option (result a) * state)%type.

(** One step of HOL's [evaluate]: [go] evaluates at the same clock and
    [termdep] (structurally smaller programs), [lower] at a smaller clock
    and [deeper] at a smaller [termdep]. *)
Definition evaluate_body (go lower deeper : prog a -> state -> res)
    (p : prog a) (s : state) : res :=
  match p with
  | Skip => (NONE, s)
  | Alloc n names =>
      match get_var n s with
      | SOME (Word w) => alloc w names s
      | _ => (SOME Error, s)
      end
  | StoreConsts t1 t2 addr offset words =>
      match get_var addr s, get_var offset s with
      | SOME (Word a0), SOME (Word off) =>
          if negb (const_addresses a0 words (mdomain s)) then (SOME Error, s)
          else
            let s := set_memory (const_writes a0 off words (memory s)) s in
            let s := set_var offset (Word off) (unset_var t1 (unset_var t2 s)) in
            (NONE, set_var addr (Word (a0 + bytes_in_word * n2w (LENGTH words))%w) s)
      | _, _ => (SOME Error, s)
      end
  | Move pri moves =>
      if ALL_DISTINCT (MAP FST moves) then
        match get_vars (MAP SND moves) s with
        | NONE => (SOME Error, s)
        | SOME vs => (NONE, set_vars (MAP FST moves) vs s)
        end
      else (SOME Error, s)
  | Inst i =>
      match inst i s with
      | SOME s1 => (NONE, s1)
      | NONE => (SOME Error, s)
      end
  | Assign v exp =>
      match word_exp s exp with
      | NONE => (SOME Error, s)
      | SOME w => (NONE, set_var v w s)
      end
  | Get v name =>
      match get_store name s with
      | NONE => (SOME Error, s)
      | SOME x => (NONE, set_var v x s)
      end
  | Set_ v exp =>
      if bool_decide (v = Handler) || bool_decide (v = BitmapBase) then (SOME Error, s)
      else
        match word_exp s exp with
        | NONE => (SOME Error, s)
        | SOME w => (NONE, set_store v w s)
        end
  | OpCurrHeap b dst src =>
      match word_exp s (Op b [Var src; Lookup CurrHeap]) with
      | NONE => (SOME Error, s)
      | SOME w => (NONE, set_var dst w s)
      end
  | Store exp v =>
      match word_exp s exp, get_var v s with
      | SOME (Word a0), SOME w =>
          match mem_store a0 w s with
          | SOME s1 => (NONE, s1)
          | NONE => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end
  | Tick =>
      if clock s =? 0 then (SOME TimeOut, flush_state true s) else (NONE, dec_clock s)
  | MustTerminate p =>
      if termdep s =? 0 then (SOME Error, s) else
        let '(res, s1) :=
          deeper p (set_termdep (termdep s - 1) (set_clock (MustTerminate_limit a) s)) in
        if bool_decide (res = SOME TimeOut) then (SOME Error, s)
        else (res, set_termdep (termdep s) (set_clock (clock s) s1))
  | Seq c1 c2 =>
      let '(res, s1) := fix_clock s (go c1 s) in
      if bool_decide (res = NONE) then go c2 s1 else (res, s1)
  | Return n ms =>
      match get_var n s, get_vars ms s with
      | SOME (Loc l1 l2), SOME ys => (SOME (Result (Loc l1 l2) ys), flush_state false s)
      | _, _ => (SOME Error, s)
      end
  | Raise n =>
      match get_var n s with
      | NONE => (SOME Error, s)
      | SOME w =>
          match jump_exc s with
          | NONE => (SOME Error, s)
          | SOME (s, (l1, l2)) => (SOME (Exception (Loc l1 l2) w), s)
          end
      end
  | wordLang.Break k => (SOME (Break k), s)
  | wordLang.Continue k => (SOME (Continue k), s)
  | If cmp r1 ri c1 c2 =>
      match get_var r1 s, get_var_imm ri s with
      | SOME x, SOME y =>
          match word_cmp cmp x y with
          | SOME true => go c1 s
          | SOME false => go c2 s
          | NONE => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end
  | Loop names c exit_names =>
      match cut_state (names, LN) s with
      | NONE => (SOME Error, s)
      | SOME s =>
          let '(res, s1) := fix_clock s (go c s) in
          if cont_loop res then
            (if clock s1 =? 0 then (SOME TimeOut, flush_state true s1)
             else lower (STOP (Loop names c exit_names)) (dec_clock s1))
          else if bool_decide (res = SOME (Break 0)) then
            match cut_state (exit_names, LN) s1 with
            | NONE => (SOME Error, s1)
            | SOME s2 => (NONE, s2)
            end
          else (exit_loop res, s1)
      end
  | LocValue r l1 =>
      if classical_dec (l1 IN domain (code s)) then (NONE, set_var r (Loc l1 0) s)
      else (SOME Error, s)
  | Install ptr len dptr dlen names =>
      match cut_env names (locals s) with
      | NONE => (SOME Error, s)
      | SOME env =>
          match get_var ptr s, get_var len s, get_var dptr s, get_var dlen s with
          | SOME (Word w1), SOME (Word w2), SOME (Word w3), SOME (Word w4) =>
              let '(cfg, progs) := compile_oracle s 0 in
              match buffer_flush (code_buffer s) w1 w2, buffer_flush (data_buffer s) w3 w4 with
              | SOME (bytes, cb), SOME (data, db) =>
                  let new_oracle := shift_seq 1 (compile_oracle s) in
                  match compile s cfg progs, progs with
                  | SOME (bytes', (data', cfg')), (k, prog) :: _ =>
                      if bool_decide (bytes = bytes') && bool_decide (data = data') &&
                         ⌜FST (new_oracle 0) = cfg'⌝ then
                        let s' :=
                          set_stack_size LN
                            (set_stack_max NONE
                              (set_compile_oracle new_oracle
                                (set_fp_regs FEMPTY
                                  (set_locals (insert ptr (Loc k 0) env)
                                    (set_code (union (code s) (fromAList progs))
                                      (set_data_buffer db
                                        (set_code_buffer cb s))))))) in
                        (NONE, s')
                      else (SOME Error, s)
                  | _, _ => (SOME Error, s)
                  end
              | _, _ => (SOME Error, s)
              end
          | _, _, _, _ => (SOME Error, s)
          end
      end
  | CodeBufferWrite r1 r2 =>
      match get_var r1 s, get_var r2 s with
      | SOME (Word w1), SOME (Word w2) =>
          match buffer_write (code_buffer s) w1 (w2w w2) with
          | SOME new_cb => (NONE, set_code_buffer new_cb s)
          | _ => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end
  | DataBufferWrite r1 r2 =>
      match get_var r1 s, get_var r2 s with
      | SOME (Word w1), SOME (Word w2) =>
          match buffer_write (data_buffer s) w1 w2 with
          | SOME new_db => (NONE, set_data_buffer new_db s)
          | _ => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end
  | FFI ffi_index ptr1 len1 ptr2 len2 names =>
      match get_var len1 s, get_var ptr1 s, get_var len2 s, get_var ptr2 s with
      | SOME (Word w), SOME (Word w2), SOME (Word w3), SOME (Word w4) =>
          match cut_env names (locals s) with
          | NONE => (SOME Error, s)
          | SOME env =>
              match read_bytearray w2 (w2n w) (mem_load_byte_aux (memory s) (mdomain s) (be s)),
                    read_bytearray w4 (w2n w3) (mem_load_byte_aux (memory s) (mdomain s) (be s)) with
              | SOME bytes, SOME bytes2 =>
                  match call_FFI (ffi s) (ExtCall ffi_index) bytes bytes2 with
                  | FFI_final outcome => (SOME (FinalFFI outcome), flush_state true s)
                  | FFI_return new_ffi new_bytes =>
                      let new_m := write_bytearray w4 new_bytes (memory s) (mdomain s) (be s) in
                      (NONE, set_ffi new_ffi (set_fp_regs FEMPTY (set_locals env (set_memory new_m s))))
                  end
              | _, _ => (SOME Error, s)
              end
          end
      | _, _, _, _ => (SOME Error, s)
      end
  | ShareInst op v exp =>
      match word_exp s exp with
      | SOME (Word ad) => share_inst op v ad s
      | _ => (SOME Error, s)
      end
  | Call ret dest args handler0 =>
      match get_vars args s with
      | NONE => (SOME Error, s)
      | SOME xs =>
          if bad_dest_args dest args then (SOME Error, s)
          else
            match find_code dest (add_ret_loc ret xs) (code s) (state_stack_size s) with
            | NONE => (SOME Error, s)
            | SOME (args1, (prog, ss)) =>
                match ret with
                | NONE =>
                    if ⌜handler0 = NONE⌝ then
                      if clock s =? 0 then (SOME TimeOut, flush_state true s)
                      else
                        let '(res, s) := lower prog (call_env args1 ss (dec_clock s)) in
                        if bad_fun_return res then (SOME Error, s) else (res, s)
                    else (SOME Error, s)
                | SOME (n, (names, (ret_handler, (l1, l2)))) =>
                    if ⌜domain (FST names) = {}⌝ || negb (ALL_DISTINCT n) then (SOME Error, s)
                    else
                      match cut_envs names (locals s) with
                      | NONE => (SOME Error, s)
                      | SOME envs =>
                          if clock s =? 0 then
                            (SOME TimeOut,
                             flush_state true
                               (set_stack_max
                                  (stack_max (call_env args1 ss (push_env envs handler0 s)))
                                  (set_stack [] s)))
                          else
                            match fix_clock (call_env args1 ss (push_env envs handler0 (dec_clock s)))
                                    (lower prog (call_env args1 ss
                                                   (push_env envs handler0 (dec_clock s)))) with
                            | (SOME (Result x ys), s2) =>
                                if negb (bool_decide (x = Loc l1 l2)) ||
                                   negb (LENGTH ys =? LENGTH n) then (SOME Error, s2)
                                else
                                  match pop_env s2 with
                                  | NONE => (SOME Error, s2)
                                  | SOME s1 =>
                                      if ⌜domain (locals s1) =
                                          domain (FST envs) UNION domain (SND envs)⌝
                                      then lower ret_handler (set_vars n ys s1)
                                      else (SOME Error, s1)
                                  end
                            | (SOME (Exception x y), s2) =>
                                match handler0 with
                                | NONE => (SOME (Exception x y), s2)
                                | SOME (n, (h, (l1, l2))) =>
                                    if negb (bool_decide (x = Loc l1 l2)) then (SOME Error, s2)
                                    else if ⌜domain (locals s2) =
                                             domain (FST envs) UNION domain (SND envs)⌝
                                    then lower h (set_var n y s2)
                                    else (SOME Error, s2)
                                end
                            | (NONE, s) => (SOME Error, s)
                            | (SOME (Break _), s) => (SOME Error, s)
                            | (SOME (Continue _), s) => (SOME Error, s)
                            | res => res
                            end
                      end
                end
            end
      end
  end.

(** Clock fuel [cf] (outer) and the program (inner), with [deeper] fixed. *)
Fixpoint evaluate_c (deeper : prog a -> state -> res) (cf : nat) (p0 : prog a) (s0 : state)
    {struct cf} : res :=
  let lower (p : prog a) (s : state) : res :=
    match cf with O => (SOME Error, s) | Datatypes.S cf' => evaluate_c deeper cf' p s end in
  let fix go (p : prog a) (s : state) {struct p} : res := evaluate_body go lower deeper p s in
  go p0 s0.

(** [termdep] fuel [tf]: [deeper] calls restart the clock fuel from the
    (new) state's clock. *)
Fixpoint evaluate_t (tf : nat) (cf : nat) (p : prog a) (s : state) {struct tf} : res :=
  evaluate_c
    (fun p' s' =>
       match tf with
       | O => (SOME Error, s')
       | Datatypes.S tf' => evaluate_t tf' (Datatypes.S (N.to_nat (clock s'))) p' s'
       end) cf p s.

(** HOL [evaluate]: run with fuels above the state's [termdep] and clock. *)
Definition evaluate (x : prog a * state) : res :=
  let '(p, s) := x in
  evaluate_t (Datatypes.S (N.to_nat (termdep s))) (Datatypes.S (N.to_nat (clock s))) p s.

End Evaluate.

(** ** Clock and [termdep] lemmas *)
Section ClockLemmas.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "termdep_rw" *)
Theorem termdep_rw : forall p_1 ss (s : state) n v,
  termdep (call_env p_1 ss s) = termdep s /\
  termdep (dec_clock s) = termdep s /\
  termdep (set_var n v s) = termdep s.
Proof. intros; repeat split. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "fix_clock_IMP_LESS_EQ" *)
Theorem fix_clock_IMP_LESS_EQ : forall {R} (s : state) res s1 (x : R * state),
  fix_clock s x = (res, s1) -> (clock s1 <= clock s)%N /\ termdep s1 = termdep s.
Proof.
  intros R s res s1 [r s'] H; cbn in H; inversion H; subst; cbn.
  split; [|reflexivity]. destruct (N.ltb_spec (clock s) (clock s')); lia.
Qed.

Lemma mem_store_clock : forall (addr : word a) w (s s1 : state),
  mem_store addr w s = SOME s1 -> clock s1 = clock s /\ termdep s1 = termdep s.
Proof.
  intros addr w s s1; unfold mem_store; destruct (classical_dec _); intros H;
    inversion H; split; reflexivity.
Qed.

End ClockLemmas.

Ltac cbn_state :=
  cbn [clock termdep set_locals set_locals_size set_fp_regs set_store_field set_stack
       set_stack_limit set_stack_max set_stack_size set_memory set_mdomain set_sh_mdomain
       set_permute set_compile set_compile_oracle set_code_buffer set_data_buffer set_gc_fun
       set_handler set_clock set_termdep set_code set_be set_ffi
       dec_clock call_env set_var set_vars unset_var set_store set_fp_var flush_state
       fst snd] in *.

(** Facts about the clock and [termdep] of the states in the context. *)
Ltac clock_facts :=
  repeat match goal with
         | H : fix_clock _ _ = (_, _) |- _ =>
             apply fix_clock_IMP_LESS_EQ in H; destruct H
         | H : pop_env _ = SOME _ |- _ =>
             let H' := fresh "Hp" in
             pose proof (pop_env_termdep _ _ H) as H';
             apply pop_env_clock in H
         | H : cut_state _ _ = SOME _ |- _ => apply cut_state_clock in H; destruct H
         | H : jump_exc _ = SOME (_, _) |- _ => apply jump_exc_clock in H; destruct H
         | H : mem_store _ _ _ = SOME _ |- _ => apply mem_store_clock in H; destruct H
         | H : (_ =? 0)%N = false |- _ => apply N.eqb_neq in H
         end;
  cbn_state;
  rewrite ?push_env_clock, ?push_env_termdep in *;
  cbn_state.

(** ** HOL's [evaluate_def]

    Termination measure, as in HOL: [termdep], then the clock, then the
    program size (Galette counts the constructors that [evaluate] recurses
    into at the same clock; only the existence of a decreasing measure
    matters). *)
Section EvaluateEqns.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).
Local Abbreviation res := (option (result a) * state)%type.

Fixpoint psize (p : prog a) : nat :=
  match p with
  | Seq c1 c2 => Datatypes.S (psize c1 + psize c2)
  | If _ _ _ c1 c2 => Datatypes.S (psize c1 + psize c2)
  | Loop _ c _ => Datatypes.S (psize c)
  | _ => 1
  end.

Definition eval_lt (x y : prog a * state) : Prop :=
  (termdep (snd x) < termdep (snd y))%N \/
  (termdep (snd x) = termdep (snd y) /\
   ((clock (snd x) < clock (snd y))%N \/
    (clock (snd x) = clock (snd y) /\ (psize (fst x) < psize (fst y))%nat))).

Lemma eval_lt_wf : well_founded eval_lt.
Proof.
  intros [p s].
  remember (N.to_nat (termdep s)) as t eqn:Ht. revert p s Ht.
  induction t as [t IHt] using (well_founded_induction lt_wf).
  intros p s Ht.
  remember (N.to_nat (clock s)) as k eqn:Hk. revert p s Ht Hk.
  induction k as [k IHk] using (well_founded_induction lt_wf).
  intros p s Ht Hk.
  remember (psize p) as n eqn:Hn. revert p s Ht Hk Hn.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros p s Ht Hk Hn; constructor; intros [p' s'] [Hlt|[Heq [Hlt|[Heq' Hlt]]]]; cbn in *.
  - eapply IHt; [|reflexivity]. lia.
  - eapply IHk; [| |reflexivity]; lia.
  - eapply IHn; [| | |reflexivity]; lia.
Qed.

Definition lowerF (de : prog a -> state -> res) (cf : nat) (p : prog a) (s : state) : res :=
  match cf with O => (SOME Error, s) | Datatypes.S cf' => evaluate_c de cf' p s end.

Definition deeperF (tf : nat) (p : prog a) (s : state) : res :=
  match tf with
  | O => (SOME Error, s)
  | Datatypes.S tf' => evaluate_t tf' (Datatypes.S (N.to_nat (clock s))) p s
  end.

Lemma evaluate_c_unfold de cf p s :
  evaluate_c de cf p s = evaluate_body (evaluate_c de cf) (lowerF de cf) de p s.
Proof. destruct cf, p; reflexivity. Qed.

Lemma evaluate_t_unfold tf cf p s :
  evaluate_t tf cf p s = evaluate_c (deeperF tf) cf p s.
Proof. destruct tf; reflexivity. Qed.

Ltac prove_lt := clock_facts; cbn [psize] in *; lia.

(** Every recursive call of [evaluate_body] is smaller in [eval_lt]: two
    instances that agree on smaller arguments compute the same step. *)
Lemma evaluate_body_ext (go1 go2 lo1 lo2 de1 de2 : prog a -> state -> res) p s :
  (forall p' s', (termdep s' <= termdep s)%N -> (clock s' <= clock s)%N ->
                 (psize p' < psize p)%nat -> go1 p' s' = go2 p' s') ->
  (forall p' s', (termdep s' <= termdep s)%N -> (clock s' < clock s)%N ->
                 lo1 p' s' = lo2 p' s') ->
  (forall p' s', (termdep s' < termdep s)%N -> de1 p' s' = de2 p' s') ->
  evaluate_body go1 lo1 de1 p s = evaluate_body go2 lo2 de2 p s.
Proof.
  intros Hgo Hlo Hde.
  destruct p; cbn [evaluate_body];
  repeat first
    [ reflexivity
    | match goal with
      | |- context [go1 ?p' ?s'] => rewrite (Hgo p' s') by prove_lt
      | |- context [lo1 ?p' ?s'] => rewrite (Hlo p' s') by prove_lt
      | |- context [de1 ?p' ?s'] => rewrite (Hde p' s') by prove_lt
      end
    | match goal with
      | |- context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
      end ].
Qed.

Lemma evaluate_t_fuel : forall (x : prog a * state) tf1 tf2 cf1 cf2,
  (N.to_nat (termdep (snd x)) < tf1)%nat -> (N.to_nat (termdep (snd x)) < tf2)%nat ->
  (N.to_nat (clock (snd x)) < cf1)%nat -> (N.to_nat (clock (snd x)) < cf2)%nat ->
  evaluate_t tf1 cf1 (fst x) (snd x) = evaluate_t tf2 cf2 (fst x) (snd x).
Proof.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros tf1 tf2 cf1 cf2 T1 T2 C1 C2; cbn [fst snd] in *.
  rewrite !evaluate_t_unfold, !evaluate_c_unfold. apply evaluate_body_ext.
  - intros p' s' Ht Hc Hp. rewrite <- !evaluate_t_unfold.
    apply (IH (p', s')); cbn; [unfold eval_lt; cbn; lia|lia..].
  - intros p' s' Ht Hc. destruct cf1 as [|cf1]; [lia|]. destruct cf2 as [|cf2]; [lia|].
    cbn [lowerF]. rewrite <- !evaluate_t_unfold.
    apply (IH (p', s')); cbn; [unfold eval_lt; cbn; lia|lia..].
  - intros p' s' Ht. destruct tf1 as [|tf1]; [lia|]. destruct tf2 as [|tf2]; [lia|].
    cbn [deeperF]. apply (IH (p', s')); cbn; [unfold eval_lt; cbn; lia|lia..].
Qed.

Lemma evaluate_eq_t tf cf (p : prog a) (s : state) :
  (N.to_nat (termdep s) < tf)%nat -> (N.to_nat (clock s) < cf)%nat ->
  evaluate (p, s) = evaluate_t tf cf p s.
Proof.
  intros H1 H2; unfold evaluate.
  apply (evaluate_t_fuel (p, s)); cbn; lia.
Qed.

(** [evaluate] is a fixed point of its one-step body. *)
Lemma evaluate_eqn (p : prog a) (s : state) :
  evaluate (p, s) =
  evaluate_body (fun p' s' => evaluate (p', s')) (fun p' s' => evaluate (p', s'))
    (fun p' s' => evaluate (p', s')) p s.
Proof.
  rewrite (evaluate_eq_t (Datatypes.S (N.to_nat (termdep s))) (Datatypes.S (N.to_nat (clock s))))
    by lia.
  rewrite evaluate_t_unfold, evaluate_c_unfold. apply evaluate_body_ext.
  - intros p' s' Ht Hc Hp. rewrite <- evaluate_t_unfold. symmetry; apply evaluate_eq_t; lia.
  - intros p' s' Ht Hc. cbn [lowerF]. rewrite <- evaluate_t_unfold.
    symmetry; apply evaluate_eq_t; lia.
  - intros p' s' Ht. cbn [deeperF]. symmetry; apply evaluate_eq_t; lia.
Qed.

End EvaluateEqns.

(** ** The clock never increases and [termdep] is constant *)

(** Case-split every [match] in [H] (after each split, [H] is reduced). *)
Ltac split_H H :=
  repeat match type of H with
         | context [match ?x with _ => _ end] =>
             let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H
         end.

Section Clock.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "gc_clock" *)
Theorem gc_clock : forall (s1 s2 : state),
  gc s1 = SOME s2 -> (clock s2 <= clock s1)%N /\ termdep s2 = termdep s1.
Proof.
  intros s1 s2 H; unfold gc in H; cbn zeta in H; split_H H; try discriminate H.
  injection H as <-; cbn_state; split; lia.
Qed.

(** HOL's statement also quantifies a vacuous variable [xs]; it is
    omitted. *)
(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "alloc_clock" *)
Theorem alloc_clock : forall (x : word a) names (s1 : state) vs s2,
  alloc x names s1 = (vs, s2) -> (clock s2 <= clock s1)%N /\ termdep s2 = termdep s1.
Proof.
  intros x names s1 vs s2 H; unfold alloc in H; split_H H;
    repeat match goal with E : gc _ = SOME _ |- _ => apply gc_clock in E; destruct E end;
    injection H as <- <-; clock_facts; split; lia.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "sh_mem_set_var_clock" *)
Theorem sh_mem_set_var_clock : forall v (s1 : state) v2 s2 res,
  sh_mem_set_var res v s1 = (v2, s2) -> (clock s2 <= clock s1)%N /\ termdep s2 = termdep s1.
Proof.
  intros v s1 v2 s2 res H; unfold sh_mem_set_var in H; split_H H;
    injection H as <- <-; cbn_state; split; lia.
Qed.

(** HOL's statement also quantifies a vacuous variable [v1]; it is
    omitted. *)
(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "share_inst_clock" *)
Theorem share_inst_clock : forall op v ad (s1 : state) v2 s2,
  share_inst op v ad s1 = (v2, s2) -> (clock s2 <= clock s1)%N /\ termdep s2 = termdep s1.
Proof.
  intros op v ad s1 v2 s2 H; destruct op; cbn [share_inst] in H;
    first
      [ apply sh_mem_set_var_clock in H; exact H
      | unfold sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32 in H;
        split_H H; injection H as <- <-; cbn_state; split; lia ].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "inst_clock" *)
Theorem inst_clock : forall i (s s2 : state),
  inst i s = SOME s2 -> (clock s2 <= clock s)%N /\ termdep s2 = termdep s.
Proof.
  intros i s s2 H; unfold inst, assign in H; split_H H; try discriminate H;
    injection H as <-; clock_facts; split; lia.
Qed.

End Clock.

Section EvaluateClock.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

Ltac prove_eval_lt := unfold eval_lt; cbn [fst snd]; clock_facts; cbn [psize] in *; lia.

Ltac clock_step IH H :=
  repeat first
    [ match type of H with
      | evaluate (?p', ?s'') = (?r', ?t) =>
          let Hc := fresh "Hc" in
          assert (Hc : (clock t <= clock s'')%N /\ termdep t = termdep s'')
            by (exact (IH (p', s'') ltac:(prove_eval_lt) r' t H));
          clear H; destruct Hc; clock_facts; split; lia
      | (_, _) = (_, _) => injection H as <- <-; clock_facts; split; lia
      | alloc _ _ _ = (_, _) =>
          apply alloc_clock in H; destruct H; clock_facts; split; lia
      | share_inst _ _ _ _ = (_, _) =>
          apply share_inst_clock in H; destruct H; clock_facts; split; lia
      end
    | match goal with
      | E : evaluate (?p', ?s'') = (?r', ?t) |- _ =>
          let Hc := fresh "Hc" in
          assert (Hc : (clock t <= clock s'')%N /\ termdep t = termdep s'')
            by (exact (IH (p', s'') ltac:(prove_eval_lt) r' t E));
          clear E; destruct Hc
      | E : inst _ _ = SOME _ |- _ => apply inst_clock in E; destruct E
      end
    | match type of H with
      | context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H
      end ].

(** HOL's statement; the proof is by well-founded induction on [eval_lt]
    (HOL: [recInduct evaluate_ind]). *)
(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "evaluate_clock" *)
Theorem evaluate_clock : forall (xs : prog a) (s1 : state) vs s2,
  evaluate (xs, s1) = (vs, s2) -> (clock s2 <= clock s1)%N /\ termdep s2 = termdep s1.
Proof.
  enough (G : forall x : prog a * state, forall r s',
            evaluate x = (r, s') -> (clock s' <= clock (snd x))%N /\ termdep s' = termdep (snd x))
    by (intros xs s1 vs s2 H; exact (G (xs, s1) vs s2 H)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s' H; cbn [snd].
  rewrite evaluate_eqn in H.
  destruct p; cbn [evaluate_body] in H; clock_step IH H.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "fix_clock_evaluate" *)
Theorem fix_clock_evaluate : forall (c1 : prog a) (s : state),
  fix_clock s (evaluate (c1, s)) = evaluate (c1, s).
Proof.
  intros c1 s; destruct (evaluate (c1, s)) as [r s'] eqn:E.
  destruct (evaluate_clock c1 s r s' E) as [Hc Ht].
  unfold fix_clock; f_equal.
  destruct (N.ltb_spec (clock s) (clock s')); [lia|].
  rewrite <- Ht; destruct s'; reflexivity.
Qed.

End EvaluateClock.

Section EvaluateDef.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(** HOL's [evaluate_def] as stored by HOL after the definition, i.e. with
    [fix_clock] removed using [fix_clock_evaluate] (HOL rebinds the name
    [evaluate_def] to this theorem). *)
(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "evaluate_def" 1369 *)
Theorem evaluate_def :
  (forall (s : state),
     evaluate (Skip, s) =
      (NONE, s)) /\
  (forall n names (s : state),
     evaluate (Alloc n names, s) =
      match get_var n s with
      | SOME (Word w) => alloc w names s
      | _ => (SOME Error, s)
      end) /\
  (forall t1 t2 addr offset words (s : state),
     evaluate (StoreConsts t1 t2 addr offset words, s) =
      match get_var addr s, get_var offset s with
      | SOME (Word a0), SOME (Word off) =>
          if negb (const_addresses a0 words (mdomain s)) then (SOME Error, s)
          else
            let s := set_memory (const_writes a0 off words (memory s)) s in
            let s := set_var offset (Word off) (unset_var t1 (unset_var t2 s)) in
            (NONE, set_var addr (Word (a0 + bytes_in_word * n2w (LENGTH words))%w) s)
      | _, _ => (SOME Error, s)
      end) /\
  (forall pri moves (s : state),
     evaluate (Move pri moves, s) =
      if ALL_DISTINCT (MAP FST moves) then
        match get_vars (MAP SND moves) s with
        | NONE => (SOME Error, s)
        | SOME vs => (NONE, set_vars (MAP FST moves) vs s)
        end
      else (SOME Error, s)) /\
  (forall i (s : state),
     evaluate (Inst i, s) =
      match inst i s with
      | SOME s1 => (NONE, s1)
      | NONE => (SOME Error, s)
      end) /\
  (forall v exp (s : state),
     evaluate (Assign v exp, s) =
      match word_exp s exp with
      | NONE => (SOME Error, s)
      | SOME w => (NONE, set_var v w s)
      end) /\
  (forall v name (s : state),
     evaluate (Get v name, s) =
      match get_store name s with
      | NONE => (SOME Error, s)
      | SOME x => (NONE, set_var v x s)
      end) /\
  (forall v exp (s : state),
     evaluate (Set_ v exp, s) =
      if bool_decide (v = Handler) || bool_decide (v = BitmapBase) then (SOME Error, s)
      else
        match word_exp s exp with
        | NONE => (SOME Error, s)
        | SOME w => (NONE, set_store v w s)
        end) /\
  (forall b dst src (s : state),
     evaluate (OpCurrHeap b dst src, s) =
      match word_exp s (Op b [Var src; Lookup CurrHeap]) with
      | NONE => (SOME Error, s)
      | SOME w => (NONE, set_var dst w s)
      end) /\
  (forall exp v (s : state),
     evaluate (Store exp v, s) =
      match word_exp s exp, get_var v s with
      | SOME (Word a0), SOME w =>
          match mem_store a0 w s with
          | SOME s1 => (NONE, s1)
          | NONE => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end) /\
  (forall (s : state),
     evaluate (Tick, s) =
      if clock s =? 0 then (SOME TimeOut, flush_state true s) else (NONE, dec_clock s)) /\
  (forall p (s : state),
     evaluate (MustTerminate p, s) =
      if termdep s =? 0 then (SOME Error, s) else
        let '(res, s1) :=
          evaluate (p, set_termdep (termdep s - 1) (set_clock (MustTerminate_limit a) s)) in
        if bool_decide (res = SOME TimeOut) then (SOME Error, s)
        else (res, set_termdep (termdep s) (set_clock (clock s) s1))) /\
  (forall c1 c2 (s : state),
     evaluate (Seq c1 c2, s) =
      let '(res, s1) := evaluate (c1, s) in
      if bool_decide (res = NONE) then evaluate (c2, s1) else (res, s1)) /\
  (forall n ms (s : state),
     evaluate (Return n ms, s) =
      match get_var n s, get_vars ms s with
      | SOME (Loc l1 l2), SOME ys => (SOME (Result (Loc l1 l2) ys), flush_state false s)
      | _, _ => (SOME Error, s)
      end) /\
  (forall n (s : state),
     evaluate (Raise n, s) =
      match get_var n s with
      | NONE => (SOME Error, s)
      | SOME w =>
          match jump_exc s with
          | NONE => (SOME Error, s)
          | SOME (s, (l1, l2)) => (SOME (Exception (Loc l1 l2) w), s)
          end
      end) /\
  (forall k (s : state),
     evaluate (wordLang.Break k, s) =
      (SOME (Break k), s)) /\
  (forall k (s : state),
     evaluate (wordLang.Continue k, s) =
      (SOME (Continue k), s)) /\
  (forall cmp r1 ri c1 c2 (s : state),
     evaluate (If cmp r1 ri c1 c2, s) =
      match get_var r1 s, get_var_imm ri s with
      | SOME x, SOME y =>
          match word_cmp cmp x y with
          | SOME true => evaluate (c1, s)
          | SOME false => evaluate (c2, s)
          | NONE => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end) /\
  (forall names c exit_names (s : state),
     evaluate (Loop names c exit_names, s) =
      match cut_state (names, LN) s with
      | NONE => (SOME Error, s)
      | SOME s =>
          let '(res, s1) := evaluate (c, s) in
          if cont_loop res then
            (if clock s1 =? 0 then (SOME TimeOut, flush_state true s1)
             else evaluate (STOP (Loop names c exit_names), dec_clock s1))
          else if bool_decide (res = SOME (Break 0)) then
            match cut_state (exit_names, LN) s1 with
            | NONE => (SOME Error, s1)
            | SOME s2 => (NONE, s2)
            end
          else (exit_loop res, s1)
      end) /\
  (forall r l1 (s : state),
     evaluate (LocValue r l1, s) =
      if classical_dec (l1 IN domain (code s)) then (NONE, set_var r (Loc l1 0) s)
      else (SOME Error, s)) /\
  (forall ptr len dptr dlen names (s : state),
     evaluate (Install ptr len dptr dlen names, s) =
      match cut_env names (locals s) with
      | NONE => (SOME Error, s)
      | SOME env =>
          match get_var ptr s, get_var len s, get_var dptr s, get_var dlen s with
          | SOME (Word w1), SOME (Word w2), SOME (Word w3), SOME (Word w4) =>
              let '(cfg, progs) := compile_oracle s 0 in
              match buffer_flush (code_buffer s) w1 w2, buffer_flush (data_buffer s) w3 w4 with
              | SOME (bytes, cb), SOME (data, db) =>
                  let new_oracle := shift_seq 1 (compile_oracle s) in
                  match compile s cfg progs, progs with
                  | SOME (bytes', (data', cfg')), (k, prog) :: _ =>
                      if bool_decide (bytes = bytes') && bool_decide (data = data') &&
                         ⌜FST (new_oracle 0) = cfg'⌝ then
                        let s' :=
                          set_stack_size LN
                            (set_stack_max NONE
                              (set_compile_oracle new_oracle
                                (set_fp_regs FEMPTY
                                  (set_locals (insert ptr (Loc k 0) env)
                                    (set_code (union (code s) (fromAList progs))
                                      (set_data_buffer db
                                        (set_code_buffer cb s))))))) in
                        (NONE, s')
                      else (SOME Error, s)
                  | _, _ => (SOME Error, s)
                  end
              | _, _ => (SOME Error, s)
              end
          | _, _, _, _ => (SOME Error, s)
          end
      end) /\
  (forall r1 r2 (s : state),
     evaluate (CodeBufferWrite r1 r2, s) =
      match get_var r1 s, get_var r2 s with
      | SOME (Word w1), SOME (Word w2) =>
          match buffer_write (code_buffer s) w1 (w2w w2) with
          | SOME new_cb => (NONE, set_code_buffer new_cb s)
          | _ => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end) /\
  (forall r1 r2 (s : state),
     evaluate (DataBufferWrite r1 r2, s) =
      match get_var r1 s, get_var r2 s with
      | SOME (Word w1), SOME (Word w2) =>
          match buffer_write (data_buffer s) w1 w2 with
          | SOME new_db => (NONE, set_data_buffer new_db s)
          | _ => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end) /\
  (forall ffi_index ptr1 len1 ptr2 len2 names (s : state),
     evaluate (FFI ffi_index ptr1 len1 ptr2 len2 names, s) =
      match get_var len1 s, get_var ptr1 s, get_var len2 s, get_var ptr2 s with
      | SOME (Word w), SOME (Word w2), SOME (Word w3), SOME (Word w4) =>
          match cut_env names (locals s) with
          | NONE => (SOME Error, s)
          | SOME env =>
              match read_bytearray w2 (w2n w) (mem_load_byte_aux (memory s) (mdomain s) (be s)),
                    read_bytearray w4 (w2n w3) (mem_load_byte_aux (memory s) (mdomain s) (be s)) with
              | SOME bytes, SOME bytes2 =>
                  match call_FFI (ffi s) (ExtCall ffi_index) bytes bytes2 with
                  | FFI_final outcome => (SOME (FinalFFI outcome), flush_state true s)
                  | FFI_return new_ffi new_bytes =>
                      let new_m := write_bytearray w4 new_bytes (memory s) (mdomain s) (be s) in
                      (NONE, set_ffi new_ffi (set_fp_regs FEMPTY (set_locals env (set_memory new_m s))))
                  end
              | _, _ => (SOME Error, s)
              end
          end
      | _, _, _, _ => (SOME Error, s)
      end) /\
  (forall op v exp (s : state),
     evaluate (ShareInst op v exp, s) =
      match word_exp s exp with
      | SOME (Word ad) => share_inst op v ad s
      | _ => (SOME Error, s)
      end) /\
  (forall ret dest args handler (s : state),
     evaluate (Call ret dest args handler, s) =
      match get_vars args s with
      | NONE => (SOME Error, s)
      | SOME xs =>
          if bad_dest_args dest args then (SOME Error, s)
          else
            match find_code dest (add_ret_loc ret xs) (code s) (state_stack_size s) with
            | NONE => (SOME Error, s)
            | SOME (args1, (prog, ss)) =>
                match ret with
                | NONE =>
                    if ⌜handler = NONE⌝ then
                      if clock s =? 0 then (SOME TimeOut, flush_state true s)
                      else
                        let '(res, s) := evaluate (prog, call_env args1 ss (dec_clock s)) in
                        if bad_fun_return res then (SOME Error, s) else (res, s)
                    else (SOME Error, s)
                | SOME (n, (names, (ret_handler, (l1, l2)))) =>
                    if ⌜domain (FST names) = {}⌝ || negb (ALL_DISTINCT n) then (SOME Error, s)
                    else
                      match cut_envs names (locals s) with
                      | NONE => (SOME Error, s)
                      | SOME envs =>
                          if clock s =? 0 then
                            (SOME TimeOut,
                             flush_state true
                               (set_stack_max
                                  (stack_max (call_env args1 ss (push_env envs handler s)))
                                  (set_stack [] s)))
                          else
                            match evaluate (prog, call_env args1 ss (push_env envs handler (dec_clock s))) with
                            | (SOME (Result x ys), s2) =>
                                if negb (bool_decide (x = Loc l1 l2)) ||
                                   negb (LENGTH ys =? LENGTH n) then (SOME Error, s2)
                                else
                                  match pop_env s2 with
                                  | NONE => (SOME Error, s2)
                                  | SOME s1 =>
                                      if ⌜domain (locals s1) =
                                          domain (FST envs) UNION domain (SND envs)⌝
                                      then evaluate (ret_handler, set_vars n ys s1)
                                      else (SOME Error, s1)
                                  end
                            | (SOME (Exception x y), s2) =>
                                match handler with
                                | NONE => (SOME (Exception x y), s2)
                                | SOME (n, (h, (l1, l2))) =>
                                    if negb (bool_decide (x = Loc l1 l2)) then (SOME Error, s2)
                                    else if ⌜domain (locals s2) =
                                             domain (FST envs) UNION domain (SND envs)⌝
                                    then evaluate (h, set_var n y s2)
                                    else (SOME Error, s2)
                                end
                            | (NONE, s) => (SOME Error, s)
                            | (SOME (Break _), s) => (SOME Error, s)
                            | (SOME (Continue _), s) => (SOME Error, s)
                            | res => res
                            end
                      end
                end
            end
      end).
Proof.
  repeat split; intros;
      (etransitivity; [apply evaluate_eqn|]); cbn [evaluate_body];
    repeat first
      [ reflexivity
      | rewrite fix_clock_evaluate
      | match goal with |- context [match ?x with _ => _ end] => destruct x end ].
Qed.

End EvaluateDef.

(** ** Observational semantics *)
Section Semantics.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

#[local] Instance behaviour_inhabited : Inhabited behaviour := Fail.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "semantics_def" *)
Definition semantics (s : state) (start : N) : behaviour :=
  let prog := @Call a NONE (SOME start) [0] NONE in
  if classical_dec (exists k,
       match fst (evaluate (prog, set_clock k s)) with
       | SOME (Exception _ _) => True
       | SOME (Result ret _) => ret <> Loc 1 0
       | SOME Error => True
       | NONE => True
       | _ => False
       end)
  then Fail
  else
    match some (fun res => exists k t r outcome,
             evaluate (prog, set_clock k s) = (r, t) /\
             match r with
             | SOME (FinalFFI e) => outcome = FFI_outcome e
             | SOME (Result _ _) => outcome = Success
             | SOME NotEnoughSpace => outcome = Resource_limit_hit
             | _ => False
             end /\
             res = Terminate outcome (io_events (ffi t))) with
    | SOME res => res
    | NONE =>
        Diverge (build_lprefix_lub
                   (IMAGE (fun k => fromList (io_events (ffi (snd (evaluate (prog, set_clock k s))))))
                          UNIV))
    end.

(*! HOL "cakeml/compiler/backend/semantics/wordSemScript.sml" "word_lang_safe_for_space_def" *)
Definition word_lang_safe_for_space (s : state) (start : N) : Prop :=
  let prog := @Call a NONE (SOME start) [0] NONE in
  forall k res t, evaluate (prog, set_clock k s) = (res, t) ->
    exists max, stack_max t = SOME max /\ (max <= stack_limit t)%N.

End Semantics.
