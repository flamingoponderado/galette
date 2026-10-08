(** * CakeML [stackSem]: semantics of stackLang

    Port of [cakeml/compiler/backend/semantics/stackSemScript.sml].
    Functional big-step semantics with a clock, as in HOL.  Carrier notes:
    - [state] is a Rocq record with HOL's field names (types ['a], ['c],
      ['ffi] are [a : N], [c], [ffi_t]); HOL's [s with f := v] is
      [set_<f> v s] (helpers below; the one for [store] is [set_store_fld]
      since HOL's own [set_store] is a different function).
    - HOL tuples nest to the right: [x # y # z] is [x * (y * z)] and the
      pattern [(x, y, z)] is [(x, (y, z))].
    - Sets are [pred_set] sets ([_ -> Prop]); the semantics is not executable,
      so classical decisions ([classical_dec], [⌜_⌝]) are used where HOL tests
      membership in a set or equality on an arbitrary type.
    - The result constructors [Break], [Continue], [Halt] shadow stackLang's
      program constructors of the same names, which are written
      [stackLang.Break] etc.; wordLang's expression constructors are written
      qualified ([wordLang.Op], [wordLang.Var], ...) since ASM's [Const],
      [Load], [Shift] are also in scope.
    - FP: the [fp64_*] operations come from the (placeholder)
      [machine_ieee] module; [fpfma] is [fpSem.fpfma].
    - Functions defined in HOL by well-founded recursion ([bit_length],
      [enc_stack], [dec_stack], [copy_words_for_pattern], [copy_words],
      [evaluate]) are computed with a sufficient fuel, and HOL's equations
      are proved as the tagged [_def] theorems.  [evaluate_def] is tagged
      twice: HOL's original equations (with [fix_clock]) and the rebound
      version (rewritten with [fix_clock_evaluate]).  HOL's tests
      [if res = NONE then ... else ...] are written as [match res with NONE
      => ... | _ => ... end].
    - Not ported: HOL's [evaluate_ind] (the generated recursion-induction
      principle); use well-founded induction on [eval_lt] instead. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.integer Require Import integer_word.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map.
From Galette.HOL.src.finite_maps Require sptree.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.HOL.src.floating_point Require Import binary_ieee machine_ieee.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.semantics Require fpSem.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend.semantics Require wordSem.
Import wordLang (word_loc, Word, Loc).
Import wordSem (buffer, buffer_flush, buffer_write, gc_fun_type, mem_load_byte_aux,
  mem_store_byte_aux, mem_load_32, mem_store_32, write_bytearray).
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "result" *)
Inductive result (a : N) : Type :=
| Result : word_loc a -> result a
| Exception : word_loc a -> result a
| Break : N -> result a
| Continue : N -> result a
| Halt : word_loc a -> result a
| TimeOut : result a
| FinalFFI : final_event -> result a
| Error : result a.
Arguments Result {a} _. Arguments Exception {a} _. Arguments Break {a} _.
Arguments Continue {a} _. Arguments Halt {a} _. Arguments TimeOut {a}.
Arguments FinalFFI {a} _. Arguments Error {a}.

#[global] Instance result_inhabited {a} : Inhabited (result a) := Error.

(** ** Bitmaps *)

Section Bitmaps.
Context {a : N}.
Local Open Scope word_scope.

(** HOL [bit_length] recurses on [w >>> 1] (well-founded on [w2n]); here it
    is the binary size of [w2n w]. *)
Definition bit_length (w : word a) : N := N.size (w2n w).

Lemma bool_decide_false {P : Prop} `{Decision P} : bool_decide P = false -> ~ P.
Proof. intros H1 H2. apply (proj2 (bool_decide_spec P)) in H2. congruence. Qed.

Lemma size_div2 x : x <> 0 -> N.size x = N.succ (N.size (x / 2)).
Proof.
  intros H. rewrite <- N.div2_div. destruct x as [|p]; [contradiction|].
  destruct p as [p|p|]; reflexivity.
Qed.

Lemma size_lsr1 (p : word a) : p <> n2w 0 ->
  N.size (w2n p) = N.succ (N.size (w2n (p >>> 1))).
Proof.
  intros H. rewrite w2n_lsr. apply size_div2.
  intros E; apply H, word_eq_w2n; rewrite E, w2n_n2w; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "bit_length_def" *)
Theorem bit_length_def : forall w : word a,
  bit_length w = if bool_decide (w = n2w 0) then 0%N else (bit_length (w >>> 1) + 1)%N.
Proof.
  intros w; unfold bit_length.
  destruct (bool_decide (w = n2w 0)) eqn:E.
  - apply bool_decide_spec in E; subst; rewrite w2n_n2w; reflexivity.
  - apply bool_decide_false in E. rewrite (size_lsr1 w E); lia.
Qed.


(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "filter_bitmap_def" *)
Fixpoint filter_bitmap {A} (bs : list bool) (rs : list A) : option (list A * list A) :=
  match bs, rs with
  | [], rs => SOME ([], rs)
  | false :: bs, r :: rs => filter_bitmap bs rs
  | true :: bs, r :: rs =>
      match filter_bitmap bs rs with
      | NONE => NONE
      | SOME (ts, rs') => SOME (r :: ts, rs')
      end
  | _, _ => NONE
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "map_bitmap_def" *)
Fixpoint map_bitmap {A} (bs : list bool) (ts rs : list A) : option (list A * (list A * list A)) :=
  match bs, ts, rs with
  | [], ts, rs => SOME ([], (ts, rs))
  | false :: bs, ts, r :: rs =>
      match map_bitmap bs ts rs with
      | NONE => NONE
      | SOME (xs, (ys, zs)) => SOME (r :: xs, (ys, zs))
      end
  | true :: bs, t :: ts, r :: rs =>
      match map_bitmap bs ts rs with
      | NONE => NONE
      | SOME (xs, (ys, zs)) => SOME (t :: xs, (ys, zs))
      end
  | _, _, _ => NONE
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "filter_bitmap_LENGTH" *)
Theorem filter_bitmap_LENGTH : forall {A} (bs : list bool) (xs : list A) x y,
  filter_bitmap bs xs = SOME (x, y) -> (LENGTH y <= LENGTH xs)%N.
Proof.
  intros A bs; induction bs as [|b bs IH]; intros xs x y H.
  - cbn in H; injection H as <- <-; lia.
  - destruct xs as [|r xs]; [destruct b; discriminate|].
    cbn [LENGTH]. destruct b; cbn in H.
    + destruct (filter_bitmap bs xs) as [[ts rs']|] eqn:E; [|discriminate].
      injection H as <- <-. specialize (IH _ _ _ E); lia.
    + specialize (IH _ _ _ H); lia.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "map_bitmap_LENGTH" *)
Theorem map_bitmap_LENGTH : forall {A} (t1 : list bool) (t2 t3 : list A) x y z,
  map_bitmap t1 t2 t3 = SOME (x, (y, z)) ->
  (LENGTH y <= LENGTH t2 /\ LENGTH z <= LENGTH t3)%N.
Proof.
  intros A t1; induction t1 as [|b bs IH]; intros t2 t3 x y z H.
  - cbn in H; injection H as <- <- <-; lia.
  - destruct b; cbn in H.
    + destruct t2 as [|t t2]; [discriminate|]. destruct t3 as [|r t3]; [discriminate|].
      destruct (map_bitmap bs t2 t3) as [[xs [ys zs]]|] eqn:E; [|discriminate].
      injection H as <- <- <-. specialize (IH _ _ _ _ _ E); cbn [LENGTH]; lia.
    + destruct t3 as [|r t3]; [destruct t2; discriminate|].
      destruct (map_bitmap bs t2 t3) as [[xs [ys zs]]|] eqn:E; [|discriminate].
      injection H as <- <- <-. specialize (IH _ _ _ _ _ E); cbn [LENGTH]; lia.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "read_bitmap_def" *)
Fixpoint read_bitmap (ws : list (word a)) : option (list bool) :=
  match ws with
  | [] => NONE
  | w :: ws =>
      if word_msb w then
        match read_bitmap ws with
        | NONE => NONE
        | SOME bs => SOME (GENLIST (fun i => w ' i) (dimindex a - 1) ++ bs)
        end
      else SOME (GENLIST (fun i => w ' i) (bit_length w - 1))
  end.

End Bitmaps.

(** ** State *)

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "state" *)
Record state (a : N) (c : Type) (ffi_t : Type) : Type := mk_state {
  regs : fmap N (word_loc a);
  fp_regs : fmap N word64;
  store : fmap store_name (word_loc a);
  stack : list (word_loc a);
  stack_space : N;
  memory : word a -> word_loc a;
  mdomain : word a -> Prop;
  sh_mdomain : word a -> Prop;
  bitmaps : list (word a);
  compile : c -> list (N * prog a) -> option (list word8 * c);
  compile_oracle : N -> c * (list (N * prog a) * list (word a));
  code_buffer : buffer a 8;
  data_buffer : buffer a a;
  gc_fun : gc_fun_type a;
  use_stack : bool;
  use_store : bool;
  use_alloc : bool;
  clock : N;
  code : sptree.spt (prog a);
  ffi : ffi_state ffi_t;
  ffi_save_regs : N -> Prop;
  be : bool
}.
Arguments mk_state {a c ffi_t}.
Arguments regs {a c ffi_t}. Arguments fp_regs {a c ffi_t}. Arguments store {a c ffi_t}.
Arguments stack {a c ffi_t}. Arguments stack_space {a c ffi_t}. Arguments memory {a c ffi_t}.
Arguments mdomain {a c ffi_t}. Arguments sh_mdomain {a c ffi_t}. Arguments bitmaps {a c ffi_t}.
Arguments compile {a c ffi_t}. Arguments compile_oracle {a c ffi_t}.
Arguments code_buffer {a c ffi_t}. Arguments data_buffer {a c ffi_t}. Arguments gc_fun {a c ffi_t}.
Arguments use_stack {a c ffi_t}. Arguments use_store {a c ffi_t}. Arguments use_alloc {a c ffi_t}.
Arguments clock {a c ffi_t}. Arguments code {a c ffi_t}. Arguments ffi {a c ffi_t}.
Arguments ffi_save_regs {a c ffi_t}. Arguments be {a c ffi_t}.

(** HOL [s with f := x] for each field. *)
Section Updates.
Context {a : N} {c ffi_t : Type}.
Definition set_regs x (s : state a c ffi_t) : state a c ffi_t := mk_state x s.(fp_regs) s.(store) s.(stack) s.(stack_space) s.(memory) s.(mdomain) s.(sh_mdomain) s.(bitmaps) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(use_stack) s.(use_store) s.(use_alloc) s.(clock) s.(code) s.(ffi) s.(ffi_save_regs) s.(be).
Definition set_fp_regs x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) x s.(store) s.(stack) s.(stack_space) s.(memory) s.(mdomain) s.(sh_mdomain) s.(bitmaps) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(use_stack) s.(use_store) s.(use_alloc) s.(clock) s.(code) s.(ffi) s.(ffi_save_regs) s.(be).
Definition set_store_fld x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) x s.(stack) s.(stack_space) s.(memory) s.(mdomain) s.(sh_mdomain) s.(bitmaps) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(use_stack) s.(use_store) s.(use_alloc) s.(clock) s.(code) s.(ffi) s.(ffi_save_regs) s.(be).
Definition set_stack x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(store) x s.(stack_space) s.(memory) s.(mdomain) s.(sh_mdomain) s.(bitmaps) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(use_stack) s.(use_store) s.(use_alloc) s.(clock) s.(code) s.(ffi) s.(ffi_save_regs) s.(be).
Definition set_stack_space x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(store) s.(stack) x s.(memory) s.(mdomain) s.(sh_mdomain) s.(bitmaps) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(use_stack) s.(use_store) s.(use_alloc) s.(clock) s.(code) s.(ffi) s.(ffi_save_regs) s.(be).
Definition set_memory x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(store) s.(stack) s.(stack_space) x s.(mdomain) s.(sh_mdomain) s.(bitmaps) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(use_stack) s.(use_store) s.(use_alloc) s.(clock) s.(code) s.(ffi) s.(ffi_save_regs) s.(be).
Definition set_mdomain x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(store) s.(stack) s.(stack_space) s.(memory) x s.(sh_mdomain) s.(bitmaps) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(use_stack) s.(use_store) s.(use_alloc) s.(clock) s.(code) s.(ffi) s.(ffi_save_regs) s.(be).
Definition set_sh_mdomain x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(store) s.(stack) s.(stack_space) s.(memory) s.(mdomain) x s.(bitmaps) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(use_stack) s.(use_store) s.(use_alloc) s.(clock) s.(code) s.(ffi) s.(ffi_save_regs) s.(be).
Definition set_bitmaps x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(store) s.(stack) s.(stack_space) s.(memory) s.(mdomain) s.(sh_mdomain) x s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(use_stack) s.(use_store) s.(use_alloc) s.(clock) s.(code) s.(ffi) s.(ffi_save_regs) s.(be).
Definition set_compile x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(store) s.(stack) s.(stack_space) s.(memory) s.(mdomain) s.(sh_mdomain) s.(bitmaps) x s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(use_stack) s.(use_store) s.(use_alloc) s.(clock) s.(code) s.(ffi) s.(ffi_save_regs) s.(be).
Definition set_compile_oracle x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(store) s.(stack) s.(stack_space) s.(memory) s.(mdomain) s.(sh_mdomain) s.(bitmaps) s.(compile) x s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(use_stack) s.(use_store) s.(use_alloc) s.(clock) s.(code) s.(ffi) s.(ffi_save_regs) s.(be).
Definition set_code_buffer x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(store) s.(stack) s.(stack_space) s.(memory) s.(mdomain) s.(sh_mdomain) s.(bitmaps) s.(compile) s.(compile_oracle) x s.(data_buffer) s.(gc_fun) s.(use_stack) s.(use_store) s.(use_alloc) s.(clock) s.(code) s.(ffi) s.(ffi_save_regs) s.(be).
Definition set_data_buffer x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(store) s.(stack) s.(stack_space) s.(memory) s.(mdomain) s.(sh_mdomain) s.(bitmaps) s.(compile) s.(compile_oracle) s.(code_buffer) x s.(gc_fun) s.(use_stack) s.(use_store) s.(use_alloc) s.(clock) s.(code) s.(ffi) s.(ffi_save_regs) s.(be).
Definition set_gc_fun x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(store) s.(stack) s.(stack_space) s.(memory) s.(mdomain) s.(sh_mdomain) s.(bitmaps) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) x s.(use_stack) s.(use_store) s.(use_alloc) s.(clock) s.(code) s.(ffi) s.(ffi_save_regs) s.(be).
Definition set_use_stack x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(store) s.(stack) s.(stack_space) s.(memory) s.(mdomain) s.(sh_mdomain) s.(bitmaps) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) x s.(use_store) s.(use_alloc) s.(clock) s.(code) s.(ffi) s.(ffi_save_regs) s.(be).
Definition set_use_store x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(store) s.(stack) s.(stack_space) s.(memory) s.(mdomain) s.(sh_mdomain) s.(bitmaps) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(use_stack) x s.(use_alloc) s.(clock) s.(code) s.(ffi) s.(ffi_save_regs) s.(be).
Definition set_use_alloc x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(store) s.(stack) s.(stack_space) s.(memory) s.(mdomain) s.(sh_mdomain) s.(bitmaps) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(use_stack) s.(use_store) x s.(clock) s.(code) s.(ffi) s.(ffi_save_regs) s.(be).
Definition set_clock x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(store) s.(stack) s.(stack_space) s.(memory) s.(mdomain) s.(sh_mdomain) s.(bitmaps) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(use_stack) s.(use_store) s.(use_alloc) x s.(code) s.(ffi) s.(ffi_save_regs) s.(be).
Definition set_code x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(store) s.(stack) s.(stack_space) s.(memory) s.(mdomain) s.(sh_mdomain) s.(bitmaps) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(use_stack) s.(use_store) s.(use_alloc) s.(clock) x s.(ffi) s.(ffi_save_regs) s.(be).
Definition set_ffi x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(store) s.(stack) s.(stack_space) s.(memory) s.(mdomain) s.(sh_mdomain) s.(bitmaps) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(use_stack) s.(use_store) s.(use_alloc) s.(clock) s.(code) x s.(ffi_save_regs) s.(be).
Definition set_ffi_save_regs x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(store) s.(stack) s.(stack_space) s.(memory) s.(mdomain) s.(sh_mdomain) s.(bitmaps) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(use_stack) s.(use_store) s.(use_alloc) s.(clock) s.(code) s.(ffi) x s.(be).
Definition set_be x (s : state a c ffi_t) : state a c ffi_t := mk_state s.(regs) s.(fp_regs) s.(store) s.(stack) s.(stack_space) s.(memory) s.(mdomain) s.(sh_mdomain) s.(bitmaps) s.(compile) s.(compile_oracle) s.(code_buffer) s.(data_buffer) s.(gc_fun) s.(use_stack) s.(use_store) s.(use_alloc) s.(clock) s.(code) s.(ffi) s.(ffi_save_regs) x.
End Updates.

Section Ops.
Context {a : N} {c ffi_t : Type}.
Local Open Scope word_scope.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "mem_store_def" *)
Definition mem_store (addr : word a) (w : word_loc a) (s : state a c ffi_t) : option (state a c ffi_t) :=
  if classical_dec (addr IN mdomain s) then SOME (set_memory ((addr =+ w) (memory s)) s)
  else NONE.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "mem_load_def" *)
Definition mem_load (addr : word a) (s : state a c ffi_t) : option (word_loc a) :=
  if classical_dec (addr IN mdomain s) then SOME (memory s addr) else NONE.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "dec_clock_def" *)
Definition dec_clock (s : state a c ffi_t) : state a c ffi_t := set_clock (clock s - 1) s.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "word_exp_def" *)
Fixpoint word_exp (s : state a c ffi_t) (e : wordLang.exp a) {struct e} : option (word a) :=
  match e with
  | wordLang.Const w => SOME w
  | wordLang.Var v =>
      match FLOOKUP (regs s) v with
      | SOME (Word w) => SOME w
      | _ => NONE
      end
  | wordLang.Lookup name =>
      match FLOOKUP (store s) name with
      | SOME (Word w) => SOME w
      | _ => NONE
      end
  | wordLang.Load addr =>
      match word_exp s addr with
      | SOME w =>
          match mem_load w s with
          | SOME (Word w) => SOME w
          | _ => NONE
          end
      | _ => NONE
      end
  | wordLang.Op op wexps =>
      let ws := MAP (word_exp s) wexps in
      if EVERY IS_SOME ws then wordLang.word_op op (MAP THE ws) else NONE
  | wordLang.Shift sh wexp wexp1 =>
      match word_exp s wexp, word_exp s wexp1 with
      | SOME w, SOME w1 => wordLang.word_sh sh w (w2n w1)
      | _, _ => NONE
      end
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "get_var_def" *)
Definition get_var (v : N) (s : state a c ffi_t) : option (word_loc a) := FLOOKUP (regs s) v.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "get_vars_def" *)
Fixpoint get_vars (vs : list N) (s : state a c ffi_t) : option (list (word_loc a)) :=
  match vs with
  | [] => SOME []
  | v :: vs =>
      match get_var v s with
      | NONE => NONE
      | SOME x =>
          match get_vars vs s with
          | NONE => NONE
          | SOME xs => SOME (x :: xs)
          end
      end
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "get_fp_var_def" *)
Definition get_fp_var (v : N) (s : state a c ffi_t) : option word64 := FLOOKUP (fp_regs s) v.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "set_var_def" *)
Definition set_var (v : N) (x : word_loc a) (s : state a c ffi_t) : state a c ffi_t :=
  set_regs (regs s |+ (v, x)) s.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "set_fp_var_def" *)
Definition set_fp_var (v : N) (x : word64) (s : state a c ffi_t) : state a c ffi_t :=
  set_fp_regs (fp_regs s |+ (v, x)) s.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "set_store_def" *)
Definition set_store (v : store_name) (x : word_loc a) (s : state a c ffi_t) : state a c ffi_t :=
  set_store_fld (store s |+ (v, x)) s.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "empty_env_def" *)
Definition empty_env (s : state a c ffi_t) : state a c ffi_t := set_stack [] (set_regs FEMPTY s).

(** HOL names the address argument of the shared-memory operations [a]; it
    is [ad] here ([a] is the word-width index). *)

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "sh_mem_store_def" *)
Definition sh_mem_store (r : N) (ad : word a) (s : state a c ffi_t)
    : option (result a) * state a c ffi_t :=
  match get_var r s with
  | SOME (Word w) =>
      if classical_dec (ad IN sh_mdomain s) then
        match call_FFI (ffi s) (SharedMem MappedWrite) [n2w 0 : word8]
                (word_to_bytes w false ++ word_to_bytes ad false) with
        | FFI_final outcome => (SOME (FinalFFI outcome), s)
        | FFI_return new_ffi new_bytes => (NONE, set_ffi new_ffi s)
        end
      else (SOME Error, s)
  | _ => (SOME Error, s)
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "sh_mem_load_def" *)
Definition sh_mem_load (r : N) (ad : word a) (s : state a c ffi_t)
    : option (result a) * state a c ffi_t :=
  if classical_dec (ad IN sh_mdomain s) then
    match call_FFI (ffi s) (SharedMem MappedRead) [n2w 0 : word8] (word_to_bytes ad false) with
    | FFI_final outcome => (SOME (FinalFFI outcome), s)
    | FFI_return new_ffi new_bytes =>
        (NONE, set_ffi new_ffi (set_regs (regs s |+ (r, Word (word_of_bytes false (n2w 0) new_bytes))) s))
    end
  else (SOME Error, s).

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "sh_mem_store_byte_def" *)
Definition sh_mem_store_byte (r : N) (ad : word a) (s : state a c ffi_t)
    : option (result a) * state a c ffi_t :=
  match get_var r s with
  | SOME (Word w) =>
      if classical_dec (byte_align ad IN sh_mdomain s) then
        match call_FFI (ffi s) (SharedMem MappedWrite) [n2w 1 : word8]
                ([get_byte (n2w 0) w false] ++ word_to_bytes ad false) with
        | FFI_final outcome => (SOME (FinalFFI outcome), s)
        | FFI_return new_ffi new_bytes => (NONE, set_ffi new_ffi s)
        end
      else (SOME Error, s)
  | _ => (SOME Error, s)
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "sh_mem_store16_def" *)
Definition sh_mem_store16 (r : N) (ad : word a) (s : state a c ffi_t)
    : option (result a) * state a c ffi_t :=
  match get_var r s with
  | SOME (Word w) =>
      if classical_dec (byte_align ad IN sh_mdomain s) then
        match call_FFI (ffi s) (SharedMem MappedWrite) [n2w 2 : word8]
                (TAKE 2 (word_to_bytes w false) ++ word_to_bytes ad false) with
        | FFI_final outcome => (SOME (FinalFFI outcome), s)
        | FFI_return new_ffi new_bytes => (NONE, set_ffi new_ffi s)
        end
      else (SOME Error, s)
  | _ => (SOME Error, s)
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "sh_mem_store32_def" *)
Definition sh_mem_store32 (r : N) (ad : word a) (s : state a c ffi_t)
    : option (result a) * state a c ffi_t :=
  match get_var r s with
  | SOME (Word w) =>
      if classical_dec (byte_align ad IN sh_mdomain s) then
        match call_FFI (ffi s) (SharedMem MappedWrite) [n2w 4 : word8]
                (TAKE 4 (word_to_bytes w false) ++ word_to_bytes ad false) with
        | FFI_final outcome => (SOME (FinalFFI outcome), s)
        | FFI_return new_ffi new_bytes => (NONE, set_ffi new_ffi s)
        end
      else (SOME Error, s)
  | _ => (SOME Error, s)
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "sh_mem_load_byte_def" *)
Definition sh_mem_load_byte (r : N) (ad : word a) (s : state a c ffi_t)
    : option (result a) * state a c ffi_t :=
  if classical_dec (byte_align ad IN sh_mdomain s) then
    match call_FFI (ffi s) (SharedMem MappedRead) [n2w 1 : word8] (word_to_bytes ad false) with
    | FFI_final outcome => (SOME (FinalFFI outcome), s)
    | FFI_return new_ffi new_bytes =>
        (NONE, set_ffi new_ffi (set_regs (regs s |+ (r, Word (word_of_bytes false (n2w 0) new_bytes))) s))
    end
  else (SOME Error, s).

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "sh_mem_load16_def" *)
Definition sh_mem_load16 (r : N) (ad : word a) (s : state a c ffi_t)
    : option (result a) * state a c ffi_t :=
  if classical_dec (byte_align ad IN sh_mdomain s) then
    match call_FFI (ffi s) (SharedMem MappedRead) [n2w 2 : word8] (word_to_bytes ad false) with
    | FFI_final outcome => (SOME (FinalFFI outcome), s)
    | FFI_return new_ffi new_bytes =>
        (NONE, set_ffi new_ffi (set_regs (regs s |+ (r, Word (word_of_bytes false (n2w 0) new_bytes))) s))
    end
  else (SOME Error, s).

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "sh_mem_load32_def" *)
Definition sh_mem_load32 (r : N) (ad : word a) (s : state a c ffi_t)
    : option (result a) * state a c ffi_t :=
  if classical_dec (byte_align ad IN sh_mdomain s) then
    match call_FFI (ffi s) (SharedMem MappedRead) [n2w 4 : word8] (word_to_bytes ad false) with
    | FFI_final outcome => (SOME (FinalFFI outcome), s)
    | FFI_return new_ffi new_bytes =>
        (NONE, set_ffi new_ffi (set_regs (regs s |+ (r, Word (word_of_bytes false (n2w 0) new_bytes))) s))
    end
  else (SOME Error, s).

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "sh_mem_op_def" *)
Definition sh_mem_op (op : memop) (r : N) (ad : word a) (s : state a c ffi_t)
    : option (result a) * state a c ffi_t :=
  match op with
  | Load => sh_mem_load r ad s
  | Store => sh_mem_store r ad s
  | Load8 => sh_mem_load_byte r ad s
  | Store8 => sh_mem_store_byte r ad s
  | Load16 => sh_mem_load16 r ad s
  | Store16 => sh_mem_store16 r ad s
  | Load32 => sh_mem_load32 r ad s
  | Store32 => sh_mem_store32 r ad s
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "full_read_bitmap_def" *)
Definition full_read_bitmap (bitmaps0 : list (word a)) (x : word_loc a) : option (list bool) :=
  match x with
  | Word w =>
      if bool_decide (w = n2w 0) then NONE
      else read_bitmap (DROP (w2n (w - n2w 1)) bitmaps0)
  | _ => NONE
  end.

End Ops.

(** ** Stack encoding for the garbage collector

    [enc_stack]/[dec_stack] recurse (in HOL, well-founded on the stack
    length) on the stack remaining after a frame; they are computed with a
    fuel above that length. *)

Section EncDec.
Context {a : N}.
Local Open Scope word_scope.

Fixpoint enc_stack_f (n : nat) (bitmaps0 : list (word a)) (l : list (word_loc a))
    : option (list (word_loc a)) :=
  match n with
  | O => NONE
  | Datatypes.S n' =>
      match l with
      | [] => NONE
      | w :: ws =>
          if bool_decide (w = Word (n2w 0)) then (if bool_decide (ws = []) then SOME [] else NONE)
          else
            match full_read_bitmap bitmaps0 w with
            | NONE => NONE
            | SOME bs =>
                match filter_bitmap bs ws with
                | NONE => NONE
                | SOME (ts, ws') =>
                    match enc_stack_f n' bitmaps0 ws' with
                    | NONE => NONE
                    | SOME rs => SOME (ts ++ rs)
                    end
                end
            end
      end
  end.

Definition enc_stack (bitmaps0 : list (word a)) (l : list (word_loc a)) : option (list (word_loc a)) :=
  enc_stack_f (Datatypes.S (length l)) bitmaps0 l.

Lemma enc_stack_f_fuel : forall n1 n2 bitmaps0 l,
  (length l < n1)%nat -> (length l < n2)%nat ->
  enc_stack_f n1 bitmaps0 l = enc_stack_f n2 bitmaps0 l.
Proof.
  induction n1 as [|n1 IH]; intros n2 bitmaps0 l H1 H2; [lia|].
  destruct n2 as [|n2]; [lia|].
  destruct l as [|w ws]; cbn [enc_stack_f]; [reflexivity|].
  destruct (bool_decide _); [reflexivity|].
  destruct (full_read_bitmap bitmaps0 w) as [bs|]; [|reflexivity].
  destruct (filter_bitmap bs ws) as [[ts ws']|] eqn:E; [|reflexivity].
  apply filter_bitmap_LENGTH in E. rewrite !LENGTH_length in E.
  cbn [length] in *. rewrite (IH n2) by lia. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "enc_stack_def" *)
Theorem enc_stack_def :
  (forall bitmaps0, enc_stack bitmaps0 [] = NONE) /\
  (forall bitmaps0 w ws,
     enc_stack bitmaps0 (w :: ws) =
     if bool_decide (w = Word (n2w 0)) then (if bool_decide (ws = []) then SOME [] else NONE)
     else
       match full_read_bitmap bitmaps0 w with
       | NONE => NONE
       | SOME bs =>
           match filter_bitmap bs ws with
           | NONE => NONE
           | SOME (ts, ws') =>
               match enc_stack bitmaps0 ws' with
               | NONE => NONE
               | SOME rs => SOME (ts ++ rs)
               end
           end
       end).
Proof.
  split; [reflexivity|]. intros bitmaps0 w ws.
  unfold enc_stack at 1; cbn [enc_stack_f].
  destruct (bool_decide _); [reflexivity|].
  destruct (full_read_bitmap bitmaps0 w) as [bs|]; [|reflexivity].
  destruct (filter_bitmap bs ws) as [[ts ws']|] eqn:E; [|reflexivity].
  apply filter_bitmap_LENGTH in E. rewrite !LENGTH_length in E.
  unfold enc_stack. rewrite (enc_stack_f_fuel (length (w :: ws)) (Datatypes.S (length ws'))) by (cbn; lia).
  reflexivity.
Qed.

Fixpoint dec_stack_f (n : nat) (bitmaps0 : list (word a)) (ts l : list (word_loc a))
    : option (list (word_loc a)) :=
  match n with
  | O => NONE
  | Datatypes.S n' =>
      match l with
      | [] => NONE
      | w :: ws =>
          if bool_decide (w = Word (n2w 0)) then
            (if andb (bool_decide (ts = [])) (bool_decide (ws = [])) then SOME [Word (n2w 0)] else NONE)
          else
            match full_read_bitmap bitmaps0 w with
            | NONE => NONE
            | SOME bs =>
                match map_bitmap bs ts ws with
                | NONE => NONE
                | SOME (hd, (ts', ws')) =>
                    match dec_stack_f n' bitmaps0 ts' ws' with
                    | NONE => NONE
                    | SOME rest => SOME (([w] ++ hd) ++ rest)
                    end
                end
            end
      end
  end.

Definition dec_stack (bitmaps0 : list (word a)) (ts l : list (word_loc a)) : option (list (word_loc a)) :=
  dec_stack_f (Datatypes.S (length l)) bitmaps0 ts l.

Lemma dec_stack_f_fuel : forall n1 n2 bitmaps0 ts l,
  (length l < n1)%nat -> (length l < n2)%nat ->
  dec_stack_f n1 bitmaps0 ts l = dec_stack_f n2 bitmaps0 ts l.
Proof.
  induction n1 as [|n1 IH]; intros n2 bitmaps0 ts l H1 H2; [lia|].
  destruct n2 as [|n2]; [lia|].
  destruct l as [|w ws]; cbn [dec_stack_f]; [reflexivity|].
  destruct (bool_decide _); [reflexivity|].
  destruct (full_read_bitmap bitmaps0 w) as [bs|]; [|reflexivity].
  destruct (map_bitmap bs ts ws) as [[hd [ts' ws']]|] eqn:E; [|reflexivity].
  apply map_bitmap_LENGTH in E. rewrite !LENGTH_length in E.
  cbn [length] in *. rewrite (IH n2) by lia. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "dec_stack_def" *)
Theorem dec_stack_def :
  (forall bitmaps0 ts, dec_stack bitmaps0 ts [] = NONE) /\
  (forall bitmaps0 ts w ws,
     dec_stack bitmaps0 ts (w :: ws) =
     if bool_decide (w = Word (n2w 0)) then
       (if andb (bool_decide (ts = [])) (bool_decide (ws = [])) then SOME [Word (n2w 0)] else NONE)
     else
       match full_read_bitmap bitmaps0 w with
       | NONE => NONE
       | SOME bs =>
           match map_bitmap bs ts ws with
           | NONE => NONE
           | SOME (hd, (ts', ws')) =>
               match dec_stack bitmaps0 ts' ws' with
               | NONE => NONE
               | SOME rest => SOME (([w] ++ hd) ++ rest)
               end
           end
       end).
Proof.
  split; [reflexivity|]. intros bitmaps0 ts w ws.
  unfold dec_stack at 1; cbn [dec_stack_f].
  destruct (bool_decide _); [reflexivity|].
  destruct (full_read_bitmap bitmaps0 w) as [bs|]; [|reflexivity].
  destruct (map_bitmap bs ts ws) as [[hd [ts' ws']]|] eqn:E; [|reflexivity].
  apply map_bitmap_LENGTH in E. rewrite !LENGTH_length in E.
  unfold dec_stack. rewrite (dec_stack_f_fuel (length (w :: ws)) (Datatypes.S (length ws'))) by (cbn; lia).
  reflexivity.
Qed.

End EncDec.

Section Gc.
Context {a : N} {c ffi_t : Type}.
Local Open Scope word_scope.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "gc_def" *)
Definition gc (s : state a c ffi_t) : option (state a c ffi_t) :=
  if LENGTH (stack s) <? stack_space s then NONE
  else
    let unused := TAKE (stack_space s) (stack s) in
    let stack0 := DROP (stack_space s) (stack s) in
    match enc_stack (bitmaps s) (DROP (stack_space s) (stack s)) with
    | NONE => NONE
    | SOME wl_list =>
        match gc_fun s (wl_list, (memory s, (mdomain s, store s))) with
        | NONE => NONE
        | SOME (wl, (m, st)) =>
            match dec_stack (bitmaps s) wl stack0 with
            | NONE => NONE
            | SOME stack1 =>
                SOME (set_memory m (set_regs FEMPTY (set_store_fld st (set_stack (unused ++ stack1) s))))
            end
        end
    end.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "has_space_def" *)
Definition has_space (wl : word_loc a) (store0 : fmap store_name (word_loc a)) : option bool :=
  match wl, FLOOKUP store0 NextFree, FLOOKUP store0 TriggerGC with
  | Word w, SOME (Word n), SOME (Word l) => SOME (w2n w <=? w2n (l - n))
  | _, _, _ => NONE
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "alloc_def" *)
Definition alloc (w : word a) (s : state a c ffi_t) : option (result a) * state a c ffi_t :=
  match gc (set_store AllocSize (Word w) s) with
  | NONE => (SOME Error, s)
  | SOME s =>
      match FLOOKUP (store s) AllocSize with
      | NONE => (SOME Error, s)
      | SOME w =>
          match has_space w (store s) with
          | NONE => (SOME Error, s)
          | SOME true => (NONE, s)
          | SOME false => (SOME (Halt (Word (n2w 1))), empty_env s)
          end
      end
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "assign_def" *)
Definition assign (reg0 : N) (exp0 : wordLang.exp a) (s : state a c ffi_t) : option (state a c ffi_t) :=
  match word_exp s exp0 with
  | NONE => NONE
  | SOME w => SOME (set_var reg0 (Word w) s)
  end.

End Gc.

Section Inst.
Context {a : N} {c ffi_t : Type}.
Local Open Scope word_scope.

(** HOL's address register in [Addr a w] is named [ad] here ([a] is the
    word-width index).  HOL's final catch-all [| _ => NONE] is redundant
    (all instruction shapes are listed) and is omitted. *)
(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "inst_def" *)
Definition inst (i : asm.inst a) (s : state a c ffi_t) : option (state a c ffi_t) :=
  match i with
  | asm.Skip => SOME s
  | asm.Const reg0 w => assign reg0 (wordLang.Const w) s
  | Arith (Binop bop r1 r2 ri) =>
      if andb (bool_decide (bop = asm.Or)) (bool_decide (ri = Reg r2)) then
        match FLOOKUP (regs s) r2 with
        | NONE => NONE
        | SOME w => SOME (set_var r1 w s)
        end
      else
        assign r1
          (wordLang.Op bop [wordLang.Var r2; match ri with Reg r3 => wordLang.Var r3
                                                         | Imm w => wordLang.Const w end]) s
  | Arith (Shift sh r1 r2 ri) =>
      assign r1
        (wordLang.Shift sh (wordLang.Var r2) (match ri with Reg r3 => wordLang.Var r3
                                                        | Imm w => wordLang.Const w end)) s
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
          let res := (w2n l + w2n r + (if bool_decide (c0 = (n2w 0 : word a)) then 0 else 1))%N in
          SOME (set_var r4 (Word (if (dimword a <=? res)%N then (n2w 1 : word a) else n2w 0))
                  (set_var r1 (Word (n2w res)) s))
      | _ => NONE
      end
  | Arith (AddOverflow r1 r2 r3 r4) =>
      let vs := get_vars [r2; r3] s in
      match vs with
      | SOME [Word w2; Word w3] =>
          SOME (set_var r4 (Word (if negb (Z.eqb (w2i (w2 + w3)) (w2i w2 + w2i w3)%Z)
                                  then n2w 1 else n2w 0))
                  (set_var r1 (Word (w2 + w3)) s))
      | _ => NONE
      end
  | Arith (SubOverflow r1 r2 r3 r4) =>
      let vs := get_vars [r2; r3] s in
      match vs with
      | SOME [Word w2; Word w3] =>
          SOME (set_var r4 (Word (if negb (Z.eqb (w2i (w2 - w3)) (w2i w2 - w2i w3)%Z)
                                  then n2w 1 else n2w 0))
                  (set_var r1 (Word (w2 - w3)) s))
      | _ => NONE
      end
  | Arith (LongMul r1 r2 r3 r4) =>
      let vs := get_vars [r3; r4] s in
      match vs with
      | SOME [Word w3; Word w4] =>
          let r := (w2n w3 * w2n w4)%N in
          SOME (set_var r2 (Word (n2w r)) (set_var r1 (Word (n2w (r DIV dimword a))) s))
      | _ => NONE
      end
  | Arith (LongDiv r1 r2 r3 r4 r5) =>
      let vs := get_vars [r3; r4; r5] s in
      match vs with
      | SOME [Word w3; Word w4; Word w5] =>
          let n := (w2n w3 * dimword a + w2n w4)%N in
          let d := w2n w5 in
          let q := (n DIV d)%N in
          if andb (negb (d =? 0)%N) (q <? dimword a)%N then
            SOME (set_var r1 (Word (n2w q)) (set_var r2 (Word (n2w (n MOD d))) s))
          else NONE
      | _ => NONE
      end
  | Mem Load r (Addr ad w) =>
      match word_exp s (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w]) with
      | NONE => NONE
      | SOME w =>
          match mem_load w s with
          | NONE => NONE
          | SOME w => SOME (set_var r w s)
          end
      end
  | Mem Load8 r (Addr ad w) =>
      match word_exp s (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w]) with
      | SOME w =>
          match mem_load_byte_aux (memory s) (mdomain s) (be s) w with
          | NONE => NONE
          | SOME w => SOME (set_var r (Word (w2w w)) s)
          end
      | _ => NONE
      end
  | Mem Load16 _ _ => NONE
  | Mem Load32 r (Addr ad w) =>
      match word_exp s (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w]) with
      | SOME w =>
          match mem_load_32 (memory s) (mdomain s) (be s) w with
          | NONE => NONE
          | SOME w => SOME (set_var r (Word (w2w w)) s)
          end
      | _ => NONE
      end
  | Mem Store r (Addr ad w) =>
      match word_exp s (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w]), get_var r s with
      | SOME ad, SOME w =>
          match mem_store ad w s with
          | SOME s1 => SOME s1
          | NONE => NONE
          end
      | _, _ => NONE
      end
  | Mem Store8 r (Addr ad w) =>
      match word_exp s (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w]), get_var r s with
      | SOME ad, SOME (Word w) =>
          match mem_store_byte_aux (memory s) (mdomain s) (be s) ad (w2w w) with
          | SOME new_m => SOME (set_memory new_m s)
          | NONE => NONE
          end
      | _, _ => NONE
      end
  | Mem Store16 _ _ => NONE
  | Mem Store32 r (Addr ad w) =>
      match word_exp s (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w]), get_var r s with
      | SOME ad, SOME (Word w) =>
          match mem_store_32 (memory s) (mdomain s) (be s) ad (w2w w) with
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
          SOME (set_fp_var d1 (fpSem.fpfma f1 f2 f3) s)
      | _, _, _ => NONE
      end
  | FP (FPMovToReg r1 r2 d) =>
      match get_fp_var d s with
      | SOME v =>
          if (dimindex a =? 64)%N then SOME (set_var r1 (Word (w2w v)) s)
          else SOME (set_var r2 (Word ((63 >< 32) v)) (set_var r1 (Word ((31 >< 0) v)) s))
      | _ => NONE
      end
  | FP (FPMovFromReg d r1 r2) =>
      if (dimindex a =? 64)%N then
        match get_var r1 s with
        | SOME (Word w1) => SOME (set_fp_var d (w2w w1) s)
        | _ => NONE
        end
      else
        match get_var r1 s, get_var r2 s with
        | SOME (Word w1), SOME (Word w2) => SOME (set_fp_var d (w2 @@ w1) s)
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
              if Z.eqb (w2i w) i then
                (if (dimindex a =? 64)%N then SOME (set_fp_var d1 (w2w w) s)
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
      if (dimindex a =? 64)%N then
        match get_fp_var d2 s with
        | SOME f =>
            let i := w2i ((31 >< 0) f : word32) in
            SOME (set_fp_var d1 (int_to_fp64 roundTiesToEven i) s)
        | NONE => NONE
        end
      else
        match get_fp_var (d2 DIV 2) s with
        | SOME v =>
            let i := w2i (if ODD d2 then (63 >< 32) v else (31 >< 0) v : word a) in
            SOME (set_fp_var d1 (int_to_fp64 roundTiesToEven i) s)
        | NONE => NONE
        end
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "get_var_imm_def" *)
Definition get_var_imm (ri : reg_imm a) (s : state a c ffi_t) : option (word_loc a) :=
  match ri with
  | Reg n => get_var n s
  | Imm w => SOME (Word w)
  end.

End Inst.

Section Code.
Context {a : N} {c ffi_t : Type}.
Local Open Scope word_scope.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "find_code_def" *)
Definition find_code (dest : N + N) (regs0 : fmap N (word_loc a)) (code0 : sptree.spt (prog a))
    : option (prog a) :=
  match dest with
  | inl p => sptree.lookup p code0
  | inr r =>
      match FLOOKUP regs0 r with
      | SOME (Loc loc n) => if (n =? 0)%N then sptree.lookup loc code0 else NONE
      | _ => NONE
      end
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "fix_clock_def" *)
Definition fix_clock {R} (s : state a c ffi_t) (p : R * state a c ffi_t) : R * state a c ffi_t :=
  let '(res, s1) := p in (res, set_clock (MIN (clock s) (clock s1)) s1).

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "fix_clock_IMP" *)
Theorem fix_clock_IMP : forall {R} (s : state a c ffi_t) (x : R * state a c ffi_t) res s1,
  fix_clock s x = (res, s1) -> (clock s1 <= clock s)%N.
Proof.
  intros R s [r s'] res s1 H; cbn in H; inversion H; subst; cbn.
  unfold MIN; destruct (N.ltb_spec (clock s) (clock s')); lia.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "STOP_def" *)
Definition STOP {A} (x : A) : A := x.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "get_labels_def" *)
Fixpoint get_labels (p : prog a) : N * N -> Prop :=
  match p with
  | Seq p1 p2 => get_labels p1 UNION get_labels p2
  | If _ _ _ p1 p2 => get_labels p1 UNION get_labels p2
  | Loop p => get_labels p
  | Call ret _ handler =>
      match ret with
      | NONE => EMPTY
      | SOME (r, (_, (l1, l2))) =>
          (l1, l2) INSERT (get_labels r UNION
            match handler with
            | NONE => EMPTY
            | SOME (r, (l1, l2)) => (l1, l2) INSERT get_labels r
            end)
      end
  | stackLang.Halt _ => EMPTY
  | _ => EMPTY
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "loc_check_def" *)
Definition loc_check (code0 : sptree.spt (prog a)) (l : N * N) : Prop :=
  let '(l1, l2) := l in
  (l2 = 0 /\ l1 IN sptree.domain code0) \/
  exists n e, sptree.lookup n code0 = SOME e /\ (l1, l2) IN get_labels e.

(** HOL [copy_words_for_pattern] recurses on [pattern >>> 1] (well-founded,
    HOL's automatic termination proof); here with a fuel above the bit size
    of the pattern. *)
Fixpoint copy_words_for_pattern_f (n : nat) (pattern : word a) (i : N) (ad off : word a)
    (bs : list (word a)) (dm : word a -> Prop) (m : word a -> word_loc a)
    : option (N * (word a * (word a -> word_loc a))) :=
  match n with
  | O => NONE
  | Datatypes.S n' =>
      if bool_decide (pattern = n2w 0) then NONE else
      if bool_decide (pattern = n2w 1) then SOME (i, (ad, m)) else
        if andb ⌜ad IN dm⌝ (i <? LENGTH bs) then
          let b := pattern ' 0 in
          let w := EL i bs in
          let m := (ad =+ Word (if b then w + off else w)) m in
          copy_words_for_pattern_f n' (pattern >>> 1) (i + 1) (ad + bytes_in_word) off bs dm m
        else NONE
  end.

Definition copy_words_for_pattern (pattern : word a) (i : N) (ad off : word a)
    (bs : list (word a)) (dm : word a -> Prop) (m : word a -> word_loc a)
    : option (N * (word a * (word a -> word_loc a))) :=
  copy_words_for_pattern_f (Datatypes.S (N.to_nat (N.size (w2n pattern)))) pattern i ad off bs dm m.

Lemma copy_words_for_pattern_f_fuel : forall n1 n2 p i ad off bs dm m,
  (N.to_nat (N.size (w2n p)) < n1)%nat -> (N.to_nat (N.size (w2n p)) < n2)%nat ->
  copy_words_for_pattern_f n1 p i ad off bs dm m = copy_words_for_pattern_f n2 p i ad off bs dm m.
Proof.
  induction n1 as [|n1 IH]; intros n2 p i ad off bs dm m H1 H2; [lia|].
  destruct n2 as [|n2]; [lia|]. cbn [copy_words_for_pattern_f].
  destruct (bool_decide (p = n2w 0)) eqn:Hp; [reflexivity|]. apply bool_decide_false in Hp.
  destruct (bool_decide (p = n2w 1)); [reflexivity|].
  destruct (andb _ _); [|reflexivity].
  pose proof (size_lsr1 p Hp) as Hs.
  apply IH; lia.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "copy_words_for_pattern_def" *)
Theorem copy_words_for_pattern_def : forall (pattern : word a) (i : N) (ad off : word a)
    (bs : list (word a)) (dm : word a -> Prop) (m : word a -> word_loc a),
  copy_words_for_pattern pattern i ad off bs dm m =
  if bool_decide (pattern = n2w 0) then NONE else
  if bool_decide (pattern = n2w 1) then SOME (i, (ad, m)) else
    if andb ⌜ad IN dm⌝ (i <? LENGTH bs) then
      let b := pattern ' 0 in
      let w := EL i bs in
      let m := (ad =+ Word (if b then w + off else w)) m in
      copy_words_for_pattern (pattern >>> 1) (i + 1) (ad + bytes_in_word) off bs dm m
    else NONE.
Proof.
  intros. unfold copy_words_for_pattern at 1; cbn [copy_words_for_pattern_f].
  destruct (bool_decide (pattern = n2w 0)) eqn:Hp; [reflexivity|]. apply bool_decide_false in Hp.
  destruct (bool_decide (pattern = n2w 1)); [reflexivity|].
  destruct (andb _ _); [|reflexivity].
  pose proof (size_lsr1 pattern Hp) as Hs.
  unfold copy_words_for_pattern. apply copy_words_for_pattern_f_fuel; lia.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "copy_words_for_pattern_LESS_EQ" *)
Theorem copy_words_for_pattern_LESS_EQ : forall p i ad f bs dm m j a1,
  copy_words_for_pattern p i ad f bs dm m = SOME (j, a1) -> (i <= j)%N.
Proof.
  enough (G : forall n p i ad f bs dm m j a1,
             copy_words_for_pattern_f n p i ad f bs dm m = SOME (j, a1) -> (i <= j)%N)
    by (intros; eapply G; eassumption).
  induction n as [|n IH]; intros p i ad f bs dm m j a1 H; cbn [copy_words_for_pattern_f] in H;
    [discriminate|].
  destruct (bool_decide (p = n2w 0)); [discriminate|].
  destruct (bool_decide (p = n2w 1)); [injection H as <- _; lia|].
  destruct (andb _ _); [|discriminate].
  apply IH in H; lia.
Qed.

(** HOL [copy_words]: well-founded on [LENGTH bs - i]; computed with that
    fuel. *)
Fixpoint copy_words_f (n : nat) (i : N) (ad off : word a) (bs : list (word a))
    (dm : word a -> Prop) (m : word a -> word_loc a) : option (word a * (word a -> word_loc a)) :=
  match n with
  | O => NONE
  | Datatypes.S n' =>
      if LENGTH bs <=? i then NONE
      else
        let pattern := EL i bs in
        match copy_words_for_pattern pattern (i + 1) ad off bs dm m with
        | NONE => NONE
        | SOME (i1, (a1, m1)) =>
            if word_msb pattern then copy_words_f n' i1 a1 off bs dm m1 else SOME (a1, m1)
        end
  end.

Definition copy_words (i : N) (ad off : word a) (bs : list (word a)) (dm : word a -> Prop)
    (m : word a -> word_loc a) : option (word a * (word a -> word_loc a)) :=
  copy_words_f (Datatypes.S (N.to_nat (LENGTH bs - i))) i ad off bs dm m.

Lemma copy_words_f_fuel : forall n1 n2 i ad off bs dm m,
  (N.to_nat (LENGTH bs - i) < n1)%nat -> (N.to_nat (LENGTH bs - i) < n2)%nat ->
  copy_words_f n1 i ad off bs dm m = copy_words_f n2 i ad off bs dm m.
Proof.
  induction n1 as [|n1 IH]; intros n2 i ad off bs dm m H1 H2; [lia|].
  destruct n2 as [|n2]; [lia|]. cbn [copy_words_f].
  destruct (N.leb_spec (LENGTH bs) i); [reflexivity|].
  destruct (copy_words_for_pattern _ _ _ _ _ _ _) as [[i1 [a1 m1]]|] eqn:E; [|reflexivity].
  apply copy_words_for_pattern_LESS_EQ in E.
  destruct (word_msb _); [|reflexivity].
  apply IH; lia.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "copy_words_def" *)
Theorem copy_words_def : forall (i : N) (ad off : word a) (bs : list (word a))
    (dm : word a -> Prop) (m : word a -> word_loc a),
  copy_words i ad off bs dm m =
  if LENGTH bs <=? i then NONE
  else
    let pattern := EL i bs in
    match copy_words_for_pattern pattern (i + 1) ad off bs dm m with
    | NONE => NONE
    | SOME (i1, (a1, m1)) =>
        if word_msb pattern then copy_words i1 a1 off bs dm m1 else SOME (a1, m1)
    end.
Proof.
  intros. unfold copy_words at 1; cbn [copy_words_f].
  destruct (N.leb_spec (LENGTH bs) i); [reflexivity|].
  destruct (copy_words_for_pattern _ _ _ _ _ _ _) as [[i1 [a1 m1]]|] eqn:E; [|reflexivity].
  apply copy_words_for_pattern_LESS_EQ in E.
  destruct (word_msb _); [|reflexivity].
  unfold copy_words. apply copy_words_f_fuel; lia.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "unset_var_def" *)
Definition unset_var (v : N) (s : state a c ffi_t) : state a c ffi_t :=
  set_regs (regs s \\ v) s.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "store_const_sem_def" *)
Definition store_const_sem (t1 t2 : N) (s : state a c ffi_t) : option (result a) * state a c ffi_t :=
  if negb (ALL_DISTINCT [0; 1; 2; 3; t1; t2]) then (SOME Error, s) else
    match get_var 1 s, get_var 2 s, get_var 3 s with
    | SOME (Word i), SOME (Word ad), SOME (Word off) =>
        match copy_words (w2n i) ad off (bitmaps s) (mdomain s) (memory s) with
        | NONE => (SOME Error, s)
        | SOME (ad, m) =>
            (NONE,
             (if use_alloc s then unset_var 0 else I)
               (set_var t1 (Word (n2w 1)) (set_var t2 (Word (n2w 1))
                  (set_var 1 (Word (n2w 1)) (set_var 2 (Word ad) (set_memory m s))))))
        end
    | _, _, _ => (SOME Error, s)
    end.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "check_store_consts_opt_def" *)
Definition check_store_consts_opt (t1 t2 : N) (stub : option N) (c0 : sptree.spt (prog a)) : bool :=
  match stub with
  | NONE => true
  | SOME n => ⌜sptree.lookup n c0 = SOME (Seq (StoreConsts t1 t2 NONE) (Return 0))⌝
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "dest_Seq_def" *)
Definition dest_Seq (p : prog a) : option (prog a * prog a) :=
  match p with
  | Seq p1 p2 => SOME (p1, p2)
  | _ => NONE
  end.

End Code.

Section Res.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "bad_fun_return_def" *)
Definition bad_fun_return (r : option (result a)) : bool :=
  match r with
  | NONE => true
  | SOME (Break _) => true
  | SOME (Continue _) => true
  | _ => false
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "cont_loop_def" *)
Definition cont_loop (r : option (result a)) : bool :=
  match r with
  | NONE => true
  | SOME (Continue n) => (n =? 0)%N
  | _ => false
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "exit_loop_def" *)
Definition exit_loop (r : option (result a)) : option (result a) :=
  match r with
  | SOME (Break n) => if (n =? 0)%N then NONE else SOME (Break (n - 1))
  | SOME (Continue n) => SOME (Continue (n - 1))
  | res => res
  end.

End Res.

(** ** [evaluate]

    HOL defines [evaluate] by well-founded recursion on
    [(clock, prog_size)].  As in [panSem]: [evaluate_body go lower] is one
    step of HOL's clauses, with [go] for structurally smaller programs at the
    same clock bound and [lower] for calls at a smaller clock;
    [evaluate_c] ties the knot with a clock fuel, and [evaluate_eqn] shows
    that [evaluate] is a fixed point of the step.  HOL's equations are the
    tagged [evaluate_def] theorems below. *)

Section Evaluate.
Context {a : N} {c ffi_t : Type}.
Local Open Scope word_scope.

Definition evaluate_body
    (go lower : prog a -> state a c ffi_t -> option (result a) * state a c ffi_t)
    (p : prog a) (s : state a c ffi_t) : option (result a) * state a c ffi_t :=
  match p with
  | Skip => (NONE, s)
  | stackLang.Halt v =>
      match get_var v s with
      | SOME w => (SOME (Halt w), empty_env s)
      | NONE => (SOME Error, s)
      end
  | Alloc n =>
      if negb (use_alloc s) then (SOME Error, s) else
      match get_var n s with
      | SOME (Word w) => alloc w s
      | _ => (SOME Error, s)
      end
  | StoreConsts t1 t2 stub_opt =>
      if negb (use_store s) then (SOME Error, s) else
      if andb (negb (use_alloc s)) (IS_SOME stub_opt) then (SOME Error, s) else
      if negb (check_store_consts_opt t1 t2 stub_opt (code s)) then (SOME Error, s) else
        store_const_sem t1 t2 s
  | Inst i =>
      match inst i s with
      | SOME s1 => (NONE, s1)
      | NONE => (SOME Error, s)
      end
  | Get v name =>
      if negb (use_store s) then (SOME Error, s) else
      match FLOOKUP (store s) name with
      | SOME x => (NONE, set_var v x s)
      | NONE => (SOME Error, s)
      end
  | Set_ name v =>
      if negb (use_store s) then (SOME Error, s) else
      match get_var v s with
      | SOME w => (NONE, set_store name w s)
      | NONE => (SOME Error, s)
      end
  | OpCurrHeap binop v src =>
      if negb (use_store s) then (SOME Error, s) else
      match word_exp s (wordLang.Op binop [wordLang.Var src; wordLang.Lookup CurrHeap]) with
      | SOME w => (NONE, set_var v (Word w) s)
      | _ => (SOME Error, s)
      end
  | Tick =>
      if (clock s =? 0)%N then (SOME TimeOut, empty_env s) else (NONE, dec_clock s)
  | Seq c1 c2 =>
      let '(res, s1) := fix_clock s (go c1 s) in
      match res with NONE => go c2 s1 | _ => (res, s1) end
  | Return n =>
      match get_var n s with
      | SOME (Loc l1 l2) => (SOME (Result (Loc l1 l2)), s)
      | _ => (SOME Error, s)
      end
  | Raise n =>
      match get_var n s with
      | SOME (Loc l1 l2) => (SOME (Exception (Loc l1 l2)), s)
      | _ => (SOME Error, s)
      end
  | stackLang.Break n => (SOME (Break n), s)
  | stackLang.Continue n => (SOME (Continue n), s)
  | If cmp r1 ri c1 c2 =>
      match get_var r1 s, get_var_imm ri s with
      | SOME x, SOME y =>
          match wordSem.word_cmp cmp x y with
          | SOME true => go c1 s
          | SOME false => go c2 s
          | NONE => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end
  | Loop c1 =>
      let '(res, s1) := fix_clock s (go c1 s) in
      if cont_loop res then
        (if (clock s1 =? 0)%N then (SOME TimeOut, empty_env s1) else
           lower (STOP (Loop c1)) (dec_clock s1))
      else (exit_loop res, s1)
  | JumpLower r1 r2 dest =>
      match get_var r1 s, get_var r2 s with
      | SOME (Word x), SOME (Word y) =>
          if word_cmp Lower x y then
            match find_code (inl dest) (regs s) (code s) with
            | NONE => (SOME Error, s)
            | SOME prog0 =>
                if (clock s =? 0)%N then (SOME TimeOut, empty_env s) else
                  match lower prog0 (dec_clock s) with
                  | (res, s) => if bad_fun_return res then (SOME Error, s) else (res, s)
                  end
            end
          else (NONE, s)
      | _, _ => (SOME Error, s)
      end
  | RawCall dest =>
      match sptree.lookup dest (code s) with
      | NONE => (SOME Error, s)
      | SOME prog0 =>
          match dest_Seq prog0 with
          | SOME (_, body) =>
              if (clock s =? 0)%N then (SOME TimeOut, empty_env s) else
                match lower body (dec_clock s) with
                | (res, s) => if bad_fun_return res then (SOME Error, s) else (res, s)
                end
          | _ => (SOME Error, s)
          end
      end
  | Call ret dest handler =>
      match ret with
      | NONE =>
          match find_code dest (regs s) (code s) with
          | NONE => (SOME Error, s)
          | SOME prog0 =>
              if negb (bool_decide (handler = NONE)) then (SOME Error, s) else
              if (clock s =? 0)%N then (SOME TimeOut, empty_env s) else
                match fix_clock (dec_clock s) (lower prog0 (dec_clock s)) with
                | (res, s) => if bad_fun_return res then (SOME Error, s) else (res, s)
                end
          end
      | SOME (ret_handler, (link_reg, (l1, l2))) =>
          match find_code dest (regs s \\ link_reg) (code s) with
          | NONE => (SOME Error, s)
          | SOME prog0 =>
              if (clock s =? 0)%N then (SOME TimeOut, empty_env s) else
                match fix_clock (dec_clock (set_var link_reg (Loc l1 l2) s))
                        (lower prog0 (dec_clock (set_var link_reg (Loc l1 l2) s))) with
                | (SOME (Result x), s2) =>
                    if negb (bool_decide (x = Loc l1 l2)) then (SOME Error, s2)
                    else lower ret_handler s2
                | (SOME (Exception x), s2) =>
                    match handler with
                    | NONE => (SOME (Exception x), s2)
                    | SOME (h, (l1, l2)) =>
                        if negb (bool_decide (x = Loc l1 l2)) then (SOME Error, s2) else
                          lower h s2
                    end
                | (NONE, s) => (SOME Error, s)
                | (SOME (Break _), s) => (SOME Error, s)
                | (SOME (Continue _), s) => (SOME Error, s)
                | (res, s) => (res, s)
                end
          end
      end
  | Install ptr len dptr dlen ret =>
      match get_var ptr s, get_var len s, get_var dptr s, get_var dlen s with
      | SOME (Word w1), SOME (Word w2), SOME (Word w3), SOME (Word w4) =>
          let '(cfg, (progs, bm)) := compile_oracle s 0 in
          match buffer_flush (code_buffer s) w1 w2,
                (if use_stack s then buffer_flush (data_buffer s) w3 w4
                 else SOME (bm, data_buffer s)) with
          | SOME (bytes, cb), SOME (data, db) =>
              let new_oracle := shift_seq 1 (compile_oracle s) in
              match compile s cfg progs, progs with
              | SOME (bytes', cfg'), (k, prog0) :: _ =>
                  if andb (andb (bool_decide (bytes = bytes')) (bool_decide (data = bm)))
                          ⌜FST (new_oracle 0) = cfg'⌝ then
                    let s' :=
                      set_compile_oracle new_oracle
                        (set_fp_regs FEMPTY
                          (set_regs (DRESTRICT (regs s) (ffi_save_regs s) |+ (ptr, Loc k 0))
                            (set_code (sptree.union (code s) (sptree.fromAList progs))
                              (set_data_buffer db
                                (set_code_buffer cb
                                  (set_bitmaps (bitmaps s ++ bm) s)))))) in
                    (NONE, s')
                  else (SOME Error, s)
              | _, _ => (SOME Error, s)
              end
          | _, _ => (SOME Error, s)
          end
      | _, _, _, _ => (SOME Error, s)
      end
  | ShMemOp op r (Addr ad w) =>
      match word_exp s (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w]) with
      | SOME ad =>
          if (clock s =? 0)%N then (SOME TimeOut, empty_env s) else
            sh_mem_op op r ad (dec_clock s)
      | _ => (SOME Error, s)
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
      if negb (use_stack s) then (SOME Error, s) else
      match get_var r1 s, get_var r2 s with
      | SOME (Word w1), SOME (Word w2) =>
          match buffer_write (data_buffer s) w1 w2 with
          | SOME new_db => (NONE, set_data_buffer new_db s)
          | _ => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end
  | FFI ffi_index ptr len ptr2 len2 ret =>
      match get_var len s, get_var ptr s, get_var len2 s, get_var ptr2 s with
      | SOME (Word w), SOME (Word w2), SOME (Word w3), SOME (Word w4) =>
          match read_bytearray w2 (w2n w) (mem_load_byte_aux (memory s) (mdomain s) (be s)),
                read_bytearray w4 (w2n w3) (mem_load_byte_aux (memory s) (mdomain s) (be s)) with
          | SOME bytes, SOME bytes2 =>
              match call_FFI (ffi s) (ExtCall ffi_index) bytes bytes2 with
              | FFI_final outcome => (SOME (FinalFFI outcome), s)
              | FFI_return new_ffi new_bytes =>
                  let new_m := write_bytearray w4 new_bytes (memory s) (mdomain s) (be s) in
                  (NONE, set_ffi new_ffi (set_fp_regs FEMPTY
                           (set_regs (DRESTRICT (regs s) (ffi_save_regs s)) (set_memory new_m s))))
              end
          | _, _ => (SOME Error, s)
          end
      | _, _, _, _ => (SOME Error, s)
      end
  | LocValue r l1 l2 =>
      if classical_dec (loc_check (code s) (l1, l2)) then (NONE, set_var r (Loc l1 l2) s)
      else (SOME Error, s)
  | StackAlloc n =>
      if negb (use_stack s) then (SOME Error, s) else
      if (stack_space s <? n)%N then (SOME (Halt (Word (n2w 2))), empty_env s) else
        (NONE, set_stack_space (stack_space s - n) s)
  | StackFree n =>
      if negb (use_stack s) then (SOME Error, s) else
      if (LENGTH (stack s) <? stack_space s + n)%N then (SOME Error, empty_env s) else
        (NONE, set_stack_space (stack_space s + n) s)
  | StackLoad r n =>
      if negb (use_stack s) then (SOME Error, s) else
      if (stack_space s + n <? LENGTH (stack s))%N
      then (NONE, set_var r (EL (stack_space s + n) (stack s)) s)
      else (SOME Error, empty_env s)
  | StackLoadAny r rn =>
      if negb (use_stack s) then (SOME Error, s) else
      match get_var rn s with
      | SOME (Word w) =>
          let i := (stack_space s + w2n (w >>> word_shift a))%N in
          if andb (i <? LENGTH (stack s))%N
                  (bool_decide ((w >>> word_shift a) << word_shift a = w))
          then (NONE, set_var r (EL i (stack s)) s)
          else (SOME Error, empty_env s)
      | _ => (SOME Error, empty_env s)
      end
  | StackStore r n =>
      if negb (use_stack s) then (SOME Error, s) else
      if (LENGTH (stack s) <=? stack_space s + n)%N then (SOME Error, empty_env s) else
      match get_var r s with
      | NONE => (SOME Error, empty_env s)
      | SOME v => (NONE, set_stack (LUPDATE v (stack_space s + n) (stack s)) s)
      end
  | StackStoreAny r rn =>
      if negb (use_stack s) then (SOME Error, s) else
      match get_var r s, get_var rn s with
      | SOME v, SOME (Word w) =>
          let i := (stack_space s + w2n (w >>> word_shift a))%N in
          if andb (i <? LENGTH (stack s))%N
                  (bool_decide ((w >>> word_shift a) << word_shift a = w))
          then (NONE, set_stack (LUPDATE v i (stack s)) s)
          else (SOME Error, empty_env s)
      | _, _ => (SOME Error, empty_env s)
      end
  | StackGetSize r =>
      if negb (use_stack s) then (SOME Error, s) else
      (NONE, set_var r (Word (n2w (stack_space s))) s)
  | StackSetSize r =>
      if negb (use_stack s) then (SOME Error, s) else
      match get_var r s with
      | SOME (Word w) =>
          if (LENGTH (stack s) <=? w2n w)%N then (SOME Error, empty_env s)
          else (NONE, set_var r (Word (w << word_shift a)) (set_stack_space (w2n w) s))
      | _ => (SOME Error, s)
      end
  | BitmapLoad r v =>
      if orb (negb (use_stack s)) (r =? v)%N then (SOME Error, s) else
      match get_var v s with
      | SOME (Word w) =>
          if (LENGTH (bitmaps s) <=? w2n w)%N then (SOME Error, s)
          else (NONE, set_var r (Word (EL (w2n w) (bitmaps s))) s)
      | _ => (SOME Error, s)
      end
  end.

Fixpoint evaluate_c (cf : nat) (p0 : prog a) (s0 : state a c ffi_t) {struct cf}
    : option (result a) * state a c ffi_t :=
  let lower (p : prog a) (s : state a c ffi_t) : option (result a) * state a c ffi_t :=
    match cf with O => (SOME Error, s) | Datatypes.S cf' => evaluate_c cf' p s end in
  let fix go (p : prog a) (s : state a c ffi_t) {struct p} : option (result a) * state a c ffi_t :=
    evaluate_body go lower p s in
  go p0 s0.

(** HOL [evaluate]: run with a clock fuel above the state's clock. *)
Definition evaluate (x : prog a * state a c ffi_t) : option (result a) * state a c ffi_t :=
  let '(p, s) := x in evaluate_c (Datatypes.S (N.to_nat (clock s))) p s.

End Evaluate.

(** ** HOL's [evaluate_def]

    Termination measure, as in HOL: the clock, then the program size
    (Galette counts [Seq]/[If]/[Loop] nodes; only the existence of a
    decreasing measure matters). *)
Section EvaluateEqns.
Context {a : N} {c ffi_t : Type}.

Fixpoint psize (p : prog a) : nat :=
  match p with
  | Seq c1 c2 => Datatypes.S (psize c1 + psize c2)
  | If _ _ _ c1 c2 => Datatypes.S (psize c1 + psize c2)
  | Loop c1 => Datatypes.S (psize c1)
  | _ => 1
  end.

Definition eval_lt (x y : prog a * state a c ffi_t) : Prop :=
  (clock (snd x) < clock (snd y))%N \/
  (clock (snd x) = clock (snd y) /\ (psize (fst x) < psize (fst y))%nat).

Lemma eval_lt_wf : well_founded eval_lt.
Proof.
  intros [p s].
  remember (N.to_nat (clock s)) as n eqn:Hc. revert p s Hc.
  induction n as [n IHc] using (well_founded_induction lt_wf).
  intros p s Hc.
  remember (psize p) as m eqn:Hn. revert p s Hc Hn.
  induction m as [m IHn] using (well_founded_induction lt_wf).
  intros p s Hc Hn; constructor; intros [p' s'] [Hlt|[Heq Hlt]]; cbn in *.
  - eapply IHc; [|reflexivity]. lia.
  - eapply IHn; [| |reflexivity]; [lia|]. lia.
Qed.

Definition lowerF (cf : nat) (p : prog a) (s : state a c ffi_t) : option (result a) * state a c ffi_t :=
  match cf with O => (SOME Error, s) | Datatypes.S cf' => evaluate_c cf' p s end.

Lemma evaluate_c_unfold cf p s :
  evaluate_c cf p s = evaluate_body (evaluate_c cf) (lowerF cf) p s.
Proof. destruct cf, p; reflexivity. Qed.

Ltac clock_facts :=
  repeat match goal with
         | H : fix_clock _ _ = (_, _) |- _ =>
             let Hle := fresh "Hle" in
             pose proof (fix_clock_IMP _ _ _ _ H) as Hle; clear H
         | H : (clock _ =? 0)%N = false |- _ => apply N.eqb_neq in H
         end;
  cbn [clock set_var set_regs set_clock dec_clock empty_env set_stack STOP psize] in *.

Ltac prove_eval_lt := unfold eval_lt; cbn [fst snd]; clock_facts; lia.
Ltac prove_clock_lt := clock_facts; lia.

Lemma evaluate_body_ext
    (go1 go2 lo1 lo2 : prog a -> state a c ffi_t -> option (result a) * state a c ffi_t) p s :
  (forall p' s', eval_lt (p', s') (p, s) -> go1 p' s' = go2 p' s') ->
  (forall p' s', (clock s' < clock s)%N -> lo1 p' s' = lo2 p' s') ->
  evaluate_body go1 lo1 p s = evaluate_body go2 lo2 p s.
Proof.
  intros Hgo Hlo.
  destruct p; cbn [evaluate_body];
  repeat first
    [ reflexivity
    | match goal with
      | |- context [go1 ?p' ?s'] => rewrite (Hgo p' s') by prove_eval_lt
      | |- context [lo1 ?p' ?s'] => rewrite (Hlo p' s') by prove_clock_lt
      end
    | match goal with
      | |- context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
      end ].
Qed.

Lemma evaluate_c_fuel : forall (x : prog a * state a c ffi_t) cf1 cf2,
  (N.to_nat (clock (snd x)) < cf1)%nat -> (N.to_nat (clock (snd x)) < cf2)%nat ->
  evaluate_c cf1 (fst x) (snd x) = evaluate_c cf2 (fst x) (snd x).
Proof.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros cf1 cf2 H1 H2; cbn [fst snd] in *.
  rewrite !evaluate_c_unfold. apply evaluate_body_ext.
  - intros p' s' Hlt. apply (IH (p', s') Hlt); cbn;
      destruct Hlt as [Hlt|[Heq _]]; cbn in *; lia.
  - intros p' s' Hlt. destruct cf1 as [|cf1]; [lia|]. destruct cf2 as [|cf2]; [lia|].
    cbn [lowerF]. apply (IH (p', s')); [left; exact Hlt| |]; cbn; lia.
Qed.

Lemma evaluate_eq_c cf (p : prog a) (s : state a c ffi_t) :
  (N.to_nat (clock s) < cf)%nat -> evaluate (p, s) = evaluate_c cf p s.
Proof.
  intros H; unfold evaluate.
  apply (evaluate_c_fuel (p, s)); cbn; lia.
Qed.

(** [evaluate] is a fixed point of its one-step body. *)
Lemma evaluate_eqn (p : prog a) (s : state a c ffi_t) :
  evaluate (p, s) =
  evaluate_body (fun p' s' => evaluate (p', s')) (fun p' s' => evaluate (p', s')) p s.
Proof.
  rewrite (evaluate_eq_c (Datatypes.S (N.to_nat (clock s)))) by lia.
  rewrite evaluate_c_unfold. apply evaluate_body_ext.
  - intros p' s' Hlt. symmetry; apply evaluate_eq_c.
    destruct Hlt as [Hlt|[Heq _]]; cbn in *; lia.
  - intros p' s' Hlt. cbn [lowerF]. symmetry; apply evaluate_eq_c. lia.
Qed.

(** *** The clock never increases *)

Ltac split_H H :=
  repeat match type of H with
         | context [match ?x with _ => _ end] =>
             let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H
         end.

Ltac fin :=
  cbn [clock set_var set_fp_var set_store set_regs set_fp_regs set_store_fld set_stack
       set_stack_space set_memory set_mdomain set_sh_mdomain set_bitmaps set_compile
       set_compile_oracle set_code_buffer set_data_buffer set_gc_fun set_use_stack
       set_use_store set_use_alloc set_code set_ffi set_ffi_save_regs set_be set_clock
       empty_env unset_var dec_clock I] in *; lia.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "gc_clock" *)
Theorem gc_clock : forall (s1 s2 : state a c ffi_t), gc s1 = SOME s2 -> clock s2 <= clock s1.
Proof.
  intros s1 s2 H; unfold gc in H; split_H H; try discriminate.
  injection H as <-; fin.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "alloc_clock" *)
Theorem alloc_clock : forall {B} (x : word a) (xs : B) (s1 : state a c ffi_t) vs s2,
  alloc x s1 = (vs, s2) -> clock s2 <= clock s1.
Proof.
  intros B x xs s1 vs s2 H; unfold alloc in H.
  destruct (gc (set_store AllocSize (Word x) s1)) as [s3|] eqn:Eg;
    [|injection H as <- <-; lia].
  apply gc_clock in Eg. cbn [clock set_store set_store_fld] in Eg.
  split_H H; injection H as <- <-; fin.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "store_const_sem_clock" *)
Theorem store_const_sem_clock : forall t1 t2 (s1 : state a c ffi_t) v s2,
  store_const_sem t1 t2 s1 = (v, s2) -> clock s2 <= clock s1.
Proof.
  intros t1 t2 s1 v s2 H; unfold store_const_sem in H; split_H H;
    injection H as <- <-; fin.
Qed.

Lemma mem_store_clock (ad : word a) w (s s' : state a c ffi_t) :
  mem_store ad w s = SOME s' -> clock s' = clock s.
Proof.
  unfold mem_store; destruct (classical_dec _); [|discriminate].
  intros H; injection H as <-; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "inst_clock" *)
Theorem inst_clock : forall (i : asm.inst a) (s s2 : state a c ffi_t),
  inst i s = SOME s2 -> clock s2 <= clock s.
Proof.
  intros i s s2 H.
  destruct i as [| | x | m r [ad w] | f];
    [| | destruct x | destruct m | destruct f]; cbn [inst] in H;
    unfold assign in H; split_H H; try discriminate;
    repeat match goal with E : mem_store _ _ _ = SOME _ |- _ => apply mem_store_clock in E end;
    injection H as <-; fin.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "sh_mem_op_clock" *)
Theorem sh_mem_op_clock : forall op r ad (s : state a c ffi_t) res s',
  sh_mem_op op r ad s = (res, s') -> clock s' <= clock s.
Proof.
  intros op r ad s res s' H.
  destruct op; cbn [sh_mem_op] in H;
    unfold sh_mem_load, sh_mem_store, sh_mem_load_byte, sh_mem_store_byte,
      sh_mem_load16, sh_mem_store16, sh_mem_load32, sh_mem_store32 in H;
    split_H H; injection H as <- <-; fin.
Qed.

Ltac clock_step IH H :=
  repeat first
    [ match type of H with
      | evaluate (?p', ?s'') = (?r', ?t) =>
          let Hc := fresh "Hc" in
          assert (Hc : (clock t <= clock s'')%N)
            by (apply (IH (p', s'') ltac:(prove_eval_lt) r' t H));
          clear H; clock_facts; fin
      | (_, _) = (_, _) => injection H as <- <-; clock_facts; fin
      | alloc _ _ = (_, _) => apply (alloc_clock _ tt) in H; clock_facts; fin
      | store_const_sem _ _ _ = (_, _) => apply store_const_sem_clock in H; clock_facts; fin
      | sh_mem_op _ _ _ _ = (_, _) => apply sh_mem_op_clock in H; clock_facts; fin
      end
    | match goal with
      | E : evaluate (?p', ?s'') = (?r', ?t) |- _ =>
          let Hc := fresh "Hc" in
          assert (Hc : (clock t <= clock s'')%N)
            by (apply (IH (p', s'') ltac:(prove_eval_lt) r' t E));
          clear E
      | E : fix_clock _ _ = (_, _) |- _ =>
          let Hle := fresh "Hle" in
          pose proof (fix_clock_IMP _ _ _ _ E) as Hle; clear E
      | E : (clock _ =? 0)%N = false |- _ => apply N.eqb_neq in E
      | E : inst _ _ = SOME _ |- _ => apply inst_clock in E
      end
    | match type of H with
      | context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H
      end ].

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "evaluate_clock" *)
Theorem evaluate_clock : forall (xs : prog a) (s1 : state a c ffi_t) vs s2,
  evaluate (xs, s1) = (vs, s2) -> clock s2 <= clock s1.
Proof.
  enough (G : forall x : prog a * state a c ffi_t, forall r s',
            evaluate x = (r, s') -> (clock s' <= clock (snd x))%N)
    by (intros p s r s' H; exact (G (p, s) r s' H)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s' H; cbn [snd].
  rewrite evaluate_eqn in H.
  destruct p; cbn [evaluate_body] in H; clock_step IH H.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "fix_clock_evaluate" *)
Theorem fix_clock_evaluate : forall (xs : prog a) (s : state a c ffi_t),
  fix_clock s (evaluate (xs, s)) = evaluate (xs, s).
Proof.
  intros p s; destruct (evaluate (p, s)) as [r s'] eqn:E.
  pose proof (evaluate_clock p s r s' E) as Hc.
  unfold fix_clock, MIN; f_equal.
  destruct (N.ltb_spec (clock s) (clock s')); [lia|].
  destruct s'; reflexivity.
Qed.

Local Open Scope word_scope.

(** HOL's defining equations (with [fix_clock]). *)
(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "evaluate_def" 773 *)
Theorem evaluate_def_fix_clock :
  (forall  (s : state a c ffi_t),
     evaluate (Skip, s) =   (NONE, s)) /\
  (forall v (s : state a c ffi_t),
     evaluate (stackLang.Halt v, s) =
        match get_var v s with
        | SOME w => (SOME (Halt w), empty_env s)
        | NONE => (SOME Error, s)
        end) /\
  (forall n (s : state a c ffi_t),
     evaluate (Alloc n, s) =
        if negb (use_alloc s) then (SOME Error, s) else
        match get_var n s with
        | SOME (Word w) => alloc w s
        | _ => (SOME Error, s)
        end) /\
  (forall t1 t2 stub_opt (s : state a c ffi_t),
     evaluate (StoreConsts t1 t2 stub_opt, s) =
        if negb (use_store s) then (SOME Error, s) else
        if andb (negb (use_alloc s)) (IS_SOME stub_opt) then (SOME Error, s) else
        if negb (check_store_consts_opt t1 t2 stub_opt (code s)) then (SOME Error, s) else
          store_const_sem t1 t2 s) /\
  (forall i (s : state a c ffi_t),
     evaluate (Inst i, s) =
        match inst i s with
        | SOME s1 => (NONE, s1)
        | NONE => (SOME Error, s)
        end) /\
  (forall v name (s : state a c ffi_t),
     evaluate (Get v name, s) =
        if negb (use_store s) then (SOME Error, s) else
        match FLOOKUP (store s) name with
        | SOME x => (NONE, set_var v x s)
        | NONE => (SOME Error, s)
        end) /\
  (forall name v (s : state a c ffi_t),
     evaluate (Set_ name v, s) =
        if negb (use_store s) then (SOME Error, s) else
        match get_var v s with
        | SOME w => (NONE, set_store name w s)
        | NONE => (SOME Error, s)
        end) /\
  (forall binop v src (s : state a c ffi_t),
     evaluate (OpCurrHeap binop v src, s) =
        if negb (use_store s) then (SOME Error, s) else
        match word_exp s (wordLang.Op binop [wordLang.Var src; wordLang.Lookup CurrHeap]) with
        | SOME w => (NONE, set_var v (Word w) s)
        | _ => (SOME Error, s)
        end) /\
  (forall  (s : state a c ffi_t),
     evaluate (Tick, s) =
        if (clock s =? 0)%N then (SOME TimeOut, empty_env s) else (NONE, dec_clock s)) /\
  (forall c1 c2 (s : state a c ffi_t),
     evaluate (Seq c1 c2, s) =
        let '(res, s1) := fix_clock s (evaluate (c1, s)) in
        match res with NONE => evaluate (c2, s1) | _ => (res, s1) end) /\
  (forall n (s : state a c ffi_t),
     evaluate (Return n, s) =
        match get_var n s with
        | SOME (Loc l1 l2) => (SOME (Result (Loc l1 l2)), s)
        | _ => (SOME Error, s)
        end) /\
  (forall n (s : state a c ffi_t),
     evaluate (Raise n, s) =
        match get_var n s with
        | SOME (Loc l1 l2) => (SOME (Exception (Loc l1 l2)), s)
        | _ => (SOME Error, s)
        end) /\
  (forall n (s : state a c ffi_t),
     evaluate (stackLang.Break n, s) =   (SOME (Break n), s)) /\
  (forall n (s : state a c ffi_t),
     evaluate (stackLang.Continue n, s) =   (SOME (Continue n), s)) /\
  (forall cmp r1 ri c1 c2 (s : state a c ffi_t),
     evaluate (If cmp r1 ri c1 c2, s) =
        match get_var r1 s, get_var_imm ri s with
        | SOME x, SOME y =>
            match wordSem.word_cmp cmp x y with
            | SOME true => evaluate (c1, s)
            | SOME false => evaluate (c2, s)
            | NONE => (SOME Error, s)
            end
        | _, _ => (SOME Error, s)
        end) /\
  (forall c1 (s : state a c ffi_t),
     evaluate (Loop c1, s) =
        let '(res, s1) := fix_clock s (evaluate (c1, s)) in
        if cont_loop res then
          (if (clock s1 =? 0)%N then (SOME TimeOut, empty_env s1) else
             evaluate (STOP (Loop c1), (dec_clock s1)))
        else (exit_loop res, s1)) /\
  (forall r1 r2 dest (s : state a c ffi_t),
     evaluate (JumpLower r1 r2 dest, s) =
        match get_var r1 s, get_var r2 s with
        | SOME (Word x), SOME (Word y) =>
            if word_cmp Lower x y then
              match find_code (inl dest) (regs s) (code s) with
              | NONE => (SOME Error, s)
              | SOME prog0 =>
                  if (clock s =? 0)%N then (SOME TimeOut, empty_env s) else
                    match evaluate (prog0, (dec_clock s)) with
                    | (res, s) => if bad_fun_return res then (SOME Error, s) else (res, s)
                    end
              end
            else (NONE, s)
        | _, _ => (SOME Error, s)
        end) /\
  (forall dest (s : state a c ffi_t),
     evaluate (RawCall dest, s) =
        match sptree.lookup dest (code s) with
        | NONE => (SOME Error, s)
        | SOME prog0 =>
            match dest_Seq prog0 with
            | SOME (_, body) =>
                if (clock s =? 0)%N then (SOME TimeOut, empty_env s) else
                  match evaluate (body, (dec_clock s)) with
                  | (res, s) => if bad_fun_return res then (SOME Error, s) else (res, s)
                  end
            | _ => (SOME Error, s)
            end
        end) /\
  (forall ret dest handler (s : state a c ffi_t),
     evaluate (Call ret dest handler, s) =
        match ret with
        | NONE =>
            match find_code dest (regs s) (code s) with
            | NONE => (SOME Error, s)
            | SOME prog0 =>
                if negb (bool_decide (handler = NONE)) then (SOME Error, s) else
                if (clock s =? 0)%N then (SOME TimeOut, empty_env s) else
                  match fix_clock (dec_clock s) (evaluate (prog0, (dec_clock s))) with
                  | (res, s) => if bad_fun_return res then (SOME Error, s) else (res, s)
                  end
            end
        | SOME (ret_handler, (link_reg, (l1, l2))) =>
            match find_code dest (regs s \\ link_reg) (code s) with
            | NONE => (SOME Error, s)
            | SOME prog0 =>
                if (clock s =? 0)%N then (SOME TimeOut, empty_env s) else
                  match fix_clock (dec_clock (set_var link_reg (Loc l1 l2) s))
                          (evaluate (prog0, (dec_clock (set_var link_reg (Loc l1 l2) s)))) with
                  | (SOME (Result x), s2) =>
                      if negb (bool_decide (x = Loc l1 l2)) then (SOME Error, s2)
                      else evaluate (ret_handler, s2)
                  | (SOME (Exception x), s2) =>
                      match handler with
                      | NONE => (SOME (Exception x), s2)
                      | SOME (h, (l1, l2)) =>
                          if negb (bool_decide (x = Loc l1 l2)) then (SOME Error, s2) else
                            evaluate (h, s2)
                      end
                  | (NONE, s) => (SOME Error, s)
                  | (SOME (Break _), s) => (SOME Error, s)
                  | (SOME (Continue _), s) => (SOME Error, s)
                  | (res, s) => (res, s)
                  end
            end
        end) /\
  (forall ptr len dptr dlen ret (s : state a c ffi_t),
     evaluate (Install ptr len dptr dlen ret, s) =
        match get_var ptr s, get_var len s, get_var dptr s, get_var dlen s with
        | SOME (Word w1), SOME (Word w2), SOME (Word w3), SOME (Word w4) =>
            let '(cfg, (progs, bm)) := compile_oracle s 0 in
            match buffer_flush (code_buffer s) w1 w2,
                  (if use_stack s then buffer_flush (data_buffer s) w3 w4
                   else SOME (bm, data_buffer s)) with
            | SOME (bytes, cb), SOME (data, db) =>
                let new_oracle := shift_seq 1 (compile_oracle s) in
                match compile s cfg progs, progs with
                | SOME (bytes', cfg'), (k, prog0) :: _ =>
                    if andb (andb (bool_decide (bytes = bytes')) (bool_decide (data = bm)))
                            ⌜FST (new_oracle 0) = cfg'⌝ then
                      let s' :=
                        set_compile_oracle new_oracle
                          (set_fp_regs FEMPTY
                            (set_regs (DRESTRICT (regs s) (ffi_save_regs s) |+ (ptr, Loc k 0))
                              (set_code (sptree.union (code s) (sptree.fromAList progs))
                                (set_data_buffer db
                                  (set_code_buffer cb
                                    (set_bitmaps (bitmaps s ++ bm) s)))))) in
                      (NONE, s')
                    else (SOME Error, s)
                | _, _ => (SOME Error, s)
                end
            | _, _ => (SOME Error, s)
            end
        | _, _, _, _ => (SOME Error, s)
        end) /\
  (forall op r ad w (s : state a c ffi_t),
     evaluate (ShMemOp op r (Addr ad w), s) =
        match word_exp s (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w]) with
        | SOME ad =>
            if (clock s =? 0)%N then (SOME TimeOut, empty_env s) else
              sh_mem_op op r ad (dec_clock s)
        | _ => (SOME Error, s)
        end) /\
  (forall r1 r2 (s : state a c ffi_t),
     evaluate (CodeBufferWrite r1 r2, s) =
        match get_var r1 s, get_var r2 s with
        | SOME (Word w1), SOME (Word w2) =>
            match buffer_write (code_buffer s) w1 (w2w w2) with
            | SOME new_cb => (NONE, set_code_buffer new_cb s)
            | _ => (SOME Error, s)
            end
        | _, _ => (SOME Error, s)
        end) /\
  (forall r1 r2 (s : state a c ffi_t),
     evaluate (DataBufferWrite r1 r2, s) =
        if negb (use_stack s) then (SOME Error, s) else
        match get_var r1 s, get_var r2 s with
        | SOME (Word w1), SOME (Word w2) =>
            match buffer_write (data_buffer s) w1 w2 with
            | SOME new_db => (NONE, set_data_buffer new_db s)
            | _ => (SOME Error, s)
            end
        | _, _ => (SOME Error, s)
        end) /\
  (forall ffi_index ptr len ptr2 len2 ret (s : state a c ffi_t),
     evaluate (FFI ffi_index ptr len ptr2 len2 ret, s) =
        match get_var len s, get_var ptr s, get_var len2 s, get_var ptr2 s with
        | SOME (Word w), SOME (Word w2), SOME (Word w3), SOME (Word w4) =>
            match read_bytearray w2 (w2n w) (mem_load_byte_aux (memory s) (mdomain s) (be s)),
                  read_bytearray w4 (w2n w3) (mem_load_byte_aux (memory s) (mdomain s) (be s)) with
            | SOME bytes, SOME bytes2 =>
                match call_FFI (ffi s) (ExtCall ffi_index) bytes bytes2 with
                | FFI_final outcome => (SOME (FinalFFI outcome), s)
                | FFI_return new_ffi new_bytes =>
                    let new_m := write_bytearray w4 new_bytes (memory s) (mdomain s) (be s) in
                    (NONE, set_ffi new_ffi (set_fp_regs FEMPTY
                             (set_regs (DRESTRICT (regs s) (ffi_save_regs s)) (set_memory new_m s))))
                end
            | _, _ => (SOME Error, s)
            end
        | _, _, _, _ => (SOME Error, s)
        end) /\
  (forall r l1 l2 (s : state a c ffi_t),
     evaluate (LocValue r l1 l2, s) =
        if classical_dec (loc_check (code s) (l1, l2)) then (NONE, set_var r (Loc l1 l2) s)
        else (SOME Error, s)) /\
  (forall n (s : state a c ffi_t),
     evaluate (StackAlloc n, s) =
        if negb (use_stack s) then (SOME Error, s) else
        if (stack_space s <? n)%N then (SOME (Halt (Word (n2w 2))), empty_env s) else
          (NONE, set_stack_space (stack_space s - n) s)) /\
  (forall n (s : state a c ffi_t),
     evaluate (StackFree n, s) =
        if negb (use_stack s) then (SOME Error, s) else
        if (LENGTH (stack s) <? stack_space s + n)%N then (SOME Error, empty_env s) else
          (NONE, set_stack_space (stack_space s + n) s)) /\
  (forall r n (s : state a c ffi_t),
     evaluate (StackLoad r n, s) =
        if negb (use_stack s) then (SOME Error, s) else
        if (stack_space s + n <? LENGTH (stack s))%N
        then (NONE, set_var r (EL (stack_space s + n) (stack s)) s)
        else (SOME Error, empty_env s)) /\
  (forall r rn (s : state a c ffi_t),
     evaluate (StackLoadAny r rn, s) =
        if negb (use_stack s) then (SOME Error, s) else
        match get_var rn s with
        | SOME (Word w) =>
            let i := (stack_space s + w2n (w >>> word_shift a))%N in
            if andb (i <? LENGTH (stack s))%N
                    (bool_decide ((w >>> word_shift a) << word_shift a = w))
            then (NONE, set_var r (EL i (stack s)) s)
            else (SOME Error, empty_env s)
        | _ => (SOME Error, empty_env s)
        end) /\
  (forall r n (s : state a c ffi_t),
     evaluate (StackStore r n, s) =
        if negb (use_stack s) then (SOME Error, s) else
        if (LENGTH (stack s) <=? stack_space s + n)%N then (SOME Error, empty_env s) else
        match get_var r s with
        | NONE => (SOME Error, empty_env s)
        | SOME v => (NONE, set_stack (LUPDATE v (stack_space s + n) (stack s)) s)
        end) /\
  (forall r rn (s : state a c ffi_t),
     evaluate (StackStoreAny r rn, s) =
        if negb (use_stack s) then (SOME Error, s) else
        match get_var r s, get_var rn s with
        | SOME v, SOME (Word w) =>
            let i := (stack_space s + w2n (w >>> word_shift a))%N in
            if andb (i <? LENGTH (stack s))%N
                    (bool_decide ((w >>> word_shift a) << word_shift a = w))
            then (NONE, set_stack (LUPDATE v i (stack s)) s)
            else (SOME Error, empty_env s)
        | _, _ => (SOME Error, empty_env s)
        end) /\
  (forall r (s : state a c ffi_t),
     evaluate (StackGetSize r, s) =
        if negb (use_stack s) then (SOME Error, s) else
        (NONE, set_var r (Word (n2w (stack_space s))) s)) /\
  (forall r (s : state a c ffi_t),
     evaluate (StackSetSize r, s) =
        if negb (use_stack s) then (SOME Error, s) else
        match get_var r s with
        | SOME (Word w) =>
            if (LENGTH (stack s) <=? w2n w)%N then (SOME Error, empty_env s)
            else (NONE, set_var r (Word (w << word_shift a)) (set_stack_space (w2n w) s))
        | _ => (SOME Error, s)
        end) /\
  (forall r v (s : state a c ffi_t),
     evaluate (BitmapLoad r v, s) =
        if orb (negb (use_stack s)) (r =? v)%N then (SOME Error, s) else
        match get_var v s with
        | SOME (Word w) =>
            if (LENGTH (bitmaps s) <=? w2n w)%N then (SOME Error, s)
            else (NONE, set_var r (Word (EL (w2n w) (bitmaps s))) s)
        | _ => (SOME Error, s)
        end).
Proof.
  repeat split; intros; rewrite evaluate_eqn at 1; reflexivity.
Qed.

(** HOL's rebound [evaluate_def] ([fix_clock] removed by
    [fix_clock_evaluate]). *)
(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "evaluate_def" 1108 *)
Theorem evaluate_def :
  (forall  (s : state a c ffi_t),
     evaluate (Skip, s) =   (NONE, s)) /\
  (forall v (s : state a c ffi_t),
     evaluate (stackLang.Halt v, s) =
        match get_var v s with
        | SOME w => (SOME (Halt w), empty_env s)
        | NONE => (SOME Error, s)
        end) /\
  (forall n (s : state a c ffi_t),
     evaluate (Alloc n, s) =
        if negb (use_alloc s) then (SOME Error, s) else
        match get_var n s with
        | SOME (Word w) => alloc w s
        | _ => (SOME Error, s)
        end) /\
  (forall t1 t2 stub_opt (s : state a c ffi_t),
     evaluate (StoreConsts t1 t2 stub_opt, s) =
        if negb (use_store s) then (SOME Error, s) else
        if andb (negb (use_alloc s)) (IS_SOME stub_opt) then (SOME Error, s) else
        if negb (check_store_consts_opt t1 t2 stub_opt (code s)) then (SOME Error, s) else
          store_const_sem t1 t2 s) /\
  (forall i (s : state a c ffi_t),
     evaluate (Inst i, s) =
        match inst i s with
        | SOME s1 => (NONE, s1)
        | NONE => (SOME Error, s)
        end) /\
  (forall v name (s : state a c ffi_t),
     evaluate (Get v name, s) =
        if negb (use_store s) then (SOME Error, s) else
        match FLOOKUP (store s) name with
        | SOME x => (NONE, set_var v x s)
        | NONE => (SOME Error, s)
        end) /\
  (forall name v (s : state a c ffi_t),
     evaluate (Set_ name v, s) =
        if negb (use_store s) then (SOME Error, s) else
        match get_var v s with
        | SOME w => (NONE, set_store name w s)
        | NONE => (SOME Error, s)
        end) /\
  (forall binop v src (s : state a c ffi_t),
     evaluate (OpCurrHeap binop v src, s) =
        if negb (use_store s) then (SOME Error, s) else
        match word_exp s (wordLang.Op binop [wordLang.Var src; wordLang.Lookup CurrHeap]) with
        | SOME w => (NONE, set_var v (Word w) s)
        | _ => (SOME Error, s)
        end) /\
  (forall  (s : state a c ffi_t),
     evaluate (Tick, s) =
        if (clock s =? 0)%N then (SOME TimeOut, empty_env s) else (NONE, dec_clock s)) /\
  (forall c1 c2 (s : state a c ffi_t),
     evaluate (Seq c1 c2, s) =
        let '(res, s1) := evaluate (c1, s) in
        match res with NONE => evaluate (c2, s1) | _ => (res, s1) end) /\
  (forall n (s : state a c ffi_t),
     evaluate (Return n, s) =
        match get_var n s with
        | SOME (Loc l1 l2) => (SOME (Result (Loc l1 l2)), s)
        | _ => (SOME Error, s)
        end) /\
  (forall n (s : state a c ffi_t),
     evaluate (Raise n, s) =
        match get_var n s with
        | SOME (Loc l1 l2) => (SOME (Exception (Loc l1 l2)), s)
        | _ => (SOME Error, s)
        end) /\
  (forall n (s : state a c ffi_t),
     evaluate (stackLang.Break n, s) =   (SOME (Break n), s)) /\
  (forall n (s : state a c ffi_t),
     evaluate (stackLang.Continue n, s) =   (SOME (Continue n), s)) /\
  (forall cmp r1 ri c1 c2 (s : state a c ffi_t),
     evaluate (If cmp r1 ri c1 c2, s) =
        match get_var r1 s, get_var_imm ri s with
        | SOME x, SOME y =>
            match wordSem.word_cmp cmp x y with
            | SOME true => evaluate (c1, s)
            | SOME false => evaluate (c2, s)
            | NONE => (SOME Error, s)
            end
        | _, _ => (SOME Error, s)
        end) /\
  (forall c1 (s : state a c ffi_t),
     evaluate (Loop c1, s) =
        let '(res, s1) := evaluate (c1, s) in
        if cont_loop res then
          (if (clock s1 =? 0)%N then (SOME TimeOut, empty_env s1) else
             evaluate (STOP (Loop c1), (dec_clock s1)))
        else (exit_loop res, s1)) /\
  (forall r1 r2 dest (s : state a c ffi_t),
     evaluate (JumpLower r1 r2 dest, s) =
        match get_var r1 s, get_var r2 s with
        | SOME (Word x), SOME (Word y) =>
            if word_cmp Lower x y then
              match find_code (inl dest) (regs s) (code s) with
              | NONE => (SOME Error, s)
              | SOME prog0 =>
                  if (clock s =? 0)%N then (SOME TimeOut, empty_env s) else
                    match evaluate (prog0, (dec_clock s)) with
                    | (res, s) => if bad_fun_return res then (SOME Error, s) else (res, s)
                    end
              end
            else (NONE, s)
        | _, _ => (SOME Error, s)
        end) /\
  (forall dest (s : state a c ffi_t),
     evaluate (RawCall dest, s) =
        match sptree.lookup dest (code s) with
        | NONE => (SOME Error, s)
        | SOME prog0 =>
            match dest_Seq prog0 with
            | SOME (_, body) =>
                if (clock s =? 0)%N then (SOME TimeOut, empty_env s) else
                  match evaluate (body, (dec_clock s)) with
                  | (res, s) => if bad_fun_return res then (SOME Error, s) else (res, s)
                  end
            | _ => (SOME Error, s)
            end
        end) /\
  (forall ret dest handler (s : state a c ffi_t),
     evaluate (Call ret dest handler, s) =
        match ret with
        | NONE =>
            match find_code dest (regs s) (code s) with
            | NONE => (SOME Error, s)
            | SOME prog0 =>
                if negb (bool_decide (handler = NONE)) then (SOME Error, s) else
                if (clock s =? 0)%N then (SOME TimeOut, empty_env s) else
                  match evaluate (prog0, (dec_clock s)) with
                  | (res, s) => if bad_fun_return res then (SOME Error, s) else (res, s)
                  end
            end
        | SOME (ret_handler, (link_reg, (l1, l2))) =>
            match find_code dest (regs s \\ link_reg) (code s) with
            | NONE => (SOME Error, s)
            | SOME prog0 =>
                if (clock s =? 0)%N then (SOME TimeOut, empty_env s) else
                  match evaluate (prog0, (dec_clock (set_var link_reg (Loc l1 l2) s))) with
                  | (SOME (Result x), s2) =>
                      if negb (bool_decide (x = Loc l1 l2)) then (SOME Error, s2)
                      else evaluate (ret_handler, s2)
                  | (SOME (Exception x), s2) =>
                      match handler with
                      | NONE => (SOME (Exception x), s2)
                      | SOME (h, (l1, l2)) =>
                          if negb (bool_decide (x = Loc l1 l2)) then (SOME Error, s2) else
                            evaluate (h, s2)
                      end
                  | (NONE, s) => (SOME Error, s)
                  | (SOME (Break _), s) => (SOME Error, s)
                  | (SOME (Continue _), s) => (SOME Error, s)
                  | (res, s) => (res, s)
                  end
            end
        end) /\
  (forall ptr len dptr dlen ret (s : state a c ffi_t),
     evaluate (Install ptr len dptr dlen ret, s) =
        match get_var ptr s, get_var len s, get_var dptr s, get_var dlen s with
        | SOME (Word w1), SOME (Word w2), SOME (Word w3), SOME (Word w4) =>
            let '(cfg, (progs, bm)) := compile_oracle s 0 in
            match buffer_flush (code_buffer s) w1 w2,
                  (if use_stack s then buffer_flush (data_buffer s) w3 w4
                   else SOME (bm, data_buffer s)) with
            | SOME (bytes, cb), SOME (data, db) =>
                let new_oracle := shift_seq 1 (compile_oracle s) in
                match compile s cfg progs, progs with
                | SOME (bytes', cfg'), (k, prog0) :: _ =>
                    if andb (andb (bool_decide (bytes = bytes')) (bool_decide (data = bm)))
                            ⌜FST (new_oracle 0) = cfg'⌝ then
                      let s' :=
                        set_compile_oracle new_oracle
                          (set_fp_regs FEMPTY
                            (set_regs (DRESTRICT (regs s) (ffi_save_regs s) |+ (ptr, Loc k 0))
                              (set_code (sptree.union (code s) (sptree.fromAList progs))
                                (set_data_buffer db
                                  (set_code_buffer cb
                                    (set_bitmaps (bitmaps s ++ bm) s)))))) in
                      (NONE, s')
                    else (SOME Error, s)
                | _, _ => (SOME Error, s)
                end
            | _, _ => (SOME Error, s)
            end
        | _, _, _, _ => (SOME Error, s)
        end) /\
  (forall op r ad w (s : state a c ffi_t),
     evaluate (ShMemOp op r (Addr ad w), s) =
        match word_exp s (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w]) with
        | SOME ad =>
            if (clock s =? 0)%N then (SOME TimeOut, empty_env s) else
              sh_mem_op op r ad (dec_clock s)
        | _ => (SOME Error, s)
        end) /\
  (forall r1 r2 (s : state a c ffi_t),
     evaluate (CodeBufferWrite r1 r2, s) =
        match get_var r1 s, get_var r2 s with
        | SOME (Word w1), SOME (Word w2) =>
            match buffer_write (code_buffer s) w1 (w2w w2) with
            | SOME new_cb => (NONE, set_code_buffer new_cb s)
            | _ => (SOME Error, s)
            end
        | _, _ => (SOME Error, s)
        end) /\
  (forall r1 r2 (s : state a c ffi_t),
     evaluate (DataBufferWrite r1 r2, s) =
        if negb (use_stack s) then (SOME Error, s) else
        match get_var r1 s, get_var r2 s with
        | SOME (Word w1), SOME (Word w2) =>
            match buffer_write (data_buffer s) w1 w2 with
            | SOME new_db => (NONE, set_data_buffer new_db s)
            | _ => (SOME Error, s)
            end
        | _, _ => (SOME Error, s)
        end) /\
  (forall ffi_index ptr len ptr2 len2 ret (s : state a c ffi_t),
     evaluate (FFI ffi_index ptr len ptr2 len2 ret, s) =
        match get_var len s, get_var ptr s, get_var len2 s, get_var ptr2 s with
        | SOME (Word w), SOME (Word w2), SOME (Word w3), SOME (Word w4) =>
            match read_bytearray w2 (w2n w) (mem_load_byte_aux (memory s) (mdomain s) (be s)),
                  read_bytearray w4 (w2n w3) (mem_load_byte_aux (memory s) (mdomain s) (be s)) with
            | SOME bytes, SOME bytes2 =>
                match call_FFI (ffi s) (ExtCall ffi_index) bytes bytes2 with
                | FFI_final outcome => (SOME (FinalFFI outcome), s)
                | FFI_return new_ffi new_bytes =>
                    let new_m := write_bytearray w4 new_bytes (memory s) (mdomain s) (be s) in
                    (NONE, set_ffi new_ffi (set_fp_regs FEMPTY
                             (set_regs (DRESTRICT (regs s) (ffi_save_regs s)) (set_memory new_m s))))
                end
            | _, _ => (SOME Error, s)
            end
        | _, _, _, _ => (SOME Error, s)
        end) /\
  (forall r l1 l2 (s : state a c ffi_t),
     evaluate (LocValue r l1 l2, s) =
        if classical_dec (loc_check (code s) (l1, l2)) then (NONE, set_var r (Loc l1 l2) s)
        else (SOME Error, s)) /\
  (forall n (s : state a c ffi_t),
     evaluate (StackAlloc n, s) =
        if negb (use_stack s) then (SOME Error, s) else
        if (stack_space s <? n)%N then (SOME (Halt (Word (n2w 2))), empty_env s) else
          (NONE, set_stack_space (stack_space s - n) s)) /\
  (forall n (s : state a c ffi_t),
     evaluate (StackFree n, s) =
        if negb (use_stack s) then (SOME Error, s) else
        if (LENGTH (stack s) <? stack_space s + n)%N then (SOME Error, empty_env s) else
          (NONE, set_stack_space (stack_space s + n) s)) /\
  (forall r n (s : state a c ffi_t),
     evaluate (StackLoad r n, s) =
        if negb (use_stack s) then (SOME Error, s) else
        if (stack_space s + n <? LENGTH (stack s))%N
        then (NONE, set_var r (EL (stack_space s + n) (stack s)) s)
        else (SOME Error, empty_env s)) /\
  (forall r rn (s : state a c ffi_t),
     evaluate (StackLoadAny r rn, s) =
        if negb (use_stack s) then (SOME Error, s) else
        match get_var rn s with
        | SOME (Word w) =>
            let i := (stack_space s + w2n (w >>> word_shift a))%N in
            if andb (i <? LENGTH (stack s))%N
                    (bool_decide ((w >>> word_shift a) << word_shift a = w))
            then (NONE, set_var r (EL i (stack s)) s)
            else (SOME Error, empty_env s)
        | _ => (SOME Error, empty_env s)
        end) /\
  (forall r n (s : state a c ffi_t),
     evaluate (StackStore r n, s) =
        if negb (use_stack s) then (SOME Error, s) else
        if (LENGTH (stack s) <=? stack_space s + n)%N then (SOME Error, empty_env s) else
        match get_var r s with
        | NONE => (SOME Error, empty_env s)
        | SOME v => (NONE, set_stack (LUPDATE v (stack_space s + n) (stack s)) s)
        end) /\
  (forall r rn (s : state a c ffi_t),
     evaluate (StackStoreAny r rn, s) =
        if negb (use_stack s) then (SOME Error, s) else
        match get_var r s, get_var rn s with
        | SOME v, SOME (Word w) =>
            let i := (stack_space s + w2n (w >>> word_shift a))%N in
            if andb (i <? LENGTH (stack s))%N
                    (bool_decide ((w >>> word_shift a) << word_shift a = w))
            then (NONE, set_stack (LUPDATE v i (stack s)) s)
            else (SOME Error, empty_env s)
        | _, _ => (SOME Error, empty_env s)
        end) /\
  (forall r (s : state a c ffi_t),
     evaluate (StackGetSize r, s) =
        if negb (use_stack s) then (SOME Error, s) else
        (NONE, set_var r (Word (n2w (stack_space s))) s)) /\
  (forall r (s : state a c ffi_t),
     evaluate (StackSetSize r, s) =
        if negb (use_stack s) then (SOME Error, s) else
        match get_var r s with
        | SOME (Word w) =>
            if (LENGTH (stack s) <=? w2n w)%N then (SOME Error, empty_env s)
            else (NONE, set_var r (Word (w << word_shift a)) (set_stack_space (w2n w) s))
        | _ => (SOME Error, s)
        end) /\
  (forall r v (s : state a c ffi_t),
     evaluate (BitmapLoad r v, s) =
        if orb (negb (use_stack s)) (r =? v)%N then (SOME Error, s) else
        match get_var v s with
        | SOME (Word w) =>
            if (LENGTH (bitmaps s) <=? w2n w)%N then (SOME Error, s)
            else (NONE, set_var r (Word (EL (w2n w) (bitmaps s))) s)
        | _ => (SOME Error, s)
        end).
Proof.
  repeat split; intros; rewrite evaluate_eqn at 1; cbn [evaluate_body];
    repeat first
      [ reflexivity
      | rewrite fix_clock_evaluate
      | match goal with
        | |- context [match ?x with _ => _ end] =>
            let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
        end ].
Qed.

End EvaluateEqns.

(** ** Observable semantics *)
Section Semantics.
Context {a : N} {c ffi_t : Type}.

#[local] Instance behaviour_inhabited : Inhabited behaviour := Fail.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "semantics_def" *)
Definition semantics (start : N) (s : state a c ffi_t) : behaviour :=
  let prog0 := @Call a NONE (inl start) NONE in
  if classical_dec (exists k,
       let res := FST (evaluate (prog0, set_clock k s)) in
       res <> SOME TimeOut /\ res <> SOME (Result (Loc 1 0)) /\
       (forall w, res <> SOME (Halt (Word w))) /\ forall f, res <> SOME (FinalFFI f))
  then Fail
  else
    match some (fun res => exists k t r outcome,
             evaluate (prog0, set_clock k s) = (SOME r, t) /\
             match r with
             | FinalFFI e => outcome = FFI_outcome e
             | Halt w => outcome = if bool_decide (w = Word (n2w 0)) then Success
                                   else Resource_limit_hit
             | Result _ => outcome = Success
             | _ => False
             end /\
             res = Terminate outcome (io_events (ffi t))) with
    | SOME res => res
    | NONE =>
        Diverge (build_lprefix_lub
                   (IMAGE (fun k => fromList (io_events (ffi (SND (evaluate (prog0, set_clock k s))))))
                          UNIV))
    end.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "read_stack_def" *)
Definition read_stack (s : state a c ffi_t) : list (word_loc a) := stack s.

(*! HOL "cakeml/compiler/backend/semantics/stackSemScript.sml" "read_stack_space_def" *)
Definition read_stack_space (s : state a c ffi_t) : N := stack_space s.

End Semantics.
