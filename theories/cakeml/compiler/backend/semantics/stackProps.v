(** * CakeML [stackProps]: properties of stackLang and its semantics

    Port of [cakeml/compiler/backend/semantics/stackPropsScript.sml].

    Carrier notes:
    - HOL's [s with f := v] is [set_f v s] ([stackSem]); HOL's
      [(f ## g) p] is [PAIR_MAP].
    - The syntactic predicates ([stack_asm_ok], [reg_bound], [call_args],
      ...) are boolean, like the [asm] predicates they are built from
      ([inst_ok], [reg_ok]); HOL's [x IN {a; b}] on an explicit finite set
      is [MEM x [a; b]] (as in [asm]); the label sets are [pred_set] sets.
    - [reg_bound_def] lists the [Halt] and [StackStore] clauses twice in
      HOL; the (identical) second copies are redundant and omitted here,
      since Rocq rejects redundant [match] clauses.
    - HOL's [set_fp_var_const] is declared twice (once [local]); the
      second declaration is [set_fp_var_const_2] here.
    - [evaluate_mono] states [subspt] on [prog] trees, which needs
      decidable equality on [stackLang$prog]: a classical instance
      ([prog_eq_dec_classical], Galette-only) is provided.

    Not ported: HOL's [case_eq_thms] (an ML-level list of the
    [case_eq] theorems of several datatypes, not a single HOL theorem).

    Proof method: HOL's [recInduct evaluate_ind] is well-founded induction
    on [eval_lt] ([stackSem]); one step of [evaluate] is unfolded with
    [evaluate_eqn] and [fix_clock_evaluate].  The Galette-only helpers
    (record-update commutations, induction on [wordLang$exp], the
    case-splitting tactics) have no HOL original. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
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
From Galette.cakeml.semantics Require fpSem ast.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang.
From Galette.cakeml.compiler.backend Require wordLang stack_names.
From Galette.cakeml.compiler.backend.semantics Require wordSem.
From Galette.cakeml.compiler.backend.semantics Require Import stackSem backendProps.
Import wordLang (word_loc, Word, Loc).
Import wordSem (buffer, buffer_flush, buffer_write, gc_fun_type, mem_load_byte_aux,
  mem_store_byte_aux, mem_load_32, mem_store_32, write_bytearray).
Open Scope N_scope.

(** ** Galette-only infrastructure *)

(** Decidable equality on programs, classically (HOL equality); used by
    [subspt] on code trees. *)
#[global] Instance prog_eq_dec_classical {a : N} : EqDecision (prog a) :=
  fun x y => classical_dec (x = y).

Section WExpInd.
Context {a : N}.

(** Induction on wordLang expressions with hypotheses for the nested list. *)
Fixpoint wexp_ind (P : wordLang.exp a -> Prop)
    (Hc : forall w, P (wordLang.Const w)) (Hv : forall n, P (wordLang.Var n))
    (Hl : forall n, P (wordLang.Lookup n)) (Hld : forall e, P e -> P (wordLang.Load e))
    (Hop : forall op es, Forall P es -> P (wordLang.Op op es))
    (Hsh : forall sh e1 e2, P e1 -> P e2 -> P (wordLang.Shift sh e1 e2))
    (e : wordLang.exp a) : P e :=
  let rec := wexp_ind P Hc Hv Hl Hld Hop Hsh in
  let fix go (l : list (wordLang.exp a)) : Forall P l :=
    match l with [] => Forall_nil _ | x :: xs => Forall_cons _ (rec x) (go xs) end in
  match e with
  | wordLang.Const w => Hc w
  | wordLang.Var n => Hv n
  | wordLang.Lookup n => Hl n
  | wordLang.Load e => Hld e (rec e)
  | wordLang.Op op es => Hop op es (go es)
  | wordLang.Shift sh e1 e2 => Hsh sh e1 e2 (rec e1) (rec e2)
  end.

End WExpInd.

(** Galette-only: induction on [stackLang.prog] with hypotheses for the
    sub-programs nested in [Call]'s return and handler options. *)
Section ProgInd.
Context {a : N}.
Lemma prog_nested_ind (P : prog a -> Prop) :
  (forall ret dest h,
     (forall p1 x, ret = Some (p1, x) -> P p1) ->
     (forall p2 x, h = Some (p2, x) -> P p2) -> P (Call ret dest h)) ->
  (forall p1 p2, P p1 -> P p2 -> P (Seq p1 p2)) ->
  (forall c r ri p1 p2, P p1 -> P p2 -> P (If c r ri p1 p2)) ->
  (forall p, P p -> P (Loop p)) ->
  (forall p, match p with Call _ _ _ | Seq _ _ | If _ _ _ _ _ | Loop _ => False | _ => True end ->
     P p) ->
  forall p, P p.
Proof.
  intros HC HS HI HL HO; fix IH 1; intros p; destruct p;
    try (apply HO; exact Logic.I).
  - apply HC.
    + destruct o as [[q y]|]; intros p1 x E; [injection E as E _; rewrite <- E; apply IH|discriminate].
    + destruct o0 as [[q y]|]; intros p2 x E; [injection E as E _; rewrite <- E; apply IH|discriminate].
  - apply HS; apply IH.
  - apply HI; apply IH.
  - apply HL; apply IH.
Qed.
End ProgInd.

Ltac stk_fields :=
  cbn [regs fp_regs store stack stack_space memory mdomain sh_mdomain bitmaps compile
       compile_oracle code_buffer data_buffer gc_fun use_stack use_store use_alloc clock code
       ffi ffi_save_regs be
       set_regs set_fp_regs set_store_fld set_stack set_stack_space set_memory set_mdomain
       set_sh_mdomain set_bitmaps set_compile set_compile_oracle set_code_buffer
       set_data_buffer set_gc_fun set_use_stack set_use_store set_use_alloc set_clock set_code
       set_ffi set_ffi_save_regs set_be
       set_var set_fp_var set_store empty_env dec_clock unset_var I fst snd] in *.

Ltac stk_split H :=
  repeat match type of H with
         | context [match ?x with _ => _ end] =>
             let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H
         end.

Ltac stk_split_goal :=
  repeat match goal with
         | |- context [match ?x with _ => _ end] =>
             let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
         end.

Ltac destruct_ands :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end.

(** ** Field lemmas *)

Section Consts.
Context {a : N} {c ffi_t : Type}.
Implicit Types s z : state a c ffi_t.
Local Open Scope word_scope.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "set_store_const" *)
Theorem set_store_const : forall x0 y0 z,
  ffi (set_store x0 y0 z) = ffi z /\
  clock (set_store x0 y0 z) = clock z /\
  use_alloc (set_store x0 y0 z) = use_alloc z /\
  use_store (set_store x0 y0 z) = use_store z /\
  use_stack (set_store x0 y0 z) = use_stack z /\
  code (set_store x0 y0 z) = code z /\
  be (set_store x0 y0 z) = be z /\
  gc_fun (set_store x0 y0 z) = gc_fun z /\
  memory (set_store x0 y0 z) = memory z /\
  mdomain (set_store x0 y0 z) = mdomain z /\
  sh_mdomain (set_store x0 y0 z) = sh_mdomain z /\
  bitmaps (set_store x0 y0 z) = bitmaps z /\
  data_buffer (set_store x0 y0 z) = data_buffer z /\
  code_buffer (set_store x0 y0 z) = code_buffer z /\
  compile (set_store x0 y0 z) = compile z /\
  compile_oracle (set_store x0 y0 z) = compile_oracle z /\
  stack_space (set_store x0 y0 z) = stack_space z /\
  stack (set_store x0 y0 z) = stack z.
Proof. intros; repeat split. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "set_store_with_const" *)
Theorem set_store_with_const : forall x0 y0 z k,
  set_store x0 y0 (set_clock k z) = set_clock k (set_store x0 y0 z).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "set_var_const" *)
Theorem set_var_const : forall x0 y0 z,
  ffi (set_var x0 y0 z) = ffi z /\
  clock (set_var x0 y0 z) = clock z /\
  use_alloc (set_var x0 y0 z) = use_alloc z /\
  use_store (set_var x0 y0 z) = use_store z /\
  use_stack (set_var x0 y0 z) = use_stack z /\
  code (set_var x0 y0 z) = code z /\
  be (set_var x0 y0 z) = be z /\
  fp_regs (set_var x0 y0 z) = fp_regs z /\
  data_buffer (set_var x0 y0 z) = data_buffer z /\
  code_buffer (set_var x0 y0 z) = code_buffer z /\
  gc_fun (set_var x0 y0 z) = gc_fun z /\
  memory (set_var x0 y0 z) = memory z /\
  mdomain (set_var x0 y0 z) = mdomain z /\
  sh_mdomain (set_var x0 y0 z) = sh_mdomain z /\
  bitmaps (set_var x0 y0 z) = bitmaps z /\
  compile (set_var x0 y0 z) = compile z /\
  compile_oracle (set_var x0 y0 z) = compile_oracle z /\
  store (set_var x0 y0 z) = store z /\
  stack (set_var x0 y0 z) = stack z /\
  stack_space (set_var x0 y0 z) = stack_space z.
Proof. intros; repeat split. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "set_var_with_const" *)
Theorem set_var_with_const : forall x0 y0 z clk m ffi0 stk stk_space,
  set_var x0 y0 (set_clock clk z) = set_clock clk (set_var x0 y0 z) /\
  set_var x0 y0 (set_memory m z) = set_memory m (set_var x0 y0 z) /\
  set_var x0 y0 (set_ffi ffi0 z) = set_ffi ffi0 (set_var x0 y0 z) /\
  set_var x0 y0 (set_stack stk z) = set_stack stk (set_var x0 y0 z) /\
  set_var x0 y0 (set_stack_space stk_space z) = set_stack_space stk_space (set_var x0 y0 z).
Proof. intros; repeat split. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "set_fp_var_with_const" *)
Local Theorem set_fp_var_with_const : forall x0 y0 z k,
  set_fp_var x0 y0 (set_clock k z) = set_clock k (set_fp_var x0 y0 z).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "set_fp_var_const" 90 *)
Local Theorem set_fp_var_const : forall x0 y0 z,
  ffi (set_fp_var x0 y0 z) = ffi z /\
  clock (set_fp_var x0 y0 z) = clock z /\
  use_alloc (set_fp_var x0 y0 z) = use_alloc z /\
  use_store (set_fp_var x0 y0 z) = use_store z /\
  use_stack (set_fp_var x0 y0 z) = use_stack z /\
  code (set_fp_var x0 y0 z) = code z /\
  be (set_fp_var x0 y0 z) = be z /\
  gc_fun (set_fp_var x0 y0 z) = gc_fun z /\
  mdomain (set_fp_var x0 y0 z) = mdomain z /\
  sh_mdomain (set_fp_var x0 y0 z) = sh_mdomain z /\
  bitmaps (set_fp_var x0 y0 z) = bitmaps z /\
  compile (set_fp_var x0 y0 z) = compile z /\
  compile_oracle (set_fp_var x0 y0 z) = compile_oracle z /\
  stack (set_fp_var x0 y0 z) = stack z /\
  stack_space (set_fp_var x0 y0 z) = stack_space z.
Proof. intros; repeat split. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "get_fp_var_with_const" *)
Local Theorem get_fp_var_with_const : forall x0 (y : state a c ffi_t) k,
  get_fp_var x0 (set_clock k y) = get_fp_var x0 y.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "get_var_with_const" *)
Theorem get_var_with_const : forall r (t : state a c ffi_t) clk stk_space,
  get_var r (set_clock clk t) = get_var r t /\
  get_var r (set_stack_space stk_space t) = get_var r t.
Proof. intros; split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "get_vars_with_const" *)
Local Theorem get_vars_with_const : forall xs (y : state a c ffi_t) k,
  get_vars xs (set_clock k y) = get_vars xs y.
Proof. intros xs y k; induction xs as [|x0 xs IH]; cbn; [reflexivity|]. rewrite IH; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "get_var_imm_with_const" *)
Theorem get_var_imm_with_const : forall x0 (y : state a c ffi_t) k,
  get_var_imm x0 (set_clock k y) = get_var_imm x0 y.
Proof. intros [] y k; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "set_fp_var_const" 137 *)
Theorem set_fp_var_const_2 : forall x0 y0 z,
  stack_space (set_fp_var x0 y0 z) = stack_space z /\
  stack (set_fp_var x0 y0 z) = stack z.
Proof. intros; split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "empty_env_const" *)
Theorem empty_env_const : forall (x : state a c ffi_t) z,
  ffi (empty_env x) = ffi x /\
  clock (empty_env x) = clock x /\
  use_alloc (empty_env z) = use_alloc z /\
  use_store (empty_env z) = use_store z /\
  use_stack (empty_env z) = use_stack z /\
  code (empty_env z) = code z /\
  be (empty_env z) = be z /\
  gc_fun (empty_env z) = gc_fun z /\
  mdomain (empty_env z) = mdomain z /\
  sh_mdomain (empty_env z) = sh_mdomain z /\
  bitmaps (empty_env z) = bitmaps z /\
  data_buffer (empty_env z) = data_buffer z /\
  code_buffer (empty_env z) = code_buffer z /\
  compile (empty_env z) = compile z /\
  compile_oracle (empty_env z) = compile_oracle z.
Proof. intros; repeat split. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "empty_env_with_const" *)
Theorem empty_env_with_const : forall (x : state a c ffi_t) y0,
  empty_env (set_clock y0 x) = set_clock y0 (empty_env x).
Proof. reflexivity. Qed.

Ltac const_tac H :=
  stk_split H; try discriminate;
  repeat match goal with
         | E : Some _ = Some _ |- _ => injection E as E
         end;
  try (injection H as <- <-); subst; stk_fields; repeat split.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "alloc_const" *)
Theorem alloc_const : forall (w : word a) s r t,
  alloc w s = (r, t) ->
  ffi t = ffi s /\
  clock t = clock s /\
  use_alloc t = use_alloc s /\
  use_store t = use_store s /\
  use_stack t = use_stack s /\
  code t = code s /\
  be t = be s /\
  gc_fun t = gc_fun s /\
  mdomain t = mdomain s /\
  sh_mdomain t = sh_mdomain s /\
  bitmaps t = bitmaps s /\
  compile t = compile s /\
  data_buffer t = data_buffer s /\
  code_buffer t = code_buffer s /\
  compile_oracle t = compile_oracle s.
Proof.
  intros w s r t H; unfold alloc in H.
  destruct (gc (set_store AllocSize (Word w) s)) as [s2|] eqn:Eg;
    [|injection H as <- <-; repeat split].
  unfold gc in Eg; stk_split Eg; try discriminate. injection Eg as <-.
  stk_split H; injection H as <- <-; stk_fields; repeat split; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "store_const_sem_const" *)
Theorem store_const_sem_const : forall t1 t2 s r t,
  store_const_sem t1 t2 s = (r, t) ->
  ffi t = ffi s /\
  clock t = clock s /\
  use_alloc t = use_alloc s /\
  use_store t = use_store s /\
  use_stack t = use_stack s /\
  code t = code s /\
  be t = be s /\
  gc_fun t = gc_fun s /\
  mdomain t = mdomain s /\
  sh_mdomain t = sh_mdomain s /\
  bitmaps t = bitmaps s /\
  compile t = compile s /\
  store t = store s /\
  data_buffer t = data_buffer s /\
  code_buffer t = code_buffer s /\
  compile_oracle t = compile_oracle s.
Proof.
  intros t1 t2 s r t H; unfold store_const_sem in H.
  stk_split H; injection H as <- <-; stk_fields; repeat split; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "gc_with_const" *)
Theorem gc_with_const : forall (x : state a c ffi_t) k,
  gc (set_clock k x) = OPTION_MAP (fun s => set_clock k s) (gc x).
Proof.
  intros x k; unfold gc; stk_fields.
  stk_split_goal; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "alloc_with_const" *)
Theorem alloc_with_const : forall x (y : state a c ffi_t) (z : N),
  alloc x (set_clock z y) = (I ## (fun s => set_clock z s)) (alloc x y).
Proof.
  intros x y z; unfold alloc.
  rewrite set_store_with_const, gc_with_const.
  destruct (gc (set_store AllocSize (Word x) y)) as [s|]; cbn [OPTION_MAP option_map]; [|reflexivity].
  stk_fields. stk_split_goal; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "store_const_sem_with_const" *)
Theorem store_const_sem_with_const : forall (t1 t2 : N) (y : state a c ffi_t) (z : N),
  store_const_sem t1 t2 (set_clock z y) = (I ## (fun s => set_clock z s)) (store_const_sem t1 t2 y).
Proof.
  intros t1 t2 y z; unfold store_const_sem, get_var; stk_fields.
  stk_split_goal; reflexivity.
Qed.

(** HOL's name; the statement is about [mem_store]. *)
(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "mem_load_with_const" *)
Theorem mem_load_with_const : forall x y z k,
  mem_store x y (set_clock k z) = OPTION_MAP (fun s => set_clock k s) (mem_store x y z).
Proof. intros; unfold mem_store; stk_fields. destruct (classical_dec _); reflexivity. Qed.

Ltac sh_with_const :=
  intros; unfold sh_mem_load, sh_mem_store, sh_mem_load_byte, sh_mem_store_byte,
    sh_mem_load16, sh_mem_store16, sh_mem_load32, sh_mem_store32, get_var; stk_fields;
  stk_split_goal; reflexivity.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "sh_mem_load_with_const" *)
Theorem sh_mem_load_with_const : forall r x (y : state a c ffi_t) k,
  sh_mem_load r x (set_clock k y) = (I ## (fun s => set_clock k s)) (sh_mem_load r x y).
Proof. sh_with_const. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "sh_mem_store_with_const" *)
Theorem sh_mem_store_with_const : forall x y z k,
  sh_mem_store x y (set_clock k z) = (I ## (fun s => set_clock k s)) (sh_mem_store x y z).
Proof. sh_with_const. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "sh_mem_load32_with_const" *)
Theorem sh_mem_load32_with_const : forall r x (y : state a c ffi_t) k,
  sh_mem_load32 r x (set_clock k y) = (I ## (fun s => set_clock k s)) (sh_mem_load32 r x y).
Proof. sh_with_const. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "sh_mem_store32_with_const" *)
Theorem sh_mem_store32_with_const : forall x y z k,
  sh_mem_store32 x y (set_clock k z) = (I ## (fun s => set_clock k s)) (sh_mem_store32 x y z).
Proof. sh_with_const. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "sh_mem_load16_with_const" *)
Theorem sh_mem_load16_with_const : forall r x (y : state a c ffi_t) k,
  sh_mem_load16 r x (set_clock k y) = (I ## (fun s => set_clock k s)) (sh_mem_load16 r x y).
Proof. sh_with_const. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "sh_mem_store16_with_const" *)
Theorem sh_mem_store16_with_const : forall x y z k,
  sh_mem_store16 x y (set_clock k z) = (I ## (fun s => set_clock k s)) (sh_mem_store16 x y z).
Proof. sh_with_const. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "sh_mem_load_byte_with_const" *)
Theorem sh_mem_load_byte_with_const : forall r x (y : state a c ffi_t) k,
  sh_mem_load_byte r x (set_clock k y) = (I ## (fun s => set_clock k s)) (sh_mem_load_byte r x y).
Proof. sh_with_const. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "sh_mem_store_byte_with_const" *)
Theorem sh_mem_store_byte_with_const : forall x y z k,
  sh_mem_store_byte x y (set_clock k z) = (I ## (fun s => set_clock k s)) (sh_mem_store_byte x y z).
Proof. sh_with_const. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "sh_mem_op_with_const" *)
Local Theorem sh_mem_op_with_const : forall op x y z k,
  sh_mem_op op x y (set_clock k z) = (I ## (fun s => set_clock k s)) (sh_mem_op op x y z).
Proof. intros [] x y z k; cbn [sh_mem_op]; sh_with_const. Qed.

Lemma word_exp_cong (s t : state a c ffi_t) :
  regs s = regs t -> store s = store t -> memory s = memory t -> mdomain s = mdomain t ->
  forall e, word_exp s e = word_exp t e.
Proof.
  intros H1 H2 H3 H4 e; induction e using wexp_ind; cbn [word_exp];
    rewrite ?H1, ?H2; try reflexivity.
  - rewrite IHe; unfold mem_load; rewrite H3, H4; reflexivity.
  - rewrite (map_ext_Forall _ _ H); reflexivity.
  - rewrite IHe1, IHe2; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "word_exp_with_const" *)
Theorem word_exp_with_const : forall s y k, word_exp (set_clock k s) y = word_exp s y.
Proof. intros s y k; apply word_exp_cong; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "assign_with_const" *)
Theorem assign_with_const : forall x y s k,
  assign x y (set_clock k s) = OPTION_MAP (fun s => set_clock k s) (assign x y s).
Proof.
  intros; unfold assign; rewrite word_exp_with_const; destruct (word_exp s y); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "inst_const" *)
Theorem inst_const : forall i s t,
  inst i s = SOME t ->
  ffi t = ffi s /\
  clock t = clock s /\
  use_alloc t = use_alloc s /\
  use_store t = use_store s /\
  use_stack t = use_stack s /\
  code t = code s /\
  be t = be s /\
  gc_fun t = gc_fun s /\
  mdomain t = mdomain s /\
  sh_mdomain t = sh_mdomain s /\
  bitmaps t = bitmaps s /\
  compile t = compile s /\
  compile_oracle t = compile_oracle s.
Proof.
  intros i s t H.
  destruct i as [| | x | m r [ad w] | f]; [| | destruct x | destruct m | destruct f];
    cbn [inst] in H; unfold assign, mem_store in H; stk_split H; try discriminate;
    repeat match goal with
           | E : (if classical_dec _ then _ else _) = SOME _ |- _ =>
               destruct (classical_dec _); [injection E as <-|discriminate]
           end;
    injection H as <-; stk_fields; repeat split.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "inst_with_const" *)
Theorem inst_with_const : forall i s k,
  inst i (set_clock k s) = OPTION_MAP (fun s => set_clock k s) (inst i s).
Proof.
  intros i s k.
  destruct i as [| | x | m r [ad w] | f]; [| | destruct x | destruct m | destruct f];
    cbn [inst]; rewrite ?assign_with_const, ?word_exp_with_const, ?get_vars_with_const;
    try reflexivity;
    unfold get_var, mem_load, get_fp_var; stk_fields;
    repeat (rewrite ?mem_load_with_const; cbn [option_map];
            match goal with
            | |- context [match ?x with _ => _ end] => destruct x eqn:?; cbn beta iota zeta
            end);
    first [reflexivity | cbn [option_map] in *; congruence].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "dec_clock_const" *)
Theorem dec_clock_const : forall s z,
  ffi (dec_clock s) = ffi s /\
  use_alloc (dec_clock z) = use_alloc z /\
  use_store (dec_clock z) = use_store z /\
  use_stack (dec_clock z) = use_stack z /\
  stack (dec_clock z) = stack z /\
  store (dec_clock z) = store z /\
  code (dec_clock z) = code z /\
  data_buffer (dec_clock z) = data_buffer z /\
  code_buffer (dec_clock z) = code_buffer z /\
  fp_regs (dec_clock z) = fp_regs z /\
  be (dec_clock z) = be z /\
  gc_fun (dec_clock z) = gc_fun z /\
  memory (dec_clock z) = memory z /\
  mdomain (dec_clock z) = mdomain z /\
  sh_mdomain (dec_clock z) = sh_mdomain z /\
  bitmaps (dec_clock z) = bitmaps z /\
  stack_space (dec_clock z) = stack_space z /\
  compile (dec_clock z) = compile z /\
  compile_oracle (dec_clock z) = compile_oracle z.
Proof. intros; repeat split. Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "sh_mem_op_const" *)
Theorem sh_mem_op_const : forall op ad r s res t,
  sh_mem_op op ad r s = (res, t) ->
  clock t = clock s /\
  use_alloc t = use_alloc s /\
  use_store t = use_store s /\
  use_stack t = use_stack s /\
  code t = code s /\
  be t = be s /\
  gc_fun t = gc_fun s /\
  mdomain t = mdomain s /\
  sh_mdomain t = sh_mdomain s /\
  bitmaps t = bitmaps s /\
  compile t = compile s /\
  compile_oracle t = compile_oracle s.
Proof.
  intros op ad r s res t H.
  destruct op; cbn [sh_mem_op] in H;
    unfold sh_mem_load, sh_mem_store, sh_mem_load_byte, sh_mem_store_byte,
      sh_mem_load16, sh_mem_store16, sh_mem_load32, sh_mem_store32 in H;
    stk_split H; injection H as <- <-; stk_fields; repeat split; congruence.
Qed.

End Consts.

(** ** Invariants of [evaluate] *)

Lemma isPREFIX_trans2 {A} `{EqDecision A} (x y z : list A) :
  isPREFIX x y -> isPREFIX y z -> isPREFIX x z.
Proof. intros H1 H2; apply (isPREFIX_TRANS x y z); split; assumption. Qed.

Lemma isPREFIX_app_r {A} `{EqDecision A} (l m : list A) : isPREFIX l (l ++ m).
Proof.
  induction l as [|x l IH]; cbn; [reflexivity|].
  unfold is_true in *; rewrite IH, Bool.andb_true_r; apply bool_decide_spec; reflexivity.
Qed.

Lemma call_FFI_io {ffi_t} (st : ffi_state ffi_t) s conf bytes st' bytes' :
  call_FFI st s conf bytes = FFI_return st' bytes' ->
  isPREFIX (io_events st) (io_events st').
Proof.
  unfold call_FFI; destruct (negb _).
  - destruct (ffi_state_oracle st s _ conf bytes); [|discriminate].
    destruct (_ =? _); [|discriminate]. intros H; injection H as <- _; cbn.
    apply isPREFIX_app_r.
  - intros H; injection H as <- _; apply isPREFIX_REFL.
Qed.

Ltac stk_clk :=
  repeat match goal with H : (clock _ =? 0)%N = false |- _ => apply N.eqb_neq in H end;
  stk_fields.

Ltac stk_eval_lt := unfold eval_lt; cbn [fst snd psize STOP]; stk_clk; lia.

(** One step of an invariant proof: split the [match]es of [H] (an unfolded
    [evaluate]), and replace every recursive [evaluate] by the induction
    hypothesis and [evaluate_clock]. *)
Ltac inv_step IH H :=
  repeat first
    [ progress rewrite ?fix_clock_evaluate in H
    | match goal with
      | E : fix_clock _ (evaluate _) = _ |- _ => rewrite fix_clock_evaluate in E
      end
    | match goal with
      | E : evaluate (?p', ?s'') = (?r', ?t) |- _ =>
          let Hc := fresh "Hc" in let Hi := fresh "Hi" in
          pose proof (evaluate_clock p' s'' r' t E) as Hc;
          pose proof (IH (p', s'') ltac:(stk_eval_lt) r' t E) as Hi; clear E
      end
    | match type of H with
      | context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H
      end ].

Ltac inv_start IH H :=
  rewrite evaluate_eqn in H;
  match goal with p : prog _ |- _ => destruct p end;
  cbn [evaluate_body] in H; rewrite ?fix_clock_evaluate in H;
  inv_step IH H;
  repeat match goal with
         | E : (_, _) = (_, _) |- _ => injection E as <- <-
         | E : alloc _ _ = (_, _) |- _ => pose proof (alloc_const _ _ _ _ E); clear E
         | E : store_const_sem _ _ _ = (_, _) |- _ =>
             pose proof (store_const_sem_const _ _ _ _ _ E); clear E
         | E : inst _ _ = SOME _ |- _ => pose proof (inst_const _ _ _ E); clear E
         end;
  destruct_ands.

Section EvalProps.
Context {a : N} {c ffi_t : Type}.
Local Open Scope word_scope.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_consts" *)
Theorem evaluate_consts : forall (c0 : prog a) (s : state a c ffi_t) r s1,
  evaluate (c0, s) = (r, s1) ->
  use_alloc s1 = use_alloc s /\
  use_store s1 = use_store s /\
  use_stack s1 = use_stack s /\
  be s1 = be s /\
  gc_fun s1 = gc_fun s /\
  mdomain s1 = mdomain s /\
  sh_mdomain s1 = sh_mdomain s /\
  compile s1 = compile s.
Proof.
  enough (G : forall x : prog a * state a c ffi_t, forall r s1, evaluate x = (r, s1) ->
    let s := snd x in
    use_alloc s1 = use_alloc s /\ use_store s1 = use_store s /\ use_stack s1 = use_stack s /\
    be s1 = be s /\ gc_fun s1 = gc_fun s /\ mdomain s1 = mdomain s /\
    sh_mdomain s1 = sh_mdomain s /\ compile s1 = compile s)
    by (intros p s r s1 H; exact (G (p, s) r s1 H)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s1 H; cbn [snd].
  inv_start IH H;
  repeat match goal with
         | E : sh_mem_op _ _ _ _ = (_, _) |- _ => pose proof (sh_mem_op_const _ _ _ _ _ _ E); clear E
         end;
  stk_fields; destruct_ands; repeat split; congruence.
Qed.

(** The code/bitmap/oracle relation of [evaluate_code_bitmaps]. *)
Definition cb_rel (o1 : N -> c * (list (N * prog a) * list (word a))) (cd1 : sptree.spt (prog a))
    (b1 : list (word a)) o2 cd2 b2 : Prop :=
  exists n,
    o2 = shift_seq n o1 /\
    cd2 = FOLDL sptree.union cd1 (MAP (sptree.fromAList ∘ FST ∘ SND) (GENLIST o1 n)) /\
    b2 = b1 ++ FLAT (MAP (SND ∘ SND) (GENLIST o1 n)).

Lemma cb_refl o cd b : cb_rel o cd b o cd b.
Proof.
  exists 0; split; [|split; [reflexivity|cbn; rewrite app_nil_r; reflexivity]].
  apply functional_extensionality; intros i; unfold shift_seq; rewrite N.add_0_r; reflexivity.
Qed.

Lemma cb_trans o1 cd1 b1 o2 cd2 b2 o3 cd3 b3 :
  cb_rel o1 cd1 b1 o2 cd2 b2 -> cb_rel o2 cd2 b2 o3 cd3 b3 -> cb_rel o1 cd1 b1 o3 cd3 b3.
Proof.
  intros [n1 [-> [-> ->]]] [n2 [-> [-> ->]]]. exists (n2 + n1)%N.
  rewrite GENLIST_APPEND. unfold shift_seq.
  split; [|split].
  - apply functional_extensionality; intros i; f_equal; lia.
  - rewrite map_app, !FOLDL_fold_left, fold_left_app; reflexivity.
  - rewrite map_app, concat_app, app_assoc; reflexivity.
Qed.

Lemma cb_install (o : N -> c * (list (N * prog a) * list (word a))) cd b cfg progs bm :
  o 0 = (cfg, (progs, bm)) ->
  cb_rel o cd b (shift_seq 1 o) (sptree.union cd (sptree.fromAList progs)) (b ++ bm).
Proof.
  intros E; exists 1; split; [reflexivity|].
  change (GENLIST o 1) with [o 0]. rewrite E; cbn. rewrite app_nil_r; split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_code_bitmaps" *)
Theorem evaluate_code_bitmaps : forall (c0 : prog a) (s : state a c ffi_t) r s1,
  evaluate (c0, s) = (r, s1) ->
  exists n,
    compile_oracle s1 = shift_seq n (compile_oracle s) /\
    code s1 = FOLDL sptree.union (code s)
                (MAP (sptree.fromAList ∘ FST ∘ SND) (GENLIST (compile_oracle s) n)) /\
    bitmaps s1 = bitmaps s ++ FLAT (MAP (SND ∘ SND) (GENLIST (compile_oracle s) n)).
Proof.
  enough (G : forall x : prog a * state a c ffi_t, forall r s1, evaluate x = (r, s1) ->
    cb_rel (compile_oracle (snd x)) (code (snd x)) (bitmaps (snd x))
           (compile_oracle s1) (code s1) (bitmaps s1))
    by (intros p s r s1 H; exact (G (p, s) r s1 H)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s1 H; cbn [snd].
  inv_start IH H;
  repeat match goal with
         | E : sh_mem_op _ _ _ _ = (_, _) |- _ => pose proof (sh_mem_op_const _ _ _ _ _ _ E); clear E
         end;
  stk_fields; destruct_ands;
  repeat match goal with
         | E : compile_oracle ?t = _ |- _ => rewrite E; clear E
         | E : code ?t = _ |- _ => rewrite E; clear E
         | E : bitmaps ?t = _ |- _ => rewrite E; clear E
         end;
  eauto using cb_refl, cb_trans, cb_install.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_mono" *)
Theorem evaluate_mono : forall (c0 : prog a) (s : state a c ffi_t) r s1,
  evaluate (c0, s) = (r, s1) ->
  isPREFIX (bitmaps s) (bitmaps s1) /\ sptree.subspt (code s) (code s1).
Proof.
  intros c0 s r s1 H; destruct (evaluate_code_bitmaps c0 s r s1 H) as [n [_ [E1 E2]]].
  rewrite E1, E2; split; [apply isPREFIX_app_r|apply sptree.subspt_FOLDL_union].
Qed.

Lemma sh_mem_op_io op r ad (s : state a c ffi_t) res t :
  sh_mem_op op r ad s = (res, t) -> isPREFIX (io_events (ffi s)) (io_events (ffi t)).
Proof.
  intros H; destruct op; cbn [sh_mem_op] in H;
    unfold sh_mem_load, sh_mem_store, sh_mem_load_byte, sh_mem_store_byte,
      sh_mem_load16, sh_mem_store16, sh_mem_load32, sh_mem_store32 in H;
    stk_split H; injection H as <- <-; stk_fields;
    first [apply isPREFIX_REFL | eapply call_FFI_io; eassumption].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_io_events_mono" *)
Theorem evaluate_io_events_mono : forall (exps : prog a) (s1 : state a c ffi_t) res s2,
  evaluate (exps, s1) = (res, s2) ->
  isPREFIX (io_events (ffi s1)) (io_events (ffi s2)).
Proof.
  enough (G : forall x : prog a * state a c ffi_t, forall r s1, evaluate x = (r, s1) ->
    isPREFIX (io_events (ffi (snd x))) (io_events (ffi s1)))
    by (intros p s r s1 H; exact (G (p, s) r s1 H)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s1 H; cbn [snd].
  inv_start IH H;
  repeat match goal with
         | E : sh_mem_op _ _ _ _ = (_, _) |- _ => pose proof (sh_mem_op_io _ _ _ _ _ _ E); clear E
         | E : call_FFI _ _ _ _ = FFI_return _ _ |- _ => pose proof (call_FFI_io _ _ _ _ _ _ E); clear E
         end;
  stk_fields;
  repeat match goal with
         | E : ffi ?t = _ |- _ => rewrite E in *; clear E
         end;
  eauto using isPREFIX_REFL, isPREFIX_trans2.
Qed.

End EvalProps.

(** ** Syntactic properties *)

Section Syntax.
Context {a : N}.
Local Open Scope word_scope.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "extract_labels_def" *)
Fixpoint extract_labels (p : prog a) : list (N * N) :=
  match p with
  | Call ret dest h =>
      match ret with
      | NONE => []
      | SOME (ret_handler, (_, (l1, l2))) =>
          let ret_rest := extract_labels ret_handler in
          match h with
          | NONE => [(l1, l2)] ++ ret_rest
          | SOME (prog0, (l1', l2')) =>
              let h_rest := extract_labels prog0 in
              [(l1, l2); (l1', l2')] ++ ret_rest ++ h_rest
          end
      end
  | Loop s1 => extract_labels s1
  | Seq s1 s2 => extract_labels s1 ++ extract_labels s2
  | If cmp r1 ri e2 e3 => extract_labels e2 ++ extract_labels e3
  | _ => []
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "addr_ok_def" *)
Definition addr_ok (op : memop) (ad0 : addr a) (c : asm_config a) : bool :=
  let '(Addr ad w) := ad0 in
  reg_ok ad c &&
  (if MEM op [Load; Store; Load32; Store32]
   then addr_offset_ok c w
   else if MEM op [Load16; Store16]
   then hw_offset_ok c w && negb (bool_decide (ISA c = Ag32)) else byte_offset_ok c w).

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "stack_asm_ok_def" *)
Fixpoint stack_asm_ok (c : asm_config a) (p : prog a) : bool :=
  match p with
  | Inst i => inst_ok i c
  | ShMemOp op r ad => reg_ok r c && addr_ok op ad c
  | CodeBufferWrite r1 r2 =>
      (r1 <? reg_count c)%N && (r2 <? reg_count c)%N &&
      negb (MEM r1 (avoid_regs c)) && negb (MEM r2 (avoid_regs c))
  | Seq p1 p2 => stack_asm_ok c p1 && stack_asm_ok c p2
  | If cmp n r p p' => stack_asm_ok c p && stack_asm_ok c p'
  | Loop p => stack_asm_ok c p
  | Raise n => (n <? reg_count c)%N && negb (MEM n (avoid_regs c))
  | Return n => (n <? reg_count c)%N && negb (MEM n (avoid_regs c))
  | Call r tar h =>
      match tar with inr r => (r <? reg_count c)%N && negb (MEM r (avoid_regs c)) | _ => true end &&
      match r with
      | SOME (p, _) =>
          stack_asm_ok c p &&
          match h with
          | SOME (p', _) => stack_asm_ok c p'
          | _ => true
          end
      | _ => true
      end
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "reg_name_def" *)
Definition reg_name (r : N) (c : asm_config a) : bool :=
  (r <? reg_count c - LENGTH (avoid_regs c))%N.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "reg_imm_name_def" *)
Definition reg_imm_name (b : binop + cmp) (ri : reg_imm a) (c : asm_config a) : bool :=
  match ri with
  | Reg r => reg_name r c
  | Imm w => valid_imm c b w
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "arith_name_def" *)
Definition arith_name (x : arith a) (c : asm_config a) : bool :=
  match x with
  | Binop b r1 r2 ri =>
      implb (two_reg_arith c)
        (bool_decide (r1 = r2) || bool_decide (b = Or) && bool_decide (ri = Reg r2)) &&
      reg_name r1 c && reg_name r2 c && reg_imm_name (inl b) ri c
  | Shift l r1 r2 (Imm i) =>
      implb (two_reg_arith c) (bool_decide (r1 = r2)) && reg_name r1 c && reg_name r2 c &&
      implb (bool_decide (i = n2w 0)) (bool_decide (l = ast.Lsl)) && (w2n i <? dimindex a)%N
  | Shift l r1 r2 (Reg r3) =>
      implb (two_reg_arith c) (bool_decide (r1 = r2)) && reg_name r1 c &&
      reg_name r2 c && reg_name r3 c && implb (bool_decide (ISA c = x86_64)) (bool_decide (r3 = 4%N))
  | Div r1 r2 r3 =>
      reg_name r1 c && reg_name r2 c && reg_name r3 c &&
      MEM (ISA c) [ARMv8; MIPS; RISC_V]
  | LongMul r1 r2 r3 r4 =>
      reg_name r1 c && reg_name r2 c && reg_name r3 c && reg_name r4 c &&
      implb (bool_decide (ISA c = x86_64))
        (bool_decide (r1 = 3%N) && bool_decide (r2 = 0%N) && bool_decide (r3 = 0%N)) &&
      implb (bool_decide (ISA c = ARMv7)) (negb (bool_decide (r1 = r2))) &&
      implb (bool_decide (ISA c = ARMv8) || bool_decide (ISA c = RISC_V) || bool_decide (ISA c = Ag32))
        (negb (bool_decide (r1 = r3)) && negb (bool_decide (r1 = r4)))
  | LongDiv r1 r2 r3 r4 r5 =>
      bool_decide (ISA c = x86_64) && bool_decide (r1 = 0%N) && bool_decide (r2 = 3%N) &&
      bool_decide (r3 = 3%N) && bool_decide (r4 = 0%N) && reg_name r5 c
  | AddCarry r1 r2 r3 r4 =>
      implb (two_reg_arith c) (bool_decide (r1 = r2)) && reg_name r1 c && reg_name r2 c &&
      reg_name r3 c && reg_name r4 c &&
      implb (bool_decide (ISA c = MIPS) || bool_decide (ISA c = RISC_V))
        (negb (bool_decide (r1 = r3)) && negb (bool_decide (r1 = r4)))
  | AddOverflow r1 r2 r3 r4 =>
      implb (two_reg_arith c) (bool_decide (r1 = r2)) && reg_name r1 c && reg_name r2 c &&
      reg_name r3 c && reg_name r4 c &&
      implb (bool_decide (ISA c = MIPS) || bool_decide (ISA c = RISC_V))
        (negb (bool_decide (r1 = r3)))
  | SubOverflow r1 r2 r3 r4 =>
      implb (two_reg_arith c) (bool_decide (r1 = r2)) && reg_name r1 c && reg_name r2 c &&
      reg_name r3 c && reg_name r4 c &&
      implb (bool_decide (ISA c = MIPS) || bool_decide (ISA c = RISC_V))
        (negb (bool_decide (r1 = r3)))
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "fp_name_def" *)
Definition fp_name (x : fp) (c : asm_config a) : bool :=
  match x with
  | FPLess r d1 d2 => reg_name r c && fp_reg_ok d1 c && fp_reg_ok d2 c
  | FPLessEqual r d1 d2 => reg_name r c && fp_reg_ok d1 c && fp_reg_ok d2 c
  | FPEqual r d1 d2 => reg_name r c && fp_reg_ok d1 c && fp_reg_ok d2 c
  | FPAbs d1 d2 =>
      implb (two_reg_arith c) (negb (bool_decide (d1 = d2))) && fp_reg_ok d1 c && fp_reg_ok d2 c
  | FPNeg d1 d2 =>
      implb (two_reg_arith c) (negb (bool_decide (d1 = d2))) && fp_reg_ok d1 c && fp_reg_ok d2 c
  | FPSqrt d1 d2 => fp_reg_ok d1 c && fp_reg_ok d2 c
  | FPAdd d1 d2 d3 =>
      implb (two_reg_arith c) (bool_decide (d1 = d2)) &&
      fp_reg_ok d1 c && fp_reg_ok d2 c && fp_reg_ok d3 c
  | FPSub d1 d2 d3 =>
      implb (two_reg_arith c) (bool_decide (d1 = d2)) &&
      fp_reg_ok d1 c && fp_reg_ok d2 c && fp_reg_ok d3 c
  | FPMul d1 d2 d3 =>
      implb (two_reg_arith c) (bool_decide (d1 = d2)) &&
      fp_reg_ok d1 c && fp_reg_ok d2 c && fp_reg_ok d3 c
  | FPDiv d1 d2 d3 =>
      implb (two_reg_arith c) (bool_decide (d1 = d2)) &&
      fp_reg_ok d1 c && fp_reg_ok d2 c && fp_reg_ok d3 c
  | FPFma d1 d2 d3 =>
      bool_decide (ISA c = ARMv7) && (2 <? fp_reg_count c)%N &&
      fp_reg_ok d1 c && fp_reg_ok d2 c && fp_reg_ok d3 c
  | FPMov d1 d2 => fp_reg_ok d1 c && fp_reg_ok d2 c
  | FPMovToReg r1 r2 d =>
      reg_name r1 c &&
      implb (bool_decide (dimindex a = 32%N)) (negb (bool_decide (r1 = r2)) && reg_name r2 c) &&
      fp_reg_ok d c
  | FPMovFromReg d r1 r2 =>
      reg_name r1 c &&
      implb (bool_decide (dimindex a = 32%N)) (negb (bool_decide (r1 = r2)) && reg_name r2 c) &&
      fp_reg_ok d c
  | FPToInt d1 d2 => fp_reg_ok d1 c && fp_reg_ok d2 c
  | FPFromInt d1 d2 => fp_reg_ok d1 c && fp_reg_ok d2 c
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "addr_name_def" *)
Definition addr_name (m : memop) (ad0 : addr a) (c : asm_config a) : bool :=
  let '(Addr r w) := ad0 in
  reg_name r c &&
  (if MEM m [Load; Store; Load32; Store32]
   then addr_offset_ok c w
   else if MEM m [Load16; Store16]
   then hw_offset_ok c w && negb (bool_decide (ISA c = Ag32))
   else byte_offset_ok c w).

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "inst_name_def" *)
Definition inst_name (c : asm_config a) (i : asm.inst a) : bool :=
  match i with
  | Const r w => reg_name r c
  | Mem m r ad => reg_name r c && addr_name m ad c
  | Arith x => arith_name x c
  | FP f => fp_name f c
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "stack_asm_name_def" *)
Fixpoint stack_asm_name (c : asm_config a) (p : prog a) : bool :=
  match p with
  | Inst i => inst_name c i
  | OpCurrHeap b r1 r2 => implb (two_reg_arith c) (bool_decide (r1 = r2)) && reg_name r1 c && reg_name r2 c
  | ShMemOp op r ad => reg_name r c && addr_name op ad c
  | CodeBufferWrite r1 r2 => reg_name r1 c && reg_name r2 c
  | DataBufferWrite r1 r2 => reg_name r1 c && reg_name r2 c
  | Seq p1 p2 => stack_asm_name c p1 && stack_asm_name c p2
  | If cmp n r p p' => stack_asm_name c p && stack_asm_name c p'
  | Loop p => stack_asm_name c p
  | Raise n => reg_name n c
  | Return n => reg_name n c
  | Call r tar h =>
      match tar with inr r => reg_name r c | _ => true end &&
      match r with
      | SOME (p, _) =>
          stack_asm_name c p &&
          match h with
          | SOME (p', _) => stack_asm_name c p'
          | _ => true
          end
      | _ => true
      end
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "fixed_names_def" *)
Definition fixed_names (names : sptree.spt N) (c : asm_config a) : bool :=
  if bool_decide (ISA c = x86_64) then
    bool_decide (stack_names.find_name names 3 = 2%N) &&
    bool_decide (stack_names.find_name names 4 = 1%N) &&
    bool_decide (stack_names.find_name names 0 = 0%N)
  else true.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "stack_asm_remove_def" *)
Fixpoint stack_asm_remove (c : asm_config a) (p : prog a) : bool :=
  match p with
  | Get n s => reg_name n c
  | OpCurrHeap binop v src => reg_name v c && reg_name src c
  | Set_ s n => reg_name n c
  | StackStore n n0 => reg_name n c
  | StackStoreAny n n0 => reg_name n c && reg_name n0 c
  | StackLoad n n0 => reg_name n c
  | StackLoadAny n n0 => reg_name n c && reg_name n0 c
  | StackGetSize n => reg_name n c
  | StackSetSize n => reg_name n c
  | BitmapLoad n n0 => reg_name n c && reg_name n0 c
  | StoreConsts n n0 _ => reg_name n c && reg_name n0 c
  | Seq p1 p2 => stack_asm_remove c p1 && stack_asm_remove c p2
  | If cmp n r p p' => stack_asm_remove c p && stack_asm_remove c p'
  | Loop p => stack_asm_remove c p
  | Call r tar h =>
      match r with
      | SOME (p, _) =>
          stack_asm_remove c p &&
          match h with
          | SOME (p', _) => stack_asm_remove c p'
          | _ => true
          end
      | _ => true
      end
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "alloc_arg_def" *)
Fixpoint alloc_arg (p : prog a) : bool :=
  match p with
  | Alloc v => bool_decide (v = 1%N)
  | Seq p1 p2 => alloc_arg p1 && alloc_arg p2
  | If c r ri p1 p2 => alloc_arg p1 && alloc_arg p2
  | Loop p1 => alloc_arg p1
  | Call x1 _ x2 =>
      match x1 with SOME (y, _) => alloc_arg y | NONE => true end &&
      match x2 with SOME (y, _) => alloc_arg y | NONE => true end
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "reg_bound_exp_def" *)
Fixpoint reg_bound_exp (e : wordLang.exp a) (k : N) : bool :=
  match e with
  | wordLang.Var n => (n <? k)%N
  | wordLang.Load e => reg_bound_exp e k
  | wordLang.Shift _ e1 e2 => reg_bound_exp e1 k && reg_bound_exp e2 k
  | wordLang.Lookup _ => false
  | wordLang.Op _ es => EVERY (fun e => reg_bound_exp e k) es
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "reg_bound_inst_def" *)
Definition reg_bound_inst (i : asm.inst a) (k : N) : bool :=
  match i with
  | Mem _ n (Addr ad _) => (n <? k)%N && (ad <? k)%N
  | Const n _ => (n <? k)%N
  | Arith (Shift _ n r2 ri) =>
      (r2 <? k)%N && (n <? k)%N && match ri with Reg r => (r <? k)%N | _ => true end
  | Arith (Binop _ n r2 ri) =>
      (r2 <? k)%N && (n <? k)%N && match ri with Reg r1 => (r1 <? k)%N | _ => true end
  | Arith (Div r1 r2 r3) => (r1 <? k)%N && (r2 <? k)%N && (r3 <? k)%N
  | Arith (AddCarry r1 r2 r3 r4) => (r1 <? k)%N && (r2 <? k)%N && (r3 <? k)%N && (r4 <? k)%N
  | Arith (AddOverflow r1 r2 r3 r4) => (r1 <? k)%N && (r2 <? k)%N && (r3 <? k)%N && (r4 <? k)%N
  | Arith (SubOverflow r1 r2 r3 r4) => (r1 <? k)%N && (r2 <? k)%N && (r3 <? k)%N && (r4 <? k)%N
  | Arith (LongMul r1 r2 r3 r4) => (r1 <? k)%N && (r2 <? k)%N && (r3 <? k)%N && (r4 <? k)%N
  | Arith (LongDiv r1 r2 r3 r4 r5) =>
      (r1 <? k)%N && (r2 <? k)%N && (r3 <? k)%N && (r4 <? k)%N && (r5 <? k)%N
  | FP (FPLess r f1 f2) => (r <? k)%N
  | FP (FPLessEqual r f1 f2) => (r <? k)%N
  | FP (FPEqual r f1 f2) => (r <? k)%N
  | FP (FPMovToReg r1 r2 d) => (r1 <? k)%N && (r2 <? k)%N
  | FP (FPMovFromReg d r1 r2) => (r1 <? k)%N && (r2 <? k)%N
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "reg_bound_def" *)
Fixpoint reg_bound (p : prog a) (k : N) : bool :=
  match p with
  | stackLang.Halt v1 => (v1 <? k)%N
  | Raise v1 => (v1 <? k)%N
  | Get v1 n => (v1 <? k)%N
  | OpCurrHeap op v1 v2 => (v1 <? k)%N && (v2 <? k)%N
  | Set_ n v1 => (v1 <? k)%N && negb (bool_decide (n = BitmapBase))
  | LocValue v1 l1 l2 => (v1 <? k)%N
  | StoreConsts t1 t2 _ => (3 <? k)%N && (t1 <? k)%N && (t2 <? k)%N
  | Return v1 => (v1 <? k)%N
  | JumpLower v1 v2 dest => (v1 <? k)%N && (v2 <? k)%N
  | Seq p1 p2 => reg_bound p1 k && reg_bound p2 k
  | If c r ri p1 p2 =>
      (r <? k)%N && match ri with Reg n => (n <? k)%N | _ => true end &&
      reg_bound p1 k && reg_bound p2 k
  | Loop p1 => reg_bound p1 k
  | FFI ffi_index ptr' len' ptr2' len2' ret' =>
      (ptr' <? k)%N && (len' <? k)%N && (ptr2' <? k)%N && (len2' <? k)%N && (ret' <? k)%N
  | Call x1 dest x2 =>
      match dest with inr i => (i <? k)%N | _ => true end &&
      match x1 with
      | NONE => true
      | SOME (y, (r, _)) =>
          reg_bound y k && (r <? k)%N &&
          match x2 with SOME (y, _) => reg_bound y k | NONE => true end
      end
  | Install ptr len dptr dlen ret =>
      (ptr <? k)%N && (len <? k)%N && (dptr <? k)%N && (dlen <? k)%N && (ret <? k)%N
  | ShMemOp op r (Addr ad _) => (r <? k)%N && (ad <? k)%N
  | CodeBufferWrite r1 r2 => (r1 <? k)%N && (r2 <? k)%N
  | DataBufferWrite r1 r2 => (r1 <? k)%N && (r2 <? k)%N
  | BitmapLoad r v => (r <? k)%N && (v <? k)%N
  | Inst i => reg_bound_inst i k
  | StackStore r _ => (r <? k)%N
  | StackSetSize r => (r <? k)%N
  | StackGetSize r => (r <? k)%N
  | StackLoad r n => (r <? k)%N
  | StackLoadAny r r2 => (r <? k)%N && (r2 <? k)%N
  | StackStoreAny r r2 => (r <? k)%N && (r2 <? k)%N
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "call_args_def" *)
Fixpoint call_args (p : prog a) (ptr len ptr2 len2 ret : N) : bool :=
  match p with
  | Seq p1 p2 => call_args p1 ptr len ptr2 len2 ret && call_args p2 ptr len ptr2 len2 ret
  | If c r ri p1 p2 => call_args p1 ptr len ptr2 len2 ret && call_args p2 ptr len ptr2 len2 ret
  | Loop p1 => call_args p1 ptr len ptr2 len2 ret
  | stackLang.Halt n => bool_decide (n = ptr)
  | FFI ffi_index ptr' len' ptr2' len2' ret' =>
      bool_decide (ptr' = ptr) && bool_decide (len' = len) && bool_decide (ptr2' = ptr2) &&
      bool_decide (len2' = len2) && bool_decide (ret' = ret)
  | Call x1 _ x2 =>
      match x1 with
      | NONE => true
      | SOME (y, (r, _)) =>
          call_args y ptr len ptr2 len2 ret && bool_decide (r = ret) &&
          match x2 with SOME (y, _) => call_args y ptr len ptr2 len2 ret | NONE => true end
      end
  | Install ptr' len' _ _ ret' =>
      bool_decide (ptr' = ptr) && bool_decide (len' = len) && bool_decide (ret' = ret)
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "stack_get_handler_labels_def" *)
Fixpoint stack_get_handler_labels (n : N) (p : prog a) : N * N -> Prop :=
  match p with
  | Call r d h =>
      match r with
      | SOME (x, _) =>
          stack_get_handler_labels n x UNION
          match h with
          | SOME (x, (l1, l2)) =>
              (if decide (l1 = n) then (l1, l2) INSERT {} else {}) UNION
              stack_get_handler_labels n x
          | _ => {}
          end
      | _ => {}
      end
  | Seq p1 p2 => stack_get_handler_labels n p1 UNION stack_get_handler_labels n p2
  | If _ _ _ p1 p2 => stack_get_handler_labels n p1 UNION stack_get_handler_labels n p2
  | Loop p => stack_get_handler_labels n p
  | _ => {}
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "get_code_labels_def" *)
Fixpoint get_code_labels (p : prog a) : N * N -> Prop :=
  match p with
  | Call r d h =>
      match d with inl x => (x, 0%N) INSERT {} | _ => {} end UNION
      match r with SOME (x, _) => get_code_labels x | _ => {} end UNION
      match h with SOME (x, _) => get_code_labels x | _ => {} end
  | Seq p1 p2 => get_code_labels p1 UNION get_code_labels p2
  | If _ _ _ p1 p2 => get_code_labels p1 UNION get_code_labels p2
  | Loop p => get_code_labels p
  | JumpLower _ _ t => (t, 0%N) INSERT {}
  | RawCall t => (t, 1%N) INSERT {}
  | LocValue _ l1 l2 => (l1, l2) INSERT {}
  | StoreConsts _ _ (SOME l) => (l, 0%N) INSERT {}
  | _ => {}
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "stack_good_code_labels_def" *)
Definition stack_good_code_labels (p : list (N * prog a)) (elabs : N -> Prop) : Prop :=
  BIGUNION (IMAGE get_code_labels (set (MAP SND p))) SUBSET
  BIGUNION (set (MAP (fun '(n, pp) => stack_get_handler_labels n pp) p)) UNION
  IMAGE (fun n => (n, 0%N)) (set (MAP FST p)) UNION IMAGE (fun n => (n, 0%N)) elabs UNION
  IMAGE (fun n => (n, 1%N)) (set (MAP FST p)) UNION IMAGE (fun n => (n, 1%N)) elabs.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "stack_good_handler_labels_def" *)
Definition stack_good_handler_labels (p : list (N * prog a)) : Prop :=
  restrict_nonzero (BIGUNION (IMAGE get_code_labels (set (MAP SND p)))) SUBSET
  BIGUNION (set (MAP (fun '(n, pp) => stack_get_handler_labels n pp) p)) UNION
  IMAGE (fun n => (n, 1%N)) (set (MAP FST p)).

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "no_install_def" *)
Fixpoint no_install (p : prog a) : bool :=
  match p with
  | Call r d h =>
      match r with SOME (x, _) => no_install x | _ => true end &&
      match h with SOME (x, _) => no_install x | _ => true end
  | Seq p1 p2 => no_install p1 && no_install p2
  | If _ _ _ p1 p2 => no_install p1 && no_install p2
  | Loop p => no_install p
  | Install _ _ _ _ _ => false
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "no_shmemop_def" *)
Fixpoint no_shmemop (p : prog a) : bool :=
  match p with
  | Call r d h =>
      match r with SOME (x, _) => no_shmemop x | _ => true end &&
      match h with SOME (x, _) => no_shmemop x | _ => true end
  | Seq p1 p2 => no_shmemop p1 && no_shmemop p2
  | If _ _ _ p1 p2 => no_shmemop p1 && no_shmemop p2
  | Loop p => no_shmemop p
  | ShMemOp _ _ _ => false
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "clock_neutral_def" *)
Fixpoint clock_neutral (p : prog a) : bool :=
  match p with
  | Seq p1 p2 => clock_neutral p1 && clock_neutral p2
  | LocValue _ _ _ => true
  | stackLang.Halt _ => true
  | Inst _ => true
  | Skip => true
  | If _ _ _ p1 p2 => clock_neutral p1 && clock_neutral p2
  | _ => false
  end.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "find_code_IMP_get_labels" *)
Theorem find_code_IMP_get_labels : forall d (r : fmap N (word_loc a)) code0 e,
  find_code d r code0 = SOME e -> get_labels e SUBSET loc_check code0.
Proof.
  intros d r code0 e H [l1 l2] Hl.
  assert (Hn : exists n, sptree.lookup n code0 = SOME e).
  { destruct d as [n|n]; cbn in H; [eauto|].
    destruct (FLOOKUP r n) as [[w|n1 n2]|]; try discriminate.
    destruct (n2 =? 0)%N; [eauto|discriminate]. }
  destruct Hn as [n Hn]. right; exists n, e; split; assumption.
Qed.

End Syntax.

(** ** Adding clock *)

Section AddClock.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

Lemma regs_set_clock k s : regs (set_clock k s) = regs s. Proof. reflexivity. Qed.
Lemma fp_regs_set_clock k s : fp_regs (set_clock k s) = fp_regs s. Proof. reflexivity. Qed.
Lemma store_set_clock k s : store (set_clock k s) = store s. Proof. reflexivity. Qed.
Lemma stack_set_clock k s : stack (set_clock k s) = stack s. Proof. reflexivity. Qed.
Lemma stack_space_set_clock k s : stack_space (set_clock k s) = stack_space s. Proof. reflexivity. Qed.
Lemma memory_set_clock k s : memory (set_clock k s) = memory s. Proof. reflexivity. Qed.
Lemma mdomain_set_clock k s : mdomain (set_clock k s) = mdomain s. Proof. reflexivity. Qed.
Lemma sh_mdomain_set_clock k s : sh_mdomain (set_clock k s) = sh_mdomain s. Proof. reflexivity. Qed.
Lemma bitmaps_set_clock k s : bitmaps (set_clock k s) = bitmaps s. Proof. reflexivity. Qed.
Lemma compile_set_clock k s : compile (set_clock k s) = compile s. Proof. reflexivity. Qed.
Lemma compile_oracle_set_clock k s : compile_oracle (set_clock k s) = compile_oracle s. Proof. reflexivity. Qed.
Lemma code_buffer_set_clock k s : code_buffer (set_clock k s) = code_buffer s. Proof. reflexivity. Qed.
Lemma data_buffer_set_clock k s : data_buffer (set_clock k s) = data_buffer s. Proof. reflexivity. Qed.
Lemma gc_fun_set_clock k s : gc_fun (set_clock k s) = gc_fun s. Proof. reflexivity. Qed.
Lemma use_stack_set_clock k s : use_stack (set_clock k s) = use_stack s. Proof. reflexivity. Qed.
Lemma use_store_set_clock k s : use_store (set_clock k s) = use_store s. Proof. reflexivity. Qed.
Lemma use_alloc_set_clock k s : use_alloc (set_clock k s) = use_alloc s. Proof. reflexivity. Qed.
Lemma code_set_clock k s : code (set_clock k s) = code s. Proof. reflexivity. Qed.
Lemma ffi_set_clock k s : ffi (set_clock k s) = ffi s. Proof. reflexivity. Qed.
Lemma ffi_save_regs_set_clock k s : ffi_save_regs (set_clock k s) = ffi_save_regs s. Proof. reflexivity. Qed.
Lemma be_set_clock k s : be (set_clock k s) = be s. Proof. reflexivity. Qed.
Lemma clock_set_clock k s : clock (set_clock k s) = k. Proof. reflexivity. Qed.
Lemma set_clock_set_clock k k' s : set_clock k (set_clock k' s) = set_clock k s. Proof. reflexivity. Qed.
Lemma set_regs_set_clock v k s : set_regs v (set_clock k s) = set_clock k (set_regs v s). Proof. reflexivity. Qed.
Lemma set_fp_regs_set_clock v k s : set_fp_regs v (set_clock k s) = set_clock k (set_fp_regs v s). Proof. reflexivity. Qed.
Lemma set_store_fld_set_clock v k s : set_store_fld v (set_clock k s) = set_clock k (set_store_fld v s). Proof. reflexivity. Qed.
Lemma set_stack_set_clock v k s : set_stack v (set_clock k s) = set_clock k (set_stack v s). Proof. reflexivity. Qed.
Lemma set_stack_space_set_clock v k s : set_stack_space v (set_clock k s) = set_clock k (set_stack_space v s). Proof. reflexivity. Qed.
Lemma set_memory_set_clock v k s : set_memory v (set_clock k s) = set_clock k (set_memory v s). Proof. reflexivity. Qed.
Lemma set_mdomain_set_clock v k s : set_mdomain v (set_clock k s) = set_clock k (set_mdomain v s). Proof. reflexivity. Qed.
Lemma set_sh_mdomain_set_clock v k s : set_sh_mdomain v (set_clock k s) = set_clock k (set_sh_mdomain v s). Proof. reflexivity. Qed.
Lemma set_bitmaps_set_clock v k s : set_bitmaps v (set_clock k s) = set_clock k (set_bitmaps v s). Proof. reflexivity. Qed.
Lemma set_compile_set_clock v k s : set_compile v (set_clock k s) = set_clock k (set_compile v s). Proof. reflexivity. Qed.
Lemma set_compile_oracle_set_clock v k s : set_compile_oracle v (set_clock k s) = set_clock k (set_compile_oracle v s). Proof. reflexivity. Qed.
Lemma set_code_buffer_set_clock v k s : set_code_buffer v (set_clock k s) = set_clock k (set_code_buffer v s). Proof. reflexivity. Qed.
Lemma set_data_buffer_set_clock v k s : set_data_buffer v (set_clock k s) = set_clock k (set_data_buffer v s). Proof. reflexivity. Qed.
Lemma set_gc_fun_set_clock v k s : set_gc_fun v (set_clock k s) = set_clock k (set_gc_fun v s). Proof. reflexivity. Qed.
Lemma set_use_stack_set_clock v k s : set_use_stack v (set_clock k s) = set_clock k (set_use_stack v s). Proof. reflexivity. Qed.
Lemma set_use_store_set_clock v k s : set_use_store v (set_clock k s) = set_clock k (set_use_store v s). Proof. reflexivity. Qed.
Lemma set_use_alloc_set_clock v k s : set_use_alloc v (set_clock k s) = set_clock k (set_use_alloc v s). Proof. reflexivity. Qed.
Lemma set_code_set_clock v k s : set_code v (set_clock k s) = set_clock k (set_code v s). Proof. reflexivity. Qed.
Lemma set_ffi_set_clock v k s : set_ffi v (set_clock k s) = set_clock k (set_ffi v s). Proof. reflexivity. Qed.
Lemma set_ffi_save_regs_set_clock v k s : set_ffi_save_regs v (set_clock k s) = set_clock k (set_ffi_save_regs v s). Proof. reflexivity. Qed.
Lemma set_be_set_clock v k s : set_be v (set_clock k s) = set_clock k (set_be v s). Proof. reflexivity. Qed.
Lemma set_var_set_clock v x k s : set_var v x (set_clock k s) = set_clock k (set_var v x s). Proof. reflexivity. Qed.
Lemma set_fp_var_set_clock v x k s : set_fp_var v x (set_clock k s) = set_clock k (set_fp_var v x s). Proof. reflexivity. Qed.
Lemma set_store_set_clock v x k s : set_store v x (set_clock k s) = set_clock k (set_store v x s). Proof. reflexivity. Qed.
Lemma empty_env_set_clock k s : empty_env (set_clock k s) = set_clock k (empty_env s). Proof. reflexivity. Qed.
Lemma unset_var_set_clock v k s : unset_var v (set_clock k s) = set_clock k (unset_var v s). Proof. reflexivity. Qed.
Lemma get_var_set_clock v k s : get_var v (set_clock k s) = get_var v s. Proof. reflexivity. Qed.
Lemma dec_clock_eq s : dec_clock s = set_clock (clock s - 1) s. Proof. reflexivity. Qed.

End AddClock.

Create Rewrite HintDb stkc.
Global Hint Rewrite @regs_set_clock @fp_regs_set_clock @store_set_clock @stack_set_clock @stack_space_set_clock @memory_set_clock @mdomain_set_clock @sh_mdomain_set_clock @bitmaps_set_clock @compile_set_clock @compile_oracle_set_clock @code_buffer_set_clock @data_buffer_set_clock @gc_fun_set_clock @use_stack_set_clock @use_store_set_clock @use_alloc_set_clock @code_set_clock @ffi_set_clock @ffi_save_regs_set_clock @be_set_clock @clock_set_clock @set_clock_set_clock @set_regs_set_clock @set_fp_regs_set_clock @set_store_fld_set_clock @set_stack_set_clock @set_stack_space_set_clock @set_memory_set_clock @set_mdomain_set_clock @set_sh_mdomain_set_clock @set_bitmaps_set_clock @set_compile_set_clock @set_compile_oracle_set_clock @set_code_buffer_set_clock @set_data_buffer_set_clock @set_gc_fun_set_clock @set_use_stack_set_clock @set_use_store_set_clock @set_use_alloc_set_clock @set_code_set_clock @set_ffi_set_clock @set_ffi_save_regs_set_clock @set_be_set_clock @set_var_set_clock @set_fp_var_set_clock @set_store_set_clock @empty_env_set_clock @unset_var_set_clock @get_var_set_clock @dec_clock_eq @get_var_imm_with_const @word_exp_with_const @inst_with_const @alloc_with_const @store_const_sem_with_const @sh_mem_op_with_const : stkc.

Ltac stk_eq :=
  autorewrite with stkc; stk_clk; destruct_ands;
  first [ reflexivity
        | apply pair_equal_spec; split; [reflexivity|]; f_equal; lia
        | f_equal; lia ].

Ltac ac_simpl H :=
  autorewrite with stkc in H |- *;
  cbn [PAIR_MAP I option_map cont_loop exit_loop bad_fun_return fst snd] in H |- *.

Ltac ac_loop IH extra H :=
  repeat first
    [ progress (rewrite ?fix_clock_evaluate in H)
    | progress (rewrite ?fix_clock_evaluate)
    | match goal with E : fix_clock _ (evaluate _) = _ |- _ => rewrite fix_clock_evaluate in E end
    | match goal with
      | E : (?x =? 0)%N = false |- context [(?x + extra =? 0)%N] =>
          let E' := fresh "E" in
          assert (E' : (x + extra =? 0)%N = false) by (apply N.eqb_neq; apply N.eqb_neq in E; lia);
          rewrite E'; clear E'; cbn beta iota zeta
      end
    | match goal with
      | E : evaluate (?p', ?s'') = (?r', ?t) |- _ =>
          let Hc := fresh "Hc" in
          pose proof (evaluate_clock p' s'' r' t E) as Hc;
          let Heq := fresh "Heq" in let Hn := fresh "Hn" in
          destruct (classical_dec (r' = SOME TimeOut)) as [Heq | Hn];
          [ first [discriminate Heq | subst r'; clear E; try ac_simpl H]
          | let Hi := fresh "Hi" in
            pose proof (IH (p', s'') ltac:(stk_eval_lt) r' t E Hn) as Hi; clear E;
            cbn [fst snd] in Hi;
            match goal with
            | |- context [evaluate (p', ?X)] =>
                replace X with (set_clock (clock s'' + extra) s'') by stk_eq; rewrite Hi; clear Hi
            end ]
      end
    | match type of H with
      | context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; ac_simpl H
      end ].

Section AddClockThm.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_add_clock" *)
Theorem evaluate_add_clock : forall extra (p : prog a) (s : state a c ffi_t) r s',
  evaluate (p, s) = (r, s') /\ r <> SOME TimeOut ->
  evaluate (p, set_clock (clock s + extra) s) = (r, set_clock (clock s' + extra) s').
Proof.
  intros extra.
  enough (G : forall x : prog a * state a c ffi_t, forall r s', evaluate x = (r, s') ->
    r <> SOME TimeOut ->
    evaluate (fst x, set_clock (clock (snd x) + extra) (snd x)) = (r, set_clock (clock s' + extra) s'))
    by (intros p s r s' [H Hr]; exact (G (p, s) r s' H Hr)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s' H Hr; cbn [fst snd].
  rewrite evaluate_eqn in H |- *.
  destruct p; cbn [evaluate_body] in H |- *; ac_simpl H; ac_loop IH extra H;
  try (match goal with Hr : ?x <> ?x |- _ => exfalso; exact (Hr eq_refl) end);
  try (injection H as <- <-);
  try (match goal with Hr : ?x <> ?x |- _ => exfalso; exact (Hr eq_refl) end);
  repeat match goal with
         | E : alloc _ _ = (_, _) |- _ => pose proof (alloc_const _ _ _ _ E); rewrite E; clear E
         | E : store_const_sem _ _ _ = (_, _) |- _ =>
             pose proof (store_const_sem_const _ _ _ _ _ E); rewrite E; clear E
         | E : sh_mem_op _ _ _ _ = (_, _) |- _ =>
             pose proof (sh_mem_op_const _ _ _ _ _ _ E); rewrite E; clear E
         | E : inst _ _ = SOME _ |- _ => pose proof (inst_const _ _ _ E); clear E
         end;
  cbn [PAIR_MAP I] in *;
  stk_eq.
Qed.

End AddClockThm.

Section More.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "pair_map_eq" *)
Theorem pair_map_eq : forall {A B C D} (f : A -> C) (g : B -> D) p x y,
  (f ## g) p = (x, y) <-> (exists q r, p = (q, r) /\ x = f q /\ y = g r).
Proof.
  intros A B C D f g [q r] x y; cbn; split.
  - intros H; injection H as <- <-; eauto.
  - intros [q' [r' [E [-> ->]]]]; injection E as -> ->; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "bad_fun_return_IMP" *)
Theorem bad_fun_return_IMP : forall res : option (result a),
  bad_fun_return res -> res = NONE \/ exists n, res = SOME (Break n) \/ res = SOME (Continue n).
Proof.
  intros [[]|] H; cbn in H; try discriminate; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "cont_loop_IMP" *)
Theorem cont_loop_IMP : forall res : option (result a),
  cont_loop res -> res = NONE \/ res = SOME (Continue 0).
Proof.
  intros [[]|] H; cbn in H; try discriminate; auto.
  apply N.eqb_eq in H; subst; auto.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "with_clock_ffi" *)
Theorem with_clock_ffi : forall (s : state a c ffi_t) k, ffi (set_clock k s) = ffi s.
Proof. reflexivity. Qed.

End More.
Ltac io_facts :=
  repeat match goal with
         | E : alloc _ _ = (_, _) |- _ => pose proof (alloc_const _ _ _ _ E); clear E
         | E : store_const_sem _ _ _ = (_, _) |- _ =>
             pose proof (store_const_sem_const _ _ _ _ _ E); clear E
         | E : inst _ _ = SOME _ |- _ => pose proof (inst_const _ _ _ E); clear E
         | E : sh_mem_op _ _ _ _ = (_, _) |- _ => pose proof (sh_mem_op_io _ _ _ _ _ _ E); clear E
         | E : call_FFI _ _ _ _ = FFI_return _ _ |- _ => pose proof (call_FFI_io _ _ _ _ _ _ E); clear E
         end.

Ltac io_loop IH extra H :=
  repeat first
    [ progress (rewrite ?fix_clock_evaluate in H)
    | progress (rewrite ?fix_clock_evaluate)
    | match goal with E : fix_clock _ (evaluate _) = _ |- _ => rewrite fix_clock_evaluate in E end
    | match goal with
      | E : (?x =? 0)%N = false |- context [(?x + extra =? 0)%N] =>
          let E' := fresh "E" in
          assert (E' : (x + extra =? 0)%N = false) by (apply N.eqb_neq; apply N.eqb_neq in E; lia);
          rewrite E'; clear E'; cbn beta iota zeta
      end
    | match goal with
      | E : evaluate (?p', ?s'') = (?r', ?t) |- _ =>
          let Hc := fresh "Hc" in
          pose proof (evaluate_clock p' s'' r' t E) as Hc;
          let Heq := fresh "Heq" in let Hn := fresh "Hn" in
          destruct (classical_dec (r' = SOME TimeOut)) as [Heq | Hn];
          [ first
              [ discriminate Heq
              | try subst r';
                let Hp := fresh "Hp" in
                pose proof (IH (p', s'') ltac:(stk_eval_lt) _ _ E) as Hp; clear E;
                cbn [fst snd] in Hp;
                match goal with
                | |- context [evaluate (p', ?X)] =>
                    replace X with (set_clock (clock s'' + extra) s'') by stk_eq;
                    let r2 := fresh "r" in let t2 := fresh "t" in let E2 := fresh "E" in
                    destruct (evaluate (p', set_clock (clock s'' + extra) s'')) as [r2 t2] eqn:E2;
                    clear E2; cbn [SND snd] in Hp
                end;
                try ac_simpl H ]
          | let Hi := fresh "Hi" in
            pose proof (evaluate_add_clock extra p' s'' r' t (conj E Hn)) as Hi; clear E;
            match goal with
            | |- context [evaluate (p', ?X)] =>
                replace X with (set_clock (clock s'' + extra) s'') by stk_eq; rewrite Hi; clear Hi
            end ]
      end
    | match type of H with
      | context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; ac_simpl H
      end ].

Ltac io_goal_split :=
  repeat first
    [ match goal with
      | |- context [evaluate (?q, ?Y)] =>
          let r3 := fresh "r" in let t3 := fresh "t" in let E3 := fresh "E" in
          destruct (evaluate (q, Y)) as [r3 t3] eqn:E3;
          pose proof (evaluate_io_events_mono _ _ _ _ E3); clear E3; cbn beta iota zeta
      end
    | match goal with
      | |- context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
      end
    | match goal with
      | |- context [sh_mem_op ?o ?r ?w ?st] =>
          let E := fresh "E" in destruct (sh_mem_op o r w st) eqn:E; cbn [SND snd PAIR_MAP I]
      | |- context [alloc ?w ?st] =>
          let E := fresh "E" in destruct (alloc w st) eqn:E; cbn [SND snd PAIR_MAP I]
      | |- context [store_const_sem ?t1 ?t2 ?st] =>
          let E := fresh "E" in destruct (store_const_sem t1 t2 st) eqn:E; cbn [SND snd PAIR_MAP I]
      end ].

Section IoMono.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_add_clock_io_events_mono" *)
Theorem evaluate_add_clock_io_events_mono : forall extra (e : prog a) (s : state a c ffi_t),
  isPREFIX (io_events (ffi (SND (evaluate (e, s)))))
           (io_events (ffi (SND (evaluate (e, set_clock (clock s + extra) s))))).
Proof.
  intros extra.
  enough (G : forall x : prog a * state a c ffi_t, forall r s1, evaluate x = (r, s1) ->
    isPREFIX (io_events (ffi s1))
      (io_events (ffi (SND (evaluate (fst x, set_clock (clock (snd x) + extra) (snd x)))))))
    by (intros e s; destruct (evaluate (e, s)) as [r s1] eqn:E; exact (G (e, s) r s1 E)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s1 H; cbn [fst snd].
  destruct (classical_dec (r = SOME TimeOut)) as [->|Hr].
  2:{ rewrite (evaluate_add_clock extra p s r s1 (conj H Hr)); apply isPREFIX_REFL. }
  rewrite evaluate_eqn in H |- *.
  destruct p; cbn [evaluate_body] in H |- *; ac_simpl H; io_loop IH extra H;
  try discriminate H; try (injection H; intros; subst); try rewrite H;
  io_goal_split; io_facts;
  cbn [PAIR_MAP I SND snd] in *; stk_fields; destruct_ands;
  repeat match goal with
         | E : ffi ?t = _ |- _ => rewrite E in *; clear E
         end;
  eauto using isPREFIX_REFL, isPREFIX_trans2.
Qed.

End IoMono.
Section Neutral.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "inst_clock_neutral" *)
Local Theorem inst_clock_neutral : forall i (s t : state a c ffi_t) k,
  (inst i s = SOME t -> inst i (set_clock k s) = SOME (set_clock k t)) /\
  (inst i s = NONE -> inst i (set_clock k s) = NONE).
Proof. intros i s t k; rewrite inst_with_const; split; intros ->; reflexivity. Qed.

Lemma inst_with_ffi i (s : state a c ffi_t) k :
  inst i (set_ffi k s) = OPTION_MAP (fun s => set_ffi k s) (inst i s).
Proof.
  assert (W : forall e, word_exp (set_ffi k s) e = word_exp s e) by (apply word_exp_cong; reflexivity).
  assert (V : forall xs, get_vars xs (set_ffi k s) = get_vars xs s).
  { induction xs as [|x0 xs IH]; cbn; [reflexivity|]. rewrite IH; reflexivity. }
  assert (M : forall x y, mem_store x y (set_ffi k s) = OPTION_MAP (fun s => set_ffi k s) (mem_store x y s)).
  { intros; unfold mem_store; stk_fields. destruct (classical_dec _); reflexivity. }
  destruct i as [| | x | m r [ad w] | f]; [| | destruct x | destruct m | destruct f];
    cbn [inst]; unfold assign; rewrite ?W, ?V; try reflexivity;
    unfold get_var, mem_load, get_fp_var; stk_fields;
    repeat (rewrite ?M; cbn [option_map];
            match goal with
            | |- context [match ?x with _ => _ end] => destruct x eqn:?; cbn beta iota zeta
            end);
    first [reflexivity | cbn [option_map] in *; congruence].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "inst_clock_neutral_ffi" *)
Local Theorem inst_clock_neutral_ffi : forall i (s t : state a c ffi_t) k,
  (inst i s = SOME t -> inst i (set_ffi k s) = SOME (set_ffi k t)) /\
  (inst i s = NONE -> inst i (set_ffi k s) = NONE).
Proof. intros i s t k; rewrite inst_with_ffi; split; intros ->; reflexivity. Qed.

(** HOL names the new clock [c]; it is [k] here ([c] is the state's
    compiler-configuration type). *)
(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_clock_neutral" *)
Theorem evaluate_clock_neutral : forall (prog0 : prog a) (s : state a c ffi_t) res t k,
  evaluate (prog0, s) = (res, t) /\ clock_neutral prog0 ->
  evaluate (prog0, set_clock k s) = (res, set_clock k t).
Proof.
  induction prog0; intros st res t k [H Hn]; cbn [clock_neutral] in Hn; try discriminate;
    rewrite evaluate_eqn in H |- *; cbn [evaluate_body] in H |- *.
  - injection H as <- <-; reflexivity.
  - rewrite inst_with_const. destruct (inst i st); injection H as <- <-; reflexivity.
  - apply andb_prop in Hn as [Hn1 Hn2].
    rewrite !fix_clock_evaluate in *.
    destruct (evaluate (prog0_1, st)) as [r1 s1] eqn:E1.
    rewrite (IHprog0_1 st r1 s1 k (conj E1 Hn1)).
    destruct r1; [injection H as <- <-; reflexivity|].
    apply IHprog0_2; split; assumption.
  - apply andb_prop in Hn as [Hn1 Hn2].
    rewrite get_var_imm_with_const. change (get_var n (set_clock k st)) with (get_var n st).
    destruct (get_var n st), (get_var_imm r st); try (injection H as <- <-; reflexivity).
    destruct (wordSem.word_cmp c0 w w0) as [[]|]; try (injection H as <- <-; reflexivity).
    + apply IHprog0_1; split; assumption.
    + apply IHprog0_2; split; assumption.
  - change (code (set_clock k st)) with (code st).
    destruct (classical_dec _); injection H as <- <-; reflexivity.
  - change (get_var n (set_clock k st)) with (get_var n st).
    destruct (get_var n st); injection H as <- <-; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_ffi_neutral" *)
Theorem evaluate_ffi_neutral : forall (prog0 : prog a) (st : state a c ffi_t) res t k,
  evaluate (prog0, st) = (res, t) /\ clock_neutral prog0 ->
  evaluate (prog0, set_ffi k st) = (res, set_ffi k t).
Proof.
  induction prog0; intros st res t k [H Hn]; cbn [clock_neutral] in Hn; try discriminate;
    rewrite evaluate_eqn in H |- *; cbn [evaluate_body] in H |- *.
  - injection H as <- <-; reflexivity.
  - rewrite inst_with_ffi. destruct (inst i st); injection H as <- <-; reflexivity.
  - apply andb_prop in Hn as [Hn1 Hn2].
    rewrite !fix_clock_evaluate in *.
    destruct (evaluate (prog0_1, st)) as [r1 s1] eqn:E1.
    rewrite (IHprog0_1 st r1 s1 k (conj E1 Hn1)).
    destruct r1; [injection H as <- <-; reflexivity|].
    apply IHprog0_2; split; assumption.
  - apply andb_prop in Hn as [Hn1 Hn2].
    replace (get_var_imm r (set_ffi k st)) with (get_var_imm r st) by (destruct r; reflexivity).
    change (get_var n (set_ffi k st)) with (get_var n st).
    destruct (get_var n st), (get_var_imm r st); try (injection H as <- <-; reflexivity).
    destruct (wordSem.word_cmp c0 w w0) as [[]|]; try (injection H as <- <-; reflexivity).
    + apply IHprog0_1; split; assumption.
    + apply IHprog0_2; split; assumption.
  - change (code (set_ffi k st)) with (code st).
    destruct (classical_dec _); injection H as <- <-; reflexivity.
  - change (get_var n (set_ffi k st)) with (get_var n st).
    destruct (get_var n st); injection H as <- <-; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "semantics_Terminate_IMP_PREFIX" *)
Theorem semantics_Terminate_IMP_PREFIX : forall start (s1 : state a c ffi_t) x l,
  semantics start s1 = Terminate x l -> isPREFIX (io_events (ffi s1)) l.
Proof.
  intros start s1 x l H; unfold semantics in H.
  destruct (classical_dec _) as [_|_]; [discriminate|].
  unfold some in H. destruct (classical_dec _) as [Ex|_]; [|discriminate].
  match type of H with
  | @select _ ?I ?P = _ => pose proof (@select_spec _ I P Ex) as [k [t [r [outcome [E [_ Eres]]]]]]
  end.
  rewrite Eres in H; injection H as <- <-.
  exact (evaluate_io_events_mono _ (set_clock k s1) _ _ E).
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "semantics_Diverge_IMP_LPREFIX" *)
Theorem semantics_Diverge_IMP_LPREFIX : forall start (s1 : state a c ffi_t) l,
  semantics start s1 = Diverge l -> LPREFIX (fromList (io_events (ffi s1))) l.
Proof.
  intros start s1 l H; unfold semantics in H.
  destruct (classical_dec _) as [_|_]; [discriminate|].
  unfold some in H. destruct (classical_dec _) as [Ex|_].
  { match type of H with
    | @select _ ?I ?P = _ => pose proof (@select_spec _ I P Ex) as [k [t [r [o [_ [_ Eres]]]]]]
    end.
    rewrite Eres in H; discriminate. }
  injection H as <-.
  set (g := fun k => io_events (ffi (SND (evaluate (@Call a NONE (inl start) NONE, set_clock k s1))))).
  replace (IMAGE _ UNIV) with (IMAGE fromList (IMAGE g UNIV))
    by (rewrite <- IMAGE_COMPOSE; reflexivity).
  assert (C : lprefix_chain (IMAGE fromList (IMAGE g UNIV))).
  { apply prefix_chain_lprefix_chain.
    intros l1 l2 [[k1 [-> _]] [k2 [-> _]]].
    assert (M : forall k d, isPREFIX (g k) (g (k + d))).
    { intros k d; unfold g.
      pose proof (evaluate_add_clock_io_events_mono d (@Call a NONE (inl start) NONE) (set_clock k s1)) as P.
      exact P. }
    destruct (N.le_ge_cases k1 k2) as [Hle|Hle].
    - left; replace k2 with (k1 + (k2 - k1)) by lia; apply M.
    - right; replace k1 with (k2 + (k1 - k2)) by lia; apply M. }
  destruct (build_lprefix_lub_thm _ C) as [U _]. apply U.
  exists (g 0); split; [|exists 0; split; [reflexivity|exact Logic.I]].
  unfold g. rewrite evaluate_eqn; cbn [evaluate_body].
  destruct (find_code _ _ _); [destruct (negb _)|]; reflexivity.
Qed.

End Neutral.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "map_bitmap_length" *)
Theorem map_bitmap_length : forall {A} (a : list bool) (b c : list A) x y z,
  map_bitmap a b c = SOME (x, (y, z)) ->
  LENGTH c = LENGTH x + LENGTH z /\ LENGTH x = LENGTH a.
Proof.
  intros A a0; induction a0 as [|h t IH]; intros b c0 x y z H.
  - cbn in H; injection H as <- <- <-; cbn; split; reflexivity.
  - destruct h; cbn in H.
    + destruct b as [|bh b]; [discriminate|]. destruct c0 as [|ch c0]; [discriminate|].
      destruct (map_bitmap t b c0) as [[xs [ys zs]]|] eqn:E; [|discriminate].
      injection H as <- <- <-. destruct (IH _ _ _ _ _ E) as [H1 H2]. cbn [LENGTH]; lia.
    + destruct c0 as [|ch c0]; [destruct b; discriminate|].
      destruct (map_bitmap t b c0) as [[xs [ys zs]]|] eqn:E; [|discriminate].
      injection H as <- <- <-. destruct (IH _ _ _ _ _ E) as [H1 H2]. cbn [LENGTH]; lia.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/stackPropsScript.sml" "dec_stack_length" *)
Theorem dec_stack_length : forall {a : N} (bs : list (word a)) enc orig_stack new_stack,
  dec_stack bs enc orig_stack = SOME new_stack -> LENGTH orig_stack = LENGTH new_stack.
Proof.
  intros a bs.
  enough (G : forall n enc orig_stack new_stack, (length orig_stack < n)%nat ->
            dec_stack bs enc orig_stack = SOME new_stack -> LENGTH orig_stack = LENGTH new_stack)
    by (intros enc o ns; apply (G (Datatypes.S (length o))); lia).
  induction n as [|n IH]; intros enc o ns Hl H; [lia|].
  destruct o as [|w ws]; [rewrite (proj1 dec_stack_def) in H; discriminate|].
  rewrite (proj2 dec_stack_def) in H.
  destruct (bool_decide _).
  - destruct (andb _ _) eqn:Ea; [|discriminate]. injection H as <-.
    apply andb_prop in Ea as [_ Ea]. apply bool_decide_spec in Ea; subst ws; reflexivity.
  - destruct (full_read_bitmap bs w) as [bs'|]; [|discriminate].
    destruct (map_bitmap bs' enc ws) as [[hd [ts' ws']]|] eqn:Em; [|discriminate].
    destruct (dec_stack bs ts' ws') as [rest|] eqn:Ed; [|discriminate].
    injection H as <-.
    destruct (map_bitmap_length _ _ _ _ _ _ Em) as [L1 _].
    pose proof (map_bitmap_LENGTH _ _ _ _ _ _ Em) as [_ L2].
    rewrite !LENGTH_length in *. cbn [length] in Hl.
    assert (L3 := IH ts' ws' rest ltac:(lia) Ed). rewrite !LENGTH_length in *.
    rewrite ?LENGTH_length; cbn [length app]; rewrite ?length_app; lia.
Qed.

(** ** Galette-only: [semantics] is preserved by a clock-adjusting simulation

    If every non-[Error] run of the start call from [s] is matched by a run
    from [t] with some extra clock, with the same result and FFI state, and
    [s] does not [Fail], then [t] has the same [semantics].  This is the
    argument of the [compile_semantics] theorems of the stack-to-stack
    passes (HOL proves it inline each time). *)
Section SemSim.
Context {a : N} {c1 c2 ffi_t : Type}.

Lemma io_chain_stack {c} start (x : state a c ffi_t) :
  lprefix_chain (IMAGE (fun k => fromList (io_events (ffi (SND (evaluate (@Call a NONE (inl start) NONE, set_clock k x))))))
                       UNIV).
Proof.
  set (g := fun k => io_events (ffi (SND (evaluate (@Call a NONE (inl start) NONE, set_clock k x))))).
  replace (IMAGE _ UNIV) with (IMAGE fromList (IMAGE g UNIV)) by (rewrite <- IMAGE_COMPOSE; reflexivity).
  apply prefix_chain_lprefix_chain.
  intros l1 l2 [[k1 [-> _]] [k2 [-> _]]].
  assert (M : forall k d, isPREFIX (g k) (g (k + d))).
  { intros k d; unfold g.
    exact (evaluate_add_clock_io_events_mono d (@Call a NONE (inl start) NONE) (set_clock k x)). }
  destruct (N.le_ge_cases k1 k2) as [Hle|Hle].
  - left; replace k2 with (k1 + (k2 - k1)) by lia; apply M.
  - right; replace k1 with (k2 + (k1 - k2)) by lia; apply M.
Qed.

Lemma semantics_sim start (s : state a c1 ffi_t) (t : state a c2 ffi_t) :
  semantics start s <> Fail ->
  (forall k r s1, evaluate (@Call a NONE (inl start) NONE, set_clock k s) = (r, s1) -> r <> SOME Error ->
     exists ck t1, evaluate (@Call a NONE (inl start) NONE, set_clock (k + ck) t) = (r, t1) /\ ffi t1 = ffi s1) ->
  semantics start t = semantics start s.
Proof.
  intros HF Hsim.
  set (P := @Call a NONE (inl start) NONE).
  set (bad := fun res : option (result a) =>
         res <> SOME TimeOut /\ res <> SOME (Result (Loc 1 0)) /\
         (forall w, res <> SOME (Halt (Word w))) /\ forall f, res <> SOME (FinalFFI f)).
  assert (OKs : forall k, ~ bad (FST (evaluate (P, set_clock k s)))).
  { intros k Hk; apply HF; unfold semantics; cbv zeta.
    destruct (classical_dec _) as [_|Hn]; [reflexivity|exfalso; apply Hn; exists k; exact Hk]. }
  assert (NE : forall k, FST (evaluate (P, set_clock k s)) <> SOME Error).
  { intros k E; apply (OKs k); rewrite E; unfold bad; repeat split; congruence. }
  assert (A : forall k, exists ck t1,
            evaluate (P, set_clock (k + ck) t) = (FST (evaluate (P, set_clock k s)), t1) /\
            ffi t1 = ffi (SND (evaluate (P, set_clock k s)))).
  { intros k; destruct (evaluate (P, set_clock k s)) as [r s1] eqn:E; cbn [FST SND].
    apply (Hsim k r s1 E). pose proof (NE k) as H; rewrite E in H; exact H. }
  assert (B : forall k e r t', evaluate (P, set_clock k t) = (r, t') -> r <> SOME TimeOut ->
            evaluate (P, set_clock (k + e) t) = (r, set_clock (clock t' + e) t')).
  { intros k e r t' E Hr. exact (evaluate_add_clock e P (set_clock k t) r t' (conj E Hr)). }
  assert (OKt : forall k, ~ bad (FST (evaluate (P, set_clock k t)))).
  { intros k Hk. destruct (A k) as (ck & t1 & E1 & _).
    destruct (evaluate (P, set_clock k t)) as [r t'] eqn:Et; cbn [FST] in Hk.
    pose proof (B k ck r t' Et (proj1 Hk)) as E2. rewrite E1 in E2. injection E2 as E2 _.
    apply (OKs k); subst r; exact Hk. }
  unfold semantics; cbv zeta; fold P.
  destruct (classical_dec _) as [[k Hk]|_]; [exfalso; exact (OKt k Hk)|].
  destruct (classical_dec _) as [[k Hk]|_]; [exfalso; exact (OKs k Hk)|].
  match goal with |- match some ?Q1 with _ => _ end = match some ?Q2 with _ => _ end =>
    assert (EQ : Q1 = Q2) end.
  { apply functional_extensionality; intros res; apply propositional_extensionality; split.
    - intros (k & t0 & r & o & E & M & R).
      assert (Hr : SOME r <> SOME TimeOut) by (intros H; injection H as ->; exact M).
      destruct (A k) as (ck & t1 & E1 & F1).
      rewrite (B k ck _ _ E Hr) in E1.
      destruct (evaluate (P, set_clock k s)) as [r0 s0] eqn:Es; cbn [FST SND] in E1, F1.
      injection E1 as <- <-.
      exists k, s0, r, o. split; [exact Es|]. split; [exact M|]. rewrite R, <- F1; reflexivity.
    - intros (k & t0 & r & o & E & M & R).
      destruct (A k) as (ck & t1 & E1 & F1). rewrite E in E1, F1; cbn [FST SND] in E1, F1.
      exists (k + ck), t1, r, o. split; [exact E1|split; [exact M|rewrite R, F1; reflexivity]]. }
  rewrite EQ. destruct (some _); [reflexivity|].
  f_equal.
  set (Xt := IMAGE (fun k => fromList (io_events (ffi (SND (evaluate (P, set_clock k t)))))) UNIV).
  set (Xs := IMAGE (fun k => fromList (io_events (ffi (SND (evaluate (P, set_clock k s)))))) UNIV).
  assert (Ct : lprefix_chain Xt) by exact (io_chain_stack start t).
  assert (Cs : lprefix_chain Xs) by exact (io_chain_stack start s).
  assert (EQV : equiv_lprefix_chain Xs Xt).
  { apply (equiv_lprefix_chain_thm _ _ (conj Cs Ct)); split.
    - intros ll1 n x [[k [-> _]] Hx].
      destruct (A k) as (ck & t1 & E1 & F1).
      exists (fromList (io_events (ffi (SND (evaluate (P, set_clock (k + ck) t)))))).
      split; [exists (k + ck); split; [reflexivity|exact Logic.I]|].
      rewrite E1; cbn [SND]; rewrite F1; exact Hx.
    - intros ll2 n x [[k [-> _]] Hx].
      destruct (A k) as (ck & t1 & E1 & F1).
      exists (fromList (io_events (ffi (SND (evaluate (P, set_clock k s)))))).
      split; [exists k; split; [reflexivity|exact Logic.I]|].
      pose proof (evaluate_add_clock_io_events_mono ck P (set_clock k t)) as M.
      replace (evaluate (P, set_clock (clock (set_clock k t) + ck) (set_clock k t)))
        with (evaluate (P, set_clock (k + ck) t)) in M by reflexivity.
      rewrite E1 in M; cbn [SND] in M; rewrite F1 in M.
      assert (L : LPREFIX (fromList (io_events (ffi (SND (evaluate (P, set_clock k t))))))
                          (fromList (io_events (ffi (SND (evaluate (P, set_clock k s)))))))
        by (apply LPREFIX_fromList; rewrite toList_fromList; exact M).
      apply LPREFIX_pfx in L. exact (L n x Hx). }
  apply (unique_lprefix_lub Xt); split.
  - exact (build_lprefix_lub_thm _ Ct).
  - apply (lprefix_lub_new_chain Xs Xt).
    split; [exact Ct|split; [exact EQV|exact (build_lprefix_lub_thm _ Cs)]].
Qed.

End SemSim.
