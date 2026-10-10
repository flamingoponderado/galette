(** * CakeML [wordProps]: the remaining constant-field lemmas

    Port of the declarations of the "CONST LEMMAS" part of
    [cakeml/compiler/backend/semantics/wordPropsScript.sml] not ported in
    [wordProps.consts] ([alloc_with_const], [mem_load_with_const], ...,
    [cut_state_const]), and of the [get]/[set] lemmas that follow the
    "CONST LEMMAS END" marker.

    Carrier notes (as in [wordProps.consts]):
    - HOL [s with f := v] is [set_f v s]; HOL [s.stack_size] is
      [state_stack_size s]; HOL [I ## f] is [PAIR_MAP I f].
    - HOL's free variables are quantified; names clashing with Rocq names
      are renamed ([c] to [c0], [code] to [code0], [store] to [store0], [a]
      to [ad]).
    - [sh_mem_set_var_const]: HOL's free variables [outcome], [f], [l] of
      the conditional conjuncts are universally quantified with the
      others. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.finite_maps Require Import finite_map sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common wordLang.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import consts.
Open Scope N_scope.

(** Split every [match] of the goal, destructing the scrutinee. *)
Local Ltac split_all :=
  repeat match goal with
         | |- context [match ?x with _ => _ end] =>
             let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
         end.

Section WithConst.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(** A state update that does not touch the locals, the store, the memory or
    its domain leaves [word_exp] unchanged. *)
Local Lemma word_exp_upd (f : state -> state) s e :
  locals (f s) = locals s -> store (f s) = store s -> memory (f s) = memory s ->
  mdomain (f s) = mdomain s -> word_exp (f s) e = word_exp s e.
Proof. intros; apply word_exp_state_cong; assumption. Qed.

(** [alloc] commutes with an update [f] that commutes with its
    primitives. *)
Local Lemma alloc_upd (f : state -> state) w names s :
  (forall t, locals (f t) = locals t) ->
  (forall t x y, set_store x y (f t) = f (set_store x y t)) ->
  (forall t x y, push_env x y (f t) = f (push_env x y t)) ->
  (forall t, gc (f t) = OPTION_MAP f (gc t)) ->
  (forall t, pop_env (f t) = OPTION_MAP f (pop_env t)) ->
  (forall t x, get_store x (f t) = get_store x t) ->
  (forall t x, has_space x (f t) = has_space x t) ->
  (forall t b, flush_state b (f t) = f (flush_state b t)) ->
  alloc w names (f s) = PAIR_MAP I f (alloc w names s).
Proof.
  intros Hl Hs Hp Hg Hpo Hgs Hh Hf; unfold alloc; rewrite Hl.
  destruct (cut_envs _ _); [|rewrite Hf; reflexivity].
  rewrite Hs, Hp, Hg. destruct (gc _); cbn [OPTION_MAP option_map]; [|rewrite Hf; reflexivity].
  rewrite Hpo. destruct (pop_env _); cbn [OPTION_MAP option_map]; [|rewrite Hf; reflexivity].
  rewrite Hgs. destruct (get_store _ _); [|reflexivity].
  rewrite Hh. destruct (has_space _ _) as [[]|]; [reflexivity|rewrite Hf|]; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "alloc_with_const" *)
Theorem alloc_with_const : forall c0 names (s : state) k t code0 compile_oracle0 comp,
  alloc c0 names (set_clock k s) = PAIR_MAP I (fun s => set_clock k s) (alloc c0 names s) /\
  alloc c0 names (set_termdep t s) = PAIR_MAP I (fun s => set_termdep t s) (alloc c0 names s) /\
  alloc c0 names (set_code code0 s) = PAIR_MAP I (fun s => set_code code0 s) (alloc c0 names s) /\
  alloc c0 names (set_compile_oracle compile_oracle0 s) =
    PAIR_MAP I (fun s => set_compile_oracle compile_oracle0 s) (alloc c0 names s) /\
  alloc c0 names (set_compile comp s) = PAIR_MAP I (fun s => set_compile comp s) (alloc c0 names s).
Proof.
  intros; repeat split;
    match goal with |- alloc _ _ (?F ?v ?s0) = _ => apply (alloc_upd (F v)) end;
    first [ intros; reflexivity
          | intros t' x [[? [? [? ?]]]|]; unfold push_env; destruct (env_to_list _ _); reflexivity
          | intros t'; unfold gc; cbn [gc_fun stack memory mdomain store set_clock set_termdep
              set_code set_compile_oracle set_compile];
            destruct (gc_fun t' _) as [[? [? ?]]|]; [destruct (dec_stack _ _)|]; reflexivity
          | intros t'; unfold pop_env; cbn [stack set_clock set_termdep set_code set_compile_oracle
              set_compile]; destruct (stack t') as [|[? ? ? [[? ?]|]] ?]; reflexivity
          | intros t' []; reflexivity ].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "mem_load_with_const" *)
Theorem mem_load_with_const : forall x (y : state) l td k xs perm c0 co cc,
  mem_load x (set_locals l y) = mem_load x y /\
  mem_load x (set_termdep td y) = mem_load x y /\
  mem_load x (set_clock k y) = mem_load x y /\
  mem_load x (set_stack xs y) = mem_load x y /\
  mem_load x (set_permute perm y) = mem_load x y /\
  mem_load x (set_code c0 y) = mem_load x y /\
  mem_load x (set_compile_oracle co y) = mem_load x y /\
  mem_load x (set_compile cc y) = mem_load x y.
Proof. intros; repeat split; reflexivity. Qed.

Local Ltac mem_store_tac :=
  intros; unfold mem_store; repeat split; cbn [mdomain set_locals set_clock set_code
    set_compile set_compile_oracle set_permute set_stack];
  destruct (classical_dec _); cbn [OPTION_MAP option_map]; [|reflexivity..];
  repeat match goal with s : state |- _ => destruct s end; reflexivity.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "mem_store_with_const" *)
Theorem mem_store_with_const : forall x z (y : state) l k code0 c0 co perm xs,
  mem_store x z (set_locals l y) = OPTION_MAP (fun s => set_locals l s) (mem_store x z y) /\
  mem_store x z (set_clock k y) = OPTION_MAP (fun s => set_clock k s) (mem_store x z y) /\
  mem_store x z (set_code code0 y) = OPTION_MAP (fun s => set_code code0 s) (mem_store x z y) /\
  mem_store x z (set_compile c0 y) = OPTION_MAP (fun s => set_compile c0 s) (mem_store x z y) /\
  mem_store x z (set_compile_oracle co y) =
    OPTION_MAP (fun s => set_compile_oracle co s) (mem_store x z y) /\
  mem_store x z (set_permute perm y) = OPTION_MAP (fun s => set_permute perm s) (mem_store x z y) /\
  mem_store x z (set_stack xs y) = OPTION_MAP (fun s => set_stack xs s) (mem_store x z y).
Proof. mem_store_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "word_exp_with_const" *)
Theorem word_exp_with_const : forall (x : state) y k xs perm termdep0 c0 co cc,
  word_exp (set_clock k x) y = word_exp x y /\
  word_exp (set_stack xs x) y = word_exp x y /\
  word_exp (set_permute perm x) y = word_exp x y /\
  word_exp (set_termdep termdep0 x) y = word_exp x y /\
  word_exp (set_code c0 x) y = word_exp x y /\
  word_exp (set_compile_oracle co x) y = word_exp x y /\
  word_exp (set_compile cc x) y = word_exp x y.
Proof. intros; repeat split; apply word_exp_state_cong; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "assign_const_full" *)
Theorem assign_const_full : forall x y (z ad : state),
  assign x y z = SOME ad ->
  code ad = code z /\
  code_buffer ad = code_buffer z /\
  data_buffer ad = data_buffer z /\
  compile ad = compile z /\
  compile_oracle ad = compile_oracle z /\
  clock ad = clock z /\
  ffi ad = ffi z /\
  handler ad = handler z /\
  stack ad = stack z /\
  locals_size ad = locals_size z /\
  stack_limit ad = stack_limit z /\
  stack_max ad = stack_max z /\
  state_stack_size ad = state_stack_size z.
Proof.
  intros x y z ad H; unfold assign in H; destruct (word_exp _ _); [|discriminate].
  injection H as <-; repeat split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "assign_const" *)
Theorem assign_const : forall x y (z ad : state),
  assign x y z = SOME ad ->
  clock ad = clock z /\
  ffi ad = ffi z.
Proof. intros x y z ad H; apply assign_const_full in H; destr_conj; split; assumption. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "assign_with_const" *)
Theorem assign_with_const : forall x y (z : state) k code0 c0 co perm xs,
  assign x y (set_clock k z) = OPTION_MAP (fun s => set_clock k s) (assign x y z) /\
  assign x y (set_code code0 z) = OPTION_MAP (fun s => set_code code0 s) (assign x y z) /\
  assign x y (set_compile c0 z) = OPTION_MAP (fun s => set_compile c0 s) (assign x y z) /\
  assign x y (set_compile_oracle co z) =
    OPTION_MAP (fun s => set_compile_oracle co s) (assign x y z) /\
  assign x y (set_permute perm z) = OPTION_MAP (fun s => set_permute perm s) (assign x y z) /\
  assign x y (set_stack xs z) = OPTION_MAP (fun s => set_stack xs s) (assign x y z).
Proof.
  intros; unfold assign; repeat split;
    (rewrite word_exp_state_cong with (t := z) by reflexivity);
    destruct (word_exp _ _); reflexivity.
Qed.

(** [inst] commutes with an update [f] of a field that [inst] neither
    reads nor writes. *)
Local Lemma inst_upd (f : state -> state) i s :
  (forall t, locals (f t) = locals t) -> (forall t, store (f t) = store t) ->
  (forall t, memory (f t) = memory t) -> (forall t, mdomain (f t) = mdomain t) ->
  (forall t, be (f t) = be t) -> (forall t, fp_regs (f t) = fp_regs t) ->
  (forall t v, set_locals v (f t) = f (set_locals v t)) ->
  (forall t v, set_memory v (f t) = f (set_memory v t)) ->
  (forall t v, set_fp_regs v (f t) = f (set_fp_regs v t)) ->
  inst i (f s) = OPTION_MAP f (inst i s).
Proof.
  intros Hl Hs Hm Hd Hb Hf Sl Sm Sf.
  assert (Hw : forall e, word_exp (f s) e = word_exp s e) by (intros; apply word_exp_state_cong; auto).
  assert (Hv : forall vs, get_vars vs (f s) = get_vars vs s).
  { induction vs as [|v vs IH]; cbn; [reflexivity|]. unfold get_var; rewrite Hl, IH; reflexivity. }
  assert (Hg : forall v, get_var v (f s) = get_var v s) by (intros; unfold get_var; rewrite Hl; reflexivity).
  assert (Hfp : forall v, get_fp_var v (f s) = get_fp_var v s) by (intros; unfold get_fp_var; rewrite Hf; reflexivity).
  assert (Hml : forall w, mem_load w (f s) = mem_load w s)
    by (intros; unfold mem_load; rewrite Hm, Hd; reflexivity).
  assert (Hsv : forall v x t, set_var v x (f t) = f (set_var v x t))
    by (intros; unfold set_var; rewrite Hl, Sl; reflexivity).
  assert (Hsf : forall v x t, set_fp_var v x (f t) = f (set_fp_var v x t))
    by (intros; unfold set_fp_var; rewrite Hf, Sf; reflexivity).
  assert (Hms : forall w x, mem_store w x (f s) = OPTION_MAP f (mem_store w x s)).
  { intros; unfold mem_store; rewrite Hd. destruct (classical_dec _); [|reflexivity].
    cbn; rewrite Hm, Sm; reflexivity. }
  destruct i as [|r w|ar|m r [ad w]|fi];
    [reflexivity| |destruct ar|destruct m|destruct fi];
    cbn [inst]; unfold assign; rewrite ?Hw, ?Hv, ?Hm, ?Hd, ?Hb, ?Hfp, ?Hg;
    repeat first
      [ progress (rewrite ?Hml, ?Hms, ?Hm, ?Hd, ?Hb, ?Hfp, ?Hg, ?Hv)
      | match goal with
        | |- context [match ?x with _ => _ end] =>
            lazymatch x with context [f] => fail | _ => idtac end;
            let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
        end ];
    cbn [OPTION_MAP option_map]; rewrite ?Hsv, ?Hsf, ?Sm; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "inst_with_const" *)
Theorem inst_with_const : forall i (s : state) k code0 c0 co perm xs,
  inst i (set_clock k s) = OPTION_MAP (fun s => set_clock k s) (inst i s) /\
  inst i (set_code code0 s) = OPTION_MAP (fun s => set_code code0 s) (inst i s) /\
  inst i (set_compile c0 s) = OPTION_MAP (fun s => set_compile c0 s) (inst i s) /\
  inst i (set_compile_oracle co s) = OPTION_MAP (fun s => set_compile_oracle co s) (inst i s) /\
  inst i (set_permute perm s) = OPTION_MAP (fun s => set_permute perm s) (inst i s) /\
  inst i (set_stack xs s) = OPTION_MAP (fun s => set_stack xs s) (inst i s).
Proof. intros; repeat split; apply inst_upd; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "inst_const_full" *)
Theorem inst_const_full : forall i (s s' : state),
  inst i s = SOME s' ->
  code s' = code s /\
  code_buffer s' = code_buffer s /\
  data_buffer s' = data_buffer s /\
  compile s' = compile s /\
  compile_oracle s' = compile_oracle s /\
  clock s' = clock s /\
  ffi s' = ffi s /\
  handler s' = handler s /\
  stack s' = stack s /\
  locals_size s' = locals_size s /\
  stack_limit s' = stack_limit s /\
  stack_max s' = stack_max s /\
  state_stack_size s' = state_stack_size s.
Proof.
  intros i s s' H;
    destruct i as [|r w|ar|m r [ad w]|f]; [|cbn [inst] in H|destruct ar|destruct m|destruct f];
    cbn [inst] in H; unfold assign in H; split_H H; leaf H;
    repeat match goal with E : mem_store _ _ _ = SOME _ |- _ => apply mem_store_const in E end;
    destr_conj; unfold set_var, set_vars, set_fp_var in *;
    unfold_sets; repeat split; congruence.
Qed.

(** HOL's [local] duplicate of [inst_const_full]'s facts, with the
    equations oriented as in HOL. *)
(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "inst_code_gc_fun_const" *)
Theorem inst_code_gc_fun_const : forall i (s t : state),
  inst i s = SOME t ->
  code s = code t /\ gc_fun s = gc_fun t /\ sh_mdomain s = sh_mdomain t /\ mdomain s = mdomain t /\
  be s = be t /\ compile s = compile t /\ state_stack_size s = state_stack_size t /\
  stack_limit s = stack_limit t.
Proof.
  intros i s t H;
    destruct i as [|r w|ar|m r [ad w]|f]; [|cbn [inst] in H|destruct ar|destruct m|destruct f];
    cbn [inst] in H; unfold assign in H; split_H H; leaf H;
    repeat match goal with E : mem_store _ _ _ = SOME _ |- _ => apply mem_store_const in E end;
    destr_conj; unfold set_var, set_vars, set_fp_var in *;
    unfold_sets; repeat split; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "jump_exc_const" *)
Theorem jump_exc_const : forall (s s' : state) y,
  jump_exc s = SOME (s', y) ->
  be s' = be s /\
  gc_fun s' = gc_fun s /\
  mdomain s' = mdomain s /\
  sh_mdomain s' = sh_mdomain s /\
  code s' = code s /\
  code_buffer s' = code_buffer s /\
  data_buffer s' = data_buffer s /\
  compile s' = compile s /\
  compile_oracle s' = compile_oracle s /\
  clock s' = clock s /\
  ffi s' = ffi s /\
  stack_limit s' = stack_limit s /\
  stack_max s' = stack_max s /\
  state_stack_size s' = state_stack_size s.
Proof.
  intros s s' y H; unfold jump_exc in H; split_H H; leaf H;
    try discriminate H; repeat split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "jump_exc_with_const" *)
Theorem jump_exc_with_const : forall (s : state) k perm,
  jump_exc (set_clock k s) = OPTION_MAP (fun '(s, t) => (set_clock k s, t)) (jump_exc s) /\
  jump_exc (set_permute perm s) = OPTION_MAP (fun '(s, t) => (set_permute perm s, t)) (jump_exc s).
Proof.
  intros; unfold jump_exc; split; cbn [handler stack set_clock set_permute];
    (destruct (_ <? _); [|reflexivity];
     destruct (LASTN _ _) as [|[m e0 e [[n [l1 l2]]|]] xs]; reflexivity).
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "get_var_imm_with_const" *)
Theorem get_var_imm_with_const : forall x (y : state) k code0 compile0 compile_oracle0 td xs perm,
  get_var_imm x (set_clock k y) = get_var_imm x y /\
  get_var_imm x (set_code code0 y) = get_var_imm x y /\
  get_var_imm x (set_compile compile0 y) = get_var_imm x y /\
  get_var_imm x (set_compile_oracle compile_oracle0 y) = get_var_imm x y /\
  get_var_imm x (set_termdep td y) = get_var_imm x y /\
  get_var_imm x (set_stack xs y) = get_var_imm x y /\
  get_var_imm x (set_permute perm y) = get_var_imm x y.
Proof. intros [] y; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "dec_clock_const" *)
Theorem dec_clock_const : forall (s : state) locs p,
  locals (dec_clock s) = locals s /\
  locals_size (dec_clock s) = locals_size s /\
  fp_regs (dec_clock s) = fp_regs s /\
  store (dec_clock s) = store s /\
  stack (dec_clock s) = stack s /\
  stack_limit (dec_clock s) = stack_limit s /\
  stack_max (dec_clock s) = stack_max s /\
  state_stack_size (dec_clock s) = state_stack_size s /\
  memory (dec_clock s) = memory s /\
  mdomain (dec_clock s) = mdomain s /\
  sh_mdomain (dec_clock s) = sh_mdomain s /\
  permute (dec_clock s) = permute s /\
  compile (dec_clock s) = compile s /\
  compile_oracle (dec_clock s) = compile_oracle s /\
  code_buffer (dec_clock s) = code_buffer s /\
  data_buffer (dec_clock s) = data_buffer s /\
  gc_fun (dec_clock s) = gc_fun s /\
  handler (dec_clock s) = handler s /\
  termdep (dec_clock s) = termdep s /\
  code (dec_clock s) = code s /\
  be (dec_clock s) = be s /\
  ffi (dec_clock s) = ffi s /\
  clock (dec_clock (set_locals locs s)) = clock (dec_clock s) /\
  clock (dec_clock (set_permute p s)) = clock (dec_clock s).
Proof. intros; repeat split; reflexivity. Qed.

(** ** Shared memory *)

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "sh_mem_set_var_const" *)
Theorem sh_mem_set_var_const : forall r v (s : state) x s' outcome f l,
  sh_mem_set_var r v s = (x, s') ->
  clock s' = clock s /\
  compile_oracle s' = compile_oracle s /\
  compile s' = compile s /\
  be s' = be s /\
  gc_fun s' = gc_fun s /\
  mdomain s' = mdomain s /\
  sh_mdomain s' = sh_mdomain s /\
  code s' = code s /\
  code_buffer s' = code_buffer s /\
  data_buffer s' = data_buffer s /\
  permute s' = permute s /\
  handler s' = handler s /\
  stack_limit s' = stack_limit s /\
  stack_max s' = stack_max s /\
  (r = NONE -> ffi s' = ffi s) /\
  (r = SOME (FFI_final outcome) -> ffi s' = ffi s) /\
  (r = NONE -> locals_size s' = locals_size s) /\
  (r = SOME (FFI_return f l) -> locals_size s' = locals_size s) /\
  (r = NONE -> stack_max s' = stack_max s) /\
  (r = SOME (FFI_return f l) -> stack_max s' = stack_max s) /\
  (r = NONE -> state_stack_size s' = state_stack_size s) /\
  (r = SOME (FFI_return f l) -> state_stack_size s' = state_stack_size s).
Proof.
  intros r v s x s' outcome f l H; unfold sh_mem_set_var in H;
    destruct r as [[|]|]; injection H as <- <-; repeat split; intros; try discriminate;
    reflexivity.
Qed.

Local Ltac sh_store_tac H :=
  split_H H; leaf H; repeat split; intros; try discriminate; reflexivity.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "sh_mem_store_const" *)
Theorem sh_mem_store_const : forall ad v (s : state) res s',
  sh_mem_store ad v s = (res, s') ->
  clock s' = clock s /\
  compile_oracle s' = compile_oracle s /\
  compile s' = compile s /\
  be s' = be s /\
  gc_fun s' = gc_fun s /\
  mdomain s' = mdomain s /\
  sh_mdomain s' = sh_mdomain s /\
  code s' = code s /\
  code_buffer s' = code_buffer s /\
  data_buffer s' = data_buffer s /\
  permute s' = permute s /\
  handler s' = handler s /\
  stack_limit s' = stack_limit s /\
  stack_max s' = stack_max s /\
  (res = SOME Error -> locals_size s' = locals_size s) /\
  (res = NONE -> locals_size s' = locals_size s) /\
  (res = NONE -> stack_max s' = stack_max s) /\
  (res = SOME Error -> stack_max s' = stack_max s) /\
  (res = NONE -> state_stack_size s' = state_stack_size s) /\
  (res = SOME Error -> state_stack_size s' = state_stack_size s).
Proof. intros ad v s res s' H; unfold sh_mem_store in H; sh_store_tac H. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "sh_mem_store_byte_const" *)
Theorem sh_mem_store_byte_const : forall ad v (s : state) res s',
  sh_mem_store_byte ad v s = (res, s') ->
  clock s' = clock s /\
  compile_oracle s' = compile_oracle s /\
  compile s' = compile s /\
  be s' = be s /\
  gc_fun s' = gc_fun s /\
  mdomain s' = mdomain s /\
  sh_mdomain s' = sh_mdomain s /\
  code s' = code s /\
  code_buffer s' = code_buffer s /\
  data_buffer s' = data_buffer s /\
  permute s' = permute s /\
  handler s' = handler s /\
  stack_limit s' = stack_limit s /\
  stack_max s' = stack_max s /\
  (res = SOME Error -> locals_size s' = locals_size s) /\
  (res = NONE -> locals_size s' = locals_size s) /\
  (res = NONE -> stack_max s' = stack_max s) /\
  (res = SOME Error -> stack_max s' = stack_max s) /\
  (res = NONE -> state_stack_size s' = state_stack_size s) /\
  (res = SOME Error -> state_stack_size s' = state_stack_size s).
Proof. intros ad v s res s' H; unfold sh_mem_store_byte in H; sh_store_tac H. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "sh_mem_store16_const" *)
Theorem sh_mem_store16_const : forall ad v (s : state) res s',
  sh_mem_store16 ad v s = (res, s') ->
  clock s' = clock s /\
  compile_oracle s' = compile_oracle s /\
  compile s' = compile s /\
  be s' = be s /\
  gc_fun s' = gc_fun s /\
  mdomain s' = mdomain s /\
  sh_mdomain s' = sh_mdomain s /\
  code s' = code s /\
  code_buffer s' = code_buffer s /\
  data_buffer s' = data_buffer s /\
  permute s' = permute s /\
  handler s' = handler s /\
  stack_limit s' = stack_limit s /\
  stack_max s' = stack_max s /\
  (res = SOME Error -> locals_size s' = locals_size s) /\
  (res = NONE -> locals_size s' = locals_size s) /\
  (res = NONE -> stack_max s' = stack_max s) /\
  (res = SOME Error -> stack_max s' = stack_max s) /\
  (res = NONE -> state_stack_size s' = state_stack_size s) /\
  (res = SOME Error -> state_stack_size s' = state_stack_size s).
Proof. intros ad v s res s' H; unfold sh_mem_store16 in H; sh_store_tac H. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "sh_mem_store32_const" *)
Theorem sh_mem_store32_const : forall ad v (s : state) res s',
  sh_mem_store32 ad v s = (res, s') ->
  clock s' = clock s /\
  compile_oracle s' = compile_oracle s /\
  compile s' = compile s /\
  be s' = be s /\
  gc_fun s' = gc_fun s /\
  mdomain s' = mdomain s /\
  sh_mdomain s' = sh_mdomain s /\
  code s' = code s /\
  code_buffer s' = code_buffer s /\
  data_buffer s' = data_buffer s /\
  permute s' = permute s /\
  handler s' = handler s /\
  stack_limit s' = stack_limit s /\
  stack_max s' = stack_max s /\
  (res = SOME Error -> locals_size s' = locals_size s) /\
  (res = NONE -> locals_size s' = locals_size s) /\
  (res = NONE -> stack_max s' = stack_max s) /\
  (res = SOME Error -> stack_max s' = stack_max s) /\
  (res = NONE -> state_stack_size s' = state_stack_size s) /\
  (res = SOME Error -> state_stack_size s' = state_stack_size s).
Proof. intros ad v s res s' H; unfold sh_mem_store32 in H; sh_store_tac H. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "sh_mem_set_var_with_const" *)
Theorem sh_mem_set_var_with_const : forall res v (s : state) p k,
  sh_mem_set_var res v (set_permute p s) = PAIR_MAP I (fun s => set_permute p s) (sh_mem_set_var res v s) /\
  sh_mem_set_var res v (set_clock k s) = PAIR_MAP I (fun s => set_clock k s) (sh_mem_set_var res v s).
Proof. intros [[|]|] v s p k; split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "sh_mem_load_with_const" *)
Theorem sh_mem_load_with_const : forall ad (s : state) l p k xs,
  sh_mem_load ad (set_locals l s) = sh_mem_load ad s /\
  sh_mem_load ad (set_permute p s) = sh_mem_load ad s /\
  sh_mem_load ad (set_clock k s) = sh_mem_load ad s /\
  sh_mem_load ad (set_stack xs s) = sh_mem_load ad s.
Proof. intros; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "sh_mem_load_byte_with_const" *)
Theorem sh_mem_load_byte_with_const : forall ad (s : state) l p k xs,
  sh_mem_load_byte ad (set_locals l s) = sh_mem_load_byte ad s /\
  sh_mem_load_byte ad (set_permute p s) = sh_mem_load_byte ad s /\
  sh_mem_load_byte ad (set_clock k s) = sh_mem_load_byte ad s /\
  sh_mem_load_byte ad (set_stack xs s) = sh_mem_load_byte ad s.
Proof. intros; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "sh_mem_load16_with_const" *)
Theorem sh_mem_load16_with_const : forall ad (s : state) l p k xs,
  sh_mem_load16 ad (set_locals l s) = sh_mem_load16 ad s /\
  sh_mem_load16 ad (set_permute p s) = sh_mem_load16 ad s /\
  sh_mem_load16 ad (set_clock k s) = sh_mem_load16 ad s /\
  sh_mem_load16 ad (set_stack xs s) = sh_mem_load16 ad s.
Proof. intros; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "sh_mem_load32_with_const" *)
Theorem sh_mem_load32_with_const : forall ad (s : state) l p k xs,
  sh_mem_load32 ad (set_locals l s) = sh_mem_load32 ad s /\
  sh_mem_load32 ad (set_permute p s) = sh_mem_load32 ad s /\
  sh_mem_load32 ad (set_clock k s) = sh_mem_load32 ad s /\
  sh_mem_load32 ad (set_stack xs s) = sh_mem_load32 ad s.
Proof. intros; repeat split; reflexivity. Qed.

Local Ltac sh_with_tac :=
  intros; split; cbn [sh_mdomain ffi set_clock set_permute];
  (destruct (classical_dec _); [|reflexivity]; destruct (call_FFI _ _ _ _); reflexivity).

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "sh_mem_store_with_const" *)
Theorem sh_mem_store_with_const : forall ad w (s : state) p k,
  sh_mem_store ad w (set_permute p s) = PAIR_MAP I (fun s => set_permute p s) (sh_mem_store ad w s) /\
  sh_mem_store ad w (set_clock k s) = PAIR_MAP I (fun s => set_clock k s) (sh_mem_store ad w s).
Proof. unfold sh_mem_store; sh_with_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "sh_mem_store_byte_with_const" *)
Theorem sh_mem_store_byte_with_const : forall ad w (s : state) p k,
  sh_mem_store_byte ad w (set_permute p s) =
    PAIR_MAP I (fun s => set_permute p s) (sh_mem_store_byte ad w s) /\
  sh_mem_store_byte ad w (set_clock k s) =
    PAIR_MAP I (fun s => set_clock k s) (sh_mem_store_byte ad w s).
Proof. unfold sh_mem_store_byte; sh_with_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "sh_mem_store16_with_const" *)
Theorem sh_mem_store16_with_const : forall ad w (s : state) p k,
  sh_mem_store16 ad w (set_permute p s) =
    PAIR_MAP I (fun s => set_permute p s) (sh_mem_store16 ad w s) /\
  sh_mem_store16 ad w (set_clock k s) =
    PAIR_MAP I (fun s => set_clock k s) (sh_mem_store16 ad w s).
Proof. unfold sh_mem_store16; sh_with_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "sh_mem_store32_with_const" *)
Theorem sh_mem_store32_with_const : forall ad w (s : state) p k,
  sh_mem_store32 ad w (set_permute p s) =
    PAIR_MAP I (fun s => set_permute p s) (sh_mem_store32 ad w s) /\
  sh_mem_store32 ad w (set_clock k s) =
    PAIR_MAP I (fun s => set_clock k s) (sh_mem_store32 ad w s).
Proof. unfold sh_mem_store32; sh_with_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "share_inst_with_const" *)
Theorem share_inst_with_const : forall op v c0 (s : state) p k,
  share_inst op v c0 (set_permute p s) = PAIR_MAP I (fun s => set_permute p s) (share_inst op v c0 s) /\
  share_inst op v c0 (set_clock k s) = PAIR_MAP I (fun s => set_clock k s) (share_inst op v c0 s).
Proof.
  intros; destruct op; cbn [share_inst];
    unfold sh_mem_set_var, sh_mem_load, sh_mem_load_byte, sh_mem_load16, sh_mem_load32,
      sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32;
    split; cbn [sh_mdomain ffi set_clock set_permute]; unfold get_var; cbn [locals set_clock set_permute];
    split_all; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "cut_state_with_const" *)
Theorem cut_state_with_const : forall x (z : state) k code0 c0 co perm xs,
  cut_state x (set_clock k z) = OPTION_MAP (fun s => set_clock k s) (cut_state x z) /\
  cut_state x (set_code code0 z) = OPTION_MAP (fun s => set_code code0 s) (cut_state x z) /\
  cut_state x (set_compile c0 z) = OPTION_MAP (fun s => set_compile c0 s) (cut_state x z) /\
  cut_state x (set_compile_oracle co z) = OPTION_MAP (fun s => set_compile_oracle co s) (cut_state x z) /\
  cut_state x (set_permute perm z) = OPTION_MAP (fun s => set_permute perm s) (cut_state x z) /\
  cut_state x (set_stack xs z) = OPTION_MAP (fun s => set_stack xs s) (cut_state x z).
Proof.
  intros; unfold cut_state; repeat split; cbn [locals set_clock set_code set_compile
    set_compile_oracle set_permute set_stack]; destruct (cut_env _ _); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "cut_state_const" *)
Theorem cut_state_const : forall x (s s' : state),
  cut_state x s = SOME s' ->
  exists l, s' = set_locals l s.
Proof.
  intros x s s' H; unfold cut_state in H; destruct (cut_env _ _) as [l|]; [|discriminate].
  injection H as <-; exists l; reflexivity.
Qed.

(** ** [get]/[set] lemmas *)

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "get_var_set_store" *)
Theorem get_var_set_store : forall v1 v2 x (s : state),
  get_var v1 (set_store v2 x s) = get_var v1 s.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "get_var_set_fp_var" *)
Theorem get_var_set_fp_var : forall v1 v2 x (s : state),
  get_var v1 (set_fp_var v2 x s) = get_var v1 s.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "get_var_set_var" *)
Theorem get_var_set_var : forall v1 v2 x (s : state),
  get_var v1 (set_var v2 x s) = if decide (v1 = v2) then SOME x else get_var v1 s.
Proof.
  intros; unfold get_var, set_var; cbn [locals set_locals]. apply lookup_insert.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "get_store_set_store" *)
Theorem get_store_set_store : forall v1 v2 x (s : state),
  get_store v1 (set_store v2 x s) = if decide (v1 = v2) then SOME x else get_store v1 s.
Proof.
  intros; unfold get_store, set_store; cbn [store set_store_field]. rewrite FLOOKUP_UPDATE.
  destruct (decide (v1 = v2)), (decide (v2 = v1)); congruence.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "get_fp_var_set_fp_var" *)
Theorem get_fp_var_set_fp_var : forall v1 v2 x (s : state),
  get_fp_var v1 (set_fp_var v2 x s) = if decide (v1 = v2) then SOME x else get_fp_var v1 s.
Proof.
  intros; unfold get_fp_var, set_fp_var; cbn [fp_regs set_fp_regs]. rewrite FLOOKUP_UPDATE.
  destruct (decide (v1 = v2)), (decide (v2 = v1)); congruence.
Qed.

End WithConst.
