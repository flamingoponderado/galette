(** * CakeML [word_removeProof]: correctness of [word_remove]

    Port of [cakeml/compiler/backend/proofs/word_removeProofScript.sml].

    Notes:
    - HOL's free variable [c] (the compiler function stored in the state)
      is [c0] (the type of compiler configurations is the section variable
      [c], as in [wordSem]).  HOL [s with f := v] is [set_f v s]; HOL's
      [s.stack_size] is [state_stack_size s]; HOL's [I ## I ## f] ([##]
      associates to the right in HOL, to the left in Galette) is
      [I ## (I ## f)].
    - [push_env_case_handler]: HOL's free variable [handler] is [h] (it
      would shadow the state field [handler]).
    - HOL's [compile_state_update] lists the [memory] update twice; both
      conjuncts are kept.
    - Proof method of [word_remove_correct]: well-founded induction on
      [eval_lt] with [evaluate_eqn] (HOL: [recInduct evaluate_ind]).  The
      Galette-only helpers (the [compile_state] rewrite database and the
      tactic for the cases without recursive calls) have no HOL original. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common wordLang word_remove.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem wordConvs.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import
  consts consts_with clock dec_clock.
Open Scope N_scope.

Section CompileState.
Context {a : N} {c ffi_t : Type}.
Implicit Types s z : state a c ffi_t.
Local Abbreviation compile_fun :=
  (c -> list (N * (N * prog a)) -> option (list word8 * (list (word a) * c))).

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "compile_state_def" *)
Definition compile_state (clk : N) (c0 : compile_fun) (s : state a c ffi_t) : state a c ffi_t :=
  set_compile c0
    (set_compile_oracle ((I ## MAP (I ## (I ## remove_must_terminate))) ∘ compile_oracle s)
      (set_code (map (I ## remove_must_terminate) (code s))
        (set_termdep 0
          (set_clock (clock s + clk) s)))).

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "compile_state_const" *)
Theorem compile_state_const : forall clk c0 s,
  locals (compile_state clk c0 s) = locals s /\
  permute (compile_state clk c0 s) = permute s /\
  ffi (compile_state clk c0 s) = ffi s /\
  code_buffer (compile_state clk c0 s) = code_buffer s /\
  data_buffer (compile_state clk c0 s) = data_buffer s /\
  code (compile_state clk c0 s) = map (I ## remove_must_terminate) (code s) /\
  clock (compile_state clk c0 s) = clock s + clk /\
  termdep (compile_state clk c0 s) = 0 /\
  compile_oracle (compile_state clk c0 s) =
    (I ## MAP (I ## (I ## remove_must_terminate))) ∘ compile_oracle s /\
  compile (compile_state clk c0 s) = c0 /\
  stack (compile_state clk c0 s) = stack s /\
  store (compile_state clk c0 s) = store s /\
  fp_regs (compile_state clk c0 s) = fp_regs s /\
  memory (compile_state clk c0 s) = memory s /\
  mdomain (compile_state clk c0 s) = mdomain s /\
  sh_mdomain (compile_state clk c0 s) = sh_mdomain s /\
  be (compile_state clk c0 s) = be s /\
  gc_fun (compile_state clk c0 s) = gc_fun s /\
  handler (compile_state clk c0 s) = handler s /\
  locals_size (compile_state clk c0 s) = locals_size s /\
  state_stack_size (compile_state clk c0 s) = state_stack_size s /\
  stack_max (compile_state clk c0 s) = stack_max s /\
  stack_limit (compile_state clk c0 s) = stack_limit s.
Proof. intros; repeat split. Qed.

End CompileState.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "find_code_map_I" *)
Theorem find_code_map_I : forall {a} d (l : list (word_loc a)) (f : prog a -> prog a) t lsz,
  find_code d l (map (I ## f) t) lsz = OPTION_MAP (I ## (f ## I)) (find_code d l t lsz).
Proof.
  intros a [d|] l f t lsz; unfold find_code; rewrite ?lookup_map.
  - destruct (lookup d t) as [[ar e]|]; cbn; [|reflexivity].
    destruct (_ =? _); reflexivity.
  - destruct (bool_decide _); [reflexivity|].
    destruct (LAST l) as [w|l1 l2]; [reflexivity|].
    destruct (l2 =? 0); [|reflexivity].
    rewrite lookup_map. destruct (lookup l1 t) as [[ar e]|]; cbn; [|reflexivity].
    destruct (_ =? _); reflexivity.
Qed.

Section CompileStateLemmas.
Context {a : N} {c ffi_t : Type}.
Implicit Types s z : state a c ffi_t.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "compile_state_update" *)
Theorem compile_state_update : forall clk c0 s f1 f2 f10 f9 f8 f7 f6 f5 f4 f11 f3 f12 f13 f14 f15,
  set_stack f1 (compile_state clk c0 s) = compile_state clk c0 (set_stack f1 s) /\
  set_permute f2 (compile_state clk c0 s) = compile_state clk c0 (set_permute f2 s) /\
  set_ffi f10 (compile_state clk c0 s) = compile_state clk c0 (set_ffi f10 s) /\
  set_data_buffer f9 (compile_state clk c0 s) = compile_state clk c0 (set_data_buffer f9 s) /\
  set_code_buffer f8 (compile_state clk c0 s) = compile_state clk c0 (set_code_buffer f8 s) /\
  set_memory f7 (compile_state clk c0 s) = compile_state clk c0 (set_memory f7 s) /\
  set_locals f6 (compile_state clk c0 s) = compile_state clk c0 (set_locals f6 s) /\
  set_memory f5 (compile_state clk c0 s) = compile_state clk c0 (set_memory f5 s) /\
  set_store_field f4 (compile_state clk c0 s) = compile_state clk c0 (set_store_field f4 s) /\
  set_fp_regs f11 (compile_state clk c0 s) = compile_state clk c0 (set_fp_regs f11 s) /\
  set_handler f3 (compile_state clk c0 s) = compile_state clk c0 (set_handler f3 s) /\
  set_locals_size f12 (compile_state clk c0 s) = compile_state clk c0 (set_locals_size f12 s) /\
  set_stack_size f13 (compile_state clk c0 s) = compile_state clk c0 (set_stack_size f13 s) /\
  set_stack_max f14 (compile_state clk c0 s) = compile_state clk c0 (set_stack_max f14 s) /\
  set_stack_limit f15 (compile_state clk c0 s) = compile_state clk c0 (set_stack_limit f15 s).
Proof. intros; repeat split. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "get_var_compile_state" *)
Theorem get_var_compile_state : forall x clk c0 s,
  get_var x (compile_state clk c0 s) = get_var x s.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "get_fp_var_compile_state" *)
Theorem get_fp_var_compile_state : forall x clk c0 s,
  get_fp_var x (compile_state clk c0 s) = get_fp_var x s.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "get_vars_compile_state" *)
Theorem get_vars_compile_state : forall xs clk c0 s,
  get_vars xs (compile_state clk c0 s) = get_vars xs s.
Proof. induction xs as [|x xs IH]; intros; cbn; [reflexivity|]. rewrite IH; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "set_var_compile_state" *)
Theorem set_var_compile_state : forall x y clk c0 s,
  set_var x y (compile_state clk c0 s) = compile_state clk c0 (set_var x y s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "unset_var_compile_state" *)
Theorem unset_var_compile_state : forall x clk c0 s,
  unset_var x (compile_state clk c0 s) = compile_state clk c0 (unset_var x s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "set_fp_var_compile_state" *)
Theorem set_fp_var_compile_state : forall x y clk c0 s,
  set_fp_var x y (compile_state clk c0 s) = compile_state clk c0 (set_fp_var x y s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "set_vars_compile_state" *)
Theorem set_vars_compile_state : forall xs ys clk c0 s,
  set_vars xs ys (compile_state clk c0 s) = compile_state clk c0 (set_vars xs ys s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "get_store_compile_state" *)
Theorem get_store_compile_state : forall x clk c0 s,
  get_store x (compile_state clk c0 s) = get_store x s.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "set_store_compile_state" *)
Theorem set_store_compile_state : forall x y clk c0 s,
  set_store x y (compile_state clk c0 s) = compile_state clk c0 (set_store x y s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "push_env_compile_state" *)
Theorem push_env_compile_state : forall env h clk c0 s,
  push_env env h (compile_state clk c0 s) = compile_state clk c0 (push_env env h s).
Proof.
  intros env [[? [? [? ?]]]|] clk c0 s; unfold push_env; cbn [permute compile_state
    set_compile set_compile_oracle set_code set_termdep set_clock];
    destruct (env_to_list _ _); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "pop_env_compile_state" *)
Theorem pop_env_compile_state : forall clk c0 s,
  pop_env (compile_state clk c0 s) = OPTION_MAP (compile_state clk c0) (pop_env s).
Proof.
  intros clk c0 s; unfold pop_env; cbn [stack compile_state set_compile set_compile_oracle
    set_code set_termdep set_clock].
  destruct (stack s) as [|[m e0 e [[n x]|]] xs]; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "call_env_compile_state" *)
Theorem call_env_compile_state : forall x lsz clk c0 z,
  call_env x lsz (compile_state clk c0 z) = compile_state clk c0 (call_env x lsz z).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "flush_state_compile_state" *)
Theorem flush_state_compile_state : forall x clk c0 z,
  flush_state x (compile_state clk c0 z) = compile_state clk c0 (flush_state x z).
Proof. intros [] clk c0 z; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "has_space_compile_state" *)
Theorem has_space_compile_state : forall n clk c0 s,
  has_space n (compile_state clk c0 s) = has_space n s.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "gc_compile_state" *)
Theorem gc_compile_state : forall clk c0 s,
  gc (compile_state clk c0 s) = OPTION_MAP (compile_state clk c0) (gc s).
Proof.
  intros clk c0 s; unfold gc; cbn [stack memory mdomain store gc_fun compile_state set_compile
    set_compile_oracle set_code set_termdep set_clock].
  destruct (gc_fun s _) as [[wl [m st]]|]; [|reflexivity].
  destruct (dec_stack wl (stack s)); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "alloc_compile_state" *)
Theorem alloc_compile_state : forall w names clk c0 s,
  alloc w names (compile_state clk c0 s) = (I ## compile_state clk c0) (alloc w names s).
Proof.
  intros w names clk c0 s; unfold alloc.
  change (locals (compile_state clk c0 s)) with (locals s).
  destruct (cut_envs _ _) as [envs|]; [|(cbn [PAIR_MAP I]; rewrite flush_state_compile_state; reflexivity)].
  rewrite set_store_compile_state, push_env_compile_state, gc_compile_state.
  destruct (gc _) as [s1|]; cbn [OPTION_MAP option_map]; [|(cbn [PAIR_MAP I]; rewrite flush_state_compile_state; reflexivity)].
  rewrite pop_env_compile_state. destruct (pop_env s1) as [s2|]; cbn [option_map];
    [|(cbn [PAIR_MAP I]; rewrite flush_state_compile_state; reflexivity)].
  change (get_store ?x (compile_state clk c0 s2)) with (get_store x s2).
  destruct (get_store _ _) as [w'|]; [|reflexivity].
  change (has_space ?x (compile_state clk c0 s2)) with (has_space x s2).
  destruct (has_space _ _) as [[]|]; [reflexivity|(cbn [PAIR_MAP I]; rewrite flush_state_compile_state; reflexivity)|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "mem_load_compile_state" *)
Theorem mem_load_compile_state : forall w clk c0 s,
  mem_load w (compile_state clk c0 s) = mem_load w s.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "mem_store_compile_state" *)
Theorem mem_store_compile_state : forall x y clk c0 s,
  mem_store x y (compile_state clk c0 s) = OPTION_MAP (compile_state clk c0) (mem_store x y s).
Proof.
  intros; unfold mem_store; cbn [mdomain compile_state set_compile set_compile_oracle set_code
    set_termdep set_clock].
  destruct (classical_dec _); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "word_exp_compile_state" *)
Theorem word_exp_compile_state : forall clk c0 s y,
  word_exp (compile_state clk c0 s) y = word_exp s y.
Proof. intros; apply word_exp_state_cong; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "assign_compile_state" *)
Theorem assign_compile_state : forall x y clk c0 s,
  assign x y (compile_state clk c0 s) = OPTION_MAP (compile_state clk c0) (assign x y s).
Proof.
  intros; unfold assign; rewrite word_exp_compile_state. destruct (word_exp s y); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "inst_compile_state" *)
Theorem inst_compile_state : forall i clk c0 s,
  inst i (compile_state clk c0 s) = OPTION_MAP (compile_state clk c0) (inst i s).
Proof.
  intros i clk c0 s.
  destruct i as [|r w|ar|m r [ad w]|f];
    [reflexivity| |destruct ar|destruct m|destruct f];
    cbn [inst]; unfold assign; rewrite ?word_exp_compile_state, ?get_vars_compile_state;
    repeat first
      [ progress (rewrite ?mem_load_compile_state, ?get_fp_var_compile_state,
                    ?mem_store_compile_state, ?get_var_compile_state)
      | match goal with
        | |- context [memory (compile_state ?k ?f ?t)] =>
            change (memory (compile_state k f t)) with (memory t)
        | |- context [mdomain (compile_state ?k ?f ?t)] =>
            change (mdomain (compile_state k f t)) with (mdomain t)
        | |- context [be (compile_state ?k ?f ?t)] =>
            change (be (compile_state k f t)) with (be t)
        end
      | match goal with
        | |- context [match ?x with _ => _ end] =>
            lazymatch x with context [compile_state] => fail | _ => idtac end;
            let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
        end ];
    reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "cut_state_compile_state" *)
Theorem cut_state_compile_state : forall names clk c0 s,
  cut_state names (compile_state clk c0 s) = OPTION_MAP (compile_state clk c0) (cut_state names s).
Proof.
  intros; unfold cut_state; cbn [locals compile_state set_compile set_compile_oracle set_code
    set_termdep set_clock].
  destruct (cut_env _ _); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "evaluate_add_clock_compile_state" *)
Theorem evaluate_add_clock_compile_state : forall (p : prog a) clk c0 s res s',
  evaluate (p, compile_state clk c0 s) = (res, compile_state 0 c0 s') /\
  res <> SOME TimeOut ->
  forall extra, evaluate (p, compile_state (clk + extra) c0 s) =
                (res, compile_state extra c0 s').
Proof.
  intros p clk c0 s res s' H extra.
  pose proof (evaluate_add_clock extra p _ _ _ H) as E.
  replace (compile_state (clk + extra) c0 s)
    with (set_clock (clock (compile_state clk c0 s) + extra) (compile_state clk c0 s)).
  2:{ apply state_component_equality; cbn; repeat split; lia. }
  rewrite E; f_equal. apply state_component_equality; cbn; repeat split; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "compile_state_dec_clock" *)
Theorem compile_state_dec_clock : forall clk c0 s,
  clock s <> 0 -> compile_state clk c0 (dec_clock s) = dec_clock (compile_state clk c0 s).
Proof. intros; apply state_component_equality; cbn; repeat split; lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "jump_exc_compile_state" *)
Theorem jump_exc_compile_state : forall clk c0 s,
  jump_exc (compile_state clk c0 s) = OPTION_MAP (compile_state clk c0 ## I) (jump_exc s).
Proof.
  intros; unfold jump_exc; cbn [handler stack compile_state set_compile set_compile_oracle
    set_code set_termdep set_clock].
  destruct (_ <? _); [|reflexivity].
  destruct (LASTN _ _) as [|[m e0 e [[n [l1 l2]]|]] xs]; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "get_var_imm_compile_state" *)
Theorem get_var_imm_compile_state : forall x clk c0 s,
  get_var_imm x (compile_state clk c0 s) = get_var_imm x s.
Proof. intros [] clk c0 s; reflexivity. Qed.

End CompileStateLemmas.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "push_env_case_handler" *)
Theorem push_env_case_handler : forall {a c ffi_t} x (h : option (N * (prog a * (N * N))))
    (f : prog a -> prog a),
  @push_env a c ffi_t x
    (match h with NONE => NONE | SOME (v, (prog, (l1, l2))) => SOME (v, (f prog, (l1, l2))) end) =
  push_env x h.
Proof. intros a c ffi_t x [[v [p [l1 l2]]]|] f; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "pair_map_I" *)
Theorem pair_map_I : forall {A B C} (f : B -> C),
  (fun '(k, v) => (k, f v)) = (I ## f : A * B -> A * C) /\
  (fun '(k, v) => (f k, v)) = (f ## I : B * A -> C * A).
Proof. intros; split; apply functional_extensionality; intros [x y]; reflexivity. Qed.

(** ** Correctness *)

(** Galette-only: rewriting the target state outwards. *)
Create Rewrite HintDb word_remove_cs.
Global Hint Rewrite @get_var_compile_state @get_fp_var_compile_state @get_vars_compile_state
  @set_var_compile_state @unset_var_compile_state @set_fp_var_compile_state
  @set_vars_compile_state @get_store_compile_state @set_store_compile_state
  @push_env_compile_state @pop_env_compile_state @call_env_compile_state
  @flush_state_compile_state @has_space_compile_state @gc_compile_state @alloc_compile_state
  @mem_load_compile_state @mem_store_compile_state @word_exp_compile_state
  @assign_compile_state @inst_compile_state @cut_state_compile_state @jump_exc_compile_state
  @get_var_imm_compile_state @push_env_case_handler : word_remove_cs.

Section Correct.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

Lemma cs_set_stack xs clk c0 s :
  set_stack xs (compile_state clk c0 s) = compile_state clk c0 (set_stack xs s).
Proof. reflexivity. Qed.
Lemma cs_set_stack_max xs clk c0 s :
  set_stack_max xs (compile_state clk c0 s) = compile_state clk c0 (set_stack_max xs s).
Proof. reflexivity. Qed.
Lemma cs_set_code_buffer xs clk c0 s :
  set_code_buffer xs (compile_state clk c0 s) = compile_state clk c0 (set_code_buffer xs s).
Proof. reflexivity. Qed.
Lemma cs_set_data_buffer xs clk c0 s :
  set_data_buffer xs (compile_state clk c0 s) = compile_state clk c0 (set_data_buffer xs s).
Proof. reflexivity. Qed.
Lemma cs_set_memory xs clk c0 s :
  set_memory xs (compile_state clk c0 s) = compile_state clk c0 (set_memory xs s).
Proof. reflexivity. Qed.
Lemma cs_set_locals xs clk c0 s :
  set_locals xs (compile_state clk c0 s) = compile_state clk c0 (set_locals xs s).
Proof. reflexivity. Qed.
Lemma cs_set_fp_regs xs clk c0 s :
  set_fp_regs xs (compile_state clk c0 s) = compile_state clk c0 (set_fp_regs xs s).
Proof. reflexivity. Qed.
Lemma cs_set_ffi xs clk c0 s :
  set_ffi xs (compile_state clk c0 s) = compile_state clk c0 (set_ffi xs s).
Proof. reflexivity. Qed.
Lemma cs_dec_clock0 c0 s : dec_clock (compile_state 0 c0 s) = compile_state 0 c0 (dec_clock s).
Proof. apply state_component_equality; cbn; repeat split; lia. Qed.
Lemma cs_clock0 c0 s : clock (compile_state 0 c0 s) = clock s.
Proof. cbn; lia. Qed.
Lemma cs_code c0 clk s : code (compile_state clk c0 s) = map (I ## remove_must_terminate) (code s).
Proof. reflexivity. Qed.
Lemma cs_code_buffer c0 clk s : code_buffer (compile_state clk c0 s) = code_buffer s.
Proof. reflexivity. Qed.
Lemma cs_data_buffer c0 clk s : data_buffer (compile_state clk c0 s) = data_buffer s.
Proof. reflexivity. Qed.
Lemma cs_memory c0 clk s : memory (compile_state clk c0 s) = memory s.
Proof. reflexivity. Qed.
Lemma cs_mdomain c0 clk s : mdomain (compile_state clk c0 s) = mdomain s.
Proof. reflexivity. Qed.
Lemma cs_be c0 clk s : be (compile_state clk c0 s) = be s.
Proof. reflexivity. Qed.
Lemma cs_ffi c0 clk s : ffi (compile_state clk c0 s) = ffi s.
Proof. reflexivity. Qed.
Lemma cs_locals c0 clk s : locals (compile_state clk c0 s) = locals s.
Proof. reflexivity. Qed.
Lemma cs_compile c0 clk s : compile (compile_state clk c0 s) = c0.
Proof. reflexivity. Qed.

Lemma share_inst_compile_state op v ad clk c0 s :
  share_inst op v ad (compile_state clk c0 s) = (I ## compile_state clk c0) (share_inst op v ad s).
Proof.
  destruct op; cbn [share_inst];
    unfold sh_mem_set_var, sh_mem_load, sh_mem_load_byte, sh_mem_load16, sh_mem_load32,
      sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32;
    cbn [sh_mdomain ffi compile_state set_compile set_compile_oracle set_code set_termdep
      set_clock];
    rewrite ?get_var_compile_state;
    repeat match goal with
           | |- context [match ?x with _ => _ end] =>
               lazymatch x with context [compile_state] => fail | _ => idtac end;
               let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
           end; reflexivity.
Qed.

End Correct.

Global Hint Rewrite @cs_set_stack @cs_set_stack_max @cs_set_code_buffer @cs_set_data_buffer
  @cs_set_memory @cs_set_locals @cs_set_fp_regs @cs_set_ffi @cs_dec_clock0 @cs_clock0 @cs_code
  @cs_code_buffer @cs_data_buffer @cs_memory @cs_mdomain @cs_be @cs_ffi @cs_locals @cs_compile
  @share_inst_compile_state @domain_map @find_code_map_I : word_remove_cs.

Section Helpers.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

Lemma cs_clock clk c0 s : clock (compile_state clk c0 s) = clock s + clk.
Proof. reflexivity. Qed.
Lemma cs_state_stack_size clk c0 s :
  state_stack_size (compile_state clk c0 s) = state_stack_size s.
Proof. reflexivity. Qed.
Lemma cs_compile_oracle clk c0 s :
  compile_oracle (compile_state clk c0 s) =
  (I ## MAP (I ## (I ## remove_must_terminate))) ∘ compile_oracle s.
Proof. reflexivity. Qed.

Lemma add_ret_loc_rmt (ret : option (list N * (cutsets * (prog a * (N * N))))) xs :
  add_ret_loc
    (match ret with
     | None => None
     | Some (v, (cutset, (ret_handler, (l1, l2)))) =>
         Some (v, (cutset, (remove_must_terminate ret_handler, (l1, l2))))
     end) xs = add_ret_loc ret xs.
Proof. destruct ret as [[? [? [? [? ?]]]]|]; reflexivity. Qed.

Lemma bd_true (P : Prop) `{Decision P} : P -> bool_decide P = true.
Proof. apply bool_decide_spec. Qed.
Lemma bd_false (P : Prop) `{Decision P} : ~ P -> bool_decide P = false.
Proof. intros HP; destruct (bool_decide P) eqn:E; [|reflexivity]. apply bool_decide_spec in E; tauto. Qed.

Lemma bd_handler_rmt (h : option (N * (prog a * (N * N)))) :
  ⌜match h with
   | None => None
   | Some (v, (prog, (l1, l2))) => Some (v, (remove_must_terminate prog, (l1, l2)))
   end = NONE⌝ = ⌜h = NONE⌝.
Proof.
  destruct h as [[? [? [? ?]]]|].
  - rewrite !bd_false by discriminate; reflexivity.
  - rewrite !bd_true by reflexivity; reflexivity.
Qed.

Lemma FST_shift_seq_rmt (co : N -> c * list (N * (N * prog a))) k i :
  FST (shift_seq k ((I ## MAP (I ## (I ## remove_must_terminate))) ∘ co) i) =
  FST (shift_seq k co i).
Proof. unfold shift_seq; destruct (co (i + k)); reflexivity. Qed.

Lemma compile_push_env x y s : compile (push_env x y s) = compile s.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (push_env_const x y s)))))))))). Qed.

Lemma compile_pop_env s t : pop_env s = SOME t -> compile t = compile s.
Proof. intros H; exact (proj1 (proj2 (proj2 (proj2 (pop_env_const _ _ H))))). Qed.

Lemma compile_cut_state x s t : cut_state x s = SOME t -> compile t = compile s.
Proof. intros H; apply cut_state_const in H; destruct H as [l ->]; reflexivity. Qed.

Lemma compile_evaluate (p : prog a) s r t : evaluate (p, s) = (r, t) -> compile t = compile s.
Proof. intros H; symmetry; exact (proj1 (proj2 (proj2 (proj2 (proj2 (evaluate_consts _ _ _ _ H)))))). Qed.

Lemma cs_stack_max clk c0 s : stack_max (compile_state clk c0 s) = stack_max s.
Proof. reflexivity. Qed.
Lemma cs_stack clk c0 s : stack (compile_state clk c0 s) = stack s.
Proof. reflexivity. Qed.
Lemma push_env_SOME_rmt x v (p : prog a) l s :
  push_env x (SOME (v, (remove_must_terminate p, l))) s = push_env x (SOME (v, (p, l))) s.
Proof. destruct l; reflexivity. Qed.

End Helpers.

Global Hint Rewrite @cs_clock @cs_state_stack_size @cs_compile_oracle @add_ret_loc_rmt
  @bd_handler_rmt @FST_shift_seq_rmt N.add_0_r @cs_stack_max @cs_stack @push_env_SOME_rmt
  : word_remove_cs.

Ltac wr_state_eq :=
  apply state_component_equality;
  cbn [compile_state set_compile set_compile_oracle set_code set_termdep set_clock
       locals locals_size fp_regs store stack stack_limit stack_max state_stack_size memory
       mdomain sh_mdomain permute compile compile_oracle code_buffer data_buffer gc_fun
       handler clock termdep code be ffi];
  repeat split; try reflexivity; lia.

(** Galette-only: the tactics of the main proof. *)

(** Run the target program: push [compile_state] outwards and rewrite with
    the case equations and the evaluations of the context. *)
(** Rewrite the goal with the case equations of the context (as
    [wordProps.clock]'s [rw_cases], but matching the hypotheses first: the
    goals here are large). *)
Ltac wr_cases :=
  repeat match goal with
         | E : ?X = ?v |- _ =>
             lazymatch v with
             | true => idtac | false => idtac | SOME _ => idtac | NONE => idtac
             end;
             lazymatch goal with |- context [X] => idtac end;
             rewrite E; cbn beta iota zeta
         end.

Ltac wr_run :=
  repeat first
    [ progress (autorewrite with word_remove_cs)
    | progress wr_cases
    | progress (cbn [option_map PAIR_MAP I fst snd STOP List.map])
    | rewrite fix_clock_evaluate
    | match goal with
      | Hk : evaluate (?p, ?s) = _ |- context [evaluate (?p, ?s)] => rewrite Hk
      end ].

Ltac wr_contra Hr :=
  first [ exfalso; apply Hr; reflexivity | bd_contra | discriminate ].

(** The cases without recursive calls: run both sides with clock [0]. *)
(** Case split [H] (then the goal) and close. *)
Ltac wr_finish H Hr :=
  revert H;
  repeat match goal with
         | |- ?P -> _ =>
             match P with
             | context [match ?x with _ => _ end] =>
                 let E := fresh "E" in destruct x eqn:E;
                 cbn beta iota zeta; wr_run
             end
         end;
  intros H;
  repeat match goal with
         | |- context [match ?x with _ => _ end] =>
             lazymatch x with context [compile_state] => fail | _ => idtac end;
             let E := fresh "E" in destruct x eqn:E;
             cbn beta iota zeta; wr_run
         end;
  first
    [ rewrite H; reflexivity
    | injection H as <- <-;
      first [ wr_contra Hr
            | reflexivity
            | f_equal; apply state_component_equality; cbn;
              repeat split; try reflexivity;
              rewrite map_union, ?map_insert, map_fromAList; repeat f_equal;
              apply functional_extensionality; intros [? ?]; reflexivity ] ].

Ltac wr_simple H Hr :=
  exists 0; rewrite evaluate_eqn; cbn [evaluate_body]; wr_run; wr_finish H Hr.


Section Main.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(** HOL's free variable [c] (the compiler function) is quantified first. *)
(*! HOL "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "word_remove_correct" *)
Theorem word_remove_correct : forall c0 (prog : prog a) (st : state) res rst,
  evaluate (prog, st) = (res, rst) /\
  compile st = (fun cfg => c0 cfg ∘ MAP (I ## (I ## remove_must_terminate))) /\
  res <> SOME Error ->
  exists clk,
    evaluate (remove_must_terminate prog, compile_state clk c0 st) =
    (res, compile_state 0 c0 rst).
Proof.
  intros c0.
  enough (G : forall x : prog a * state, forall res rst,
    evaluate x = (res, rst) ->
    compile (snd x) = (fun cfg => c0 cfg ∘ MAP (I ## (I ## remove_must_terminate))) ->
    res <> SOME Error ->
    exists clk, evaluate (remove_must_terminate (fst x), compile_state clk c0 (snd x)) =
                (res, compile_state 0 c0 rst))
    by (intros p st res rst (H & Hc & Hr); exact (G (p, st) res rst H Hc Hr)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros res rst H Hc Hr; cbn [fst snd] in *.
  rewrite evaluate_eqn in H.
  destruct p; cbn [evaluate_body] in H; cbn [remove_must_terminate];
    rewrite ?fix_clock_evaluate in H.
  all: try (rewrite Hc in H; cbn beta in H).
  all: try solve [wr_simple H Hr].
  - (* MustTerminate *)
    destruct (termdep s =? 0) eqn:Et; [injection H as <- <-; wr_contra Hr|].
    apply N.eqb_neq in Et.
    destruct (evaluate (p, set_termdep (termdep s - 1) (set_clock (MustTerminate_limit a) s)))
      as [r1 t1] eqn:E1.
    destruct (bool_decide (r1 = SOME TimeOut)) eqn:Eto; [injection H as <- <-; wr_contra Hr|].
    injection H as <- <-.
    assert (Hto : r1 <> SOME TimeOut) by (intros ->; bd_contra).
    pose proof (evaluate_dec_clock _ _ _ _ E1) as E2.
    pose proof (evaluate_add_clock (clock s) _ _ _ _ (conj E2 Hto)) as E3.
    match type of E3 with
    | evaluate ?x = _ =>
        assert (Hlt : eval_lt x (MustTerminate p, s))
          by (unfold eval_lt; cbn [fst snd clock termdep set_clock set_termdep]; lia);
        destruct (IH x Hlt _ _ E3 Hc Hr) as [clk Hk]
    end.
    cbn [fst snd FST SND] in Hk.
    exists (clk + (MustTerminate_limit a - clock t1)).
    match type of Hk with
    | evaluate (_, ?X) = _ =>
        replace (compile_state (clk + (MustTerminate_limit a - clock t1)) c0 s) with X
          by wr_state_eq
    end.
    rewrite Hk; f_equal; wr_state_eq.
  - (* Call *)
    destruct (get_vars l s) as [xs|] eqn:Eg; [|injection H as <- <-; wr_contra Hr].
    destruct (bad_dest_args o0 l) eqn:Ebd; [injection H as <- <-; wr_contra Hr|].
    destruct (find_code o0 (add_ret_loc o xs) (code s) (state_stack_size s))
      as [[args1 [q ss]]|] eqn:Ef; [|injection H as <- <-; wr_contra Hr].
    destruct o as [[n [names [rh [l1 l2]]]]|]; cbn [add_ret_loc] in Ef.
    + destruct (⌜domain (FST names) = {}⌝ || negb (ALL_DISTINCT n)) eqn:Ec1;
        [injection H as <- <-; wr_contra Hr|].
      destruct (cut_envs names (locals s)) as [envs|] eqn:Ece;
        [|injection H as <- <-; wr_contra Hr].
      destruct (clock s =? 0) eqn:Ez.
      { injection H as <- <-. exists 0. rewrite evaluate_eqn; cbn [evaluate_body add_ret_loc].
        wr_run. reflexivity. }
      rewrite ?fix_clock_evaluate in H.
      destruct (evaluate (q, call_env args1 ss (push_env envs o1 (dec_clock s))))
        as [r1 t1] eqn:E1.
      pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
      assert (HcS : compile (call_env args1 ss (push_env envs o1 (dec_clock s))) =
                    (fun cfg => c0 cfg ∘ MAP (I ## (I ## remove_must_terminate)))).
      { unfold call_env; cbn [compile set_stack_max set_locals_size set_locals].
        rewrite compile_push_env; exact Hc. }
      assert (Hct1 : compile t1 = (fun cfg => c0 cfg ∘ MAP (I ## (I ## remove_must_terminate))))
        by (rewrite (compile_evaluate _ _ _ _ E1); exact HcS).
      apply N.eqb_neq in Ez.
      destruct r1 as [[x ys|x y|k|k| | |f|]|];
        try (injection H as <- <-; wr_contra Hr).
      3-5: injection H as <- <-;
          destruct (IH (q, call_env args1 ss (push_env envs o1 (dec_clock s))) ltac:(wd_eval_lt) _ _ E1 HcS Hr) as [k1 Hk1]; cbn [fst snd FST SND] in Hk1;
          exists k1;
          assert (Ez' : (clock s + k1 =? 0) = false) by (apply N.eqb_neq; lia);
          rewrite evaluate_eqn; cbn [evaluate_body add_ret_loc];
          rewrite <- (compile_state_dec_clock k1 c0 s Ez); wr_run; reflexivity.
      * (* Result *)
        destruct (negb (bool_decide (x = Loc l1 l2)) || negb (LENGTH ys =? LENGTH n)) eqn:Ec2;
          [injection H as <- <-; wr_contra Hr|].
        destruct (pop_env t1) as [t2|] eqn:Ep; [|injection H as <- <-; wr_contra Hr].
        destruct (⌜domain (locals t2) = domain (FST envs) UNION domain (SND envs)⌝) eqn:Ed;
          [|injection H as <- <-; wr_contra Hr].
        assert (Hn1 : SOME (Result x ys) <> SOME Error) by discriminate.
        assert (Ht1 : SOME (Result x ys) <> SOME TimeOut) by discriminate.
        destruct (IH (q, call_env args1 ss (push_env envs o1 (dec_clock s))) ltac:(wd_eval_lt) _ _ E1 HcS Hn1) as [k1 Hk1]; cbn [fst snd FST SND] in Hk1.
        assert (Hc2 : compile (set_vars n ys t2) =
                      (fun cfg => c0 cfg ∘ MAP (I ## (I ## remove_must_terminate))))
          by (change (compile (set_vars n ys t2)) with (compile t2);
              rewrite (compile_pop_env _ _ Ep); exact Hct1).
        pose proof (pop_env_clock _ _ Ep) as Hpc.
        destruct (IH (rh, set_vars n ys t2) ltac:(wd_eval_lt) _ _ H Hc2 Hr) as [k2 Hk2].
        cbn [fst snd FST SND] in Hk2.
        pose proof (evaluate_add_clock_compile_state _ _ _ _ _ _ (conj Hk1 Ht1) k2) as Hk1'.
        exists (k1 + k2).
        assert (Ez' : (clock s + (k1 + k2) =? 0) = false) by (apply N.eqb_neq; lia).
        rewrite evaluate_eqn; cbn [evaluate_body add_ret_loc].
        rewrite <- (compile_state_dec_clock (k1 + k2) c0 s Ez). wr_run. reflexivity.
      * (* Exception *)
        assert (Hn1 : SOME (Exception x y) <> SOME Error) by discriminate.
        assert (Ht1 : SOME (Exception x y) <> SOME TimeOut) by discriminate.
        destruct (IH (q, call_env args1 ss (push_env envs o1 (dec_clock s))) ltac:(wd_eval_lt) _ _ E1 HcS Hn1) as [k1 Hk1]; cbn [fst snd FST SND] in Hk1.
        destruct o1 as [[hn [hp [hl1 hl2]]]|].
        -- destruct (negb (bool_decide (x = Loc hl1 hl2))) eqn:Ec2;
             [injection H as <- <-; wr_contra Hr|].
           destruct (⌜domain (locals t1) = domain (FST envs) UNION domain (SND envs)⌝) eqn:Ed;
             [|injection H as <- <-; wr_contra Hr].
           assert (Hc2 : compile (set_var hn y t1) =
                         (fun cfg => c0 cfg ∘ MAP (I ## (I ## remove_must_terminate))))
             by exact Hct1.
           destruct (IH (hp, set_var hn y t1) ltac:(wd_eval_lt) _ _ H Hc2 Hr) as [k2 Hk2].
           cbn [fst snd FST SND] in Hk2.
           pose proof (evaluate_add_clock_compile_state _ _ _ _ _ _ (conj Hk1 Ht1) k2) as Hk1'.
           exists (k1 + k2).
           assert (Ez' : (clock s + (k1 + k2) =? 0) = false) by (apply N.eqb_neq; lia).
           rewrite evaluate_eqn; cbn [evaluate_body add_ret_loc].
           rewrite <- (compile_state_dec_clock (k1 + k2) c0 s Ez). wr_run. reflexivity.
        -- injection H as <- <-. exists k1.
           assert (Ez' : (clock s + k1 =? 0) = false) by (apply N.eqb_neq; lia).
           rewrite evaluate_eqn; cbn [evaluate_body add_ret_loc].
           rewrite <- (compile_state_dec_clock k1 c0 s Ez). wr_run. reflexivity.
    + destruct (⌜o1 = NONE⌝) eqn:Eh; [|injection H as <- <-; wr_contra Hr].
      destruct (clock s =? 0) eqn:Ez.
      { injection H as <- <-. exists 0. rewrite evaluate_eqn; cbn [evaluate_body add_ret_loc].
        wr_run. reflexivity. }
      destruct (evaluate (q, call_env args1 ss (dec_clock s))) as [r1 t1] eqn:E1.
      destruct (bad_fun_return r1) eqn:Ebf; [injection H as <- <-; wr_contra Hr|].
      injection H as <- <-.
      apply N.eqb_neq in Ez.
      destruct (IH (q, call_env args1 ss (dec_clock s)) ltac:(wd_eval_lt) _ _ E1 Hc Hr) as [k1 Hk1]; cbn [fst snd FST SND] in Hk1.
      exists k1.
      assert (Ez' : (clock s + k1 =? 0) = false) by (apply N.eqb_neq; lia).
      rewrite evaluate_eqn; cbn [evaluate_body add_ret_loc].
      rewrite <- (compile_state_dec_clock k1 c0 s Ez). wr_run. reflexivity.
  - (* Seq *)
    destruct (evaluate (p1, s)) as [r1 s1] eqn:E1.
    pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
    destruct (bool_decide (r1 = NONE)) eqn:En.
    + apply bool_decide_spec in En; subst r1.
      assert (Hc' : compile s1 = (fun cfg => c0 cfg ∘ MAP (I ## (I ## remove_must_terminate))))
        by (rewrite (compile_evaluate _ _ _ _ E1); exact Hc).
      assert (Hn : (NONE : option (result a)) <> SOME Error) by discriminate.
      assert (Ht : (NONE : option (result a)) <> SOME TimeOut) by discriminate.
      destruct (IH (p1, s) ltac:(wd_eval_lt) _ _ E1 Hc Hn) as [k1 Hk1].
      destruct (IH (p2, s1) ltac:(wd_eval_lt) _ _ H Hc' Hr) as [k2 Hk2].
      cbn [fst snd FST SND] in Hk1, Hk2.
      exists (k1 + k2). rewrite evaluate_eqn; cbn [evaluate_body]; rewrite fix_clock_evaluate.
      rewrite (evaluate_add_clock_compile_state _ _ _ _ _ _ (conj Hk1 Ht) k2).
      rewrite bd_true by reflexivity. exact Hk2.
    + injection H as <- <-.
      destruct (IH (p1, s) ltac:(wd_eval_lt) _ _ E1 Hc Hr) as [k1 Hk1]. cbn [fst snd FST SND] in Hk1.
      exists k1. rewrite evaluate_eqn; cbn [evaluate_body]; rewrite fix_clock_evaluate, Hk1, En.
      reflexivity.
  - (* If *)
    split_H H; try (injection H as <- <-; wr_contra Hr);
    match type of H with
    | evaluate (?q, s) = _ =>
        destruct (IH (q, s) ltac:(wd_eval_lt) _ _ H Hc Hr) as [k Hk]; cbn [fst snd FST SND] in Hk;
        exists k; rewrite evaluate_eqn; cbn [evaluate_body]; wr_run; reflexivity
    end.
  - (* Loop *)
    destruct (cut_state (s0, LN) s) as [s'|] eqn:Ecut; [|injection H as <- <-; wr_contra Hr].
    rewrite ?fix_clock_evaluate in H.
    assert (Hcs : compile s' = (fun cfg => c0 cfg ∘ MAP (I ## (I ## remove_must_terminate))))
      by (rewrite (compile_cut_state _ _ _ Ecut); exact Hc).
    pose proof (cut_state_clock _ _ _ Ecut) as Hcl.
    destruct (evaluate (p, s')) as [r t1] eqn:E1.
    pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
    assert (Hct1 : compile t1 = (fun cfg => c0 cfg ∘ MAP (I ## (I ## remove_must_terminate))))
      by (rewrite (compile_evaluate _ _ _ _ E1); exact Hcs).
    destruct (cont_loop r) eqn:Ecl.
    + assert (Hto : r <> SOME TimeOut) by (apply cont_loop_not_timeout; exact Ecl).
      assert (Her : r <> SOME Error) by (intros ->; discriminate Ecl).
      destruct (IH (p, s') ltac:(wd_eval_lt) _ _ E1 Hcs Her) as [k1 Hk1]; cbn [fst snd FST SND] in Hk1.
      destruct (clock t1 =? 0) eqn:Ez.
      * injection H as <- <-. exists k1. rewrite evaluate_eqn; cbn [evaluate_body].
        wr_run. reflexivity.
      * unfold STOP in H. apply N.eqb_neq in Ez.
        assert (Hcd : compile (dec_clock t1) =
                      (fun cfg => c0 cfg ∘ MAP (I ## (I ## remove_must_terminate))))
          by exact Hct1.
        destruct (IH (Loop s0 p s1, dec_clock t1) ltac:(wd_eval_lt) _ _ H Hcd Hr) as [k2 Hk2].
        cbn [fst snd FST SND remove_must_terminate] in Hk2.
        exists (k1 + k2). rewrite evaluate_eqn; cbn [evaluate_body].
        rewrite cut_state_compile_state, Ecut; cbn [option_map]. rewrite fix_clock_evaluate.
        rewrite (evaluate_add_clock_compile_state _ _ _ _ _ _ (conj Hk1 Hto) k2), Ecl.
        assert (Ez' : (clock (compile_state k2 c0 t1) =? 0) = false)
          by (apply N.eqb_neq; cbn [clock compile_state set_compile set_compile_oracle set_code
                                    set_termdep set_clock]; lia).
        rewrite Ez'. rewrite <- (compile_state_dec_clock k2 c0 t1 Ez). unfold STOP. exact Hk2.
    + assert (Her : r <> SOME Error).
      { intros ->. destruct (bool_decide _) eqn:Eb in H; [bd_contra|]. cbn [exit_loop] in H.
        injection H as <- <-. apply Hr; reflexivity. }
      destruct (IH (p, s') ltac:(wd_eval_lt) _ _ E1 Hcs Her) as [k1 Hk1]; cbn [fst snd FST SND] in Hk1.
      exists k1. rewrite evaluate_eqn; cbn [evaluate_body].
      wr_run; wr_finish H Hr.
Qed.

End Main.
