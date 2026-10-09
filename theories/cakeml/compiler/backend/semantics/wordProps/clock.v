(** * CakeML [wordProps]: clock lemmas

    Port of the part of [cakeml/compiler/backend/semantics/wordPropsScript.sml]
    after the "CONST LEMMAS END" marker that deals with the clock: adding
    clock ([evaluate_add_clock]) and the monotonicity of the IO events
    ([evaluate_io_events_mono], [evaluate_add_clock_io_events_mono]).

    HOL's proofs are by [recInduct evaluate_ind]; here they are by
    well-founded induction on [eval_lt] with [evaluate_eqn].  HOL's
    [evaluate_clock_const] and [evaluate_clock_with_const] ([local]) are
    replaced by the Galette-only [set_clock] commutation lemmas of the
    section "Commuting with [set_clock]".  HOL [s with clock := k] is
    [set_clock k s]; HOL's [x ≼ y] is [isPREFIX x y]. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
From Galette.cakeml.misc Require Import misc.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.finite_maps Require Import finite_map sptree.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common wordLang.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import consts.
Open Scope N_scope.

(** ** Commuting with [set_clock] (Galette-only) *)

Section SetClock.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

Lemma locals_set_clock k s : locals (set_clock k s) = locals s. Proof. reflexivity. Qed.
Lemma locals_size_set_clock k s : locals_size (set_clock k s) = locals_size s. Proof. reflexivity. Qed.
Lemma fp_regs_set_clock k s : fp_regs (set_clock k s) = fp_regs s. Proof. reflexivity. Qed.
Lemma store_set_clock k s : store (set_clock k s) = store s. Proof. reflexivity. Qed.
Lemma stack_set_clock k s : stack (set_clock k s) = stack s. Proof. reflexivity. Qed.
Lemma stack_limit_set_clock k s : stack_limit (set_clock k s) = stack_limit s. Proof. reflexivity. Qed.
Lemma stack_max_set_clock k s : stack_max (set_clock k s) = stack_max s. Proof. reflexivity. Qed.
Lemma state_stack_size_set_clock k s : state_stack_size (set_clock k s) = state_stack_size s. Proof. reflexivity. Qed.
Lemma memory_set_clock k s : memory (set_clock k s) = memory s. Proof. reflexivity. Qed.
Lemma mdomain_set_clock k s : mdomain (set_clock k s) = mdomain s. Proof. reflexivity. Qed.
Lemma sh_mdomain_set_clock k s : sh_mdomain (set_clock k s) = sh_mdomain s. Proof. reflexivity. Qed.
Lemma permute_set_clock k s : permute (set_clock k s) = permute s. Proof. reflexivity. Qed.
Lemma compile_set_clock k s : compile (set_clock k s) = compile s. Proof. reflexivity. Qed.
Lemma compile_oracle_set_clock k s : compile_oracle (set_clock k s) = compile_oracle s. Proof. reflexivity. Qed.
Lemma code_buffer_set_clock k s : code_buffer (set_clock k s) = code_buffer s. Proof. reflexivity. Qed.
Lemma data_buffer_set_clock k s : data_buffer (set_clock k s) = data_buffer s. Proof. reflexivity. Qed.
Lemma gc_fun_set_clock k s : gc_fun (set_clock k s) = gc_fun s. Proof. reflexivity. Qed.
Lemma handler_set_clock k s : handler (set_clock k s) = handler s. Proof. reflexivity. Qed.
Lemma termdep_set_clock k s : termdep (set_clock k s) = termdep s. Proof. reflexivity. Qed.
Lemma code_set_clock k s : code (set_clock k s) = code s. Proof. reflexivity. Qed.
Lemma be_set_clock k s : be (set_clock k s) = be s. Proof. reflexivity. Qed.
Lemma ffi_set_clock k s : ffi (set_clock k s) = ffi s. Proof. reflexivity. Qed.
Lemma clock_set_clock k s : clock (set_clock k s) = k. Proof. reflexivity. Qed.
Lemma set_clock_set_clock k k' s : set_clock k (set_clock k' s) = set_clock k s. Proof. reflexivity. Qed.

Lemma set_locals_set_clock v k s : set_locals v (set_clock k s) = set_clock k (set_locals v s). Proof. reflexivity. Qed.
Lemma set_locals_size_set_clock v k s : set_locals_size v (set_clock k s) = set_clock k (set_locals_size v s). Proof. reflexivity. Qed.
Lemma set_fp_regs_set_clock v k s : set_fp_regs v (set_clock k s) = set_clock k (set_fp_regs v s). Proof. reflexivity. Qed.
Lemma set_store_field_set_clock v k s : set_store_field v (set_clock k s) = set_clock k (set_store_field v s). Proof. reflexivity. Qed.
Lemma set_stack_set_clock v k s : set_stack v (set_clock k s) = set_clock k (set_stack v s). Proof. reflexivity. Qed.
Lemma set_stack_limit_set_clock v k s : set_stack_limit v (set_clock k s) = set_clock k (set_stack_limit v s). Proof. reflexivity. Qed.
Lemma set_stack_max_set_clock v k s : set_stack_max v (set_clock k s) = set_clock k (set_stack_max v s). Proof. reflexivity. Qed.
Lemma set_stack_size_set_clock v k s : set_stack_size v (set_clock k s) = set_clock k (set_stack_size v s). Proof. reflexivity. Qed.
Lemma set_memory_set_clock v k s : set_memory v (set_clock k s) = set_clock k (set_memory v s). Proof. reflexivity. Qed.
Lemma set_mdomain_set_clock v k s : set_mdomain v (set_clock k s) = set_clock k (set_mdomain v s). Proof. reflexivity. Qed.
Lemma set_sh_mdomain_set_clock v k s : set_sh_mdomain v (set_clock k s) = set_clock k (set_sh_mdomain v s). Proof. reflexivity. Qed.
Lemma set_permute_set_clock v k s : set_permute v (set_clock k s) = set_clock k (set_permute v s). Proof. reflexivity. Qed.
Lemma set_compile_set_clock v k s : set_compile v (set_clock k s) = set_clock k (set_compile v s). Proof. reflexivity. Qed.
Lemma set_compile_oracle_set_clock v k s : set_compile_oracle v (set_clock k s) = set_clock k (set_compile_oracle v s). Proof. reflexivity. Qed.
Lemma set_code_buffer_set_clock v k s : set_code_buffer v (set_clock k s) = set_clock k (set_code_buffer v s). Proof. reflexivity. Qed.
Lemma set_data_buffer_set_clock v k s : set_data_buffer v (set_clock k s) = set_clock k (set_data_buffer v s). Proof. reflexivity. Qed.
Lemma set_gc_fun_set_clock v k s : set_gc_fun v (set_clock k s) = set_clock k (set_gc_fun v s). Proof. reflexivity. Qed.
Lemma set_handler_set_clock v k s : set_handler v (set_clock k s) = set_clock k (set_handler v s). Proof. reflexivity. Qed.
Lemma set_termdep_set_clock v k s : set_termdep v (set_clock k s) = set_clock k (set_termdep v s). Proof. reflexivity. Qed.
Lemma set_code_set_clock v k s : set_code v (set_clock k s) = set_clock k (set_code v s). Proof. reflexivity. Qed.
Lemma set_be_set_clock v k s : set_be v (set_clock k s) = set_clock k (set_be v s). Proof. reflexivity. Qed.
Lemma set_ffi_set_clock v k s : set_ffi v (set_clock k s) = set_clock k (set_ffi v s). Proof. reflexivity. Qed.

Lemma set_var_set_clock v x k s : set_var v x (set_clock k s) = set_clock k (set_var v x s). Proof. reflexivity. Qed.
Lemma unset_var_set_clock v k s : unset_var v (set_clock k s) = set_clock k (unset_var v s). Proof. reflexivity. Qed.
Lemma set_vars_set_clock vs xs k s : set_vars vs xs (set_clock k s) = set_clock k (set_vars vs xs s). Proof. reflexivity. Qed.
Lemma set_store_set_clock v x k s : set_store v x (set_clock k s) = set_clock k (set_store v x s). Proof. reflexivity. Qed.
Lemma set_fp_var_set_clock v x k s : set_fp_var v x (set_clock k s) = set_clock k (set_fp_var v x s). Proof. reflexivity. Qed.
Lemma flush_state_set_clock b k s : flush_state b (set_clock k s) = set_clock k (flush_state b s). Proof. destruct b; reflexivity. Qed.
Lemma call_env_set_clock x ss k s : call_env x ss (set_clock k s) = set_clock k (call_env x ss s). Proof. reflexivity. Qed.
Lemma dec_clock_eq s : dec_clock s = set_clock (clock s - 1) s. Proof. reflexivity. Qed.
Lemma push_env_set_clock x y k s : push_env x y (set_clock k s) = set_clock k (push_env x y s).
Proof. exact (proj1 (push_env_with_const x y s k (compile s) (compile_oracle s) (code s) (termdep s) (locals s))). Qed.
Lemma clock_push_env x y s : clock (push_env x y s) = clock s.
Proof. apply push_env_clock. Qed.
Lemma ffi_push_env x y s : ffi (push_env x y s) = ffi s.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (push_env_const x y s)))))). Qed.

Lemma get_var_set_clock v k s : get_var v (set_clock k s) = get_var v s. Proof. reflexivity. Qed.
Lemma get_vars_set_clock vs k s : get_vars vs (set_clock k s) = get_vars vs s.
Proof. induction vs as [|v vs IH]; cbn; [reflexivity|]. rewrite IH; reflexivity. Qed.
Lemma get_store_set_clock v k s : get_store v (set_clock k s) = get_store v s. Proof. reflexivity. Qed.
Lemma get_fp_var_set_clock v k s : get_fp_var v (set_clock k s) = get_fp_var v s. Proof. reflexivity. Qed.
Lemma mem_load_set_clock v k s : mem_load v (set_clock k s) = mem_load v s. Proof. reflexivity. Qed.
Lemma get_var_imm_set_clock ri k s : get_var_imm ri (set_clock k s) = get_var_imm ri s.
Proof. destruct ri; reflexivity. Qed.
Lemma has_space_set_clock x k s : has_space x (set_clock k s) = has_space x s. Proof. reflexivity. Qed.
Lemma word_exp_set_clock e k s : word_exp (set_clock k s) e = word_exp s e.
Proof. apply word_exp_state_cong; reflexivity. Qed.

Lemma mem_store_set_clock x y k s :
  mem_store x y (set_clock k s) = OPTION_MAP (set_clock k) (mem_store x y s).
Proof. unfold mem_store; cbn [mdomain set_clock]. destruct (classical_dec _); reflexivity. Qed.

Lemma cut_state_set_clock names k s :
  cut_state names (set_clock k s) = OPTION_MAP (set_clock k) (cut_state names s).
Proof. unfold cut_state; cbn [locals set_clock]. destruct (cut_env _ _); reflexivity. Qed.

Lemma pop_env_set_clock k s : pop_env (set_clock k s) = OPTION_MAP (set_clock k) (pop_env s).
Proof. exact (proj1 (pop_env_with_const s k (compile s) (compile_oracle s) (code s) (termdep s)
                     (permute s) (locals s) (locals_size s))). Qed.

Lemma gc_set_clock k s : gc (set_clock k s) = OPTION_MAP (set_clock k) (gc s).
Proof. exact (proj1 (gc_with_const s k (compile s) (compile_oracle s) (code s) (permute s)
                     (termdep s) (locals s) (locals_size s))). Qed.

Lemma jump_exc_set_clock k s :
  jump_exc (set_clock k s) = OPTION_MAP (fun '(s, t) => (set_clock k s, t)) (jump_exc s).
Proof.
  unfold jump_exc; cbn [handler stack set_clock].
  destruct (_ <? _); [|reflexivity].
  destruct (LASTN _ _) as [|[m e0 e [[n [l1 l2]]|]] xs]; reflexivity.
Qed.

Lemma inst_set_clock i k s : inst i (set_clock k s) = OPTION_MAP (set_clock k) (inst i s).
Proof.
  destruct i as [|r w|ar|m r [ad w]|f];
    [reflexivity| |destruct ar|destruct m|destruct f];
    cbn [inst]; unfold assign; rewrite ?word_exp_set_clock, ?get_vars_set_clock;
    repeat first
      [ progress (rewrite ?mem_load_set_clock, ?get_fp_var_set_clock, ?mem_store_set_clock, ?get_var_set_clock;
                  cbn [memory mdomain be set_clock])
      | match goal with
        | |- context [match ?x with _ => _ end] =>
            lazymatch x with context [set_clock] => fail | _ => idtac end;
            let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
        end ];
    reflexivity.
Qed.

Lemma alloc_set_clock w names k s :
  alloc w names (set_clock k s) = PAIR_MAP (fun r => r) (set_clock k) (alloc w names s).
Proof.
  unfold alloc; rewrite locals_set_clock.
  destruct (cut_envs _ _) as [envs|]; [|reflexivity].
  rewrite set_store_set_clock, push_env_set_clock, gc_set_clock.
  destruct (gc _) as [s1|]; cbn [OPTION_MAP option_map]; [|reflexivity].
  rewrite pop_env_set_clock. destruct (pop_env s1) as [s2|]; cbn [option_map]; [|reflexivity].
  rewrite get_store_set_clock. destruct (get_store _ _) as [w'|]; [|reflexivity].
  rewrite has_space_set_clock. destruct (has_space _ _) as [[]|]; reflexivity.
Qed.

Lemma share_inst_set_clock op v ad k s :
  share_inst op v ad (set_clock k s) = PAIR_MAP (fun r => r) (set_clock k) (share_inst op v ad s).
Proof.
  destruct op; cbn [share_inst];
    unfold sh_mem_set_var, sh_mem_load, sh_mem_load_byte, sh_mem_load16, sh_mem_load32,
      sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32;
    cbn [sh_mdomain ffi set_clock];
    rewrite ?get_var_set_clock;
    repeat match goal with
           | |- context [match ?x with _ => _ end] =>
               lazymatch x with context [set_clock] => fail | _ => idtac end;
               let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
           end; reflexivity.
Qed.

End SetClock.

Create Rewrite HintDb wdc.
Global Hint Rewrite @locals_set_clock @locals_size_set_clock @fp_regs_set_clock @store_set_clock
  @stack_set_clock @stack_limit_set_clock @stack_max_set_clock @state_stack_size_set_clock
  @memory_set_clock @mdomain_set_clock @sh_mdomain_set_clock @permute_set_clock
  @compile_set_clock @compile_oracle_set_clock @code_buffer_set_clock @data_buffer_set_clock
  @gc_fun_set_clock @handler_set_clock @termdep_set_clock @code_set_clock @be_set_clock
  @ffi_set_clock @clock_set_clock @set_clock_set_clock
  @set_locals_set_clock @set_locals_size_set_clock @set_fp_regs_set_clock
  @set_store_field_set_clock @set_stack_set_clock @set_stack_limit_set_clock
  @set_stack_max_set_clock @set_stack_size_set_clock @set_memory_set_clock
  @set_mdomain_set_clock @set_sh_mdomain_set_clock @set_permute_set_clock
  @set_compile_set_clock @set_compile_oracle_set_clock @set_code_buffer_set_clock
  @set_data_buffer_set_clock @set_gc_fun_set_clock @set_handler_set_clock
  @set_termdep_set_clock @set_code_set_clock @set_be_set_clock @set_ffi_set_clock
  @set_var_set_clock @unset_var_set_clock @set_vars_set_clock @set_store_set_clock
  @set_fp_var_set_clock @flush_state_set_clock @call_env_set_clock @dec_clock_eq
  @push_env_set_clock @clock_push_env
  @get_var_set_clock @get_vars_set_clock @get_store_set_clock @get_fp_var_set_clock
  @mem_load_set_clock @get_var_imm_set_clock @has_space_set_clock @word_exp_set_clock
  @mem_store_set_clock @cut_state_set_clock @pop_env_set_clock @gc_set_clock
  @jump_exc_set_clock @inst_set_clock @alloc_set_clock @share_inst_set_clock : wdc.

Lemma clock_set_termdep {a c ffi_t} v (s : state a c ffi_t) : clock (set_termdep v s) = clock s.
Proof. reflexivity. Qed.
Lemma clock_set_stack_max {a c ffi_t} v (s : state a c ffi_t) : clock (set_stack_max v s) = clock s.
Proof. reflexivity. Qed.
Lemma clock_set_stack {a c ffi_t} v (s : state a c ffi_t) : clock (set_stack v s) = clock s.
Proof. reflexivity. Qed.
Lemma clock_call_env {a c ffi_t} x ss (s : state a c ffi_t) : clock (call_env x ss s) = clock s.
Proof. reflexivity. Qed.
Lemma clock_set_vars {a c ffi_t} x y (s : state a c ffi_t) : clock (set_vars x y s) = clock s.
Proof. reflexivity. Qed.
Lemma clock_set_var {a c ffi_t} x y (s : state a c ffi_t) : clock (set_var x y s) = clock s.
Proof. reflexivity. Qed.
Lemma clock_set_locals {a c ffi_t} x (s : state a c ffi_t) : clock (set_locals x s) = clock s.
Proof. reflexivity. Qed.
Lemma clock_flush_state {a c ffi_t} b (s : state a c ffi_t) : clock (flush_state b s) = clock s.
Proof. destruct b; reflexivity. Qed.
Global Hint Rewrite @clock_set_termdep @clock_set_stack_max @clock_set_stack @clock_call_env
  @clock_set_vars @clock_set_var @clock_set_locals @clock_flush_state : wdc.

Lemma termdep_set_stack_max {a c ffi_t} v (s : state a c ffi_t) : termdep (set_stack_max v s) = termdep s.
Proof. reflexivity. Qed.
Lemma termdep_set_stack {a c ffi_t} v (s : state a c ffi_t) : termdep (set_stack v s) = termdep s.
Proof. reflexivity. Qed.
Lemma termdep_call_env {a c ffi_t} x ss (s : state a c ffi_t) : termdep (call_env x ss s) = termdep s.
Proof. reflexivity. Qed.
Lemma termdep_set_vars {a c ffi_t} x y (s : state a c ffi_t) : termdep (set_vars x y s) = termdep s.
Proof. reflexivity. Qed.
Lemma termdep_set_var {a c ffi_t} x y (s : state a c ffi_t) : termdep (set_var x y s) = termdep s.
Proof. reflexivity. Qed.
Lemma termdep_set_locals {a c ffi_t} x (s : state a c ffi_t) : termdep (set_locals x s) = termdep s.
Proof. reflexivity. Qed.
Lemma termdep_flush_state {a c ffi_t} b (s : state a c ffi_t) : termdep (flush_state b s) = termdep s.
Proof. destruct b; reflexivity. Qed.
Lemma termdep_set_termdep {a c ffi_t} v (s : state a c ffi_t) : termdep (set_termdep v s) = v.
Proof. reflexivity. Qed.
Global Hint Rewrite @termdep_set_stack_max @termdep_set_stack @termdep_call_env @termdep_set_vars
  @termdep_set_var @termdep_set_locals @termdep_flush_state @termdep_set_termdep
  @push_env_termdep : wdc.

(** Clock facts of the primitives in the context. *)
Ltac wd_clk :=
  repeat match goal with
         | H : (_ =? 0)%N = false |- _ => apply N.eqb_neq in H
         | H : cut_state _ _ = SOME _ |- _ => apply cut_state_clock in H; destruct H
         | H : pop_env _ = SOME _ |- _ =>
             let H' := fresh "Hp" in
             pose proof (pop_env_termdep _ _ H) as H'; apply pop_env_clock in H
         | H : jump_exc _ = SOME _ |- _ => apply jump_exc_clock in H; destruct H
         | H : mem_store _ _ _ = SOME _ |- _ => apply mem_store_clock in H; destruct H
         | H : inst _ _ = SOME _ |- _ => apply inst_const in H; destruct H
         | H : alloc _ _ _ = (_, _) |- _ => apply alloc_const in H; destruct H
         | H : share_inst _ _ _ _ = (_, _) |- _ =>
             apply share_inst_const in H;
             destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _)
         end;
  autorewrite with wdc in *.

Ltac wd_eq :=
  wd_clk;
  first [ reflexivity
        | apply pair_equal_spec; split; [reflexivity|]; f_equal; lia
        | f_equal; lia ].

Ltac ac_simpl H :=
  autorewrite with wdc in H |- *;
  cbn [PAIR_MAP option_map cont_loop exit_loop bad_fun_return fst snd] in H |- *.

Ltac wd_eval_lt := unfold eval_lt; cbn [fst snd psize STOP]; wd_clk; lia.

Lemma bool_decide_refl_false {A} `{EqDecision A} (x : A) : bool_decide (x = x) = false -> False.
Proof. intros E. rewrite (proj2 (bool_decide_spec (x = x)) eq_refl) in E. discriminate E. Qed.

(** Close goals with a contradictory [bool_decide] equation. *)
Ltac bd_contra :=
  match goal with
  | E : bool_decide (?x = ?x) = false |- _ => exfalso; exact (bool_decide_refl_false x E)
  | E : bool_decide _ = true |- _ => apply bool_decide_spec in E; discriminate E
  end.

(** Rewrite the goal with the case equations of the context. *)
Ltac rw_cases :=
  repeat match goal with
         | E : ?X = ?v |- context [?X] =>
             lazymatch v with
             | true => idtac | false => idtac | SOME _ => idtac | NONE => idtac
             end;
             rewrite E; cbn beta iota zeta
         end.

Ltac ac_loop IH extra H :=
  repeat first
    [ bd_contra
    | progress (rewrite ?fix_clock_evaluate in H)
    | progress (rewrite ?fix_clock_evaluate)
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
            pose proof (IH (p', s'') ltac:(wd_eval_lt) r' t E Hn) as Hi; clear E;
            cbn [fst snd] in Hi;
            match goal with
            | |- context [evaluate (p', ?X)] =>
                replace X with (set_clock (clock s'' + extra) s'') by wd_eq; rewrite Hi; clear Hi
            end ]
      end
    | match type of H with
      | context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; ac_simpl H
      end ].

Section AddClock.
Context {a : N} {c ffi_t : Type}.

(** HOL's free variable [extra] is quantified first. *)
(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_add_clock" *)
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
         | E : alloc _ _ _ = _ |- context [alloc _ _ _] => rewrite E
         | E : share_inst _ _ _ _ = _ |- context [share_inst _ _ _ _] => rewrite E
         end;
  cbn [PAIR_MAP fst snd]; rw_cases;
  wd_eq.
Qed.

End AddClock.

(** ** IO events (Galette-only helpers) *)

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

Section IoFacts.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

Lemma jump_exc_ffi s s1 l : jump_exc s = SOME (s1, l) -> ffi s1 = ffi s.
Proof.
  unfold jump_exc. destruct (_ <? _); [|discriminate].
  destruct (LASTN _ _) as [|[m e0 e [[n [l1 l2]]|]] xs]; intros H; inversion H; reflexivity.
Qed.

Lemma cut_state_ffi names s s1 : cut_state names s = SOME s1 -> ffi s1 = ffi s.
Proof. unfold cut_state; destruct (cut_env _ _); intros H; inversion H; reflexivity. Qed.

Lemma pop_env_ffi s s1 : pop_env s = SOME s1 -> ffi s1 = ffi s.
Proof. intros H; exact (proj1 (proj2 (pop_env_const _ _ H))). Qed.

Lemma mem_store_ffi x y s s1 : mem_store x y s = SOME s1 -> ffi s1 = ffi s.
Proof. unfold mem_store; destruct (classical_dec _); intros H; inversion H; reflexivity. Qed.

Lemma share_inst_io op v ad s res t :
  share_inst op v ad s = (res, t) -> isPREFIX (io_events (ffi s)) (io_events (ffi t)).
Proof.
  intros H; destruct op; cbn [share_inst] in H;
    unfold sh_mem_set_var, sh_mem_load, sh_mem_load_byte, sh_mem_load16, sh_mem_load32,
      sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32 in H;
    split_H H; leaf H;
    repeat match goal with
           | E : context [match ?x with _ => _ end] |- _ =>
               destruct x; cbn beta iota in E; try discriminate E
           end;
    repeat match goal with E : SOME _ = SOME _ |- _ => injection E as E end;
    cbn [ffi set_ffi set_var set_locals flush_state set_locals_size set_store_field set_stack];
    first [ apply isPREFIX_REFL | eapply call_FFI_io; eassumption
          | destruct (_ : bool); apply isPREFIX_REFL ].
Qed.

End IoFacts.

Ltac io_facts :=
  repeat match goal with
         | E : alloc _ _ _ = (_, _) |- _ =>
             let H' := fresh "Hf" in
             pose proof (proj1 (proj2 (alloc_const _ _ _ _ _ E))) as H'; clear E
         | E : inst _ _ = SOME _ |- _ =>
             let H' := fresh "Hf" in pose proof (proj2 (inst_const _ _ _ E)) as H'; clear E
         | E : jump_exc _ = SOME (_, _) |- _ => apply jump_exc_ffi in E
         | E : cut_state _ _ = SOME _ |- _ => apply cut_state_ffi in E
         | E : pop_env _ = SOME _ |- _ => apply pop_env_ffi in E
         | E : mem_store _ _ _ = SOME _ |- _ => apply mem_store_ffi in E
         | E : share_inst _ _ _ _ = (_, _) |- _ => apply share_inst_io in E
         | E : call_FFI _ _ _ _ = FFI_return _ _ |- _ => apply call_FFI_io in E
         end.

Ltac ffi_cbn :=
  cbn [ffi set_locals set_locals_size set_fp_regs set_store_field set_stack
       set_stack_limit set_stack_max set_stack_size set_memory set_mdomain set_sh_mdomain
       set_permute set_compile set_compile_oracle set_code_buffer set_data_buffer set_gc_fun
       set_handler set_clock set_termdep set_code set_be set_ffi
       dec_clock call_env set_var set_vars unset_var set_store set_fp_var flush_state
       fst snd] in *;
  rewrite ?ffi_push_env in *.

Ltac io_step IH H :=
  repeat first
    [ progress rewrite ?fix_clock_evaluate in H
    | match goal with
      | E : evaluate (?p', ?s'') = (?r', ?t) |- _ =>
          let Hc := fresh "Hc" in let Hi := fresh "Hi" in
          pose proof (evaluate_clock p' s'' r' t E) as Hc;
          pose proof (IH (p', s'') ltac:(wd_eval_lt) r' t E) as Hi; clear E
      end
    | match type of H with
      | context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H
      end ].

Section IoMono.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_io_events_mono" *)
Theorem evaluate_io_events_mono : forall (exps : prog a) (s1 : state a c ffi_t) res s2,
  evaluate (exps, s1) = (res, s2) ->
  isPREFIX (io_events (ffi s1)) (io_events (ffi s2)).
Proof.
  enough (G : forall x : prog a * state a c ffi_t, forall r s1, evaluate x = (r, s1) ->
    isPREFIX (io_events (ffi (snd x))) (io_events (ffi s1)))
    by (intros p s r s1 H; exact (G (p, s) r s1 H)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s1 H; cbn [snd].
  rewrite evaluate_eqn in H; destruct p; cbn [evaluate_body] in H; io_step IH H;
  repeat match goal with E : (_, _) = (_, _) |- _ => injection E as <- <- end;
  io_facts; ffi_cbn;
  repeat match goal with
         | E : ffi ?t = _ |- _ => rewrite E in *; clear E
         end;
  eauto using isPREFIX_REFL, isPREFIX_trans2.
Qed.

End IoMono.

Ltac io_loop IH extra H :=
  repeat first
    [ bd_contra
    | progress (rewrite ?fix_clock_evaluate in H)
    | progress (rewrite ?fix_clock_evaluate)
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
                pose proof (IH (p', s'') ltac:(wd_eval_lt) _ _ E) as Hp; clear E;
                cbn [fst snd] in Hp;
                match goal with
                | |- context [evaluate (p', ?X)] =>
                    replace X with (set_clock (clock s'' + extra) s'') by wd_eq;
                    let r2 := fresh "r" in let t2 := fresh "t" in let E2 := fresh "E" in
                    destruct (evaluate (p', set_clock (clock s'' + extra) s'')) as [r2 t2] eqn:E2;
                    pose proof (evaluate_io_events_mono _ _ _ _ E2); clear E2; cbn [snd] in Hp
                end;
                try ac_simpl H ]
          | let Hi := fresh "Hi" in
            pose proof (evaluate_add_clock extra p' s'' r' t (conj E Hn)) as Hi; clear E;
            match goal with
            | |- context [evaluate (p', ?X)] =>
                replace X with (set_clock (clock s'' + extra) s'') by wd_eq; rewrite Hi; clear Hi
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
      | |- context [share_inst ?o ?r ?w ?st] =>
          let E := fresh "E" in destruct (share_inst o r w st) eqn:E; cbn [PAIR_MAP snd fst]
      | |- context [alloc ?w ?n ?st] =>
          let E := fresh "E" in destruct (alloc w n st) eqn:E; cbn [PAIR_MAP snd fst]
      end ].

Section IoMono2.
Context {a : N} {c ffi_t : Type}.

(** HOL's [SND (evaluate ...)] is [snd (evaluate ...)]. *)
(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_add_clock_io_events_mono" *)
Theorem evaluate_add_clock_io_events_mono : forall (exps : prog a) (s : state a c ffi_t) extra,
  isPREFIX (io_events (ffi (snd (evaluate (exps, s)))))
           (io_events (ffi (snd (evaluate (exps, set_clock (clock s + extra) s))))).
Proof.
  intros e s extra; revert e s.
  enough (G : forall x : prog a * state a c ffi_t, forall r s1, evaluate x = (r, s1) ->
    isPREFIX (io_events (ffi s1))
      (io_events (ffi (snd (evaluate (fst x, set_clock (clock (snd x) + extra) (snd x)))))))
    by (intros e s; destruct (evaluate (e, s)) as [r s1] eqn:E; exact (G (e, s) r s1 E)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s1 H; cbn [fst snd].
  destruct (classical_dec (r = SOME TimeOut)) as [->|Hr].
  2:{ rewrite (evaluate_add_clock extra p s r s1 (conj H Hr)); apply isPREFIX_REFL. }
  rewrite evaluate_eqn in H |- *.
  destruct p; cbn [evaluate_body] in H |- *; ac_simpl H; io_loop IH extra H;
  try discriminate H; try (injection H; intros; subst); try rewrite H;
  repeat match goal with
         | E : alloc _ _ _ = _ |- context [alloc _ _ _] => rewrite E
         | E : share_inst _ _ _ _ = _ |- context [share_inst _ _ _ _] => rewrite E
         end;
  cbn [PAIR_MAP snd fst]; rw_cases;
  io_goal_split; io_facts;
  ffi_cbn;
  repeat match goal with
         | E : ffi ?t = _ |- _ => rewrite E in *; clear E
         end;
  eauto using isPREFIX_REFL, isPREFIX_trans2.
Qed.

End IoMono2.
