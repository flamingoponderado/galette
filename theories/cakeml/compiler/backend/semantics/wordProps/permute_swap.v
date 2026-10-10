(** * CakeML [wordProps]: the permutation oracle

    Port of the "Permute Swap Lemma" part of
    [cakeml/compiler/backend/semantics/wordPropsScript.sml]:
    [permute_swap_lemma] (for any target final permutation oracle there is
    an initial one producing it, with the same result).

    HOL's [let (res,rst) = evaluate (prog,st) in ...] is a [let '(res, rst)]
    pattern; HOL [s with permute := p] is [set_permute p s].  The proof is by
    well-founded induction on [eval_lt] with [evaluate_eqn] (HOL:
    [recInduct evaluate_ind]); HOL's witness
    [λx. if x = 0 then st.permute 0 else perm (x-1)] is the Galette-only
    [perm_cons (permute st 0) perm].  The section "Commuting with
    [set_permute]" is Galette-only infrastructure.

    Also [permute_swap_lemma2] and [permute_swap_lemma3] (no_alloc and
    no_install programs run the same on stacks whose frames are
    permuted).  They are stated with the Galette-only [PERM_STACK] of
    [wordProps.code], which uses Rocq's [Permutation] for HOL's [PERM],
    and so are not tagged (as [stack_size_perm]).  HOL
    [st with <|permute := perm; stack := stack|>] is
    [set_stack stack (set_permute perm st)]. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
From Galette.cakeml.misc Require Import misc.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common wordLang.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem wordConvs.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import consts clock consts_with code stack_swap.
From Stdlib Require Import Permutation.
Open Scope N_scope.

(** ** Commuting with [set_permute] (Galette-only) *)

Section SetPermute.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

Lemma locals_set_permute p s : locals (set_permute p s) = locals s. Proof. reflexivity. Qed.
Lemma locals_size_set_permute p s : locals_size (set_permute p s) = locals_size s. Proof. reflexivity. Qed.
Lemma fp_regs_set_permute p s : fp_regs (set_permute p s) = fp_regs s. Proof. reflexivity. Qed.
Lemma store_set_permute p s : store (set_permute p s) = store s. Proof. reflexivity. Qed.
Lemma stack_set_permute p s : stack (set_permute p s) = stack s. Proof. reflexivity. Qed.
Lemma stack_limit_set_permute p s : stack_limit (set_permute p s) = stack_limit s. Proof. reflexivity. Qed.
Lemma stack_max_set_permute p s : stack_max (set_permute p s) = stack_max s. Proof. reflexivity. Qed.
Lemma state_stack_size_set_permute p s : state_stack_size (set_permute p s) = state_stack_size s. Proof. reflexivity. Qed.
Lemma memory_set_permute p s : memory (set_permute p s) = memory s. Proof. reflexivity. Qed.
Lemma mdomain_set_permute p s : mdomain (set_permute p s) = mdomain s. Proof. reflexivity. Qed.
Lemma sh_mdomain_set_permute p s : sh_mdomain (set_permute p s) = sh_mdomain s. Proof. reflexivity. Qed.
Lemma permute_set_permute p s : permute (set_permute p s) = p. Proof. reflexivity. Qed.
Lemma compile_set_permute p s : compile (set_permute p s) = compile s. Proof. reflexivity. Qed.
Lemma compile_oracle_set_permute p s : compile_oracle (set_permute p s) = compile_oracle s. Proof. reflexivity. Qed.
Lemma code_buffer_set_permute p s : code_buffer (set_permute p s) = code_buffer s. Proof. reflexivity. Qed.
Lemma data_buffer_set_permute p s : data_buffer (set_permute p s) = data_buffer s. Proof. reflexivity. Qed.
Lemma gc_fun_set_permute p s : gc_fun (set_permute p s) = gc_fun s. Proof. reflexivity. Qed.
Lemma handler_set_permute p s : handler (set_permute p s) = handler s. Proof. reflexivity. Qed.
Lemma clock_set_permute p s : clock (set_permute p s) = clock s. Proof. reflexivity. Qed.
Lemma termdep_set_permute p s : termdep (set_permute p s) = termdep s. Proof. reflexivity. Qed.
Lemma code_set_permute p s : code (set_permute p s) = code s. Proof. reflexivity. Qed.
Lemma be_set_permute p s : be (set_permute p s) = be s. Proof. reflexivity. Qed.
Lemma ffi_set_permute p s : ffi (set_permute p s) = ffi s. Proof. reflexivity. Qed.
Lemma set_permute_set_permute p q s : set_permute p (set_permute q s) = set_permute p s. Proof. reflexivity. Qed.

Lemma set_locals_set_permute v p s : set_locals v (set_permute p s) = set_permute p (set_locals v s). Proof. reflexivity. Qed.
Lemma set_locals_size_set_permute v p s : set_locals_size v (set_permute p s) = set_permute p (set_locals_size v s). Proof. reflexivity. Qed.
Lemma set_fp_regs_set_permute v p s : set_fp_regs v (set_permute p s) = set_permute p (set_fp_regs v s). Proof. reflexivity. Qed.
Lemma set_store_field_set_permute v p s : set_store_field v (set_permute p s) = set_permute p (set_store_field v s). Proof. reflexivity. Qed.
Lemma set_stack_set_permute v p s : set_stack v (set_permute p s) = set_permute p (set_stack v s). Proof. reflexivity. Qed.
Lemma set_stack_max_set_permute v p s : set_stack_max v (set_permute p s) = set_permute p (set_stack_max v s). Proof. reflexivity. Qed.
Lemma set_stack_size_set_permute v p s : set_stack_size v (set_permute p s) = set_permute p (set_stack_size v s). Proof. reflexivity. Qed.
Lemma set_memory_set_permute v p s : set_memory v (set_permute p s) = set_permute p (set_memory v s). Proof. reflexivity. Qed.
Lemma set_compile_oracle_set_permute v p s : set_compile_oracle v (set_permute p s) = set_permute p (set_compile_oracle v s). Proof. reflexivity. Qed.
Lemma set_code_buffer_set_permute v p s : set_code_buffer v (set_permute p s) = set_permute p (set_code_buffer v s). Proof. reflexivity. Qed.
Lemma set_data_buffer_set_permute v p s : set_data_buffer v (set_permute p s) = set_permute p (set_data_buffer v s). Proof. reflexivity. Qed.
Lemma set_handler_set_permute v p s : set_handler v (set_permute p s) = set_permute p (set_handler v s). Proof. reflexivity. Qed.
Lemma set_clock_set_permute v p s : set_clock v (set_permute p s) = set_permute p (set_clock v s). Proof. reflexivity. Qed.
Lemma set_termdep_set_permute v p s : set_termdep v (set_permute p s) = set_permute p (set_termdep v s). Proof. reflexivity. Qed.
Lemma set_code_set_permute v p s : set_code v (set_permute p s) = set_permute p (set_code v s). Proof. reflexivity. Qed.
Lemma set_ffi_set_permute v p s : set_ffi v (set_permute p s) = set_permute p (set_ffi v s). Proof. reflexivity. Qed.
Lemma set_var_set_permute v x p s : set_var v x (set_permute p s) = set_permute p (set_var v x s). Proof. reflexivity. Qed.
Lemma unset_var_set_permute v p s : unset_var v (set_permute p s) = set_permute p (unset_var v s). Proof. reflexivity. Qed.
Lemma set_vars_set_permute vs xs p s : set_vars vs xs (set_permute p s) = set_permute p (set_vars vs xs s). Proof. reflexivity. Qed.
Lemma set_store_set_permute v x p s : set_store v x (set_permute p s) = set_permute p (set_store v x s). Proof. reflexivity. Qed.
Lemma set_fp_var_set_permute v x p s : set_fp_var v x (set_permute p s) = set_permute p (set_fp_var v x s). Proof. reflexivity. Qed.
Lemma flush_state_set_permute b p s : flush_state b (set_permute p s) = set_permute p (flush_state b s). Proof. destruct b; reflexivity. Qed.
Lemma call_env_set_permute x ss p s : call_env x ss (set_permute p s) = set_permute p (call_env x ss s). Proof. reflexivity. Qed.
Lemma dec_clock_set_permute p s : dec_clock (set_permute p s) = set_permute p (dec_clock s). Proof. reflexivity. Qed.
Lemma get_var_set_permute v p s : get_var v (set_permute p s) = get_var v s. Proof. reflexivity. Qed.
Lemma get_vars_set_permute vs p s : get_vars vs (set_permute p s) = get_vars vs s.
Proof. induction vs as [|v vs IH]; cbn; [reflexivity|]. rewrite IH; reflexivity. Qed.
Lemma get_store_set_permute v p s : get_store v (set_permute p s) = get_store v s. Proof. reflexivity. Qed.
Lemma get_fp_var_set_permute v p s : get_fp_var v (set_permute p s) = get_fp_var v s. Proof. reflexivity. Qed.
Lemma mem_load_set_permute v p s : mem_load v (set_permute p s) = mem_load v s. Proof. reflexivity. Qed.
Lemma get_var_imm_set_permute ri p s : get_var_imm ri (set_permute p s) = get_var_imm ri s.
Proof. destruct ri; reflexivity. Qed.
Lemma has_space_set_permute x p s : has_space x (set_permute p s) = has_space x s. Proof. reflexivity. Qed.
Lemma word_exp_set_permute e p s : word_exp (set_permute p s) e = word_exp s e.
Proof. apply word_exp_state_cong; reflexivity. Qed.
Lemma mem_store_set_permute x y p s :
  mem_store x y (set_permute p s) = OPTION_MAP (set_permute p) (mem_store x y s).
Proof. unfold mem_store; cbn [mdomain set_permute]. destruct (classical_dec _); reflexivity. Qed.
Lemma cut_state_set_permute names p s :
  cut_state names (set_permute p s) = OPTION_MAP (set_permute p) (cut_state names s).
Proof. unfold cut_state; cbn [locals set_permute]. destruct (cut_env _ _); reflexivity. Qed.
Lemma pop_env_set_permute p s : pop_env (set_permute p s) = OPTION_MAP (set_permute p) (pop_env s).
Proof. unfold pop_env; cbn [stack set_permute]; destruct (stack s) as [|[? ? ? [[? ?]|]] ?]; reflexivity. Qed.
Lemma gc_set_permute p s : gc (set_permute p s) = OPTION_MAP (set_permute p) (gc s).
Proof.
  unfold gc; cbn [stack memory mdomain store gc_fun set_permute].
  destruct (gc_fun s _) as [[? [? ?]]|]; [destruct (dec_stack _ _)|]; reflexivity.
Qed.
Lemma jump_exc_set_permute p s :
  jump_exc (set_permute p s) = OPTION_MAP (fun '(s, t) => (set_permute p s, t)) (jump_exc s).
Proof. exact (proj2 (jump_exc_with_const s 0 p)). Qed.
Lemma inst_set_permute i p s : inst i (set_permute p s) = OPTION_MAP (set_permute p) (inst i s).
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (inst_with_const i s 0 (code s) (compile s) (compile_oracle s) p (stack s))))))). Qed.
Lemma share_inst_set_permute op v ad p s :
  share_inst op v ad (set_permute p s) = PAIR_MAP I (set_permute p) (share_inst op v ad s).
Proof. exact (proj1 (share_inst_with_const op v ad s p 0)). Qed.

End SetPermute.

Create Rewrite HintDb wdp.
Global Hint Rewrite @locals_set_permute @locals_size_set_permute @fp_regs_set_permute @store_set_permute
  @stack_set_permute @stack_limit_set_permute @stack_max_set_permute @state_stack_size_set_permute
  @memory_set_permute @mdomain_set_permute @sh_mdomain_set_permute @permute_set_permute
  @compile_set_permute @compile_oracle_set_permute @code_buffer_set_permute @data_buffer_set_permute
  @gc_fun_set_permute @handler_set_permute @clock_set_permute @termdep_set_permute @code_set_permute
  @be_set_permute @ffi_set_permute @set_permute_set_permute
  @set_locals_set_permute @set_locals_size_set_permute @set_fp_regs_set_permute
  @set_store_field_set_permute @set_stack_set_permute @set_stack_max_set_permute
  @set_stack_size_set_permute @set_memory_set_permute @set_compile_oracle_set_permute
  @set_code_buffer_set_permute @set_data_buffer_set_permute @set_handler_set_permute
  @set_clock_set_permute @set_termdep_set_permute @set_code_set_permute @set_ffi_set_permute
  @set_var_set_permute @unset_var_set_permute @set_vars_set_permute @set_store_set_permute
  @set_fp_var_set_permute @flush_state_set_permute @call_env_set_permute @dec_clock_set_permute
  @get_var_set_permute @get_vars_set_permute @get_store_set_permute @get_fp_var_set_permute
  @mem_load_set_permute @get_var_imm_set_permute @has_space_set_permute @word_exp_set_permute
  @mem_store_set_permute @cut_state_set_permute @pop_env_set_permute @gc_set_permute
  @jump_exc_set_permute @inst_set_permute @share_inst_set_permute : wdp.

Section PermSwap.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(** Galette-only: HOL's [λx. if x = 0 then h else p (x - 1)]. *)
Definition perm_cons (h : N -> N) (p : N -> N -> N) : N -> N -> N :=
  fun x => if x =? 0 then h else p (x - 1).

Lemma push_env_perm_cons envs (h : option (N * (prog a * (N * N)))) (s : state) perm :
  push_env envs h (set_permute (perm_cons (permute s 0) perm) s) = set_permute perm (push_env envs h s).
Proof.
  assert (Hp : (fun n => perm_cons (permute s 0) perm (n + 1)) = perm).
  { apply functional_extensionality; intros n; unfold perm_cons.
    replace (n + 1 =? 0) with false by (symmetry; apply N.eqb_neq; lia). f_equal; lia. }
  destruct h as [[? [? [? ?]]]|]; unfold push_env, env_to_list;
    unfold set_permute, set_stack_max, set_stack, set_handler; cbn;
    f_equal; exact Hp.
Qed.

Lemma alloc_perm_cons w names (s : state) r t perm :
  alloc w names s = (r, t) -> r <> SOME Error ->
  alloc w names (set_permute (perm_cons (permute s 0) perm) s) = (r, set_permute perm t).
Proof.
  intros H Hr; unfold alloc in *; autorewrite with wdp.
  destruct (cut_envs names (locals s)) as [envs|]; [|injection H as <- _; exfalso; apply Hr; reflexivity].
  change (permute s 0) with (permute (set_store stackLang.AllocSize (Word w) s) 0).
  rewrite push_env_perm_cons; autorewrite with wdp.
  destruct (gc _) as [s1|]; cbn [OPTION_MAP option_map] in *; [|injection H as <- _; exfalso; apply Hr; reflexivity].
  autorewrite with wdp.
  destruct (pop_env s1) as [s2|]; cbn [OPTION_MAP option_map] in *; [|injection H as <- _; exfalso; apply Hr; reflexivity].
  autorewrite with wdp.
  destruct (get_store _ s2); [|injection H as <- _; exfalso; apply Hr; reflexivity].
  autorewrite with wdp.
  destruct (has_space _ s2) as [[]|]; injection H as <- <-; autorewrite with wdp;
    try reflexivity; exfalso; apply Hr; reflexivity.
Qed.

Lemma push_env_perm_cons' envs (h : option (N * (prog a * (N * N)))) (s : state) perm h0 :
  h0 = permute s 0 ->
  push_env envs h (set_permute (perm_cons h0 perm) s) = set_permute perm (push_env envs h s).
Proof. intros ->; apply push_env_perm_cons. Qed.

Lemma call_env_push_env_stack_max x ss envs (h : option (N * (prog a * (N * N)))) p (s : state) :
  stack_max (call_env x ss (push_env envs h (set_permute p s))) =
  stack_max (call_env x ss (push_env envs h s)).
Proof. destruct h as [[? [? [? ?]]]|]; unfold call_env, push_env, env_to_list; reflexivity. Qed.

Lemma stack_max_push_env_set_permute envs (h : option (N * (prog a * (N * N)))) p (s : state) :
  stack_max (push_env envs h (set_permute p s)) = stack_max (push_env envs h s).
Proof.
  destruct h as [[? [? [? ?]]]|]; unfold push_env, env_to_list; reflexivity.
Qed.

Local Ltac ps_simpl H := autorewrite with wdp in H |- *; cbn [PAIR_MAP option_map fst snd I] in H |- *.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "permute_swap_lemma" *)
Theorem permute_swap_lemma : forall (prog : prog a) (st : state) perm,
  let '(res, rst) := evaluate (prog, st) in
  res <> SOME Error ->
  exists perm', evaluate (prog, set_permute perm' st) = (res, set_permute perm rst).
Proof.
  enough (G : forall x : prog a * state, forall r t, evaluate x = (r, t) -> r <> SOME Error ->
    forall perm, exists perm', evaluate (fst x, set_permute perm' (snd x)) = (r, set_permute perm t)).
  { intros prog st perm; destruct (evaluate (prog, st)) as [r t] eqn:E; intros Hr.
    exact (G (prog, st) r t E Hr perm). }
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r t H Hr perm; cbn [fst snd].
  rewrite evaluate_eqn in H; destruct p; cbn [evaluate_body] in H.
  all: try (exists perm; rewrite evaluate_eqn; cbn [evaluate_body]; ps_simpl H;
            split_H H; leaf H; try (exfalso; apply Hr; reflexivity);
            repeat progress (rw_cases; autorewrite with wdp;
              repeat match goal with
                     | E : share_inst _ _ _ _ = _ |- context [share_inst _ _ _ _] => rewrite E
                     end; cbn [PAIR_MAP I fst snd option_map]); reflexivity).
  - (* MustTerminate *)
    destruct (termdep s =? 0) eqn:Et; [injection H as <- _; exfalso; apply Hr; reflexivity|].
    destruct (evaluate (p, set_termdep (termdep s - 1) (set_clock (MustTerminate_limit a) s)))
      as [r1 s1] eqn:E1.
    pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
    destruct (bool_decide (r1 = SOME TimeOut)) eqn:Eb; [injection H as <- _; exfalso; apply Hr; reflexivity|].
    injection H as <- <-.
    destruct (IH (p, set_termdep (termdep s - 1) (set_clock (MustTerminate_limit a) s))
                 ltac:(wd_eval_lt) r1 s1 E1 Hr perm) as [q Hq]; cbn [fst snd] in Hq.
    exists q; rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with wdp; rewrite Et;
      cbn beta iota zeta; rewrite Hq; cbn beta iota zeta; rewrite Eb; autorewrite with wdp; reflexivity.
  - (* Call *)
    rename o into ret, o0 into dest, l into args, o1 into handler0.
    destruct (get_vars args s) as [xs|] eqn:Eg; [|injection H as <- _; exfalso; apply Hr; reflexivity].
    cbn beta iota zeta in H.
    destruct (bad_dest_args dest args) eqn:Ebd; [injection H as <- _; exfalso; apply Hr; reflexivity|].
    destruct (find_code dest (add_ret_loc ret xs) (code s) (state_stack_size s)) as [[args1 [prg ss]]|] eqn:Ef;
      [|injection H as <- _; exfalso; apply Hr; reflexivity].
    cbn beta iota zeta in H.
    Local Ltac call_pre Eg Ebd Ef :=
      rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with wdp; rewrite Eg; cbn beta iota zeta;
      rewrite Ebd; rewrite Ef; cbn beta iota zeta.
    destruct ret as [[n [names [ret_handler [l1 l2]]]]|].
    + destruct (⌜domain (FST names) = {}⌝ || negb (ALL_DISTINCT n)) eqn:Ed;
        [injection H as <- _; exfalso; apply Hr; reflexivity|].
      destruct (cut_envs names (locals s)) as [envs|] eqn:Ec; [|injection H as <- _; exfalso; apply Hr; reflexivity].
      destruct (clock s =? 0) eqn:Ez.
      * injection H as <- <-. exists perm. call_pre Eg Ebd Ef. rewrite Ed, Ec, Ez; cbn beta iota zeta.
        rewrite call_env_push_env_stack_max; autorewrite with wdp; reflexivity.
      * rewrite fix_clock_evaluate in H.
        destruct (evaluate (prg, call_env args1 ss (push_env envs handler0 (dec_clock s)))) as [r1 s2] eqn:E1.
        pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
        Local Ltac call_post Ed Ec Ez :=
          rewrite Ed, Ec, Ez; cbn beta iota zeta; rewrite fix_clock_evaluate;
          erewrite push_env_perm_cons' by reflexivity; autorewrite with wdp.
        destruct r1 as [r1|]; [destruct r1 as [x ys|x y|k|k| | |f|]|];
          try (injection H as <- _; exfalso; apply Hr; reflexivity).
        -- destruct (negb ⌜x = Loc l1 l2⌝ || negb (LENGTH ys =? LENGTH n)) eqn:Ex;
             [injection H as <- _; exfalso; apply Hr; reflexivity|].
           destruct (pop_env s2) as [s3|] eqn:Ep; [|injection H as <- _; exfalso; apply Hr; reflexivity].
           destruct (⌜domain (locals s3) = domain (FST envs) UNION domain (SND envs)⌝) eqn:Edom;
             [|injection H as <- _; exfalso; apply Hr; reflexivity].
           destruct (IH (ret_handler, set_vars n ys s3) ltac:(wd_eval_lt) r t H Hr perm) as [q1 Hq1].
           destruct (IH (prg, call_env args1 ss (push_env envs handler0 (dec_clock s))) ltac:(wd_eval_lt)
                        _ s2 E1 ltac:(discriminate) q1) as [q2 Hq2].
           cbn [fst snd] in Hq1, Hq2.
           exists (perm_cons (permute s 0) q2). call_pre Eg Ebd Ef. call_post Ed Ec Ez.
           rewrite Hq2; cbn beta iota zeta; rewrite Ex; autorewrite with wdp; rewrite Ep;
             cbn [OPTION_MAP option_map]; autorewrite with wdp; rewrite Edom; exact Hq1.
        -- destruct handler0 as [[hn [hp [hl1 hl2]]]|].
           ++ destruct (negb ⌜x = Loc hl1 hl2⌝) eqn:Ex; [injection H as <- _; exfalso; apply Hr; reflexivity|].
              destruct (⌜domain (locals s2) = domain (FST envs) UNION domain (SND envs)⌝) eqn:Edom;
                [|injection H as <- _; exfalso; apply Hr; reflexivity].
              destruct (IH (hp, set_var hn y s2) ltac:(wd_eval_lt) r t H Hr perm) as [q1 Hq1].
              destruct (IH (prg, call_env args1 ss (push_env envs (SOME (hn, (hp, (hl1, hl2)))) (dec_clock s)))
                           ltac:(wd_eval_lt) _ s2 E1 ltac:(discriminate) q1) as [q2 Hq2].
              cbn [fst snd] in Hq1, Hq2.
              exists (perm_cons (permute s 0) q2). call_pre Eg Ebd Ef. call_post Ed Ec Ez.
              rewrite Hq2; cbn beta iota zeta; rewrite Ex; autorewrite with wdp; rewrite Edom; exact Hq1.
           ++ injection H as <- <-.
              destruct (IH (prg, call_env args1 ss (push_env envs NONE (dec_clock s)))
                           ltac:(wd_eval_lt) _ s2 E1 ltac:(discriminate) perm) as [q2 Hq2].
              cbn [fst snd] in Hq2.
              exists (perm_cons (permute s 0) q2). call_pre Eg Ebd Ef. call_post Ed Ec Ez.
              rewrite Hq2; reflexivity.
        -- injection H as <- <-.
           destruct (IH (prg, call_env args1 ss (push_env envs handler0 (dec_clock s)))
                        ltac:(wd_eval_lt) _ s2 E1 ltac:(discriminate) perm) as [q2 Hq2].
           cbn [fst snd] in Hq2.
           exists (perm_cons (permute s 0) q2). call_pre Eg Ebd Ef. call_post Ed Ec Ez.
           rewrite Hq2; reflexivity.
        -- injection H as <- <-.
           destruct (IH (prg, call_env args1 ss (push_env envs handler0 (dec_clock s)))
                        ltac:(wd_eval_lt) _ s2 E1 ltac:(discriminate) perm) as [q2 Hq2].
           cbn [fst snd] in Hq2.
           exists (perm_cons (permute s 0) q2). call_pre Eg Ebd Ef. call_post Ed Ec Ez.
           rewrite Hq2; reflexivity.
        -- injection H as <- <-.
           destruct (IH (prg, call_env args1 ss (push_env envs handler0 (dec_clock s)))
                        ltac:(wd_eval_lt) _ s2 E1 ltac:(discriminate) perm) as [q2 Hq2].
           cbn [fst snd] in Hq2.
           exists (perm_cons (permute s 0) q2). call_pre Eg Ebd Ef. call_post Ed Ec Ez.
           rewrite Hq2; reflexivity.
    + destruct (⌜handler0 = NONE⌝) eqn:Eh; [|injection H as <- _; exfalso; apply Hr; reflexivity].
      destruct (clock s =? 0) eqn:Ez.
      * injection H as <- <-. exists perm. call_pre Eg Ebd Ef. rewrite Eh, Ez; reflexivity.
      * destruct (evaluate (prg, call_env args1 ss (dec_clock s))) as [r1 s2] eqn:E1.
        pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
        destruct (bad_fun_return r1) eqn:Eb; [injection H as <- _; exfalso; apply Hr; reflexivity|].
        injection H as <- <-.
        assert (Hr1 : r1 <> SOME Error) by exact Hr.
        destruct (IH (prg, call_env args1 ss (dec_clock s)) ltac:(wd_eval_lt) _ s2 E1 Hr1 perm) as [q Hq].
        cbn [fst snd] in Hq.
        exists q. call_pre Eg Ebd Ef. rewrite Eh, Ez; cbn beta iota zeta; autorewrite with wdp; rewrite Hq; cbn beta iota zeta;
          rewrite Eb; reflexivity.
  - (* Seq *)
    rewrite fix_clock_evaluate in H. destruct (evaluate (p1, s)) as [r1 s1] eqn:E1.
    pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
    destruct (bool_decide (r1 = NONE)) eqn:Eb.
    + pose proof Eb as Eb'; apply bool_decide_spec in Eb'; subst r1.
      destruct (IH (p2, s1) ltac:(wd_eval_lt) r t H Hr perm) as [q1 Hq1].
      destruct (IH (p1, s) ltac:(wd_eval_lt) NONE s1 E1 ltac:(discriminate) q1) as [q2 Hq2].
      cbn [fst snd] in Hq1, Hq2.
      exists q2; rewrite evaluate_eqn; cbn [evaluate_body]; rewrite fix_clock_evaluate, Hq2;
        cbn beta iota zeta; rewrite Eb; exact Hq1.
    + injection H as <- <-.
      destruct (IH (p1, s) ltac:(wd_eval_lt) r1 s1 E1 Hr perm) as [q Hq]; cbn [fst snd] in Hq.
      exists q; rewrite evaluate_eqn; cbn [evaluate_body]; rewrite fix_clock_evaluate, Hq;
        cbn beta iota zeta; rewrite Eb; reflexivity.
  - (* If *)
    split_H H; try (injection H as <- _; exfalso; apply Hr; reflexivity);
      [destruct (IH (p1, s) ltac:(wd_eval_lt) r t H Hr perm) as [q Hq]
      |destruct (IH (p2, s) ltac:(wd_eval_lt) r t H Hr perm) as [q Hq]];
      cbn [fst snd] in Hq;
      exists q; rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with wdp; rw_cases; exact Hq.
  - (* Loop *)
    destruct (cut_state (s0, LN) s) as [s2|] eqn:Ec; [|injection H as <- _; exfalso; apply Hr; reflexivity].
    cbn beta iota zeta in H; rewrite fix_clock_evaluate in H.
    destruct (evaluate (p, s2)) as [r1 s3] eqn:E1.
    pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
    destruct (cont_loop r1) eqn:Ecl.
    + assert (Hr1 : r1 <> SOME Error) by (destruct r1 as [[]|]; cbn in Ecl; congruence).
      destruct (clock s3 =? 0) eqn:Ez.
      * injection H as <- <-.
        destruct (IH (p, s2) ltac:(wd_eval_lt) r1 s3 E1 Hr1 perm) as [q Hq]; cbn [fst snd] in Hq.
        exists q; rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with wdp; rewrite Ec;
          cbn [OPTION_MAP option_map]; rewrite fix_clock_evaluate, Hq; cbn beta iota zeta;
          rewrite Ecl; autorewrite with wdp; rewrite Ez; reflexivity.
      * destruct (IH (STOP (Loop s0 p s1), dec_clock s3) ltac:(wd_eval_lt) r t H Hr perm) as [q1 Hq1].
        destruct (IH (p, s2) ltac:(wd_eval_lt) r1 s3 E1 Hr1 q1) as [q2 Hq2].
        cbn [fst snd] in Hq1, Hq2.
        exists q2; rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with wdp; rewrite Ec;
          cbn [OPTION_MAP option_map]; rewrite fix_clock_evaluate, Hq2; cbn beta iota zeta;
          rewrite Ecl; autorewrite with wdp; rewrite Ez; exact Hq1.
    + destruct (bool_decide (r1 = SOME (Break 0))) eqn:Eb.
      * destruct (cut_state (s1, LN) s3) as [s4|] eqn:Ec2; [|injection H as <- _; exfalso; apply Hr; reflexivity].
        injection H as <- <-.
        assert (Hr1 : r1 <> SOME Error) by (apply bool_decide_spec in Eb; subst; discriminate).
        destruct (IH (p, s2) ltac:(wd_eval_lt) r1 s3 E1 Hr1 perm) as [q Hq]; cbn [fst snd] in Hq.
        exists q; rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with wdp; rewrite Ec;
          cbn [OPTION_MAP option_map]; rewrite fix_clock_evaluate, Hq; cbn beta iota zeta;
          rewrite Ecl, Eb; autorewrite with wdp; rewrite Ec2; reflexivity.
      * injection H as <- <-.
        assert (Hr1 : r1 <> SOME Error) by (intros ->; apply Hr; reflexivity).
        destruct (IH (p, s2) ltac:(wd_eval_lt) r1 s3 E1 Hr1 perm) as [q Hq]; cbn [fst snd] in Hq.
        exists q; rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with wdp; rewrite Ec;
          cbn [OPTION_MAP option_map]; rewrite fix_clock_evaluate, Hq; cbn beta iota zeta;
          rewrite Ecl, Eb; reflexivity.
  - (* Alloc *)
    split_H H; try (injection H as <- _; exfalso; apply Hr; reflexivity).
    exists (perm_cons (permute s 0) perm); rewrite evaluate_eqn; cbn [evaluate_body];
      autorewrite with wdp; rw_cases; apply alloc_perm_cons; assumption.
Qed.

End PermSwap.

(** ** [permute_swap_lemma2] and [permute_swap_lemma3] *)

(** Commuting with [set_stack], without [set_permute_set_stack] (which
    would loop with [wdp]) (Galette-only). *)
Create Rewrite HintDb wps.
Global Hint Rewrite @locals_set_stack @locals_size_set_stack @fp_regs_set_stack @store_set_stack
  @stack_limit_set_stack @stack_max_set_stack @state_stack_size_set_stack @memory_set_stack
  @mdomain_set_stack @sh_mdomain_set_stack @permute_set_stack @compile_set_stack
  @compile_oracle_set_stack @code_buffer_set_stack @data_buffer_set_stack @gc_fun_set_stack
  @handler_set_stack @clock_set_stack @termdep_set_stack @code_set_stack @be_set_stack
  @ffi_set_stack @stack_set_stack @set_stack_set_stack @set_locals_set_stack
  @set_locals_size_set_stack @set_fp_regs_set_stack @set_store_field_set_stack
  @set_stack_max_set_stack @set_stack_size_set_stack @set_memory_set_stack @set_mdomain_set_stack
  @set_sh_mdomain_set_stack @set_compile_set_stack @set_compile_oracle_set_stack
  @set_code_buffer_set_stack @set_data_buffer_set_stack @set_gc_fun_set_stack
  @set_handler_set_stack @set_clock_set_stack @set_termdep_set_stack @set_code_set_stack
  @set_be_set_stack @set_ffi_set_stack @set_var_set_stack @unset_var_set_stack
  @set_vars_set_stack @set_store_set_stack @set_fp_var_set_stack @flush_state_true_set_stack
  @flush_state_false_set_stack @dec_clock_set_stack @get_var_set_stack @get_vars_set_stack
  @get_store_set_stack @get_fp_var_set_stack @mem_load_set_stack @get_var_imm_set_stack
  @has_space_set_stack @word_exp_set_stack @mem_store_set_stack @cut_state_set_stack
  @inst_set_stack @sh_mem_load_set_stack @sh_mem_load_byte_set_stack @sh_mem_load16_set_stack
  @sh_mem_load32_set_stack : wps.

Section PermSwap2.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).
Local Abbreviation frame := (stack_frame a).

(** Galette-only helpers. *)
Local Lemma LIST_REL_app {A B} (R : A -> B -> Prop) l1 l2 m1 m2 :
  LIST_REL R l1 l2 -> LIST_REL R m1 m2 -> LIST_REL R (l1 ++ m1) (l2 ++ m2).
Proof. induction 1; cbn; [auto|]. intros Hm; constructor; auto. Qed.

Local Lemma LIST_REL_REVERSE {A B} (R : A -> B -> Prop) l1 l2 :
  LIST_REL R l1 l2 -> LIST_REL R (REVERSE l1) (REVERSE l2).
Proof.
  induction 1; cbn; [constructor|].
  apply LIST_REL_app; [assumption|constructor; [assumption|constructor]].
Qed.

Local Lemma LIST_REL_TAKE {A B} (R : A -> B -> Prop) n l1 l2 :
  LIST_REL R l1 l2 -> LIST_REL R (TAKE n l1) (TAKE n l2).
Proof.
  intros H; revert n; induction H; intros n; cbn; [constructor|].
  destruct (n =? 0); cbn; constructor; auto.
Qed.

Local Lemma LIST_REL_LASTN {A B} (R : A -> B -> Prop) n l1 l2 :
  LIST_REL R l1 l2 -> LIST_REL R (LASTN n l1) (LASTN n l2).
Proof. intros H; unfold LASTN; apply LIST_REL_REVERSE, LIST_REL_TAKE, LIST_REL_REVERSE, H. Qed.

Local Lemma LIST_REL_LENGTH' {A B} (R : A -> B -> Prop) l1 l2 :
  LIST_REL R l1 l2 -> LENGTH l1 = LENGTH l2.
Proof.
  intros H; rewrite !LENGTH_length; f_equal; induction H; cbn; [reflexivity|]. f_equal; assumption.
Qed.

Local Lemma call_env_set_stack args ss xs (s : state) :
  stack_size xs = stack_size (stack s) ->
  call_env args ss (set_stack xs s) = set_stack xs (call_env args ss s).
Proof. intros H; unfold call_env; unfold_sets; rewrite H; reflexivity. Qed.

Local Lemma push_env_set_stack envs (h : option (N * (prog a * (N * N)))) p stk (s : state) :
  LIST_REL PERM_STACK stk (stack s) ->
  exists fr, push_env envs h (set_permute p (set_stack stk s)) =
     set_permute (fun n => p (n + 1)) (set_stack (fr :: stk) (push_env envs h s)) /\
     LIST_REL PERM_STACK (fr :: stk) (stack (push_env envs h s)).
Proof.
  intros H. pose proof (stack_size_perm _ _ H) as Hsz. pose proof (LIST_REL_LENGTH' _ _ _ H) as Hl.
  assert (Hc : forall f, stack_size (f :: stk) = stack_size (f :: stack s)).
  { intros f; change (OPTION_MAP2 N.add (stack_size_frame f) (stack_size stk) =
                      OPTION_MAP2 N.add (stack_size_frame f) (stack_size (stack s))); rewrite Hsz; reflexivity. }
  pose proof (env_to_list_PERM (SND envs) p (permute s)) as HP.
  pose proof (env_to_list_ALL_DISTINCT_FST (SND envs) p) as Hd.
  destruct (env_to_list (SND envs) p) as [l q] eqn:E1.
  destruct (env_to_list (SND envs) (permute s)) as [l' q'] eqn:E2.
  assert (Hq : q = fun n => p (n + 1)) by (unfold env_to_list in E1; injection E1 as _ <-; reflexivity).
  cbn [FST fst] in HP, Hd. subst q.
  destruct h as [[w [hp [l1 l2]]]|]; unfold push_env; cbn [permute set_permute set_stack locals_size stack handler];
    rewrite ?E1, ?E2; cbn zeta.
  - eexists; split.
    + unfold_sets. rewrite Hc, Hl. reflexivity.
    + unfold_sets. constructor; [|exact H]. cbn. repeat split; assumption.
  - eexists; split.
    + unfold_sets. rewrite Hc. reflexivity.
    + unfold_sets. constructor; [|exact H]. cbn. repeat split; assumption.
Qed.

Local Lemma pop_env_set_stack stk (s s1 : state) :
  LIST_REL PERM_STACK stk (stack s) -> pop_env s = SOME s1 ->
  exists stk', pop_env (set_stack stk s) = SOME (set_stack stk' s1) /\ LIST_REL PERM_STACK stk' (stack s1).
Proof.
  intros H Hp; unfold pop_env in *; unfold_sets.
  destruct (stack s) as [|f xs]; [discriminate|].
  inversion H as [|f' f0 stk' xs' Hf Hr]; subst.
  destruct f' as [m' e0' e' h'], f as [m e0 e h]; destruct Hf as (-> & -> & -> & HP & Hd).
  rewrite (PERM_fromAList _ _ (conj HP Hd)).
  destruct h as [[n ?]|]; injection Hp as <-; exists stk'; split; try reflexivity; exact Hr.
Qed.

Local Lemma jump_exc_set_stack stk (s s1 : state) l :
  LIST_REL PERM_STACK stk (stack s) -> jump_exc s = SOME (s1, l) ->
  exists stk', jump_exc (set_stack stk s) = SOME (set_stack stk' s1, l) /\ LIST_REL PERM_STACK stk' (stack s1).
Proof.
  intros H Hj; unfold jump_exc in *; unfold_sets.
  rewrite (LIST_REL_LENGTH' _ _ _ H).
  destruct (handler s <? LENGTH (stack s)); [|discriminate].
  pose proof (LIST_REL_LASTN _ (handler s + 1) _ _ H) as HL.
  destruct (LASTN (handler s + 1) (stack s)) as [|f xs]; [discriminate|].
  inversion HL as [|f' f0 stk' xs' Hf Hr]; subst.
  destruct f' as [m' e0' e' h'], f as [m e0 e h]; destruct Hf as (-> & -> & -> & HP & Hd).
  destruct h as [[n [l1 l2]]|]; [|discriminate]. injection Hj as <- <-.
  rewrite (PERM_fromAList _ _ (conj HP Hd)).
  exists stk'; split; [reflexivity|exact Hr].
Qed.

Local Lemma share_inst_set_stack op v ad xs (s t : state) r :
  share_inst op v ad s = (r, t) ->
  (share_inst op v ad (set_stack xs s) = (r, set_stack xs t) /\ stack t = stack s) \/
  (share_inst op v ad (set_stack xs s) = (r, set_stack [] t) /\ stack t = []).
Proof.
  intros H; destruct op; cbn [share_inst] in *;
    unfold sh_mem_set_var, sh_mem_load, sh_mem_load_byte, sh_mem_load16, sh_mem_load32,
      sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32 in *;
    cbn [sh_mdomain ffi set_stack]; rewrite ?get_var_set_stack;
    split_H H; leaf H; try rw_cases;
    first [ left; split; reflexivity | right; split; reflexivity ].
Qed.


Local Ltac sw_simpl H := autorewrite with wdp wps in H |- *; cbn [PAIR_MAP option_map fst snd I] in H |- *.

Local Ltac no_contra :=
  match goal with
  | Hn : no_alloc _ |- _ => exfalso; unfold no_alloc in Hn; cbn [not_created_subprogs] in Hn; apply Hn; reflexivity
  | Hn : no_install _ |- _ => exfalso; unfold no_install in Hn; cbn [not_created_subprogs] in Hn; apply Hn; reflexivity
  end.

Local Ltac sub_no :=
  first [ assumption
        | unfold no_alloc, no_install in *; cbn [not_created_subprogs STOP] in *; destr_conj; assumption ].

(** HOL's [PERM] is Rocq's [Permutation] (in [PERM_STACK]), so this is
    not tagged.  HOL [st with <|permute := perm; stack := stack|>] is
    [set_stack stack (set_permute perm st)]. *)
Theorem permute_swap_lemma2 : forall (prog : prog a) (st : state) perm stack,
  let '(res, rst) := evaluate (prog, st) in
  res <> SOME Error /\ no_alloc_code (code st) /\ no_alloc prog /\
  no_install_code (code st) /\ no_install prog /\
  LIST_REL PERM_STACK stack (wordSem.stack st) ->
  exists perm' stack',
    evaluate (prog, set_stack stack (set_permute perm st)) =
      (res, set_stack stack' (set_permute perm' rst)) /\
    LIST_REL PERM_STACK stack' (wordSem.stack rst).
Proof.
  enough (G : forall x : prog a * state, forall r t, evaluate x = (r, t) -> r <> SOME Error ->
    no_alloc_code (code (snd x)) -> no_alloc (fst x) -> no_install_code (code (snd x)) -> no_install (fst x) ->
    forall perm stk, LIST_REL PERM_STACK stk (stack (snd x)) ->
    exists perm' stk', evaluate (fst x, set_permute perm (set_stack stk (snd x))) =
                         (r, set_permute perm' (set_stack stk' t)) /\ LIST_REL PERM_STACK stk' (stack t)).
  { intros prog st perm stk; destruct (evaluate (prog, st)) as [r t] eqn:E; intros (Hr & H1 & H2 & H3 & H4 & H5).
    destruct (G (prog, st) r t E Hr H1 H2 H3 H4 perm stk H5) as (q & stk' & Hq & Hrel).
    exists q, stk'; split; [|exact Hrel]. rewrite !set_stack_set_permute. exact Hq. }
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r t H Hr Hac Hna Hic Hni perm stk Hrel; cbn [fst snd] in *.
  rewrite evaluate_eqn in H; destruct p; cbn [evaluate_body] in H.
  all: try no_contra.
  all: try (rewrite evaluate_eqn; cbn [evaluate_body]; sw_simpl H;
            split_H H; leaf H; try (exfalso; apply Hr; reflexivity);
            repeat progress (rw_cases; autorewrite with wdp wps; cbn [PAIR_MAP I fst snd option_map]);
            first [ exists perm, stk; split; [reflexivity|unfold_sets; exact Hrel]
                  | exists perm, (@nil frame); split; [reflexivity|unfold_sets; constructor] ]).

  - (* Inst *)
    destruct (inst i s) as [s1|] eqn:Ei; [|injection H as <- _; exfalso; apply Hr; reflexivity].
    injection H as <- <-. exists perm, stk; split.
    + rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with wdp wps; rewrite Ei; reflexivity.
    + apply inst_const_full in Ei; destr_conj. match goal with E : stack s1 = _ |- _ => rewrite E end; exact Hrel.
  - (* Store *)
    split_H H; leaf H; try (exfalso; apply Hr; reflexivity).
    exists perm, stk; split.
    + rewrite evaluate_eqn; cbn [evaluate_body];
      repeat progress (autorewrite with wdp wps; rw_cases; cbn [option_map]); reflexivity.
    + match goal with E : mem_store _ _ _ = SOME _ |- _ => apply mem_store_const in E end; destr_conj.
      match goal with E : stack _ = stack s |- _ => rewrite E end; exact Hrel.
  - (* MustTerminate *)
    destruct (termdep s =? 0) eqn:Et; [injection H as <- _; exfalso; apply Hr; reflexivity|].
    destruct (evaluate (p, set_termdep (termdep s - 1) (set_clock (MustTerminate_limit a) s)))
      as [r1 s1] eqn:E1.
    pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
    destruct (bool_decide (r1 = SOME TimeOut)) eqn:Eb; [injection H as <- _; exfalso; apply Hr; reflexivity|].
    injection H as <- <-.
    destruct (IH (p, set_termdep (termdep s - 1) (set_clock (MustTerminate_limit a) s))
                 ltac:(wd_eval_lt) r1 s1 E1 Hr Hac ltac:(sub_no) Hic ltac:(sub_no) perm stk Hrel)
      as (q & stk1 & Hq & Hrel1); cbn [fst snd] in Hq.
    exists q, stk1; split; [|exact Hrel1].
    rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with wdp wps; rewrite Et;
      cbn beta iota zeta; rewrite Hq; cbn beta iota zeta; rewrite Eb; autorewrite with wdp wps; reflexivity.
  - (* Call *)
    rename o into ret, o0 into dest, l into args, o1 into handler0.
    destruct (get_vars args s) as [xs|] eqn:Eg; [|injection H as <- _; exfalso; apply Hr; reflexivity].
    cbn beta iota zeta in H.
    destruct (bad_dest_args dest args) eqn:Ebd; [injection H as <- _; exfalso; apply Hr; reflexivity|].
    destruct (find_code dest (add_ret_loc ret xs) (code s) (state_stack_size s)) as [[args1 [prg ss]]|] eqn:Ef;
      [|injection H as <- _; exfalso; apply Hr; reflexivity].
    cbn beta iota zeta in H.
    assert (Hnap : no_alloc prg) by (eapply no_alloc_find_code; split; eassumption).
    assert (Hnip : no_install prg) by (eapply no_install_find_code; split; eassumption).
    pose proof (stack_size_perm _ _ Hrel) as Hsz.
    Local Ltac call_pre2 Eg Ebd Ef :=
      rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with wdp wps; rewrite Eg; cbn beta iota zeta;
      rewrite Ebd; rewrite Ef; cbn beta iota zeta.
    destruct ret as [[n [names [ret_handler [l1 l2]]]]|].
    + destruct (⌜domain (FST names) = {}⌝ || negb (ALL_DISTINCT n)) eqn:Ed;
        [injection H as <- _; exfalso; apply Hr; reflexivity|].
      destruct (cut_envs names (locals s)) as [envs|] eqn:Ec; [|injection H as <- _; exfalso; apply Hr; reflexivity].
      destruct (clock s =? 0) eqn:Ez.
      * injection H as <- <-. exists perm, (@nil frame); split; [|constructor].
        call_pre2 Eg Ebd Ef. rewrite Ed, Ec, Ez; cbn beta iota zeta.
        destruct (push_env_set_stack envs handler0 perm stk s Hrel) as (fr & Ep & Hrelp).
        rewrite Ep. autorewrite with wdp.
        rewrite call_env_set_stack by exact (stack_size_perm _ _ Hrelp).
        autorewrite with wdp wps. reflexivity.
      * rewrite fix_clock_evaluate in H.
        destruct (evaluate (prg, call_env args1 ss (push_env envs handler0 (dec_clock s)))) as [r1 s2] eqn:E1.
        pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
        destruct (push_env_set_stack envs handler0 perm stk (dec_clock s) Hrel) as (fr & Ep & Hrelp).
        pose proof (push_env_const envs handler0 (dec_clock s)) as Hpc; destr_conj.
        assert (Hcc : code (call_env args1 ss (push_env envs handler0 (dec_clock s))) = code s)
          by (unfold call_env, dec_clock in *; unfold_sets; congruence).
        assert (Hac' : no_alloc_code (code (call_env args1 ss (push_env envs handler0 (dec_clock s)))))
          by (rewrite Hcc; exact Hac).
        assert (Hic' : no_install_code (code (call_env args1 ss (push_env envs handler0 (dec_clock s)))))
          by (rewrite Hcc; exact Hic).
        assert (Hcs : code s = code s2).
        { rewrite <- Hcc. apply (no_install_evaluate_const_code prg _ r1 s2); repeat split; assumption. }
        assert (Hrelc : LIST_REL PERM_STACK (fr :: stk)
                          (stack (call_env args1 ss (push_env envs handler0 (dec_clock s))))) by exact Hrelp.
        Local Ltac call_post2 Ed Ec Ez Ep Hrelp Hq :=
          rewrite Ed, Ec, Ez; cbn beta iota zeta; rewrite fix_clock_evaluate;
          rewrite Ep; autorewrite with wdp;
          rewrite call_env_set_stack by exact (stack_size_perm _ _ Hrelp);
          rewrite Hq; cbn beta iota zeta.
        destruct r1 as [r1|]; [destruct r1 as [x ys|x y|k|k| | |f|]|];
          try (injection H as <- _; exfalso; apply Hr; reflexivity).
        -- destruct (negb ⌜x = Loc l1 l2⌝ || negb (LENGTH ys =? LENGTH n)) eqn:Ex;
             [injection H as <- _; exfalso; apply Hr; reflexivity|].
           destruct (pop_env s2) as [s3|] eqn:Ep2; [|injection H as <- _; exfalso; apply Hr; reflexivity].
           destruct (⌜domain (locals s3) = domain (FST envs) UNION domain (SND envs)⌝) eqn:Edom;
             [|injection H as <- _; exfalso; apply Hr; reflexivity].
           destruct (IH (prg, call_env args1 ss (push_env envs handler0 (dec_clock s))) ltac:(wd_eval_lt)
                        _ s2 E1 ltac:(discriminate) Hac' Hnap Hic' Hnip (fun k0 => perm (k0 + 1)) _ Hrelc) as (q & stk2 & Hq & Hrel2).
           cbn [fst snd] in Hq.
           destruct (pop_env_set_stack stk2 s2 s3 Hrel2 Ep2) as (stk3 & Epop & Hrel3).
           pose proof (pop_env_const _ _ Ep2) as Hpc2; destr_conj.
           assert (Hc3 : code (set_vars n ys s3) = code s) by (cbn; congruence).
           rewrite <- Hc3 in Hac, Hic.
           destruct (IH (ret_handler, set_vars n ys s3) ltac:(wd_eval_lt) r t H Hr Hac ltac:(sub_no) Hic
                        ltac:(sub_no) q stk3 Hrel3) as (q3 & stk4 & Hq3 & Hrel4).
           cbn [fst snd] in Hq3.
           exists q3, stk4; split; [|exact Hrel4].
           call_pre2 Eg Ebd Ef. call_post2 Ed Ec Ez Ep Hrelp Hq.
           rewrite Ex; autorewrite with wdp; rewrite Epop; cbn [OPTION_MAP option_map].
           autorewrite with wdp wps; rewrite Edom; cbn beta iota zeta.
           autorewrite with wdp wps in Hq3 |- *; exact Hq3.
        -- destruct handler0 as [[hn [hp [hl1 hl2]]]|].
           ++ destruct (negb ⌜x = Loc hl1 hl2⌝) eqn:Ex; [injection H as <- _; exfalso; apply Hr; reflexivity|].
              destruct (⌜domain (locals s2) = domain (FST envs) UNION domain (SND envs)⌝) eqn:Edom;
                [|injection H as <- _; exfalso; apply Hr; reflexivity].
              destruct (IH (prg, call_env args1 ss (push_env envs (SOME (hn, (hp, (hl1, hl2)))) (dec_clock s)))
                           ltac:(wd_eval_lt) _ s2 E1 ltac:(discriminate) Hac' Hnap Hic' Hnip (fun k0 => perm (k0 + 1)) _ Hrelc)
                as (q & stk2 & Hq & Hrel2).
              cbn [fst snd] in Hq.
              assert (Hc3 : code (set_var hn y s2) = code s) by (cbn; congruence).
              rewrite <- Hc3 in Hac, Hic.
              destruct (IH (hp, set_var hn y s2) ltac:(wd_eval_lt) r t H Hr Hac ltac:(sub_no) Hic
                           ltac:(sub_no) q stk2 Hrel2) as (q3 & stk3 & Hq3 & Hrel3).
              cbn [fst snd] in Hq3.
              exists q3, stk3; split; [|exact Hrel3].
              call_pre2 Eg Ebd Ef. call_post2 Ed Ec Ez Ep Hrelp Hq.
              rewrite Ex; autorewrite with wdp wps; rewrite Edom; cbn beta iota zeta.
              autorewrite with wdp wps in Hq3 |- *; exact Hq3.
           ++ injection H as <- <-.
              destruct (IH (prg, call_env args1 ss (push_env envs NONE (dec_clock s)))
                           ltac:(wd_eval_lt) _ s2 E1 ltac:(discriminate) Hac' Hnap Hic' Hnip (fun k0 => perm (k0 + 1)) _ Hrelc)
                as (q & stk2 & Hq & Hrel2).
              cbn [fst snd] in Hq.
              exists q, stk2; split; [|exact Hrel2].
              call_pre2 Eg Ebd Ef. call_post2 Ed Ec Ez Ep Hrelp Hq. reflexivity.
        -- injection H as <- <-.
           destruct (IH (prg, call_env args1 ss (push_env envs handler0 (dec_clock s)))
                        ltac:(wd_eval_lt) _ s2 E1 ltac:(discriminate) Hac' Hnap Hic' Hnip (fun k0 => perm (k0 + 1)) _ Hrelc)
             as (q & stk2 & Hq & Hrel2).
           cbn [fst snd] in Hq.
           exists q, stk2; split; [|exact Hrel2].
           call_pre2 Eg Ebd Ef. call_post2 Ed Ec Ez Ep Hrelp Hq. reflexivity.
        -- injection H as <- <-.
           destruct (IH (prg, call_env args1 ss (push_env envs handler0 (dec_clock s)))
                        ltac:(wd_eval_lt) _ s2 E1 ltac:(discriminate) Hac' Hnap Hic' Hnip (fun k0 => perm (k0 + 1)) _ Hrelc)
             as (q & stk2 & Hq & Hrel2).
           cbn [fst snd] in Hq.
           exists q, stk2; split; [|exact Hrel2].
           call_pre2 Eg Ebd Ef. call_post2 Ed Ec Ez Ep Hrelp Hq. reflexivity.
        -- injection H as <- <-.
           destruct (IH (prg, call_env args1 ss (push_env envs handler0 (dec_clock s)))
                        ltac:(wd_eval_lt) _ s2 E1 ltac:(discriminate) Hac' Hnap Hic' Hnip (fun k0 => perm (k0 + 1)) _ Hrelc)
             as (q & stk2 & Hq & Hrel2).
           cbn [fst snd] in Hq.
           exists q, stk2; split; [|exact Hrel2].
           call_pre2 Eg Ebd Ef. call_post2 Ed Ec Ez Ep Hrelp Hq. reflexivity.
    + destruct (⌜handler0 = NONE⌝) eqn:Eh; [|injection H as <- _; exfalso; apply Hr; reflexivity].
      destruct (clock s =? 0) eqn:Ez.
      * injection H as <- <-. exists perm, (@nil frame); split; [|constructor].
        call_pre2 Eg Ebd Ef. rewrite Eh, Ez. reflexivity.
      * destruct (evaluate (prg, call_env args1 ss (dec_clock s))) as [r1 s2] eqn:E1.
        pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
        destruct (bad_fun_return r1) eqn:Eb; [injection H as <- _; exfalso; apply Hr; reflexivity|].
        injection H as <- <-.
        destruct (IH (prg, call_env args1 ss (dec_clock s)) ltac:(wd_eval_lt) _ s2 E1 Hr Hac Hnap Hic Hnip
                     perm stk Hrel) as (q & stk2 & Hq & Hrel2).
        cbn [fst snd] in Hq.
        exists q, stk2; split; [|exact Hrel2].
        call_pre2 Eg Ebd Ef. rewrite Eh, Ez; cbn beta iota zeta. autorewrite with wdp.
        rewrite call_env_set_stack by exact Hsz.
        rewrite Hq; cbn beta iota zeta; rewrite Eb; reflexivity.
  - (* Seq *)
    rewrite fix_clock_evaluate in H. destruct (evaluate (p1, s)) as [r1 s1] eqn:E1.
    pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
    destruct (bool_decide (r1 = NONE)) eqn:Eb.
    + pose proof Eb as Eb'; apply bool_decide_spec in Eb'; subst r1.
      destruct (IH (p1, s) ltac:(wd_eval_lt) NONE s1 E1 ltac:(discriminate) Hac ltac:(sub_no) Hic ltac:(sub_no)
                   perm stk Hrel) as (q & stk1 & Hq & Hrel1).
      assert (Hcs : code s = code s1)
        by (apply (no_install_evaluate_const_code p1 s NONE s1); repeat split; [exact E1|sub_no|exact Hic]).
      rewrite Hcs in Hac, Hic.
      destruct (IH (p2, s1) ltac:(wd_eval_lt) r t H Hr Hac ltac:(sub_no) Hic ltac:(sub_no) q stk1 Hrel1)
        as (q2 & stk2 & Hq2 & Hrel2).
      cbn [fst snd] in Hq, Hq2.
      exists q2, stk2; split; [|exact Hrel2].
      rewrite evaluate_eqn; cbn [evaluate_body]; rewrite fix_clock_evaluate, Hq;
        cbn beta iota zeta; rewrite Eb; exact Hq2.
    + injection H as <- <-.
      destruct (IH (p1, s) ltac:(wd_eval_lt) r1 s1 E1 Hr Hac ltac:(sub_no) Hic ltac:(sub_no)
                   perm stk Hrel) as (q & stk1 & Hq & Hrel1); cbn [fst snd] in Hq.
      exists q, stk1; split; [|exact Hrel1].
      rewrite evaluate_eqn; cbn [evaluate_body]; rewrite fix_clock_evaluate, Hq;
        cbn beta iota zeta; rewrite Eb; reflexivity.
  - (* If *)
    split_H H; try (injection H as <- _; exfalso; apply Hr; reflexivity);
      [destruct (IH (p1, s) ltac:(wd_eval_lt) r t H Hr Hac ltac:(sub_no) Hic ltac:(sub_no) perm stk Hrel)
         as (q & stk1 & Hq & Hrel1)
      |destruct (IH (p2, s) ltac:(wd_eval_lt) r t H Hr Hac ltac:(sub_no) Hic ltac:(sub_no) perm stk Hrel)
         as (q & stk1 & Hq & Hrel1)];
      cbn [fst snd] in Hq;
      exists q, stk1; (split; [|exact Hrel1]);
      rewrite evaluate_eqn; cbn [evaluate_body]; repeat progress (autorewrite with wdp wps; rw_cases); exact Hq.
  - (* Loop *)
    destruct (cut_state (s0, LN) s) as [s2|] eqn:Ec; [|injection H as <- _; exfalso; apply Hr; reflexivity].
    cbn beta iota zeta in H; rewrite fix_clock_evaluate in H.
    pose proof Ec as Ec'; apply cut_state_const in Ec'; destruct Ec' as [lc ->].
    destruct (evaluate (p, set_locals lc s)) as [r1 s3] eqn:E1.
    pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
    assert (Hcs : code (set_locals lc s) = code s3).
    { apply (no_install_evaluate_const_code p (set_locals lc s) r1 s3); repeat split; [exact E1|sub_no|exact Hic]. }
    Local Ltac loop_pre Ec Hq :=
      rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with wdp wps; rewrite Ec;
      cbn [OPTION_MAP option_map]; rewrite fix_clock_evaluate, Hq; cbn beta iota zeta.
    destruct (cont_loop r1) eqn:Ecl.
    + assert (Hr1 : r1 <> SOME Error) by (destruct r1 as [[]|]; cbn in Ecl; congruence).
      destruct (IH (p, set_locals lc s) ltac:(wd_eval_lt) r1 s3 E1 Hr1 Hac ltac:(sub_no) Hic ltac:(sub_no)
                   perm stk Hrel) as (q & stk1 & Hq & Hrel1); cbn [fst snd] in Hq.
      destruct (clock s3 =? 0) eqn:Ez.
      * injection H as <- <-. exists q, (@nil frame); split; [|constructor].
        loop_pre Ec Hq; rewrite Ecl; autorewrite with wdp wps; rewrite Ez; reflexivity.
      * change (code (set_locals lc s)) with (code s) in Hcs. rewrite Hcs in Hac, Hic.
        destruct (IH (STOP (Loop s0 p s1), dec_clock s3) ltac:(wd_eval_lt) r t H Hr Hac ltac:(sub_no)
                     Hic ltac:(sub_no) q stk1 Hrel1) as (q2 & stk2 & Hq2 & Hrel2); cbn [fst snd] in Hq2.
        exists q2, stk2; split; [|exact Hrel2].
        loop_pre Ec Hq; rewrite Ecl; autorewrite with wdp wps; rewrite Ez; cbn beta iota zeta.
        autorewrite with wdp wps in Hq2; exact Hq2.
    + destruct (bool_decide (r1 = SOME (Break 0))) eqn:Eb.
      * destruct (cut_state (s1, LN) s3) as [s4|] eqn:Ec2; [|injection H as <- _; exfalso; apply Hr; reflexivity].
        injection H as <- <-.
        assert (Hr1 : r1 <> SOME Error) by (apply bool_decide_spec in Eb; subst; discriminate).
        destruct (IH (p, set_locals lc s) ltac:(wd_eval_lt) r1 s3 E1 Hr1 Hac ltac:(sub_no) Hic ltac:(sub_no)
                     perm stk Hrel) as (q & stk1 & Hq & Hrel1); cbn [fst snd] in Hq.
        pose proof Ec2 as Ec2'; apply cut_state_const in Ec2'; destruct Ec2' as [lc2 ->].
        exists q, stk1; split; [|exact Hrel1].
        loop_pre Ec Hq; rewrite Ecl, Eb; autorewrite with wdp wps; rewrite Ec2; reflexivity.
      * injection H as <- <-.
        assert (Hr1 : r1 <> SOME Error) by (intros ->; apply Hr; reflexivity).
        destruct (IH (p, set_locals lc s) ltac:(wd_eval_lt) r1 s3 E1 Hr1 Hac ltac:(sub_no) Hic ltac:(sub_no)
                     perm stk Hrel) as (q & stk1 & Hq & Hrel1); cbn [fst snd] in Hq.
        exists q, stk1; split; [|exact Hrel1].
        loop_pre Ec Hq; rewrite Ecl, Eb; reflexivity.
  - (* Raise *)
    split_H H; leaf H; try (exfalso; apply Hr; reflexivity).
    match goal with E : jump_exc s = SOME (?s1, _) |- _ =>
      destruct (jump_exc_set_stack stk s s1 _ Hrel E) as (stk1 & Ej & Hrel1) end.
    exists perm, stk1; split; [|exact Hrel1].
    rewrite evaluate_eqn; cbn [evaluate_body]; repeat progress (autorewrite with wdp wps; rw_cases).
    try rewrite Ej; reflexivity.
  - (* ShareInst *)
    split_H H; leaf H; try (exfalso; apply Hr; reflexivity).
    destruct (share_inst_set_stack _ _ _ stk _ _ _ H) as [[Es Est]|[Es Est]];
      [exists perm, stk|exists perm, (@nil frame)]; (split; [|rewrite Est; first [exact Hrel|constructor]]);
      rewrite evaluate_eqn; cbn [evaluate_body]; repeat progress (autorewrite with wdp wps; rw_cases);
      try rewrite Es; cbn [PAIR_MAP I]; reflexivity.
Qed.

(** HOL's [PERM] is Rocq's [Permutation] (in [PERM_STACK]), so this is
    not tagged.  HOL's statement also quantifies a vacuous variable
    [stack]; it is omitted. *)
Theorem permute_swap_lemma3 : forall (prog : prog a) (st : state) perm,
  let '(res, rst) := evaluate (prog, st) in
  res <> SOME Error /\ no_alloc_code (code st) /\ no_alloc prog /\
  no_install_code (code st) /\ no_install prog /\
  EVERY (fun st => match st with StackFrame _ _ vs handler => ALL_DISTINCT (MAP FST vs) end)
    (wordSem.stack st) ->
  exists perm' stack',
    evaluate (prog, set_permute perm st) = (res, set_stack stack' (set_permute perm' rst)) /\
    LIST_REL PERM_STACK stack' (wordSem.stack rst).
Proof.
  intros prog st perm.
  pose proof (permute_swap_lemma2 prog st perm (stack st)) as H2.
  destruct (evaluate (prog, st)) as [r t] eqn:E.
  intros (Hr & H1 & H3 & H4 & H5 & Hev).
  assert (Hrel : LIST_REL PERM_STACK (stack st) (stack st)).
  { clear -Hev. induction (stack st) as [|[m e0 e h] l IH]; constructor.
    - cbn in Hev. apply andb_prop in Hev as [Hd _]. cbn; repeat split; [apply Permutation_refl|exact Hd].
    - cbn in Hev. apply andb_prop in Hev as [_ Hl]. exact (IH Hl). }
  destruct (H2 (conj Hr (conj H1 (conj H3 (conj H4 (conj H5 Hrel)))))) as (q & stk & Hq & Hrel2).
  exists q, stk; split; [|exact Hrel2].
  replace (set_permute perm st) with (set_stack (stack st) (set_permute perm st)); [exact Hq|].
  apply state_component_equality; unfold_sets; repeat split; reflexivity.
Qed.

End PermSwap2.
