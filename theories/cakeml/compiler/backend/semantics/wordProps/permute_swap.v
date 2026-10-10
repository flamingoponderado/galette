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
    [set_permute]" is Galette-only infrastructure. *)

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
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import consts clock consts_with.
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
