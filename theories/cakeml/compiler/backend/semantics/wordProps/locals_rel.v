(** * CakeML [wordProps]: extra locals ([locals_rel])

    Port of the "Locals extend lemma" part of
    [cakeml/compiler/backend/semantics/wordPropsScript.sml]: [locals_rel],
    its lemmas for the primitives, and [locals_rel_evaluate_thm] (extra
    temporaries not mentioned in a program do not affect its evaluation).

    Carrier notes:
    - HOL's free variables ([temp], [st], [loc], ...) are quantified first.
      HOL's boolean predicate [λx. x < temp] is [fun x => x <? temp].
    - HOL [st with locals := loc] is [set_locals loc st].
    - [locals_rel_evaluate_thm] is proved by induction on the program
      ([prog_nested_ind]), as HOL's proof (complete induction on the
      program size); HOL's per-constructor [Resume] blocks are the bullets
      of the proof. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
From Galette.cakeml.misc Require Import misc.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common wordLang.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem wordConvs.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import consts clock consts_with.
Open Scope N_scope.

Section LocalsRel.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_def" *)
Definition locals_rel (temp : N) (s t : num_map (word_loc a)) : Prop :=
  forall x, x < temp -> lookup x s = lookup x t.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "the_words_EVERY_IS_SOME" *)
Theorem the_words_EVERY_IS_SOME : forall (ls : list (option (word_loc a))) x,
  the_words ls = SOME x -> EVERY IS_SOME ls.
Proof.
  induction ls as [|w ls IH]; intros x H; [reflexivity|].
  cbn in H |- *. destruct w as [[w|]|]; [|discriminate..].
  destruct (the_words ls) as [xs|] eqn:E; [|discriminate]. exact (IH xs eq_refl).
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_get_var" *)
Theorem locals_rel_get_var : forall temp (st : state) loc r x,
  r < temp /\ get_var r st = SOME x /\ locals_rel temp (locals st) loc ->
  get_var r (set_locals loc st) = SOME x.
Proof.
  intros temp st loc r x (Hr & H & Hl); unfold get_var in *; cbn [locals set_locals].
  rewrite <- Hl by exact Hr; exact H.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_get_var_simp" *)
Theorem locals_rel_get_var_simp : forall temp (st : state) loc r,
  r < temp /\ locals_rel temp (locals st) loc ->
  get_var r (set_locals loc st) = get_var r st.
Proof.
  intros temp st loc r (Hr & Hl); unfold get_var; cbn [locals set_locals].
  symmetry; apply Hl, Hr.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_get_vars_simp" *)
Theorem locals_rel_get_vars_simp : forall temp (st : state) loc l,
  EVERY (fun x => x <? temp) l /\ locals_rel temp (locals st) loc ->
  get_vars l (set_locals loc st) = get_vars l st.
Proof.
  intros temp st loc l [He Hl]; induction l as [|x l IH]; [reflexivity|].
  cbn [get_vars EVERY] in He |- *; apply andb_prop in He as [Hx He]; apply N.ltb_lt in Hx.
  rewrite (locals_rel_get_var_simp temp st loc x (conj Hx Hl)), (IH He); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_get_vars" *)
Theorem locals_rel_get_vars : forall temp (st : state) loc ls vs,
  get_vars ls st = SOME vs /\ EVERY (fun x => x <? temp) ls /\ locals_rel temp (locals st) loc ->
  get_vars ls (set_locals loc st) = SOME vs.
Proof.
  intros temp st loc ls vs (H & He & Hl); rewrite (locals_rel_get_vars_simp temp) by (split; assumption).
  exact H.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_alist_insert" *)
Theorem locals_rel_alist_insert : forall temp ls vs (s t : num_map (word_loc a)),
  locals_rel temp s t /\ EVERY (fun x => x <? temp) ls ->
  locals_rel temp (alist_insert ls vs s) (alist_insert ls vs t).
Proof.
  intros temp ls; induction ls as [|v ls IH]; intros vs s t [Hl He]; [exact Hl|].
  destruct vs as [|w vs]; [exact Hl|].
  cbn in He |- *; apply andb_prop in He as [_ He].
  intros x Hx; rewrite !lookup_insert. destruct (decide (x = v)); [reflexivity|].
  apply (IH vs s t (conj Hl He)), Hx.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_get_var_imm" *)
Theorem locals_rel_get_var_imm : forall temp (st : state) loc r x,
  every_var_imm (fun x => x <? temp) r /\ get_var_imm r st = SOME x /\
  locals_rel temp (locals st) loc ->
  get_var_imm r (set_locals loc st) = SOME x.
Proof.
  intros temp st loc [r|w] x (He & H & Hl); cbn [get_var_imm every_var_imm] in He, H |- *; [|exact H].
  apply N.ltb_lt in He. apply (locals_rel_get_var temp); repeat split; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_get_var_imm_simp" *)
Theorem locals_rel_get_var_imm_simp : forall temp (st : state) loc r,
  every_var_imm (fun x => x <? temp) r /\ locals_rel temp (locals st) loc ->
  get_var_imm r (set_locals loc st) = get_var_imm r st.
Proof.
  intros temp st loc [r|w] (He & Hl); cbn [get_var_imm every_var_imm] in He |- *; [|reflexivity].
  apply N.ltb_lt in He. apply (locals_rel_get_var_simp temp); split; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_word_exp_simp" *)
Theorem locals_rel_word_exp_simp : forall temp loc (s : state) exp,
  every_var_exp (fun x => x <? temp) exp /\ locals_rel temp (locals s) loc ->
  word_exp (set_locals loc s) exp = word_exp s exp.
Proof.
  intros temp loc s exp [He Hl].
  induction exp as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using exp_nested_ind;
    cbn [word_exp every_var_exp] in He |- *; try reflexivity.
  - apply N.ltb_lt in He; apply (locals_rel_get_var_simp temp); split; assumption.
  - rewrite (IH He); reflexivity.
  - replace (MAP (word_exp (set_locals loc s)) es) with (MAP (word_exp s) es); [reflexivity|].
    induction IH as [|x l Hx Hl' IHl]; cbn in He |- *; [reflexivity|].
    apply andb_prop in He as [He1 He2]. rewrite (Hx He1), (IHl He2); reflexivity.
  - apply andb_prop in He as [He1 He2]. rewrite (IH1 He1), (IH2 He2); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_word_exp" *)
Theorem locals_rel_word_exp : forall temp loc (s : state) exp w,
  every_var_exp (fun x => x <? temp) exp /\ word_exp s exp = SOME w /\
  locals_rel temp (locals s) loc ->
  word_exp (set_locals loc s) exp = SOME w.
Proof.
  intros temp loc s exp w (He & H & Hl); rewrite (locals_rel_word_exp_simp temp) by (split; assumption).
  exact H.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_set_var" *)
Theorem locals_rel_set_var : forall temp (v : word_loc a) n s t,
  locals_rel temp s t -> locals_rel temp (insert n v s) (insert n v t).
Proof.
  intros temp v n s t H x Hx; rewrite !lookup_insert; destruct (decide (x = n)); auto.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_delete" *)
Theorem locals_rel_delete : forall temp n (s t : num_map (word_loc a)),
  locals_rel temp s t -> locals_rel temp (delete n s) (delete n t).
Proof.
  intros temp n s t H x Hx; rewrite !lookup_delete; destruct (decide (x = n)); auto.
Qed.

(** Galette-only: [every_name] gives the bound on every name of the
    cutsets. *)
Local Lemma every_name_lt temp (names : cutsets) x :
  every_name (fun x => x <? temp) names ->
  (domain (FST names) x \/ domain (SND names) x) -> x < temp.
Proof.
  unfold every_name; intros H Hx; apply andb_prop in H as [H1 H2].
  unfold is_true in H1, H2; rewrite EVERY_Forall, Forall_forall in H1, H2.
  destruct Hx as [Hx|Hx]; apply domain_lookup in Hx as [v Hv];
    apply N.ltb_lt; [apply H1|apply H2]; apply in_map_iff; exists (x, v); (split; [reflexivity|]);
    apply MEM_In, MEM_toAList, Hv.
Qed.

Local Lemma locals_rel_cut_names temp (loc loc' : num_map (word_loc a)) (ns : num_set) x :
  locals_rel temp loc loc' -> (forall y, domain ns y -> y < temp) ->
  cut_names ns loc = SOME x -> cut_names ns loc' = SOME x.
Proof.
  intros Hl Hn; unfold cut_names.
  destruct (classical_dec (domain ns SUBSET domain loc)) as [Hs|]; [|discriminate].
  intros H; injection H as <-.
  assert (Hs' : domain ns SUBSET domain loc').
  { intros y Hy; specialize (Hs y Hy); unfold pred_set.IN in *.
    apply domain_lookup in Hs as [v Hv]; apply domain_lookup; exists v.
    rewrite <- Hl by (apply Hn, Hy); exact Hv. }
  destruct (classical_dec (domain ns SUBSET domain loc')) as [_|Hn']; [|contradiction].
  f_equal. apply spt_eq_thm; [split; apply wf_inter|]. intros n; rewrite !lookup_inter.
  destruct (lookup n ns) eqn:E; [|destruct (lookup n loc), (lookup n loc'); reflexivity].
  rewrite Hl; [reflexivity|]. apply Hn, domain_lookup; eexists; exact E.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_cut_envs" *)
Theorem locals_rel_cut_envs : forall temp loc loc' names (x : num_map (word_loc a) * num_map (word_loc a)),
  locals_rel temp loc loc' /\ every_name (fun x => x <? temp) names /\ cut_envs names loc = SOME x ->
  cut_envs names loc' = SOME x.
Proof.
  intros temp loc loc' names x (Hl & Hn & H); unfold cut_envs in *.
  destruct (cut_names (FST names) loc) as [e1|] eqn:E1; [|discriminate].
  destruct (cut_names (SND names) loc) as [e2|] eqn:E2; [|discriminate].
  rewrite (locals_rel_cut_names temp loc loc' _ _ Hl (fun y Hy => every_name_lt temp names y Hn (or_introl Hy)) E1).
  rewrite (locals_rel_cut_names temp loc loc' _ _ Hl (fun y Hy => every_name_lt temp names y Hn (or_intror Hy)) E2).
  exact H.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_cut_env" *)
Theorem locals_rel_cut_env : forall temp loc loc' names (x : num_map (word_loc a)),
  locals_rel temp loc loc' /\ every_name (fun x => x <? temp) names /\ cut_env names loc = SOME x ->
  cut_env names loc' = SOME x.
Proof.
  intros temp loc loc' names x (Hl & Hn & H); unfold cut_env in *.
  destruct (cut_envs names loc) as [[e1 e2]|] eqn:E; [|discriminate].
  rewrite (locals_rel_cut_envs temp loc loc' names (e1, e2) (conj Hl (conj Hn E))); exact H.
Qed.

End LocalsRel.

(** Split the boolean conjunctions of the context into atoms. *)
Local Ltac bool_atoms :=
  unfold is_true in *;
  repeat match goal with
         | H : (_ && _) = true |- _ => apply andb_prop in H as [? ?]
         end.

(** Prove a boolean conjunction of atoms of the context. *)
Local Ltac bool_goal :=
  unfold is_true; cbn [every_var_exp every_var_imm EVERY MAP FST SND fst snd];
  repeat match goal with |- (_ && _) = true => apply andb_true_intro; split end;
  first [ assumption | reflexivity ].

Local Ltac lr_side Hl :=
  bool_atoms;
  repeat match goal with H : (_ <? _) = true |- _ => apply N.ltb_lt in H end;
  split; [|exact Hl];
  first [ assumption | bool_goal | idtac ];
  repeat match goal with H : _ < _ |- _ => apply N.ltb_lt in H end; bool_goal.

Local Ltac lr_rw temp loc st Hl :=
  repeat first
    [ rewrite (locals_rel_word_exp_simp temp loc st) by lr_side Hl
    | rewrite (locals_rel_get_vars_simp temp st loc) by lr_side Hl
    | rewrite (locals_rel_get_var_simp temp st loc) by lr_side Hl
    | rewrite (locals_rel_get_var_imm_simp temp st loc) by lr_side Hl ].

(** ** Galette-only infrastructure for [locals_rel_evaluate_thm] *)

Section LocalsRelInfra.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

Lemma mem_store_set_locals x y l (s : state) :
  mem_store x y (set_locals l s) = OPTION_MAP (set_locals l) (mem_store x y s).
Proof. unfold mem_store; cbn [mdomain set_locals]; destruct (classical_dec _); reflexivity. Qed.

Lemma inst_locals_rel temp i (st st' : state) loc :
  inst i st = SOME st' -> every_var_inst (fun x => x <? temp) i -> locals_rel temp (locals st) loc ->
  exists loc', inst i (set_locals loc st) = SOME (set_locals loc' st') /\ locals_rel temp (locals st') loc'.
Proof.
  intros H Hv Hl.
  destruct i as [|r w|ar|m r [ad w]|f]; [|cbn [inst] in H|destruct ar|destruct m|destruct f];
    cbn [inst every_var_inst] in H, Hv |- *; unfold assign in H |- *;
    try (match goal with ri : reg_imm _ |- _ => destruct ri end);
    cbn [every_var_imm] in Hv;
    lr_rw temp loc st Hl;
    unfold get_fp_var, mem_load in *; cbn [fp_regs memory mdomain be set_locals] in *;
    rewrite ?mem_store_set_locals;
    split_H H; leaf H; try discriminate H;
    do 3 (rw_cases; lr_rw temp loc st Hl; rewrite ?mem_store_set_locals); rw_cases; cbn [OPTION_MAP option_map];
    eexists; (split; [reflexivity|]);
    cbn [locals set_var set_locals set_fp_var set_fp_regs set_memory];
    try (match goal with E : mem_store _ _ _ = SOME _ |- _ => rewrite (proj1 (mem_store_const _ _ _ _ E)) end);
    repeat apply locals_rel_set_var; exact Hl.
Qed.


Lemma set_locals_eta (s : state) : set_locals (locals s) s = s.
Proof. destruct s; reflexivity. Qed.
Lemma locals_set_locals l (s : state) : locals (set_locals l s) = l.
Proof. reflexivity. Qed.
Lemma jump_exc_set_locals l (s : state) : jump_exc (set_locals l s) = jump_exc s.
Proof.
  unfold jump_exc; cbn [handler stack set_locals].
  destruct (_ <? _); [|reflexivity].
  destruct (LASTN _ _) as [|[m e0 e [[n [l1 l2]]|]] xs]; reflexivity.
Qed.
Lemma alloc_set_locals w names l (s : state) envs :
  cut_envs names l = SOME envs -> cut_envs names (locals s) = SOME envs ->
  alloc w names (set_locals l s) = alloc w names s.
Proof.
  intros Hc Hc'; unfold alloc; rewrite locals_set_locals, Hc, Hc'.
  assert (Hp : forall x y (t : state) (e : num_map (word_loc a) * num_map (word_loc a)),
      push_env e NONE (set_store x y (set_locals l t)) = set_locals l (push_env e NONE (set_store x y t)))
    by (intros; unfold push_env; destruct (env_to_list _ _); reflexivity).
  assert (Hg : forall t : state, gc (set_locals l t) = OPTION_MAP (set_locals l) (gc t))
    by (intros t; unfold gc; cbn [stack memory mdomain store gc_fun set_locals];
        destruct (gc_fun _ _) as [[? [? ?]]|]; [destruct (dec_stack _ _)|]; reflexivity).
  rewrite Hp, Hg.
  destruct (gc _) as [s1|]; cbn [OPTION_MAP option_map]; [|reflexivity].
  replace (pop_env (set_locals l s1)) with (pop_env s1)
    by (unfold pop_env; cbn [stack set_locals]; destruct (stack s1) as [|[? ? ? [[? ?]|]] ?]; reflexivity).
  reflexivity.
Qed.

Lemma locals_size_set_locals l (s : state) : locals_size (set_locals l s) = locals_size s. Proof. reflexivity. Qed.
Lemma fp_regs_set_locals l (s : state) : fp_regs (set_locals l s) = fp_regs s. Proof. reflexivity. Qed.
Lemma store_set_locals l (s : state) : store (set_locals l s) = store s. Proof. reflexivity. Qed.
Lemma stack_set_locals l (s : state) : stack (set_locals l s) = stack s. Proof. reflexivity. Qed.
Lemma stack_limit_set_locals l (s : state) : stack_limit (set_locals l s) = stack_limit s. Proof. reflexivity. Qed.
Lemma stack_max_set_locals l (s : state) : stack_max (set_locals l s) = stack_max s. Proof. reflexivity. Qed.
Lemma state_stack_size_set_locals l (s : state) : state_stack_size (set_locals l s) = state_stack_size s. Proof. reflexivity. Qed.
Lemma memory_set_locals l (s : state) : memory (set_locals l s) = memory s. Proof. reflexivity. Qed.
Lemma mdomain_set_locals l (s : state) : mdomain (set_locals l s) = mdomain s. Proof. reflexivity. Qed.
Lemma sh_mdomain_set_locals l (s : state) : sh_mdomain (set_locals l s) = sh_mdomain s. Proof. reflexivity. Qed.
Lemma permute_set_locals l (s : state) : permute (set_locals l s) = permute s. Proof. reflexivity. Qed.
Lemma compile_set_locals l (s : state) : compile (set_locals l s) = compile s. Proof. reflexivity. Qed.
Lemma compile_oracle_set_locals l (s : state) : compile_oracle (set_locals l s) = compile_oracle s. Proof. reflexivity. Qed.
Lemma code_buffer_set_locals l (s : state) : code_buffer (set_locals l s) = code_buffer s. Proof. reflexivity. Qed.
Lemma data_buffer_set_locals l (s : state) : data_buffer (set_locals l s) = data_buffer s. Proof. reflexivity. Qed.
Lemma gc_fun_set_locals l (s : state) : gc_fun (set_locals l s) = gc_fun s. Proof. reflexivity. Qed.
Lemma handler_set_locals l (s : state) : handler (set_locals l s) = handler s. Proof. reflexivity. Qed.
Lemma clock_set_locals l (s : state) : clock (set_locals l s) = clock s. Proof. reflexivity. Qed.
Lemma termdep_set_locals l (s : state) : termdep (set_locals l s) = termdep s. Proof. reflexivity. Qed.
Lemma code_set_locals l (s : state) : code (set_locals l s) = code s. Proof. reflexivity. Qed.
Lemma be_set_locals l (s : state) : be (set_locals l s) = be s. Proof. reflexivity. Qed.
Lemma ffi_set_locals l (s : state) : ffi (set_locals l s) = ffi s. Proof. reflexivity. Qed.
Lemma get_store_set_locals v l (s : state) : get_store v (set_locals l s) = get_store v s. Proof. reflexivity. Qed.
Lemma mem_load_set_locals v l (s : state) : mem_load v (set_locals l s) = mem_load v s. Proof. reflexivity. Qed.
Lemma get_fp_var_set_locals v l (s : state) : get_fp_var v (set_locals l s) = get_fp_var v s. Proof. reflexivity. Qed.
Lemma flush_state_set_locals b l (s : state) : flush_state b (set_locals l s) = flush_state b s. Proof. destruct b; reflexivity. Qed.
Lemma dec_clock_set_locals l (s : state) : dec_clock (set_locals l s) = set_locals l (dec_clock s). Proof. reflexivity. Qed.
Lemma sh_mem_load_set_locals v l (s : state) : sh_mem_load v (set_locals l s) = sh_mem_load v s. Proof. reflexivity. Qed.
Lemma sh_mem_load_byte_set_locals v l (s : state) : sh_mem_load_byte v (set_locals l s) = sh_mem_load_byte v s. Proof. reflexivity. Qed.
Lemma sh_mem_load16_set_locals v l (s : state) : sh_mem_load16 v (set_locals l s) = sh_mem_load16 v s. Proof. reflexivity. Qed.
Lemma sh_mem_load32_set_locals v l (s : state) : sh_mem_load32 v (set_locals l s) = sh_mem_load32 v s. Proof. reflexivity. Qed.
Lemma call_env_set_locals x ss l (s : state) : call_env x ss (set_locals l s) = call_env x ss s. Proof. reflexivity. Qed.
Lemma push_env_set_locals x y l (s : state) : push_env x y (set_locals l s) = set_locals l (push_env x y s).
Proof. destruct y as [[? [? [? ?]]]|]; unfold push_env; destruct (env_to_list _ _); reflexivity. Qed.
Lemma has_space_set_locals v l (s : state) : has_space v (set_locals l s) = has_space v s. Proof. reflexivity. Qed.

End LocalsRelInfra.
Create Rewrite HintDb lrl.
Global Hint Rewrite @locals_size_set_locals @fp_regs_set_locals @store_set_locals @stack_set_locals @stack_limit_set_locals @stack_max_set_locals @state_stack_size_set_locals @memory_set_locals @mdomain_set_locals @sh_mdomain_set_locals @permute_set_locals @compile_set_locals @compile_oracle_set_locals @code_buffer_set_locals @data_buffer_set_locals @gc_fun_set_locals @handler_set_locals @clock_set_locals @termdep_set_locals @code_set_locals @be_set_locals @ffi_set_locals @get_store_set_locals @mem_load_set_locals @get_fp_var_set_locals @flush_state_set_locals @dec_clock_set_locals @sh_mem_load_set_locals @sh_mem_load_byte_set_locals @sh_mem_load16_set_locals @sh_mem_load32_set_locals @has_space_set_locals @call_env_set_locals @push_env_set_locals @locals_set_locals @jump_exc_set_locals @mem_store_set_locals : lrl.
Section LocalsRelEval.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

Local Ltac lr_cut temp loc st Hl :=
  repeat match goal with
  | E : cut_env ?n (locals st) = SOME ?e |- context [cut_env ?n loc] =>
      let Hn := fresh in assert (Hn : is_true (every_name (fun x => x <? temp) n)) by bool_goal;
      rewrite (locals_rel_cut_env temp (locals st) loc n e (conj Hl (conj Hn E))); clear Hn
  | E : cut_envs ?n (locals st) = SOME ?e |- context [cut_envs ?n loc] =>
      let Hn := fresh in assert (Hn : is_true (every_name (fun x => x <? temp) n)) by bool_goal;
      rewrite (locals_rel_cut_envs temp (locals st) loc n e (conj Hl (conj Hn E))); clear Hn
  end.

Local Ltac lr_atoms :=
  rewrite ?fix_clock_evaluate in *;
  repeat match goal with E : ?v = _ |- _ => is_var v; subst v end;
  repeat match goal with H : (match _ with _ => _ end) = true |- _ => progress (cbn beta iota zeta in H) end;
  bool_atoms.

Local Ltac lr_norm temp loc st Hl :=
  repeat progress (lr_rw temp loc st Hl; autorewrite with lrl; lr_cut temp loc st Hl; rw_cases;
                   rewrite ?fix_clock_evaluate;
                   repeat match goal with E : evaluate ?x = _ |- context [evaluate ?x] => rewrite E end;
                   cbn beta iota zeta;
                   cbn [OPTION_MAP option_map]).

Local Ltac lr_close_rel :=
  cbn [locals set_var set_vars unset_var set_locals set_fp_var set_fp_regs set_memory set_store
       set_store_field set_code_buffer set_data_buffer set_ffi dec_clock set_clock];
  try (match goal with E : mem_store _ _ _ = SOME _ |- _ => rewrite (proj1 (mem_store_const _ _ _ _ E)) end);
  repeat first [ apply locals_rel_set_var | apply locals_rel_delete
               | apply locals_rel_alist_insert; split; [|bool_goal] ];
  assumption.

Local Ltac lr_match_refl :=
  match goal with
  | |- match ?r with _ => _ end => destruct r as [[]|]; try reflexivity; intros ? ?; reflexivity
  | _ => try reflexivity; intros ? ?; reflexivity
  end.

Local Ltac lr_close :=
  first [ eexists; split; [reflexivity|lr_close_rel]
        | eexists; split; [reflexivity|lr_match_refl]
        | match goal with |- exists l, (_, _) = (_, set_locals l ?S) /\ _ =>
            exists (locals S); rewrite set_locals_eta; split; [reflexivity|lr_match_refl] end ].

Lemma share_inst_locals_rel temp op v ad (st st' : state) loc r :
  share_inst op v ad st = (r, st') -> r <> SOME Error -> v < temp -> locals_rel temp (locals st) loc ->
  exists loc', share_inst op v ad (set_locals loc st) = (r, set_locals loc' st') /\
    match r with
    | NONE => locals_rel temp (locals st') loc'
    | SOME (Break _) => locals_rel temp (locals st') loc'
    | SOME (Continue _) => locals_rel temp (locals st') loc'
    | SOME _ => locals st' = loc'
    end.
Proof.
  intros H Hr Hv Hl.
  destruct op; cbn [share_inst] in H |- *;
    unfold sh_mem_set_var, sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32 in H |- *;
    rewrite ?(locals_rel_get_var_simp temp st loc v (conj Hv Hl)); autorewrite with lrl;
    split_H H; leaf H; try (exfalso; apply Hr; reflexivity); rw_cases; lr_close.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_evaluate_thm" *)
Theorem locals_rel_evaluate_thm : forall (prog : prog a) (st : state) res rst loc temp,
  evaluate (prog, st) = (res, rst) /\ res <> SOME Error /\
  every_var (fun x => x <? temp) prog /\ locals_rel temp (locals st) loc ->
  exists loc',
    evaluate (prog, set_locals loc st) = (res, set_locals loc' rst) /\
    match res with
    | NONE => locals_rel temp (locals rst) loc'
    | SOME (Break _) => locals_rel temp (locals rst) loc'
    | SOME (Continue _) => locals_rel temp (locals rst) loc'
    | SOME _ => locals rst = loc'
    end.
Proof.
  intros prog.
  induction prog as [| | | | | | |p IHp|ret dest args h Hr Hh|p1 p2 IHp1 IHp2|cmp r ri p1 p2 IHp1 IHp2
                 |n1 p n2 IHp| | | | | | | | | | | | | |] using prog_nested_ind;
    intros st res rst loc temp (H & Hr0 & Hv & Hl);
    rewrite evaluate_eqn in H |- *; cbn [evaluate_body every_var] in H, Hv |- *; bool_atoms.
  all: try (lr_norm temp loc st Hl;
       rewrite ?fix_clock_evaluate in H;
       split_H H; leaf H; try (exfalso; apply Hr0; reflexivity); lr_atoms;
       lr_norm temp loc st Hl;
       first [ eexists; split; [reflexivity|lr_close_rel]
             | eexists; split; [reflexivity|lr_match_refl]
             | match goal with |- exists l, (_, _) = (_, set_locals l ?S) /\ _ =>
                 exists (locals S); rewrite set_locals_eta; split; [reflexivity|lr_match_refl] end ]).
  - (* Inst *)
    destruct (inst i st) as [s1|] eqn:E; injection H as <- <-; [|exfalso; apply Hr0; reflexivity].
    destruct (inst_locals_rel temp i st s1 loc E) as [l1 [Hi Hm]]; [assumption|exact Hl|].
    rewrite Hi; exists l1; split; [reflexivity|exact Hm].
  - (* MustTerminate *)
    autorewrite with lrl.
    destruct (termdep st =? 0) eqn:Et; [injection H as <- _; exfalso; apply Hr0; reflexivity|].
    destruct (evaluate (p, set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) st)))
      as [r1 s1] eqn:E1.
    destruct (bool_decide (r1 = SOME TimeOut)) eqn:Eb; [injection H as <- _; exfalso; apply Hr0; reflexivity|].
    injection H as <- <-.
    destruct (IHp (set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) st)) r1 s1 loc temp)
      as [l1 [He Hm]]; [repeat split; assumption|].
    change (set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) (set_locals loc st)))
      with (set_locals loc (set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) st))).
    rewrite He; cbn beta iota zeta; rewrite Eb; exists l1; split; [reflexivity|exact Hm].
  - (* Seq *)
    rewrite fix_clock_evaluate in H |- *.
    destruct (evaluate (p1, st)) as [r1 s1] eqn:E1.
    assert (Hr1 : r1 <> SOME Error)
      by (destruct (bool_decide (r1 = NONE)) eqn:Eb;
          [apply bool_decide_spec in Eb; subst r1; discriminate|injection H as <- _; exact Hr0]).
    destruct (IHp1 st r1 s1 loc temp) as [l1 [He1 Hm1]]; [repeat split; assumption|].
    rewrite He1; cbn beta iota zeta.
    destruct (bool_decide (r1 = NONE)) eqn:Eb.
    + apply bool_decide_spec in Eb; subst r1.
      apply (IHp2 s1 res rst l1 temp); repeat split; assumption.
    + injection H as <- <-; exists l1; split; [reflexivity|exact Hm1].
  - (* If *)
    lr_norm temp loc st Hl.
    split_H H; try (injection H as <- _; exfalso; apply Hr0; reflexivity); lr_atoms; lr_norm temp loc st Hl;
      [apply (IHp1 st) | apply (IHp2 st)]; repeat split; assumption.
  - (* Loop *)
    destruct (cut_state (n1, LN) st) as [s|] eqn:Ec; [|injection H as <- _; exfalso; apply Hr0; reflexivity].
    assert (Ec' : cut_state (n1, LN) (set_locals loc st) = SOME s).
    { unfold cut_state in *; rewrite locals_set_locals.
      destruct (cut_env (n1, LN) (locals st)) as [env|] eqn:Ee; [|discriminate].
      injection Ec as <-.
      assert (Hn : is_true (every_name (fun x => x <? temp) (n1, LN)))
        by (unfold every_name; cbn [FST SND fst snd]; unfold is_true;
            apply andb_true_intro; split; [assumption|reflexivity]).
      rewrite (locals_rel_cut_env temp (locals st) loc (n1, LN) env (conj Hl (conj Hn Ee))).
      reflexivity. }
    rewrite Ec'. rewrite H. exists (locals rst); rewrite set_locals_eta; split; [reflexivity|lr_match_refl].
  - (* Alloc *)
    lr_norm temp loc st Hl.
    split_H H; try (injection H as <- _; exfalso; apply Hr0; reflexivity); lr_norm temp loc st Hl.
    destruct (cut_envs names (locals st)) as [envs|] eqn:Ec.
    2:{ exfalso; unfold alloc in H; rewrite Ec in H; injection H as <- _; apply Hr0; reflexivity. }
    assert (Hn : is_true (every_name (fun x => x <? temp) names)) by bool_goal.
    rewrite (alloc_set_locals _ names loc st envs
               (locals_rel_cut_envs temp (locals st) loc names envs (conj Hl (conj Hn Ec))) Ec).
    rewrite H. exists (locals rst); rewrite set_locals_eta; split; [reflexivity|lr_match_refl].
  - (* ShareInst *)
    lr_norm temp loc st Hl.
    destruct (word_exp st e) as [[ad|]|] eqn:E; try (injection H as <- _; exfalso; apply Hr0; reflexivity).
    apply (share_inst_locals_rel temp op v ad st rst loc res H Hr0); [apply N.ltb_lt; assumption|exact Hl].
Qed.
End LocalsRelEval.
