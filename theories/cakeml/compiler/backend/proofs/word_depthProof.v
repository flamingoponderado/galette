(** * CakeML [word_depthProof]: the call-graph bound on stack depth

    A port of [cakeml/compiler/backend/proofs/word_depthProofScript.sml]:
    [max_depth] applied to the call graph produced by
    [word_depth$call_graph] bounds the [stack_max] reached by [evaluate].

    Notes:
    - HOL's [$+] on [num option]s is [N.add] under [OPTION_MAP2]; HOL's
      [s.stack_size] is [state_stack_size s].
    - [option_le] is boolean ([backendProps.v]).
    - HOL's free variables ([ss], [xs], [code], ...) are quantified
      explicitly.
    - [max_depth_call_graph_lemma] is proved by well-founded induction on
      [eval_lt] (HOL: [recInduct evaluate_ind]); [option_le_max_depth_graph]
      by induction on [size funs], the call depth and the program (HOL:
      [recInduct call_graph_ind]). *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang wordLang word_depth.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem wordConvs backendProps.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import
  consts clock consts_with dec_clock code stack_swap stack_max.
Open Scope N_scope.

Lemma MEM_iff_d {A} `{EqDecision A} (x : A) l : is_true (MEM x l) <-> In x l.
Proof. unfold is_true; apply MEM_In. Qed.

Ltac onum_destr t :=
  lazymatch t with
  | Some _ => fail | None => fail
  | (if _ then _ else _) => fail
  | match _ with _ => _ end => fail
  | _ => destruct t
  end.

Ltac onum :=
  unfold is_true, option_le, OPTION_MAP2, OPTION_MAP in *;
  repeat first
    [ progress cbn [IS_SOME THE andb option_map] in *
    | match goal with
      | |- context [IS_SOME ?t] => onum_destr t
      | H : context [IS_SOME ?t] |- _ => onum_destr t
      | |- context [match ?t with Some _ => _ | None => _ end] => onum_destr t
      | H : context [match ?t with Some _ => _ | None => _ end] |- _ => onum_destr t
      end ];
  repeat rewrite N.leb_le in *; rewrite ?MAX_max in *;
  intuition (try discriminate; try lia; try (f_equal; lia)).

(*! HOL "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "option_le_X_MAX_X" *)
Theorem option_le_X_MAX_X : forall x m,
  option_le x (OPTION_MAP2 MAX m x) /\ option_le x (OPTION_MAP2 MAX x m).
Proof. intros x m; split; onum. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "OPTION_MAP2_MAX_IDEMPOT" *)
Theorem OPTION_MAP2_MAX_IDEMPOT : forall (x : option N), OPTION_MAP2 MAX x x = x.
Proof. intros [x|]; unfold OPTION_MAP2; cbn; [rewrite MAX_max; f_equal; lia|reflexivity]. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "OPTION_MAP2_SOME_0" *)
Theorem OPTION_MAP2_SOME_0 : forall (x : option N),
  OPTION_MAP2 N.add x (SOME 0) = x /\ OPTION_MAP2 MAX x (SOME 0) = x.
Proof. intros [x|]; unfold OPTION_MAP2; cbn; rewrite ?MAX_max; split; try reflexivity; f_equal; lia. Qed.

Section Depth.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "max_depth_mk_Branch" *)
Theorem max_depth_mk_Branch : forall s t1 t2, max_depth s (mk_Branch t1 t2) = max_depth s (Branch t1 t2).
Proof.
  intros s t1 t2. unfold mk_Branch. cbn [max_depth].
  destruct (decide (t1 = t2)) as [->|]; [rewrite OPTION_MAP2_MAX_IDEMPOT; reflexivity|].
  destruct (decide (t1 = Leaf)) as [->|]; [cbn [max_depth]; destruct (max_depth s t2); unfold OPTION_MAP2; cbn; rewrite ?MAX_max; [f_equal; lia|reflexivity]|].
  destruct (decide (t2 = Leaf)) as [->|]; [cbn [max_depth]; rewrite (proj2 (OPTION_MAP2_SOME_0 _)); reflexivity|].
  destruct (decide (t1 = Unknown)) as [->|]; [reflexivity|].
  destruct (decide (t2 = Unknown)) as [->|]; [cbn [max_depth]; destruct (max_depth s t1); reflexivity|].
  reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "MEM_max_depth_graphs" *)
Theorem MEM_max_depth_graphs : forall (ss : num_map N) xs (funs code : num_map (N * prog a)) ns name y,
  MEM name ns /\ lookup name code = SOME y ->
  option_le (max_depth_graphs ss [name] xs funs code) (max_depth_graphs ss ns xs funs code).
Proof.
  intros ss xs funs code ns; induction ns as [|h ns IH]; intros name y [Hm Hl]; [discriminate Hm|].
  cbn [max_depth_graphs] in *. rewrite Hl. destruct y as [y0 y1].
  rewrite MEM_iff_d in Hm. destruct Hm as [<-|Hm].
  - rewrite Hl. onum.
  - specialize (IH name (y0, y1) (conj (proj2 (MEM_iff_d _ _) Hm) Hl)). cbn [max_depth_graphs] in IH. rewrite Hl in IH.
    destruct (lookup h code) as [[z0 z1]|]; [|onum]. revert IH. onum.
Qed.

Lemma option_le_MAX_mono x1 x2 y1 y2 :
  option_le x1 x2 -> option_le y1 y2 -> option_le (OPTION_MAP2 MAX x1 y1) (OPTION_MAP2 MAX x2 y2).
Proof. onum. Qed.

Lemma option_le_add_mono x1 x2 y1 y2 :
  option_le x1 x2 -> option_le y1 y2 -> option_le (OPTION_MAP2 N.add x1 y1) (OPTION_MAP2 N.add x2 y2).
Proof. onum. Qed.

Lemma option_le_OPTION_MAP_mono k x1 x2 :
  option_le x1 x2 -> option_le (OPTION_MAP (N.add k) x1) (OPTION_MAP (N.add k) x2).
Proof. onum. Qed.

Lemma option_le_SOME_0' x : option_le (SOME 0) x.
Proof. onum. Qed.

Lemma option_le_refl' x : option_le x x.
Proof. onum. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "option_le_max_depth_graph" *)
Theorem option_le_max_depth_graph : forall (ss : num_map N) (funs : num_map (N * prog a)) h ns1 t x1 ns2,
  set ns2 SUBSET set ns1 /\ LENGTH ns2 <= LENGTH ns1 ->
  option_le (max_depth ss (call_graph funs h ns1 t x1)) (max_depth ss (call_graph funs h ns2 t x1)).
Proof.
  intros ss funs h ns1 t x1 ns2 Hns.
  remember (N.to_nat (t - LENGTH ns2)) as k eqn:Hk. revert h ns1 ns2 x1 Hk Hns.
  induction k as [k IHk] using (well_founded_induction lt_wf). intros h ns1 ns2 x1 Hk Hns.
  revert h. induction x1 as [| | | | | | |p IH|ret dest args hd IHr IHh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2
                     |n1 p n2 IH| | | | | | | | | | | | | |] using prog_nested_ind; intros h;
    destruct (@call_graph_eqns a) as (Eseq & Eif & Ecall & Emt & Ealloc & Einst & Eloop & Eother);
    try (match goal with |- is_true (option_le (max_depth _ (call_graph _ _ _ _ ?P)) _) =>
           rewrite (Eother funs h ns1 t P : call_graph funs h ns1 t P = Leaf),
                   (Eother funs h ns2 t P : call_graph funs h ns2 t P = Leaf) end; apply option_le_refl'; fail).
  all: try (rewrite !Einst; apply option_le_refl').
  all: try (rewrite !Ealloc; apply option_le_refl').
  (* MustTerminate *)
  - rewrite !Emt. apply IH.
  (* Call *)
  - rewrite !Ecall. destruct dest as [d|]; [|apply option_le_refl'].
    destruct (MEM d ns1 && match ret with None => true | Some _ => false end) eqn:E1;
      [cbn [max_depth]; apply option_le_SOME_0'|].
    assert (E2 : (MEM d ns2 && match ret with None => true | Some _ => false end) = false).
    { destruct ret; [rewrite Bool.andb_false_r; reflexivity|]. rewrite Bool.andb_true_r in *.
      destruct (MEM d ns2) eqn:Em; [|reflexivity]. exfalso. destruct Hns as [Hs _].
      apply MEM_iff_d in Em. assert (Hd : d IN set ns1) by (apply Hs, IN_set, Em).
      apply IN_set, MEM_iff_d in Hd. rewrite Hd in E1. discriminate. }
    rewrite E2. destruct (lookup d funs) as [[x body]|]; [|apply option_le_refl'].
    destruct ret as [[rv [cs [rp [l1 l2]]]]|].
    + cbv zeta. destruct hd as [[hv [hp [l1' l2']]]|]; repeat (rewrite ?max_depth_mk_Branch; cbn [max_depth]).
      * apply option_le_MAX_mono; [apply option_le_refl'|]. apply option_le_MAX_mono; [apply option_le_refl'|].
        apply option_le_MAX_mono; [apply IHh|apply IHr].
      * apply option_le_MAX_mono; [apply option_le_refl'|]. apply option_le_MAX_mono; [apply option_le_refl'|apply IHr].
    + destruct (LENGTH ns1 <? t) eqn:Elt1; [|cbn [max_depth]; apply option_le_SOME_0'].
      destruct Hns as [Hs Hl].
      assert (Elt2 : (LENGTH ns2 <? t) = true) by (apply N.ltb_lt; apply N.ltb_lt in Elt1; lia).
      rewrite Elt2, !max_depth_mk_Branch. cbn [max_depth]. apply option_le_MAX_mono; [apply option_le_refl'|].
      apply (IHk (N.to_nat (t - LENGTH (d :: ns2)))).
      * cbn [LENGTH]. apply N.ltb_lt in Elt2. lia.
      * reflexivity.
      * split; [|cbn [LENGTH]; lia]. intros z [Hz|Hz]; [left; exact Hz|right; apply Hs, Hz].
  (* Seq *)
  - rewrite !Eseq, !max_depth_mk_Branch. cbn [max_depth]. apply option_le_MAX_mono; [apply IH1|apply IH2].
  (* If *)
  - rewrite !Eif, !max_depth_mk_Branch. cbn [max_depth]. apply option_le_MAX_mono; [apply IH1|apply IH2].
  (* Loop *)
  - rewrite !Eloop. apply IH.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "option_le_max_depth_graphs" *)
Theorem option_le_max_depth_graphs : forall (ss : num_map N) (funs funs2 : num_map (N * prog a)) ns ns1 ns2,
  set ns2 SUBSET set ns1 /\ LENGTH ns2 <= LENGTH ns1 ->
  option_le (max_depth_graphs ss ns ns1 funs funs2) (max_depth_graphs ss ns ns2 funs funs2).
Proof.
  intros ss funs funs2 ns; induction ns as [|h ns IH]; intros ns1 ns2 Hns; cbn [max_depth_graphs];
    [apply option_le_refl'|].
  destruct (lookup h funs2) as [[x body]|]; [|apply option_le_refl'].
  apply option_le_MAX_mono; [apply option_le_refl'|]. apply option_le_MAX_mono.
  - apply option_le_max_depth_graph, Hns.
  - apply IH, Hns.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "LENGTH_LESS_size" *)
Theorem LENGTH_LESS_size : forall name ns (funs : num_map (N * prog a)) y,
  ~ MEM name ns /\ set ns SUBSET domain funs /\ ALL_DISTINCT ns /\ lookup name funs = SOME y ->
  LENGTH ns < size funs.
Proof.
  intros name ns funs y (Hm & Hs & Hd & Hl). rewrite <- LENGTH_toAList.
  set (K := MAP fst (toAList funs)).
  assert (HK : forall x, In x K <-> domain funs x).
  { intros x. pose proof (f_equal (fun P => P x) (set_MAP_FST_toAList_domain funs)) as E. cbv beta in E.
    rewrite <- E. unfold K. symmetry. apply MEM_iff_d. }
  assert (Hnd : NoDup (name :: ns)).
  { constructor; [rewrite <- MEM_iff_d; exact Hm|apply ALL_DISTINCT_NoDup, Hd]. }
  assert (Hinc : incl (name :: ns) K).
  { intros x [<-|Hx]; apply HK; [apply domain_lookup; eauto|apply Hs, IN_set, Hx]. }
  pose proof (NoDup_incl_length Hnd Hinc) as Hle. unfold K in Hle.
  rewrite !LENGTH_length. rewrite length_map in Hle. cbn [length] in Hle. lia.
Qed.

Section Main.
Context {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

Definition dbound (s : state) funs n ns funs2 (p : prog a) : option N :=
  OPTION_MAP2 MAX (stack_max s)
    (OPTION_MAP2 N.add (stack_size (stack s))
      (OPTION_MAP2 MAX (max_depth_graphs (state_stack_size s) ns ns funs funs2)
        (max_depth (state_stack_size s) (call_graph funs n ns (size funs2) p)))).

Definition dgoal (p : prog a) (s : state) (res : option (result a)) (s1 : state) funs n ns funs2 : Prop :=
  option_le (stack_max s1) (dbound s funs n ns funs2 p) /\
  (max_depth_graphs (state_stack_size s) ns ns funs funs2 <> NONE /\
   max_depth (state_stack_size s) (call_graph funs n ns (size funs2) p) <> NONE ->
   state_stack_size s1 = state_stack_size s /\
   ((res = NONE \/ (exists k, res = SOME (Break k)) \/ (exists k, res = SOME (Continue k))) ->
    locals_size s1 = locals_size s)).

Definition dhyp (s : state) (res : option (result a)) funs n ns funs2 : Prop :=
  subspt funs funs2 /\ subspt funs2 (code s) /\
  locals_size s = lookup n (state_stack_size s) /\ res <> SOME Error /\
  MEM n ns /\ ALL_DISTINCT ns /\ set ns SUBSET domain funs2.

Lemma dgoal_triv p (s s1 : state) res funs n ns funs2 :
  stack_max s1 = stack_max s -> state_stack_size s1 = state_stack_size s ->
  ((res = NONE \/ (exists k, res = SOME (Break k)) \/ (exists k, res = SOME (Continue k))) ->
    locals_size s1 = locals_size s) ->
  dgoal p s res s1 funs n ns funs2.
Proof.
  intros H1 H2 H3. split; [rewrite H1; unfold dbound; apply option_le_X_MAX_X|auto].
Qed.

Lemma res_nbc_none : forall (r : result a), ~ (SOME r = NONE \/ (exists k, SOME r = SOME (Break k)) \/ (exists k, SOME r = SOME (Continue k))) ->
  True.
Proof. auto. Qed.

Ltac nbc := let H := fresh in intros H; destruct H as [H|[[? H]|[? H]]]; discriminate H.

Ltac proj_simp :=
  unfold set_var, set_vars, unset_var, set_store, flush_state, dec_clock, set_fp_var in *;
  cbn [stack_max state_stack_size locals_size set_locals set_locals_size set_store_field set_stack
       set_memory set_fp_regs set_clock set_termdep set_ffi set_code_buffer set_data_buffer set_handler
       set_stack_max set_stack_size set_compile_oracle set_code set_permute] in *.

Ltac simple_case Hev Hres :=
  repeat match type of Hev with
         | context [match ?x with _ => _ end] =>
             lazymatch x with
             | context [match _ with _ => _ end] => fail
             | _ => let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in Hev
             end
         end;
  first [ (injection Hev as <- _; exfalso; apply Hres; reflexivity)
        | (injection Hev as <- <-; apply dgoal_triv;
           repeat match goal with
                  | E : inst _ _ = SOME _ |- _ => apply inst_const_full in E; destr_conj
                  | E : mem_store _ _ _ = SOME _ |- _ => apply mem_store_const in E; destr_conj
                  | E : jump_exc _ = SOME (_, _) |- _ => apply jump_exc_const in E; destr_conj
                  end;
           proj_simp; try congruence; try nbc; try reflexivity) ].

Definition hsz (h : option (N * (prog a * (N * N)))) : N :=
  match h with NONE => 0 | SOME _ => 3 end.

Lemma ce_pe args1 ss envs (h : option (N * (prog a * (N * N)))) (s : state) :
  code (call_env args1 ss (push_env envs h s)) = code s /\
  state_stack_size (call_env args1 ss (push_env envs h s)) = state_stack_size s /\
  locals_size (call_env args1 ss (push_env envs h s)) = ss /\
  clock (call_env args1 ss (push_env envs h s)) = clock s /\
  termdep (call_env args1 ss (push_env envs h s)) = termdep s /\
  (exists l, stack (call_env args1 ss (push_env envs h s)) =
     StackFrame (locals_size s) (toAList (FST envs)) l
       (match h with NONE => NONE | SOME (_, (_, (l1, l2))) => SOME (handler s, (l1, l2)) end) :: stack s) /\
  handler (call_env args1 ss (push_env envs h s)) =
    (match h with NONE => handler s | SOME _ => LENGTH (stack s) end) /\
  stack_size (stack (call_env args1 ss (push_env envs h s))) =
    OPTION_MAP2 N.add (OPTION_MAP (N.add (hsz h)) (locals_size s)) (stack_size (stack s)) /\
  stack_max (call_env args1 ss (push_env envs h s)) =
    OPTION_MAP2 MAX (OPTION_MAP2 MAX (stack_max s) (stack_size (stack (call_env args1 ss (push_env envs h s)))))
      (OPTION_MAP2 N.add (stack_size (stack (call_env args1 ss (push_env envs h s)))) ss).
Proof.
  destruct h as [[w [hp [l1 l2]]]|]; unfold call_env, push_env; destruct (env_to_list _ _) as [l perm];
    cbn [code state_stack_size locals_size clock termdep stack handler stack_max set_stack_max
         set_locals_size set_locals set_permute set_stack set_handler];
    (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity|]);
    (split; [reflexivity|]); (split; [eexists; reflexivity|]); (split; [reflexivity|]);
    (split; [|reflexivity]); unfold stack_size; cbn [FOLDR stack_size_frame hsz];
    cbn; destruct (locals_size s); reflexivity || (cbn; f_equal; lia).
Qed.

Lemma pop_key (st : list (stack_frame a)) m e0 e o (s2 s3 : state) :
  s_key_eq (StackFrame m e0 e o :: st) (stack s2) -> pop_env s2 = SOME s3 ->
  locals_size s3 = m /\ stack_size (stack s3) = stack_size st.
Proof.
  intros K P. unfold pop_env in P. destruct (stack s2) as [|[m' e0' e' o'] xs]; [contradiction|].
  cbn [s_key_eq] in K. destruct K as [K Fr]. apply s_key_eq_stack_size in K.
  apply s_frame_key_eq_def2 in Fr. destruct Fr as (_ & <- & _ & <-).
  destruct o as [[? ?]|]; injection P as <-; cbn; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "max_depth_call_graph_lemma" *)
Theorem max_depth_call_graph_lemma : forall (prog : prog a) (s : state) res s1 funs n ns funs2,
  evaluate (prog, s) = (res, s1) /\
  subspt funs funs2 /\ subspt funs2 (code s) /\
  locals_size s = lookup n (state_stack_size s) /\ res <> SOME Error /\
  MEM n ns /\ ALL_DISTINCT ns /\ set ns SUBSET domain funs2 ->
  option_le (stack_max s1)
    (OPTION_MAP2 MAX (stack_max s)
      (OPTION_MAP2 N.add (stack_size (stack s))
        (OPTION_MAP2 MAX
          (max_depth_graphs (state_stack_size s) ns ns funs funs2)
          (max_depth (state_stack_size s) (call_graph funs n ns (size funs2) prog))))) /\
  (max_depth_graphs (state_stack_size s) ns ns funs funs2 <> NONE /\
   max_depth (state_stack_size s) (call_graph funs n ns (size funs2) prog) <> NONE ->
   state_stack_size s1 = state_stack_size s /\
   ((res = NONE \/ (exists k, res = SOME (Break k)) \/ (exists k, res = SOME (Continue k))) ->
    locals_size s1 = locals_size s)).
Proof.
  enough (G : forall x : prog a * state, forall res s1 funs n ns funs2,
            evaluate x = (res, s1) -> dhyp (snd x) res funs n ns funs2 ->
            dgoal (fst x) (snd x) res s1 funs n ns funs2)
    by (intros prog s res s1 funs n ns funs2 (E & H1 & H2 & H3 & H4 & H5 & H6 & H7);
        exact (G (prog, s) res s1 funs n ns funs2 E (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 H7)))))))).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros res s1 funs n ns funs2 Hev Hh. cbn [fst snd] in *.
  pose proof Hh as (Hsub1 & Hsub2 & Hls & Hres & Hmn & Hdn & Hns).
  destruct (@call_graph_eqns a) as (Eseq & Eif & Ecall & Emt & Ealloc & Einst & Eloop & Eother).
  destruct p; rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  all: try (simple_case Hev Hres; fail).
  (* MustTerminate *)
  - destruct (termdep s =? 0) eqn:Et; [injection Hev as <- _; contradiction|].
    set (s' := set_termdep (termdep s - 1) (set_clock (MustTerminate_limit a) s)) in Hev.
    destruct (evaluate (p, s')) as [r1 t1] eqn:E1.
    destruct (⌜r1 = SOME TimeOut⌝); [injection Hev as <- _; contradiction|]. injection Hev as <- <-.
    assert (Hlt : eval_lt (p, s') (MustTerminate p, s))
      by (unfold eval_lt; cbn [fst snd]; left; unfold s'; cbn; apply N.eqb_neq in Et; lia).
    destruct (IH (p, s') Hlt r1 t1 funs n ns funs2 E1) as [HA HB].
    { split; [exact Hsub1|split; [exact Hsub2|split; [exact Hls|split; [exact Hres|auto]]]]. }
    unfold dgoal, dbound in *. rewrite Emt. cbn [fst snd] in *. unfold s' in *; cbn in HA, HB |- *.
    split; [exact HA|exact HB].
  (* Call *)
  - destruct (get_vars l s) as [xs|] eqn:Egv; [|injection Hev as <- _; contradiction].
    destruct (bad_dest_args o0 l); [injection Hev as <- _; contradiction|].
    destruct o0 as [d|]; [|unfold dgoal, dbound; rewrite Ecall; cbn [max_depth]; split; [onum|intros [_ H]; onum]].
    destruct (find_code (SOME d) (add_ret_loc o xs) (code s) (state_stack_size s)) as [[args1 [prog0 ss]]|] eqn:Efc;
      [|injection Hev as <- _; contradiction].
    assert (Hfc : exists ar, lookup d (code s) = SOME (ar, prog0) /\ ss = lookup d (state_stack_size s)).
    { unfold find_code in Efc. destruct (lookup d (code s)) as [[ar body]|]; [|discriminate].
      destruct (_ =? _); [|discriminate]. injection Efc as _ <- <-. eauto. }
    destruct Hfc as [ar [Hcd ->]].
    assert (Hfd : forall a0 body, lookup d funs = SOME (a0, body) ->
              lookup d funs2 = SOME (a0, body) /\ body = prog0 /\ a0 = ar).
    { intros a0 body E. pose proof (proj1 (subspt_lookup _ _) Hsub1 _ _ E) as E2. split; [exact E2|].
      pose proof (proj1 (subspt_lookup _ _) Hsub2 _ _ E2) as E3. rewrite Hcd in E3. injection E3 as -> ->. auto. }
    unfold dgoal, dbound. rewrite Ecall.
    destruct o as [[n' [names [ret_handler [l1 l2]]]]|].
    2: { destruct (⌜o1 = NONE⌝) eqn:Eh; [|injection Hev as <- _; contradiction]. apply bool_decide_spec in Eh; subst o1.
      destruct (clock s =? 0) eqn:Ec0.
      { injection Hev as <- <-. unfold flush_state; cbn [stack_max state_stack_size set_locals_size set_store_field set_stack set_locals].
        split; [apply option_le_X_MAX_X|intros _; split; [reflexivity|nbc]]. }
      set (sc := call_env args1 (lookup d (state_stack_size s)) (dec_clock s)) in Hev.
      destruct (evaluate (prog0, sc)) as [r2 t2] eqn:E2.
      destruct (bad_fun_return r2) eqn:Ebf; [injection Hev as <- _; contradiction|]. injection Hev as <- <-.
      assert (Hlt : eval_lt (prog0, sc) (wordLang.Call NONE (SOME d) l NONE, s))
        by (unfold eval_lt, sc, call_env, dec_clock; cbn; apply N.eqb_neq in Ec0; right; split; [reflexivity|left; lia]).
      assert (Hsc : stack_max sc = OPTION_MAP2 MAX (stack_max s) (OPTION_MAP2 N.add (stack_size (stack s)) (lookup d (state_stack_size s))) /\
                    stack sc = stack s /\ state_stack_size sc = state_stack_size s /\
                    locals_size sc = lookup d (state_stack_size s) /\ code sc = code s)
        by (unfold sc, call_env, dec_clock; cbn; auto 6).
      destruct Hsc as (Hsm & Hst & Hss & Hlsz & Hcode).
      assert (Hloc : ~ (r2 = NONE \/ (exists k, r2 = SOME (Break k)) \/ (exists k, r2 = SOME (Continue k))))
        by (intros [->|[[k ->]|[k ->]]]; discriminate Ebf).
      assert (Hdom : lookup d funs2 = SOME (ar, prog0) -> True) by auto.
      destruct (MEM d ns) eqn:Emem; cbn [andb].
      + assert (Hd2 : lookup d funs2 = SOME (ar, prog0)).
        { assert (Hdd : domain funs2 d) by (apply Hns, IN_set, MEM_iff_d; exact Emem).
          apply domain_lookup in Hdd. destruct Hdd as [[a0 b0] Hdd]. pose proof (proj1 (subspt_lookup _ _) Hsub2 _ _ Hdd) as E3.
          rewrite Hcd in E3. rewrite Hdd, E3. reflexivity. }
        destruct (IH (prog0, sc) Hlt r2 t2 funs d ns funs2 E2) as [HA HB].
        { unfold dhyp; cbn [snd]. rewrite Hcode, Hss, Hlsz.
          split; [exact Hsub1|split; [exact Hsub2|split; [reflexivity|split; [exact Hres|auto]]]]. }
        unfold dbound in HA. cbn [fst snd] in HA, HB. rewrite Hsm, Hst, Hss in HA. rewrite Hss in HB.
        pose proof (MEM_max_depth_graphs (state_stack_size s) ns funs funs2 ns d _ (conj Emem Hd2)) as Hg.
        cbn [max_depth_graphs] in Hg. rewrite Hd2 in Hg.
        cbn [max_depth].
        split.
        * revert HA Hg. clear. onum.
        * intros [Hg1 _]. destruct HB as [HS _]; [|split; [exact HS|intros Hr; contradiction]].
          split; [exact Hg1|]. revert Hg Hg1. clear. onum.
      + destruct (lookup d funs) as [[a0 body]|] eqn:Eld; [|cbn [max_depth]; split; [onum|intros [_ H]; onum]].
        destruct (Hfd _ _ eq_refl) as (Hd2 & -> & ->).
        assert (Hlen : LENGTH ns < size funs2)
          by (apply (LENGTH_LESS_size d ns funs2 (ar, prog0)); repeat split; auto; rewrite Emem; discriminate).
        assert (Hlen' : (LENGTH ns <? size funs2) = true) by (apply N.ltb_lt; exact Hlen).
        rewrite Hlen', max_depth_mk_Branch. cbn [max_depth].
        destruct (IH (prog0, sc) Hlt r2 t2 funs d (d :: ns) funs2 E2) as [HA HB].
        { unfold dhyp; cbn [snd]. rewrite Hcode, Hss, Hlsz.
          split; [exact Hsub1|split; [exact Hsub2|split; [reflexivity|split; [exact Hres|]]]].
          split; [apply MEM_iff_d; left; reflexivity|split].
          - cbn [ALL_DISTINCT]. rewrite Emem. exact Hdn.
          - intros x Hx. apply IN_set in Hx. destruct Hx as [<-|Hx]; [apply domain_lookup; eauto|apply Hns, IN_set, Hx]. }
        unfold dbound in HA. cbn [fst snd] in HA, HB. rewrite Hsm, Hst, Hss in HA. rewrite Hss in HB.
        cbn [max_depth_graphs] in HA, HB. rewrite Hd2 in HA, HB.
        pose proof (option_le_max_depth_graphs (state_stack_size s) funs funs2 ns (d :: ns) ns) as Hg.
        specialize (Hg ltac:(split; [intros x Hx; apply IN_set; right; apply IN_set, Hx|cbn [LENGTH]; lia])).
        split.
        * revert HA Hg. clear. onum.
        * intros [Hg1 Hg2]. destruct HB as [HS _]; [|split; [exact HS|intros Hr; contradiction]].
          split; revert Hg Hg1 Hg2; clear; onum. }
    destruct (⌜domain (FST names) = {}⌝ || negb (ALL_DISTINCT n')); [injection Hev as <- _; contradiction|].
    destruct (cut_envs names (locals s)) as [envs|] eqn:Ecut; [|injection Hev as <- _; contradiction].
    rewrite andb_false_r.
    destruct (lookup d funs) as [[a0 body]|] eqn:Eld; [|cbn [max_depth]; split; [onum|intros [_ H]; onum]].
    destruct (Hfd _ _ eq_refl) as (Hd2 & -> & ->).
    match goal with |- context [max_depth ?SS ?T] =>
      assert (Hmd : max_depth SS T =
        OPTION_MAP2 MAX (OPTION_MAP2 N.add (lookup n SS) (OPTION_MAP (N.add (hsz o1)) (lookup d SS)))
          (OPTION_MAP2 MAX (OPTION_MAP2 N.add (lookup n SS)
                             (OPTION_MAP (N.add (hsz o1)) (max_depth SS (call_graph (delete d funs) d [d] (size funs2) prog0))))
             (OPTION_MAP2 MAX (max_depth SS (match o1 with NONE => Leaf | SOME (_, (p7, _)) => call_graph funs n ns (size funs2) p7 end))
                (max_depth SS (call_graph funs n ns (size funs2) ret_handler)))))
        by (destruct o1 as [[? [? [? ?]]]|]; do 3 (rewrite ?max_depth_mk_Branch; cbn [max_depth hsz]); clear; onum)
    end.
    rewrite Hmd. clear Hmd.
    destruct (lookup n (state_stack_size s)) as [vn|] eqn:Evn; [|split; [onum|intros [_ H]; onum]].
    destruct (lookup d (state_stack_size s)) as [vd|] eqn:Evd; [|split; [onum|intros [_ H]; onum]].
    destruct (max_depth (state_stack_size s) (call_graph (delete d funs) d [d] (size funs2) prog0)) as [vb|] eqn:Evb;
      [|split; [onum|intros [_ H]; onum]].
    destruct (max_depth (state_stack_size s) (match o1 with NONE => Leaf | SOME (_, (p7, _)) => call_graph funs n ns (size funs2) p7 end))
      as [vh|] eqn:Evh; [|split; [onum|intros [_ H]; onum]].
    destruct (max_depth (state_stack_size s) (call_graph funs n ns (size funs2) ret_handler)) as [vr|] eqn:Evr;
      [|split; [onum|intros [_ H]; onum]].
    destruct (max_depth_graphs (state_stack_size s) ns ns funs funs2) as [g|] eqn:Eg; [|split; [onum|intros [H _]; onum]].
    destruct (clock s =? 0) eqn:Ec0.
    { pose proof (ce_pe args1 (SOME vd) envs o1 s) as (_ & _ & _ & _ & _ & _ & _ & Hsz & Hsm).
      rewrite Hsm, Hsz, Hls in Hev. injection Hev as <- <-. unfold flush_state.
      cbn [stack_max state_stack_size set_locals_size set_store_field set_stack set_locals set_stack_max]. split; [clear; onum|intros _; split; [reflexivity|nbc]]. }
    set (sc := call_env args1 (SOME vd) (push_env envs o1 (dec_clock s))) in Hev.
    rewrite fix_clock_evaluate in Hev.
    destruct (evaluate (prog0, sc)) as [r2 s2] eqn:E2.
    pose proof (ce_pe args1 (SOME vd) envs o1 (dec_clock s)) as (Hc_code & Hc_ss & Hc_ls & Hc_clk & Hc_td & [lf Hc_stk] & Hc_h & Hc_sz & Hc_sm).
    fold sc in Hc_code, Hc_ss, Hc_ls, Hc_clk, Hc_td, Hc_stk, Hc_h, Hc_sz, Hc_sm.
    unfold dec_clock in Hc_code, Hc_ss, Hc_clk, Hc_td, Hc_stk, Hc_h, Hc_sz, Hc_sm.
    cbn [code state_stack_size clock termdep stack handler locals_size stack_max set_clock] in Hc_code, Hc_ss, Hc_clk, Hc_td, Hc_stk, Hc_h, Hc_sz, Hc_sm.
    rewrite Hls in Hc_sz, Hc_stk. rewrite Hc_sz in Hc_sm.
    assert (Hr2 : r2 <> SOME Error) by (intros ->; cbn iota in Hev; injection Hev as <- _; contradiction).
    assert (Hlt1 : eval_lt (prog0, sc) (wordLang.Call (SOME (n', (names, (ret_handler, (l1, l2))))) (SOME d) l o1, s))
      by (unfold eval_lt; cbn [fst snd]; rewrite Hc_clk, Hc_td; apply N.eqb_neq in Ec0; right; split; [reflexivity|left; lia]).
    destruct (IH (prog0, sc) Hlt1 r2 s2 (delete d funs) d [d] funs2 E2) as [HA1 HB1].
    { unfold dhyp; cbn [snd]. rewrite Hc_code, Hc_ss, Hc_ls, Evd.
      split; [apply subspt_lookup; intros x y E; rewrite lookup_delete in E; destruct (decide (x = d)); [discriminate|];
              exact (proj1 (subspt_lookup _ _) Hsub1 _ _ E)|].
      split; [exact Hsub2|split; [reflexivity|split; [exact Hr2|]]].
      split; [apply MEM_iff_d; left; reflexivity|split; [reflexivity|]].
      intros x Hx. apply IN_set in Hx. destruct Hx as [<-|[]]. apply domain_lookup; eauto. }
    unfold dbound in HA1. cbn [fst snd max_depth_graphs] in HA1, HB1. rewrite Hc_ss, Hd2, Evd, Evb in HA1, HB1.
    rewrite Hc_sm, Hc_sz in HA1.
    destruct HB1 as [HS1 HL1]; [split; cbn; discriminate|]. rewrite ?Hc_ss in HS1.
    assert (HB0 : option_le (stack_max s2) (OPTION_MAP2 MAX (stack_max s) (OPTION_MAP2 N.add (stack_size (stack s))
        (OPTION_MAP2 MAX (SOME g) (OPTION_MAP2 MAX (OPTION_MAP2 N.add (SOME vn) (OPTION_MAP (N.add (hsz o1)) (SOME vd)))
          (OPTION_MAP2 MAX (OPTION_MAP2 N.add (SOME vn) (OPTION_MAP (N.add (hsz o1)) (SOME vb)))
             (OPTION_MAP2 MAX (SOME vh) (SOME vr)))))))) by (revert HA1; clear; onum).
    clear HA1.
    pose proof (evaluate_stack_swap prog0 sc) as SW. rewrite E2 in SW.
    destruct r2 as [[x ys|x y|k|k| | |f|]|]; cbn iota in Hev;
      try (injection Hev as <- _; contradiction);
      try (injection Hev as <- <-; split; [exact HB0|intros _; split; [exact HS1|nbc]]).
    + (* Result *)
      destruct (negb ⌜x = Loc l1 l2⌝ || negb (LENGTH ys =? LENGTH n')); [injection Hev as <- _; contradiction|].
      destruct (pop_env s2) as [s3|] eqn:Ep; [|injection Hev as <- _; contradiction].
      destruct (⌜domain (locals s3) = domain (FST envs) UNION domain (SND envs)⌝); [|injection Hev as <- _; contradiction].
      destruct SW as [K _]. rewrite Hc_stk in K. destruct (pop_key _ _ _ _ _ _ _ K Ep) as [Hl3 Hs3].
      assert (Ep3 : stack_max s3 = stack_max s2 /\ state_stack_size s3 = state_stack_size s2 /\ clock s3 = clock s2 /\
                    termdep s3 = termdep s2 /\ code s3 = code s2) by (pose proof (pop_env_const _ _ Ep); tauto).
      destruct Ep3 as (Em3 & Ess3 & Ecl3 & Etd3 & Ecd3).
      destruct (evaluate_clock _ _ _ _ E2) as [Hck2 Htd2].
      assert (Hlt2 : eval_lt (ret_handler, set_vars n' ys s3) (wordLang.Call (SOME (n', (names, (ret_handler, (l1, l2))))) (SOME d) l o1, s)).
      { unfold eval_lt, set_vars; cbn [fst snd clock termdep set_locals]. rewrite Ecl3, Etd3, Htd2, Hc_td.
        rewrite Hc_clk in Hck2. apply N.eqb_neq in Ec0. right; split; [reflexivity|left; lia]. }
      destruct (IH _ Hlt2 res s1 funs n ns funs2 Hev) as [HA2 HB2].
      { unfold dhyp, set_vars; cbn [snd code locals_size state_stack_size set_locals]. rewrite Ecd3, Hl3, Ess3, HS1, Evn.
        split; [exact Hsub1|split; [eapply subspt_trans; split; [exact Hsub2|]|]].
        - rewrite <- Hc_code. apply (evaluate_code_only_grows _ _ _ _ E2).
        - split; [reflexivity|split; [exact Hres|auto]]. }
      unfold dbound, set_vars in HA2, HB2. cbn [fst snd stack_max stack state_stack_size locals_size set_locals] in HA2, HB2.
      rewrite Em3, Hs3, Ess3, HS1, Eg, Evr in HA2. rewrite Ess3, HS1, Eg, Evr in HB2.
      split.
      * revert HA2 HB0. clear. onum.
      * intros _. destruct HB2 as [HS2 HL2]; [split; discriminate|]. split; [exact HS2|].
        intros Hr. rewrite (HL2 Hr). rewrite Hl3, Hls. reflexivity.
    + (* Exception *)
      destruct o1 as [[n2 [hp [l3 l4]]]|].
      2: { injection Hev as <- <-. split; [exact HB0|intros _; split; [exact HS1|nbc]]. }
      destruct (negb ⌜x = Loc l3 l4⌝); [injection Hev as <- _; contradiction|].
      destruct (⌜domain (locals s2) = domain (FST envs) UNION domain (SND envs)⌝); [|injection Hev as <- _; contradiction].
      destruct SW as (Hhl & e0 & e & nn & ls & m & lss & HL & Hm & _ & Ks & _).
      rewrite Hc_h, Hc_stk in HL. rewrite LASTN_LENGTH_cond in HL by (cbn [LENGTH]; lia).
      injection HL as Em _ _ _ <-. apply s_key_eq_stack_size in Ks.
      destruct (evaluate_clock _ _ _ _ E2) as [Hck2 Htd2].
      assert (Hlt2 : eval_lt (hp, set_var n2 y s2) (wordLang.Call (SOME (n', (names, (ret_handler, (l1, l2))))) (SOME d) l (SOME (n2, (hp, (l3, l4)))), s)).
      { unfold eval_lt, set_var; cbn [fst snd clock termdep set_locals]. rewrite Htd2, Hc_td.
        rewrite Hc_clk in Hck2. apply N.eqb_neq in Ec0. right; split; [reflexivity|left; lia]. }
      destruct (IH _ Hlt2 res s1 funs n ns funs2 Hev) as [HA2 HB2].
      { unfold dhyp, set_var; cbn [snd code locals_size state_stack_size set_locals]. rewrite HS1, Evn, <- Hm, <- Em.
        split; [exact Hsub1|split; [eapply subspt_trans; split; [exact Hsub2|]|]].
        - rewrite <- Hc_code. apply (evaluate_code_only_grows _ _ _ _ E2).
        - split; [reflexivity|split; [exact Hres|auto]]. }
      cbn in Evh.
      unfold dbound, set_var in HA2, HB2. cbn [fst snd stack_max stack state_stack_size locals_size set_locals] in HA2, HB2.
      rewrite Ks, HS1, Eg, Evh in HA2. rewrite HS1, Eg, Evh in HB2.
      split.
      * revert HA2 HB0. clear. onum.
      * intros _. destruct HB2 as [HS2 HL2]; [split; discriminate|]. split; [exact HS2|].
        intros Hr. rewrite (HL2 Hr). cbn [locals_size set_locals set_var] in *. congruence.
  (* Seq *)
  - rewrite fix_clock_evaluate in Hev. destruct (evaluate (p1, s)) as [r1 t1] eqn:E1.
    assert (Hlt1 : eval_lt (p1, s) (Seq p1 p2, s)) by (unfold eval_lt; cbn; right; split; [reflexivity|right; split; [reflexivity|lia]]).
    destruct (evaluate_clock _ _ _ _ E1) as [Hc1 Ht1].
    destruct (⌜r1 = NONE⌝) eqn:Er1.
    + apply bool_decide_spec in Er1. subst r1.
      destruct (IH (p1, s) Hlt1 NONE t1 funs n ns funs2 E1) as [HA1 HB1].
      { split; [exact Hsub1|split; [exact Hsub2|split; [exact Hls|split; [discriminate|auto]]]]. }
      cbn [fst snd] in *. unfold dgoal, dbound in *. rewrite Eseq, max_depth_mk_Branch. cbn [max_depth].
      destruct (max_depth_graphs (state_stack_size s) ns ns funs funs2) as [g|] eqn:Eg; [|split; [onum|intros [H _]; congruence]].
      destruct (max_depth (state_stack_size s) (call_graph funs n ns (size funs2) p1)) as [d1|] eqn:Ed1; [|split; [onum|intros [_ H]; onum]].
      destruct (HB1 ltac:(split; discriminate)) as [HS1 HL1]. specialize (HL1 (or_introl eq_refl)).
      assert (Hlt2 : eval_lt (p2, t1) (Seq p1 p2, s)).
      { unfold eval_lt; cbn [fst snd psize]. right. split; [exact Ht1|].
        destruct (N.lt_ge_cases (clock t1) (clock s)); [left; exact H|right; split; [lia|lia]]. }
      destruct (IH (p2, t1) Hlt2 res s1 funs n ns funs2 Hev) as [HA2 HB2].
      { unfold dhyp; cbn [snd]. split; [exact Hsub1|split; [eapply subspt_trans; split; [exact Hsub2|apply (evaluate_code_only_grows _ _ _ _ E1)]|]].
        split; [rewrite HL1, HS1; exact Hls|split; [exact Hres|auto]]. }
      cbn [fst snd] in *. rewrite HS1, (evaluate_NONE_stack_size_const _ _ _ E1), Eg in HA2. rewrite HS1, Eg in HB2.
      split.
      * revert HA1 HA2. onum.
      * intros [_ Hd]. destruct (max_depth (state_stack_size s) (call_graph funs n ns (size funs2) p2)) as [d2|] eqn:Ed2;
          [|onum]. destruct (HB2 ltac:(split; discriminate)) as [HS2 HL2]. split; [congruence|].
        intros Hr. rewrite (HL2 Hr). exact HL1.
    + injection Hev as <- <-.
      destruct (IH (p1, s) Hlt1 r1 t1 funs n ns funs2 E1) as [HA1 HB1].
      { split; [exact Hsub1|split; [exact Hsub2|split; [exact Hls|split; [exact Hres|auto]]]]. }
      cbn [fst snd] in *. unfold dgoal, dbound in *. rewrite Eseq, max_depth_mk_Branch. cbn [max_depth].
      split.
      * revert HA1. onum.
      * intros [Hg Hd]. destruct (HB1) as [HS1 HL1].
        { split; [exact Hg|]. intros E; apply Hd. rewrite E. onum. }
        split; [exact HS1|exact HL1].
  (* If *)
  - destruct (get_var n0 s) as [x|]; [|injection Hev as <- _; contradiction].
    destruct (get_var_imm r s) as [y|]; [|injection Hev as <- _; contradiction].
    destruct (word_cmp c0 x y) as [[]|]; [| |injection Hev as <- _; contradiction].
    + assert (Hlt : eval_lt (p1, s) (If c0 n0 r p1 p2, s)) by (unfold eval_lt; cbn; right; split; [reflexivity|right; split; [reflexivity|lia]]).
      destruct (IH (p1, s) Hlt res s1 funs n ns funs2 Hev Hh) as [HA HB]. cbn [fst snd] in *.
      unfold dgoal, dbound in *. rewrite Eif, max_depth_mk_Branch. cbn [max_depth].
      split; [revert HA; onum|intros [Hg Hd]; apply HB; split; [exact Hg|intros E; apply Hd; rewrite E; onum]].
    + assert (Hlt : eval_lt (p2, s) (If c0 n0 r p1 p2, s)) by (unfold eval_lt; cbn; right; split; [reflexivity|right; split; [reflexivity|lia]]).
      destruct (IH (p2, s) Hlt res s1 funs n ns funs2 Hev Hh) as [HA HB]. cbn [fst snd] in *.
      unfold dgoal, dbound in *. rewrite Eif, max_depth_mk_Branch. cbn [max_depth].
      split; [revert HA; onum|intros [Hg Hd]; apply HB; split; [exact Hg|intros E; apply Hd; rewrite E; onum]].
  (* Loop *)
  - destruct (cut_state (s0, LN) s) as [s'|] eqn:Ecut; [|injection Hev as <- _; contradiction].
    assert (Es' : exists env, s' = set_locals env s)
      by (unfold cut_state in Ecut; destruct (cut_env _ _) as [env|]; [injection Ecut as <-; eexists; reflexivity|discriminate]).
    destruct Es' as [env ->]. clear Ecut.
    rewrite fix_clock_evaluate in Hev. destruct (evaluate (p, set_locals env s)) as [r1 t1] eqn:E1.
    assert (Hr1 : r1 <> SOME Error).
    { intros ->. cbn [cont_loop] in Hev. destruct (⌜SOME (@Error a) = SOME (Break 0)⌝) eqn:Eb.
      - apply bool_decide_spec in Eb. discriminate.
      - injection Hev as <- _. contradiction. }
    assert (Hlt1 : eval_lt (p, set_locals env s) (Loop s0 p s2, s))
      by (unfold eval_lt; cbn; right; split; [reflexivity|right; split; [reflexivity|lia]]).
    destruct (IH (p, set_locals env s) Hlt1 r1 t1 funs n ns funs2 E1) as [HA HB].
    { split; [exact Hsub1|split; [exact Hsub2|split; [exact Hls|split; [exact Hr1|auto]]]]. }
    unfold dbound in HA. cbn [fst snd stack_max state_stack_size stack locals_size code set_locals] in HA, HB.
    destruct (evaluate_clock _ _ _ _ E1) as [Hc1 Ht1]. cbn [clock termdep set_locals] in Hc1, Ht1.
    unfold dgoal, dbound. rewrite Eloop.
    destruct (max_depth_graphs (state_stack_size s) ns ns funs funs2) as [g|] eqn:Eg; [|split; [onum|intros [H _]; congruence]].
    destruct (max_depth (state_stack_size s) (call_graph funs n ns (size funs2) p)) as [d1|] eqn:Ed1; [|split; [onum|intros [_ H]; onum]].
    destruct (HB ltac:(split; discriminate)) as [HS1 HL1].
    destruct (cont_loop r1) eqn:Ecl.
    + assert (Hr1' : r1 = NONE \/ r1 = SOME (Continue 0))
        by (destruct r1 as [[]|]; cbn in Ecl; try discriminate; auto;
            right; apply N.eqb_eq in Ecl; subst; reflexivity).
      specialize (HL1 ltac:(destruct Hr1' as [->| ->]; [left; reflexivity|right; right; eexists; reflexivity])).
      destruct (clock t1 =? 0) eqn:Ec0.
      * injection Hev as <- <-. unfold flush_state; cbn [stack_max state_stack_size set_locals_size set_store_field set_stack set_locals].
        split; [exact HA|intros _; split; [exact HS1|nbc]].
      * unfold STOP in Hev.
        assert (Hlt2 : eval_lt (Loop s0 p s2, dec_clock t1) (Loop s0 p s2, s)).
        { unfold eval_lt, dec_clock; cbn [fst snd clock termdep set_clock]. right. split; [exact Ht1|left].
          apply N.eqb_neq in Ec0. lia. }
        assert (Hst : stack_size (stack t1) = stack_size (stack s)).
        { pose proof (evaluate_stack_swap p (set_locals env s)) as SW. rewrite E1 in SW.
          destruct Hr1' as [->| ->]; destruct SW as [K _]; symmetry; apply s_key_eq_stack_size, K. }
        destruct (IH (Loop s0 p s2, dec_clock t1) Hlt2 res s1 funs n ns funs2 Hev) as [HA2 HB2].
        { unfold dhyp, dec_clock; cbn [snd code locals_size state_stack_size set_clock].
          split; [exact Hsub1|split; [eapply subspt_trans; split; [exact Hsub2|apply (evaluate_code_only_grows _ _ _ _ E1)]|]].
          split; [rewrite HL1, HS1; exact Hls|split; [exact Hres|auto]]. }
        unfold dgoal, dbound, dec_clock in HA2, HB2. cbn [fst snd stack_max state_stack_size stack set_clock] in HA2, HB2.
        rewrite Eloop, HS1, Hst, Eg, Ed1 in HA2. rewrite Eloop, HS1, Eg, Ed1 in HB2.
        split.
        -- revert HA HA2. clear. onum.
        -- intros _. destruct (HB2 ltac:(split; discriminate)) as [HS2 HL2]. split; [congruence|].
           intros Hr. cbn [locals_size set_clock] in HL2. rewrite (HL2 Hr). exact HL1.
    + destruct (⌜r1 = SOME (Break 0)⌝) eqn:Eb.
      * apply bool_decide_spec in Eb. subst r1.
        specialize (HL1 ltac:(right; left; eexists; reflexivity)).
        destruct (cut_state (s2, LN) t1) as [t2|] eqn:Ecut2; [|injection Hev as <- _; contradiction].
        injection Hev as <- <-.
        assert (Et2 : exists env, t2 = set_locals env t1)
          by (unfold cut_state in Ecut2; destruct (cut_env _ _) as [env2|]; [injection Ecut2 as <-; eexists; reflexivity|discriminate]).
        destruct Et2 as [env2 ->]. cbn [stack_max state_stack_size locals_size set_locals].
        split; [exact HA|intros _; split; [exact HS1|intros _; exact HL1]].
      * injection Hev as <- <-. split; [exact HA|intros _; split; [exact HS1|]].
        intros Hr. apply HL1. destruct r1 as [[]|]; cbn [exit_loop] in Hr; try exact Hr;
          destruct Hr as [Hr|[[? Hr]|[? Hr]]]; try discriminate Hr; eauto.
  (* Alloc *)
  - destruct (get_var n0 s) as [[w|]|]; [|injection Hev as <- _; contradiction..].
    unfold alloc in Hev.
    destruct (cut_envs p (locals s)) as [envs|] eqn:Ec; [|injection Hev as <- _; contradiction].
    set (s0 := push_env envs NONE (set_store AllocSize (Word w) s)) in Hev.
    destruct (gc s0) as [g|] eqn:Eg; [|injection Hev as <- _; contradiction].
    destruct (pop_env g) as [q|] eqn:Ep; [|injection Hev as <- _; contradiction].
    pose proof (gc_s_key_eq _ _ Eg) as Kg.
    assert (Gm : stack_max g = stack_max s0 /\ state_stack_size g = state_stack_size s0)
      by (pose proof (gc_const _ _ Eg); tauto).
    assert (Qm : stack_max q = stack_max g /\ state_stack_size q = state_stack_size g)
      by (pose proof (pop_env_const _ _ Ep); tauto).
    unfold s0, push_env in Kg, Gm. destruct (env_to_list (SND envs) (permute (set_store AllocSize (Word w) s))) as [l perm] eqn:El.
    unfold set_store in Kg, Gm. cbn [stack set_permute set_stack_max set_stack locals_size set_store_field stack_max state_stack_size] in Kg, Gm.
    assert (Ql : locals_size q = locals_size s).
    { unfold pop_env in Ep. destruct (stack g) as [|[m e0 e o] xs]; [contradiction|].
      cbn in Kg. destruct Kg as [_ Kf]. destruct o as [[? ?]|]; [contradiction|].
      destruct Kf as (_ & _ & <-). injection Ep as <-. reflexivity. }
    assert (Hsz : stack_size (StackFrame (locals_size s) (toAList (FST envs)) l NONE :: stack s) =
                  OPTION_MAP2 N.add (locals_size s) (stack_size (stack s))) by reflexivity.
    rewrite Hsz, Hls in Gm. destruct Gm as [Gm Gs]. destruct Qm as [Qm Qs]. rewrite Gm in Qm. rewrite Gs in Qs.
    unfold dgoal, dbound. rewrite Ealloc. cbn [max_depth].
    assert (Hb : option_le (stack_max q) (OPTION_MAP2 MAX (stack_max s)
      (OPTION_MAP2 N.add (stack_size (stack s)) (OPTION_MAP2 MAX (max_depth_graphs (state_stack_size s) ns ns funs funs2)
        (OPTION_MAP2 N.add (lookup n (state_stack_size s)) (SOME 0)))))).
    { rewrite Qm. clear. onum. }
    destruct (get_store AllocSize q) as [w'|]; [|injection Hev as <- _; contradiction].
    destruct (has_space w' q) as [[]|]; [injection Hev as <- <-|injection Hev as <- <-|injection Hev as <- _; contradiction].
    + split; [exact Hb|intros _; split; [exact Qs|intros _; exact Ql]].
    + unfold flush_state; cbn. split; [exact Hb|intros _; split; [exact Qs|nbc]].
  (* Install *)
  - unfold dgoal, dbound. rewrite Einst. cbn [max_depth]. split; [onum|intros [_ H]; onum].
  (* ShareInst *)
  - unfold share_inst, sh_mem_set_var, sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32,
      sh_mem_load, sh_mem_load_byte, sh_mem_load16, sh_mem_load32 in Hev.
    simple_case Hev Hres.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "max_depth_call_graph" *)
Theorem max_depth_call_graph : forall (prog : prog a) (s : state) res s1 funs n a0,
  evaluate (prog, s) = (res, s1) /\ subspt funs (code s) /\
  lookup n funs = SOME (a0, prog) /\
  locals_size s = lookup n (state_stack_size s) /\ res <> SOME Error ->
  option_le (stack_max s1)
    (OPTION_MAP2 MAX (stack_max s)
      (OPTION_MAP2 N.add (stack_size (stack s))
        (max_depth (state_stack_size s) (full_call_graph n funs)))).
Proof.
  intros prog s res s1 funs n a0 (E & Hsub & Hl & Hls & Hres).
  destruct (max_depth_call_graph_lemma prog s res s1 funs n [n] funs) as [HA _].
  { repeat split; auto.
    - apply subspt_lookup; auto.
    - apply MEM_iff_d; left; reflexivity.
    - intros x Hx. apply IN_set in Hx. destruct Hx as [<-|[]]. apply domain_lookup; eauto. }
  unfold full_call_graph. rewrite Hl. cbn [max_depth max_depth_graphs] in HA |- *. rewrite Hl in HA.
  revert HA. clear. onum.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "max_depth_Call_SOME" *)
Theorem max_depth_Call_SOME : forall n1 n2 n3 n4 dest args (s : state) res s1 funs,
  evaluate (wordLang.Call (SOME (n1, (n2, (Skip, (n3, n4))))) (SOME dest) args NONE, s) = (res, s1) /\
  res <> SOME Error /\ subspt funs (code s) ->
  option_le (stack_max s1)
    (OPTION_MAP2 MAX (stack_max s)
      (OPTION_MAP2 N.add (locals_size s)
        (OPTION_MAP2 N.add (stack_size (stack s))
          (max_depth (state_stack_size s) (full_call_graph dest funs))))).
Proof.
  intros n1 n2 n3 n4 dest args s res s1 funs (Hev & Hres & Hsub).
  unfold full_call_graph.
  destruct (lookup dest funs) as [[a0 body]|] eqn:Eld; [|cbn [max_depth]; onum].
  pose proof (proj1 (subspt_lookup _ _) Hsub _ _ Eld) as Hcd.
  rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  destruct (get_vars args s) as [xs|]; [|injection Hev as <- _; contradiction].
  destruct (bad_dest_args (SOME dest) args); [injection Hev as <- _; contradiction|].
  destruct (find_code (SOME dest) (add_ret_loc (SOME (n1, (n2, (Skip, (n3, n4))))) xs) (code s) (state_stack_size s))
    as [[args1 [prog0 ss]]|] eqn:Efc; [|injection Hev as <- _; contradiction].
  assert (Hfc : prog0 = body /\ ss = lookup dest (state_stack_size s)).
  { unfold find_code in Efc. rewrite Hcd in Efc. destruct (_ =? _); [|discriminate]. injection Efc as _ <- <-. auto. }
  destruct Hfc as [-> ->].
  destruct (⌜domain (FST n2) = {}⌝ || negb (ALL_DISTINCT n1)); [injection Hev as <- _; contradiction|].
  destruct (cut_envs n2 (locals s)) as [envs|] eqn:Ecut; [|injection Hev as <- _; contradiction].
  cbn [max_depth].
  destruct (clock s =? 0) eqn:Ec0.
  { pose proof (ce_pe args1 (lookup dest (state_stack_size s)) envs NONE s) as (_ & _ & _ & _ & _ & _ & _ & Hsz & Hsm).
    rewrite Hsm, Hsz in Hev. injection Hev as <- <-. unfold flush_state.
    cbn [stack_max set_locals_size set_store_field set_stack set_locals set_stack_max hsz].
    clear. onum. }
  set (sc := call_env args1 (lookup dest (state_stack_size s)) (push_env envs NONE (dec_clock s))) in Hev.
  rewrite fix_clock_evaluate in Hev.
  destruct (evaluate (body, sc)) as [r2 s2] eqn:E2.
  pose proof (ce_pe args1 (lookup dest (state_stack_size s)) envs NONE (dec_clock s))
    as (Hc_code & Hc_ss & Hc_ls & _ & _ & _ & _ & Hc_sz & Hc_sm).
  fold sc in Hc_code, Hc_ss, Hc_ls, Hc_sz, Hc_sm.
  unfold dec_clock in Hc_code, Hc_ss, Hc_sz, Hc_sm.
  cbn [code state_stack_size stack locals_size stack_max set_clock hsz] in Hc_code, Hc_ss, Hc_sz, Hc_sm.
  rewrite Hc_sz in Hc_sm.
  assert (Hr2 : r2 <> SOME Error) by (intros ->; cbn iota in Hev; injection Hev as <- _; contradiction).
  pose proof (max_depth_call_graph body sc r2 s2 funs dest a0) as HA.
  specialize (HA ltac:(rewrite Hc_code, Hc_ls, Hc_ss; repeat split; auto)).
  unfold full_call_graph in HA. rewrite Eld, Hc_sm, Hc_sz, Hc_ss in HA. cbn [max_depth] in HA.
  assert (Hm : stack_max s1 = stack_max s2).
  { destruct r2 as [[x ys|x y|k|k| | |f|]|]; cbn iota in Hev; try (injection Hev as <- <-; reflexivity);
      try (injection Hev as <- _; contradiction).
    destruct (negb ⌜x = Loc n3 n4⌝ || negb (LENGTH ys =? LENGTH n1)); [injection Hev as <- _; contradiction|].
    destruct (pop_env s2) as [s3|] eqn:Ep; [|injection Hev as <- _; contradiction].
    destruct (⌜domain (locals s3) = domain (FST envs) UNION domain (SND envs)⌝); [|injection Hev as <- _; contradiction].
    rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev. injection Hev as _ <-.
    unfold set_vars; cbn [stack_max set_locals].
    pose proof (pop_env_const _ _ Ep); tauto. }
  rewrite Hm. revert HA. clear. onum.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "max_depth_Call_NONE" *)
Theorem max_depth_Call_NONE : forall dest args (s : state) res s1 funs,
  evaluate (wordLang.Call NONE (SOME dest) args NONE, s) = (res, s1) /\
  res <> SOME Error /\ subspt funs (code s) ->
  option_le (stack_max s1)
    (OPTION_MAP2 MAX (stack_max s)
      (OPTION_MAP2 N.add (stack_size (stack s))
        (max_depth (state_stack_size s) (full_call_graph dest funs)))).
Proof.
  intros dest args s res s1 funs (Hev & Hres & Hsub).
  unfold full_call_graph.
  destruct (lookup dest funs) as [[a0 body]|] eqn:Eld; [|cbn [max_depth]; onum].
  pose proof (proj1 (subspt_lookup _ _) Hsub _ _ Eld) as Hcd.
  rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  destruct (get_vars args s) as [xs|]; [|injection Hev as <- _; contradiction].
  destruct (bad_dest_args (SOME dest) args); [injection Hev as <- _; contradiction|].
  destruct (find_code (SOME dest) (add_ret_loc NONE xs) (code s) (state_stack_size s))
    as [[args1 [prog0 ss]]|] eqn:Efc; [|injection Hev as <- _; contradiction].
  assert (Hfc : prog0 = body /\ ss = lookup dest (state_stack_size s)).
  { unfold find_code in Efc. rewrite Hcd in Efc. destruct (_ =? _); [|discriminate]. injection Efc as _ <- <-. auto. }
  destruct Hfc as [-> ->].
  destruct (⌜(NONE : option (N * (prog a * (N * N)))) = NONE⌝) eqn:Eh;
    [|exfalso; match type of Eh with ?b = false => assert (Hb : b = true) by (apply bool_decide_spec; reflexivity) end; congruence].
  cbn [max_depth].
  destruct (clock s =? 0) eqn:Ec0.
  { injection Hev as <- <-. unfold flush_state. cbn [stack_max set_locals_size set_store_field set_stack set_locals].
    apply option_le_X_MAX_X. }
  destruct (evaluate (body, call_env args1 (lookup dest (state_stack_size s)) (dec_clock s))) as [r2 s2] eqn:E2.
  destruct (bad_fun_return r2); [injection Hev as <- _; contradiction|]. injection Hev as <- <-.
  pose proof (max_depth_call_graph _ _ _ _ funs dest a0 (conj E2 (conj Hsub (conj Eld (conj eq_refl Hres))))) as HA.
  unfold full_call_graph, call_env, dec_clock in HA. rewrite Eld in HA.
  cbn [max_depth stack_max stack state_stack_size set_stack_max set_locals_size set_locals set_clock] in HA.
  revert HA. clear. onum.
Qed.

End Main.
End Depth.


