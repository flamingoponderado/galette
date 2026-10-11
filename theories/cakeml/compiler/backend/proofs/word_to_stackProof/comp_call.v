(** * CakeML [word_to_stackProof]: the call cases of [comp_correct]

    Part of the port of
    [cakeml/compiler/backend/proofs/word_to_stackProofScript.sml] (HOL lines
    7924-10049): the [Call] case of [comp_correct] (split by HOL into
    [Call_tail], in [comp_correct.v], and [Call_returning], here) and the
    assembled [comp_correct].

    HOL proves the returning-call case in one long script with the
    no-handler and handler sub-cases inline; here the common reasoning is
    factored into Galette-only lemmas: [wret_cont] (the word-side
    continuation after the callee returns), [call_ret_overflow] (the
    stack-overflow results), [state_rel_callee] (the callee's [state_rel]),
    [state_rel_return_NONE]/[state_rel_return_SOME] (the caller's
    [state_rel] after a normal return), [state_rel_exc_handler] (the
    caller's [state_rel] when an exception is caught) and
    [stack_rel_frame_lookup] (variables of a stack frame).

    [comp_correct] is the theorem of HOL line 5756, stated with HOL's
    [goal] expanded; HOL's later ML rebinding [val comp_correct] (line
    10066, a reordering of the quantifiers) is not a stored theorem and is
    left out.  It is proved by
    well-founded induction on [wordSem.eval_lt] ([comp_goal_all]),
    dispatching to the case lemmas. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words byte.
From Galette.HOL.src.n_bit.words Require Import lemmas fcp_defs.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.misc.misc Require Import fromList2.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc parmove.
From Galette.cakeml.compiler.backend.reg_alloc.parmove Require proofs.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend Require Import word_to_stack.
From Galette.cakeml.compiler.backend.semantics Require Import wordConvs.
From Galette.cakeml.compiler.backend.semantics Require wordSem.
From Galette.cakeml.compiler.backend.semantics.wordProps Require stack_swap stack_max clock dec_clock.
From Galette.cakeml.compiler.backend.semantics Require Import stackSem stackProps.
From Galette.cakeml.compiler.backend.proofs.word_to_stackProof Require Import basic compile_props state_rel gc stack_rel moves inst comp_lemmas syntax.
From Galette.cakeml.compiler.backend.proofs.word_to_stackProof Require Import comp_correct.
From Galette.cakeml.compiler.backend.semantics.wordProps Require consts.
Import wordLang (word_loc, Word, Loc).
Import wordSem (stack_frame, StackFrame).
Open Scope N_scope.

(** ** Galette-only helpers for the returning-call case *)

(** The word-side continuation of a returning call, after the callee has
    returned [(r, s2)] (the tail of [wordSem.evaluate] on [Call]). *)
Definition wret_cont {a C F} (vs : list N) (envs : num_map (word_loc a) * num_map (word_loc a))
    (ret_code : wordLang.prog a) (l1 l2 : N) (h : option (N * (wordLang.prog a * (N * N))))
    (r : option (wordSem.result a)) (s2 : wordSem.state a C F) : option (wordSem.result a) * wordSem.state a C F :=
  match r with
  | SOME (wordSem.Result x ys) =>
      if negb ⌜x = Loc l1 l2⌝ || negb (LENGTH ys =? LENGTH vs)
      then (SOME wordSem.Error, s2)
      else
        match wordSem.pop_env s2 with
        | SOME s3 =>
            if ⌜domain (wordSem.locals s3) = domain (FST envs) UNION domain (SND envs)⌝
            then wordSem.evaluate (ret_code, wordSem.set_vars vs ys s3)
            else (SOME wordSem.Error, s3)
        | NONE => (SOME wordSem.Error, s2)
        end
  | SOME (wordSem.Exception x y) =>
      match h with
      | SOME (n, (hc, (h1, h2))) =>
          if negb ⌜x = Loc h1 h2⌝ then (SOME wordSem.Error, s2)
          else if ⌜domain (wordSem.locals s2) = domain (FST envs) UNION domain (SND envs)⌝
          then wordSem.evaluate (hc, wordSem.set_var n y s2)
          else (SOME wordSem.Error, s2)
      | NONE => (SOME (wordSem.Exception x y), s2)
      end
  | SOME wordSem.TimeOut => (SOME wordSem.TimeOut, s2)
  | SOME wordSem.NotEnoughSpace => (SOME wordSem.NotEnoughSpace, s2)
  | SOME (wordSem.FinalFFI f) => (SOME (wordSem.FinalFFI f), s2)
  | _ => (SOME wordSem.Error, s2)
  end.

Lemma wret_cont_mono {a C F} vs envs ret_code l1 l2 h r (s2 : wordSem.state a C F) res s1 :
  wret_cont vs envs ret_code l1 l2 h r s2 = (res, s1) -> res <> SOME wordSem.Error ->
  isPREFIX (io_events (wordSem.ffi s2)) (io_events (wordSem.ffi s1)) /\
  (the (wordSem.stack_limit s2 + 1) (wordSem.stack_max s2) > wordSem.stack_limit s2 ->
   the (wordSem.stack_limit s1 + 1) (wordSem.stack_max s1) > wordSem.stack_limit s1).
Proof.
  intros He Hr. unfold wret_cont in He.
  destruct r as [[x ys|x y|bn|cn| | |fe|]|]; try (injection He as <- <-; split; [apply isPREFIX_REFL|tauto]); try (injection He as <- _; congruence).
  - destruct (negb _ || negb _); [injection He as <- _; congruence|].
    destruct (wordSem.pop_env s2) as [s3|] eqn:Ep; [|injection He as <- _; congruence].
    destruct (consts.pop_env_const _ _ Ep) as (_ & Hf & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsl & Hsm & _).
    destruct (⌜_⌝); [|injection He as <- _; congruence].
    split.
    + rewrite <- Hf. exact (clock.evaluate_io_events_mono _ _ _ _ He).
    + intros G. rewrite <- Hsl, <- Hsm in G. exact (stack_max.evaluate_stack_limit_stack_max _ _ _ _ (conj He G)).
  - destruct h as [[n [hc [h1 h2]]]|]; [|injection He as <- <-; split; [apply isPREFIX_REFL|tauto]].
    destruct (negb _); [injection He as <- _; congruence|].
    destruct (⌜_⌝); [|injection He as <- _; congruence].
    split.
    + exact (clock.evaluate_io_events_mono _ _ _ _ He).
    + intros G. exact (stack_max.evaluate_stack_limit_stack_max _ _ _ _ (conj He G)).
Qed.

Section CallRetHelpers.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(** The callee's [stack_max] exceeds the limit when its frame does not fit. *)
Lemma callee_stack_max_gt ac k f' s T lens envs h args1 ss fs :
  state_rel ac k 0 0 (wordSem.set_locals_size (SOME 0) (wordSem.set_locals LN (wordSem.push_env envs NONE s))) T (f' :: lens) 0 ->
  the fs ss = fs ->
  (match h with NONE => stack_space T < fs | SOME _ => stack_space T < fs + 3 end) ->
  the (wordSem.stack_limit s + 1) (wordSem.stack_max (wordSem.call_env args1 ss (wordSem.push_env envs h (wordSem.dec_clock s)))) >
  wordSem.stack_limit s.
Proof.
  intros HP Hthe Hov. sr_destr HP. destruct Hssr as (A1 & A2 & A3).
  unfold wordSem.push_env, wordSem.env_to_list in *. unfold wordSem.call_env, wordSem.dec_clock in *. ws_fields.
  destruct h as [[hv [hc [h1 h2]]]|]; ws_fields; rewrite A2;
  unfold wordSem.stack_size in *; cbn [FOLDR] in *;
  remember (FOLDR (OPTION_MAP2 N.add ∘ wordSem.stack_size_frame) (SOME 1) (wordSem.stack s)) as Z;
  cbn [wordSem.stack_size_frame] in *;
  (destruct (wordSem.stack_max s) as [m|]; [|unfold OPTION_MAP2; cbn; lia]);
  (destruct (wordSem.locals_size s) as [ls|]; [|unfold OPTION_MAP2; cbn; lia]);
  (destruct Z as [z0|]; [|unfold OPTION_MAP2; cbn; lia]);
  unfold OPTION_MAP2 in *; cbn [IS_SOME THE andb option_map the] in *; destruct (A3 _ eq_refl) as (_ & _ & z & Ez & Hz);
  injection Ez as <-; (destruct ss as [x|]; cbn [IS_SOME THE andb option_map the] in *; [subst x|lia]); rewrite !MAX_max; lia.
Qed.

End CallRetHelpers.

Lemma MAX_LIST_le_iff (l : list N) m : MAX_LIST l <= m <-> Forall (fun x => x <= m) l.
Proof.
  induction l as [|x l IH]; cbn [MAX_LIST]; [split; [constructor|lia]|].
  rewrite MAX_max, Forall_cons_iff, <- IH. lia.
Qed.

Lemma call_ret_convs {a} k f' vs live (ret_code : wordLang.prog a) l1 l2 dest args h :
  is_true (post_alloc_conventions k (wordLang.Call (SOME (vs, (live, (ret_code, (l1, l2))))) dest args h)) ->
  is_true (flat_exp_conventions (wordLang.Call (SOME (vs, (live, (ret_code, (l1, l2))))) dest args h)) ->
  wordLang.max_var (wordLang.Call (SOME (vs, (live, (ret_code, (l1, l2))))) dest args h) < 2 * f' + 2 * k ->
  args = GENLIST (fun x => 2 * (x + 1)) (LENGTH args) /\ vs = GENLIST (fun x => 2 * (x + 1)) (LENGTH vs) /\
  is_true (post_alloc_conventions k ret_code) /\ is_true (flat_exp_conventions ret_code) /\
  wordLang.max_var ret_code < 2 * f' + 2 * k /\
  (forall x, x IN domain (FST live) \/ x IN domain (SND live) -> EVEN x /\ k <= x DIV 2 /\ x < 2 * f' + 2 * k) /\
  2 * LENGTH args < 2 * f' + 2 * k /\ 2 * LENGTH vs < 2 * f' + 2 * k /\
  match h with
  | NONE => True
  | SOME (v, (hc, _)) => v = 2 /\ is_true (post_alloc_conventions k hc) /\ is_true (flat_exp_conventions hc) /\
                         wordLang.max_var hc < 2 * f' + 2 * k
  end.
Proof.
  unfold post_alloc_conventions. cbn [wordLang.every_var wordLang.every_stack_var call_arg_convention flat_exp_conventions wordLang.max_var].
  intros Hp Hf Hm. unfold is_true in *.
  assert (Hm' : wordLang.max_var ret_code < 2 * f' + 2 * k /\ MAX_LIST args < 2 * f' + 2 * k /\ MAX_LIST vs < 2 * f' + 2 * k /\
                wordLang.cutsets_max live < 2 * f' + 2 * k /\
                match h with NONE => True | SOME (v, (hc, _)) => v < 2 * f' + 2 * k /\ wordLang.max_var hc < 2 * f' + 2 * k end).
  { destruct h as [[v [hc [h1 h2]]]|]; rewrite ?max3_lt_iff, ?MAX_lt_iff in Hm; rewrite ?max3_lt_iff, ?MAX_lt_iff in Hm; tauto. }
  clear Hm. destruct Hm' as (Hm1 & Hm2 & Hm3 & Hm4 & Hm5).
  assert (G : forall P : Prop, P -> P) by auto.
  destruct h as [[v [hc [h1 h2]]]|];
  repeat match goal with
         | H : _ && _ = true |- _ => apply andb_true_iff in H; destruct H
         | H : _ /\ _ |- _ => destruct H
         | H : ⌜_⌝ = true |- _ => apply bool_decide_spec in H
         | H : (_ =? _) = true |- _ => apply N.eqb_eq in H
         end;
  (split; [assumption|]); (split; [assumption|]);
  (split; [rewrite !andb_true_iff; tauto|]); (split; [rewrite ?andb_true_iff; tauto|]); (split; [assumption|]);
  (split;
   [intros x Hx; split; [apply is_phy_var_EVEN; match goal with H : wordLang.every_name is_phy_var live = true |- _ => apply (every_name_dom _ _ _ H Hx) end|];
    split;
    [match goal with H : wordLang.every_name (fun x => 2 * k <=? x) live = true |- _ =>
       pose proof (every_name_dom _ _ _ H Hx) as Hk end; apply N.leb_le in Hk; apply N.div_le_lower_bound; lia
    |unfold wordLang.cutsets_max in Hm4; rewrite MAX_max in Hm4;
     destruct Hx as [Hx|Hx]; apply domain_toAList in Hx; apply MAX_LIST_In' in Hx; lia]|]);
  (split; [match goal with H : args = _ |- _ => rewrite H, MAX_LIST_GENLIST_evens2 in Hm2; exact Hm2 end|]);
  (split; [match goal with H : vs = _ |- _ => rewrite H, MAX_LIST_GENLIST_evens2 in Hm3; exact Hm3 end|]);
  [|exact Logic.I].
  split; [assumption|]. split; [rewrite !andb_true_iff; tauto|]. split; [assumption|]. tauto.
Qed.

Section CallRetHelpers2.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(** [state_rel] for the callee of a returning call. *)
Lemma state_rel_callee ac k f' s T lens envs h args1 ss fs svc sac F S R xs l1 l2 args :
  state_rel ac k 0 0 (wordSem.set_locals_size (SOME 0) (wordSem.set_locals LN (wordSem.push_env envs h s))) T (f' :: lens) 0 ->
  (forall i, i <> k -> FLOOKUP R i = FLOOKUP (regs T) i) ->
  (forall n v, lookup n (wordSem.locals s) = SOME v -> n DIV 2 < k -> FLOOKUP (regs T) (n DIV 2) = SOME v) ->
  (forall n v, lookup n (wordSem.locals s) = SOME v -> k <= n DIV 2 ->
     oEL (F - 1 - (n DIV 2 - k)) (DROP (stack_space T) (stackSem.stack T)) = SOME v) ->
  LENGTH S = LENGTH (stackSem.stack T) -> DROP (stack_space T) S = DROP (stack_space T) (stackSem.stack T) ->
  (forall x, x < sac -> oEL x (DROP (stack_space T - sac) S) = oEL (x + F) (DROP (stack_space T - sac) (stackSem.stack T))) ->
  sac <= F ->
  wordSem.get_vars args s = SOME xs -> args = GENLIST (fun x => 2 * (x + 1)) (LENGTH args) ->
  (exists l, Loc l1 l2 :: xs = args1 ++ l) ->
  LENGTH args1 - k = sac -> sac <= svc -> sac <= stack_space T ->
  fs = (if svc =? 0 then 0 else svc + 1) -> the fs ss = fs -> fs - sac <= stack_space T - sac ->
  state_rel ac k fs svc (wordSem.call_env args1 ss (wordSem.push_env envs h (wordSem.dec_clock s)))
    (set_stack_space (stack_space T - sac - (fs - sac))
       (dec_clock (set_var 0 (Loc l1 l2) (set_regs R (set_stack S (set_stack_space (stack_space T - sac) T))))))
    (f' :: lens) 0.
Proof.
  intros HP HR Hregs Hfr HLS HDS Hmv HsF Egv Hargs [lx Hxs] Hsac Hsv Hss Hfs Hthe Hno.
  assert (Hfs2 : sac <= fs) by (subst fs; destruct (svc =? 0) eqn:E; [apply N.eqb_eq in E|]; lia).
  unfold wordSem.call_env, wordSem.dec_clock, dec_clock, set_var.
  unfold wordSem.push_env in *. change (wordSem.permute (wordSem.set_clock (wordSem.clock s - 1) s)) with (wordSem.permute s).
  destruct (wordSem.env_to_list (SND envs) (wordSem.permute s)) as [el perm] eqn:Eel.
  pose proof HP as HP'.
  assert (OM2 : forall (x : option N) y z, OPTION_MAP2 MAX x y = SOME z -> exists x0 y0, x = SOME x0 /\ y = SOME y0 /\ z = MAX x0 y0).
  { intros [x0|] [y0|] z E; unfold OPTION_MAP2 in E; cbn in E; try discriminate. injection E as <-. eauto. }
  assert (OA2 : forall (x : option N) y z, OPTION_MAP2 N.add x y = SOME z -> exists x0 y0, x = SOME x0 /\ y = SOME y0 /\ z = x0 + y0).
  { intros [x0|] [y0|] z E; unfold OPTION_MAP2 in E; cbn [IS_SOME andb] in E; try discriminate. injection E as <-. eauto. }
  destruct h as [[hv [hc [h1 h2]]]|]; (sr_destr HP'; sr_split; ws_fields; stk_fields; try assumption;
  [ rewrite Hclock; reflexivity
  | lia
  | rewrite HLS; exact Hsl
  | destruct (svc =? 0); exact Hfs
  | apply wf_fromList2
  | unfold stack_size_rel in *; destruct Hssr as (A1 & A2 & A3); split; [intros _; exact Hthe|];
    split; [rewrite A2, HLS; reflexivity|];
    intros sm Hsm; destruct (OM2 _ _ _ Hsm) as (m & w & Em & Ew & ->); destruct (OA2 _ _ _ Ew) as (z & x & Ez & Ex & ->);
    destruct (A3 m Em) as (_ & _ & z' & Ez' & Hz');
    rewrite Ez in Ez'; injection Ez' as <-; rewrite Ex in Hthe |- *; cbn in Hthe; subst x;
    split; [rewrite MAX_max; lia|]; split; [reflexivity|]; exists z; split; [exact Ez|lia]
  | rewrite DROP_DROP_EQ; replace (fs + (stack_space T - sac - (fs - sac) + 0)) with (stack_space T) by lia;
    rewrite HDS, HLS; rewrite DROP_DROP_EQ in Hsr; replace (0 + (stack_space T + 0)) with (stack_space T) in Hsr by lia; exact Hsr
  | intros n v Hn; pose proof Hn as Hn'; rewrite lookup_fromList2' in Hn';
    destruct (decide _) as [(He & Hlt)|]; [|discriminate]; split; [exact He|];
    assert (Hpre : lookup n (fromList2 (Loc l1 l2 :: xs)) = SOME v)
      by (apply (lookup_fromList2_prefix n args1 _ v); split; [apply isPREFIX_iff; exists lx; exact Hxs|exact Hn]);
    destruct (decide (n = 0)) as [->|Hn0];
    [ rewrite lookup_fromList2' in Hpre; rewrite decide_True in Hpre by (split; [reflexivity|rewrite LENGTH_cons'; lia]);
      cbn in Hpre; injection Hpre as <-; replace (0 DIV 2) with 0 by reflexivity;
      rewrite (proj2 (N.ltb_lt 0 k)) by lia; rewrite FLOOKUP_UPDATE, decide_True by reflexivity; reflexivity
    | assert (Hl : lookup n (wordSem.locals s) = SOME v)
        by (apply (get_vars_fromList2_eq_cons args s xs n v l1 l2); split; [rewrite <- Hargs; exact Egv|split; [exact Hpre|exact Hn0]]);
      pose proof (even_div2 n He) as En;
      destruct (n DIV 2 <? k) eqn:Ek;
      [ apply N.ltb_lt in Ek; rewrite FLOOKUP_UPDATE, decide_False by lia; rewrite HR by lia; exact (Hregs n v Hl Ek)
      | apply N.ltb_ge in Ek;
        assert (Hsvc : svc <> 0) by lia;
        assert (Hfs1 : fs = svc + 1) by (rewrite Hfs; apply N.eqb_neq in Hsvc; rewrite Hsvc; reflexivity);
        split; [|lia];
        rewrite oEL_TAKE_lt by lia; rewrite oEL_DROP;
        replace (stack_space T - sac - (fs - sac) + 0 + (fs - 1 - (n DIV 2 - k))) with ((stack_space T - sac) + (sac - 1 - (n DIV 2 - k))) by lia;
        rewrite <- oEL_DROP; rewrite Hmv by lia; rewrite oEL_DROP;
        replace (stack_space T - sac + (sac - 1 - (n DIV 2 - k) + F)) with (stack_space T + (F - 1 - (n DIV 2 - k))) by lia;
        rewrite <- oEL_DROP; exact (Hfr n v Hl Ek) ] ] ]).
Qed.

End CallRetHelpers2.

Section FrameLookup.
Context {a : N}.

(** Galette-only: a variable of the top frame of a [stack_rel] is in the
    top frame of the stack. *)
Lemma stack_rel_frame_lookup k hdl m l0 el (hnd : option (N * (N * N))) (st : list (stack_frame a)) shandler stk len bms f' lens n v :
  stack_rel k hdl (StackFrame m l0 el hnd :: st) shandler stk len bms (f' :: lens) ->
  lookup n (union (fromAList el) (fromAList l0)) = SOME v -> k <= n DIV 2 ->
  n DIV 2 - k < f' /\ oEL ((if hnd is SOME _ then 3 else 0) + f' - (n DIV 2 - k)) stk = SOME v.
Proof.
  intros [_ (abs & Ha & _ & Hrel)] Hl Hk.
  assert (Hframe : forall bits frame, LENGTH frame = f' ->
            (forall n v, ALOOKUP l0 n = SOME v /\ ALOOKUP el n = NONE ->
               adjust_names n < k + LENGTH bits /\ oEL (k + LENGTH bits - (adjust_names n + 1)) bits = SOME false /\
               ALOOKUP (index_list frame k) (n DIV 2) = SOME v) ->
            filter_bitmap bits (index_list frame k) = SOME (MAP_FST adjust_names el, []) ->
            n DIV 2 - k < f' /\ oEL (f' - (n DIV 2 - k + 1)) frame = SOME v).
  { intros bits frame HLf Hl0 Hfb. rewrite lookup_union, !lookup_fromAList in Hl.
    destruct (ALOOKUP el n) as [v'|] eqn:Eel.
    - injection Hl as <-.
      assert (Hm : MEM (n DIV 2, v') (index_list frame k)).
      { apply (filter_bitmap_MEM bits _ (MAP_FST adjust_names el)). split; [exact Hfb|].
        apply ALOOKUP_MEM in Eel. unfold is_true in *. rewrite MEM_In in *. unfold MAP_FST.
        apply (in_map (fun '(x, y) => (adjust_names x, y)) _ _ Eel). }
      pose proof (MEM_index_list_LIM _ _ _ _ Hm) as Hlim. pose proof (MEM_index_list_EL _ _ _ _ Hm) as Hel.
      split; [lia|]. rewrite oEL_EL by lia. rewrite HLf in Hel. f_equal. exact Hel.
    - destruct (Hl0 n v (conj Hl Eel)) as (_ & _ & Hai).
      assert (Hlt : n DIV 2 < LENGTH frame + k).
      { pose proof (ALOOKUP_MEM _ _ _ Hai) as Hm. apply MEM_index_list_LIM in Hm. lia. }
      rewrite ALOOKUP_index_list in Hai by exact Hlt. split; [lia|]. rewrite <- Hai. f_equal. lia. }
  destruct hnd as [[hh [hl1 hl2]]|].
  - destruct stk as [|w0 stk]; [discriminate|]. cbn [abs_stack] in Ha.
    destruct (bool_decide (w0 = Word (n2w 1))); [|discriminate]. cbn [negb] in Ha.
    destruct stk as [|loc [|hv [|w stk]]]; try discriminate.
    destruct (full_read_bitmap bms w) as [bits|]; [|discriminate].
    destruct (negb (LENGTH bits =? f')) eqn:Eb; [discriminate|]. apply negb_false_iff, N.eqb_eq in Eb.
    destruct (LENGTH stk <? f') eqn:El; [discriminate|]. apply N.ltb_ge in El.
    destruct (abs_stack bms st (DROP f' stk) lens) as [ys|]; [|discriminate]. injection Ha as <-.
    cbn [stack_rel_aux] in Hrel. destruct Hrel as (_ & _ & Hl0 & Hfb & _).
    destruct (Hframe bits (TAKE f' stk)) as [Hlt Ho]; [rewrite LENGTH_TAKE_le; lia|exact Hl0|exact Hfb|].
    split; [exact Hlt|]. rewrite oEL_TAKE_lt in Ho by lia.
    rewrite !oEL_cons_pos by lia.
    replace (3 + f' - (n DIV 2 - k) - 1 - 1 - 1 - 1) with (f' - (n DIV 2 - k + 1)) by lia. exact Ho.
  - destruct stk as [|w stk]; [discriminate|]. cbn [abs_stack] in Ha.
    destruct (full_read_bitmap bms w) as [bits|]; [|discriminate].
    destruct (negb (LENGTH bits =? f')) eqn:Eb; [discriminate|]. apply negb_false_iff, N.eqb_eq in Eb.
    destruct (LENGTH stk <? f') eqn:El; [discriminate|]. apply N.ltb_ge in El.
    destruct (abs_stack bms st (DROP f' stk) lens) as [ys|]; [|discriminate]. injection Ha as <-.
    cbn [stack_rel_aux] in Hrel. destruct Hrel as (Hl0 & Hfb & _).
    destruct (Hframe bits (TAKE f' stk)) as [Hlt Ho]; [rewrite LENGTH_TAKE_le; lia|exact Hl0|exact Hfb|].
    split; [exact Hlt|]. rewrite oEL_TAKE_lt in Ho by lia.
    rewrite oEL_cons_pos by lia.
    replace (0 + f' - (n DIV 2 - k) - 1) with (f' - (n DIV 2 - k + 1)) by lia. exact Ho.
Qed.

End FrameLookup.

Lemma lookup_alist_insert_evens {A} (ys : list A) (t : num_map A) n : forall j,
  lookup n (alist_insert (GENLIST (fun x => 2 * (x + j + 1)) (LENGTH ys)) ys t) =
  if decide (EVEN n = true /\ j + 1 <= n DIV 2 /\ n DIV 2 <= j + LENGTH ys) then oEL (n DIV 2 - j - 1) ys else lookup n t.
Proof.
  induction ys as [|y ys IH]; intros j.
  - cbn. rewrite decide_False by (cbn; lia). reflexivity.
  - rewrite LENGTH_cons', N.add_1_r, GENLIST_CONS_aux. cbn [alist_insert].
    replace (GENLIST (fun i => 2 * (SUC i + j + 1)) (LENGTH ys)) with (GENLIST (fun x => 2 * (x + (j + 1) + 1)) (LENGTH ys))
      by (rewrite !GENLIST_seq; apply map_ext; intros; cbv beta; lia).
    rewrite lookup_insert, IH. destruct (decide (n = 2 * (0 + j + 1))) as [->|Hn].
    + rewrite decide_True.
      * replace (2 * (0 + j + 1) DIV 2 - j - 1) with 0 by (rewrite N.mul_comm, N.div_mul by lia; lia). reflexivity.
      * rewrite N.mul_comm, N.div_mul by lia. split; [apply N.even_spec; exists (0 + j + 1); lia|]. lia.
    + destruct (decide (EVEN n = true /\ j + 1 + 1 <= n DIV 2 /\ n DIV 2 <= j + 1 + LENGTH ys)) as [(He & H1 & H2)|Hc].
      * rewrite decide_True by (split; [exact He|lia]). cbn [oEL]. replace (n DIV 2 - j - 1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
        f_equal. lia.
      * rewrite decide_False; [reflexivity|]. intros (He & H1 & H2). apply Hn.
        pose proof (even_div2 n He). assert (n DIV 2 = j + 1) by (apply NNPP; intros C; apply Hc; split; [exact He|lia]). lia.
Qed.

Lemma lookup_alist_insert_evens0 {A} (ys : list A) (t : num_map A) n :
  lookup n (alist_insert (GENLIST (fun x => 2 * (x + 1)) (LENGTH ys)) ys t) =
  if decide (EVEN n = true /\ 1 <= n DIV 2 /\ n DIV 2 <= LENGTH ys) then oEL (n DIV 2 - 1) ys else lookup n t.
Proof.
  pose proof (lookup_alist_insert_evens ys t n 0) as H.
  replace (GENLIST (fun x => 2 * (x + 0 + 1)) (LENGTH ys)) with (GENLIST (fun x => 2 * (x + 1)) (LENGTH ys)) in H
    by (rewrite !GENLIST_seq; apply map_ext; intros; cbv beta; lia).
  rewrite H. destruct (decide (EVEN n = true /\ 0 + 1 <= n DIV 2 <= 0 + LENGTH ys)) as [G|G];
    destruct (decide (EVEN n = true /\ 1 <= n DIV 2 <= LENGTH ys)) as [G'|G'];
    [f_equal; lia|exfalso; apply G'; split; [apply G|lia]|exfalso; apply G; split; [apply G'|lia]|reflexivity].
Qed.

Section ReturnRestore.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(** Galette-only: [state_rel] after a returning call without handler has
    returned and the return values have been copied ([copy_ret_aux]). *)
Lemma state_rel_return_NONE ac k f f' s2 t1 lens m l0 el st ys vs R' S' :
  let nsr := LENGTH vs + 1 - k in
  state_rel ac k 0 0 s2 t1 (f' :: lens) nsr ->
  (forall i, i < LENGTH ys -> if i + 1 <? k then FLOOKUP (regs t1) (i + 1) = SOME (EL i ys)
     else oEL (LENGTH ys - (i + 1)) (DROP (stack_space t1) (stackSem.stack t1)) = SOME (EL i ys)) ->
  wordSem.stack s2 = StackFrame m l0 el NONE :: st ->
  LENGTH ys = LENGTH vs -> vs = GENLIST (fun x => 2 * (x + 1)) (LENGTH vs) -> LENGTH vs < f' + k ->
  f' <> 0 -> f = f' + 1 ->
  (forall n, n IN domain (union (fromAList el) (fromAList l0)) -> EVEN n /\ k <= n DIV 2) ->
  LENGTH S' = LENGTH (stackSem.stack t1) ->
  DROP (f + nsr + stack_space t1) S' = DROP (f + nsr + stack_space t1) (stackSem.stack t1) ->
  (forall i, i <> k -> FLOOKUP R' i = FLOOKUP (regs t1) i) ->
  (forall mm, mm < f - nsr -> EL mm (DROP (nsr + stack_space t1) S') = EL mm (DROP (nsr + stack_space t1) (stackSem.stack t1))) ->
  (forall x, x < nsr -> EL (x + f) (DROP (stack_space t1) S') = EL x (DROP (stack_space t1) (stackSem.stack t1))) ->
  state_rel ac k f f'
    (wordSem.set_vars vs ys (wordSem.set_locals_size m (wordSem.set_stack st (wordSem.set_locals (union (fromAList el) (fromAList l0)) s2))))
    (set_stack_space (stack_space t1 + nsr) (set_regs R' (set_stack S' t1))) lens 0.
Proof.
  intros nsr HR1 Hys Hst HLy Hvs Hlv Hf'0 Hf Hdom HLS HDS HR' Hkeep Hcp.
  pose proof HR1 as HS. sr_destr HS. rewrite Hst in Hssr, Hsr.
  pose proof (stack_rel_cons_LEN_NONE _ _ _ _ _ _ _ _ _ _ _ _ Hsr) as HLEN. rewrite LENGTH_DROP', LENGTH_DROP' in HLEN.
  pose proof (stack_rel_cons_locals_size _ _ _ _ _ _ _ _ _ _ _ _ _ Hsr) as Hthe.
  pose proof (stack_rel_DROP_NONE _ _ _ _ _ _ _ _ _ _ _ _ Hsr) as Hsr2.
  assert (HL1 : stack_space t1 + nsr + f <= LENGTH (stackSem.stack t1)) by lia.
  unfold wordSem.set_vars. sr_split; ws_fields; stk_fields; try assumption.
  - rewrite HLS. exact HL1.
  - rewrite HLS. exact Hsl.
  - rewrite (proj2 (N.eqb_neq f' 0) Hf'0). exact Hf.
  - apply wf_alist_insert, wf_union. split; apply wf_fromAList.
  - unfold stack_size_rel in *. destruct Hssr as (A1 & A2 & A3).
    split; [intros _; destruct m; cbn in Hthe |- *; lia|]. split; [rewrite A2, HLS; reflexivity|].
    intros sm Hsm. destruct (A3 sm Hsm) as (B1 & _ & z & Bz & Bz').
    rewrite (proj1 (dec_clock.stack_size_eq m l0 el st NONE [] [] (0, (0, 0)))) in Bz.
    destruct m as [m0|]; [|unfold OPTION_MAP2 in Bz; cbn in Bz; discriminate]. cbn in Hthe. subst m0.
    destruct (wordSem.stack_size st) as [z0|] eqn:Ez0; [|unfold OPTION_MAP2 in Bz; cbn in Bz; discriminate].
    unfold OPTION_MAP2 in Bz. cbn [IS_SOME THE andb] in Bz. injection Bz as <-.
    rewrite HLS. split; [lia|]. split; [reflexivity|]. exists z0. split; [reflexivity|lia].
  - rewrite !DROP_DROP_EQ in *. replace (f + (stack_space t1 + nsr + 0)) with (f + nsr + stack_space t1) by lia.
    rewrite HDS, HLS. replace (f' + 1 + 0 + (stack_space t1 + nsr)) with (f + nsr + stack_space t1) in Hsr2 by lia.
    exact Hsr2.
  - intros n v Hn. rewrite Hvs, <- HLy, lookup_alist_insert_evens0 in Hn.
    destruct (decide (EVEN n = true /\ 1 <= n DIV 2 <= LENGTH ys)) as [(He & H1 & H2)|Hnv].
    + split; [exact He|]. pose proof (oEL_SOME_EL _ _ _ Hn) as Ev. pose proof (Hys (n DIV 2 - 1) ltac:(lia)) as Hy.
      replace (n DIV 2 - 1 + 1) with (n DIV 2) in Hy by lia. rewrite Ev in Hy.
      destruct (n DIV 2 <? k) eqn:Ek.
      * apply N.ltb_lt in Ek. rewrite HR' by lia. exact Hy.
      * apply N.ltb_ge in Ek. split; [|lia].
        pose proof (oEL_SOME_lt _ _ _ Hy) as Hb. rewrite LENGTH_DROP' in Hb.
        rewrite oEL_TAKE_lt by lia. rewrite oEL_DROP.
        replace (stack_space t1 + nsr + 0 + (f - 1 - (n DIV 2 - k)))
          with (stack_space t1 + ((LENGTH ys - n DIV 2) + f)) by lia.
        rewrite <- oEL_DROP. rewrite oEL_EL by (rewrite LENGTH_DROP', HLS; lia).
        rewrite Hcp by lia. rewrite <- oEL_EL by (rewrite LENGTH_DROP'; lia). exact Hy.
    + assert (Hd : n IN domain (union (fromAList el) (fromAList l0))) by (apply domain_lookup; eauto).
      destruct (Hdom n Hd) as [He Hk2]. split; [exact He|].
      destruct (stack_rel_frame_lookup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsr Hn Hk2) as [Hlt Ho].
      assert (Hgt : LENGTH vs + 1 <= n DIV 2) by (apply NNPP; intros C; apply Hnv; split; [exact He|lia]).
      replace (n DIV 2 <? k) with false by (symmetry; apply N.ltb_ge; lia). split; [|lia].
      rewrite DROP_DROP_EQ in Ho. pose proof (oEL_SOME_lt _ _ _ Ho) as Hb. rewrite LENGTH_DROP' in Hb.
      rewrite oEL_TAKE_lt by lia. rewrite oEL_DROP.
      replace (stack_space t1 + nsr + 0 + (f - 1 - (n DIV 2 - k))) with ((nsr + stack_space t1) + (f - 1 - (n DIV 2 - k))) by lia.
      rewrite <- oEL_DROP. rewrite oEL_EL by (rewrite LENGTH_DROP', HLS; lia).
      rewrite Hkeep by lia. rewrite <- oEL_EL by (rewrite LENGTH_DROP'; lia).
      rewrite oEL_DROP. rewrite oEL_DROP in Ho. rewrite <- Ho. f_equal. lia.
Qed.

End ReturnRestore.

Section StackSteps.
Context {a : N} {c ffi_t : Type}.
Implicit Types (X : stackSem.state a c ffi_t).

Lemma ev_stackargs n F k X :
  use_stack X ->
  evaluate (stack_move n 0 F k (StackAlloc n), X) =
  if stack_space X <? n then (SOME (Halt (Word (n2w 2))), empty_env X)
  else evaluate (stack_move n 0 F k Skip, set_stack_space (stack_space X - n) X).
Proof.
  intros Hu. rewrite evaluate_stack_move_seq, ev_seq, ev_stackalloc, Hu. cbn [negb].
  destruct (stack_space X <? n); reflexivity.
Qed.

Lemma ev_call_ret (rh : prog a) l1 l2 dest' hdl sp X :
  find_code dest' (regs X \\ 0) (code X) = SOME sp ->
  evaluate (Call (SOME (rh, (0, (l1, l2)))) dest' hdl, X) =
  if clock X =? 0 then (SOME TimeOut, empty_env X) else
  match evaluate (sp, dec_clock (set_var 0 (Loc l1 l2) X)) with
  | (SOME (Result x), s2) => if negb (bool_decide (x = Loc l1 l2)) then (SOME Error, s2) else evaluate (rh, s2)
  | (SOME (Exception x), s2) =>
      match hdl with
      | NONE => (SOME (Exception x), s2)
      | SOME (h, (l1', l2')) => if negb (bool_decide (x = Loc l1' l2')) then (SOME Error, s2) else evaluate (h, s2)
      end
  | (NONE, s) => (SOME Error, s)
  | (SOME (Break _), s) => (SOME Error, s)
  | (SOME (Continue _), s) => (SOME Error, s)
  | (res, s) => (res, s)
  end.
Proof.
  intros Hf. rewrite evaluate_eqn. cbn [evaluate_body]. rewrite Hf.
  destruct (clock X =? 0); [reflexivity|]. rewrite fix_clock_evaluate. reflexivity.
Qed.

Lemma call_state_eq X Y v ck : clock X <> 0 ->
  set_stack_space Y (dec_clock (set_var 0 v (set_clock (clock X + ck) X))) =
  set_clock (clock (set_stack_space Y (dec_clock (set_var 0 v X))) + ck) (set_stack_space Y (dec_clock (set_var 0 v X))).
Proof. intros H. destruct X. unfold dec_clock, set_var, set_clock, set_stack_space, set_regs in *. cbn in *. f_equal. lia. Qed.

End StackSteps.

Lemma find_code_preserve {a} dest' (R0 R1 : fmap N (word_loc a)) (C0 C1 : spt (prog a)) sp :
  find_code dest' R0 C0 = SOME sp -> is_true (subspt C0 C1) ->
  (forall r, dest' = inr r -> FLOOKUP R1 r = FLOOKUP R0 r) -> find_code dest' R1 C1 = SOME sp.
Proof.
  destruct dest' as [p|r]; cbn [find_code]; intros Hf Hs HR; pose proof (proj1 (subspt_lookup C0 C1) Hs) as Hs'.
  - apply Hs'. exact Hf.
  - rewrite (HR r eq_refl). destruct (FLOOKUP R0 r) as [[w|l n]|]; try discriminate.
    destruct (n =? 0); [|discriminate]. apply Hs'. exact Hf.
Qed.

Section CallRetOverflow.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(** Galette-only: the result of a returning call whose stack frame does not
    fit. *)
Lemma call_ret_overflow ac k f f' s T lens envs h args1 ss fs prog vs ret_code l1 l2 res s1 (T' : stackSem.state a c ffi_t) :
  state_rel ac k 0 0 (wordSem.set_locals_size (SOME 0) (wordSem.set_locals LN (wordSem.push_env envs NONE s))) T (f' :: lens) 0 ->
  the fs ss = fs -> (match h with NONE => stack_space T < fs | SOME _ => stack_space T < fs + 3 end) ->
  good_dimindex a -> res <> SOME wordSem.Error ->
  (if wordSem.clock s =? 0 then
     (SOME wordSem.TimeOut,
      wordSem.flush_state true
        (wordSem.set_stack_max (wordSem.stack_max (wordSem.call_env args1 ss (wordSem.push_env envs h s)))
           (wordSem.set_stack [] s)))
   else
     let '(r, s2) := wordSem.evaluate (prog, wordSem.call_env args1 ss (wordSem.push_env envs h (wordSem.dec_clock s))) in
     wret_cont vs envs ret_code l1 l2 h r s2) = (res, s1) ->
  ffi T' = wordSem.ffi s ->
  comp_res ac k f f' s res s1 T' (SOME (Halt (Word (n2w 2 : word a)))) lens.
Proof.
  intros HP Hthe Hov Hgd Hres Hev HT'.
  pose proof (callee_stack_max_gt ac k f' s T lens envs h args1 ss fs HP Hthe Hov) as Hgt.
  rewrite bd_true' by (destruct res as [r0|]; [cbn; intros E; injection E as E; apply (compile_result_NOT_2 r0 Hgd), E|discriminate]).
  split; [reflexivity|]. rewrite HT'.
  unfold wordSem.push_env, wordSem.env_to_list in *.
  destruct h as [[hv [hc [h1 h2]]]|];
  (destruct (wordSem.clock s =? 0);
   [ injection Hev as <- <-; unfold wordSem.flush_state; ws_fields; split; [apply isPREFIX_REFL|exact Hgt]
   | match type of Hev with context [wordSem.evaluate (?P, ?S)] => destruct (wordSem.evaluate (P, S)) as [r s2] eqn:Ep end;
     destruct (wret_cont_mono _ _ _ _ _ _ _ _ _ _ Hev Hres) as [M1 M2];
     split;
     [ eapply isPREFIX_TRANS; split; [|exact M1]; exact (clock.evaluate_io_events_mono _ _ _ _ Ep)
     | apply M2; apply (stack_max.evaluate_stack_limit_stack_max _ _ _ _ (conj Ep Hgt)) ] ]).
Qed.

End CallRetOverflow.

Lemma cut_envs_frame_dom {a} (live : wordLang.cutsets) (l : num_map (word_loc a)) envs perm (el' : list (N * word_loc a)) n :
  wordSem.cut_envs live l = SOME envs ->
  MAP FST el' = MAP FST (wordSem.list_rearrange perm (mllist.sort wordSem.key_val_compare (toAList (SND envs)))) ->
  n IN domain (union (fromAList el') (fromAList (toAList (FST envs)))) ->
  n IN domain (FST live) \/ n IN domain (SND live).
Proof.
  unfold wordSem.cut_envs, wordSem.cut_names. intros Hc Hel Hn.
  destruct (classical_dec (domain (FST live) SUBSET domain l)); [|discriminate].
  destruct (classical_dec (domain (SND live) SUBSET domain l)); [|discriminate].
  injection Hc as <-. cbn [FST SND fst snd] in *.
  rewrite domain_union, !domain_fromAList in Hn. unfold pred_set.IN in Hn. destruct Hn as [Hn|Hn].
  - right. cbv beta in Hn. rewrite Hel in Hn. unfold is_true in Hn. rewrite MEM_In in Hn.
    apply in_map_iff in Hn as [[x v] [Ex Hin]]. cbn in Ex. subst x.
    assert (Hm : MEM (n, v) (toAList (inter l (SND live)))).
    { apply (proj1 (mllist.sort_MEM _ wordSem.key_val_compare _)). apply (proj1 (consts.mem_list_rearrange _ _ perm)). unfold is_true; rewrite MEM_In; exact Hin. }
    apply MEM_toAList in Hm. assert (Hd : n IN domain (inter l (SND live))) by (apply domain_lookup; eauto).
    rewrite domain_inter in Hd. apply Hd.
  - left. unfold is_true in Hn. rewrite MEM_In in Hn. apply in_map_iff in Hn as [[x v] [Ex Hin]]. cbn in Ex. subst x.
    assert (Hm : MEM (n, v) (toAList (inter l (FST live)))) by (unfold is_true; rewrite MEM_In; exact Hin).
    apply MEM_toAList in Hm. assert (Hd : n IN domain (inter l (FST live))) by (apply domain_lookup; eauto).
    rewrite domain_inter in Hd. apply Hd.
Qed.

Section ExcRestore.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(** Galette-only: [state_rel] at the start of an exception handler. *)
Lemma state_rel_exc_handler ac k f f' s2 t1 lens l0 l y :
  state_rel ac k 0 0 (push_locals l0 l s2) t1 (f' :: lens) 0 ->
  wordSem.locals s2 = union (fromAList l) (fromAList l0) ->
  FLOOKUP (regs t1) 1 = SOME y ->
  f' <> 0 -> f = f' + 1 ->
  (forall n, n IN domain (wordSem.locals s2) -> EVEN n /\ k <= n DIV 2) ->
  state_rel ac k f f' (wordSem.set_var 2 y s2) t1 lens 0.
Proof.
  intros HR Hl Hy Hf'0 Hf Hdom.
  pose proof HR as HS. unfold push_locals in HS. sr_destr HS. ws_fields.
  pose proof (stack_rel_cons_LEN_NONE _ _ _ _ _ _ _ _ _ _ _ _ Hsr) as HLEN. rewrite !LENGTH_DROP' in HLEN.
  pose proof (stack_rel_cons_locals_size _ _ _ _ _ _ _ _ _ _ _ _ _ Hsr) as Hthe.
  pose proof (stack_rel_DROP_NONE _ _ _ _ _ _ _ _ _ _ _ _ Hsr) as Hsr2.
  unfold wordSem.set_var. sr_split; ws_fields; try assumption.
  - lia.
  - rewrite (proj2 (N.eqb_neq f' 0) Hf'0). exact Hf.
  - apply wf_insert. rewrite Hl. apply wf_union. split; apply wf_fromAList.
  - unfold stack_size_rel in *. destruct Hssr as (A1 & A2 & A3).
    split; [intros _; destruct (wordSem.locals_size s2); cbn in Hthe |- *; lia|]. split; [exact A2|].
    intros sm Hsm. destruct (A3 sm Hsm) as (B1 & _ & z & Bz & Bz').
    rewrite (proj1 (dec_clock.stack_size_eq (wordSem.locals_size s2) l0 l (wordSem.stack s2) NONE [] [] (0, (0, 0)))) in Bz.
    destruct (wordSem.locals_size s2) as [m0|]; [|unfold OPTION_MAP2 in Bz; cbn in Bz; discriminate]. cbn in Hthe. subst m0.
    destruct (wordSem.stack_size (wordSem.stack s2)) as [z0|] eqn:Ez0; [|unfold OPTION_MAP2 in Bz; cbn in Bz; discriminate].
    unfold OPTION_MAP2 in Bz. cbn [IS_SOME THE andb] in Bz. injection Bz as <-.
    split; [lia|]. split; [reflexivity|]. exists z0. split; [reflexivity|lia].
  - rewrite !DROP_DROP_EQ in *. replace (f + (stack_space t1 + 0)) with (f' + 1 + 0 + (stack_space t1 + 0)) by lia. exact Hsr2.
  - intros n v Hn. rewrite lookup_insert in Hn. destruct (decide (n = 2)) as [->|Hn2].
    + injection Hn as <-. split; [reflexivity|]. replace (2 DIV 2) with 1 by reflexivity.
      rewrite (proj2 (N.ltb_lt 1 k)) by lia. exact Hy.
    + assert (Hd : n IN domain (wordSem.locals s2)) by (apply domain_lookup; eauto).
      destruct (Hdom n Hd) as [He Hk2]. split; [exact He|]. rewrite Hl in Hn.
      destruct (stack_rel_frame_lookup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsr Hn Hk2) as [Hlt Ho].
      replace (n DIV 2 <? k) with false by (symmetry; apply N.ltb_ge; lia). split; [|lia].
      rewrite DROP_DROP_EQ in Ho. pose proof (oEL_SOME_lt _ _ _ Ho) as Hb.
      rewrite oEL_TAKE_lt by lia. rewrite oEL_DROP. rewrite oEL_DROP in Ho. rewrite <- Ho. f_equal. lia.
Qed.

End ExcRestore.

Section ReturnRestoreH.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(** Galette-only: as [state_rel_return_NONE], for a call with a handler
    (after [PopHandler]). *)
Lemma state_rel_return_SOME ac k f f' s2 t1 lens m l0 el hh hl1 hl2 st ys vs R' S' :
  let nsr := LENGTH vs + 1 - k in
  state_rel ac k 0 0 s2 t1 (f' :: lens) nsr ->
  (forall i, i < LENGTH ys -> if i + 1 <? k then FLOOKUP (regs t1) (i + 1) = SOME (EL i ys)
     else oEL (LENGTH ys - (i + 1)) (DROP (stack_space t1) (stackSem.stack t1)) = SOME (EL i ys)) ->
  wordSem.stack s2 = StackFrame m l0 el (SOME (hh, (hl1, hl2))) :: st ->
  LENGTH ys = LENGTH vs -> vs = GENLIST (fun x => 2 * (x + 1)) (LENGTH vs) -> LENGTH vs < f' + k ->
  f' <> 0 -> f = f' + 1 ->
  (forall n, n IN domain (union (fromAList el) (fromAList l0)) -> EVEN n /\ k <= n DIV 2) ->
  LENGTH S' = LENGTH (stackSem.stack t1) ->
  DROP (f + 3 + nsr + stack_space t1) S' = DROP (f + 3 + nsr + stack_space t1) (stackSem.stack t1) ->
  (forall i, i <> k -> FLOOKUP R' i = FLOOKUP (regs t1) i) ->
  (forall mm, mm < f + 3 - nsr -> EL mm (DROP (nsr + stack_space t1) S') = EL mm (DROP (nsr + stack_space t1) (stackSem.stack t1))) ->
  (forall x, x < nsr -> EL (x + (f + 3)) (DROP (stack_space t1) S') = EL x (DROP (stack_space t1) (stackSem.stack t1))) ->
  state_rel ac k f f'
    (wordSem.set_vars vs ys (wordSem.set_handler hh (wordSem.set_locals_size m (wordSem.set_stack st
       (wordSem.set_locals (union (fromAList el) (fromAList l0)) s2)))))
    (set_stack_space (stack_space t1 + nsr + 3)
       (set_store Handler (EL (stack_space t1 + nsr + 2) S')
          (set_var k (EL (stack_space t1 + nsr + 2) S')
             (set_stack_space (stack_space t1 + nsr) (set_regs R' (set_stack S' t1)))))) lens 0.
Proof.
  intros nsr HR1 Hys Hst HLy Hvs Hlv Hf'0 Hf Hdom HLS HDS HR' Hkeep Hcp.
  pose proof HR1 as HS. sr_destr HS. rewrite Hst in Hssr, Hsr.
  pose proof (stack_rel_cons_LEN_SOME _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsr) as HLEN. rewrite LENGTH_DROP', LENGTH_DROP' in HLEN.
  pose proof (stack_rel_cons_locals_size _ _ _ _ _ _ _ _ _ _ _ _ _ Hsr) as Hthe.
  pose proof (stack_rel_DROP_SOME _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsr) as Hsr2.
  assert (HL1 : stack_space t1 + nsr + 3 + f <= LENGTH (stackSem.stack t1)) by lia.
  assert (Hw : EL 2 (DROP 0 (DROP (stack_space t1 + nsr) (stackSem.stack t1))) = EL (stack_space t1 + nsr + 2) S').
  { assert (G : EL 2 (DROP (nsr + stack_space t1) S') = EL 2 (DROP (nsr + stack_space t1) (stackSem.stack t1))) by (apply Hkeep; lia).
    rewrite !EL_DROP_add in G. rewrite !EL_DROP_add.
    match goal with |- EL ?i _ = EL ?j _ => replace i with (nsr + stack_space t1 + 2) by lia; replace j with (nsr + stack_space t1 + 2) by lia end.
    symmetry. exact G. }
  unfold wordSem.set_vars, set_store, set_var. sr_split; ws_fields; stk_fields; try assumption.
  - rewrite DOMSUB_FUPDATE. exact Hstore.
  - rewrite FDOM_FUPDATE. left. reflexivity.
  - rewrite HLS. exact HL1.
  - rewrite HLS. exact Hsl.
  - rewrite (proj2 (N.eqb_neq f' 0) Hf'0). exact Hf.
  - apply wf_alist_insert, wf_union. split; apply wf_fromAList.
  - unfold stack_size_rel in *. destruct Hssr as (A1 & A2 & A3).
    split; [intros _; destruct m; cbn in Hthe |- *; lia|]. split; [rewrite A2, HLS; reflexivity|].
    intros sm Hsm. destruct (A3 sm Hsm) as (B1 & _ & z & Bz & Bz').
    rewrite (proj1 (proj2 (dec_clock.stack_size_eq m l0 el st m l0 el (hh, (hl1, hl2))))) in Bz.
    destruct m as [m0|]; [|unfold OPTION_MAP2 in Bz; cbn [IS_SOME andb option_map] in Bz; discriminate]. cbn [the] in Hthe. subst m0.
    destruct (wordSem.stack_size st) as [z0|] eqn:Ez0; [|unfold OPTION_MAP2 in Bz; cbn in Bz; discriminate].
    change (option_map (N.add 3) (SOME (f' + 1))) with (SOME (3 + (f' + 1))) in Bz.
    unfold OPTION_MAP2 in Bz. cbn [IS_SOME THE andb] in Bz. apply some_inj in Bz. subst z.
    rewrite HLS. split; [lia|]. split; [reflexivity|]. exists z0. split; [reflexivity|lia].
  - rewrite FLOOKUP_UPDATE, decide_True by reflexivity. rewrite <- Hw.
    rewrite !DROP_DROP_EQ in *. replace (f + (stack_space t1 + nsr + 3 + 0)) with (f + 3 + nsr + stack_space t1) by lia.
    rewrite HDS, HLS. replace (f' + 4 + (0 + (stack_space t1 + nsr))) with (f + 3 + nsr + stack_space t1) in Hsr2 by lia.
    exact Hsr2.
  - intros n v Hn. rewrite Hvs, <- HLy, lookup_alist_insert_evens0 in Hn.
    destruct (decide (EVEN n = true /\ 1 <= n DIV 2 <= LENGTH ys)) as [(He & H1 & H2)|Hnv].
    + split; [exact He|]. pose proof (oEL_SOME_EL _ _ _ Hn) as Ev. pose proof (Hys (n DIV 2 - 1) ltac:(lia)) as Hy.
      replace (n DIV 2 - 1 + 1) with (n DIV 2) in Hy by lia. rewrite Ev in Hy.
      destruct (n DIV 2 <? k) eqn:Ek.
      * apply N.ltb_lt in Ek. rewrite FLOOKUP_UPDATE, decide_False by lia. rewrite HR' by lia. exact Hy.
      * apply N.ltb_ge in Ek. split; [|lia].
        pose proof (oEL_SOME_lt _ _ _ Hy) as Hb. rewrite LENGTH_DROP' in Hb.
        rewrite oEL_TAKE_lt by lia. rewrite oEL_DROP.
        replace (stack_space t1 + nsr + 3 + 0 + (f - 1 - (n DIV 2 - k)))
          with (stack_space t1 + ((LENGTH ys - n DIV 2) + (f + 3))) by lia.
        rewrite <- oEL_DROP. rewrite oEL_EL by (rewrite LENGTH_DROP', HLS; lia).
        rewrite Hcp by lia. rewrite <- oEL_EL by (rewrite LENGTH_DROP'; lia). exact Hy.
    + assert (Hd : n IN domain (union (fromAList el) (fromAList l0))) by (apply domain_lookup; eauto).
      destruct (Hdom n Hd) as [He Hk2]. split; [exact He|].
      destruct (stack_rel_frame_lookup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsr Hn Hk2) as [Hlt Ho].
      assert (Hgt : LENGTH vs + 1 <= n DIV 2) by (apply NNPP; intros C; apply Hnv; split; [exact He|lia]).
      replace (n DIV 2 <? k) with false by (symmetry; apply N.ltb_ge; lia). split; [|lia].
      rewrite DROP_DROP_EQ in Ho. pose proof (oEL_SOME_lt _ _ _ Ho) as Hb. rewrite LENGTH_DROP' in Hb.
      rewrite oEL_TAKE_lt by lia. rewrite oEL_DROP.
      replace (stack_space t1 + nsr + 3 + 0 + (f - 1 - (n DIV 2 - k))) with ((nsr + stack_space t1) + (3 + f - 1 - (n DIV 2 - k))) by lia.
      rewrite <- oEL_DROP. rewrite oEL_EL by (rewrite LENGTH_DROP', HLS; lia).
      rewrite Hkeep by lia. rewrite <- oEL_EL by (rewrite LENGTH_DROP'; lia).
      rewrite oEL_DROP. rewrite oEL_DROP in Ho. rewrite <- Ho. f_equal. lia.
Qed.

End ReturnRestoreH.

Section PopH.
Context {a : N} {c ffi_t : Type}.
Implicit Types (X : stackSem.state a c ffi_t).

Lemma ev_pophandler_skip k f f' X :
  use_stack X -> use_store X -> stack_space X + 3 <= LENGTH (stackSem.stack X) ->
  evaluate (PopHandler false (k, (f, f')) Skip, X) =
  (NONE, set_stack_space (stack_space X + 3)
           (set_store Handler (EL (stack_space X + 2) (stackSem.stack X))
              (set_var k (EL (stack_space X + 2) (stackSem.stack X)) X))).
Proof.
  intros Hu Hs Hl. unfold PopHandler. cbn [handler_slots].
  rewrite ev_seq, ev_stackload, Hu. cbn [negb].
  replace (stack_space X + 2 <? LENGTH (stackSem.stack X)) with true by (symmetry; apply N.ltb_lt; lia).
  cbv iota beta. rewrite ev_seq. rewrite evaluate_eqn. cbn [evaluate_body]. unfold set_var at 1. stk_fields. rewrite Hs. cbn [negb].
  unfold stackSem.get_var. stk_fields. rewrite FLOOKUP_UPDATE, decide_True by reflexivity. cbv iota beta.
  rewrite ev_seq, ev_stackfree. unfold set_store at 1, set_var at 1. stk_fields. rewrite Hu. cbn [negb].
  replace (LENGTH (stackSem.stack X) <? stack_space X + 3) with false by (symmetry; apply N.ltb_ge; lia).
  cbv iota beta. rewrite ev_skip. reflexivity.
Qed.

End PopH.

Section PopH2.
Context {a : N} {c ffi_t : Type}.
Implicit Types (X : stackSem.state a c ffi_t).

Lemma ev_pophandler_q k (p : prog a) X :
  use_stack X -> use_store X -> stack_space X + 3 <= LENGTH (stackSem.stack X) ->
  evaluate (Seq (StackLoad k 2) (Seq (Set_ Handler k) (Seq (StackFree 3) p)), X) =
  evaluate (p, set_stack_space (stack_space X + 3)
           (set_store Handler (EL (stack_space X + 2) (stackSem.stack X))
              (set_var k (EL (stack_space X + 2) (stackSem.stack X)) X))).
Proof.
  intros Hu Hs Hl.
  rewrite ev_seq, ev_stackload, Hu. cbn [negb].
  replace (stack_space X + 2 <? LENGTH (stackSem.stack X)) with true by (symmetry; apply N.ltb_lt; lia).
  cbv iota beta. rewrite ev_seq. rewrite evaluate_eqn. cbn [evaluate_body]. unfold set_var at 1. stk_fields. rewrite Hs. cbn [negb].
  unfold stackSem.get_var. stk_fields. rewrite FLOOKUP_UPDATE, decide_True by reflexivity. cbv iota beta.
  rewrite ev_seq, ev_stackfree. unfold set_store at 1, set_var at 1. stk_fields. rewrite Hu. cbn [negb].
  replace (LENGTH (stackSem.stack X) <? stack_space X + 3) with false by (symmetry; apply N.ltb_ge; lia).
  cbv iota beta. reflexivity.
Qed.

End PopH2.

Lemma oEL_TAKE_SOME {A} i m (l : list A) v : oEL i (TAKE m l) = SOME v -> oEL i l = SOME v.
Proof.
  intros H. pose proof (oEL_SOME_lt _ _ _ H) as Hl. destruct (N.ltb_spec i m) as [Hi|Hi].
  - rewrite oEL_TAKE_lt in H by exact Hi. exact H.
  - rewrite oEL_TAKE_ge in H by exact Hi. discriminate.
Qed.

Lemma domain_nonempty {A} (t : num_map A) : ⌜domain t = {}⌝ = false -> exists x, x IN domain t.
Proof.
  intros H. apply bdf in H. apply NNPP. intros C. apply H. apply set_ext. intros x. split; [|intros []].
  intros Hx. apply C. exists x. exact Hx.
Qed.

Section CallRet.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "Call_returning" *)
Lemma comp_correct_Call_returning ac vs live ret_code l1 l2 dest args h s :
  (forall y, wordSem.eval_lt y (wordLang.Call (SOME (vs, (live, (ret_code, (l1, l2))))) dest args h, s) -> comp_goal ac y) ->
  comp_goal ac (wordLang.Call (SOME (vs, (live, (ret_code, (l1, l2))))) dest args h, s).
Proof.
  intros IH. goal_intro. cbn [comp] in Hcomp.
  destruct (call_dest dest args (k, (f, f'))) as [q0 dest'] eqn:Ecd.
  destruct (wLive live (bs, n) (k, (f, f'))) as [q1 [bs1 n1]] eqn:Ewl.
  destruct (comp ac false ret_code (bs1, n1) (k, (f, f'))) as [q2 [bs2 n2]] eqn:Ec2.
  pose proof (call_ret_convs k f' vs live ret_code l1 l2 dest args h Hpac Hflat Hmax)
    as (Hargs & Hvs & Hpac2 & Hflat2 & Hmax2 & Hlive & Hla & Hlv & Hhcl).
  wev Hev.
  destruct (wordSem.get_vars args s) as [xs|] eqn:Egv; [|injection Hev as <- _; congruence].
  destruct (wordSem.bad_dest_args dest args) eqn:Ebd; [injection Hev as <- _; congruence|].
  cbn [wordSem.add_ret_loc] in Hev.
  destruct (wordSem.find_code dest (Loc l1 l2 :: xs) (wordSem.code s) (wordSem.state_stack_size s))
    as [[args1 [prog ss]]|] eqn:Efc; [|injection Hev as <- _; congruence].
  destruct (⌜domain (FST live) = {}⌝ || negb (ALL_DISTINCT vs)) eqn:Elv; [injection Hev as <- _; congruence|].
  apply orb_false_iff in Elv as [Elv _].
  destruct (wordSem.cut_envs live (wordSem.locals s)) as [envs|] eqn:Ecut; [|injection Hev as <- _; congruence].
  pose proof H as HS0. sr_destr HS0.
  assert (Hf'0 : f' <> 0).
  { destruct (domain_nonempty _ Elv) as [x Hx]. destruct (Hlive x (or_introl Hx)) as (_ & Hx1 & Hx2).
    intros ->. assert (x DIV 2 < k) by (apply N.Div0.div_lt_upper_bound; lia). lia. }
  assert (Hf : f = f' + 1) by (revert Hff; rewrite (proj2 (N.eqb_neq f' 0) Hf'0); auto).
  destruct (call_dest_lemma ac k f f' s t lens dest args q0 dest' xs (SOME (vs, (live, (ret_code, (l1, l2))))))
    as (t4 & E4 & H4 & HL4 & HS4 & Hfc).
  { split; [rewrite Ebd; discriminate|]. split; [exact H|]. split; [exact Ecd|exact Egv]. }
  destruct (Hfc args1 prog ss Efc) as (bs0 & i0 & bs3 & i3 & fs & sp & Ecp & Hi1 & Hi2 & Hi3 & Hthe & Hfind).
  destruct (wfind_code_props _ _ _ _ _ _ _ Efc) as ((p & ar & Elk) & (lx & Hxs) & HLa1 & Hne).
  destruct (Hcode p prog ar Elk) as (Hpac1 & Hflat1 & _).
  pose proof (dec_clock.get_vars_length_lemma _ _ _ Egv) as HLxs.
  pose proof (evaluate_mono _ _ _ _ E4) as [Hbm4 Hcd4]. pose proof (isPREFIX_LENGTH' _ _ Hbm4) as Hlbm4.
  pose proof (comp_IMP_isPREFIX _ _ _ _ _ _ _ Ec2) as Hp2. cbn [FST fst] in Hp2.
  destruct (wLive_LENGTH live (bs, n) (k, (f, f')) q1 (bs1, n1)) as [HLw1 HLw2]; [split; [exact Ewl|exact Hbs1]|].
  cbn [FST SND fst snd] in HLw1, HLw2.
  destruct (comp_IMP_LENGTH _ _ _ _ _ _ _ (conj Ec2 HLw1)) as [HLc1 HLc2]. cbn [FST SND fst snd] in HLc1, HLc2.
  (* the callee *)
  unfold compile_prog in Ecp. cbv zeta in Ecp.
  match type of Ecp with context [comp ?A ?B ?C ?D ?E] => destruct (comp A B C D E) as [qb [bs4 i4]] eqn:Eqb end.
  injection Ecp as Esp Efs Ebs3 Ei3. subst sp bs3 i3.
  set (sac := LENGTH args1 - k) in *.
  set (svc := MAX (wordLang.max_var prog DIV 2 + 1 - k) sac) in *.
  rewrite Efs in Hfind, Eqb.
  assert (Hsv : sac <= svc) by (unfold svc; rewrite MAX_max; lia).
  assert (Hfs2 : sac <= fs) by (rewrite <- Efs; destruct (svc =? 0) eqn:E; [apply N.eqb_eq in E|]; lia).
  assert (Hsac : stack_arg_count dest' (LENGTH args + 1) k = sac).
  { unfold sac. destruct dest as [pos|]; cbn [call_dest] in Ecd.
    - injection Ecd as <- <-. cbn in HLa1 |- *. lia.
    - destruct (LENGTH args =? 0) eqn:E0.
      + apply N.eqb_eq in E0. injection Ecd as <- <-. cbn in HLa1 |- *. lia.
      + destruct (wReg2 (LAST args) (k, (f, f'))) as [x1 r]. injection Ecd as <- <-. cbn in HLa1 |- *.
        lia. }
  assert (HLa2 : LENGTH args1 <= LENGTH args + 1) by (destruct dest; cbn in HLa1; lia).
  assert (HsF : sac <= f) by (unfold sac; lia).
  assert (Hdr : forall r, dest' = inr r -> r <> 0 /\ r <> k).
  { intros r Er. destruct dest as [pos|]; cbn [call_dest] in Ecd; [injection Ecd as _ <-; discriminate|].
    destruct (LENGTH args =? 0) eqn:E0; [injection Ecd as _ <-; discriminate|]. apply N.eqb_neq in E0.
    unfold wReg2 in Ecd. destruct (LAST args DIV 2 <? k) eqn:Ek; injection Ecd as _ <-; injection Er as <-; [|lia].
    apply N.ltb_lt in Ek. split; [|lia].
    rewrite Hargs in Ek |- *. destruct (LAST_GENLIST_evens (LENGTH args) E0) as [Hl0 Hle].
    pose proof (even_div2 _ Hle). lia. }
  assert (Hnt : (NONE : option (stackSem.result a)) <> SOME TimeOut) by discriminate.
  rewrite wordSem.fix_clock_evaluate in Hev.
  destruct h as [[hv [hc [h1 h2]]]|].
  1:{
  destruct (comp ac false hc (bs2, n2) (k, (f, f'))) as [q4 [bs3 n3]] eqn:Ec4.
  injection Hcomp as <- <- <-.
  destruct Hhcl as (-> & Hpac4 & Hflat4 & Hmax4).
  pose proof (comp_IMP_isPREFIX _ _ _ _ _ _ _ Ec4) as Hp4. cbn [FST fst] in Hp4.
  destruct (comp_IMP_LENGTH _ _ _ _ _ _ _ (conj Ec4 HLc1)) as [HLd1 HLd2]. cbn [FST SND fst snd] in HLd1, HLd2.
  destruct (evaluate_wLive ac k f f' lens live bs n q1 bs1 n1 s t4 envs) as (t5 & E5 & HP5 & H5 & HL5 & HS5 & HG5).
  { split; [exact Ewl|]. split; [intros x Hx; destruct (Hlive x (or_introl Hx)) as (? & ? & _); split; assumption|].
    split; [intros x Hx; destruct (Hlive x (or_intror Hx)) as (? & ? & _); split; assumption|].
    split; [exact H4|]. split; [lia|]. split; [exact Ecut|]. split; [exact Hbs1|]. split; [lia|].
    eapply isPREFIX_TRANS; split; [exact Hp2|]. eapply isPREFIX_TRANS; split; [exact Hp4|].
    eapply isPREFIX_TRANS; split; [exact Hpre|]. apply isPREFIX_DROP; exact Hbm4. }
  pose proof H5 as H5'. sr_destr H5'.
  pose proof (evaluate_mono _ _ _ _ E5) as [Hbm5 Hcd5]. pose proof (isPREFIX_LENGTH' _ _ Hbm5) as Hlbm5.
  cbn [StackHandlerArgs StackArgs handler_slots]. rewrite Hsac.
  (* space for the handler *)
  destruct (stack_space t5 <? 3) eqn:Eov1.
  { apply N.ltb_lt in Eov1. exists 0, (empty_env t5), (SOME (Halt (Word (n2w 2)))). split.
    - rewrite set_clock_add0, (ev_seq_none _ _ _ _ E4), (ev_seq_none _ _ _ _ E5), ev_seq, ev_seq, ev_stackalloc, Hus0.
      cbn [negb]. rewrite (proj2 (N.ltb_lt _ _) Eov1). reflexivity.
    - apply (call_ret_overflow ac k f f' s t5 lens envs (SOME (2, (hc, (h1, h2)))) args1 ss fs prog vs ret_code l1 l2 res s1 _ HP5 Hthe ltac:(cbn; lia) Hgd Hres Hev).
      unfold empty_env. stk_fields. exact Hffi0. }
  apply N.ltb_ge in Eov1.
  assert (Hlc : loc_check (code t5) (h1, h2)).
  { apply (loc_check_SUBSET _ _ (subspt_trans _ _ _ (conj Hcd4 Hcd5))), Hlab. cbn [get_labels].
    cbv [pred_set.UNION pred_set.INSERT pred_set.IN pred_set.EMPTY]. tauto. }
  destruct (evaluate_PushHandler ac k f f' s t5 lens envs 2 hc h1 h2) as (tp & Ep' & Etp & HELp & HGp & HSp & HLp & HPp).
  { split; [exact Eov1|]. split; [exact HP5|exact Hlc]. }
  assert (Htp : clock tp = clock t5 /\ code tp = code t5 /\ bitmaps tp = bitmaps t5 /\ use_stack tp = use_stack t5 /\ ffi tp = ffi t5).
  { rewrite Etp. stk_fields. repeat split. }
  destruct Htp as (Hctp & Hcodetp & Hbmtp & Hustp & Hffitp).
  destruct (stack_space tp <? sac) eqn:Eov2.
  { apply N.ltb_lt in Eov2. exists 0, (empty_env tp), (SOME (Halt (Word (n2w 2)))). split.
    - rewrite set_clock_add0, (ev_seq_none _ _ _ _ E4), (ev_seq_none _ _ _ _ E5), (ev_seq_none _ _ _ _ Ep'), ev_seq.
      rewrite (ev_stackargs _ _ _ _ ltac:(rewrite Hustp; exact Hus0)).
      rewrite (proj2 (N.ltb_lt _ _) Eov2). reflexivity.
    - apply (call_ret_overflow ac k f f' s t5 lens envs (SOME (2, (hc, (h1, h2)))) args1 ss fs prog vs ret_code l1 l2 res s1 _ HP5 Hthe ltac:(cbn; lia) Hgd Hres Hev).
      unfold empty_env. stk_fields. rewrite Hffitp. exact Hffi0. }
  apply N.ltb_ge in Eov2.
  assert (Hustp' : use_stack tp) by (rewrite Hustp; exact Hus0).
  destruct (evaluate_stack_move k sac 0 (set_stack_space (stack_space tp - sac) tp) (f + 3))
    as (T7 & E7 & S7 & R7 & ET7 & HG7 & HL7 & HS7 & HD7 & HEL7).
  { stk_fields. split; [exact Hustp'|]. split; [lia|lia]. }
  cbv zeta in HEL7. stk_fields. subst T7.
  set (T7 := set_regs R7 (set_stack S7 (set_stack_space (stack_space tp - sac) tp))) in *.
  assert (E7' : evaluate (stack_move sac 0 (f + 3) k (StackAlloc sac), tp) = (NONE, T7))
    by (rewrite (ev_stackargs _ _ _ _ Hustp'), (proj2 (N.ltb_ge _ _) Eov2); exact E7).
  assert (HR7 : forall i, i <> k -> FLOOKUP R7 i = FLOOKUP (regs tp) i).
  { intros i Hi. pose proof (HG7 i Hi) as G. unfold stackSem.get_var, T7 in G. stk_fields. exact G. }
  assert (Hfind7 : find_code dest' (regs T7 \\ 0) (code T7) = SOME (Seq (StackAlloc (fs - sac)) qb)).
  { apply (find_code_preserve dest' (regs t4) _ (code t4)); [exact Hfind|unfold T7; stk_fields; rewrite Hcodetp; exact Hcd5|].
    intros r Er. destruct (Hdr r Er) as [Hr0 Hrk]. unfold T7. stk_fields. rewrite DOMSUB_FLOOKUP_THM.
    rewrite decide_False by congruence. rewrite HR7 by exact Hrk.
    pose proof (HGp r Hrk) as G. unfold stackSem.get_var in G. rewrite G.
    pose proof (HG5 r Hrk) as G2. unfold stackSem.get_var in G2. exact G2. }
  assert (Hc7 : clock T7 = wordSem.clock s) by (unfold T7; stk_fields; congruence).
  set (CALL := Call (SOME (Seq Skip (copy_ret false true (k, (f, f')) vs (PopHandler false (k, (f, f')) q2)), (0, (l1, l2)))) dest' (SOME (q4, (h1, h2)))).
  assert (Epre : forall ck, evaluate (Seq q0 (Seq q1 (Seq (PushHandler false h1 h2 (k, (f, f'))) (Seq (stack_move sac 0 (f + 3) k (StackAlloc sac))
                    (Seq Skip CALL)))), set_clock (clock t + ck) t) =
                  evaluate (CALL, set_clock (clock T7 + ck) T7)).
  { intros ck. rewrite (ev_seq_none _ _ _ _ (evaluate_add_clock ck _ _ _ _ (conj E4 Hnt))).
    rewrite (ev_seq_none _ _ _ _ (evaluate_add_clock ck _ _ _ _ (conj E5 Hnt))).
    rewrite (ev_seq_none _ _ _ _ (evaluate_add_clock ck _ _ _ _ (conj Ep' Hnt))).
    rewrite (ev_seq_none _ _ _ _ (evaluate_add_clock ck _ _ _ _ (conj E7' Hnt))).
    rewrite (ev_seq_none _ _ _ _ (ev_skip _)). reflexivity. }
  destruct (wordSem.clock s =? 0) eqn:Ec0.
  { injection Hev as <- <-. apply N.eqb_eq in Ec0.
    exists 0, (empty_env (set_clock (clock T7 + 0) T7)), (SOME TimeOut). split.
    - rewrite Epre. unfold CALL. rewrite (ev_call_ret _ _ _ _ _ _ (set_clock (clock T7 + 0) T7) Hfind7). stk_fields.
      rewrite Hc7, Ec0. reflexivity.
    - cbn [option_map compile_result]. rewrite bd_neq_false.
      unfold wordSem.flush_state, empty_env, T7. ws_fields. stk_fields. split; [rewrite Hffitp; symmetry; exact Hffi0|lia]. }
  apply N.eqb_neq in Ec0.
  set (hnd := SOME (2, (hc, (h1, h2)))) in *.
  destruct (wordSem.evaluate (prog, wordSem.call_env args1 ss (wordSem.push_env envs hnd (wordSem.dec_clock s)))) as [r s2] eqn:Ep.
  change (wret_cont vs envs ret_code l1 l2 hnd r s2 = (res, s1)) in Hev.
  assert (Hev' : (if wordSem.clock s =? 0 then
       (SOME wordSem.TimeOut, wordSem.flush_state true
          (wordSem.set_stack_max (wordSem.stack_max (wordSem.call_env args1 ss (wordSem.push_env envs hnd s))) (wordSem.set_stack [] s)))
     else let '(r, s2) := wordSem.evaluate (prog, wordSem.call_env args1 ss (wordSem.push_env envs hnd (wordSem.dec_clock s))) in
       wret_cont vs envs ret_code l1 l2 hnd r s2) = (res, s1))
    by (rewrite (proj2 (N.eqb_neq _ _) Ec0), Ep; exact Hev).
  assert (Ecall : forall ck, evaluate (CALL, set_clock (clock T7 + ck) T7) =
                  match evaluate (Seq (StackAlloc (fs - sac)) qb, dec_clock (set_var 0 (Loc l1 l2) (set_clock (clock T7 + ck) T7))) with
                  | (SOME (Result x), s2) => if negb (bool_decide (x = Loc l1 l2)) then (SOME Error, s2)
                                             else evaluate (Seq Skip (copy_ret false true (k, (f, f')) vs (PopHandler false (k, (f, f')) q2)), s2)
                  | (SOME (Exception x), s2) => if negb (bool_decide (x = Loc h1 h2)) then (SOME Error, s2) else evaluate (q4, s2)
                  | (NONE, s) => (SOME Error, s)
                  | (SOME (Break _), s) => (SOME Error, s)
                  | (SOME (Continue _), s) => (SOME Error, s)
                  | (res, s) => (res, s)
                  end).
  { intros ck. unfold CALL. rewrite (ev_call_ret _ _ _ _ _ _ (set_clock (clock T7 + ck) T7) Hfind7). stk_fields.
    replace (clock T7 + ck =? 0) with false by (symmetry; apply N.eqb_neq; lia). reflexivity. }
  assert (HsT7 : stack_space T7 = stack_space tp - sac) by (unfold T7; stk_fields; reflexivity).
  destruct (stack_space T7 <? fs - sac) eqn:Eov3.
  { apply N.ltb_lt in Eov3. exists 0. eexists. eexists. split.
    - rewrite Epre, Ecall, ev_seq, ev_stackalloc. unfold dec_clock, set_var. stk_fields.
      unfold T7 at 1. stk_fields. rewrite Hustp'. cbn [negb].
      replace (stack_space T7 <? fs - sac) with true by (symmetry; apply N.ltb_lt; exact Eov3). reflexivity.
    - apply (call_ret_overflow ac k f f' s t5 lens envs hnd args1 ss fs prog vs ret_code l1 l2 res s1 _ HP5 Hthe ltac:(cbn; lia) Hgd Hres Hev').
      unfold empty_env, dec_clock, set_var, T7. stk_fields. rewrite Hffitp. exact Hffi0. }
  apply N.ltb_ge in Eov3.
  set (T8 := set_stack_space (stack_space T7 - (fs - sac)) (dec_clock (set_var 0 (Loc l1 l2) T7))).
  assert (HT8 : state_rel ac k fs svc (wordSem.call_env args1 ss (wordSem.push_env envs hnd (wordSem.dec_clock s))) T8 (f' :: lens) 0).
  { apply (state_rel_callee ac k f' s tp lens envs hnd args1 ss fs svc sac (f + 3) S7 R7 xs l1 l2 args HPp HR7).
    - intros n0 v Hl Hkn. destruct (Hloc0 n0 v Hl) as [_ G]. rewrite (proj2 (N.ltb_lt _ _) Hkn) in G.
      pose proof (HGp (n0 DIV 2) ltac:(lia)) as G2. unfold stackSem.get_var in G2. rewrite G2. exact G.
    - intros n0 v Hl Hkn. destruct (Hloc0 n0 v Hl) as [_ G]. rewrite (proj2 (N.ltb_ge _ _) Hkn) in G.
      destruct G as [G Gk]. apply oEL_TAKE_SOME in G. rewrite N.add_0_r in G.
      pose proof (oEL_SOME_lt _ _ _ G) as Gb. rewrite LENGTH_DROP' in Gb.
      rewrite oEL_EL in G by (rewrite LENGTH_DROP'; lia).
      rewrite HELp in G by lia. rewrite <- oEL_EL in G by (rewrite LENGTH_DROP'; lia).
      replace (f + 3 - 1 - (n0 DIV 2 - k)) with (f - 1 - (n0 DIV 2 - k) + 3) by lia. exact G.
    - rewrite HL7. reflexivity.
    - rewrite HS7 in HD7. stk_fields. replace (stack_space tp - sac + 0 + sac) with (stack_space tp) in HD7 by lia. exact HD7.
    - intros x Hx. rewrite HS7 in HEL7. stk_fields. rewrite !N.add_0_r in HEL7.
      rewrite !oEL_EL by (rewrite LENGTH_DROP'; try rewrite <- HL7; stk_fields; lia). rewrite HEL7 by exact Hx. reflexivity.
    - lia.
    - exact Egv.
    - exact Hargs.
    - exists lx. exact Hxs.
    - reflexivity.
    - exact Hsv.
    - exact Eov2.
    - symmetry. exact Efs.
    - exact Hthe.
    - rewrite <- HsT7. exact Eov3. }
  assert (Hr : r <> SOME wordSem.Error) by (intros ->; injection Hev as <- _; congruence).
  pose proof (evaluate_mono _ _ _ _ Ep') as [Hbmp Hcdp].
  pose proof (evaluate_mono _ _ _ _ E7') as [Hbm7 Hcd7].
  assert (Hbm8 : bitmaps T8 = bitmaps T7) by reflexivity.
  assert (Hcd8 : code T8 = code T7) by reflexivity.
  destruct (IH (prog, wordSem.call_env args1 ss (wordSem.push_env envs hnd (wordSem.dec_clock s))))
    with k fs svc r s2 T8 bs0 i0 bs4 i4 qb (f' :: lens) as (ck & t1 & res1 & Eq1 & HRc).
  { right. cbn [snd]. unfold hnd, wordSem.call_env, wordSem.push_env, wordSem.env_to_list, wordSem.dec_clock. ws_fields.
    split; [reflexivity|]. left. lia. }
  { split; [exact Ep|]. split; [exact Hr|]. split; [exact HT8|]. split; [exact Hpac1|]. split; [exact Hflat1|].
    split; [exact Eqb|]. split; [exact Hi1|].
    pose proof (isPREFIX_LENGTH' _ _ Hbm7) as Hlbm7. pose proof (isPREFIX_LENGTH' _ _ Hbmp) as Hlbmp.
    rewrite Hbm8. split; [lia|]. split.
    - eapply isPREFIX_TRANS; split; [exact Hi3|]. apply isPREFIX_DROP.
      eapply isPREFIX_TRANS; split; [exact Hbm4|]. eapply isPREFIX_TRANS; split; [exact Hbm5|].
      eapply isPREFIX_TRANS; split; [exact Hbmp|exact Hbm7].
    - split.
      + pose proof (find_code_IMP_get_labels _ _ _ _ Hfind) as Hgl. intros z Hz. rewrite Hcd8.
        apply (loc_check_SUBSET _ _ Hcd7), (loc_check_SUBSET _ _ Hcdp), (loc_check_SUBSET _ _ Hcd5), Hgl. cbn [get_labels]. right. exact Hz.
      + unfold svc. pose proof (N.div_mod (wordLang.max_var prog) 2 ltac:(lia)) as D1.
        pose proof (N.mod_lt (wordLang.max_var prog) 2 ltac:(lia)) as D2. rewrite MAX_max. lia. }
  assert (Ecb : forall ck', evaluate (Seq (StackAlloc (fs - sac)) qb, dec_clock (set_var 0 (Loc l1 l2) (set_clock (clock T7 + ck') T7))) =
                            evaluate (qb, set_clock (clock T8 + ck') T8)).
  { intros ck'. rewrite ev_seq, ev_stackalloc. unfold dec_clock at 1, set_var at 1. stk_fields.
    unfold T7 at 1. stk_fields. rewrite Hustp'. cbn [negb].
    replace (stack_space T7 <? fs - sac) with false by (symmetry; apply N.ltb_ge; exact Eov3).
    unfold T8. rewrite <- call_state_eq by lia. reflexivity. }
  assert (Hhcall : wordSem.handler (wordSem.call_env args1 ss (wordSem.push_env envs hnd (wordSem.dec_clock s))) = LENGTH (wordSem.stack s))
    by (unfold hnd, wordSem.call_env, wordSem.push_env, wordSem.env_to_list, wordSem.dec_clock; ws_fields; reflexivity).
  destruct (decide (OPTION_MAP compile_result r = res1)) as [<-|Hne1].
  2:{ rewrite bd_true' in HRc by exact Hne1. destruct HRc as (-> & Hio1 & Hsl1).
      exists ck, t1, (SOME (Halt (Word (n2w 2)))). split.
      - rewrite Epre, Ecall, Ecb, Eq1. reflexivity.
      - rewrite bd_true' by (destruct res as [r0|]; [cbn; intros E; injection E as E; apply (compile_result_NOT_2 r0 Hgd), E|discriminate]).
        destruct (wret_cont_mono _ _ _ _ _ _ _ _ _ _ Hev Hres) as [M1 M2].
        split; [reflexivity|]. split; [eapply isPREFIX_TRANS; split; [exact Hio1|exact M1]|apply M2; exact Hsl1]. }
  rewrite bd_neq_false in HRc.
  destruct r as [[x ys|x y|bn|cn| | |fe|]|]; unfold wret_cont in Hev;
    try (injection Hev as <- _; congruence);
    try (match type of Hev with (SOME ?R, _) = _ =>
           injection Hev as <- <-; exists ck, t1, (OPTION_MAP compile_result (SOME R)); split;
           [rewrite Epre, Ecall, Ecb, Eq1; reflexivity|rewrite bd_neq_false; exact HRc] end).
  - (* Result *)
    destruct (negb ⌜x = Loc l1 l2⌝ || negb (LENGTH ys =? LENGTH vs)) eqn:Ex; [injection Hev as <- _; congruence|].
    apply orb_false_iff in Ex as [Ex1 Ex2]. apply negb_false_iff in Ex1, Ex2. apply bool_decide_spec in Ex1. subst x.
    apply N.eqb_eq in Ex2.
    pose proof (stack_swap.evaluate_stack_swap prog (wordSem.call_env args1 ss (wordSem.push_env envs hnd (wordSem.dec_clock s)))) as Hsw.
    rewrite Ep in Hsw. destruct Hsw as (Hkey & Hhnd & _). rewrite Hhcall in Hhnd.
    unfold hnd, wordSem.call_env, wordSem.push_env, wordSem.env_to_list, wordSem.dec_clock in Hkey. ws_fields.
    destruct (wordSem.stack s2) as [|[m l0' el' hnd'] st] eqn:Est2; [cbn in Hkey; contradiction|].
    destruct hnd' as [hnd'|]; cbn [stack_swap.s_key_eq stack_swap.s_frame_key_eq] in Hkey; [|tauto].
    destruct Hkey as (_ & Hmf & <- & <- & <-).
    destruct (wordSem.pop_env s2) as [s3|] eqn:Epop; [|injection Hev as <- _; congruence].
    unfold wordSem.pop_env in Epop. rewrite Est2 in Epop. injection Epop as <-.
    destruct (⌜_⌝) eqn:Edom in Hev; [|injection Hev as <- _; congruence].
    set (s3 := wordSem.set_vars vs ys _) in Hev.
    cbn [option_map compile_result] in HRc. destruct HRc as [HR1 Hys].
    replace (LENGTH ys - (k - 1)) with (LENGTH vs + 1 - k) in HR1 by lia.
    pose proof HR1 as HS1. sr_destr HS1. rewrite Est2 in Hsr1.
    pose proof (stack_rel_cons_LEN_SOME _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsr1) as HLEN. rewrite !LENGTH_DROP' in HLEN.
    destruct (evaluate_copy_ret_aux k (f + 3) (LENGTH vs + 1 - k) t1) as (t' & Ecr & S' & R' & Et' & HLS' & HSS' & HDS' & HG' & Hkeep & Hcp).
    { split; [exact Hus1|]. split; [lia|lia]. }
    cbv zeta in Hcp. subst t'. stk_fields.
    set (T9 := set_stack_space (stack_space t1 + (LENGTH vs + 1 - k) + 3)
       (set_store Handler (EL (stack_space t1 + (LENGTH vs + 1 - k) + 2) S')
          (set_var k (EL (stack_space t1 + (LENGTH vs + 1 - k) + 2) S')
             (set_stack_space (stack_space t1 + (LENGTH vs + 1 - k)) (set_regs R' (set_stack S' t1)))))).
    assert (HT9 : state_rel ac k f f' s3 T9 lens 0).
    { apply (state_rel_return_SOME ac k f f' s2 t1 lens _ _ el' _ h1 h2 st ys vs R' S' HR1 Hys Est2 Ex2 Hvs ltac:(lia) Hf'0 Hf).
      - intros n0 Hn0. destruct (Hlive n0 (cut_envs_frame_dom _ _ _ _ _ _ Ecut (eq_sym Hmf) Hn0)) as (? & ? & _). split; assumption.
      - exact HLS'.
      - exact HDS'.
      - intros i Hi. pose proof (HG' i Hi) as G. unfold stackSem.get_var in G. stk_fields. exact G.
      - exact Hkeep.
      - exact Hcp. }
    pose proof (evaluate_mono _ _ _ _ Eq1) as [Hbmq Hcdq]. stk_fields.
    pose proof (wordSem.evaluate_clock _ _ _ _ Ep) as [Hck2 Htd2].
    assert (Hcd9 : is_true (subspt (code t) (code T9))).
    { unfold T9. stk_fields. rewrite <- Hcodetp in Hcd5.
      apply (subspt_trans _ _ _ (conj Hcd4 (subspt_trans _ _ _ (conj Hcd5 (subspt_trans _ _ _ (conj Hcd7 Hcdq)))))). }
    assert (Hbm9 : is_true (isPREFIX (bitmaps t) (bitmaps T9))).
    { unfold T9. stk_fields. eapply isPREFIX_TRANS; split; [exact Hbm4|]. eapply isPREFIX_TRANS; split; [exact Hbm5|].
      eapply isPREFIX_TRANS; split; [exact Hbmp|]. eapply isPREFIX_TRANS; split; [exact Hbm7|exact Hbmq]. }
    destruct (IH (ret_code, s3)) with k f f' res s1 T9 bs1 n1 bs2 n2 q2 lens as (ck' & t2 & res2 & Eq2 & HR2).
    { right. cbn [snd]. unfold s3, wordSem.set_vars. ws_fields.
      unfold hnd, wordSem.call_env, wordSem.push_env, wordSem.env_to_list, wordSem.dec_clock in Hck2, Htd2. ws_fields.
      split; [exact Htd2|]. left. lia. }
    { split; [exact Hev|]. split; [exact Hres|]. split; [exact HT9|]. split; [exact Hpac2|]. split; [exact Hflat2|].
      split; [exact Ec2|]. split; [exact HLw1|]. pose proof (isPREFIX_LENGTH' _ _ Hbm9) as Hlbm9. split; [lia|].
      split; [rewrite <- HLw2; eapply isPREFIX_TRANS; split; [exact Hp4|]; eapply isPREFIX_TRANS; split; [exact Hpre|apply isPREFIX_DROP; exact Hbm9]|].
      split; [|exact Hmax2].
      intros z Hz. apply (loc_check_SUBSET _ _ Hcd9), Hlab.
      assert (Hz2 : get_labels (copy_ret false true (k, (f, f')) vs (PopHandler false (k, (f, f')) q2)) z)
        by (rewrite get_labels_copy_ret; unfold PopHandler; cbn [get_labels]; cbv [pred_set.UNION pred_set.INSERT pred_set.IN pred_set.EMPTY] in *; tauto).
      cbn [get_labels] in Hz2 |- *. cbv [pred_set.UNION pred_set.INSERT pred_set.IN pred_set.EMPTY] in *. tauto. }
    exists (ck + ck'), t2, res2. split.
    + rewrite Epre, Ecall, Ecb.
      assert (HnT1 : SOME (Result (Loc l1 l2 : word_loc a)) <> SOME TimeOut) by discriminate.
      pose proof (evaluate_add_clock ck' _ _ _ _ (conj Eq1 HnT1)) as Ea. stk_fields.
      rewrite set_clock_set_clock, <- N.add_assoc in Ea. rewrite Ea. cbn [option_map compile_result]. cbv iota beta.
      rewrite bool_decide_eq_true_2 by reflexivity. cbn [negb].
      rewrite (ev_seq_none _ _ _ _ (ev_skip _)), (evaluate_copy_ret_Seq' true k f f' vs (PopHandler false (k, (f, f')) q2)).
      cbv zeta. unfold num_stack_ret.
      rewrite ev_seq, evaluate_copy_ret_aux_clock, Ecr. cbn [PAIR_MAP I FST SND fst snd]. cbv iota beta.
      rewrite evaluate_SeqStackFree by (stk_fields; split; [exact Hus1|lia]).
      rewrite ev_seq, ev_stackfree. stk_fields. rewrite Hus1. cbn [negb].
      replace (LENGTH S' <? stack_space t1 + (LENGTH vs + 1 - k)) with false by (symmetry; apply N.ltb_ge; lia).
      cbv iota beta. unfold PopHandler. cbn [handler_slots].
      rewrite ev_pophandler_q by (stk_fields; first [exact Hus1|exact Hust1|lia]).
      exact Eq2.
    + assert (Hh3 : wordSem.handler s3 = wordSem.handler s) by (unfold s3, wordSem.set_vars; ws_fields; reflexivity).
      rewrite Hh3 in HR2. exact HR2.
  - (* Exception *)
    unfold hnd in Hev. cbv iota beta in Hev.
    destruct (negb ⌜x = Loc h1 h2⌝) eqn:Ex; [injection Hev as <- _; congruence|].
    apply negb_false_iff, bool_decide_spec in Ex. subst x.
    destruct (⌜_⌝) eqn:Edom in Hev; [|injection Hev as <- _; congruence].
    cbn [option_map compile_result] in HRc. destruct HRc as (l0 & l & HR0 & HRl & HRy).
    rewrite Hhcall, <- (state_rel_IMP_LENGTH _ _ _ _ _ _ _ _ H) in HR0.
    rewrite LASTN_MORE in HR0 by (rewrite LENGTH_cons'; lia).
    pose proof (stack_swap.evaluate_stack_swap prog (wordSem.call_env args1 ss (wordSem.push_env envs hnd (wordSem.dec_clock s)))) as Hsw.
    rewrite Ep in Hsw. destruct Hsw as (_ & e0 & e & nn & ls & m & lss & Hlast & _ & (Hmf & Hloc2) & _ & Hhnd & _).
    rewrite Hhcall in Hlast. unfold hnd, wordSem.call_env, wordSem.push_env, wordSem.env_to_list, wordSem.dec_clock in Hlast.
    ws_fields. rewrite LASTN_MORE in Hlast by (rewrite LENGTH_cons'; lia).
    injection Hlast as Em Ee0 Ee Enn Els. subst e0 e nn. cbn in Hhnd.
    assert (HT1 : state_rel ac k f f' (wordSem.set_var 2 y s2) t1 lens 0).
    { apply (state_rel_exc_handler ac k f f' s2 t1 lens l0 l y HR0 HRl HRy Hf'0 Hf).
      intros n0 Hn0. rewrite Hloc2 in Hn0.
      destruct (Hlive n0 (cut_envs_frame_dom _ _ _ _ _ _ Ecut (eq_sym Hmf) Hn0)) as (? & ? & _). split; assumption. }
    pose proof (evaluate_mono _ _ _ _ Eq1) as [Hbmq Hcdq]. stk_fields.
    pose proof (wordSem.evaluate_clock _ _ _ _ Ep) as [Hck2 Htd2].
    assert (Hcd1 : is_true (subspt (code t) (code t1))).
    { rewrite <- Hcodetp in Hcd5.
      apply (subspt_trans _ _ _ (conj Hcd4 (subspt_trans _ _ _ (conj Hcd5 (subspt_trans _ _ _ (conj Hcd7 Hcdq)))))). }
    assert (Hbm1' : is_true (isPREFIX (bitmaps t) (bitmaps t1))).
    { eapply isPREFIX_TRANS; split; [exact Hbm4|]. eapply isPREFIX_TRANS; split; [exact Hbm5|].
      eapply isPREFIX_TRANS; split; [exact Hbmp|]. eapply isPREFIX_TRANS; split; [exact Hbm7|exact Hbmq]. }
    destruct (IH (hc, wordSem.set_var 2 y s2)) with k f f' res s1 t1 bs2 n2 bs3 n3 q4 lens as (ck' & t2 & res2 & Eq2 & HR2).
    { right. cbn [snd]. unfold wordSem.set_var. ws_fields.
      unfold hnd, wordSem.call_env, wordSem.push_env, wordSem.env_to_list, wordSem.dec_clock in Hck2, Htd2. ws_fields.
      split; [exact Htd2|]. left. lia. }
    { split; [exact Hev|]. split; [exact Hres|]. split; [exact HT1|]. split; [exact Hpac4|]. split; [exact Hflat4|].
      split; [exact Ec4|]. split; [exact HLc1|]. pose proof (isPREFIX_LENGTH' _ _ Hbm1') as Hlbm1. split; [lia|].
      split; [rewrite <- HLc2, <- HLw2; eapply isPREFIX_TRANS; split; [exact Hpre|apply isPREFIX_DROP; exact Hbm1']|].
      split; [|exact Hmax4].
      intros z Hz. apply (loc_check_SUBSET _ _ Hcd1), Hlab.
      cbn [get_labels]. cbv [pred_set.UNION pred_set.INSERT pred_set.IN pred_set.EMPTY] in *. tauto. }
    exists (ck + ck'), t2, res2. split.
    + rewrite Epre, Ecall, Ecb.
      assert (HnT1 : SOME (Exception (Loc h1 h2 : word_loc a)) <> SOME TimeOut) by discriminate.
      pose proof (evaluate_add_clock ck' _ _ _ _ (conj Eq1 HnT1)) as Ea. stk_fields.
      rewrite set_clock_set_clock, <- N.add_assoc in Ea. rewrite Ea. cbn [option_map compile_result]. cbv iota beta.
      rewrite bool_decide_eq_true_2 by reflexivity. cbn [negb]. exact Eq2.
    + assert (Hh3 : wordSem.handler (wordSem.set_var 2 y s2) = wordSem.handler s) by (unfold wordSem.set_var; ws_fields; exact Hhnd).
      rewrite Hh3 in HR2. exact HR2.
  }
  injection Hcomp as <- <- <-.
  destruct (evaluate_wLive ac k f f' lens live bs n q1 bs1 n1 s t4 envs) as (t5 & E5 & HP5 & H5 & HL5 & HS5 & HG5).
  { split; [exact Ewl|]. split; [intros x Hx; destruct (Hlive x (or_introl Hx)) as (? & ? & _); split; assumption|].
    split; [intros x Hx; destruct (Hlive x (or_intror Hx)) as (? & ? & _); split; assumption|].
    split; [exact H4|]. split; [lia|]. split; [exact Ecut|]. split; [exact Hbs1|]. split; [lia|].
    eapply isPREFIX_TRANS; split; [exact Hp2|]. eapply isPREFIX_TRANS; split; [exact Hpre|]. apply isPREFIX_DROP; exact Hbm4. }
  pose proof H5 as H5'. sr_destr H5'.
  pose proof (evaluate_mono _ _ _ _ E5) as [Hbm5 Hcd5]. pose proof (isPREFIX_LENGTH' _ _ Hbm5) as Hlbm5.
  cbn [StackArgs]. rewrite Hsac.
  destruct (stack_space t5 <? sac) eqn:Eov2.
  { apply N.ltb_lt in Eov2. exists 0, (empty_env t5), (SOME (Halt (Word (n2w 2)))). split.
    - rewrite set_clock_add0, (ev_seq_none _ _ _ _ E4), (ev_seq_none _ _ _ _ E5), ev_seq, (ev_stackargs _ _ _ _ Hus0).
      rewrite (proj2 (N.ltb_lt _ _) Eov2). reflexivity.
    - apply (call_ret_overflow ac k f f' s t5 lens envs NONE args1 ss fs prog vs ret_code l1 l2 res s1 _ HP5 Hthe ltac:(cbn; lia) Hgd Hres Hev).
      unfold empty_env. stk_fields. exact Hffi0. }
  apply N.ltb_ge in Eov2.
  destruct (evaluate_stack_move k sac 0 (set_stack_space (stack_space t5 - sac) t5) f)
    as (T7 & E7 & S7 & R7 & ET7 & HG7 & HL7 & HS7 & HD7 & HEL7).
  { stk_fields. split; [exact Hus0|]. split; [lia|exact HsF]. }
  cbv zeta in HEL7. stk_fields. subst T7.
  set (T7 := set_regs R7 (set_stack S7 (set_stack_space (stack_space t5 - sac) t5))) in *.
  assert (E7' : evaluate (stack_move sac 0 f k (StackAlloc sac), t5) = (NONE, T7))
    by (rewrite (ev_stackargs _ _ _ _ Hus0), (proj2 (N.ltb_ge _ _) Eov2); exact E7).
  assert (HR7 : forall i, i <> k -> FLOOKUP R7 i = FLOOKUP (regs t5) i).
  { intros i Hi. pose proof (HG7 i Hi) as G. unfold stackSem.get_var, T7 in G. stk_fields. exact G. }
  assert (Hfind7 : find_code dest' (regs T7 \\ 0) (code T7) = SOME (Seq (StackAlloc (fs - sac)) qb)).
  { apply (find_code_preserve dest' (regs t4) _ (code t4)); [exact Hfind|unfold T7; stk_fields; exact Hcd5|].
    intros r Er. destruct (Hdr r Er) as [Hr0 Hrk]. unfold T7. stk_fields. rewrite DOMSUB_FLOOKUP_THM.
    rewrite decide_False by congruence. rewrite HR7 by exact Hrk.
    pose proof (HG5 r Hrk) as G. unfold stackSem.get_var in G. exact G. }
  assert (Hc7 : clock T7 = wordSem.clock s) by (unfold T7; stk_fields; congruence).
  assert (Epre : forall ck, evaluate (Seq q0 (Seq q1 (Seq (stack_move sac 0 f k (StackAlloc sac))
                    (Seq Skip (Call (SOME (Seq Skip (copy_ret false false (k, (f, f')) vs q2), (0, (l1, l2)))) dest' NONE)))),
                    set_clock (clock t + ck) t) =
                  evaluate (Call (SOME (Seq Skip (copy_ret false false (k, (f, f')) vs q2), (0, (l1, l2)))) dest' NONE,
                    set_clock (clock T7 + ck) T7)).
  { intros ck. rewrite (ev_seq_none _ _ _ _ (evaluate_add_clock ck _ _ _ _ (conj E4 Hnt))).
    rewrite (ev_seq_none _ _ _ _ (evaluate_add_clock ck _ _ _ _ (conj E5 Hnt))).
    rewrite (ev_seq_none _ _ _ _ (evaluate_add_clock ck _ _ _ _ (conj E7' Hnt))).
    rewrite (ev_seq_none _ _ _ _ (ev_skip _)). reflexivity. }
  destruct (wordSem.clock s =? 0) eqn:Ec0.
  { injection Hev as <- <-. apply N.eqb_eq in Ec0.
    exists 0, (empty_env (set_clock (clock T7 + 0) T7)), (SOME TimeOut). split.
    - rewrite Epre, (ev_call_ret _ _ _ _ _ _ (set_clock (clock T7 + 0) T7) Hfind7). stk_fields.
      rewrite Hc7, Ec0. reflexivity.
    - cbn [option_map compile_result]. rewrite bd_neq_false.
      unfold wordSem.flush_state, empty_env, T7. ws_fields. stk_fields. split; [symmetry; exact Hffi0|lia]. }
  apply N.eqb_neq in Ec0.
  destruct (wordSem.evaluate (prog, wordSem.call_env args1 ss (wordSem.push_env envs NONE (wordSem.dec_clock s)))) as [r s2] eqn:Ep.
  change (wret_cont vs envs ret_code l1 l2 NONE r s2 = (res, s1)) in Hev.
  assert (Hev' : (if wordSem.clock s =? 0 then
       (SOME wordSem.TimeOut, wordSem.flush_state true
          (wordSem.set_stack_max (wordSem.stack_max (wordSem.call_env args1 ss (wordSem.push_env envs NONE s))) (wordSem.set_stack [] s)))
     else let '(r, s2) := wordSem.evaluate (prog, wordSem.call_env args1 ss (wordSem.push_env envs NONE (wordSem.dec_clock s))) in
       wret_cont vs envs ret_code l1 l2 NONE r s2) = (res, s1))
    by (rewrite (proj2 (N.eqb_neq _ _) Ec0), Ep; exact Hev).
  assert (Ecall : forall ck, evaluate (Call (SOME (Seq Skip (copy_ret false false (k, (f, f')) vs q2), (0, (l1, l2)))) dest' NONE,
                    set_clock (clock T7 + ck) T7) =
                  match evaluate (Seq (StackAlloc (fs - sac)) qb, dec_clock (set_var 0 (Loc l1 l2) (set_clock (clock T7 + ck) T7))) with
                  | (SOME (Result x), s2) => if negb (bool_decide (x = Loc l1 l2)) then (SOME Error, s2)
                                             else evaluate (Seq Skip (copy_ret false false (k, (f, f')) vs q2), s2)
                  | (SOME (Exception x), s2) => (SOME (Exception x), s2)
                  | (NONE, s) => (SOME Error, s)
                  | (SOME (Break _), s) => (SOME Error, s)
                  | (SOME (Continue _), s) => (SOME Error, s)
                  | (res, s) => (res, s)
                  end).
  { intros ck. rewrite (ev_call_ret _ _ _ _ _ _ (set_clock (clock T7 + ck) T7) Hfind7). stk_fields.
    replace (clock T7 + ck =? 0) with false by (symmetry; apply N.eqb_neq; lia). reflexivity. }
  assert (HsT7 : stack_space T7 = stack_space t5 - sac) by (unfold T7; stk_fields; reflexivity).
  destruct (stack_space T7 <? fs - sac) eqn:Eov3.
  { apply N.ltb_lt in Eov3. exists 0. eexists. eexists. split.
    - rewrite Epre, Ecall, ev_seq, ev_stackalloc. unfold dec_clock, set_var. stk_fields.
      unfold T7 at 1. stk_fields. rewrite Hus0. cbn [negb].
      replace (stack_space T7 <? fs - sac) with true by (symmetry; apply N.ltb_lt; exact Eov3). reflexivity.
    - apply (call_ret_overflow ac k f f' s t5 lens envs NONE args1 ss fs prog vs ret_code l1 l2 res s1 _ HP5 Hthe ltac:(cbn; lia) Hgd Hres Hev').
      unfold empty_env, dec_clock, set_var, T7. stk_fields. exact Hffi0. }
  apply N.ltb_ge in Eov3.
  set (T8 := set_stack_space (stack_space T7 - (fs - sac)) (dec_clock (set_var 0 (Loc l1 l2) T7))).
  assert (HT8 : state_rel ac k fs svc (wordSem.call_env args1 ss (wordSem.push_env envs NONE (wordSem.dec_clock s))) T8 (f' :: lens) 0).
  { apply (state_rel_callee ac k f' s t5 lens envs NONE args1 ss fs svc sac f S7 R7 xs l1 l2 args HP5 HR7).
    - intros n0 v Hl Hkn. destruct (Hloc0 n0 v Hl) as [_ G]. rewrite (proj2 (N.ltb_lt _ _) Hkn) in G. exact G.
    - intros n0 v Hl Hkn. destruct (Hloc0 n0 v Hl) as [_ G]. rewrite (proj2 (N.ltb_ge _ _) Hkn) in G.
      destruct G as [G _]. apply oEL_TAKE_SOME in G. rewrite N.add_0_r in G. exact G.
    - rewrite HL7. reflexivity.
    - rewrite HS7 in HD7. stk_fields. replace (stack_space t5 - sac + 0 + sac) with (stack_space t5) in HD7 by lia. exact HD7.
    - intros x Hx. rewrite HS7 in HEL7. stk_fields. rewrite !N.add_0_r in HEL7.
      rewrite !oEL_EL by (rewrite LENGTH_DROP'; try rewrite <- HL7; stk_fields; lia). rewrite HEL7 by exact Hx. reflexivity.
    - exact HsF.
    - exact Egv.
    - exact Hargs.
    - exists lx. exact Hxs.
    - reflexivity.
    - exact Hsv.
    - exact Eov2.
    - symmetry. exact Efs.
    - exact Hthe.
    - rewrite <- HsT7. exact Eov3. }
  assert (Hr : r <> SOME wordSem.Error) by (intros ->; injection Hev as <- _; congruence).
  pose proof (evaluate_mono _ _ _ _ E7') as [Hbm7 Hcd7].
  assert (Hbm8 : bitmaps T8 = bitmaps T7) by reflexivity.
  assert (Hcd8 : code T8 = code T7) by reflexivity.
  destruct (IH (prog, wordSem.call_env args1 ss (wordSem.push_env envs NONE (wordSem.dec_clock s))))
    with k fs svc r s2 T8 bs0 i0 bs4 i4 qb (f' :: lens) as (ck & t1 & res1 & Eq1 & HRc).
  { right. cbn [snd]. unfold wordSem.call_env, wordSem.push_env, wordSem.env_to_list, wordSem.dec_clock. ws_fields.
    split; [reflexivity|]. left. lia. }
  { split; [exact Ep|]. split; [exact Hr|]. split; [exact HT8|]. split; [exact Hpac1|]. split; [exact Hflat1|].
    split; [exact Eqb|]. split; [exact Hi1|].
    pose proof (isPREFIX_LENGTH' _ _ Hbm7) as Hlbm7.
    rewrite Hbm8. split; [lia|]. split.
    - eapply isPREFIX_TRANS; split; [exact Hi3|]. apply isPREFIX_DROP.
      eapply isPREFIX_TRANS; split; [exact Hbm4|]. eapply isPREFIX_TRANS; split; [exact Hbm5|exact Hbm7].
    - split.
      + pose proof (find_code_IMP_get_labels _ _ _ _ Hfind) as Hgl. intros z Hz. rewrite Hcd8.
        apply (loc_check_SUBSET _ _ Hcd7), (loc_check_SUBSET _ _ Hcd5), Hgl. cbn [get_labels]. right. exact Hz.
      + unfold svc. pose proof (N.div_mod (wordLang.max_var prog) 2 ltac:(lia)) as D1.
        pose proof (N.mod_lt (wordLang.max_var prog) 2 ltac:(lia)) as D2. rewrite MAX_max. lia. }
  assert (Ecb : forall ck', evaluate (Seq (StackAlloc (fs - sac)) qb, dec_clock (set_var 0 (Loc l1 l2) (set_clock (clock T7 + ck') T7))) =
                            evaluate (qb, set_clock (clock T8 + ck') T8)).
  { intros ck'. rewrite ev_seq, ev_stackalloc. unfold dec_clock at 1, set_var at 1. stk_fields.
    unfold T7 at 1. stk_fields. rewrite Hus0. cbn [negb].
    replace (stack_space T7 <? fs - sac) with false by (symmetry; apply N.ltb_ge; exact Eov3).
    unfold T8. rewrite <- call_state_eq by lia. reflexivity. }
  assert (Hhcall : wordSem.handler (wordSem.call_env args1 ss (wordSem.push_env envs NONE (wordSem.dec_clock s))) = wordSem.handler s)
    by (unfold wordSem.call_env, wordSem.push_env, wordSem.env_to_list, wordSem.dec_clock; ws_fields; reflexivity).
  destruct (decide (OPTION_MAP compile_result r = res1)) as [<-|Hne1].
  2:{ rewrite bd_true' in HRc by exact Hne1. destruct HRc as (-> & Hio1 & Hsl1).
      exists ck, t1, (SOME (Halt (Word (n2w 2)))). split.
      - rewrite Epre, Ecall, Ecb, Eq1. reflexivity.
      - rewrite bd_true' by (destruct res as [r0|]; [cbn; intros E; injection E as E; apply (compile_result_NOT_2 r0 Hgd), E|discriminate]).
        destruct (wret_cont_mono _ _ _ _ _ _ _ _ _ _ Hev Hres) as [M1 M2].
        split; [reflexivity|]. split; [eapply isPREFIX_TRANS; split; [exact Hio1|exact M1]|apply M2; exact Hsl1]. }
  rewrite bd_neq_false in HRc.
  destruct r as [[x ys|x y|bn|cn| | |fe|]|]; unfold wret_cont in Hev;
    try (injection Hev as <- _; congruence);
    try (match type of Hev with (SOME ?R, _) = _ =>
           injection Hev as <- <-; exists ck, t1, (OPTION_MAP compile_result (SOME R)); split;
           [rewrite Epre, Ecall, Ecb, Eq1; reflexivity|rewrite bd_neq_false; exact HRc] end).
  - (* Result *)
    destruct (negb ⌜x = Loc l1 l2⌝ || negb (LENGTH ys =? LENGTH vs)) eqn:Ex; [injection Hev as <- _; congruence|].
    apply orb_false_iff in Ex as [Ex1 Ex2]. apply negb_false_iff in Ex1, Ex2. apply bool_decide_spec in Ex1. subst x.
    apply N.eqb_eq in Ex2.
    pose proof (stack_swap.evaluate_stack_swap prog (wordSem.call_env args1 ss (wordSem.push_env envs NONE (wordSem.dec_clock s)))) as Hsw.
    rewrite Ep in Hsw. destruct Hsw as (Hkey & Hhnd & _). rewrite Hhcall in Hhnd.
    unfold wordSem.call_env, wordSem.push_env, wordSem.env_to_list, wordSem.dec_clock in Hkey. ws_fields.
    destruct (wordSem.stack s2) as [|[m l0' el' hnd'] st] eqn:Est2; [cbn in Hkey; contradiction|].
    destruct hnd' as [hnd'|]; cbn [stack_swap.s_key_eq stack_swap.s_frame_key_eq] in Hkey; [tauto|].
    destruct Hkey as (_ & Hmf & <- & <-).
    destruct (wordSem.pop_env s2) as [s3|] eqn:Epop; [|injection Hev as <- _; congruence].
    unfold wordSem.pop_env in Epop. rewrite Est2 in Epop. injection Epop as <-.
    destruct (⌜_⌝) eqn:Edom in Hev; [|injection Hev as <- _; congruence].
    set (s3 := wordSem.set_vars vs ys _) in Hev.
    cbn [option_map compile_result] in HRc. destruct HRc as [HR1 Hys].
    replace (LENGTH ys - (k - 1)) with (LENGTH vs + 1 - k) in HR1 by lia.
    pose proof HR1 as HS1. sr_destr HS1. rewrite Est2 in Hsr1.
    pose proof (stack_rel_cons_LEN_NONE _ _ _ _ _ _ _ _ _ _ _ _ Hsr1) as HLEN. rewrite !LENGTH_DROP' in HLEN.
    destruct (evaluate_copy_ret_aux k f (LENGTH vs + 1 - k) t1) as (t' & Ecr & S' & R' & Et' & HLS' & HSS' & HDS' & HG' & Hkeep & Hcp).
    { split; [exact Hus1|]. split; [lia|lia]. }
    cbv zeta in Hcp. subst t'. stk_fields.
    set (T9 := set_stack_space (stack_space t1 + (LENGTH vs + 1 - k)) (set_regs R' (set_stack S' t1))).
    assert (HT9 : state_rel ac k f f' s3 T9 lens 0).
    { apply (state_rel_return_NONE ac k f f' s2 t1 lens _ _ el' st ys vs R' S' HR1 Hys Est2 Ex2 Hvs ltac:(lia) Hf'0 Hf).
      - intros n0 Hn0. destruct (Hlive n0 (cut_envs_frame_dom _ _ _ _ _ _ Ecut (eq_sym Hmf) Hn0)) as (? & ? & _). split; assumption.
      - exact HLS'.
      - exact HDS'.
      - intros i Hi. pose proof (HG' i Hi) as G. unfold stackSem.get_var in G. stk_fields. exact G.
      - exact Hkeep.
      - exact Hcp. }
    pose proof (evaluate_mono _ _ _ _ Eq1) as [Hbmq Hcdq]. stk_fields.
    pose proof (wordSem.evaluate_clock _ _ _ _ Ep) as [Hck2 Htd2].
    assert (Hcd9 : is_true (subspt (code t) (code T9))).
    { unfold T9. stk_fields. apply (subspt_trans _ _ _ (conj Hcd4 (subspt_trans _ _ _ (conj Hcd5 (subspt_trans _ _ _ (conj Hcd7 Hcdq)))))). }
    assert (Hbm9 : is_true (isPREFIX (bitmaps t) (bitmaps T9))).
    { unfold T9. stk_fields. eapply isPREFIX_TRANS; split; [exact Hbm4|]. eapply isPREFIX_TRANS; split; [exact Hbm5|].
      eapply isPREFIX_TRANS; split; [exact Hbm7|exact Hbmq]. }
    destruct (IH (ret_code, s3)) with k f f' res s1 T9 bs1 n1 bs2 n2 q2 lens as (ck' & t2 & res2 & Eq2 & HR2).
    { right. cbn [snd]. unfold s3, wordSem.set_vars. ws_fields.
      unfold wordSem.call_env, wordSem.push_env, wordSem.env_to_list, wordSem.dec_clock in Hck2, Htd2. ws_fields.
      split; [exact Htd2|]. left. lia. }
    { split; [exact Hev|]. split; [exact Hres|]. split; [exact HT9|]. split; [exact Hpac2|]. split; [exact Hflat2|].
      split; [exact Ec2|]. split; [exact HLw1|]. pose proof (isPREFIX_LENGTH' _ _ Hbm9) as Hlbm9. split; [lia|].
      split; [rewrite <- HLw2; eapply isPREFIX_TRANS; split; [exact Hpre|apply isPREFIX_DROP; exact Hbm9]|].
      split; [|exact Hmax2].
      intros z Hz. apply (loc_check_SUBSET _ _ Hcd9), Hlab.
      assert (Hz2 : get_labels (if num_stack_ret k vs =? 0 then q2 else Seq (copy_ret_aux k f (num_stack_ret k vs)) (SeqStackFree (num_stack_ret k vs) q2)) z)
        by (change (get_labels (copy_ret false false (k, (f, f')) vs q2) z); rewrite get_labels_copy_ret; exact Hz).
      cbn [get_labels]. cbv [pred_set.UNION pred_set.INSERT pred_set.IN pred_set.EMPTY] in *. tauto. }
    exists (ck + ck'), t2, res2. split.
    + rewrite Epre, Ecall, Ecb.
      assert (HnT1 : SOME (Result (Loc l1 l2 : word_loc a)) <> SOME TimeOut) by discriminate.
      pose proof (evaluate_add_clock ck' _ _ _ _ (conj Eq1 HnT1)) as Ea. stk_fields.
      rewrite set_clock_set_clock, <- N.add_assoc in Ea. rewrite Ea. cbn [option_map compile_result]. cbv iota beta.
      rewrite bool_decide_eq_true_2 by reflexivity. cbn [negb].
      rewrite (ev_seq_none _ _ _ _ (ev_skip _)), evaluate_copy_ret_Seq'. cbv zeta. unfold num_stack_ret.
      rewrite ev_seq, evaluate_copy_ret_aux_clock, Ecr. cbn [PAIR_MAP I FST SND fst snd]. cbv iota beta.
      rewrite evaluate_SeqStackFree by (stk_fields; split; [exact Hus1|lia]).
      rewrite ev_seq, ev_stackfree. stk_fields. rewrite Hus1. cbn [negb].
      replace (LENGTH S' <? stack_space t1 + (LENGTH vs + 1 - k)) with false by (symmetry; apply N.ltb_ge; lia).
      cbv iota beta. exact Eq2.
    + assert (Hh3 : wordSem.handler s3 = wordSem.handler s).
      { unfold s3, wordSem.set_vars. ws_fields. rewrite Hhnd. reflexivity. }
      rewrite Hh3 in HR2. exact HR2.
  - (* Exception *)
    injection Hev as <- <-. exists ck, t1, (SOME (Exception x)). split; [rewrite Epre, Ecall, Ecb, Eq1; reflexivity|].
    cbn [option_map compile_result]. rewrite bd_neq_false. destruct HRc as (l0 & l & HR0 & HR1 & HR2).
    exists l0, l. split; [|split; [exact HR1|exact HR2]].
    rewrite Hhcall in HR0.
    assert (Hhl : wordSem.handler s + 1 <= LENGTH lens).
    { pose proof (stack_swap.evaluate_stack_swap prog (wordSem.call_env args1 ss (wordSem.push_env envs NONE (wordSem.dec_clock s)))) as Hsw.
      rewrite Ep in Hsw. destruct Hsw as (Hlt & e0 & e & nn & ls & m & lss & Hlast & _).
      rewrite Hhcall in Hlt, Hlast. unfold wordSem.call_env, wordSem.push_env, wordSem.env_to_list, wordSem.dec_clock in Hlt, Hlast.
      ws_fields. rewrite LENGTH_cons' in Hlt. rewrite (state_rel_IMP_LENGTH _ _ _ _ _ _ _ _ H).
      destruct (decide (wordSem.handler s = LENGTH (wordSem.stack s))) as [E|E]; [|lia].
      rewrite E in Hlast. rewrite LASTN_MORE in Hlast by (rewrite LENGTH_cons'; lia). discriminate. }
    rewrite LASTN_cons_lt in HR0 by lia. exact HR0.
Qed.

End CallRet.

Section CallCase.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "Call" *)
Lemma comp_correct_Call ac ret dest args h s :
  (forall y, wordSem.eval_lt y (wordLang.Call ret dest args h, s) -> comp_goal ac y) ->
  comp_goal ac (wordLang.Call ret dest args h, s).
Proof.
  intros IH. destruct ret as [[vs [live [rc [l1 l2]]]]|].
  - apply comp_correct_Call_returning. exact IH.
  - apply comp_correct_Call_tail. exact IH.
Qed.

(** Galette-only: [comp_goal] holds everywhere, by well-founded induction
    on [wordSem.eval_lt] (HOL uses [evaluate_ind]). *)
Lemma comp_goal_all ac (x : wordLang.prog a * wordSem.state a (N * c) ffi_t) : comp_goal ac x.
Proof.
  induction x as [[p s] IH] using (well_founded_induction wordSem.eval_lt_wf).
  destruct p.
  - apply comp_correct_Skip.
  - apply comp_correct_Move.
  - apply comp_correct_Inst.
  - apply comp_correct_Assign.
  - apply comp_correct_Get.
  - apply comp_correct_Set.
  - apply comp_correct_Store.
  - apply comp_correct_MustTerminate.
  - apply comp_correct_Call. exact IH.
  - apply comp_correct_Seq. exact IH.
  - apply comp_correct_If. exact IH.
  - apply comp_correct_Loop. exact IH.
  - apply comp_correct_Alloc.
  - apply comp_correct_StoreConsts.
  - apply comp_correct_Raise.
  - apply comp_correct_Return.
  - apply comp_correct_Break.
  - apply comp_correct_Continue.
  - apply comp_correct_Tick.
  - apply comp_correct_OpCurrHeap.
  - apply comp_correct_LocValue.
  - apply comp_correct_Install.
  - apply comp_correct_CodeBufferWrite.
  - apply comp_correct_DataBufferWrite.
  - apply comp_correct_FFI.
  - apply comp_correct_ShareInst.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 *)
Theorem comp_correct : forall ac (prog : wordLang.prog a) (s : wordSem.state a (N * c) ffi_t)
    k f f' res s1 (t : stackSem.state a c ffi_t) bs n bs' n' sprog lens,
  wordSem.evaluate (prog, s) = (res, s1) /\ res <> SOME wordSem.Error /\
  state_rel ac k f f' s t lens 0 /\
  post_alloc_conventions k prog /\
  flat_exp_conventions prog /\
  comp ac false prog (bs, n) (k, (f, f')) = (sprog, (bs', n')) /\
  LENGTH (append bs) <= n /\ n - LENGTH (append bs) <= LENGTH (bitmaps t) /\
  isPREFIX (append bs') (DROP (n - LENGTH (append bs)) (bitmaps t)) /\
  get_labels sprog SUBSET loc_check (code t) /\
  wordLang.max_var prog < 2 * f' + 2 * k ->
  exists ck (t1 : stackSem.state a c ffi_t) res1,
    evaluate (sprog, set_clock (clock t + ck) t) = (res1, t1) /\
    comp_res ac k f f' s res s1 t1 res1 lens.
Proof. intros ac prog s. exact (comp_goal_all ac (prog, s)). Qed.

End CallCase.
