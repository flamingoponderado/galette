(** * Pancake [loop_callProof]: correctness of [loop_call]

    Port of [cakeml/pancake/proofs/loop_callProofScript.sml].

    Proof notes: HOL's [recInduct evaluate_ind] is well-founded induction on
    [eval_lt] ([loopSem]); one step of [evaluate] is unfolded with the
    tactics of [loopProps].  The helper lemmas [labels_in_LN] and
    [evaluate_Call_find_code] have no HOL original. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require wordLang backend_common.
Import wordLang(word_loc(..)).
From Galette.cakeml.pancake Require Import loopLang loop_call.
From Galette.cakeml.pancake.semantics Require Import loopSem loopProps.
Open Scope N_scope.

Section Proof.
Context {a : N} {ffi_t : Type}.
Implicit Types s : state a ffi_t.

(*! HOL "cakeml/pancake/proofs/loop_callProofScript.sml" "labels_in_def" *)
Definition labels_in (l : num_map N) (locals : spt (word_loc a)) : Prop :=
  forall n x, lookup n l = SOME x -> lookup n locals = SOME (Loc x 0).

Lemma labels_in_LN locals : labels_in LN locals.
Proof. intros n x H; rewrite lookup_LN in H; discriminate. Qed.

(*! HOL "cakeml/pancake/proofs/loop_callProofScript.sml" "get_vars_front" *)
Theorem get_vars_front : forall xs ys s,
  get_vars xs s = SOME ys /\ xs <> [] ->
  get_vars (FRONT xs) s = SOME (FRONT ys).
Proof.
  induction xs as [|x xs IH]; intros ys s [H Hne]; [congruence|].
  cbn [get_vars] in H.
  destruct (lookup x (locals s)) as [v|] eqn:Ex; [|discriminate].
  destruct (get_vars xs s) as [vs|] eqn:Exs; [|discriminate].
  injection H as <-.
  destruct xs as [|x' xs'].
  - cbn in Exs; injection Exs as <-; reflexivity.
  - assert (Hne' : x' :: xs' <> []) by discriminate.
    specialize (IH vs s (conj Exs Hne')).
    destruct vs as [|v' vs'].
    + cbn [get_vars] in Exs.
      destruct (lookup x' (locals s)); [|discriminate].
      destruct (get_vars xs' s); discriminate.
    + replace (FRONT (x :: x' :: xs')) with (x :: FRONT (x' :: xs')) by reflexivity.
      replace (FRONT (v :: v' :: vs')) with (v :: FRONT (v' :: vs')) by reflexivity.
      cbn [get_vars]. rewrite Ex, IH. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_callProofScript.sml" "get_vars_last" *)
Theorem get_vars_last : forall xs ys s,
  get_vars xs s = SOME ys /\ xs <> [] ->
  lookup (LAST xs) (locals s) = SOME (LAST ys).
Proof.
  induction xs as [|x xs IH]; intros ys s [H Hne]; [congruence|].
  cbn [get_vars] in H.
  destruct (lookup x (locals s)) as [v|] eqn:Ex; [|discriminate].
  destruct (get_vars xs s) as [vs|] eqn:Exs; [|discriminate].
  injection H as <-.
  destruct xs as [|x' xs'].
  - cbn in Exs; injection Exs as <-; exact Ex.
  - assert (Hne' : x' :: xs' <> []) by discriminate.
    specialize (IH vs s (conj Exs Hne')).
    destruct vs as [|v' vs'].
    + cbn [get_vars] in Exs.
      destruct (lookup x' (locals s)); [|discriminate].
      destruct (get_vars xs' s); discriminate.
    + exact IH.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_callProofScript.sml" "evaluate_ShMem_neq_locals" *)
Theorem evaluate_ShMem_neq_locals : forall op v ad s res s' n x,
  evaluate (ShMem op v ad, s) = (res, s') /\ v <> n /\
  ~ (exists x, res = SOME (FinalFFI x)) /\ lookup n (locals s) = x ->
  lookup n (locals s') = x.
Proof.
  intros op v ad s res s' n x (H & Hn & Hf & <-).
  unfold_eval_in H.
  destruct op; cbn [sh_mem_op is_load] in H; unfold sh_mem_load, sh_mem_store in H;
  repeat match type of H with
         | context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta in H
         | context [if ?x then _ else _] => destruct x; cbn beta iota zeta in H
         end;
  injection H as <- <-; state_cbn;
  try reflexivity;
  try (exfalso; apply Hf; eexists; reflexivity);
  rewrite lookup_insert; destruct (decide (n = v)); congruence.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_callProofScript.sml" "evaluate_ShMem_not_load_locals" *)
Theorem evaluate_ShMem_not_load_locals : forall op v ad s res s',
  evaluate (ShMem op v ad, s) = (res, s') /\ ~ is_load op /\
  ~ (exists x, res = SOME (FinalFFI x)) ->
  locals s = locals s'.
Proof.
  intros op v ad s res s' (H & Hl & Hf).
  unfold_eval_in H.
  destruct op; cbn [sh_mem_op is_load] in H, Hl; try (exfalso; apply Hl; reflexivity);
  unfold sh_mem_store in H;
  repeat match type of H with
         | context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta in H
         | context [if ?x then _ else _] => destruct x; cbn beta iota zeta in H
         end;
  injection H as <- <-; state_cbn;
  try reflexivity;
  exfalso; apply Hf; eexists; reflexivity.
Qed.

Lemma LENGTH_FRONT_cons {A} (v0 : A) vs : LENGTH (FRONT (v0 :: vs)) = LENGTH vs.
Proof.
  revert v0; induction vs as [|v1 vs IHv]; intros v0; [reflexivity|].
  change (FRONT (v0 :: v1 :: vs)) with (v0 :: FRONT (v1 :: vs)).
  cbn [LENGTH]. rewrite IHv. reflexivity.
Qed.

(** Two calls whose arguments evaluate and whose code lookups agree behave
    the same. *)
Lemma evaluate_Call_find_code ret d1 a1 d2 a2 h s vs1 vs2 :
  get_vars a1 s = SOME vs1 -> get_vars a2 s = SOME vs2 ->
  find_code d1 vs1 (code s) = find_code d2 vs2 (code s) ->
  evaluate (Call ret d1 a1 h, s) = evaluate (Call ret d2 a2 h, s).
Proof.
  intros H1 H2 H3. rewrite !evaluate_unfold; cbn [evaluate_body].
  rewrite H1, H2, H3; reflexivity.
Qed.

Ltac lab_tac Hl :=
  unfold labels_in in *; intros ?k ?x ?Hk;
  repeat match goal with
         | H : (_, _) = (_, _) |- _ => injection H as <- <-
         end;
  state_cbn;
  rewrite ?lookup_insert, ?lookup_delete in *;
  repeat match goal with
         | |- context [decide ?P] => destruct (decide P); subst
         | H : context [decide ?P] |- _ => destruct (decide P); subst
         end;
  try congruence;
  try (apply Hl; congruence);
  try match goal with
      | E : lookup ?m (locals _) = SOME ?w |- SOME ?w = _ => rewrite <- E; apply Hl; congruence
      end.

(*! HOL "cakeml/pancake/proofs/loop_callProofScript.sml" "compile_correct" *)
Theorem compile_correct : forall (v : prog a) (v1 : state a ffi_t) res s1 l p nl,
  evaluate (v, v1) = (res, s1) /\ res <> SOME Error /\
  comp l v = (p, nl) /\ labels_in l (locals v1) ->
  evaluate (p, v1) = (res, s1) /\ labels_in nl (locals s1).
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall res s1 l p nl,
            evaluate x = (res, s1) -> res <> SOME Error ->
            comp l (fst x) = (p, nl) -> labels_in l (locals (snd x)) ->
            evaluate (p, snd x) = (res, s1) /\ labels_in nl (locals s1))
    by (intros v v1 res s1 l p nl (H1 & H2 & H3 & H4); exact (G (v, v1) res s1 l p nl H1 H2 H3 H4)).
  intros x; induction x as [[v s] IH] using (well_founded_induction eval_lt_wf).
  intros res s1 l p nl H Hne Hc Hl; cbn [fst snd] in *.
  assert (IH' : forall p' s', eval_lt (p', s') (v, s) -> forall res s1 l p nl,
             evaluate (p', s') = (res, s1) -> res <> SOME Error ->
             comp l p' = (p, nl) -> labels_in l (locals s') ->
             evaluate (p, s') = (res, s1) /\ labels_in nl (locals s1))
    by (intros p' s' Hlt; exact (IH (p', s') Hlt)).
  clear IH; rename IH' into IH.
  destruct v; cbn [comp] in Hc.
  - (* Skip *)
    injection Hc as <- <-; split; [exact H|].
    unfold_eval_in H; injection H as <- <-; exact Hl.
  - (* Assign *)
    destruct e;
    match type of Hc with
    | (_, ?m) = _ =>
        let E := fresh "E" in
        assert (E : evaluate (p, s) = (res, s1)) by (injection Hc as <- _; exact H);
        split; [exact E|]; clear E
    end;
    unfold_eval_in H; cbn [eval] in H; split_eval H; try (injection H as <- _; congruence);
    injection H as <- <-; injection Hc as _ <-;
    repeat match goal with
           | |- context [match ?x with _ => _ end] => destruct x eqn:?
           end;
    lab_tac Hl.
  - (* Primitive *)
    injection Hc as <- <-; split; [exact H|].
    unfold_eval_in H; split_eval H; try (injection H as <- _; congruence).
    injection H as <- <-. unfold labels_in in *; intros k x Hk.
    state_cbn. rewrite backend_common.lookup_list_delete in Hk.
    rewrite lookup_alist_insert_any.
    destruct (MEM k l0) eqn:Em; [discriminate|].
    destruct (ALOOKUP (ZIP (l0, l3)) k) eqn:Ea; [|apply Hl; exact Hk].
    exfalso. apply ALOOKUP_In in Ea.
    clear - Ea Em. revert l3 Ea; induction l0 as [|y ys IHl]; intros [|z zs] Ea;
      cbn in Ea; try contradiction.
    cbn [MEM] in Em. unfold bool_decide in Em.
    destruct (decide (k = y)); [discriminate|].
    destruct Ea as [Ea|Ea]; [injection Ea as -> _; congruence|].
    eapply IHl; eauto.
  - (* Arith *)
    assert (E0 : evaluate (p, s) = (res, s1)) by (destruct l0; injection Hc as <- _; exact H).
    split; [exact E0|]; clear E0.
    unfold_eval_in H.
    destruct (loop_arith s l0) as [s0|] eqn:E; [|injection H as <- _; congruence].
    injection H as <- <-.
    unfold labels_in in *; intros k x Hk.
    assert (Hk' : lookup k l = SOME x /\ ~ In k (assigned_vars (@Arith a l0))).
    { destruct l0; injection Hc as _ <-; cbn [assigned_vars In];
      repeat match type of Hk with context [match ?x with _ => _ end] => destruct x eqn:? end;
      rewrite ?lookup_delete in Hk;
      repeat match type of Hk with context [decide ?P] => destruct (decide P) end;
      try discriminate; (split; [exact Hk|intuition congruence]). }
    destruct Hk' as [Hk1 Hk2].
    rewrite (loop_arith_lookup _ _ _ k E Hk2). apply Hl; exact Hk1.
  - (* Store *)
    injection Hc as <- <-; split; [exact H|].
    unfold_eval_in H; split_eval H; try (injection H as <- _; congruence).
    injection H as <- <-.
    match goal with E : mem_store _ _ _ = SOME _ |- _ => apply mem_store_locals in E; rewrite E end.
    exact Hl.
  - (* SetGlobal *)
    injection Hc as <- <-; split; [exact H|].
    unfold_eval_in H; split_eval H; try (injection H as <- _; congruence).
    injection H as <- <-. exact Hl.
  - (* Load32 *)
    assert (E : evaluate (p, s) = (res, s1)) by (injection Hc as <- _; exact H);
    split; [exact E|]; clear E.
    unfold_eval_in H; split_eval H; try (injection H as <- _; congruence).
    injection H as <- <-; injection Hc as _ <-.
    destruct (lookup n0 l) eqn:?; lab_tac Hl.
  - (* LoadByte *)
    assert (E : evaluate (p, s) = (res, s1)) by (injection Hc as <- _; exact H);
    split; [exact E|]; clear E.
    unfold_eval_in H; split_eval H; try (injection H as <- _; congruence).
    injection H as <- <-; injection Hc as _ <-.
    destruct (lookup n0 l) eqn:?; lab_tac Hl.
  - (* Store32 *)
    injection Hc as <- <-; split; [exact H|].
    unfold_eval_in H; split_eval H; try (injection H as <- _; congruence).
    injection H as <- <-. exact Hl.
  - (* StoreByte *)
    injection Hc as <- <-; split; [exact H|].
    unfold_eval_in H; split_eval H; try (injection H as <- _; congruence).
    injection H as <- <-. exact Hl.
  - (* Seq *)
    destruct (comp l v1) as [np nl1] eqn:C1.
    destruct (comp nl1 v2) as [nq nl2] eqn:C2.
    injection Hc as <- <-.
    split; [|apply labels_in_LN].
    unfold_eval_in H. unfold_eval.
    destruct (evaluate (v1, s)) as [r1 t1] eqn:E1.
    assert (Hr1 : r1 <> SOME Error) by (intros ->; injection H as <- _; congruence).
    destruct (IH v1 s ltac:(prove_lt) r1 t1 l np nl1 E1 Hr1 C1 Hl) as [E1' Hl1].
    rewrite E1'.
    destruct r1 as [r1|]; [exact H|].
    exact (proj1 (IH v2 t1 ltac:(prove_lt) res s1 nl1 nq nl2 H Hne C2 Hl1)).
  - (* If *)
    destruct (comp l v1) as [np nl1] eqn:C1.
    destruct (comp l v2) as [nq nl2] eqn:C2.
    injection Hc as <- <-.
    split; [|apply labels_in_LN].
    unfold_eval_in H. unfold_eval.
    destruct (lookup n (locals s)) as [[w1|]|]; try exact H.
    destruct (get_var_imm r s) as [[w2|]|]; try exact H.
    cbn zeta in H |- *.
    destruct (word_cmp c w1 w2).
    + destruct (evaluate (v1, s)) as [r1 t1] eqn:E1.
      assert (Hr1 : r1 <> SOME Error)
        by (intros ->; cbn in H; injection H as <- _; congruence).
      rewrite (proj1 (IH v1 s ltac:(prove_lt) r1 t1 l np nl1 E1 Hr1 C1 Hl)); exact H.
    + destruct (evaluate (v2, s)) as [r1 t1] eqn:E1.
      assert (Hr1 : r1 <> SOME Error)
        by (intros ->; cbn in H; injection H as <- _; congruence).
      rewrite (proj1 (IH v2 s ltac:(prove_lt) r1 t1 l nq nl2 E1 Hr1 C2 Hl)); exact H.
  - (* Loop *)
    destruct (comp LN v) as [np nl1] eqn:C1.
    injection Hc as <- <-.
    split; [|apply labels_in_LN].
    unfold_eval_in H. unfold_eval.
    destruct (cut_res s0 (NONE, s)) as [[r0|] s'] eqn:Ecut; [exact H|].
    rewrite fix_clock_evaluate in H |- *.
    destruct (evaluate (v, s')) as [rb tb] eqn:Eb.
    assert (Hrb : rb <> SOME Error)
      by (intros ->; injection H as <- _; cbn in Hne; congruence).
    rewrite (proj1 (IH v s' ltac:(prove_lt) rb tb LN np nl1 Eb Hrb C1 (labels_in_LN _))).
    assert (HL : forall res' t', evaluate (Loop s0 v s2, tb) = (res', t') -> res' <> SOME Error ->
                   evaluate (Loop s0 np s2, tb) = (res', t')).
    { intros res' t' He Hne'.
      apply (proj1 (IH (Loop s0 v s2) tb ltac:(prove_lt) res' t' LN (Loop s0 np s2) LN He Hne'
                        ltac:(cbn [comp]; rewrite C1; reflexivity) (labels_in_LN _))). }
    destruct rb as [[ | | k | k | | | ]|]; try exact H.
    + destruct k; [|exact H]. exact (HL _ _ H Hne).
    + exact (HL _ _ H Hne).
  - (* Break *)
    injection Hc as <- <-; split; [exact H|].
    unfold_eval_in H; injection H as <- <-; exact Hl.
  - (* Continue *)
    injection Hc as <- <-; split; [exact H|].
    unfold_eval_in H; injection H as <- <-; exact Hl.
  - (* Raise *)
    injection Hc as <- <-; split; [exact H|]. apply labels_in_LN.
  - (* Return *)
    injection Hc as <- <-; split; [exact H|]. apply labels_in_LN.
  - (* ShMem *)
    injection Hc as <- <-; split; [exact H|]. apply labels_in_LN.
  - (* Tick *)
    injection Hc as <- <-; split; [exact H|]. apply labels_in_LN.
  - (* Mark *)
    destruct (comp l v) as [np nl1] eqn:C1.
    injection Hc as <- <-.
    unfold_eval_in H.
    destruct (IH v s ltac:(prove_lt) res s1 l np nl1 H Hne C1 Hl) as [E1 Hl1].
    split; [|exact Hl1].
    unfold_eval. exact E1.
  - (* Fail *)
    unfold_eval_in H; injection H as <- _; congruence.
  - (* LocValue *)
    injection Hc as <- <-; split; [exact H|].
    unfold_eval_in H; split_eval H; try (injection H as <- _; congruence).
    injection H as <- <-. lab_tac Hl.
  - (* Call *)
    assert (Hp : evaluate (p, s) = (res, s1)).
    { destruct o0 as [d|].
      - injection Hc as <- _; exact H.
      - destruct l0 as [|arg args].
        + unfold_eval_in H; cbn [get_vars find_code] in H.
          injection H as <- _; congruence.
        + destruct (lookup (LAST (arg :: args)) l) as [lab|] eqn:Elab;
            injection Hc as <- _; [|exact H].
          rewrite <- H.
          unfold_eval_in H.
          destruct (get_vars (arg :: args) s) as [vs|] eqn:Ev;
            [|injection H as <- _; congruence].
          assert (Hne' : arg :: args <> []) by discriminate.
          change (match args with [] => [] | _ :: _ => arg :: FRONT args end)
            with (FRONT (arg :: args)).
          apply (evaluate_Call_find_code _ _ _ _ _ _ _ (FRONT vs) vs);
            [apply get_vars_front; split; [exact Ev|exact Hne'] | exact Ev|].
          pose proof (get_vars_last _ _ _ (conj Ev Hne')) as Hlast.
          rewrite (Hl _ _ Elab) in Hlast. injection Hlast as Hlast.
          cbn [find_code]. rewrite <- Hlast.
          destruct vs as [|v0 vs];
            [cbn [get_vars] in Ev; destruct (lookup arg (locals s)), (get_vars args s); discriminate|].
          unfold bool_decide; destruct (decide _) as [Hd|Hd]; [discriminate|].
          destruct (lookup lab (code s)) as [[params body]|]; [|reflexivity].
          rewrite LENGTH_FRONT_cons. cbn [LENGTH].
          destruct (N.eqb_spec (LENGTH vs) (LENGTH params)) as [Hq|Hq];
            destruct (N.eqb_spec (N.succ (LENGTH vs)) (LENGTH params + 1)) as [Hq'|Hq'];
            try reflexivity; lia. }
    destruct o0 as [d|]; [injection Hc as _ <-|destruct l0; [|destruct lookup]; injection Hc as _ <-];
      (split; [exact Hp|apply labels_in_LN]).
  - (* FFI *)
    injection Hc as <- <-; split; [exact H|]. apply labels_in_LN.
Qed.

End Proof.
