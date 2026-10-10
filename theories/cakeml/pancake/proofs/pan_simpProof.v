(** * CakeML Pancake [pan_simpProof]: correctness of [pan_simp]

    Port of [cakeml/pancake/proofs/pan_simpProofScript.sml].

    Proof notes: HOL's [recInduct evaluate_ind] is well-founded induction on
    [eval_lt]; the Galette-only helpers below (nested induction on
    programs, congruences of [evaluate]) have no HOL original.  The
    semantics-preservation theorem [state_rel_imp_semantics] is proved by
    showing that the source and target runs agree, clock by clock, on their
    results and FFI states (no least-upper-bound reasoning is needed).
    HOL's [compile_eval_correct_none] is inside a comment block of the HOL
    script (it is not a HOL theorem) and is not ported. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.pancake Require Import panLang pan_simp.
From Galette.cakeml.pancake.semantics Require Import panSem pan_commonProps panProps.
Open Scope N_scope.
Local Open Scope fmap_scope.

(** ** Galette-only infrastructure *)

Section ProgInd.
Context {a : N}.

(** Induction on programs with an induction hypothesis for the exception
    handler of [Call]. *)
Definition prog_nested_ind (P : prog a -> Prop)
    (Hskip : P Skip)
    (Hdec : forall v s e p, P p -> P (Dec v s e p))
    (Hassign : forall vk v e, P (Assign vk v e))
    (Hprim : forall v op es, P (Primitive v op es))
    (Hstore : forall e1 e2, P (Store e1 e2))
    (Hstore32 : forall e1 e2, P (Store32 e1 e2))
    (Hstoreb : forall e1 e2, P (StoreByte e1 e2))
    (Hseq : forall p q, P p -> P q -> P (Seq p q))
    (Hif : forall e p q, P p -> P q -> P (If e p q))
    (Hwhile : forall e p, P p -> P (While e p))
    (Hbreak : P panLang.Break) (Hcont : P panLang.Continue)
    (Hcall : forall ct f args,
        match ct with Some (_, Some (_, (_, h))) => P h | _ => True end -> P (Call ct f args))
    (Hdeccall : forall v s f args p, P p -> P (DecCall v s f args p))
    (Hext : forall f e1 e2 e3 e4, P (ExtCall f e1 e2 e3 e4))
    (Hraise : forall eid e, P (Raise eid e))
    (Hret : forall e, P (panLang.Return e))
    (Hshl : forall op vk v e, P (ShMemLoad op vk v e))
    (Hshs : forall op e1 e2, P (ShMemStore op e1 e2))
    (Htick : P Tick) (Hannot : forall s1 s2, P (Annot s1 s2)) : forall p, P p :=
  fix go (p : prog a) : P p :=
    match p with
    | Skip => Hskip
    | Dec v s e p => Hdec v s e p (go p)
    | Assign vk v e => Hassign vk v e
    | Primitive v op es => Hprim v op es
    | Store e1 e2 => Hstore e1 e2
    | Store32 e1 e2 => Hstore32 e1 e2
    | StoreByte e1 e2 => Hstoreb e1 e2
    | Seq p q => Hseq p q (go p) (go q)
    | If e p q => Hif e p q (go p) (go q)
    | While e p => Hwhile e p (go p)
    | panLang.Break => Hbreak
    | panLang.Continue => Hcont
    | Call ct f args =>
        Hcall ct f args
          (match ct as ct0 return
                 (match ct0 with Some (_, Some (_, (_, h))) => P h | _ => True end) with
           | Some (_, Some (_, (_, h))) => go h
           | Some (_, None) => I
           | None => I
           end)
    | DecCall v s f args p => Hdeccall v s f args p (go p)
    | ExtCall f e1 e2 e3 e4 => Hext f e1 e2 e3 e4
    | Raise eid e => Hraise eid e
    | panLang.Return e => Hret e
    | ShMemLoad op vk v e => Hshl op vk v e
    | ShMemStore op e1 e2 => Hshs op e1 e2
    | Tick => Htick
    | Annot s1 s2 => Hannot s1 s2
    end.

End ProgInd.

(** ** Expression identifiers and exceptions *)

Section Ids.
Context {a : N}.

Lemma exp_ids_seq_call_ret (p : prog a) : exp_ids (seq_call_ret p) = exp_ids p.
Proof.
  unfold seq_call_ret.
  repeat match goal with |- context [match ?x with _ => _ end] =>
    destruct x; cbn [exp_ids]; try reflexivity end.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "exp_ids_ret_to_tail_eq" *)
Theorem exp_ids_ret_to_tail_eq : forall p : prog a, exp_ids (ret_to_tail p) = exp_ids p.
Proof.
  induction p using prog_nested_ind; cbn [ret_to_tail exp_ids]; try reflexivity.
  - rewrite IHp; reflexivity.
  - rewrite exp_ids_seq_call_ret; cbn [exp_ids]; rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp; reflexivity.
  - destruct ct as [[rv [[eid [ev h]]|]]|]; cbn; try reflexivity. rewrite H; reflexivity.
  - rewrite IHp; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "exp_ids_seq_assoc_eq" *)
Theorem exp_ids_seq_assoc_eq : forall p q : prog a,
  exp_ids (seq_assoc p q) = exp_ids p ++ exp_ids q.
Proof.
  intros p q; revert p; induction q using prog_nested_ind; intros p0;
    try (destruct ct as [[rv [[eid [ev h]]|]]|]); cbn [seq_assoc exp_ids];
    unfold SmartSeq; try destruct (decide (p0 = Skip)) as [->|]; cbn [exp_ids];
    repeat first [rewrite IHq | rewrite IHq1 | rewrite IHq2 | rewrite H];
    cbn [exp_ids List.app]; rewrite ?app_nil_r, ?app_assoc; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "exp_ids_compile_eq" *)
Theorem exp_ids_compile_eq : forall p : prog a, exp_ids (compile p) = exp_ids p.
Proof.
  intros p; unfold compile; rewrite exp_ids_ret_to_tail_eq, exp_ids_seq_assoc_eq; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "map_snd_f_eq" *)
Theorem map_snd_f_eq : forall {A B C D} (p : list (A * (B * C))) (f : C -> C) (g : C -> D),
  MAP (g ∘ SND ∘ SND ∘ (fun '(name, (params, body)) => (name, (params, f body)))) p =
  MAP (g ∘ f) (MAP (SND ∘ SND) p).
Proof.
  intros A B C D p f g; induction p as [|[x [y z]] p IH]; cbn; [reflexivity|].
  rewrite IH; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "size_of_eids_compile_eq" *)
Theorem size_of_eids_compile_eq : forall pan_code : list (decl a),
  size_of_eids (compile_prog pan_code) = size_of_eids pan_code.
Proof.
  unfold size_of_eids, compile_prog; induction pan_code as [|d ds IH]; [reflexivity|].
  destruct d; cbn [MAP List.map FILTER List.filter is_exn_decl]; rewrite ?LENGTH_cons, ?IH; reflexivity.
Qed.

End Ids.

(** ** [evaluate] and [seq_assoc], [ret_to_tail] *)

Section Evaluate.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma evaluate_Seq_eq (c1 c2 : prog a) s :
  evaluate (Seq c1 c2, s) =
  let '(res, s1) := evaluate (c1, s) in
  match res with NONE => evaluate (c2, s1) | _ => (res, s1) end.
Proof. rewrite evaluate_unfold; cbn [evaluate_body]; rewrite fix_clock_evaluate; reflexivity. Qed.

(** Unfold one step of [evaluate] in the goal (both sides). *)
Ltac unfold_eval :=
  rewrite ?evaluate_unfold; cbn [evaluate_body]; rewrite ?fix_clock_evaluate.

(** Congruences: [evaluate] of a compound program depends on its
    sub-programs only through their [evaluate]. *)
Ltac cong_tac Hq :=
  repeat first
    [ rewrite Hq
    | progress (rewrite ?fix_clock_evaluate)
    | reflexivity
    | match goal with |- context [match ?x with _ => _ end] =>
        let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta end ].

Lemma evaluate_Seq_cong1 (p1 p2 q : prog a) :
  (forall s, evaluate (p1, s) = evaluate (p2, s)) ->
  forall s, evaluate (Seq p1 q, s) = evaluate (Seq p2 q, s).
Proof. intros Hq s; rewrite !evaluate_Seq_eq, Hq; reflexivity. Qed.

Lemma evaluate_Seq_cong2 (p q1 q2 : prog a) :
  (forall s, evaluate (q1, s) = evaluate (q2, s)) ->
  forall s, evaluate (Seq p q1, s) = evaluate (Seq p q2, s).
Proof. intros Hq s; rewrite !evaluate_Seq_eq; cong_tac Hq. Qed.

Lemma evaluate_Dec_cong v sh e (q1 q2 : prog a) :
  (forall s, evaluate (q1, s) = evaluate (q2, s)) ->
  forall s, evaluate (Dec v sh e q1, s) = evaluate (Dec v sh e q2, s).
Proof. intros Hq s; unfold_eval; cong_tac Hq. Qed.

Lemma evaluate_If_cong e (p1 p2 q1 q2 : prog a) :
  (forall s, evaluate (p1, s) = evaluate (p2, s)) ->
  (forall s, evaluate (q1, s) = evaluate (q2, s)) ->
  forall s, evaluate (If e p1 q1, s) = evaluate (If e p2 q2, s).
Proof. intros Hp Hq s; unfold_eval; cong_tac Hp; cong_tac Hq. Qed.

Lemma evaluate_Call_cong rv eid ev f args (h1 h2 : prog a) :
  (forall s, evaluate (h1, s) = evaluate (h2, s)) ->
  forall s, evaluate (Call (Some (rv, Some (eid, (ev, h1)))) f args, s) =
            evaluate (Call (Some (rv, Some (eid, (ev, h2)))) f args, s).
Proof. intros Hq s; unfold_eval; cong_tac Hq. Qed.

Lemma evaluate_DecCall_cong v sh f args (q1 q2 : prog a) :
  (forall s, evaluate (q1, s) = evaluate (q2, s)) ->
  forall s, evaluate (DecCall v sh f args q1, s) = evaluate (DecCall v sh f args q2, s).
Proof. intros Hq s; unfold_eval; cong_tac Hq. Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_SmartSeq" *)
Theorem evaluate_SmartSeq : forall (p q : prog a) s,
  evaluate (SmartSeq p q, s) = evaluate (Seq p q, s).
Proof.
  intros p q s; unfold SmartSeq; destruct (decide (p = Skip)) as [->|]; [|reflexivity].
  rewrite evaluate_Seq_eq, (evaluate_unfold Skip s); reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_seq_skip" *)
Theorem evaluate_seq_skip : forall (p : prog a) s, evaluate (Seq p Skip, s) = evaluate (p, s).
Proof.
  intros p s; rewrite evaluate_Seq_eq.
  destruct (evaluate (p, s)) as [[r|] s1]; [reflexivity|].
  rewrite (evaluate_unfold Skip s1); reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_skip_seq" *)
Theorem evaluate_skip_seq : forall (p : prog a) s, evaluate (Seq Skip p, s) = evaluate (p, s).
Proof. intros p s; rewrite evaluate_Seq_eq, (evaluate_unfold Skip s); reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_while_body_same" *)
Theorem evaluate_while_body_same : forall (body body' : prog a) e,
  (forall s : state a ffi_t, evaluate (body, s) = evaluate (body', s)) ->
  forall s : state a ffi_t, evaluate (While e body, s) = evaluate (While e body', s).
Proof.
  intros body body' e Hb s.
  remember (While e body, s) as x eqn:Hx. revert s Hx.
  induction x as [x IH] using (well_founded_induction eval_lt_wf); intros s Hx; subst x.
  unfold_eval. rewrite Hb.
  destruct (eval s e) as [[[w]| |]|]; try reflexivity.
  destruct (negb _); [|reflexivity]. destruct (clock s =? 0) eqn:Hc; [reflexivity|].
  destruct (evaluate (body', dec_clock s)) as [r s1] eqn:E.
  rewrite <- Hb in E; pose proof (evaluate_clock _ _ _ _ E) as Hcl.
  apply N.eqb_neq in Hc.
  destruct r as [[]|]; try reflexivity;
    apply (IH (While e body, s1)); try reflexivity;
    left; cbn [snd clock dec_clock set_clock] in *; unfold dec_clock, set_clock in Hcl; cbn in Hcl; lia.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_while_no_error_imp" *)
Theorem evaluate_while_no_error_imp : forall s e w (c : prog a),
  eval s e = SOME (ValWord w) /\ w <> words.n2w 0 /\ clock s <> 0 /\
  FST (evaluate (While e c, s)) <> SOME Error ->
  FST (evaluate (c, dec_clock s)) <> SOME Error.
Proof.
  intros s e w c [He [Hw [Hc H]]]; intros Herr; apply H; clear H.
  unfold_eval; rewrite He; cbn [ValWord].
  replace (negb (bool_decide (w = words.n2w 0))) with true
    by (symmetry; apply Bool.negb_true_iff, Bool.not_true_iff_false; intros Hb;
        apply bool_decide_spec in Hb; exact (Hw Hb)).
  apply N.eqb_neq in Hc; rewrite Hc.
  destruct (evaluate (c, dec_clock s)) as [r s1]; cbn in Herr; subst r; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_seq_assoc" *)
Theorem evaluate_seq_assoc : forall (p q : prog a) s,
  evaluate (seq_assoc p q, s) = evaluate (Seq p q, s).
Proof.
  intros p q; revert p; induction q using prog_nested_ind; intros p0 st0;
    cbn [seq_assoc]; rewrite ?evaluate_SmartSeq; try reflexivity.
  - symmetry; apply evaluate_seq_skip.
  - apply evaluate_Seq_cong2; intros st1; apply evaluate_Dec_cong; intros st2.
    rewrite IHq; apply evaluate_skip_seq.
  - rewrite IHq2. rewrite (evaluate_Seq_cong1 _ (Seq p0 q1) q2 (IHq1 p0)).
    rewrite !evaluate_Seq_eq. destruct (evaluate (p0, st0)) as [[r|] st1]; [reflexivity|].
    rewrite evaluate_Seq_eq; reflexivity.
  - apply evaluate_Seq_cong2; intros st1; apply evaluate_If_cong; intros st2;
      [rewrite IHq1|rewrite IHq2]; apply evaluate_skip_seq.
  - apply evaluate_Seq_cong2; intros st1; apply evaluate_while_body_same; intros st2.
    rewrite IHq; apply evaluate_skip_seq.
  - destruct ct as [[rv [[eid [ev h]]|]]|]; cbn [seq_assoc]; rewrite ?evaluate_SmartSeq;
      try reflexivity.
    apply evaluate_Seq_cong2; intros st1; apply evaluate_Call_cong; intros st2.
    rewrite H; apply evaluate_skip_seq.
  - apply evaluate_Seq_cong2; intros st1; apply evaluate_DecCall_cong; intros st2.
    rewrite IHq; apply evaluate_skip_seq.
  - rewrite evaluate_Seq_eq. destruct (evaluate (p0, st0)) as [[r|] st1]; [reflexivity|].
    rewrite evaluate_unfold; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_seq_no_error_fst" *)
Theorem evaluate_seq_no_error_fst : forall (p p' : prog a) s,
  FST (evaluate (Seq p p', s)) <> SOME Error -> FST (evaluate (p, s)) <> SOME Error.
Proof.
  intros p p' s H Herr; apply H; clear H; rewrite evaluate_Seq_eq.
  destruct (evaluate (p, s)) as [r s1]; cbn in Herr; subst r; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "eval_seq_assoc_eq_evaluate" *)
Theorem eval_seq_assoc_eq_evaluate : forall (p : prog a) s res t,
  evaluate (seq_assoc Skip p, s) = (res, t) -> evaluate (p, s) = (res, t).
Proof. intros p s res t; rewrite evaluate_seq_assoc, evaluate_skip_seq; exact id. Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "eval_seq_assoc_not_error" *)
Theorem eval_seq_assoc_not_error : forall (p : prog a) s,
  FST (evaluate (p, s)) <> SOME Error -> FST (evaluate (seq_assoc Skip p, s)) <> SOME Error.
Proof. intros p s; rewrite evaluate_seq_assoc, evaluate_skip_seq; exact id. Qed.

(** Rewrite the goal's scrutinees (including calls of [evaluate]) with the
    equations of the context. *)
Ltac goal_scrut_all :=
  match goal with
  | E : ?x = _ |- context [match ?x with _ => _ end] => rewrite E; cbn beta iota zeta
  end.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_seq_call_ret_eq" *)
Theorem evaluate_seq_call_ret_eq : forall (p : prog a) s,
  FST (evaluate (p, s)) <> SOME Error -> evaluate (seq_call_ret p, s) = evaluate (p, s).
Proof.
  intros p s H; unfold seq_call_ret.
  repeat match goal with |- context [match ?x with _ => _ end] =>
    destruct x; try reflexivity end.
  subst.
  destruct (evaluate (Seq _ _, s)) as [res st] eqn:H0; cbn [fst] in H.
  rewrite evaluate_Seq_eq, (evaluate_unfold (Call _ _ _)) in H0; cbn [evaluate_body] in H0.
  split_all H0.
  all: try (rewrite evaluate_unfold in H0; cbn [evaluate_body eval] in H0;
            destruct_kvars_all; state_cbn; rewrite ?FLOOKUP_UPDATE in H0; split_all H0).
  all: leaf_subst H0; try congruence.
  all: rewrite evaluate_unfold; cbn [evaluate_body].
  all: repeat first [ progress (rewrite ?fix_clock_evaluate) | goal_scrut_all ].
  all: state_eq.
Qed.

Lemma ret_to_tail_correct_aux : forall (p : prog a) s res st,
  evaluate (p, s) = (res, st) -> res <> SOME Error ->
  evaluate (ret_to_tail p, s) = (res, st).
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall res st,
            evaluate x = (res, st) -> res <> SOME Error ->
            evaluate (ret_to_tail (fst x), snd x) = (res, st))
    by (intros p s res st H1 H2; exact (G (p, s) res st H1 H2)).
  intros x; induction x as [[p t] IH] using (well_founded_induction eval_lt_wf).
  intros res st H Hres; cbn [fst snd].
  rewrite evaluate_unfold in H.
  destruct p; try (destruct o as [[rv [[eid [ev h]]|]]|]);
  lazymatch goal with
  | |- evaluate (ret_to_tail (Seq ?p1 ?p2), ?t) = ?R =>
      cut (evaluate (Seq (ret_to_tail p1) (ret_to_tail p2), t) = R);
      [ intros HS; cbn [ret_to_tail]; rewrite evaluate_seq_call_ret_eq;
        [exact HS | rewrite HS; exact Hres] | ]
  | _ => cbn [ret_to_tail]
  end;
  cbn [evaluate_body] in H; unfold sh_mem_load, sh_mem_store in *; split_all H.
  all: leaf_subst H; try congruence.
  all: rewrite evaluate_unfold; cbn [evaluate_body]; unfold sh_mem_load, sh_mem_store.
  all: repeat first
    [ progress (rewrite ?fix_clock_evaluate)
    | goal_scrut
    | match goal with E : evaluate (?p', ?g) = _ |- context [evaluate (?p', ?g)] =>
        rewrite E; cbn beta iota zeta end
    | match goal with |- context [evaluate (?q, ?g)] =>
        match goal with E : evaluate (?p', g) = (?r1, ?t1) |- _ =>
          let q' := eval cbn [ret_to_tail] in (ret_to_tail p') in
          constr_eq q' q;
          let HI := fresh "HI" in
          assert (HI : evaluate (ret_to_tail p', g) = (r1, t1))
            by (apply (IH (p', g)); [prove_lt | exact E | congruence]);
          change q with (ret_to_tail p'); rewrite HI; clear HI; cbn beta iota zeta
        end
      end ].
  all: reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "ret_to_tail_correct" *)
Theorem ret_to_tail_correct : forall (p : prog a) s,
  FST (evaluate (p, s)) <> SOME Error -> evaluate (ret_to_tail p, s) = evaluate (p, s).
Proof.
  intros p s H; destruct (evaluate (p, s)) as [res st] eqn:E.
  apply ret_to_tail_correct_aux; [exact E|exact H].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "compile_correct_same_state" *)
Theorem compile_correct_same_state : forall (p : prog a) s,
  FST (evaluate (p, s)) <> SOME Error -> evaluate (compile p, s) = evaluate (p, s).
Proof.
  intros p s H; unfold compile.
  rewrite ret_to_tail_correct; rewrite evaluate_seq_assoc, evaluate_skip_seq; [reflexivity|exact H].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_seq_simp" *)
Theorem evaluate_seq_simp : forall (p : prog a) s res t,
  evaluate (p, s) = (res, t) /\ res <> SOME Error -> evaluate (compile p, s) = (res, t).
Proof.
  intros p s res t [H Hr]; rewrite compile_correct_same_state; [exact H|rewrite H; exact Hr].
Qed.

End Evaluate.

(** ** The state relation *)

Section StateRel.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "state_rel_def" *)
Definition state_rel (s t : state a ffi_t)
    (c : fmap funname (list (varname * shape) * (prog a * shape))) : Prop :=
  t = set_code c s /\
  (forall f, FLOOKUP (code s) f = NONE -> FLOOKUP c f = NONE) /\
  (forall f vshs prog rshape,
     FLOOKUP (code s) f = SOME (vshs, (prog, rshape)) ->
     FLOOKUP c f = SOME (vshs, (compile prog, rshape))).

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "state_rel_intro" *)
Theorem state_rel_intro : forall s t c,
  state_rel s t c ->
  t = set_code c s /\
  (forall f vshs prog rshape,
     FLOOKUP (code s) f = SOME (vshs, (prog, rshape)) ->
     FLOOKUP c f = SOME (vshs, (compile prog, rshape))).
Proof. intros s t c [H1 [_ H3]]; split; assumption. Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "state_rel_upd_inv" *)
Theorem state_rel_upd_inv : forall s t code,
  state_rel s t code -> exists s_code, s = set_code s_code t.
Proof. intros s t c [-> _]; exists (panSem.code s); destruct s; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "opt_mmap_eq_some_helper" *)
Theorem opt_mmap_eq_some_helper : forall {A B} (f g : A -> option B) `{EqDecision A} xs zs,
  OPT_MMAP f xs = SOME zs /\
  (forall x, is_true (MEM x xs) -> forall y, f x = SOME y -> g x = SOME y) ->
  OPT_MMAP g xs = SOME zs.
Proof.
  intros A B f g HA xs; induction xs as [|x xs IH]; intros zs [H1 H2]; [exact H1|].
  cbn in H1 |- *. destruct (f x) as [y|] eqn:Ef; [|discriminate]; cbn in H1.
  destruct (OPT_MMAP f xs) as [ys|] eqn:Eo; [|discriminate]; cbn in H1.
  rewrite (H2 x) with (y := y); cbn.
  - rewrite (IH ys); [exact H1|]. split; [reflexivity|].
    intros x' Hx' y' Hy'. apply (H2 x'); [|exact Hy'].
    unfold is_true in *; cbn; rewrite Hx', Bool.orb_true_r; reflexivity.
  - unfold is_true; cbn; apply Bool.orb_true_iff; left; apply bool_decide_spec; reflexivity.
  - exact Ef.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "compile_eval_correct" *)
Theorem compile_eval_correct : forall s e v0 t,
  eval s e = SOME v0 /\ state_rel s t (code t) -> eval t e = SOME v0.
Proof. intros s e v0 t [H [-> _]]; rewrite eval_set_code; exact H. Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "OPT_MMAP_NONE" *)
Theorem OPT_MMAP_NONE : forall {A B} (f : A -> option B) `{EqDecision A} xs,
  OPT_MMAP f xs = NONE -> exists x, is_true (MEM x xs) /\ f x = NONE.
Proof.
  intros A B f HA xs; induction xs as [|x xs IH]; intros H; [discriminate|].
  cbn in H. destruct (f x) eqn:Ef; cbn in H.
  - destruct (OPT_MMAP f xs) eqn:Eo; [discriminate|].
    destruct (IH eq_refl) as [y [Hy1 Hy2]]; exists y; split; [|exact Hy2].
    unfold is_true in *; cbn; rewrite Hy1, Bool.orb_true_r; reflexivity.
  - exists x; split; [|exact Ef].
    unfold is_true; cbn; apply Bool.orb_true_iff; left; apply bool_decide_spec; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "OPT_MMAP_NONE'" *)
Theorem OPT_MMAP_NONE' : forall {A B} (f : A -> option B) `{EqDecision A} x xs,
  is_true (MEM x xs) /\ f x = NONE -> OPT_MMAP f xs = NONE.
Proof.
  intros A B f HA x xs; induction xs as [|y xs IH]; intros [Hm Hf]; [discriminate|].
  cbn in Hm |- *. unfold is_true in Hm; apply Bool.orb_true_iff in Hm as [Hm|Hm].
  - apply bool_decide_spec in Hm; subst; rewrite Hf; reflexivity.
  - destruct (f y); cbn; [|reflexivity]. rewrite (IH (conj Hm Hf)); reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "OPT_MMAP_eval_some_eq" *)
Theorem OPT_MMAP_eval_some_eq : forall s t es vs,
  OPT_MMAP (fun a0 => eval s a0) es = SOME vs /\ state_rel s t (code t) ->
  OPT_MMAP (fun a0 => eval t a0) es = SOME vs.
Proof. intros s t es vs [H [-> _]]; rewrite eval_set_code; exact H. Qed.

Definition code_ok (cs c : fmap funname (list (varname * shape) * (prog a * shape))) : Prop :=
  forall f vshs prog rshape,
    FLOOKUP cs f = SOME (vshs, (prog, rshape)) ->
    FLOOKUP c f = SOME (vshs, (compile prog, rshape)).

Lemma lookup_code_ok cs c fname (args : list (v a)) prog0 nl rsh :
  code_ok cs c -> lookup_code cs fname args = SOME (prog0, (nl, rsh)) ->
  lookup_code c fname args = SOME (compile prog0, (nl, rsh)).
Proof.
  intros Hc H; unfold lookup_code in *.
  destruct (FLOOKUP cs fname) as [[vshs [p rs]]|] eqn:E; [|discriminate].
  rewrite (Hc _ _ _ _ E). destruct (_ && _); [|discriminate].
  injection H as H1 H2 H3; subst; reflexivity.
Qed.

Lemma compile_correct_aux : forall (p : prog a) s res s1 c,
  evaluate (p, s) = (res, s1) -> res <> SOME Error -> code_ok (code s) c ->
  evaluate (p, set_code c s) = (res, set_code c s1).
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall res s1 c,
            evaluate x = (res, s1) -> res <> SOME Error -> code_ok (code (snd x)) c ->
            evaluate (fst x, set_code c (snd x)) = (res, set_code c s1))
    by (intros p s res s1 c H1 H2 H3; exact (G (p, s) res s1 c H1 H2 H3)).
  intros x; induction x as [[p t] IH] using (well_founded_induction eval_lt_wf).
  intros res st c H Hres Hc; cbn [fst snd] in *.
  rewrite evaluate_unfold in H |- *.
  destruct p; cbn [evaluate_body] in H |- *;
    unfold sh_mem_load, sh_mem_store in *; split_all H.
  all: leaf_subst H; try congruence.
  all: repeat match goal with
       | E : evaluate (?p', ?s') = (?r1, ?t1) |- _ =>
           lazymatch goal with
           | _ : code t1 = code s' |- _ => fail
           | _ => pose proof (evaluate_code_invariant p' s' r1 t1 E)
           end
       end.
  all: repeat first
    [ progress (repeat first [rewrite fix_clock_evaluate | rewrite eval_set_code
          | rewrite lookup_kvar_set_code | rewrite is_valid_value_set_code])
    | progress state_cbn_goal
    | match goal with E : lookup_code (code _) ?f ?args = SOME (?p0, (?nl, ?rsh)) |- _ =>
        let E' := fresh "E" in
        pose proof (lookup_code_ok _ _ _ _ _ _ _ Hc E) as E';
        rewrite E'; clear E; cbn beta iota zeta
      end
    | goal_scrut
    | match goal with
      | |- context [evaluate (?q, ?g)] =>
          match goal with
          | E : evaluate (?p', ?s') = (?r1, ?t1) |- _ =>
              let Hr1 := fresh "Hr" in
              assert (Hr1 : r1 <> SOME Error) by congruence;
              let Hcs := fresh "Hcs" in
              assert (Hcs : code_ok (code s') c)
                by (match type of Hc with code_ok ?cs _ =>
                      replace (code s') with cs by (clock_ctx; congruence); exact Hc end);
              let HI := fresh "HI" in
              pose proof (IH (p', s') ltac:(prove_lt) r1 t1 c E Hr1 Hcs) as HI;
              cbn [fst snd] in HI;
              let Hg := fresh "Hg" in
              assert (Hg : g = set_code c s') by state_eq;
              first [ constr_eq q p'
                    | constr_eq q (compile p');
                      rewrite Hg, compile_correct_same_state by (rewrite HI; exact Hr1) ];
              try rewrite Hg; rewrite HI; clear Hg HI Hr1 Hcs; cbn beta iota zeta
          end
      end ].
  all: state_eq.
Qed.

(** HOL's statement has a vacuous quantifier [ctxt] (of an arbitrary
    type), kept here. *)
(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "compile_correct" *)
Theorem compile_correct : forall {C : Type} (p : prog a) s res s1 t (ctxt : C),
  evaluate (p, s) = (res, s1) /\ res <> SOME Error /\ state_rel s t (code t) ->
  exists t1, evaluate (seq_assoc Skip p, t) = (res, t1) /\ state_rel s1 t1 (code t1).
Proof.
  intros C p s res s1 t ctxt [H [Hres [Ht [Hn Hs]]]].
  pose proof (compile_correct_aux p s res s1 (code t) H Hres Hs) as HA.
  exists (set_code (code t) s1).
  rewrite evaluate_seq_assoc, evaluate_skip_seq, Ht. rewrite Ht in HA.
  cbn [code set_code] in HA |- *. split; [exact HA|].
  pose proof (evaluate_code_invariant p s res s1 H) as Hcode.
  split; [destruct s1; reflexivity|]. rewrite Hcode. split; assumption.
Qed.

End StateRel.

(** ** Programs and semantics *)

Section Semantics.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "functions_compile_prog" *)
Theorem functions_compile_prog : forall prog : list (decl a),
  functions (compile_prog prog) =
  MAP (fun '(x, (y, (z, t))) => (x, (y, (compile z, t)))) (functions prog).
Proof.
  unfold compile_prog; induction prog as [|d ds IH]; [reflexivity|].
  destruct d; cbn [MAP List.map functions name params body fun_decl_return]; rewrite ?IH; reflexivity.
Qed.

Lemma MAP_FST_functions_compile_prog (prog : list (decl a)) :
  MAP FST (functions (compile_prog prog)) = MAP FST (functions prog).
Proof.
  rewrite functions_compile_prog, map_map.
  apply map_ext; intros [x [y [z t]]]; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "first_compile_prog_all_distinct" *)
Theorem first_compile_prog_all_distinct : forall prog : list (decl a),
  is_true (ALL_DISTINCT (MAP FST (functions prog))) ->
  is_true (ALL_DISTINCT (MAP FST (functions (compile_prog prog)))).
Proof. intros prog H; rewrite MAP_FST_functions_compile_prog; exact H. Qed.

Lemma EL_MAP_lt {A B} `{Inhabited A} `{Inhabited B} (f : A -> B) n (l : list A) :
  n < LENGTH l -> EL n (MAP f l) = f (EL n l).
Proof.
  revert n; induction l as [|x l IH]; intros n Hn; [cbn in Hn; lia|].
  destruct (N.eq_dec n 0) as [->|Hn0].
  - reflexivity.
  - cbn [MAP List.map]; rewrite !EL_cons_pos by lia. apply IH. rewrite LENGTH_cons in Hn; lia.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "el_compile_prog_el_prog_eq" *)
Theorem el_compile_prog_el_prog_eq : forall (prog : list (decl a)) n start pprog p rshape,
  EL n (functions (compile_prog prog)) = (start, ([], (pprog, rshape))) /\
  is_true (ALL_DISTINCT (MAP FST (functions prog))) /\ n < LENGTH (functions prog) /\
  ALOOKUP (functions prog) start = SOME ([], (p, rshape)) ->
  EL n (functions prog) = (start, ([], (p, rshape))).
Proof.
  intros prog n start pprog p rshape [H1 [H2 [H3 H4]]].
  rewrite functions_compile_prog, EL_MAP_lt in H1 by exact H3.
  pose proof (ALOOKUP_ALL_DISTINCT_EL (functions prog) n (conj H3 H2)) as HA.
  destruct (EL n (functions prog)) as [st [ps [z rs]]].
  injection H1 as -> -> _ ->. cbn in HA. rewrite HA in H4. injection H4 as ->. reflexivity.
Qed.

(** Equality of shapes in statements ([ALL_DISTINCT] of parameter lists). *)
#[local] Instance shape_eq_dec_cl : EqDecision shape := fun x y => classical_dec (x = y).

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "compile_prog_distinct_params" *)
Theorem compile_prog_distinct_params : forall prog : list (decl a),
  is_true (EVERY (fun '(name, (params, body)) => ALL_DISTINCT params) (functions prog)) ->
  is_true (EVERY (fun '(name, (params, body)) => ALL_DISTINCT params)
                 (functions (compile_prog prog))).
Proof.
  intros prog; rewrite functions_compile_prog.
  induction (functions prog) as [|[x [y [z t]]] l IH]; cbn; [tauto|].
  unfold is_true; rewrite !Bool.andb_true_iff; intros [H1 H2]; split; [exact H1|apply IH, H2].
Qed.

(** [panSem]'s [semantics] as a function of its clocked runs. *)
#[local] Instance behaviour_inhabited' : Inhabited behaviour := Fail.

Definition sem_of (F : N -> option (result a) * state a ffi_t) : behaviour :=
  if classical_dec (exists k,
       match fst (F k) with
       | SOME TimeOut => False
       | SOME (FinalFFI _) => False
       | SOME (Return _) => False
       | _ => True
       end)
  then Fail
  else
    match some (fun res => exists k t r outcome,
             F k = (r, t) /\
             match r with
             | SOME (FinalFFI e) => outcome = FFI_outcome e
             | SOME (Return _) => outcome = Success
             | _ => False
             end /\
             res = Terminate outcome (io_events (ffi t))) with
    | SOME res => res
    | NONE =>
        Diverge (build_lprefix_lub
                   (IMAGE (fun k => fromList (io_events (ffi (snd (F k))))) UNIV))
    end.

Lemma semantics_sem_of s start :
  semantics s start = sem_of (fun k => evaluate (TailCall start [], set_clock k s)).
Proof. reflexivity. Qed.

Lemma sem_of_cong F1 F2 :
  (forall k, fst (F1 k) = fst (F2 k) /\ ffi (snd (F1 k)) = ffi (snd (F2 k))) ->
  sem_of F1 = sem_of F2.
Proof.
  intros HF; unfold sem_of.
  match goal with |- (if classical_dec ?P1 then _ else _) = (if classical_dec ?P2 then _ else _) =>
    replace P1 with P2; [|apply propositional_extensionality; split; intros [k Hk];
                           exists k; [rewrite (proj1 (HF k))|rewrite <- (proj1 (HF k))]; exact Hk]
  end.
  destruct (classical_dec _); [reflexivity|].
  match goal with |- match some ?Q1 with _ => _ end = match some ?Q2 with _ => _ end =>
    replace Q1 with Q2
  end.
  - destruct (some _); [reflexivity|]. f_equal. f_equal. f_equal.
    apply functional_extensionality; intros k; rewrite (proj2 (HF k)); reflexivity.
  - apply functional_extensionality; intros res; apply propositional_extensionality.
    split; intros [k [t [r [out [H1 [H2 H3]]]]]]; exists k.
    + destruct (HF k) as [Hf Hs]; rewrite H1 in Hf, Hs; cbn in Hf, Hs.
      exists (snd (F1 k)), r, out; split; [rewrite <- Hf; destruct (F1 k); reflexivity|].
      split; [exact H2|rewrite Hs; exact H3].
    + destruct (HF k) as [Hf Hs]; rewrite H1 in Hf, Hs; cbn in Hf, Hs.
      exists (snd (F2 k)), r, out; split; [rewrite Hf; destruct (F2 k); reflexivity|].
      split; [exact H2|rewrite <- Hs; exact H3].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "state_rel_imp_semantics" *)
Theorem state_rel_imp_semantics : forall s t (pan_code : list (decl a)) start,
  state_rel s t (code t) /\
  is_true (ALL_DISTINCT (MAP FST (functions pan_code))) /\
  code s = alist_to_fmap (functions pan_code) /\
  code t = alist_to_fmap (functions (compile_prog pan_code)) /\
  semantics s start <> Fail ->
  semantics t start = semantics s start.
Proof.
  intros s t pan_code start [[Ht [_ Hc]] [_ [_ [_ Hsem]]]].
  assert (Hne : forall k, fst (evaluate (TailCall start [], set_clock k s)) <> SOME Error).
  { intros k Herr; apply Hsem; unfold semantics.
    destruct (classical_dec _) as [_|Hn]; [reflexivity|]. exfalso; apply Hn.
    exists k; rewrite Herr; exact I. }
  rewrite !semantics_sem_of; apply sem_of_cong; intros k.
  destruct (evaluate (TailCall start [], set_clock k s)) as [r s1] eqn:E.
  specialize (Hne k); rewrite E in Hne; cbn in Hne.
  pose proof (compile_correct_aux _ _ _ _ (code t) E Hne Hc) as HA.
  replace (set_clock k t) with (set_code (code t) (set_clock k s))
    by (rewrite Ht; destruct s; reflexivity).
  rewrite HA; split; reflexivity.
Qed.

Lemma state_rel_evaluate_decls_aux : forall (pan_code : list (decl a)) s t s',
  state_rel s t (code t) -> evaluate_decls s pan_code = SOME s' ->
  exists t', evaluate_decls t (compile_prog pan_code) = SOME t' /\ state_rel s' t' (code t').
Proof.
  induction pan_code as [|d ds IH]; intros s t s' Hr H.
  - injection H as <-; exists t; split; [reflexivity|exact Hr].
  - destruct Hr as [Ht [Hn Hc]].
    unfold compile_prog; cbn [MAP List.map]; fold (compile_prog ds).
    rewrite evaluate_decls_cons_cases in H |- *.
    destruct d as [fi|sh v0 e|eid sh|nm flds]; cbn beta iota.
    + rewrite Ht; cbn [structs set_code code name params body fun_decl_return].
      destruct (_ && _); [|discriminate].
      apply (IH _ (set_code (code t |+ (name fi, (params fi, (compile (body fi), fun_decl_return fi))))
                             (set_code (code t) s))) in H as [t' [H1 H2]].
      * exists t'; split; [|exact H2]. rewrite <- H1; f_equal; destruct s; reflexivity.
      * split; [destruct s; reflexivity|]. cbn [code set_code]. split.
        -- intros f Hf; rewrite FLOOKUP_UPDATE in Hf |- *.
           destruct (decide _); [discriminate|]; apply Hn, Hf.
        -- intros f vshs pr rs Hf; rewrite FLOOKUP_UPDATE in Hf |- *.
           destruct (decide _); [injection Hf as -> -> ->; reflexivity|]; apply Hc, Hf.
    + rewrite Ht.
      rewrite (eval_state_cong (set_locals FEMPTY (set_code (code t) s)) (set_locals FEMPTY s))
        by reflexivity.
      destruct (eval _ e) as [res|]; [|discriminate].
      destruct (bool_decide _); [|discriminate].
      apply (IH _ (set_globals (globals s |+ (v0, res)) (set_code (code t) s))) in H
        as [t' [H1 H2]].
      * exists t'; split; [|exact H2]. rewrite <- H1; f_equal; destruct s; reflexivity.
      * split; [destruct s; reflexivity|]. cbn [code set_code set_globals]. split; assumption.
    + rewrite Ht; cbn [structs eshapes set_code].
      destruct (_ && _); [|discriminate].
      apply (IH _ (set_eshapes (eshapes s |+ (eid, sh)) (set_code (code t) s))) in H
        as [t' [H1 H2]].
      * exists t'; split; [|exact H2]. rewrite <- H1; f_equal; destruct s; reflexivity.
      * split; [destruct s; reflexivity|]. cbn [code set_code set_eshapes]. split; assumption.
    + apply (IH s t) in H as [t' [H1 H2]]; [exists t'; split; assumption|].
      split; [exact Ht|split; assumption].
Qed.

(** HOL's statement has a vacuous quantifier [start] (of an arbitrary
    type), kept here. *)
(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "state_rel_imp_evaluate_decls" *)
Theorem state_rel_imp_evaluate_decls : forall {C : Type} s (pan_code : list (decl a)) t s' (start : C),
  state_rel s t (code t) /\
  is_true (ALL_DISTINCT (MAP FST (functions pan_code))) /\
  evaluate_decls s pan_code = SOME s' ->
  exists t', evaluate_decls t (compile_prog pan_code) = SOME t' /\ state_rel s' t' (code t').
Proof. intros C s pan_code t s' start [H1 [_ H2]]; exact (state_rel_evaluate_decls_aux _ _ _ _ H1 H2). Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "decs_stcnames_compile_prog" *)
Theorem decs_stcnames_compile_prog : forall ctxt (pan_code : list (decl a)),
  decs_stcnames ctxt (compile_prog pan_code) = decs_stcnames ctxt pan_code.
Proof.
  intros ctxt ds; revert ctxt; induction ds as [|d ds IH]; intros ctxt; [reflexivity|].
  unfold compile_prog in *; destruct d; cbn [MAP List.map decs_stcnames]; rewrite ?IH; reflexivity.
Qed.

Lemma FEMPTY_FUPDATE_LIST_alist {K V} {HK : EqDecision K} (l : list (K * V)) :
  is_true (ALL_DISTINCT (MAP FST l)) -> FEMPTY |++ l = alist_to_fmap l.
Proof.
  induction l as [|[k v] l IH]; intros H; [apply fmap_ext; intros; reflexivity|].
  cbn in H; unfold is_true in H; apply Bool.andb_true_iff in H as [Hm Hd].
  change (FEMPTY |+ (k, v) |++ l = alist_to_fmap ((k, v) :: l)).
  rewrite FUPDATE_FUPDATE_LIST_COMMUTES.
  - rewrite IH by exact Hd. symmetry; apply alist_to_fmap_thm.
  - intros Hm'; unfold is_true in Hm'; rewrite Hm' in Hm; discriminate.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_simpProofScript.sml" "state_rel_imp_semantics_decls" *)
Theorem state_rel_imp_semantics_decls : forall s t (pan_code : list (decl a)) start,
  state_rel s t (code t) /\
  is_true (ALL_DISTINCT (MAP FST (functions pan_code))) /\
  code s = FEMPTY /\ code t = FEMPTY /\
  semantics_decls s start pan_code <> Fail ->
  semantics_decls s start pan_code = semantics_decls t start (compile_prog pan_code).
Proof.
  intros s t pan_code start [Hr [Hd [Hs [Ht Hsem]]]].
  unfold semantics_decls in *; rewrite decs_stcnames_compile_prog.
  destruct (decs_stcnames [] pan_code) as [ctxt|]; [|reflexivity].
  destruct (evaluate_decls (set_structs ctxt s) pan_code) as [s'|] eqn:E; [|congruence].
  assert (Hr' : state_rel (set_structs ctxt s) (set_structs ctxt t) (code (set_structs ctxt t))).
  { destruct Hr as [-> [Hn Hc]]; split; [destruct s; reflexivity|split; assumption]. }
  destruct (state_rel_evaluate_decls_aux _ _ _ _ Hr' E) as [t' [E' Hr'']].
  rewrite E'; symmetry. apply (state_rel_imp_semantics _ _ pan_code).
  split; [exact Hr''|split; [exact Hd|split; [|split; [|exact Hsem]]]].
  - rewrite (evaluate_decls_functions _ _ _ E); cbn [code set_structs]; rewrite Hs.
    apply FEMPTY_FUPDATE_LIST_alist, Hd.
  - rewrite (evaluate_decls_functions _ _ _ E'); cbn [code set_structs]; rewrite Ht.
    apply FEMPTY_FUPDATE_LIST_alist, first_compile_prog_all_distinct, Hd.
Qed.

End Semantics.
