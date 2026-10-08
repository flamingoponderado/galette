(** * CakeML Pancake [loopProps]: properties of loopLang and loopSem

    Port of [cakeml/pancake/semantics/loopPropsScript.sml].

    Carrier notes:
    - [every_prog], [survives] and [comp_syntax_ok] are HOL boolean
      functions whose values are built from predicates ([every_prog]'s
      argument [p] is applied to HOL predicates such as
      [\r. ∀n. r ≠ Break n]), set membership ([n ∈ domain cs]), equality of
      [num_set]s and an existential; they are [Prop]-valued here, with
      HOL's clauses in HOL's order.
    - HOL's [s with <|locals := l; clock := c|>] is
      [set_clock c (set_locals l s)]; HOL's [x ∈ domain t] is
      [x IN domain t].

    Proof method: HOL's [recInduct evaluate_ind] is well-founded induction
    on [eval_lt] ([loopSem]); one step of [evaluate] is unfolded with
    [evaluate_eqn] and [fix_clock_evaluate].  The helpers of the section
    "Galette-only infrastructure" (nested induction on [prog] and [exp],
    state congruences, case-splitting tactics) have no HOL original. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require wordLang.
Import wordLang(word_loc(..)).
From Galette.cakeml.pancake Require Import loopLang pan_common.
From Galette.cakeml.pancake.semantics Require Import loopSem pan_commonProps.
Open Scope N_scope.

(** ** Galette-only infrastructure *)

Section Ind.
Context {a : N}.

(** Induction on programs with induction hypotheses for the handler
    programs of [Call]. *)
Lemma prog_nested_ind (P : prog a -> Prop)
    (Hskip : P Skip)
    (Hassign : forall n e, P (Assign n e))
    (Hprim : forall l pop r, P (Primitive l pop r))
    (Harith : forall ar, P (Arith ar))
    (Hstore : forall e n, P (Store e n))
    (Hsetg : forall w e, P (SetGlobal w e))
    (Hl32 : forall n m, P (Load32 n m))
    (Hlb : forall n m, P (LoadByte n m))
    (Hs32 : forall n m, P (Store32 n m))
    (Hsb : forall n m, P (StoreByte n m))
    (Hseq : forall p q, P p -> P q -> P (Seq p q))
    (Hif : forall c n ri p q l, P p -> P q -> P (If c n ri p q l))
    (Hloop : forall l1 p l2, P p -> P (Loop l1 p l2))
    (Hbrk : forall n, P (loopLang.Break n))
    (Hcont : forall n, P (loopLang.Continue n))
    (Hraise : forall n, P (Raise n))
    (Hret : forall ns, P (Return ns))
    (Hshm : forall op n e, P (ShMem op n e))
    (Htick : P Tick)
    (Hmark : forall p, P p -> P (Mark p))
    (Hfail : P Fail)
    (Hlocv : forall n m, P (LocValue n m))
    (Hcall : forall ret dest args h,
        match h with Some (_, (p, (q, _))) => P p /\ P q | None => True end ->
        P (Call ret dest args h))
    (Hffi : forall s n1 n2 n3 n4 l, P (FFI s n1 n2 n3 n4 l))
    : forall p : prog a, P p.
Proof.
  fix rec 1; intros p; destruct p.
  - apply Hskip.
  - apply Hassign.
  - apply Hprim.
  - apply Harith.
  - apply Hstore.
  - apply Hsetg.
  - apply Hl32.
  - apply Hlb.
  - apply Hs32.
  - apply Hsb.
  - apply Hseq; apply rec.
  - apply Hif; apply rec.
  - apply Hloop; apply rec.
  - apply Hbrk.
  - apply Hcont.
  - apply Hraise.
  - apply Hret.
  - apply Hshm.
  - apply Htick.
  - apply Hmark; apply rec.
  - apply Hfail.
  - apply Hlocv.
  - apply Hcall. destruct o1 as [[n0 [p0 [q0 l0]]]|]; [split; apply rec|exact Logic.I].
  - apply Hffi.
Qed.

(** Induction on expressions with induction hypotheses for the nested list
    of [Op]. *)
Fixpoint exp_nested_ind (P : exp a -> Prop)
    (Hc : forall w, P (Const w)) (Hv : forall n, P (Var n)) (Hl : forall n, P (Lookup n))
    (Hld : forall e, P e -> P (Load e))
    (Hop : forall op es, Forall P es -> P (Op op es))
    (Hsh : forall s e1 e2, P e1 -> P e2 -> P (Shift s e1 e2))
    (Hb : P BaseAddr) (Ht : P TopAddr) (e : exp a) : P e :=
  let rec := exp_nested_ind P Hc Hv Hl Hld Hop Hsh Hb Ht in
  let fix go (l : list (exp a)) : Forall P l :=
    match l with [] => Forall_nil _ | x :: xs => Forall_cons _ (rec x) (go xs) end in
  match e with
  | Const w => Hc w
  | Var n => Hv n
  | Lookup n => Hl n
  | Load e => Hld e (rec e)
  | Op op es => Hop op es (go es)
  | Shift s e1 e2 => Hsh s e1 e2 (rec e1) (rec e2)
  | BaseAddr => Hb
  | TopAddr => Ht
  end.

End Ind.

Section StateHelpers.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma MAP_ext_Forall {A B} (f g : A -> B) l :
  Forall (fun x => f x = g x) l -> MAP f l = MAP g l.
Proof. induction 1; cbn; congruence. Qed.

(** [eval] reads only the locals, globals, memory, [mdomain], [base_addr]
    and [top_addr] of the state. *)
Lemma eval_state_cong_gen s t e :
  globals s = globals t -> memory s = memory t -> mdomain s = mdomain t ->
  base_addr s = base_addr t -> top_addr s = top_addr t ->
  (forall n, In n (locals_touched e) -> lookup n (locals s) = lookup n (locals t)) ->
  eval s e = eval t e.
Proof.
  intros H2 H3 H4 H5 H6.
  induction e as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2| |] using exp_nested_ind;
    intros HL; cbn [eval locals_touched] in *; try congruence.
  - apply HL; left; reflexivity.
  - rewrite IH by exact HL. destruct (eval t e) as [[w|]|]; try reflexivity.
    unfold mem_load; rewrite H3, H4; reflexivity.
  - rewrite (MAP_ext_Forall (eval s) (eval t)); [reflexivity|].
    rewrite Forall_forall in IH |- *. intros x Hx. apply IH; [exact Hx|].
    intros n Hn; apply HL. apply in_concat. exists (locals_touched x); split; [|exact Hn].
    apply in_map; exact Hx.
  - rewrite IH1, IH2; [reflexivity| |]; intros n Hn; apply HL, in_or_app; auto.
Qed.

Lemma eval_state_cong s t :
  locals s = locals t -> globals s = globals t -> memory s = memory t ->
  mdomain s = mdomain t -> base_addr s = base_addr t -> top_addr s = top_addr t ->
  eval s = eval t.
Proof.
  intros H1 H2 H3 H4 H5 H6; apply functional_extensionality; intros e.
  apply eval_state_cong_gen; auto. intros; rewrite H1; reflexivity.
Qed.

Lemma eval_set_clock k s : eval (set_clock k s) = eval s.
Proof. apply eval_state_cong; reflexivity. Qed.
Lemma eval_set_ffi f s : eval (set_ffi f s) = eval s.
Proof. apply eval_state_cong; reflexivity. Qed.

Lemma get_vars_set_clock vs k s : get_vars vs (set_clock k s) = get_vars vs s.
Proof. induction vs; cbn; [reflexivity|]. rewrite IHvs; reflexivity. Qed.

Lemma get_vars_locals vs s t : locals s = locals t -> get_vars vs s = get_vars vs t.
Proof. intros H; induction vs; cbn; [reflexivity|]. rewrite IHvs, H; reflexivity. Qed.

Lemma set_clock_id s : set_clock (clock s) s = s.
Proof. destruct s; reflexivity. Qed.

End StateHelpers.

(** Projections of state updates. *)
Ltac state_cbn :=
  cbn [locals globals memory mdomain sh_mdomain clock code be ffi base_addr top_addr
       set_locals set_memory set_clock set_ffi set_var set_vars set_globals dec_clock
       call_env] in *.

Ltac eqb_facts :=
  repeat match goal with
         | H : (_ =? _)%N = false |- _ => apply N.eqb_neq in H
         | H : (_ =? _)%N = true |- _ => apply N.eqb_eq in H
         end.

Lemma evaluate_unfold {a ffi_t} (p : prog a) (s : state a ffi_t) :
  evaluate (p, s) =
  evaluate_body (fun p' s' => evaluate (p', s')) (fun p' s' => evaluate (p', s')) p s.
Proof. apply evaluate_eqn. Qed.

(** Unfold one step of [evaluate (p, s)] in hypothesis [H]. *)
Ltac unfold_eval_in H :=
  rewrite evaluate_unfold in H; cbn [evaluate_body] in H; unfold fcl in H;
  cbn beta in H; rewrite ?fix_clock_evaluate in H.

(** Unfold one step of [evaluate (p, s)] in the goal. *)
Ltac unfold_eval :=
  rewrite evaluate_unfold; cbn [evaluate_body]; unfold fcl; cbn beta;
  rewrite ?fix_clock_evaluate.

(** Split in hypothesis [H] the first [match] whose scrutinee is not a call
    of [evaluate] (goal split along). *)
Ltac split_nonrec H :=
  match type of H with
  | context [match ?x with _ => _ end] =>
      lazymatch x with
      | evaluate _ => fail
      | _ => let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H
      end
  | context [if ?x then _ else _] =>
      lazymatch x with
      | evaluate _ => fail
      | _ => let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H
      end
  end.

(** Split in [H] the first [match] on an [evaluate] call, naming the
    result. *)
Ltac split_rec H :=
  match type of H with
  | context [match evaluate ?x with _ => _ end] =>
      let r := fresh "r" in let t := fresh "t" in let E := fresh "Ev" in
      destruct (evaluate x) as [r t] eqn:E; cbn beta iota zeta in H
  | context [let '(_, _) := evaluate ?x in _] =>
      let r := fresh "r" in let t := fresh "t" in let E := fresh "Ev" in
      destruct (evaluate x) as [r t] eqn:E; cbn beta iota zeta in H
  end.

(** Case split hypothesis [H] (an unfolded step of [evaluate]): nested
    [match]es and [if]s, [cut_res], and the inner [evaluate] calls (named
    [Ev*]); a top-level [evaluate] call is left alone. *)
Ltac split_eval H :=
  repeat first
    [ rewrite fix_clock_evaluate in H
    | split_nonrec H
    | match type of H with
      | evaluate _ = _ => fail 1
      | context [evaluate ?x] =>
          let r := fresh "r" in let t := fresh "t" in let E := fresh "Ev" in
          destruct (evaluate x) as [r t] eqn:E; cbn beta iota zeta in H
      end
    | match type of H with
      | context [cut_res _ (?r, _)] =>
          tryif is_var r then (destruct r; cbn beta iota zeta in H)
          else (unfold cut_res in H; cbn beta iota zeta in H)
      end ].

(** ** Definitions *)

Section Defs.
Context {a : N}.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "every_prog_def" *)
Fixpoint every_prog (p : prog a -> Prop) (prog0 : prog a) : Prop :=
  match prog0 with
  | Seq p1 p2 => p (Seq p1 p2) /\ every_prog p p1 /\ every_prog p p2
  | Loop l1 body l2 => p (Loop l1 body l2) /\ every_prog p body
  | If x1 x2 x3 p1 p2 l1 => p (If x1 x2 x3 p1 p2 l1) /\ every_prog p p1 /\ every_prog p p2
  | Mark p1 => p (Mark p1) /\ every_prog p p1
  | Call ret dest args handler =>
      p (Call ret dest args handler) /\
      match handler with
      | Some (n, (q, (r, l))) => every_prog p q /\ every_prog p r
      | None => True
      end
  | prog0 => p prog0
  end.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "survives_def" *)
Fixpoint survives (n : N) (p0 : prog a) : Prop :=
  match p0 with
  | If c r ri p q cs => survives n p /\ survives n q /\ n IN domain cs
  | Loop il p ol => n IN domain il /\ n IN domain ol /\ survives n p
  | Call (Some (m, cs)) trgt args None => n IN domain cs
  | Call (Some (m, cs)) trgt args (Some (r, (p, (q, ps)))) =>
      n IN domain cs /\ n IN domain ps /\ survives n p /\ survives n q
  | FFI fi ptr1 len1 ptr2 len2 cs => n IN domain cs
  | Mark p => survives n p
  | Seq p q => survives n p /\ survives n q
  | _ => True
  end.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "cut_sets_def" *)
Fixpoint cut_sets (l : num_set) (p0 : prog a) : num_set :=
  match p0 with
  | Skip => l
  | LocValue n m => insert n tt l
  | Assign n e => insert n tt l
  | Load32 n m => insert m tt l
  | LoadByte n m => insert m tt l
  | Seq p q => cut_sets (cut_sets l p) q
  | If _ _ _ p q nl => nl
  | Arith arith =>
      match arith with
      | LLongDiv r1 r2 _ _ _ => insert r1 tt (insert r2 tt l)
      | LLongMul r1 r2 _ _ => insert r1 tt (insert r2 tt l)
      | LDiv r1 _ _ => insert r1 tt l
      end
  | _ => l
  end.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "comp_syntax_ok_def" *)
Fixpoint comp_syntax_ok (l : num_set) (p0 : prog a) : Prop :=
  match p0 with
  | Skip => True
  | Assign n e => True
  | Loop lin p lout => l = lin /\ l = lout /\ comp_syntax_ok lin p
  | Arith arith => True
  | loopLang.Break _ => True
  | LocValue n m => True
  | Load32 n m => True
  | LoadByte n m => True
  | Seq p q => comp_syntax_ok l p /\ comp_syntax_ok (cut_sets l p) q
  | If c n r p q nl =>
      comp_syntax_ok l p /\ comp_syntax_ok l q /\
      exists ns, nl = FOLDL (fun sp n => insert n tt sp) l ns
  | _ => False
  end.

End Defs.

(** ** Basic properties *)

Section Basic.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "evaluate_tail_calls_eqs" *)
Theorem evaluate_tail_calls_eqs : forall f (t : state a ffi_t) lc x,
  find_code (SOME f) ([] : list (word_loc a)) (code t) = SOME x ->
  evaluate (Call NONE (SOME f) [] NONE, t) =
  evaluate (Call NONE (SOME f) [] NONE, set_locals lc t).
Proof.
  intros f t lc x H. rewrite !evaluate_unfold; cbn [evaluate_body get_vars code set_locals].
  rewrite H; destruct x; reflexivity.
Qed.

Lemma dom_ins {A} k (v : A) t x : domain (insert k v t) x <-> x = k \/ domain t x.
Proof. rewrite domain_insert; reflexivity. Qed.
Lemma dom_LN {A} x : domain (@LN A) x <-> False.
Proof. reflexivity. Qed.

Lemma acc_vars_acc_iff : forall (p : prog a) l x,
  domain (acc_vars p l) x <-> domain (acc_vars p LN) x \/ domain l x.
Proof.
  intros p; induction p as [|n e|l pop r|ar|e n|w e|n m|n m|n m|n m|p1 p2 IHp1 IHp2|c n ri p1 p2 l IHp1 IHp2|l1 p1 l2 IHp|n|n|n|vs0|mo n e| |p1 IHp| |n m|ret dest args h H|str n1 n2 n3 n4 l] using prog_nested_ind; intros l0 x; cbn [acc_vars];
    try (rewrite ?dom_ins, ?domain_list_insert, ?dom_LN; tauto); try apply IHp.
  - destruct ar; rewrite ?dom_ins, ?dom_LN; tauto.
  - rewrite (IHp1 (acc_vars p2 l0)), (IHp1 (acc_vars p2 LN)), (IHp2 l0). tauto.
  - rewrite (IHp1 (acc_vars p2 l0)), (IHp1 (acc_vars p2 LN)), (IHp2 l0). tauto.
  - destruct ret as [[vs live]|]; [|rewrite dom_LN; tauto]. cbn zeta.
    destruct h as [[n [p1 [p2 l1]]]|]; [|rewrite !domain_list_insert, ?dom_LN; tauto].
    destruct H as [IH1 IH2].
    rewrite (IH1 (acc_vars p2 _)), (IH1 (acc_vars p2 (insert n tt (list_insert vs LN)))),
      (IH2 (insert n tt (list_insert vs l0))), (IH2 (insert n tt (list_insert vs LN))),
      !dom_ins, !domain_list_insert, ?dom_LN. tauto.
Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "acc_vars_acc" *)
Theorem acc_vars_acc : forall (p : prog a) l,
  domain (acc_vars p l) = domain (acc_vars p LN) UNION domain l.
Proof. intros p l; apply set_ext; intros x; apply acc_vars_acc_iff. Qed.

End Basic.

(** Prove [eval_lt] goals from the clock facts in context. *)
Ltac prove_lt :=
  unfold eval_lt; cbn [fst snd psize];
  repeat match goal with
         | E : evaluate _ = (_, _) |- _ => pose proof (evaluate_clock _ _ _ _ E); clear E
         | E : cut_res _ (NONE, _) = (NONE, _) |- _ => pose proof (cut_res_NONE_clock _ _ _ E); clear E
         | E : cut_res _ (_, _) = (_, _) |- _ => pose proof (cut_res_clock _ _ _ _ _ E); clear E
         | E : cut_state _ _ = SOME _ |- _ => apply cut_state_clock in E
         | E : (_ =? _)%N = false |- _ => apply N.eqb_neq in E
         end;
  state_cbn; lia.

Section Props1.
Context {a : N} {ffi_t : Type}.

Lemma cut_res_NONE_SOME live (s : state a ffi_t) r t :
  cut_res live (NONE, s) = (SOME r, t) -> r = Error \/ r = TimeOut.
Proof.
  cbn [cut_res IS_SOME]; destruct (cut_state live s); [|intros H; inversion H; auto].
  destruct (_ =? _)%N; intros H; inversion H; auto.
Qed.

Lemma sh_mem_op_res op v (addr : word a) (s : state a ffi_t) r t :
  sh_mem_op op v addr s = (r, t) ->
  r = NONE \/ r = SOME Error \/ exists e, r = SOME (FinalFFI e).
Proof.
  intros H; destruct op; cbn [sh_mem_op] in H; unfold sh_mem_load, sh_mem_store in H;
  repeat match type of H with
         | context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta in H
         end; inversion H; eauto.
Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "evaluate_Loop_body_same" *)
Theorem evaluate_Loop_body_same : forall (body body' : prog a) l1 l2,
  (forall s : state a ffi_t, evaluate (body, s) = evaluate (body', s)) ->
  forall s : state a ffi_t, evaluate (Loop l1 body l2, s) = evaluate (Loop l1 body' l2, s).
Proof.
  intros body body' l1 l2 H s.
  remember (N.to_nat (clock s)) as c eqn:Hc. revert s Hc.
  induction c as [c IH] using (well_founded_induction lt_wf). intros s Hc.
  rewrite (evaluate_unfold (Loop l1 body l2)), (evaluate_unfold (Loop l1 body' l2)).
  cbn [evaluate_body]; unfold fcl; cbn beta.
  destruct (cut_res l1 (NONE, s)) as [r s1] eqn:Ec. destruct r as [r|]; [reflexivity|].
  rewrite !fix_clock_evaluate, H.
  destruct (evaluate (body', s1)) as [r2 s2] eqn:Eb.
  assert (Hlt : (clock s2 < clock s)%N) by prove_lt.
  repeat match goal with |- context [match ?x with _ => _ end] =>
    lazymatch x with evaluate _ => fail | _ => destruct x; cbn beta iota zeta end end;
  try reflexivity; (eapply IH; [|reflexivity]; lia).
Qed.


(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "evaluate_no_Break_Continue" *)
Theorem evaluate_no_Break_Continue : forall (prog0 : prog a) (s : state a ffi_t) res t,
  evaluate (prog0, s) = (res, t) /\
  every_prog (fun r => (forall n, r <> loopLang.Break n) /\ (forall n, r <> loopLang.Continue n)) prog0 ->
  (forall n, res <> SOME (Break n)) /\ (forall n, res <> SOME (Continue n)).
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall res t, evaluate x = (res, t) ->
            every_prog (fun r => (forall n, r <> loopLang.Break n) /\ (forall n, r <> loopLang.Continue n)) (fst x) ->
            (forall n, res <> SOME (Break n)) /\ (forall n, res <> SOME (Continue n)))
    by (intros p s res t [H1 H2]; exact (G (p, s) res t H1 H2)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros res t H Hev; cbn [fst snd] in *.
  destruct p; unfold_eval_in H; split_eval H.
  all: repeat match goal with
         | Ev : evaluate (?p', ?s') = (?r', ?t') |- _ =>
             let G := fresh "G" in let Ck := fresh "Ck" in
             pose proof (IH (p', s') ltac:(prove_lt) r' t' Ev ltac:(cbn [fst every_prog] in *; tauto)) as G;
             pose proof (evaluate_clock _ _ _ _ Ev) as Ck; clear Ev
         end.
  all: repeat match goal with
         | E : cut_res _ (NONE, _) = (SOME _, _) |- _ =>
             apply cut_res_NONE_SOME in E; destruct E as [->| ->]
         | E : sh_mem_op _ _ _ _ = (_, _) |- _ =>
             apply sh_mem_op_res in E; destruct E as [->|[->|[? ->]]]
         end.
  all: unfold exit_loop in *; cbn beta iota in *; cbn [every_prog] in *; eqb_facts.
  all: try match type of H with (_, _) = (_, _) => injection H as <- <- end.
  all: try solve [split; intros ? ?; discriminate].
  all: first
    [ assumption
    | exfalso; match goal with
      | G : (forall n, SOME (Break ?m) <> _) /\ _ |- _ => exact (proj1 G m eq_refl)
      | G : _ /\ (forall n, SOME (Continue ?m) <> _) |- _ => exact (proj2 G m eq_refl)
      | G : (forall n, loopLang.Break ?m <> _) /\ _ |- _ => exact (proj1 G m eq_refl)
      | G : _ /\ (forall n, loopLang.Continue ?m <> _) |- _ => exact (proj2 G m eq_refl)
      end ].
Qed.


(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "locals_touched_eq_eval_eq" *)
Theorem locals_touched_eq_eval_eq : forall (s : state a ffi_t) e (t : state a ffi_t),
  globals s = globals t /\ memory s = memory t /\ mdomain s = mdomain t /\
  base_addr s = base_addr t /\ top_addr s = top_addr t /\
  (forall n, MEM n (locals_touched e) -> lookup n (locals s) = lookup n (locals t)) ->
  eval t e = eval s e.
Proof.
  intros s e t (H1 & H2 & H3 & H4 & H5 & H6). symmetry.
  apply eval_state_cong_gen; auto. intros n Hn; apply H6, MEM_In, Hn.
Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "get_var_imm_add_clk_eq" *)
Theorem get_var_imm_add_clk_eq : forall ri (s : state a ffi_t) ck,
  get_var_imm ri (set_clock ck s) = get_var_imm ri s.
Proof. intros [] s ck; reflexivity. Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "get_vars_local_clock_upd_eq" *)
Theorem get_vars_local_clock_upd_eq : forall ns (st : state a ffi_t) l ck,
  get_vars ns (set_clock ck (set_locals l st)) = get_vars ns (set_locals l st).
Proof. intros; apply get_vars_set_clock. Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "get_vars_clock_upd_eq" *)
Theorem get_vars_clock_upd_eq : forall ns (st : state a ffi_t) ck,
  get_vars ns (set_clock ck st) = get_vars ns st.
Proof. intros; apply get_vars_set_clock. Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "lookup_alist_insert_any" *)
Theorem lookup_alist_insert_any : forall (n : N) xs (ys : list (word_loc a)) t,
  lookup n (alist_insert xs ys t) =
  match ALOOKUP (ZIP (xs, ys)) n with NONE => lookup n t | SOME v => SOME v end.
Proof.
  intros n xs; induction xs as [|x xs IH]; intros [|y ys] t; try reflexivity.
  cbn [alist_insert ZIP ALOOKUP]. rewrite lookup_insert.
  destruct (decide (n = x)), (decide (x = n)); subst; try congruence.
  apply IH.
Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "get_vars_local_update_some_eq" *)
Theorem get_vars_local_update_some_eq : forall ns vs (st : state a ffi_t),
  ALL_DISTINCT ns /\ LENGTH ns = LENGTH vs ->
  get_vars ns (set_locals (alist_insert ns vs (locals st)) st) = SOME vs.
Proof.
  intros ns; induction ns as [|n ns IH]; intros [|v vs] st [Hd Hl];
    cbn [LENGTH] in Hl; try lia; [reflexivity|].
  unfold is_true in Hd; cbn [ALL_DISTINCT] in Hd. apply andb_prop in Hd as [Hn Hd].
  cbn [get_vars alist_insert locals set_locals]. rewrite lookup_insert1.
  rewrite <- alist_insert_pull_insert by (intros Hc; unfold is_true in Hc; rewrite Hc in Hn; discriminate).
  assert (Hl2 : LENGTH ns = LENGTH vs) by lia.
  specialize (IH vs (set_locals (insert n v (locals st)) st) (conj Hd Hl2)).
  cbn [locals set_locals] in IH. rewrite (get_vars_locals ns _ (set_locals (alist_insert ns vs (insert n v (locals st))) (set_locals (insert n v (locals st)) st))) by reflexivity.
  rewrite IH; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "lookup_set_vars" *)
Theorem lookup_set_vars : forall n xs ys (s : state a ffi_t),
  lookup n (locals (set_vars xs ys s)) =
  match ALOOKUP (ZIP (xs, ys)) n with NONE => lookup n (locals s) | SOME v => SOME v end.
Proof. intros; apply lookup_alist_insert_any. Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "lookup_set_vars_not_MEM" *)
Theorem lookup_set_vars_not_MEM : forall n xs ys (s : state a ffi_t),
  ~ MEM n xs -> lookup n (locals (set_vars xs ys s)) = lookup n (locals s).
Proof.
  intros n xs ys s H; rewrite lookup_set_vars.
  destruct (ALOOKUP (ZIP (xs, ys)) n) eqn:E; [|reflexivity].
  exfalso; apply H, MEM_In. apply ALOOKUP_In in E.
  revert ys E; induction xs as [|x xs IH]; intros [|y ys] E; cbn in E; try contradiction.
  destruct E as [E|E]; [injection E as -> _; left; reflexivity|right; eapply IH; eauto].
  intros Hm; apply H; unfold is_true; cbn [MEM]; rewrite Hm; destruct (bool_decide _); reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "loop_eval_nested_assign_distinct_eq" *)
Theorem loop_eval_nested_assign_distinct_eq : forall es ns (t : state a ffi_t) ev,
  MAP (eval t) es = MAP SOME ev /\
  distinct_lists ns (FLAT (MAP locals_touched es)) /\
  ALL_DISTINCT ns /\
  LENGTH ns = LENGTH es ->
  evaluate (nested_seq (MAP2 Assign ns es), t) =
  (NONE, set_locals (alist_insert ns ev (locals t)) t).
Proof.
  intros es; induction es as [|e es IH]; intros ns t ev (Hm & Hdl & Hd & Hl).
  - destruct ns; cbn [LENGTH] in Hl; [|lia]. destruct ev; [|discriminate].
    cbn [MAP2 nested_seq alist_insert]. rewrite evaluate_unfold; cbn [evaluate_body]. destruct t; reflexivity.
  - destruct ns as [|h ns]; cbn [LENGTH] in Hl; [lia|].
    destruct ev as [|v ev]; [discriminate|]. cbn [MAP] in Hm. injection Hm as Hv Hm.
    cbn [MAP2 nested_seq]. unfold_eval. rewrite evaluate_unfold; cbn [evaluate_body]. rewrite Hv.
    cbn beta iota.
    unfold is_true in Hd; cbn [ALL_DISTINCT] in Hd. apply andb_prop in Hd as [Hn Hd].
    rewrite distinct_lists_iff in Hdl.
    rewrite (IH ns (set_var h v t) ev).
    + cbn [alist_insert set_var set_locals locals].
      rewrite alist_insert_pull_insert by (intros Hc; unfold is_true in Hc; rewrite Hc in Hn; discriminate).
      reflexivity.
    + split; [|split; [|split]]; [| | exact Hd | lia].
      * rewrite <- Hm. apply map_ext_in; intros x Hx.
        symmetry; apply eval_state_cong_gen; try reflexivity.
        intros n Hn0; cbn [set_var set_locals locals]. rewrite lookup_insert.
        destruct (decide (n = h)) as [->|]; [|reflexivity].
        exfalso; apply (Hdl h); [left; reflexivity|]. cbn [MAP FLAT]. apply in_or_app; right.
        apply in_concat; exists (locals_touched x); split; [apply in_map|]; assumption.
      * apply distinct_lists_iff; intros x Hx1 Hx2. apply (Hdl x); [right; exact Hx1|].
        cbn [MAP FLAT]; apply in_or_app; right; exact Hx2.
Qed.

End Props1.

(** ** Unassigned variables *)

Section Props2.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma cut_state_eq live s s' :
  cut_state live s = SOME s' ->
  s' = set_locals (inter (locals s) live) s /\ domain live SUBSET domain (locals s).
Proof. unfold cut_state; destruct (classical_dec _); intros H; inversion H; auto. Qed.

Lemma cut_res_NONE_eq live s s' :
  cut_res live (NONE, s) = (NONE, s') ->
  s' = dec_clock (set_locals (inter (locals s) live) s) /\ clock s <> 0 /\
  domain live SUBSET domain (locals s).
Proof.
  cbn [cut_res IS_SOME]. destruct (cut_state live s) as [s0|] eqn:E; [|discriminate].
  apply cut_state_eq in E as [-> Hd]. cbn [clock set_locals].
  destruct (N.eqb_spec (clock s) 0); [discriminate|]. intros H; inversion H; auto.
Qed.

Lemma mem_store_locals adr w s st : mem_store adr w s = SOME st -> locals st = locals s.
Proof. unfold mem_store; destruct (classical_dec _); intros H; inversion H; reflexivity. Qed.

Lemma lookup_insert_ne {A} n k (v : A) (m : spt A) : n <> k -> lookup n (insert k v m) = lookup n m.
Proof. intros H; rewrite lookup_insert; destruct (decide (n = k)); congruence. Qed.

Lemma lookup_inter_dom {A} n (t : spt A) (l : num_set) :
  n IN domain l -> lookup n (inter t l) = lookup n t.
Proof. intros H; rewrite lookup_inter_alt; destruct (decide _); [reflexivity|contradiction]. Qed.

Lemma lookup_alist_insert_notin n xs (ys : list (word_loc a)) (m : spt (word_loc a)) :
  ~ In n xs -> lookup n (alist_insert xs ys m) = lookup n m.
Proof.
  intros H; rewrite lookup_alist_insert_any.
  destruct (ALOOKUP (ZIP (xs, ys)) n) eqn:E; [|reflexivity].
  exfalso; apply H; clear H. apply ALOOKUP_In in E.
  revert ys E; induction xs as [|x xs IH]; intros [|y ys] E; cbn in E; try contradiction.
  destruct E as [E|E]; [injection E as -> _; left; reflexivity|right; eapply IH; eauto].
Qed.

Lemma loop_arith_lookup s ar s' n :
  loop_arith s ar = SOME s' -> ~ In n (assigned_vars (@Arith a ar)) ->
  lookup n (locals s') = lookup n (locals s).
Proof.
  intros H Hn; destruct ar; cbn [loop_arith assigned_vars In] in *;
  repeat match type of H with
         | context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta in H
         | context [if ?x then _ else _] => destruct x; cbn beta iota zeta in H
         end; try discriminate; inversion H; subst; cbn [set_var set_locals locals];
  rewrite ?lookup_insert_ne by (intro; subst; tauto); reflexivity.
Qed.

Lemma sh_mem_op_lookup op r (ad : word a) s t n :
  sh_mem_op op r ad s = (NONE, t) -> n <> r -> lookup n (locals t) = lookup n (locals s).
Proof.
  intros H Hn; destruct op; cbn [sh_mem_op] in H; unfold sh_mem_load, sh_mem_store in H;
  repeat match type of H with
         | context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta in H
         | context [if ?x then _ else _] => destruct x; cbn beta iota zeta in H
         end; inversion H; subst; cbn [set_var set_ffi set_locals locals];
  rewrite ?lookup_insert_ne by exact Hn; reflexivity.
Qed.

End Props2.

(** Normalise the hypotheses produced by [split_eval]. *)
Ltac norm_hyps :=
  repeat match goal with
         | E : cut_res _ (NONE, _) = (NONE, _) |- _ =>
             apply cut_res_NONE_eq in E; destruct E as (-> & ? & ?)
         | E : cut_state _ _ = SOME _ |- _ => apply cut_state_eq in E; destruct E as (-> & ?)
         | E : cut_res _ (NONE, _) = (SOME _, _) |- _ =>
             apply cut_res_NONE_SOME in E; destruct E as [->| ->]
         | E : (_ =? _)%N = false |- _ => apply N.eqb_neq in E
         | E : (_ =? _)%N = true |- _ => apply N.eqb_eq in E
         end.

Ltac side_c :=
  first [ assumption | tauto | (intros ->; tauto)
        | (intros Hc; apply MEM_In in Hc; tauto) ].

Ltac lk_simp :=
  state_cbn;
  repeat first
    [ rewrite lookup_insert_ne by side_c
    | rewrite lookup_inter_dom by side_c
    | rewrite lookup_alist_insert_notin by side_c ].

Ltac lk_chain :=
  repeat progress (lk_simp;
    try match goal with
        | G : lookup ?n (locals ?x) = _ |- context [lookup ?n (locals ?x)] => rewrite G
        | G : locals ?x = _ |- context [locals ?x] => rewrite G
        end).

Ltac res_c :=
  first [ assumption | left; reflexivity | right; left; eexists; reflexivity
        | right; right; eexists; reflexivity ].

Section Props2b.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "unassigned_vars_evaluate_same" *)
Theorem unassigned_vars_evaluate_same : forall (p : prog a) s res t n v,
  evaluate (p, s) = (res, t) /\
  (res = NONE \/ (exists n, res = SOME (Continue n)) \/ (exists n, res = SOME (Break n))) /\
  lookup n (locals s) = SOME v /\
  ~ MEM n (assigned_vars p) /\ survives n p ->
  lookup n (locals t) = lookup n (locals s).
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall res t n v,
            evaluate x = (res, t) ->
            (res = NONE \/ (exists n, res = SOME (Continue n)) \/ (exists n, res = SOME (Break n))) ->
            lookup n (locals (snd x)) = SOME v ->
            ~ In n (assigned_vars (fst x)) -> survives n (fst x) ->
            lookup n (locals t) = lookup n (locals (snd x)))
    by (intros p s res t n v (H1 & H2 & H3 & H4 & H5);
        exact (G (p, s) res t n v H1 H2 H3 (fun Hc => H4 (proj2 (MEM_In _ _) Hc)) H5)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros res t n v H Hres HL Hm Hs; cbn [fst snd] in *.
  destruct p; unfold_eval_in H; split_eval H.
  all: cbn [assigned_vars survives] in Hm, Hs; repeat (cbn [In] in Hm; rewrite ?in_app_iff in Hm).
  all: try match type of H with (_, _) = (_, _) => injection H as <- <- end.
  all: norm_hyps.
  all: repeat match goal with
         | E : mem_store _ _ _ = SOME _ |- _ => apply mem_store_locals in E
         | E : loop_arith _ _ = SOME _ |- _ => apply (loop_arith_lookup _ _ _ n) in E; [|exact Hm]
         end.
  all: repeat match goal with
         | Ev : evaluate (?p', ?s') = (?r', ?t') |- _ =>
             let G := fresh "G" in let Ck := fresh "Ck" in
             assert (G : lookup n (locals t') = lookup n (locals s'))
               by (eapply (IH (p', s') ltac:(prove_lt) r' t' n);
                   [ exact Ev | res_c | cbn [snd]; lk_chain; first [reflexivity | eassumption]
                   | cbn [fst assigned_vars]; repeat (cbn [In]; rewrite ?in_app_iff); tauto
                   | cbn [fst survives]; tauto ]);
             pose proof (evaluate_clock _ _ _ _ Ev) as Ck; clear Ev
         end.
  all: try solve [destruct Hres as [Hr|[[? Hr]|[? Hr]]]; discriminate].
  all: try solve [lk_chain; reflexivity].
  all: try match goal with
         | H : sh_mem_op _ _ _ _ = (_, _) |- _ =>
             destruct Hres as [->|[[k ->]|[k ->]]];
             [ eapply sh_mem_op_lookup; [exact H | intro; subst; tauto]
             | apply sh_mem_op_res in H; destruct H as [Hr|[Hr|[? Hr]]]; discriminate.. ]
         end.
Qed.

End Props2b.

(** ** Nested sequences and [comp_syntax_ok] *)

Section Props3.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "evaluate_nested_seq_cases" *)
Theorem evaluate_nested_seq_cases :
  (forall (p q : list (prog a)) s st t,
    evaluate (nested_seq (p ++ q), s) = (NONE, t) /\
    evaluate (nested_seq p, s) = (NONE, st) ->
    evaluate (nested_seq q, st) = (NONE, t)) /\
  (forall (p : list (prog a)) s st q,
    evaluate (nested_seq p, s) = (NONE, st) ->
    evaluate (nested_seq (p ++ q), s) = evaluate (nested_seq q, st)) /\
  (forall (p : list (prog a)) s res st q,
    evaluate (nested_seq p, s) = (res, st) /\ res <> NONE ->
    evaluate (nested_seq (p ++ q), s) = evaluate (nested_seq p, s)).
Proof.
  assert (A2 : forall (p : list (prog a)) s st q,
    evaluate (nested_seq p, s) = (NONE, st) ->
    evaluate (nested_seq (p ++ q), s) = evaluate (nested_seq q, st)).
  { induction p as [|c p IH]; intros s st q H.
    - cbn [nested_seq app] in *. rewrite evaluate_unfold in H; cbn in H.
      injection H as <-; reflexivity.
    - cbn [nested_seq app] in *. unfold_eval_in H. unfold_eval.
      destruct (evaluate (c, s)) as [[r|] s1]; [discriminate|]. cbn beta iota in *.
      apply IH, H. }
  split; [|split; [exact A2|]].
  - intros p q s st t [H1 H2]. rewrite (A2 p s st q H2) in H1. exact H1.
  - induction p as [|c p IH]; intros s res st q [H Hr].
    + cbn [nested_seq] in H. rewrite evaluate_unfold in H; cbn in H. congruence.
    + cbn [nested_seq app] in *. rewrite H. unfold_eval. unfold_eval_in H.
      destruct (evaluate (c, s)) as [[r|] s1]; cbn beta iota in *; [exact H|].
      rewrite (IH s1 res st q (conj H Hr)). exact H.
Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "survives_nested_seq_intro" *)
Theorem survives_nested_seq_intro : forall (p q : list (prog a)) n,
  survives n (nested_seq p) /\ survives n (nested_seq q) ->
  survives n (nested_seq (p ++ q)).
Proof.
  induction p as [|c p IH]; intros q n [H1 H2]; cbn [nested_seq app survives] in *; [exact H2|].
  destruct H1; split; [assumption|apply IH; split; assumption].
Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "nested_assigns_survives" *)
Theorem nested_assigns_survives : forall xs (ys : list (exp a)) n,
  LENGTH xs = LENGTH ys -> survives n (nested_seq (MAP2 Assign xs ys)).
Proof.
  induction xs as [|x xs IH]; intros [|y ys] n H; cbn [LENGTH] in H; try lia; cbn; auto.
  split; [exact Logic.I|]. apply IH; lia.
Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "comp_syn_ok_seq2" *)
Theorem comp_syn_ok_seq2 : forall l (p q : prog a),
  comp_syntax_ok l p /\ comp_syntax_ok (cut_sets l p) q -> comp_syntax_ok l (Seq p q).
Proof. intros l p q H; exact H. Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "comp_syn_ok_nested_seq" *)
Theorem comp_syn_ok_nested_seq : forall (p q : list (prog a)) l,
  comp_syntax_ok l (nested_seq p) /\
  comp_syntax_ok (cut_sets l (nested_seq p)) (nested_seq q) ->
  comp_syntax_ok l (nested_seq (p ++ q)).
Proof.
  induction p as [|c p IH]; intros q l [H1 H2]; cbn [nested_seq app comp_syntax_ok cut_sets] in *;
    [exact H2|]. destruct H1 as [H1 H3]. split; [exact H1|]. apply IH; split; assumption.
Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "comp_syn_ok_nested_seq2" *)
Theorem comp_syn_ok_nested_seq2 : forall (p q : list (prog a)) l,
  comp_syntax_ok l (nested_seq (p ++ q)) ->
  comp_syntax_ok l (nested_seq p) /\
  comp_syntax_ok (cut_sets l (nested_seq p)) (nested_seq q).
Proof.
  induction p as [|c p IH]; intros q l H; cbn [nested_seq app comp_syntax_ok cut_sets] in *;
    [split; [exact Logic.I|exact H]|].
  destruct H as [H1 H2]. apply IH in H2 as [H2 H3]. tauto.
Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "cut_sets_nested_seq" *)
Theorem cut_sets_nested_seq : forall (p q : list (prog a)) l,
  cut_sets l (nested_seq (p ++ q)) = cut_sets (cut_sets l (nested_seq p)) (nested_seq q).
Proof.
  induction p as [|c p IH]; intros q l; [reflexivity|].
  change (cut_sets (cut_sets l c) (nested_seq (p ++ q)) =
          cut_sets (cut_sets (cut_sets l c) (nested_seq p)) (nested_seq q)).
  apply IH.
Qed.

Lemma FOLDL_insert_union : forall ns (l : num_set),
  exists l', FOLDL (fun sp n => insert n tt sp) l ns = union l l'.
Proof.
  induction ns as [|x ns IH]; intros l; cbn [FOLDL].
  - exists LN; symmetry; apply union_LN.
  - destruct (IH (insert x tt l)) as [l' ->]. exists (union (insert x tt LN) l').
    rewrite insert_union, union_assoc, (union_num_set_sym l). reflexivity.
Qed.

Lemma ins_union k (l : num_set) : insert k tt l = union l (insert k tt LN).
Proof. rewrite insert_union, union_num_set_sym; reflexivity. Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "cut_sets_union_accumulate" *)
Theorem cut_sets_union_accumulate : forall (p : prog a) l,
  comp_syntax_ok l p -> exists l' : num_set, cut_sets l p = union l l'.
Proof.
  induction p as [|n e|l0 pop r|ar|e n|w e|n m|n m|n m|n m|p1 p2 IHp1 IHp2|c n ri p1 p2 l0 IHp1 IHp2|l1 p1 l2 IHp|n|n|n|vs0|mo n e| |p1 IHp| |n m|ret dest args h H|str n1 n2 n3 n4 l0] using prog_nested_ind;
    intros l Hc; cbn [comp_syntax_ok] in Hc; try contradiction.
  - exists LN; exact (eq_sym (proj1 (union_LN l))).
  - eexists; exact (ins_union n l).
  - destruct ar; cbn [cut_sets];
      match goal with
      | |- exists l', insert ?x tt (insert ?y tt ?l) = _ =>
          rewrite (ins_union x), (ins_union y), <- union_assoc; eexists; reflexivity
      | |- exists l', insert ?x tt ?l = _ => eexists; exact (ins_union x l)
      end.
  - eexists; exact (ins_union m l).
  - eexists; exact (ins_union m l).
  - destruct Hc as [H1 H2]. cbn [cut_sets]. destruct (IHp1 l H1) as [l1 E1]. rewrite E1 in *.
    destruct (IHp2 _ H2) as [l2 E2]. rewrite E2. exists (union l1 l2). symmetry; apply union_assoc.
  - cbn [cut_sets]. destruct Hc as (_ & _ & ns & ->). apply FOLDL_insert_union.
  - exists LN; exact (eq_sym (proj1 (union_LN l))).
  - exists LN; exact (eq_sym (proj1 (union_LN l))).
  - eexists; exact (ins_union n l).
Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "cut_sets_union_domain_subset" *)
Theorem cut_sets_union_domain_subset : forall (p : prog a) l,
  comp_syntax_ok l p -> domain l SUBSET domain (cut_sets l p).
Proof.
  intros p l H; destruct (cut_sets_union_accumulate p l H) as [l' ->].
  intros x Hx; unfold pred_set.IN in *; rewrite domain_union; left; exact Hx.
Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "cut_sets_union_domain_union" *)
Theorem cut_sets_union_domain_union : forall (p : prog a) l,
  comp_syntax_ok l p -> exists l' : num_set, domain (cut_sets l p) = domain l UNION domain l'.
Proof.
  intros p l H; destruct (cut_sets_union_accumulate p l H) as [l' ->].
  exists l'; rewrite domain_union; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "comp_syn_impl_cut_sets_subspt" *)
Theorem comp_syn_impl_cut_sets_subspt : forall (p : prog a) l,
  comp_syntax_ok l p -> subspt l (cut_sets l p).
Proof.
  intros p l H; destruct (cut_sets_union_accumulate p l H) as [l' ->]. apply subspt_union.
Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "comp_syn_cut_sets_mem_domain" *)
Theorem comp_syn_cut_sets_mem_domain : forall (p : prog a) l n,
  comp_syntax_ok l p /\ n IN domain l -> n IN domain (cut_sets l p).
Proof. intros p l n [H1 H2]. exact (cut_sets_union_domain_subset p l H1 n H2). Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "assigned_vars_nested_seq_split" *)
Theorem assigned_vars_nested_seq_split : forall (p q : list (prog a)),
  assigned_vars (nested_seq (p ++ q)) =
  assigned_vars (nested_seq p) ++ assigned_vars (nested_seq q).
Proof.
  induction p as [|c p IH]; intros q; cbn [nested_seq app assigned_vars]; [reflexivity|].
  rewrite IH, app_assoc; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "assigned_vars_seq_split" *)
Theorem assigned_vars_seq_split : forall (q p : prog a),
  assigned_vars (Seq p q) = assigned_vars p ++ assigned_vars q.
Proof. reflexivity. Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "assigned_vars_nested_assign" *)
Theorem assigned_vars_nested_assign : forall xs (ys : list (exp a)),
  LENGTH xs = LENGTH ys -> assigned_vars (nested_seq (MAP2 Assign xs ys)) = xs.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; cbn [LENGTH] in H; try lia; [reflexivity|].
  cbn [MAP2 nested_seq assigned_vars app]. rewrite IH by lia. reflexivity.
Qed.


(** [t] differs from [s] only in its locals and clock. *)
Definition lc_eq s t : Prop :=
  globals t = globals s /\ memory t = memory s /\ mdomain t = mdomain s /\
  sh_mdomain t = sh_mdomain s /\ code t = code s /\ be t = be s /\ ffi t = ffi s /\
  base_addr t = base_addr s /\ top_addr t = top_addr s.

Lemma lc_eq_iff s t : t = set_clock (clock t) (set_locals (locals t) s) <-> lc_eq s t.
Proof.
  destruct s, t; unfold lc_eq; cbn; split.
  - intros H; injection H; intros; subst; repeat split.
  - intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9); subst; reflexivity.
Qed.

Lemma cut_res_lc l r s r' s' : cut_res l (r, s) = (r', s') -> lc_eq s s'.
Proof.
  unfold cut_res; destruct (IS_SOME r); [intros H; inversion H; subst; repeat split|].
  destruct (cut_state l s) as [s0|] eqn:E; [|intros H; inversion H; subst; repeat split].
  apply cut_state_eq in E as [-> _].
  destruct (_ =? _)%N; intros H; inversion H; subst; repeat split.
Qed.

Ltac lc_solve :=
  unfold lc_eq in *; state_cbn;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat split; congruence.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "comp_syn_ok_upd_local_clock" *)
Theorem comp_syn_ok_upd_local_clock : forall (p : prog a) s res t l,
  evaluate (p, s) = (res, t) /\ comp_syntax_ok l p ->
  t = set_clock (clock t) (set_locals (locals t) s).
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall res t l,
            evaluate x = (res, t) -> comp_syntax_ok l (fst x) -> lc_eq (snd x) t)
    by (intros p s res t l [H1 H2]; apply lc_eq_iff; exact (G (p, s) res t l H1 H2)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros res t l H Hc; cbn [fst snd] in *.
  destruct p; pose proof Hc as Hc0; cbn [comp_syntax_ok] in Hc; try contradiction;
    unfold_eval_in H; split_eval H.
  all: try match type of H with (_, _) = (_, _) => injection H as <- <- end.
  all: repeat match goal with E : cut_res _ (NONE, _) = (SOME _, _) |- _ => apply cut_res_lc in E end.
  all: norm_hyps.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: repeat match goal with
         | Ev : evaluate (?p', ?s') = (?r', ?t') |- _ =>
             let G := fresh "G" in let Ck := fresh "Ck" in
             assert (G : lc_eq s' t')
               by (eapply (IH (p', s') ltac:(prove_lt) r' t'); [exact Ev|];
                   cbn [fst]; first [exact Hc0 | eassumption]);
             pose proof (evaluate_clock _ _ _ _ Ev) as Ck; clear Ev
         end.
  all: try match goal with
         | E : loop_arith _ ?ar = SOME _ |- _ =>
             destruct ar; cbn [loop_arith] in E;
             repeat match type of E with
                    | context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta in E
                    | context [if ?x then _ else _] => destruct x; cbn beta iota zeta in E
                    end; try discriminate; injection E as <-
         end.
  all: try solve [lc_solve].
Qed.

Lemma cut_res_lookup l r s r' s' n :
  cut_res l (r, s) = (r', s') -> n IN domain l ->
  lookup n (locals s') = lookup n (locals s) \/ r' = SOME TimeOut.
Proof.
  intros H Hn; unfold cut_res in H; destruct (IS_SOME r); [inversion H; auto|].
  destruct (cut_state l s) as [s0|] eqn:E; [|inversion H; auto].
  apply cut_state_eq in E as [-> _].
  destruct (_ =? _)%N; inversion H; subst; auto.
  left; cbn [dec_clock set_clock set_locals locals]. apply lookup_inter_dom, Hn.
Qed.

Lemma FOLDL_insert_domain : forall ns (l : num_set) n,
  n IN domain l -> n IN domain (FOLDL (fun sp n => insert n tt sp) l ns).
Proof.
  intros ns l n H; destruct (FOLDL_insert_union ns l) as [l' ->].
  unfold pred_set.IN in *; rewrite domain_union; left; exact H.
Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "comp_syn_ok_lookup_locals_eq" *)
Theorem comp_syn_ok_lookup_locals_eq : forall (p : prog a) s res t l n,
  evaluate (p, s) = (res, t) /\ res <> SOME TimeOut /\
  comp_syntax_ok l p /\ n IN domain l /\ ~ MEM n (assigned_vars p) ->
  lookup n (locals t) = lookup n (locals s).
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall res t l n,
            evaluate x = (res, t) -> res <> SOME TimeOut ->
            comp_syntax_ok l (fst x) -> n IN domain l -> ~ In n (assigned_vars (fst x)) ->
            lookup n (locals t) = lookup n (locals (snd x)))
    by (intros p s res t l n (H1 & H2 & H3 & H4 & H5);
        exact (G (p, s) res t l n H1 H2 H3 H4 (fun Hc => H5 (proj2 (MEM_In _ _) Hc)))).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros res t l n H Hres Hc Hn Hm; cbn [fst snd] in *.
  destruct p; cbn [comp_syntax_ok] in Hc; try contradiction; unfold_eval_in H; split_eval H.
  all: cbn [assigned_vars] in Hm; repeat (cbn [In] in Hm; rewrite ?in_app_iff in Hm).
  all: try match type of H with (_, _) = (_, _) => injection H as <- <- end.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H | H : exists _, _ |- _ => destruct H end; subst.
  all: repeat match goal with E : cut_res _ (NONE, _) = (SOME _, _) |- _ =>
         apply (cut_res_lookup _ _ _ _ _ n) in E; [destruct E as [E|E]; [|congruence]|assumption] end.
  all: norm_hyps.
  all: try match goal with H : ?x = FOLDL _ _ _ |- _ =>
         assert (n IN domain x) by (rewrite H; apply FOLDL_insert_domain; assumption) end.
  all: repeat match goal with
         | E : loop_arith _ _ = SOME _ |- _ => apply (loop_arith_lookup _ _ _ n) in E; [|exact Hm]
         end.
  all: repeat match goal with
         | Ev : evaluate (?p', ?s') = (?r', ?t') |- _ =>
             let G := fresh "G" in let Ck := fresh "Ck" in
             assert (G : lookup n (locals t') = lookup n (locals s'))
               by (eapply (IH (p', s') ltac:(prove_lt) r' t'); [exact Ev | try discriminate; assumption
                   | cbn [fst comp_syntax_ok]; first [eassumption | tauto]
                   | first [eassumption | apply FOLDL_insert_domain; assumption
                           | apply comp_syn_cut_sets_mem_domain; split; assumption]
                   | cbn [fst assigned_vars]; repeat (cbn [In]; rewrite ?in_app_iff); tauto]);
             pose proof (evaluate_clock _ _ _ _ Ev) as Ck; clear Ev
         end.
  all: try solve [lk_chain; reflexivity].
  all: try solve [exfalso; apply Hres; reflexivity].
  all: try (lk_chain; first [reflexivity | (rewrite lookup_inter_dom by (apply FOLDL_insert_domain; assumption); lk_chain; reflexivity)]).
Qed.

End Props3.

(** ** Adding clock *)

Section Clock1.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma set_locals_set_clock l k s : set_locals l (set_clock k s) = set_clock k (set_locals l s).
Proof. reflexivity. Qed.
Lemma set_memory_set_clock m k s : set_memory m (set_clock k s) = set_clock k (set_memory m s).
Proof. reflexivity. Qed.
Lemma set_ffi_set_clock f k s : set_ffi f (set_clock k s) = set_clock k (set_ffi f s).
Proof. reflexivity. Qed.
Lemma set_var_set_clock v w k s : set_var v w (set_clock k s) = set_clock k (set_var v w s).
Proof. reflexivity. Qed.
Lemma set_vars_set_clock v w k s : set_vars v w (set_clock k s) = set_clock k (set_vars v w s).
Proof. reflexivity. Qed.
Lemma set_globals_set_clock v w k s : set_globals v w (set_clock k s) = set_clock k (set_globals v w s).
Proof. reflexivity. Qed.
Lemma call_env_set_clock v k s : call_env v (set_clock k s) = set_clock k (call_env v s).
Proof. reflexivity. Qed.
Lemma dec_clock_set_clock k s : dec_clock (set_clock k s) = set_clock (k - 1) s.
Proof. reflexivity. Qed.
Lemma set_clock_set_clock k1 k2 s : set_clock k1 (set_clock k2 s) = set_clock k1 s.
Proof. reflexivity. Qed.
Lemma locals_set_clock k s : locals (set_clock k s) = locals s. Proof. reflexivity. Qed.
Lemma globals_set_clock k s : globals (set_clock k s) = globals s. Proof. reflexivity. Qed.
Lemma memory_set_clock k s : memory (set_clock k s) = memory s. Proof. reflexivity. Qed.
Lemma mdomain_set_clock k s : mdomain (set_clock k s) = mdomain s. Proof. reflexivity. Qed.
Lemma sh_mdomain_set_clock k s : sh_mdomain (set_clock k s) = sh_mdomain s. Proof. reflexivity. Qed.
Lemma code_set_clock k s : code (set_clock k s) = code s. Proof. reflexivity. Qed.
Lemma be_set_clock k s : be (set_clock k s) = be s. Proof. reflexivity. Qed.
Lemma ffi_set_clock k s : ffi (set_clock k s) = ffi s. Proof. reflexivity. Qed.
Lemma clock_set_clock k s : clock (set_clock k s) = k. Proof. reflexivity. Qed.
Lemma get_var_imm_set_clock ri k s : get_var_imm ri (set_clock k s) = get_var_imm ri s.
Proof. destruct ri; reflexivity. Qed.

Lemma loop_arith_set_clock k s ar :
  loop_arith (set_clock k s) ar = OPTION_MAP (set_clock k) (loop_arith s ar).
Proof.
  destruct ar; cbn [loop_arith locals set_clock];
  repeat match goal with |- context [match ?x with _ => _ end] =>
    lazymatch x with set_clock _ _ => fail | _ => destruct x end end; reflexivity.
Qed.

Lemma mem_store_set_clock adr w k s :
  mem_store adr w (set_clock k s) = OPTION_MAP (set_clock k) (mem_store adr w s).
Proof. unfold mem_store; cbn [mdomain set_clock]; destruct (classical_dec _); reflexivity. Qed.

Lemma cut_state_set_clock l k s :
  cut_state l (set_clock k s) = OPTION_MAP (set_clock k) (cut_state l s).
Proof. unfold cut_state; cbn [locals set_clock]; destruct (classical_dec _); reflexivity. Qed.

Lemma sh_mem_op_set_clock op r ad k s :
  sh_mem_op op r ad (set_clock k s) =
  (fst (sh_mem_op op r ad s), set_clock k (snd (sh_mem_op op r ad s))).
Proof.
  destruct op; cbn [sh_mem_op]; unfold sh_mem_load, sh_mem_store; cbn [locals ffi sh_mdomain set_clock];
  repeat match goal with |- context [match ?x with _ => _ end] =>
    lazymatch x with set_clock _ _ => fail | _ => destruct x end end; reflexivity.
Qed.

End Clock1.

Create Rewrite HintDb clk.
#[global] Hint Rewrite @set_locals_set_clock @set_memory_set_clock @set_ffi_set_clock
  @set_var_set_clock @set_vars_set_clock @set_globals_set_clock @call_env_set_clock
  @dec_clock_set_clock @set_clock_set_clock @locals_set_clock @globals_set_clock
  @memory_set_clock @mdomain_set_clock @sh_mdomain_set_clock @code_set_clock @be_set_clock
  @ffi_set_clock @clock_set_clock @get_var_imm_set_clock @loop_arith_set_clock
  @mem_store_set_clock @cut_state_set_clock @sh_mem_op_set_clock @eval_set_clock
  @get_vars_set_clock : clk.

Section Clock2.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma cut_res_add_clock' l r s q s' ck :
  cut_res l (r, s) = (q, s') -> q <> SOME TimeOut ->
  cut_res l (r, set_clock (clock s + ck) s) = (q, set_clock (clock s' + ck) s').
Proof.
  unfold cut_res; destruct (IS_SOME r); [intros H _; inversion H; reflexivity|].
  rewrite cut_state_set_clock. destruct (cut_state l s) as [s0|] eqn:E; cbn [OPTION_MAP];
    [|intros H _; inversion H; reflexivity].
  pose proof (cut_state_clock _ _ _ E) as Hc.
  destruct (N.eqb_spec (clock s0) 0) as [Z|Z]; intros H Hq; inversion H; subst; [congruence|].
  cbn [clock set_clock]. destruct (N.eqb_spec (clock s + ck) 0); [lia|].
  f_equal. unfold dec_clock, set_clock; cbn [clock]. f_equal. lia.
Qed.

Ltac state_eq :=
  unfold dec_clock, call_env, set_var, set_vars, set_globals, set_clock, set_locals, set_memory, set_ffi;
  cbn [clock locals globals memory mdomain sh_mdomain code be ffi base_addr top_addr];
  f_equal; lia.

Lemma cut_res_not_timeout l r s q s' :
  cut_res l (r, s) = (q, s') -> q <> SOME TimeOut -> r <> SOME TimeOut.
Proof. intros H Hq ->; cbn in H; inversion H; subst; congruence. Qed.

Ltac rnt := first [discriminate | assumption | congruence
  | match goal with E : cut_res _ (?r, _) = (?q, _) |- ?r <> _ =>
      eapply cut_res_not_timeout; [exact E|assumption] end].

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "evaluate_add_clock_eq" *)
Theorem evaluate_add_clock_eq : forall (p : prog a) t res st ck,
  evaluate (p, t) = (res, st) /\ res <> SOME TimeOut ->
  evaluate (p, set_clock (clock t + ck) t) = (res, set_clock (clock st + ck) st).
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall res st ck,
            evaluate x = (res, st) -> res <> SOME TimeOut ->
            evaluate (fst x, set_clock (clock (snd x) + ck) (snd x)) =
              (res, set_clock (clock st + ck) st))
    by (intros p t res st ck [H1 H2]; exact (G (p, t) res st ck H1 H2)).
  intros x; induction x as [[p t] IH] using (well_founded_induction eval_lt_wf).
  intros res st ck H Hres; cbn [fst snd] in *.
  destruct p; unfold_eval_in H; unfold_eval.
  all: repeat first
    [ rewrite fix_clock_evaluate in H
    | split_nonrec H
    | match type of H with
      | evaluate _ = _ => fail 1
      | context [evaluate ?x] =>
          let r := fresh "r" in let t := fresh "t" in let E := fresh "Ev" in
          destruct (evaluate x) as [r t] eqn:E; cbn beta iota zeta in H
      end ].
  all: try match type of H with (_, _) = (_, _) => injection H as <- <- end.
  all: unfold exit_loop in Hres; cbn beta iota in Hres.
  all: try (exfalso; apply Hres; reflexivity).
  all: repeat match goal with
         | E : (?k =? 0)%N = false |- _ =>
             let c := fresh "C" in pose proof (proj1 (N.eqb_neq _ _) E) as c; revert E
         end; intros.
  all: repeat match goal with
         | E : loop_arith _ _ = SOME _ |- _ =>
             let c := fresh "C" in pose proof (loop_arith_clock _ _ _ E) as c; revert E
         | E : mem_store _ _ _ = SOME _ |- _ =>
             let c := fresh "C" in pose proof (mem_store_clock _ _ _ _ E) as c; revert E
         | E : cut_state _ _ = SOME _ |- _ =>
             let c := fresh "C" in pose proof (cut_state_clock _ _ _ E) as c; revert E
         | E : sh_mem_op _ _ _ _ = (_, _) |- _ =>
             let c := fresh "C" in pose proof (sh_mem_op_clock _ _ _ _ _ _ E) as c; revert E
         end; intros.
  all: repeat first
    [ progress (autorewrite with clk)
    | progress (cbn beta iota zeta)
    | rewrite fix_clock_evaluate
    | progress (unfold exit_loop)
    | progress (cbn [option_map fst snd])
    | match goal with
      | E : ?x = _ |- context [?x] =>
          tryif is_var x then fail else
          lazymatch x with evaluate _ => fail | cut_res _ _ => fail | _ => rewrite E end
      end
    | match goal with
      | |- context [(?k + ?c =? 0)%N] => rewrite (proj2 (N.eqb_neq (k + c) 0)) by lia
      end
    | match goal with
      | |- context [evaluate (?c, ?X)] =>
          match goal with
          | Ev : evaluate (c, ?s') = (?r, ?s'') |- _ =>
              replace X with (set_clock (clock s' + ck) s') by state_eq;
              let HH := fresh "HH" in
              pose proof (IH (c, s') ltac:(prove_lt) r s'' ck Ev ltac:(rnt)) as HH;
              cbn [fst snd] in HH; rewrite HH; clear HH
          end
      end
    | match goal with
      | |- context [cut_res ?l (?r, ?X)] =>
          match goal with
          | E : cut_res l (r, ?Y) = (?q, ?Y') |- _ =>
              replace X with (set_clock (clock Y + ck) Y) by state_eq;
              rewrite (cut_res_add_clock' _ _ _ _ _ ck E ltac:(rnt))
          end
      end ].
  all: try solve [first [reflexivity | f_equal; state_eq]].
Qed.


(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "eval_upd_clock_eq" *)
Theorem eval_upd_clock_eq : forall t e ck, eval (set_clock ck t) e = eval t e.
Proof. intros; rewrite eval_set_clock; reflexivity. Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "eval_upd_locals_clock_eq" *)
Theorem eval_upd_locals_clock_eq : forall t e l ck,
  eval (set_clock ck (set_locals l t)) e = eval (set_locals l t) e.
Proof. intros; rewrite eval_set_clock; reflexivity. Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "cut_res_add_clock" *)
Theorem cut_res_add_clock : forall l res s q r ck,
  cut_res l (res, s) = (q, r) /\ q <> SOME TimeOut ->
  cut_res l (res, set_clock (ck + clock s) s) = (q, set_clock (ck + clock r) r).
Proof.
  intros l res s q r ck [H1 H2]. rewrite !(N.add_comm ck).
  exact (cut_res_add_clock' l res s q r ck H1 H2).
Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "get_vars_clock" *)
Theorem get_vars_clock : forall vs s c, get_vars vs (set_clock c s) = get_vars vs s.
Proof. intros; apply get_vars_set_clock. Qed.

End Clock2.

(** ** Nested sequences, I/O events *)

Section Props4.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "evaluate_nested_seq_comb_seq" *)
Theorem evaluate_nested_seq_comb_seq : forall (p q : list (prog a)) t,
  evaluate (Seq (nested_seq p) (nested_seq q), t) = evaluate (nested_seq (p ++ q), t).
Proof.
  intros p q t. destruct (@evaluate_nested_seq_cases a ffi_t) as (_ & C2 & C3).
  unfold_eval. destruct (evaluate (nested_seq p, t)) as [[r|] s1] eqn:E; cbn beta iota.
  - assert (Hn : SOME r <> NONE) by discriminate.
    rewrite (C3 p t (SOME r) s1 q (conj E Hn)). exact (eq_sym E).
  - symmetry; apply C2, E.
Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "nested_seq_pure_evaluation" *)
Theorem nested_seq_pure_evaluation : forall (p q : list (prog a)) t r st l m e v ck ck',
  evaluate (nested_seq p, set_clock (ck + clock t) t) = (NONE, st) /\
  evaluate (nested_seq q, set_clock (ck' + clock st) st) = (NONE, r) /\
  comp_syntax_ok l (nested_seq p) /\
  comp_syntax_ok (cut_sets l (nested_seq p)) (nested_seq q) /\
  (forall n, MEM n (assigned_vars (nested_seq p)) -> n < m) /\
  (forall n, MEM n (assigned_vars (nested_seq q)) -> m <= n) /\
  (forall n, MEM n (locals_touched e) -> n < m /\ n IN domain (cut_sets l (nested_seq p))) /\
  eval st e = SOME v ->
  eval r e = SOME v.
Proof.
  intros p q t r st l m e v ck ck' (H1 & H2 & Hc1 & Hc2 & Hp & Hq & He & Hv).
  rewrite <- Hv.
  pose proof (comp_syn_ok_upd_local_clock _ _ _ _ _ (conj H2 Hc2)) as Hr.
  apply lc_eq_iff in Hr. destruct Hr as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
  apply eval_state_cong_gen; cbn [globals memory mdomain base_addr top_addr set_clock] in *;
    try congruence.
  intros n Hn. apply MEM_In in Hn. destruct (He n Hn) as [Hlt Hd].
  assert (Hn1 : (NONE : option (result a)) <> SOME TimeOut) by discriminate.
  assert (Hn2 : ~ MEM n (assigned_vars (nested_seq q))) by (intros Hm; specialize (Hq n Hm); lia).
  rewrite (comp_syn_ok_lookup_locals_eq (nested_seq q) _ NONE r _ n
             (conj H2 (conj Hn1 (conj Hc2 (conj Hd Hn2))))).
  reflexivity.
Qed.


Lemma pre_refl {A} `{EqDecision A} (l : list A) : is_true (isPREFIX l l).
Proof. induction l; cbn; unfold is_true in *; [reflexivity|]. rewrite IHl, bool_decide_eq_true_2 by reflexivity; reflexivity. Qed.

Lemma pre_trans {A} `{EqDecision A} (l1 l2 l3 : list A) :
  is_true (isPREFIX l1 l2) -> is_true (isPREFIX l2 l3) -> is_true (isPREFIX l1 l3).
Proof.
  revert l2 l3; induction l1 as [|x l1 IH]; intros [|y l2] [|z l3]; cbn; unfold is_true; auto; try discriminate.
  intros H1 H2. apply andb_prop in H1 as [E1 H1]; apply andb_prop in H2 as [E2 H2].
  apply bool_decide_spec in E1, E2; subst. rewrite bool_decide_eq_true_2 by reflexivity.
  cbn. eapply IH; eassumption.
Qed.

Lemma pre_app {A} `{EqDecision A} (l1 l2 : list A) : is_true (isPREFIX l1 (l1 ++ l2)).
Proof. induction l1; cbn; unfold is_true in *; [reflexivity|]. rewrite IHl1, bool_decide_eq_true_2 by reflexivity; reflexivity. Qed.

Lemma call_FFI_prefix (st : ffi_state ffi_t) n c b st' bs :
  call_FFI st n c b = FFI_return st' bs -> is_true (isPREFIX (io_events st) (io_events st')).
Proof.
  unfold call_FFI. destruct (negb _); [|intros H; inversion H; apply pre_refl].
  destruct (ffi_state_oracle st _ _ _ _); [|discriminate].
  destruct (_ =? _)%N; [|discriminate]. intros H; inversion H; cbn. apply pre_app.
Qed.

Lemma sh_mem_op_prefix op r (ad : word a) s res t :
  sh_mem_op op r ad s = (res, t) -> is_true (isPREFIX (io_events (ffi s)) (io_events (ffi t))).
Proof.
  intros H; destruct op; cbn [sh_mem_op] in H; unfold sh_mem_load, sh_mem_store in H;
  repeat match type of H with
         | context [match ?x with _ => _ end] =>
             let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H
         | context [if ?x then _ else _] => destruct x; cbn beta iota zeta in H
         end; inversion H; subst; cbn [set_var set_ffi set_locals call_env ffi];
  first [apply pre_refl | eapply call_FFI_prefix; eassumption].
Qed.

Lemma cut_res_ffi l r s r' s' : cut_res l (r, s) = (r', s') -> ffi s' = ffi s.
Proof.
  unfold cut_res; destruct (IS_SOME r); [intros H; inversion H; reflexivity|].
  destruct (cut_state l s) as [s0|] eqn:E; [|intros H; inversion H; reflexivity].
  apply cut_state_eq in E as [-> _]. destruct (_ =? _)%N; intros H; inversion H; reflexivity.
Qed.

Lemma ffi_loop_arith s ar s' : loop_arith s ar = SOME s' -> ffi s' = ffi s.
Proof.
  intros H; destruct ar; cbn [loop_arith] in H;
  repeat match type of H with
         | context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta in H
         | context [if ?x then _ else _] => destruct x; cbn beta iota zeta in H
         end; try discriminate; inversion H; reflexivity.
Qed.

Lemma ffi_mem_store adr w s st : mem_store adr w s = SOME st -> ffi st = ffi s.
Proof. unfold mem_store; destruct (classical_dec _); intros H; inversion H; reflexivity. Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "evaluate_io_events_mono" *)
Theorem evaluate_io_events_mono : forall (exps : prog a) s1 res s2,
  evaluate (exps, s1) = (res, s2) ->
  is_true (isPREFIX (io_events (ffi s1)) (io_events (ffi s2))).
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall res s2,
            evaluate x = (res, s2) ->
            is_true (isPREFIX (io_events (ffi (snd x))) (io_events (ffi s2))))
    by (intros p s res t H; exact (G (p, s) res t H)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros res t H; cbn [snd].
  destruct p; unfold_eval_in H; split_eval H.
  all: try match type of H with (_, _) = (_, _) => injection H as <- <- end.
  all: repeat match goal with
         | E : cut_res _ (_, _) = (_, _) |- _ =>
             let c := fresh "F" in pose proof (cut_res_ffi _ _ _ _ _ E) as c; revert E
         | E : loop_arith _ _ = SOME _ |- _ =>
             let c := fresh "F" in pose proof (ffi_loop_arith _ _ _ E) as c; revert E
         | E : mem_store _ _ _ = SOME _ |- _ =>
             let c := fresh "F" in pose proof (ffi_mem_store _ _ _ _ E) as c; revert E
         | E : cut_state _ _ = SOME _ |- _ =>
             let c := fresh "F" in pose proof (f_equal ffi (proj1 (cut_state_eq _ _ _ E))) as c; revert E
         | E : sh_mem_op _ _ _ _ = (_, _) |- _ =>
             let c := fresh "P" in pose proof (sh_mem_op_prefix _ _ _ _ _ _ E) as c; revert E
         | E : call_FFI _ _ _ _ = FFI_return _ _ |- _ =>
             let c := fresh "P" in pose proof (call_FFI_prefix _ _ _ _ _ _ E) as c; revert E
         end; intros.
  all: repeat match goal with
         | Ev : evaluate (?p', ?s') = (?r', ?t') |- _ =>
             let G := fresh "P" in let Ck := fresh "Ck" in
             pose proof (IH (p', s') ltac:(prove_lt) r' t' Ev) as G;
             pose proof (evaluate_clock _ _ _ _ Ev) as Ck; clear Ev
         end.
  all: cbn [snd fst] in *; state_cbn.
  all: repeat match goal with
         | F : ffi ?x = _ |- context [ffi ?x] => rewrite F
         | P : is_true (isPREFIX _ (io_events (ffi ?x))) |- is_true (isPREFIX _ (io_events (ffi ?x))) =>
             eapply pre_trans; [|exact P]; clear P
         | P : is_true (isPREFIX _ (io_events ?x)) |- is_true (isPREFIX _ (io_events ?x)) =>
             eapply pre_trans; [|exact P]; clear P
         end.
  all: try apply pre_refl.
Qed.

End Props4.

Section Props5.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma io_whole (p : prog a) s q u :
  evaluate (p, s) = (q, u) -> is_true (isPREFIX (io_events (ffi s)) (io_events (ffi u))).
Proof. apply evaluate_io_events_mono. Qed.

Lemma io_cut l r s r' s' : cut_res l (r, s) = (r', s') -> io_events (ffi s') = io_events (ffi s).
Proof. intros H. rewrite (cut_res_ffi _ _ _ _ _ H). reflexivity. Qed.

(*! HOL "cakeml/pancake/semantics/loopPropsScript.sml" "evaluate_add_clock_io_events_mono" *)
Theorem evaluate_add_clock_io_events_mono : forall (exps : prog a) s extra,
  is_true (isPREFIX (io_events (ffi (snd (evaluate (exps, s)))))
    (io_events (ffi (snd (evaluate (exps, set_clock (clock s + extra) s)))))).
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall extra,
            is_true (isPREFIX (io_events (ffi (snd (evaluate x))))
              (io_events (ffi (snd (evaluate (fst x, set_clock (clock (snd x) + extra) (snd x))))))))
    by (intros p s extra; exact (G (p, s) extra)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros e; cbn [fst snd].
  assert (IH' : forall p' s', eval_lt (p', s') (p, s) -> forall e r t q u,
             evaluate (p', s') = (r, t) -> evaluate (p', set_clock (clock s' + e) s') = (q, u) ->
             is_true (isPREFIX (io_events (ffi t)) (io_events (ffi u)))).
  { intros p' s' Hlt e' r t q u E1 E2. pose proof (IH (p', s') Hlt e') as G.
    cbn [fst snd] in G. rewrite E1, E2 in G. exact G. }
  clear IH.
  destruct (evaluate (p, s)) as [r t] eqn:H.
  destruct (decide (r = SOME TimeOut)) as [->|Hr].
  2: { rewrite (evaluate_add_clock_eq p s r t e (conj H Hr)). cbn [snd ffi set_clock].
       apply pre_refl. }
  cbn [snd].
  destruct (evaluate (p, set_clock (clock s + e) s)) as [q u] eqn:H2. cbn [snd].
  pose proof (io_whole _ _ _ _ H2) as Hw. cbn [ffi set_clock] in Hw.
  assert (Hnt : forall {B} (x : B), (NONE : option (result a)) <> SOME TimeOut) by discriminate.
  destruct p as [ | | | | | | | | | | p1 p2 | c n ri p1 p2 live | li body lo | | | | | | | p | | |
                 ret dest args handler | ];
    unfold_eval_in H; unfold_eval_in H2.
  - (* Skip *) injection H as Hx _; discriminate.
  - (* Assign *) split_eval H; injection H as Hx _; discriminate.
  - (* Primitive *) split_eval H; injection H as Hx _; discriminate.
  - (* Arith *) split_eval H; injection H as Hx _; discriminate.
  - (* Store *) split_eval H; injection H as Hx _; discriminate.
  - (* SetGlobal *) split_eval H; injection H as Hx _; discriminate.
  - (* Load32 *) split_eval H; injection H as Hx _; discriminate.
  - (* LoadByte *) split_eval H; injection H as Hx _; discriminate.
  - (* Store32 *) split_eval H; injection H as Hx _; discriminate.
  - (* StoreByte *) split_eval H; injection H as Hx _; discriminate.
  - (* Seq *)
    destruct (evaluate (p1, s)) as [r1 s1] eqn:E1.
    destruct r1 as [r1|].
    + injection H as -> <-.
      destruct (evaluate (p1, set_clock (clock s + e) s)) as [r1' s1'] eqn:E1'.
      pose proof (IH' p1 s ltac:(prove_lt) e _ _ _ _ E1 E1') as P1.
      destruct r1' as [r1'|]; [injection H2 as _ <-; exact P1|].
      eapply pre_trans; [exact P1|exact (io_whole _ _ _ _ H2)].
    + rewrite (evaluate_add_clock_eq p1 s NONE s1 e (conj E1 (Hnt _ tt))) in H2.
      cbv beta iota in H2.
      exact (IH' p2 s1 ltac:(prove_lt) e _ _ _ _ H H2).
  - (* If *)
    cbn [locals set_clock get_var_imm] in H2.
    destruct (lookup n (locals s)) as [[x|]|]; try (injection H as Hx _; discriminate).
    replace (get_var_imm ri (set_clock (clock s + e) s)) with (get_var_imm ri s) in H2
      by (destruct ri; reflexivity).
    destruct (get_var_imm ri s) as [[y|]|]; try (injection H as Hx _; discriminate).
    cbv zeta in H, H2.
    destruct (word_cmp c x y);
    [ destruct (evaluate (p1, s)) as [rb tb] eqn:Eb | destruct (evaluate (p2, s)) as [rb tb] eqn:Eb ];
    (destruct (decide (rb = SOME TimeOut)) as [->|Hrb];
     [ cbn [cut_res IS_SOME] in H; injection H as <-;
       match type of H2 with cut_res _ (evaluate (?c, ?X)) = _ =>
         destruct (evaluate (c, X)) as [rb' tb'] eqn:Eb' end;
       rewrite (io_cut _ _ _ _ _ H2);
       (eapply IH'; [|exact Eb|exact Eb']); prove_lt
     | rewrite (evaluate_add_clock_eq _ s rb tb e (conj Eb Hrb)) in H2;
       rewrite (io_cut _ _ _ _ _ H), (io_cut _ _ _ _ _ H2); cbn [ffi set_clock]; apply pre_refl ]).
  - (* Loop *)
    destruct (cut_res li (NONE, s)) as [[c|] s'] eqn:Ec.
    + injection H as _ <-. rewrite (io_cut _ _ _ _ _ Ec). exact Hw.
    + rewrite (cut_res_add_clock' _ _ _ _ _ e Ec (Hnt _ tt)) in H2. cbv beta iota in H2.
      rewrite fix_clock_evaluate in H, H2.
      destruct (evaluate (body, s')) as [rb tb] eqn:Eb.
      destruct (decide (rb = SOME TimeOut)) as [->|Hrb].
      * cbv beta iota in H. injection H as <-.
        destruct (evaluate (body, set_clock (clock s' + e) s')) as [rb' tb'] eqn:Eb'.
        pose proof (IH' body s' ltac:(prove_lt) e _ _ _ _ Eb Eb') as P.
        eapply pre_trans; [exact P|].
        destruct rb' as [[ | | k | k | | | ]|]; cbv beta iota in H2;
          try (destruct k); try (injection H2 as _ <-; apply pre_refl);
          try exact (io_whole _ _ _ _ H2);
          rewrite (io_cut _ _ _ _ _ H2); apply pre_refl.
      * rewrite (evaluate_add_clock_eq body s' rb tb e (conj Eb Hrb)) in H2.
        destruct rb as [[ | | k | k | | | ]|]; cbv beta iota in H, H2;
          try (destruct k; cbv beta iota in H, H2);
          try (injection H as Hx _; cbn in Hx; discriminate);
          try congruence;
          try exact (IH' (Loop li body lo) tb ltac:(prove_lt) e _ _ _ _ H H2);
          (rewrite (io_cut _ _ _ _ _ H), (io_cut _ _ _ _ _ H2); cbn [ffi set_clock]; apply pre_refl).
  - (* Break *) injection H as Hx _; discriminate.
  - (* Continue *) injection H as Hx _; discriminate.
  - (* Raise *) split_eval H; injection H as Hx _; discriminate.
  - (* Return *) split_eval H; injection H as Hx _; discriminate.
  - (* ShMem *)
    split_eval H; try (injection H as Hx _; discriminate);
      apply sh_mem_op_res in H as [Hx|[Hx|[? Hx]]]; discriminate.
  - (* Tick *)
    destruct (clock s =? 0) eqn:Ec; [injection H as <-|injection H as Hx _; discriminate].
    cbn [clock set_clock] in H2.
    destruct (clock s + e =? 0); injection H2 as _ <-; cbn [ffi set_locals dec_clock set_clock];
      apply pre_refl.
  - (* Mark *) exact (IH' p s ltac:(prove_lt) e _ _ _ _ H H2).
  - (* Fail *) injection H as Hx _; discriminate.
  - (* LocValue *) split_eval H; injection H as Hx _; discriminate.
  - (* Call *)
    rewrite get_vars_set_clock in H2.
    destruct (get_vars args s) as [vals|]; [|injection H as Hx _; discriminate].
    cbn [code set_clock] in H2.
    destruct (find_code dest vals (code s)) as [[env prog0]|]; [|injection H as Hx _; discriminate].
    destruct ret as [[ns live]|].
    + destruct (ALL_DISTINCT ns); cbn [negb] in H, H2; [|injection H as Hx _; discriminate].
      destruct (cut_res live (NONE, s)) as [[c|] s'] eqn:Ec.
      * injection H as _ <-. rewrite (io_cut _ _ _ _ _ Ec). exact Hw.
      * rewrite (cut_res_add_clock' _ _ _ _ _ e Ec (Hnt _ tt)) in H2. cbv beta iota in H, H2.
        rewrite fix_clock_evaluate in H, H2.
        change (set_locals env (set_clock (clock s' + e) s'))
          with (set_clock (clock (set_locals env s') + e) (set_locals env s')) in H2.
        destruct (evaluate (prog0, set_locals env s')) as [rb tb] eqn:Eb.
        destruct (decide (rb = SOME TimeOut)) as [->|Hrb].
        -- cbv beta iota in H. injection H as <-.
           destruct (evaluate (prog0, set_clock (clock (set_locals env s') + e) (set_locals env s')))
             as [rb' tb'] eqn:Eb'.
           pose proof (IH' prog0 (set_locals env s') ltac:(prove_lt) e _ _ _ _ Eb Eb') as P.
           eapply pre_trans; [exact P|].
           destruct rb' as [[retvs|exn| | | | |]|]; cbv beta iota in H2;
             try (injection H2 as _ <-; apply pre_refl).
           ++ destruct (negb _); cbv beta iota in H2; [injection H2 as _ <-; apply pre_refl|].
              destruct handler as [[n [h [r lo]]]|];
                [|injection H2 as _ <-; cbn [ffi set_vars set_locals]; apply pre_refl].
              match type of H2 with cut_res _ (evaluate ?y) = _ =>
                destruct (evaluate y) as [rr tr] eqn:Er end.
              rewrite (io_cut _ _ _ _ _ H2). pose proof (io_whole _ _ _ _ Er) as Pr.
              cbn [ffi set_vars set_locals] in Pr. exact Pr.
           ++ destruct handler as [[n [h [r lo]]]|];
                [|injection H2 as _ <-; cbn [ffi set_locals]; apply pre_refl].
              match type of H2 with cut_res _ (evaluate ?y) = _ =>
                destruct (evaluate y) as [rr tr] eqn:Er end.
              rewrite (io_cut _ _ _ _ _ H2). pose proof (io_whole _ _ _ _ Er) as Pr.
              cbn [ffi set_var set_locals] in Pr. exact Pr.
        -- rewrite (evaluate_add_clock_eq _ _ rb tb e (conj Eb Hrb)) in H2.
           destruct rb as [[retvs|exn| | | | |]|]; cbv beta iota in H, H2;
             try congruence; try (injection H as Hx _; congruence).
           ++ destruct (negb _); cbv beta iota in H, H2; [injection H as Hx _; discriminate|].
              destruct handler as [[n [h [r lo]]]|]; [|injection H as Hx _; discriminate].
              set (X := set_vars ns retvs (set_locals (locals s') tb)) in H.
              change (set_vars ns retvs (set_locals (locals (set_clock (clock s' + e) s'))
                                           (set_clock (clock tb + e) tb)))
                with (set_clock (clock X + e) X) in H2.
              destruct (evaluate (r, X)) as [rr tr] eqn:Er.
              destruct (decide (rr = SOME TimeOut)) as [->|Hrr].
              ** cbn [cut_res IS_SOME] in H. injection H as <-.
                 destruct (evaluate (r, set_clock (clock X + e) X)) as [rr' tr'] eqn:Er'.
                 rewrite (io_cut _ _ _ _ _ H2).
                 assert (Hlt : eval_lt (r, X) (Call (SOME (ns, live)) dest args
                                                 (SOME (n, (h, (r, lo)))), s)).
                 { pose proof (evaluate_clock _ _ _ _ Eb). pose proof (cut_res_NONE_clock _ _ _ Ec).
                   unfold eval_lt, X. cbn [fst snd]. left. state_cbn. lia. }
                 exact (IH' r X Hlt e _ _ _ _ Er Er').
              ** rewrite (evaluate_add_clock_eq _ _ rr tr e (conj Er Hrr)) in H2.
                 rewrite (io_cut _ _ _ _ _ H), (io_cut _ _ _ _ _ H2). cbn [ffi set_clock].
                 apply pre_refl.
           ++ destruct handler as [[n [h [r lo]]]|]; [|injection H as Hx _; discriminate].
              set (X := set_var n exn (set_locals (locals s') tb)) in H.
              change (set_var n exn (set_locals (locals (set_clock (clock s' + e) s'))
                                       (set_clock (clock tb + e) tb)))
                with (set_clock (clock X + e) X) in H2.
              destruct (evaluate (h, X)) as [rr tr] eqn:Er.
              destruct (decide (rr = SOME TimeOut)) as [->|Hrr].
              ** cbn [cut_res IS_SOME] in H. injection H as <-.
                 destruct (evaluate (h, set_clock (clock X + e) X)) as [rr' tr'] eqn:Er'.
                 rewrite (io_cut _ _ _ _ _ H2).
                 assert (Hlt : eval_lt (h, X) (Call (SOME (ns, live)) dest args
                                                 (SOME (n, (h, (r, lo)))), s)).
                 { pose proof (evaluate_clock _ _ _ _ Eb). pose proof (cut_res_NONE_clock _ _ _ Ec).
                   unfold eval_lt, X. cbn [fst snd]. left. state_cbn. lia. }
                 exact (IH' h X Hlt e _ _ _ _ Er Er').
              ** rewrite (evaluate_add_clock_eq _ _ rr tr e (conj Er Hrr)) in H2.
                 rewrite (io_cut _ _ _ _ _ H), (io_cut _ _ _ _ _ H2). cbn [ffi set_clock].
                 apply pre_refl.
    + destruct (IS_SOME handler); cbv beta iota in H, H2; [congruence|].
      destruct (clock s =? 0) eqn:Ec.
      * injection H as <-. exact Hw.
      * apply N.eqb_neq in Ec. cbn [clock set_clock] in H2.
        destruct (N.eqb_spec (clock s + e) 0) as [|_]; [lia|].
        replace (set_locals env (dec_clock (set_clock (clock s + e) s)))
          with (set_clock (clock (set_locals env (dec_clock s)) + e) (set_locals env (dec_clock s)))
          in H2 by (destruct s; cbn in *; unfold set_locals, dec_clock, set_clock; cbn; f_equal; lia).
        destruct (evaluate (prog0, set_locals env (dec_clock s))) as [rb tb] eqn:Eb.
        destruct (evaluate (prog0, set_clock (clock (set_locals env (dec_clock s)) + e)
                                     (set_locals env (dec_clock s)))) as [rb' tb'] eqn:Eb'.
        assert (Ht : t = tb)
          by (destruct rb as [[]|]; cbv beta iota in H; apply (f_equal snd) in H; cbn in H; congruence).
        assert (Hu : u = tb')
          by (destruct rb' as [[]|]; cbv beta iota in H2; apply (f_equal snd) in H2; cbn in H2; congruence).
        subst t u.
        assert (Hlt : eval_lt (prog0, set_locals env (dec_clock s)) (Call NONE dest args handler, s)).
        { unfold eval_lt. cbn [fst snd]. left. state_cbn. lia. }
        exact (IH' _ _ Hlt e _ _ _ _ Eb Eb').
  - (* FFI *)
    split_eval H; injection H as Hx _; discriminate.
Qed.

End Props5.
