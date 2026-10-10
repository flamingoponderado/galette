(** * CakeML Pancake [panProps]: properties of the Pancake semantics

    Port of [cakeml/pancake/semantics/panPropsScript.sml].

    Proof method: HOL's [recInduct evaluate_ind] is well-founded induction
    on [eval_lt] ([panSem]); a case of [evaluate] is unfolded with
    [evaluate_eqn] and [fix_clock_evaluate], and its [match]es are split by
    the guarded loops below.  The Galette-only helpers at the top of this
    file (nested induction on [exp], state-update commutations, the
    case-splitting tactics) have no HOL original. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.pancake Require Import panLang pan_common.
From Galette.cakeml.pancake.semantics Require Import panSem pan_commonProps.
Open Scope N_scope.
Local Open Scope fmap_scope.

(** ** Galette-only infrastructure *)

(** HOL [structs_nil_v] is [TAKE 0 s.structs] evaluated, i.e. [[]] at the
    type of the [structs] field. *)
(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "is_wf_shape_nil" *)
Abbreviation is_wf_shape_nil := (is_wf_shape ([] : list (stcname * struct_info))).

Section ExpInd.
Context {a : N}.

(** Induction on expressions with induction hypotheses for the nested
    lists. *)
Fixpoint exp_nested_ind (P : exp a -> Prop)
    (Hc : forall w, P (Const w)) (Hv : forall vk v0, P (Var vk v0))
    (Hrs : forall es, Forall P es -> P (panLang.RStruct es))
    (Hrf : forall i e, P e -> P (RField i e))
    (Hns : forall nm es, Forall (fun p => P (snd p)) es -> P (panLang.NStruct nm es))
    (Hnf : forall f e, P e -> P (NField f e))
    (Hl : forall sh e, P e -> P (Load sh e))
    (Hl32 : forall e, P e -> P (Load32 e))
    (Hlb : forall e, P e -> P (LoadByte e))
    (Hop : forall op es, Forall P es -> P (Op op es))
    (Hpop : forall op es, Forall P es -> P (Panop op es))
    (Hcmp : forall c e1 e2, P e1 -> P e2 -> P (Cmp c e1 e2))
    (Hsh : forall s e1 e2, P e1 -> P e2 -> P (Shift s e1 e2))
    (Hb : P BaseAddr) (Ht : P TopAddr) (Hbw : P BytesInWord) (e : exp a) : P e :=
  let rec := exp_nested_ind P Hc Hv Hrs Hrf Hns Hnf Hl Hl32 Hlb Hop Hpop Hcmp Hsh Hb Ht Hbw in
  let fix go (l : list (exp a)) : Forall P l :=
    match l with [] => Forall_nil _ | x :: xs => Forall_cons _ (rec x) (go xs) end in
  let fix go2 (l : list (fldname * exp a)) : Forall (fun p => P (snd p)) l :=
    match l with [] => Forall_nil _ | x :: xs => Forall_cons _ (rec (snd x)) (go2 xs) end in
  match e with
  | Const w => Hc w
  | Var vk v0 => Hv vk v0
  | panLang.RStruct es => Hrs es (go es)
  | RField i e => Hrf i e (rec e)
  | panLang.NStruct nm es => Hns nm es (go2 es)
  | NField f e => Hnf f e (rec e)
  | Load sh e => Hl sh e (rec e)
  | Load32 e => Hl32 e (rec e)
  | LoadByte e => Hlb e (rec e)
  | Op op es => Hop op es (go es)
  | Panop op es => Hpop op es (go es)
  | Cmp c e1 e2 => Hcmp c e1 e2 (rec e1) (rec e2)
  | Shift s e1 e2 => Hsh s e1 e2 (rec e1) (rec e2)
  | BaseAddr => Hb
  | TopAddr => Ht
  | BytesInWord => Hbw
  end.

End ExpInd.

Lemma OPT_MMAP_Forall_ext {A B} (f g : A -> option B) l :
  Forall (fun x => f x = g x) l -> OPT_MMAP f l = OPT_MMAP g l.
Proof. induction 1 as [|x l Hx _ IH]; cbn; [reflexivity|]. rewrite Hx, IH; reflexivity. Qed.

Lemma OPT_MMAP_ext_In {A B} (f g : A -> option B) l :
  (forall x, In x l -> f x = g x) -> OPT_MMAP f l = OPT_MMAP g l.
Proof. intros H; apply OPT_MMAP_Forall_ext, Forall_forall, H. Qed.

Section StateHelpers.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(** [eval] reads only the locals, globals, structs, memory, memaddrs, [be],
    [base_addr] and [top_addr] of the state. *)
Lemma eval_state_cong s t :
  locals s = locals t -> globals s = globals t -> structs s = structs t ->
  memory s = memory t -> memaddrs s = memaddrs t -> be s = be t ->
  base_addr s = base_addr t -> top_addr s = top_addr t ->
  eval s = eval t.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8; apply functional_extensionality; intros e.
  induction e using exp_nested_ind; cbn [eval];
    rewrite ?H1, ?H2, ?H3, ?H4, ?H5, ?H6, ?H7, ?H8;
    repeat match goal with IH : eval s ?e = eval t ?e |- _ => rewrite IH; clear IH end;
    try match goal with v : varkind |- _ => destruct v; cbn; congruence end;
    try match goal with IH : Forall _ ?l |- context [OPT_MMAP ?f ?l] =>
      erewrite (OPT_MMAP_ext_In f _ l); [|intros x Hx; exact (proj1 (Forall_forall _ _) IH x Hx)]
    end;
    reflexivity.
Qed.

Lemma eval_set_clock k s : eval (set_clock k s) = eval s.
Proof. apply eval_state_cong; reflexivity. Qed.
Lemma eval_set_ffi f s : eval (set_ffi f s) = eval s.
Proof. apply eval_state_cong; reflexivity. Qed.
Lemma eval_set_code c s : eval (set_code c s) = eval s.
Proof. apply eval_state_cong; reflexivity. Qed.
Lemma eval_set_eshapes c s : eval (set_eshapes c s) = eval s.
Proof. apply eval_state_cong; reflexivity. Qed.

Lemma lookup_kvar_set_clock vk v0 k s : lookup_kvar vk v0 (set_clock k s) = lookup_kvar vk v0 s.
Proof. destruct vk; reflexivity. Qed.
Lemma lookup_kvar_set_code vk v0 c s : lookup_kvar vk v0 (set_code c s) = lookup_kvar vk v0 s.
Proof. destruct vk; reflexivity. Qed.
Lemma is_valid_value_set_clock vk v0 k s : is_valid_value (set_clock k s) vk v0 = is_valid_value s vk v0.
Proof. destruct vk; reflexivity. Qed.
Lemma is_valid_value_set_code vk v0 c s : is_valid_value (set_code c s) vk v0 = is_valid_value s vk v0.
Proof. destruct vk; reflexivity. Qed.

Lemma set_clock_id s : set_clock (clock s) s = s.
Proof. destruct s; reflexivity. Qed.
Lemma set_clock_set_clock k1 k2 s : set_clock k1 (set_clock k2 s) = set_clock k1 s.
Proof. destruct s; reflexivity. Qed.

End StateHelpers.

(** Projections of state updates. *)
Ltac state_cbn :=
  cbn [locals globals structs code eshapes memory memaddrs sh_memaddrs clock be ffi
       base_addr top_addr set_locals set_globals set_structs set_memory set_clock set_ffi
       set_code set_eshapes dec_clock empty_locals set_var set_global set_kvar] in *.

(** Turn [(x =? 0) = b] hypotheses into arithmetic facts. *)
Ltac eqb_facts :=
  repeat match goal with
         | H : (_ =? _)%N = false |- _ => apply N.eqb_neq in H
         | H : (_ =? _)%N = true |- _ => apply N.eqb_eq in H
         end.

(** Clock facts of the [evaluate] equations in the context. *)
Ltac add_clock_facts :=
  repeat match goal with
  | E : evaluate (?p, ?s) = (?r, ?t) |- _ =>
      lazymatch goal with
      | _ : (clock t <= clock s)%N |- _ => fail
      | _ => pose proof (evaluate_clock p s r t E)
      end
  end.

Ltac destruct_kvars :=
  repeat match goal with |- context [set_kvar ?vk _ _ _] => is_var vk; destruct vk end.

(** [eval_lt] for a recursive call, from the clock facts in the context. *)
Ltac prove_lt :=
  unfold eval_lt; cbn [fst snd psize]; add_clock_facts; eqb_facts;
  destruct_kvars; state_cbn; lia.

(** Equality of states built from the same states by updates. *)
Ltac state_eq_rec := first [reflexivity | lia | progress f_equal; state_eq_rec].
Ltac state_eq :=
  eqb_facts;
  repeat match goal with vk : varkind |- _ => destruct vk end;
  repeat match goal with s : state _ _ |- _ => destruct s end;
  unfold dec_clock, empty_locals, set_var, set_global, set_kvar, set_locals, set_globals,
    set_structs, set_memory, set_clock, set_ffi, set_code, set_eshapes, upd_locals in *;
  cbn in *; state_eq_rec.

(** Split, in hypothesis [H], the first [match] whose scrutinee is not a
    call of [evaluate]; the goal is split along. *)
Ltac split_nonrec H :=
  match type of H with
  | context [match ?x with _ => _ end] =>
      lazymatch x with
      | evaluate _ => fail
      | _ => let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H |- *
      end
  end.

Ltac dump := try (match goal with H : ?T |- _ => idtac H ":" T; fail end); match goal with |- ?g => idtac "GOAL" g end.

(** Split every [match] of hypothesis [H], including calls of [evaluate]
    (which become equations [E : evaluate _ = (_, _)]). *)
Ltac split_all H :=
  repeat first
    [ progress (repeat rewrite fix_clock_evaluate in H)
    | match type of H with
      | context [match ?x with _ => _ end] =>
          lazymatch x with
          | context [match _ with _ => _ end] => fail
          | _ => let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H
          end
      end ].

Ltac state_cbn_goal :=
  cbn [locals globals structs code eshapes memory memaddrs sh_memaddrs clock be ffi
       base_addr top_addr set_locals set_globals set_structs set_memory set_clock set_ffi
       set_code set_eshapes dec_clock empty_locals set_var set_global set_kvar].

Ltac destruct_kvars_all :=
  repeat match goal with H : context [set_kvar ?vk _ _ _] |- _ => is_var vk; destruct vk end;
  destruct_kvars.

Ltac clock_ctx := add_clock_facts; eqb_facts; destruct_kvars_all; state_cbn.

(** Rewrite the goal's scrutinees with the equations of the context. *)
Ltac goal_scrut :=
  match goal with
  | E : ?x = _ |- context [match ?x with _ => _ end] =>
      lazymatch x with evaluate _ => fail | _ => rewrite E; cbn beta iota zeta end
  end.

Ltac goal_eqb :=
  match goal with |- context [(?x =? 0)] =>
    first [ rewrite (proj2 (N.eqb_neq x 0)) by (clock_ctx; lia)
          | rewrite (proj2 (N.eqb_eq x 0)) by (clock_ctx; lia) ];
    cbn beta iota zeta
  end.

(** Leaf of a split: [H : (r, s) = (res, st)] is substituted. *)
Ltac leaf_subst H :=
  lazymatch type of H with
  | (_, _) = (_, _) => injection H as <- <-
  | _ => idtac
  end.

(** Prefix order on lists (HOL [rich_list]'s [IS_PREFIX_REFL],
    [IS_PREFIX_TRANS], [IS_PREFIX_APPEND] for [isPREFIX]). *)
Local Lemma isPREFIX_refl {A} {HA : EqDecision A} (l : list A) : is_true (isPREFIX l l).
Proof.
  induction l as [|x l IH]; cbn; [reflexivity|].
  unfold is_true; rewrite Bool.andb_true_iff; split; [apply bool_decide_spec; reflexivity|exact IH].
Qed.

Local Lemma isPREFIX_trans {A} {HA : EqDecision A} (l1 l2 l3 : list A) :
  is_true (isPREFIX l1 l2) -> is_true (isPREFIX l2 l3) -> is_true (isPREFIX l1 l3).
Proof.
  revert l2 l3; induction l1 as [|x l1 IH]; intros [|y l2] [|z l3] H1 H2; cbn in *;
    try reflexivity; try discriminate.
  unfold is_true in *; rewrite Bool.andb_true_iff in *. destruct H1 as [H1 H1'], H2 as [H2 H2'].
  apply bool_decide_spec in H1, H2; subst.
  split; [apply bool_decide_spec; reflexivity|eapply IH; eassumption].
Qed.

Local Lemma isPREFIX_app {A} {HA : EqDecision A} (l1 l2 : list A) : is_true (isPREFIX l1 (l1 ++ l2)).
Proof.
  induction l1 as [|x l1 IH]; cbn; [reflexivity|].
  unfold is_true; rewrite Bool.andb_true_iff; split; [apply bool_decide_spec; reflexivity|exact IH].
Qed.

Local Lemma isPREFIX_length {A} {HA : EqDecision A} (l1 l2 : list A) :
  is_true (isPREFIX l1 l2) -> (length l1 <= length l2)%nat.
Proof.
  revert l2; induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in *; try lia; try discriminate.
  unfold is_true in H; rewrite Bool.andb_true_iff in H; apply le_n_S, IH, H.
Qed.

Local Lemma isPREFIX_antisym {A} {HA : EqDecision A} (l1 l2 : list A) :
  is_true (isPREFIX l1 l2) -> is_true (isPREFIX l2 l1) -> l1 = l2.
Proof.
  revert l2; induction l1 as [|x l1 IH]; intros [|y l2] H1 H2; cbn in *;
    try reflexivity; try discriminate.
  unfold is_true in *; rewrite Bool.andb_true_iff in *. destruct H1 as [H1 H1'], H2 as [_ H2'].
  apply bool_decide_spec in H1; subst; f_equal; apply IH; assumption.
Qed.

Lemma call_FFI_return_io {ffi_t} (st : ffi_state ffi_t) s conf bytes st' bytes' :
  call_FFI st s conf bytes = FFI_return st' bytes' ->
  is_true (isPREFIX (io_events st) (io_events st')) /\
  ffi_state_oracle st' = ffi_state_oracle st /\
  (io_events st' = io_events st -> st' = st).
Proof.
  unfold call_FFI; destruct (negb _).
  - destruct (ffi_state_oracle st s _ conf bytes); [|discriminate].
    destruct (_ =? _); [|discriminate]. intros H; injection H as <- _; cbn.
    split; [apply isPREFIX_app|split; [reflexivity|]].
    intros Heq; apply (f_equal (@length _)) in Heq; rewrite length_app in Heq; cbn in Heq; lia.
  - intros H; injection H as <- _; split; [apply isPREFIX_refl|split; reflexivity].
Qed.

(** ** Value shapes *)

Section Shapes.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "v2word_def" *)
Definition v2word (x : v a) : word_lab a :=
  match x with Val (Word v0) => Word v0 | _ => ARB end.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "shape_of_val" *)
Theorem shape_of_val : forall x : word_lab a, shape_of (Val x) = One.
Proof. reflexivity. Qed.

End Shapes.

(** ** [eval] and state updates *)

Section EvalUpd.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "eval_upd_clock_eq" *)
Theorem eval_upd_clock_eq : forall (t : state a ffi_t) e ck, eval (set_clock ck t) e = eval t e.
Proof. intros; rewrite eval_set_clock; reflexivity. Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "eval_upd_code_eq" *)
Theorem eval_upd_code_eq : forall (t : state a ffi_t) e code, eval (set_code code t) e = eval t e.
Proof. intros; rewrite eval_set_code; reflexivity. Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "eval_upd_eshapes_eq" *)
Theorem eval_upd_eshapes_eq : forall (t : state a ffi_t) e esh, eval (set_eshapes esh t) e = eval t e.
Proof. intros; rewrite eval_set_eshapes; reflexivity. Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "opt_mmap_eval_upd_clock_eq" *)
Theorem opt_mmap_eval_upd_clock_eq : forall es (s : state a ffi_t) ck,
  OPT_MMAP (eval (set_clock (ck + clock s) s)) es = OPT_MMAP (eval s) es.
Proof. intros; rewrite eval_set_clock; reflexivity. Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "opt_mmap_eval_upd_clock_eq1" *)
Theorem opt_mmap_eval_upd_clock_eq1 : forall es (s : state a ffi_t) ck,
  OPT_MMAP (eval (set_clock ck s)) es = OPT_MMAP (eval s) es.
Proof. intros; rewrite eval_set_clock; reflexivity. Qed.

End EvalUpd.

(** ** Clocks *)

Section Clock.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma evaluate_unfold (p : prog a) s :
  evaluate (p, s) =
  evaluate_body (fun p' s' => evaluate (p', s')) (fun p' s' => evaluate (p', s')) p s.
Proof. apply evaluate_eqn. Qed.

Lemma sh_mem_load_set_clock vk v0 addr nb k s :
  sh_mem_load vk v0 addr nb (set_clock k s) =
  (fst (sh_mem_load vk v0 addr nb s), set_clock k (snd (sh_mem_load vk v0 addr nb s))).
Proof.
  unfold sh_mem_load; destruct s; cbn.
  repeat match goal with |- context [match ?x with _ => _ end] =>
    destruct x eqn:?; cbn beta iota zeta end; destruct vk; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_add_clock_eq" *)
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
  intros res st ck H Hres; cbn [fst snd].
  rewrite evaluate_unfold in H |- *.
  destruct p; cbn [evaluate_body] in H |- *; rewrite ?fix_clock_evaluate in H |- *;
    rewrite ?eval_set_clock, ?lookup_kvar_set_clock, ?is_valid_value_set_clock in *;
    unfold sh_mem_load, sh_mem_store in *; state_cbn.
  all: repeat first
    [ progress (repeat first [rewrite fix_clock_evaluate in H | rewrite fix_clock_evaluate
          | rewrite eval_set_clock | rewrite lookup_kvar_set_clock
          | rewrite is_valid_value_set_clock])
    | match type of H with
      | (?r1, ?s1) = (_, _) =>
          injection H as <- <-; first [congruence | state_eq]
      | evaluate (?p', ?s') = _ =>
          match goal with |- evaluate (p', ?g) = _ =>
            let Hg := fresh "Hg" in
            assert (Hg : g = set_clock (clock s' + ck) s') by state_eq;
            try rewrite Hg; exact (IH (p', s') ltac:(prove_lt) res st ck H Hres)
          end
      end
    | split_nonrec H
    | match type of H with
      | context [match evaluate (?p', ?s') with _ => _ end] =>
          let r := fresh "r" in let t' := fresh "t" in let E := fresh "E" in
          let Hr := fresh "Hr" in
          destruct (evaluate (p', s')) as [r t'] eqn:E;
          destruct (decide (r = SOME TimeOut)) as [->|Hr];
          [ cbn beta iota zeta in H
          | match goal with |- context [evaluate (p', ?g)] =>
              let Hg := fresh "Hg" in
              assert (Hg : g = set_clock (clock s' + ck) s') by state_eq;
              let HI := fresh "HI" in
              pose proof (IH (p', s') ltac:(prove_lt) r t' ck E Hr) as HI; cbn [fst snd] in HI;
              try rewrite Hg; rewrite HI; clear Hg HI;
              cbn beta iota zeta in H |- *
            end ]
      end
    | match goal with |- context [(?x + ?y =? 0)] =>
        rewrite (proj2 (N.eqb_neq (x + y) 0)) by (eqb_facts; lia); cbn beta iota zeta
      end ].
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub" *)
Theorem evaluate_clock_sub : forall (p : prog a) t res st ck,
  evaluate (p, t) = (res, set_clock (clock st + ck) st) /\ res <> SOME TimeOut ->
  evaluate (p, set_clock (clock t - ck) t) = (res, st).
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall res st ck,
            evaluate x = (res, set_clock (clock st + ck) st) -> res <> SOME TimeOut ->
            evaluate (fst x, set_clock (clock (snd x) - ck) (snd x)) = (res, st))
    by (intros p t res st ck [H1 H2]; exact (G (p, t) res st ck H1 H2)).
  intros x; induction x as [[p t] IH] using (well_founded_induction eval_lt_wf).
  intros res st ck H Hres; cbn [fst snd].
  remember (set_clock (clock st + ck) st) as st' eqn:Hst.
  assert (Hst2 : st = set_clock (clock st' - ck) st') by (subst st'; state_eq).
  assert (Hck : ck <= clock st') by (subst st'; state_cbn; lia).
  clear Hst; subst st.
  rewrite evaluate_unfold in H |- *.
  destruct p; cbn [evaluate_body] in H |- *;
    unfold sh_mem_load, sh_mem_store in *; split_all H.
  all: leaf_subst H.
  all: try congruence.
  all: repeat first
    [ progress (repeat first [rewrite fix_clock_evaluate | rewrite eval_set_clock
          | rewrite lookup_kvar_set_clock | rewrite is_valid_value_set_clock])
    | progress state_cbn_goal
    | goal_scrut
    | goal_eqb
    | match goal with
      | |- context [evaluate (?p', ?g)] =>
          match goal with
          | E : evaluate (p', ?s') = (?r1, ?t1) |- _ =>
              let Hc := fresh "Hc" in
              assert (Hc : ck <= clock t1) by (clock_ctx; lia);
              let E' := fresh "E'" in
              assert (E' : evaluate (p', s') =
                             (r1, set_clock (clock (set_clock (clock t1 - ck) t1) + ck)
                                    (set_clock (clock t1 - ck) t1)))
                by (rewrite E; state_eq);
              let HI := fresh "HI" in
              pose proof (IH (p', s') ltac:(prove_lt) _ _ ck E' ltac:(congruence)) as HI;
              cbn [fst snd] in HI;
              let Hg := fresh "Hg" in
              assert (Hg : g = set_clock (clock s' - ck) s') by state_eq;
              try rewrite Hg; rewrite HI; clear Hg HI E' Hc; cbn beta iota zeta
          end
      end ].
  all: state_eq.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_min_clock" *)
Theorem evaluate_min_clock : forall (prog0 : prog a) s q r,
  evaluate (prog0, s) = (q, r) /\ q <> SOME TimeOut ->
  exists k, evaluate (prog0, set_clock k s) = (q, set_clock 0 r).
Proof.
  intros prog0 s q r [H Hq]. exists (clock s - clock r).
  apply evaluate_clock_sub; split; [|exact Hq].
  rewrite H; f_equal; destruct r; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_add_clock_or_timeout" *)
Theorem evaluate_add_clock_or_timeout : forall (p : prog a) s q t k q' t',
  evaluate (p, s) = (q, set_clock 0 t) /\ q <> SOME TimeOut ->
  evaluate (p, set_clock k s) = (q', t') ->
  (q' = SOME TimeOut /\ k < clock s \/
   q' = q /\ clock s <= k /\ t' = set_clock (k - clock s) t).
Proof.
  intros p s q t k q' t' [H Hq] H'.
  destruct (N.le_gt_cases (clock s) k) as [Hk|Hk].
  - right. pose proof (evaluate_add_clock_eq p s q (set_clock 0 t) (k - clock s) (conj H Hq)) as HA.
    replace (clock s + (k - clock s)) with k in HA by lia.
    rewrite H' in HA. assert (Hq' : q' = q) by congruence. subst q'.
    split; [reflexivity|split; [exact Hk|]].
    apply (f_equal snd) in HA; cbn in HA; rewrite HA. destruct t; reflexivity.
  - left. split; [|exact Hk].
    destruct (decide (q' = SOME TimeOut)) as [E|E]; [exact E|exfalso].
    pose proof (evaluate_add_clock_eq p (set_clock k s) q' t' (clock s - k) (conj H' E)) as HA.
    cbn [clock set_clock] in HA. rewrite set_clock_set_clock in HA.
    replace (k + (clock s - k)) with (clock s) in HA by lia.
    rewrite set_clock_id, H in HA. apply (f_equal snd), (f_equal clock) in HA.
    unfold set_clock in HA; cbn in HA; lia.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub1" *)
Theorem evaluate_clock_sub1 : forall (p : prog a) t res st t' ck,
  evaluate (p, t) = (res, st) /\ res <> SOME TimeOut /\
  evaluate (p, set_clock (ck + clock t) t) = evaluate (p, t') ->
  evaluate (p, t) = evaluate (p, set_clock (clock t' - ck) t').
Proof.
  intros p t res st t' ck [H [Hr Heq]].
  pose proof (evaluate_add_clock_eq p t res st ck (conj H Hr)) as HA.
  rewrite N.add_comm in Heq; rewrite Heq in HA.
  rewrite H; symmetry; apply evaluate_clock_sub; split; [exact HA|exact Hr].
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_io_events_mono" *)
Theorem evaluate_io_events_mono : forall (exps : prog a) s1 res s2,
  evaluate (exps, s1) = (res, s2) ->
  is_true (isPREFIX (io_events (ffi s1)) (io_events (ffi s2))).
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall res s2,
            evaluate x = (res, s2) ->
            is_true (isPREFIX (io_events (ffi (snd x))) (io_events (ffi s2))))
    by (intros p s r t H; exact (G (p, s) r t H)).
  intros x; induction x as [[p t] IH] using (well_founded_induction eval_lt_wf).
  intros res st H; cbn [fst snd].
  rewrite evaluate_unfold in H.
  destruct p; cbn [evaluate_body] in H; unfold sh_mem_load, sh_mem_store in *; split_all H.
  all: leaf_subst H.
  all: repeat match goal with
       | E : evaluate (?p', ?s') = (?r1, ?t1) |- _ =>
           let HI := fresh "HI" in
           pose proof (IH (p', s') ltac:(prove_lt) r1 t1 E) as HI; cbn [fst snd] in HI;
           pose proof (evaluate_clock p' s' r1 t1 E); clear E
       | E : call_FFI _ _ _ _ = FFI_return _ _ |- _ =>
           apply call_FFI_return_io in E as [? [? ?]]
       end.
  all: destruct_kvars; state_cbn.
  all: try apply isPREFIX_refl.
  all: eauto using isPREFIX_trans.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" *)
Theorem evaluate_invariants : forall (p : prog a) t res st,
  evaluate (p, t) = (res, st) ->
  memaddrs st = memaddrs t /\ sh_memaddrs st = sh_memaddrs t /\ be st = be t /\ eshapes st = eshapes t /\ base_addr st = base_addr t /\ structs st = structs t /\ code st = code t /\ ffi_state_oracle (ffi st) = ffi_state_oracle (ffi t).
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall res st,
            evaluate x = (res, st) ->
            memaddrs st = memaddrs (snd x) /\ sh_memaddrs st = sh_memaddrs (snd x) /\ be st = be (snd x) /\ eshapes st = eshapes (snd x) /\ base_addr st = base_addr (snd x) /\ structs st = structs (snd x) /\ code st = code (snd x) /\ ffi_state_oracle (ffi st) = ffi_state_oracle (ffi (snd x)))
    by (intros p s r t H; exact (G (p, s) r t H)).
  intros x; induction x as [[p t] IH] using (well_founded_induction eval_lt_wf).
  intros res st H; cbn [fst snd].
  rewrite evaluate_unfold in H.
  destruct p; cbn [evaluate_body] in H; unfold sh_mem_load, sh_mem_store in *; split_all H.
  all: leaf_subst H.
  all: repeat match goal with
       | E : evaluate (?p', ?s') = (?r1, ?t1) |- _ =>
           let HI := fresh "HI" in
           pose proof (IH (p', s') ltac:(prove_lt) r1 t1 E) as HI; cbn [fst snd] in HI;
           pose proof (evaluate_clock p' s' r1 t1 E); clear E;
           destruct HI as [? [? [? [? [? [? [? ?]]]]]]]
       | E : call_FFI _ _ _ _ = FFI_return _ _ |- _ =>
           apply call_FFI_return_io in E as [? [? ?]]
       end.
  all: destruct_kvars_all; state_cbn.
  all: repeat split; congruence.
Qed.

Lemma evaluate_code_invariant (p : prog a) t res st :
  evaluate (p, t) = (res, st) -> code st = code t.
Proof. intros H; apply evaluate_invariants in H; tauto. Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_global_shape_invariant" *)
Theorem evaluate_global_shape_invariant : forall (p : prog a) s res st n v0,
  evaluate (p, s) = (res, st) /\ FLOOKUP (globals s) n = SOME v0 ->
  exists v', FLOOKUP (globals st) n = SOME v' /\ shape_of v' = shape_of v0.
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall res st,
            evaluate x = (res, st) ->
            forall n v0, FLOOKUP (globals (snd x)) n = SOME v0 ->
            exists v', FLOOKUP (globals st) n = SOME v' /\ shape_of v' = shape_of v0)
    by (intros p s r t n v0 [H1 H2]; exact (G (p, s) r t H1 n v0 H2)).
  intros x; induction x as [[p t] IH] using (well_founded_induction eval_lt_wf).
  intros res st H; cbn [fst snd].
  rewrite evaluate_unfold in H.
  destruct p; cbn [evaluate_body] in H; unfold sh_mem_load, sh_mem_store in *; split_all H.
  all: leaf_subst H.
  all: repeat match goal with
       | E : evaluate (?p', ?s') = (?r1, ?t1) |- _ =>
           let HI := fresh "HI" in
           pose proof (IH (p', s') ltac:(prove_lt) r1 t1 E) as HI; cbn [fst snd] in HI;
           pose proof (evaluate_clock p' s' r1 t1 E); clear E
       end.
  all: intros gn gv Hn.
  all: destruct_kvars_all; state_cbn.
  all: repeat match goal with
       | HI : forall n v0, FLOOKUP (globals ?A) n = SOME v0 -> _,
         Hn : FLOOKUP (globals ?A) ?gn = SOME ?gv |- _ =>
           let v' := fresh "v'" in let Hn' := fresh "Hn" in let Hs := fresh "Hs" in
           destruct (HI gn gv Hn) as [v' [Hn' Hs]]; clear HI
       end.
  all: try (match goal with
            | Hn : FLOOKUP (globals ?X) ?n = SOME ?v
              |- exists v', FLOOKUP (globals ?X) ?n = SOME v' /\ _ =>
                exists v; split; [exact Hn|congruence]
            end).
  all: rewrite ?FLOOKUP_UPDATE.
  all: destruct (decide _) as [<-|?]; cbn beta iota.
  all: try (match goal with
            | Hn : FLOOKUP (globals ?X) ?n = SOME ?v
              |- exists v', FLOOKUP (globals ?X) ?n = SOME v' /\ _ =>
                exists v; split; [exact Hn|congruence]
            end).
  all: eexists; split; [reflexivity|].
  all: unfold is_valid_value, lookup_kvar in *.
  all: repeat match goal with
       | E : context [FLOOKUP (globals ?X) ?n], Hn : FLOOKUP (globals ?X) ?n = SOME _ |- _ =>
           rewrite Hn in E
       end.
  all: repeat match goal with E : bool_decide _ = true |- _ => apply bool_decide_spec in E end.
  all: try congruence.
  all: repeat match goal with E : SOME _ = SOME _ |- _ => injection E as E end; subst; reflexivity.
Qed.

End Clock.

(** ** Declarations *)

Section Decls.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma evaluate_decls_cons_cases s d ds :
  evaluate_decls s (d :: ds) =
  match d with
  | Name nm flds => evaluate_decls s ds
  | Decl sh v0 e =>
      match eval (set_locals FEMPTY s) e with
      | SOME res =>
          if bool_decide (sh = shape_of res)
          then evaluate_decls (set_globals (globals s |+ (v0, res)) s) ds
          else NONE
      | NONE => NONE
      end
  | Function fi =>
      if andb (EVERY (is_wf_shape (structs s) ∘ snd) (params fi))
              (is_wf_shape (structs s) (fun_decl_return fi))
      then evaluate_decls
             (set_code (code s |+ (name fi, (params fi, (body fi, fun_decl_return fi)))) s) ds
      else NONE
  | ExnDecl eid sh =>
      if andb (bool_decide (FLOOKUP (eshapes s) eid = NONE)) (is_wf_shape (structs s) sh)
      then evaluate_decls (set_eshapes (eshapes s |+ (eid, sh)) s) ds
      else NONE
  end.
Proof. destruct d; reflexivity. Qed.

Ltac decls_split H :=
  rewrite evaluate_decls_cons_cases in H;
  repeat match type of H with
         | context [match ?x with _ => _ end] =>
             let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H
         end;
  try discriminate.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_eshapes" *)
Theorem evaluate_decls_eshapes : forall s (ds : list (decl a)) s',
  evaluate_decls s ds = SOME s' -> eshapes s' = eshapes s |++ exceptions ds.
Proof.
  intros s ds; revert s; induction ds as [|d ds IH]; intros s s' H.
  - injection H as <-; reflexivity.
  - destruct d; decls_split H; apply IH in H; rewrite H; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_functions" *)
Theorem evaluate_decls_functions : forall s (pan_code : list (decl a)) s',
  evaluate_decls s pan_code = SOME s' -> code s' = code s |++ functions pan_code.
Proof.
  intros s ds; revert s; induction ds as [|d ds IH]; intros s s' H.
  - injection H as <-; reflexivity.
  - destruct d; decls_split H; apply IH in H; rewrite H; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_only_exn_decls" *)
Theorem evaluate_decls_only_exn_decls : forall s (ds : list (decl a)) s',
  is_true (EVERY is_exn_decl ds) /\ evaluate_decls s ds = SOME s' ->
  s' = set_eshapes (eshapes s |++ exceptions ds) s.
Proof.
  intros s ds; revert s; induction ds as [|d ds IH]; intros s s' [Hd H].
  - injection H as <-; destruct s; reflexivity.
  - destruct d; cbn in Hd; try discriminate. decls_split H.
    rewrite (IH _ _ (conj Hd H)); destruct s; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_only_functions" *)
Theorem evaluate_decls_only_functions : forall s (pan_code : list (decl a)) s',
  is_true (EVERY is_function pan_code) /\ evaluate_decls s pan_code = SOME s' ->
  s' = set_code (code s |++ functions pan_code) s.
Proof.
  intros s ds; revert s; induction ds as [|d ds IH]; intros s s' [Hd H].
  - injection H as <-; destruct s; reflexivity.
  - destruct d; cbn in Hd; try discriminate. decls_split H.
    rewrite (IH _ _ (conj Hd H)); destruct s; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_only_funs_and_exn_decls" *)
Theorem evaluate_decls_only_funs_and_exn_decls : forall s (ds : list (decl a)) s',
  is_true (EVERY (fun d => is_function d || is_exn_decl d) ds) /\
  evaluate_decls s ds = SOME s' ->
  s' = set_eshapes (eshapes s |++ exceptions ds) (set_code (code s |++ functions ds) s).
Proof.
  intros s ds; revert s; induction ds as [|d ds IH]; intros s s' [Hd H].
  - injection H as <-; destruct s; reflexivity.
  - destruct d; cbn in Hd; try discriminate; decls_split H;
      rewrite (IH _ _ (conj Hd H)); destruct s; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_append" *)
Theorem evaluate_decls_append : forall s (ds1 ds2 : list (decl a)),
  evaluate_decls s (ds1 ++ ds2) =
  match evaluate_decls s ds1 with
  | NONE => NONE
  | SOME s' => evaluate_decls s' ds2
  end.
Proof.
  intros s ds1; revert s; induction ds1 as [|d ds IH]; intros s ds2; [reflexivity|].
  cbn [List.app]; rewrite !evaluate_decls_cons_cases.
  destruct d; repeat match goal with |- context [match ?x with _ => _ end] =>
    lazymatch x with evaluate_decls _ _ => fail | _ => destruct x end end; cbn; try apply IH;
    reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_names" *)
Theorem evaluate_decls_names : forall s (decs : list (decl a)),
  is_true (EVERY is_name decs) -> evaluate_decls s decs = SOME s.
Proof.
  intros s ds; revert s; induction ds as [|d ds IH]; intros s Hd; [reflexivity|].
  destruct d; cbn in Hd; try discriminate. apply IH, Hd.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decl_commute" *)
Theorem evaluate_decl_commute : forall s fi sh v' e (ds : list (decl a)),
  evaluate_decls s (Function fi :: Decl sh v' e :: ds) =
  evaluate_decls s (Decl sh v' e :: Function fi :: ds).
Proof.
  intros s fi sh v' e ds; rewrite !evaluate_decls_cons_cases; cbn beta iota.
  rewrite (eval_state_cong (set_locals FEMPTY (set_code _ s)) (set_locals FEMPTY s)) by reflexivity.
  destruct (EVERY _ _ && _) eqn:Ew; cbn beta iota.
  - destruct (eval _ e) as [res|]; [|reflexivity].
    destruct (bool_decide _); [|reflexivity]. destruct s; cbn in *.
    rewrite Ew. reflexivity.
  - destruct (eval _ e) as [res|]; [|reflexivity].
    destruct (bool_decide _); [|reflexivity]. destruct s; cbn in *.
    rewrite Ew. reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "functions_eq_FILTER" *)
Theorem functions_eq_FILTER : forall prog : list (decl a),
  functions prog =
  MAP (fun x => match x with
                | Function fi => (name fi, (params fi, (body fi, fun_decl_return fi)))
                | _ => ARB
                end) (FILTER is_function prog).
Proof.
  induction prog as [|d ds IH]; [reflexivity|]. destruct d; cbn; rewrite IH; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "functions_append" *)
Theorem functions_append : forall prog1 prog2 : list (decl a),
  functions (prog1 ++ prog2) = functions prog1 ++ functions prog2.
Proof. induction prog1 as [|d ds IH]; intros; [reflexivity|]. destruct d; cbn; rewrite IH; reflexivity. Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "functions_FILTER" *)
Theorem functions_FILTER : forall prog : list (decl a),
  functions (FILTER is_function prog) = functions prog.
Proof. induction prog as [|d ds IH]; [reflexivity|]. destruct d; cbn; rewrite ?IH; reflexivity. Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "functions_FILTER'" *)
Theorem functions_FILTER' : forall prog : list (decl a),
  functions (FILTER is_decl prog) = [].
Proof. induction prog as [|d ds IH]; [reflexivity|]. destruct d; cbn; rewrite ?IH; reflexivity. Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "decs_stcnames_only_functions" *)
Theorem decs_stcnames_only_functions : forall ctxt (code : list (decl a)),
  is_true (EVERY (fun d => is_function d || is_decl d || is_exn_decl d) code) ->
  decs_stcnames ctxt code = SOME ctxt.
Proof.
  intros ctxt ds; induction ds as [|d ds IH]; intros Hd; [reflexivity|].
  destruct d; cbn in Hd |- *; try discriminate; apply IH, Hd.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "decs_stcnames_only_functions2" *)
Theorem decs_stcnames_only_functions2 : forall ctxt (code : list (decl a)),
  is_true (EVERY is_function code) -> decs_stcnames ctxt code = SOME ctxt.
Proof.
  intros ctxt ds; induction ds as [|d ds IH]; intros Hd; [reflexivity|].
  destruct d; cbn in Hd |- *; try discriminate; apply IH, Hd.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_swap_locals" *)
Theorem evaluate_decls_swap_locals : forall s (prog : list (decl a)) s' locals,
  evaluate_decls s prog = SOME s' ->
  evaluate_decls (set_locals locals s) prog = SOME (set_locals locals s').
Proof.
  intros s ds; revert s; induction ds as [|d ds IH]; intros s s' lc H.
  - injection H as <-; reflexivity.
  - rewrite evaluate_decls_cons_cases in H |- *.
    replace (set_locals FEMPTY (set_locals lc s)) with (set_locals FEMPTY s) by (destruct s; reflexivity).
    destruct d;
      repeat match type of H with
             | context [match ?x with _ => _ end] =>
                 let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H |- *
             end; try discriminate;
      try (exact (IH _ _ lc H));
      match goal with |- context [evaluate_decls ?S2 ds] =>
        match type of H with evaluate_decls ?S1 ds = _ =>
          replace S2 with (set_locals lc S1) by (destruct s; reflexivity)
        end
      end;
      destruct s; cbn in *; rewrite ?E; cbn; try exact (IH _ _ lc H).
Qed.

End Decls.

Lemma OPT_MMAP_mono_Forall {A B} (f g : A -> option B) l xs :
  OPT_MMAP f l = SOME xs -> Forall (fun x => forall y, f x = SOME y -> g x = SOME y) l ->
  OPT_MMAP g l = SOME xs.
Proof.
  intros H HF; revert xs H; induction HF as [|x l Hx _ IH]; intros xs H; [exact H|].
  cbn in H |- *. destruct (f x) as [y|] eqn:E; [|discriminate]; cbn in H.
  destruct (OPT_MMAP f l) as [ys|] eqn:E2; [|discriminate]; cbn in H.
  rewrite (Hx y eq_refl), (IH ys eq_refl); exact H.
Qed.

Ltac split_in_H H :=
  repeat match type of H with
  | context [match ?x with _ => _ end] =>
      lazymatch x with
      | context [match _ with _ => _ end] => fail
      | _ => let y := fresh "y" in let E := fresh "E" in
             remember x as y eqn:E in H; destruct y; symmetry in E; cbn beta iota zeta in H
      end
  end.

Ltac eval_mono_tac H :=
  cbn [eval] in H |- *; state_cbn; split_in_H H; try discriminate;
  repeat match goal with
         | E : eval ?S1 ?e' = SOME ?x,
           IH : forall v, eval ?S1 ?e' = SOME v -> _ |- _ =>
             let E' := fresh "E" in pose proof (IH x E) as E'; clear E
         | E : OPT_MMAP ?f ?l = SOME ?xs, IH : Forall _ ?l |- context [OPT_MMAP ?g ?l] =>
             let E' := fresh "E" in
             assert (E' : OPT_MMAP g l = SOME xs)
               by (eapply OPT_MMAP_mono_Forall; [exact E|exact IH]);
             clear E
         end;
  repeat (match goal with E : ?x = _ |- context [match ?x with _ => _ end] =>
            rewrite E; cbn beta iota zeta end);
  try congruence.


(** ** Variables of expressions, local updates *)

Section VarExp.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma In_FLAT_MAP {A B} (f : A -> list B) (l : list A) y :
  In y (FLAT (MAP f l)) <-> exists x, In x l /\ In y (f x).
Proof.
  rewrite in_concat; split.
  - intros [ys [Hys Hy]]; apply in_map_iff in Hys as [x [<- Hx]]; eauto.
  - intros [x [Hx Hy]]; exists (f x); split; [apply in_map, Hx|exact Hy].
Qed.

Lemma MEM_is_true_In {A} `{EqDecision A} (x : A) l : is_true (MEM x l) <-> In x l.
Proof. apply MEM_In. Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "flookup_res_var_some_eq_lookup" *)
Theorem flookup_res_var_some_eq_lookup : forall lc lc' (v0 : varname) (value : v a),
  FLOOKUP (res_var lc (v0, FLOOKUP lc' v0)) v0 = SOME value -> FLOOKUP lc' v0 = SOME value.
Proof.
  intros lc lc' v0 value; destruct (FLOOKUP lc' v0) eqn:E; cbn [res_var].
  - rewrite FLOOKUP_UPDATE; destruct (decide _); [exact id|congruence].
  - rewrite DOMSUB_FLOOKUP_THM; destruct (decide _); [discriminate|congruence].
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "flookup_res_var_diff_eq_org" *)
Theorem flookup_res_var_diff_eq_org : forall (n m : varname) lc (v0 : option (v a)),
  n <> m -> FLOOKUP (res_var lc (n, v0)) m = FLOOKUP lc m.
Proof.
  intros n m lc v0 H; destruct v0; cbn [res_var];
    [rewrite FLOOKUP_UPDATE|rewrite DOMSUB_FLOOKUP_THM]; destruct (decide _); congruence.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "FLOOKUP_pan_res_var_thm" *)
Theorem FLOOKUP_pan_res_var_thm : forall l (m n : varname) (v0 : option (v a)),
  FLOOKUP (res_var l (m, v0)) n = if decide (n = m) then v0 else FLOOKUP l n.
Proof.
  intros l m n v0; destruct v0; cbn [res_var];
    [rewrite FLOOKUP_UPDATE|rewrite DOMSUB_FLOOKUP_THM];
    destruct (decide (m = n)), (decide (n = m)); congruence.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "fdoms_eq_flookup_some_none" *)
Theorem fdoms_eq_flookup_some_none : forall {K V} (fm fm' : fmap K V) n (v0 : V),
  FDOM fm = FDOM fm' /\ FLOOKUP fm n = SOME v0 -> exists v1, FLOOKUP fm' n = SOME v1.
Proof.
  intros K V fm fm' n v0 [H1 H2].
  assert (Hd : FDOM fm' n) by (rewrite <- H1; unfold FDOM; congruence).
  unfold FDOM in Hd; destruct (FLOOKUP fm' n); [eauto|congruence].
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "update_locals_not_vars_eval_eq_eq" *)
Theorem update_locals_not_vars_eval_eq_eq : forall s (e : exp a) (v0 : v a) n w,
  ~ is_true (MEM n (var_exp e)) ->
  eval (set_locals (locals s |+ (n, w)) s) e = eval s e.
Proof.
  intros s e v0 n w; rewrite MEM_is_true_In.
  induction e using exp_nested_ind; cbn [eval var_exp]; intros Hn;
    rewrite ?in_app_iff in Hn;
    repeat match goal with IH : ~ In n (var_exp ?e) -> eval _ ?e = eval s ?e |- _ =>
             rewrite IH by tauto; clear IH end;
    try reflexivity.
  all: try (destruct vk; cbn [var_exp] in Hn; state_cbn; [|reflexivity]; rewrite FLOOKUP_UPDATE;
            destruct (decide _) as [->|]; [cbn in Hn; tauto|reflexivity]).
  all: match goal with IH : Forall _ ?l |- context [OPT_MMAP ?f ?l] =>
      erewrite (OPT_MMAP_ext_In f _ l); [reflexivity|]
    end.
  all: intros x Hx; rewrite Forall_forall in *.
  all: match goal with IH : forall x, In x _ -> _ |- _ => apply IH end; [exact Hx|];
    intros Hi; apply Hn, In_FLAT_MAP; eauto.
Qed.
(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "update_locals_not_vars_eval_eq" *)
Theorem update_locals_not_vars_eval_eq : forall s (e : exp a) (v0 : v a) n w,
  ~ is_true (MEM n (var_exp e)) /\ eval s e = SOME v0 ->
  eval (set_locals (locals s |+ (n, w)) s) e = SOME v0.
Proof. intros s e v0 n w [H1 H2]; rewrite update_locals_not_vars_eval_eq_eq; assumption. Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "update_locals_not_vars_eval_eq_NONE" *)
Theorem update_locals_not_vars_eval_eq_NONE : forall s (e : exp a) (v0 : v a) n w,
  ~ is_true (MEM n (var_exp e)) /\ eval s e = NONE ->
  eval (set_locals (locals s |+ (n, w)) s) e = NONE.
Proof. intros s e v0 n w [H1 H2]; rewrite update_locals_not_vars_eval_eq_eq; assumption. Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "eval_fresh_var" *)
Theorem eval_fresh_var : forall s (e : exp a) n w,
  ~ is_true (MEM n (var_exp e)) ->
  eval (set_locals (locals s |+ (n, w)) s) e = eval s e.
Proof. intros s e n w H; apply update_locals_not_vars_eval_eq_eq; [exact w|exact H]. Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "OPT_MMAP_update_locals_not_vars_eval_eq" *)
Theorem OPT_MMAP_update_locals_not_vars_eval_eq : forall s (es : list (exp a)) vs n w,
  ~ is_true (MEM n (FLAT (MAP var_exp es))) /\ OPT_MMAP (eval s) es = SOME vs ->
  OPT_MMAP (eval (set_locals (locals s |+ (n, w)) s)) es = SOME vs.
Proof.
  intros s es vs n w [H1 H2]; rewrite <- H2; apply OPT_MMAP_ext_In; intros x Hx.
  apply eval_fresh_var; rewrite MEM_is_true_In in *; intros Hi; apply H1, In_FLAT_MAP; eauto.
Qed.



(** Monotonicity of [eval] in the state: [H : eval S1 e = SOME v] (split)
    gives the goal [eval S2 e = SOME v] from the induction hypotheses. *)
(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "eval_empty_locals_IMP" *)
Theorem eval_empty_locals_IMP : forall s (e : exp a) v0,
  eval (set_locals FEMPTY s) e = SOME v0 -> eval s e = SOME v0.
Proof.
  intros s e; induction e using exp_nested_ind; intros rv Hev; eval_mono_tac Hev.
  all: try (destruct vk; cbn in Hev; discriminate).
Qed.

End VarExp.

(** ** Loads from memory *)

Section MemLoadProps.
Context {a : N}.
Local Open Scope word_scope.

Lemma mem_load_f_Comb' f (stcs : list (stcname * struct_info)) l (addr : word a) dm m :
  mem_load_f f stcs (Comb l) addr dm m =
  match mem_loads_f f stcs l addr dm m with
  | Some vs => SOME (RStruct vs) | None => NONE end.
Proof.
  destruct f as [|f]; [|apply mem_load_f_Comb].
  cbn [mem_load_f].
  match goal with |- match ?F l addr with _ => _ end = _ =>
    assert (E : forall l0 addr0, F l0 addr0 = mem_loads_f O stcs l0 addr0 dm m)
  end.
  { intros l0; induction l0 as [|x xs IH]; intros addr0; [reflexivity|].
    cbn [mem_loads_f]. rewrite <- IH. reflexivity. }
  rewrite E; reflexivity.
Qed.

Lemma mem_load_f_One f (stcs : list (stcname * struct_info)) (addr : word a) dm m :
  mem_load_f f stcs One addr dm m =
  if classical_dec (addr IN dm) then SOME (Val (m addr)) else NONE.
Proof. destruct f; reflexivity. Qed.

(** One induction for the properties of [mem_load] proved by HOL's
    [mem_load_ind]: a property [P] of the arguments and result, closed
    under the three equations. *)
Lemma mem_load_f_mono : forall f (stcs : list (stcname * struct_info)) sh (addr : word a)
    dm1 dm2 m1 m2 v0,
  (forall x, x IN dm1 -> x IN dm2 /\ m1 x = m2 x) ->
  mem_load_f f stcs sh addr dm1 m1 = SOME v0 -> mem_load_f f stcs sh addr dm2 m2 = SOME v0.
Proof.
  induction f as [|f IHf]; intros stcs sh addr dm1 dm2 m1 m2 v0 Hd;
    revert addr v0; induction sh as [| l Hl | nm] using shape_nested_ind; intros addr v0 H.
  all: lazymatch goal with
  | |- mem_load_f _ _ One _ _ _ = _ =>
       rewrite mem_load_f_One in H |- *;
       destruct (classical_dec (addr IN dm1)) as [Hi|]; [|discriminate];
       destruct (Hd addr Hi) as [Hi2 Hm];
       destruct (classical_dec (addr IN dm2)); [rewrite <- Hm; exact H|contradiction]
  | |- mem_load_f _ _ (Comb _) _ _ _ = _ =>
       rewrite mem_load_f_Comb' in H |- *;
       destruct (mem_loads_f _ stcs l addr dm1 m1) as [vs|] eqn:E; [|discriminate];
       enough (E2 : mem_loads_f _ stcs l addr dm2 m2 = SOME vs) by (rewrite E2; exact H);
       clear H; revert addr vs E; induction Hl as [|x xs Hx Hxs IHl]; intros addr vs E;
         [exact E|];
       cbn [mem_loads_f] in E |- *;
       destruct (mem_load_f _ stcs x addr dm1 m1) as [y|] eqn:Ey; [|discriminate];
       destruct (mem_loads_f _ stcs xs _ dm1 m1) as [ys|] eqn:Eys; [|discriminate];
       rewrite (Hx _ _ Ey), (IHl _ _ Eys); exact E
  | |- _ => idtac
  end.
  - rewrite mem_load_f_Named in H; destruct (dropWhile _ stcs) as [|[]]; discriminate.
  - rewrite mem_load_f_Named in H |- *.
    destruct (dropWhile _ stcs) as [|[nm' info] stcs']; [discriminate|].
    destruct (mem_load_flds_f f stcs' (fields info) addr dm1 m1) as [vf|] eqn:E; [|discriminate].
    enough (E2 : mem_load_flds_f f stcs' (fields info) addr dm2 m2 = SOME vf) by (rewrite E2; exact H).
    clear H; revert addr vf E; induction (fields info) as [|[fld sh] fl IHfl]; intros addr vf E;
      [exact E|].
    cbn [mem_load_flds_f] in E |- *.
    destruct (mem_load_f f stcs' sh addr dm1 m1) as [y|] eqn:Ey; [|discriminate].
    destruct (mem_load_flds_f f stcs' fl _ dm1 m1) as [ys|] eqn:Eys; [|discriminate].
    rewrite (IHf _ _ _ _ _ _ _ _ Hd Ey), (IHfl _ _ Eys); exact E.
Qed.

Lemma mem_loads_f_mono f (stcs : list (stcname * struct_info)) shs (addr : word a) dm1 dm2 m1 m2 vs :
  (forall x, x IN dm1 -> x IN dm2 /\ m1 x = m2 x) ->
  mem_loads_f f stcs shs addr dm1 m1 = SOME vs -> mem_loads_f f stcs shs addr dm2 m2 = SOME vs.
Proof.
  intros Hd; revert addr vs; induction shs as [|x xs IH]; intros addr vs E; [exact E|].
  cbn [mem_loads_f] in E |- *.
  destruct (mem_load_f f stcs x addr dm1 m1) as [y|] eqn:Ey; [|discriminate].
  destruct (mem_loads_f f stcs xs _ dm1 m1) as [ys|] eqn:Eys; [|discriminate].
  rewrite (mem_load_f_mono _ _ _ _ _ _ _ _ _ Hd Ey), (IH _ _ Eys); exact E.
Qed.

Lemma mem_load_flds_f_mono f (stcs : list (stcname * struct_info)) fl (addr : word a) dm1 dm2 m1 m2 vs :
  (forall x, x IN dm1 -> x IN dm2 /\ m1 x = m2 x) ->
  mem_load_flds_f f stcs fl addr dm1 m1 = SOME vs -> mem_load_flds_f f stcs fl addr dm2 m2 = SOME vs.
Proof.
  intros Hd; revert addr vs; induction fl as [|[fld x] xs IH]; intros addr vs E; [exact E|].
  cbn [mem_load_flds_f] in E |- *.
  destruct (mem_load_f f stcs x addr dm1 m1) as [y|] eqn:Ey; [|discriminate].
  destruct (mem_load_flds_f f stcs xs _ dm1 m1) as [ys|] eqn:Eys; [|discriminate].
  rewrite (mem_load_f_mono _ _ _ _ _ _ _ _ _ Hd Ey), (IH _ _ Eys); exact E.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "mem_load_swap_memory" *)
Theorem mem_load_swap_memory :
  (forall sh (addr : word a) addrs memory1 stcs v0 memory2,
     mem_load sh addr addrs memory1 stcs = SOME v0 /\
     (forall addr, addr IN addrs -> memory1 addr = memory2 addr) ->
     mem_load sh addr addrs memory2 stcs = SOME v0) /\
  (forall shs (addr : word a) addrs memory1 stcs v0 memory2,
     mem_loads shs addr addrs memory1 stcs = SOME v0 /\
     (forall addr, addr IN addrs -> memory1 addr = memory2 addr) ->
     mem_loads shs addr addrs memory2 stcs = SOME v0) /\
  (forall flds (addr : word a) addrs memory1 stcs vs memory2,
     mem_load_flds flds addr addrs memory1 stcs = SOME vs /\
     (forall addr, addr IN addrs -> memory1 addr = memory2 addr) ->
     mem_load_flds flds addr addrs memory2 stcs = SOME vs).
Proof.
  refine (conj _ (conj _ _)); intros x addr addrs m1 stcs v0 m2 [H Hm].
  all: first [eapply mem_load_f_mono; [|exact H] | eapply mem_loads_f_mono; [|exact H]
             | eapply mem_load_flds_f_mono; [|exact H]]; intros y Hy; split; [exact Hy|apply Hm, Hy].
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "mem_load_swap_memaddrs" *)
Theorem mem_load_swap_memaddrs :
  (forall sh (addr : word a) addrs memory stcs v0 addrs2,
     mem_load sh addr addrs memory stcs = SOME v0 /\ addrs SUBSET addrs2 ->
     mem_load sh addr addrs2 memory stcs = SOME v0) /\
  (forall shs (addr : word a) addrs memory stcs v0 addrs2,
     mem_loads shs addr addrs memory stcs = SOME v0 /\ addrs SUBSET addrs2 ->
     mem_loads shs addr addrs2 memory stcs = SOME v0) /\
  (forall flds (addr : word a) addrs memory stcs vs addrs2,
     mem_load_flds flds addr addrs memory stcs = SOME vs /\ addrs SUBSET addrs2 ->
     mem_load_flds flds addr addrs2 memory stcs = SOME vs).
Proof.
  refine (conj _ (conj _ _)); intros x addr addrs m stcs v0 a2 [H Hs].
  all: first [eapply mem_load_f_mono; [|exact H] | eapply mem_loads_f_mono; [|exact H]
             | eapply mem_load_flds_f_mono; [|exact H]]; intros y Hy; split; [apply Hs, Hy|reflexivity].
Qed.

End MemLoadProps.

Section EvalMono.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.
Local Open Scope word_scope.

(** HOL [s with memaddrs := x] (Galette helper; [panSem] has no
    [set_memaddrs]). *)
Definition set_memaddrs x (s : state a ffi_t) := mk_state s.(locals) s.(globals) s.(structs) s.(code) s.(eshapes) s.(memory) x s.(sh_memaddrs) s.(clock) s.(be) s.(ffi) s.(base_addr) s.(top_addr).

Lemma mem_load_byte_mono (m1 m2 : word a -> word_lab a) dm1 dm2 be0 w b :
  (forall x, x IN dm1 -> x IN dm2 /\ m1 x = m2 x) ->
  mem_load_byte m1 dm1 be0 w = SOME b -> mem_load_byte m2 dm2 be0 w = SOME b.
Proof.
  intros Hd; unfold mem_load_byte.
  destruct (classical_dec (byte_align w IN dm1)) as [Hi|];
    [|destruct (m1 (byte_align w)); discriminate].
  destruct (Hd _ Hi) as [Hi2 Hm]; rewrite <- Hm.
  destruct (m1 (byte_align w)); destruct (classical_dec (byte_align w IN dm2)); [exact id|contradiction].
Qed.

Lemma mem_load_32_mono (m1 m2 : word a -> word_lab a) dm1 dm2 be0 w b :
  (forall x, x IN dm1 -> x IN dm2 /\ m1 x = m2 x) ->
  mem_load_32 m1 dm1 be0 w = SOME b -> mem_load_32 m2 dm2 be0 w = SOME b.
Proof.
  intros Hd; unfold mem_load_32. destruct (aligned 2 w); [|discriminate].
  destruct (classical_dec (byte_align w IN dm1)) as [Hi|];
    [|destruct (m1 (byte_align w)); discriminate].
  destruct (Hd _ Hi) as [Hi2 Hm]; rewrite <- Hm.
  destruct (m1 (byte_align w)); destruct (classical_dec (byte_align w IN dm2)); [exact id|contradiction].
Qed.

Lemma eval_mono s1 s2 :
  locals s1 = locals s2 -> globals s1 = globals s2 -> structs s1 = structs s2 ->
  be s1 = be s2 -> base_addr s1 = base_addr s2 -> top_addr s1 = top_addr s2 ->
  (forall x, x IN memaddrs s1 -> x IN memaddrs s2 /\ memory s1 x = memory s2 x) ->
  forall e v0, eval s1 e = SOME v0 -> eval s2 e = SOME v0.
Proof.
  intros H1 H2 H3 H4 H5 H6 Hd e; induction e using exp_nested_ind; intros rv Hev;
    cbn [eval] in Hev |- *; rewrite <- ?H1, <- ?H2, <- ?H3, <- ?H4, <- ?H5, <- ?H6;
    eval_mono_tac Hev.
  all: try (destruct vk; cbn in *; congruence).
  all: try (eapply mem_load_f_mono; [exact Hd|eassumption]).
  all: match goal with
       | E : mem_load_32 _ _ _ _ = SOME _ |- _ => rewrite (mem_load_32_mono _ _ _ _ _ _ _ Hd E)
       | E : mem_load_byte _ _ _ _ = SOME _ |- _ => rewrite (mem_load_byte_mono _ _ _ _ _ _ _ Hd E)
       end; exact Hev.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "eval_swap_memaddrs" *)
Theorem eval_swap_memaddrs : forall s exp (v0 : v a) memaddrs,
  eval s exp = SOME v0 /\ panSem.memaddrs s SUBSET memaddrs ->
  eval (set_memaddrs memaddrs s) exp = SOME v0.
Proof.
  intros s e v0 m [H Hs]; apply (eval_mono s (set_memaddrs m s)); try reflexivity; [|exact H].
  intros x Hx; split; [apply Hs, Hx|reflexivity].
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "eval_swap_memory" *)
Theorem eval_swap_memory : forall s exp (v0 : v a) mry,
  eval s exp = SOME v0 /\ (forall addr, addr IN memaddrs s -> memory s addr = mry addr) ->
  eval (set_memory mry s) exp = SOME v0.
Proof.
  intros s e v0 m [H Hs]; apply (eval_mono s (set_memory m s)); try reflexivity; [|exact H].
  intros x Hx; split; [exact Hx|apply Hs, Hx].
Qed.

End EvalMono.

Section DeclsSwap.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma evaluate_decls_swap_gen (G : state a ffi_t -> state a ffi_t) (P : state a ffi_t -> Prop) :
  (forall s, structs (G s) = structs s /\ code (G s) = code s /\ eshapes (G s) = eshapes s /\
             globals (G s) = globals s) ->
  (forall s x, G (set_globals x s) = set_globals x (G s) /\ P (set_globals x s) = P s) ->
  (forall s x, G (set_code x s) = set_code x (G s) /\ P (set_code x s) = P s) ->
  (forall s x, G (set_eshapes x s) = set_eshapes x (G s) /\ P (set_eshapes x s) = P s) ->
  (forall s e v0, P s -> eval (set_locals FEMPTY s) e = SOME v0 ->
                  eval (set_locals FEMPTY (G s)) e = SOME v0) ->
  forall (ds : list (decl a)) s s', P s -> evaluate_decls s ds = SOME s' ->
  evaluate_decls (G s) ds = SOME (G s').
Proof.
  intros HG Hgl Hco Hes Hev ds; induction ds as [|d ds IH]; intros s s' Hp H.
  - injection H as <-; reflexivity.
  - rewrite evaluate_decls_cons_cases in H |- *.
    destruct (HG s) as [Hst [Hc [He Hg]]].
    destruct d; rewrite ?Hst, ?Hc, ?He, ?Hg.
    + destruct (_ && _); [|discriminate].
      rewrite <- (proj1 (Hco _ _)). apply IH; [rewrite (proj2 (Hco _ _)); exact Hp|exact H].
    + destruct (eval (set_locals FEMPTY s) e) as [res|] eqn:E; [|discriminate].
      rewrite (Hev _ _ _ Hp E).
      destruct (bool_decide _); [|discriminate].
      rewrite <- (proj1 (Hgl _ _)). apply IH; [rewrite (proj2 (Hgl _ _)); exact Hp|exact H].
    + destruct (_ && _); [|discriminate].
      rewrite <- (proj1 (Hes _ _)). apply IH; [rewrite (proj2 (Hes _ _)); exact Hp|exact H].
    + apply IH; assumption.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_swap_memaddrs" *)
Theorem evaluate_decls_swap_memaddrs : forall s (prog : list (decl a)) s' memaddrs,
  evaluate_decls s prog = SOME s' /\ panSem.memaddrs s SUBSET memaddrs ->
  evaluate_decls (set_memaddrs memaddrs s) prog = SOME (set_memaddrs memaddrs s').
Proof.
  intros s ds s' m [H Hs].
  apply (evaluate_decls_swap_gen (set_memaddrs m) (fun s => panSem.memaddrs s SUBSET m));
    try exact H; try exact Hs.
  - intros t; repeat split.
  - intros t x; split; [destruct t; reflexivity|reflexivity].
  - intros t x; split; [destruct t; reflexivity|reflexivity].
  - intros t x; split; [destruct t; reflexivity|reflexivity].
  - intros t e v0 Hp He. rewrite (eval_state_cong _ (set_memaddrs m (set_locals FEMPTY t))) by reflexivity.
    apply eval_swap_memaddrs; split; [exact He|exact Hp].
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_memaddrs_mono" *)
Theorem evaluate_decls_memaddrs_mono : forall s (prog : list (decl a)) s' memaddrs,
  evaluate_decls s prog = SOME s' /\ panSem.memaddrs s SUBSET memaddrs ->
  evaluate_decls (set_memaddrs memaddrs s) prog = SOME (set_memaddrs memaddrs s').
Proof. exact evaluate_decls_swap_memaddrs. Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_swap_memory" *)
Theorem evaluate_decls_swap_memory : forall s (prog : list (decl a)) s' mry,
  evaluate_decls s prog = SOME s' /\
  (forall addr, addr IN memaddrs s -> memory s addr = mry addr) ->
  evaluate_decls (set_memory mry s) prog = SOME (set_memory mry s').
Proof.
  intros s ds s' m [H Hs].
  apply (evaluate_decls_swap_gen (set_memory m)
           (fun s => forall addr, addr IN memaddrs s -> memory s addr = m addr));
    try exact H; try exact Hs.
  - intros t; repeat split.
  - intros t x; split; [destruct t; reflexivity|reflexivity].
  - intros t x; split; [destruct t; reflexivity|reflexivity].
  - intros t x; split; [destruct t; reflexivity|reflexivity].
  - intros t e v0 Hp He. rewrite (eval_state_cong _ (set_memory m (set_locals FEMPTY t))) by reflexivity.
    apply eval_swap_memory; split; [exact He|exact Hp].
Qed.

End DeclsSwap.

(** ** Well-formed values *)

Section WfShapes.
Context {a : N}.

(** Induction on values with induction hypotheses for the nested lists. *)
Fixpoint v_nested_ind (P : v a -> Prop) (Hval : forall w, P (Val w))
    (Hrs : forall vs, Forall P vs -> P (RStruct vs))
    (Hns : forall nm vs, Forall (fun p => P (snd p)) vs -> P (NStruct nm vs)) (x : v a) : P x :=
  let rec := v_nested_ind P Hval Hrs Hns in
  match x with
  | Val w => Hval w
  | RStruct vs =>
      Hrs vs ((fix go (l : list (v a)) : Forall P l :=
                 match l with [] => Forall_nil _ | y :: ys => Forall_cons _ (rec y) (go ys) end) vs)
  | NStruct nm vs =>
      Hns nm vs ((fix go (l : list (fldname * v a)) : Forall (fun p => P (snd p)) l :=
                    match l with [] => Forall_nil _ | y :: ys => Forall_cons _ (rec (snd y)) (go ys) end) vs)
  end.

(** HOL [is_wf_shape_v] (structural; HOL's equations are [is_wf_shape_v_def]). *)
Fixpoint is_wf_shape_v (sctxt : list (stcname * struct_info)) (x : v a) : bool :=
  match x with
  | Val _ => true
  | RStruct vs =>
      (fix go (l : list (v a)) : bool :=
         match l with [] => true | y :: ys => is_wf_shape_v sctxt y && go ys end) vs
  | NStruct nm nm_vs =>
      negb ⌜ALOOKUP sctxt nm = NONE⌝ &&
      (fix go (l : list (fldname * v a)) : bool :=
         match l with [] => true | y :: ys => is_wf_shape_v sctxt (snd y) && go ys end) nm_vs
  end.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "is_wf_shape_v_def" *)
Theorem is_wf_shape_v_def : forall sctxt,
  (forall v0, is_wf_shape_v sctxt (Val v0) = true) /\
  (forall vs, is_wf_shape_v sctxt (RStruct vs) = EVERY (is_wf_shape_v sctxt) vs) /\
  (forall nm nm_vs, is_wf_shape_v sctxt (NStruct nm nm_vs) =
     negb ⌜ALOOKUP sctxt nm = NONE⌝ && EVERY (is_wf_shape_v sctxt) (MAP SND nm_vs)).
Proof.
  intros sctxt; split; [reflexivity|split].
  - intros vs; cbn; induction vs as [|y ys IH]; [reflexivity|]; cbn; rewrite IH; reflexivity.
  - intros nm vs; cbn; f_equal; induction vs as [|y ys IH]; [reflexivity|]; cbn; rewrite IH; reflexivity.
Qed.

Lemma is_wf_shape_v_RStruct sctxt vs :
  is_true (is_wf_shape_v sctxt (RStruct vs)) <-> Forall (fun x => is_true (is_wf_shape_v sctxt x)) vs.
Proof.
  rewrite (proj1 (proj2 (is_wf_shape_v_def sctxt))); unfold is_true; rewrite EVERY_Forall; reflexivity.
Qed.

Lemma is_wf_shape_v_NStruct sctxt nm vs :
  is_true (is_wf_shape_v sctxt (NStruct nm vs)) <->
  ALOOKUP sctxt nm <> NONE /\ Forall (fun p => is_true (is_wf_shape_v sctxt (snd p))) vs.
Proof.
  rewrite (proj2 (proj2 (is_wf_shape_v_def sctxt))); unfold is_true.
  rewrite Bool.andb_true_iff, Bool.negb_true_iff, EVERY_Forall, Forall_map.
  split; intros [H1 H2]; split; try exact H2.
  - intros Hc; rewrite (proj2 (bool_decide_spec _) Hc) in H1; discriminate.
  - destruct (bool_decide _) eqn:E; [apply bool_decide_spec in E; contradiction|reflexivity].
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "is_wf_shape_of_v" *)
Theorem is_wf_shape_of_v : forall sctxt (x : v a),
  is_true (is_wf_shape_v sctxt x) -> is_true (is_wf_shape sctxt (shape_of x)).
Proof.
  intros sctxt x; induction x as [w|vs IH|nm vs IH] using v_nested_ind; intros H; [reflexivity| |].
  - rewrite is_wf_shape_v_RStruct in H. cbn [shape_of is_wf_shape]. unfold is_true.
    rewrite EVERY_Forall, Forall_map. rewrite Forall_forall in *. intros x Hx; apply (IH x Hx); apply H; exact Hx.
  - apply is_wf_shape_v_NStruct in H as [H _]. cbn. destruct (ALOOKUP sctxt nm); [reflexivity|congruence].
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "is_wf_shape_v_nil_step1" *)
Theorem is_wf_shape_v_nil_step1 : forall sctxt (x : v a),
  sctxt = [] /\ is_true (is_wf_shape sctxt (shape_of x)) -> is_true (is_wf_shape_v sctxt x).
Proof.
  intros sctxt x; induction x as [w|vs IH|nm vs IH] using v_nested_ind; intros [-> H]; [reflexivity| |].
  - apply is_wf_shape_v_RStruct. cbn [shape_of is_wf_shape] in H. unfold is_true in H.
    rewrite EVERY_Forall, Forall_map in H. rewrite Forall_forall in *.
    intros x Hx; apply IH; [exact Hx|split; [reflexivity|apply H, Hx]].
  - discriminate.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "is_wf_shape_v_nil" 56 *)
Theorem is_wf_shape_v_nil_thm : forall (x : v a) xs,
  xs = [] -> is_wf_shape xs (shape_of x) = is_wf_shape_v xs x.
Proof.
  intros x xs Hxs; apply Bool.eq_true_iff_eq; split; intros H.
  - apply is_wf_shape_v_nil_step1; split; assumption.
  - apply is_wf_shape_of_v, H.
Qed.

Lemma ALOOKUP_DROP_not_none (k : N) (sctxt : list (stcname * struct_info)) nm :
  ALOOKUP (DROP k sctxt) nm <> NONE -> ALOOKUP sctxt nm <> NONE.
Proof.
  rewrite DROP_skipn; intros H Hn; apply H. apply ALOOKUP_None_iff in Hn; apply ALOOKUP_None_iff.
  intros Hi; apply Hn. rewrite <- (firstn_skipn (N.to_nat k) sctxt), map_app.
  apply in_or_app; right; exact Hi.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "is_wf_shape_v_drop" *)
Theorem is_wf_shape_v_drop : forall k sctxt (x : v a),
  is_true (is_wf_shape_v (DROP k sctxt) x) -> is_true (is_wf_shape_v sctxt x).
Proof.
  intros k sctxt x; induction x as [w|vs IH|nm vs IH] using v_nested_ind; intros H; [reflexivity| |].
  - rewrite is_wf_shape_v_RStruct in *. rewrite Forall_forall in *. intros y Hy; apply (IH y Hy); apply H; exact Hy.
  - rewrite is_wf_shape_v_NStruct in *. destruct H as [H1 H2]; split.
    + eapply ALOOKUP_DROP_not_none, H1.
    + rewrite Forall_forall in *; intros y Hy; apply (IH y Hy); apply H2; exact Hy.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "pan_primop_is_wf_shape_v" *)
Theorem pan_primop_is_wf_shape_v : forall sctxt pop (args : list (v a)) value,
  pan_primop pop args = SOME value -> is_true (is_wf_shape_v sctxt value).
Proof.
  intros sctxt [] args value; unfold pan_primop.
  destruct (_ && _); [|discriminate].
  destruct (backend_common.word_add_carry _ _ _); intros H; injection H as <-; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "dropWhile_eq_cons_IMP" *)
Theorem dropWhile_eq_cons_IMP : forall {A} `{Inhabited A} (P : A -> bool) xs y ys,
  dropWhile P xs = y :: ys ->
  exists n, n < LENGTH xs /\ y = EL n xs /\ ~ is_true (P y) /\ DROP n xs = y :: ys.
Proof.
  intros A HA P xs; induction xs as [|x xs IH]; intros y ys H; [discriminate|].
  cbn in H. destruct (P x) eqn:E.
  - destruct (IH _ _ H) as [n [H1 [H2 [H3 H4]]]]. exists (n + 1).
    rewrite LENGTH_cons; split; [lia|]. rewrite EL_cons_pos by lia.
    replace (n + 1 - 1) with n by lia. split; [exact H2|split; [exact H3|]].
    rewrite DROP_skipn in *. replace (N.to_nat (n + 1)) with (Datatypes.S (N.to_nat n)) by lia.
    exact H4.
  - injection H as <- <-. exists 0. rewrite LENGTH_cons. split; [lia|].
    split; [reflexivity|split; [unfold is_true; congruence|reflexivity]].
Qed.

Lemma dropWhile_nm (stcs : list (stcname * struct_info)) nm nm' info stcs' :
  dropWhile (fun '(n, i) => negb (bool_decide (n = nm))) stcs = (nm', info) :: stcs' ->
  nm' = nm /\ In (nm', info) stcs /\ exists k, stcs' = DROP k stcs.
Proof.
  revert stcs'; induction stcs as [|[n i] stcs IH]; intros stcs' H; [discriminate|].
  cbn in H. destruct (bool_decide (n = nm)) eqn:E; cbn in H.
  - injection H as -> -> ->. apply bool_decide_spec in E.
    split; [exact E|split; [left; reflexivity|exists 1; rewrite DROP_skipn; reflexivity]].
  - destruct (IH _ H) as [H1 [H2 [k H3]]]. split; [exact H1|split; [right; exact H2|]].
    exists (k + 1). rewrite H3, !DROP_skipn.
    replace (N.to_nat (k + 1)) with (Datatypes.S (N.to_nat k)) by lia; reflexivity.
Qed.

Lemma mem_load_f_wf : forall f (stcs : list (stcname * struct_info)) sh (addr : word a) dm m v0,
  mem_load_f f stcs sh addr dm m = SOME v0 -> is_true (is_wf_shape_v stcs v0).
Proof.
  induction f as [|f IHf]; intros stcs sh; induction sh as [| l Hl | nm] using shape_nested_ind;
    intros addr dm m v0 H.
  all: lazymatch goal with
  | H : mem_load_f _ _ One _ _ _ = _ |- _ =>
      rewrite mem_load_f_One in H; destruct (classical_dec _); [|discriminate];
      injection H as <-; reflexivity
  | H : mem_load_f _ _ (Comb _) _ _ _ = _ |- _ =>
      rewrite mem_load_f_Comb' in H;
      destruct (mem_loads_f _ stcs l addr dm m) as [vs|] eqn:E; [|discriminate];
      injection H as <-; apply is_wf_shape_v_RStruct;
      clear - Hl E; revert addr vs E; induction Hl as [|x xs Hx Hxs IHl]; intros addr vs E;
        [injection E as <-; constructor|];
      cbn [mem_loads_f] in E;
      destruct (mem_load_f _ stcs x addr dm m) as [y|] eqn:Ey; [|discriminate];
      destruct (mem_loads_f _ stcs xs _ dm m) as [ys|] eqn:Eys; [|discriminate];
      injection E as <-; constructor; [exact (Hx _ _ _ _ Ey)|exact (IHl _ _ Eys)]
  | _ => idtac
  end.
  - rewrite mem_load_f_Named in H; destruct (dropWhile _ stcs) as [|[]]; discriminate.
  - rewrite mem_load_f_Named in H.
    destruct (dropWhile _ stcs) as [|[nm' info] stcs'] eqn:Ed; [discriminate|].
    destruct (dropWhile_nm _ _ _ _ _ Ed) as [-> [Hin [k Hk]]].
    destruct (mem_load_flds_f f stcs' (fields info) addr dm m) as [vf|] eqn:E; [|discriminate].
    injection H as <-. apply is_wf_shape_v_NStruct; split.
    + intros Hn; apply ALOOKUP_None_iff in Hn; apply Hn, in_map_iff; exists (nm, info); split; [reflexivity|exact Hin].
    + clear Ed Hin. revert addr vf E; induction (fields info) as [|[fld sh] fl IHfl]; intros addr vf E;
        [injection E as <-; constructor|].
      cbn [mem_load_flds_f] in E.
      destruct (mem_load_f f stcs' sh addr dm m) as [y|] eqn:Ey; [|discriminate].
      destruct (mem_load_flds_f f stcs' fl _ dm m) as [ys|] eqn:Eys; [|discriminate].
      injection E as <-; constructor; [|exact (IHfl _ _ Eys)].
      cbn [snd]; apply (is_wf_shape_v_drop k); rewrite <- Hk; exact (IHf _ _ _ _ _ _ Ey).
Qed.

Lemma mem_loads_f_wf f (stcs : list (stcname * struct_info)) shs (addr : word a) dm m vs :
  mem_loads_f f stcs shs addr dm m = SOME vs -> Forall (fun x => is_true (is_wf_shape_v stcs x)) vs.
Proof.
  revert addr vs; induction shs as [|x xs IH]; intros addr vs E; [injection E as <-; constructor|].
  cbn [mem_loads_f] in E.
  destruct (mem_load_f f stcs x addr dm m) as [y|] eqn:Ey; [|discriminate].
  destruct (mem_loads_f f stcs xs _ dm m) as [ys|] eqn:Eys; [|discriminate].
  injection E as <-; constructor; [exact (mem_load_f_wf _ _ _ _ _ _ _ Ey)|exact (IH _ _ Eys)].
Qed.

Lemma mem_load_flds_f_wf f (stcs : list (stcname * struct_info)) fl (addr : word a) dm m vs :
  mem_load_flds_f f stcs fl addr dm m = SOME vs ->
  Forall (fun x => is_true (is_wf_shape_v stcs x)) (MAP SND vs).
Proof.
  revert addr vs; induction fl as [|[fld x] xs IH]; intros addr vs E; [injection E as <-; constructor|].
  cbn [mem_load_flds_f] in E.
  destruct (mem_load_f f stcs x addr dm m) as [y|] eqn:Ey; [|discriminate].
  destruct (mem_load_flds_f f stcs xs _ dm m) as [ys|] eqn:Eys; [|discriminate].
  injection E as <-; constructor; [exact (mem_load_f_wf _ _ _ _ _ _ _ Ey)|exact (IH _ _ Eys)].
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "mem_load_is_wf_shape_v" *)
Theorem mem_load_is_wf_shape_v :
  (forall shape (w : word a) sa sm sctxt v0,
     mem_load shape w sa sm sctxt = SOME v0 -> is_true (is_wf_shape_v sctxt v0)) /\
  (forall shapes (w : word a) sa sm sctxt vs,
     mem_loads shapes w sa sm sctxt = SOME vs -> is_true (EVERY (is_wf_shape_v sctxt) vs)) /\
  (forall flds (w : word a) sa sm sctxt nm_vs,
     mem_load_flds flds w sa sm sctxt = SOME nm_vs ->
     is_true (EVERY (is_wf_shape_v sctxt) (MAP SND nm_vs))).
Proof.
  refine (conj _ (conj _ _)); intros.
  - eapply mem_load_f_wf; eassumption.
  - unfold is_true; rewrite EVERY_Forall; eapply mem_loads_f_wf; eassumption.
  - unfold is_true; rewrite EVERY_Forall; eapply mem_load_flds_f_wf; eassumption.
Qed.

Lemma mem_load_f_shape : forall f (stcs : list (stcname * struct_info)) sh (addr : word a) dm m v0,
  mem_load_f f stcs sh addr dm m = SOME v0 -> shape_of v0 = sh.
Proof.
  induction f as [|f IHf]; intros stcs sh; induction sh as [| l Hl | nm] using shape_nested_ind;
    intros addr dm m v0 H.
  all: lazymatch goal with
  | H : mem_load_f _ _ One _ _ _ = _ |- _ =>
      rewrite mem_load_f_One in H; destruct (classical_dec _); [|discriminate];
      injection H as <-; reflexivity
  | H : mem_load_f _ _ (Comb _) _ _ _ = _ |- _ =>
      rewrite mem_load_f_Comb' in H;
      destruct (mem_loads_f _ stcs l addr dm m) as [vs|] eqn:E; [|discriminate];
      injection H as <-; cbn [shape_of]; f_equal;
      clear - Hl E; revert addr vs E; induction Hl as [|x xs Hx Hxs IHl]; intros addr vs E;
        [injection E as <-; reflexivity|];
      cbn [mem_loads_f] in E;
      destruct (mem_load_f _ stcs x addr dm m) as [y|] eqn:Ey; [|discriminate];
      destruct (mem_loads_f _ stcs xs _ dm m) as [ys|] eqn:Eys; [|discriminate];
      injection E as <-; cbn [MAP List.map]; rewrite (Hx _ _ _ _ Ey), (IHl _ _ Eys); reflexivity
  | _ => idtac
  end.
  - rewrite mem_load_f_Named in H; destruct (dropWhile _ stcs) as [|[]]; discriminate.
  - rewrite mem_load_f_Named in H.
    destruct (dropWhile _ stcs) as [|[nm' info] stcs'] eqn:Ed; [discriminate|].
    destruct (dropWhile_nm _ _ _ _ _ Ed) as [-> _].
    destruct (mem_load_flds_f f stcs' (fields info) addr dm m); [|discriminate].
    injection H as <-; reflexivity.
Qed.

Lemma mem_loads_f_shape f (stcs : list (stcname * struct_info)) shs (addr : word a) dm m vs :
  mem_loads_f f stcs shs addr dm m = SOME vs -> MAP shape_of vs = shs.
Proof.
  revert addr vs; induction shs as [|x xs IH]; intros addr vs E; [injection E as <-; reflexivity|].
  cbn [mem_loads_f] in E.
  destruct (mem_load_f f stcs x addr dm m) as [y|] eqn:Ey; [|discriminate].
  destruct (mem_loads_f f stcs xs _ dm m) as [ys|] eqn:Eys; [|discriminate].
  injection E as <-; cbn [MAP List.map]; rewrite (mem_load_f_shape _ _ _ _ _ _ _ Ey), (IH _ _ Eys); reflexivity.
Qed.

Lemma mem_load_flds_f_shape f (stcs : list (stcname * struct_info)) fl (addr : word a) dm m vs :
  mem_load_flds_f f stcs fl addr dm m = SOME vs -> MAP (shape_of ∘ SND) vs = MAP SND fl.
Proof.
  revert addr vs; induction fl as [|[fld x] xs IH]; intros addr vs E; [injection E as <-; reflexivity|].
  cbn [mem_load_flds_f] in E.
  destruct (mem_load_f f stcs x addr dm m) as [y|] eqn:Ey; [|discriminate].
  destruct (mem_load_flds_f f stcs xs _ dm m) as [ys|] eqn:Eys; [|discriminate].
  injection E as <-; cbn [MAP List.map snd]; rewrite (mem_load_f_shape _ _ _ _ _ _ _ Ey), (IH _ _ Eys); reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "mem_loads_some_shape_eq" *)
Theorem mem_loads_some_shape_eq :
  (forall sh adr dm (m : word a -> word_lab a) stcs v0,
     mem_load sh adr dm m stcs = SOME v0 -> shape_of v0 = sh) /\
  (forall shs adr dm (m : word a -> word_lab a) stcs vs,
     mem_loads shs adr dm m stcs = SOME vs -> MAP shape_of vs = shs) /\
  (forall flds adr dm (m : word a -> word_lab a) stcs vs,
     mem_load_flds flds adr dm m stcs = SOME vs -> MAP (shape_of ∘ SND) vs = MAP SND flds).
Proof.
  refine (conj _ (conj _ _)); intros.
  - eapply mem_load_f_shape; eassumption.
  - eapply mem_loads_f_shape; eassumption.
  - eapply mem_load_flds_f_shape; eassumption.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "mem_load_some_shape_eq" *)
Theorem mem_load_some_shape_eq : forall sh adr dm (m : word a -> word_lab a) stcs v0,
  mem_load sh adr dm m stcs = SOME v0 -> shape_of v0 = sh.
Proof. exact (proj1 mem_loads_some_shape_eq). Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "size_of_sh_with_ctxt_eq" *)
Theorem size_of_sh_with_ctxt_eq : forall sh sctxt,
  is_true (is_wf_shape_nil sh) -> size_of_sh_with_ctxt sctxt sh = size_of_shape sh.
Proof.
  intros sh sctxt; induction sh as [| l Hl | nm] using shape_nested_ind; intros H;
    [reflexivity| |discriminate].
  cbn [size_of_sh_with_ctxt size_of_shape is_wf_shape] in *. f_equal.
  unfold is_true in H; rewrite EVERY_Forall in H.
  induction Hl as [|x xs Hx Hxs IHl]; [reflexivity|]. inversion H; subst.
  cbn [MAP List.map]; rewrite Hx, IHl by assumption; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "length_flatten_eq_size_of_shape" *)
Theorem length_flatten_eq_size_of_shape : forall x : v a,
  is_true (is_wf_shape_nil (shape_of x)) -> LENGTH (flatten x) = size_of_shape (shape_of x).
Proof.
  intros x; induction x as [w|vs IH|nm vs IH] using v_nested_ind; intros H; [reflexivity| |discriminate].
  cbn [flatten shape_of size_of_shape is_wf_shape] in *.
  unfold is_true in H; rewrite EVERY_Forall, Forall_map in H.
  induction IH as [|x xs Hx Hxs IHl]; [reflexivity|]. inversion H; subst.
  cbn [MAP List.map FLAT List.concat SUM]. rewrite <- IHl by assumption.
  rewrite !LENGTH_length, length_app, <- Hx by assumption. rewrite LENGTH_length. lia.
Qed.

End WfShapes.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "is_wf_shape_v_nil" 36 *)
Abbreviation is_wf_shape_v_nil := (is_wf_shape_v ([] : list (stcname * struct_info))).

Section EvalWf.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "OPT_MMAP_MEM_IMP" *)
Theorem OPT_MMAP_MEM_IMP : forall {A B} `{EqDecision A} `{EqDecision B} (f : A -> option B) xs ys y,
  OPT_MMAP f xs = SOME ys /\ is_true (MEM y ys) -> exists x, is_true (MEM x xs) /\ f x = SOME y.
Proof.
  intros A B HA HB f xs; induction xs as [|x xs IH]; intros ys y [H Hm].
  - injection H as <-; discriminate.
  - cbn in H. destruct (f x) as [z|] eqn:Ef; [|discriminate]; cbn in H.
    destruct (OPT_MMAP f xs) as [zs|] eqn:Eo; [|discriminate]; cbn in H. injection H as <-.
    unfold is_true in *; cbn in Hm |- *. apply Bool.orb_true_iff in Hm as [Hm|Hm].
    + apply bool_decide_spec in Hm; subst. exists x; split; [|exact Ef].
      apply Bool.orb_true_iff; left; apply bool_decide_spec; reflexivity.
    + destruct (IH zs y (conj eq_refl Hm)) as [x' [H1 H2]]; exists x'; split; [|exact H2].
      apply Bool.orb_true_iff; right; exact H1.
Qed.

Lemma OPT_MMAP_In {A B} (f : A -> option B) xs ys y :
  OPT_MMAP f xs = SOME ys -> In y ys -> exists x, In x xs /\ f x = SOME y.
Proof.
  revert ys; induction xs as [|x xs IH]; intros ys H Hy; cbn in H.
  - injection H as <-; destruct Hy.
  - destruct (f x) as [z|] eqn:Ef; [|discriminate]; cbn in H.
    destruct (OPT_MMAP f xs) as [zs|] eqn:Eo; [|discriminate]; cbn in H. injection H as <-.
    destruct Hy as [<-|Hy]; [exists x; split; [left; reflexivity|exact Ef]|].
    destruct (IH zs eq_refl Hy) as [x' [H1 H2]]; exists x'; split; [right; exact H1|exact H2].
Qed.

Lemma OPT_MMAP_LENGTH {A B} (f : A -> option B) xs ys :
  OPT_MMAP f xs = SOME ys -> length xs = length ys.
Proof.
  revert ys; induction xs as [|x xs IH]; intros ys H; cbn in H; [injection H as <-; reflexivity|].
  destruct (f x); [|discriminate]; cbn in H. destruct (OPT_MMAP f xs) as [zs|] eqn:Eo; [|discriminate].
  cbn in H; injection H as <-; cbn; f_equal; apply IH; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "eval_is_wf_shape_v" *)
Theorem eval_is_wf_shape_v : forall s (exp : exp a) v0,
  eval s exp = SOME v0 /\
  FEVERY (fun '(nm, v0) => is_true (is_wf_shape_v (structs s) v0)) (locals s) /\
  FEVERY (fun '(nm, v0) => is_true (is_wf_shape_v (structs s) v0)) (globals s) ->
  is_true (is_wf_shape_v (structs s) v0).
Proof.
  intros s e; induction e using exp_nested_ind; intros rv [Hev [Hl Hg]];
    cbn [eval] in Hev; split_in_H Hev; try discriminate.
  all: try (injection Hev as <-); try reflexivity.
  all: try (match type of Hev with OPTION_MAP _ ?X = _ =>
              destruct X; cbn in Hev; [injection Hev as <-; reflexivity|discriminate] end).
  all: try (match type of Hev with FLOOKUP _ _ = _ =>
              first [exact (Hl _ _ Hev) | exact (Hg _ _ Hev)] end).
  all: try (match type of Hev with mem_load _ _ _ _ _ = _ =>
              exact (proj1 mem_load_is_wf_shape_v _ _ _ _ _ _ Hev) end).
  all: try solve
    [ repeat match goal with
      | Hev : (if ?c then _ else _) = SOME _ |- _ => destruct c; [|discriminate]
      | Hev : OPTION_MAP _ ?X = SOME _ |- _ => destruct X; cbn in Hev; [|discriminate]
      | Hev : SOME _ = SOME _ |- _ => injection Hev as <-
      | Hev : match ?X with _ => _ end = SOME _ |- _ => destruct X; try discriminate
      end; reflexivity ].
  - (* RStruct *)
    apply is_wf_shape_v_RStruct, Forall_forall; intros y Hy.
    destruct (OPT_MMAP_In _ _ _ _ E Hy) as [x [Hx Hex]].
    rewrite Forall_forall in H; exact (H x Hx y (conj Hex (conj Hl Hg))).
  - (* RField *)
    match goal with Hv : ?v = RStruct _ |- _ => subst v end.
    specialize (IHe _ (conj E (conj Hl Hg))). apply is_wf_shape_v_RStruct in IHe.
    rewrite Forall_forall in IHe; apply IHe.
    match goal with Hb : (_ <? _) = true |- _ =>
      apply N.ltb_lt in Hb; rewrite EL_nth by exact Hb; apply nth_In;
      rewrite LENGTH_length in Hb; lia end.
  - (* NStruct *)
    match type of Hev with (if ?c then _ else _) = _ =>
      destruct c; [injection Hev as <-|discriminate] end.
    apply is_wf_shape_v_NStruct; split; [congruence|].
    apply Forall_forall; intros [fld y] Hy; cbn [snd].
    assert (Hy' : In y l1) by (clear - Hy; revert l1 Hy; induction (MAP FST es) as [|n ns IHn];
                                intros [|z zs] Hy; cbn in Hy; try tauto;
                                destruct Hy as [Hy|Hy]; [injection Hy as _ ->; left; reflexivity|
                                                        right; exact (IHn _ Hy)]).
    destruct (OPT_MMAP_In _ _ _ _ E2 Hy') as [x [Hx Hex]].
    rewrite Forall_forall in H; exact (H x Hx y (conj Hex (conj Hl Hg))).
  - (* NField *)
    match goal with Hv : ?v = NStruct _ _ |- _ => subst v end.
    specialize (IHe _ (conj E (conj Hl Hg))). apply is_wf_shape_v_NStruct in IHe as [_ IHe].
    rewrite Forall_forall in IHe; apply (IHe (f, rv)), ALOOKUP_In, Hev.
Qed.

End EvalWf.

(** ** Localised programs *)

Section Localised.
Context {a : N}.

(** HOL's [every_exp]; the [NStruct] clause maps over the pairs instead of
    over [MAP SND nm_es] (structural recursion), and HOL's equations are
    [every_exp_def] below. *)
Fixpoint every_exp (P : exp a -> bool) (e : exp a) : bool :=
  match e with
  | Const w => P (Const w)
  | Var vk v => P (Var vk v)
  | panLang.RStruct es => P (panLang.RStruct es) && EVERY (every_exp P) es
  | RField i e => P (RField i e) && every_exp P e
  | panLang.NStruct nm nm_es =>
      P (panLang.NStruct nm nm_es) && EVERY (fun p => every_exp P (SND p)) nm_es
  | NField i e => P (NField i e) && every_exp P e
  | Load sh e => P (Load sh e) && every_exp P e
  | Load32 e => P (Load32 e) && every_exp P e
  | LoadByte e => P (LoadByte e) && every_exp P e
  | Op bop es => P (Op bop es) && EVERY (every_exp P) es
  | Panop op es => P (Panop op es) && EVERY (every_exp P) es
  | Cmp c e1 e2 => P (Cmp c e1 e2) && every_exp P e1 && every_exp P e2
  | Shift sh e1 e2 => P (Shift sh e1 e2) && every_exp P e1 && every_exp P e2
  | BaseAddr => P BaseAddr
  | TopAddr => P TopAddr
  | BytesInWord => P BytesInWord
  end.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "every_exp_def" *)
Theorem every_exp_def : forall P,
  (forall w, every_exp P (Const w) = P (Const w)) /\
  (forall vk v, every_exp P (Var vk v) = P (Var vk v)) /\
  (forall es, every_exp P (panLang.RStruct es) = (P (panLang.RStruct es) && EVERY (every_exp P) es)) /\
  (forall i e, every_exp P (RField i e) = (P (RField i e) && every_exp P e)) /\
  (forall nm nm_es, every_exp P (panLang.NStruct nm nm_es) =
     (P (panLang.NStruct nm nm_es) && EVERY (every_exp P) (MAP SND nm_es))) /\
  (forall i e, every_exp P (NField i e) = (P (NField i e) && every_exp P e)) /\
  (forall sh e, every_exp P (Load sh e) = (P (Load sh e) && every_exp P e)) /\
  (forall e, every_exp P (Load32 e) = (P (Load32 e) && every_exp P e)) /\
  (forall e, every_exp P (LoadByte e) = (P (LoadByte e) && every_exp P e)) /\
  (forall bop es, every_exp P (Op bop es) = (P (Op bop es) && EVERY (every_exp P) es)) /\
  (forall op es, every_exp P (Panop op es) = (P (Panop op es) && EVERY (every_exp P) es)) /\
  (forall c e1 e2, every_exp P (Cmp c e1 e2) = (P (Cmp c e1 e2) && every_exp P e1 && every_exp P e2)) /\
  (forall sh e1 e2, every_exp P (Shift sh e1 e2) = (P (Shift sh e1 e2) && every_exp P e1 && every_exp P e2)) /\
  every_exp P BaseAddr = P BaseAddr /\
  every_exp P TopAddr = P TopAddr /\
  every_exp P BytesInWord = P BytesInWord.
Proof.
  intros P. repeat split; intros; try reflexivity.
  cbn [every_exp]. f_equal. induction nm_es as [|[n e] l IH]; [reflexivity|]. cbn. rewrite IH. reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "localised_exp_real_def" *)
Definition localised_exp : exp a -> bool :=
  every_exp (fun e => match e with Var tp _ => bool_decide (tp = Local) | _ => true end).

(** HOL's catch-all clause [localised_prog _ ⇔ T] covers the remaining
    constructors. *)
(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "localised_prog_def" *)
Fixpoint localised_prog (p : prog a) : bool :=
  match p with
  | Raise _ e => localised_exp e
  | Dec _ _ e p => localised_exp e && localised_prog p
  | Seq p q => localised_prog p && localised_prog q
  | If e p q => localised_exp e && localised_prog p && localised_prog q
  | While e p => localised_exp e && localised_prog p
  | Store e1 e2 => localised_exp e1 && localised_exp e2
  | Store32 e1 e2 => localised_exp e1 && localised_exp e2
  | StoreByte e1 e2 => localised_exp e1 && localised_exp e2
  | ExtCall fn e1 e2 e3 e4 =>
      localised_exp e1 && localised_exp e2 && localised_exp e3 && localised_exp e4
  | panLang.Return e => localised_exp e
  | ShMemStore op e1 e2 => localised_exp e1 && localised_exp e2
  | ShMemLoad op vk v e => bool_decide (vk = Local) && localised_exp e
  | Call hdl f args =>
      EVERY localised_exp args &&
      match hdl with
      | SOME (_, SOME (_, (_, p))) => localised_prog p
      | _ => true
      end &&
      match hdl with
      | SOME (SOME (Global, _), _) => false
      | _ => true
      end
  | DecCall vn sh fn args p => EVERY localised_exp args && localised_prog p
  | Assign Local _ e => localised_exp e
  | Assign Global _ _ => false
  | Primitive _ _ es => EVERY localised_exp es
  | _ => true
  end.

End Localised.

(** ** Well-formedness of values is invariant under [evaluate] *)

Section WfInvariant.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Local Definition wfl (sc : list (stcname * struct_info)) (m : fmap varname (v a)) : Prop :=
  FEVERY (fun '(nm, v0) => is_true (is_wf_shape_v sc v0)) m.

Local Lemma wfl_FEMPTY sc : wfl sc FEMPTY.
Proof. intros k v0 H; discriminate. Qed.

Local Lemma wfl_update sc m k (v0 : v a) :
  wfl sc m -> is_true (is_wf_shape_v sc v0) -> wfl sc (m |+ (k, v0)).
Proof.
  intros Hm Hv k' v' H. rewrite FLOOKUP_UPDATE in H.
  destruct (decide (k = k')); [injection H as <-; exact Hv|exact (Hm _ _ H)].
Qed.

Local Lemma wfl_flookup sc m k (v0 : v a) : wfl sc m -> FLOOKUP m k = SOME v0 -> is_true (is_wf_shape_v sc v0).
Proof. intros Hm H; exact (Hm _ _ H). Qed.

Local Lemma wfl_res_var sc m k (o : option (v a)) :
  wfl sc m -> (forall v0, o = SOME v0 -> is_true (is_wf_shape_v sc v0)) -> wfl sc (res_var m (k, o)).
Proof.
  intros Hm Ho k' v' H. destruct o as [v0|]; cbn [res_var] in H.
  - rewrite FLOOKUP_UPDATE in H. destruct (decide (k = k')); [injection H as <-; apply Ho; reflexivity|exact (Hm _ _ H)].
  - rewrite DOMSUB_FLOOKUP_THM in H. destruct (decide _); [discriminate|exact (Hm _ _ H)].
Qed.

Local Lemma wfl_lookup_code sc (cd : fmap funname (list (varname * shape) * (prog a * shape))) fname
    (args : list (v a)) p0 nl rsh :
  lookup_code cd fname args = SOME (p0, (nl, rsh)) ->
  Forall (fun v0 => is_true (is_wf_shape_v sc v0)) args -> wfl sc nl.
Proof.
  unfold lookup_code. destruct (FLOOKUP cd fname) as [[vshs [p rs]]|]; [|discriminate].
  destruct (_ && _); [|discriminate]. intros H Ha; injection H as _ <- _.
  intros k v0 Hk. rewrite FLOOKUP_FUPDATE_LIST in Hk.
  destruct (ALOOKUP (REVERSE _) k) eqn:E; [|discriminate]. injection Hk as <-.
  apply ALOOKUP_In in E. apply in_rev in E.
  revert E. generalize (MAP fst vshs) as ks. intros ks. revert ks.
  induction args as [|x xs IH]; intros [|k' ks] Hin; cbn in Hin; try contradiction.
  inversion Ha; subst. destruct Hin as [Hin|Hin]; [injection Hin as <- <-; assumption|].
  apply (IH ltac:(assumption) ks Hin).
Qed.

Local Lemma wf_args s (es : list (exp a)) args :
  OPT_MMAP (eval s) es = SOME args -> wfl (structs s) (locals s) -> wfl (structs s) (globals s) ->
  Forall (fun v0 => is_true (is_wf_shape_v (structs s) v0)) args.
Proof.
  intros H Hl Hg. apply Forall_forall. intros v0 Hv.
  destruct (OPT_MMAP_In _ _ _ _ H Hv) as (e & _ & He). apply (eval_is_wf_shape_v s e v0).
  split; [exact He|split; assumption].
Qed.

Local Definition wf_res sc (res : option (result a)) : Prop :=
  match res with
  | SOME (Exception eid exn) => is_true (is_wf_shape_v sc exn)
  | SOME (Return retv) => is_true (is_wf_shape_v sc retv)
  | _ => True
  end.

Local Lemma wf_inv_aux : forall x : prog a * state a ffi_t, forall res st,
  evaluate x = (res, st) -> wfl (structs (snd x)) (locals (snd x)) -> wfl (structs (snd x)) (globals (snd x)) ->
  wfl (structs (snd x)) (locals st) /\ wfl (structs (snd x)) (globals st) /\ wf_res (structs (snd x)) res.
Proof.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros res st H Hl Hg; cbn [fst snd] in *.
  assert (Hev : forall e v0, eval s e = SOME v0 -> is_true (is_wf_shape_v (structs s) v0))
    by (intros e v0 He; apply (eval_is_wf_shape_v s e v0); split; [exact He|split; assumption]).
  assert (Triv : forall r, (match r with SOME (Exception _ _) => False | SOME (Return _) => False | _ => True end) ->
            wf_res (structs s) r)
    by (intros [[]|]; cbn; tauto).
  rewrite evaluate_unfold in H.
  destruct p as [|vn sh e p|vk vn e|vn pop es|e1 e2|e1 e2|e1 e2|p1 p2|e p1 p2|e p| | |ct f args
                 |vn sh f args p|f e1 e2 e3 e4|eid e|e|op vk vn e|op e1 e2| |m1 m2];
    cbn [evaluate_body] in H; unfold sh_mem_load, sh_mem_store in H;
    rewrite ?fix_clock_evaluate in H.
  - (* Skip *) injection H as <- <-. split; [exact Hl|split; [exact Hg|exact Logic.I]].
  - (* Dec *)
    destruct (eval s e) as [value|] eqn:Ee; [|injection H as <- <-; repeat split; assumption].
    destruct (bool_decide _); [|injection H as <- <-; repeat split; assumption].
    destruct (evaluate (p, set_locals (locals s |+ (vn, value)) s)) as [r1 t1] eqn:E1.
    injection H as <- <-.
    destruct (IH (p, set_locals (locals s |+ (vn, value)) s) ltac:(prove_lt) r1 t1 E1) as (A1 & A2 & A3);
      cbn [fst snd] in *; state_cbn; [apply wfl_update; [exact Hl|exact (Hev _ _ Ee)]|exact Hg|].
    split; [|split; [exact A2|exact A3]].
    apply wfl_res_var; [exact A1|intros v' Hv'; exact (wfl_flookup _ _ _ _ Hl Hv')].
  - (* Assign *)
    destruct (eval s e) as [value|] eqn:Ee; [|injection H as <- <-; repeat split; assumption].
    destruct (is_valid_value _ _ _ _); [|injection H as <- <-; repeat split; assumption].
    injection H as <- <-. destruct vk; state_cbn; (split; [|split; [|exact Logic.I]]); try assumption;
      apply wfl_update; [exact Hl|exact (Hev _ _ Ee)|exact Hg|exact (Hev _ _ Ee)].
  - (* Primitive *)
    destruct (OPT_MMAP (eval s) es) as [vs|] eqn:Ee; [|injection H as <- <-; repeat split; assumption].
    destruct (pan_primop _ _) as [value|] eqn:Ep; [|injection H as <- <-; repeat split; assumption].
    destruct (is_valid_value _ _ _ _); [|injection H as <- <-; repeat split; assumption].
    injection H as <- <-. state_cbn. split; [|split; [exact Hg|exact Logic.I]].
    apply wfl_update; [exact Hl|exact (pan_primop_is_wf_shape_v _ _ _ _ Ep)].
  - (* Store *)
    split_all H; leaf_subst H; state_cbn; repeat split; assumption.
  - split_all H; leaf_subst H; state_cbn; repeat split; assumption.
  - split_all H; leaf_subst H; state_cbn; repeat split; assumption.
  - (* Seq *)
    destruct (evaluate (p1, s)) as [r1 s1] eqn:E1.
    destruct (IH (p1, s) ltac:(prove_lt) r1 s1 E1) as (A1 & A2 & A3); cbn [fst snd] in *; try assumption.
    pose proof (evaluate_invariants _ _ _ _ E1) as (_ & _ & _ & _ & _ & Hs1 & _).
    destruct r1 as [r1|]; [injection H as <- <-; split; [exact A1|split; assumption]|].
    destruct (IH (p2, s1) ltac:(prove_lt) res st H) as (B1 & B2 & B3); cbn [fst snd] in *; rewrite ?Hs1 in *;
      try assumption. split; [exact B1|split; [exact B2|exact B3]].
  - (* If *)
    destruct (eval s e) as [[[w]| |]|] eqn:Ee; try (injection H as <- <-; repeat split; assumption).
    destruct (negb _).
    + exact (IH (p1, s) ltac:(prove_lt) res st H Hl Hg).
    + exact (IH (p2, s) ltac:(prove_lt) res st H Hl Hg).
  - (* While *)
    destruct (eval s e) as [[[w]| |]|] eqn:Ee; try (injection H as <- <-; repeat split; assumption).
    destruct (negb _); [|injection H as <- <-; repeat split; assumption].
    destruct (clock s =? 0) eqn:Ec; [injection H as <- <-; state_cbn; repeat split; try assumption; apply wfl_FEMPTY|].
    destruct (evaluate (p, dec_clock s)) as [r1 s1] eqn:E1.
    destruct (IH (p, dec_clock s) ltac:(prove_lt) r1 s1 E1) as (A1 & A2 & A3); cbn [fst snd] in *; state_cbn;
      try assumption.
    pose proof (evaluate_invariants _ _ _ _ E1) as (_ & _ & _ & _ & _ & Hs1 & _). state_cbn.
    destruct r1 as [[| | | |rv|eid ev|ff]|];
      try (injection H as <- <-; split; [exact A1|split; [exact A2|exact A3]]).
    + destruct (IH (While e p, s1) ltac:(prove_lt) res st H) as (B1 & B2 & B3); cbn [fst snd] in *; rewrite ?Hs1 in *;
        try assumption. split; [exact B1|split; [exact B2|exact B3]].
    + destruct (IH (While e p, s1) ltac:(prove_lt) res st H) as (B1 & B2 & B3); cbn [fst snd] in *; rewrite ?Hs1 in *;
        try assumption. split; [exact B1|split; [exact B2|exact B3]].
  - injection H as <- <-; repeat split; assumption.
  - injection H as <- <-; repeat split; assumption.
  - (* Call *)
    destruct (OPT_MMAP (eval s) args) as [vals|] eqn:Ea; [|injection H as <- <-; repeat split; assumption].
    destruct (lookup_code (code s) f vals) as [[p0 [nl rsh]]|] eqn:El;
      [|injection H as <- <-; repeat split; assumption].
    destruct (clock s =? 0) eqn:Ec; [injection H as <- <-; state_cbn; repeat split; try assumption; apply wfl_FEMPTY|].
    rewrite fix_clock_evaluate in H.
    destruct (evaluate (p0, set_locals nl (dec_clock s))) as [r1 st1] eqn:E1.
    destruct (IH (p0, set_locals nl (dec_clock s)) ltac:(prove_lt) r1 st1 E1) as (A1 & A2 & A3);
      cbn [fst snd] in *; state_cbn; [exact (wfl_lookup_code _ _ _ _ _ _ _ El (wf_args _ _ _ Ea Hl Hg))|exact Hg|].
    pose proof (evaluate_invariants _ _ _ _ E1) as (_ & _ & _ & Hes & _ & Hs1 & _). state_cbn.
    destruct r1 as [[| | | |rv|eid ev|ff]|];
      try (injection H as <- <-; state_cbn; repeat split; try assumption; apply wfl_FEMPTY).
    + destruct (negb _); [injection H as <- <-; repeat split; assumption|].
      destruct ct as [[[[rk rt]|] hdl]|].
      * destruct (is_valid_value _ _ _ _); [|injection H as <- <-; repeat split; assumption].
        injection H as <- <-. destruct rk; state_cbn; (split; [|split; [|exact Logic.I]]); try assumption;
          apply wfl_update; assumption.
      * injection H as <- <-. state_cbn. split; [exact Hl|split; [exact A2|exact Logic.I]].
      * injection H as <- <-. state_cbn. split; [apply wfl_FEMPTY|split; [exact A2|exact A3]].
    + destruct ct as [[rv' [[eid' [evar hp]]|]]|];
        try (injection H as <- <-; state_cbn; split; [apply wfl_FEMPTY|split; [exact A2|exact A3]]).
      destruct (bool_decide _); [|injection H as <- <-; state_cbn; split; [apply wfl_FEMPTY|split; [exact A2|exact A3]]].
      destruct (FLOOKUP (eshapes s) eid); [|injection H as <- <-; repeat split; assumption].
      destruct (_ && _); [|injection H as <- <-; repeat split; assumption].
      destruct (IH (hp, set_var evar ev (set_locals (locals s) st1)) ltac:(prove_lt) res st H)
        as (B1 & B2 & B3); cbn [fst snd] in *; state_cbn; rewrite ?Hs1 in *; try (apply wfl_update; assumption);
        try assumption.
      split; [exact B1|split; [exact B2|exact B3]].
  - (* DecCall *)
    destruct (OPT_MMAP (eval s) args) as [vals|] eqn:Ea; [|injection H as <- <-; repeat split; assumption].
    destruct (lookup_code (code s) f vals) as [[p0 [nl rsh]]|] eqn:El;
      [|injection H as <- <-; repeat split; assumption].
    destruct (clock s =? 0) eqn:Ec; [injection H as <- <-; state_cbn; repeat split; try assumption; apply wfl_FEMPTY|].
    rewrite fix_clock_evaluate in H.
    destruct (evaluate (p0, set_locals nl (dec_clock s))) as [r1 st1] eqn:E1.
    destruct (IH (p0, set_locals nl (dec_clock s)) ltac:(prove_lt) r1 st1 E1) as (A1 & A2 & A3);
      cbn [fst snd] in *; state_cbn; [exact (wfl_lookup_code _ _ _ _ _ _ _ El (wf_args _ _ _ Ea Hl Hg))|exact Hg|].
    pose proof (evaluate_invariants _ _ _ _ E1) as (_ & _ & _ & _ & _ & Hs1 & _). state_cbn.
    destruct r1 as [[| | | |rv|eid ev|ff]|];
      try (injection H as <- <-; state_cbn; repeat split; try assumption; apply wfl_FEMPTY).
    destruct (_ && _); [|injection H as <- <-; repeat split; assumption].
    destruct (evaluate (p, set_var vn rv (set_locals (locals s) st1))) as [r2 st2] eqn:E2.
    injection H as <- <-.
    destruct (IH (p, set_var vn rv (set_locals (locals s) st1)) ltac:(prove_lt) r2 st2 E2)
      as (B1 & B2 & B3); cbn [fst snd] in *; state_cbn; rewrite ?Hs1 in *; try (apply wfl_update; assumption);
      try assumption.
    state_cbn. split; [|split; [exact B2|exact B3]].
    apply wfl_res_var; [exact B1|intros v' Hv'; exact (wfl_flookup _ _ _ _ Hl Hv')].
  - (* ExtCall *)
    split_all H; leaf_subst H; state_cbn; repeat split; try assumption; apply wfl_FEMPTY.
  - (* Raise *)
    destruct (FLOOKUP (eshapes s) eid) as [sh|]; [|injection H as <- <-; repeat split; assumption].
    destruct (eval s e) as [value|] eqn:Ee; [|injection H as <- <-; repeat split; assumption].
    destruct (_ && _); [|injection H as <- <-; repeat split; assumption].
    injection H as <- <-. state_cbn. split; [apply wfl_FEMPTY|split; [exact Hg|exact (Hev _ _ Ee)]].
  - (* Return *)
    destruct (eval s e) as [value|] eqn:Ee; [|injection H as <- <-; repeat split; assumption].
    destruct (_ <=? 32); [|injection H as <- <-; repeat split; assumption].
    injection H as <- <-. state_cbn. split; [apply wfl_FEMPTY|split; [exact Hg|exact (Hev _ _ Ee)]].
  - (* ShMemLoad *)
    split_all H; leaf_subst H; destruct_kvars_all; state_cbn; (split; [|split; [|exact Logic.I]]);
      try assumption; try apply wfl_FEMPTY; apply wfl_update; try assumption; reflexivity.
  - (* ShMemStore *)
    split_all H; leaf_subst H; state_cbn; repeat split; assumption.
  - (* Tick *)
    destruct (clock s =? 0); injection H as <- <-; state_cbn; repeat split; try assumption; apply wfl_FEMPTY.
  - injection H as <- <-; repeat split; assumption.
Qed.

(*! HOL "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_is_wf_shape_invariant" *)
Theorem evaluate_is_wf_shape_invariant : forall (p : prog a) s res s',
  evaluate (p, s) = (res, s') /\
  FEVERY (fun '(nm, v0) => is_true (is_wf_shape_v (structs s) v0)) (locals s) /\
  FEVERY (fun '(nm, v0) => is_true (is_wf_shape_v (structs s) v0)) (globals s) ->
  FEVERY (fun '(nm, v0) => is_true (is_wf_shape_v (structs s') v0)) (locals s') /\
  FEVERY (fun '(nm, v0) => is_true (is_wf_shape_v (structs s') v0)) (globals s') /\
  match res with
  | SOME (Exception eid exn) => is_true (is_wf_shape_v (structs s) exn)
  | SOME (Return retv) => is_true (is_wf_shape_v (structs s) retv)
  | _ => True
  end.
Proof.
  intros p s res s' (H & H1 & H2).
  pose proof (evaluate_invariants _ _ _ _ H) as (_ & _ & _ & _ & _ & Hs & _). rewrite Hs.
  exact (wf_inv_aux (p, s) res s' H H1 H2).
Qed.

End WfInvariant.
