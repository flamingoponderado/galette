(** * Pancake [crep_inlineProof]: correctness of function inlining

    Port of [cakeml/pancake/proofs/crep_inlineProofScript.sml]: the state,
    locals and code relations, the simulation lemmas for [evaluate] on
    extended locals, nested declarations and argument loading, the
    correctness of [unreach_elim], [transform_eoc] and [transform_branch],
    the main simulation [inline_prog_correct], the syntactic lemmas on
    [exps_of], and the observable-semantics theorems
    [state_rel_imp_semantics_local] and [state_rel_imp_semantics].

    Carrier notes as in [crepProps]: HOL's [s with locals := l] is
    [set_locals l s]; [SUBMAP] is [⊑]; [FDOM] is a predicate; HOL's
    [inl_fs \\ name] is [fdomsub inl_fs name] (notation [\\]).  Further
    representation choices:
    - HOL's boolean side conditions [(case r of ... => T | _ => F) = T]
      are written as the [Prop]-valued [match r with ... => True | _ => False
      end]; HOL's [¬has_return p], [not_branch_ret p] and [¬cont_res r] are
      the corresponding [bool]s coerced to [Prop].
    - In the post-conditions, HOL's catch-all case [res => r1 = res] binds
      the scrutinee; in [wrapped_transform_if] HOL's [res => F] is written
      [_ => False] and the bound name [ffi] of [SOME (FinalFFI ffi)] is [f]
      (the projection [ffi] is a constant here).
    - [MEM] on lists of functions ([exps_of_inst_inline],
      [every_inst_crep_inline]) needs decidable equality on [crepLang$prog];
      a classical instance ([cprog_eq_dec_classical], Galette-only, local to
      its section) provides it.
    - In [every_inst_crep_inline], HOL's predicate
      [λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2] (a HOL [bool]) is the
      [bool] [if classical_dec (...) then true else false], since
      [crepProps.every_exp] takes a [bool]-valued predicate.
    - HOL's tuples [(name, params, body)] are [(name, (params, body))].

    Not ported: [unreach_elim_prog_size] (about HOL's generated [prog_size],
    which has no Rocq counterpart); its uses are replaced by the Galette-only
    [unreach_elim_psize] on [crepSem.psize].

    Proof method: HOL's [recInduct evaluate_ind] is well-founded induction on
    [eval_lt], as in [crepProps]; HOL's tactic proofs are not followed
    step by step.
    - [evaluate_state_locals_rel_strong] is derived from the Galette-only
      lemma [evaluate_FUNION]: running a program on [s] with extra locals [X]
      ([FUNION (locals s) X]) gives the same result and, for the results that
      continue, the same final locals extended by [X].  The [nested_decs] /
      [arg_load] lemmas are derived from the explicit evaluation of
      [nested_decs] ([nested_decs_eval]) and the Galette-only
      [arg_load_master] by pointwise reasoning on [FLOOKUP].
    - [inline_prog_correct] is assembled ([inl_all]) from one Galette-only
      lemma per kind of program ([inl_simple], [inl_Dec], [inl_Seq], [inl_If],
      [inl_While], and for calls [inl_call_plain], [inl_call_tail],
      [inl_call_nontail]) about the induction predicate [inl_P].
    - [state_rel_imp_semantics_local] uses
      [crep_to_loopProof.crep_sem_is_wrapper]: by
      [evaluate_call_same_result_state] the two wrapped functions agree at
      every clock.
    - [inline_prog] is a well-founded [Fix]; proofs only rewrite with its
      equations ([inline_prog_def]) and avoid conversions that would make the
      kernel unfold it (e.g. [exps_of] is rewritten with equations rather than
      reduced by [cbn] around [inline_prog] terms). *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require asm.
From Galette.cakeml.pancake Require Import pan_common crepLang crep_inline.
From Galette.cakeml.pancake.semantics Require panSem.
From Galette.cakeml.pancake.semantics Require Import pan_commonProps crepSem crepProps.
From Galette.cakeml.pancake.proofs Require crep_to_loopProof.
Import panSem(word_lab(..)).
Open Scope N_scope.
Local Open Scope fmap_scope.

Section Rel.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "state_rel_def" *)
Definition state_rel s t : Prop :=
  globals s = globals t /\
  code s = code t /\
  memory s = memory t /\
  memaddrs s = memaddrs t /\
  sh_memaddrs s = sh_memaddrs t /\
  clock s = clock t /\
  be s = be t /\
  ffi s = ffi t /\
  base_addr s = base_addr t /\
  top_addr s = top_addr t.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "locals_rel_def" *)
Definition locals_rel s t : Prop := locals s ⊑ locals t.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "locals_strong_rel_def" *)
Definition locals_strong_rel s t : Prop := locals s = locals t.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "locals_ext_rel_def" *)
Definition locals_ext_rel (a0 b a' b' : state a ffi_t) : Prop :=
  FDIFF (locals a') (FDOM (locals a0)) = FDIFF (locals b') (FDOM (locals b)).

Lemma state_rel_set_locals s t l : state_rel s t -> set_locals l t = set_locals l s.
Proof.
  destruct s, t; intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10); cbn in *; subst; reflexivity.
Qed.

Lemma state_rel_refl s : state_rel s s.
Proof. repeat split. Qed.

Lemma state_rel_sym s t : state_rel s t -> state_rel t s.
Proof. unfold state_rel; intuition congruence. Qed.

Lemma state_rel_trans s t u : state_rel s t -> state_rel t u -> state_rel s u.
Proof. unfold state_rel; intuition congruence. Qed.

Lemma state_rel_eta s t : state_rel s t -> t = set_locals (locals t) s.
Proof.
  destruct s, t; intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10); cbn in *; subst; reflexivity.
Qed.

End Rel.

Section Basic.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "OPT_MMAP_SOME_ALL" *)
Theorem OPT_MMAP_SOME_ALL : forall {A B} `{EqDecision A} (f : A -> option B) l,
  ((exists x, OPT_MMAP f l = SOME x) <-> (forall x, MEM x l -> exists y, f x = SOME y)).
Proof.
  intros A B HA f l; induction l as [|h l IH]; cbn.
  - split; [intros _ x Hx; discriminate|intros _; eexists; reflexivity].
  - split.
    + intros [x Hx] y Hy. destruct (f h) as [z|] eqn:Ez; [|discriminate].
      destruct (OPT_MMAP f l) as [zs|] eqn:Ezs; [|discriminate].
      unfold is_true in Hy; apply Bool.orb_true_iff in Hy as [Hy|Hy].
      * apply bool_decide_spec in Hy; subst; eexists; exact Ez.
      * apply (proj1 IH); [eexists; reflexivity|exact Hy].
    + intros H. destruct (H h) as [z Hz].
      { unfold is_true; apply Bool.orb_true_iff; left; apply bool_decide_spec; reflexivity. }
      rewrite Hz. destruct (proj2 IH) as [zs Hzs].
      { intros x Hx; apply H; unfold is_true; apply Bool.orb_true_iff; right; exact Hx. }
      rewrite Hzs; eexists; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "OPT_MMAP_ALL_EQ" *)
Theorem OPT_MMAP_ALL_EQ : forall {A B} `{EqDecision A} (f g : A -> option B) l,
  (forall x, MEM x l -> f x = g x) -> (OPT_MMAP f l = OPT_MMAP g l).
Proof.
  intros A B HA f g l H; apply OPT_MMAP_ext_In'; intros x Hx; apply H, MEM_In, Hx.
Qed.

Lemma eval_submap_locals s (e : exp a) wl l :
  eval s e = SOME wl -> locals s ⊑ l -> eval (set_locals l s) e = SOME wl.
Proof.
  revert wl; induction e as [w|v0|e IH|e IH|e IH|g|op es IH|op es IH|c e1 e2 IH1 IH2|sh e1 e2 IH1 IH2| |]
    using cexp_nested_ind; intros wl H Hs; cbn [eval] in *; unfold mem_load in *;
    cbn [locals globals memory memaddrs be base_addr top_addr set_locals] in *; try exact H.
  - apply Hs, H.
  - destruct (eval s e) as [[w]|] eqn:E; [|discriminate]. rewrite (IH _ eq_refl Hs); exact H.
  - destruct (eval s e) as [[w]|] eqn:E; [|discriminate]. rewrite (IH _ eq_refl Hs); exact H.
  - destruct (eval s e) as [[w]|] eqn:E; [|discriminate]. rewrite (IH _ eq_refl Hs); exact H.
  - destruct (OPT_MMAP (eval s) es) as [ws|] eqn:E; [|discriminate].
    erewrite OPT_MMAP_ext_In'; [rewrite E; exact H|].
    intros x Hx. destruct (OPT_MMAP_In_SOME _ _ _ x E Hx) as [y Hy].
    rewrite Hy. exact (proj1 (Forall_forall _ _) IH x Hx y Hy Hs).
  - destruct (OPT_MMAP (eval s) es) as [ws|] eqn:E; [|discriminate].
    erewrite OPT_MMAP_ext_In'; [rewrite E; exact H|].
    intros x Hx. destruct (OPT_MMAP_In_SOME _ _ _ x E Hx) as [y Hy].
    rewrite Hy. exact (proj1 (Forall_forall _ _) IH x Hx y Hy Hs).
  - destruct (eval s e1) as [[w1]|] eqn:E1; [|discriminate].
    destruct (eval s e2) as [[w2]|] eqn:E2; [|discriminate].
    rewrite (IH1 _ eq_refl Hs), (IH2 _ eq_refl Hs); exact H.
  - destruct (eval s e1) as [[w1]|] eqn:E1; [|discriminate].
    destruct (eval s e2) as [[w2]|] eqn:E2; [|discriminate].
    rewrite (IH1 _ eq_refl Hs), (IH2 _ eq_refl Hs); exact H.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "eval_original_extend_locals" *)
Theorem eval_original_extend_locals : forall s (e : exp a) wl l,
  eval s e = SOME wl /\
  locals s ⊑ l ->
  eval (set_locals l s) e = SOME wl.
Proof. intros s e wl l [H1 H2]; apply eval_submap_locals; assumption. Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "eval_original_extend_locals_rel" *)
Theorem eval_original_extend_locals_rel : forall s (e : exp a) wl t,
  eval s e = SOME wl ->
  locals_rel s t /\ state_rel s t ->
  eval t e = SOME wl.
Proof.
  intros s e wl t H [Hl Hs]. rewrite (state_rel_eta s t Hs).
  apply eval_submap_locals; assumption.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "eval_state_locals_rel" *)
Theorem eval_state_locals_rel : forall s (e : exp a) wl t,
  eval s e = SOME wl /\ state_rel s t /\ locals_rel s t ->
  eval t e = SOME wl.
Proof. intros s e wl t (H1 & H2 & H3); eapply eval_original_extend_locals_rel; eauto. Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "eval_optmmap_state_locals_rel" *)
Theorem eval_optmmap_state_locals_rel : forall s (es : list (exp a)) ws t,
  OPT_MMAP (eval s) es = SOME ws /\ state_rel s t /\ locals_rel s t ->
  OPT_MMAP (eval t) es = SOME ws.
Proof.
  intros s es ws t (H & Hs & Hl). rewrite <- H. apply OPT_MMAP_ext_In'; intros x Hx.
  destruct (OPT_MMAP_In_SOME _ _ _ x H Hx) as [y Hy]. rewrite Hy.
  eapply eval_state_locals_rel; eauto.
Qed.

Context {K V : Type} `{HK : EqDecision K}.
Implicit Types f g : fmap K V.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "SUBMAP_IMP_FUPDATE_SUBMAP" *)
Theorem SUBMAP_IMP_FUPDATE_SUBMAP : forall f g x y,
  f ⊑ g -> f |+ (x, y) ⊑ g |+ (x, y).
Proof. intros f g x y H k v; fm_lookup; destruct (decide (x = k)); auto. Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "SUBMAP_IMP_DOMSUB_SUBMAP" *)
Theorem SUBMAP_IMP_DOMSUB_SUBMAP : forall f g x,
  f ⊑ g -> f \\ x ⊑ g \\ x.
Proof. intros f g x H k v; fm_lookup; destruct (decide (x = k)); auto. Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "SUBMAP_IMP_DOMSUB_FUPDATE" *)
Theorem SUBMAP_IMP_DOMSUB_FUPDATE : forall f g x y,
  f ⊑ g -> f \\ x ⊑ g |+ (x, y).
Proof. intros f g x y H k v; fm_lookup; destruct (decide (x = k)); [discriminate|auto]. Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "SUBMAP_IMP_FUPDATE_LIST_SUBMAP" *)
Theorem SUBMAP_IMP_FUPDATE_LIST_SUBMAP : forall (x : list K) (y : list V) f g,
  f ⊑ g /\ LENGTH x = LENGTH y -> f |++ ZIP (x, y) ⊑ g |++ ZIP (x, y).
Proof.
  intros x y f g [H _] k v.
  destruct (in_dec (fun u w => decide (u = w)) k (map fst (ZIP (x, y)))) as [Hi|Hn].
  - rewrite (FLOOKUP_FUPDATE_LIST_in _ f g k Hi); auto.
  - rewrite !FLOOKUP_FUPDATE_LIST_notin by exact Hn; apply H.
Qed.

End Basic.

Section Basic2.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.
Implicit Types f g : fmap varname (word_lab a).

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "res_var_submap_res_var" *)
Theorem res_var_submap_res_var : forall f g x y,
  f ⊑ g -> res_var f (x, y) ⊑ res_var g (x, y).
Proof.
  intros f g x [y|] H; cbn [res_var];
    [apply SUBMAP_IMP_FUPDATE_SUBMAP|apply SUBMAP_IMP_DOMSUB_SUBMAP]; exact H.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "locals_rel_dec_clock" *)
Theorem locals_rel_dec_clock : forall s t,
  locals_rel s t /\ state_rel s t ->
  locals_rel (dec_clock s) (dec_clock t) /\ state_rel (dec_clock s) (dec_clock t).
Proof.
  intros s t [Hl Hs]; split; [exact Hl|].
  unfold state_rel in *; cbn; intuition congruence.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "opt_mmap_some_then_subset_fdom" *)
Theorem opt_mmap_some_then_subset_fdom : forall vs f (vals : list (word_lab a)),
  OPT_MMAP (FLOOKUP f) vs = SOME vals -> set vs SUBSET FDOM f.
Proof.
  intros vs f vals H x Hx. apply IN_set in Hx.
  destruct (OPT_MMAP_In_SOME _ _ _ x H Hx) as [y Hy]. unfold_sets; unfold FDOM; congruence.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "eval_dec_clock_eq" *)
Theorem eval_dec_clock_eq : forall s (e : exp a), eval (dec_clock s) e = eval s e.
Proof. intros; rewrite eval_dec_clock; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "opt_mmap_eval_dec_clock_eq" *)
Theorem opt_mmap_eval_dec_clock_eq : forall s (es : list (exp a)),
  OPT_MMAP (eval (dec_clock s)) es = OPT_MMAP (eval s) es.
Proof. intros; rewrite eval_dec_clock; reflexivity. Qed.

End Basic2.

(** ** Domains of locals *)

Section Fdom.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.
Implicit Types f g : fmap varname (word_lab a).

Definition cres (r : option (result a)) : bool :=
  match r with
  | NONE => true
  | SOME (Continue n) => true
  | SOME (Break n) => true
  | _ => false
  end.

Lemma FLOOKUP_FUPDATE_LIST_in_some (l : list (varname * word_lab a)) f k :
  In k (map fst l) -> FLOOKUP (f |++ l) k <> None.
Proof.
  revert f; induction l as [|[x v] l IH]; intros f Hi; [destruct Hi|].
  change (FLOOKUP ((f |+ (x, v)) |++ l) k <> None).
  destruct (in_dec (fun u w => decide (u = w)) k (map fst l)) as [Hl|Hl]; [apply IH, Hl|].
  rewrite FLOOKUP_FUPDATE_LIST_notin by exact Hl. cbn in Hi.
  destruct Hi as [->|]; [|tauto]. fm_auto.
Qed.

Lemma fupd_list_dom f (l : list (varname * word_lab a)) k :
  (forall x, In x (map fst l) -> FLOOKUP f x <> None) ->
  (FLOOKUP (f |++ l) k = None <-> FLOOKUP f k = None).
Proof.
  intros H. destruct (in_dec (fun u w => decide (u = w)) k (map fst l)) as [Hi|Hn].
  - pose proof (FLOOKUP_FUPDATE_LIST_in_some _ f k Hi). pose proof (H k Hi). tauto.
  - rewrite FLOOKUP_FUPDATE_LIST_notin by exact Hn; tauto.
Qed.

Ltac zip_dom :=
  apply iff_sym, fupd_list_dom; intros x Hi; apply In_map_fst_ZIP in Hi;
  first [ match goal with E : OPT_MMAP (FLOOKUP _) _ = SOME _ |- _ =>
            destruct (OPT_MMAP_In_SOME _ _ _ x E Hi); congruence end
        | match goal with E : (_ && (EVERY _ _ && _))%bool = true |- _ =>
            apply Bool.andb_true_iff in E as [_ E]; apply Bool.andb_true_iff in E as [E _];
            apply EVERY_Forall in E; rewrite Forall_forall in E; specialize (E x Hi);
            cbn in E; destruct (FLOOKUP _ x); discriminate end ].

Lemma fupd_zip_dom f l (vs : list (word_lab a)) k :
  (forall x, In x l -> FLOOKUP f x <> None) ->
  (FLOOKUP (f |++ ZIP (l, vs)) k = None <-> FLOOKUP f k = None).
Proof.
  intros H. destruct (in_dec (fun u w => decide (u = w)) k (map fst (ZIP (l, vs)))) as [Hi|Hn].
  - pose proof (FLOOKUP_FUPDATE_LIST_in_some _ f k Hi).
    pose proof (H k (In_map_fst_ZIP _ _ _ Hi)). tauto.
  - rewrite FLOOKUP_FUPDATE_LIST_notin by exact Hn; tauto.
Qed.

Definition dom_eq f g : Prop := forall k, FLOOKUP f k = None <-> FLOOKUP g k = None.

Lemma dom_eq_FDOM f g : dom_eq f g -> FDOM f = FDOM g.
Proof.
  intros H; apply functional_extensionality; intros k; unfold FDOM.
  apply propositional_extensionality; specialize (H k); tauto.
Qed.

Ltac dom_ih IH :=
  repeat match goal with
  | E : evaluate (?p', ?s') = (?r, ?s0) |- _ =>
      let Hx := fresh "Hd" in
      assert (Hx : dom_eq (locals s') (locals s0))
        by (apply (IH (p', s') ltac:(lt_tac) r s0 E); first [reflexivity | assumption]);
      clear E
  end.

Lemma evaluate_dom_eq (p : prog a) s r t :
  evaluate (p, s) = (r, t) -> cres r = true -> dom_eq (locals s) (locals t).
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall r t,
            evaluate x = (r, t) -> cres r = true -> dom_eq (locals (snd x)) (locals t))
    by exact (G (p, s) r t).
  clear p s r t.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r t H Hc; cbn [snd].
  destruct p; unfold_eval_in H; repeat split_in H.
  all: first [ injection H as <- <-; try discriminate Hc | idtac ].
  all: try (unfold dom_eq; tauto).
  all: dom_ih IH; unfold dom_eq in *; intros k;
       repeat match goal with Hd : forall k, _ <-> _ |- _ => specialize (Hd k) end.
  all: state_cbn.
  all: try solve [ zip_dom ].
  all: try match goal with |- context [match FLOOKUP ?f ?n with _ => _ end] =>
         destruct (FLOOKUP f n) eqn:? end.
  all: try solve [ fm_lookup; repeat (destruct (decide _)); subst; intuition congruence ].
  all: match goal with H : sh_mem_op ?op _ _ _ = _ |- _ =>
         destruct op; cbn [sh_mem_op] in H; unfold sh_mem_load, sh_mem_store in H;
         repeat split_in H; injection H as <- <-; try discriminate Hc
       end.
  all: state_cbn; fm_lookup; repeat (destruct (decide _)); subst; intuition congruence.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_locals_same_fdom" *)
Theorem evaluate_locals_same_fdom : forall (p : prog a) s r s',
  evaluate (p, s) = (r, s') /\
  (match r with
   | NONE => true
   | SOME (Continue n) => true
   | SOME (Break n) => true
   | _ => false
   end) = true ->
  FDOM (locals s) = FDOM (locals s').
Proof. intros p s r s' [H Hc]; apply dom_eq_FDOM, (evaluate_dom_eq p s r s' H Hc). Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_locals_same_fdom'" *)
Theorem evaluate_locals_same_fdom' : forall (p : prog a) s r s',
  evaluate (p, s) = (r, s') /\
  (r = NONE \/ (exists n, r = SOME (Break n)) \/ (exists n, r = SOME (Continue n))) ->
  FDOM (locals s) = FDOM (locals s').
Proof.
  intros p s r s' [H Hr]; apply dom_eq_FDOM, (evaluate_dom_eq p s r s' H).
  destruct Hr as [->|[[n ->]|[n ->]]]; reflexivity.
Qed.

End Fdom.

(** ** Evaluation on extended locals (Galette-only simulation) *)

Section Ext.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.
Implicit Types f g X : fmap varname (word_lab a).

Definition ext_res X (r : option (result a)) (s' t' : state a ffi_t) : Prop :=
  state_rel s' t' /\ (cres r = true -> t' = set_locals (FUNION (locals s') X) s').

Lemma FUNION_FUPDATE_LIST f X (l : list (varname * word_lab a)) :
  FUNION (f |++ l) X = FUNION f X |++ l.
Proof.
  revert f; induction l as [|[k v] l IH]; intros f; [reflexivity|].
  change (FUNION ((f |+ (k, v)) |++ l) X = (FUNION f X |+ (k, v)) |++ l).
  rewrite IH, FUNION_FUPDATE_1; reflexivity.
Qed.

Lemma OPT_MMAP_FLOOKUP_FUNION f X l (ws : list (word_lab a)) :
  OPT_MMAP (FLOOKUP f) l = SOME ws -> OPT_MMAP (FLOOKUP (FUNION f X)) l = SOME ws.
Proof.
  intros H; rewrite <- H; apply OPT_MMAP_ext_In'; intros x Hx.
  destruct (OPT_MMAP_In_SOME _ _ _ x H Hx) as [y Hy]. rewrite FLOOKUP_FUNION, Hy; reflexivity.
Qed.

Lemma EVERY_IS_SOME_FUNION f X l :
  EVERY (fun v => IS_SOME (FLOOKUP f v)) l = true ->
  EVERY (fun v => IS_SOME (FLOOKUP (FUNION f X) v)) l = true.
Proof.
  induction l as [|x l IH]; cbn [EVERY]; [reflexivity|].
  rewrite FLOOKUP_FUNION; destruct (FLOOKUP f x); cbn [IS_SOME andb]; [exact IH|discriminate].
Qed.

Lemma eval_FUNION s X (e : exp a) v :
  eval s e = SOME v -> eval (set_locals (FUNION (locals s) X) s) e = SOME v.
Proof. intros H; apply eval_submap_locals; [exact H|apply (proj1 SUBMAP_FUNION_ID)]. Qed.

Lemma opt_mmap_eval_FUNION s X (es : list (exp a)) vs :
  OPT_MMAP (eval s) es = SOME vs -> OPT_MMAP (eval (set_locals (FUNION (locals s) X) s)) es = SOME vs.
Proof.
  intros H. eapply eval_optmmap_state_locals_rel; split; [exact H|split].
  - repeat split.
  - apply (proj1 SUBMAP_FUNION_ID).
Qed.

Lemma ext_res_set X r s' : ext_res X r s' (set_locals (FUNION (locals s') X) s').
Proof. split; [repeat split|reflexivity]. Qed.

Lemma ext_res_nc X r s' t' : cres r = false -> state_rel s' t' -> ext_res X r s' t'.
Proof. intros Hc Hs; split; [exact Hs|congruence]. Qed.

Lemma sh_mem_op_FUNION op v (addr : word a) s X r s' :
  sh_mem_op op v addr s = (r, s') -> r <> SOME Error ->
  exists t', sh_mem_op op v addr (set_locals (FUNION (locals s) X) s) = (r, t') /\ ext_res X r s' t'.
Proof.
  intros H Hne. destruct op; cbn [sh_mem_op] in *; unfold sh_mem_load, sh_mem_store in *;
    cbn [locals set_locals sh_memaddrs ffi] in *; rewrite ?FLOOKUP_FUNION;
    repeat split_in H; try (injection H as <- <-); try congruence;
    eexists; (split; [reflexivity|]);
    first [ apply ext_res_nc; [reflexivity|repeat split]
          | split; [repeat split|intros _; cbv [set_ffi set_var set_locals]; cbn [locals];
                    f_equal; apply fmap_ext; intros; fm_auto] ].
Qed.


(** Rewrite lemmas for state updates (Galette-only). *)
Lemma sl_locals l s : locals (set_locals l s) = l. Proof. reflexivity. Qed.
Lemma sl_clock l s : clock (set_locals l s) = clock s. Proof. reflexivity. Qed.
Lemma sl_code l s : code (set_locals l s) = code s. Proof. reflexivity. Qed.
Lemma sl_globals l s : globals (set_locals l s) = globals s. Proof. reflexivity. Qed.
Lemma sl_memory l s : memory (set_locals l s) = memory s. Proof. reflexivity. Qed.
Lemma sl_memaddrs l s : memaddrs (set_locals l s) = memaddrs s. Proof. reflexivity. Qed.
Lemma sl_sh_memaddrs l s : sh_memaddrs (set_locals l s) = sh_memaddrs s. Proof. reflexivity. Qed.
Lemma sl_be l s : be (set_locals l s) = be s. Proof. reflexivity. Qed.
Lemma sl_ffi l s : ffi (set_locals l s) = ffi s. Proof. reflexivity. Qed.
Lemma sl_base_addr l s : base_addr (set_locals l s) = base_addr s. Proof. reflexivity. Qed.
Lemma sl_top_addr l s : top_addr (set_locals l s) = top_addr s. Proof. reflexivity. Qed.
Lemma sl_sl l1 l2 s : set_locals l1 (set_locals l2 s) = set_locals l1 s. Proof. reflexivity. Qed.
Lemma sl_dec_clock l s : dec_clock (set_locals l s) = set_locals l (dec_clock s). Proof. reflexivity. Qed.
Lemma sl_empty_locals l s : empty_locals (set_locals l s) = empty_locals s. Proof. reflexivity. Qed.
Lemma sl_set_var v w l s : set_var v w (set_locals l s) = set_locals (l |+ (v, w)) s. Proof. reflexivity. Qed.
Lemma sl_set_ffi fs l s : set_ffi fs (set_locals l s) = set_locals l (set_ffi fs s). Proof. reflexivity. Qed.
Lemma sl_set_memory m l s : set_memory m (set_locals l s) = set_locals l (set_memory m s). Proof. reflexivity. Qed.
Lemma sl_set_globals gv w l s : set_globals gv w (set_locals l s) = set_locals l (set_globals gv w s). Proof. reflexivity. Qed.
Lemma sl_set_clock c l s : set_clock c (set_locals l s) = set_locals l (set_clock c s). Proof. reflexivity. Qed.
Lemma sl_locals_set_ffi fs s : locals (set_ffi fs s) = locals s. Proof. reflexivity. Qed.
Lemma sl_locals_set_memory m s : locals (set_memory m s) = locals s. Proof. reflexivity. Qed.
Lemma sl_locals_set_globals gv w s : locals (set_globals gv w s) = locals s. Proof. reflexivity. Qed.
Lemma sl_locals_dec_clock s : locals (dec_clock s) = locals s. Proof. reflexivity. Qed.
Lemma sl_locals_set_clock c s : locals (set_clock c s) = locals s. Proof. reflexivity. Qed.
Lemma sl_clock_dec_clock s : clock (dec_clock s) = clock s - 1. Proof. reflexivity. Qed.
Lemma sl_code_dec_clock s : code (dec_clock s) = code s. Proof. reflexivity. Qed.

End Ext.

Ltac sl_simp :=
  rewrite ?sl_locals, ?sl_clock, ?sl_code, ?sl_globals, ?sl_memory, ?sl_memaddrs, ?sl_sh_memaddrs,
    ?sl_be, ?sl_ffi, ?sl_base_addr, ?sl_top_addr, ?sl_sl, ?sl_dec_clock, ?sl_empty_locals,
    ?sl_set_var, ?sl_set_ffi, ?sl_set_memory, ?sl_set_globals, ?sl_set_clock, ?sl_locals_set_ffi,
    ?sl_locals_set_memory, ?sl_locals_set_globals, ?sl_locals_dec_clock, ?sl_locals_set_clock,
    ?sl_clock_dec_clock, ?sl_code_dec_clock.

Ltac sl_simp_in H :=
  rewrite ?sl_locals, ?sl_clock, ?sl_code, ?sl_globals, ?sl_memory, ?sl_memaddrs, ?sl_sh_memaddrs,
    ?sl_be, ?sl_ffi, ?sl_base_addr, ?sl_top_addr, ?sl_sl, ?sl_dec_clock, ?sl_empty_locals,
    ?sl_set_var, ?sl_set_ffi, ?sl_set_memory, ?sl_set_globals, ?sl_set_clock, ?sl_locals_set_ffi,
    ?sl_locals_set_memory, ?sl_locals_set_globals, ?sl_locals_dec_clock, ?sl_locals_set_clock,
    ?sl_clock_dec_clock, ?sl_code_dec_clock in H.

(** One step of [evaluate] in the goal. *)
Ltac ev_goal :=
  rewrite evaluate_unfold; cbn [evaluate_body]; rewrite ?fcl_evaluate; cbn beta.

(** Rewrite the goal with the equational hypotheses whose left-hand side
    is not a variable. *)
Ltac rw_hyps :=
  repeat match goal with
  | E : ?l = ?r |- context [?l] =>
      tryif constr_eq l r then fail else (tryif is_var l then fail else rewrite E)
  end; cbn beta iota zeta.

Section Ext2.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.
Implicit Types f g X : fmap varname (word_lab a).

Ltac ext_exps X :=
  repeat match goal with
  | E : eval ?s ?e = SOME ?v |- context [eval (set_locals (FUNION (locals ?s) X) ?s) ?e] =>
      rewrite (eval_FUNION s X e v E)
  | E : OPT_MMAP (eval ?s) ?es = SOME ?v |- context [OPT_MMAP (eval (set_locals (FUNION (locals ?s) X) ?s)) ?es] =>
      rewrite (opt_mmap_eval_FUNION s X es v E)
  | E : OPT_MMAP (FLOOKUP ?f) ?l = SOME ?v |- context [OPT_MMAP (FLOOKUP (FUNION ?f X)) ?l] =>
      rewrite (OPT_MMAP_FLOOKUP_FUNION f X l v E)
  | |- context [FLOOKUP (FUNION ?f X) ?k] => rewrite (FLOOKUP_FUNION f X k)
  | E : (?L && (EVERY ?P ?l && ?D))%bool = true |- _ =>
      let E1 := fresh "E" in let E2 := fresh "E" in let E3 := fresh "E" in let E4 := fresh "E" in
      apply Bool.andb_true_iff in E as [E1 E2]; apply Bool.andb_true_iff in E2 as [E3 E4];
      pose proof (EVERY_IS_SOME_FUNION _ X _ E3)
  end.

Lemma state_rel_set_locals2 s t l1 l2 : state_rel s t -> state_rel (set_locals l1 s) (set_locals l2 t).
Proof. unfold state_rel; cbn; tauto. Qed.

Ltac ext_fin :=
  eexists; split; [reflexivity|];
  split; [ sl_simp; first [ apply state_rel_refl | assumption | apply state_rel_set_locals2; assumption
                          | unfold state_rel; cbn; repeat split ]
         | let Hc := fresh "Hc" in intros Hc; try discriminate Hc;
           repeat match goal with H1 : cres ?r = true -> _ = _ |- _ => specialize (H1 Hc); subst end;
           sl_simp; rewrite ?FUNION_FUPDATE_LIST, ?FUNION_FUPDATE_1;
           first [reflexivity | f_equal; apply fmap_ext; intros; rewrite ?FLOOKUP_res_var;
                                repeat match goal with |- context [match FLOOKUP (locals ?s) ?k with _ => _ end] =>
                                  destruct (FLOOKUP (locals s) k) eqn:? end; fm_auto] ].

Ltac ext_ih IH' :=
  match goal with
  | E : evaluate (?q, ?Y) = (?r1, ?s1) |- context [evaluate (?q, ?Yg)] =>
      tryif constr_eq Y Yg then fail else
      let t1 := fresh "t" in let Ht := fresh "Ht" in let Hs := fresh "Hs" in let Hc := fresh "Hcont" in
      destruct (IH' q Y r1 s1 ltac:(lt_tac) E ltac:(first [discriminate | assumption | congruence]))
        as (t1 & Ht & Hs & Hc);
      sl_simp_in Ht; rewrite ?FUNION_FUPDATE_1, ?FUNION_FUPDATE_LIST in Ht;
      rewrite Ht; cbn beta iota zeta;
      try (specialize (Hc eq_refl); subst t1)
  end.

Lemma evaluate_FUNION (p : prog a) s r s' X :
  evaluate (p, s) = (r, s') -> r <> SOME Error ->
  exists t', evaluate (p, set_locals (FUNION (locals s) X) s) = (r, t') /\ ext_res X r s' t'.
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall r s' X,
     evaluate x = (r, s') -> r <> SOME Error ->
     exists t', evaluate (fst x, set_locals (FUNION (locals (snd x)) X) (snd x)) = (r, t') /\ ext_res X r s' t')
    by exact (G (p, s) r s' X).
  clear p s r s' X.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s' X H Hne; cbn [fst snd].
  assert (IH' : forall q Y r1 s1, eval_lt (q, Y) (p, s) -> evaluate (q, Y) = (r1, s1) -> r1 <> SOME Error ->
             exists t1, evaluate (q, set_locals (FUNION (locals Y) X) Y) = (r1, t1) /\ ext_res X r1 s1 t1)
    by (intros q Y r1 s1 Hlt E Hn; exact (IH (q, Y) Hlt r1 s1 X E Hn)).
  clear IH.
  destruct p; unfold_eval_in H; ev_goal; sl_simp; rewrite ?FLOOKUP_FUNION;
    repeat split_in H.
  all: try solve [injection H as H1 H2; subst; congruence].
  all: ext_exps X; rw_hyps; sl_simp; rw_hyps.
  all: try (injection H as <- <-).
  all: do 3 try (ext_ih IH'; rw_hyps).
  all: try match goal with
       | H : sh_mem_op ?op ?v ?ad ?s = (?r, ?s') |- context [sh_mem_op ?op ?v ?ad (set_locals (FUNION (locals ?s) ?X0) ?s)] =>
           let t1 := fresh "t" in let Ht := fresh "Ht" in let Hx := fresh "Hx" in
           destruct (sh_mem_op_FUNION op v ad s X0 r s' H Hne) as (t1 & Ht & Hx);
           rewrite Ht; exists t1; split; [reflexivity|exact Hx]
       end.
  all: ext_fin.
Qed.

End Ext2.
Lemma LENGTH_MAP_i {A B} (f : A -> B) l : LENGTH (MAP f l) = LENGTH l.
Proof. rewrite !LENGTH_length, length_map. reflexivity. Qed.

Lemma LENGTH_app_i {A} (x y : list A) : LENGTH (x ++ y) = LENGTH x + LENGTH y.
Proof. rewrite !LENGTH_length, length_app. lia. Qed.

Lemma LENGTH_GENLIST_i {A} (f : N -> A) n : LENGTH (GENLIST f n) = n.
Proof.
  induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (GENLIST_thm f n)), SNOC_app, LENGTH_app_i, IH. cbn. lia.
Qed.

Section LocalsRel.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma state_rel_sl_r s t l : state_rel s t -> state_rel s (set_locals l t).
Proof. unfold state_rel; cbn; tauto. Qed.
Lemma state_rel_sl_l s t l : state_rel s t -> state_rel (set_locals l s) t.
Proof. unfold state_rel; cbn; tauto. Qed.

(** Running a program on locals extended to a supermap (Galette-only
    corollary of [evaluate_FUNION]). *)
Lemma evaluate_submap_locals (p : prog a) L M Y r s' :
  evaluate (p, set_locals L Y) = (r, s') -> r <> SOME Error -> L ⊑ M ->
  exists t', evaluate (p, set_locals M Y) = (r, t') /\ state_rel s' t' /\
    (cres r = true -> locals t' = FUNION (locals s') M /\ dom_eq L (locals s')).
Proof.
  intros H Hne Hsub.
  destruct (evaluate_FUNION p (set_locals L Y) r s' M H Hne) as (t' & Ht & Hs & Hc).
  rewrite sl_locals, sl_sl, (proj1 (SUBMAP_FUNION_ABSORPTION L M) Hsub) in Ht.
  exists t'. split; [exact Ht|]. split; [exact Hs|].
  intros Hcr. split; [rewrite (Hc Hcr); reflexivity|].
  exact (evaluate_dom_eq p (set_locals L Y) r s' H Hcr).
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong" *)
Theorem evaluate_state_locals_rel_strong : forall (p : prog a) s r s' t,
  evaluate (p, s) = (r, s') /\
  r <> SOME Error /\
  locals_rel s t /\ state_rel s t ->
  exists t',
    evaluate (p, t) = (r, t') /\ state_rel s' t' /\
    match r with
    | NONE => locals_rel s' t' /\ locals_ext_rel s s' t t'
    | SOME (Break n) => locals_rel s' t' /\ locals_ext_rel s s' t t'
    | SOME (Continue n) => locals_rel s' t' /\ locals_ext_rel s s' t t'
    | SOME Error => False
    | _ => True
    end.
Proof.
  intros p s r s' t (H & Hne & Hl & Hs).
  rewrite <- (set_locals_id s) in H.
  destruct (evaluate_submap_locals p (locals s) (locals t) s r s' H Hne Hl) as (t' & Ht & Hs' & Hc).
  rewrite <- (state_rel_eta s t Hs) in Ht.
  exists t'. split; [exact Ht|]. split; [exact Hs'|].
  assert (Hcont : cres r = true -> locals_rel s' t' /\ locals_ext_rel s s' t t').
  { intros Hcr. destruct (Hc Hcr) as [Ht' Hd]. unfold locals_rel, locals_ext_rel. rewrite Ht'.
    split; [apply (proj1 SUBMAP_FUNION_ID)|].
    apply fmap_ext; intros k. rewrite !FLOOKUP_FDIFF, FLOOKUP_FUNION.
    specialize (Hd k). unfold locals_rel, SUBMAP in Hl. specialize (Hl k).
    unfold_sets; unfold FDOM.
    destruct (FLOOKUP (locals s) k) eqn:E1, (FLOOKUP (locals s') k) eqn:E2,
      (FLOOKUP (locals t) k) eqn:E3;
      repeat destruct (classical_dec _); try reflexivity; intuition congruence. }
  destruct r as [[]|]; cbn; try exact I; try (apply Hcont; reflexivity); congruence.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "opt_mmap_flookup_some_then_same_fdom" *)
Theorem opt_mmap_flookup_some_then_same_fdom : forall vs (fm : fmap varname (word_lab a)) vals
    (upd_vals : list (word_lab a)),
  OPT_MMAP (FLOOKUP fm) vs = SOME vals /\ LENGTH vs = LENGTH upd_vals ->
  FDOM (fm |++ ZIP (vs, upd_vals)) = FDOM fm.
Proof.
  intros vs fm vals upd [H _]. apply functional_extensionality; intros k.
  apply propositional_extensionality. rewrite FDOM_FUPDATE_LIST_iff. unfold_sets. split; [|tauto].
  intros [Hk|Hk]; [exact Hk|]. apply In_map_fst_ZIP in Hk.
  destruct (OPT_MMAP_In_SOME _ _ _ k H Hk) as [y Hy]. unfold FDOM. congruence.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel" *)
Theorem evaluate_state_locals_rel : forall (p : prog a) s r s' t,
  evaluate (p, s) = (r, s') ->
  r <> SOME Error ->
  locals_rel s t /\ state_rel s t ->
  exists t',
    evaluate (p, t) = (r, t') /\ state_rel s' t' /\
    match r with
    | NONE => locals_rel s' t'
    | SOME (Break n) => locals_rel s' t'
    | SOME (Continue n) => locals_rel s' t'
    | SOME Error => False
    | _ => True
    end.
Proof.
  intros p s r s' t H Hne [Hl Hs].
  destruct (evaluate_state_locals_rel_strong p s r s' t (conj H (conj Hne (conj Hl Hs))))
    as (t' & Ht & Hs' & Hc).
  exists t'. split; [exact Ht|]. split; [exact Hs'|].
  destruct r as [[]|]; tauto.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "single_dec_evaluate" *)
Theorem single_dec_evaluate : forall (p : prog a) s r s' v e val,
  eval s e = SOME val /\
  evaluate (p, set_locals (locals s |+ (v, val)) s) = (r, s') /\
  r <> SOME Error ->
  exists t', evaluate (Dec v e p, s) = (r, t') /\ state_rel s' t'.
Proof.
  intros p s r s' v e val (He & H & _).
  rewrite (proj1 (proj2 evaluate_def)), He, H.
  eexists; split; [reflexivity|]. apply state_rel_sl_r, state_rel_refl.
Qed.

End LocalsRel.

Section Generic.
Context {K V : Type} `{HK : EqDecision K}.
Implicit Types lc : fmap K V.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "res_var_commutes_strong" *)
Theorem res_var_commutes_strong : forall lc h lc' n,
  res_var (res_var lc (h, FLOOKUP lc' h)) (n, FLOOKUP lc' n) =
  res_var (res_var lc (n, FLOOKUP lc' n)) (h, FLOOKUP lc' h).
Proof.
  intros lc h lc' n. apply fmap_ext; intros k.
  destruct (FLOOKUP lc' h) eqn:E1, (FLOOKUP lc' n) eqn:E2; cbn [res_var]; fm_auto.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "res_var_foldl_commutes_strong" *)
Theorem res_var_foldl_commutes_strong : forall h (vs : list K) lc1 lc2,
  res_var (FOLDL res_var lc1 (ZIP (vs, MAP (FLOOKUP lc2) vs))) (h, FLOOKUP lc2 h) =
  FOLDL res_var (res_var lc1 (h, FLOOKUP lc2 h)) (ZIP (vs, MAP (FLOOKUP lc2) vs)).
Proof.
  intros h vs; induction vs as [|v vs IH]; intros lc1 lc2; [reflexivity|].
  cbn [MAP List.map]. change (ZIP (v :: vs, FLOOKUP lc2 v :: MAP (FLOOKUP lc2) vs))
    with ((v, FLOOKUP lc2 v) :: ZIP (vs, MAP (FLOOKUP lc2) vs)). cbn [FOLDL].
  rewrite IH, res_var_commutes_strong. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "not_some_is_none" *)
Theorem not_some_is_none : forall a0 : option V, (forall v, a0 <> SOME v) <-> a0 = NONE.
Proof.
  intros [v|]; split; intros H.
  - exfalso; exact (H v eq_refl).
  - discriminate.
  - reflexivity.
  - intros w; discriminate.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "fdom_eq_flookup_thm" *)
Theorem fdom_eq_flookup_thm : forall f1 f2 : fmap K V,
  FDOM f1 = FDOM f2 <->
  (forall x, (exists v, FLOOKUP f1 x = SOME v) -> (exists v, FLOOKUP f2 x = SOME v)) /\
  (forall x, FLOOKUP f1 x = NONE -> FLOOKUP f2 x = NONE).
Proof.
  intros f1 f2. split.
  - intros E. split.
    + intros x [v Hv]. assert (Hd : FDOM f1 x) by (unfold FDOM; congruence).
      rewrite E in Hd. unfold FDOM in Hd. destruct (FLOOKUP f2 x); [eexists; reflexivity|congruence].
    + intros x Hx. destruct (FLOOKUP f2 x) eqn:E2; [|reflexivity].
      assert (Hd : FDOM f2 x) by (unfold FDOM; congruence). rewrite <- E in Hd. contradiction.
  - intros [H1 H2]. apply functional_extensionality; intros x. apply propositional_extensionality.
    unfold FDOM. specialize (H1 x). specialize (H2 x).
    destruct (FLOOKUP f1 x), (FLOOKUP f2 x); try tauto.
    all: first [ split; intros _; discriminate
               | exfalso; destruct (H1 (ex_intro _ _ eq_refl)) as [w Hw]; discriminate ].
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "flookup_res_var_is_mem_zip_eq" *)
Theorem flookup_res_var_is_mem_zip_eq : forall (xs : list K) x lc1 lc2,
  MEM x xs ->
  FLOOKUP (FOLDL res_var lc1 (ZIP (xs, MAP (FLOOKUP lc2) xs))) x = FLOOKUP lc2 x.
Proof.
  induction xs as [|y xs IH]; intros x lc1 lc2 Hx; [discriminate|].
  cbn [MAP List.map]. change (ZIP (y :: xs, FLOOKUP lc2 y :: MAP (FLOOKUP lc2) xs))
    with ((y, FLOOKUP lc2 y) :: ZIP (xs, MAP (FLOOKUP lc2) xs)). cbn [FOLDL].
  rewrite <- res_var_foldl_commutes_strong.
  destruct (decide (x = y)) as [->|Hne].
  - destruct (FLOOKUP lc2 y) eqn:E; cbn [res_var]; fm_auto.
  - destruct (FLOOKUP lc2 y) eqn:E; cbn [res_var]; fm_lookup;
      (destruct (decide _); [congruence|]); apply IH;
      unfold is_true in *; rewrite MEM_In in *; destruct Hx; congruence.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "SUBMAP_DIFF_LIST" *)
Theorem SUBMAP_DIFF_LIST : forall (l : fmap K V) vs vals,
  LENGTH vs = LENGTH vals /\
  ALL_DISTINCT vs /\
  (forall v, MEM v vs -> v NOTIN FDOM l) ->
  l ⊑ l |++ ZIP (vs, vals).
Proof.
  intros l vs vals (_ & _ & H) k v Hk. rewrite FLOOKUP_FUPDATE_LIST_notin; [exact Hk|].
  intros Hi. apply In_map_fst_ZIP in Hi. apply (H k (proj2 (MEM_In _ _) Hi)). unfold_sets; unfold FDOM. congruence.
Qed.

End Generic.

Section Nested.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(** Evaluation of [nested_decs] (Galette-only). *)
Lemma nested_decs_eval : forall vs (es : list (exp a)) p s vals,
  OPT_MMAP (eval s) es = SOME vals -> LENGTH vs = LENGTH es -> ALL_DISTINCT vs ->
  (forall v, MEM v vs -> forall e, MEM e es -> ~ MEM v (var_cexp e)) ->
  evaluate (nested_decs vs es p, s) =
  let '(r, s') := evaluate (p, set_locals (locals s |++ ZIP (vs, vals)) s) in
  (r, set_locals (FOLDL res_var (locals s') (ZIP (vs, MAP (FLOOKUP (locals s)) vs))) s').
Proof.
  induction vs as [|v vs IH]; intros [|e es] p s vals Ho Hl Hd Hv; rewrite ?LENGTH_cons in Hl;
    cbn [LENGTH] in Hl; try lia.
  - cbn in Ho. injection Ho as <-. cbn [nested_decs]. change (locals s |++ ZIP ([], [])) with (locals s).
    rewrite set_locals_id. destruct (evaluate (p, s)) as [r s']. cbn. rewrite set_locals_id. reflexivity.
  - cbn [OPT_MMAP] in Ho. destruct (eval s e) as [w|] eqn:He; [|discriminate].
    destruct (OPT_MMAP (eval s) es) as [l|] eqn:Hes; [|discriminate]. injection Ho as <-.
    cbn [ALL_DISTINCT] in Hd. apply andb_prop in Hd as [Hnv Hd].
    cbn [nested_decs]. rewrite (proj1 (proj2 evaluate_def)), He. cbv beta iota.
    rewrite (IH es p (set_locals (locals s |+ (v, w)) s) l).
    + sl_simp. change (locals s |++ ZIP (v :: vs, w :: l)) with ((locals s |+ (v, w)) |++ ZIP (vs, l)).
      destruct (evaluate (p, set_locals ((locals s |+ (v, w)) |++ ZIP (vs, l)) s)) as [r s'].
      cbv beta iota. sl_simp. f_equal. f_equal.
      replace (MAP (FLOOKUP (locals s |+ (v, w))) vs) with (MAP (FLOOKUP (locals s)) vs).
      * rewrite res_var_foldl_commutes_strong. reflexivity.
      * apply map_ext_in. intros k Hk. rewrite FLOOKUP_UPDATE. destruct (decide (v = k)) as [->|]; [|reflexivity].
        exfalso. apply MEM_In in Hk. rewrite Hk in Hnv. discriminate.
    + rewrite <- Hes. apply OPT_MMAP_ext_In''. intros x Hx.
      apply update_locals_not_vars_eval_eq'; [exact w|].
      apply (Hv v); [apply MEM_In; left; reflexivity|apply MEM_In; right; exact Hx].
    + rewrite !LENGTH_length in *. cbn [length] in Hl. lia.
    + exact Hd.
    + intros v' Hv' e' He'. apply Hv; apply MEM_In; right; apply MEM_In; assumption.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "nested_decs_evaluate" *)
Theorem nested_decs_evaluate : forall vs (es : list (exp a)) p s r s' vals,
  OPT_MMAP (eval s) es = SOME vals /\
  LENGTH vs = LENGTH es /\
  ALL_DISTINCT vs /\
  (forall v, MEM v vs -> forall e, MEM e es -> ~ MEM v (var_cexp e)) /\
  evaluate (p, set_locals (locals s |++ ZIP (vs, vals)) s) = (r, s') /\
  r <> SOME Error ->
  exists t',
    evaluate (nested_decs vs es p, s) = (r, t') /\ state_rel s' t'.
Proof.
  intros vs es p s r s' vals (Ho & Hl & Hd & Hv & H & _).
  rewrite (nested_decs_eval vs es p s vals Ho Hl Hd Hv), H.
  eexists; split; [reflexivity|]. apply state_rel_sl_r, state_rel_refl.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "genlist_less_than" *)
Theorem genlist_less_than : forall n a0 v, MEM v (GENLIST (fun x => a0 + SUC x) n) -> a0 < v.
Proof. intros n a0 v H. apply MEM_In, In_GENLIST_iff in H as (i & _ & ->). lia. Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "genlist_not_in" *)
Theorem genlist_not_in : forall n a0 v, v <= a0 -> ~ MEM v (GENLIST (fun x => a0 + SUC x) n).
Proof. intros n a0 v Hv H. apply genlist_less_than in H. lia. Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "genlist_all_distinct" *)
Theorem genlist_all_distinct : forall n a0, ALL_DISTINCT (GENLIST (fun x => a0 + SUC x) n).
Proof. intros n a0. apply ALL_DISTINCT_GENLIST. intros m1 m2 (_ & _ & E). lia. Qed.

Lemma sh_mem_op_res op v (ad : word a) s r s' :
  sh_mem_op op v ad s = (r, s') -> r = NONE \/ r = SOME Error \/ exists f, r = SOME (FinalFFI f).
Proof.
  intros H. destruct op; cbn [sh_mem_op] in H; unfold sh_mem_load, sh_mem_store in H;
    repeat split_in H; injection H as <- _; eauto.
Qed.

(** [has_return] (Galette-only form of [not_has_return_not_evaluate_return]). *)
Lemma no_return_evaluate : forall (p : prog a) s r s',
  has_return p = false -> evaluate (p, s) = (r, s') -> forall retv, r <> SOME (Return retv).
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall r s',
            has_return (fst x) = false -> evaluate x = (r, s') -> forall retv, r <> SOME (Return retv))
    by (intros p s; exact (G (p, s))).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s' Hhr H retv; cbn [fst snd] in *.
  destruct p; unfold_eval_in H; cbn [has_return] in Hhr;
    repeat match type of Hhr with (_ || _)%bool = false => apply Bool.orb_false_iff in Hhr as [? Hhr] end;
    repeat split_in H.
  all: try (injection H as <- <-; discriminate).
  all: cbn beta iota in Hhr.
  all: try match goal with
       | E : evaluate (?q, ?Y) = (SOME (Return ?l), ?s1) |- _ =>
           exfalso; apply (IH (q, Y) ltac:(lt_tac) _ s1 ltac:(cbn [fst]; assumption) E l); reflexivity
       end.
  all: try (injection H as <- <-).
  all: try match goal with
       | E : evaluate (?q, ?Y) = (?r, ?s1) |- ?r <> _ =>
           apply (IH (q, Y) ltac:(lt_tac) _ s1 ltac:(cbn [fst]; assumption) E)
       end.
  all: try discriminate.
  all: match goal with E : sh_mem_op _ _ _ _ = _ |- _ =>
         destruct (sh_mem_op_res _ _ _ _ _ _ E) as [->|[->|[f ->]]]; discriminate end.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "not_has_return_not_evaluate_return" *)
Theorem not_has_return_not_evaluate_return : forall (p : prog a) s,
  ~ has_return p ->
  exists r s',
    evaluate (p, s) = (r, s') /\
    match r with
    | SOME (Return retv) => False
    | _ => True
    end.
Proof.
  intros p s Hh. destruct (evaluate (p, s)) as [r s'] eqn:E. exists r, s'. split; [reflexivity|].
  assert (Hf : has_return p = false) by (destruct (has_return p); [exfalso; apply Hh; reflexivity|reflexivity]).
  destruct r as [[]|]; try exact I. exact (no_return_evaluate p s _ s' Hf E l eq_refl).
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "not_has_return_not_evaluate_return'" *)
Theorem not_has_return_not_evaluate_return' : forall (p : prog a) s r s' retv,
  ~ has_return p /\
  evaluate (p, s) = (r, s') ->
  r <> SOME (Return retv).
Proof.
  intros p s r s' retv [Hh E].
  assert (Hf : has_return p = false) by (destruct (has_return p); [exfalso; apply Hh; reflexivity|reflexivity]).
  exact (no_return_evaluate p s r s' Hf E retv).
Qed.

End Nested.

Section Nested2.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_nested_decs_locals_nested_res_var" *)
Theorem evaluate_nested_decs_locals_nested_res_var : forall (p : prog a) s r s' vs es vals,
  OPT_MMAP (eval s) es = SOME vals /\
  LENGTH vs = LENGTH es /\
  ALL_DISTINCT vs /\
  (forall v, MEM v vs -> forall e, MEM e es -> ~ MEM v (var_cexp e)) /\
  evaluate (p, set_locals (locals s |++ ZIP (vs, vals)) s) = (r, s') ->
  exists t',
    evaluate (nested_decs vs es p, s) = (r, t') /\ state_rel s' t' /\
    locals t' = FOLDL res_var (locals s') (ZIP (vs, MAP (FLOOKUP (locals s)) vs)).
Proof.
  intros p s r s' vs es vals (Ho & Hl & Hd & Hv & H).
  rewrite (nested_decs_eval vs es p s vals Ho Hl Hd Hv), H.
  eexists; split; [reflexivity|]. split; [apply state_rel_sl_r, state_rel_refl|reflexivity].
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_nested_decs_locals_nested_res_var_drule" *)
Theorem evaluate_nested_decs_locals_nested_res_var_drule : forall (p : prog a) s r s' vs es vals r1 t',
  OPT_MMAP (eval s) es = SOME vals /\
  LENGTH vs = LENGTH es /\
  ALL_DISTINCT vs /\
  (forall v, MEM v vs -> forall e, MEM e es -> ~ MEM v (var_cexp e)) /\
  evaluate (p, set_locals (locals s |++ ZIP (vs, vals)) s) = (r, s') /\
  evaluate (nested_decs vs es p, s) = (r1, t') ->
  r1 = r /\ state_rel s' t' /\
  locals t' = FOLDL res_var (locals s') (ZIP (vs, MAP (FLOOKUP (locals s)) vs)).
Proof.
  intros p s r s' vs es vals r1 t' (Ho & Hl & Hd & Hv & H & H1).
  destruct (evaluate_nested_decs_locals_nested_res_var p s r s' vs es vals (conj Ho (conj Hl (conj Hd (conj Hv H)))))
    as (t'' & H2 & Hs & Hloc).
  rewrite H1 in H2. injection H2 as -> ->. tauto.
Qed.

Lemma afv_var_prog (p : prog a) x : MEM x (assigned_free_vars p) -> MEM x (var_prog p).
Proof.
  revert x; induction p using cprog_nested_ind; intros x Hx; cbn [assigned_free_vars var_prog] in *;
    unfold is_true in *; rewrite ?MEM_In in *; rewrite ?in_app_iff in *; cbn [In] in *; try tauto.
  - apply filter_In in Hx as [Hx _]. right; right. apply MEM_In, IHp, MEM_In, Hx.
  - destruct Hx as [Hx|Hx]; [left|right]; apply MEM_In; [apply IHp1|apply IHp2]; apply MEM_In, Hx.
  - destruct Hx as [Hx|Hx]; right; [left|right]; apply MEM_In; [apply IHp1|apply IHp2]; apply MEM_In, Hx.
  - right; apply MEM_In, IHp, MEM_In, Hx.
  - destruct o as [[rts [[w q]|]]|]; cbn in *; try tauto.
    rewrite in_app_iff in *. destruct Hx as [Hx|Hx]; [tauto|].
    right; right; apply MEM_In, (H rts w q eq_refl), MEM_In, Hx.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "not_var_prog_flookup_eqn" *)
Theorem not_var_prog_flookup_eqn : forall (p : prog a) s r s' x,
  evaluate (p, s) = (r, s') /\
  ~ MEM x (var_prog p) /\
  match r with
  | NONE => True
  | SOME (Break n) => True
  | SOME (Continue n) => True
  | _ => False
  end ->
  FLOOKUP (locals s') x = FLOOKUP (locals s) x.
Proof.
  intros p s r s' x (H & Hx & Hr).
  assert (Hr' : exists k, r = NONE \/ r = SOME (Continue k) \/ r = SOME (Break k))
    by (destruct r as [[| |n|n| | |]|]; try contradiction;
        [exists n; right; right; reflexivity|exists n; right; left; reflexivity|exists 0; left; reflexivity]).
  destruct Hr' as [k Hr'].
  apply (unassigned_free_vars_evaluate_same p s r s' x k). split; [exact H|]. split; [exact Hr'|].
  intros Hm. apply Hx, afv_var_prog, Hm.
Qed.

(** Pointwise lookups (Galette-only). *)
Definition zl (xs : list varname) (ys : list (word_lab a)) k := FLOOKUP (FEMPTY |++ ZIP (xs, ys)) k.

Lemma FLOOKUP_ZIP_split (f : fmap varname (word_lab a)) xs ys k :
  LENGTH xs = LENGTH ys ->
  FLOOKUP (f |++ ZIP (xs, ys)) k = if in_dec (fun x y => decide (x = y)) k xs then zl xs ys k else FLOOKUP f k.
Proof.
  intros Hl. unfold zl. destruct (in_dec _ k xs) as [Hi|Hn].
  - apply FLOOKUP_FUPDATE_LIST_in. rewrite In_ZIP_fst_iff by exact Hl. exact Hi.
  - apply FLOOKUP_FUPDATE_LIST_notin. rewrite In_ZIP_fst_iff by exact Hl. exact Hn.
Qed.

Lemma zl_some xs ys k : LENGTH xs = LENGTH ys -> In k xs -> zl xs ys k <> None.
Proof.
  intros Hl Hi. unfold zl. apply FLOOKUP_FUPDATE_LIST_in_some. rewrite In_ZIP_fst_iff by exact Hl. exact Hi.
Qed.

End Nested2.

Ltac lk :=
  repeat first
    [ rewrite FOLDL_res_var_map_lookup
    | rewrite FLOOKUP_FUNION
    | rewrite FLOOKUP_FDIFF
    | rewrite FLOOKUP_res_var
    | rewrite FLOOKUP_UPDATE
    | rewrite DOMSUB_FLOOKUP_THM
    | match goal with |- context [FLOOKUP (?f |++ ZIP (?xs, ?ys)) ?k] =>
        lazymatch f with FEMPTY => fail | _ =>
          rewrite (FLOOKUP_ZIP_split f xs ys k) by (rewrite ?LENGTH_MAP_i in *; lia) end end ].

Ltac lk_in H :=
  repeat first
    [ rewrite FOLDL_res_var_map_lookup in H
    | rewrite FLOOKUP_FUNION in H
    | rewrite FLOOKUP_FDIFF in H
    | rewrite FLOOKUP_res_var in H
    | rewrite FLOOKUP_UPDATE in H
    | rewrite DOMSUB_FLOOKUP_THM in H
    | match type of H with context [FLOOKUP (?f |++ ZIP (?xs, ?ys)) ?k] =>
        lazymatch f with FEMPTY => fail | _ =>
          rewrite (FLOOKUP_ZIP_split f xs ys k) in H by (lia) end end ].

Ltac lk_cases :=
  repeat match goal with
  | |- context [in_dec ?d ?k ?l] => destruct (in_dec d k l)
  | H : context [in_dec ?d ?k ?l] |- _ => destruct (in_dec d k l)
  | |- context [classical_dec ?P] => destruct (classical_dec P)
  | H : context [classical_dec ?P] |- _ => destruct (classical_dec P)
  | |- context [decide ?P] => destruct (decide P)
  | H : context [decide ?P] |- _ => destruct (decide P)
  | |- context [match FLOOKUP ?f ?k with _ => _ end] => destruct (FLOOKUP f k) eqn:?
  | H : context [match FLOOKUP ?f ?k with _ => _ end] |- _ => destruct (FLOOKUP f k) eqn:?
  end.

Section ArgLoad.
Context {a : N} {ffi_t : Type}.
Implicit Types s : state a ffi_t.

(** [nested_decs] around a program run on smaller locals (Galette-only). *)
Lemma nested_decs_sub vs (es : list (exp a)) p s vals L r s' :
  OPT_MMAP (eval s) es = SOME vals -> LENGTH vs = LENGTH es -> ALL_DISTINCT vs ->
  (forall v, MEM v vs -> forall e, MEM e es -> ~ MEM v (var_cexp e)) ->
  evaluate (p, set_locals L s) = (r, s') -> r <> SOME Error -> L ⊑ locals s |++ ZIP (vs, vals) ->
  exists t', evaluate (nested_decs vs es p, s) = (r, t') /\ state_rel s' t' /\
    (cres r = true ->
     locals t' = FOLDL res_var (FUNION (locals s') (locals s |++ ZIP (vs, vals)))
                   (ZIP (vs, MAP (FLOOKUP (locals s)) vs)) /\
     dom_eq L (locals s')).
Proof.
  intros Ho Hl Hd Hv H Hne Hsub.
  destruct (evaluate_submap_locals p L _ s r s' H Hne Hsub) as (t1 & Ht1 & Hs1 & Hc1).
  rewrite (nested_decs_eval vs es p s vals Ho Hl Hd Hv), Ht1.
  eexists; split; [reflexivity|]. split; [apply state_rel_sl_r, Hs1|].
  intros Hc. destruct (Hc1 Hc) as [E1 E2]. rewrite sl_locals, E1. split; [reflexivity|exact E2].
Qed.

Lemma cont_not_error (r : option (result a)) :
  match r with NONE => True | SOME (Break n) => True | SOME (Continue n) => True | _ => False end ->
  r <> SOME Error /\ cres r = true.
Proof. destruct r as [[]|]; cbn; intuition discriminate. Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "nested_decs_evaluate_sublocals_strong" *)
Theorem nested_decs_evaluate_sublocals_strong : forall vs (es : list (exp a)) p s r s' vals
    (t : fmap varname (word_lab a)),
  OPT_MMAP (eval s) es = SOME vals /\
  LENGTH vs = LENGTH es /\
  ALL_DISTINCT vs /\
  (forall v, MEM v vs -> forall e, MEM e es -> ~ MEM v (var_cexp e)) /\
  (forall v, MEM v vs -> v NOTIN FDOM t) /\
  evaluate (p, set_locals (t |++ ZIP (vs, vals)) s) = (r, s') /\
  t ⊑ locals s /\
  match r with
  | NONE => True
  | SOME (Break n) => True
  | SOME (Continue n) => True
  | _ => False
  end ->
  exists t',
    evaluate (nested_decs vs es p, s) = (r, t') /\ state_rel s' t' /\
    FDIFF (locals s) (FDOM t) ⊑ locals t'.
Proof.
  intros vs es p s r s' vals t (Ho & Hl & Hd & Hv & Ht & H & Hsub & Hr).
  destruct (cont_not_error r Hr) as [Hne Hc].
  pose proof (opt_mmap_length_eq _ _ _ Ho) as Hle.
  assert (Ht' : forall v, In v vs -> FLOOKUP t v = None).
  { intros v Hi. specialize (Ht v (proj2 (MEM_In _ _) Hi)). unfold_sets; unfold FDOM in Ht.
    destruct (FLOOKUP t v); [exfalso; apply Ht; discriminate|reflexivity]. }
  assert (Hsub' : t |++ ZIP (vs, vals) ⊑ locals s |++ ZIP (vs, vals)).
  { intros k w Hk. lk_in Hk. lk. lk_cases; first [solve [intuition congruence] | apply Hsub, Hk]. }
  destruct (nested_decs_sub vs es p s vals _ r s' Ho Hl Hd Hv H Hne Hsub') as (t' & E & Hs & Hc').
  exists t'. split; [exact E|]. split; [exact Hs|].
  destruct (Hc' Hc) as [Eloc Hdom]. rewrite Eloc. intros k w Hk. specialize (Hdom k). specialize (Ht' k).
  lk_in Hk. lk_in Hdom. lk. unfold_sets; unfold FDOM in *. lk_cases; intuition congruence.
Qed.

(** The two nested declarations of [arg_load] (Galette-only). *)
Lemma arg_load_master s (es : list (exp a)) vals vs (t : fmap varname (word_lab a)) p r s' tmp_vars :
  OPT_MMAP (eval s) es = SOME vals -> LENGTH vs = LENGTH vals -> ALL_DISTINCT vs -> t ⊑ locals s ->
  evaluate (p, set_locals (t |++ ZIP (vs, vals)) s) = (r, s') ->
  (forall v, MEM v vs \/ MEM v tmp_vars -> v NOTIN FDOM t) -> r <> SOME Error ->
  ALL_DISTINCT tmp_vars -> LENGTH tmp_vars = LENGTH vs -> (forall x, MEM x tmp_vars -> ~ MEM x vs) ->
  (forall x, MEM x tmp_vars -> ~ MEM x (FLAT (MAP var_cexp es))) ->
  exists t',
    evaluate (nested_decs tmp_vars es (nested_decs vs (MAP Var tmp_vars) p), s) = (r, t') /\
    state_rel s' t' /\
    (cres r = true ->
     (forall k, FLOOKUP (locals t') k =
        if in_dec (fun x y => decide (x = y)) k tmp_vars then FLOOKUP (locals s) k
        else if in_dec (fun x y => decide (x = y)) k vs then FLOOKUP (locals s) k
        else match FLOOKUP (locals s') k with SOME w => SOME w | NONE => FLOOKUP (locals s) k end) /\
     (forall k, FLOOKUP (locals s') k = NONE <-> FLOOKUP (t |++ ZIP (vs, vals)) k = NONE)).
Proof.
  intros Ho Hl Hd Hsub H Ht Hne Hdt Hlt Htv Hte.
  pose proof (opt_mmap_length_eq _ _ _ Ho) as Hle.
  assert (Hvc : forall v, MEM v tmp_vars -> forall e, MEM e es -> ~ MEM v (var_cexp e)).
  { intros v Hv e He Hm. apply (Hte v Hv). apply MEM_In. eapply In_FLAT_MAP; apply MEM_In; eassumption. }
  rewrite (nested_decs_eval tmp_vars es _ s vals Ho ltac:(lia) Hdt Hvc).
  set (S1 := set_locals (locals s |++ ZIP (tmp_vars, vals)) s).
  assert (Ho' : OPT_MMAP (eval S1) (MAP Var tmp_vars) = SOME vals).
  { rewrite <- lookup_locals_eq_map_vars. unfold S1; rewrite sl_locals.
    apply opt_mmap_some_eq_zip_flookup. split; [exact Hdt|lia]. }
  assert (Hv' : forall v, MEM v vs -> forall e, MEM e (MAP (@Var a) tmp_vars) -> ~ MEM v (var_cexp e)).
  { intros v Hv e He Hm. apply MEM_In, in_map_iff in He as (x & <- & Hx). cbn [var_cexp] in Hm.
    unfold is_true in Hm; rewrite MEM_In in Hm. destruct Hm as [<-|[]].
    apply (Htv x (proj2 (MEM_In _ _) Hx)), Hv. }
  assert (Ht1 : forall v, In v vs \/ In v tmp_vars -> FLOOKUP t v = None).
  { intros v Hi. assert (Hm : MEM v vs \/ MEM v tmp_vars) by (unfold is_true; rewrite !MEM_In; exact Hi).
    specialize (Ht v Hm). unfold_sets; unfold FDOM in Ht.
    destruct (FLOOKUP t v); [exfalso; apply Ht; discriminate|reflexivity]. }
  assert (Htv' : forall x, In x tmp_vars -> ~ In x vs).
  { intros x Hx Hy. apply (Htv x (proj2 (MEM_In _ _) Hx)), MEM_In, Hy. }
  assert (Hsub' : t |++ ZIP (vs, vals) ⊑ locals S1 |++ ZIP (vs, vals)).
  { intros k w Hk. unfold S1; rewrite sl_locals. specialize (Ht1 k). specialize (Htv' k).
    lk_in Hk. lk. lk_cases; first [solve [intuition congruence] | apply Hsub, Hk]. }
  destruct (nested_decs_sub vs (MAP Var tmp_vars) p S1 vals _ r s' Ho' ltac:(rewrite LENGTH_MAP_i; lia) Hd Hv' H Hne Hsub')
    as (t1 & E1 & Hs1 & Hc1).
  rewrite E1. cbv beta iota.
  eexists; split; [reflexivity|]. split; [apply state_rel_sl_r, Hs1|].
  intros Hc. destruct (Hc1 Hc) as [L1 D1]. rewrite sl_locals, L1. unfold S1; rewrite !sl_locals.
  split.
  - intros k. specialize (Ht1 k). specialize (Htv' k). specialize (D1 k). lk. lk_in D1.
    lk_cases; intuition congruence.
  - intros k. specialize (D1 k). tauto.
Qed.

End ArgLoad.

Section ArgLoad2.
Context {a : N} {ffi_t : Type}.
Implicit Types s : state a ffi_t.

Lemma arg_load_facts s (es : list (exp a)) vals vs (t : fmap varname (word_lab a)) p r s' tmp_vars :
  OPT_MMAP (eval s) es = SOME vals -> LENGTH vs = LENGTH vals -> ALL_DISTINCT vs -> t ⊑ locals s ->
  evaluate (p, set_locals (t |++ ZIP (vs, vals)) s) = (r, s') ->
  (forall v, MEM v vs \/ MEM v tmp_vars -> v NOTIN FDOM t) -> r <> SOME Error ->
  ALL_DISTINCT tmp_vars -> LENGTH tmp_vars = LENGTH vs -> (forall x, MEM x tmp_vars -> ~ MEM x vs) ->
  (forall x, MEM x tmp_vars -> ~ MEM x (FLAT (MAP var_cexp es))) ->
  exists t',
    evaluate (nested_decs tmp_vars es (nested_decs vs (MAP Var tmp_vars) p), s) = (r, t') /\
    state_rel s' t' /\
    (cres r = true ->
     FDIFF (locals s) (FDOM t) = FDIFF (locals t') (FDOM t) /\
     FOLDL res_var (locals s') (ZIP (vs, MAP (FLOOKUP (locals s)) vs)) ⊑ locals t').
Proof.
  intros Ho Hl Hd Hsub H Ht Hne Hdt Hlt Htv Hte.
  destruct (arg_load_master s es vals vs t p r s' tmp_vars Ho Hl Hd Hsub H Ht Hne Hdt Hlt Htv Hte)
    as (t' & E & Hs & Hc).
  exists t'. split; [exact E|]. split; [exact Hs|]. intros Hcr. destruct (Hc Hcr) as [Hlk Hdom].
  assert (Ht1 : forall v, In v vs \/ In v tmp_vars -> FLOOKUP t v = None).
  { intros v Hi. assert (Hm : MEM v vs \/ MEM v tmp_vars) by (unfold is_true; rewrite !MEM_In; exact Hi).
    specialize (Ht v Hm). unfold_sets; unfold FDOM in Ht.
    destruct (FLOOKUP t v); [exfalso; apply Ht; discriminate|reflexivity]. }
  assert (Htv' : forall x, In x tmp_vars -> ~ In x vs).
  { intros x Hx Hy. apply (Htv x (proj2 (MEM_In _ _) Hx)), MEM_In, Hy. }
  split.
  - apply fmap_ext; intros k. rewrite !FLOOKUP_FDIFF, Hlk. specialize (Hdom k). specialize (Ht1 k).
    specialize (Htv' k). lk_in Hdom. unfold_sets; unfold FDOM in *. lk_cases; intuition congruence.
  - intros k w Hk. rewrite Hlk. specialize (Hdom k). specialize (Ht1 k). specialize (Htv' k).
    lk_in Hk. lk_in Hdom. lk_cases; intuition congruence.
Qed.

Lemma FDIFF_eq_SUBMAP (f g : fmap varname (word_lab a)) P : FDIFF f P = FDIFF g P -> FDIFF f P ⊑ g.
Proof. intros E k v Hk. rewrite E in Hk. rewrite FLOOKUP_FDIFF in Hk. destruct (classical_dec _); congruence. Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "general_simulate_arg_load_correct" *)
Theorem general_simulate_arg_load_correct : forall s (es : list (exp a)) (vals : list (word_lab a)) vs
    (t : fmap varname (word_lab a)) p r s' tmp_vars,
  OPT_MMAP (eval s) es = SOME vals /\
  LENGTH vs = LENGTH vals /\
  ALL_DISTINCT vs /\
  t ⊑ locals s /\
  evaluate (p, set_locals (t |++ ZIP (vs, vals)) s) = (r, s') /\
  (forall v, MEM v vs \/ MEM v tmp_vars -> v NOTIN FDOM t) /\
  r <> SOME Error /\
  ALL_DISTINCT tmp_vars /\ LENGTH tmp_vars = LENGTH vs /\
  (forall x, MEM x tmp_vars -> ~ MEM x vs) /\
  (forall x, MEM x tmp_vars -> ~ MEM x (FLAT (MAP var_cexp es))) ->
  exists t',
    evaluate (nested_decs tmp_vars es (nested_decs vs (MAP Var tmp_vars) p), s) = (r, t') /\
    state_rel s' t'.
Proof.
  intros s es vals vs t p r s' tmp_vars (Ho & Hl & Hd & Hsub & H & Ht & Hne & Hdt & Hlt & Htv & Hte).
  destruct (arg_load_master s es vals vs t p r s' tmp_vars Ho Hl Hd Hsub H Ht Hne Hdt Hlt Htv Hte)
    as (t' & E & Hs & _). eauto.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "general_simulate_arg_load_preserve_locals" *)
Theorem general_simulate_arg_load_preserve_locals : forall s (es : list (exp a)) (vals : list (word_lab a)) vs
    (t : fmap varname (word_lab a)) p r s' tmp_vars,
  OPT_MMAP (eval s) es = SOME vals /\
  LENGTH vs = LENGTH vals /\
  ALL_DISTINCT vs /\
  t ⊑ locals s /\
  evaluate (p, set_locals (t |++ ZIP (vs, vals)) s) = (r, s') /\
  (forall v, MEM v vs \/ MEM v tmp_vars -> v NOTIN FDOM t) /\
  match r with
  | NONE => True
  | SOME (Break n) => True
  | SOME (Continue n) => True
  | _ => False
  end /\
  ALL_DISTINCT tmp_vars /\ LENGTH tmp_vars = LENGTH vs /\
  (forall x, MEM x tmp_vars -> ~ MEM x vs) /\
  (forall x, MEM x tmp_vars -> ~ MEM x (FLAT (MAP var_cexp es))) ->
  exists t',
    evaluate (nested_decs tmp_vars es (nested_decs vs (MAP Var tmp_vars) p), s) = (r, t') /\
    state_rel s' t' /\
    FOLDL res_var (locals s') (ZIP (vs, MAP (FLOOKUP (locals s)) vs)) ⊑ locals t'.
Proof.
  intros s es vals vs t p r s' tmp_vars (Ho & Hl & Hd & Hsub & H & Ht & Hr & Hdt & Hlt & Htv & Hte).
  destruct (cont_not_error r Hr) as [Hne Hc].
  destruct (arg_load_facts s es vals vs t p r s' tmp_vars Ho Hl Hd Hsub H Ht Hne Hdt Hlt Htv Hte)
    as (t' & E & Hs & Hf). exists t'. split; [exact E|]. split; [exact Hs|]. apply (Hf Hc).
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "general_simulate_arg_load_strong" *)
Theorem general_simulate_arg_load_strong : forall s (es : list (exp a)) (vals : list (word_lab a)) vs
    (t : fmap varname (word_lab a)) p r s' tmp_vars,
  OPT_MMAP (eval s) es = SOME vals /\
  LENGTH vs = LENGTH vals /\
  ALL_DISTINCT vs /\
  t ⊑ locals s /\
  evaluate (p, set_locals (t |++ ZIP (vs, vals)) s) = (r, s') /\
  (forall v, MEM v vs \/ MEM v tmp_vars -> v NOTIN FDOM t) /\
  match r with
  | NONE => True
  | SOME (Break n) => True
  | SOME (Continue n) => True
  | _ => False
  end /\
  ALL_DISTINCT tmp_vars /\ LENGTH tmp_vars = LENGTH vs /\
  (forall x, MEM x tmp_vars -> ~ MEM x vs) /\
  (forall x, MEM x tmp_vars -> ~ MEM x (FLAT (MAP var_cexp es))) ->
  exists t',
    evaluate (nested_decs tmp_vars es (nested_decs vs (MAP Var tmp_vars) p), s) = (r, t') /\
    state_rel s' t' /\
    FDIFF (locals s) (FDOM t) ⊑ locals t'.
Proof.
  intros s es vals vs t p r s' tmp_vars (Ho & Hl & Hd & Hsub & H & Ht & Hr & Hdt & Hlt & Htv & Hte).
  destruct (cont_not_error r Hr) as [Hne Hc].
  destruct (arg_load_facts s es vals vs t p r s' tmp_vars Ho Hl Hd Hsub H Ht Hne Hdt Hlt Htv Hte)
    as (t' & E & Hs & Hf). exists t'. split; [exact E|]. split; [exact Hs|].
  apply FDIFF_eq_SUBMAP, (Hf Hc).
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "general_simulate_arg_load_strong_1" *)
Theorem general_simulate_arg_load_strong_1 : forall s (es : list (exp a)) (vals : list (word_lab a)) vs
    (t : fmap varname (word_lab a)) p r s' tmp_vars,
  OPT_MMAP (eval s) es = SOME vals /\
  LENGTH vs = LENGTH vals /\
  ALL_DISTINCT vs /\
  t ⊑ locals s /\
  evaluate (p, set_locals (t |++ ZIP (vs, vals)) s) = (r, s') /\
  (forall v, MEM v vs \/ MEM v tmp_vars -> v NOTIN FDOM t) /\
  match r with
  | NONE => True
  | SOME (Break n) => True
  | SOME (Continue n) => True
  | _ => False
  end /\
  ALL_DISTINCT tmp_vars /\ LENGTH tmp_vars = LENGTH vs /\
  (forall x, MEM x tmp_vars -> ~ MEM x vs) /\
  (forall x, MEM x tmp_vars -> ~ MEM x (FLAT (MAP var_cexp es))) ->
  exists t',
    evaluate (nested_decs tmp_vars es (nested_decs vs (MAP Var tmp_vars) p), s) = (r, t') /\
    state_rel s' t' /\
    FDIFF (locals s) (FDOM t) ⊑ locals t' /\
    FOLDL res_var (locals s') (ZIP (vs, MAP (FLOOKUP (locals s)) vs)) ⊑ locals t'.
Proof.
  intros s es vals vs t p r s' tmp_vars (Ho & Hl & Hd & Hsub & H & Ht & Hr & Hdt & Hlt & Htv & Hte).
  destruct (cont_not_error r Hr) as [Hne Hc].
  destruct (arg_load_facts s es vals vs t p r s' tmp_vars Ho Hl Hd Hsub H Ht Hne Hdt Hlt Htv Hte)
    as (t' & E & Hs & Hf). exists t'. split; [exact E|]. split; [exact Hs|].
  destruct (Hf Hc) as [E1 E2]. split; [apply FDIFF_eq_SUBMAP, E1|exact E2].
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "general_simulate_arg_load_strong_all" *)
Theorem general_simulate_arg_load_strong_all : forall s (es : list (exp a)) (vals : list (word_lab a)) vs
    (t : fmap varname (word_lab a)) p r s' tmp_vars,
  OPT_MMAP (eval s) es = SOME vals /\
  LENGTH vs = LENGTH vals /\
  ALL_DISTINCT vs /\
  t ⊑ locals s /\
  evaluate (p, set_locals (t |++ ZIP (vs, vals)) s) = (r, s') /\
  (forall v, MEM v vs \/ MEM v tmp_vars -> v NOTIN FDOM t) /\
  r <> SOME Error /\
  ALL_DISTINCT tmp_vars /\ LENGTH tmp_vars = LENGTH vs /\
  (forall x, MEM x tmp_vars -> ~ MEM x vs) /\
  (forall x, MEM x tmp_vars -> ~ MEM x (FLAT (MAP var_cexp es))) ->
  exists t',
    evaluate (nested_decs tmp_vars es (nested_decs vs (MAP Var tmp_vars) p), s) = (r, t') /\
    state_rel s' t' /\
    match r with
    | NONE => FDIFF (locals s) (FDOM t) ⊑ locals t' /\
              FOLDL res_var (locals s') (ZIP (vs, MAP (FLOOKUP (locals s)) vs)) ⊑ locals t'
    | SOME (Break n) => FDIFF (locals s) (FDOM t) ⊑ locals t' /\
              FOLDL res_var (locals s') (ZIP (vs, MAP (FLOOKUP (locals s)) vs)) ⊑ locals t'
    | SOME (Continue n) => FDIFF (locals s) (FDOM t) ⊑ locals t' /\
              FOLDL res_var (locals s') (ZIP (vs, MAP (FLOOKUP (locals s)) vs)) ⊑ locals t'
    | SOME Error => False
    | _ => True
    end.
Proof.
  intros s es vals vs t p r s' tmp_vars (Ho & Hl & Hd & Hsub & H & Ht & Hne & Hdt & Hlt & Htv & Hte).
  destruct (arg_load_facts s es vals vs t p r s' tmp_vars Ho Hl Hd Hsub H Ht Hne Hdt Hlt Htv Hte)
    as (t' & E & Hs & Hf). exists t'. split; [exact E|]. split; [exact Hs|].
  destruct r as [[]|]; try exact I; try (exfalso; apply Hne; reflexivity);
    (destruct (Hf eq_refl) as [E1 E2]; split; [apply FDIFF_eq_SUBMAP, E1|exact E2]).
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "general_simulate_arg_load_strong_all_drule" *)
Theorem general_simulate_arg_load_strong_all_drule : forall s (es : list (exp a)) (vals : list (word_lab a)) vs
    (t : fmap varname (word_lab a)) p r s' tmp_vars r1 t',
  OPT_MMAP (eval s) es = SOME vals /\
  LENGTH vs = LENGTH vals /\
  ALL_DISTINCT vs /\
  t ⊑ locals s /\
  evaluate (p, set_locals (t |++ ZIP (vs, vals)) s) = (r, s') /\
  (forall v, MEM v vs \/ MEM v tmp_vars -> v NOTIN FDOM t) /\
  r <> SOME Error /\
  ALL_DISTINCT tmp_vars /\ LENGTH tmp_vars = LENGTH vs /\
  (forall x, MEM x tmp_vars -> ~ MEM x vs) /\
  (forall x, MEM x tmp_vars -> ~ MEM x (FLAT (MAP var_cexp es))) /\
  evaluate (nested_decs tmp_vars es (nested_decs vs (MAP Var tmp_vars) p), s) = (r1, t') ->
  r1 = r /\
  state_rel s' t' /\
  match r with
  | NONE => FDIFF (locals s) (FDOM t) ⊑ locals t' /\
            FOLDL res_var (locals s') (ZIP (vs, MAP (FLOOKUP (locals s)) vs)) ⊑ locals t'
  | SOME (Break n) => FDIFF (locals s) (FDOM t) ⊑ locals t' /\
            FOLDL res_var (locals s') (ZIP (vs, MAP (FLOOKUP (locals s)) vs)) ⊑ locals t'
  | SOME (Continue n) => FDIFF (locals s) (FDOM t) ⊑ locals t' /\
            FOLDL res_var (locals s') (ZIP (vs, MAP (FLOOKUP (locals s)) vs)) ⊑ locals t'
  | SOME Error => False
  | _ => True
  end.
Proof.
  intros s es vals vs t p r s' tmp_vars r1 t' (Ho & Hl & Hd & Hsub & H & Ht & Hne & Hdt & Hlt & Htv & Hte & H1).
  destruct (general_simulate_arg_load_strong_all s es vals vs t p r s' tmp_vars
              ltac:(repeat split; assumption)) as (t'' & E & Hs & Hc).
  rewrite H1 in E. injection E as -> ->. tauto.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "arg_load_correct" *)
Theorem arg_load_correct : forall s (es : list (exp a)) (vals : list (word_lab a)) vs
    (t : fmap varname (word_lab a)) p r s' tmp_vars,
  OPT_MMAP (eval s) es = SOME vals /\
  LENGTH vs = LENGTH vals /\
  ALL_DISTINCT vs /\
  t ⊑ locals s /\
  evaluate (p, set_locals (t |++ ZIP (vs, vals)) s) = (r, s') /\
  (forall v, MEM v vs \/ MEM v tmp_vars -> v NOTIN FDOM t) /\
  r <> SOME Error /\
  ALL_DISTINCT tmp_vars /\ LENGTH tmp_vars = LENGTH vs /\
  (forall x, MEM x tmp_vars -> ~ MEM x vs) /\
  (forall x, MEM x tmp_vars -> ~ MEM x (FLAT (MAP var_cexp es))) ->
  exists t',
    evaluate (arg_load tmp_vars es vs p, s) = (r, t') /\
    state_rel s' t' /\
    match r with
    | NONE => FDIFF (locals s) (FDOM t) ⊑ locals t' /\
              FOLDL res_var (locals s') (ZIP (vs, MAP (FLOOKUP (locals s)) vs)) ⊑ locals t'
    | SOME (Break n) => FDIFF (locals s) (FDOM t) ⊑ locals t' /\
              FOLDL res_var (locals s') (ZIP (vs, MAP (FLOOKUP (locals s)) vs)) ⊑ locals t'
    | SOME (Continue n) => FDIFF (locals s) (FDOM t) ⊑ locals t' /\
              FOLDL res_var (locals s') (ZIP (vs, MAP (FLOOKUP (locals s)) vs)) ⊑ locals t'
    | SOME Error => False
    | _ => True
    end.
Proof.
  intros s es vals vs t p r s' tmp_vars Hyp. unfold arg_load.
  exact (general_simulate_arg_load_strong_all s es vals vs t p r s' tmp_vars Hyp).
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "arg_load_stronger" *)
Theorem arg_load_stronger : forall s (es : list (exp a)) (vals : list (word_lab a)) vs
    (t : fmap varname (word_lab a)) p r s' tmp_vars,
  OPT_MMAP (eval s) es = SOME vals /\
  LENGTH vs = LENGTH vals /\
  ALL_DISTINCT vs /\
  t ⊑ locals s /\
  evaluate (p, set_locals (t |++ ZIP (vs, vals)) s) = (r, s') /\
  (forall v, MEM v vs \/ MEM v tmp_vars -> v NOTIN FDOM t) /\
  r <> SOME Error /\
  ALL_DISTINCT tmp_vars /\ LENGTH tmp_vars = LENGTH vs /\
  (forall x, MEM x tmp_vars -> ~ MEM x vs) /\
  (forall x, MEM x tmp_vars -> ~ MEM x (FLAT (MAP var_cexp es))) ->
  exists t',
    evaluate (arg_load tmp_vars es vs p, s) = (r, t') /\
    state_rel s' t' /\
    match r with
    | NONE => FDIFF (locals s) (FDOM t) = FDIFF (locals t') (FDOM t) /\
              FOLDL res_var (locals s') (ZIP (vs, MAP (FLOOKUP (locals s)) vs)) ⊑ locals t'
    | SOME (Break n) => FDIFF (locals s) (FDOM t) = FDIFF (locals t') (FDOM t) /\
              FOLDL res_var (locals s') (ZIP (vs, MAP (FLOOKUP (locals s)) vs)) ⊑ locals t'
    | SOME (Continue n) => FDIFF (locals s) (FDOM t) = FDIFF (locals t') (FDOM t) /\
              FOLDL res_var (locals s') (ZIP (vs, MAP (FLOOKUP (locals s)) vs)) ⊑ locals t'
    | SOME Error => False
    | _ => True
    end.
Proof.
  intros s es vals vs t p r s' tmp_vars (Ho & Hl & Hd & Hsub & H & Ht & Hne & Hdt & Hlt & Htv & Hte).
  destruct (arg_load_facts s es vals vs t p r s' tmp_vars Ho Hl Hd Hsub H Ht Hne Hdt Hlt Htv Hte)
    as (t' & E & Hs & Hf). exists t'. unfold arg_load. split; [exact E|]. split; [exact Hs|].
  destruct r as [[]|]; try exact I; try (exfalso; apply Hne; reflexivity); exact (Hf eq_refl).
Qed.

End ArgLoad2.
Section Code.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "state_rel_code_def" *)
Definition state_rel_code s t : Prop :=
  globals s = globals t /\
  memory s = memory t /\
  memaddrs s = memaddrs t /\
  sh_memaddrs s = sh_memaddrs t /\
  clock s = clock t /\
  be s = be t /\
  ffi s = ffi t /\
  base_addr s = base_addr t /\
  top_addr s = top_addr t.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "fdom_subset_flookup_thm" *)
Theorem fdom_subset_flookup_thm : forall {K V} (f g : fmap K V),
  FDOM f SUBSET FDOM g <-> (forall x p, FLOOKUP f x = SOME p -> exists q, FLOOKUP g x = SOME q).
Proof.
  intros K V f g. unfold_sets; unfold FDOM. split.
  - intros H x p Hx. specialize (H x). destruct (FLOOKUP g x); [eexists; reflexivity|].
    exfalso; apply H; [congruence|reflexivity].
  - intros H x Hx. destruct (FLOOKUP f x) eqn:E; [|contradiction].
    destruct (H x _ E) as [q Hq]. congruence.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "eval_state_locals_same_code_fdom_same" *)
Theorem eval_state_locals_same_code_fdom_same : forall s (e : exp a) val s1,
  eval s e = SOME val /\
  state_rel_code s s1 /\
  locals_strong_rel s s1 /\
  FDOM (code s) SUBSET FDOM (code s1) ->
  eval s1 e = SOME val.
Proof.
  intros s e val s1 (He & (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) & Hl & _).
  unfold locals_strong_rel in Hl. rewrite <- (eval_state_cong s s1); assumption.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "code_inl_rel_def" *)
Definition code_inl_rel (inl_fs : fmap funname (list varname * prog a)) s t : Prop :=
  forall fname args prog,
    FLOOKUP (code s) fname = SOME (args, prog) ->
    exists inl_bag,
      inl_bag ⊑ inl_fs /\
      FLOOKUP (code t) fname = SOME (args, inline_prog inl_bag prog).

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "eval_code_inl" *)
Theorem eval_code_inl : forall s (e : exp a) val s1 inl_fs,
  eval s e = SOME val /\
  state_rel_code s s1 /\
  locals_strong_rel s s1 /\
  code_inl_rel inl_fs s s1 ->
  eval s1 e = SOME val.
Proof.
  intros s e val s1 inl_fs (He & Hs & Hl & Hc).
  apply (eval_state_locals_same_code_fdom_same s e val s1). split; [exact He|]. split; [exact Hs|].
  split; [exact Hl|]. intros x Hx. unfold_sets; unfold FDOM in *.
  destruct (FLOOKUP (code s) x) as [[args prog]|] eqn:E; [|contradiction].
  destruct (Hc x args prog E) as (bag & _ & E2). rewrite E2. discriminate.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "opt_mmap_eval_code_inl" *)
Theorem opt_mmap_eval_code_inl : forall s (es : list (exp a)) vals s1 inl_fs,
  OPT_MMAP (eval s) es = SOME vals /\
  state_rel_code s s1 /\
  locals_strong_rel s s1 /\
  code_inl_rel inl_fs s s1 ->
  OPT_MMAP (eval s1) es = SOME vals.
Proof.
  intros s es vals s1 inl_fs (Ho & Hs & Hl & Hc). rewrite <- Ho. apply OPT_MMAP_ext_In''.
  intros e He. destruct (OPT_MMAP_In_SOME _ _ _ e Ho He) as [v Hv]. rewrite Hv.
  apply (eval_code_inl s e v s1 inl_fs). tauto.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_is_total" *)
Theorem evaluate_is_total : forall (p : prog a) s, exists r s', evaluate (p, s) = (r, s').
Proof. intros p s. destruct (evaluate (p, s)) as [r s']. eauto. Qed.

End Code.

Lemma MAX_LIST_ge_i (l : list N) x : In x l -> x <= MAX_LIST l.
Proof.
  induction l as [|y l IH]; intros Hx; [destruct Hx|]. cbn [MAX_LIST]. unfold MAX.
  destruct (N.ltb_spec y (MAX_LIST l)); destruct Hx as [->|Hx]; try lia; specialize (IH Hx); lia.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "MORE_THEN_NOT_MAX_LIST" *)
Theorem MORE_THEN_NOT_MAX_LIST : forall l x, MAX_LIST l < x -> ~ MEM x l.
Proof. intros l x Hx Hm. apply MEM_In, MAX_LIST_ge_i in Hm. lia. Qed.

Section Unreach.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(** [unreach_elim] does not grow [psize] (Galette-only; HOL's
    [unreach_elim_prog_size] is about the generated [prog_size]). *)
Lemma unreach_elim_psize (p : prog a) : forall q r, unreach_elim p = (q, r) -> (psize q <= psize p)%nat.
Proof.
  induction p using cprog_nested_ind; intros q0 r0 Hq; cbn [unreach_elim] in Hq;
    try (injection Hq as <- <-; cbn [psize]; lia).
  - destruct (unreach_elim p) as [p' r'] eqn:E. injection Hq as <- <-. cbn [psize].
    specialize (IHp _ _ eq_refl). lia.
  - destruct (unreach_elim p1) as [p1' r1] eqn:E1. specialize (IHp1 _ _ eq_refl).
    destruct (decide (r1 <> None)).
    + injection Hq as <- <-. cbn [psize]. lia.
    + destruct (unreach_elim p2) as [p2' r2] eqn:E2. specialize (IHp2 _ _ eq_refl).
      injection Hq as <- <-. cbn [psize]. lia.
  - destruct (unreach_elim p1) as [p1' r1] eqn:E1, (unreach_elim p2) as [p2' r2] eqn:E2.
    specialize (IHp1 _ _ eq_refl). specialize (IHp2 _ _ eq_refl).
    injection Hq as <- <-. cbn [psize]. lia.
  - destruct (unreach_elim p) as [p' r'] eqn:E. injection Hq as <- <-. cbn [psize].
    specialize (IHp _ _ eq_refl). lia.
  - destruct o as [[rts [[w hdl]|]]|].
    + destruct (unreach_elim hdl) as [h' rh]. injection Hq as <- <-. cbn; lia.
    + injection Hq as <- <-. cbn; lia.
    + injection Hq as <- <-. cbn; lia.
Qed.

Lemma unreach_elim_Seq_fix (p1 p2 : prog a) r :
  unreach_elim (Seq p1 p2) = (Seq p1 p2, r) ->
  unreach_elim p1 = (p1, NONE) /\ unreach_elim p2 = (p2, r).
Proof.
  cbn [unreach_elim]. destruct (unreach_elim p1) as [p1' r1] eqn:E1.
  destruct (decide (r1 <> None)) as [Hn|Hn].
  - intros H. injection H as H1 _. apply unreach_elim_psize in E1. subst p1'. cbn [psize] in E1. lia.
  - destruct (unreach_elim p2) as [p2' r2] eqn:E2. intros H. injection H as <- <- <-.
    destruct r1; [exfalso; apply Hn; discriminate|]. tauto.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "unreach_elim_not_none_evaluate" *)
Theorem unreach_elim_not_none_evaluate : forall (p : prog a) s r s' p1 e,
  unreach_elim p = (p1, SOME e) /\
  evaluate (p, s) = (r, s') ->
  exists e, r = SOME e.
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall r s' p1 e,
            unreach_elim (fst x) = (p1, SOME e) -> evaluate x = (r, s') -> exists e, r = SOME e)
    by (intros p s r s' p1 e [H1 H2]; exact (G (p, s) r s' p1 e H1 H2)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s' p1 e Hu H; cbn [fst snd] in *.
  destruct p; cbn [unreach_elim] in Hu; unfold_eval_in H.
  all: try (injection Hu as _ Hu; discriminate Hu).
  all: repeat match type of Hu with context [let '(_, _) := unreach_elim ?q in _] =>
         let E := fresh "U" in destruct (unreach_elim q) as [? ?] eqn:E end.
  all: repeat match type of Hu with context [decide ?P] => destruct (decide P) end.
  all: repeat split_in H.
  all: try (injection H as <- <-; eexists; reflexivity).
  all: try (injection H as <- <-).
  all: repeat match type of Hu with context [match ?o with _ => _ end] => destruct o end.
  all: try (injection Hu as _ Hu'; discriminate Hu').
  all: try (injection Hu as _ Hu'; subst).
  all: try match goal with
       | E : evaluate (?q, ?Y) = (?r0, ?s0), U : unreach_elim ?q = (?q', SOME ?e') |- _ =>
           let Hx := fresh "Hx" in
           destruct (IH (q, Y) ltac:(lt_tac) r0 s0 q' e' U E) as [? Hx];
           first [discriminate Hx | subst; eexists; reflexivity]
       end.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "unreach_elim_correct" *)
Theorem unreach_elim_correct : forall (p : prog a) s r s' p1 (s1 : option early_exit),
  evaluate (p, s) = (r, s') /\
  r <> SOME Error /\
  unreach_elim p = (p1, s1) ->
  evaluate (p1, s) = (r, s').
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall r s' p1 (s1 : option early_exit),
            evaluate x = (r, s') -> r <> SOME Error -> unreach_elim (fst x) = (p1, s1) ->
            evaluate (p1, snd x) = (r, s'))
    by (intros p s r s' p1 s1 (H1 & H2 & H3); exact (G (p, s) r s' p1 s1 H1 H2 H3)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s' p1 s1 H Hne Hu; cbn [fst snd] in *.
  assert (IH' : forall q Y r0 s0 q' x0, eval_lt (q, Y) (p, s) -> r0 <> SOME Error ->
             unreach_elim q = (q', x0) -> evaluate (q, Y) = (r0, s0) -> evaluate (q', Y) = (r0, s0))
    by (intros q Y r0 s0 q' x0 Hlt Hn U E; exact (IH (q, Y) Hlt r0 s0 q' x0 E Hn U)).
  clear IH.
  destruct p; cbn [unreach_elim] in Hu.
  all: try match type of Hu with context [match ?o with NONE => _ | SOME _ => _ end] =>
         is_var o; destruct o as [[? [[? ?]|]]|] end.
  all: repeat match type of Hu with context [let '(_, _) := unreach_elim ?q in _] =>
         let U := fresh "U" in destruct (unreach_elim q) as [? ?] eqn:U end.
  all: repeat match type of Hu with context [decide ?P] => destruct (decide P) end.
  all: injection Hu as <- <-.
  all: try exact H.
  all: unfold_eval_in H; repeat split_in H.
  all: try (injection H as H1 H2; subst; cbn [exit_loop] in Hne; congruence).
  all: try match goal with
       | U : unreach_elim ?q = (?q', SOME ?e'), E : evaluate (?q, ?Y) = (NONE, _) |- _ =>
           destruct (unreach_elim_not_none_evaluate q Y _ _ q' e' (conj U E)); discriminate
       end.
  all: try (injection H as <- <-).
  all: try (lazymatch goal with |- evaluate (?q, _) = _ => tryif is_var q then fail else ev_goal end); rw_hyps.
  all: try match goal with U : unreach_elim ?q = (?q', ?x) |- context [While ?e ?q'] =>
         assert (unreach_elim (While e q) = (While e q', NONE)) by (cbn [unreach_elim]; rewrite U; reflexivity)
       end.
  all: try match goal with n : ?o <> NONE |- _ => is_var o; destruct o; [|exfalso; apply n; reflexivity] end.
  all: try match goal with
       | U : unreach_elim ?q = (?q', SOME ?e'), E : evaluate (?q, ?Y) = (NONE, _) |- _ =>
           destruct (unreach_elim_not_none_evaluate q Y _ _ q' e' (conj U E)); discriminate
       end.
  all: repeat (match goal with
       | E : evaluate (?q, ?Y) = (?r0, ?s0), U : unreach_elim ?q = (?q', ?x) |- context [evaluate (?q', ?Y)] =>
           tryif constr_eq q q' then fail else
           rewrite (IH' q Y r0 s0 q' x ltac:(lt_tac) ltac:(first [discriminate | assumption | congruence]) U E)
       end; cbn beta iota zeta).
  all: try exact H; try reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "unreach_elim_converge" *)
Theorem unreach_elim_converge : forall (p : prog a) q (r : option early_exit),
  unreach_elim p = (q, r) ->
  unreach_elim q = (q, r).
Proof.
  intros p; induction p using cprog_nested_ind; intros q0 r0 Hq; cbn [unreach_elim] in Hq.
  all: try (injection Hq as <- <-; reflexivity).
  - destruct (unreach_elim p) as [p' r'] eqn:E. injection Hq as <- <-. cbn [unreach_elim].
    rewrite (IHp _ _ eq_refl). reflexivity.
  - destruct (unreach_elim p1) as [p1' r1] eqn:E1. destruct (decide (r1 <> None)) as [Hn|Hn].
    + injection Hq as <- <-. exact (IHp1 _ _ eq_refl).
    + destruct (unreach_elim p2) as [p2' r2] eqn:E2. injection Hq as <- <-. cbn [unreach_elim].
      rewrite (IHp1 _ _ eq_refl). destruct (decide (r1 <> None)); [contradiction|].
      rewrite (IHp2 _ _ eq_refl). reflexivity.
  - destruct (unreach_elim p1) as [p1' r1] eqn:E1, (unreach_elim p2) as [p2' r2] eqn:E2.
    injection Hq as <- <-. cbn [unreach_elim]. rewrite (IHp1 _ _ eq_refl), (IHp2 _ _ eq_refl). reflexivity.
  - destruct (unreach_elim p) as [p' r'] eqn:E. injection Hq as <- <-. cbn [unreach_elim].
    rewrite (IHp _ _ eq_refl). reflexivity.
  - destruct o as [[rts [[w hdl]|]]|].
    + destruct (unreach_elim hdl) as [h' rh] eqn:E. injection Hq as <- <-. cbn [unreach_elim].
      rewrite (H rts w hdl eq_refl _ _ E). reflexivity.
    + injection Hq as <- <-. reflexivity.
    + injection Hq as <- <-. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "unreach_elim_fix_point" *)
Theorem unreach_elim_fix_point : forall (q : prog a) (r : option early_exit),
  (exists p, unreach_elim p = (q, r)) <-> unreach_elim q = (q, r).
Proof.
  intros q r. split.
  - intros [p Hp]. exact (unreach_elim_converge p q r Hp).
  - intros H. exists q. exact H.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "unreach_elim_nested_decs" *)
Theorem unreach_elim_nested_decs : forall vs (es : list (exp a)) p (r : option early_exit),
  LENGTH vs = LENGTH es /\
  unreach_elim p = (p, r) ->
  unreach_elim (nested_decs vs es p) = (nested_decs vs es p, r).
Proof.
  induction vs as [|v vs IH]; intros [|e es] p r [Hl Hu]; rewrite ?LENGTH_cons in Hl;
    cbn [LENGTH] in Hl; try lia; cbn [nested_decs]; [exact Hu|].
  cbn [unreach_elim]. rewrite (IH es p r); [reflexivity|]. split; [lia|exact Hu].
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "unreach_elim_arg_load" *)
Theorem unreach_elim_arg_load : forall (p : prog a) tmp_vars args args_vname (r : option early_exit),
  LENGTH tmp_vars = LENGTH args /\
  LENGTH args = LENGTH args_vname /\
  unreach_elim p = (p, r) ->
  unreach_elim (arg_load tmp_vars args args_vname p) = (arg_load tmp_vars args args_vname p, r).
Proof.
  intros p tmp args vn r (H1 & H2 & Hu). unfold arg_load.
  apply unreach_elim_nested_decs. split; [exact H1|].
  apply unreach_elim_nested_decs. split; [rewrite LENGTH_MAP_i; lia|exact Hu].
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "unreach_elim_arg_load_perm" *)
Theorem unreach_elim_arg_load_perm : forall (p : prog a) tmp_vars args args_vname (r : option early_exit),
  LENGTH tmp_vars = LENGTH args_vname /\
  LENGTH args = LENGTH args_vname /\
  unreach_elim p = (p, r) ->
  unreach_elim (arg_load tmp_vars args args_vname p) = (arg_load tmp_vars args args_vname p, r).
Proof.
  intros p tmp args vn r (H1 & H2 & Hu). apply unreach_elim_arg_load.
  split; [lia|]. split; [exact H2|exact Hu].
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "not_has_return_imp_not_branch_ret" *)
Theorem not_has_return_imp_not_branch_ret : forall p : prog a, ~ has_return p -> not_branch_ret p.
Proof.
  intros p; induction p using cprog_nested_ind; cbn [has_return not_branch_ret]; intros Hh;
    unfold is_true in *; try reflexivity.
  - apply IHp, Hh.
  - apply Bool.andb_true_iff. split; [apply IHp1|apply IHp2]; intros C; apply Hh; rewrite C;
      [reflexivity|apply Bool.orb_true_r].
  - apply Bool.andb_true_iff. split; apply Bool.negb_true_iff;
      destruct (has_return p1), (has_return p2); try reflexivity; exfalso; apply Hh; reflexivity.
  - apply Bool.negb_true_iff. destruct (has_return p); [exfalso; apply Hh|]; reflexivity.
  - destruct o as [[rts [[w hdl]|]]|]; try reflexivity.
    + apply Bool.negb_true_iff. destruct (has_return hdl); [exfalso; apply Hh|]; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "not_has_return_imp_unreach_elim" *)
Theorem not_has_return_imp_unreach_elim : forall (p : prog a) r,
  ~ has_return p /\ unreach_elim p = (p, r) -> r <> SOME Ret.
Proof.
  intros p; induction p using cprog_nested_ind; intros r0 [Hh Hu]; cbn [has_return] in Hh;
    cbn [unreach_elim] in Hu; unfold is_true in Hh.
  all: try (injection Hu as Hu; subst; discriminate).
  - destruct (unreach_elim p) as [p' r'] eqn:E. injection Hu as -> ->. apply (IHp r0). split; [exact Hh|first [exact E|reflexivity]].
  - destruct (unreach_elim p1) as [p1' r1] eqn:E1. destruct (decide (r1 <> None)) as [Hn|Hn].
    + injection Hu as H1 _. apply unreach_elim_psize in E1. subst p1'. cbn [psize] in E1. lia.
    + destruct (unreach_elim p2) as [p2' r2] eqn:E2. injection Hu as -> -> ->.
      apply (IHp2 r0). split; [|first [exact E2|reflexivity]]. intros C; apply Hh; rewrite C; apply Bool.orb_true_r.
  - destruct (unreach_elim p1) as [p1' r1] eqn:E1, (unreach_elim p2) as [p2' r2] eqn:E2.
    injection Hu as -> -> Hr.
    assert (N1 : r1 <> SOME Ret) by (apply (IHp1 r1); split; [intros C; apply Hh; rewrite C; reflexivity|first [exact E1|reflexivity]]).
    assert (N2 : r2 <> SOME Ret) by (apply (IHp2 r2); split; [intros C; apply Hh; rewrite C; apply Bool.orb_true_r|first [exact E2|reflexivity]]).
    subst r0. destruct r1 as [[]|], r2 as [[]|]; congruence.
  - destruct (unreach_elim p) as [p' r'] eqn:E. injection Hu as _ <-. discriminate.
  - destruct o as [[rts [[w hdl]|]]|].
    + destruct (unreach_elim hdl) as [h' rh] eqn:E. injection Hu as _ <-. discriminate.
    + injection Hu as <-. discriminate.
    + exfalso; apply Hh; reflexivity.
  - exfalso; apply Hh; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "not_branch_ret_evaluate_return_unreach_elim" *)
Theorem not_branch_ret_evaluate_return_unreach_elim : forall (p : prog a) s r s',
  unreach_elim p = (p, NONE) /\
  not_branch_ret p /\
  evaluate (p, s) = (r, s') ->
  forall rv, r <> SOME (Return rv).
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall r s',
            unreach_elim (fst x) = (fst x, NONE) -> not_branch_ret (fst x) -> evaluate x = (r, s') ->
            forall rv, r <> SOME (Return rv))
    by (intros p s r s' (H1 & H2 & H3); exact (G (p, s) r s' H1 H2 H3)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s' Hu Hn H rv; cbn [fst snd] in *.
  assert (Hnr : forall q, has_return q = false -> forall Y r0 s0, evaluate (q, Y) = (r0, s0) -> r0 <> SOME (Return rv))
    by (intros q Hq Y r0 s0 E; exact (no_return_evaluate q Y r0 s0 Hq E rv)).
  destruct p; cbn [not_branch_ret] in Hn; unfold is_true in Hn.
  all: try (eapply Hnr; [|exact H]; reflexivity).
  - (* Dec *)
    cbn [unreach_elim] in Hu. match type of Hu with context [unreach_elim ?q] =>
      destruct (unreach_elim q) as [p' r'] eqn:U end. injection Hu as -> ->.
    unfold_eval_in H. repeat split_in H; [|injection H as <- _; discriminate].
    injection H as <- _.
    match goal with E : evaluate (?q, ?Y) = _ |- _ => apply (IH (q, Y) ltac:(lt_tac) _ _ U Hn E) end.
  - (* Seq *)
    apply unreach_elim_Seq_fix in Hu as [Hu1 Hu2]. apply Bool.andb_true_iff in Hn as [Hn1 Hn2].
    unfold_eval_in H. repeat split_in H.
    + injection H as <- _.
      match goal with E : evaluate (?q, ?Y) = _ |- _ => apply (IH (q, Y) ltac:(lt_tac) _ _ Hu1 Hn1 E) end.
    + match type of H with evaluate (?q, ?Y) = _ => apply (IH (q, Y) ltac:(lt_tac) _ _ Hu2 Hn2 H) end.
  - (* If *)
    apply Bool.andb_true_iff in Hn as [Hn1 Hn2]. apply Bool.negb_true_iff in Hn1, Hn2.
    eapply Hnr; [|exact H]. cbn [has_return]. rewrite Hn1, Hn2. reflexivity.
  - (* While *)
    apply Bool.negb_true_iff in Hn. eapply Hnr; [|exact H]. cbn [has_return]. exact Hn.
  - (* Call *)
    destruct o as [[rts [[w hdl]|]]|].
    + apply Bool.negb_true_iff in Hn. eapply Hnr; [|exact H]. cbn [has_return]. exact Hn.
    + eapply Hnr; [|exact H]; reflexivity.
    + cbn [unreach_elim] in Hu. discriminate.
  - (* Return *)
    cbn [unreach_elim] in Hu. discriminate.
Qed.

End Unreach.

Section OptMmap.
Context {K V : Type} `{HK : EqDecision K}.
Implicit Types fm : fmap K V.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "opt_mmap_some_imp_fupdate_exist_some" *)
Theorem opt_mmap_some_imp_fupdate_exist_some : forall (vs : list K) fm (vals : list V) nv,
  OPT_MMAP (FLOOKUP fm) vs = SOME vals ->
  exists z, OPT_MMAP (FLOOKUP (fm |+ nv)) vs = SOME z.
Proof.
  intros vs fm vals [k v] H. apply OPT_MMAP_SOME_ALL. intros x Hx.
  destruct (proj1 (OPT_MMAP_SOME_ALL _ vs) (ex_intro _ _ H) x Hx) as [y Hy].
  rewrite FLOOKUP_UPDATE. destruct (decide (k = x)); eauto.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "opt_mmap_some_imp_fupdate_list_exist_some" *)
Theorem opt_mmap_some_imp_fupdate_list_exist_some : forall (xs : list K) (ys : list V) vs fm (vals : list V),
  OPT_MMAP (FLOOKUP fm) vs = SOME vals /\ LENGTH xs = LENGTH ys ->
  exists z, OPT_MMAP (FLOOKUP (fm |++ ZIP (xs, ys))) vs = SOME z.
Proof.
  intros xs ys vs fm vals [H _]. apply OPT_MMAP_SOME_ALL. intros x Hx.
  destruct (proj1 (OPT_MMAP_SOME_ALL _ vs) (ex_intro _ _ H) x Hx) as [y Hy].
  destruct (in_dec (fun u w => decide (u = w)) x (map fst (ZIP (xs, ys)))) as [Hi|Hn].
  - destruct (FLOOKUP (fm |++ ZIP (xs, ys)) x) eqn:E; [eexists; reflexivity|].
    exfalso. revert E. generalize fm. clear H Hy. induction (ZIP (xs, ys)) as [|[k v] l IH]; intros f E; [destruct Hi|].
    change (FLOOKUP ((f |+ (k, v)) |++ l) x = NONE) in E.
    destruct (in_dec (fun u w => decide (u = w)) x (map fst l)) as [Hi'|Hn'].
    + exact (IH Hi' _ E).
    + rewrite FLOOKUP_FUPDATE_LIST_notin in E by exact Hn'. cbn in Hi. destruct Hi as [<-|Hi]; [|tauto].
      rewrite FLOOKUP_UPDATE in E. destruct (decide (k = k)); congruence.
  - rewrite FLOOKUP_FUPDATE_LIST_notin by exact Hn. eauto.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "opt_mmap_flookup_not_mem_domsub" *)
Theorem opt_mmap_flookup_not_mem_domsub : forall (vs : list K) fm (vals : list V) x,
  OPT_MMAP (FLOOKUP fm) vs = SOME vals /\ ~ MEM x vs ->
  OPT_MMAP (FLOOKUP (fm \\ x)) vs = SOME vals.
Proof.
  intros vs fm vals x [H Hx]. rewrite <- H. apply OPT_MMAP_ext_In''. intros y Hy.
  rewrite DOMSUB_FLOOKUP_THM. destruct (decide (x = y)) as [->|]; [|reflexivity].
  exfalso. apply Hx, MEM_In, Hy.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "fdoms_eq_opt_mmap_flookup_some" *)
Theorem fdoms_eq_opt_mmap_flookup_some : forall (vs : list K) fm fm' (vals : list V),
  FDOM fm = FDOM fm' /\ OPT_MMAP (FLOOKUP fm) vs = SOME vals ->
  exists z, OPT_MMAP (FLOOKUP fm') vs = SOME z.
Proof.
  intros vs fm fm' vals [Hd H]. apply OPT_MMAP_SOME_ALL. intros x Hx.
  destruct (proj1 (OPT_MMAP_SOME_ALL _ vs) (ex_intro _ _ H) x Hx) as [y Hy].
  assert (Hin : FDOM fm' x) by (rewrite <- Hd; unfold FDOM; congruence).
  unfold FDOM in Hin. destruct (FLOOKUP fm' x); [eauto|contradiction].
Qed.

End OptMmap.

Section NestedSeq.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "opt_mmap_update_locals_not_vars_eval_eq" *)
Theorem opt_mmap_update_locals_not_vars_eval_eq : forall (es : list (exp a)) n vs w s,
  ~ MEM n (FLAT (MAP var_cexp es)) /\ OPT_MMAP (eval s) es = SOME vs ->
  OPT_MMAP (eval (set_locals (locals s |+ (n, w)) s)) es = SOME vs.
Proof.
  intros es n vs w s [Hn H]. rewrite <- H. apply OPT_MMAP_ext_In''. intros e He.
  apply update_locals_not_vars_eval_eq'; [exact w|]. intros Hm. apply Hn, MEM_In.
  eapply In_FLAT_MAP; [exact He|apply MEM_In, Hm].
Qed.

(** Evaluation of [nested_seq (MAP2 Assign ns es)] (Galette-only). *)
Lemma nested_seq_assign_eval : forall ns (es : list (exp a)) s ws vals,
  OPT_MMAP (eval s) es = SOME ws ->
  (forall x, MEM x ns -> ~ MEM x (FLAT (MAP var_cexp es))) ->
  OPT_MMAP (FLOOKUP (locals s)) ns = SOME vals ->
  LENGTH ns = LENGTH ws ->
  ALL_DISTINCT ns ->
  evaluate (nested_seq (MAP2 Assign ns es), s) = (NONE, set_locals (locals s |++ ZIP (ns, ws)) s).
Proof.
  induction ns as [|n ns IH]; intros es s ws vals Ho Hv Hl Hlen Hd.
  - destruct ws; [|rewrite LENGTH_cons in Hlen; cbn in Hlen; lia].
    pose proof (opt_mmap_length_eq _ _ _ Ho) as Hle. destruct es; [|rewrite LENGTH_cons in Hle; cbn in Hle; lia].
    cbn [MAP2 nested_seq]. rewrite (proj1 evaluate_def). change (locals s |++ ZIP ([], [])) with (locals s).
    rewrite set_locals_id. reflexivity.
  - pose proof (opt_mmap_length_eq _ _ _ Ho) as Hle.
    destruct es as [|e es]; [destruct ws; [rewrite ?LENGTH_cons in Hlen; cbn in Hlen; lia|cbn in Ho; discriminate]|].
    cbn [OPT_MMAP] in Ho. destruct (eval s e) as [w|] eqn:He; [|discriminate].
    destruct (OPT_MMAP (eval s) es) as [ws'|] eqn:Hes; [|discriminate]. injection Ho as <-.
    cbn [OPT_MMAP] in Hl. destruct (FLOOKUP (locals s) n) as [vn|] eqn:Hn; [|discriminate].
    destruct (OPT_MMAP (FLOOKUP (locals s)) ns) as [vals'|] eqn:Hns; [|discriminate].
    cbn [ALL_DISTINCT] in Hd. apply andb_prop in Hd as [Hnn Hd].
    assert (Hv1 : ~ MEM n (FLAT (MAP var_cexp es))).
    { intros Hm. apply (Hv n); [apply MEM_In; left; reflexivity|]. apply MEM_In.
      cbn [MAP List.map FLAT List.concat]. apply in_or_app; right; apply MEM_In, Hm. }
    cbn [MAP2 nested_seq]. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 evaluate_def)))))))))).
    rewrite (proj1 (proj2 (proj2 (proj2 evaluate_def)))), He, Hn. cbv beta iota.
    rewrite (IH es (set_locals (locals s |+ (n, w)) s) ws' vals').
    + rewrite sl_locals, sl_sl. reflexivity.
    + apply opt_mmap_update_locals_not_vars_eval_eq. split; [exact Hv1|exact Hes].
    + intros x Hx Hm. apply (Hv x); [apply MEM_In; right; apply MEM_In, Hx|]. apply MEM_In.
      cbn [MAP List.map FLAT List.concat]. apply in_or_app; right; apply MEM_In, Hm.
    + rewrite sl_locals. apply opt_mmap_flookup_update. split; [exact Hns|].
      intros Hm. rewrite Hm in Hnn. discriminate.
    + rewrite !LENGTH_cons in Hlen. lia.
    + exact Hd.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_nested_seq_assign" *)
Theorem evaluate_nested_seq_assign : forall ns s (es : list (exp a)) ws vals,
  OPT_MMAP (eval s) es = SOME ws /\
  (forall x, MEM x ns -> ~ MEM x (FLAT (MAP var_cexp es))) /\
  OPT_MMAP (FLOOKUP (locals s)) ns = SOME vals /\
  LENGTH ns = LENGTH ws /\
  ALL_DISTINCT ns ->
  exists s',
    evaluate (nested_seq (MAP2 Assign ns es), s) = (NONE, s') /\
    state_rel s s' /\
    (forall x, ~ MEM x ns -> FLOOKUP (locals s') x = FLOOKUP (locals s) x) /\
    OPT_MMAP (FLOOKUP (locals s')) ns = SOME ws.
Proof.
  intros ns s es ws vals (Ho & Hv & Hl & Hlen & Hd).
  rewrite (nested_seq_assign_eval ns es s ws vals Ho Hv Hl Hlen Hd).
  eexists; split; [reflexivity|]. split; [apply state_rel_sl_r, state_rel_refl|]. rewrite sl_locals. split.
  - intros x Hx. apply FLOOKUP_FUPDATE_LIST_notin. intros Hi. apply In_map_fst_ZIP in Hi.
    apply Hx, MEM_In, Hi.
  - apply opt_mmap_some_eq_zip_flookup. split; [exact Hd|exact Hlen].
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_nested_seq_assign_drule" *)
Theorem evaluate_nested_seq_assign_drule : forall ns s (es : list (exp a)) ws vals r s',
  OPT_MMAP (eval s) es = SOME ws /\
  (forall x, MEM x ns -> ~ MEM x (FLAT (MAP var_cexp es))) /\
  OPT_MMAP (FLOOKUP (locals s)) ns = SOME vals /\
  LENGTH ns = LENGTH ws /\
  ALL_DISTINCT ns /\
  evaluate (nested_seq (MAP2 Assign ns es), s) = (r, s') ->
  r = NONE /\
  state_rel s s' /\
  (forall x, ~ MEM x ns -> FLOOKUP (locals s') x = FLOOKUP (locals s) x) /\
  OPT_MMAP (FLOOKUP (locals s')) ns = SOME ws.
Proof.
  intros ns s es ws vals r s' (Ho & Hv & Hl & Hlen & Hd & H).
  destruct (evaluate_nested_seq_assign ns s es ws vals (conj Ho (conj Hv (conj Hl (conj Hlen Hd)))))
    as (s'' & E & Hs & Hx & Hr). rewrite H in E. injection E as -> ->. tauto.
Qed.

End NestedSeq.
Ltac ev_goal_at p := rewrite (evaluate_unfold p); cbn [evaluate_body]; rewrite ?fcl_evaluate; cbn beta.

Section Transform.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma strong_eq s t : state_rel s t -> locals_strong_rel s t -> t = s.
Proof.
  destruct s, t; intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) H11;
    unfold locals_strong_rel in H11; cbn in *; subst; reflexivity.
Qed.

Lemma locals_strong_refl s : locals_strong_rel s s.
Proof. reflexivity. Qed.

(** The post-condition of [transform_eoc_correct] (Galette-only name). *)
Definition eoc_post (rts : list varname) (r : option (result a)) s' (r1 : option (result a)) s1' : Prop :=
  state_rel s' s1' /\
  match r with
  | NONE => r1 = NONE /\ locals_strong_rel s' s1'
  | SOME (Break n) => r1 = SOME (Break n) /\ locals_strong_rel s' s1'
  | SOME (Continue n) => r1 = SOME (Continue n) /\ locals_strong_rel s' s1'
  | SOME (Return retvs) => r1 = NONE /\ OPT_MMAP (FLOOKUP (locals s1')) rts = SOME retvs
  | SOME Error => False
  | res => r1 = res
  end.

Lemma eoc_post_refl rts r s' :
  (forall retvs, r <> SOME (Return retvs)) -> r <> SOME Error -> eoc_post rts r s' r s'.
Proof.
  intros H1 H2. split; [apply state_rel_refl|].
  destruct r as [[| |n|n|retvs|eid|f]|]; try (split; reflexivity); try reflexivity;
    try congruence; exfalso; exact (H1 _ eq_refl).
Qed.

Lemma has_return_false_not (p : prog a) : ~ has_return p -> has_return p = false.
Proof. destruct (has_return p); [intros H; exfalso; apply H; reflexivity|reflexivity]. Qed.

Lemma opt_mmap_res_var_notin (l : fmap varname (word_lab a)) v x (rts : list varname) :
  ~ MEM v rts -> OPT_MMAP (FLOOKUP (res_var l (v, x))) rts = OPT_MMAP (FLOOKUP l) rts.
Proof.
  intros Hv. apply OPT_MMAP_ext_In''. intros y Hy. rewrite FLOOKUP_res_var.
  destruct (decide (y = v)) as [->|]; [|reflexivity]. exfalso; apply Hv, MEM_In, Hy.
Qed.

Lemma eoc_post_some rts x s' r1 s1' :
  eoc_post rts (SOME x) s' r1 s1' -> (forall rv, x <> Return rv) -> x <> Error -> r1 = SOME x.
Proof.
  intros [_ H] Hr He. destruct x as [| |n|n|retvs|eid|f]; cbn in H; try tauto; try congruence;
  exfalso; exact (Hr _ eq_refl).
Qed.

Lemma MEM_app_iff (x : varname) l1 l2 : MEM x (l1 ++ l2) <-> MEM x l1 \/ MEM x l2.
Proof. unfold is_true; rewrite !MEM_In, in_app_iff; tauto. Qed.

Ltac eoc_same Hev :=
  injection Hev as <- <-; eexists _, _; split; [reflexivity|]; apply eoc_post_refl;
  [intros ? ?; discriminate|discriminate].

Lemma transform_eoc_G : forall (x : prog a * state a ffi_t) r s' res rts,
  evaluate x = (r, s') ->
  unreach_elim (fst x) = (fst x, res) ->
  not_branch_ret (fst x) ->
  (forall retvs, r = SOME (Return retvs) -> LENGTH rts = LENGTH retvs) ->
  (forall x0, MEM x0 rts -> ~ MEM x0 (var_prog (fst x))) ->
  (exists z, OPT_MMAP (FLOOKUP (locals (snd x))) rts = SOME z) ->
  ALL_DISTINCT rts ->
  r <> SOME Error ->
  exists r1 s1', evaluate (transform_eoc rts (fst x), snd x) = (r1, s1') /\ eoc_post rts r s' r1 s1'.
Proof.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s' res rts Hev Hu Hn Hlen Hvar [z Hz] Hd Hne; cbn [fst snd] in *.
  assert (Hsame : has_return p = false -> transform_eoc rts p = p ->
                  exists r1 s1', evaluate (transform_eoc rts p, s) = (r1, s1') /\ eoc_post rts r s' r1 s1').
  { intros Hh Ht. rewrite Ht. exists r, s'. split; [exact Hev|]. apply eoc_post_refl; [|exact Hne].
    intros retvs. exact (no_return_evaluate p s r s' Hh Hev retvs). }
  destruct p as [|v e p|v e|lhs pop rhs|e1 e2|e1 e2|e1 e2|g e|c1 c2|e c1 c2|e c|n|n|ctyp f args|fi p1 l1 p2 l2|w|es|op v e|].
  all: try (apply Hsame; reflexivity).
  - (* Dec *)
    cbn [unreach_elim] in Hu. destruct (unreach_elim p) as [p' r'] eqn:U. injection Hu as -> ->.
    cbn [not_branch_ret] in Hn. cbn [transform_eoc].
    assert (Hv : ~ MEM v rts).
    { intros Hm; apply (Hvar v Hm); cbn [var_prog]. unfold is_true; rewrite MEM_In; left; reflexivity. }
    assert (Hvar' : forall x0, MEM x0 rts -> ~ MEM x0 (var_prog p)).
    { intros x0 Hx Hm; apply (Hvar x0 Hx); cbn [var_prog]. rewrite !MEM_app_iff. tauto. }
    unfold_eval_in Hev. repeat split_in Hev; [|injection Hev as <- _; congruence].
    injection Hev as <- <-.
    destruct (IH (p, set_locals (locals s |+ (v, w)) s) ltac:(lt_tac) o s0 res rts E0 U Hn Hlen Hvar'
                 ltac:(exists z; cbn [snd]; rewrite sl_locals; apply opt_mmap_flookup_update; split; assumption) Hd Hne)
      as (r1 & t1 & Ht1 & Hs1 & Hp). cbn [fst snd] in Ht1.
    ev_goal. rewrite E. cbv beta iota. rewrite Ht1. cbv beta iota.
    eexists _, _. split; [reflexivity|]. split; [apply state_rel_set_locals2, Hs1|].
    unfold locals_strong_rel in *. destruct o as [[| |n|n|retvs|eid|f]|]; cbv beta iota in Hp |- *;
      try (match type of Hp with _ /\ _ => destruct Hp as [-> Hp]; rewrite ?sl_locals, Hp; split; reflexivity end);
      try exact Hp.
    destruct Hp as [-> Hp]. split; [reflexivity|]. rewrite ?sl_locals, opt_mmap_res_var_notin by exact Hv. exact Hp.
  - (* Seq *)
    apply unreach_elim_Seq_fix in Hu as [U1 U2]. cbn [not_branch_ret] in Hn.
    apply Bool.andb_true_iff in Hn as [Hn1 Hn2]. cbn [transform_eoc].
    assert (Hv1 : forall x0, MEM x0 rts -> ~ MEM x0 (var_prog c1))
      by (intros x0 Hx Hm; apply (Hvar x0 Hx); cbn [var_prog]; rewrite MEM_app_iff; tauto).
    assert (Hv2 : forall x0, MEM x0 rts -> ~ MEM x0 (var_prog c2))
      by (intros x0 Hx Hm; apply (Hvar x0 Hx); cbn [var_prog]; rewrite MEM_app_iff; tauto).
    unfold_eval_in Hev. repeat split_in Hev.
    + injection Hev as <- <-.
      assert (Hnr : forall rv, r0 <> Return rv).
      { intros rv E'. subst r0. exact (not_branch_ret_evaluate_return_unreach_elim c1 s _ s0
                                        (conj U1 (conj Hn1 E)) rv eq_refl). }
      destruct (IH (c1, s) ltac:(lt_tac) (SOME r0) s0 NONE rts E U1 Hn1
                   ltac:(intros rv Hrv; injection Hrv as Hrv; exfalso; exact (Hnr rv Hrv)) Hv1
                   ltac:(exists z; exact Hz) Hd Hne) as (r1 & t1 & Ht1 & Hp). cbn [fst snd] in Ht1.
      pose proof (eoc_post_some rts r0 s0 r1 t1 Hp Hnr ltac:(congruence)) as ->.
      ev_goal. rewrite Ht1. cbv beta iota. eexists _, _. split; [reflexivity|exact Hp].
    + destruct (IH (c1, s) ltac:(lt_tac) NONE s0 NONE rts E U1 Hn1
                   ltac:(intros rv Hrv; discriminate) Hv1 ltac:(exists z; exact Hz) Hd ltac:(discriminate))
        as (r1 & t1 & Ht1 & Hs1 & -> & Hl1). cbn [fst snd] in Ht1.
      pose proof (strong_eq _ _ Hs1 Hl1) as ->.
      assert (Hz2 : exists z, OPT_MMAP (FLOOKUP (locals s0)) rts = SOME z).
      { apply (fdoms_eq_opt_mmap_flookup_some rts (locals s) (locals s0) z). split; [|exact Hz].
        apply (evaluate_locals_same_fdom' c1 s NONE s0). split; [exact E|left; reflexivity]. }
      destruct (IH (c2, s0) ltac:(lt_tac) r s' res rts Hev U2 Hn2 Hlen Hv2 Hz2 Hd Hne)
        as (r2 & t2 & Ht2 & Hp2). cbn [fst snd] in Ht2.
      ev_goal. rewrite Ht1. cbv beta iota. rewrite Ht2. eexists _, _. split; [reflexivity|exact Hp2].
  - (* If *)
    cbn [unreach_elim] in Hu. destruct (unreach_elim c1) as [p1' r1'] eqn:U1, (unreach_elim c2) as [p2' r2'] eqn:U2.
    injection Hu as -> -> _. cbn [not_branch_ret] in Hn.
    apply Bool.andb_true_iff in Hn as [Hn1 Hn2]. apply Bool.negb_true_iff in Hn1, Hn2.
    assert (Hb1 : not_branch_ret c1) by (apply not_has_return_imp_not_branch_ret; rewrite Hn1; discriminate).
    assert (Hb2 : not_branch_ret c2) by (apply not_has_return_imp_not_branch_ret; rewrite Hn2; discriminate).
    assert (Hv1 : forall x0, MEM x0 rts -> ~ MEM x0 (var_prog c1))
      by (intros x0 Hx Hm; apply (Hvar x0 Hx); cbn [var_prog]; rewrite !MEM_app_iff; tauto).
    assert (Hv2 : forall x0, MEM x0 rts -> ~ MEM x0 (var_prog c2))
      by (intros x0 Hx Hm; apply (Hvar x0 Hx); cbn [var_prog]; rewrite !MEM_app_iff; tauto).
    cbn [transform_eoc]. unfold_eval_in Hev. repeat split_in Hev; try (injection Hev as <- _; congruence).
    + destruct (IH (c1, s) ltac:(lt_tac) r s' r1' rts Hev U1 Hb1 Hlen Hv1 ltac:(exists z; exact Hz) Hd Hne)
        as (r1 & t1 & Ht1 & Hp). cbn [fst snd] in Ht1.
      ev_goal. rw_hyps. try rewrite Ht1. eexists _, _. split; [reflexivity|exact Hp].
    + destruct (IH (c2, s) ltac:(lt_tac) r s' r2' rts Hev U2 Hb2 Hlen Hv2 ltac:(exists z; exact Hz) Hd Hne)
        as (r1 & t1 & Ht1 & Hp). cbn [fst snd] in Ht1.
      ev_goal. rw_hyps. try rewrite Ht1. eexists _, _. split; [reflexivity|exact Hp].
  - (* While *)
    cbn [unreach_elim] in Hu. destruct (unreach_elim c) as [c' rc] eqn:U. injection Hu as -> <-.
    assert (Hu' : unreach_elim (While e c) = (While e c, NONE)) by (cbn [unreach_elim]; rewrite U; reflexivity).
    pose proof Hn as Hn0. cbn [not_branch_ret] in Hn. apply Bool.negb_true_iff in Hn.
    assert (Hb : not_branch_ret c) by (apply not_has_return_imp_not_branch_ret; rewrite Hn; discriminate).
    assert (Hv1 : forall x0, MEM x0 rts -> ~ MEM x0 (var_prog c))
      by (intros x0 Hx Hm; apply (Hvar x0 Hx); cbn [var_prog]; rewrite MEM_app_iff; tauto).
    cbn [transform_eoc]. unfold_eval_in Hev.
    destruct (eval s e) as [[w]|] eqn:Ee; try (injection Hev as <- _; congruence).
    destruct (negb (bool_decide (w = n2w 0))) eqn:Ew.
    2: { injection Hev as <- <-. ev_goal. rewrite Ee. cbv beta iota. rewrite Ew. eexists _, _.
         split; [reflexivity|]. apply eoc_post_refl; [intros ? ?; discriminate|discriminate]. }
    destruct (clock s =? 0) eqn:Ec.
    { injection Hev as <- <-. ev_goal. rewrite Ee. cbv beta iota. rewrite Ew, Ec. eexists _, _.
      split; [reflexivity|]. apply eoc_post_refl; [intros ? ?; discriminate|discriminate]. }
    destruct (evaluate (c, dec_clock s)) as [o s1] eqn:E3. cbv beta iota in Hev.
    assert (Hno : forall rv, o <> SOME (Return rv)) by (intros rv; exact (no_return_evaluate c _ o s1 Hn E3 rv)).
    assert (Hoe : o <> SOME Error) by (intros ->; injection Hev as <- _; apply Hne; reflexivity).
    destruct (IH (c, dec_clock s) ltac:(lt_tac) o s1 rc rts E3 U Hb
                 ltac:(intros rv Hrv; exfalso; exact (Hno rv Hrv)) Hv1 ltac:(exists z; exact Hz) Hd Hoe)
      as (r1 & t1 & Ht1 & Hp). cbn [fst snd] in Ht1.
    ev_goal. rewrite Ee. cbv beta iota. rewrite Ew, Ec. cbv beta iota. rewrite Ht1. cbv beta iota.
    assert (Hrec : forall o', (o = NONE \/ o = SOME (Continue o')) -> t1 = s1 ->
                evaluate (While e c, s1) = (r, s') ->
                exists r2 t2, evaluate (While e (transform_eoc rts c), s1) = (r2, t2) /\ eoc_post rts r s' r2 t2).
    { intros o' Ho -> Hev'. 
      assert (Hz2 : exists z, OPT_MMAP (FLOOKUP (locals s1)) rts = SOME z).
      { apply (fdoms_eq_opt_mmap_flookup_some rts (locals s) (locals s1) z). split; [|exact Hz].
        apply (evaluate_locals_same_fdom' c (dec_clock s) o s1). split; [exact E3|].
        destruct Ho as [->| ->]; [left; reflexivity|right; right; exists o'; reflexivity]. }
      destruct (IH (While e c, s1) ltac:(lt_tac) r s' NONE rts Hev' Hu' Hn0 Hlen Hvar Hz2 Hd Hne)
        as (r2 & t2 & Ht2 & Hp2). cbn [fst snd transform_eoc] in Ht2. eauto. }
    destruct o as [[| |n|n|rv|eid|f]|].
    + exfalso; apply Hoe; reflexivity.
    + rewrite (eoc_post_some rts _ s1 r1 t1 Hp ltac:(intros ? ?; discriminate) ltac:(discriminate)).
      injection Hev as <- <-. eexists _, _. split; [reflexivity|]. split; [exact (proj1 Hp)|reflexivity].
    + destruct Hp as [Hs1 [-> Hl1]]. destruct n as [|pn].
      * injection Hev as <- <-. eexists _, _. split; [reflexivity|]. split; [exact Hs1|]. split; [reflexivity|exact Hl1].
      * injection Hev as <- <-. eexists _, _. split; [reflexivity|]. split; [exact Hs1|]. split; [reflexivity|exact Hl1].
    + destruct Hp as [Hs1 [-> Hl1]]. destruct n as [|pn].
      * pose proof (strong_eq _ _ Hs1 Hl1) as ->. cbv beta iota.
        destruct (Hrec 0 (or_intror eq_refl) eq_refl Hev) as (r2 & t2 & Ht2 & Hp2). rewrite Ht2. eauto.
      * injection Hev as <- <-. eexists _, _. split; [reflexivity|]. split; [exact Hs1|]. split; [reflexivity|exact Hl1].
    + exfalso; exact (Hno rv eq_refl).
    + rewrite (eoc_post_some rts _ s1 r1 t1 Hp ltac:(intros ? ?; discriminate) ltac:(discriminate)).
      injection Hev as <- <-. eexists _, _. split; [reflexivity|]. split; [exact (proj1 Hp)|reflexivity].
    + rewrite (eoc_post_some rts _ s1 r1 t1 Hp ltac:(intros ? ?; discriminate) ltac:(discriminate)).
      injection Hev as <- <-. eexists _, _. split; [reflexivity|]. split; [exact (proj1 Hp)|reflexivity].
    + destruct Hp as [Hs1 [-> Hl1]]. pose proof (strong_eq _ _ Hs1 Hl1) as ->. cbv beta iota.
      destruct (Hrec 0 (or_introl eq_refl) eq_refl Hev) as (r2 & t2 & Ht2 & Hp2). rewrite Ht2. eauto.
  - (* Call *)
    destruct ctyp as [[rs [[w hdl]|]]|].
    + cbn [unreach_elim] in Hu. destruct (unreach_elim hdl) as [h' rh] eqn:U. injection Hu as -> _.
      cbn [not_branch_ret] in Hn. apply Bool.negb_true_iff in Hn.
      assert (Hb : not_branch_ret hdl) by (apply not_has_return_imp_not_branch_ret; rewrite Hn; discriminate).
      assert (Hv1 : forall x0, MEM x0 rts -> ~ MEM x0 (var_prog hdl))
        by (intros x0 Hx Hm; apply (Hvar x0 Hx); cbn [var_prog]; rewrite !MEM_app_iff; tauto).
      cbn [transform_eoc]. unfold_eval_in Hev. repeat split_in Hev.
      all: try (injection Hev as <- _; congruence).
      all: ev_goal; rw_hyps.
      all: try eoc_same Hev.
      destruct (IH (hdl, set_locals (locals s) s0) ltac:(lt_tac) r s' rh rts Hev U Hb Hlen Hv1
                   ltac:(exists z; cbn [snd]; rewrite sl_locals; exact Hz) Hd Hne)
        as (r1 & t1 & Ht1 & Hp). cbn [fst snd] in Ht1. rewrite Ht1. eauto.
    + apply Hsame; reflexivity.
    + cbn [transform_eoc]. unfold_eval_in Hev. repeat split_in Hev.
      all: try (injection Hev as <- _; congruence).
      all: ev_goal; unfold is_true in Hd; rw_hyps; cbv beta iota.
      all: try eoc_same Hev.
      injection Hev as <- <-. cbn [negb]. rewrite (Hlen l0 eq_refl), N.eqb_refl. cbn [negb].
      eexists _, _. split; [reflexivity|].
      split; [unfold empty_locals; apply state_rel_set_locals2, state_rel_refl|]. split; [reflexivity|].
      rewrite sl_locals. apply opt_mmap_some_eq_zip_flookup. split; [exact Hd|exact (Hlen l0 eq_refl)].
  - (* Return *)
    cbn [transform_eoc]. unfold_eval_in Hev. repeat split_in Hev; [|injection Hev as <- _; congruence].
    injection Hev as <- <-.
    destruct (evaluate_nested_seq_assign rts s es l z) as (s1 & E1 & Hs1 & _ & Hr1).
    { split; [exact E|]. split; [|split; [exact Hz|split; [exact (Hlen l eq_refl)|exact Hd]]].
      intros x0 Hx Hm. apply (Hvar x0 Hx). cbn [var_prog]. exact Hm. }
    rewrite E1. eexists _, _. split; [reflexivity|]. split; [apply state_rel_sl_l, Hs1|].
    split; [reflexivity|exact Hr1].
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "transform_eoc_correct" *)
Theorem transform_eoc_correct : forall (p : prog a) s r s' (res : option early_exit) rts,
  evaluate (p, s) = (r, s') /\
  unreach_elim p = (p, res) /\
  not_branch_ret p /\
  (forall retvs, r = SOME (Return retvs) -> LENGTH rts = LENGTH retvs) /\
  (forall x, MEM x rts -> ~ MEM x (var_prog p)) /\
  (exists z, OPT_MMAP (FLOOKUP (locals s)) rts = SOME z) /\
  ALL_DISTINCT rts /\
  r <> SOME Error ->
  exists r1 s1',
    evaluate (transform_eoc rts p, s) = (r1, s1') /\
    state_rel s' s1' /\
    match r with
    | NONE => r1 = NONE /\ locals_strong_rel s' s1'
    | SOME (Break n) => r1 = SOME (Break n) /\ locals_strong_rel s' s1'
    | SOME (Continue n) => r1 = SOME (Continue n) /\ locals_strong_rel s' s1'
    | SOME (Return retvs) => r1 = NONE /\ OPT_MMAP (FLOOKUP (locals s1')) rts = SOME retvs
    | SOME Error => False
    | res => r1 = res
    end.
Proof.
  intros p s r s' res rts (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  exact (transform_eoc_G (p, s) r s' res rts H1 H2 H3 H4 H5 H6 H7 H8).
Qed.


Definition br_post (ld : N) (rts : list varname) (r : option (result a)) s' (r1 : option (result a)) s1' : Prop :=
  state_rel s' s1' /\
  match r with
  | NONE => r1 = NONE /\ locals_strong_rel s' s1'
  | SOME (Break n) => r1 = SOME (Break n) /\ locals_strong_rel s' s1'
  | SOME (Continue n) => r1 = SOME (Continue n) /\ locals_strong_rel s' s1'
  | SOME (Return retvs) => r1 = SOME (Break ld) /\ OPT_MMAP (FLOOKUP (locals s1')) rts = SOME retvs
  | SOME Error => False
  | res => r1 = res
  end.

Lemma br_post_refl ld rts r s' :
  (forall retvs, r <> SOME (Return retvs)) -> r <> SOME Error -> br_post ld rts r s' r s'.
Proof.
  intros H1 H2. split; [apply state_rel_refl|].
  destruct r as [[| |n|n|retvs|eid|f]|]; try (split; reflexivity); try reflexivity;
    try congruence; exfalso; exact (H1 _ eq_refl).
Qed.

Lemma br_post_some ld rts x s' r1 s1' :
  br_post ld rts (SOME x) s' r1 s1' -> x <> Error -> exists y, r1 = SOME y.
Proof.
  intros [_ H] He. destruct x as [| |n|n|retvs|eid|f]; cbv beta iota in H; try tauto.
  all: first [ match type of H with _ /\ _ => destruct H as [H _] end; subst r1; eexists; reflexivity
             | subst r1; eexists; reflexivity ].
Qed.

Ltac br_same Hev :=
  injection Hev as <- <-; eexists _, _; split; [reflexivity|]; apply br_post_refl;
  [intros ? ?; discriminate|discriminate].

Lemma transform_branch_G : forall (x : prog a * state a ffi_t) r s' ld rts,
  evaluate x = (r, s') ->
  (forall retvs, r = SOME (Return retvs) -> LENGTH rts = LENGTH retvs) ->
  (forall x0, MEM x0 rts -> ~ MEM x0 (var_prog (fst x))) ->
  (exists z, OPT_MMAP (FLOOKUP (locals (snd x))) rts = SOME z) ->
  ALL_DISTINCT rts ->
  r <> SOME Error ->
  exists r1 s1', evaluate (transform_branch ld rts (fst x), snd x) = (r1, s1') /\ br_post ld rts r s' r1 s1'.
Proof.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s' ld rts Hev Hlen Hvar [z Hz] Hd Hne; cbn [fst snd] in *.
  assert (Hsame : has_return p = false -> transform_branch ld rts p = p ->
                  exists r1 s1', evaluate (transform_branch ld rts p, s) = (r1, s1') /\ br_post ld rts r s' r1 s1').
  { intros Hh Ht. rewrite Ht. exists r, s'. split; [exact Hev|]. apply br_post_refl; [|exact Hne].
    intros retvs. exact (no_return_evaluate p s r s' Hh Hev retvs). }
  destruct p as [|v e p|v e|lhs pop rhs|e1 e2|e1 e2|e1 e2|g e|c1 c2|e c1 c2|e c|n|n|ctyp f args|fi p1 l1 p2 l2|w|es|op v e|].
  all: try (apply Hsame; reflexivity).
  - (* Dec *)
    cbn [transform_branch].
    assert (Hv : ~ MEM v rts).
    { intros Hm; apply (Hvar v Hm); cbn [var_prog]. unfold is_true; rewrite MEM_In; left; reflexivity. }
    assert (Hvar' : forall x0, MEM x0 rts -> ~ MEM x0 (var_prog p)).
    { intros x0 Hx Hm; apply (Hvar x0 Hx); cbn [var_prog]. rewrite !MEM_app_iff. tauto. }
    unfold_eval_in Hev. repeat split_in Hev; [|injection Hev as <- _; congruence].
    injection Hev as <- <-.
    destruct (IH (p, set_locals (locals s |+ (v, w)) s) ltac:(lt_tac) o s0 ld rts E0 Hlen Hvar'
                 ltac:(exists z; cbn [snd]; rewrite sl_locals; apply opt_mmap_flookup_update; split; assumption) Hd Hne)
      as (r1 & t1 & Ht1 & Hs1 & Hp). cbn [fst snd] in Ht1.
    ev_goal. rewrite E. cbv beta iota. rewrite Ht1. cbv beta iota.
    eexists _, _. split; [reflexivity|]. split; [apply state_rel_set_locals2, Hs1|].
    unfold locals_strong_rel in *. destruct o as [[| |n|n|retvs|eid|f]|]; cbv beta iota in Hp |- *;
      try (match type of Hp with _ /\ _ => destruct Hp as [-> Hp]; rewrite ?sl_locals, Hp; split; reflexivity end);
      try exact Hp.
    destruct Hp as [-> Hp]. split; [reflexivity|]. rewrite ?sl_locals, opt_mmap_res_var_notin by exact Hv. exact Hp.
  - (* Seq *)
    cbn [transform_branch].
    assert (Hv1 : forall x0, MEM x0 rts -> ~ MEM x0 (var_prog c1))
      by (intros x0 Hx Hm; apply (Hvar x0 Hx); cbn [var_prog]; rewrite MEM_app_iff; tauto).
    assert (Hv2 : forall x0, MEM x0 rts -> ~ MEM x0 (var_prog c2))
      by (intros x0 Hx Hm; apply (Hvar x0 Hx); cbn [var_prog]; rewrite MEM_app_iff; tauto).
    unfold_eval_in Hev. repeat split_in Hev.
    + injection Hev as <- <-.
      destruct (IH (c1, s) ltac:(lt_tac) (SOME r0) s0 ld rts E Hlen Hv1
                   ltac:(exists z; exact Hz) Hd Hne) as (r1 & t1 & Ht1 & Hp). cbn [fst snd] in Ht1.
      destruct (br_post_some ld rts r0 s0 r1 t1 Hp ltac:(congruence)) as [y ->].
      ev_goal. rewrite Ht1. cbv beta iota. eexists _, _. split; [reflexivity|exact Hp].
    + destruct (IH (c1, s) ltac:(lt_tac) NONE s0 ld rts E
                   ltac:(intros rv Hrv; discriminate) Hv1 ltac:(exists z; exact Hz) Hd ltac:(discriminate))
        as (r1 & t1 & Ht1 & Hs1 & -> & Hl1). cbn [fst snd] in Ht1.
      pose proof (strong_eq _ _ Hs1 Hl1) as ->.
      assert (Hz2 : exists z, OPT_MMAP (FLOOKUP (locals s0)) rts = SOME z).
      { apply (fdoms_eq_opt_mmap_flookup_some rts (locals s) (locals s0) z). split; [|exact Hz].
        apply (evaluate_locals_same_fdom' c1 s NONE s0). split; [exact E|left; reflexivity]. }
      destruct (IH (c2, s0) ltac:(lt_tac) r s' ld rts Hev Hlen Hv2 Hz2 Hd Hne)
        as (r2 & t2 & Ht2 & Hp2). cbn [fst snd] in Ht2.
      ev_goal. rewrite Ht1. cbv beta iota. rewrite Ht2. eexists _, _. split; [reflexivity|exact Hp2].
  - (* If *)
    assert (Hv1 : forall x0, MEM x0 rts -> ~ MEM x0 (var_prog c1))
      by (intros x0 Hx Hm; apply (Hvar x0 Hx); cbn [var_prog]; rewrite !MEM_app_iff; tauto).
    assert (Hv2 : forall x0, MEM x0 rts -> ~ MEM x0 (var_prog c2))
      by (intros x0 Hx Hm; apply (Hvar x0 Hx); cbn [var_prog]; rewrite !MEM_app_iff; tauto).
    cbn [transform_branch]. unfold_eval_in Hev. repeat split_in Hev; try (injection Hev as <- _; congruence).
    + destruct (IH (c1, s) ltac:(lt_tac) r s' ld rts Hev Hlen Hv1 ltac:(exists z; exact Hz) Hd Hne)
        as (r1 & t1 & Ht1 & Hp). cbn [fst snd] in Ht1.
      ev_goal. rw_hyps. try rewrite Ht1. eexists _, _. split; [reflexivity|exact Hp].
    + destruct (IH (c2, s) ltac:(lt_tac) r s' ld rts Hev Hlen Hv2 ltac:(exists z; exact Hz) Hd Hne)
        as (r1 & t1 & Ht1 & Hp). cbn [fst snd] in Ht1.
      ev_goal. rw_hyps. try rewrite Ht1. eexists _, _. split; [reflexivity|exact Hp].
  - (* While *)
    assert (Hv1 : forall x0, MEM x0 rts -> ~ MEM x0 (var_prog c))
      by (intros x0 Hx Hm; apply (Hvar x0 Hx); cbn [var_prog]; rewrite MEM_app_iff; tauto).
    cbn [transform_branch]. unfold_eval_in Hev.
    destruct (eval s e) as [[w]|] eqn:Ee; try (injection Hev as <- _; congruence).
    destruct (negb (bool_decide (w = n2w 0))) eqn:Ew.
    2: { injection Hev as <- <-. ev_goal. rewrite Ee. cbv beta iota. rewrite Ew. eexists _, _.
         split; [reflexivity|]. apply br_post_refl; [intros ? ?; discriminate|discriminate]. }
    destruct (clock s =? 0) eqn:Ec.
    { injection Hev as <- <-. ev_goal. rewrite Ee. cbv beta iota. rewrite Ew, Ec. eexists _, _.
      split; [reflexivity|]. apply br_post_refl; [intros ? ?; discriminate|discriminate]. }
    destruct (evaluate (c, dec_clock s)) as [o s1] eqn:E3. cbv beta iota in Hev.
    assert (Hoe : o <> SOME Error) by (intros ->; injection Hev as <- _; apply Hne; reflexivity).
    assert (Hlo : forall retvs, o = SOME (Return retvs) -> LENGTH rts = LENGTH retvs).
    { intros retvs ->. injection Hev as <- _. apply Hlen. reflexivity. }
    destruct (IH (c, dec_clock s) ltac:(lt_tac) o s1 (ld + 1) rts E3 Hlo Hv1 ltac:(exists z; exact Hz) Hd Hoe)
      as (r1 & t1 & Ht1 & Hp). cbn [fst snd] in Ht1.
    ev_goal. rewrite Ee. cbv beta iota. rewrite Ew, Ec. cbv beta iota. rewrite Ht1. cbv beta iota.
    assert (Hrec : forall o', (o = NONE \/ o = SOME (Continue o')) -> t1 = s1 ->
                evaluate (While e c, s1) = (r, s') ->
                exists r2 t2, evaluate (While e (transform_branch (ld + 1) rts c), s1) = (r2, t2) /\ br_post ld rts r s' r2 t2).
    { intros o' Ho -> Hev'.
      assert (Hz2 : exists z, OPT_MMAP (FLOOKUP (locals s1)) rts = SOME z).
      { apply (fdoms_eq_opt_mmap_flookup_some rts (locals s) (locals s1) z). split; [|exact Hz].
        apply (evaluate_locals_same_fdom' c (dec_clock s) o s1). split; [exact E3|].
        destruct Ho as [->| ->]; [left; reflexivity|right; right; exists o'; reflexivity]. }
      destruct (IH (While e c, s1) ltac:(lt_tac) r s' ld rts Hev' Hlen Hvar Hz2 Hd Hne)
        as (r2 & t2 & Ht2 & Hp2). cbn [fst snd transform_branch] in Ht2. eauto. }
    destruct o as [[| |n|n|rv|eid|f]|].
    + exfalso; apply Hoe; reflexivity.
    + destruct Hp as [Hs1 ->]. injection Hev as <- <-. eexists _, _. split; [reflexivity|]. split; [exact Hs1|reflexivity].
    + destruct Hp as [Hs1 [-> Hl1]]. destruct n as [|pn].
      * injection Hev as <- <-. eexists _, _. split; [reflexivity|]. split; [exact Hs1|]. split; [reflexivity|exact Hl1].
      * injection Hev as <- <-. eexists _, _. split; [reflexivity|]. split; [exact Hs1|]. split; [reflexivity|exact Hl1].
    + destruct Hp as [Hs1 [-> Hl1]]. destruct n as [|pn].
      * pose proof (strong_eq _ _ Hs1 Hl1) as ->. cbv beta iota.
        destruct (Hrec 0 (or_intror eq_refl) eq_refl Hev) as (r2 & t2 & Ht2 & Hp2). rewrite Ht2. eauto.
      * injection Hev as <- <-. eexists _, _. split; [reflexivity|]. split; [exact Hs1|]. split; [reflexivity|exact Hl1].
    + destruct Hp as [Hs1 [-> Hl1]]. injection Hev as <- <-.
      replace (ld + 1) with (N.pos (N.succ_pos ld)) by (rewrite N.succ_pos_spec; lia). cbv beta iota.
      eexists _, _. split; [reflexivity|]. split; [exact Hs1|]. split; [|exact Hl1].
      cbn [exit_loop]. f_equal. f_equal. rewrite N.succ_pos_spec. lia.
    + destruct Hp as [Hs1 ->]. injection Hev as <- <-. eexists _, _. split; [reflexivity|]. split; [exact Hs1|reflexivity].
    + destruct Hp as [Hs1 ->]. injection Hev as <- <-. eexists _, _. split; [reflexivity|]. split; [exact Hs1|reflexivity].
    + destruct Hp as [Hs1 [-> Hl1]]. pose proof (strong_eq _ _ Hs1 Hl1) as ->. cbv beta iota.
      destruct (Hrec 0 (or_introl eq_refl) eq_refl Hev) as (r2 & t2 & Ht2 & Hp2). rewrite Ht2. eauto.
  - (* Call *)
    destruct ctyp as [[rs [[w hdl]|]]|].
    + assert (Hv1 : forall x0, MEM x0 rts -> ~ MEM x0 (var_prog hdl))
        by (intros x0 Hx Hm; apply (Hvar x0 Hx); cbn [var_prog]; rewrite !MEM_app_iff; tauto).
      cbn [transform_branch]. unfold_eval_in Hev. repeat split_in Hev.
      all: try (injection Hev as <- _; congruence).
      all: ev_goal; rw_hyps.
      all: try br_same Hev.
      destruct (IH (hdl, set_locals (locals s) s0) ltac:(lt_tac) r s' ld rts Hev Hlen Hv1
                   ltac:(exists z; cbn [snd]; rewrite sl_locals; exact Hz) Hd Hne)
        as (r1 & t1 & Ht1 & Hp). cbn [fst snd] in Ht1. rewrite Ht1. eauto.
    + apply Hsame; reflexivity.
    + cbn [transform_branch]. unfold_eval_in Hev. repeat split_in Hev.
      all: try (injection Hev as <- _; congruence).
      all: ev_goal; ev_goal_at (Call (SOME (rts, NONE)) f args); unfold is_true in Hd; rw_hyps; cbv beta iota.
      all: cbn [negb]; cbv beta iota.
      all: try (injection Hev as <- <-; cbv beta iota; eexists _, _; split; [reflexivity|];
                apply br_post_refl; [intros ? ?; discriminate|discriminate]).
      injection Hev as <- <-. rewrite (Hlen l0 eq_refl), N.eqb_refl. cbn [negb]. cbv beta iota. ev_goal.
      eexists _, _. split; [reflexivity|].
      split; [unfold empty_locals; apply state_rel_set_locals2, state_rel_refl|]. split; [reflexivity|].
      rewrite sl_locals. apply opt_mmap_some_eq_zip_flookup. split; [exact Hd|exact (Hlen l0 eq_refl)].
  - (* Return *)
    cbn [transform_branch]. unfold_eval_in Hev. repeat split_in Hev; [|injection Hev as <- _; congruence].
    injection Hev as <- <-.
    destruct (evaluate_nested_seq_assign rts s es l z) as (s1 & E1 & Hs1 & _ & Hr1).
    { split; [exact E|]. split; [|split; [exact Hz|split; [exact (Hlen l eq_refl)|exact Hd]]].
      intros x0 Hx Hm. apply (Hvar x0 Hx). cbn [var_prog]. exact Hm. }
    ev_goal. rewrite E1. cbv beta iota. ev_goal. eexists _, _. split; [reflexivity|].
    split; [apply state_rel_sl_l, Hs1|]. split; [reflexivity|exact Hr1].
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "transform_branch_correct" *)
Theorem transform_branch_correct : forall (p : prog a) s r s' (res : option early_exit) ld rts,
  evaluate (p, s) = (r, s') /\
  (forall retvs, r = SOME (Return retvs) -> LENGTH rts = LENGTH retvs) /\
  (forall x, MEM x rts -> ~ MEM x (var_prog p)) /\
  (exists z, OPT_MMAP (FLOOKUP (locals s)) rts = SOME z) /\
  ALL_DISTINCT rts /\
  r <> SOME Error ->
  exists r1 s1',
    evaluate (transform_branch ld rts p, s) = (r1, s1') /\
    state_rel s' s1' /\
    match r with
    | NONE => r1 = NONE /\ locals_strong_rel s' s1'
    | SOME (Break n) => r1 = SOME (Break n) /\ locals_strong_rel s' s1'
    | SOME (Continue n) => r1 = SOME (Continue n) /\ locals_strong_rel s' s1'
    | SOME (Return retvs) => r1 = SOME (Break ld) /\ OPT_MMAP (FLOOKUP (locals s1')) rts = SOME retvs
    | SOME Error => False
    | res => r1 = res
    end.
Proof.
  intros p s r s' res ld rts (H1 & H2 & H3 & H4 & H5 & H6).
  exact (transform_branch_G (p, s) r s' ld rts H1 H2 H3 H4 H5 H6).
Qed.

End Transform.

Section Wrapped.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "cont_res_def" *)
Definition cont_res (r : option (result a)) : bool :=
  match r with
  | NONE => true
  | SOME (Break n) => true
  | SOME (Continue n) => true
  | SOME Error => true
  | _ => false
  end.

Lemma one_ne_zero_i : (n2w 1 : word a) <> n2w 0.
Proof.
  intros H. apply n2w_11 in H.
  assert (Hd : 2 <= dimword a).
  { unfold dimword, dimindex. apply (N.le_trans _ (2 ^ 1)); [cbn; lia|]. apply N.pow_le_mono_r; lia. }
  rewrite (N.mod_small 1), (N.mod_small 0) in H by lia. discriminate.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "wrapped_transform_if" *)
Theorem wrapped_transform_if : forall (p : prog a) s r s' (res : option early_exit) rts loc,
  evaluate (p, set_locals loc (dec_clock s)) = (r, s') /\
  unreach_elim p = (p, res) /\
  (forall retvs, r = SOME (Return retvs) -> LENGTH rts = LENGTH retvs) /\
  (forall x, MEM x rts -> ~ MEM x (var_prog p)) /\
  (exists z, OPT_MMAP (FLOOKUP loc) rts = SOME z) /\
  ALL_DISTINCT rts /\
  ~ cont_res r /\
  clock s <> 0 /\
  r <> SOME Error ->
  exists r1 s1',
    evaluate (if not_branch_ret p then Seq Tick (transform_eoc rts p)
              else While (Const (n2w 1)) (transform_branch 0 rts p), set_locals loc s) = (r1, s1') /\
    state_rel s' s1' /\
    match r with
    | SOME (Return retvs) => r1 = NONE /\ OPT_MMAP (FLOOKUP (locals s1')) rts = SOME retvs
    | SOME (Exception eid) => r1 = SOME (Exception eid)
    | SOME TimeOut => r1 = SOME TimeOut
    | SOME (FinalFFI f) => r1 = SOME (FinalFFI f)
    | _ => False
    end.
Proof.
  intros p s r s' res rts loc (H & Hu & Hlen & Hvar & Hz & Hd & Hc & Hck & Hne).
  assert (Hz' : exists z, OPT_MMAP (FLOOKUP (locals (set_locals loc (dec_clock s)))) rts = SOME z)
    by (rewrite sl_locals; exact Hz).
  destruct (not_branch_ret p) eqn:Hnb.
  - destruct (transform_eoc_correct p (set_locals loc (dec_clock s)) r s' res rts
                (conj H (conj Hu (conj Hnb (conj Hlen (conj Hvar (conj Hz' (conj Hd Hne))))))))
      as (r1 & s1 & E1 & Hs1 & Hp).
    ev_goal. ev_goal_at (@Tick a). rewrite sl_clock. apply N.eqb_neq in Hck. rewrite Hck. cbv beta iota.
    rewrite sl_dec_clock, E1. exists r1, s1. split; [reflexivity|]. split; [exact Hs1|].
    destruct r as [[| |n|n|rv|eid|f]|]; cbv beta iota in Hp; cbn in Hc |- *;
      first [exfalso; apply Hc; reflexivity | tauto].
  - destruct (transform_branch_correct p (set_locals loc (dec_clock s)) r s' res 0 rts
                (conj H (conj Hlen (conj Hvar (conj Hz' (conj Hd Hne))))))
      as (r1 & s1 & E1 & Hs1 & Hp).
    ev_goal. cbn [eval].
    destruct (bool_decide ((n2w 1 : word a) = n2w 0)) eqn:Eb;
      [apply bool_decide_spec in Eb; exfalso; exact (one_ne_zero_i Eb)|].
    cbn [negb]. rewrite sl_clock. apply N.eqb_neq in Hck. rewrite Hck. cbv beta iota.
    rewrite sl_dec_clock, E1. cbv beta iota.
    destruct r as [[| |n|n|rv|eid|f]|]; cbn in Hc; try (exfalso; apply Hc; reflexivity); cbv beta iota in Hp;
      try (subst r1; eexists _, _; split; [reflexivity|]; split; [exact Hs1|reflexivity]).
    destruct Hp as [-> Hp]. eexists _, _. split; [reflexivity|]. split; [exact Hs1|]. split; [reflexivity|exact Hp].
Qed.

End Wrapped.

Section VarProg.
Context {a : N}.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "mem_var_prog_nested_seq" *)
Theorem mem_var_prog_nested_seq : forall (ps : list (prog a)) x,
  MEM x (var_prog (nested_seq ps)) = MEM x (FLAT (MAP var_prog ps)).
Proof.
  induction ps as [|p ps IH]; intros x; [reflexivity|]. cbn [nested_seq var_prog MAP List.map FLAT List.concat].
  apply Bool.eq_iff_eq_true. unfold is_true. rewrite !MEM_In, !in_app_iff, <- !MEM_In, IH. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "MEM_MAP2_IMP" *)
Theorem MEM_MAP2_IMP : forall {A B C} `{EqDecision C} `{EqDecision A} `{EqDecision B}
    (f : A -> B -> C) l1 l2 x,
  MEM x (MAP2 f l1 l2) -> exists y1 y2, x = f y1 y2 /\ MEM y1 l1 /\ MEM y2 l2.
Proof.
  intros A B C HC HA HB f l1; induction l1 as [|y1 l1 IH]; intros [|y2 l2] x Hx; try discriminate.
  cbn [MAP2] in Hx. unfold is_true in Hx. rewrite MEM_In in Hx. cbn [In] in Hx. destruct Hx as [<-|Hx].
  - exists y1, y2. unfold is_true. rewrite !MEM_In. cbn. tauto.
  - destruct (IH l2 x (proj2 (MEM_In _ _) Hx)) as (z1 & z2 & -> & H1 & H2).
    exists z1, z2. unfold is_true in *. rewrite !MEM_In in *. cbn. tauto.
Qed.

Lemma In_MAP2_IMP {A B C} (f : A -> B -> C) l1 l2 x :
  In x (MAP2 f l1 l2) -> exists y1 y2, x = f y1 y2 /\ In y1 l1 /\ In y2 l2.
Proof.
  revert l2; induction l1 as [|y1 l1 IH]; intros [|y2 l2] Hx; cbn [MAP2 In] in Hx; try contradiction.
  destruct Hx as [<-|Hx].
  - exists y1, y2. cbn. tauto.
  - destruct (IH l2 Hx) as (z1 & z2 & -> & H1 & H2). exists z1, z2. cbn. tauto.
Qed.

Lemma MEM_app_iff' (x : varname) l1 l2 : MEM x (l1 ++ l2) <-> MEM x l1 \/ MEM x l2.
Proof. unfold is_true; rewrite !MEM_In, in_app_iff; tauto. Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "mem_var_prog_transform_eoc" *)
Theorem mem_var_prog_transform_eoc : forall rts (p : prog a) x,
  MEM x (var_prog (transform_eoc rts p)) -> MEM x (var_prog p) \/ MEM x rts.
Proof.
  intros rts p; induction p using cprog_nested_ind; intros x Hx; cbn [transform_eoc var_prog] in *;
    rewrite ?MEM_app_iff' in *; try tauto.
  - destruct Hx as [Hx|[Hx|Hx]]; [tauto|tauto|]. destruct (IHp x Hx); tauto.
  - destruct Hx as [Hx|Hx]; [destruct (IHp1 x Hx)|destruct (IHp2 x Hx)]; tauto.
  - destruct Hx as [Hx|[Hx|Hx]]; [tauto| destruct (IHp1 x Hx)|destruct (IHp2 x Hx)]; tauto.
  - destruct Hx as [Hx|Hx]; [tauto|destruct (IHp x Hx); tauto].
  - destruct o as [[rs [[w hdl]|]]|]; cbn [var_prog] in *; rewrite ?MEM_app_iff' in *; try tauto.
    destruct Hx as [Hx|[Hx|Hx]]; [tauto|tauto|]. destruct (H rs w hdl eq_refl x Hx); tauto.
  - rewrite mem_var_prog_nested_seq in Hx. unfold is_true in Hx. rewrite MEM_In in Hx.
    apply in_concat in Hx as (l & Hl & Hx). apply in_map_iff in Hl as (q & <- & Hq).
    destruct (In_MAP2_IMP _ _ _ _ Hq) as (y1 & y2 & -> & H1 & H2).
    cbn [var_prog app In] in Hx.
    destruct Hx as [<-|Hx]; [right; apply MEM_In, H1|left; apply MEM_In]. eapply In_FLAT_MAP; [exact H2|exact Hx].
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "mem_var_prog_transform_branch" *)
Theorem mem_var_prog_transform_branch : forall ld rts (p : prog a) x,
  MEM x (var_prog (transform_branch ld rts p)) -> MEM x (var_prog p) \/ MEM x rts.
Proof.
  intros ld rts p; revert ld; induction p using cprog_nested_ind; intros ld x Hx;
    cbn [transform_branch var_prog] in *; rewrite ?MEM_app_iff' in *; try tauto.
  - destruct Hx as [Hx|[Hx|Hx]]; [tauto|tauto|]. destruct (IHp ld x Hx); tauto.
  - destruct Hx as [Hx|Hx]; [destruct (IHp1 ld x Hx)|destruct (IHp2 ld x Hx)]; tauto.
  - destruct Hx as [Hx|[Hx|Hx]]; [tauto| destruct (IHp1 ld x Hx)|destruct (IHp2 ld x Hx)]; tauto.
  - destruct Hx as [Hx|Hx]; [tauto|destruct (IHp (ld + 1) x Hx); tauto].
  - destruct o as [[rs [[w hdl]|]]|]; cbn [var_prog] in *; rewrite ?MEM_app_iff' in *; try tauto.
    destruct Hx as [Hx|[Hx|Hx]]; [tauto|tauto|]. destruct (H rs w hdl eq_refl ld x Hx); tauto.
  - destruct Hx as [Hx|Hx]; [|cbn in Hx; discriminate].
    rewrite mem_var_prog_nested_seq in Hx. unfold is_true in Hx. rewrite MEM_In in Hx.
    apply in_concat in Hx as (l & Hl & Hx). apply in_map_iff in Hl as (q & <- & Hq).
    destruct (In_MAP2_IMP _ _ _ _ Hq) as (y1 & y2 & -> & H1 & H2).
    cbn [var_prog app In] in Hx.
    destruct Hx as [<-|Hx]; [right; apply MEM_In, H1|left; apply MEM_In]. eapply In_FLAT_MAP; [exact H2|exact Hx].
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "unreach_elim_preserve_has_return" *)
Theorem unreach_elim_preserve_has_return : forall (p : prog a) q (r : option early_exit),
  ~ has_return p /\
  unreach_elim p = (q, r) ->
  ~ has_return q.
Proof.
  intros p; induction p using cprog_nested_ind; intros q0 r0 [Hh Hu]; cbn [unreach_elim has_return] in *;
    unfold is_true in *.
  all: try (injection Hu as <- _; cbn [has_return]; exact Hh).
  - destruct (unreach_elim p) as [p' r'] eqn:E. injection Hu as <- _. cbn [has_return].
    exact (IHp p' r' (conj Hh eq_refl)).
  - destruct (unreach_elim p1) as [p1' r1] eqn:E1.
    assert (N1 : has_return p1 <> true) by (intros C; apply Hh; rewrite C; reflexivity).
    assert (N2 : has_return p2 <> true) by (intros C; apply Hh; rewrite C; apply Bool.orb_true_r).
    destruct (decide (r1 <> None)).
    + injection Hu as <- _. exact (IHp1 p1' r1 (conj N1 eq_refl)).
    + destruct (unreach_elim p2) as [p2' r2] eqn:E2. injection Hu as <- _. cbn [has_return].
      pose proof (IHp1 p1' r1 (conj N1 eq_refl)). pose proof (IHp2 p2' r2 (conj N2 eq_refl)).
      destruct (has_return p1'), (has_return p2'); cbn; tauto.
  - destruct (unreach_elim p1) as [p1' r1] eqn:E1, (unreach_elim p2) as [p2' r2] eqn:E2.
    assert (N1 : has_return p1 <> true) by (intros C; apply Hh; rewrite C; reflexivity).
    assert (N2 : has_return p2 <> true) by (intros C; apply Hh; rewrite C; apply Bool.orb_true_r).
    injection Hu as <- _. cbn [has_return].
    pose proof (IHp1 p1' r1 (conj N1 eq_refl)). pose proof (IHp2 p2' r2 (conj N2 eq_refl)).
    destruct (has_return p1'), (has_return p2'); cbn; tauto.
  - destruct (unreach_elim p) as [p' r'] eqn:E. injection Hu as <- _. cbn [has_return].
    exact (IHp p' r' (conj Hh eq_refl)).
  - destruct o as [[rts [[w hdl]|]]|].
    + destruct (unreach_elim hdl) as [h' rh] eqn:E. injection Hu as <- _. cbn [has_return].
      exact (H rts w hdl eq_refl h' rh (conj Hh E)).
    + injection Hu as <- _. exact Hh.
    + injection Hu as <- _. exact Hh.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "unreach_elim_preserve_not_branch_ret" *)
Theorem unreach_elim_preserve_not_branch_ret : forall (p : prog a) q (r : option early_exit),
  not_branch_ret p /\
  unreach_elim p = (q, r) ->
  not_branch_ret q.
Proof.
  intros p; induction p using cprog_nested_ind; intros q0 r0 [Hn Hu]; cbn [unreach_elim not_branch_ret] in *.
  all: try (injection Hu as <- _; cbn [not_branch_ret]; exact Hn).
  - destruct (unreach_elim p) as [p' r'] eqn:E. injection Hu as <- _. cbn [not_branch_ret].
    exact (IHp p' r' (conj Hn eq_refl)).
  - destruct (unreach_elim p1) as [p1' r1] eqn:E1. unfold is_true in Hn.
    apply Bool.andb_true_iff in Hn as [Hn1 Hn2].
    destruct (decide (r1 <> None)).
    + injection Hu as <- _. exact (IHp1 p1' r1 (conj Hn1 eq_refl)).
    + destruct (unreach_elim p2) as [p2' r2] eqn:E2. injection Hu as <- _. cbn [not_branch_ret].
      unfold is_true. apply Bool.andb_true_iff. split; [exact (IHp1 p1' r1 (conj Hn1 eq_refl))|exact (IHp2 p2' r2 (conj Hn2 eq_refl))].
  - destruct (unreach_elim p1) as [p1' r1] eqn:E1, (unreach_elim p2) as [p2' r2] eqn:E2.
    injection Hu as <- _. cbn [not_branch_ret]. unfold is_true in *.
    apply Bool.andb_true_iff in Hn as [Hn1 Hn2]. apply Bool.negb_true_iff in Hn1, Hn2.
    apply Bool.andb_true_iff. split; apply Bool.negb_true_iff.
    + destruct (has_return p1') eqn:C; [|reflexivity]. exfalso.
      apply (unreach_elim_preserve_has_return p1 p1' r1); [split; [rewrite Hn1; discriminate|exact E1]|exact C].
    + destruct (has_return p2') eqn:C; [|reflexivity]. exfalso.
      apply (unreach_elim_preserve_has_return p2 p2' r2); [split; [rewrite Hn2; discriminate|exact E2]|exact C].
  - destruct (unreach_elim p) as [p' r'] eqn:E. injection Hu as <- _. cbn [not_branch_ret]. unfold is_true in *.
    apply Bool.negb_true_iff in Hn. apply Bool.negb_true_iff.
    destruct (has_return p') eqn:C; [|reflexivity]. exfalso.
    apply (unreach_elim_preserve_has_return p p' r'); [split; [rewrite Hn; discriminate|exact E]|exact C].
  - destruct o as [[rts [[w hdl]|]]|].
    + destruct (unreach_elim hdl) as [h' rh] eqn:E. injection Hu as <- _. cbn [not_branch_ret]. unfold is_true in *.
      apply Bool.negb_true_iff in Hn. apply Bool.negb_true_iff.
      destruct (has_return h') eqn:C; [|reflexivity]. exfalso.
      apply (unreach_elim_preserve_has_return hdl h' rh); [split; [rewrite Hn; discriminate|exact E]|exact C].
    + injection Hu as <- _. exact Hn.
    + injection Hu as <- _. exact Hn.
Qed.

End VarProg.
Section Aux.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_replicate_const" *)
Theorem evaluate_replicate_const : forall n s,
  OPT_MMAP (eval s) (REPLICATE n (@Const a (n2w 0))) = SOME (REPLICATE n (Word (n2w 0))).
Proof.
  intros n s. induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite !(proj2 (REPLICATE_thm _ _)). cbn [OPT_MMAP eval]. rewrite IH. reflexivity.
Qed.

Lemma MAX_LIST_le_i (l : list N) m : (forall x, In x l -> x <= m) -> MAX_LIST l <= m.
Proof.
  induction l as [|y l IH]; intros H; cbn [MAX_LIST]; [lia|]. unfold MAX.
  pose proof (H y (or_introl eq_refl)). assert (MAX_LIST l <= m) by (apply IH; intros; apply H; right; assumption).
  destruct (N.ltb_spec y (MAX_LIST l)); lia.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "max_list_genlist_add_suc_val" *)
Theorem max_list_genlist_add_suc_val : forall n k,
  n <> 0 -> MAX_LIST (GENLIST (fun x => SUC x + k) n) = n + k.
Proof.
  intros n k Hn. apply N.le_antisymm.
  - apply MAX_LIST_le_i. intros x Hx. apply In_GENLIST_iff in Hx as (i & Hi & ->). lia.
  - apply MAX_LIST_ge_i, In_GENLIST_iff. exists (n - 1). split; [lia|]. lia.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "update_list_locals_not_vars_eval_eq" *)
Theorem update_list_locals_not_vars_eval_eq : forall vs s res (e : exp a) (vals : list (word_lab a)),
  (forall x, MEM x vs -> ~ MEM x (var_cexp e)) /\ eval s e = res /\ LENGTH vs = LENGTH vals ->
  eval (set_locals (locals s |++ ZIP (vs, vals)) s) e = res.
Proof.
  intros vs s res e vals (Hv & He & _). rewrite <- He.
  transitivity (eval (set_locals (locals s) s) e); [|rewrite set_locals_id; reflexivity].
  apply eval_locals_cong. intros n Hn. apply FLOOKUP_FUPDATE_LIST_notin. intros Hi.
  apply In_map_fst_ZIP in Hi. apply (Hv n (proj2 (MEM_In _ _) Hi)), MEM_In, Hn.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "opt_mmap_update_list_locals_not_vars_eval_eq" *)
Theorem opt_mmap_update_list_locals_not_vars_eval_eq : forall (es : list (exp a)) vs (vals : list (word_lab a)) s res,
  (forall x, MEM x vs -> ~ MEM x (FLAT (MAP var_cexp es))) /\ OPT_MMAP (eval s) es = res /\
  LENGTH vs = LENGTH vals ->
  OPT_MMAP (eval (set_locals (locals s |++ ZIP (vs, vals)) s)) es = res.
Proof.
  intros es vs vals s res (Hv & He & Hl). rewrite <- He. apply OPT_MMAP_ext_In''. intros e Hein.
  apply update_list_locals_not_vars_eval_eq. split; [|split; [reflexivity|exact Hl]].
  intros x Hx Hm. apply (Hv x Hx), MEM_In. eapply In_FLAT_MAP; [exact Hein|apply MEM_In, Hm].
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "opt_mmap_update_list_locals_not_vars_eval_eq'" *)
Theorem opt_mmap_update_list_locals_not_vars_eval_eq' : forall (es : list (exp a)) vs (ws : list (word_lab a))
    (vals : list (word_lab a)) s locs,
  (forall x, MEM x vs -> ~ MEM x (FLAT (MAP var_cexp es))) /\ LENGTH vs = LENGTH vals ->
  OPT_MMAP (eval (set_locals (locs |++ ZIP (vs, vals)) s)) es = OPT_MMAP (eval (set_locals locs s)) es.
Proof.
  intros es vs ws vals s locs [Hv Hl].
  pose proof (opt_mmap_update_list_locals_not_vars_eval_eq es vs vals (set_locals locs s) _
                (conj Hv (conj eq_refl Hl))) as H.
  rewrite sl_locals, sl_sl in H. exact H.
Qed.

End Aux.

Section AuxFmap.
Context {K V : Type} `{HK : EqDecision K}.

Lemma FDOM_FEMPTY_ZIP (zs : list K) (vs : list V) x :
  LENGTH zs = LENGTH vs -> (x IN FDOM (FEMPTY |++ ZIP (zs, vs)) <-> In x zs).
Proof.
  intros Hl. unfold_sets. rewrite FDOM_FUPDATE_LIST_iff, In_ZIP_fst_iff by exact Hl. unfold_sets; unfold FDOM.
  rewrite FLOOKUP_EMPTY. tauto.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "FDIFF_fupdate_list_empty_flookup_var" *)
Local Theorem FDIFF_fupdate_list_empty_flookup_var : forall (fm : fmap K V) zs (val val2 : V) fm' x v,
  FDIFF (fm |++ ZIP (zs, REPLICATE (LENGTH zs) val)) (FDOM (FEMPTY |++ ZIP (zs, REPLICATE (LENGTH zs) val2))) ⊑ fm' /\
  FLOOKUP fm x = SOME v /\
  ~ MEM x zs ->
  FLOOKUP fm' x = SOME v.
Proof.
  intros fm zs val val2 fm' x v (Hs & Hx & Hn). apply Hs. rewrite FLOOKUP_FDIFF.
  destruct (classical_dec _) as [Hi|_].
  - apply FDOM_FEMPTY_ZIP in Hi; [|rewrite LENGTH_REPLICATE; reflexivity]. exfalso; apply Hn, MEM_In, Hi.
  - rewrite FLOOKUP_FUPDATE_LIST_notin; [exact Hx|]. rewrite In_ZIP_fst_iff by (rewrite LENGTH_REPLICATE; reflexivity).
    intros Hi; apply Hn, MEM_In, Hi.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "FDIFF_fupdate_list_empty_flookup" *)
Local Theorem FDIFF_fupdate_list_empty_flookup : forall xs (fm : fmap K V) zs (val val2 : V) fm' vs,
  FDIFF (fm |++ ZIP (zs, REPLICATE (LENGTH zs) val)) (FDOM (FEMPTY |++ ZIP (zs, REPLICATE (LENGTH zs) val2))) ⊑ fm' /\
  OPT_MMAP (FLOOKUP fm) xs = SOME vs /\
  (forall x, MEM x xs -> ~ MEM x zs) ->
  OPT_MMAP (FLOOKUP fm') xs = SOME vs.
Proof.
  intros xs fm zs val val2 fm' vs (Hs & Ho & Hn). rewrite <- Ho. apply OPT_MMAP_ext_In''. intros x Hx.
  destruct (OPT_MMAP_In_SOME _ _ _ x Ho Hx) as [y Hy]. rewrite Hy.
  apply (FDIFF_fupdate_list_empty_flookup_var fm zs val val2 fm' x y). split; [exact Hs|]. split; [exact Hy|].
  apply Hn, MEM_In, Hx.
Qed.

Lemma FOLDL_res_var_lookup_gen (l : fmap K V) ns (f : K -> option V) x :
  FLOOKUP (FOLDL res_var l (ZIP (ns, MAP f ns))) x =
  if in_dec (fun u w => decide (u = w)) x ns then f x else FLOOKUP l x.
Proof.
  revert l; induction ns as [|n ns IH]; intros l; [reflexivity|].
  cbn [MAP List.map]. change (ZIP (n :: ns, f n :: MAP f ns)) with ((n, f n) :: ZIP (ns, MAP f ns)).
  cbn [FOLDL]. rewrite IH. destruct (in_dec _ x ns) as [Hi|Hi]; destruct (in_dec _ x (n :: ns)) as [Hj|Hj];
    cbn [In] in *; try reflexivity; try tauto.
  all: destruct (f n) eqn:Ef; cbn [res_var]; fm_lookup; destruct (decide (n = x)); subst; try tauto; congruence.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "FOLDL_res_var_ZIP_lookup_var" *)
Local Theorem FOLDL_res_var_ZIP_lookup_var : forall (l : fmap K V) ns l' l1 x v,
  FOLDL res_var l (ZIP (ns, MAP (FLOOKUP l') ns)) ⊑ l1 /\
  FLOOKUP l x = SOME v /\
  ~ MEM x ns ->
  FLOOKUP l1 x = SOME v.
Proof.
  intros l ns l' l1 x v (Hs & Hx & Hn). apply Hs. rewrite FOLDL_res_var_lookup_gen.
  destruct (in_dec _ x ns) as [Hi|]; [exfalso; apply Hn, MEM_In, Hi|exact Hx].
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "FOLDL_res_var_ZIP_lookup" *)
Local Theorem FOLDL_res_var_ZIP_lookup : forall (l : fmap K V) ns l' l1 xs vs,
  FOLDL res_var l (ZIP (ns, MAP (FLOOKUP l') ns)) ⊑ l1 /\
  OPT_MMAP (FLOOKUP l) xs = SOME vs /\
  (forall x, MEM x xs -> ~ MEM x ns) ->
  OPT_MMAP (FLOOKUP l1) xs = SOME vs.
Proof.
  intros l ns l' l1 xs vs (Hs & Ho & Hn). rewrite <- Ho. apply OPT_MMAP_ext_In''. intros x Hx.
  destruct (OPT_MMAP_In_SOME _ _ _ x Ho Hx) as [y Hy]. rewrite Hy.
  apply (FOLDL_res_var_ZIP_lookup_var l ns l' l1 x y). split; [exact Hs|]. split; [exact Hy|].
  apply Hn, MEM_In, Hx.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "submap_finish_flookup" *)
Local Theorem submap_finish_flookup : forall (fm : fmap K V) q (l : list V) fm' ns,
  (forall x y, ~ MEM x q /\ ~ MEM x ns /\ FLOOKUP fm x = SOME y -> FLOOKUP fm' x = SOME y) /\
  (forall x, MEM x q -> ~ MEM x ns) /\
  ALL_DISTINCT q /\
  OPT_MMAP (FLOOKUP fm') q = SOME l ->
  fm |++ ZIP (q, l) ⊑ FOLDL res_var fm' (ZIP (ns, MAP (FLOOKUP fm) ns)).
Proof.
  intros fm q l fm' ns (H1 & H2 & Hd & Ho) k v Hk. rewrite FOLDL_res_var_lookup_gen.
  pose proof (opt_mmap_length_eq _ _ _ Ho) as Hl.
  destruct (in_dec _ k ns) as [Hi|Hi].
  - assert (Hq : ~ In k q) by (intros Hq; apply (H2 k (proj2 (MEM_In _ _) Hq)), MEM_In, Hi).
    rewrite FLOOKUP_FUPDATE_LIST_notin in Hk; [exact Hk|]. rewrite In_ZIP_fst_iff by exact Hl. exact Hq.
  - destruct (in_dec (fun u w => decide (u = w)) k q) as [Hq|Hq].
    + assert (E : FLOOKUP (fm |++ ZIP (q, l)) k = FLOOKUP (fm' |++ ZIP (q, l)) k)
        by (apply FLOOKUP_FUPDATE_LIST_in; rewrite In_ZIP_fst_iff by exact Hl; exact Hq).
      rewrite E in Hk. rewrite <- Hk. clear -Ho Hd Hq HK.
      revert l Ho. induction q as [|y q IH]; intros l Ho; [destruct Hq|].
      cbn [OPT_MMAP] in Ho. destruct (FLOOKUP fm' y) as [w'|] eqn:Ey; [|discriminate].
      destruct (OPT_MMAP (FLOOKUP fm') q) as [l'|] eqn:Eq; [|discriminate]. cbn in Ho. injection Ho as <-.
      cbn [ALL_DISTINCT] in Hd. apply andb_prop in Hd as [Hny Hd].
      change (ZIP (y :: q, w' :: l')) with ((y, w') :: ZIP (q, l')). cbn [FUPDATE_LIST FOLDL].
      change (FOLDL FUPDATE (fm' |+ (y, w')) (ZIP (q, l'))) with ((fm' |+ (y, w')) |++ ZIP (q, l')).
      destruct Hq as [<-|Hq].
      * rewrite FLOOKUP_FUPDATE_LIST_notin.
        -- rewrite FLOOKUP_UPDATE. destruct (decide (y = y)); congruence.
        -- intros Hi. apply In_map_fst_ZIP, MEM_In in Hi. rewrite Hi in Hny. discriminate.
      * rewrite (IH Hd Hq l' eq_refl). apply FLOOKUP_FUPDATE_LIST_in.
        rewrite In_ZIP_fst_iff by exact (opt_mmap_length_eq _ _ _ Eq). exact Hq.
    + rewrite FLOOKUP_FUPDATE_LIST_notin in Hk by (rewrite In_ZIP_fst_iff by exact Hl; exact Hq).
      apply (H1 k v). split; [intros Hm; apply Hq, MEM_In, Hm|]. split; [intros Hm; apply Hi, MEM_In, Hm|exact Hk].
Qed.

End AuxFmap.
Section InlineAux.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma rel_code_eq s s1 : state_rel_code s s1 -> locals_strong_rel s s1 -> s1 = set_code (code s1) s.
Proof.
  destruct s, s1; intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) H10;
    unfold locals_strong_rel in H10; cbn in *; subst; reflexivity.
Qed.

Lemma sh_mem_op_set_code op v (addr : word a) c s :
  sh_mem_op op v addr (set_code c s) =
  (fst (sh_mem_op op v addr s), set_code c (snd (sh_mem_op op v addr s))).
Proof.
  destruct op; cbn [sh_mem_op]; unfold sh_mem_load, sh_mem_store; destruct s; cbn;
    repeat match goal with |- context [match ?x with _ => _ end] =>
      destruct x eqn:?; cbn beta iota zeta end; reflexivity.
Qed.

Definition is_simple (p : prog a) : bool :=
  match p with
  | Dec _ _ _ | Seq _ _ | If _ _ _ | While _ _ | Call _ _ _ => false
  | _ => true
  end.

Lemma evaluate_set_code_simple (p : prog a) c s :
  is_simple p = true ->
  evaluate (p, set_code c s) = (fst (evaluate (p, s)), set_code c (snd (evaluate (p, s)))).
Proof.
  intros Hs. destruct p; try discriminate Hs.
  all: rewrite !evaluate_unfold; cbn [evaluate_body]; rewrite ?eval_set_code.
  all: try (rewrite sh_mem_op_set_code).
  all: destruct s; cbn;
    repeat match goal with |- context [match ?x with _ => _ end] =>
      destruct x eqn:?; cbn beta iota zeta end; try reflexivity.
  all: match goal with |- context [sh_mem_op ?op ?v ?w (set_code ?c ?s0)] =>
         rewrite (sh_mem_op_set_code op v w c s0); destruct (sh_mem_op op v w s0); reflexivity end.
Qed.

(** Post-condition of [inline_prog_correct] (Galette-only name). *)
Definition inl_post (inl_fs : fmap funname (list varname * prog a)) (r : option (result a)) s' s1' : Prop :=
  state_rel_code s' s1' /\
  code_inl_rel inl_fs s' s1' /\
  match r with
  | NONE => locals_strong_rel s' s1'
  | SOME (Break n) => locals_strong_rel s' s1'
  | SOME (Continue n) => locals_strong_rel s' s1'
  | SOME Error => False
  | _ => True
  end.

Lemma code_inl_rel_code inl_fs s t s' t' :
  code s' = code s -> code t' = code t -> code_inl_rel inl_fs s t -> code_inl_rel inl_fs s' t'.
Proof. intros E1 E2 H. unfold code_inl_rel in *. rewrite E1, E2. exact H. Qed.

Lemma state_rel_code_refl s : state_rel_code s s.
Proof. repeat split. Qed.

Lemma state_rel_code_set_code s c : state_rel_code s (set_code c s).
Proof. repeat split. Qed.

Lemma state_rel_code_sl s t l1 l2 : state_rel_code s t -> state_rel_code (set_locals l1 s) (set_locals l2 t).
Proof. unfold state_rel_code; cbn; tauto. Qed.

Lemma state_rel_code_trans s t u : state_rel_code s t -> state_rel_code t u -> state_rel_code s u.
Proof. unfold state_rel_code; intuition congruence. Qed.

Lemma state_rel_imp_code s t : state_rel s t -> state_rel_code s t.
Proof. unfold state_rel, state_rel_code; tauto. Qed.

Lemma state_rel_code_sl_l s t l : state_rel_code s t -> state_rel_code (set_locals l s) t.
Proof. unfold state_rel_code; cbn; tauto. Qed.

Lemma state_rel_code_sl_r s t l : state_rel_code s t -> state_rel_code s (set_locals l t).
Proof. unfold state_rel_code; cbn; tauto. Qed.

Lemma inl_post_set_code inl_fs r s s' c :
  r <> SOME Error -> code s' = code s -> code_inl_rel inl_fs s (set_code c s) ->
  inl_post inl_fs r s' (set_code c s').
Proof.
  intros Hne E Hc. split; [apply state_rel_code_set_code|]. split.
  - apply (code_inl_rel_code inl_fs s (set_code c s)); [exact E|reflexivity|exact Hc].
  - destruct r as [[]|]; try exact I; try reflexivity. congruence.
Qed.

(** The induction predicate of [inline_prog_correct] (Galette-only). *)
Definition inl_P (p : prog a) s : Prop :=
  forall r s' inl_fs s1 inl_bag,
    evaluate (p, s) = (r, s') ->
    r <> SOME Error ->
    inl_fs ⊑ code s ->
    inl_bag ⊑ inl_fs ->
    state_rel_code s s1 ->
    locals_strong_rel s s1 ->
    code_inl_rel inl_fs s s1 ->
    exists s1', evaluate (inline_prog inl_bag p, s1) = (r, s1') /\ inl_post inl_fs r s' s1'.

Lemma inl_simple (p : prog a) s : is_simple p = true -> inl_P p s.
Proof.
  intros Hsim r s' inl_fs s1 bag H Hne Hfs Hbag Hsr Hls Hci.
  assert (Hid : inline_prog bag p = p) by (destruct p; try discriminate Hsim; apply inline_prog_def).
  rewrite Hid, (rel_code_eq s s1 Hsr Hls), (evaluate_set_code_simple p _ s Hsim), H. cbn [fst snd].
  eexists; split; [reflexivity|]. apply (inl_post_set_code inl_fs r s s'); [exact Hne| |].
  - exact (evaluate_code_invariant p s r s' H).
  - rewrite <- (rel_code_eq s s1 Hsr Hls). exact Hci.
Qed.

Lemma eval_rel s s1 : state_rel_code s s1 -> locals_strong_rel s s1 -> eval s1 = eval s.
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) H10. symmetry. apply eval_state_cong; assumption.
Qed.

Lemma inl_post_cont inl_fs (o : option (result a)) st st1 :
  inl_post inl_fs o st st1 -> cres o = true -> locals_strong_rel st st1.
Proof. intros (_ & _ & H) Hc. destruct o as [[]|]; try discriminate Hc; exact H. Qed.

Lemma inl_post_sl inl_fs (o : option (result a)) st st1 l1 l2 :
  inl_post inl_fs o st st1 -> (cres o = true -> l1 = l2) ->
  inl_post inl_fs o (set_locals l1 st) (set_locals l2 st1).
Proof.
  intros (H1 & H2 & H3) H. split; [apply state_rel_code_sl, H1|]. split.
  - apply (code_inl_rel_code inl_fs st st1); [reflexivity|reflexivity|exact H2].
  - destruct o as [[]|]; try exact H3; try exact I; unfold locals_strong_rel; rewrite !sl_locals; apply H; reflexivity.
Qed.

Lemma inl_Dec v e (p : prog a) s :
  (forall p' s', eval_lt (p', s') (Dec v e p, s) -> inl_P p' s') -> inl_P (Dec v e p) s.
Proof.
  intros IH r s' inl_fs s1 bag H Hne Hfs Hbag Hsr Hls Hci.
  rewrite (proj1 (proj2 inline_prog_def)).
  unfold_eval_in H. destruct (eval s e) as [w|] eqn:He; [|injection H as <- _; congruence].
  destruct (evaluate (p, set_locals (locals s |+ (v, w)) s)) as [o st] eqn:E0. injection H as <- <-.
  destruct (IH p (set_locals (locals s |+ (v, w)) s) ltac:(lt_tac) o st inl_fs (set_locals (locals s1 |+ (v, w)) s1) bag E0 Hne
              ltac:(rewrite sl_code; exact Hfs) Hbag ltac:(apply state_rel_code_sl, Hsr)
              ltac:(unfold locals_strong_rel in *; rewrite !sl_locals, Hls; reflexivity)
              ltac:(apply (code_inl_rel_code inl_fs s s1); [reflexivity|reflexivity|exact Hci]))
    as (st1 & Ht1 & Hp).
  ev_goal. rewrite (eval_rel s s1 Hsr Hls), He. cbv beta iota. rewrite Ht1. cbv beta iota.
  eexists; split; [reflexivity|]. apply inl_post_sl; [exact Hp|].
  intros Hc. pose proof (inl_post_cont _ _ _ _ Hp Hc) as Hl. unfold locals_strong_rel in *. rewrite Hl, Hls.
  reflexivity.
Qed.

Lemma inl_Seq (c1 c2 : prog a) s :
  (forall p' s', eval_lt (p', s') (Seq c1 c2, s) -> inl_P p' s') -> inl_P (Seq c1 c2) s.
Proof.
  intros IH r s' inl_fs s1 bag H Hne Hfs Hbag Hsr Hls Hci.
  rewrite (proj1 (proj2 (proj2 inline_prog_def))). cbv zeta.
  unfold_eval_in H. destruct (evaluate (c1, s)) as [o st] eqn:E1.
  destruct o as [x|].
  - injection H as <- <-.
    destruct (IH c1 s ltac:(lt_tac) (SOME x) st inl_fs s1 bag E1 Hne Hfs Hbag Hsr Hls Hci) as (st1 & Ht1 & Hp).
    ev_goal. rewrite Ht1. eexists; split; [reflexivity|exact Hp].
  - destruct (IH c1 s ltac:(lt_tac) NONE st inl_fs s1 bag E1 ltac:(discriminate) Hfs Hbag Hsr Hls Hci)
      as (st1 & Ht1 & Hs1 & Hc1 & Hl1).
    pose proof (evaluate_code_invariant c1 s _ _ E1) as Ec.
    destruct (IH c2 st ltac:(lt_tac) r s' inl_fs st1 bag H Hne ltac:(rewrite Ec; exact Hfs) Hbag Hs1 Hl1 Hc1)
      as (st2 & Ht2 & Hp2).
    ev_goal. rewrite Ht1. cbv beta iota. rewrite Ht2. eexists; split; [reflexivity|exact Hp2].
Qed.

Lemma inl_If e (c1 c2 : prog a) s :
  (forall p' s', eval_lt (p', s') (If e c1 c2, s) -> inl_P p' s') -> inl_P (If e c1 c2) s.
Proof.
  intros IH r s' inl_fs s1 bag H Hne Hfs Hbag Hsr Hls Hci.
  rewrite (proj1 (proj2 (proj2 (proj2 inline_prog_def)))). cbv zeta.
  unfold_eval_in H. destruct (eval s e) as [[w]|] eqn:He; [|injection H as <- _; congruence].
  ev_goal. rewrite (eval_rel s s1 Hsr Hls), He. cbv beta iota.
  destruct (negb (bool_decide (w = n2w 0))) eqn:Ew.
  - destruct (IH c1 s ltac:(lt_tac) r s' inl_fs s1 bag H Hne Hfs Hbag Hsr Hls Hci) as (st1 & Ht1 & Hp).
    rewrite Ht1. eexists; split; [reflexivity|exact Hp].
  - destruct (IH c2 s ltac:(lt_tac) r s' inl_fs s1 bag H Hne Hfs Hbag Hsr Hls Hci) as (st1 & Ht1 & Hp).
    rewrite Ht1. eexists; split; [reflexivity|exact Hp].
Qed.

Lemma inl_While e (c : prog a) s :
  (forall p' s', eval_lt (p', s') (While e c, s) -> inl_P p' s') -> inl_P (While e c) s.
Proof.
  intros IH r s' inl_fs s1 bag H Hne Hfs Hbag Hsr Hls Hci.
  rewrite (proj1 (proj2 (proj2 (proj2 (proj2 inline_prog_def))))).
  unfold_eval_in H. destruct (eval s e) as [[w]|] eqn:He; [|injection H as <- _; congruence].
  ev_goal. rewrite (eval_rel s s1 Hsr Hls), He. cbv beta iota.
  destruct (negb (bool_decide (w = n2w 0))) eqn:Ew.
  2: { injection H as <- <-. eexists; split; [reflexivity|]. split; [exact Hsr|]. split; [exact Hci|exact Hls]. }
  assert (Hck : clock s1 = clock s) by (symmetry; apply Hsr).
  rewrite Hck. destruct (clock s =? 0) eqn:Ec.
  { injection H as <- <-. eexists; split; [reflexivity|]. split; [apply state_rel_code_sl, Hsr|].
    split; [|exact I]. apply (code_inl_rel_code inl_fs s s1); [reflexivity|reflexivity|exact Hci]. }
  destruct (evaluate (c, dec_clock s)) as [o st] eqn:E3. cbv beta iota in H.
  assert (Hoe : o <> SOME Error) by (intros ->; injection H as <- _; apply Hne; reflexivity).
  assert (Hsr' : state_rel_code (dec_clock s) (dec_clock s1)) by (unfold state_rel_code in *; cbn; intuition congruence).
  destruct (IH c (dec_clock s) ltac:(lt_tac) o st inl_fs (dec_clock s1) bag E3 Hoe Hfs Hbag Hsr' Hls
              ltac:(apply (code_inl_rel_code inl_fs s s1); [reflexivity|reflexivity|exact Hci]))
    as (st1 & Ht1 & Hp). rewrite Ht1.
  pose proof (evaluate_code_invariant c _ _ _ E3) as Ec3.
  assert (Hrec : evaluate (While e c, st) = (r, s') -> locals_strong_rel st st1 ->
            exists s1', evaluate (While e (inline_prog bag c), st1) = (r, s1') /\ inl_post inl_fs r s' s1').
  { intros Hw Hl. destruct Hp as (Hs1 & Hc1 & _).
    destruct (IH (While e c) st ltac:(lt_tac) r s' inl_fs st1 bag Hw Hne ltac:(rewrite Ec3; exact Hfs) Hbag Hs1 Hl Hc1)
      as (st2 & Ht2 & Hp2). rewrite (proj1 (proj2 (proj2 (proj2 (proj2 inline_prog_def))))) in Ht2.
    eauto. }
  destruct o as [[| |n|n|rv|eid|f]|]; cbv beta iota in H |- *.
  - exfalso; apply Hoe; reflexivity.
  - injection H as <- <-. eexists; split; [reflexivity|exact Hp].
  - destruct n as [|pn]; injection H as <- <-; eexists; (split; [reflexivity|]);
      destruct Hp as (Hs1 & Hc1 & Hl1); (split; [exact Hs1|]); (split; [exact Hc1|exact Hl1]).
  - destruct n as [|pn].
    + exact (Hrec H (inl_post_cont _ _ _ _ Hp eq_refl)).
    + injection H as <- <-; eexists; (split; [reflexivity|]);
        destruct Hp as (Hs1 & Hc1 & Hl1); (split; [exact Hs1|]); (split; [exact Hc1|exact Hl1]).
  - injection H as <- <-. eexists; split; [reflexivity|exact Hp].
  - injection H as <- <-. eexists; split; [reflexivity|exact Hp].
  - injection H as <- <-. eexists; split; [reflexivity|exact Hp].
  - exact (Hrec H (inl_post_cont _ _ _ _ Hp eq_refl)).
Qed.

End InlineAux.

Section InlineCall.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Definition map_ctyp (g : prog a -> prog a) (ctyp : option (list varname * option (word a * prog a))) :=
  match ctyp with
  | None => None
  | Some (x, None) => Some (x, None)
  | Some (x, Some (w, hdl)) => Some (x, Some (w, g hdl))
  end.

Lemma inl_post_nc inl_fs (r : option (result a)) (st st1 : state a ffi_t) :
  cres r = false -> r <> SOME Error -> state_rel_code st st1 -> code_inl_rel inl_fs st st1 ->
  inl_post inl_fs r st st1.
Proof.
  intros Hc Hne Hs Hci. split; [exact Hs|]. split; [exact Hci|].
  destruct r as [[]|]; try discriminate Hc; try exact I. congruence.
Qed.

Lemma inl_call_plain ctyp f (args : list (exp a)) s bag inl_fs s1 r s' :
  (forall p' s', eval_lt (p', s') (Call ctyp f args, s) -> inl_P p' s') ->
  evaluate (Call ctyp f args, s) = (r, s') -> r <> SOME Error -> inl_fs ⊑ code s -> bag ⊑ inl_fs ->
  state_rel_code s s1 -> locals_strong_rel s s1 -> code_inl_rel inl_fs s s1 ->
  exists s1', evaluate (Call (map_ctyp (inline_prog bag) ctyp) f args, s1) = (r, s1') /\ inl_post inl_fs r s' s1'.
Proof.
  intros IH H Hne Hfs Hbag Hsr Hls Hci.
  unfold_eval_in H. ev_goal. rewrite (eval_rel s s1 Hsr Hls).
  destruct (OPT_MMAP (eval s) args) as [argv|] eqn:Ha; [|injection H as <- _; congruence].
  unfold lookup_code in H |- *.
  destruct (FLOOKUP (code s) f) as [[ns prog]|] eqn:Hf; [|injection H as <- _; congruence].
  destruct (Hci f ns prog Hf) as (bag' & Hbag' & Hf1). rewrite Hf1.
  destruct ((LENGTH ns =? LENGTH argv) && ALL_DISTINCT ns)%bool eqn:Hl; [|injection H as <- _; congruence].
  cbv beta iota in H |- *.
  assert (Hnd : match map_ctyp (inline_prog bag) ctyp with NONE => false | SOME (rts, _) => negb (ALL_DISTINCT rts) end =
                match ctyp with NONE => false | SOME (rts, _) => negb (ALL_DISTINCT rts) end)
    by (destruct ctyp as [[? [[? ?]|]]|]; reflexivity).
  rewrite Hnd. destruct (match ctyp with NONE => false | SOME (rts, _) => negb (ALL_DISTINCT rts) end) eqn:Hd;
    [injection H as <- _; congruence|].
  assert (Hck : clock s1 = clock s) by (symmetry; apply Hsr). rewrite Hck.
  destruct (clock s =? 0) eqn:Ec.
  { injection H as <- <-. eexists; split; [reflexivity|]. apply inl_post_nc; [reflexivity|discriminate| |].
    - apply state_rel_code_sl, Hsr.
    - apply (code_inl_rel_code inl_fs s s1); [reflexivity|reflexivity|exact Hci]. }
  destruct (evaluate (prog, set_locals (FEMPTY |++ ZIP (ns, argv)) (dec_clock s))) as [q st] eqn:Eq.
  assert (Hqe : q <> SOME Error) by (intros ->; injection H as <- _; congruence).
  pose proof (evaluate_code_invariant _ _ _ _ Eq) as Ecq. rewrite sl_code, sl_code_dec_clock in Ecq.
  destruct (IH prog (set_locals (FEMPTY |++ ZIP (ns, argv)) (dec_clock s)) ltac:(lt_tac) q st inl_fs
              (set_locals (FEMPTY |++ ZIP (ns, argv)) (dec_clock s1)) bag' Eq Hqe
              ltac:(rewrite sl_code; exact Hfs) Hbag'
              ltac:(apply state_rel_code_sl; unfold state_rel_code in *; cbn; intuition congruence)
              ltac:(reflexivity)
              ltac:(apply (code_inl_rel_code inl_fs s s1); [reflexivity|reflexivity|exact Hci]))
    as (st1 & Ht1 & Hp). rewrite Ht1.
  pose proof (evaluate_code_invariant _ _ _ _ Ht1) as Ecq1. rewrite sl_code, sl_code_dec_clock in Ecq1.
  destruct Hp as (Hs1 & Hc1 & _).
  assert (Hci1 : code_inl_rel inl_fs st st1) by (apply (code_inl_rel_code inl_fs s s1); assumption).
  assert (Hpost_nc : forall r0, cres r0 = false -> r0 <> SOME Error ->
            inl_post inl_fs r0 (empty_locals st) (empty_locals st1)).
  { intros r0 H1 H2. apply inl_post_nc; [exact H1|exact H2|apply state_rel_code_sl, Hs1|].
    apply (code_inl_rel_code inl_fs st st1); [reflexivity|reflexivity|exact Hci1]. }
  destruct q as [[| |n|n|retvs|eid|ff]|]; cbv beta iota in H |- *;
    try (injection H as <- _; congruence).
  - injection H as <- <-. eexists; split; [reflexivity|]. apply Hpost_nc; [reflexivity|discriminate].
  - destruct ctyp as [[rts h]|].
    + cbn [map_ctyp]. destruct h as [[w hdl]|]; cbv beta iota in H |- *.
      all: destruct (negb (LENGTH retvs =? LENGTH rts)) eqn:El; [injection H as <- _; congruence|].
      all: rewrite <- Hls; destruct (OPT_MMAP (FLOOKUP (locals s)) rts) eqn:Eo; [|injection H as <- _; congruence].
      all: injection H as <- <-; eexists; split; [reflexivity|].
      all: split; [apply state_rel_code_sl, Hs1|]; split;
           [apply (code_inl_rel_code inl_fs st st1); [reflexivity|reflexivity|exact Hci1]|reflexivity].
    + cbn [map_ctyp]. injection H as <- <-. eexists; split; [reflexivity|]. apply Hpost_nc; [reflexivity|discriminate].
  - destruct ctyp as [[rts [[w hdl]|]]|]; cbn [map_ctyp]; cbv beta iota in H |- *.
    + destruct (bool_decide (eid = w)) eqn:Ew.
      * pose proof (evaluate_code_invariant _ _ _ _ Eq) as _.
        destruct (IH hdl (set_locals (locals s) st) ltac:(lt_tac) r s' inl_fs (set_locals (locals s1) st1) bag H Hne
                    ltac:(rewrite sl_code, Ecq; exact Hfs) Hbag ltac:(apply state_rel_code_sl, Hs1)
                    ltac:(unfold locals_strong_rel in *; rewrite !sl_locals; exact Hls)
                    ltac:(apply (code_inl_rel_code inl_fs st st1); [reflexivity|reflexivity|exact Hci1]))
          as (st2 & Ht2 & Hp2). rewrite Ht2. eauto.
      * injection H as <- <-. eexists; split; [reflexivity|]. apply Hpost_nc; [reflexivity|discriminate].
    + injection H as <- <-. eexists; split; [reflexivity|]. apply Hpost_nc; [reflexivity|discriminate].
    + injection H as <- <-. eexists; split; [reflexivity|]. apply Hpost_nc; [reflexivity|discriminate].
  - injection H as <- <-. eexists; split; [reflexivity|]. apply Hpost_nc; [reflexivity|discriminate].
Qed.

End InlineCall.

Section InlineTail.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma genlist_gt_i (m n x : N) : In x (GENLIST (fun x => SUC x + m) n) -> m < x.
Proof. intros H. apply In_GENLIST_iff in H as (i & _ & ->). lia. Qed.

Lemma MAX_ge_l (m n : N) : m <= MAX m n.
Proof. unfold MAX. destruct (N.ltb_spec m n); lia. Qed.
Lemma MAX_ge_r (m n : N) : n <= MAX m n.
Proof. unfold MAX. destruct (N.ltb_spec m n); lia. Qed.

Lemma genlist_distinct_i (m n : N) : ALL_DISTINCT (GENLIST (fun x => SUC x + m) n).
Proof. apply ALL_DISTINCT_GENLIST. intros m1 m2 (_ & _ & E). lia. Qed.

Lemma tmp_vars_facts (args : list (exp a)) (args_vname : list varname) :
  let tmp_vars := GENLIST (fun x => SUC x + MAX (MAX_LIST (FLAT (MAP var_cexp args))) (MAX_LIST args_vname))
                    (LENGTH args_vname) in
  ALL_DISTINCT tmp_vars /\ LENGTH tmp_vars = LENGTH args_vname /\
  (forall x, MEM x tmp_vars -> ~ MEM x args_vname) /\
  (forall x, MEM x tmp_vars -> ~ MEM x (FLAT (MAP var_cexp args))).
Proof.
  cbv zeta. split; [apply genlist_distinct_i|]. split; [apply LENGTH_GENLIST_i|]. split.
  - intros x Hx Hm. apply MEM_In, genlist_gt_i in Hx. apply MEM_In, MAX_LIST_ge_i in Hm.
    pose proof (MAX_ge_r (MAX_LIST (FLAT (MAP var_cexp args))) (MAX_LIST args_vname)). lia.
  - intros x Hx Hm. apply MEM_In, genlist_gt_i in Hx. apply MEM_In, MAX_LIST_ge_i in Hm.
    pose proof (MAX_ge_l (MAX_LIST (FLAT (MAP var_cexp args))) (MAX_LIST args_vname)). lia.
Qed.

Lemma callee_lookup (bag inl_fs : fmap funname (list varname * prog a)) s f args_vname p0 :
  FLOOKUP bag f = SOME (args_vname, p0) -> bag ⊑ inl_fs -> inl_fs ⊑ code s ->
  FLOOKUP (code s) f = SOME (args_vname, p0).
Proof. intros H1 H2 H3. apply H3, H2, H1. Qed.

Lemma inl_call_tail f (args : list (exp a)) s bag inl_fs s1 r s' args_vname p0 ic et :
  (forall p' s', eval_lt (p', s') (Call NONE f args, s) -> inl_P p' s') ->
  evaluate (Call NONE f args, s) = (r, s') -> r <> SOME Error -> inl_fs ⊑ code s -> bag ⊑ inl_fs ->
  state_rel_code s s1 -> locals_strong_rel s s1 -> code_inl_rel inl_fs s s1 ->
  FLOOKUP bag f = SOME (args_vname, p0) ->
  unreach_elim (inline_prog (bag \\ f) p0) = (ic, et) ->
  exists s1',
    evaluate (inline_tail (arg_load
       (GENLIST (fun x => SUC x + MAX (MAX_LIST (FLAT (MAP var_cexp args))) (MAX_LIST args_vname))
          (LENGTH args_vname)) args args_vname ic), s1) = (r, s1') /\
    inl_post inl_fs r s' s1'.
Proof.
  intros IH H Hne Hfs Hbag Hsr Hls Hci Hf Hue.
  pose proof (callee_lookup bag inl_fs s f args_vname p0 Hf Hbag Hfs) as Hfc.
  destruct (tmp_vars_facts args args_vname) as (Hdt & Hlt & Htv & Hte).
  set (tmp := GENLIST _ _) in *.
  unfold_eval_in H. unfold lookup_code in H. rewrite Hfc in H.
  destruct (OPT_MMAP (eval s) args) as [argv|] eqn:Ha; [|injection H as <- _; congruence].
  destruct ((LENGTH args_vname =? LENGTH argv) && ALL_DISTINCT args_vname)%bool eqn:Hl;
    [|injection H as <- _; congruence].
  apply andb_prop in Hl as [Hl Hd]. apply N.eqb_eq in Hl.
  cbv beta iota in H. assert (Hck : clock s1 = clock s) by (symmetry; apply Hsr).
  unfold inline_tail. ev_goal. ev_goal_at (@Tick a). rewrite Hck.
  destruct (clock s =? 0) eqn:Ec.
  { injection H as <- <-. cbv beta iota. eexists; split; [reflexivity|].
    apply inl_post_nc; [reflexivity|discriminate|apply state_rel_code_sl, Hsr|].
    apply (code_inl_rel_code inl_fs s s1); [reflexivity|reflexivity|exact Hci]. }
  cbv beta iota.
  destruct (evaluate (p0, set_locals (FEMPTY |++ ZIP (args_vname, argv)) (dec_clock s))) as [q st] eqn:Eq.
  assert (Hq : r = q /\ s' = empty_locals st /\ cres q = false).
  { destruct q as [[| | | | | |]|]; cbv beta iota in H; injection H as <- <-; try congruence;
      (split; [reflexivity|split; reflexivity]). }
  destruct Hq as (-> & -> & Hcq).
  pose proof (evaluate_code_invariant _ _ _ _ Eq) as Ecq. rewrite sl_code, sl_code_dec_clock in Ecq.
  set (T0 := set_locals (FEMPTY |++ ZIP (args_vname, argv)) (dec_clock s1)).
  destruct (IH p0 (set_locals (FEMPTY |++ ZIP (args_vname, argv)) (dec_clock s)) ltac:(lt_tac) q st inl_fs
              T0 (bag \\ f) Eq Hne
              ltac:(rewrite sl_code; exact Hfs)
              ltac:(apply (SUBMAP_TRANS _ bag); split; [apply SUBMAP_DOMSUB|exact Hbag])
              ltac:(unfold T0; apply state_rel_code_sl; unfold state_rel_code in *; cbn; intuition congruence)
              ltac:(reflexivity)
              ltac:(apply (code_inl_rel_code inl_fs s s1); [reflexivity|reflexivity|exact Hci]))
    as (st1 & Ht1 & Hs1 & Hc1 & _).
  pose proof (unreach_elim_correct _ T0 q st1 ic et (conj Ht1 (conj Hne Hue))) as Ht2.
  assert (Ho : OPT_MMAP (eval (dec_clock s1)) args = SOME argv)
    by (rewrite eval_dec_clock, (eval_rel s s1 Hsr Hls); exact Ha).
  destruct (arg_load_master (dec_clock s1) args argv args_vname FEMPTY ic q st1 tmp Ho Hl Hd
              (SUBMAP_FEMPTY _) Ht2 ltac:(intros v _ Hv; unfold_sets; unfold FDOM in Hv; apply Hv; reflexivity)
              Hne Hdt ltac:(exact Hlt) Htv Hte)
    as (t' & E & Hst & _).
  unfold arg_load. rewrite E.
  eexists; split; [reflexivity|]. apply inl_post_nc; [exact Hcq|exact Hne| |].
  - apply state_rel_code_sl_l. apply (state_rel_code_trans _ st1); [exact Hs1|apply state_rel_imp_code, Hst].
  - pose proof (evaluate_code_invariant _ _ _ _ E) as Ect.
    apply (code_inl_rel_code inl_fs s s1); [rewrite <- Ecq; reflexivity|rewrite Ect; reflexivity|exact Hci].
Qed.

End InlineTail.

Ltac lk2 :=
  repeat first
    [ rewrite FOLDL_res_var_map_lookup
    | rewrite FLOOKUP_FUNION
    | rewrite FLOOKUP_FDIFF
    | rewrite FLOOKUP_res_var
    | rewrite FLOOKUP_UPDATE
    | rewrite DOMSUB_FLOOKUP_THM
    | rewrite FLOOKUP_EMPTY
    | match goal with |- context [FLOOKUP (?f |++ ZIP (?xs, ?ys)) ?k] =>
          rewrite (FLOOKUP_ZIP_split f xs ys k) by (rewrite ?LENGTH_MAP_i, ?LENGTH_REPLICATE in *; lia) end ].

Ltac lk2_in H :=
  repeat first
    [ rewrite FOLDL_res_var_map_lookup in H
    | rewrite FLOOKUP_FUNION in H
    | rewrite FLOOKUP_FDIFF in H
    | rewrite FLOOKUP_res_var in H
    | rewrite FLOOKUP_UPDATE in H
    | rewrite DOMSUB_FLOOKUP_THM in H
    | rewrite FLOOKUP_EMPTY in H
    | match type of H with context [FLOOKUP (?f |++ ZIP (?xs, ?ys)) ?k] =>
          rewrite (FLOOKUP_ZIP_split f xs ys k) in H by (rewrite ?LENGTH_MAP_i, ?LENGTH_REPLICATE in *; lia) end ].

Section InlineNontail.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma temp_rets_facts (args : list (exp a)) (args_vname rts : list varname) (ic : prog a) x :
  (args_vname = [] -> args = []) ->
  In x (GENLIST (fun x => SUC x + MAX_LIST [MAX_LIST rts; vmax_prog ic;
          MAX_LIST (GENLIST (fun x => SUC x + MAX (MAX_LIST (FLAT (MAP var_cexp args))) (MAX_LIST args_vname))
                      (LENGTH args_vname))]) (LENGTH rts)) ->
  ~ In x rts /\
  ~ In x (GENLIST (fun x => SUC x + MAX (MAX_LIST (FLAT (MAP var_cexp args))) (MAX_LIST args_vname))
            (LENGTH args_vname)) /\
  ~ In x args_vname /\ ~ In x (FLAT (MAP var_cexp args)) /\ ~ In x (var_prog ic).
Proof.
  intros Hnil Hx. apply genlist_gt_i in Hx.
  set (M := MAX (MAX_LIST (FLAT (MAP var_cexp args))) (MAX_LIST args_vname)) in *.
  set (tmp := GENLIST (fun x => SUC x + M) (LENGTH args_vname)) in *.
  assert (H1 : MAX_LIST rts <= MAX_LIST [MAX_LIST rts; vmax_prog ic; MAX_LIST tmp])
    by (apply MAX_LIST_ge_i; left; reflexivity).
  assert (H2 : vmax_prog ic <= MAX_LIST [MAX_LIST rts; vmax_prog ic; MAX_LIST tmp])
    by (apply MAX_LIST_ge_i; right; left; reflexivity).
  assert (H3 : MAX_LIST tmp <= MAX_LIST [MAX_LIST rts; vmax_prog ic; MAX_LIST tmp])
    by (apply MAX_LIST_ge_i; right; right; left; reflexivity).
  assert (Hav : forall y, In y args_vname \/ In y (FLAT (MAP var_cexp args)) -> y < x).
  { intros y Hy. destruct args_vname as [|v0 vs0].
    - rewrite (Hnil eq_refl) in Hy. cbn in Hy. destruct Hy as [[]|[]].
    - assert (Hm : SUC 0 + M <= MAX_LIST tmp).
      { apply MAX_LIST_ge_i. unfold tmp. apply In_GENLIST_iff. exists 0. split; [rewrite LENGTH_cons; lia|reflexivity]. }
      assert (y <= M).
      { destruct Hy as [Hy|Hy]; apply MAX_LIST_ge_i in Hy; [pose proof (MAX_ge_r (MAX_LIST (FLAT (MAP var_cexp args))) (MAX_LIST (v0 :: vs0)))
                                                         |pose proof (MAX_ge_l (MAX_LIST (FLAT (MAP var_cexp args))) (MAX_LIST (v0 :: vs0)))]; unfold M; lia. }
      lia. }
  split; [intros Hy; apply MAX_LIST_ge_i in Hy; lia|].
  split; [intros Hy; apply MAX_LIST_ge_i in Hy; lia|].
  split; [intros Hy; specialize (Hav x (or_introl Hy)); lia|].
  split; [intros Hy; specialize (Hav x (or_intror Hy)); lia|].
  intros Hy. apply MAX_LIST_ge_i in Hy. change (MAX_LIST (var_prog ic)) with (vmax_prog ic) in Hy. lia.
Qed.

Lemma transformed_clock0 (nb : bool) (p1 p2 : prog a) s :
  clock s = 0 ->
  evaluate (if nb then Seq Tick p1 else While (Const (n2w 1)) p2, s) = (SOME TimeOut, empty_locals s).
Proof.
  intros Hc. destruct nb.
  - ev_goal. ev_goal_at (@Tick a). rewrite Hc. reflexivity.
  - ev_goal. cbn [eval].
    destruct (bool_decide ((n2w 1 : word a) = n2w 0)) eqn:Eb;
      [apply bool_decide_spec in Eb; exfalso; exact (one_ne_zero_i Eb)|].
    cbn [negb]. rewrite Hc. reflexivity.
Qed.

Lemma submap_zip_ext (xs zs : list varname) (ys ws : list (word_lab a)) :
  LENGTH xs = LENGTH ys -> LENGTH zs = LENGTH ws -> (forall x, In x xs -> ~ In x zs) ->
  FEMPTY |++ ZIP (xs, ys) ⊑ (FEMPTY |++ ZIP (zs, ws)) |++ ZIP (xs, ys).
Proof.
  intros H1 H2 H3 k v Hk. lk2_in Hk. lk2. lk_cases; congruence.
Qed.

Lemma In_REPLICATE_i {A} n (x y : A) : In y (REPLICATE n x) -> y = x.
Proof.
  induction n as [|n IH] using N.peano_ind; [intros []|].
  rewrite (proj2 (REPLICATE_thm _ _)). intros [<-|H]; [reflexivity|exact (IH H)].
Qed.

Lemma inl_call_nontail f (args : list (exp a)) s bag inl_fs s1 r s' args_vname p0 ic et rts :
  (forall p' s', eval_lt (p', s') (Call (SOME (rts, NONE)) f args, s) -> inl_P p' s') ->
  evaluate (Call (SOME (rts, NONE)) f args, s) = (r, s') -> r <> SOME Error -> inl_fs ⊑ code s -> bag ⊑ inl_fs ->
  state_rel_code s s1 -> locals_strong_rel s s1 -> code_inl_rel inl_fs s s1 ->
  FLOOKUP bag f = SOME (args_vname, p0) ->
  unreach_elim (inline_prog (bag \\ f) p0) = (ic, et) ->
  let tmp_vars := GENLIST (fun x => SUC x + MAX (MAX_LIST (FLAT (MAP var_cexp args))) (MAX_LIST args_vname))
                    (LENGTH args_vname) in
  let ret_max := MAX_LIST [MAX_LIST rts; vmax_prog ic; MAX_LIST tmp_vars] in
  let temp_rets := GENLIST (fun x => SUC x + ret_max) (LENGTH rts) in
  exists s1',
    evaluate (inline_nontail (if not_branch_ret ic then Seq Tick (transform_eoc temp_rets ic)
                              else While (Const (n2w 1)) (transform_branch 0 temp_rets ic))
                rts temp_rets tmp_vars args args_vname, s1) = (r, s1') /\
    inl_post inl_fs r s' s1'.
Proof.
  intros IH H Hne Hfs Hbag Hsr Hls Hci Hf Hue tmp ret_max temp_rets.
  pose proof (callee_lookup bag inl_fs s f args_vname p0 Hf Hbag Hfs) as Hfc.
  destruct (tmp_vars_facts args args_vname) as (Hdt & Hlt & Htv & Hte). fold tmp in Hdt, Hlt, Htv, Hte.
  set (transformed := if not_branch_ret ic then Seq Tick (transform_eoc temp_rets ic)
                      else While (Const (n2w 1)) (transform_branch 0 temp_rets ic)).
  unfold_eval_in H. unfold lookup_code in H. rewrite Hfc in H.
  destruct (OPT_MMAP (eval s) args) as [argv|] eqn:Ha; [|injection H as <- _; congruence].
  destruct ((LENGTH args_vname =? LENGTH argv) && ALL_DISTINCT args_vname)%bool eqn:Hl;
    [|injection H as <- _; congruence].
  apply andb_prop in Hl as [Hl Hd]. apply N.eqb_eq in Hl.
  cbv beta iota in H.
  destruct (negb (ALL_DISTINCT rts)) eqn:Hdr; [injection H as <- _; congruence|].
  assert (Hdr' : ALL_DISTINCT rts) by (destruct (ALL_DISTINCT rts); [reflexivity|discriminate]).
  pose proof (opt_mmap_length_eq _ _ _ Ha) as Hla.
  assert (Hnil : args_vname = [] -> args = []).
  { intros ->. destruct args as [|e0 args]; [reflexivity|]. rewrite LENGTH_cons in Hla. cbn in Hl. lia. }
  assert (Htr : forall x, In x temp_rets -> ~ In x rts /\ ~ In x tmp /\ ~ In x args_vname /\
                  ~ In x (FLAT (MAP var_cexp args)) /\ ~ In x (var_prog ic))
    by (intros x Hx; exact (temp_rets_facts args args_vname rts ic x Hnil Hx)).
  assert (Hdtr : ALL_DISTINCT temp_rets) by apply genlist_distinct_i.
  assert (Hltr : LENGTH temp_rets = LENGTH rts) by apply LENGTH_GENLIST_i.
  unfold inline_nontail.
  set (zeros := REPLICATE (LENGTH temp_rets) (@Word a (n2w 0))).
  rewrite (nested_decs_eval temp_rets (REPLICATE (LENGTH temp_rets) (Const (n2w 0))) _ s1 zeros
             (evaluate_replicate_const _ _) ltac:(rewrite LENGTH_REPLICATE; reflexivity) Hdtr).
  2: { intros v Hv e He Hm. apply MEM_In, In_REPLICATE_i in He. subst e. discriminate Hm. }
  set (S2 := set_locals (locals s1 |++ ZIP (temp_rets, zeros)) s1).
  set (tt := FEMPTY |++ ZIP (temp_rets, zeros)).
  assert (Hlz : LENGTH temp_rets = LENGTH zeros) by (unfold zeros; rewrite LENGTH_REPLICATE; reflexivity).
  assert (Ho2 : OPT_MMAP (eval S2) args = SOME argv).
  { unfold S2. rewrite <- (eval_rel s s1 Hsr Hls) in Ha.
    apply (opt_mmap_update_list_locals_not_vars_eval_eq args temp_rets zeros s1). split; [|split; [exact Ha|exact Hlz]].
    intros x Hx Hm. apply MEM_In in Hx, Hm. exact (proj1 (proj2 (proj2 (proj2 (Htr x Hx)))) Hm). }
  assert (Htt : tt ⊑ locals S2).
  { intros k v Hk. unfold tt in Hk. unfold S2. rewrite sl_locals. lk2_in Hk. lk2. lk_cases; congruence. }
  assert (Htt_dom : forall v, MEM v args_vname \/ MEM v tmp -> v NOTIN FDOM tt).
  { intros v Hv Hin. unfold_sets; unfold FDOM, tt in Hin. lk2_in Hin. lk_cases; [|apply Hin; reflexivity].
    unfold is_true in Hv; rewrite !MEM_In in Hv. specialize (Htr v i). tauto. }
  assert (Hck : clock s1 = clock s) by (symmetry; apply Hsr).
  destruct (clock s =? 0) eqn:Ec.
  - (* clock 0 *)
    injection H as <- <-. apply N.eqb_eq in Ec.
    pose proof (transformed_clock0 (not_branch_ret ic) (transform_eoc temp_rets ic) (transform_branch 0 temp_rets ic)
                  (set_locals (tt |++ ZIP (args_vname, argv)) S2) ltac:(unfold S2; rewrite !sl_clock; lia)) as Et.
    fold transformed in Et.
    destruct (arg_load_master S2 args argv args_vname tt transformed _ _ tmp Ho2 Hl Hd Htt Et Htt_dom
                ltac:(discriminate) Hdt Hlt Htv Hte) as (t' & E & Hst & _).
    ev_goal. unfold arg_load. rewrite E. cbv beta iota.
    eexists; split; [reflexivity|]. apply inl_post_nc; [reflexivity|discriminate| |].
    + apply state_rel_code_sl_l, state_rel_code_sl_r. apply (state_rel_code_trans _ s1); [exact Hsr|].
      apply (state_rel_code_trans _ (empty_locals (set_locals (tt |++ ZIP (args_vname, argv)) S2)));
        [unfold empty_locals, S2; apply state_rel_code_sl_r, state_rel_code_sl_r, state_rel_code_sl_r, state_rel_code_refl
        |apply state_rel_imp_code, Hst].
    + pose proof (evaluate_code_invariant _ _ _ _ E) as Ect.
      apply (code_inl_rel_code inl_fs s s1); [reflexivity|rewrite sl_code, Ect; reflexivity|exact Hci].
  - (* clock <> 0 *)
    apply N.eqb_neq in Ec.
    destruct (evaluate (p0, set_locals (FEMPTY |++ ZIP (args_vname, argv)) (dec_clock s))) as [q st] eqn:Eq.
    assert (Hsrc : (exists retvs z, q = SOME (Return retvs) /\ LENGTH retvs = LENGTH rts /\
                      OPT_MMAP (FLOOKUP (locals s)) rts = SOME z /\
                      r = NONE /\ s' = set_locals (locals s |++ ZIP (rts, retvs)) st) \/
                   (cres q = false /\ (forall rv, q <> SOME (Return rv)) /\ q <> SOME Error /\
                    r = q /\ s' = empty_locals st)).
    { destruct q as [[| | | |retvs| |]|]; cbv beta iota in H;
        try (injection H as <- <-; right; split; [reflexivity|]; split; [intros ? ?; discriminate|];
             split; [discriminate|split; reflexivity]);
        try (injection H as <- _; congruence).
      left. destruct (negb (LENGTH retvs =? LENGTH rts)) eqn:El; [injection H as <- _; congruence|].
      destruct (OPT_MMAP (FLOOKUP (locals s)) rts) as [z|] eqn:Ez; [|injection H as <- _; congruence].
      injection H as <- <-. exists retvs, z. split; [reflexivity|]. split; [|tauto].
      apply Bool.negb_false_iff, N.eqb_eq in El. exact El. }
    assert (Hqe : q <> SOME Error) by (destruct Hsrc as [(? & ? & -> & _)|(_ & _ & ? & _)]; [discriminate|assumption]).
    pose proof (evaluate_code_invariant _ _ _ _ Eq) as Ecq. rewrite sl_code, sl_code_dec_clock in Ecq.
    set (T0 := set_locals (FEMPTY |++ ZIP (args_vname, argv)) (dec_clock s1)).
    destruct (IH p0 (set_locals (FEMPTY |++ ZIP (args_vname, argv)) (dec_clock s)) ltac:(lt_tac) q st inl_fs
                T0 (bag \\ f) Eq Hqe
                ltac:(rewrite sl_code; exact Hfs)
                ltac:(apply (SUBMAP_TRANS _ bag); split; [apply SUBMAP_DOMSUB|exact Hbag])
                ltac:(unfold T0; apply state_rel_code_sl; unfold state_rel_code in *; cbn; intuition congruence)
                ltac:(reflexivity)
                ltac:(apply (code_inl_rel_code inl_fs s s1); [reflexivity|reflexivity|exact Hci]))
      as (st1 & Ht1 & Hs1 & Hc1 & _).
    pose proof (unreach_elim_correct _ T0 q st1 ic et (conj Ht1 (conj Hqe Hue))) as Ht2.
    set (loc := tt |++ ZIP (args_vname, argv)).
    assert (Hsubl : FEMPTY |++ ZIP (args_vname, argv) ⊑ loc).
    { apply submap_zip_ext; [exact Hl|exact Hlz|]. intros x Hx Hy. exact (proj1 (proj2 (proj2 (Htr x Hy))) Hx). }
    destruct (evaluate_submap_locals ic _ loc (dec_clock s1) q st1 Ht2 Hqe Hsubl) as (st2 & Ht3 & Hs2 & _).
    assert (Hz : exists z, OPT_MMAP (FLOOKUP loc) temp_rets = SOME z).
    { exists zeros. unfold loc. rewrite opt_mmap_disj_zip_flookup.
      - unfold tt. apply opt_mmap_some_eq_zip_flookup. split; [exact Hdtr|exact Hlz].
      - split; [|exact Hl]. apply distinct_lists_iff. intros x Hx Hy. exact (proj1 (proj2 (proj2 (Htr x Hy))) Hx). }
    destruct (wrapped_transform_if ic s1 q st2 et temp_rets loc) as (r1 & s1'' & Ewt & Hs3 & Hp3).
    { split; [exact Ht3|]. split; [exact (unreach_elim_converge _ _ _ Hue)|].
      split; [intros retvs ->; destruct Hsrc as [(rv & z & Eqr & Hlr & _)|(_ & Hnr & _)];
              [injection Eqr as <-; lia|exfalso; exact (Hnr retvs eq_refl)]|].
      split; [intros x Hx Hm; apply MEM_In in Hx, Hm; exact (proj2 (proj2 (proj2 (proj2 (Htr x Hx)))) Hm)|].
      split; [exact Hz|]. split; [exact Hdtr|].
      split; [destruct Hsrc as [(rv & z & -> & _)|(Hcq & _)]; [cbn; discriminate|];
              destruct q as [[]|]; cbn in Hcq |- *; congruence|].
      split; [lia|exact Hqe]. }
    assert (Hr1e : r1 <> SOME Error).
    { destruct Hsrc as [(rv & z & -> & _)|(Hcq & Hnr & _)]; [destruct Hp3 as [-> _]; discriminate|].
      destruct q as [[| | | | | |]|]; cbn in Hp3; try discriminate Hcq; try congruence; subst r1; discriminate. }
    assert (Ewt' : evaluate (transformed, set_locals (tt |++ ZIP (args_vname, argv)) S2) = (r1, s1''))
      by (unfold S2; rewrite sl_sl; exact Ewt).
    destruct (arg_load_master S2 args argv args_vname tt transformed r1 s1'' tmp Ho2 Hl Hd Htt Ewt' Htt_dom
                Hr1e Hdt Hlt Htv Hte) as (t' & E & Hst & Hc).
    pose proof (evaluate_code_invariant _ _ _ _ E) as Ect. unfold S2 in Ect. rewrite sl_code in Ect.
    assert (Hsc : state_rel_code st t')
      by (apply (state_rel_code_trans _ st1); [exact Hs1|];
          apply state_rel_imp_code, (state_rel_trans _ st2); [exact Hs2|];
          apply (state_rel_trans _ s1''); [exact Hs3|exact Hst]).
    ev_goal. unfold arg_load. rewrite E. cbv beta iota.
    destruct Hsrc as [(retvs & z & -> & Hlr & Hz0 & -> & ->)|(Hcq & Hnr & _ & -> & ->)].
    + (* Return *)
      destruct Hp3 as [-> Hr3]. cbv beta iota. destruct (Hc eq_refl) as [Hlk Hdom].
      assert (Ho3 : OPT_MMAP (eval t') (MAP Var temp_rets) = SOME retvs).
      { rewrite <- lookup_locals_eq_map_vars, <- Hr3. apply OPT_MMAP_ext_In''. intros k Hk.
        rewrite Hlk. destruct (Htr k Hk) as (_ & Hk2 & Hk3 & _).
        destruct (in_dec _ k tmp); [contradiction|]. destruct (in_dec _ k args_vname); [contradiction|].
        destruct (OPT_MMAP_In_SOME _ _ _ k Hr3 Hk) as [y Hy]. rewrite Hy. reflexivity. }
      assert (Hrv : forall x, MEM x rts -> ~ MEM x (FLAT (MAP var_cexp (MAP (@Var a) temp_rets)))).
      { rewrite map_var_cexp_eq_var. intros x Hx Hm. apply MEM_In in Hx, Hm. exact (proj1 (Htr x Hm) Hx). }
      assert (Hrl : exists vals, OPT_MMAP (FLOOKUP (locals t')) rts = SOME vals).
      { apply OPT_MMAP_SOME_ALL. intros k Hk. apply MEM_In in Hk.
        destruct (OPT_MMAP_In_SOME _ _ _ k Hz0 Hk) as [y Hy].
        assert (Hnt : ~ In k temp_rets) by (intros Ht; exact (proj1 (Htr k Ht) Hk)).
        rewrite Hlk. unfold S2. rewrite sl_locals. lk2. rewrite <- Hls.
        lk_cases; try contradiction; eauto. }
      destruct Hrl as [vals Hrl].
      rewrite (nested_seq_assign_eval rts (MAP Var temp_rets) t' retvs vals Ho3 Hrv Hrl ltac:(lia) Hdr').
      cbv beta iota. eexists; split; [reflexivity|].
      split; [apply state_rel_code_sl, state_rel_code_sl_r, Hsc|].
      split; [apply (code_inl_rel_code inl_fs s s1); [rewrite ?sl_code, ?Ecq; reflexivity|rewrite ?sl_code, ?Ect; reflexivity|exact Hci]|].
      unfold locals_strong_rel. rewrite !sl_locals. apply fmap_ext. intros k.
      specialize (Hlk k). specialize (Hdom k). unfold tt in Hdom. lk2_in Hdom.
      assert (Hrk : In k temp_rets -> ~ In k rts /\ ~ In k tmp /\ ~ In k args_vname) by
        (intros Hk; destruct (Htr k Hk) as (? & ? & ? & _); tauto).
      lk2. rewrite Hlk. unfold S2. rewrite sl_locals. lk2. rewrite <- Hls.
      lk_cases; intuition congruence.
    + (* Exception, TimeOut, FinalFFI *)
      assert (Hr1 : r1 = q).
      { destruct q as [[| | | | | |]|]; cbn in Hp3; try discriminate Hcq; try congruence; exfalso; exact (Hnr _ eq_refl). }
      subst r1. destruct q as [x|]; [|discriminate Hcq]. cbv beta iota.
      eexists; split; [reflexivity|]. apply inl_post_nc; [exact Hcq|exact Hqe| |].
      * apply state_rel_code_sl_l, state_rel_code_sl_r, Hsc.
      * apply (code_inl_rel_code inl_fs s s1); [unfold empty_locals; rewrite ?sl_code, ?Ecq; reflexivity|rewrite ?sl_code, ?Ect; reflexivity|exact Hci].
Qed.

End InlineNontail.

Section InlineMain.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma inl_Call ctyp f (args : list (exp a)) s :
  (forall p' s', eval_lt (p', s') (Call ctyp f args, s) -> inl_P p' s') -> inl_P (Call ctyp f args) s.
Proof.
  intros IH r s' inl_fs s1 bag H Hne Hfs Hbag Hsr Hls Hci.
  rewrite (proj1 inline_prog_def). cbv zeta.
  destruct ctyp as [[rts [[w hdl]|]]|].
  - assert (Eq : forall (X : prog a),
              (if negb (ALL_DISTINCT rts) then Call (SOME (rts, SOME (w, inline_prog bag hdl))) f args else X) =
              Call (map_ctyp (inline_prog bag) (SOME (rts, SOME (w, hdl)))) f args ->
              (if negb (ALL_DISTINCT rts) then Call (SOME (rts, SOME (w, inline_prog bag hdl))) f args else X) =
              Call (map_ctyp (inline_prog bag) (SOME (rts, SOME (w, hdl)))) f args) by tauto.
    cbv beta iota. erewrite Eq.
    + exact (inl_call_plain _ f args s bag inl_fs s1 r s' IH H Hne Hfs Hbag Hsr Hls Hci).
    + destruct (negb (ALL_DISTINCT rts)); [reflexivity|].
      destruct (FLOOKUP bag f) as [[av p0]|]; [|reflexivity].
      destruct (unreach_elim (inline_prog (bag \\ f) p0)); reflexivity.
  - cbv beta iota. destruct (negb (ALL_DISTINCT rts)) eqn:Hd.
    + exact (inl_call_plain (SOME (rts, NONE)) f args s bag inl_fs s1 r s' IH H Hne Hfs Hbag Hsr Hls Hci).
    + destruct (FLOOKUP bag f) as [[av p0]|] eqn:Hf.
      * destruct (unreach_elim (inline_prog (bag \\ f) p0)) as [ic et] eqn:Hue. cbv beta iota zeta.
        exact (inl_call_nontail f args s bag inl_fs s1 r s' av p0 ic et rts IH H Hne Hfs Hbag Hsr Hls Hci Hf Hue).
      * exact (inl_call_plain (SOME (rts, NONE)) f args s bag inl_fs s1 r s' IH H Hne Hfs Hbag Hsr Hls Hci).
  - cbv beta iota. destruct (FLOOKUP bag f) as [[av p0]|] eqn:Hf.
    + destruct (unreach_elim (inline_prog (bag \\ f) p0)) as [ic et] eqn:Hue. cbv beta iota zeta.
      exact (inl_call_tail f args s bag inl_fs s1 r s' av p0 ic et IH H Hne Hfs Hbag Hsr Hls Hci Hf Hue).
    + exact (inl_call_plain NONE f args s bag inl_fs s1 r s' IH H Hne Hfs Hbag Hsr Hls Hci).
Qed.

Lemma inl_all : forall x : prog a * state a ffi_t, inl_P (fst x) (snd x).
Proof.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf). cbn [fst snd].
  assert (IH' : forall p' s', eval_lt (p', s') (p, s) -> inl_P p' s') by (intros p' s' Hlt; exact (IH (p', s') Hlt)).
  destruct p; try (apply inl_simple; reflexivity).
  - apply inl_Dec, IH'.
  - apply inl_Seq, IH'.
  - apply inl_If, IH'.
  - apply inl_While, IH'.
  - apply inl_Call, IH'.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "inline_prog_correct" *)
Theorem inline_prog_correct : forall (p : prog a) s r s' inl_fs s1 inl_bag,
  evaluate (p, s) = (r, s') /\
  r <> SOME Error /\
  inl_fs ⊑ code s /\
  inl_bag ⊑ inl_fs /\
  state_rel_code s s1 /\
  locals_strong_rel s s1 /\
  code_inl_rel inl_fs s s1 ->
  exists s1',
    evaluate (inline_prog inl_bag p, s1) = (r, s1') /\
    state_rel_code s' s1' /\
    code_inl_rel inl_fs s' s1' /\
    match r with
    | NONE => locals_strong_rel s' s1'
    | SOME (Break n) => locals_strong_rel s' s1'
    | SOME (Continue n) => locals_strong_rel s' s1'
    | SOME Error => False
    | _ => True
    end.
Proof.
  intros p s r s' inl_fs s1 inl_bag (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  exact (inl_all (p, s) r s' inl_fs s1 inl_bag H1 H2 H3 H4 H5 H6 H7).
Qed.

End InlineMain.
Ltac mem2in := unfold is_true in *;
  repeat match goal with
  | H : context [MEM ?x ?l = true] |- _ => rewrite (MEM_In x l) in H
  | |- context [MEM ?x ?l = true] => rewrite (MEM_In x l)
  end.

Section ExpsOf.
Context {a : N}.

#[local] Instance cprog_eq_dec_classical : EqDecision (prog a) := fun x y => classical_dec (x = y).

Lemma MEM_app_e (e : exp a) l1 l2 : MEM e (l1 ++ l2) <-> MEM e l1 \/ MEM e l2.
Proof. unfold is_true; rewrite !MEM_In, in_app_iff; tauto. Qed.

Lemma MEM_cons_e (e e0 : exp a) l : MEM e (e0 :: l) <-> e = e0 \/ MEM e l.
Proof. unfold is_true; rewrite !MEM_In. cbn [In]. intuition congruence. Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "exps_of_nested_seq_assign" *)
Theorem exps_of_nested_seq_assign : forall ns (es : list (exp a)) e,
  MEM e (exps_of (nested_seq (MAP2 Assign ns es))) -> MEM e es.
Proof.
  induction ns as [|n ns IH]; intros [|e0 es] e H; cbn [MAP2 nested_seq exps_of] in H; try discriminate.
  rewrite MEM_app_e in H. destruct H as [H|H].
  - mem2in. destruct H as [<-|[]]. left. reflexivity.
  - apply IH in H. mem2in. right. exact H.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "exps_of_nested_decs" *)
Theorem exps_of_nested_decs : forall (e : exp a) vs es p,
  MEM e (exps_of (nested_decs vs es p)) -> MEM e es \/ MEM e (exps_of p).
Proof.
  intros e vs; induction vs as [|v vs IH]; intros [|e0 es] p H; cbn [nested_decs exps_of] in H; try (right; exact H);
    try discriminate.
  apply MEM_In in H. destruct H as [<-|H].
  - left. apply MEM_In. left. reflexivity.
  - destruct (IH es p (proj2 (MEM_In _ _) H)) as [H1|H1]; [left|right; exact H1].
    apply MEM_In. right. apply MEM_In, H1.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "exps_of_arg_load" *)
Theorem exps_of_arg_load : forall (e : exp a) tmp_vars args args_vname p,
  MEM e (exps_of (arg_load tmp_vars args args_vname p)) ->
  MEM e args \/ (exists c, MEM c tmp_vars /\ e = Var c) \/ MEM e (exps_of p).
Proof.
  intros e tmp args vn p H. unfold arg_load in H.
  destruct (exps_of_nested_decs _ _ _ _ H) as [H1|H1]; [left; exact H1|].
  destruct (exps_of_nested_decs _ _ _ _ H1) as [H2|H2]; [|right; right; exact H2].
  right; left. unfold is_true in H2. rewrite MEM_In in H2. apply in_map_iff in H2 as (c & <- & Hc).
  exists c. split; [apply MEM_In, Hc|reflexivity].
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "submap_flookup_alist_to_fmap" *)
Theorem submap_flookup_alist_to_fmap : forall {K V} `{EqDecision K} `{EqDecision V}
    (s : fmap K V) (t : list (K * V)) x v,
  s ⊑ alist_to_fmap t /\ FLOOKUP s x = SOME v -> MEM (x, v) t.
Proof.
  intros K V HK HV s t x v [Hs Hx]. apply Hs in Hx. rewrite FLOOKUP_alist_to_fmap in Hx.
  apply MEM_In, ALOOKUP_In, Hx.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "exps_of_unreach_elim" *)
Theorem exps_of_unreach_elim : forall (p : prog a) q (r : option early_exit) e (rt : option early_exit),
  unreach_elim p = (q, r) /\ MEM e (exps_of q) -> MEM e (exps_of p).
Proof.
  intros p; induction p using cprog_nested_ind; intros q0 r0 ex rt [Hu He]; cbn [unreach_elim] in Hu.
  all: try (injection Hu as <- _; exact He).
  - destruct (unreach_elim p) as [p' r'] eqn:E. injection Hu as <- _. cbn [exps_of] in *.
    mem2in. cbn [In] in *. destruct He as [He|He]; [left; exact He|right].
    apply MEM_In. apply (IHp p' r' ex rt). split; [reflexivity|apply MEM_In, He].
  - destruct (unreach_elim p1) as [p1' r1] eqn:E1. cbn [exps_of]. rewrite MEM_app_e.
    destruct (decide (r1 <> None)).
    + injection Hu as <- _. left. exact (IHp1 p1' r1 ex rt (conj eq_refl He)).
    + destruct (unreach_elim p2) as [p2' r2] eqn:E2. injection Hu as <- _. cbn [exps_of] in He.
      rewrite MEM_app_e in He. destruct He as [He|He]; [left; exact (IHp1 p1' r1 ex rt (conj eq_refl He))
                                                      |right; exact (IHp2 p2' r2 ex rt (conj eq_refl He))].
  - destruct (unreach_elim p1) as [p1' r1] eqn:E1, (unreach_elim p2) as [p2' r2] eqn:E2.
    injection Hu as <- _. cbn [exps_of] in *. mem2in. cbn [In] in *.
    rewrite !in_app_iff in *. destruct He as [He|[He|He]]; [left; exact He| |].
    + right; left. apply MEM_In, (IHp1 p1' r1 ex rt). split; [reflexivity|apply MEM_In, He].
    + right; right. apply MEM_In, (IHp2 p2' r2 ex rt). split; [reflexivity|apply MEM_In, He].
  - destruct (unreach_elim p) as [p' r'] eqn:E. injection Hu as <- _. cbn [exps_of] in *.
    mem2in. cbn [In] in *. destruct He as [He|He]; [left; exact He|right].
    apply MEM_In. apply (IHp p' r' ex rt). split; [reflexivity|apply MEM_In, He].
  - destruct o as [[rts [[w hdl]|]]|].
    + destruct (unreach_elim hdl) as [h' rh] eqn:E. injection Hu as <- _. cbn [exps_of] in *.
      rewrite MEM_app_e in *. destruct He as [He|He]; [left; exact He|right].
      exact (H rts w hdl eq_refl h' rh ex rt (conj E He)).
    + injection Hu as <- _. exact He.
    + injection Hu as <- _. exact He.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "exps_of_transform_eoc" *)
Theorem exps_of_transform_eoc : forall rts (p : prog a) e,
  MEM e (exps_of (transform_eoc rts p)) -> MEM e (exps_of p).
Proof.
  intros rts p; induction p using cprog_nested_ind; intros ex He; cbn [transform_eoc exps_of] in *;
    try exact He.
  - rewrite MEM_cons_e in *. destruct He as [He|He]; [left; exact He|right; apply IHp, He].
  - rewrite MEM_app_e in *. destruct He as [He|He]; [left; apply IHp1, He|right; apply IHp2, He].
  - rewrite MEM_cons_e, !MEM_app_e in *. destruct He as [He|[He|He]];
      [left; exact He|right; left; apply IHp1, He|right; right; apply IHp2, He].
  - rewrite MEM_cons_e in *. destruct He as [He|He]; [left; exact He|right; apply IHp, He].
  - destruct o as [[rs [[w hdl]|]]|]; cbn [exps_of] in *; try exact He.
    rewrite MEM_app_e in *. destruct He as [He|He]; [left; exact He|right; exact (H rs w hdl eq_refl ex He)].
  - apply (exps_of_nested_seq_assign rts). exact He.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "exps_of_transform_branch" *)
Theorem exps_of_transform_branch : forall ld rts (p : prog a) e,
  MEM e (exps_of (transform_branch ld rts p)) -> MEM e (exps_of p).
Proof.
  intros ld rts p; revert ld; induction p using cprog_nested_ind; intros ld ex He;
    cbn [transform_branch exps_of] in *; try exact He.
  - rewrite MEM_cons_e in *. destruct He as [He|He]; [left; exact He|right; apply (IHp ld), He].
  - rewrite MEM_app_e in *. destruct He as [He|He]; [left; apply (IHp1 ld), He|right; apply (IHp2 ld), He].
  - rewrite MEM_cons_e, !MEM_app_e in *. destruct He as [He|[He|He]];
      [left; exact He|right; left; apply (IHp1 ld), He|right; right; apply (IHp2 ld), He].
  - rewrite MEM_cons_e in *. destruct He as [He|He]; [left; exact He|right; apply (IHp (ld + 1)), He].
  - destruct o as [[rs [[w hdl]|]]|]; cbn [exps_of] in *; try exact He.
    + rewrite MEM_app_e in *. destruct He as [He|He]; [left; exact He|right; exact (H rs w hdl eq_refl ld ex He)].
    + rewrite app_nil_r in He. exact He.
  - rewrite app_nil_r in He. apply (exps_of_nested_seq_assign rts). exact He.
Qed.

Definition inl_exp_ok (crep_code : list (funname * (list varname * prog a))) (p : prog a) (e : exp a) : Prop :=
  In e (exps_of p) \/ (exists c, e = Const c) \/ (exists v, e = Var v) \/
  (exists name params body, In (name, (params, body)) crep_code /\ In e (exps_of body)).

Lemma inl_exp_ok_callee crep_code (fs : fmap funname (list varname * prog a)) f av p0 p e :
  fs ⊑ alist_to_fmap crep_code -> FLOOKUP fs f = SOME (av, p0) ->
  inl_exp_ok crep_code p0 e -> inl_exp_ok crep_code p e.
Proof.
  intros Hs Hf [H|[H|[H|H]]]; unfold inl_exp_ok; [|tauto|tauto|tauto].
  right; right; right. exists f, av, p0. split; [|exact H].
  apply Hs in Hf. rewrite FLOOKUP_alist_to_fmap in Hf. apply ALOOKUP_In, Hf.
Qed.

(** Equations of [exps_of], used by rewriting so that the kernel never
    unfolds [exps_of] around [inline_prog] terms (Galette-only). *)
Lemma exps_of_Dec v (e : exp a) p : exps_of (Dec v e p) = e :: exps_of p. Proof. reflexivity. Qed.
Lemma exps_of_Seq (p q : prog a) : exps_of (Seq p q) = exps_of p ++ exps_of q. Proof. reflexivity. Qed.
Lemma exps_of_If (e : exp a) p q : exps_of (If e p q) = e :: exps_of p ++ exps_of q. Proof. reflexivity. Qed.
Lemma exps_of_While (e : exp a) p : exps_of (While e p) = e :: exps_of p. Proof. reflexivity. Qed.
Lemma exps_of_Tick : exps_of (@Tick a) = []. Proof. reflexivity. Qed.
Lemma exps_of_Call_hdl rts w (hdl : prog a) f es :
  exps_of (Call (SOME (rts, SOME (w, hdl))) f es) = es ++ exps_of hdl. Proof. reflexivity. Qed.
Lemma exps_of_Call_nohdl rts f (es : list (exp a)) : exps_of (Call (SOME (rts, NONE)) f es) = es. Proof. reflexivity. Qed.
Lemma exps_of_Call_tail f (es : list (exp a)) : exps_of (Call NONE f es) = es. Proof. reflexivity. Qed.
Lemma In_cons_i {A} (x y : A) l : In x (y :: l) <-> y = x \/ In x l. Proof. reflexivity. Qed.

Lemma inline_prog_simple (fs : fmap funname (list varname * prog a)) (p : prog a) :
  is_simple p = true -> inline_prog fs p = p.
Proof. intros Hsim. destruct p; try discriminate Hsim; apply inline_prog_def. Qed.

Lemma exps_inl_In (crep_code : list (funname * (list varname * prog a))) : forall n
    (fs : fmap funname (list varname * prog a)) (p : prog a) e,
  N.to_nat (FCARD fs) = n -> fs ⊑ alist_to_fmap crep_code ->
  In e (exps_of (inline_prog fs p)) -> inl_exp_ok crep_code p e.
Proof.
  intros n; induction n as [n IHn] using (well_founded_induction lt_wf).
  intros fs p; induction p using cprog_nested_ind; intros ex Hn Hs He.
  all: unfold inl_exp_ok.
  all: try (rewrite (proj1 (proj2 inline_prog_def)) in He || rewrite (proj1 (proj2 (proj2 inline_prog_def))) in He ||
            rewrite (proj1 (proj2 (proj2 (proj2 inline_prog_def)))) in He ||
            rewrite (proj1 (proj2 (proj2 (proj2 (proj2 inline_prog_def))))) in He).
  all: try (rewrite inline_prog_simple in He by reflexivity; left; exact He).
  - (* Dec *)
    rewrite exps_of_Dec, In_cons_i in He. cbn [exps_of In]. destruct He as [<-|He]; [left; left; reflexivity|].
    destruct (IHp ex Hn Hs He) as [H1|H1]; [left; right; exact H1|right; exact H1].
  - (* Seq *)
    cbv zeta in He. rewrite exps_of_Seq in He. cbn [exps_of]. apply in_app_iff in He. destruct He as [He|He].
    + destruct (IHp1 ex Hn Hs He) as [H1|H1]; [left; apply in_app_iff; left; exact H1|right; exact H1].
    + destruct (IHp2 ex Hn Hs He) as [H1|H1]; [left; apply in_app_iff; right; exact H1|right; exact H1].
  - (* If *)
    cbv zeta in He. rewrite exps_of_If, In_cons_i in He. cbn [exps_of In]. destruct He as [<-|He]; [left; left; reflexivity|].
    apply in_app_iff in He. destruct He as [He|He].
    + destruct (IHp1 ex Hn Hs He) as [H1|H1]; [left; right; apply in_app_iff; left; exact H1|right; exact H1].
    + destruct (IHp2 ex Hn Hs He) as [H1|H1]; [left; right; apply in_app_iff; right; exact H1|right; exact H1].
  - (* While *)
    rewrite exps_of_While, In_cons_i in He. cbn [exps_of In]. destruct He as [<-|He]; [left; left; reflexivity|].
    destruct (IHp ex Hn Hs He) as [H1|H1]; [left; right; exact H1|right; exact H1].
  - (* Call *)
    assert (Hargs : forall x, In x es -> inl_exp_ok crep_code (Call o f es) x).
    { intros x Hx. left. destruct o as [[? [[? ?]|]]|]; cbn [exps_of]; try exact Hx. apply in_app_iff; left; exact Hx. }
    assert (Hcallee : forall av p0, FLOOKUP fs f = SOME (av, p0) -> forall ic et,
              unreach_elim (inline_prog (fs \\ f) p0) = (ic, et) ->
              forall x, MEM x (exps_of ic) -> inl_exp_ok crep_code (Call o f es) x).
    { intros av p0 Hf ic et Hue x Hx.
      pose proof (exps_of_unreach_elim _ ic et x et (conj Hue Hx)) as Hx'.
      apply (inl_exp_ok_callee crep_code fs f av p0 _ x Hs Hf).
      apply (IHn (N.to_nat (FCARD (fs \\ f)))
               ltac:(rewrite <- Hn; exact (FCARD_fdomsub_lt fs f _ Hf)) (fs \\ f) p0 x eq_refl).
      - apply (SUBMAP_TRANS _ fs). split; [apply SUBMAP_DOMSUB|exact Hs].
      - apply MEM_In, Hx'. }
    assert (Hvar : forall x c, x = Var c -> inl_exp_ok crep_code (Call o f es) x)
      by (intros x c ->; right; right; left; eexists; reflexivity).
    assert (Hconst : forall x c, x = Const c -> inl_exp_ok crep_code (Call o f es) x)
      by (intros x c ->; right; left; eexists; reflexivity).
    assert (Hargl : forall tmp av p, MEM ex (exps_of (arg_load tmp es av p)) ->
              (MEM ex (exps_of p) -> inl_exp_ok crep_code (Call o f es) ex) ->
              inl_exp_ok crep_code (Call o f es) ex).
    { intros tmp av p0 H1 H2. destruct (exps_of_arg_load _ _ _ _ _ H1) as [H3|[(c & _ & H3)|H3]].
      - apply Hargs, MEM_In, H3.
      - exact (Hvar _ _ H3).
      - exact (H2 H3). }
    rewrite (proj1 inline_prog_def) in He. cbv zeta in He.
    destruct o as [[rts [[w hdl]|]]|].
    + assert (Hh : In ex (exps_of (Call (SOME (rts, SOME (w, inline_prog fs hdl))) f es))).
      { destruct (negb (ALL_DISTINCT rts)); [exact He|].
        destruct (FLOOKUP fs f) as [[av p0]|]; [|exact He].
        destruct (unreach_elim (inline_prog (fs \\ f) p0)); exact He. }
      rewrite exps_of_Call_hdl in Hh. apply in_app_iff in Hh. destruct Hh as [Hh|Hh]; [apply Hargs, Hh|].
      destruct (H rts w hdl eq_refl ex Hn Hs Hh) as [H1|H1]; [|right; exact H1].
      left. cbn [exps_of]. apply in_app_iff. right. exact H1.
    + cbv beta iota in He. destruct (negb (ALL_DISTINCT rts)); [rewrite exps_of_Call_nohdl in He; apply Hargs, He|].
      destruct (FLOOKUP fs f) as [[av p0]|] eqn:Hf; [|rewrite exps_of_Call_nohdl in He; apply Hargs, He].
      destruct (unreach_elim (inline_prog (fs \\ f) p0)) as [ic et] eqn:Hue. cbv beta iota zeta in He.
      unfold inline_nontail in He. apply MEM_In in He. 
      destruct (exps_of_nested_decs _ _ _ _ He) as [H1|H1].
      * apply MEM_In, In_REPLICATE_i in H1. exact (Hconst _ _ H1).
      * rewrite exps_of_Seq in H1. apply MEM_app_e in H1. destruct H1 as [H1|H1].
        -- apply (Hargl _ _ _ H1). intros H2. destruct (not_branch_ret ic).
           ++ rewrite exps_of_Seq, exps_of_Tick, app_nil_l in H2.
              exact (Hcallee av p0 eq_refl ic et Hue ex (exps_of_transform_eoc _ _ _ H2)).
           ++ rewrite exps_of_While in H2. apply MEM_cons_e in H2. destruct H2 as [H2|H2]; [exact (Hconst _ _ H2)|].
              exact (Hcallee av p0 eq_refl ic et Hue ex (exps_of_transform_branch _ _ _ _ H2)).
        -- apply exps_of_nested_seq_assign in H1. apply MEM_In, in_map_iff in H1 as (c & <- & _).
           exact (Hvar _ c eq_refl).
    + cbv beta iota in He. destruct (FLOOKUP fs f) as [[av p0]|] eqn:Hf; [|rewrite exps_of_Call_tail in He; apply Hargs, He].
      destruct (unreach_elim (inline_prog (fs \\ f) p0)) as [ic et] eqn:Hue. cbv beta iota zeta in He.
      unfold inline_tail in He. rewrite exps_of_Seq, exps_of_Tick, app_nil_l in He. apply MEM_In in He.
      apply (Hargl _ _ _ He). exact (Hcallee av p0 eq_refl ic et Hue ex).
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "exps_of_inst_inline" *)
Theorem exps_of_inst_inline : forall inl_fs (prog : crepLang.prog a)
    (crep_code : list (funname * (list varname * crepLang.prog a))) e,
  inl_fs ⊑ alist_to_fmap crep_code /\
  MEM e (exps_of (inline_prog inl_fs prog)) ->
  MEM e (exps_of prog) \/
  (exists c, e = Const c) \/
  (exists v, e = Var v) \/
  (exists name params body,
     MEM (name, (params, body)) crep_code /\
     MEM e (exps_of body)).
Proof.
  intros inl_fs p crep_code e [Hs He].
  destruct (exps_inl_In crep_code _ inl_fs p e eq_refl Hs (proj1 (MEM_In _ _) He)) as [H|[H|[H|H]]].
  - left; apply MEM_In, H.
  - right; left; exact H.
  - right; right; left; exact H.
  - right; right; right. destruct H as (name & params & body & H1 & H2).
    exists name, params, body. split; apply MEM_In; assumption.
Qed.

Definition crepop_len2 (x : exp a) : bool :=
  if classical_dec (forall op es, x = Crepop op es -> LENGTH es = 2) then true else false.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "every_inst_crep_inline" *)
Theorem every_inst_crep_inline : forall (crep_code : list (funname * (list varname * prog a))) inl_fs,
  (forall e, MEM e crep_code ->
     (fun '(name, (params, body)) =>
        forall e, MEM e (exps_of body) ->
          every_exp (fun x => if classical_dec (forall op es, x = Crepop op es -> LENGTH es = 2) then true else false)
            e) e) /\
  inl_fs ⊑ alist_to_fmap crep_code ->
  forall e, MEM e (compile_inl_prog inl_fs crep_code) ->
     (fun '(name, (params, body)) =>
        forall e, MEM e (exps_of body) ->
          every_exp (fun x => if classical_dec (forall op es, x = Crepop op es -> LENGTH es = 2) then true else false)
            e) e.
Proof.
  intros crep_code inl_fs [Hall Hs] [name [params body]] Hm. unfold compile_inl_prog in Hm.
  apply MEM_In, in_map_iff in Hm as ([name0 [params0 body0]] & Heq & Hin). injection Heq as -> -> <-.
  intros e He.
  destruct (exps_of_inst_inline (inl_fs \\ name) body0 crep_code e) as [H1|[[c ->]|[[v ->]|H1]]].
  - split; [apply (SUBMAP_TRANS _ inl_fs); split; [apply SUBMAP_DOMSUB|exact Hs]|exact He].
  - exact (Hall (name, (params, body0)) (proj2 (MEM_In _ _) Hin) e H1).
  - cbn [every_exp]. destruct (classical_dec _) as [_|Hn]; [reflexivity|].
    exfalso; apply Hn; intros op es E; discriminate E.
  - cbn [every_exp]. destruct (classical_dec _) as [_|Hn]; [reflexivity|].
    exfalso; apply Hn; intros op es E; discriminate E.
  - destruct H1 as (name' & params' & body' & H2 & H3).
    exact (Hall (name', (params', body')) H2 e H3).
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "fst_map_3_f" *)
Theorem fst_map_3_f : forall inl_fs (x : funname * (list varname * prog a)),
  FST x = (FST ∘ (fun '(name, (params, body)) => (name, (params, inline_prog (fdomsub inl_fs name) body)))) x.
Proof. intros inl_fs [name [params body]]. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "compile_inline_distinct" *)
Theorem compile_inline_distinct : forall (crep_code : list (funname * (list varname * prog a))) inl_fs,
  ALL_DISTINCT (MAP FST crep_code) -> ALL_DISTINCT (MAP FST (compile_inl_prog inl_fs crep_code)).
Proof.
  intros crep_code inl_fs H. unfold compile_inl_prog. rewrite map_map.
  erewrite map_ext; [exact H|]. intros [name [params body]]. reflexivity.
Qed.

End ExpsOf.

Section Semantics.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_call_same_result_state" *)
Theorem evaluate_call_same_result_state : forall e (args : list (exp a)) s r s' t inl_fs,
  evaluate (Call NONE e args, s) = (r, s') /\
  state_rel_code s t /\
  inl_fs ⊑ code s /\
  locals_strong_rel s t /\
  code_inl_rel inl_fs s t /\
  r <> SOME Error ->
  FST (evaluate (Call NONE e args, t)) = FST (evaluate (Call NONE e args, s)) /\
  state_rel_code (SND (evaluate (Call NONE e args, s))) (SND (evaluate (Call NONE e args, t))).
Proof.
  intros e args s r s' t inl_fs (H & Hsr & Hfs & Hls & Hci & Hne).
  destruct (inline_prog_correct (Call NONE e args) s r s' inl_fs t FEMPTY
              (conj H (conj Hne (conj Hfs (conj (SUBMAP_FEMPTY _) (conj Hsr (conj Hls Hci)))))))
    as (t' & Ht & Hs' & _).
  rewrite (proj1 inline_prog_def) in Ht. cbv zeta beta iota in Ht. rewrite FLOOKUP_EMPTY in Ht.
  rewrite Ht, H. cbn [fst snd]. split; [reflexivity|exact Hs'].
Qed.

Lemma ALOOKUP_MAP_inl (l : list (funname * (list varname * prog a))) (g : funname -> prog a -> prog a) k :
  ALOOKUP (MAP (fun '(name, (params, body)) => (name, (params, g name body))) l) k =
  match ALOOKUP l k with SOME (params, body) => SOME (params, g k body) | NONE => NONE end.
Proof.
  induction l as [|[name [params body]] l IH]; [reflexivity|]. cbn [MAP List.map ALOOKUP].
  destruct (decide (name = k)) as [->|]; [reflexivity|exact IH].
Qed.

Lemma ALOOKUP_FILTER_key (l : list (funname * (list varname * prog a))) names k :
  ALOOKUP (FILTER (fun '(x, y) => MEM x names) l) k = if MEM k names then ALOOKUP l k else NONE.
Proof.
  induction l as [|[x y] l IH]; [destruct (MEM k names); reflexivity|]. cbn [List.filter ALOOKUP].
  destruct (MEM x names) eqn:Ex; cbn [ALOOKUP].
  - destruct (decide (x = k)) as [->|]; [rewrite Ex; reflexivity|exact IH].
  - rewrite IH. destruct (decide (x = k)) as [->|]; [rewrite Ex; reflexivity|reflexivity].
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "state_rel_imp_semantics_local" *)
Theorem state_rel_imp_semantics_local : forall s t (crep_code : list (funname * (list varname * prog a)))
    start inl_fs ns prog,
  state_rel_code s t /\
  locals_strong_rel s t /\
  ALL_DISTINCT (MAP FST crep_code) /\
  code s = alist_to_fmap crep_code /\
  inl_fs ⊑ code s /\
  code t = alist_to_fmap (compile_inl_prog inl_fs crep_code) /\
  FLOOKUP (code s) start = SOME (ns, prog) /\
  semantics s start <> Fail ->
  semantics t start = semantics s start.
Proof.
  intros s t crep_code start inl_fs ns prog (Hsr & Hls & _ & Hcs & Hfs & Hct & _ & Hsem).
  assert (Hci : code_inl_rel inl_fs s t).
  { intros fname args prog' Hf. exists (inl_fs \\ fname). split; [apply SUBMAP_DOMSUB|].
    rewrite Hct, FLOOKUP_alist_to_fmap. unfold compile_inl_prog. rewrite ALOOKUP_MAP_inl.
    rewrite Hcs, FLOOKUP_alist_to_fmap in Hf. rewrite Hf. reflexivity. }
  rewrite crep_to_loopProof.crep_sem_is_wrapper in Hsem |- *. rewrite crep_to_loopProof.crep_sem_is_wrapper.
  cbv zeta in Hsem |- *. f_equal. apply functional_extensionality. intros k. unfold PAIR_MAP. cbv beta.
  destruct (evaluate (Call NONE start [], set_clock k s)) as [r s'] eqn:E.
  assert (Hne : r <> SOME Error).
  { intros ->. apply Hsem. unfold crep_to_loopProof.semantics_wrapper.
    destruct (classical_dec _) as [_|Hn]; [reflexivity|]. exfalso; apply Hn.
    exists k, (io_events (ffi s')). unfold PAIR_MAP. cbv beta. rewrite E. reflexivity. }
  destruct (evaluate_call_same_result_state start [] (set_clock k s) r s' (set_clock k t) inl_fs)
    as [H1 H2].
  { split; [exact E|]. split; [unfold state_rel_code in *; cbn; intuition congruence|].
    split; [exact Hfs|]. split; [exact Hls|]. split; [|exact Hne].
    apply (code_inl_rel_code inl_fs s t); [reflexivity|reflexivity|exact Hci]. }
  rewrite E in H1, H2. destruct (evaluate (Call NONE start [], set_clock k t)) as [r' t'] eqn:E'.
  cbn [FST SND fst snd] in H1, H2 |- *. rewrite H1.
  destruct H2 as (_ & _ & _ & _ & _ & _ & Hff & _). rewrite Hff. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_inlineProofScript.sml" "state_rel_imp_semantics" *)
Theorem state_rel_imp_semantics : forall s t (crep_code : list (funname * (list varname * prog a)))
    start inl_fname ns prog,
  state_rel_code s t /\
  locals_strong_rel s t /\
  ALL_DISTINCT (MAP FST crep_code) /\
  code s = alist_to_fmap crep_code /\
  code t = alist_to_fmap (compile_inl_top inl_fname crep_code) /\
  FLOOKUP (code s) start = SOME (ns, prog) /\
  semantics s start <> Fail ->
  semantics t start = semantics s start.
Proof.
  intros s t crep_code start inl_fname ns prog (Hsr & Hls & Hd & Hcs & Hct & Hf & Hsem).
  unfold compile_inl_top in Hct. cbv zeta in Hct.
  assert (Hsub : alist_to_fmap (FILTER (fun '(x, y) => MEM x inl_fname) crep_code) ⊑ code s).
  { intros k v Hk. rewrite FLOOKUP_alist_to_fmap, ALOOKUP_FILTER_key in Hk. rewrite Hcs, FLOOKUP_alist_to_fmap.
    destruct (MEM k inl_fname); [exact Hk|discriminate]. }
  exact (state_rel_imp_semantics_local s t crep_code start
           (alist_to_fmap (FILTER (fun '(x, y) => MEM x inl_fname) crep_code)) ns prog
           (conj Hsr (conj Hls (conj Hd (conj Hcs (conj Hsub (conj Hct (conj Hf Hsem)))))))).
Qed.

End Semantics.
