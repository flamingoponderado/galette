(** * Pancake [crep_inlineProof]: correctness of function inlining (partial)

    Port of the first part of
    [cakeml/pancake/proofs/crep_inlineProofScript.sml]: the state and
    locals relations and the simulation lemmas for [evaluate] on extended
    locals and nested declarations.  The rest of the script is not ported
    yet (see the list at the end of this file).

    Carrier notes as in [crepProps]: HOL's [s with locals := l] is
    [set_locals l s]; [SUBMAP] is [⊑]; [FDOM] is a predicate.

    Proof method: the simulation [evaluate_state_locals_rel_strong] is
    derived from the Galette-only lemma [evaluate_FUNION_locals]: running a
    program on [s] with extra locals [X] ([FUNION (locals s) X]) gives the
    same result and, for the results that continue, the same final locals
    extended by [X].  It is proved by well-founded induction on [eval_lt],
    as in [crepProps]. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require asm.
From Galette.cakeml.pancake Require Import pan_common crepLang crep_inline.
From Galette.cakeml.pancake.semantics Require panSem.
From Galette.cakeml.pancake.semantics Require Import pan_commonProps crepSem crepProps.
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

Definition cont_res (r : option (result a)) : bool :=
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
  evaluate (p, s) = (r, t) -> cont_res r = true -> dom_eq (locals s) (locals t).
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall r t,
            evaluate x = (r, t) -> cont_res r = true -> dom_eq (locals (snd x)) (locals t))
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

Definition ext_res (X : fmap varname (word_lab a)) (r : option (result a)) (s' t' : state a ffi_t) : Prop :=
  state_rel s' t' /\ (cont_res r = true -> t' = set_locals (FUNION (locals s') X) s').

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

Ltac st_proof :=
  unfold state_rel in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat split;
  cbv beta iota delta [set_clock dec_clock set_locals set_memory set_ffi set_code set_globals
       set_var empty_locals];
  cbn [clock locals globals code memory memaddrs sh_memaddrs be ffi base_addr top_addr];
  first [ reflexivity
        | f_equal; first [ congruence | apply fmap_ext; intros; rewrite ?FUNION_FUPDATE_LIST; fm_auto ] ].

Ltac ext_rw IH X :=
  match goal with
  | E : evaluate (?q, ?Y) = (?r1, ?s1) |- context [evaluate (?q, ?Yg)] =>
      let X' := match goal with
                | _ => constr:(X)
                end in
      first [ replace Yg with (set_locals (FUNION (locals Y) X) Y) by st_proof;
              let t1 := fresh "t" in let Ht := fresh "Ht" in let Hr := fresh "Hrel" in
              let Hc := fresh "Hcont" in
              destruct (IH (q, Y) ltac:(lt_tac) r1 s1 X E ltac:(first [discriminate | assumption | congruence]))
                as (t1 & Ht & Hr & Hc);
              clear E; rewrite Ht; cbn beta iota zeta;
              try (specialize (Hc eq_refl); subst t1)
            | replace Yg with (set_locals (FUNION (locals Y) FEMPTY) Y) by st_proof;
              let t1 := fresh "t" in let Ht := fresh "Ht" in let Hr := fresh "Hrel" in
              let Hc := fresh "Hcont" in
              destruct (IH (q, Y) ltac:(lt_tac) r1 s1 FEMPTY E ltac:(first [discriminate | assumption | congruence]))
                as (t1 & Ht & Hr & Hc);
              clear E; rewrite Ht; cbn beta iota zeta;
              try (specialize (Hc eq_refl); subst t1) ]
  end.

Ltac ext_exps X :=
  repeat match goal with
  | E : eval ?s ?e = SOME ?v |- context [eval (set_locals (FUNION (locals ?s) X) ?s) ?e] =>
      rewrite (eval_FUNION s X e v E)
  | E : OPT_MMAP (eval ?s) ?es = SOME ?v |- context [OPT_MMAP (eval (set_locals (FUNION (locals ?s) X) ?s)) ?es] =>
      rewrite (opt_mmap_eval_FUNION s X es v E)
  | E : OPT_MMAP (FLOOKUP ?f) ?l = SOME ?v |- context [OPT_MMAP (FLOOKUP (FUNION ?f X)) ?l] =>
      rewrite (OPT_MMAP_FLOOKUP_FUNION f X l v E)
  | |- context [FLOOKUP (FUNION ?f X) ?k] => rewrite (FLOOKUP_FUNION f X k)
  | E : (?L && (EVERY ?P ?l && ?D))%bool = true |- context [(?L && (EVERY ?Q ?l && ?D))%bool] =>
      lazymatch Q with P => fail | _ => idtac end;
      replace (L && (EVERY Q l && D))%bool with true
        by (symmetry; apply Bool.andb_true_iff in E as [E1 E2];
            apply Bool.andb_true_iff in E2 as [E3 E4];
            rewrite E1, E4, (EVERY_IS_SOME_FUNION _ X _ E3); reflexivity)
  | |- context [match FLOOKUP ?f ?k with _ => _ end] =>
      lazymatch f with FUNION _ _ => fail | _ => idtac end;
      let E := fresh "EF" in destruct (FLOOKUP f k) eqn:E
  end; cbn beta iota zeta.

End Ext.
