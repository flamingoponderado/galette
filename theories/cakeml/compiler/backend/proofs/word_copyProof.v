(** * CakeML [word_copyProof]: correctness of [word_copy]

    Port of [cakeml/compiler/backend/proofs/word_copyProofScript.sml].

    Notes:
    - HOL's free variables are quantified explicitly (first, when HOL's
      statement quantifies only some of them).  HOL [s with f := v] is
      [set_f v s]; HOL's [c ∈ domain t] is [c IN domain t].
    - HOL's [is_alloc_var] is [reg_alloc.is_alloc_var].
    - Not ported: the ML function [word_exp_cong_tac] (a proof tactic).
    - Proofs are by structural induction on programs ([prog_nested_ind])
      instead of HOL's recursion-induction principles; the Galette-only
      tactics and helpers below have no HOL original. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common wordLang word_copy.
From Galette.cakeml.compiler.backend.reg_alloc Require reg_alloc.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem wordConvs.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import
  consts consts_with clock dec_clock.
Open Scope N_scope.

(** ** Galette-only helpers *)

Lemma bd_true (P : Prop) `{Decision P} : P -> bool_decide P = true.
Proof. apply bool_decide_spec. Qed.
Lemma bd_false (P : Prop) `{Decision P} : ~ P -> bool_decide P = false.
Proof. intros HP; destruct (bool_decide P) eqn:E; [|reflexivity]. apply bool_decide_spec in E; tauto. Qed.

Lemma domain_lookup' {A} (t : spt A) k : k IN domain t <-> exists v, lookup k t = Some v.
Proof. apply domain_lookup. Qed.

(** Unfold the copy-state operations and split every decision. *)
Ltac cps :=
  repeat first
    [ progress cbn [to_eq from_eq store_to_eq next empty_eq] in *
    | progress (rewrite ?lookup_insert in * )
    | match goal with
      | |- context [decide (?x = ?y)] => destruct (decide (x = y)); try subst x
      | H : context [decide (?x = ?y)] |- _ => destruct (decide (x = y)); try subst x
      | H : lookup _ LN = Some _ |- _ => discriminate H
      | H : Some _ = Some _ |- _ => injection H as H
      | H : Some _ = None |- _ => discriminate H
      | H : None = Some _ |- _ => discriminate H
      end ].

(** ** The copy-state invariant *)

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_inv_def" *)
Definition CPstate_inv (cs : copy_state) : Prop :=
  (forall v c, lookup v (to_eq cs) = SOME c -> c < next cs) /\
  (forall c, c IN domain (from_eq cs) -> c < next cs) /\
  (forall s c, ALOOKUP (store_to_eq cs) s = SOME c -> c < next cs) /\
  (forall c v, lookup c (from_eq cs) = SOME v -> lookup v (to_eq cs) = SOME c).

Section Inv.
Implicit Types cs : copy_state.

Lemma lookup_inter_eq_some_cp (m1 m2 : num_map N) k x :
  lookup k (inter_eq m1 m2) = SOME x -> lookup k m1 = SOME x /\ lookup k m2 = SOME x.
Proof.
  intros H. rewrite lookup_inter_eq in H. destruct (lookup k m1); [|discriminate].
  destruct (decide _) as [E|]; [|discriminate]. injection H as ->. auto.
Qed.

Lemma inv_from cs c v : CPstate_inv cs -> lookup c (from_eq cs) = SOME v -> c < next cs.
Proof. intros (_ & H2 & _) H. apply H2, domain_lookup'. eauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "unique_rep" *)
Theorem unique_rep : forall cs c c',
  CPstate_inv cs ->
  c IN domain (from_eq cs) /\ c' IN domain (from_eq cs) /\ c <> c' ->
  lookup c (from_eq cs) <> lookup c' (from_eq cs).
Proof.
  intros cs c c' (_ & _ & _ & H4) (Hc & Hc' & Hne) E.
  apply domain_lookup' in Hc as [v Hv]. rewrite Hv in E. symmetry in E.
  pose proof (H4 _ _ Hv) as A. pose proof (H4 _ _ E) as B. congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "empty_eq_inv" *)
Theorem empty_eq_inv : CPstate_inv empty_eq.
Proof.
  repeat split; intros *; try (intros H; apply domain_lookup' in H as [v Hv]);
    cbn in *; try discriminate; try contradiction.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "remove_eq_inv" *)
Theorem remove_eq_inv : forall cs v, CPstate_inv cs -> CPstate_inv (remove_eq cs v).
Proof. intros cs v H. unfold remove_eq. destruct (lookup v (to_eq cs)); [apply empty_eq_inv|exact H]. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "remove_eqs_inv" *)
Theorem remove_eqs_inv : forall vv cs, CPstate_inv cs -> CPstate_inv (remove_eqs cs vv).
Proof. induction vv as [|v vv IH]; intros cs H; [exact H|]. apply IH, remove_eq_inv, H. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "n_lt_n1" *)
Theorem n_lt_n1 : forall n x y z, n < n + 1 /\ (x < y /\ y < z -> x < z).
Proof. intros; split; lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "set_eq_inv" *)
Theorem set_eq_inv : forall cs t s,
  CPstate_inv cs /\ lookup t (to_eq cs) = NONE -> CPstate_inv (set_eq cs t s).
Proof.
  intros cs t s [(H1 & H2 & H3 & H4) Ht]. unfold set_eq.
  destruct (reg_alloc.is_alloc_var t && reg_alloc.is_alloc_var s); [|repeat split; assumption].
  assert (G : forall c' x, lookup c' (from_eq cs) = SOME x -> c' < next cs)
    by (intros c' x Hx; apply H2, domain_lookup'; eauto).
  destruct (lookup s (to_eq cs)) as [c|] eqn:Es;
    [destruct (lookup c (from_eq cs)) as [r|] eqn:Ec|].
  - assert (Hc : c < next cs) by (eapply H1; eauto).
    split; [intros v c' Hl|split; [intros c' Hd|split; [intros s0 c' Hl|intros c' v Hl]]]; cbn in *.
    + rewrite lookup_insert in Hl. destruct (decide (v = t)); [injection Hl as <-; exact Hc|eauto].
    + apply domain_lookup' in Hd as [v Hv]. rewrite lookup_insert in Hv.
      destruct (decide (c' = c)); [subst; exact Hc|eauto].
    + eauto.
    + rewrite lookup_insert in Hl. destruct (decide (c' = c)) as [->|Hne].
      * injection Hl as <-. rewrite lookup_insert. destruct (decide (t = t)); [reflexivity|congruence].
      * pose proof (H4 _ _ Hl) as A. rewrite lookup_insert. destruct (decide (v = t)); [congruence|exact A].
  - split; [intros v c' Hl|split; [intros c' Hd|split; [intros s0 c' Hl|intros c' v Hl]]]; cbn in *.
    + rewrite !lookup_insert in Hl. destruct (decide (v = t)); [injection Hl as <-; lia|].
      destruct (decide (v = s)); [injection Hl as <-; lia|]. specialize (H1 _ _ Hl); lia.
    + apply domain_lookup' in Hd as [v Hv]. rewrite lookup_insert in Hv.
      destruct (decide (c' = next cs)); [lia|]. specialize (G _ _ Hv); lia.
    + specialize (H3 _ _ Hl); lia.
    + rewrite lookup_insert in Hl. destruct (decide (c' = next cs)) as [->|Hne].
      * injection Hl as <-. rewrite lookup_insert. destruct (decide (t = t)); [reflexivity|congruence].
      * pose proof (H4 _ _ Hl) as A. rewrite !lookup_insert.
        destruct (decide (v = t)); [congruence|]. destruct (decide (v = s)) as [->|]; [congruence|exact A].
  - split; [intros v c' Hl|split; [intros c' Hd|split; [intros s0 c' Hl|intros c' v Hl]]]; cbn in *.
    + rewrite !lookup_insert in Hl. destruct (decide (v = t)); [injection Hl as <-; lia|].
      destruct (decide (v = s)); [injection Hl as <-; lia|]. specialize (H1 _ _ Hl); lia.
    + apply domain_lookup' in Hd as [v Hv]. rewrite lookup_insert in Hv.
      destruct (decide (c' = next cs)); [lia|]. specialize (G _ _ Hv); lia.
    + specialize (H3 _ _ Hl); lia.
    + rewrite lookup_insert in Hl. destruct (decide (c' = next cs)) as [->|Hne].
      * injection Hl as <-. rewrite lookup_insert. destruct (decide (t = t)); [reflexivity|congruence].
      * pose proof (H4 _ _ Hl) as A. rewrite !lookup_insert.
        destruct (decide (v = t)); [congruence|]. destruct (decide (v = s)) as [->|]; [congruence|exact A].
Qed.

Lemma ALOOKUP_merge (l1 l2 l : list (stackLang.store_name * N)) x c :
  ALOOKUP (FILTER (fun '(s, c) => bool_decide (ALOOKUP l1 s = Some c) &&
                                  bool_decide (ALOOKUP l2 s = Some c)) l) x = Some c ->
  ALOOKUP l1 x = Some c /\ ALOOKUP l2 x = Some c.
Proof.
  intros H. apply ALOOKUP_In, filter_In in H as [_ H].
  apply andb_prop in H as [H1 H2]. apply bool_decide_spec in H1, H2. auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "merge_eqs_inv" *)
Theorem merge_eqs_inv : forall cs1 cs2,
  CPstate_inv cs1 /\ CPstate_inv cs2 -> CPstate_inv (merge_eqs cs1 cs2).
Proof.
  intros cs1 cs2 [(A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4)]. unfold merge_eqs.
  split; [intros v c Hl|split; [intros c Hd|split; [intros s0 c Hl|intros c v Hl]]];
    cbn [to_eq from_eq store_to_eq next] in *; rewrite ?MAX_max.
  - apply lookup_inter_eq_some_cp in Hl as [Hl _]. specialize (A1 _ _ Hl); lia.
  - apply domain_lookup' in Hd as [v Hv]. apply lookup_inter_eq_some_cp in Hv as [Hv _].
    assert (D : c IN domain (from_eq cs1)) by (apply domain_lookup'; eauto). specialize (A2 _ D); lia.
  - apply ALOOKUP_merge in Hl as [Hl _]. specialize (A3 _ _ Hl); lia.
  - apply lookup_inter_eq_some_cp in Hl as [H1 H2].
    rewrite lookup_inter_eq, (A4 _ _ H1). rewrite (B4 _ _ H2). destruct (decide _); [reflexivity|congruence].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "set_store_eq_inv" *)
Theorem set_store_eq_inv : forall cs name e, CPstate_inv cs -> CPstate_inv (set_store_eq cs name e).
Proof.
  intros cs name e (H1 & H2 & H3 & H4). unfold set_store_eq.
  destruct (reg_alloc.is_alloc_var e); [|apply empty_eq_inv].
  assert (G : forall c' x, lookup c' (from_eq cs) = SOME x -> c' < next cs)
    by (intros c' x Hx; apply H2, domain_lookup'; eauto).
  destruct (lookup e (to_eq cs)) as [c|] eqn:Es;
    [destruct (lookup c (from_eq cs)) as [r|] eqn:Ec|].
  - split; [intros v c' Hl|split; [intros c' Hd|split; [intros s0 c' Hl|intros c' v Hl]]];
      cbn [to_eq from_eq store_to_eq next ALOOKUP] in *; eauto.
    destruct (decide (name = s0)); [injection Hl as <-; eauto|eauto].
  - split; [intros v c' Hl|split; [intros c' Hd|split; [intros s0 c' Hl|intros c' v Hl]]];
      cbn [to_eq from_eq store_to_eq next ALOOKUP] in *.
    + rewrite lookup_insert in Hl. destruct (decide (v = e)); [injection Hl as <-; lia|].
      specialize (H1 _ _ Hl); lia.
    + apply domain_lookup' in Hd as [v Hv]. rewrite lookup_insert in Hv.
      destruct (decide (c' = next cs)); [lia|]. specialize (G _ _ Hv); lia.
    + destruct (decide (name = s0)); [injection Hl as <-; lia|]. specialize (H3 _ _ Hl); lia.
    + rewrite lookup_insert in Hl. destruct (decide (c' = next cs)) as [->|Hne].
      * injection Hl as <-. rewrite lookup_insert. destruct (decide (e = e)); [reflexivity|congruence].
      * pose proof (H4 _ _ Hl) as A. rewrite lookup_insert. destruct (decide (v = e)) as [->|]; [congruence|exact A].
  - split; [intros v c' Hl|split; [intros c' Hd|split; [intros s0 c' Hl|intros c' v Hl]]];
      cbn [to_eq from_eq store_to_eq next ALOOKUP] in *.
    + rewrite lookup_insert in Hl. destruct (decide (v = e)); [injection Hl as <-; lia|].
      specialize (H1 _ _ Hl); lia.
    + apply domain_lookup' in Hd as [v Hv]. rewrite lookup_insert in Hv.
      destruct (decide (c' = next cs)); [lia|]. specialize (G _ _ Hv); lia.
    + destruct (decide (name = s0)); [injection Hl as <-; lia|]. specialize (H3 _ _ Hl); lia.
    + rewrite lookup_insert in Hl. destruct (decide (c' = next cs)) as [->|Hne].
      * injection Hl as <-. rewrite lookup_insert. destruct (decide (e = e)); [reflexivity|congruence].
      * pose proof (H4 _ _ Hl) as A. rewrite lookup_insert. destruct (decide (v = e)) as [->|]; [congruence|exact A].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "same_classD" *)
Theorem same_classD : forall cs x y,
  CPstate_inv cs /\ lookup_eq cs x = lookup_eq cs y ->
  x = y \/ (x <> y /\ exists c rep,
    lookup x (to_eq cs) = SOME c /\ lookup y (to_eq cs) = SOME c /\ lookup c (from_eq cs) = SOME rep).
Proof.
  intros cs x y [(_ & _ & _ & H4) E]. destruct (decide (x = y)) as [|Hne]; [left; assumption|right; split; [exact Hne|]].
  unfold lookup_eq in E.
  destruct (lookup x (to_eq cs)) as [cx|] eqn:Ex; [destruct (lookup cx (from_eq cs)) as [rx|] eqn:Rx|];
  destruct (lookup y (to_eq cs)) as [cy|] eqn:Ey; try destruct (lookup cy (from_eq cs)) as [ry|] eqn:Ry;
    subst; try congruence.
  - pose proof (H4 _ _ Rx) as A. pose proof (H4 _ _ Ry) as B. assert (cx = cy) by congruence. subst. eauto.
  - pose proof (H4 _ _ Rx) as A. congruence.
  - pose proof (H4 _ _ Rx) as A. congruence.
  - pose proof (H4 _ _ Ry) as B. congruence.
  - pose proof (H4 _ _ Ry) as B. congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "same_classD'" *)
Theorem same_classD' : forall cs x y,
  CPstate_inv cs /\ lookup_store_eq cs x = SOME (lookup_eq cs y) ->
  exists c rep, ALOOKUP (store_to_eq cs) x = SOME c /\ lookup y (to_eq cs) = SOME c /\
                lookup c (from_eq cs) = SOME rep.
Proof.
  intros cs x y [(_ & _ & _ & H4) E]. unfold lookup_store_eq, lookup_eq in E.
  destruct (ALOOKUP (store_to_eq cs) x) as [c|] eqn:Ec; [|discriminate].
  destruct (lookup c (from_eq cs)) as [r|] eqn:Rc; [|discriminate]. injection E as E.
  pose proof (H4 _ _ Rc) as A.
  destruct (lookup y (to_eq cs)) as [cy|] eqn:Ey; [destruct (lookup cy (from_eq cs)) as [ry|] eqn:Ry|]; subst.
  - pose proof (H4 _ _ Ry) as B. assert (c = cy) by congruence. subst. eauto.
  - exists c. eexists. split; [reflexivity|]. split; [|eassumption]. congruence.
  - congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eqI" *)
Theorem lookup_eqI : forall cs r v,
  (r = v /\ lookup v (to_eq cs) = NONE) \/
  (exists c, lookup v (to_eq cs) = SOME c /\ lookup c (from_eq cs) = SOME r) ->
  lookup_eq cs v = r.
Proof.
  intros cs r v [[-> H]|[c [H1 H2]]]; unfold lookup_eq; [rewrite H; reflexivity|rewrite H1, H2; reflexivity].
Qed.

End Inv.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "both_alloc_vars_def" *)
Definition both_alloc_vars (p : N * N) : bool :=
  let '(t, s) := p in reg_alloc.is_alloc_var t && reg_alloc.is_alloc_var s.


Section SetEq.
Implicit Types cs : copy_state.

Lemma lookup_eq_rep_fresh cs t v :
  CPstate_inv cs -> lookup t (to_eq cs) = NONE -> lookup_eq cs v = t -> v = t.
Proof.
  intros (_ & _ & _ & H4) Ht E. unfold lookup_eq in E.
  destruct (lookup v (to_eq cs)) as [c|] eqn:Ev; [|exact E].
  destruct (lookup c (from_eq cs)) as [r|] eqn:Ec; [|exact E]. subst r.
  pose proof (H4 _ _ Ec). congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eq_set_eq_not_alloc_var" *)
Theorem lookup_eq_set_eq_not_alloc_var : forall t s cs v,
  ~ both_alloc_vars (t, s) -> lookup_eq (set_eq cs t s) v = lookup_eq cs v.
Proof.
  intros t s cs v H. unfold set_eq. cbn [both_alloc_vars] in H.
  destruct (reg_alloc.is_alloc_var t && reg_alloc.is_alloc_var s); [exfalso; apply H; reflexivity|reflexivity].
Qed.

(** The two cases of [set_eq] on allocatable variables. *)
Lemma set_eq_cases cs t s :
  both_alloc_vars (t, s) ->
  (exists c r, lookup s (to_eq cs) = SOME c /\ lookup c (from_eq cs) = SOME r /\
     set_eq cs t s = {| to_eq := insert t c (to_eq cs); from_eq := insert c t (from_eq cs);
                       store_to_eq := store_to_eq cs; next := next cs |}) \/
  ((forall c, lookup s (to_eq cs) = SOME c -> lookup c (from_eq cs) = NONE) /\
     set_eq cs t s = {| to_eq := insert t (next cs) (insert s (next cs) (to_eq cs));
                       from_eq := insert (next cs) t (from_eq cs);
                       store_to_eq := store_to_eq cs; next := next cs + 1 |}).
Proof.
  intros H. cbn [both_alloc_vars] in H. unfold set_eq. unfold is_true in H. rewrite H.
  destruct (lookup s (to_eq cs)) as [c|] eqn:Es; [destruct (lookup c (from_eq cs)) as [r|] eqn:Ec|].
  - left. eauto.
  - right. split; [intros c' E; injection E as <-; exact Ec|reflexivity].
  - right. split; [discriminate|reflexivity].
Qed.

Ltac le_unfold := unfold lookup_eq; cbn [to_eq from_eq store_to_eq next].
Ltac ins :=
  repeat first
    [ rewrite lookup_insert
    | match goal with
      | |- context [decide (?x = ?x)] => destruct (decide (x = x)); [|congruence]
      | |- context [decide ?P] => destruct (decide P); try congruence
      end ].

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eq_set_eq_t" *)
Theorem lookup_eq_set_eq_t : forall cs t s,
  CPstate_inv cs /\ both_alloc_vars (t, s) -> lookup_eq (set_eq cs t s) t = t.
Proof.
  intros cs t s [Hi Hb]. destruct (set_eq_cases cs t s Hb) as [(c & r & _ & _ & ->)|(_ & ->)];
    le_unfold; ins; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eq_set_eq_is_alloc_var1" *)
Theorem lookup_eq_set_eq_is_alloc_var1 : forall cs t s v,
  CPstate_inv cs /\ both_alloc_vars (t, s) ->
  lookup t (to_eq cs) = NONE ->
  lookup_eq cs s = lookup_eq cs v ->
  lookup_eq (set_eq cs t s) v = t.
Proof.
  intros cs t s v [Hi Hb] Ht E.
  destruct (same_classD cs s v (conj Hi E)) as [<-|(Hne & c & r & Hs & Hv & Hc)].
  - destruct (decide (s = t)) as [->|Hst]; [apply lookup_eq_set_eq_t; auto|].
    destruct (set_eq_cases cs t s Hb) as [(c & r & Hs & Hc & ->)|(_ & ->)];
      le_unfold; ins; try rewrite Hs; ins; try reflexivity.
  - assert (Hvt : v <> t) by congruence.
    destruct (set_eq_cases cs t s Hb) as [(c' & r' & Hs' & Hc' & ->)|(Hn & _)];
      [|exfalso; specialize (Hn _ Hs); congruence].
    assert (c' = c) by congruence. subst c'.
    le_unfold. rewrite lookup_insert. destruct (decide (v = t)); [congruence|]. rewrite Hv.
    rewrite lookup_insert. destruct (decide (c = c)); [reflexivity|congruence].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eq_set_eq_is_alloc_var2" *)
Theorem lookup_eq_set_eq_is_alloc_var2 : forall cs t s v,
  CPstate_inv cs /\ both_alloc_vars (t, s) ->
  lookup t (to_eq cs) = NONE ->
  v <> t ->
  lookup_eq cs s <> lookup_eq cs v ->
  lookup_eq (set_eq cs t s) v = lookup_eq cs v.
Proof.
  intros cs t s v [Hi Hb] Ht Hvt Hne. pose proof Hi as (H1 & H2 & H3 & H4).
  destruct (set_eq_cases cs t s Hb) as [(c & r & Hs & Hc & ->)|(Hn & ->)]; le_unfold;
    rewrite lookup_insert; destruct (decide (v = t)); try congruence.
  - destruct (lookup v (to_eq cs)) as [cv|] eqn:Ev; [|reflexivity].
    rewrite lookup_insert. destruct (decide (cv = c)) as [->|]; [|reflexivity].
    exfalso. apply Hne. unfold lookup_eq. rewrite Hs, Hc, Ev, Hc. reflexivity.
  - rewrite lookup_insert. destruct (decide (v = s)) as [->|]; [exfalso; apply Hne; reflexivity|].
    destruct (lookup v (to_eq cs)) as [cv|] eqn:Ev; [|reflexivity].
    rewrite lookup_insert. destruct (decide (cv = next cs)) as [->|]; [|reflexivity].
    specialize (H1 _ _ Ev). lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eq_set_eq_s" *)
Theorem lookup_eq_set_eq_s : forall cs t s,
  CPstate_inv cs /\ both_alloc_vars (t, s) ->
  lookup t (to_eq cs) = NONE -> lookup_eq (set_eq cs t s) s = t.
Proof.
  intros cs t s H Ht. destruct (decide (s = t)) as [->|]; [apply lookup_eq_set_eq_t, H|].
  apply lookup_eq_set_eq_is_alloc_var1; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eq_set_eqD" *)
Theorem lookup_eq_set_eqD : forall cs t s v r,
  CPstate_inv cs ->
  lookup t (to_eq cs) = NONE ->
  lookup_eq (set_eq cs t s) v = r ->
  (r = t -> v = t \/ lookup_eq cs v = lookup_eq cs s) /\
  (r <> t -> r = lookup_eq cs v).
Proof.
  intros cs t s v r Hi Ht E.
  destruct (both_alloc_vars (t, s)) eqn:Hb.
  - destruct (decide (lookup_eq cs s = lookup_eq cs v)) as [Es|Ns].
    + rewrite (lookup_eq_set_eq_is_alloc_var1 cs t s v (conj Hi Hb) Ht Es) in E. subst r.
      split; [intros _; right; symmetry; exact Es|congruence].
    + destruct (decide (v = t)) as [->|Hvt].
      * rewrite (lookup_eq_set_eq_t cs t s (conj Hi Hb)) in E. subst r. split; [left; reflexivity|congruence].
      * rewrite (lookup_eq_set_eq_is_alloc_var2 cs t s v (conj Hi Hb) Ht Hvt Ns) in E. subst r.
        split; [intros Er; exfalso; apply Hvt; exact (lookup_eq_rep_fresh cs t v Hi Ht Er)|reflexivity].
  - rewrite lookup_eq_set_eq_not_alloc_var in E by (rewrite Hb; discriminate). subst r.
    split; [intros Er; left; exact (lookup_eq_rep_fresh cs t v Hi Ht Er)|reflexivity].
Qed.

End SetEq.

(** ** Models *)

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_models_def" *)
Definition CPstate_models {a c ffi_t} (cs : copy_state) (S : state a c ffi_t) : Prop :=
  (forall v c vrep, lookup v (to_eq cs) = SOME c -> lookup c (from_eq cs) = SOME vrep ->
                    lookup v (locals S) = lookup vrep (locals S)) /\
  (forall s c vrep, ALOOKUP (store_to_eq cs) s = SOME c -> lookup c (from_eq cs) = SOME vrep ->
                    FLOOKUP (store S) s = lookup vrep (locals S)).

Section Models.
Context {a : N} {c ffi_t : Type}.
Implicit Types cs : copy_state.
Implicit Types s st : state a c ffi_t.

(** HOL's bound variables [c] and [ffi] are [c0] and [ffi0]. *)
(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_models_with_const" *)
Theorem CPstate_models_with_const : forall cs s ls fp xs sl sm ssize m md smd p c0 co cb db g hd clk tdep cd b ffi0,
  CPstate_models cs (set_locals_size ls s) = CPstate_models cs s /\
  CPstate_models cs (set_fp_regs fp s) = CPstate_models cs s /\
  CPstate_models cs (set_stack xs s) = CPstate_models cs s /\
  CPstate_models cs (set_stack_limit sl s) = CPstate_models cs s /\
  CPstate_models cs (set_stack_max sm s) = CPstate_models cs s /\
  CPstate_models cs (set_stack_size ssize s) = CPstate_models cs s /\
  CPstate_models cs (set_memory m s) = CPstate_models cs s /\
  CPstate_models cs (set_mdomain md s) = CPstate_models cs s /\
  CPstate_models cs (set_sh_mdomain smd s) = CPstate_models cs s /\
  CPstate_models cs (set_permute p s) = CPstate_models cs s /\
  CPstate_models cs (set_compile c0 s) = CPstate_models cs s /\
  CPstate_models cs (set_compile_oracle co s) = CPstate_models cs s /\
  CPstate_models cs (set_code_buffer cb s) = CPstate_models cs s /\
  CPstate_models cs (set_data_buffer db s) = CPstate_models cs s /\
  CPstate_models cs (set_gc_fun g s) = CPstate_models cs s /\
  CPstate_models cs (set_handler hd s) = CPstate_models cs s /\
  CPstate_models cs (set_clock clk s) = CPstate_models cs s /\
  CPstate_models cs (set_termdep tdep s) = CPstate_models cs s /\
  CPstate_models cs (set_code cd s) = CPstate_models cs s /\
  CPstate_models cs (set_be b s) = CPstate_models cs s /\
  CPstate_models cs (set_ffi ffi0 s) = CPstate_models cs s.
Proof. intros; repeat split. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_model" *)
Theorem CPstate_model : forall cs st v,
  CPstate_models cs st -> lookup (lookup_eq cs v) (locals st) = lookup v (locals st).
Proof.
  intros cs st v [H1 _]. unfold lookup_eq.
  destruct (lookup v (to_eq cs)) as [cv|] eqn:Ev; [|reflexivity].
  destruct (lookup cv (from_eq cs)) as [r|] eqn:Ec; [|reflexivity].
  symmetry; exact (H1 _ _ _ Ev Ec).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_modelsI" *)
Theorem CPstate_modelsI : forall cs st,
  CPstate_inv cs /\
  (forall x y, lookup_eq cs x = lookup_eq cs y -> lookup x (locals st) = lookup y (locals st)) /\
  (forall x y, lookup_store_eq cs x = SOME (lookup_eq cs y) -> FLOOKUP (store st) x = lookup y (locals st)) ->
  CPstate_models cs st.
Proof.
  intros cs st [(_ & _ & _ & H4) [A B]]. split.
  - intros v cv vrep Ev Ec. apply A. unfold lookup_eq. rewrite Ev, Ec, (H4 _ _ Ec), Ec. reflexivity.
  - intros s cv vrep Es Ec. apply B. unfold lookup_store_eq, lookup_eq. rewrite Es, Ec, (H4 _ _ Ec), Ec.
    reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_modelsD" *)
Theorem CPstate_modelsD : forall cs st,
  CPstate_inv cs /\ CPstate_models cs st ->
  (forall x y, lookup_eq cs x = lookup_eq cs y -> lookup x (locals st) = lookup y (locals st)) /\
  (forall x y, lookup_store_eq cs x = SOME (lookup_eq cs y) -> FLOOKUP (store st) x = lookup y (locals st)).
Proof.
  intros cs st [Hi [M1 M2]]. split.
  - intros x y E. destruct (same_classD cs x y (conj Hi E)) as [->|(_ & cc & rep & Hx & Hy & Hc)];
      [reflexivity|]. rewrite (M1 _ _ _ Hx Hc), (M1 _ _ _ Hy Hc). reflexivity.
  - intros x y E. destruct (same_classD' cs x y (conj Hi E)) as (cc & rep & Hx & Hy & Hc).
    rewrite (M2 _ _ _ Hx Hc), (M1 _ _ _ Hy Hc). reflexivity.
Qed.

Lemma empty_models st : CPstate_models empty_eq st.
Proof. split; intros *; cbn; discriminate. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "remove_eq_model" *)
Theorem remove_eq_model : forall cs st t, CPstate_models cs st -> CPstate_models (remove_eq cs t) st.
Proof. intros cs st t H. unfold remove_eq. destruct (lookup t (to_eq cs)); [apply empty_models|exact H]. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "remove_eq_model_insert'" *)
Theorem remove_eq_model_insert' : forall cs st (st' : state a c ffi_t) t val,
  CPstate_inv cs /\ CPstate_models cs st /\ locals st' = insert t val (locals st) /\ store st' = store st ->
  CPstate_models (remove_eq cs t) st'.
Proof.
  intros cs st st' t val ((_ & _ & _ & H4) & [M1 M2] & El & Es). unfold remove_eq.
  destruct (lookup t (to_eq cs)) as [ct|] eqn:Et; [apply empty_models|].
  split.
  - intros v cv vrep Ev Ec. rewrite El, !lookup_insert.
    destruct (decide (v = t)); [congruence|]. pose proof (H4 _ _ Ec).
    destruct (decide (vrep = t)); [congruence|]. exact (M1 _ _ _ Ev Ec).
  - intros s0 cv vrep Es0 Ec. rewrite El, Es, lookup_insert. pose proof (H4 _ _ Ec).
    destruct (decide (vrep = t)); [congruence|]. exact (M2 _ _ _ Es0 Ec).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "remove_eq_model_insert" *)
Theorem remove_eq_model_insert : forall cs st t val,
  CPstate_inv cs -> CPstate_models cs st ->
  CPstate_models (remove_eq cs t) (set_locals (insert t val (locals st)) st).
Proof. intros cs st t val Hi Hm. exact (remove_eq_model_insert' cs st (set_locals (insert t val (locals st)) st) t val (conj Hi (conj Hm (conj eq_refl eq_refl)))). Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "remove_eq_model_set_var" *)
Theorem remove_eq_model_set_var : forall cs st t val,
  CPstate_inv cs /\ CPstate_models cs st -> CPstate_models (remove_eq cs t) (set_var t val st).
Proof. intros cs st t val [Hi Hm]. apply remove_eq_model_insert; assumption. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_models_same" *)
Theorem CPstate_models_same : forall cs st (st' : state a c ffi_t),
  CPstate_models cs st /\ locals st' = locals st /\ store st' = store st -> CPstate_models cs st'.
Proof. intros cs st st' ([M1 M2] & El & Es). split; intros *; rewrite ?El, ?Es; eauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "set_fp_var_model" *)
Theorem set_fp_var_model : forall cs st t val,
  CPstate_models cs st -> CPstate_models cs (set_fp_var t val st).
Proof. intros; assumption. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "merge_eqs_model1" *)
Theorem merge_eqs_model1 : forall cs1 cs2 st,
  CPstate_models cs1 st -> CPstate_models (merge_eqs cs1 cs2) st.
Proof.
  intros cs1 cs2 st [M1 M2]. split; cbn [merge_eqs to_eq from_eq store_to_eq].
  - intros v cv vrep Ev Ec. apply lookup_inter_eq_some_cp in Ev as [Ev _].
    apply lookup_inter_eq_some_cp in Ec as [Ec _]. eauto.
  - intros s0 cv vrep Es Ec. apply ALOOKUP_merge in Es as [Es _].
    apply lookup_inter_eq_some_cp in Ec as [Ec _]. eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "merge_eqs_model2" *)
Theorem merge_eqs_model2 : forall cs1 cs2 st,
  CPstate_models cs2 st -> CPstate_models (merge_eqs cs1 cs2) st.
Proof.
  intros cs1 cs2 st [M1 M2]. split; cbn [merge_eqs to_eq from_eq store_to_eq].
  - intros v cv vrep Ev Ec. apply lookup_inter_eq_some_cp in Ev as [_ Ev].
    apply lookup_inter_eq_some_cp in Ec as [_ Ec]. eauto.
  - intros s0 cv vrep Es Ec. apply ALOOKUP_merge in Es as [_ Es].
    apply lookup_inter_eq_some_cp in Ec as [_ Ec]. eauto.
Qed.

End Models.

Section Store.
Implicit Types cs : copy_state.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "set_eq_store_to_eq" *)
Theorem set_eq_store_to_eq : forall cs t s, store_to_eq (set_eq cs t s) = store_to_eq cs.
Proof.
  intros cs t s. unfold set_eq. destruct (_ && _); [|reflexivity].
  destruct (match lookup s (to_eq cs) with Some c => _ | None => _ end) as [?|]; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eq_remove_eq_t" *)
Theorem lookup_eq_remove_eq_t : forall cs t x,
  CPstate_inv cs /\ lookup_eq (remove_eq cs t) x = t -> x = t.
Proof.
  intros cs t x [Hi E]. unfold remove_eq in E. destruct (lookup t (to_eq cs)) eqn:Et.
  - exact E.
  - exact (lookup_eq_rep_fresh cs t x Hi Et E).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_store_eq_set_eqD" *)
Theorem lookup_store_eq_set_eqD : forall cs t s v r,
  CPstate_inv cs -> lookup t (to_eq cs) = NONE ->
  lookup_store_eq (set_eq cs t s) v = SOME r ->
  (r = t -> lookup_store_eq cs v = SOME (lookup_eq cs s)) /\
  (r <> t -> lookup_store_eq cs v = SOME r).
Proof.
  intros cs t s v r Hi Ht E. pose proof Hi as (H1 & H2 & H3 & H4).
  destruct (both_alloc_vars (t, s)) eqn:Hb.
  - destruct (set_eq_cases cs t s Hb) as [(cc & rs & Hs & Hc & Eq)|(Hn & Eq)]; rewrite Eq in E;
      unfold lookup_store_eq in E |- *; cbn [to_eq from_eq store_to_eq next] in E;
      destruct (ALOOKUP (store_to_eq cs) v) as [cv|] eqn:Ev; try discriminate;
      rewrite lookup_insert in E.
    + destruct (decide (cv = cc)) as [->|Hne].
      * injection E as <-. rewrite Hc. unfold lookup_eq. rewrite Hs, Hc. split; [reflexivity|congruence].
      * destruct (lookup cv (from_eq cs)) as [r'|] eqn:Ecv; [|discriminate]. injection E as ->.
        split; [|reflexivity]. intros ->. pose proof (H4 _ _ Ecv). congruence.
    + destruct (decide (cv = next cs)) as [->|Hne]; [specialize (H3 _ _ Ev); lia|].
      destruct (lookup cv (from_eq cs)) as [r'|] eqn:Ecv; [|discriminate]. injection E as ->.
      split; [|reflexivity]. intros ->. pose proof (H4 _ _ Ecv). congruence.
  - unfold set_eq in E. cbn [both_alloc_vars] in Hb. rewrite Hb in E.
    unfold lookup_store_eq in E |- *.
    destruct (ALOOKUP (store_to_eq cs) v) as [cv|] eqn:Ev; [|discriminate].
    destruct (lookup cv (from_eq cs)) as [r'|] eqn:Ecv; [|discriminate]. injection E as ->.
    split; [|reflexivity]. intros ->. pose proof (H4 _ _ Ecv). congruence.
Qed.

End Store.

(** ** Moves *)

Ltac dd :=
  repeat match goal with
         | |- context [decide (?x = ?x)] => destruct (decide (x = x)) as [_|]; [|congruence]
         | H : context [decide (?x = ?x)] |- _ => destruct (decide (x = x)) as [_|]; [|congruence]
         end.

Section MoveModel.
Context {a : N} {c ffi_t : Type}.
Implicit Types cs : copy_state.
Implicit Types st : state a c ffi_t.

Lemma remove_eq_to_eq_t cs t : lookup t (to_eq (remove_eq cs t)) = NONE.
Proof. unfold remove_eq. destruct (lookup t (to_eq cs)) eqn:E; [reflexivity|exact E]. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "copy_prop_move_model_aux" *)
Theorem copy_prop_move_model_aux : forall cs st t s sval,
  CPstate_inv cs /\ CPstate_models cs st /\ both_alloc_vars (t, s) /\
  lookup s (locals st) = SOME sval ->
  CPstate_models (set_eq (remove_eq cs t) t s) (set_locals (insert t sval (locals st)) st).
Proof.
  intros cs st t s sval (Hi & Hm & Hb & Hs).
  pose proof (remove_eq_inv cs t Hi) as Hi1. pose proof (remove_eq_model cs st t Hm) as [M1 M2].
  pose proof (remove_eq_to_eq_t cs t) as Ht.
  set (cs1 := remove_eq cs t) in *. pose proof Hi1 as (H1 & H2 & H3 & H4).
  destruct (set_eq_cases cs1 t s Hb) as [(cc & r & Es & Ec & ->)|(Hn & ->)];
    split; cbn [to_eq from_eq store_to_eq next locals store set_locals].
  - intros v cv vrep Ev Ecv. rewrite !lookup_insert in *.
    destruct (decide (v = t)) as [->|Hvt].
    + injection Ev as <-. dd. injection Ecv as <-. dd. reflexivity.
    + destruct (decide (cv = cc)) as [->|Hne].
      * injection Ecv as <-. dd.
        rewrite (M1 _ _ _ Ev Ec), <- (M1 _ _ _ Es Ec). exact Hs.
      * pose proof (H4 _ _ Ecv). destruct (decide (vrep = t)); [congruence|]. exact (M1 _ _ _ Ev Ecv).
  - intros s0 cv vrep Es0 Ecv. rewrite !lookup_insert in *.
    destruct (decide (cv = cc)) as [->|Hne].
    + injection Ecv as <-. dd.
      rewrite (M2 _ _ _ Es0 Ec), <- (M1 _ _ _ Es Ec). exact Hs.
    + pose proof (H4 _ _ Ecv). destruct (decide (vrep = t)); [congruence|]. exact (M2 _ _ _ Es0 Ecv).
  - intros v cv vrep Ev Ecv. rewrite !lookup_insert in *.
    destruct (decide (v = t)) as [->|Hvt].
    + injection Ev as <-. dd. injection Ecv as <-. dd. reflexivity.
    + destruct (decide (v = s)) as [->|Hvs].
      * injection Ev as <-. dd. injection Ecv as <-. dd. exact Hs.
      * specialize (H1 _ _ Ev) as Hlt. destruct (decide (cv = next cs1)); [lia|].
        pose proof (H4 _ _ Ecv). destruct (decide (vrep = t)); [congruence|]. exact (M1 _ _ _ Ev Ecv).
  - intros s0 cv vrep Es0 Ecv. rewrite !lookup_insert in *.
    specialize (H3 _ _ Es0) as Hlt. destruct (decide (cv = next cs1)); [lia|].
    pose proof (H4 _ _ Ecv). destruct (decide (vrep = t)); [congruence|]. exact (M2 _ _ _ Es0 Ecv).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "set_eq_remove_eq_models" *)
Theorem set_eq_remove_eq_models : forall cs st t s sval,
  CPstate_inv cs /\ CPstate_models cs st /\ lookup s (locals st) = SOME sval ->
  CPstate_models (set_eq (remove_eq cs t) t s) (set_locals (insert t sval (locals st)) st).
Proof.
  intros cs st t s sval (Hi & Hm & Hs). destruct (both_alloc_vars (t, s)) eqn:Hb.
  - apply copy_prop_move_model_aux. split; [exact Hi|split; [exact Hm|split; [exact Hb|exact Hs]]].
  - unfold set_eq. cbn [both_alloc_vars] in Hb. rewrite Hb.
    apply remove_eq_model_insert; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eq_idempotent" *)
Theorem lookup_eq_idempotent : forall cs x,
  CPstate_inv cs -> lookup_eq cs (lookup_eq cs x) = lookup_eq cs x.
Proof.
  intros cs x (_ & _ & _ & H4). unfold lookup_eq at 2 3.
  destruct (lookup x (to_eq cs)) as [cx|] eqn:Ex; [|unfold lookup_eq; rewrite Ex; reflexivity].
  destruct (lookup cx (from_eq cs)) as [r|] eqn:Ec; [|unfold lookup_eq; rewrite Ex, Ec; reflexivity].
  unfold lookup_eq. rewrite (H4 _ _ Ec), Ec. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_modelsD_get_var" *)
Theorem CPstate_modelsD_get_var : forall cs st x,
  CPstate_inv cs /\ CPstate_models cs st -> get_var (lookup_eq cs x) st = get_var x st.
Proof. intros cs st x [_ Hm]. unfold get_var. apply CPstate_model, Hm. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_modelsD_get_vars" *)
Theorem CPstate_modelsD_get_vars : forall cs st xs,
  CPstate_inv cs /\ CPstate_models cs st -> get_vars (MAP (lookup_eq cs) xs) st = get_vars xs st.
Proof.
  intros cs st xs H. induction xs as [|x xs IH]; [reflexivity|]. cbn [MAP List.map get_vars].
  rewrite IH, (CPstate_modelsD_get_var cs st x H). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_modelsD_get_var_imm" *)
Theorem CPstate_modelsD_get_var_imm : forall cs st x,
  CPstate_inv cs /\ CPstate_models cs st -> get_var_imm (lookup_eq_imm cs x) st = get_var_imm x st.
Proof. intros cs st [r|w] H; cbn; [apply CPstate_modelsD_get_var, H|reflexivity]. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_modelsD_Var" *)
Theorem CPstate_modelsD_Var : forall cs st x,
  CPstate_inv cs /\ CPstate_models cs st -> word_exp st (Var (lookup_eq cs x)) = word_exp st (Var x).
Proof. intros cs st x H. cbn [word_exp]. apply CPstate_modelsD_get_var, H. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_modelsD_lookup_eq_imm" *)
Theorem CPstate_modelsD_lookup_eq_imm : forall cs st (x : reg_imm a),
  CPstate_inv cs -> CPstate_models cs st ->
  word_exp st (match lookup_eq_imm cs x with Reg r => Var r | Imm w => Const w end) =
  word_exp st (match x with Reg r => Var r | Imm w => Const w end).
Proof. intros cs st [r|w] H1 H2; cbn; [apply CPstate_modelsD_get_var; split; assumption|reflexivity]. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "MAP_get_var_eqD" *)
Theorem MAP_get_var_eqD : forall st xx yy,
  MAP (fun x => get_var x st) xx = MAP (fun x => get_var x st) yy -> get_vars xx st = get_vars yy st.
Proof.
  intros st xx; induction xx as [|x xx IH]; intros [|y yy] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. cbn [get_vars]. rewrite H1, (IH yy H2). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "copy_prop_move_eval_aux1" *)
Theorem copy_prop_move_eval_aux1 : forall cs st moves,
  CPstate_inv cs -> CPstate_models cs st ->
  forall moves' cs', copy_prop_move moves cs = (moves', cs') ->
  MAP (fun x => get_var x st) (MAP SND moves') = MAP (fun x => get_var x st) (MAP SND moves).
Proof.
  intros cs st moves Hi Hm. induction moves as [|[t s] moves IH]; intros moves' cs' H;
    cbn [copy_prop_move] in H; [injection H as <- _; reflexivity|].
  destruct (copy_prop_move moves cs) as [ms cs1] eqn:E. injection H as <- _.
  cbn [MAP List.map snd SND]. rewrite (IH ms cs1 eq_refl), (CPstate_modelsD_get_var cs st s (conj Hi Hm)).
  reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "copy_prop_move_eval_aux3" *)
Theorem copy_prop_move_eval_aux3 : forall cs moves moves' cs',
  copy_prop_move moves cs = (moves', cs') -> MAP FST moves' = MAP FST moves.
Proof.
  intros cs moves; induction moves as [|[t s] moves IH]; intros moves' cs' H;
    cbn [copy_prop_move] in H; [injection H as <- _; reflexivity|].
  destruct (copy_prop_move moves cs) as [ms cs1] eqn:E. injection H as <- _.
  cbn [MAP List.map fst FST]. rewrite (IH ms cs1 eq_refl). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "copy_prop_move_get_vars" *)
Theorem copy_prop_move_get_vars : forall cs st moves moves' cs',
  CPstate_inv cs -> CPstate_models cs st -> copy_prop_move moves cs = (moves', cs') ->
  get_vars (MAP SND moves') st = get_vars (MAP SND moves) st.
Proof. intros. apply MAP_get_var_eqD. eapply copy_prop_move_eval_aux1; eauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "copy_prop_move_eval_aux2" *)
Theorem copy_prop_move_eval_aux2 : forall (moves1 moves2 : list (N * N)) st pri,
  MAP FST moves1 = MAP FST moves2 -> get_vars (MAP SND moves1) st = get_vars (MAP SND moves2) st ->
  evaluate (@Move a pri moves1, st) = evaluate (Move pri moves2, st).
Proof. intros m1 m2 st pri E1 E2. rewrite !(evaluate_eqn (Move _ _)). cbn [evaluate_body]. rewrite E1, E2. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "copy_prop_move_eval" *)
Theorem copy_prop_move_eval : forall cs st moves moves' cs' pri err st',
  CPstate_inv cs -> CPstate_models cs st -> copy_prop_move moves cs = (moves', cs') ->
  evaluate (@Move a pri moves, st) = (err, st') -> evaluate (Move pri moves', st) = (err, st').
Proof.
  intros cs st moves moves' cs' pri err st' Hi Hm E H. rewrite <- H.
  apply copy_prop_move_eval_aux2; [eapply copy_prop_move_eval_aux3; eauto|eapply copy_prop_move_get_vars; eauto].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_alist_insert_same" *)
Theorem lookup_alist_insert_same : forall (s : N) tt (values : list (word_loc a)) locals,
  s NOTIN set tt -> lookup s (alist_insert tt values locals) = lookup s locals.
Proof.
  intros s tt; induction tt as [|t tt IH]; intros values locals H; [reflexivity|].
  destruct values as [|v values]; [reflexivity|]. cbn [alist_insert]. rewrite lookup_insert.
  rewrite IN_set in H. destruct (decide (s = t)) as [->|]; [exfalso; apply H; left; reflexivity|].
  apply IH. rewrite IN_set. intros Hi; apply H; right; exact Hi.
Qed.

End MoveModel.

Section ProgInv.
Context {a : N}.
Implicit Types cs : copy_state.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "copy_prop_move_inv" *)
Theorem copy_prop_move_inv : forall cs moves moves' cs',
  CPstate_inv cs -> copy_prop_move moves cs = (moves', cs') -> CPstate_inv cs'.
Proof.
  intros cs moves; induction moves as [|[t s] moves IH]; intros moves' cs' Hi H;
    cbn [copy_prop_move] in H; [injection H as _ <-; exact Hi|].
  destruct (copy_prop_move moves cs) as [ms cs1] eqn:E. injection H as _ <-.
  apply set_eq_inv. split; [apply remove_eq_inv, (IH ms cs1 Hi eq_refl)|apply remove_eq_to_eq_t].
Qed.

Ltac inv_close :=
  first [ assumption | apply empty_eq_inv
        | repeat apply remove_eq_inv; assumption | apply remove_eqs_inv; assumption
        | apply set_store_eq_inv; assumption
        | apply set_store_eq_inv, remove_eq_inv; assumption ].

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "copy_prop_inst_inv" *)
Theorem copy_prop_inst_inv : forall cs (ins : asm.inst a) prog' cs',
  CPstate_inv cs -> copy_prop_inst ins cs = (prog', cs') -> CPstate_inv cs'.
Proof.
  intros cs ins prog' cs' Hi H.
  unfold copy_prop_inst in H. cbn zeta in H. split_H H; cbn zeta in H; injection H as _ <-; inv_close.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "copy_prop_prog_inv" *)
Theorem copy_prop_prog_inv : forall (prog : prog a) cs prog' cs',
  CPstate_inv cs /\ copy_prop_prog prog cs = (prog', cs') -> CPstate_inv cs'.
Proof.
  intros prog.
  induction prog as [ |  | i |  |  | sn e |  | q IHq | ret dest args h IHret IHh | q1 q2 IH1 IH2 | cmp r ri q1 q2 IH1 IH2 | nm q en IHq |  |  |  |  |  |  |  |  |  |  |  |  |  | ]
    using prog_nested_ind; intros cs prog' cs' [Hi H]; cbn [copy_prop_prog] in H; cbn zeta in H.
  all: try (injection H as _ <-; inv_close).
  - (* Move *)
    destruct (EVERY _ _); [|injection H as _ <-; apply empty_eq_inv].
    destruct (copy_prop_move _ cs) as [xs' c1] eqn:E. injection H as _ <-. eapply copy_prop_move_inv; eauto.
  - eapply copy_prop_inst_inv; eauto.
  - (* Get *)
    destruct (lookup_store_eq cs _) as [vv|]; [|injection H as _ <-; inv_close].
    destruct (negb _); [|injection H as _ <-; exact Hi].
    destruct (copy_prop_move _ cs) as [xs' c1] eqn:E. injection H as _ <-. eapply copy_prop_move_inv; eauto.
  - (* Set *) destruct e; injection H as _ <-; inv_close.
  - (* MustTerminate *)
    destruct (copy_prop_prog q cs) as [p1 c1] eqn:E. injection H as _ <-. exact (IHq cs p1 c1 (conj Hi E)).
  - (* Seq *)
    destruct (copy_prop_prog q1 cs) as [p1 c1] eqn:E1. destruct (copy_prop_prog q2 c1) as [p2 c2] eqn:E2.
    injection H as _ <-. exact (IH2 c1 p2 c2 (conj (IH1 cs p1 c1 (conj Hi E1)) E2)).
  - (* If *)
    destruct (copy_prop_prog q1 cs) as [p1 c1] eqn:E1. destruct (copy_prop_prog q2 cs) as [p2 c2] eqn:E2.
    injection H as _ <-. apply merge_eqs_inv. split; [exact (IH1 cs p1 c1 (conj Hi E1))|exact (IH2 cs p2 c2 (conj Hi E2))].
  - (* Loop *)
    destruct (copy_prop_prog _ empty_eq) as [p1 c1]. injection H as _ <-. apply empty_eq_inv.
Qed.

End ProgInv.

Lemma IN_INTER' {A} (x : A) s t : x IN (s INTER t) <-> x IN s /\ x IN t.
Proof. reflexivity. Qed.

Section MoveCorrect.
Context {a : N} {c ffi_t : Type}.
Implicit Types cs : copy_state.
Implicit Types st : state a c ffi_t.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "empty_eq_model" *)
Theorem empty_eq_model : forall st, CPstate_models empty_eq st.
Proof. intros; apply empty_models. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "copy_prop_move_model" *)
Theorem copy_prop_move_model : forall cs st moves moves' cs' values,
  CPstate_inv cs -> CPstate_models cs st ->
  set (MAP FST moves) INTER set (MAP SND moves) = {} ->
  copy_prop_move moves cs = (moves', cs') ->
  get_vars (MAP SND moves) st = SOME values ->
  CPstate_models cs' (set_vars (MAP FST moves) values st).
Proof.
  intros cs st moves. induction moves as [|[t s] moves IH]; intros moves' cs' values Hi Hm Hd H Hg.
  - cbn [copy_prop_move] in H. injection H as _ <-. cbn in Hg. injection Hg as <-.
    unfold set_vars; cbn [alist_insert MAP List.map]. destruct st; exact Hm.
  - cbn [copy_prop_move] in H. destruct (copy_prop_move moves cs) as [ms cs1] eqn:E.
    injection H as _ <-.
    cbn [MAP List.map fst snd FST SND get_vars] in Hg, Hd |- *.
    destruct (get_var s st) as [val|] eqn:Es; [|discriminate].
    destruct (get_vars (MAP SND moves) st) as [vs|] eqn:Ev; [|discriminate]. injection Hg as <-.
    assert (Hdisj : forall x, x IN set (MAP FST moves) -> x IN set (MAP SND moves) -> False).
    { intros x Hx Hy. assert (Hxx : x IN (set (t :: MAP FST moves) INTER set (s :: MAP SND moves))).
      { apply IN_INTER'. rewrite !IN_set in *. split; right; assumption. }
      rewrite Hd in Hxx. exact Hxx. }
    assert (Hd' : set (MAP FST moves) INTER set (MAP SND moves) = {}).
    { apply functional_extensionality; intros x; apply propositional_extensionality.
      split; [intros Hxy; apply IN_INTER' in Hxy as [Hx Hy]; exact (Hdisj x Hx Hy)|intros []]. }
    pose proof (IH ms cs1 vs Hi Hm Hd' eq_refl eq_refl) as Hm1.
    assert (Hs : s NOTIN set (MAP FST moves)).
    { intros Hx. assert (Hxx : s IN (set (t :: MAP FST moves) INTER set (s :: MAP SND moves))).
      { apply IN_INTER'. rewrite !IN_set in *. split; [right; exact Hx|left; reflexivity]. }
      rewrite Hd in Hxx. exact Hxx. }
    unfold set_vars. cbn [alist_insert].
    apply (set_eq_remove_eq_models cs1 (set_vars (MAP FST moves) vs st) t s val).
    split; [exact (copy_prop_move_inv cs moves ms cs1 Hi E)|split; [exact Hm1|]].
    unfold set_vars; cbn [locals set_locals]. rewrite lookup_alist_insert_same by exact Hs. exact Es.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "EVERY_NOT_MEM_D" *)
Theorem EVERY_NOT_MEM_D : forall (tt ss : list N),
  EVERY (fun t => negb (MEM t ss)) tt -> set tt INTER set ss = {}.
Proof.
  intros tt ss H. apply functional_extensionality; intros x; apply propositional_extensionality.
  split; [|intros []]. intros Hxy. apply IN_INTER' in Hxy as [Hx Hy]. apply IN_set in Hx. apply IN_set in Hy.
  unfold is_true in H. rewrite EVERY_Forall, Forall_forall in H. specialize (H x Hx).
  apply Bool.negb_true_iff in H. apply (MEM_In x ss) in Hy. congruence.
Qed.

Lemma evaluate_Move_eq pri (moves : list (N * N)) st :
  evaluate (Move pri moves, st) =
  if ALL_DISTINCT (MAP FST moves) then
    match get_vars (MAP SND moves) st with
    | NONE => (SOME Error, st)
    | SOME vs => (NONE, set_vars (MAP FST moves) vs st)
    end
  else (SOME Error, st).
Proof. rewrite (evaluate_eqn (Move pri moves) st); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "copy_prop_move_correct" *)
Theorem copy_prop_move_correct : forall cs st pri moves prog' cs' err st',
  CPstate_inv cs /\ CPstate_models cs st /\
  copy_prop_prog (Move pri moves) cs = (prog', cs') /\ evaluate (Move pri moves, st) = (err, st') ->
  evaluate (prog', st) = (err, st') /\ (err = NONE -> CPstate_models cs' st').
Proof.
  intros cs st pri moves prog' cs' err st' (Hi & Hm & H & Hev). cbn [copy_prop_prog] in H. cbn zeta in H.
  destruct (EVERY _ _) eqn:Ee.
  - destruct (copy_prop_move moves cs) as [ms c1] eqn:E. injection H as <- <-.
    split; [exact (copy_prop_move_eval cs st moves ms c1 pri err st' Hi Hm E Hev)|].
    intros ->. rewrite evaluate_Move_eq in Hev.
    destruct (ALL_DISTINCT _); [|discriminate].
    destruct (get_vars _ st) as [vs|] eqn:Eg; [|discriminate]. injection Hev as <-.
    exact (copy_prop_move_model cs st moves ms c1 vs Hi Hm (EVERY_NOT_MEM_D _ _ Ee) E Eg).
  - injection H as <- <-. split; [exact Hev|intros _; apply empty_eq_model].
Qed.

End MoveCorrect.

(** ** Expressions and instructions *)

Ltac split_inner H :=
  repeat match type of H with
         | context [match ?x with _ => _ end] =>
             lazymatch x with
             | context [match _ with _ => _ end] => fail
             | _ => let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H
             end
         end.

Section InstCorrect.
Context {a : N} {c ffi_t : Type}.
Implicit Types cs : copy_state.
Implicit Types st : state a c ffi_t.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "word_exp_cong_Var" *)
Theorem word_exp_cong_Var : forall st (x' x : N),
  get_var x' st = get_var x st -> word_exp st (@Var a x') = word_exp st (Var x).
Proof. intros st x' x H. exact H. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "word_exp_cong_Load" *)
Theorem word_exp_cong_Load : forall st (addr' addr : exp a),
  word_exp st addr' = word_exp st addr -> word_exp st (Load addr') = word_exp st (Load addr).
Proof. intros st addr' addr H. cbn [word_exp]. rewrite H. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "word_exp_cong_Op" *)
Theorem word_exp_cong_Op : forall st op (aa' aa : list (exp a)),
  MAP (word_exp st) aa' = MAP (word_exp st) aa -> word_exp st (Op op aa') = word_exp st (Op op aa).
Proof. intros st op aa' aa H. cbn [word_exp]. rewrite H. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "word_exp_cong_Shift" *)
Theorem word_exp_cong_Shift : forall st sh (e' e e2' e2 : exp a),
  word_exp st e' = word_exp st e -> word_exp st e2' = word_exp st e2 ->
  word_exp st (Shift sh e' e2') = word_exp st (Shift sh e e2).
Proof. intros st sh e' e e2' e2 H1 H2. cbn [word_exp]. rewrite H1, H2. reflexivity. Qed.

(** HOL's [∀ins cs st prog' cs'] with [ins] an [asm$inst]. *)
(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "copy_prop_inst_eval" *)
Theorem copy_prop_inst_eval : forall (ins : asm.inst a) cs st prog' cs',
  CPstate_inv cs -> CPstate_models cs st ->
  (prog', cs') = copy_prop_inst ins cs ->
  evaluate (prog', st) = evaluate (Inst ins, st).
Proof.
  intros ins cs st prog' cs' Hi Hm H.
  assert (GV : forall x, get_var (lookup_eq cs x) st = get_var x st)
    by (intros; apply CPstate_modelsD_get_var; split; assumption).
  unfold copy_prop_inst, lookup_eq_imm in H. cbn zeta in H. split_inner H; injection H as -> _;
    rewrite !(evaluate_eqn (Inst _)); cbn [evaluate_body inst]; unfold assign;
    cbn [word_exp get_vars MAP List.map]; rewrite ?GV; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "remove_eq_comm" *)
Theorem remove_eq_comm : forall cs x y, remove_eq (remove_eq cs x) y = remove_eq (remove_eq cs y) x.
Proof.
  intros cs x y. unfold remove_eq at 2 4.
  destruct (lookup x (to_eq cs)) eqn:Ex, (lookup y (to_eq cs)) eqn:Ey; unfold remove_eq;
    cbn [empty_eq to_eq]; rewrite ?Ex, ?Ey; reflexivity.
Qed.

Ltac mclose Hi Hm :=
  repeat first
    [ exact Hm
    | apply remove_eq_model_set_var; split; [repeat apply remove_eq_inv; exact Hi|]
    | apply remove_eq_model ].

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "copy_prop_inst_correct" *)
Theorem copy_prop_inst_correct : forall cs st (ins : asm.inst a) prog' cs' err st',
  CPstate_inv cs /\ CPstate_models cs st /\ copy_prop_inst ins cs = (prog', cs') /\
  evaluate (Inst ins, st) = (err, st') ->
  evaluate (prog', st) = (err, st') /\ (err = NONE -> CPstate_models cs' st').
Proof.
  intros cs st ins prog' cs' err st' (Hi & Hm & H & Hev). split.
  { rewrite (copy_prop_inst_eval ins cs st prog' cs' Hi Hm (eq_sym H)). exact Hev. }
  intros ->. rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  destruct (inst ins st) as [st1|] eqn:Ei; [injection Hev as <-|discriminate].
  unfold copy_prop_inst, lookup_eq_imm in H. cbn zeta in H. split_inner H; injection H as _ <-;
    cbn [inst] in Ei; unfold assign, mem_store in Ei; split_inner Ei; try discriminate Ei; try (injection Ei as <-);
    mclose Hi Hm.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "remove_eq_model_unset_var" *)
Theorem remove_eq_model_unset_var : forall cs st t,
  CPstate_inv cs -> CPstate_models cs st -> CPstate_models (remove_eq cs t) (unset_var t st).
Proof.
  intros cs st t (_ & _ & _ & H4) [M1 M2]. unfold remove_eq.
  destruct (lookup t (to_eq cs)) eqn:Et; [apply empty_models|].
  unfold unset_var. split; cbn [locals store set_locals].
  - intros v cv vrep Ev Ecv. rewrite !lookup_delete. pose proof (H4 _ _ Ecv).
    destruct (decide (v = t)); [congruence|]. destruct (decide (vrep = t)); [congruence|]. eauto.
  - intros s0 cv vrep Es Ecv. rewrite lookup_delete. pose proof (H4 _ _ Ecv).
    destruct (decide (vrep = t)); [congruence|]. eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_modelsD_copy_prop_share" *)
Theorem CPstate_modelsD_copy_prop_share : forall cs st (e : exp a),
  CPstate_inv cs -> CPstate_models cs st -> word_exp st (copy_prop_share e cs) = word_exp st e.
Proof.
  intros cs st e Hi Hm.
  assert (GV : forall x, get_var (lookup_eq cs x) st = get_var x st)
    by (intros; apply CPstate_modelsD_get_var; split; assumption).
  unfold copy_prop_share. repeat match goal with |- context [match ?x with _ => _ end] => destruct x end;
    cbn [word_exp MAP List.map]; rewrite ?GV; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_store_eq_SOME" *)
Theorem lookup_store_eq_SOME : forall cs st s v,
  CPstate_models cs st /\ lookup_store_eq cs s = SOME v -> FLOOKUP (store st) s = lookup v (locals st).
Proof.
  intros cs st s v [[_ M2] H]. unfold lookup_store_eq in H.
  destruct (ALOOKUP (store_to_eq cs) s) as [cc|] eqn:Es; [|discriminate].
  destruct (lookup cc (from_eq cs)) as [r|] eqn:Ec; [|discriminate]. injection H as <-. eauto.
Qed.

End InstCorrect.

Section SetStore.
Context {a : N} {c ffi_t : Type}.
Implicit Types cs : copy_state.
Implicit Types st : state a c ffi_t.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_remove_eq" *)
Theorem lookup_remove_eq : forall n cs, lookup n (to_eq (remove_eq cs n)) = NONE.
Proof. intros; apply remove_eq_to_eq_t. Qed.

Lemma set_store_eq_cases cs s x :
  reg_alloc.is_alloc_var x ->
  (exists cc r, lookup x (to_eq cs) = SOME cc /\ lookup cc (from_eq cs) = SOME r /\
     set_store_eq cs s x = {| to_eq := to_eq cs; from_eq := from_eq cs;
                              store_to_eq := (s, cc) :: store_to_eq cs; next := next cs |}) \/
  ((forall cc, lookup x (to_eq cs) = SOME cc -> lookup cc (from_eq cs) = NONE) /\
     set_store_eq cs s x = {| to_eq := insert x (next cs) (to_eq cs);
                              from_eq := insert (next cs) x (from_eq cs);
                              store_to_eq := (s, next cs) :: store_to_eq cs; next := next cs + 1 |}).
Proof.
  intros H. unfold set_store_eq. unfold is_true in H. rewrite H.
  destruct (lookup x (to_eq cs)) as [cc|] eqn:Es; [destruct (lookup cc (from_eq cs)) as [r|] eqn:Ec|].
  - left. eauto.
  - right. split; [intros c' E; injection E as <-; exact Ec|reflexivity].
  - right. split; [discriminate|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eq_set_store_eq" *)
Theorem lookup_eq_set_store_eq : forall cs s x y,
  CPstate_inv cs /\ reg_alloc.is_alloc_var x -> lookup_eq (set_store_eq cs s x) y = lookup_eq cs y.
Proof.
  intros cs s x y [(H1 & H2 & H3 & H4) Hx].
  destruct (set_store_eq_cases cs s x Hx) as [(cc & r & Ex & Ec & ->)|(Hn & ->)]; [reflexivity|].
  unfold lookup_eq; cbn [to_eq from_eq]. rewrite lookup_insert.
  destruct (decide (y = x)) as [->|Hne].
  - rewrite lookup_insert. destruct (decide _); [|congruence].
    destruct (lookup x (to_eq cs)) as [cx|] eqn:Ex; [rewrite (Hn _ eq_refl)|]; reflexivity.
  - destruct (lookup y (to_eq cs)) as [cy|] eqn:Ey; [|reflexivity].
    rewrite lookup_insert. destruct (decide (cy = next cs)); [specialize (H1 _ _ Ey); lia|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_store_eq_set_store_eq_1" *)
Theorem lookup_store_eq_set_store_eq_1 : forall cs s x y,
  CPstate_inv cs /\ reg_alloc.is_alloc_var x /\ lookup_store_eq (set_store_eq cs s x) s = SOME y ->
  lookup_eq cs x = lookup_eq cs y.
Proof.
  intros cs s x y [Hi [Hx H]]. pose proof Hi as (H1 & H2 & H3 & H4).
  destruct (set_store_eq_cases cs s x Hx) as [(cc & r & Ex & Ec & Eq)|(Hn & Eq)]; rewrite Eq in H;
    unfold lookup_store_eq in H; cbn [to_eq from_eq store_to_eq next ALOOKUP] in H;
    (destruct (decide (s = s)); [|congruence]).
  - rewrite Ec in H. injection H as <-. unfold lookup_eq. rewrite Ex, Ec, (H4 _ _ Ec), Ec. reflexivity.
  - rewrite lookup_insert in H. destruct (decide _); [|congruence]. injection H as <-. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_store_eq_set_store_eq_2" *)
Theorem lookup_store_eq_set_store_eq_2 : forall cs s t x y,
  CPstate_inv cs /\ reg_alloc.is_alloc_var x /\ s <> t /\
  lookup_store_eq (set_store_eq cs s x) t = SOME y ->
  lookup_store_eq cs t = SOME y.
Proof.
  intros cs s t x y [Hi [Hx [Hst H]]]. pose proof Hi as (H1 & H2 & H3 & H4).
  destruct (set_store_eq_cases cs s x Hx) as [(cc & r & Ex & Ec & Eq)|(Hn & Eq)]; rewrite Eq in H;
    unfold lookup_store_eq in H |- *; cbn [to_eq from_eq store_to_eq next ALOOKUP] in H;
    (destruct (decide (s = t)); [congruence|]); [exact H|].
  destruct (ALOOKUP (store_to_eq cs) t) as [ct|] eqn:Et; [|exact H].
  rewrite lookup_insert in H. destruct (decide (ct = next cs)); [specialize (H3 _ _ Et); lia|exact H].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "set_store_eq_model_set_store" *)
Theorem set_store_eq_model_set_store : forall cs st n w s,
  CPstate_inv cs /\ CPstate_models cs st /\ get_var n st = SOME w ->
  CPstate_models (set_store_eq cs s n) (set_store s w st).
Proof.
  intros cs st n w s (Hi & [M1 M2] & Hn). pose proof Hi as (H1 & H2 & H3 & H4).
  destruct (reg_alloc.is_alloc_var n) eqn:Ha.
  2:{ unfold set_store_eq. rewrite Ha. apply empty_models. }
  unfold get_var in Hn.
  destruct (set_store_eq_cases cs s n Ha) as [(cc & r & Ex & Ec & ->)|(Hnn & ->)];
    split; cbn [to_eq from_eq store_to_eq next ALOOKUP locals store set_store set_store_field];
    rewrite ?FLOOKUP_UPDATE.
  - exact M1.
  - intros s0 cv vrep Es0 Ecv. rewrite FLOOKUP_UPDATE. destruct (decide (s = s0)) as [->|].
    + injection Es0 as <-. rewrite Ec in Ecv. injection Ecv as <-. rewrite <- (M1 _ _ _ Ex Ec). congruence.
    + eauto.
  - intros v cv vrep Ev Ecv. rewrite lookup_insert in Ev, Ecv. destruct (decide (v = n)) as [->|].
    + injection Ev as <-. dd. injection Ecv as <-. dd. reflexivity.
    + specialize (H1 _ _ Ev) as Hlt. destruct (decide (cv = next cs)); [lia|]. eauto.
  - intros s0 cv vrep Es0 Ecv. rewrite FLOOKUP_UPDATE, lookup_insert in *. destruct (decide (s = s0)) as [->|].
    + injection Es0 as <-. dd. injection Ecv as <-. dd. congruence.
    + specialize (H3 _ _ Es0) as Hlt. destruct (decide (cv = next cs)); [lia|]. eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eq_remove_t_same" *)
Theorem lookup_eq_remove_t_same : forall cs t, lookup_eq (remove_eq cs t) t = t.
Proof. intros. unfold lookup_eq. rewrite remove_eq_to_eq_t. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_store_eq_set_store_eq_same" *)
Theorem lookup_store_eq_set_store_eq_same : forall cs s x,
  lookup x (to_eq cs) = NONE /\ reg_alloc.is_alloc_var x ->
  lookup_store_eq (set_store_eq cs s x) s = SOME x.
Proof.
  intros cs s x [Hx Ha]. unfold set_store_eq. unfold is_true in Ha. rewrite Ha, Hx.
  unfold lookup_store_eq; cbn. destruct (decide (s = s)); [|congruence].
  rewrite lookup_insert. destruct (decide _); [reflexivity|congruence].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "set_store_eq_model_set_var" *)
Theorem set_store_eq_model_set_var : forall cs st s w n,
  CPstate_inv cs /\ CPstate_models cs st /\ lookup_store_eq cs s = NONE /\ get_store s st = SOME w ->
  CPstate_models (set_store_eq (remove_eq cs n) s n) (set_var n w st).
Proof.
  intros cs st s w n (Hi & Hm & _ & Hs).
  pose proof (remove_eq_inv cs n Hi) as (H1 & H2 & H3 & H4).
  pose proof (remove_eq_model cs st n Hm) as [M1 M2]. pose proof (remove_eq_to_eq_t cs n) as Hn.
  set (cs1 := remove_eq cs n) in *.
  destruct (reg_alloc.is_alloc_var n) eqn:Ha.
  2:{ unfold set_store_eq. rewrite Ha. apply empty_models. }
  unfold set_store_eq. rewrite Ha, Hn.
  unfold get_store in Hs.
  split; cbn [to_eq from_eq store_to_eq next ALOOKUP locals store set_var set_locals].
  - intros v cv vrep Ev Ecv. rewrite !lookup_insert in *. destruct (decide (v = n)) as [->|].
    + injection Ev as <-. dd. injection Ecv as <-. dd. reflexivity.
    + specialize (H1 _ _ Ev) as Hlt. destruct (decide (cv = next cs1)); [lia|].
      pose proof (H4 _ _ Ecv). destruct (decide (vrep = n)); [congruence|]. eauto.
  - intros s0 cv vrep Es0 Ecv. rewrite !lookup_insert in *. destruct (decide (s = s0)) as [->|].
    + injection Es0 as <-. dd. injection Ecv as <-. dd. exact Hs.
    + specialize (H3 _ _ Es0) as Hlt. destruct (decide (cv = next cs1)); [lia|].
      pose proof (H4 _ _ Ecv). destruct (decide (vrep = n)); [congruence|]. eauto.
Qed.

End SetStore.

(** ** Correctness *)

Section Correct.
Context {a : N} {c ffi_t : Type}.
Implicit Types cs : copy_state.
Implicit Types st : state a c ffi_t.

(** HOL's bound variables [c], [c'] (programs) are [p], [p']. *)
(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "evaluate_Loop_body_cong_err" *)
Theorem evaluate_Loop_body_cong_err : forall st names (p p' : prog a) exit_names res s',
  (forall (v : state a c ffi_t) res s', evaluate (p, v) = (res, s') /\ res <> SOME Error -> evaluate (p', v) = (res, s')) /\
  evaluate (Loop names p exit_names, st) = (res, s') /\ res <> SOME Error ->
  evaluate (Loop names p' exit_names, st) = (res, s').
Proof.
  intros st names p p' exit_names res s' (Hs & H & Hr).
  revert res s' H Hr.
  remember (N.to_nat (clock st)) as n eqn:Hn. revert st Hn.
  induction n as [n IH] using (well_founded_induction lt_wf).
  intros st Hn res s' H Hr.
  rewrite evaluate_eqn in H |- *; cbn [evaluate_body] in H |- *.
  destruct (cut_state (names, LN) st) as [s0|] eqn:Ec; [|exact H].
  rewrite fix_clock_evaluate in H |- *.
  destruct (evaluate (p, s0)) as [r t] eqn:E1.
  assert (Hr1 : r <> SOME Error).
  { intros ->. cbn [cont_loop] in H. rewrite bd_false in H by discriminate.
    injection H as <- _. apply Hr; reflexivity. }
  rewrite (Hs _ _ _ (conj E1 Hr1)).
  destruct (cont_loop r); [|exact H].
  destruct (clock t =? 0) eqn:Ez; [exact H|].
  apply N.eqb_neq in Ez. unfold STOP in *.
  pose proof (evaluate_clock _ _ _ _ E1) as [Hc _].
  pose proof (cut_state_clock _ _ _ Ec) as [Hc' _].
  exact (IH (N.to_nat (clock (dec_clock t))) ltac:(unfold dec_clock; cbn [clock set_clock]; lia)
           (dec_clock t) eq_refl res s' H Hr).
Qed.

Lemma evaluate_Seq_eq (p1 p2 : prog a) st :
  evaluate (Seq p1 p2, st) =
  let '(res, s1) := evaluate (p1, st) in
  if bool_decide (res = NONE) then evaluate (p2, s1) else (res, s1).
Proof. rewrite (evaluate_eqn (Seq p1 p2) st); cbn [evaluate_body]. rewrite fix_clock_evaluate. reflexivity. Qed.

Ltac ev_tgt := rewrite evaluate_eqn; cbn [evaluate_body].

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "copy_prop_correct" *)
Theorem copy_prop_correct : forall (prog : prog a) cs st prog' cs' err st',
  CPstate_inv cs /\ CPstate_models cs st /\ copy_prop_prog prog cs = (prog', cs') /\
  err <> SOME Error /\ evaluate (prog, st) = (err, st') ->
  evaluate (prog', st) = (err, st') /\ (err = NONE -> CPstate_models cs' st').
Proof.
  intros prog.
  induction prog as [ |pri moves|i|v ex|gv gn|sn sexp|ex var|q IHq|ret dest args h IHret IHh
                     |q1 q2 IH1 IH2|cmp r ri q1 q2 IH1 IH2|names q exit_names IHq|an anames
                     |t1 t2 ad off ws|rv|rv rvs|k|k| |b dst src|lr ll|r1 r2 r3 r4 inames
                     |r1 r2|r1 r2|fi r1 r2 r3 r4 fnames|op v ex]
    using prog_nested_ind;
    intros cs st prog' cs' err st' (Hi & Hm & H & Herr & Hev);
    cbn [copy_prop_prog] in H; cbn zeta in H;
    assert (GV : forall x, get_var (lookup_eq cs x) st = get_var x st)
      by (intros; apply CPstate_modelsD_get_var; split; assumption);
    try (injection H as <- <-; split; [exact Hev|intros _; apply empty_eq_model]).
  - (* Skip *)
    injection H as <- <-. split; [exact Hev|]. intros ->. rewrite evaluate_eqn in Hev.
    injection Hev as <-. exact Hm.
  - (* Move *) exact (copy_prop_move_correct cs st pri moves prog' cs' err st' (conj Hi (conj Hm (conj H Hev)))).
  - (* Inst *) exact (copy_prop_inst_correct cs st i prog' cs' err st' (conj Hi (conj Hm (conj H Hev)))).
  - (* Get *)
    rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
    destruct (get_store gn st) as [x|] eqn:Eg; [|injection Hev as <- _; congruence].
    injection Hev as <- <-.
    destruct (lookup_store_eq cs gn) as [vv|] eqn:El.
    + assert (Hx : lookup vv (locals st) = SOME x)
        by (rewrite <- (lookup_store_eq_SOME cs st gn vv (conj Hm El)); exact Eg).
      destruct (negb (bool_decide (vv = gv))) eqn:Ne.
      * cbn [copy_prop_move] in H. cbn zeta in H. injection H as <- <-.
        split.
        -- rewrite evaluate_Move_eq. cbn [MAP List.map fst snd ALL_DISTINCT MEM negb andb get_vars].
           rewrite GV. unfold get_var. rewrite Hx. reflexivity.
        -- intros _. apply (set_eq_remove_eq_models cs st gv vv x). split; [exact Hi|split; [exact Hm|exact Hx]].
      * apply Bool.negb_false_iff, bool_decide_spec in Ne. subst vv.
        injection H as <- <-.
        assert (Est : set_var gv x st = st)
          by (unfold set_var; rewrite (insert_unchanged _ _ _ Hx); destruct st; reflexivity).
        rewrite Est. split; [|intros _; exact Hm]. rewrite evaluate_eqn. reflexivity.
    + injection H as <- <-. split.
      * rewrite evaluate_eqn; cbn [evaluate_body]. rewrite Eg. reflexivity.
      * intros _. apply set_store_eq_model_set_var. split; [exact Hi|split; [exact Hm|split; [exact El|exact Eg]]].
  - (* Set *)
    destruct sexp; try (injection H as <- <-; split; [exact Hev|intros _; apply empty_eq_model]).
    injection H as <- <-.
    rewrite evaluate_eqn in Hev; cbn [evaluate_body word_exp] in Hev.
    split.
    + rewrite evaluate_eqn; cbn [evaluate_body word_exp]. rewrite GV. exact Hev.
    + intros ->. destruct (_ || _); [discriminate|].
      destruct (get_var n st) as [w|] eqn:Eg; [|discriminate]. injection Hev as <-.
      apply set_store_eq_model_set_store. split; [exact Hi|split; [exact Hm|exact Eg]].
  - (* MustTerminate *)
    destruct (copy_prop_prog q cs) as [q' c1] eqn:Eq. injection H as <- <-.
    rewrite evaluate_eqn in Hev |- *; cbn [evaluate_body] in Hev |- *.
    destruct (termdep st =? 0); [split; [exact Hev|intros ->; discriminate]|].
    destruct (evaluate (q, set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) st)))
      as [r1 t1] eqn:E1.
    destruct (bool_decide (r1 = SOME TimeOut)) eqn:Et; [injection Hev as <- _; congruence|].
    injection Hev as <- <-.
      destruct (IHq cs (set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) st)) q' c1 r1 t1 (conj Hi (conj Hm (conj Eq (conj Herr E1))))) as [Ev Hn].
      rewrite Ev, Et. split; [reflexivity|]. intros ->. exact (Hn eq_refl).
  - (* Seq *)
    destruct (copy_prop_prog q1 cs) as [p1 c1] eqn:E1c. destruct (copy_prop_prog q2 c1) as [p2 c2] eqn:E2c.
    injection H as <- <-.
    rewrite evaluate_Seq_eq in Hev |- *. destruct (evaluate (q1, st)) as [r1 s1] eqn:E1.
    assert (Hr1 : r1 <> SOME Error).
    { intros ->. rewrite bd_false in Hev by discriminate. injection Hev as <- _. congruence. }
    destruct (IH1 cs st p1 c1 r1 s1 (conj Hi (conj Hm (conj E1c (conj Hr1 E1))))) as [Ev1 Hn1].
    rewrite Ev1. destruct (bool_decide (r1 = NONE)) eqn:En.
    + apply bool_decide_spec in En; subst r1.
      exact (IH2 c1 s1 p2 c2 err st' (conj (copy_prop_prog_inv q1 cs p1 c1 (conj Hi E1c))
               (conj (Hn1 eq_refl) (conj E2c (conj Herr Hev))))).
    + injection Hev as <- <-. split; [reflexivity|]. intros ->. rewrite bd_true in En by reflexivity. discriminate.
  - (* If *)
    destruct (copy_prop_prog q1 cs) as [p1 c1] eqn:E1c. destruct (copy_prop_prog q2 cs) as [p2 c2] eqn:E2c.
    injection H as <- <-.
    rewrite evaluate_eqn in Hev |- *; cbn [evaluate_body] in Hev |- *.
    rewrite GV, (CPstate_modelsD_get_var_imm cs st ri (conj Hi Hm)).
    split_H Hev; try (split; [exact Hev|intros ->; injection Hev as Hev; discriminate Hev]).
    + destruct (IH1 cs st p1 c1 err st' (conj Hi (conj Hm (conj E1c (conj Herr Hev))))) as [Ev Hn].
      split; [exact Ev|]. intros ->. apply merge_eqs_model1, Hn, eq_refl.
    + destruct (IH2 cs st p2 c2 err st' (conj Hi (conj Hm (conj E2c (conj Herr Hev))))) as [Ev Hn].
      split; [exact Ev|]. intros ->. apply merge_eqs_model2, Hn, eq_refl.
  - (* Loop *)
    destruct (copy_prop_prog q empty_eq) as [q' c1] eqn:Eq. injection H as <- <-.
    split; [|intros _; apply empty_eq_model].
    apply (evaluate_Loop_body_cong_err st names q q' exit_names err st'). split; [|split; assumption].
    intros v res s' [Hv Hr].
    exact (proj1 (IHq empty_eq v q' c1 res s' (conj empty_eq_inv (conj (empty_eq_model v) (conj Eq (conj Hr Hv)))))).
  - (* StoreConsts *)
    injection H as <- <-. split; [exact Hev|]. intros ->.
    rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev. split_H Hev; try discriminate Hev.
    injection Hev as <-. cbn zeta. cbn [remove_eqs].
    rewrite (remove_eq_comm _ ad off).
    apply remove_eq_model_set_var. split; [repeat apply remove_eq_inv; exact Hi|].
    apply remove_eq_model_set_var. split; [repeat apply remove_eq_inv; exact Hi|].
    rewrite (remove_eq_comm _ t1 t2).
    apply remove_eq_model_unset_var; [repeat apply remove_eq_inv; exact Hi|].
    apply remove_eq_model_unset_var; [exact Hi|exact Hm].
  - (* Raise *)
    injection H as <- <-. rewrite evaluate_eqn in Hev |- *; cbn [evaluate_body] in Hev |- *.
    rewrite GV. split; [exact Hev|]. intros ->. split_H Hev; discriminate.
  - (* Return *)
    injection H as <- <-. rewrite evaluate_eqn in Hev |- *; cbn [evaluate_body] in Hev |- *.
    rewrite GV, (CPstate_modelsD_get_vars cs st rvs (conj Hi Hm)). split; [exact Hev|].
    intros ->. split_H Hev; discriminate.
  - injection H as <- <-. split; [exact Hev|]. intros ->. rewrite evaluate_eqn in Hev. discriminate.
  - injection H as <- <-. split; [exact Hev|]. intros ->. rewrite evaluate_eqn in Hev. discriminate.
  - (* Tick *)
    injection H as <- <-. split; [exact Hev|]. intros ->.
    rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev. split_H Hev; try discriminate Hev; injection Hev as <-; exact Hm.
  - (* OpCurrHeap *)
    injection H as <- <-. rewrite evaluate_eqn in Hev |- *; cbn [evaluate_body word_exp MAP List.map] in Hev |- *.
    assert (Gs : get_var (if decide (lookup_eq cs src = dst) then src else lookup_eq cs src) st = get_var src st)
      by (destruct (decide _); [reflexivity|apply GV]).
    rewrite Gs. split; [exact Hev|]. intros ->. split_H Hev; try discriminate.
    injection Hev as <-. apply remove_eq_model_set_var. split; assumption.
  - (* LocValue *)
    injection H as <- <-. split; [exact Hev|]. intros ->.
    rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev. split_H Hev; try discriminate.
    injection Hev as <-. apply remove_eq_model_set_var. split; assumption.
  - (* CodeBufferWrite *)
    injection H as <- <-. rewrite evaluate_eqn in Hev |- *; cbn [evaluate_body] in Hev |- *.
    rewrite !GV. split; [exact Hev|]. intros ->. split_H Hev; try discriminate. injection Hev as <-. exact Hm.
  - (* DataBufferWrite *)
    injection H as <- <-. rewrite evaluate_eqn in Hev |- *; cbn [evaluate_body] in Hev |- *.
    rewrite !GV. split; [exact Hev|]. intros ->. split_H Hev; try discriminate. injection Hev as <-. exact Hm.
  - (* ShareInst *)
    injection H as <- <-. rewrite evaluate_eqn in Hev |- *; cbn [evaluate_body] in Hev |- *.
    rewrite (CPstate_modelsD_copy_prop_share cs st ex Hi Hm). split; [exact Hev|]. intros ->.
    destruct (word_exp st ex) as [[ad|]|]; try discriminate.
    destruct op; cbn [share_inst] in Hev;
      unfold sh_mem_set_var, sh_mem_load, sh_mem_load_byte, sh_mem_load16, sh_mem_load32,
        sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32 in Hev;
      split_H Hev; try discriminate Hev;
      repeat match goal with
             | E : context [match ?x with _ => _ end] |- _ =>
                 destruct x; cbn beta iota in E; try discriminate E
             end;
      inversion Hev; subst;
      first [ apply remove_eq_model_set_var; split; assumption
            | apply remove_eq_model; assumption
            | apply remove_eq_model; match goal with E : mem_store _ _ _ = SOME _ |- _ =>
                unfold mem_store in E; destruct (classical_dec _) in E; [injection E as <-; assumption|discriminate] end ].
Qed.

End Correct.

(*! HOL "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "evaluate_copy_prop" *)
Theorem evaluate_copy_prop : forall {a c ffi_t} (e : prog a) (s : state a c ffi_t),
  FST (evaluate (e, s)) <> SOME Error -> evaluate (copy_prop e, s) = evaluate (e, s).
Proof.
  intros a c ffi_t e s H. unfold copy_prop.
  destruct (evaluate (e, s)) as [r t] eqn:E. destruct (copy_prop_prog e empty_eq) as [e' cs'] eqn:Ec.
  cbn [FST fst] in *.
  exact (proj1 (copy_prop_correct e empty_eq s e' cs' r t
                  (conj empty_eq_inv (conj (empty_eq_model s) (conj Ec (conj H E)))))).
Qed.
