(** * HOL4 [lprefix_lub]: least upper bounds of chains of lazy lists

    Used by CakeML's observational semantics: a diverging program's I/O
    trace is the least upper bound of the traces of its clocked runs.
    Only the definitions used by the semantics are ported so far. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.coalgebras Require Import llist.
Open Scope N_scope.

Section Defs.
Context {A : Type} `{EqDecision A} `{Inhabited A}.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_chain_def" *)
Definition lprefix_chain (ls : llist A -> Prop) : Prop :=
  forall ll1 ll2, ll1 IN ls /\ ll2 IN ls -> LPREFIX ll1 ll2 \/ LPREFIX ll2 ll1.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_chain_nth_def" *)
Definition lprefix_chain_nth (n : N) (ls : llist A -> Prop) : option A :=
  some (fun x => exists l, l IN ls /\ LNTH n l = SOME x).

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_lub_def" *)
Definition lprefix_lub (ls : llist A -> Prop) (lub : llist A) : Prop :=
  (forall ll, ll IN ls -> LPREFIX ll lub) /\
  (forall ub, (forall ll, ll IN ls -> LPREFIX ll ub) -> LPREFIX lub ub).

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "build_lprefix_lub_f_def" *)
Definition build_lprefix_lub_f (ls : llist A -> Prop) (n : N) : option (N * A) :=
  OPTION_MAP (fun x => (n + 1, x)) (lprefix_chain_nth n ls).

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "build_lprefix_lub_def" *)
Definition build_lprefix_lub (ls : llist A -> Prop) : llist A :=
  LUNFOLD (build_lprefix_lub_f ls) 0.

End Defs.

(** ** Theorems *)

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "less_opt_def" *)
Definition less_opt (n : N) (m : option N) : bool :=
  match m with NONE => true | SOME m => n <? m end.

Section Thms.
Context {A : Type} `{EqDecision A} `{Inhabited A}.

Lemma LNTH_none_mono (l : llist A) n m : LNTH n l = NONE -> n <= m -> LNTH m l = NONE.
Proof.
  rewrite !LNTH_rep; intros Hn Hle; exact (lrep_ok_none _ (llist_rep_ok l) n m Hn Hle).
Qed.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lnth_some_length" *)
Theorem lnth_some_length : forall (ll : llist A) n x, LNTH n ll = SOME x -> less_opt n (LLENGTH ll).
Proof.
  intros ll n x Hx; unfold less_opt.
  destruct (LLENGTH ll) as [m|] eqn:E; [|reflexivity].
  apply LLENGTH_fin_len in E as [E _]. apply N.ltb_lt.
  destruct (N.lt_ge_cases n m); [assumption|].
  rewrite (LNTH_none_mono ll m n) in Hx; [discriminate| |assumption]. rewrite LNTH_rep; exact E.
Qed.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "less_opt_LLENGTH_LNTH_SOME" *)
Theorem less_opt_LLENGTH_LNTH_SOME : forall n (l : llist A),
  less_opt n (LLENGTH l) <-> IS_SOME (LNTH n l).
Proof.
  intros n l; split.
  - unfold less_opt; destruct (LLENGTH l) as [m|] eqn:E; rewrite LNTH_rep.
    + intros Hlt%N.ltb_lt. apply LLENGTH_fin_len in E as [_ F].
      destruct (llist_rep l n) eqn:En; [reflexivity|exfalso; exact (F n Hlt En)].
    + intros _. destruct (llist_rep l n) eqn:En; [reflexivity|].
      exfalso; exact (proj1 (LLENGTH_NONE l) E n En).
  - destruct (LNTH n l) eqn:E; [|discriminate]. intros _; eapply lnth_some_length; eauto.
Qed.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "LPREFIX_NTH" *)
Theorem LPREFIX_NTH : forall (ll1 ll2 : llist A),
  LPREFIX ll1 ll2 <-> forall n, less_opt n (LLENGTH ll1) -> LNTH n ll1 = LNTH n ll2.
Proof.
  intros ll1 ll2; rewrite LPREFIX_pfx; split.
  - intros P n Hn. apply less_opt_LLENGTH_LNTH_SOME in Hn.
    destruct (LNTH n ll1) eqn:E; [|discriminate]. symmetry; exact (P n a E).
  - intros Q i x Hx. rewrite <- Hx; symmetry; apply Q. eapply lnth_some_length; eauto.
Qed.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_chain_subset" *)
Theorem lprefix_chain_subset : forall (ls y : llist A -> Prop),
  lprefix_chain ls /\ y SUBSET ls -> lprefix_chain y.
Proof. intros ls y [C S] l1 l2 [H1 H2]; apply C; split; apply S; assumption. Qed.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_chain_LNTHs_agree" *)
Theorem lprefix_chain_LNTHs_agree : forall (ls : llist A -> Prop) l1 l2 n x1 x2,
  lprefix_chain ls /\ l1 IN ls /\ l2 IN ls /\ LNTH n l1 = SOME x1 /\ LNTH n l2 = SOME x2 ->
  x1 = x2.
Proof.
  intros ls l1 l2 n x1 x2 [C [H1 [H2 [E1 E2]]]].
  destruct (C l1 l2 (conj H1 H2)) as [P|P]; apply LPREFIX_pfx in P.
  - rewrite (P n x1 E1) in E2; inversion E2; reflexivity.
  - rewrite (P n x2 E2) in E1; inversion E1; reflexivity.
Qed.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "exists_lprefix_chain_nth" *)
Theorem exists_lprefix_chain_nth : forall (ls : llist A -> Prop) n x,
  lprefix_chain ls /\ (exists l, l IN ls /\ LNTH n l = SOME x) ->
  lprefix_chain_nth n ls = SOME x.
Proof.
  intros ls n x [C [l [Hl Hx]]]; unfold lprefix_chain_nth, some.
  destruct (classical_dec _) as [Hex|Hno]; [|exfalso; apply Hno; eauto].
  f_equal. pose proof (select_spec _ Hex) as [l' [Hl' Hx']].
  eapply lprefix_chain_LNTHs_agree; eauto 7.
Qed.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "not_exists_lprefix_chain_nth" *)
Theorem not_exists_lprefix_chain_nth : forall (ls : llist A -> Prop) n,
  lprefix_chain ls /\ (forall l, l IN ls -> LNTH n l = NONE) ->
  lprefix_chain_nth n ls = NONE.
Proof.
  intros ls n [C N0]; unfold lprefix_chain_nth, some.
  destruct (classical_dec _) as [[x [l [Hl Hx]]]|_]; [|reflexivity].
  rewrite (N0 l Hl) in Hx; discriminate.
Qed.

Lemma lprefix_chain_nth_cases (ls : llist A -> Prop) n :
  lprefix_chain ls ->
  (exists l x, l IN ls /\ LNTH n l = SOME x /\ lprefix_chain_nth n ls = SOME x) \/
  ((forall l, l IN ls -> LNTH n l = NONE) /\ lprefix_chain_nth n ls = NONE).
Proof.
  intros C. destruct (classic (exists l x, l IN ls /\ LNTH n l = SOME x)) as [[l [x [Hl Hx]]]|Hno].
  - left; exists l, x; split; [|split]; auto. apply exists_lprefix_chain_nth; eauto.
  - right. assert (N0 : forall l, l IN ls -> LNTH n l = NONE).
    { intros l Hl; destruct (LNTH n l) eqn:E; [exfalso; apply Hno; eauto|reflexivity]. }
    split; [exact N0|apply not_exists_lprefix_chain_nth; auto].
Qed.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_chain_nth_none_mono" *)
Theorem lprefix_chain_nth_none_mono : forall m n (ls : llist A -> Prop),
  lprefix_chain ls /\ m <= n /\ lprefix_chain_nth m ls = NONE ->
  lprefix_chain_nth n ls = NONE.
Proof.
  intros m n ls [C [Hle Hm]].
  destruct (lprefix_chain_nth_cases ls m C) as [[l [x [_ [_ E]]]]|[Nm _]]; [congruence|].
  apply not_exists_lprefix_chain_nth; split; [exact C|].
  intros l Hl; apply (LNTH_none_mono l m n); auto.
Qed.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "equiv_lprefix_chain_def" *)
Definition equiv_lprefix_chain (ls1 ls2 : llist A -> Prop) : Prop :=
  forall n, lprefix_chain_nth n ls1 = lprefix_chain_nth n ls2.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_rel_def" *)
Definition lprefix_rel (s1 s2 : llist A -> Prop) : Prop :=
  forall l1, l1 IN s1 -> exists l2, l2 IN s2 /\ LPREFIX l1 l2.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_lub_is_chain" *)
Theorem lprefix_lub_is_chain : forall (ls : llist A -> Prop) ll, lprefix_lub ls ll -> lprefix_chain ls.
Proof.
  intros ls ll [U _] l1 l2 [H1 H2].
  pose proof (proj1 (LPREFIX_pfx _ _) (U l1 H1)) as P1.
  pose proof (proj1 (LPREFIX_pfx _ _) (U l2 H2)) as P2.
  rewrite !LPREFIX_pfx.
  destruct (classic (pfx l1 l2)) as [Y|Hn]; [left; exact Y|right].
  unfold pfx in Hn. apply not_all_ex_not in Hn as [i Hn].
  apply not_all_ex_not in Hn as [x Hn]. apply imply_to_and in Hn as [Hx Hnx].
  assert (E2 : LNTH i l2 = NONE).
  { destruct (LNTH i l2) as [y|] eqn:E; [|reflexivity]. exfalso; apply Hnx.
    pose proof (P2 i y E) as A1; pose proof (P1 i x Hx) as A2; congruence. }
  intros j y Hy.
  assert (j < i).
  { destruct (N.lt_ge_cases j i); [assumption|]. rewrite (LNTH_none_mono l2 i j E2) in Hy; [discriminate|assumption]. }
  destruct (LNTH j l1) as [z|] eqn:Ez.
  - pose proof (P1 j z Ez) as A1; pose proof (P2 j y Hy) as A2. congruence.
  - rewrite (LNTH_none_mono l1 j i Ez) in Hx by lia; discriminate.
Qed.

(** The first [n] elements of [l] (Galette helper). *)
Lemma lrep_ok_trunc (n : N) (l : llist A) :
  lrep_ok (fun k => if k <? n then llist_rep l k else NONE).
Proof.
  intros k; cbv beta.
  destruct (N.ltb_spec (SUC k) n), (N.ltb_spec k n); try lia; try discriminate.
  apply (llist_rep_ok l).
Qed.

Definition ltrunc (n : N) (l : llist A) : llist A :=
  llist_abs_ok (fun k => if k <? n then llist_rep l k else NONE) (lrep_ok_trunc n l).

Lemma LNTH_ltrunc n l k : LNTH k (ltrunc n l) = if k <? n then LNTH k l else NONE.
Proof. rewrite !LNTH_rep; reflexivity. Qed.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_lub_nth" *)
Theorem lprefix_lub_nth : forall (ls : llist A -> Prop) lub,
  lprefix_chain ls -> (lprefix_lub ls lub <-> forall n, LNTH n lub = lprefix_chain_nth n ls).
Proof.
  intros ls lub C; split.
  - intros [U L] n.
    destruct (lprefix_chain_nth_cases ls n C) as [[l [x [Hl [Hx E]]]]|[N0 E]].
    + rewrite E. exact (proj1 (LPREFIX_pfx _ _) (U l Hl) n x Hx).
    + rewrite E. destruct (LNTH n lub) as [y|] eqn:Ey; [exfalso|reflexivity].
      assert (Hub : LPREFIX lub (ltrunc n lub)).
      { apply L. intros l Hl. apply LPREFIX_pfx. intros i z Hz.
        rewrite LNTH_ltrunc. destruct (N.ltb_spec i n).
        - exact (proj1 (LPREFIX_pfx _ _) (U l Hl) i z Hz).
        - rewrite (LNTH_none_mono l n i (N0 l Hl)) in Hz by lia; discriminate. }
      apply LPREFIX_pfx in Hub. specialize (Hub n y Ey).
      rewrite LNTH_ltrunc in Hub. destruct (N.ltb_spec n n); [lia|discriminate].
  - intros Hn. split.
    + intros l Hl; apply LPREFIX_pfx; intros i x Hx.
      rewrite Hn; apply exists_lprefix_chain_nth; eauto.
    + intros ub U. apply LPREFIX_pfx; intros i x Hx. rewrite Hn in Hx.
      destruct (lprefix_chain_nth_cases ls i C) as [[l [y [Hl [Hy E]]]]|[_ E]]; [|congruence].
      rewrite E in Hx; inversion Hx; subst.
      exact (proj1 (LPREFIX_pfx _ _) (U l Hl) i x Hy).
Qed.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "unique_lprefix_lub" *)
Theorem unique_lprefix_lub : forall (f : llist A -> Prop) ll1 ll2,
  lprefix_lub f ll1 /\ lprefix_lub f ll2 -> ll1 = ll2.
Proof.
  intros f ll1 ll2 [H1 H2]. pose proof (lprefix_lub_is_chain _ _ H1) as C.
  apply llist_ext_LNTH; intros n.
  rewrite (proj1 (lprefix_lub_nth f ll1 C) H1 n), (proj1 (lprefix_lub_nth f ll2 C) H2 n).
  reflexivity.
Qed.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "build_lprefix_lub_lem" *)
Theorem build_lprefix_lub_lem : forall (ls : llist A -> Prop), lprefix_chain ls ->
  forall m n, LNTH n (LUNFOLD (build_lprefix_lub_f ls) m) = lprefix_chain_nth (m + n) ls.
Proof.
  intros ls C m n. rewrite LNTH_rep; cbn [LUNFOLD llist_rep]; unfold lunfold_rep.
  assert (G : forall k, num_rec (build_lprefix_lub_f ls m)
                          (fun _ mo => OPTION_BIND mo (fun p => build_lprefix_lub_f ls (fst p))) k =
                        OPTION_MAP (fun x => (m + k + 1, x)) (lprefix_chain_nth (m + k) ls)).
  { induction k as [|k IH] using N.peano_ind.
    - rewrite N.add_0_r; reflexivity.
    - rewrite num_rec_SUC, IH. unfold build_lprefix_lub_f.
      destruct (lprefix_chain_nth (m + k) ls) eqn:E; cbn.
      + replace (m + k + 1) with (m + SUC k) by lia; reflexivity.
      + rewrite (lprefix_chain_nth_none_mono (m + k) (m + SUC k) ls); [reflexivity|].
        repeat split; [exact C|lia|exact E]. }
  rewrite G. destruct (lprefix_chain_nth (m + n) ls); reflexivity.
Qed.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "build_lprefix_lub_thm" *)
Theorem build_lprefix_lub_thm : forall (ls : llist A -> Prop),
  lprefix_chain ls -> lprefix_lub ls (build_lprefix_lub ls).
Proof.
  intros ls C; apply lprefix_lub_nth; [exact C|]. intros n.
  unfold build_lprefix_lub; rewrite build_lprefix_lub_lem by exact C. reflexivity.
Qed.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "build_prefix_lub_intro" *)
Theorem build_prefix_lub_intro : forall (ls : llist A -> Prop) lub,
  lprefix_chain ls -> (lprefix_lub ls lub <-> lub = build_lprefix_lub ls).
Proof.
  intros ls lub C; split.
  - intros Hl; apply (unique_lprefix_lub ls); split; [exact Hl|apply build_lprefix_lub_thm, C].
  - intros ->; apply build_lprefix_lub_thm, C.
Qed.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_lub_equiv_chain" *)
Theorem lprefix_lub_equiv_chain : forall (ls1 ls2 : llist A -> Prop) ll,
  lprefix_chain ls1 /\ lprefix_chain ls2 /\ equiv_lprefix_chain ls1 ls2 ->
  (lprefix_lub ls1 ll <-> lprefix_lub ls2 ll).
Proof.
  intros ls1 ls2 ll [C1 [C2 E]].
  rewrite (lprefix_lub_nth ls1 ll C1), (lprefix_lub_nth ls2 ll C2).
  split; intros Hh n; rewrite Hh; [|symmetry]; apply E.
Qed.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_lub_equiv_chain2" *)
Theorem lprefix_lub_equiv_chain2 : forall (ls1 ls2 : llist A -> Prop) ll1 ll2,
  lprefix_lub ls1 ll1 /\ lprefix_lub ls2 ll2 -> (ll1 = ll2 <-> equiv_lprefix_chain ls1 ls2).
Proof.
  intros ls1 ls2 ll1 ll2 [H1 H2].
  pose proof (lprefix_lub_is_chain _ _ H1) as C1; pose proof (lprefix_lub_is_chain _ _ H2) as C2.
  pose proof (proj1 (lprefix_lub_nth _ _ C1) H1) as N1.
  pose proof (proj1 (lprefix_lub_nth _ _ C2) H2) as N2.
  split.
  - intros -> n. rewrite <- N1, <- N2; reflexivity.
  - intros E; apply llist_ext_LNTH; intros n. rewrite N1, N2; apply E.
Qed.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_lub_new_chain" *)
Theorem lprefix_lub_new_chain : forall (ls1 ls2 : llist A -> Prop) ll,
  lprefix_chain ls2 /\ equiv_lprefix_chain ls1 ls2 /\ lprefix_lub ls1 ll -> lprefix_lub ls2 ll.
Proof.
  intros ls1 ls2 ll [C2 [E H1]]. pose proof (lprefix_lub_is_chain _ _ H1) as C1.
  apply (lprefix_lub_equiv_chain ls1 ls2 ll); auto.
Qed.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "equiv_lprefix_chain_thm" *)
Theorem equiv_lprefix_chain_thm : forall (ls1 ls2 : llist A -> Prop),
  lprefix_chain ls1 /\ lprefix_chain ls2 ->
  (equiv_lprefix_chain ls1 ls2 <->
   (forall ll1 n x, ll1 IN ls1 /\ LNTH n ll1 = SOME x -> exists ll2, ll2 IN ls2 /\ LNTH n ll2 = SOME x) /\
   (forall ll2 n x, ll2 IN ls2 /\ LNTH n ll2 = SOME x -> exists ll1, ll1 IN ls1 /\ LNTH n ll1 = SOME x)).
Proof.
  intros ls1 ls2 [C1 C2]; split.
  - intros E; split.
    + intros ll1 n x [Hl Hx]. assert (Hn := E n).
      rewrite (exists_lprefix_chain_nth ls1 n x) in Hn by eauto.
      destruct (lprefix_chain_nth_cases ls2 n C2) as [[l [y [Hl2 [Hy E2]]]]|[_ E2]]; congruence || eauto.
      rewrite E2 in Hn; inversion Hn; subst; eauto.
    + intros ll2 n x [Hl Hx]. assert (Hn := E n).
      rewrite (exists_lprefix_chain_nth ls2 n x) in Hn by eauto.
      destruct (lprefix_chain_nth_cases ls1 n C1) as [[l [y [Hl1 [Hy E1]]]]|[_ E1]]; congruence || eauto.
      rewrite E1 in Hn; inversion Hn; subst; eauto.
  - intros [F G] n.
    destruct (lprefix_chain_nth_cases ls1 n C1) as [[l [x [Hl [Hx E1]]]]|[N1 E1]].
    + rewrite E1; symmetry. apply exists_lprefix_chain_nth; split; [exact C2|]. apply (F l n x); auto.
    + rewrite E1; symmetry. apply not_exists_lprefix_chain_nth; split; [exact C2|].
      intros l Hl; destruct (LNTH n l) as [y|] eqn:Ey; [|reflexivity].
      destruct (G l n y (conj Hl Ey)) as [l1 [Hl1 Hy1]]. rewrite (N1 l1 Hl1) in Hy1; discriminate.
Qed.

End Thms.

Section PrefixChain.
Context {A : Type} `{EqDecision A} `{Inhabited A}.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "prefix_chain_def" *)
Definition prefix_chain (ls : list A -> Prop) : Prop :=
  forall l1 l2, l1 IN ls /\ l2 IN ls -> isPREFIX l1 l2 \/ isPREFIX l2 l1.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "prefix_chain_lprefix_chain" *)
Theorem prefix_chain_lprefix_chain : forall ls, prefix_chain ls -> lprefix_chain (IMAGE fromList ls).
Proof.
  intros ls Hc ll1 ll2 [[l1 [-> H1]] [l2 [-> H2]]].
  rewrite !LPREFIX_fromList, !toList_fromList. apply Hc; split; assumption.
Qed.

End PrefixChain.
