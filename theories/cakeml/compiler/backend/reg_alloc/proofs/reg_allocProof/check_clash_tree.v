(** * CakeML [reg_allocProof]: clash trees and the colouring checker

    Part of the [reg_allocProofScript] counterpart: the definitions and
    lemmas about [check_partial_col] / clash trees that
    [linear_scanProofScript] also uses ([in_clash_tree], [sp_inverts],
    [hide], [check_partial_col_success], [check_partial_col_domain]).  They
    are kept apart so that [linear_scanProof.v] does not depend on the
    whole graph-colouring proof. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.coretypes Require Import pair.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "in_clash_tree_def" *)
Fixpoint in_clash_tree (ct : clash_tree) (x : N) : Prop :=
  match ct with
  | Delta w r => MEM x w \/ MEM x r
  | Set_ names => x IN domain names
  | Branch name_opt t1 t2 =>
      in_clash_tree t1 x \/ in_clash_tree t2 x \/
      match name_opt with Some names => x IN domain names | None => False end
  | Seq t t' => in_clash_tree t x \/ in_clash_tree t' x
  end.

(** [g] inverts [f] as an sptree. *)
(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "sp_inverts_def" *)
Definition sp_inverts (f g : num_map N) : Prop :=
  forall m fm, lookup m f = Some fm -> lookup fm g = Some m.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "sp_inverts_insert" *)
Theorem sp_inverts_insert : forall f g x y,
  sp_inverts f g /\ x NOTIN domain f /\ y NOTIN domain g ->
  sp_inverts (insert x y f) (insert y x g).
Proof.
  unfold sp_inverts, pred_set.IN; intros f g x y (Hi & Hx & Hy) m fm.
  rewrite !lookup_insert. destruct (decide (m = x)) as [->|Hm].
  - intros [= <-]; destruct (decide (y = y)); congruence.
  - intros Hl. pose proof (Hi _ _ Hl) as Hg.
    destruct (decide (fm = y)) as [->|]; [|exact Hg].
    exfalso; apply Hy, domain_lookup; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "hide_def" *)
Definition hide {A} (x : A) : A := x.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "INJ_less" *)
Theorem INJ_less : forall {A B} (f : A -> B) s' t s,
  INJ f s' t /\ s SUBSET s' -> INJ f s t.
Proof. unfold INJ, pred_set.SUBSET; intros A B f s' t s ((H1 & H2) & H3); split; [eauto|intros x y [Hx Hy]; apply H2; split; auto]. Qed.

Lemma lookup_unit_cases (x : N) (t : num_set) :
  lookup x t = None \/ lookup x t = Some tt.
Proof. destruct (lookup x t) as [[]|]; auto. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "check_partial_col_success" *)
Theorem check_partial_col_success : forall ls live flive col,
  domain flive = IMAGE col (domain live) /\
  INJ col (set ls UNION domain live) UNIV ->
  exists livein flivein,
    check_partial_col col ls live flive = Some (livein, flivein) /\
    domain flivein = IMAGE col (domain livein).
Proof.
  induction ls as [|h ls IH]; intros live flive col (Hd & Hinj); cbn [check_partial_col].
  - eauto.
  - assert (Hinj' : INJ col (set ls UNION domain live) UNIV).
    { apply (INJ_less col (set (h :: ls) UNION domain live)); split; [exact Hinj|].
      intros z; unfold_sets; cbn [LIST_TO_SET]; tauto. }
    destruct (lookup_unit_cases h live) as [Eh|Eh]; rewrite Eh.
    + assert (Hf : lookup (col h) flive = None).
      { destruct (lookup (col h) flive) as [u|] eqn:E; [|reflexivity]. exfalso.
        assert (Hin : col h IN domain flive) by (apply domain_lookup; eauto).
        rewrite Hd in Hin; destruct Hin as (z & Hz & Hzl).
        destruct Hinj as [_ Hinj].
        assert (h = z).
        { apply Hinj; [|exact Hz]. unfold_sets; cbn [LIST_TO_SET]; split; [left; left; reflexivity|right; exact Hzl]. }
        subst z. unfold pred_set.IN in Hzl; apply domain_lookup in Hzl as [v Hv]; congruence. }
      rewrite Hf. apply IH. split.
      * rewrite !domain_insert, Hd. apply set_ext; intros z; unfold_sets.
        split; [intros [->|(w & -> & Hw)]; eauto|].
        intros (w & -> & [->|Hw]); eauto.
      * apply (INJ_less col (set (h :: ls) UNION domain live)); split; [exact Hinj|].
        intros z; rewrite domain_insert; unfold_sets; cbn [LIST_TO_SET]; tauto.
    + apply IH; auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "check_partial_col_domain" *)
Theorem check_partial_col_domain : forall ls f live flive v,
  check_partial_col f ls live flive = Some v ->
  domain (FST v) = set ls UNION domain live.
Proof.
  induction ls as [|h ls IH]; intros f live flive v; cbn [check_partial_col].
  - intros [= <-]; apply set_ext; intros z; unfold_sets; cbn [LIST_TO_SET FST]; tauto.
  - destruct (lookup_unit_cases h live) as [Eh|Eh]; rewrite Eh.
    + destruct (lookup (f h) flive) as [[]|]; [discriminate|].
      intros H; rewrite (IH _ _ _ _ H), domain_insert.
      apply set_ext; intros z; unfold_sets; cbn [LIST_TO_SET]; tauto.
    + intros H; rewrite (IH _ _ _ _ H).
      assert (domain live h) by (apply domain_lookup; eauto).
      apply set_ext; intros z; unfold_sets; cbn [LIST_TO_SET]; intuition (subst; auto).
Qed.
