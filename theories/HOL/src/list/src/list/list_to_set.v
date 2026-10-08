(** * HOL4 [list]: [LIST_TO_SET] ([set])

    Part of the [listScript] counterpart, split off so that [list.v] does not
    depend on [pred_set].  HOL's [MEM x l] abbreviates [x IN set l]; Galette's
    [MEM] is boolean ([list.v]), related to [set] by [MEM_set]. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.pred_set.src Require Import pred_set.
Open Scope N_scope.

(*! HOL "HOL/src/list/src/listScript.sml" "LIST_TO_SET_DEF" *)
Fixpoint LIST_TO_SET {A} (l : list A) : A -> Prop :=
  match l with
  | [] => fun x => False
  | h :: t => fun x => (x = h) \/ LIST_TO_SET t x
  end.

(** HOL [set] (an overload of [LIST_TO_SET]). *)
Abbreviation set := LIST_TO_SET.

Lemma IN_set {A} (x : A) l : x IN set l <-> In x l.
Proof. induction l as [|h t IH]; cbn; [tauto|]; unfold pred_set.IN in *; rewrite IH; intuition congruence. Qed.

Lemma MEM_set {A} `{EqDecision A} (x : A) l : is_true (MEM x l) <-> x IN set l.
Proof. rewrite IN_set; apply MEM_In. Qed.

Section ListToSet.
Context {A : Type}.

(*! HOL "HOL/src/list/src/listScript.sml" "LIST_TO_SET" *)
Theorem LIST_TO_SET_thm : forall (h : A) t,
  LIST_TO_SET (@nil A) = {} /\ LIST_TO_SET (h :: t) = h INSERT LIST_TO_SET t.
Proof. split; reflexivity. Qed.

(*! HOL "HOL/src/list/src/listScript.sml" "LIST_TO_SET_THM" *)
Theorem LIST_TO_SET_THM : forall (h : A) t,
  LIST_TO_SET (@nil A) = {} /\ LIST_TO_SET (h :: t) = h INSERT LIST_TO_SET t.
Proof. exact LIST_TO_SET_thm. Qed.

(*! HOL "HOL/src/list/src/listScript.sml" "LIST_TO_SET_APPEND" *)
Theorem LIST_TO_SET_APPEND : forall l1 l2 : list A, set (l1 ++ l2) = set l1 UNION set l2.
Proof.
  intros; apply EXTENSION; intros x; rewrite IN_UNION, !IN_set, in_app_iff; reflexivity.
Qed.

(*! HOL "HOL/src/list/src/listScript.sml" "LIST_TO_SET_EQ_EMPTY" *)
Theorem LIST_TO_SET_EQ_EMPTY : forall l : list A,
  ((set l = {}) <-> (l = [])) /\ (({} = set l) <-> (l = [])).
Proof.
  intros [|h t]; [split; split; reflexivity|].
  split; split; intros E; try discriminate; exfalso;
    [apply (NOT_INSERT_EMPTY h (set t))|apply (NOT_EMPTY_INSERT h (set t))]; exact E.
Qed.

(*! HOL "HOL/src/list/src/listScript.sml" "FINITE_LIST_TO_SET" *)
Theorem FINITE_LIST_TO_SET : forall l : list A, FINITE (set l).
Proof. intros l; apply FINITE_list; exists l; intros x; apply IN_set. Qed.

(*! HOL "HOL/src/list/src/listScript.sml" "LIST_TO_SET_REVERSE" *)
Theorem LIST_TO_SET_REVERSE : forall ls : list A, set (REVERSE ls) = set ls.
Proof. intros; apply EXTENSION; intros x; rewrite !IN_set, <- in_rev; reflexivity. Qed.

(*! HOL "HOL/src/list/src/listScript.sml" "LIST_TO_SET_MAP" *)
Theorem LIST_TO_SET_MAP : forall {B} (f : A -> B) l, LIST_TO_SET (MAP f l) = IMAGE f (LIST_TO_SET l).
Proof.
  intros B f l; apply EXTENSION; intros y; rewrite IN_IMAGE, IN_set, in_map_iff.
  split; intros [x [h1 h2]]; exists x; rewrite ?IN_set in *; auto.
Qed.

(*! HOL "HOL/src/list/src/listScript.sml" "LIST_TO_SET_FILTER" *)
Theorem LIST_TO_SET_FILTER : forall (P : A -> bool) l,
  LIST_TO_SET (FILTER P l) = (fun x => is_true (P x)) INTER LIST_TO_SET l.
Proof.
  intros P l; apply EXTENSION; intros x; rewrite IN_INTER, !IN_set, filter_In; unfold pred_set.IN, is_true; tauto.
Qed.

(*! HOL "HOL/src/list/src/listScript.sml" "CARD_LIST_TO_SET" *)
Theorem CARD_LIST_TO_SET : forall ls : list A, CARD (set ls) <= LENGTH ls.
Proof.
  intros ls; rewrite (CARD_enum (set ls) (nodup cdec ls)), LENGTH_length.
  - pose proof (NoDup_incl_length (NoDup_nodup cdec ls) (fun x => proj1 (nodup_In cdec ls x))); lia.
  - apply NoDup_nodup.
  - intros x; rewrite IN_set, nodup_In; reflexivity.
Qed.

(*! HOL "HOL/src/list/src/listScript.sml" "ALL_DISTINCT_CARD_LIST_TO_SET" *)
Theorem ALL_DISTINCT_CARD_LIST_TO_SET `{EqDecision A} : forall ls : list A,
  ALL_DISTINCT ls -> (CARD (set ls) = LENGTH ls).
Proof.
  intros ls h; rewrite (CARD_enum (set ls) ls), LENGTH_length; [reflexivity| |intros; apply IN_set].
  clear -h; induction ls as [|a t IH]; cbn in h; [constructor|].
  apply andb_prop in h as [h1 h2]; constructor; [|apply IH, h2].
  rewrite <- MEM_In; rewrite negb_true_iff in h1; rewrite h1; discriminate.
Qed.

End ListToSet.
