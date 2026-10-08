(** * HOL4 [pred_set]: sets as predicates

    HOL ['a set] is ['a -> bool]; Galette's is [A -> Prop].  None of this is
    executable.  The operations keep HOL's names and infix syntax:
    [x IN s], [x NOTIN s], [s SUBSET t], [s PSUBSET t], [x INSERT s],
    [s DELETE x], [s UNION t], [s INTER t], [s DIFF t], [{}] ([EMPTY]); HOL's
    singleton [{x}] is written [(x INSERT {})] (Rocq reserves braces around
    an operand of an infix notation).  These words are keywords once this module is
    imported, so the constants themselves are written qualified
    ([pred_set.UNION]) where a proof must name them.

    HOL's set-builder [{x | P x}] (constant [GSPEC]) is written as the
    predicate [fun x => P x]; HOL's [GSPEC_ETA] makes them equal.

    HOL's [IN] is declared in [boolScript] ([IN_DEF]: [IN = \x f. f x]); it is
    defined here without a tag.

    [FINITE] is HOL's impredicative definition; [CARD] is chosen by Hilbert
    choice (HOL specifies it by [CARD_DEF]). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.combin Require Import combin.
Open Scope N_scope.

(** ** Definitions *)

(** HOL [IN] ([boolScript] [IN_DEF]). *)
Definition IN {A} (x : A) (s : A -> Prop) : Prop := s x.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "EMPTY_DEF" *)
Definition EMPTY {A} : A -> Prop := fun x => False.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "UNIV_DEF" *)
Definition UNIV {A} : A -> Prop := fun x => True.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_DEF" *)
Definition SUBSET {A} (s t : A -> Prop) : Prop := forall x, IN x s -> IN x t.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "PSUBSET_DEF" *)
Definition PSUBSET {A} (s t : A -> Prop) : Prop := SUBSET s t /\ ~ (s = t).

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "UNION_DEF" *)
Definition UNION {A} (s t : A -> Prop) : A -> Prop := fun x => IN x s \/ IN x t.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INTER_DEF" *)
Definition INTER {A} (s t : A -> Prop) : A -> Prop := fun x => IN x s /\ IN x t.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DISJOINT_DEF" *)
Definition DISJOINT {A} (s t : A -> Prop) : Prop := INTER s t = EMPTY.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DIFF_DEF" *)
Definition DIFF {A} (s t : A -> Prop) : A -> Prop := fun x => IN x s /\ ~ IN x t.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INSERT_DEF" *)
Definition INSERT {A} (x : A) (s : A -> Prop) : A -> Prop := fun y => y = x \/ IN y s.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DELETE_DEF" *)
Definition DELETE {A} (s : A -> Prop) (x : A) : A -> Prop := DIFF s (INSERT x EMPTY).

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IMAGE_DEF" *)
Definition IMAGE {A B} (f : A -> B) (s : A -> Prop) : B -> Prop :=
  fun y => exists x, y = f x /\ IN x s.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "BIGUNION" *)
Definition BIGUNION {A} (P : (A -> Prop) -> Prop) : A -> Prop :=
  fun x => exists s, IN s P /\ IN x s.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "COMPL_DEF" *)
Definition COMPL {A} (P : A -> Prop) : A -> Prop := DIFF UNIV P.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "count_def" *)
Definition count (n : num) : num -> Prop := fun m => m < n.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "PREIMAGE_def" *)
Definition PREIMAGE {A B} (f : A -> B) (s : B -> Prop) : A -> Prop := fun x => IN (f x) s.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SING_DEF" *)
Definition SING {A} (s : A -> Prop) : Prop := exists x, s = INSERT x EMPTY.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INJ_DEF" *)
Definition INJ {A B} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : Prop :=
  (forall x, IN x s -> IN (f x) t) /\
  (forall x y, (IN x s /\ IN y s) -> (f x = f y) -> (x = y)).

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SURJ_DEF" *)
Definition SURJ {A B} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : Prop :=
  (forall x, IN x s -> IN (f x) t) /\
  (forall x, IN x t -> exists y, IN y s /\ (f y = x)).

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "BIJ_DEF" *)
Definition BIJ {A B} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : Prop :=
  INJ f s t /\ SURJ f s t.

(** HOL [LINV] (via [LINV_OPT]); specified by [LINV_DEF] below. *)
Definition LINV {A B} `{Inhabited A} (f : A -> B) (s : A -> Prop) (y : B) : A :=
  select (fun x => IN x s /\ f x = y).

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "FINITE_DEF" *)
Definition FINITE {A} (s : A -> Prop) : Prop :=
  forall P : (A -> Prop) -> Prop,
    P EMPTY /\ (forall s, P s -> forall e, P (INSERT e s)) -> P s.

(** HOL [CARD] (specified by [CARD_DEF] below): the length of a
    duplicate-free list enumerating the set; unspecified for infinite sets. *)
Definition CARD {A} (s : A -> Prop) : num :=
  select (fun n => exists l, NoDup l /\ (forall x, IN x s <-> In x l) /\ n = N.of_nat (length l)).

Ltac unfold_sets :=
  unfold PSUBSET, SUBSET, DELETE, COMPL, UNION, INTER, DIFF, INSERT, IMAGE,
    BIGUNION, count, PREIMAGE, EMPTY, UNIV, IN in *; cbv beta in *.

(** ** Notations *)

Notation "x 'IN' s" := (IN x s) (at level 70, no associativity).
Notation "x 'NOTIN' s" := (~ (x IN s)) (at level 70, no associativity).
Notation "s 'SUBSET' t" := (SUBSET s t) (at level 70, no associativity).
Notation "s 'PSUBSET' t" := (PSUBSET s t) (at level 70, no associativity).
Notation "x 'INSERT' s" := (INSERT x s) (at level 60, right associativity).
Notation "s 'DELETE' x" := (DELETE s x) (at level 50, left associativity).
Notation "s 'UNION' t" := (UNION s t) (at level 50, left associativity).
Notation "s 'DIFF' t" := (DIFF s t) (at level 50, left associativity).
Notation "s 'INTER' t" := (INTER s t) (at level 40, left associativity).
Notation "{}" := EMPTY.

(** HOL [INFINITE s] abbreviates [~FINITE s]. *)
Abbreviation INFINITE s := (~ FINITE s).

(** ** Tactics (Galette infrastructure) *)

Lemma set_ext {A} (s t : A -> Prop) : (forall x, s x <-> t x) -> s = t.
Proof. intros h; apply functional_extensionality; intros x; apply propositional_extensionality, h. Qed.

Lemma DISJOINT_iff {A} (s t : A -> Prop) : DISJOINT s t <-> forall x, ~ (s x /\ t x).
Proof.
  unfold DISJOINT; split.
  - intros E x hx; assert (h := f_equal (fun u => u x) E); cbn in h; unfold_sets.
    rewrite <- h; exact hx.
  - intros h; apply set_ext; intros x; unfold_sets; specialize (h x); tauto.
Qed.

Ltac sets :=
  intros; repeat rewrite DISJOINT_iff in *; unfold_sets; intros;
  repeat (match goal with
          | |- _ /\ _ => split
          | |- forall _, _ => intro
          | |- @eq (_ -> Prop) _ _ => apply set_ext; intro
          end; unfold_sets);
  try solve [firstorder (subst; first [tauto | eauto])].

Ltac sets_cl :=
  sets; try solve [match goal with |- context [?s ?x] => destruct (classic (s x)); tauto end].

(** ** Membership and extensionality *)

Section Basic.
Context {A : Type}.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SPECIFICATION" *)
Theorem SPECIFICATION : forall (P : A -> Prop) x, x IN P <-> P x.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IN_APP" *)
Theorem IN_APP : forall x (P : A -> Prop), (x IN P) <-> P x.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "EXTENSION" *)
Theorem EXTENSION : forall s t : A -> Prop, (s = t) <-> (forall x, x IN s <-> x IN t).
Proof. intros s t; split; [intros ->; reflexivity|apply set_ext]. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "NOT_IN_EMPTY" *)
Theorem NOT_IN_EMPTY : forall x : A, ~ (x IN EMPTY).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "MEMBER_NOT_EMPTY" *)
Theorem MEMBER_NOT_EMPTY : forall s : A -> Prop, (exists x, x IN s) <-> ~ (s = EMPTY).
Proof.
  intros s; split.
  - intros [x hx] ->; exact hx.
  - intros h; apply NNPP; intros hn; apply h; apply set_ext; intros x; sets.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IN_UNIV" *)
Theorem IN_UNIV : forall x : A, x IN UNIV.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "UNIV_NOT_EMPTY" *)
Theorem UNIV_NOT_EMPTY `{Inhabited A} : ~ (UNIV = (EMPTY : A -> Prop)).
Proof. intros E; apply (NOT_IN_EMPTY (inhabitant A)); rewrite <- E; exact Logic.I. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "EQ_UNIV" *)
Theorem EQ_UNIV : forall s : A -> Prop, (forall x, x IN s) <-> (s = UNIV).
Proof. intros s; split; [intros h; sets|intros -> x; exact Logic.I]. Qed.

(** ** Subsets *)

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_THM" *)
Theorem SUBSET_THM : forall P Q : A -> Prop, P SUBSET Q -> (forall x, x IN P -> x IN Q).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_TRANS" *)
Theorem SUBSET_TRANS : forall s t u : A -> Prop, s SUBSET t /\ t SUBSET u -> s SUBSET u.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_REFL" *)
Theorem SUBSET_REFL : forall s : A -> Prop, s SUBSET s.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_ANTISYM" *)
Theorem SUBSET_ANTISYM : forall s t : A -> Prop, (s SUBSET t) /\ (t SUBSET s) -> (s = t).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_ANTISYM_EQ" *)
Theorem SUBSET_ANTISYM_EQ : forall s t : A -> Prop, (s SUBSET t) /\ (t SUBSET s) <-> (s = t).
Proof. intros s t; split; [apply SUBSET_ANTISYM|intros ->; split; apply SUBSET_REFL]. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SET_EQ_SUBSET" *)
Theorem SET_EQ_SUBSET : forall s t : A -> Prop, (s = t) <-> (s SUBSET t) /\ (t SUBSET s).
Proof. intros; rewrite SUBSET_ANTISYM_EQ; reflexivity. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "EQ_SUBSET_SUBSET" *)
Theorem EQ_SUBSET_SUBSET : forall s t : A -> Prop, (s = t) -> s SUBSET t /\ t SUBSET s.
Proof. intros s t ->; split; apply SUBSET_REFL. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "EMPTY_SUBSET" *)
Theorem EMPTY_SUBSET : forall s : A -> Prop, EMPTY SUBSET s.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_EMPTY" *)
Theorem SUBSET_EMPTY : forall s : A -> Prop, s SUBSET EMPTY <-> (s = EMPTY).
Proof. intros s; split; [intros h; sets|intros ->; apply SUBSET_REFL]. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_UNIV" *)
Theorem SUBSET_UNIV : forall s : A -> Prop, s SUBSET UNIV.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "UNIV_SUBSET" *)
Theorem UNIV_SUBSET : forall s : A -> Prop, UNIV SUBSET s <-> (s = UNIV).
Proof. intros s; split; [intros h; sets|intros ->; apply SUBSET_REFL]. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "PSUBSET_TRANS" *)
Theorem PSUBSET_TRANS : forall s t u : A -> Prop, (s PSUBSET t /\ t PSUBSET u) -> (s PSUBSET u).
Proof.
  intros s t u [[h1 n1] [h2 n2]]; split; [apply (SUBSET_TRANS s t u); auto|intros ->].
  apply n2, SUBSET_ANTISYM; auto.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "PSUBSET_IRREFL" *)
Theorem PSUBSET_IRREFL : forall s : A -> Prop, ~ (s PSUBSET s).
Proof. intros s [_ h]; apply h; reflexivity. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "NOT_PSUBSET_EMPTY" *)
Theorem NOT_PSUBSET_EMPTY : forall s : A -> Prop, ~ (s PSUBSET EMPTY).
Proof. intros s [h n]; apply n, SUBSET_EMPTY, h. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "NOT_UNIV_PSUBSET" *)
Theorem NOT_UNIV_PSUBSET : forall s : A -> Prop, ~ (UNIV PSUBSET s).
Proof. intros s [h n]; apply n; symmetry; apply UNIV_SUBSET, h. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "PSUBSET_UNIV" *)
Theorem PSUBSET_UNIV : forall s : A -> Prop, (s PSUBSET UNIV) <-> exists x : A, ~ (x IN s).
Proof.
  intros s; split.
  - intros [_ n]; apply NNPP; intros hn; apply n; apply set_ext; intros x.
    split; [intros; exact Logic.I|intros _].
    apply NNPP; intros h'; apply hn; exists x; exact h'.
  - intros [x hx]; split; [apply SUBSET_UNIV|intros ->; apply hx; exact Logic.I].
Qed.

(** ** Union *)

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IN_UNION" *)
Theorem IN_UNION : forall (s t : A -> Prop) x, x IN (s UNION t) <-> x IN s \/ x IN t.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "UNION_ASSOC" *)
Theorem UNION_ASSOC : forall s t u : A -> Prop, s UNION (t UNION u) = (s UNION t) UNION u.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "UNION_IDEMPOT" *)
Theorem UNION_IDEMPOT : forall s : A -> Prop, s UNION s = s.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "UNION_COMM" *)
Theorem UNION_COMM : forall s t : A -> Prop, s UNION t = t UNION s.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_UNION" *)
Theorem SUBSET_UNION :
  (forall s t : A -> Prop, s SUBSET (s UNION t)) /\ (forall s t : A -> Prop, s SUBSET (t UNION s)).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "UNION_SUBSET" *)
Theorem UNION_SUBSET : forall s t u : A -> Prop, (s UNION t) SUBSET u <-> s SUBSET u /\ t SUBSET u.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_UNION_ABSORPTION" *)
Theorem SUBSET_UNION_ABSORPTION : forall s t : A -> Prop, s SUBSET t <-> (s UNION t = t).
Proof.
  intros s t; split; [sets|intros E x hx; rewrite <- E; left; exact hx].
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "UNION_EMPTY" *)
Theorem UNION_EMPTY :
  (forall s : A -> Prop, EMPTY UNION s = s) /\ (forall s : A -> Prop, s UNION EMPTY = s).
Proof. split; sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "UNION_UNIV" *)
Theorem UNION_UNIV :
  (forall s : A -> Prop, UNIV UNION s = UNIV) /\ (forall s : A -> Prop, s UNION UNIV = UNIV).
Proof. split; sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "EMPTY_UNION" *)
Theorem EMPTY_UNION : forall s t : A -> Prop,
  (s UNION t = EMPTY) <-> ((s = EMPTY) /\ (t = EMPTY)).
Proof.
  intros s t; split; [intros E; split; apply set_ext; intros x;
    assert (h := f_equal (fun u => u x) E); cbn in h; unfold_sets;
    (split; [intros hx; rewrite <- h; tauto|tauto])|].
  intros [-> ->]; sets.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "FORALL_IN_UNION" *)
Theorem FORALL_IN_UNION : forall (P : A -> Prop) s t,
  (forall x, x IN s UNION t -> P x) <-> (forall x, x IN s -> P x) /\ (forall x, x IN t -> P x).
Proof. sets. Qed.

(** ** Intersection *)

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IN_INTER" *)
Theorem IN_INTER : forall (s t : A -> Prop) x, x IN (s INTER t) <-> x IN s /\ x IN t.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INTER_ASSOC" *)
Theorem INTER_ASSOC : forall s t u : A -> Prop, s INTER (t INTER u) = (s INTER t) INTER u.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INTER_IDEMPOT" *)
Theorem INTER_IDEMPOT : forall s : A -> Prop, s INTER s = s.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INTER_COMM" *)
Theorem INTER_COMM : forall s t : A -> Prop, s INTER t = t INTER s.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INTER_SUBSET" *)
Theorem INTER_SUBSET :
  (forall s t : A -> Prop, (s INTER t) SUBSET s) /\ (forall s t : A -> Prop, (t INTER s) SUBSET s).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_INTER" *)
Theorem SUBSET_INTER : forall s t u : A -> Prop, s SUBSET (t INTER u) <-> s SUBSET t /\ s SUBSET u.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_INTER_ABSORPTION" *)
Theorem SUBSET_INTER_ABSORPTION : forall s t : A -> Prop, s SUBSET t <-> (s INTER t = s).
Proof.
  intros s t; split; [sets|intros E x hx; rewrite <- E in hx; apply hx].
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_INTER1" *)
Theorem SUBSET_INTER1 : forall s t : A -> Prop, s SUBSET t -> (s INTER t = s).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_INTER2" *)
Theorem SUBSET_INTER2 : forall s t : A -> Prop, s SUBSET t -> (t INTER s = s).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INTER_EMPTY" *)
Theorem INTER_EMPTY :
  (forall s : A -> Prop, EMPTY INTER s = EMPTY) /\ (forall s : A -> Prop, s INTER EMPTY = EMPTY).
Proof. split; sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INTER_UNIV" *)
Theorem INTER_UNIV :
  (forall s : A -> Prop, UNIV INTER s = s) /\ (forall s : A -> Prop, s INTER UNIV = s).
Proof. split; sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "UNION_OVER_INTER" *)
Theorem UNION_OVER_INTER : forall s t u : A -> Prop,
  s INTER (t UNION u) = (s INTER t) UNION (s INTER u).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INTER_OVER_UNION" *)
Theorem INTER_OVER_UNION : forall s t u : A -> Prop,
  s UNION (t INTER u) = (s UNION t) INTER (s UNION u).
Proof. sets. Qed.

(** ** Disjointness *)

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IN_DISJOINT" *)
Theorem IN_DISJOINT : forall s t : A -> Prop, DISJOINT s t <-> ~ (exists x, x IN s /\ x IN t).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DISJOINT_SYM" *)
Theorem DISJOINT_SYM : forall s t : A -> Prop, DISJOINT s t <-> DISJOINT t s.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DISJOINT_ALT" *)
Theorem DISJOINT_ALT : forall s t : A -> Prop, DISJOINT s t <-> forall x, x IN s -> ~ (x IN t).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DISJOINT_ALT'" *)
Theorem DISJOINT_ALT' : forall s t : A -> Prop, DISJOINT s t <-> forall x, x IN t -> x NOTIN s.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DISJOINT_EMPTY" *)
Theorem DISJOINT_EMPTY : forall s : A -> Prop, DISJOINT EMPTY s /\ DISJOINT s EMPTY.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DISJOINT_EMPTY_REFL" *)
Theorem DISJOINT_EMPTY_REFL : forall s : A -> Prop, (s = EMPTY) <-> (DISJOINT s s).
Proof. intros s; rewrite DISJOINT_iff; split; [intros ->; sets|intros h; sets]. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DISJOINT_UNION" *)
Theorem DISJOINT_UNION : forall s t u : A -> Prop,
  DISJOINT (s UNION t) u <-> DISJOINT s u /\ DISJOINT t u.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DISJOINT_UNION'" *)
Theorem DISJOINT_UNION' : forall s t u : A -> Prop,
  DISJOINT u (s UNION t) <-> DISJOINT u s /\ DISJOINT u t.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DISJOINT_UNION_BOTH" *)
Theorem DISJOINT_UNION_BOTH : forall s t u : A -> Prop,
  (DISJOINT (s UNION t) u <-> DISJOINT s u /\ DISJOINT t u) /\
  (DISJOINT u (s UNION t) <-> DISJOINT s u /\ DISJOINT t u).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DISJOINT_SUBSET" *)
Theorem DISJOINT_SUBSET : forall s t u : A -> Prop, DISJOINT s t /\ u SUBSET t -> DISJOINT s u.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_DISJOINT" *)
Theorem SUBSET_DISJOINT : forall s t u v : A -> Prop,
  DISJOINT s t /\ u SUBSET s /\ v SUBSET t -> DISJOINT u v.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DISJOINT_SUBSET'" *)
Theorem DISJOINT_SUBSET' : forall s t u : A -> Prop, DISJOINT s t /\ u SUBSET s -> DISJOINT u t.
Proof. sets. Qed.

(** ** Difference *)

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IN_DIFF" *)
Theorem IN_DIFF : forall (s t : A -> Prop) x, x IN (s DIFF t) <-> x IN s /\ x NOTIN t.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DIFF_EMPTY" *)
Theorem DIFF_EMPTY : forall s : A -> Prop, s DIFF EMPTY = s.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "EMPTY_DIFF" *)
Theorem EMPTY_DIFF : forall s : A -> Prop, EMPTY DIFF s = EMPTY.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DIFF_UNIV" *)
Theorem DIFF_UNIV : forall s : A -> Prop, s DIFF UNIV = EMPTY.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DIFF_DIFF" *)
Theorem DIFF_DIFF : forall s t : A -> Prop, (s DIFF t) DIFF t = s DIFF t.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DIFF_EQ_EMPTY" *)
Theorem DIFF_EQ_EMPTY : forall s : A -> Prop, s DIFF s = EMPTY.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DIFF_SUBSET" *)
Theorem DIFF_SUBSET : forall s t : A -> Prop, (s DIFF t) SUBSET s.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "UNION_DIFF" *)
Theorem UNION_DIFF : forall s t : A -> Prop,
  s SUBSET t -> (s UNION (t DIFF s) = t) /\ ((t DIFF s) UNION s = t).
Proof.
  intros s t h; split; apply set_ext; intros y; specialize (h y); unfold_sets;
    destruct (classic (s y)); tauto.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DIFF_UNION" *)
Theorem DIFF_UNION : forall x y z : A -> Prop, x DIFF (y UNION z) = x DIFF y DIFF z.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "UNION_DIFF_EQ" *)
Theorem UNION_DIFF_EQ :
  (forall s t : A -> Prop, (s UNION (t DIFF s)) = (s UNION t)) /\
  (forall s t : A -> Prop, ((t DIFF s) UNION s) = (t UNION s)).
Proof. split; intros s t; apply set_ext; intros y; unfold_sets; destruct (classic (s y)); tauto. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DIFF_COMM" *)
Theorem DIFF_COMM : forall x y z : A -> Prop, x DIFF y DIFF z = x DIFF z DIFF y.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DIFF_SAME_UNION" *)
Theorem DIFF_SAME_UNION : forall x y : A -> Prop,
  ((x UNION y) DIFF x = y DIFF x) /\ ((x UNION y) DIFF y = x DIFF y).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DIFF_INTER" *)
Theorem DIFF_INTER : forall s t g : A -> Prop, (s DIFF t) INTER g = s INTER g DIFF t.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DIFF_INTER2" *)
Theorem DIFF_INTER2 : forall s t : A -> Prop, s DIFF (t INTER s) = s DIFF t.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DISJOINT_DIFF" *)
Theorem DISJOINT_DIFF : forall s t : A -> Prop, DISJOINT t (s DIFF t) /\ DISJOINT (s DIFF t) t.
Proof. sets. Qed.

(** ** Insertion and deletion *)

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IN_INSERT" *)
Theorem IN_INSERT : forall (x y : A) s, x IN (y INSERT s) <-> x = y \/ x IN s.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "COMPONENT" *)
Theorem COMPONENT : forall (x : A) s, x IN (x INSERT s).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IN_DELETE" *)
Theorem IN_DELETE : forall s (x y : A), x IN (s DELETE y) <-> x IN s /\ x <> y.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "ABSORPTION" *)
Theorem ABSORPTION : forall (x : A) s, (x IN s) <-> (x INSERT s = s).
Proof.
  intros x s; split; [sets|intros E; rewrite <- E; left; reflexivity].
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "ABSORPTION_RWT" *)
Theorem ABSORPTION_RWT : forall (x : A) s, x IN s -> (x INSERT s = s).
Proof. intros; apply ABSORPTION; assumption. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INSERT_INSERT" *)
Theorem INSERT_INSERT : forall (x : A) s, x INSERT (x INSERT s) = x INSERT s.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INSERT_COMM" *)
Theorem INSERT_COMM : forall (x y : A) s, x INSERT (y INSERT s) = y INSERT (x INSERT s).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INSERT_UNIV" *)
Theorem INSERT_UNIV : forall x : A, x INSERT UNIV = UNIV.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "NOT_INSERT_EMPTY" *)
Theorem NOT_INSERT_EMPTY : forall (x : A) s, ~ (x INSERT s = EMPTY).
Proof. intros x s E; apply (NOT_IN_EMPTY x); rewrite <- E; left; reflexivity. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "NOT_EMPTY_INSERT" *)
Theorem NOT_EMPTY_INSERT : forall (x : A) s, ~ (EMPTY = x INSERT s).
Proof. intros x s E; apply (NOT_INSERT_EMPTY x s); symmetry; exact E. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INSERT_UNION" *)
Theorem INSERT_UNION : forall (x : A) s t,
  (x INSERT s) UNION t = (if classical_dec (x IN t) then s UNION t else x INSERT (s UNION t)).
Proof. intros; destruct (classical_dec _); sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INSERT_UNION_EQ" *)
Theorem INSERT_UNION_EQ : forall (x : A) s t, (x INSERT s) UNION t = x INSERT (s UNION t).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INSERT_INTER" *)
Theorem INSERT_INTER : forall (x : A) s t,
  (x INSERT s) INTER t = (if classical_dec (x IN t) then x INSERT (s INTER t) else s INTER t).
Proof. intros; destruct (classical_dec _); sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DISJOINT_INSERT" *)
Theorem DISJOINT_INSERT : forall (x : A) s t, DISJOINT (x INSERT s) t <-> DISJOINT s t /\ x NOTIN t.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DISJOINT_INSERT'" *)
Theorem DISJOINT_INSERT' : forall (x : A) s t, DISJOINT t (x INSERT s) <-> DISJOINT t s /\ x NOTIN t.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INSERT_SUBSET" *)
Theorem INSERT_SUBSET : forall (x : A) s t, (x INSERT s) SUBSET t <-> x IN t /\ s SUBSET t.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_INSERT" *)
Theorem SUBSET_INSERT : forall (x : A) s, x NOTIN s -> forall t, s SUBSET (x INSERT t) <-> s SUBSET t.
Proof. sets; specialize (H0 x0 H1); firstorder. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INSERT_DIFF" *)
Theorem INSERT_DIFF : forall s t (x : A),
  (x INSERT s) DIFF t = (if classical_dec (x IN t) then s DIFF t else (x INSERT (s DIFF t))).
Proof. intros; destruct (classical_dec _); sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "FORALL_IN_INSERT" *)
Theorem FORALL_IN_INSERT : forall (P : A -> Prop) a s,
  (forall x, x IN (a INSERT s) -> P x) <-> P a /\ (forall x, x IN s -> P x).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "EXISTS_IN_INSERT" *)
Theorem EXISTS_IN_INSERT : forall (P : A -> Prop) a s,
  (exists x, x IN (a INSERT s) /\ P x) <-> P a \/ exists x, x IN s /\ P x.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DELETE_NON_ELEMENT" *)
Theorem DELETE_NON_ELEMENT : forall (x : A) s, x NOTIN s <-> (s DELETE x = s).
Proof.
  intros x s; split; [sets|intros E h; rewrite <- E in h; sets].
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DELETE_NON_ELEMENT_RWT" *)
Theorem DELETE_NON_ELEMENT_RWT : forall s (x : A), x NOTIN s -> (s DELETE x = s).
Proof. intros; apply DELETE_NON_ELEMENT; assumption. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "EMPTY_DELETE" *)
Theorem EMPTY_DELETE : forall x : A, EMPTY DELETE x = EMPTY.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "ELT_IN_DELETE" *)
Theorem ELT_IN_DELETE : forall (x : A) s, ~ (x IN (s DELETE x)).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DELETE_DELETE" *)
Theorem DELETE_DELETE : forall (x : A) s, (s DELETE x) DELETE x = s DELETE x.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DELETE_COMM" *)
Theorem DELETE_COMM : forall (x y : A) s, (s DELETE x) DELETE y = (s DELETE y) DELETE x.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DELETE_SUBSET" *)
Theorem DELETE_SUBSET : forall (x : A) s, (s DELETE x) SUBSET s.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_DELETE" *)
Theorem SUBSET_DELETE : forall (x : A) s t, s SUBSET (t DELETE x) <-> x NOTIN s /\ s SUBSET t.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_INSERT_DELETE" *)
Theorem SUBSET_INSERT_DELETE : forall (x : A) s t, s SUBSET (x INSERT t) <-> ((s DELETE x) SUBSET t).
Proof.
  intros x s t; unfold_sets; split; intros h y hy.
  - destruct hy as [hy n]; destruct (h y hy); [tauto|auto].
  - destruct (classic (y = x)); [left; auto|right; apply h; split; [exact hy|tauto]].
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_OF_INSERT" *)
Theorem SUBSET_OF_INSERT : forall (x : A) s, s SUBSET (x INSERT s).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DIFF_INSERT" *)
Theorem DIFF_INSERT : forall s t (x : A), s DIFF (x INSERT t) = (s DELETE x) DIFF t.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DELETE_INSERT" *)
Theorem DELETE_INSERT : forall (x y : A) s,
  (x INSERT s) DELETE y = (if classical_dec (x = y) then s DELETE y else x INSERT (s DELETE y)).
Proof. intros; destruct (classical_dec _); sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INSERT_DELETE" *)
Theorem INSERT_DELETE : forall (x : A) s, x IN s -> (x INSERT (s DELETE x) = s).
Proof. sets; destruct (classic (x0 = x)); firstorder congruence. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DELETE_INTER" *)
Theorem DELETE_INTER : forall s t (x : A), (s DELETE x) INTER t = (s INTER t) DELETE x.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SET_CASES" *)
Theorem SET_CASES : forall s : A -> Prop,
  (s = EMPTY) \/ exists (x : A) t, ((s = x INSERT t) /\ ~ (x IN t)).
Proof.
  intros s; destruct (classic (s = EMPTY)) as [h|h]; [left; exact h|right].
  apply MEMBER_NOT_EMPTY in h as [x hx]; exists x, (s DELETE x).
  split; [symmetry; apply INSERT_DELETE, hx|apply ELT_IN_DELETE].
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DECOMPOSITION" *)
Theorem DECOMPOSITION : forall s (x : A), x IN s <-> exists t, s = x INSERT t /\ x NOTIN t.
Proof.
  intros s x; split.
  - intros hx; exists (s DELETE x); split; [symmetry; apply INSERT_DELETE, hx|apply ELT_IN_DELETE].
  - intros [t [-> _]]; apply COMPONENT.
Qed.

(** ** Singletons *)

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IN_SING" *)
Theorem IN_SING : forall x y : A, x IN (y INSERT {}) <-> (x = y).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SING" *)
Theorem SING_thm : forall x : A, SING (x INSERT {}).
Proof. intros x; exists x; reflexivity. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "NOT_SING_EMPTY" *)
Theorem NOT_SING_EMPTY : forall x : A, ~ ((x INSERT {}) = EMPTY).
Proof. intros; apply NOT_INSERT_EMPTY. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "NOT_EMPTY_SING" *)
Theorem NOT_EMPTY_SING : forall x : A, ~ (EMPTY = (x INSERT {})).
Proof. intros; apply NOT_EMPTY_INSERT. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "EQUAL_SING" *)
Theorem EQUAL_SING : forall x y : A, ((x INSERT {}) = (y INSERT {})) <-> (x = y).
Proof.
  intros x y; split; [intros E|intros ->; reflexivity].
  assert (h : x IN (y INSERT {})) by (rewrite <- E; left; reflexivity); sets.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INSERT_SING_UNION" *)
Theorem INSERT_SING_UNION : forall s (x : A), x INSERT s = (x INSERT {}) UNION s.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SING_DELETE" *)
Theorem SING_DELETE : forall x : A, (x INSERT {}) DELETE x = EMPTY.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DISJOINT_SING_EMPTY" *)
Theorem DISJOINT_SING_EMPTY : forall x : A, DISJOINT (x INSERT {}) EMPTY.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_SING" *)
Theorem SUBSET_SING : forall (x : A -> Prop) a, x SUBSET (a INSERT {}) <-> x = {} \/ x = (a INSERT {}).
Proof.
  intros x a; split.
  - intros h; destruct (classic (a IN x)) as [ha|ha]; [right|left]; apply set_ext; intros y;
      specialize (h y); sets.
  - intros [->| ->]; sets.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DELETE_EQ_SING" *)
Theorem DELETE_EQ_SING : forall s (x : A), (x IN s) -> ((s DELETE x = EMPTY) <-> (s = (x INSERT {}))).
Proof.
  intros s x hx; split.
  - intros E; apply set_ext; intros y; assert (h := f_equal (fun u => u y) E); cbn in h; unfold_sets.
    split; [intros hy; destruct (classic (y = x)); [left; auto|exfalso; rewrite <- h; tauto]|].
    intros [->|[]]; exact hx.
  - intros ->; apply SING_DELETE.
Qed.

End Basic.

(** ** Image *)

Section Image.
Context {A B C : Type}.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IN_IMAGE" *)
Theorem IN_IMAGE : forall (y : B) s (f : A -> B), y IN (IMAGE f s) <-> exists x : A, y = f x /\ x IN s.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IMAGE_IN" *)
Theorem IMAGE_IN : forall (x : A) s, (x IN s) -> forall (f : A -> B), f x IN (IMAGE f s).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IMAGE_EMPTY" *)
Theorem IMAGE_EMPTY : forall f : A -> B, IMAGE f EMPTY = EMPTY.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IMAGE_ID" *)
Theorem IMAGE_ID : forall s : A -> Prop, IMAGE (fun x : A => x) s = s.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IMAGE_I" *)
Theorem IMAGE_I : forall s : A -> Prop, IMAGE I s = s.
Proof. unfold I; sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IMAGE_COMPOSE" *)
Theorem IMAGE_COMPOSE : forall (f : B -> C) (g : A -> B) s, IMAGE (f ∘ g) s = IMAGE f (IMAGE g s).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IMAGE_o" *)
Theorem IMAGE_o : forall (f : B -> C) (g : A -> B) s, IMAGE (f ∘ g) s = IMAGE f (IMAGE g s).
Proof. exact IMAGE_COMPOSE. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IMAGE_IMAGE" *)
Theorem IMAGE_IMAGE : forall (f : B -> C) (g : A -> B) s, IMAGE f (IMAGE g s) = IMAGE (f ∘ g) s.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IMAGE_INSERT" *)
Theorem IMAGE_INSERT : forall (f : A -> B) x s, IMAGE f (x INSERT s) = f x INSERT (IMAGE f s).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IMAGE_EQ_EMPTY" *)
Theorem IMAGE_EQ_EMPTY : forall s (f : A -> B),
  (IMAGE f s = {} <-> s = {}) /\ ({} = IMAGE f s <-> s = {}).
Proof.
  intros s f; assert (h : IMAGE f s = {} <-> s = {}).
  { split; [intros E; apply set_ext; intros x; split; [intros hx|intros []];
      assert (hh : IMAGE f s (f x)) by (exists x; split; [reflexivity|exact hx]);
      rewrite E in hh; exact hh|].
    intros ->; apply IMAGE_EMPTY. }
  split; [exact h|split; intros E; [apply h; symmetry; exact E|symmetry; apply h, E]].
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IMAGE_DELETE" *)
Theorem IMAGE_DELETE : forall (f : A -> B) x s, ~ (x IN s) -> (IMAGE f (s DELETE x) = (IMAGE f s)).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IMAGE_UNION" *)
Theorem IMAGE_UNION : forall (f : A -> B) s t, IMAGE f (s UNION t) = (IMAGE f s) UNION (IMAGE f t).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IMAGE_SUBSET" *)
Theorem IMAGE_SUBSET : forall s t, (s SUBSET t) -> forall f : A -> B, (IMAGE f s) SUBSET (IMAGE f t).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IMAGE_INTER" *)
Theorem IMAGE_INTER : forall (f : A -> B) s t, IMAGE f (s INTER t) SUBSET (IMAGE f s INTER IMAGE f t).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IMAGE_11" *)
Theorem IMAGE_11 : forall (f : A -> B) s1 s2,
  (forall x y, (f x = f y) <-> (x = y)) -> ((IMAGE f s1 = IMAGE f s2) <-> (s1 = s2)).
Proof.
  intros f s1 s2 hf; split; [intros E|intros ->; reflexivity].
  apply set_ext; intros x; split; intros hx.
  - assert (h : IMAGE f s2 (f x)) by (rewrite <- E; exists x; auto).
    destruct h as [y [hy h]]; apply hf in hy; subst; exact h.
  - assert (h : IMAGE f s1 (f x)) by (rewrite E; exists x; auto).
    destruct h as [y [hy h]]; apply hf in hy; subst; exact h.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "DISJOINT_IMAGE" *)
Theorem DISJOINT_IMAGE : forall (f : A -> B) s1 s2,
  (forall x y, (f x = f y) <-> (x = y)) -> (DISJOINT (IMAGE f s1) (IMAGE f s2) <-> DISJOINT s1 s2).
Proof.
  intros f s1 s2 hf; rewrite !DISJOINT_iff; unfold_sets; split.
  - intros h x [h1 h2]; apply (h (f x)); split; exists x; auto.
  - intros h y [[x1 [-> h1]] [x2 [e h2]]]; apply hf in e; subst; apply (h x2); auto.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IMAGE_CONG" *)
Theorem IMAGE_CONG : forall (f : A -> B) s f' s',
  (s = s') /\ (forall x, x IN s' -> (f x = f' x)) -> IMAGE f s = IMAGE f' s'.
Proof. intros f s f' s' [-> h]; apply set_ext; intros y; unfold_sets; firstorder (subst; eauto). Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "FORALL_IN_IMAGE" *)
Theorem FORALL_IN_IMAGE : forall (P : B -> Prop) (f : A -> B) s,
  (forall y, y IN IMAGE f s -> P y) <-> (forall x, x IN s -> P (f x)).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "EXISTS_IN_IMAGE" *)
Theorem EXISTS_IN_IMAGE : forall (P : B -> Prop) (f : A -> B) s,
  (exists y, y IN IMAGE f s /\ P y) <-> exists x, x IN s /\ P (f x).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IMAGE_SING" *)
Theorem IMAGE_SING : forall (f : A -> B) x, IMAGE f (x INSERT {}) = (f x INSERT {}).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IN_PREIMAGE" *)
Theorem IN_PREIMAGE : forall (f : A -> B) s x, x IN PREIMAGE f s <-> f x IN s.
Proof. reflexivity. Qed.

End Image.

(** ** Injections, surjections, bijections *)

Section Inj.
Context {A B C : Type}.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INJ_IFF" *)
Theorem INJ_IFF : forall (f : A -> B) s t,
  INJ f s t <-> (forall x, x IN s -> f x IN t) /\
                (forall x y, x IN s /\ y IN s -> ((f x = f y) <-> (x = y))).
Proof. unfold INJ; firstorder (subst; auto). Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INJ_ID" *)
Theorem INJ_ID : forall s : A -> Prop, INJ (fun x : A => x) s s.
Proof. unfold INJ; firstorder. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INJ_COMPOSE" *)
Theorem INJ_COMPOSE : forall (f : A -> B) (g : B -> C) s t u,
  (INJ f s t /\ INJ g t u) -> INJ (g ∘ f) s u.
Proof. unfold INJ; firstorder. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INJ_EMPTY" *)
Theorem INJ_EMPTY : forall f : A -> B,
  (forall s, INJ f {} s) /\ (forall s, INJ f s {} <-> (s = {})).
Proof.
  intros f; split; [unfold INJ; sets|intros s; split].
  - intros [h _]; apply set_ext; intros x; split; [intros hx; exact (h x hx)|intros []].
  - intros ->; unfold INJ; sets.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INJ_DELETE" *)
Theorem INJ_DELETE : forall (f : A -> B) s t,
  INJ f s t -> forall e, e IN s -> INJ f (s DELETE e) (t DELETE (f e)).
Proof.
  unfold INJ; intros f s t [h1 h2] e he; unfold_sets; split; [|firstorder].
  intros x [hx n]; split; [auto|intros [E|[]]; apply n; left; apply h2; auto].
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INJ_INSERT" *)
Theorem INJ_INSERT : forall (f : A -> B) x s t,
  INJ f (x INSERT s) t <-> INJ f s t /\ (f x) IN t /\ (forall y, y IN s /\ (f x = f y) -> (x = y)).
Proof.
  intros f x s t; unfold INJ; unfold_sets; split.
  - intros [h1 h2]; split; [split; [auto|intros u v [hu hv]; apply h2; auto]|].
    split; [auto|intros y [hy e]; apply h2; auto].
  - intros [[h1 h2] [hx h3]]; split; [intros z [->|hz]; auto|].
    intros u v [[->|hu] [->|hv]] e;
      [reflexivity|apply h3; auto|symmetry; apply h3; auto|apply h2; auto].
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INJ_EXTEND" *)
Theorem INJ_EXTEND `{EqDecision A} : forall (b : A -> B) s t x y,
  INJ b s t /\ x NOTIN s /\ y NOTIN t -> INJ ((x =+ y) b) (x INSERT s) (y INSERT t).
Proof.
  unfold INJ, UPDATE; intros b s t x y [[h1 h2] [hx hy]]; unfold_sets; split.
  - intros z hz; destruct (decide (x = z)) as [<-|n]; [left; reflexivity|right].
    destruct hz as [->|hz]; [tauto|apply h1, hz].
  - intros u v [hu hv]; destruct (decide (x = u)) as [<-|nu], (decide (x = v)) as [<-|nv]; intros e.
    + reflexivity.
    + destruct hv as [->|hv]; [tauto|]; exfalso; apply hy; rewrite e; apply h1, hv.
    + destruct hu as [->|hu]; [tauto|]; exfalso; apply hy; rewrite <- e; apply h1, hu.
    + destruct hu as [->|hu]; [tauto|]; destruct hv as [->|hv]; [tauto|]; apply h2; auto.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INJ_SUBSET" 2078 *)
Theorem INJ_SUBSET : forall (f : A -> B) s t s0 t0,
  INJ f s t /\ s0 SUBSET s /\ t SUBSET t0 -> INJ f s0 t0.
Proof. unfold INJ; sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INJ_IMAGE" *)
Theorem INJ_IMAGE : forall (f : A -> B) s t, INJ f s t -> INJ f s (IMAGE f s).
Proof. unfold INJ; sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INJ_IMAGE_SUBSET" *)
Theorem INJ_IMAGE_SUBSET : forall (f : A -> B) s t, INJ f s t -> IMAGE f s SUBSET t.
Proof. unfold INJ; sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INJ_CONG" *)
Theorem INJ_CONG : forall (f g : A -> B) s t,
  (forall x, x IN s -> (f x = g x)) -> (INJ f s t <-> INJ g s t).
Proof.
  intros f g s t h; unfold INJ; split; intros [h1 h2]; split.
  - intros x hx; rewrite <- (h x hx); auto.
  - intros x y [hx hy] e; apply h2; [split; auto|rewrite (h x hx), (h y hy); exact e].
  - intros x hx; rewrite (h x hx); auto.
  - intros x y [hx hy] e; apply h2; [split; auto|rewrite <- (h x hx), <- (h y hy); exact e].
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INJ_SUBSET_UNIV" *)
Theorem INJ_SUBSET_UNIV : forall (f : A -> B) (s : A -> Prop), INJ f UNIV UNIV -> INJ f s UNIV.
Proof. unfold INJ; sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INJ_I" *)
Theorem INJ_I : forall s : A -> Prop, INJ I s UNIV.
Proof. unfold INJ, I; sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INJ_IMP_11" *)
Theorem INJ_IMP_11 : forall f : A -> B, INJ f UNIV UNIV -> forall x y, f x = f y <-> x = y.
Proof. unfold INJ; intros f [_ h] x y; split; [apply h; split; exact Logic.I|intros ->; reflexivity]. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INJ_EQ_11" *)
Theorem INJ_EQ_11 : forall (f : A -> A) s x y,
  INJ f s s /\ x IN s /\ y IN s -> ((f x = f y) <-> (x = y)).
Proof. unfold INJ; intros f s x y [[_ h] [hx hy]]; split; [apply h; auto|intros ->; reflexivity]. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INJ_ELEMENT" *)
Theorem INJ_ELEMENT : forall (f : A -> B) s t x, INJ f s t /\ x IN s -> f x IN t.
Proof. unfold INJ; firstorder. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SURJ_ID" *)
Theorem SURJ_ID : forall s : A -> Prop, SURJ (fun x : A => x) s s.
Proof. unfold SURJ; firstorder. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SURJ_COMPOSE" *)
Theorem SURJ_COMPOSE : forall (f : A -> B) (g : B -> C) s t u,
  (SURJ f s t /\ SURJ g t u) -> SURJ (g ∘ f) s u.
Proof.
  unfold SURJ; intros f g s t u [[h1 h2] [h3 h4]]; split; [auto|].
  intros z hz; destruct (h4 z hz) as [y [hy <-]]; destruct (h2 y hy) as [x [hx <-]]; eauto.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SURJ_EMPTY" *)
Theorem SURJ_EMPTY : forall f : A -> B,
  (forall s, SURJ f {} s <-> (s = {})) /\ (forall s, SURJ f s {} <-> (s = {})).
Proof.
  intros f; split; intros s; split.
  - intros [_ h]; apply set_ext; intros y; split; [intros hy; destruct (h y hy) as [x [[] _]]|intros []].
  - intros ->; unfold SURJ; sets.
  - intros [h _]; apply set_ext; intros x; split; [intros hx; exact (h x hx)|intros []].
  - intros ->; unfold SURJ; sets.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IMAGE_SURJ" *)
Theorem IMAGE_SURJ : forall (f : A -> B) s t, SURJ f s t <-> ((IMAGE f s) = t).
Proof.
  unfold SURJ; intros f s t; split.
  - intros [h1 h2]; apply set_ext; intros y; unfold_sets; split.
    + intros [x [-> hx]]; auto.
    + intros hy; destruct (h2 y hy) as [x [hx <-]]; eauto.
  - intros <-; unfold_sets; split; [eauto|intros y [x [-> hx]]; eauto].
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SURJ_IMAGE" *)
Theorem SURJ_IMAGE : forall (f : A -> B) s, SURJ f s (IMAGE f s).
Proof. intros; apply IMAGE_SURJ; reflexivity. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "BIJ_ID" *)
Theorem BIJ_ID : forall s : A -> Prop, BIJ (fun x : A => x) s s.
Proof. intros; split; [apply INJ_ID|apply SURJ_ID]. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "BIJ_I_SAME" *)
Theorem BIJ_I_SAME : forall s : A -> Prop, BIJ I s s.
Proof. intros; apply BIJ_ID. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "BIJ_IMP_11" *)
Theorem BIJ_IMP_11 : forall f : A -> B, BIJ f UNIV UNIV -> forall x y, (f x = f y) <-> (x = y).
Proof. intros f [h _]; apply INJ_IMP_11, h. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "BIJ_EMPTY" *)
Theorem BIJ_EMPTY : forall f : A -> B,
  (forall s, BIJ f {} s <-> (s = {})) /\ (forall s, BIJ f s {} <-> (s = {})).
Proof.
  intros f; split; intros s; unfold BIJ; split.
  - intros [hi hs]; apply (proj1 (SURJ_EMPTY f) s), hs.
  - intros ->; split; [apply (proj1 (INJ_EMPTY f))|apply (proj1 (SURJ_EMPTY f)); reflexivity].
  - intros [hi hs]; apply (proj2 (INJ_EMPTY f) s), hi.
  - intros ->; split; [apply (proj2 (INJ_EMPTY f)); reflexivity|apply (proj2 (SURJ_EMPTY f)); reflexivity].
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "BIJ_COMPOSE" *)
Theorem BIJ_COMPOSE : forall (f : A -> B) (g : B -> C) s t u,
  (BIJ f s t /\ BIJ g t u) -> BIJ (g ∘ f) s u.
Proof.
  intros f g s t u [[i1 s1] [i2 s2]]; split;
    [apply (INJ_COMPOSE f g s t u)|apply (SURJ_COMPOSE f g s t u)]; auto.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "BIJ_IS_INJ" *)
Theorem BIJ_IS_INJ : forall (f : A -> B) s t,
  BIJ f s t -> forall x y, x IN s /\ y IN s /\ (f x = f y) -> (x = y).
Proof. intros f s t [[_ h] _] x y (hx & hy & e); apply h; auto. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "BIJ_IS_SURJ" *)
Theorem BIJ_IS_SURJ : forall (f : A -> B) s t,
  BIJ f s t -> forall x, x IN t -> exists y, y IN s /\ f y = x.
Proof. intros f s t [_ [_ h]]; exact h. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "BIJ_ELEMENT" *)
Theorem BIJ_ELEMENT : forall (f : A -> B) s t x, BIJ f s t /\ x IN s -> f x IN t.
Proof. intros f s t x [[[h _] _] hx]; auto. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INJ_IMAGE_BIJ" *)
Theorem INJ_IMAGE_BIJ : forall s (f : A -> B), (exists t, INJ f s t) -> BIJ f s (IMAGE f s).
Proof. intros s f [t h]; split; [apply (INJ_IMAGE f s t h)|apply SURJ_IMAGE]. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "LINV_DEF" *)
Theorem LINV_DEF `{Inhabited A} : forall (f : A -> B) s t,
  INJ f s t -> (forall x, x IN s -> (LINV f s (f x) = x)).
Proof.
  intros f s t [_ h] x hx; unfold LINV.
  destruct (select_spec (fun y => y IN s /\ f y = f x)) as [h1 h2]; [exists x; auto|].
  apply h; auto.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "BIJ_LINV_INV" *)
Theorem BIJ_LINV_INV `{Inhabited A} : forall (f : A -> B) s t,
  BIJ f s t -> forall x, x IN t -> (f (LINV f s x) = x).
Proof.
  intros f s t [_ [_ h]] x hx; unfold LINV.
  destruct (select_spec (fun y => y IN s /\ f y = x)) as [h1 h2]; [|exact h2].
  destruct (h x hx) as [y [hy e]]; exists y; auto.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "BIJ_LINV_BIJ" *)
Theorem BIJ_LINV_BIJ `{Inhabited A} : forall (f : A -> B) s t, BIJ f s t -> BIJ (LINV f s) t s.
Proof.
  intros f s t hb; pose proof hb as [[hi1 hi2] [hs1 hs2]].
  assert (hm : forall x, x IN t -> LINV f s x IN s).
  { intros x hx; unfold LINV; destruct (select_spec (fun y => y IN s /\ f y = x)) as [h1 _]; [|exact h1].
    destruct (hs2 x hx) as [y [hy e]]; exists y; auto. }
  split; split; [exact hm| |exact hm|].
  - intros x y [hx hy] e; rewrite <- (BIJ_LINV_INV f s t hb x hx), <- (BIJ_LINV_INV f s t hb y hy), e;
      reflexivity.
  - intros x hx; exists (f x); split; [apply hi1, hx|apply (LINV_DEF f s t); [split|]; auto].
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "BIJ_IFF_INV" *)
Theorem BIJ_IFF_INV `{Inhabited A} : forall (f : A -> B) s t,
  BIJ f s t <->
  (forall x, x IN s -> f x IN t) /\
  exists g, (forall x, x IN t -> g x IN s) /\
            (forall x, x IN s -> (g (f x) = x)) /\
            (forall x, x IN t -> (f (g x) = x)).
Proof.
  intros f s t; split.
  - intros hb; pose proof (BIJ_LINV_BIJ f s t hb) as [[hg _] _]; split; [apply hb|].
    exists (LINV f s); split; [exact hg|split].
    + apply (LINV_DEF f s t), hb.
    + apply (BIJ_LINV_INV f s t hb).
  - intros [h1 [g (hg1 & hg2 & hg3)]]; split; split; [exact h1| |exact h1|].
    + intros x y [hx hy] e; rewrite <- (hg2 x hx), <- (hg2 y hy), e; reflexivity.
    + intros y hy; exists (g y); auto.
Qed.

End Inj.

(** ** Big union, complement, [count] *)

Section Misc.
Context {A : Type}.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IN_BIGUNION" *)
Theorem IN_BIGUNION : forall (x : A) sos, x IN BIGUNION sos <-> exists s, x IN s /\ s IN sos.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "BIGUNION_EMPTY" *)
Theorem BIGUNION_EMPTY : BIGUNION EMPTY = (EMPTY : A -> Prop).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "BIGUNION_INSERT" *)
Theorem BIGUNION_INSERT : forall (s : A -> Prop) P, BIGUNION (s INSERT P) = s UNION (BIGUNION P).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "BIGUNION_UNION" *)
Theorem BIGUNION_UNION : forall s1 s2 : (A -> Prop) -> Prop,
  BIGUNION (s1 UNION s2) = (BIGUNION s1) UNION (BIGUNION s2).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IN_COMPL" *)
Theorem IN_COMPL : forall (x : A) s, x IN COMPL s <-> x NOTIN s.
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "COMPL_COMPL" *)
Theorem COMPL_COMPL : forall s : A -> Prop, COMPL (COMPL s) = s.
Proof. sets_cl. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "COMPL_CLAUSES" *)
Theorem COMPL_CLAUSES : forall s : A -> Prop, (COMPL s INTER s = {}) /\ (COMPL s UNION s = UNIV).
Proof. sets_cl. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "COMPL_EMPTY" *)
Theorem COMPL_EMPTY : COMPL {} = (UNIV : A -> Prop).
Proof. sets. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "compl_insert" *)
Theorem compl_insert : forall s (x : A), COMPL (x INSERT s) = COMPL s DELETE x.
Proof. sets. Qed.

End Misc.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IN_COUNT" *)
Theorem IN_COUNT : forall m n, m IN count n <-> m < n.
Proof. reflexivity. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "COUNT_ZERO" *)
Theorem COUNT_ZERO : count 0 = {}.
Proof. apply set_ext; intros m; unfold_sets; lia. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "COUNT_SUC" *)
Theorem COUNT_SUC : forall n, count (SUC n) = n INSERT count n.
Proof. intros n; apply set_ext; intros m; unfold_sets; lia. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "COUNT_MONO" *)
Theorem COUNT_MONO : forall m n, m <= n -> (count m) SUBSET (count n).
Proof. intros m n h x; unfold_sets; lia. Qed.

(** ** Finite sets *)

(** Classical decisions used to build enumerations (Galette infrastructure). *)
Definition cdec {A} (x y : A) : {x = y} + {x <> y} := excluded_middle_informative (x = y).
Definition cmem {A} (s : A -> Prop) (x : A) : bool :=
  if excluded_middle_informative (x IN s) then true else false.

Lemma cmem_spec {A} (s : A -> Prop) x : cmem s x = true <-> x IN s.
Proof. unfold cmem; destruct (excluded_middle_informative _); split; congruence || tauto. Qed.

Lemma cmem_false {A} (s : A -> Prop) x : negb (cmem s x) = true <-> x NOTIN s.
Proof. rewrite negb_true_iff, <- not_true_iff_false, cmem_spec; reflexivity. Qed.

Section Finite.
Context {A : Type}.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "FINITE_EMPTY" *)
Theorem FINITE_EMPTY : FINITE (EMPTY : A -> Prop).
Proof. intros P [h _]; exact h. Qed.

Lemma FINITE_INSERT_imp (s : A -> Prop) x : FINITE s -> FINITE (x INSERT s).
Proof. intros hs P [h0 hS]; apply hS, hs; split; auto. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SIMPLE_FINITE_INDUCT" *)
Theorem SIMPLE_FINITE_INDUCT : forall P : (A -> Prop) -> Prop,
  P EMPTY /\ (forall s, P s -> (forall e, P (e INSERT s))) -> forall s, FINITE s -> P s.
Proof. intros P h s hs; apply hs, h. Qed.

(** Finiteness as covering by a list (Galette infrastructure). *)
Lemma FINITE_list (s : A -> Prop) : FINITE s <-> exists l, forall x, x IN s -> In x l.
Proof.
  split.
  - intros hs; apply (hs (fun s => exists l, forall x, x IN s -> In x l)); split.
    + exists []; intros x [].
    + intros u [l hl] e; exists (e :: l); intros x [->|hx]; [left; reflexivity|right; auto].
  - intros [l hl]; revert s hl; induction l as [|a l IH]; intros s hl.
    + replace s with (EMPTY : A -> Prop); [apply FINITE_EMPTY|].
      apply set_ext; intros x; split; [intros []|intros hx; destruct (hl x hx)].
    + assert (hd : FINITE (s DELETE a)).
      { apply IH; intros x [hx n]; destruct (hl x hx) as [<-|h]; [exfalso; apply n; left; reflexivity|exact h]. }
      destruct (classic (a IN s)) as [ha|ha].
      * rewrite <- (INSERT_DELETE a s ha); apply FINITE_INSERT_imp, hd.
      * rewrite <- (DELETE_NON_ELEMENT_RWT s a ha); exact hd.
Qed.

Lemma FINITE_enum (s : A -> Prop) : FINITE s -> exists l, NoDup l /\ forall x, x IN s <-> In x l.
Proof.
  intros h; apply FINITE_list in h as [l hl].
  exists (nodup cdec (filter (cmem s) l)); split; [apply NoDup_nodup|].
  intros x; rewrite nodup_In, filter_In, cmem_spec; firstorder.
Qed.

Lemma enum_FINITE (s : A -> Prop) l : (forall x, x IN s <-> In x l) -> FINITE s.
Proof. intros h; apply FINITE_list; exists l; apply h. Qed.

Lemma enum_length_eq (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 <-> In x l2) -> length l1 = length l2.
Proof.
  intros h1 h2 h; apply Nat.le_antisymm; apply NoDup_incl_length; auto; intros x; apply h.
Qed.

Lemma CARD_enum (s : A -> Prop) l :
  NoDup l -> (forall x, x IN s <-> In x l) -> CARD s = N.of_nat (length l).
Proof.
  intros hn hl; unfold CARD.
  destruct (select_spec (fun n => exists l, NoDup l /\ (forall x, x IN s <-> In x l) /\
    n = N.of_nat (length l))) as [l' (h1 & h2 & ->)]; [eauto|].
  f_equal; apply enum_length_eq; auto; intros x; rewrite <- h2, hl; reflexivity.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "FINITE_INDUCT" *)
Theorem FINITE_INDUCT : forall P : (A -> Prop) -> Prop,
  P {} /\ (forall s, FINITE s /\ P s -> (forall e, ~ (e IN s) -> P (e INSERT s))) ->
  forall s, FINITE s -> P s.
Proof.
  intros P [h0 hS] s hs; apply FINITE_list in hs as [l hl]; revert s hl.
  induction l as [|a l IH]; intros s hl.
  - replace s with (EMPTY : A -> Prop); [exact h0|].
    apply set_ext; intros x; split; [intros []|intros hx; destruct (hl x hx)].
  - assert (hl' : forall x, x IN (s DELETE a) -> In x l).
    { intros x [hx n]; destruct (hl x hx) as [<-|h]; [exfalso; apply n; left; reflexivity|exact h]. }
    destruct (classic (a IN s)) as [ha|ha].
    + rewrite <- (INSERT_DELETE a s ha); apply hS; [|apply ELT_IN_DELETE].
      split; [apply FINITE_list; eauto|apply IH, hl'].
    + rewrite <- (DELETE_NON_ELEMENT_RWT s a ha); apply IH, hl'.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "FINITE_INSERT" 3005 *)
Theorem FINITE_INSERT : forall (x : A) s, FINITE (x INSERT s) <-> FINITE s.
Proof.
  intros x s; split; [|apply FINITE_INSERT_imp].
  rewrite !FINITE_list; intros [l hl]; exists l; intros y hy; apply hl; right; exact hy.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_FINITE" *)
Theorem SUBSET_FINITE : forall s : A -> Prop, FINITE s -> (forall t, t SUBSET s -> FINITE t).
Proof. intros s hs t ht; rewrite FINITE_list in *; destruct hs as [l hl]; exists l; auto. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "SUBSET_FINITE_I" *)
Theorem SUBSET_FINITE_I : forall s t : A -> Prop, FINITE s /\ t SUBSET s -> FINITE t.
Proof. intros s t [h1 h2]; exact (SUBSET_FINITE s h1 t h2). Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "PSUBSET_FINITE" *)
Theorem PSUBSET_FINITE : forall s : A -> Prop, FINITE s -> (forall t, t PSUBSET s -> FINITE t).
Proof. intros s hs t [ht _]; exact (SUBSET_FINITE s hs t ht). Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "FINITE_DELETE" 3026 *)
Theorem FINITE_DELETE : forall (x : A) s, FINITE (s DELETE x) <-> FINITE s.
Proof.
  intros x s; split; [|intros h; apply (SUBSET_FINITE s h), DELETE_SUBSET].
  rewrite !FINITE_list; intros [l hl]; exists (x :: l); intros y hy.
  destruct (classic (y = x)) as [->|n]; [left; reflexivity|right; apply hl; split; auto].
  intros [e|[]]; exact (n e).
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "FINITE_UNION" 3079 *)
Theorem FINITE_UNION : forall s t : A -> Prop, FINITE (s UNION t) <-> FINITE s /\ FINITE t.
Proof.
  intros s t; split.
  - intros h; split; apply (SUBSET_FINITE _ h); apply SUBSET_UNION.
  - rewrite !FINITE_list; intros [[l1 h1] [l2 h2]]; exists (l1 ++ l2); intros x [hx|hx];
      apply in_or_app; auto.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INTER_FINITE" *)
Theorem INTER_FINITE : forall s : A -> Prop, FINITE s -> forall t, FINITE (s INTER t).
Proof. intros s hs t; apply (SUBSET_FINITE s hs); apply INTER_SUBSET. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "FINITE_DIFF" *)
Theorem FINITE_DIFF : forall s : A -> Prop, FINITE s -> forall t, FINITE (s DIFF t).
Proof. intros s hs t; apply (SUBSET_FINITE s hs); apply DIFF_SUBSET. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "FINITE_SING" *)
Theorem FINITE_SING : forall x : A, FINITE (x INSERT {}).
Proof. intros; apply FINITE_INSERT, FINITE_EMPTY. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IN_INFINITE_NOT_FINITE" *)
Theorem IN_INFINITE_NOT_FINITE : forall s t : A -> Prop,
  INFINITE s /\ FINITE t -> exists x : A, x IN s /\ ~ (x IN t).
Proof.
  intros s t [hs ht]; apply NNPP; intros hn; apply hs, (SUBSET_FINITE t ht).
  intros x hx; apply NNPP; intros n; apply hn; eauto.
Qed.


(** ** Cardinality *)

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "CARD_DEF" *)
Theorem CARD_DEF : (CARD (EMPTY : A -> Prop) = 0) /\
  (forall s : A -> Prop, FINITE s -> forall x, CARD (x INSERT s) =
     (if classical_dec (x IN s) then CARD s else SUC (CARD s))).
Proof.
  split.
  - rewrite (CARD_enum EMPTY []); [reflexivity|constructor|intros x; split; intros []].
  - intros s hs x; destruct (FINITE_enum s hs) as [l [hn hl]].
    destruct (classical_dec (x IN s)) as [hx|hx].
    + rewrite (ABSORPTION_RWT x s hx); reflexivity.
    + rewrite (CARD_enum s l hn hl), (CARD_enum (x INSERT s) (x :: l)).
      * cbn [length]; lia.
      * constructor; [rewrite <- hl; exact hx|exact hn].
      * intros y; rewrite IN_INSERT, hl; cbn; intuition congruence.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "CARD_EMPTY" *)
Theorem CARD_EMPTY : CARD (EMPTY : A -> Prop) = 0.
Proof. exact (proj1 CARD_DEF). Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "CARD_INSERT" *)
Theorem CARD_INSERT : forall s : A -> Prop, FINITE s -> forall x, CARD (x INSERT s) =
  (if classical_dec (x IN s) then CARD s else SUC (CARD s)).
Proof. exact (proj2 CARD_DEF). Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "CARD_EQ_0" *)
Theorem CARD_EQ_0 : forall s : A -> Prop, FINITE s -> ((CARD s = 0) <-> (s = EMPTY)).
Proof.
  intros s hs; destruct (FINITE_enum s hs) as [l [hn hl]]; rewrite (CARD_enum s l hn hl); split.
  - intros h; destruct l as [|a l]; [|cbn in h; lia].
    apply set_ext; intros x; specialize (hl x); unfold_sets; cbn in *; tauto.
  - intros ->; destruct l as [|a l]; [reflexivity|exfalso; apply (proj2 (hl a)); left; reflexivity].
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "CARD_SING" *)
Theorem CARD_SING : forall x : A, CARD (x INSERT {}) = 1.
Proof.
  intros x; rewrite CARD_INSERT by apply FINITE_EMPTY.
  destruct (classical_dec _) as [[]|_]; rewrite CARD_EMPTY; reflexivity.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "CARD_DELETE" *)
Theorem CARD_DELETE : forall s : A -> Prop, FINITE s ->
  forall x, CARD (s DELETE x) = (if classical_dec (x IN s) then CARD s - 1 else CARD s).
Proof.
  intros s hs x; destruct (classical_dec (x IN s)) as [hx|hx].
  - rewrite <- (INSERT_DELETE x s hx) at 2; rewrite CARD_INSERT by (apply FINITE_DELETE, hs).
    destruct (classical_dec _) as [h|_]; [exfalso; apply (ELT_IN_DELETE x s h)|lia].
  - rewrite (DELETE_NON_ELEMENT_RWT s x hx); reflexivity.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "CARD_SUBSET" *)
Theorem CARD_SUBSET : forall s : A -> Prop, FINITE s -> forall t, t SUBSET s -> CARD t <= CARD s.
Proof.
  intros s hs t ht; destruct (FINITE_enum s hs) as [ls [hn hl]].
  destruct (FINITE_enum t (SUBSET_FINITE s hs t ht)) as [lt [hn' hl']].
  rewrite (CARD_enum s ls hn hl), (CARD_enum t lt hn' hl').
  enough (length lt <= length ls)%nat by lia.
  apply NoDup_incl_length; [exact hn'|intros x hx; apply hl, ht, hl', hx].
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "CARD_PSUBSET" *)
Theorem CARD_PSUBSET : forall s : A -> Prop, FINITE s -> forall t, t PSUBSET s -> CARD t < CARD s.
Proof.
  intros s hs t [ht ne].
  assert (hy : exists y, y IN s /\ y NOTIN t).
  { apply NNPP; intros hn; apply ne, SUBSET_ANTISYM; split; [exact ht|].
    intros y hy; apply NNPP; intros n; apply hn; eauto. }
  destruct hy as [y [hys hyt]].
  destruct (FINITE_enum s hs) as [ls [hn hl]].
  destruct (FINITE_enum t (SUBSET_FINITE s hs t ht)) as [lt [hn' hl']].
  rewrite (CARD_enum s ls hn hl), (CARD_enum t lt hn' hl').
  enough (length (y :: lt) <= length ls)%nat by (cbn in *; lia).
  apply NoDup_incl_length; [constructor; [rewrite <- hl'; exact hyt|exact hn']|].
  intros x [<-|hx]; apply hl; [exact hys|apply ht, hl', hx].
Qed.

Lemma enum_filter (s t : A -> Prop) l :
  NoDup l -> (forall x, x IN s <-> In x l) ->
  NoDup (filter (cmem t) l) /\ (forall x, x IN (s INTER t) <-> In x (filter (cmem t) l)) /\
  NoDup (filter (fun x => negb (cmem t x)) l) /\
  (forall x, x IN (s DIFF t) <-> In x (filter (fun x => negb (cmem t x)) l)).
Proof.
  intros hn hl; split; [apply NoDup_filter, hn|split; [|split; [apply NoDup_filter, hn|]]];
    intros x; rewrite filter_In, <- hl; [rewrite cmem_spec|rewrite cmem_false]; reflexivity.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "CARD_INTER_LESS_EQ" *)
Theorem CARD_INTER_LESS_EQ : forall s : A -> Prop, FINITE s -> forall t, CARD (s INTER t) <= CARD s.
Proof. intros s hs t; apply CARD_SUBSET; [exact hs|apply INTER_SUBSET]. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "CARD_DIFF_EQN" *)
Theorem CARD_DIFF_EQN : forall (t s : A -> Prop), FINITE s ->
  (CARD (s DIFF t) = CARD s - CARD (s INTER t)).
Proof.
  intros t s hs; destruct (FINITE_enum s hs) as [ls [hn hl]].
  destruct (enum_filter s t ls hn hl) as (h1 & h2 & h3 & h4).
  rewrite (CARD_enum s ls hn hl), (CARD_enum _ _ h1 h2), (CARD_enum _ _ h3 h4).
  pose proof (filter_length (cmem t) ls); lia.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "CARD_DIFF" *)
Theorem CARD_DIFF : forall t : A -> Prop, FINITE t -> forall s : A -> Prop, FINITE s ->
  (CARD (s DIFF t) = (CARD s - CARD (s INTER t))).
Proof. intros t _ s hs; apply CARD_DIFF_EQN, hs. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "CARD_UNION" *)
Theorem CARD_UNION : forall s : A -> Prop, FINITE s -> forall t, FINITE t ->
  (CARD (s UNION t) + CARD (s INTER t) = CARD s + CARD t).
Proof.
  intros s hs t ht; destruct (FINITE_enum s hs) as [ls [hns hls]].
  destruct (FINITE_enum t ht) as [lt [hnt hlt]].
  destruct (enum_filter t s lt hnt hlt) as (h1 & h2 & h3 & h4).
  rewrite (CARD_enum s ls hns hls), (CARD_enum t lt hnt hlt).
  rewrite (CARD_enum (s INTER t) (filter (cmem s) lt)).
  2: exact h1.
  2: intros x; rewrite <- h2; unfold_sets; tauto.
  rewrite (CARD_enum (s UNION t) (ls ++ filter (fun x => negb (cmem s x)) lt)).
  - rewrite length_app; pose proof (filter_length (cmem s) lt); lia.
  - apply NoDup_app; [exact hns|exact h3|intros x hx hx'; apply h4 in hx'; apply hls in hx;
      destruct hx'; contradiction].
  - intros x; rewrite in_app_iff, <- h4, <- hls; unfold_sets; destruct (classic (s x)); tauto.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "CARD_UNION_EQN" *)
Theorem CARD_UNION_EQN : forall s t : A -> Prop, FINITE s /\ FINITE t ->
  (CARD (s UNION t) = CARD s + CARD t - CARD (s INTER t)).
Proof. intros s t [hs ht]; pose proof (CARD_UNION s hs t ht); lia. Qed.

End Finite.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "FINITE_BIGUNION" *)
Theorem FINITE_BIGUNION {A} : forall P : (A -> Prop) -> Prop,
  FINITE P /\ (forall s, s IN P -> FINITE s) -> FINITE (BIGUNION P).
Proof.
  intros P [hP hs]; apply FINITE_list in hP as [lP hlP]; apply FINITE_list.
  exists (flat_map (fun s => epsilon (inhabits []) (fun l => forall x, x IN s -> In x l)) lP).
  intros x [s [hsP hx]]; apply in_flat_map; exists s; split; [auto|].
  pose proof (epsilon_spec (inhabits []) (fun l => forall x, x IN s -> In x l)) as he.
  apply he; [apply (proj1 (FINITE_list s)), hs, hsP|exact hx].
Qed.

Section FiniteMaps.
Context {A B : Type}.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "IMAGE_FINITE" *)
Theorem IMAGE_FINITE : forall s : A -> Prop, FINITE s -> forall f : A -> B, FINITE (IMAGE f s).
Proof.
  intros s hs f; apply FINITE_list in hs as [l hl]; apply FINITE_list; exists (map f l).
  intros y [x [-> hx]]; apply in_map, hl, hx.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "FINITE_INJ" *)
Theorem FINITE_INJ : forall (f : A -> B) s t, INJ f s t /\ FINITE t -> FINITE s.
Proof.
  intros f s t [[hi1 hi2] ht]; destruct (classic (exists a, a IN s)) as [[a ha]|hn].
  - apply FINITE_list in ht as [l hl]; apply FINITE_list.
    exists (map (fun y => epsilon (inhabits a) (fun x => x IN s /\ f x = y)) l).
    intros x hx; apply in_map_iff; exists (f x); split; [|apply hl, hi1, hx].
    destruct (epsilon_spec (inhabits a) (fun z => z IN s /\ f z = f x)) as [h1 h2]; [eauto|].
    apply hi2; auto.
  - apply FINITE_list; exists []; intros x hx; apply hn; eauto.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "CARD_IMAGE_INJ" *)
Theorem CARD_IMAGE_INJ : forall (f : A -> B) s,
  (forall x y, x IN s /\ y IN s /\ (f x = f y) -> (x = y)) /\ FINITE s -> (CARD (IMAGE f s) = CARD s).
Proof.
  intros f s [hi hs]; destruct (FINITE_enum s hs) as [l [hn hl]].
  rewrite (CARD_enum s l hn hl), (CARD_enum (IMAGE f s) (map f l)), length_map; [reflexivity| |].
  - assert (hsub : forall x, In x l -> x IN s) by (intros x; apply hl).
    clear hl; induction hn as [|a l ha hn IH]; cbn; constructor.
    + rewrite in_map_iff; intros [x [e hx]]; apply ha.
      replace a with x; [exact hx|apply hi; split; [apply hsub; right; exact hx|split; [apply hsub; left; reflexivity|exact e]]].
    + apply IH; intros x hx; apply hsub; right; exact hx.
  - intros y; rewrite in_map_iff; split; [intros [x [-> hx]]; exists x; split; [reflexivity|apply hl, hx]|].
    intros [x [<- hx]]; exists x; split; [reflexivity|apply hl, hx].
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "CARD_INJ_IMAGE" *)
Theorem CARD_INJ_IMAGE : forall (f : A -> B) s,
  (forall x y, (f x = f y) <-> (x = y)) /\ FINITE s -> (CARD (IMAGE f s) = CARD s).
Proof. intros f s [h hs]; apply CARD_IMAGE_INJ; split; [intros x y (_ & _ & e); apply h, e|exact hs]. Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "CARD_IMAGE" *)
Theorem CARD_IMAGE : forall (f : A -> B) s, FINITE s -> (CARD (IMAGE f s) <= CARD s).
Proof.
  intros f s hs; destruct (FINITE_enum s hs) as [l [hn hl]].
  rewrite (CARD_enum s l hn hl), (CARD_enum (IMAGE f s) (nodup cdec (map f l))).
  - enough (length (nodup cdec (map f l)) <= length (map f l))%nat by (rewrite length_map in *; lia).
    apply NoDup_incl_length; [apply NoDup_nodup|intros y; apply nodup_In].
  - apply NoDup_nodup.
  - intros y; rewrite nodup_In, in_map_iff; split.
    + intros [x [-> hx]]; exists x; split; [reflexivity|apply hl, hx].
    + intros [x [<- hx]]; exists x; split; [reflexivity|apply hl, hx].
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INJ_CARD" *)
Theorem INJ_CARD : forall (f : A -> B) s t, INJ f s t /\ FINITE t -> CARD s <= CARD t.
Proof.
  intros f s t [hi ht]; pose proof (FINITE_INJ f s t (conj hi ht)) as hs.
  rewrite <- (CARD_IMAGE_INJ f s); [|split; [intros x y (hx & hy & e); apply hi; auto|exact hs]].
  apply CARD_SUBSET; [exact ht|apply (INJ_IMAGE_SUBSET f s t hi)].
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "FINITE_PREIMAGE" *)
Theorem FINITE_PREIMAGE : forall (f : A -> B) s,
  (forall x y, f x = f y <-> x = y) /\ FINITE s -> FINITE (PREIMAGE f s).
Proof.
  intros f s [hf hs]; apply (FINITE_INJ f (PREIMAGE f s) s); split; [|exact hs].
  split; [intros x hx; exact hx|intros x y _ e; apply hf, e].
Qed.

End FiniteMaps.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "FINITE_COUNT" *)
Theorem FINITE_COUNT : forall n, FINITE (count n).
Proof.
  intros n; induction n as [|n IH] using N.peano_ind.
  - rewrite COUNT_ZERO; apply FINITE_EMPTY.
  - rewrite COUNT_SUC; apply FINITE_INSERT, IH.
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "CARD_COUNT" *)
Theorem CARD_COUNT : forall n, CARD (count n) = n.
Proof.
  intros n; induction n as [|n IH] using N.peano_ind.
  - rewrite COUNT_ZERO; apply CARD_EMPTY.
  - rewrite COUNT_SUC, CARD_INSERT by apply FINITE_COUNT.
    destruct (classical_dec _) as [h|_]; [exfalso; unfold_sets; lia|rewrite IH; reflexivity].
Qed.

(*! HOL "HOL/src/pred_set/src/pred_setScript.sml" "INFINITE_NUM_UNIV" *)
Theorem INFINITE_NUM_UNIV : INFINITE (UNIV : num -> Prop).
Proof.
  intros h; apply FINITE_list in h as [l hl].
  assert (hm : forall y, In y l -> y <= fold_right N.max 0 l).
  { clear hl; induction l as [|a t IH]; cbn; [tauto|intros y [<-|h]; [lia|specialize (IH y h); lia]]. }
  specialize (hm _ (hl (N.succ (fold_right N.max 0 l)) Logic.I)); lia.
Qed.
