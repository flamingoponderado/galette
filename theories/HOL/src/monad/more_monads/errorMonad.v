(** * HOL4 [errorMonad]: the error (exception) monad

    Port of [HOL/src/monad/more_monads/errorMonadScript.sml].

    Names: HOL's type [error] has a constructor of the same name, so the
    Rocq type is [error_ty] (AGENTS.md, type/constructor clashes).  HOL's
    constructor [return] is a Rocq keyword and is named [return_]; [try] is
    an Ltac keyword and is named [try_].  Clients that also use
    [errorLogMonad] (whose [return]/[error] are functions) [Require] this
    module without importing it and write [errorMonad.return_] etc.

    Not ported: the [monadsyntax] declaration. *)

From Galette Require Import Base.
Open Scope N_scope.

(*! HOL "HOL/src/monad/more_monads/errorMonadScript.sml" "error" *)
Inductive error_ty (A E : Type) : Type :=
| return_ : A -> error_ty A E
| error : E -> error_ty A E.
Arguments return_ {A E} _.
Arguments error {A E} _.

#[global] Instance error_ty_eq_dec {A E} `{EqDecision A} `{EqDecision E} :
  EqDecision (error_ty A E).
Proof.
  intros [a|b] [c|d]; try (right; discriminate).
  - destruct (decide (a = c)) as [->|n]; [left; reflexivity|right; congruence].
  - destruct (decide (b = d)) as [->|n]; [left; reflexivity|right; congruence].
Defined.

(*! HOL "HOL/src/monad/more_monads/errorMonadScript.sml" "EXISTS_ERROR" *)
Theorem EXISTS_ERROR : forall {A E} (P : error_ty A E -> Prop),
  (exists e : error_ty A E, P e) <-> (exists a, P (return_ a)) \/ (exists e, P (error e)).
Proof.
  intros A E P; split.
  - intros [[a|e] H]; [left|right]; eauto.
  - intros [[a H]|[e H]]; eauto.
Qed.

(*! HOL "HOL/src/monad/more_monads/errorMonadScript.sml" "FORALL_ERROR" *)
Theorem FORALL_ERROR : forall {A E} (P : error_ty A E -> Prop),
  (forall e : error_ty A E, P e) <-> (forall a, P (return_ a)) /\ (forall e, P (error e)).
Proof. intros A E P; split; [auto|intros [H1 H2] [a|e]; auto]. Qed.

(*! HOL "HOL/src/monad/more_monads/errorMonadScript.sml" "bind_def" *)
Definition bind {A B E} (m : error_ty A E) (f : A -> error_ty B E) : error_ty B E :=
  match m with
  | return_ v => f v
  | error e => error e
  end.

(*! HOL "HOL/src/monad/more_monads/errorMonadScript.sml" "try_def" *)
Definition try_ {A E} (m : error_ty A E) (f : E -> error_ty A E) : error_ty A E :=
  match m with
  | return_ v => return_ v
  | error e => f e
  end.

(*! HOL "HOL/src/monad/more_monads/errorMonadScript.sml" "choice_def" *)
Definition choice {A E} (m1 m : error_ty A E) : error_ty A E :=
  match m1 with
  | return_ v => return_ v
  | error e => m
  end.

(*! HOL "HOL/src/monad/more_monads/errorMonadScript.sml" "guard_def" *)
Definition guard {E} (e : E) (b : bool) : error_ty unit E :=
  if b then return_ tt else error e.

(*! HOL "HOL/src/monad/more_monads/errorMonadScript.sml" "bind_return" *)
Theorem bind_return : forall {A E} (m : error_ty A E), bind m return_ = m.
Proof. intros A E [a|e]; reflexivity. Qed.

(*! HOL "HOL/src/monad/more_monads/errorMonadScript.sml" "bind_EQ_return" *)
Theorem bind_EQ_return : forall {A B E} (m : error_ty A E) (f : A -> error_ty B E) v,
  bind m f = return_ v <-> exists u, m = return_ u /\ f u = return_ v.
Proof.
  intros A B E [a|e] f v; cbn; split.
  - eauto.
  - intros [u [H1 H2]]; injection H1 as ->; exact H2.
  - discriminate.
  - intros [u [H1 H2]]; discriminate.
Qed.

(*! HOL "HOL/src/monad/more_monads/errorMonadScript.sml" "bind_EQ_error" *)
Theorem bind_EQ_error : forall {A B E} (m : error_ty A E) (f : A -> error_ty B E) e,
  bind m f = error e <-> m = error e \/ exists u, m = return_ u /\ f u = error e.
Proof.
  intros A B E [a|e'] f e; cbn; split.
  - eauto.
  - intros [H|[u [H1 H2]]]; [discriminate|injection H1 as ->; exact H2].
  - intros H; left; injection H as ->; reflexivity.
  - intros [H|[u [H1 H2]]]; [injection H as ->; reflexivity|discriminate].
Qed.
