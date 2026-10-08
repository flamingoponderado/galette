(** * HOL4 [errorLogMonad]: the error monad with a log of messages

    Port of [HOL/src/monad/more_monads/errorLogMonadScript.sml].

    [M A E W] is HOL's [('a,'e,'w) M = ('a,'e) error # 'w list] (result
    ['a], error ['e], log messages ['w]).  HOL's [return] is a Rocq keyword
    and is named [return_] (as the [errorMonad] constructor); HOL's overload
    [emret] (for [errorMonad$return]) is [errorMonad.return_].

    HOL's [(I ## APPEND ms1) p] (pair map) is written out as
    [let '(r, ms2) := p in (I r, APPEND ms1 ms2)], and [(I ## K []) M] as
    [let '(r, ms) := m in (I r, K [] ms)].

    HOL's [do ... od] notation for this monad ([monadsyntax] [errorLog]) is
    provided as the Rocq notations of [errorLog_scope]: [x <- m ;; k] is
    [bind m (fun x => k)], ['p <- m ;; k] binds a pattern, and [m ;; k] is
    [bind m (fun _ => k)] (the monad declares no [ignorebind]). *)

From Galette Require Import Base.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.monad.more_monads Require errorMonad.
Open Scope N_scope.

Abbreviation emret := errorMonad.return_.

(*! HOL "HOL/src/monad/more_monads/errorLogMonadScript.sml" "M" *)
Definition M (A E W : Type) : Type := errorMonad.error_ty A E * list W.

(*! HOL "HOL/src/monad/more_monads/errorLogMonadScript.sml" "M_CASES" *)
Theorem M_CASES : forall {A E W} (m : M A E W),
  (exists v ms, m = (emret v, ms)) \/ (exists e ms, m = (errorMonad.error e, ms)).
Proof. intros A E W [[v|e] ms]; [left|right]; eauto. Qed.

(*! HOL "HOL/src/monad/more_monads/errorLogMonadScript.sml" "return_def" *)
Definition return_ {A E W} (v : A) : M A E W := (emret v, []).

(*! HOL "HOL/src/monad/more_monads/errorLogMonadScript.sml" "log_def" *)
Definition log {E L} (m : L) : M unit E L := (emret tt, [m]).

(*! HOL "HOL/src/monad/more_monads/errorLogMonadScript.sml" "error_def" *)
Definition error {A E L} (e : E) : M A E L := (errorMonad.error e, []).

(*! HOL "HOL/src/monad/more_monads/errorLogMonadScript.sml" "bind_def" *)
Definition bind {A B E L} (m : M A E L) (f : A -> M B E L) : M B E L :=
  match m with
  | (errorMonad.return_ u, ms1) => let '(r, ms2) := f u in (I r, APPEND ms1 ms2)
  | (errorMonad.error e, ms1) => (errorMonad.error e, ms1)
  end.

(*! HOL "HOL/src/monad/more_monads/errorLogMonadScript.sml" "bind_IDL" *)
Theorem bind_IDL : forall {A B E W} (v : A) (f : A -> M B E W), bind (return_ v) f = f v.
Proof. intros; unfold bind, return_; destruct (f v); reflexivity. Qed.

(*! HOL "HOL/src/monad/more_monads/errorLogMonadScript.sml" "bind_IDR" *)
Theorem bind_IDR : forall {A E L} (m : M A E L), bind m return_ = m.
Proof. intros A E L [[v|e] ms]; cbn; [rewrite app_nil_r|]; reflexivity. Qed.

(*! HOL "HOL/src/monad/more_monads/errorLogMonadScript.sml" "bind_EQ_success" *)
Theorem bind_EQ_success : forall {A B E L} (m : M A E L) (f : A -> M B E L) v ms,
  bind m f = (emret v, ms) <->
  exists u ms0 ms1, m = (emret u, ms0) /\ f u = (emret v, ms1) /\ ms = ms0 ++ ms1.
Proof.
  intros A B E L [[u|e] ms0] f v ms; cbn.
  - destruct (f u) as [r ms2] eqn:Hf; split.
    + unfold I; intros H; injection H as -> <-; exists u, ms0, ms2; auto.
    + intros (u' & ms0' & ms1 & H1 & H2 & ->); injection H1 as -> ->.
      rewrite Hf in H2; injection H2 as -> ->; reflexivity.
  - split; [discriminate|]; intros (u' & ms0' & ms1 & H1 & _); discriminate.
Qed.

(*! HOL "HOL/src/monad/more_monads/errorLogMonadScript.sml" "silently_def" *)
Definition silently {X Y Z} (m : X * Y) : X * list Z :=
  let '(r, ms) := m in (I r, K [] ms).

(*! HOL "HOL/src/monad/more_monads/errorLogMonadScript.sml" "choice_def" *)
Definition choice {A E1 E2 L} (m1 : M A E1 L) (m2 : M A E2 L) : M A E2 L :=
  match m1 with
  | (errorMonad.return_ v, ms1) => (emret v, ms1)
  | (errorMonad.error e, ms1) => let '(r, ms2) := m2 in (I r, APPEND ms1 ms2)
  end.

(*! HOL "HOL/src/monad/more_monads/errorLogMonadScript.sml" "choice_return" *)
Theorem choice_return : forall {A E1 E2 L} (v : A) (m : M A E2 L),
  choice (return_ v : M A E1 L) m = return_ v.
Proof. reflexivity. Qed.

Declare Scope errorLog_scope.
Delimit Scope errorLog_scope with errorLog.
Notation "x <- m ;; k" := (bind m (fun x => k))
  (at level 61, m at next level, right associativity) : errorLog_scope.
Notation "' p <- m ;; k" := (bind m (fun x => match x with p => k end))
  (at level 61, p pattern, m at next level, right associativity) : errorLog_scope.
Notation "m ;; k" := (bind m (fun _ => k))
  (at level 61, right associativity) : errorLog_scope.
