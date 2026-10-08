(** * HOL4 [state_transformer]: the state monad (partial)

    Partial port of [HOL/src/monad/more_monads/state_transformerScript.sml]:
    [UNIT], [BIND] and the [FOR] loop combinator (used by the L3 machine
    models).  HOL's local type abbreviation [('a, 'state) M] is
    ['state -> 'a # 'state].

    [FOR] is defined in HOL by well-founded recursion on the distance
    [|j - i|]; here it is a [nat]-fuelled iteration with that distance as
    fuel, and HOL's equation is the theorem [FOR_def]. *)

From Galette Require Import Base.
From Galette.HOL.src.combin Require Import combin.
Open Scope N_scope.

Section M.
Context {S : Type}.

(*! HOL "HOL/src/monad/more_monads/state_transformerScript.sml" "UNIT_DEF" *)
Definition UNIT {B : Type} (x : B) : S -> B * S := fun s => (x, s).

(*! HOL "HOL/src/monad/more_monads/state_transformerScript.sml" "BIND_DEF" *)
Definition BIND {B C : Type} (g : S -> B * S) (f : B -> S -> C * S) : S -> C * S :=
  fun s => let '(x, s') := g s in f x s'.

(** The loop body, with the next index computed as in HOL. *)
Definition FOR_next (i j : N) : N := if i <? j then i + 1 else i - 1.

Fixpoint FOR_fuel (fuel : nat) (i j : N) (a : N -> S -> unit * S) : S -> unit * S :=
  match fuel with
  | O => a i
  | Datatypes.S f =>
      if bool_decide (i = j) then a i
      else BIND (a i) (fun _ => FOR_fuel f (FOR_next i j) j a)
  end.

Definition FOR_dist (i j : N) : N := if i <? j then j - i else i - j.

(** HOL [FOR (i, j, a)]: run [a i], [a (i +/- 1)], ..., [a j]. *)
Definition FOR (x : N * N * (N -> S -> unit * S)) : S -> unit * S :=
  let '(i, j, a) := x in FOR_fuel (N.to_nat (FOR_dist i j)) i j a.

Lemma FOR_fuel_eq f i j a :
  N.to_nat (FOR_dist i j) = f -> FOR_fuel f i j a = FOR (i, j, a).
Proof. intros <-; reflexivity. Qed.

(*! HOL "HOL/src/monad/more_monads/state_transformerScript.sml" "FOR_def" *)
Theorem FOR_def : forall i j a,
  FOR (i, j, a) =
  if bool_decide (i = j) then a i
  else BIND (a i) (fun u => FOR (if i <? j then i + 1 else i - 1, j, a)).
Proof.
  intros i j a; fold (FOR_next i j); unfold FOR.
  destruct (bool_decide (i = j)) eqn:E.
  - apply bool_decide_spec in E; subst; unfold FOR_dist.
    rewrite N.ltb_irrefl, N.sub_diag; reflexivity.
  - assert (Hd : N.to_nat (FOR_dist i j) = Datatypes.S (N.to_nat (FOR_dist (FOR_next i j) j))).
    { assert (i <> j) by (intro H; subst; rewrite (proj2 (bool_decide_spec _)) in E;
        [discriminate|reflexivity]).
      unfold FOR_dist, FOR_next.
      destruct (N.ltb_spec i j); destruct (N.ltb_spec (i + 1) j);
        destruct (N.ltb_spec (i - 1) j); lia. }
    rewrite Hd; cbn [FOR_fuel]; rewrite E; reflexivity.
Qed.

End M.
