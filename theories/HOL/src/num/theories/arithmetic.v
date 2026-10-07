(** * HOL4 [arithmetic]: natural-number arithmetic

    HOL [num] is Rocq [nat] (extracted to arbitrary-precision integers, see
    extraction/).  [SUC], [+], [*], [-] (truncated), [<], [<=] coincide with
    Rocq's; HOL's names are provided as notations so ported statements read as
    in HOL. *)

From Galette Require Import Base.

Abbreviation num := nat (only parsing).
Abbreviation SUC := S (only parsing).
Abbreviation PRE := Nat.pred (only parsing).

(** HOL defines [DIV]/[MOD] HOL-Light style ([DIV_def]/[MOD_def] via
    [OT_DIV]/[OT_MOD]): [m DIV 0 = 0], [m MOD 0 = m].  These are exactly
    [Nat.div]/[Nat.modulo]; the defining equations are not tagged because they
    mention the auxiliary [OT_] specification constants. *)
Notation "m 'DIV' n" := (Nat.div m n) (at level 40, left associativity) : nat_scope.
Notation "m 'MOD' n" := (Nat.modulo m n) (at level 40, left associativity) : nat_scope.
Notation "m ** n" := (Nat.pow m n) (at level 30, right associativity) : nat_scope.

(*! HOL "HOL/src/num/theories/arithmeticScript.sml" "EXP" *)
Lemma EXP : forall m n, m ** 0 = 1 /\ m ** S n = m * m ** n.
Proof. split; reflexivity. Qed.

(*! HOL "HOL/src/num/theories/arithmeticScript.sml" "MAX_DEF" *)
Definition MAX (m n : nat) : nat := if m <? n then n else m.

(*! HOL "HOL/src/num/theories/arithmeticScript.sml" "MIN_DEF" *)
Definition MIN (m n : nat) : nat := if m <? n then m else n.

(*! HOL "HOL/src/num/theories/arithmeticScript.sml" "EVEN" *)
Fixpoint EVEN (n : nat) : bool :=
  match n with 0 => true | S n => negb (EVEN n) end.

(*! HOL "HOL/src/num/theories/arithmeticScript.sml" "ODD" *)
Fixpoint ODD (n : nat) : bool :=
  match n with 0 => false | S n => negb (ODD n) end.

(*! HOL "HOL/src/num/theories/arithmeticScript.sml" "DIVISION" *)
Theorem DIVISION : forall n, 0 < n -> forall k, k = k DIV n * n + k MOD n /\ k MOD n < n.
Proof.
  intros n Hn k; split.
  - rewrite Nat.mul_comm; apply Nat.div_mod; lia.
  - apply Nat.mod_upper_bound; lia.
Qed.

Lemma MAX_max m n : MAX m n = Nat.max m n.
Proof. unfold MAX; destruct (Nat.ltb_spec m n); lia. Qed.

Lemma MIN_min m n : MIN m n = Nat.min m n.
Proof. unfold MIN; destruct (Nat.ltb_spec m n); lia. Qed.
