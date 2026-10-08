(** * HOL4 [arithmetic]: natural-number arithmetic

    HOL [num] is Rocq's binary [N] (HOL numerals are binary too), so concrete
    numbers such as [dimword(:64)] stay small in the kernel, and extraction
    maps [N] to arbitrary-precision integers.  Every Galette file starts with
    [Open Scope N_scope] so numerals and [+], [*], [-] (truncated), [<], [<=]
    are HOL's.  HOL recursion on [SUC n] is expressed with [N.peano_rect]
    (or recursion on another argument) and HOL's equations are proved. *)

From Galette Require Import Base.
From Stdlib Require Export NArith.
Open Scope N_scope.

Abbreviation num := N (only parsing).
Abbreviation SUC := N.succ (only parsing).
Abbreviation PRE := N.pred (only parsing).

(** HOL defines [DIV]/[MOD] HOL-Light style ([DIV_def]/[MOD_def] via
    [OT_DIV]/[OT_MOD]): [m DIV 0 = 0], [m MOD 0 = m].  These are exactly
    [N.div]/[N.modulo]; the defining equations are not tagged because they
    mention the auxiliary [OT_] specification constants. *)
Notation "m 'DIV' n" := (N.div m n) (at level 40, left associativity) : N_scope.
Notation "m 'MOD' n" := (N.modulo m n) (at level 40, left associativity) : N_scope.
Notation "m ** n" := (N.pow m n) (at level 30, right associativity) : N_scope.

Lemma DIV_0 m : m DIV 0 = 0.
Proof. destruct m; reflexivity. Qed.
Lemma MOD_0 m : m MOD 0 = m.
Proof. destruct m; reflexivity. Qed.

(*! HOL "HOL/src/num/theories/arithmeticScript.sml" "EXP" *)
Lemma EXP : forall m n, m ** 0 = 1 /\ m ** SUC n = m * m ** n.
Proof. split; [reflexivity|apply N.pow_succ_r'] . Qed.

(*! HOL "HOL/src/num/theories/arithmeticScript.sml" "MAX_DEF" *)
Definition MAX (m n : N) : N := if m <? n then n else m.

(*! HOL "HOL/src/num/theories/arithmeticScript.sml" "MIN_DEF" *)
Definition MIN (m n : N) : N := if m <? n then m else n.

(** HOL [EVEN]/[ODD] are defined by recursion on [SUC]; they are computed
    as [N.even]/[N.odd] and HOL's equations are the tagged theorems. *)
Abbreviation EVEN := N.even.
Abbreviation ODD := N.odd.

(*! HOL "HOL/src/num/theories/arithmeticScript.sml" "EVEN" *)
Theorem EVEN_thm : forall n, EVEN 0 = true /\ EVEN (SUC n) = negb (EVEN n).
Proof. intros n; split; [reflexivity|]. rewrite N.even_succ, <- N.negb_even; reflexivity. Qed.

(*! HOL "HOL/src/num/theories/arithmeticScript.sml" "ODD" *)
Theorem ODD_thm : forall n, ODD 0 = false /\ ODD (SUC n) = negb (ODD n).
Proof. intros n; split; [reflexivity|]. rewrite N.odd_succ, <- N.negb_odd; reflexivity. Qed.

(*! HOL "HOL/src/num/theories/arithmeticScript.sml" "DIVISION" *)
Theorem DIVISION : forall n, 0 < n -> forall k, k = k DIV n * n + k MOD n /\ k MOD n < n.
Proof.
  intros n Hn k; split.
  - rewrite N.mul_comm; apply N.div_mod; lia.
  - apply N.mod_lt; lia.
Qed.

Lemma MAX_max m n : MAX m n = N.max m n.
Proof. unfold MAX; destruct (N.ltb_spec m n); lia. Qed.

Lemma MIN_min m n : MIN m n = N.min m n.
Proof. unfold MIN; destruct (N.ltb_spec m n); lia. Qed.

(** Primitive recursion on HOL [num]: [num_rec z s 0 = z],
    [num_rec z s (SUC n) = s n (num_rec z s n)]. *)
Definition num_rec {A : Type} (z : A) (s : N -> A -> A) (n : N) : A :=
  N.peano_rect (fun _ => A) z s n.

Lemma num_rec_0 {A} (z : A) s : num_rec z s 0 = z.
Proof. reflexivity. Qed.

Lemma num_rec_SUC {A} (z : A) s n : num_rec z s (SUC n) = s n (num_rec z s n).
Proof. unfold num_rec; exact (N.peano_rect_succ (fun _ => A) z s n). Qed.
