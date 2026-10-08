(** * HOL4 [list]: further list functions used by the compiler backend

    Part of the [listScript] counterpart, kept apart from [list.v]:
    [oEL], [PAD_LEFT], [PAD_RIGHT], [splitAtPki], [dropWhile], [OPT_MMAP]. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option.
Open Scope N_scope.

Section Extra.
Context {A : Type}.

(*! HOL "HOL/src/list/src/listScript.sml" "oEL_def" *)
Fixpoint oEL (n : N) (l : list A) : option A :=
  match l with
  | [] => None
  | x :: xs => if n =? 0 then Some x else oEL (n - 1) xs
  end.

(*! HOL "HOL/src/list/src/listScript.sml" "PAD_LEFT" *)
Definition PAD_LEFT (c : A) (n : N) (s : list A) : list A :=
  GENLIST (K c) (n - LENGTH s) ++ s.

(*! HOL "HOL/src/list/src/listScript.sml" "PAD_RIGHT" *)
Definition PAD_RIGHT (c : A) (n : N) (s : list A) : list A :=
  s ++ GENLIST (K c) (n - LENGTH s).

(** HOL [splitAtPki P k l]: split [l] before the first element [h] at index
    [i] with [P i h], and continue with [k]. *)
(*! HOL "HOL/src/list/src/listScript.sml" "splitAtPki_def" *)
Fixpoint splitAtPki {B} (P : N -> A -> bool) (k : list A -> list A -> B) (l : list A) : B :=
  match l with
  | [] => k [] []
  | h :: t =>
      if P 0 h then k [] (h :: t)
      else splitAtPki (fun i => P (SUC i)) (fun p s => k (h :: p) s) t
  end.

End Extra.

(*! HOL "HOL/src/list/src/listScript.sml" "oEL_THM" *)
Theorem oEL_THM : forall {A} `{Inhabited A} (xs : list A) n,
  oEL n xs = if n <? LENGTH xs then Some (EL n xs) else None.
Proof.
  intros A HA xs; induction xs as [|x xs IH]; intros n; [destruct n; reflexivity|].
  cbn [oEL LENGTH]; destruct (N.eqb_spec n 0) as [->|Hn].
  { destruct (N.ltb_spec 0 (SUC (LENGTH xs))); [reflexivity|lia]. }
  rewrite IH.
  remember (n - 1) as m eqn:Hm; replace n with (SUC m) by lia.
  rewrite EL_SUC; cbn [TL].
  destruct (N.ltb_spec m (LENGTH xs)), (N.ltb_spec (SUC m) (SUC (LENGTH xs)));
    try reflexivity; lia.
Qed.

(*! HOL "HOL/src/list/src/listScript.sml" "dropWhile_def" *)
Fixpoint dropWhile {A} (P : A -> bool) (l : list A) : list A :=
  match l with [] => [] | h :: t => if P h then dropWhile P t else h :: t end.

(*! HOL "HOL/src/list/src/listScript.sml" "OPT_MMAP_def" *)
Fixpoint OPT_MMAP {A B} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | [] => SOME []
  | h0 :: t0 => OPTION_BIND (f h0) (fun h => OPTION_BIND (OPT_MMAP f t0) (fun t => SOME (h :: t)))
  end.
