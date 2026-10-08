(** * CakeML [ml_monadBase]: the state-and-exception monad

    The definitions of the monad supported by CakeML's monadic translator:
    [('a, 'b, 'c) M = 'a -> ('b, 'c) exc # 'a] (state ['a], result ['b],
    exception ['c]), its bind/return/[otherwise], and the list-backed
    arrays and references ([Msub], [Mupdate], [Marray_*], [Mref], ...).
    Arrays are HOL lists: [Msub]/[Mupdate] walk the list (linear time), and
    fail with the given exception when the index is out of bounds, exactly as
    in HOL.  The theorems of the script are not ported yet.

    HOL's [do ... od] notation for this monad (declared [st_ex] in the
    script) is provided as the Rocq notations of [monad_scope]:
    [x <- m ;; k] is [st_ex_bind m (fun x => k)], ['p <- m ;; k] binds a
    pattern, and [m ;; k] is [st_ex_ignore_bind m k] (HOL's [do m; k od]).

    [array_resize] recurses on [SUC n]; it uses [num_rec] and HOL's equation
    is the tagged [array_resize_def]. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.combin Require Import combin.
Open Scope N_scope.

(** HOL's type variables: ['a] the success type, ['b] the exception type. *)
(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "exc" *)
Inductive exc (A B : Type) : Type :=
| M_success : A -> exc A B
| M_failure : B -> exc A B.
Arguments M_success {A B} _.
Arguments M_failure {A B} _.

#[global] Instance exc_eq_dec {A B} `{EqDecision A} `{EqDecision B} : EqDecision (exc A B).
Proof.
  intros [a|b] [c|d]; try (right; discriminate).
  - destruct (decide (a = c)) as [->|n]; [left; reflexivity|right; congruence].
  - destruct (decide (b = d)) as [->|n]; [left; reflexivity|right; congruence].
Defined.

(** [M S A E] is HOL's [('a, 'b, 'c) M] with ['a = S], ['b = A], ['c = E]. *)
(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "M" *)
Definition M (S A E : Type) : Type := S -> exc A E * S.

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "liftM_def" *)
Definition liftM {A D B C} (read : D -> A) (write : (A -> A) -> D -> D) (op : M A B C)
    : M D B C :=
  fun state => let '(ret, new) := op (read state) in (ret, write (K new) state).

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "st_ex_bind_def" *)
Definition st_ex_bind {S A B E} (x : M S A E) (f : A -> M S B E) : M S B E :=
  fun s =>
    match x s with
    | (M_success y, s) => f y s
    | (M_failure x, s) => (M_failure x, s)
    end.

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "st_ex_ignore_bind_def" *)
Definition st_ex_ignore_bind {S A B E} (x : M S A E) (f : M S B E) : M S B E :=
  fun s =>
    match x s with
    | (M_success y, s) => f s
    | (M_failure x, s) => (M_failure x, s)
    end.

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "st_ex_return_def" *)
Definition st_ex_return {S A E} (x : A) : M S A E := fun s => (M_success x, s).

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "otherwise_def" *)
Definition otherwise {S A E} (x y : M S A E) : M S A E :=
  fun s =>
    match x s with
    | (M_success y, s) => (M_success y, s)
    | (M_failure e, s) => y s
    end.

Declare Scope monad_scope.
Notation "x <- m ;; k" := (st_ex_bind m (fun x => k))
  (at level 61, m at next level, right associativity) : monad_scope.
Notation "' p <- m ;; k" := (st_ex_bind m (fun x => match x with p => k end))
  (at level 61, p pattern, m at next level, right associativity) : monad_scope.
Notation "m ;; k" := (st_ex_ignore_bind m k)
  (at level 61, right associativity) : monad_scope.
Open Scope monad_scope.

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "can_def" *)
Definition can {S A B E} (f : A -> M S B E) (x : A) : M S bool E :=
  otherwise (f x ;; st_ex_return true) (st_ex_return false).

(** Dynamic allocation of references. *)
(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "store_ref" *)
Inductive store_ref : Type := StoreRef : N -> store_ref.

(** ** Arrays *)

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Msub_def" *)
Fixpoint Msub {A E} (e : E) (n : N) (l : list A) : exc A E :=
  match l with
  | [] => M_failure e
  | x :: l' => if n =? 0 then M_success x else Msub e (n - 1) l'
  end.

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mupdate_def" *)
Fixpoint Mupdate {A E} (e : E) (x : A) (n : N) (l : list A) : exc (list A) E :=
  match l with
  | [] => M_failure e
  | x' :: l' =>
      if n =? 0 then M_success (x :: l')
      else
        match Mupdate e x (n - 1) l' with
        | M_success l'' => M_success (x' :: l'')
        | other => other
        end
  end.

(** HOL [array_resize] (see [array_resize_def]). *)
Definition array_resize {A} (n : N) (x : A) (a : list A) : list A :=
  num_rec (fun _ => []) (fun _ r a => match a with [] => x :: r a | x' :: a' => x' :: r a' end) n a.

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "array_resize_def" *)
Theorem array_resize_def : forall {A} (n : N) (x : A) a,
  array_resize n x a =
  if n =? 0 then []
  else match a with
       | [] => x :: array_resize (n - 1) x a
       | x' :: a' => x' :: array_resize (n - 1) x a'
       end.
Proof.
  intros A n x a; destruct (N.eqb_spec n 0) as [->|Hn]; [reflexivity|].
  unfold array_resize at 1; rewrite <- (N.succ_pred n Hn) at 1.
  rewrite num_rec_SUC, N.sub_1_r; reflexivity.
Qed.

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Marray_length_def" *)
Definition Marray_length {S A E} (get_arr : S -> list A) : M S N E :=
  fun s => (M_success (LENGTH (get_arr s)), s).

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Marray_sub_def" *)
Definition Marray_sub {S A E} (get_arr : S -> list A) (e : E) (n : N) : M S A E :=
  fun s => (Msub e n (get_arr s), s).

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Marray_update_def" *)
Definition Marray_update {S A E} (get_arr : S -> list A) (set_arr : list A -> S -> S)
    (e : E) (n : N) (x : A) : M S unit E :=
  fun s =>
    match Mupdate e x n (get_arr s) with
    | M_success a => (M_success tt, set_arr a s)
    | M_failure e => (M_failure e, s)
    end.

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Marray_alloc_def" *)
Definition Marray_alloc {S A E} (set_arr : list A -> S -> S) (n : N) (x : A) : M S unit E :=
  fun s => (M_success tt, set_arr (REPLICATE n x) s).

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Marray_resize_def" *)
Definition Marray_resize {S A E} (get_arr : S -> list A) (set_arr : list A -> S -> S)
    (n : N) (x : A) : M S unit E :=
  fun s => (M_success tt, set_arr (array_resize n x (get_arr s)) s).

(** ** Dynamically allocated references *)

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mref_def" *)
Definition Mref {S A E} (cons : A -> S) (x : A) : M (list S) store_ref E :=
  fun s => (M_success (StoreRef (LENGTH s)), cons x :: s).

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "dref_def" *)
Definition dref {S} `{Inhabited S} (n : N) : list S -> S :=
  fun s => EL (LENGTH s - n - 1) s.

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mdref_aux_def" *)
Fixpoint Mdref_aux {S E} (e : E) (n : N) (s : list S) : exc S E :=
  match s with
  | [] => M_failure e
  | x :: s => if n =? 0 then M_success x else Mdref_aux e (n - 1) s
  end.

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mdref_def" *)
Definition Mdref {S E} (e : E) (r : store_ref) : M (list S) S E :=
  match r with StoreRef n => fun s => (Mdref_aux e (LENGTH s - n - 1) s, s) end.

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mpop_ref_def" *)
Definition Mpop_ref {S A E} (e : E) : exc A E * list S -> exc A E * list S :=
  fun '(r, s) =>
    match s with
    | x :: s => (r, s)
    | [] => (M_failure e, s)
    end.

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mref_assign_aux_def" *)
Fixpoint Mref_assign_aux {S E} (e : E) (n : N) (x : S) (s : list S) : exc (list S) E :=
  match s with
  | x' :: s =>
      if n =? 0 then M_success (x :: s)
      else
        match Mref_assign_aux e (n - 1) x s with
        | M_success s => M_success (x' :: s)
        | other => other
        end
  | [] => M_failure e
  end.

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mref_assign_def" *)
Definition Mref_assign {S E} (e : E) (r : store_ref) (x : S) : M (list S) unit E :=
  match r with
  | StoreRef n =>
      fun s =>
        match Mref_assign_aux e (LENGTH s - n - 1) x s with
        | M_success s => (M_success tt, s)
        | M_failure e => (M_failure e, s)
        end
  end.

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "ref_assign_def" *)
Definition ref_assign {S} (n : N) (x : S) : list S -> list S :=
  fun s => LUPDATE x (LENGTH s - n - 1) s.

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "ref_bind_def" *)
Definition ref_bind {S A B E} (create : M S A E) (f : A -> M S B E)
    (pop : exc B E * S -> exc B E * S) : M S B E :=
  fun s =>
    match create s with
    | (M_success x, s) => pop (f x s)
    | (M_failure x, s) => (M_failure x, s)
    end.

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mget_ref_def" *)
Definition Mget_ref {S A E} (get_var : S -> A) : M S A E := fun s => (M_success (get_var s), s).

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mset_ref_def" *)
Definition Mset_ref {S A E} (set_var : A -> S -> S) (x : A) : M S unit E :=
  fun s => (M_success tt, set_var x s).

(** ** Run *)

(*! HOL "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "run_def" *)
Definition run {S A E} (x : M S A E) (state : S) : exc A E := fst (x state).
