(** * HOL4 [list]: lists

    HOL lists are Rocq lists.  Where a HOL list function coincides with a
    Rocq standard-library function (same arguments in the same order, same
    value everywhere), the HOL name is an abbreviation of it, so Rocq's
    library lemmas apply and terms print with the HOL name.  Otherwise the HOL
    definition is ported as is; partial HOL functions ([HD], [LAST]) return
    [ARB] outside their HOL domain. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.

(** ** Functions that coincide with the Rocq standard library *)

Abbreviation APPEND := List.app.
Abbreviation LENGTH := List.length.
Abbreviation MAP := List.map.
Abbreviation FILTER := List.filter.
Abbreviation FLAT := List.concat.
Abbreviation REVERSE := List.rev.

(*! HOL "HOL/src/list/src/listScript.sml" "APPEND" 156 *)
Theorem APPEND_thm : forall {A}, (forall l : list A, APPEND [] l = l) /\
  (forall (l1 l2 : list A) h, APPEND (h :: l1) l2 = h :: APPEND l1 l2).
Proof. split; reflexivity. Qed.

(*! HOL "HOL/src/list/src/listScript.sml" "LENGTH" *)
Theorem LENGTH_thm : forall {A} (h : A) t, LENGTH (@nil A) = 0 /\ LENGTH (h :: t) = SUC (LENGTH t).
Proof. split; reflexivity. Qed.

(*! HOL "HOL/src/list/src/listScript.sml" "MAP" *)
Theorem MAP_thm : forall {A B} (f : A -> B) h t, MAP f (@nil A) = [] /\ MAP f (h :: t) = f h :: MAP f t.
Proof. split; reflexivity. Qed.

(*! HOL "HOL/src/list/src/listScript.sml" "FILTER" *)
Theorem FILTER_thm : forall {A} (P : A -> bool) h t,
  FILTER P [] = [] /\ FILTER P (h :: t) = if P h then h :: FILTER P t else FILTER P t.
Proof. split; reflexivity. Qed.

(*! HOL "HOL/src/list/src/listScript.sml" "FLAT" *)
Theorem FLAT_thm : forall {A} (h : list A) t, FLAT (@nil (list A)) = [] /\ FLAT (h :: t) = APPEND h (FLAT t).
Proof. split; reflexivity. Qed.

(*! HOL "HOL/src/list/src/listScript.sml" "REVERSE_DEF" *)
Theorem REVERSE_DEF : forall {A} (h : A) t,
  REVERSE (@nil A) = [] /\ REVERSE (h :: t) = REVERSE t ++ [h].
Proof. split; reflexivity. Qed.

(** ** Ported definitions *)

Section Defs.
Context {A B C : Type}.

(*! HOL "HOL/src/list/src/listScript.sml" "NULL_DEF" *)
Definition NULL (l : list A) : bool := match l with [] => true | _ :: _ => false end.

(*! HOL "HOL/src/list/src/listScript.sml" "HD" *)
Definition HD `{Inhabited A} (l : list A) : A := match l with h :: t => h | [] => ARB end.

(*! HOL "HOL/src/list/src/listScript.sml" "TL_DEF" *)
Definition TL (l : list A) : list A := match l with [] => [] | h :: t => t end.

(*! HOL "HOL/src/list/src/listScript.sml" "EL_def" *)
Fixpoint EL `{Inhabited A} (n : nat) (l : list A) : A :=
  match n with 0 => HD l | S n => EL n (TL l) end.

(*! HOL "HOL/src/list/src/listScript.sml" "SUM" *)
Fixpoint SUM (l : list nat) : nat := match l with [] => 0 | h :: t => h + SUM t end.

(*! HOL "HOL/src/list/src/listScript.sml" "FOLDR" *)
Fixpoint FOLDR (f : A -> B -> B) (e : B) (l : list A) : B :=
  match l with [] => e | x :: l => f x (FOLDR f e l) end.

(*! HOL "HOL/src/list/src/listScript.sml" "FOLDL" *)
Fixpoint FOLDL (f : B -> A -> B) (e : B) (l : list A) : B :=
  match l with [] => e | x :: l => FOLDL f (f e x) l end.

(*! HOL "HOL/src/list/src/listScript.sml" "EVERY_DEF" *)
Fixpoint EVERY (P : A -> bool) (l : list A) : bool :=
  match l with [] => true | h :: t => P h && EVERY P t end.

(*! HOL "HOL/src/list/src/listScript.sml" "EXISTS_DEF" *)
Fixpoint EXISTS (P : A -> bool) (l : list A) : bool :=
  match l with [] => false | h :: t => P h || EXISTS P t end.

(** HOL [MEM x l] abbreviates [x IN LIST_TO_SET l]; its characterising
    theorem [MEM] is the definition here. *)
(*! HOL "HOL/src/list/src/listScript.sml" "MEM" 1264 *)
Fixpoint MEM `{EqDecision A} (x : A) (l : list A) : bool :=
  match l with [] => false | h :: t => bool_decide (x = h) || MEM x t end.

(*! HOL "HOL/src/list/src/listScript.sml" "ALL_DISTINCT" *)
Fixpoint ALL_DISTINCT `{EqDecision A} (l : list A) : bool :=
  match l with [] => true | h :: t => negb (MEM h t) && ALL_DISTINCT t end.

(*! HOL "HOL/src/list/src/listScript.sml" "MAP2_DEF" *)
Fixpoint MAP2 (f : A -> B -> C) (l1 : list A) (l2 : list B) : list C :=
  match l1, l2 with
  | h1 :: t1, h2 :: t2 => f h1 h2 :: MAP2 f t1 t2
  | _, _ => []
  end.

(** HOL [ZIP] takes a pair and truncates to the shorter list
    ([new_specification] [ZIP_def]). *)
(*! HOL "HOL/src/list/src/listScript.sml" "ZIP_def" *)
Definition ZIP (p : list A * list B) : list (A * B) :=
  let (l1, l2) := p in
  (fix ZIP_c (l1 : list A) (l2 : list B) : list (A * B) :=
     match l1, l2 with
     | x1 :: l1, x2 :: l2 => (x1, x2) :: ZIP_c l1 l2
     | _, _ => []
     end) l1 l2.

(*! HOL "HOL/src/list/src/listScript.sml" "UNZIP" *)
Fixpoint UNZIP (l : list (A * B)) : list A * list B :=
  match l with
  | [] => ([], [])
  | x :: l => (fst x :: fst (UNZIP l), snd x :: snd (UNZIP l))
  end.

(*! HOL "HOL/src/list/src/listScript.sml" "SNOC" *)
Fixpoint SNOC (x : A) (l : list A) : list A :=
  match l with [] => [x] | x' :: l => x' :: SNOC x l end.

(*! HOL "HOL/src/list/src/listScript.sml" "GENLIST" *)
Fixpoint GENLIST (f : nat -> A) (n : nat) : list A :=
  match n with 0 => [] | S n => SNOC (f n) (GENLIST f n) end.

(*! HOL "HOL/src/list/src/listScript.sml" "LAST_DEF" *)
Fixpoint LAST `{Inhabited A} (l : list A) : A :=
  match l with
  | [] => ARB
  | h :: t => match t with [] => h | _ :: _ => LAST t end
  end.

(*! HOL "HOL/src/list/src/listScript.sml" "FRONT_DEF" *)
Fixpoint FRONT (l : list A) : list A :=
  match l with
  | [] => []
  | h :: t => match t with [] => [] | _ :: _ => h :: FRONT t end
  end.

(*! HOL "HOL/src/list/src/listScript.sml" "TAKE_def" *)
Fixpoint TAKE (n : nat) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => if n =? 0 then [] else x :: TAKE (n - 1) xs
  end.

(*! HOL "HOL/src/list/src/listScript.sml" "DROP_def" *)
Fixpoint DROP (n : nat) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => if n =? 0 then x :: xs else DROP (n - 1) xs
  end.

(*! HOL "HOL/src/list/src/listScript.sml" "LUPDATE_def" *)
Fixpoint LUPDATE (e : A) (n : nat) (l : list A) : list A :=
  match l, n with
  | [], _ => []
  | x :: l, 0 => e :: l
  | x :: l, S n => x :: LUPDATE e n l
  end.

(*! HOL "HOL/src/list/src/listScript.sml" "INDEX_FIND_def" *)
Fixpoint INDEX_FIND (i : nat) (P : A -> bool) (l : list A) : option (nat * A) :=
  match l with
  | [] => None
  | h :: t => if P h then Some (i, h) else INDEX_FIND (SUC i) P t
  end.

(*! HOL "HOL/src/list/src/listScript.sml" "FIND_def" *)
Definition FIND (P : A -> bool) : list A -> option A :=
  option_map snd ∘ INDEX_FIND 0 P.

(*! HOL "HOL/src/list/src/listScript.sml" "INDEX_OF_def" *)
Definition INDEX_OF `{EqDecision A} (x : A) : list A -> option nat :=
  option_map fst ∘ INDEX_FIND 0 (fun y => bool_decide (x = y)).

(*! HOL "HOL/src/list/src/listScript.sml" "isPREFIX" *)
Fixpoint isPREFIX `{EqDecision A} (l1 l2 : list A) : bool :=
  match l1 with
  | [] => true
  | h :: t => match l2 with [] => false | h' :: t' => bool_decide (h = h') && isPREFIX t t' end
  end.

(** [LIST_REL] relates lists elementwise; it is a [Prop] (its relation
    argument is arbitrary). *)
(*! HOL "HOL/src/list/src/listScript.sml" "LIST_REL" *)
Inductive LIST_REL (R : A -> B -> Prop) : list A -> list B -> Prop :=
| LIST_REL_nil : LIST_REL R [] []
| LIST_REL_cons a b l1 l2 : R a b -> LIST_REL R l1 l2 -> LIST_REL R (a :: l1) (b :: l2).

End Defs.

Lemma ZIP_eqns {A B} : (forall l2 : list B, ZIP ([] : list A, l2) = []) /\
  (forall l1 : list A, ZIP (l1, [] : list B) = []) /\
  (forall (x1 : A) l1 (x2 : B) l2, ZIP (x1 :: l1, x2 :: l2) = (x1, x2) :: ZIP (l1, l2)).
Proof. repeat split; intros; try reflexivity; destruct l1; reflexivity. Qed.

(** HOL [list_size]: the size function generated for [list] (used in
    termination arguments). *)
Fixpoint list_size {A} (f : A -> nat) (l : list A) : nat :=
  match l with [] => 0 | x :: xs => 1 + f x + list_size f xs end.

(*! HOL "HOL/src/list/src/listScript.sml" "LIST_REL_def" 1456 *)
Theorem LIST_REL_def : forall {A B} (R : A -> B -> Prop) a b as_ bs,
  (LIST_REL R [] [] <-> True) /\
  (LIST_REL R (a :: as_) [] <-> False) /\
  (LIST_REL R [] (b :: bs) <-> False) /\
  (LIST_REL R (a :: as_) (b :: bs) <-> R a b /\ LIST_REL R as_ bs).
Proof.
  intros; split; [|split; [|split]].
  - split; [constructor|constructor].
  - split; [inversion 1|tauto].
  - split; [inversion 1|tauto].
  - split; [inversion 1; auto|intros [? ?]; constructor; auto].
Qed.

(*! HOL "HOL/src/list/src/listScript.sml" "EL" 231 *)
Theorem EL_thm : forall {A} `{Inhabited A},
  (forall l : list A, EL 0 l = HD l) /\ (forall (l : list A) n, EL (SUC n) l = EL n (TL l)).
Proof. split; reflexivity. Qed.

(*! HOL "HOL/src/list/src/listScript.sml" "MAP2" *)
Theorem MAP2_thm : forall {A B C},
  (forall f : A -> B -> C, MAP2 f [] [] = []) /\
  (forall (f : A -> B -> C) h1 t1 h2 t2, MAP2 f (h1 :: t1) (h2 :: t2) = f h1 h2 :: MAP2 f t1 t2).
Proof. split; reflexivity. Qed.

(** ** Bridges to the standard library (Galette infrastructure) *)

Lemma MEM_In {A} `{EqDecision A} (x : A) l : MEM x l = true <-> In x l.
Proof.
  induction l as [|h t IH]; cbn; [split; [discriminate|tauto]|].
  rewrite orb_true_iff, IH, bool_decide_spec; split; intros [Hx|Hx]; auto.
Qed.

Lemma EVERY_Forall {A} (P : A -> bool) l : EVERY P l = true <-> Forall (fun x => P x = true) l.
Proof.
  induction l as [|h t IH]; cbn; [split; constructor|].
  rewrite andb_true_iff, IH; split; [intros [? ?]; constructor; auto|intros Hf; inversion Hf; auto].
Qed.

Lemma EL_nth {A} `{Inhabited A} n (l : list A) : n < length l -> EL n l = nth n l ARB.
Proof.
  revert l; induction n as [|n IH]; intros [|h t] Hl; cbn in *; try lia; auto.
  apply IH; lia.
Qed.

Lemma TAKE_firstn {A} n (l : list A) : TAKE n l = firstn n l.
Proof.
  revert n; induction l as [|x xs IH]; intros [|n]; cbn; auto.
  rewrite IH, Nat.sub_0_r; reflexivity.
Qed.

Lemma DROP_skipn {A} n (l : list A) : DROP n l = skipn n l.
Proof.
  revert n; induction l as [|x xs IH]; intros [|n]; cbn; auto using skipn_nil.
  rewrite IH, Nat.sub_0_r; reflexivity.
Qed.

Lemma FOLDL_fold_left {A B} (f : B -> A -> B) e l : FOLDL f e l = fold_left f l e.
Proof. revert e; induction l; cbn; auto. Qed.

Lemma FOLDR_fold_right {A B} (f : A -> B -> B) e l : FOLDR f e l = fold_right f e l.
Proof. induction l; cbn; congruence. Qed.

Lemma SNOC_app {A} (x : A) l : SNOC x l = l ++ [x].
Proof. induction l; cbn; congruence. Qed.
