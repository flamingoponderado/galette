(** * HOL4 [llist]: possibly infinite lists

    HOL represents ['a llist] by functions [num -> 'a option] satisfying
    [lrep_ok] (once a position is [NONE], every later one is), and so does
    Galette: [llist A] is that subtype.  Equality is therefore extensional,
    as in HOL (a coinductive Rocq type would only give bisimilarity).

    HOL defines [lrep_ok] coinductively; [lrep_ok_alt] proves it equal to the
    pointwise condition used as the definition here.  Only the part of the
    theory used by CakeML's semantics is ported. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option.
Open Scope N_scope.

Definition lrep_ok {A} (f : N -> option A) : Prop :=
  forall n, IS_SOME (f (SUC n)) = true -> IS_SOME (f n) = true.

Record llist (A : Type) : Type := llist_abs_ok {
  llist_rep : N -> option A;
  llist_rep_ok : lrep_ok llist_rep
}.
Arguments llist_abs_ok {A} _ _.
Arguments llist_rep {A} _ _.
Arguments llist_rep_ok {A} _ _ _.

Lemma llist_ext {A} (l1 l2 : llist A) :
  (forall n, llist_rep l1 n = llist_rep l2 n) -> l1 = l2.
Proof.
  destruct l1 as [f1 H1], l2 as [f2 H2]; cbn; intros E.
  assert (f1 = f2) as -> by (apply functional_extensionality; exact E).
  f_equal; apply proof_irrelevance.
Qed.

#[global] Instance llist_inhabited {A} : Inhabited (llist A).
Proof. refine (llist_abs_ok (fun _ => None) _); intros n H; discriminate. Defined.

Section Defs.
Context {A : Type}.

Lemma lrep_ok_nil : lrep_ok (fun _ : N => @None A).
Proof. intros n H; discriminate. Qed.

Definition cons_rep (h : A) (t : N -> option A) : N -> option A :=
  fun n => if n =? 0 then SOME h else t (n - 1).

Lemma lrep_ok_cons (h : A) (t : N -> option A) : lrep_ok t -> lrep_ok (cons_rep h t).
Proof.
  intros Ht n; unfold cons_rep.
  destruct (N.eqb_spec (SUC n) 0); [lia|].
  destruct (N.eqb_spec n 0) as [->|Hn]; [reflexivity|].
  replace (SUC n - 1) with (SUC (n - 1)) by lia. apply Ht.
Qed.

Lemma lrep_ok_shift (t : N -> option A) : lrep_ok t -> lrep_ok (fun n : N => t (n + 1)).
Proof. intros Ht n; replace (SUC n + 1) with (SUC (n + 1)) by lia; apply Ht. Qed.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LNIL" *)
Definition LNIL : llist A := llist_abs_ok (fun _ => None) lrep_ok_nil.

Definition LCONS (h : A) (t : llist A) : llist A :=
  llist_abs_ok (cons_rep h (llist_rep t)) (lrep_ok_cons h _ (llist_rep_ok t)).

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LHD" *)
Definition LHD (ll : llist A) : option A := llist_rep ll 0.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LTL" *)
Definition LTL (ll : llist A) : option (llist A) :=
  match LHD ll with
  | None => None
  | Some _ => Some (llist_abs_ok (fun n => llist_rep ll (n + 1))
                                 (lrep_ok_shift _ (llist_rep_ok ll)))
  end.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "fromList_def" *)
Fixpoint fromList (l : list A) : llist A :=
  match l with [] => LNIL | h :: t => LCONS h (fromList t) end.

(** HOL [LNTH]: recursion on [SUC n] via [num_rec]; [LNTH] (the HOL
    equations) is proved below. *)
Definition LNTH (n : N) : llist A -> option A :=
  num_rec LHD (fun _ r ll => OPTION_BIND (LTL ll) r) n.

(** HOL [LTAKE]. *)
Definition LTAKE (n : N) : llist A -> option (list A) :=
  num_rec (fun _ => SOME [])
    (fun _ r ll => match LHD ll with
                   | None => None
                   | Some hd => match r (THE (LTL ll)) with
                                | None => None
                                | Some tl => Some (hd :: tl)
                                end
                   end) n.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LFINITE_rules" *)
Inductive LFINITE : llist A -> Prop :=
| LFINITE_nil : LFINITE LNIL
| LFINITE_cons h t : LFINITE t -> LFINITE (LCONS h t).

(*! HOL "HOL/src/coalgebras/llistScript.sml" "llength_rel_rules" *)
Inductive llength_rel : llist A -> N -> Prop :=
| llength_rel_nil : llength_rel LNIL 0
| llength_rel_cons h n t : llength_rel t n -> llength_rel (LCONS h t) (SUC n).

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LLENGTH" *)
Definition LLENGTH (ll : llist A) : option N :=
  if classical_dec (LFINITE ll) then SOME (select (fun n => llength_rel ll n)) else NONE.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "toList" *)
Definition toList `{Inhabited A} (ll : llist A) : option (list A) :=
  if classical_dec (LFINITE ll) then LTAKE (THE (LLENGTH ll)) ll else NONE.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LPREFIX_def" *)
Definition LPREFIX `{EqDecision A} `{Inhabited A} (l1 l2 : llist A) : Prop :=
  match toList l1 with
  | None => l1 = l2
  | Some xs =>
      match toList l2 with
      | None => LTAKE (LENGTH xs) l2 = SOME xs
      | Some ys => isPREFIX xs ys = true
      end
  end.

(** HOL [LUNFOLD f z]: position [n] is the second component of the [n]-th
    iterate of [f] (stopping at the first [NONE]). *)
Definition lunfold_rep {B} (f : B -> option (B * A)) (z : B) (n : N) : option A :=
  OPTION_MAP snd (num_rec (f z) (fun _ m => OPTION_BIND m (fun p => f (fst p))) n).

Lemma lrep_ok_lunfold {B} (f : B -> option (B * A)) z : lrep_ok (lunfold_rep f z).
Proof.
  intros n; unfold lunfold_rep; rewrite num_rec_SUC.
  destruct (num_rec _ _ n); [reflexivity|discriminate].
Qed.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LUNFOLD_def" *)
Definition LUNFOLD {B} (f : B -> option (B * A)) (z : B) : llist A :=
  llist_abs_ok (lunfold_rep f z) (lrep_ok_lunfold f z).

End Defs.

(** ** Characterising theorems *)

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LHD_THM" *)
Theorem LHD_THM : forall {A},
  LHD (@LNIL A) = NONE /\ (forall (h : A) t, LHD (LCONS h t) = SOME h).
Proof. split; reflexivity. Qed.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LTL_THM" *)
Theorem LTL_THM : forall {A},
  LTL (@LNIL A) = NONE /\ (forall (h : A) t, LTL (LCONS h t) = SOME t).
Proof.
  intros A; split; [reflexivity|]; intros h t; unfold LTL, LHD; cbn.
  f_equal; apply llist_ext; intros n; cbn; unfold cons_rep.
  destruct (N.eqb_spec (n + 1) 0); [lia|]; f_equal; lia.
Qed.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "llist_CASES" *)
Theorem llist_CASES : forall {A} (l : llist A), l = LNIL \/ exists h t, l = LCONS h t.
Proof.
  intros A l; destruct (llist_rep l 0) as [h|] eqn:E0.
  - right; exists h, (llist_abs_ok (fun n => llist_rep l (n + 1))
                                    (lrep_ok_shift _ (llist_rep_ok l))).
    apply llist_ext; intros n; cbn; unfold cons_rep.
    destruct (N.eqb_spec n 0) as [->|Hn]; [exact E0|]; f_equal; lia.
  - left; apply llist_ext; intros n; cbn.
    induction n as [|n IH] using N.peano_ind; [exact E0|].
    destruct (llist_rep l (SUC n)) eqn:E; [|reflexivity].
    pose proof (llist_rep_ok l n) as Hok; rewrite E, IH in Hok; discriminate (Hok eq_refl).
Qed.
