(** * HOL4 [set_sep]: separation logic over sets (partial)

    Partial port of [HOL/examples/machine-code/hoare-triple/set_sepScript.sml]:
    the definitions, and the [fun2set] theorems used by CakeML's target
    semantics and encoder proofs.  HOL's ['a set] is [A -> Prop]; a
    separation-logic assertion is a predicate on sets, [(A -> Prop) -> Prop].
    HOL's overload [p * q] for [STAR] is not introduced as a notation. *)

From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
Open Scope N_scope.

Section Defs.
Context {A : Type}.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "one_def" *)
Definition one (x : A) : (A -> Prop) -> Prop := fun s => s = (x INSERT {}).

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "emp_def" *)
Definition emp : (A -> Prop) -> Prop := fun s => s = {}.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "cond_def" *)
Definition cond (c : Prop) : (A -> Prop) -> Prop := fun s => s = {} /\ c.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "SEP_F_def" *)
Definition SEP_F (s : A -> Prop) : Prop := False.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "SEP_T_def" *)
Definition SEP_T (s : A -> Prop) : Prop := True.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "SPLIT_def" *)
Definition SPLIT (s : A -> Prop) (uv : (A -> Prop) * (A -> Prop)) : Prop :=
  let '(u, v) := uv in (u UNION v = s) /\ DISJOINT u v.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "STAR_def" *)
Definition STAR (p q : (A -> Prop) -> Prop) : (A -> Prop) -> Prop :=
  fun s => exists u v, SPLIT s (u, v) /\ p u /\ q v.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "SEP_EQ_def" *)
Definition SEP_EQ (x : A -> Prop) : (A -> Prop) -> Prop := fun s => s = x.

(** HOL's binder [SEP_EXISTS x. p x] is [SEP_EXISTS (fun x => p x)]. *)
(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "SEP_EXISTS" *)
Definition SEP_EXISTS {B : Type} (f : B -> (A -> Prop) -> Prop) : (A -> Prop) -> Prop :=
  fun s => exists y, f y s.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "SEP_HIDE_def" *)
Definition SEP_HIDE {B : Type} (p : B -> (A -> Prop) -> Prop) : (A -> Prop) -> Prop :=
  SEP_EXISTS (fun x => p x).

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "SEP_DISJ_def" *)
Definition SEP_DISJ (p q : (A -> Prop) -> Prop) : (A -> Prop) -> Prop :=
  fun s => p s \/ q s.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "sidecond_def" *)
Definition sidecond : Prop -> (A -> Prop) -> Prop := cond.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "precond_def" *)
Definition precond : Prop -> (A -> Prop) -> Prop := cond.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "SEP_IMP_def" *)
Definition SEP_IMP (p q : (A -> Prop) -> Prop) : Prop := forall s, p s -> q s.

End Defs.

(** [fun2set (f, d)] is the graph of [f] restricted to [d]:
    HOL [{ (a, f a) | a IN d }]. *)
(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "fun2set_def" *)
Definition fun2set {A B : Type} (fd : (B -> A) * (B -> Prop)) : B * A -> Prop :=
  let '(f, d) := fd in fun x => exists a, x = (a, f a) /\ a IN d.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "SEP_ARRAY_def" *)
Fixpoint SEP_ARRAY {a : N} {B C : Type}
    (p : word a -> B -> (C -> Prop) -> Prop) (i : word a) (ad : word a) (l : list B)
    : (C -> Prop) -> Prop :=
  match l with
  | [] => emp
  | x :: xs => STAR (p ad x) (SEP_ARRAY p i (ad + i)%w xs)
  end.

Section Thms.
Context {A B : Type}.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "SPLIT_EQ" *)
Theorem SPLIT_EQ : forall (s u v : A -> Prop),
  SPLIT s (u, v) <-> (u SUBSET s) /\ (v = s DIFF u).
Proof.
  intros s u v; unfold SPLIT, pred_set.DISJOINT, pred_set.SUBSET, pred_set.DIFF, pred_set.UNION, pred_set.INTER, pred_set.IN, pred_set.EMPTY;
    split.
  - intros [Hu Hd]; subst s; split; [intros x Hx; left; exact Hx|].
    apply functional_extensionality; intros x; apply propositional_extensionality.
    split; [intros Hv; split; [right; exact Hv|]|intros [[Hx|Hx] Hn]; [contradiction|exact Hx]].
    intros Hx; assert (H : (fun x => u x /\ v x) x) by (split; assumption).
    rewrite Hd in H; exact H.
  - intros [Hu ->]; split.
    + apply functional_extensionality; intros x; apply propositional_extensionality.
      split; [intros [Hx|[Hx _]]; [apply Hu; exact Hx|exact Hx]|].
      intros Hx; destruct (classic (u x)); [left; assumption|right; split; assumption].
    + apply functional_extensionality; intros x; apply propositional_extensionality.
      split; [intros [Hx [_ Hn]]; contradiction|intros []].
Qed.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "fun2set_thm" *)
Theorem fun2set_thm : forall (f : B -> A) (d : B -> Prop) a x,
  fun2set (f, d) (a, x) <-> (f a = x) /\ a IN d.
Proof.
  intros f d a x; cbn; split.
  - intros [a' [He Hd]]; injection He as -> ->; split; [reflexivity|exact Hd].
  - intros [<- Hd]; exists a; split; [reflexivity|exact Hd].
Qed.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "IN_fun2set" *)
Theorem IN_fun2set : forall a (y : A) (h : B -> A) dh,
  (a, y) IN fun2set (h, dh) <-> (h a = y) /\ a IN dh.
Proof. intros; apply fun2set_thm. Qed.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "fun2set_eq" *)
Theorem fun2set_eq : forall (f g : B -> A) d,
  (fun2set (f, d) = fun2set (g, d)) <-> (forall a, a IN d -> f a = g a).
Proof.
  intros f g d; split.
  - intros H a Ha.
    assert (Hf : fun2set (f, d) (a, f a)) by (apply fun2set_thm; split; [reflexivity|exact Ha]).
    rewrite H in Hf; apply fun2set_thm in Hf; destruct Hf as [Hg _]; symmetry; exact Hg.
  - intros H; apply functional_extensionality; intros [a x];
      apply propositional_extensionality; rewrite !fun2set_thm; split;
      intros [Hx Ha]; (split; [|exact Ha]); rewrite <- Hx; [symmetry|]; apply H, Ha.
Qed.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "fun2set_DIFF" *)
Theorem fun2set_DIFF : forall (f : B -> A) x y,
  fun2set (f, x) DIFF fun2set (f, y) = fun2set (f, x DIFF y).
Proof.
  intros f x y; apply functional_extensionality; intros [a v];
    apply propositional_extensionality; unfold pred_set.DIFF at 1; unfold pred_set.IN at 1 2.
  rewrite !fun2set_thm; unfold pred_set.DIFF, pred_set.IN; tauto.
Qed.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "fun2set_EMPTY" *)
Theorem fun2set_EMPTY : forall (f : B -> A) df, (fun2set (f, df) = {}) <-> (df = {}).
Proof.
  intros f df; split; intros H.
  - apply functional_extensionality; intros a; apply propositional_extensionality;
      split; [|intros []].
    intros Ha; assert (Hf : fun2set (f, df) (a, f a)) by
      (apply fun2set_thm; split; [reflexivity|exact Ha]).
    rewrite H in Hf; exact Hf.
  - subst df; apply functional_extensionality; intros [a v];
      apply propositional_extensionality; rewrite fun2set_thm; split;
      [intros [_ []]|intros []].
Qed.

End Thms.
