(** * HOL4 [set_sep]: separation logic over sets (partial)

    Partial port of [HOL/examples/machine-code/hoare-triple/set_sepScript.sml]:
    the definitions, and the [fun2set] theorems used by CakeML's target
    semantics and encoder proofs.  HOL's ['a set] is [A -> Prop]; a
    separation-logic assertion is a predicate on sets, [(A -> Prop) -> Prop].
    HOL's overload [p * q] for [STAR] is not introduced as a notation. *)

From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.combin Require Import combin.
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

Section StarThms.
Context {A : Type}.
Implicit Types p q r : (A -> Prop) -> Prop.

(** Galette-only: [STAR] without [SPLIT]. *)
Lemma STAR_alt p q s : STAR p q s <-> exists u, u SUBSET s /\ p u /\ q (s DIFF u).
Proof.
  unfold STAR; split.
  - intros (u & v & Hs & Hp & Hq). apply SPLIT_EQ in Hs as [Hu ->]. exists u; auto.
  - intros (u & Hu & Hp & Hq). exists u, (s DIFF u); split; [apply SPLIT_EQ; auto|auto].
Qed.

Lemma DIFF_DIFF_SUBSET (s u : A -> Prop) : u SUBSET s -> s DIFF (s DIFF u) = u.
Proof. sets_cl. Qed.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "STAR_COMM" *)
Theorem STAR_COMM : forall p q, STAR p q = STAR q p.
Proof.
  enough (H : forall p q s, STAR p q s -> STAR q p s).
  { intros p q; apply functional_extensionality; intros s; apply propositional_extensionality; split; apply H. }
  intros p q s H; apply STAR_alt in H as (u & Hu & Hp & Hq); apply STAR_alt.
  exists (s DIFF u); split; [sets|]. rewrite DIFF_DIFF_SUBSET by exact Hu. auto.
Qed.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "STAR_ASSOC" *)
Theorem STAR_ASSOC : forall p q r, STAR p (STAR q r) = STAR (STAR p q) r.
Proof.
  intros p q r; apply functional_extensionality; intros s; apply propositional_extensionality.
  rewrite !STAR_alt; split.
  - intros (u & Hu & Hp & Hqr). apply STAR_alt in Hqr as (w & Hw & Hq & Hr).
    exists (u UNION w); split; [sets|split].
    + apply STAR_alt; exists u; split; [sets|split; [exact Hp|]].
      replace ((u UNION w) DIFF u) with w by sets_cl. exact Hq.
    + replace (s DIFF (u UNION w)) with ((s DIFF u) DIFF w) by sets_cl. exact Hr.
  - intros (uw & Huw & Hpq & Hr). apply STAR_alt in Hpq as (u & Hu & Hp & Hq).
    exists u; split; [sets|split; [exact Hp|]].
    apply STAR_alt; exists (uw DIFF u); split; [sets|split; [exact Hq|]].
    replace ((s DIFF u) DIFF (uw DIFF u)) with (s DIFF uw) by sets_cl. exact Hr.
Qed.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "SEP_EXISTS_THM" *)
Theorem SEP_EXISTS_THM : forall {B} (p : B -> (A -> Prop) -> Prop) s,
  SEP_EXISTS (fun x => p x) s <-> exists x, p x s.
Proof. reflexivity. Qed.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "cond_STAR" *)
Theorem cond_STAR : forall (c : Prop) s p,
  (STAR (cond c) p s <-> c /\ p s) /\ (STAR p (cond c) s <-> c /\ p s).
Proof.
  intros c s p.
  assert (H : STAR (cond c) p s <-> c /\ p s).
  { rewrite STAR_alt; split.
    - intros (u & _ & [-> Hc] & Hp). split; [exact Hc|]. replace s with (s DIFF {}) by sets. exact Hp.
    - intros [Hc Hp]. exists {}; split; [sets|split; [split; [reflexivity|exact Hc]|]].
      replace (s DIFF {}) with s by sets. exact Hp. }
  split; [exact H|rewrite STAR_COMM; exact H].
Qed.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "one_STAR" *)
Theorem one_STAR : forall (x : A) s p, STAR (one x) p s <-> x IN s /\ p (s DELETE x).
Proof.
  intros x s p; rewrite STAR_alt; split.
  - intros (u & Hu & -> & Hp). split; [apply Hu; sets|].
    replace (s DELETE x) with (s DIFF (x INSERT {})) by sets. exact Hp.
  - intros [Hx Hp]. exists (x INSERT {}); split; [sets|split; [reflexivity|]].
    replace (s DIFF (x INSERT {})) with (s DELETE x) by sets. exact Hp.
Qed.

End StarThms.

Section Fun2setStar.
Context {A B : Type}.

Lemma fun2set_DELETE (f : B -> A) d a :
  fun2set (f, d) DELETE (a, f a) = fun2set (f, d DELETE a).
Proof.
  apply set_ext; intros [b y]. unfold pred_set.DELETE, pred_set.DIFF, pred_set.IN, pred_set.INSERT, pred_set.EMPTY.
  change (fun2set (f, d) (b, y)) with (fun2set (f, d) (b, y)).
  rewrite !fun2set_thm. unfold pred_set.DELETE, pred_set.DIFF, pred_set.IN, pred_set.INSERT, pred_set.EMPTY.
  split.
  - intros [[E Hb] Hn]. split; [exact E|split; [exact Hb|]]. intros [Eb|[]]; subst b; apply Hn; left; f_equal; congruence.
  - intros [E [Hb Hn]]. split; [split; assumption|]. intros [Ex|[]]. injection Ex as -> _. apply Hn; left; reflexivity.
Qed.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "one_fun2set" *)
Theorem one_fun2set : forall (d : B -> Prop) a (x : A) (p : (B * A -> Prop) -> Prop) f,
  STAR (one (a, x)) p (fun2set (f, d)) <-> f a = x /\ a IN d /\ p (fun2set (f, d DELETE a)).
Proof.
  intros d a x p f. rewrite one_STAR, IN_fun2set. split.
  - intros [[Hfa Ha] Hp]. subst x. rewrite fun2set_DELETE in Hp. auto.
  - intros (Hfa & Ha & Hp). subst x. split; [split; [reflexivity|exact Ha]|]. rewrite fun2set_DELETE; exact Hp.
Qed.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "write_fun2set" *)
Theorem write_fun2set `{EqDecision B} : forall (d : B -> Prop) (y : A) a (x : A) (p : (B * A -> Prop) -> Prop) f,
  STAR (one (a, x)) p (fun2set (f, d)) -> STAR p (one (a, y)) (fun2set ((a =+ y) f, d)).
Proof.
  intros d y a x p f Hs. rewrite STAR_COMM, one_fun2set. apply one_fun2set in Hs as (_ & Ha & Hp).
  split; [rewrite APPLY_UPDATE_THM; destruct (decide (a = a)); [reflexivity|congruence]|].
  split; [exact Ha|].
  replace (fun2set ((a =+ y) f, d DELETE a)) with (fun2set (f, d DELETE a)); [exact Hp|].
  apply fun2set_eq; intros b Hb. rewrite APPLY_UPDATE_THM.
  destruct (decide (a = b)) as [<-|]; [|reflexivity].
  exfalso; apply Hb; left; reflexivity.
Qed.

(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "fun2set_STAR_IMP" *)
Theorem fun2set_STAR_IMP : forall (p q : (B * A -> Prop) -> Prop) (f : B -> A) df,
  STAR p q (fun2set (f, df)) ->
  exists x y, p (fun2set (f, df DIFF y)) /\ q (fun2set (f, df DIFF x)).
Proof.
  intros p q f df H. apply STAR_alt in H as (u & Hu & Hp & Hq).
  set (du := fun a => u (a, f a)).
  exists du, (df DIFF du). split.
  - replace (fun2set (f, df DIFF (df DIFF du))) with u; [exact Hp|].
    apply set_ext; intros [b z]. rewrite fun2set_thm.
    unfold pred_set.DIFF, pred_set.IN, du. split.
    + intros Hb. pose proof (Hu _ Hb) as Hg. apply fun2set_thm in Hg as [<- Hd].
      split; [reflexivity|split; [exact Hd|intros [_ Hn]; exact (Hn Hb)]].
    + intros [<- [Hd Hn]]. destruct (classic (u (b, f b))) as [Hy|Hy]; [exact Hy|exfalso; exact (Hn (conj Hd Hy))].
  - replace (fun2set (f, df DIFF du)) with (fun2set (f, df) DIFF u); [exact Hq|].
    apply set_ext; intros [b z]. unfold pred_set.DIFF at 1, pred_set.IN at 1 2.
    rewrite !fun2set_thm. unfold pred_set.DIFF, pred_set.IN, du. split.
    + intros [[<- Hd] Hn]; split; [reflexivity|split; [exact Hd|exact Hn]].
    + intros [<- [Hd Hn]]; split; [split; [reflexivity|exact Hd]|exact Hn].
Qed.

End Fun2setStar.

Section SepClauses.
Context {A : Type}.

Lemma DIFF_EMPTY' (s : A -> Prop) : s DIFF {} = s. Proof. sets. Qed.

Ltac sep_ext := apply functional_extensionality; intros ?s; apply propositional_extensionality.

(** HOL's [p \/ q] on assertions is [SEP_DISJ p q]; HOL's [T]/[F] are [True]/[False].
    The quantified type of [SEP_EXISTS] is inhabited, as every HOL type. *)
(*! HOL "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "SEP_CLAUSES" *)
Theorem SEP_CLAUSES : forall {B} `{Inhabited B} (p : B -> (A -> Prop) -> Prop) (q t r : (A -> Prop) -> Prop)
    (c c' : Prop) (x : B),
  (STAR (SEP_EXISTS (fun v => p v)) q = SEP_EXISTS (fun v => STAR (p v) q)) /\
  (STAR q (SEP_EXISTS (fun v => p v)) = SEP_EXISTS (fun v => STAR q (p v))) /\
  (SEP_DISJ (SEP_EXISTS (fun v => p v)) q = SEP_EXISTS (fun v => SEP_DISJ (p v) q)) /\
  (SEP_DISJ q (SEP_EXISTS (fun v => p v)) = SEP_EXISTS (fun v => SEP_DISJ q (p v))) /\
  (SEP_EXISTS (fun v : B => q) = q) /\
  (SEP_EXISTS (fun v => STAR (p v) (cond (v = x))) = p x) /\
  (SEP_DISJ q SEP_F = q) /\ (SEP_DISJ SEP_F q = q) /\ (STAR SEP_F q = SEP_F) /\ (STAR q SEP_F = SEP_F) /\
  (SEP_DISJ r r = r) /\ (STAR q (SEP_DISJ r t) = SEP_DISJ (STAR q r) (STAR q t)) /\
  (STAR (SEP_DISJ r t) q = SEP_DISJ (STAR r q) (STAR t q)) /\
  (SEP_DISJ (@cond A c) (cond c') = cond (c \/ c')) /\ (STAR (@cond A c) (cond c') = cond (c /\ c')) /\
  (@cond A True = emp) /\ (@cond A False = SEP_F) /\ (STAR emp q = q) /\ (STAR q emp = q).
Proof.
  intros B HB p q t r c c' x.
  assert (Eemp : forall q0 : (A -> Prop) -> Prop, STAR emp q0 = q0).
  { intros q0; sep_ext. rewrite STAR_alt; split.
    - intros (u & _ & -> & Hq). rewrite DIFF_EMPTY' in Hq; exact Hq.
    - intros Hq. exists {}; split; [sets|split; [reflexivity|rewrite DIFF_EMPTY'; exact Hq]]. }
  assert (EF : forall q0 : (A -> Prop) -> Prop, STAR SEP_F q0 = SEP_F).
  { intros q0; sep_ext. rewrite STAR_alt; split; [intros (u & _ & [] & _)|intros []]. }
  assert (Ec : forall (d : Prop) (q0 : (A -> Prop) -> Prop) s0, STAR (cond d) q0 s0 <-> d /\ q0 s0)
    by (intros d q0 s0; exact (proj1 (cond_STAR d s0 q0))).
  repeat split.
  - sep_ext; rewrite STAR_alt; unfold SEP_EXISTS; split.
    + intros (u & Hu & [v Hp] & Hq). exists v; apply STAR_alt; exists u; auto.
    + intros [v Hs]; apply STAR_alt in Hs as (u & Hu & Hp & Hq). exists u; split; [exact Hu|split; [exists v; exact Hp|exact Hq]].
  - rewrite STAR_COMM; sep_ext; rewrite STAR_alt; unfold SEP_EXISTS; split.
    + intros (u & Hu & [v Hp] & Hq). exists v; rewrite STAR_COMM; apply STAR_alt; exists u; auto.
    + intros [v Hs]; rewrite STAR_COMM in Hs; apply STAR_alt in Hs as (u & Hu & Hp & Hq).
      exists u; split; [exact Hu|split; [exists v; exact Hp|exact Hq]].
  - sep_ext; unfold SEP_DISJ, SEP_EXISTS; split.
    + intros [[v Hp]|Hq]; [exists v; left; exact Hp|exists (@inhabitant B HB); right; exact Hq].
    + intros [v [Hp|Hq]]; [left; exists v; exact Hp|right; exact Hq].
  - sep_ext; unfold SEP_DISJ, SEP_EXISTS; split.
    + intros [Hq|[v Hp]]; [exists (@inhabitant B HB); left; exact Hq|exists v; right; exact Hp].
    + intros [v [Hq|Hp]]; [left; exact Hq|right; exists v; exact Hp].
  - sep_ext; unfold SEP_EXISTS; split; [intros [_ Hq]; exact Hq|intros Hq; exists (@inhabitant B HB); exact Hq].
  - sep_ext; unfold SEP_EXISTS; split.
    + intros [v Hs]. rewrite STAR_COMM, Ec in Hs. destruct Hs as [-> Hp]; exact Hp.
    + intros Hp. exists x. rewrite STAR_COMM, Ec. split; [reflexivity|exact Hp].
  - sep_ext; unfold SEP_DISJ, SEP_F; tauto.
  - sep_ext; unfold SEP_DISJ, SEP_F; tauto.
  - apply EF.
  - rewrite STAR_COMM; apply EF.
  - sep_ext; unfold SEP_DISJ; tauto.
  - sep_ext; unfold SEP_DISJ; rewrite !STAR_alt; split.
    + intros (u & Hu & Hq & [Hr|Ht]); [left|right]; exists u; auto.
    + intros [(u & Hu & Hq & Hr)|(u & Hu & Hq & Ht)]; exists u; auto.
  - sep_ext; unfold SEP_DISJ; rewrite !STAR_alt; split.
    + intros (u & Hu & [Hr|Ht] & Hq); [left|right]; exists u; auto.
    + intros [(u & Hu & Hr & Hq)|(u & Hu & Ht & Hq)]; exists u; auto.
  - sep_ext; unfold SEP_DISJ, cond; tauto.
  - sep_ext; rewrite Ec; unfold cond; tauto.
  - sep_ext; unfold cond, emp; tauto.
  - sep_ext; unfold cond, SEP_F; tauto.
  - apply Eemp.
  - rewrite STAR_COMM; apply Eemp.
Qed.

End SepClauses.
