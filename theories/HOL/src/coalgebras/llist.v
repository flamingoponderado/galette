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

(** ** Representation lemmas (Galette infrastructure) *)

Section RepLemmas.
Context {A : Type}.

Lemma lrep_ok_none (f : N -> option A) : lrep_ok f ->
  forall k m, f k = None -> k <= m -> f m = None.
Proof.
  intros Hok k m Hk Hle.
  induction m as [|m IH] using N.peano_ind.
  - assert (k = 0) as -> by lia; exact Hk.
  - destruct (N.eq_dec k (SUC m)) as [->|Hne]; [exact Hk|].
    destruct (f (SUC m)) eqn:E; [|reflexivity].
    specialize (Hok m); rewrite E in Hok; cbn in Hok.
    rewrite IH in Hok by lia. discriminate (Hok eq_refl).
Qed.

Lemma LNTH_rep n : forall (ll : llist A), LNTH n ll = llist_rep ll n.
Proof.
  induction n as [|n IH] using N.peano_ind; intros ll; [reflexivity|].
  unfold LNTH; rewrite num_rec_SUC; fold (@LNTH A n).
  unfold LTL, LHD; destruct (llist_rep ll 0) eqn:E0; cbn.
  - rewrite IH; cbn; f_equal; lia.
  - symmetry; apply (lrep_ok_none _ (llist_rep_ok ll) 0); [exact E0|lia].
Qed.

Lemma llist_ext_LNTH (l1 l2 : llist A) : (forall n, LNTH n l1 = LNTH n l2) -> l1 = l2.
Proof. intros H; apply llist_ext; intros n; rewrite <- !LNTH_rep; apply H. Qed.

End RepLemmas.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LNTH_THM" *)
Theorem LNTH_THM : forall {A},
  (forall n, LNTH n (@LNIL A) = NONE) /\
  (forall (h : A) t, LNTH 0 (LCONS h t) = SOME h) /\
  (forall n (h : A) t, LNTH (SUC n) (LCONS h t) = LNTH n t).
Proof.
  intros A; repeat split; intros; rewrite ?LNTH_rep; try reflexivity.
  cbn; unfold cons_rep; destruct (N.eqb_spec (SUC n) 0); [lia|]. f_equal; lia.
Qed.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LTAKE_THM" *)
Theorem LTAKE_THM : forall {A},
  (forall (l : llist A), LTAKE 0 l = SOME []) /\
  (forall n, LTAKE (SUC n) (@LNIL A) = NONE) /\
  (forall n (h : A) t, LTAKE (SUC n) (LCONS h t) = OPTION_MAP (cons h) (LTAKE n t)).
Proof.
  intros A; repeat split; intros; unfold LTAKE; rewrite ?num_rec_SUC; try reflexivity.
  fold (@LTAKE A n). rewrite (proj2 LHD_THM), (proj2 LTL_THM). cbn.
  destruct (LTAKE n t); reflexivity.
Qed.

Section Finite.
Context {A : Type}.

Definition fin_len (ll : llist A) (n : N) : Prop :=
  llist_rep ll n = None /\ forall k, k < n -> llist_rep ll k <> None.

Lemma rep_LCONS (h : A) t n :
  llist_rep (LCONS h t) n = if n =? 0 then SOME h else llist_rep t (n - 1).
Proof. reflexivity. Qed.

Lemma rep_LCONS_SUC (h : A) t n : llist_rep (LCONS h t) (SUC n) = llist_rep t n.
Proof. rewrite rep_LCONS; destruct (N.eqb_spec (SUC n) 0); [lia|]; f_equal; lia. Qed.

Lemma LNIL_of_rep0 (ll : llist A) : llist_rep ll 0 = None -> ll = LNIL.
Proof.
  intros H; apply llist_ext; intros n; cbn.
  apply (lrep_ok_none _ (llist_rep_ok ll) 0); [exact H|lia].
Qed.

Lemma LFINITE_rep (ll : llist A) : LFINITE ll <-> exists n, llist_rep ll n = None.
Proof.
  split.
  - induction 1 as [|h t _ [n Hn]]; [exists 0; reflexivity|].
    exists (SUC n); rewrite rep_LCONS_SUC; exact Hn.
  - intros [n Hn]; revert ll Hn; induction n as [|n IH] using N.peano_ind; intros ll Hn.
    + rewrite (LNIL_of_rep0 ll Hn); constructor.
    + destruct (llist_CASES ll) as [->|[h [t ->]]]; [constructor|].
      constructor; apply IH; rewrite <- (rep_LCONS_SUC h); exact Hn.
Qed.

Lemma fin_len_exists (ll : llist A) : (exists n, llist_rep ll n = None) -> exists n, fin_len ll n.
Proof.
  intros [n Hn]; revert Hn.
  induction n as [n IH] using (well_founded_induction N.lt_wf_0); intros Hn.
  destruct (classic (exists k, k < n /\ llist_rep ll k = None)) as [[k [Hk Hk']]|Hno].
  - exact (IH k Hk Hk').
  - exists n; split; [exact Hn|]. intros k Hk E; apply Hno; eauto.
Qed.

Lemma fin_len_unique (ll : llist A) n m : fin_len ll n -> fin_len ll m -> n = m.
Proof.
  intros [Hn Hn'] [Hm Hm'].
  destruct (N.lt_trichotomy n m) as [H|[H|H]]; [exfalso; exact (Hm' n H Hn)|exact H|].
  exfalso; exact (Hn' m H Hm).
Qed.

Lemma llength_rel_fin_len (ll : llist A) n : llength_rel ll n <-> fin_len ll n.
Proof.
  split.
  - induction 1 as [|h n t _ [IH1 IH2]].
    + split; [reflexivity|intros k Hk; lia].
    + split; [rewrite rep_LCONS_SUC; exact IH1|].
      intros k Hk; rewrite rep_LCONS; destruct (N.eqb_spec k 0); [discriminate|].
      apply IH2; lia.
  - revert ll; induction n as [|n IH] using N.peano_ind; intros ll [H1 H2].
    + rewrite (LNIL_of_rep0 ll H1); constructor.
    + destruct (llist_CASES ll) as [->|[h [t ->]]]; [exfalso; apply (H2 0); [lia|reflexivity]|].
      constructor; apply IH; split; [rewrite <- (rep_LCONS_SUC h); exact H1|].
      intros k Hk; rewrite <- (rep_LCONS_SUC h); apply H2; lia.
Qed.

Lemma LLENGTH_fin_len (ll : llist A) n : LLENGTH ll = SOME n <-> fin_len ll n.
Proof.
  unfold LLENGTH; destruct (classical_dec (LFINITE ll)) as [Hf|Hf].
  - pose proof (fin_len_exists ll (proj1 (LFINITE_rep ll) Hf)) as [m Hm].
    assert (Hsel : llength_rel ll (select (fun n => llength_rel ll n))).
    { apply select_spec; exists m; apply llength_rel_fin_len; exact Hm. }
    apply llength_rel_fin_len in Hsel.
    split; [intros E; inversion E; subst; exact Hsel|].
    intros Hn; f_equal; exact (fin_len_unique ll _ _ Hsel Hn).
  - split; [discriminate|]. intros [Hn _]; exfalso; apply Hf, LFINITE_rep; eauto.
Qed.

Lemma LLENGTH_NONE (ll : llist A) : LLENGTH ll = NONE <-> forall n, llist_rep ll n <> None.
Proof.
  unfold LLENGTH; destruct (classical_dec (LFINITE ll)) as [Hf|Hf].
  - split; [discriminate|]. intros H; exfalso.
    destruct (proj1 (LFINITE_rep ll) Hf) as [n Hn]; exact (H n Hn).
  - split; [|reflexivity]. intros _ n Hn; apply Hf, LFINITE_rep; eauto.
Qed.

End Finite.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LFINITE_THM" *)
Theorem LFINITE_THM : forall {A},
  (LFINITE (@LNIL A) <-> True) /\ (forall (h : A) t, LFINITE (LCONS h t) <-> LFINITE t).
Proof.
  intros A; split; [split; [auto|intros; constructor]|].
  intros h t; rewrite !LFINITE_rep; split.
  - intros [n Hn]; destruct n as [|p] using N.peano_ind; [discriminate|].
    rewrite rep_LCONS_SUC in Hn; eauto.
  - intros [n Hn]; exists (SUC n); rewrite rep_LCONS_SUC; exact Hn.
Qed.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LLENGTH_THM" *)
Theorem LLENGTH_THM : forall {A},
  LLENGTH (@LNIL A) = SOME 0 /\
  (forall (h : A) t, LLENGTH (LCONS h t) = OPTION_MAP SUC (LLENGTH t)).
Proof.
  intros A; split.
  - apply LLENGTH_fin_len; split; [reflexivity|intros k Hk; lia].
  - intros h t; destruct (LLENGTH t) as [n|] eqn:E; cbn.
    + apply LLENGTH_fin_len in E as [E1 E2]; apply LLENGTH_fin_len; split.
      * rewrite rep_LCONS_SUC; exact E1.
      * intros k Hk; rewrite rep_LCONS; destruct (N.eqb_spec k 0); [discriminate|].
        apply E2; lia.
    + apply LLENGTH_NONE; intros n; rewrite rep_LCONS.
      destruct (N.eqb_spec n 0); [discriminate|]. apply (proj1 (LLENGTH_NONE t) E).
Qed.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "toList_THM" *)
Theorem toList_THM : forall {A} `{Inhabited A},
  toList (@LNIL A) = SOME [] /\
  (forall (h : A) t, toList (LCONS h t) = OPTION_MAP (cons h) (toList t)).
Proof.
  intros A HA; split.
  - unfold toList; destruct (classical_dec _) as [_|Hn]; [|exfalso; apply Hn; constructor].
    rewrite (proj1 LLENGTH_THM); reflexivity.
  - intros h t; unfold toList.
    destruct (classical_dec (LFINITE (LCONS h t))) as [Hc|Hc];
      destruct (classical_dec (LFINITE t)) as [Ht|Ht].
    2: exfalso; apply Ht; apply (proj1 (proj2 LFINITE_THM h t)); exact Hc.
    2: exfalso; apply Hc; apply (proj2 (proj2 LFINITE_THM h t)); exact Ht.
    2: reflexivity.
    rewrite (proj2 LLENGTH_THM).
    destruct (LLENGTH t) as [n|] eqn:E; cbn.
    + rewrite (proj2 (proj2 LTAKE_THM)); reflexivity.
    + exfalso; apply LFINITE_rep in Ht as [n Hn].
      exact (proj1 (LLENGTH_NONE t) E n Hn).
Qed.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LFINITE_fromList" *)
Theorem LFINITE_fromList : forall {A} (l : list A), LFINITE (fromList l).
Proof. intros A l; induction l; cbn; constructor; assumption. Qed.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LNTH_fromList" *)
Theorem LNTH_fromList : forall {A} `{Inhabited A} n (l : list A),
  LNTH n (fromList l) = if n <? LENGTH l then SOME (EL n l) else NONE.
Proof.
  intros A HA n l; revert n; induction l as [|x l IH]; intros n.
  - cbn [fromList LENGTH]; rewrite (proj1 LNTH_THM); destruct (N.ltb_spec n 0); [lia|reflexivity].
  - cbn [fromList LENGTH]. destruct n as [|n] using N.peano_ind.
    + rewrite (proj1 (proj2 LNTH_THM)); destruct (N.ltb_spec 0 (SUC (LENGTH l))); [reflexivity|lia].
    + rewrite (proj2 (proj2 LNTH_THM)), IH, EL_SUC.
      destruct (N.ltb_spec n (LENGTH l)), (N.ltb_spec (SUC n) (SUC (LENGTH l))); try lia; reflexivity.
Qed.

(** ** [LAPPEND]

    HOL introduces [LAPPEND] by [new_specification]; here it is defined
    pointwise (the first list up to its length, then the second), and HOL's
    specification is the tagged theorem [LAPPEND]. *)
Section Append.
Context {A : Type}.

Definition lapp_rep (l1 l2 : llist A) (n : N) : option A :=
  match LLENGTH l1 with
  | None => llist_rep l1 n
  | Some m => if n <? m then llist_rep l1 n else llist_rep l2 (n - m)
  end.

Lemma lrep_ok_lapp (l1 l2 : llist A) : lrep_ok (lapp_rep l1 l2).
Proof.
  intros n; unfold lapp_rep; destruct (LLENGTH l1) as [m|] eqn:E; [|apply (llist_rep_ok l1)].
  apply LLENGTH_fin_len in E as [E1 E2].
  destruct (N.ltb_spec (SUC n) m), (N.ltb_spec n m); try lia.
  - apply (llist_rep_ok l1).
  - intros _. destruct (llist_rep l1 n) eqn:En; [reflexivity|]. exfalso; exact (E2 n ltac:(lia) En).
  - replace (SUC n - m) with (SUC (n - m)) by lia. apply (llist_rep_ok l2).
Qed.

Definition LAPPEND_def (l1 l2 : llist A) : llist A :=
  llist_abs_ok (lapp_rep l1 l2) (lrep_ok_lapp l1 l2).

End Append.
Abbreviation LAPPEND := LAPPEND_def.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LAPPEND" *)
Theorem LAPPEND_thm : forall {A},
  (forall x : llist A, LAPPEND LNIL x = x) /\
  (forall (h : A) t x, LAPPEND (LCONS h t) x = LCONS h (LAPPEND t x)).
Proof.
  intros A; split.
  - intros x; apply llist_ext; intros n; cbn; unfold lapp_rep.
    rewrite (proj1 LLENGTH_THM). destruct (N.ltb_spec n 0); [lia|]. f_equal; lia.
  - intros h t x; apply llist_ext; intros n; cbn [LAPPEND_def LCONS llist_rep].
    unfold lapp_rep at 1, cons_rep; rewrite (proj2 LLENGTH_THM).
    destruct (LLENGTH t) as [m|] eqn:E; cbn [OPTION_MAP option_map].
    + destruct (N.eqb_spec n 0) as [->|Hn].
      * destruct (N.ltb_spec 0 (SUC m)); [reflexivity|lia].
      * unfold lapp_rep; rewrite E.
        destruct (N.ltb_spec n (SUC m)), (N.ltb_spec (n - 1) m); try lia.
        -- cbn; unfold cons_rep; destruct (N.eqb_spec n 0); [lia|reflexivity].
        -- f_equal; lia.
    + unfold lapp_rep; rewrite E; reflexivity.
Qed.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LNTH_LAPPEND" *)
Theorem LNTH_LAPPEND : forall {A} n (l1 l2 : llist A),
  LNTH n (LAPPEND l1 l2) =
  match LLENGTH l1 with
  | NONE => LNTH n l1
  | SOME m => if n <? m then LNTH n l1 else LNTH (n - m) l2
  end.
Proof.
  intros; rewrite !LNTH_rep; cbn; unfold lapp_rep.
  destruct (LLENGTH l1); [|reflexivity]. destruct (_ <? _); rewrite ?LNTH_rep; reflexivity.
Qed.

Section AppendLemmas.
Context {A : Type}.

Lemma LLENGTH_LAPPEND_aux (l1 l2 : llist A) :
  LLENGTH (LAPPEND l1 l2) =
  match LLENGTH l1, LLENGTH l2 with
  | Some m, Some k => Some (m + k)
  | _, _ => None
  end.
Proof.
  destruct (LLENGTH l1) as [m|] eqn:E1.
  - pose proof E1 as [F1 F2]%LLENGTH_fin_len.
    destruct (LLENGTH l2) as [k|] eqn:E2.
    + pose proof E2 as [G1 G2]%LLENGTH_fin_len.
      apply LLENGTH_fin_len; split; cbn; unfold lapp_rep; rewrite E1.
      * destruct (N.ltb_spec (m + k) m); [lia|]. replace (m + k - m) with k by lia; exact G1.
      * intros j Hj. destruct (N.ltb_spec j m); [apply F2; lia|]. apply G2; lia.
    + apply LLENGTH_NONE; intros n; cbn; unfold lapp_rep; rewrite E1.
      destruct (N.ltb_spec n m); [|apply (proj1 (LLENGTH_NONE l2) E2)].
      apply F2; lia.
  - apply LLENGTH_NONE; intros n; cbn; unfold lapp_rep; rewrite E1.
    apply (proj1 (LLENGTH_NONE l1) E1).
Qed.

Lemma LFINITE_LLENGTH (ll : llist A) : LFINITE ll <-> LLENGTH ll <> NONE.
Proof.
  rewrite LFINITE_rep; split.
  - intros [n Hn] E; exact (proj1 (LLENGTH_NONE ll) E n Hn).
  - intros H. destruct (LLENGTH ll) as [m|] eqn:E; [|congruence].
    apply LLENGTH_fin_len in E as [E _]; eauto.
Qed.

End AppendLemmas.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LAPPEND_ASSOC" *)
Theorem LAPPEND_ASSOC : forall {A} (ll1 ll2 ll3 : llist A),
  LAPPEND (LAPPEND ll1 ll2) ll3 = LAPPEND ll1 (LAPPEND ll2 ll3).
Proof.
  intros A l1 l2 l3; apply llist_ext; intros n; cbn [LAPPEND_def llist_rep].
  unfold lapp_rep at 1 2; rewrite LLENGTH_LAPPEND_aux.
  destruct (LLENGTH l1) as [m|] eqn:E1; [|cbn; unfold lapp_rep; rewrite E1; reflexivity].
  destruct (LLENGTH l2) as [k|] eqn:E2; cbn; unfold lapp_rep; rewrite ?E1, ?E2.
  - destruct (N.ltb_spec n (m + k)), (N.ltb_spec n m); try reflexivity.
    + destruct (N.ltb_spec (n - m) k); [reflexivity|lia].
    + lia.
    + destruct (N.ltb_spec (n - m) k); [lia|]. f_equal; lia.
  - destruct (N.ltb_spec n m); reflexivity.
Qed.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LAPPEND_fromList" *)
Theorem LAPPEND_fromList : forall {A} (l1 l2 : list A),
  LAPPEND (fromList l1) (fromList l2) = fromList (l1 ++ l2).
Proof.
  intros A l1 l2; induction l1 as [|x l1 IH]; cbn [fromList app].
  - apply (proj1 LAPPEND_thm).
  - rewrite (proj2 LAPPEND_thm), IH; reflexivity.
Qed.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LFINITE_APPEND" *)
Theorem LFINITE_APPEND : forall {A} (ll1 ll2 : llist A),
  LFINITE (LAPPEND ll1 ll2) <-> LFINITE ll1 /\ LFINITE ll2.
Proof.
  intros A l1 l2; rewrite !LFINITE_LLENGTH, LLENGTH_LAPPEND_aux.
  destruct (LLENGTH l1), (LLENGTH l2); split; intros H; try split; try discriminate;
    try tauto; try congruence; destruct H; congruence.
Qed.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LFINITE_LAPPEND_IMP_NIL" *)
Theorem LFINITE_LAPPEND_IMP_NIL : forall {A} (ll : llist A),
  LFINITE ll -> forall l2, LAPPEND ll l2 = ll -> l2 = LNIL.
Proof.
  intros A ll Hf l2 E.
  apply LFINITE_LLENGTH in Hf. destruct (LLENGTH ll) as [m|] eqn:Em; [|congruence].
  apply LNIL_of_rep0.
  pose proof (f_equal (fun l => llist_rep l m) E) as Hm; cbn in Hm; unfold lapp_rep in Hm.
  rewrite Em in Hm. destruct (N.ltb_spec m m); [lia|].
  rewrite N.sub_diag in Hm. rewrite Hm. apply LLENGTH_fin_len in Em as [Em _]; exact Em.
Qed.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LAPPEND_EQ_LNIL" *)
Theorem LAPPEND_EQ_LNIL : forall {A} (l1 l2 : llist A),
  LAPPEND l1 l2 = LNIL <-> l1 = LNIL /\ l2 = LNIL.
Proof.
  intros A l1 l2; split.
  - intros E. destruct (llist_CASES l1) as [->|[h [t ->]]].
    + rewrite (proj1 LAPPEND_thm) in E; split; [reflexivity|exact E].
    + rewrite (proj2 LAPPEND_thm) in E.
      pose proof (f_equal (fun l => llist_rep l 0) E) as H0; cbn in H0; discriminate.
  - intros [-> ->]; apply (proj1 LAPPEND_thm).
Qed.

(** ** [LPREFIX]

    HOL defines [LPREFIX] through [toList]; it is equivalent to the
    pointwise relation [pfx] below (every element of the first list is at the
    same position in the second), from which HOL's lemmas follow. *)
Section Prefix.
Context {A : Type} `{EqDecision A} `{Inhabited A}.

Definition pfx (l1 l2 : llist A) : Prop :=
  forall i x, LNTH i l1 = SOME x -> LNTH i l2 = SOME x.

Lemma pfx_LCONS (x h : A) l1 t : pfx (LCONS x l1) (LCONS h t) <-> x = h /\ pfx l1 t.
Proof.
  unfold pfx; split.
  - intros P. assert (x = h) as ->.
    { specialize (P 0 x); rewrite !(proj1 (proj2 LNTH_THM)) in P.
      specialize (P eq_refl); inversion P; reflexivity. }
    split; [reflexivity|]. intros i y Hy.
    specialize (P (SUC i) y); rewrite !(proj2 (proj2 LNTH_THM)) in P; exact (P Hy).
  - intros [-> P] i y Hy. destruct i as [|i] using N.peano_ind.
    + rewrite (proj1 (proj2 LNTH_THM)) in *; exact Hy.
    + rewrite (proj2 (proj2 LNTH_THM)) in *; exact (P i y Hy).
Qed.

Lemma pfx_LNIL l : pfx LNIL l.
Proof. intros i x Hx; rewrite (proj1 LNTH_THM) in Hx; discriminate. Qed.

Lemma pfx_LCONS_LNIL (x : A) l : ~ pfx (LCONS x l) LNIL.
Proof.
  intros P; specialize (P 0 x); rewrite (proj1 (proj2 LNTH_THM)), (proj1 LNTH_THM) in P.
  discriminate (P eq_refl).
Qed.

Lemma LTAKE_pfx n : forall (ll : llist A) xs,
  LTAKE n ll = SOME xs <-> LENGTH xs = n /\ pfx (fromList xs) ll.
Proof.
  induction n as [|n IH] using N.peano_ind; intros ll xs.
  - rewrite (proj1 LTAKE_THM); split.
    + intros E; inversion E; split; [reflexivity|apply pfx_LNIL].
    + intros [Hl _]; destruct xs; [reflexivity|cbn in Hl; lia].
  - destruct (llist_CASES ll) as [->|[h [t ->]]].
    + rewrite (proj1 (proj2 LTAKE_THM)); split; [discriminate|].
      intros [Hl P]; destruct xs as [|x xs]; [cbn in Hl; lia|]. exfalso; exact (pfx_LCONS_LNIL x _ P).
    + rewrite (proj2 (proj2 LTAKE_THM)). destruct xs as [|x xs].
      * split; [destruct (LTAKE n t); discriminate|intros [Hl _]; cbn in Hl; lia].
      * cbn [fromList]; rewrite pfx_LCONS; cbn [LENGTH].
        destruct (LTAKE n t) as [ys|] eqn:E; cbn.
        -- split.
           ++ intros F; inversion F; subst. apply IH in E as [E1 E2]. split; [lia|split; auto].
           ++ intros [Hl [-> P]]. f_equal. f_equal.
              assert (Hys := proj1 (IH t ys) E). assert (Hxs : LTAKE n t = SOME xs).
              { apply IH; split; [lia|exact P]. }
              congruence.
        -- split; [discriminate|]. intros [Hl [-> P]].
           assert (LTAKE n t = SOME xs) by (apply IH; split; [lia|exact P]). congruence.
Qed.

Lemma toList_fromList (l : list A) : toList (fromList l) = SOME l.
Proof.
  induction l as [|x l IH]; cbn [fromList].
  - apply (proj1 toList_THM).
  - rewrite (proj2 toList_THM), IH; reflexivity.
Qed.

Lemma LFINITE_fromList_ex (ll : llist A) : LFINITE ll -> exists xs, ll = fromList xs.
Proof.
  induction 1 as [|h t _ [xs ->]]; [exists []; reflexivity|]. exists (h :: xs); reflexivity.
Qed.

Lemma toList_SOME (ll : llist A) xs : toList ll = SOME xs <-> ll = fromList xs.
Proof.
  split; [|intros ->; apply toList_fromList].
  intros E. destruct (classic (LFINITE ll)) as [Hf|Hf].
  - destruct (LFINITE_fromList_ex ll Hf) as [ys ->]. rewrite toList_fromList in E.
    inversion E; reflexivity.
  - unfold toList in E; destruct (classical_dec _); [contradiction|discriminate].
Qed.

Lemma toList_NONE (ll : llist A) : toList ll = NONE <-> ~ LFINITE ll.
Proof.
  split.
  - intros E Hf; destruct (LFINITE_fromList_ex ll Hf) as [xs ->].
    rewrite toList_fromList in E; discriminate.
  - intros Hf; unfold toList; destruct (classical_dec _); [contradiction|reflexivity].
Qed.

Lemma isPREFIX_LTAKE (xs ys : list A) :
  isPREFIX xs ys = true <-> LTAKE (LENGTH xs) (fromList ys) = SOME xs.
Proof.
  revert ys; induction xs as [|x xs IH]; intros ys; cbn [isPREFIX LENGTH].
  - rewrite (proj1 LTAKE_THM); split; reflexivity.
  - destruct ys as [|y ys]; cbn [fromList].
    + rewrite (proj1 (proj2 LTAKE_THM)); split; discriminate.
    + rewrite (proj2 (proj2 LTAKE_THM)), andb_true_iff, bool_decide_spec, IH.
      destruct (LTAKE (LENGTH xs) (fromList ys)) as [zs|]; cbn; split.
      * intros [-> E]; inversion E; reflexivity.
      * intros E; inversion E; subst; split; reflexivity.
      * intros [_ E]; discriminate.
      * discriminate.
Qed.

Lemma infinite_pfx_eq (l1 l2 : llist A) : ~ LFINITE l1 -> pfx l1 l2 -> l1 = l2.
Proof.
  intros Hf P; apply llist_ext_LNTH; intros n.
  destruct (LNTH n l1) as [x|] eqn:E; [symmetry; exact (P n x E)|].
  exfalso; apply Hf, LFINITE_rep; exists n; rewrite <- LNTH_rep; exact E.
Qed.

Lemma LPREFIX_pfx (l1 l2 : llist A) : LPREFIX l1 l2 <-> pfx l1 l2.
Proof.
  unfold LPREFIX.
  destruct (toList l1) as [xs|] eqn:E1.
  - apply toList_SOME in E1 as ->.
    destruct (toList l2) as [ys|] eqn:E2.
    + apply toList_SOME in E2 as ->. rewrite isPREFIX_LTAKE, LTAKE_pfx; tauto.
    + rewrite LTAKE_pfx; tauto.
  - apply toList_NONE in E1. split; [intros ->; intros i x Hx; exact Hx|].
    apply infinite_pfx_eq; exact E1.
Qed.

End Prefix.

Section PrefixThms.
Context {A : Type} `{EqDecision A} `{Inhabited A}.

(** The list [ll] without its first [m] elements (Galette helper). *)
Lemma lrep_ok_ldrop (m : N) (ll : llist A) : lrep_ok (fun n => llist_rep ll (n + m)).
Proof.
  intros n; cbv beta. replace (SUC n + m) with (SUC (n + m)) by lia.
  exact (llist_rep_ok ll (n + m)).
Qed.

Definition ldrop (m : N) (ll : llist A) : llist A :=
  llist_abs_ok (fun n => llist_rep ll (n + m)) (lrep_ok_ldrop m ll).

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LPREFIX_APPEND" *)
Theorem LPREFIX_APPEND : forall (l1 l2 : llist A),
  LPREFIX l1 l2 <-> exists ll, l2 = LAPPEND l1 ll.
Proof.
  intros l1 l2; rewrite LPREFIX_pfx; split.
  - intros P. destruct (LLENGTH l1) as [m|] eqn:Em.
    + exists (ldrop m l2). apply llist_ext; intros n; cbn; unfold lapp_rep; rewrite Em.
      destruct (N.ltb_spec n m).
      * apply LLENGTH_fin_len in Em as [_ F].
        destruct (llist_rep l1 n) as [x|] eqn:E; [|exfalso; exact (F n H1 E)].
        rewrite <- !LNTH_rep in *. exact (P n x E).
      * unfold ldrop; cbn [llist_rep]; rewrite N.sub_add by lia; reflexivity.
    + exists LNIL. symmetry.
      assert (Hf : ~ LFINITE l1) by (rewrite LFINITE_LLENGTH; congruence).
      rewrite <- (infinite_pfx_eq l1 l2 Hf P).
      apply llist_ext; intros n; cbn; unfold lapp_rep; rewrite Em; reflexivity.
  - intros [ll ->] i x Hx. rewrite LNTH_LAPPEND.
    destruct (LLENGTH l1) as [m|] eqn:Em; [|exact Hx].
    destruct (N.ltb_spec i m); [exact Hx|].
    apply LLENGTH_fin_len in Em as [F _]. rewrite LNTH_rep in Hx.
    pose proof (lrep_ok_none _ (llist_rep_ok l1) m i F ltac:(lia)) as Z; rewrite Z in Hx; discriminate.
Qed.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LPREFIX_REFL" *)
Theorem LPREFIX_REFL : forall (ll : llist A), LPREFIX ll ll.
Proof. intros ll; apply LPREFIX_pfx; intros i x Hx; exact Hx. Qed.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LPREFIX_TRANS" *)
Theorem LPREFIX_TRANS : forall (l1 l2 l3 : llist A),
  LPREFIX l1 l2 /\ LPREFIX l2 l3 -> LPREFIX l1 l3.
Proof.
  intros l1 l2 l3 [P Q]; rewrite LPREFIX_pfx in *; intros i x Hx; apply Q, P, Hx.
Qed.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LPREFIX_LNIL" *)
Theorem LPREFIX_LNIL : forall (ll : llist A),
  LPREFIX LNIL ll /\ (LPREFIX ll LNIL <-> ll = LNIL).
Proof.
  intros ll; rewrite !LPREFIX_pfx; split; [apply pfx_LNIL|split].
  - intros P; destruct (llist_CASES ll) as [->|[h [t ->]]]; [reflexivity|].
    exfalso; exact (pfx_LCONS_LNIL h t P).
  - intros ->; apply pfx_LNIL.
Qed.

(*! HOL "HOL/src/coalgebras/llistScript.sml" "LPREFIX_fromList" *)
Theorem LPREFIX_fromList : forall (l : list A) ll,
  LPREFIX (fromList l) ll <->
  match toList ll with
  | NONE => LTAKE (LENGTH l) ll = SOME l
  | SOME ys => isPREFIX l ys = true
  end.
Proof. intros l ll; unfold LPREFIX; rewrite toList_fromList; reflexivity. Qed.

End PrefixThms.
