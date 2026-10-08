(** * CakeML [reg_allocProof]: the allocator state and its invariants

    Part of the [reg_allocProofScript] counterpart: the state invariants
    ([has_edge], [undirected], [good_ra_state], [no_clash], [good_pref]) and
    the rewriting lemmas for the monadic array accessors.

    Galette-only infrastructure in this file (untagged):
    - [SORTED] is HOL's [sortingTheory.SORTED_DEF] ([sorting.v] does not
      have it yet); [sort_SORTED] is [mllistTheory.sort_SORTED] (proved here
      from [mergesort_tail]; HOL's statement uses [transitive]/[total], here
      only totality is needed);
    - [with_f s v] is HOL's record update [s with f := v] on [ra_state];
    - generic list lemmas ([EL]/[LUPDATE]/[GENLIST]/...) and monadic bind
      lemmas used by the proofs. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.coretypes Require Import pair.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.sort Require Import sorting mergesort.
From Galette.cakeml.basis.pure Require Import mllist.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From Stdlib Require Import Permutation Sorted.
Open Scope N_scope.
Open Scope monad_scope.

(** ** Generic list lemmas (Galette infrastructure) *)

Lemma LENGTH_cons {A} (x : A) l : LENGTH (x :: l) = LENGTH l + 1.
Proof. cbn [LENGTH]; lia. Qed.

Lemma EL_cons {A} `{Inhabited A} n (x : A) l :
  EL n (x :: l) = if n =? 0 then x else EL (n - 1) l.
Proof.
  destruct (N.eqb_spec n 0) as [->|Hn]; [reflexivity|].
  rewrite <- (N.succ_pred n Hn) at 1; rewrite EL_SUC, N.sub_1_r; reflexivity.
Qed.

Lemma EL_0 {A} `{Inhabited A} (x : A) l : EL 0 (x :: l) = x.
Proof. reflexivity. Qed.

Lemma EL_In {A} `{Inhabited A} n (l : list A) : n < LENGTH l -> In (EL n l) l.
Proof.
  intros Hn; rewrite EL_nth by exact Hn; apply nth_In.
  rewrite LENGTH_length in Hn; lia.
Qed.

Lemma In_EL {A} `{Inhabited A} x (l : list A) : In x l -> exists n, n < LENGTH l /\ x = EL n l.
Proof.
  intros Hx; apply (In_nth l x ARB) in Hx as (k & Hk & <-).
  exists (N.of_nat k); split; [rewrite LENGTH_length; lia|].
  rewrite EL_nth by (rewrite LENGTH_length; lia); rewrite Nat2N.id; reflexivity.
Qed.

Lemma LENGTH_LUPDATE {A} (e : A) : forall l n, LENGTH (LUPDATE e n l) = LENGTH l.
Proof.
  induction l as [|x l IH]; intros n; cbn [LUPDATE LENGTH]; [reflexivity|].
  destruct (n =? 0); cbn [LENGTH]; rewrite ?IH; reflexivity.
Qed.

Lemma EL_LUPDATE {A} `{Inhabited A} (e : A) : forall l i n,
  EL n (LUPDATE e i l) = if decide (i = n /\ n < LENGTH l) then e else EL n l.
Proof.
  induction l as [|x l IH]; intros i n; cbn [LUPDATE LENGTH].
  - destruct (decide _) as [[_ ?]|]; [lia|reflexivity].
  - destruct (N.eqb_spec i 0) as [->|Hi]; rewrite !EL_cons.
    + destruct (N.eqb_spec n 0) as [->|Hn]; destruct (decide _) as [[? ?]|Hd].
      all: first [reflexivity | lia | (exfalso; apply Hd; split; [reflexivity|lia])].
    + destruct (N.eqb_spec n 0) as [->|Hn].
      * destruct (decide _) as [[? ?]|]; [lia|reflexivity].
      * rewrite IH; rewrite <- N.sub_1_r.
        destruct (decide (i - 1 = n - 1 /\ n - 1 < LENGTH l)) as [[? ?]|Hd1];
          destruct (decide (i = n /\ n < N.succ (LENGTH l))) as [[? ?]|Hd2]; try reflexivity; lia.
Qed.

Lemma In_LUPDATE {A} (e : A) : forall l n y, In y (LUPDATE e n l) -> y = e \/ In y l.
Proof.
  induction l as [|x l IH]; intros n y; cbn [LUPDATE]; [tauto|].
  destruct (n =? 0); cbn [In]; [intuition|].
  intros [<-|H]; [right; left; reflexivity|]. destruct (IH _ _ H); tauto.
Qed.

Lemma Forall_LUPDATE {A} (P : A -> Prop) e l n : P e -> Forall P l -> Forall P (LUPDATE e n l).
Proof.
  intros He Hl; apply Forall_forall; intros y Hy.
  destruct (In_LUPDATE e l n y Hy) as [->|Hy']; [exact He|]. eapply Forall_forall; eauto.
Qed.

Lemma EVERY_LUPDATE {A} (P : A -> bool) e l n :
  P e -> EVERY P l -> EVERY P (LUPDATE e n l).
Proof. intros He Hl; unfold is_true in *; rewrite EVERY_Forall in *; apply (Forall_LUPDATE (fun x => P x = true)); auto. Qed.

Lemma In_GENLIST {A} (f : N -> A) n y : In y (GENLIST f n) <-> exists i, i < n /\ y = f i.
Proof.
  induction n as [|n IH] using N.peano_ind.
  - cbn; split; [tauto|intros (i & Hi & _); lia].
  - rewrite (proj2 (GENLIST_thm f n)), SNOC_app, in_app_iff, IH; cbn [In]. split.
    + intros [(i & Hi & ->)|[<-|[]]]; [exists i; split; [lia|reflexivity]|exists n; split; [lia|reflexivity]].
    + intros (i & Hi & ->). destruct (N.eq_dec i n) as [->|Hn]; [right; left; reflexivity|].
      left; exists i; split; [lia|reflexivity].
Qed.

Lemma LENGTH_GENLIST {A} (f : N -> A) n : LENGTH (GENLIST f n) = n.
Proof.
  induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (GENLIST_thm f n)), SNOC_app, !LENGTH_length, length_app; cbn [length].
  rewrite LENGTH_length in IH; lia.
Qed.

Lemma In_COUNT_LIST n y : In y (COUNT_LIST n) <-> y < n.
Proof.
  rewrite COUNT_LIST_GENLIST, In_GENLIST; split; [intros (i & Hi & ->); exact Hi|].
  intros Hy; exists y; split; [exact Hy|reflexivity].
Qed.

Lemma In_REPLICATE {A} n (x : A) y : In y (REPLICATE n x) -> y = x.
Proof. rewrite REPLICATE_GENLIST, In_GENLIST; intros (i & _ & ->); reflexivity. Qed.

Lemma EL_REPLICATE {A} `{Inhabited A} n (x : A) i : i < n -> EL i (REPLICATE n x) = x.
Proof.
  intros Hi; apply (In_REPLICATE n x); apply EL_In; rewrite LENGTH_REPLICATE; exact Hi.
Qed.

Lemma MEM_iff {A} `{EqDecision A} (x : A) l : is_true (MEM x l) <-> In x l.
Proof. apply MEM_In. Qed.

Lemma EVERY_iff {A} (P : A -> bool) l : is_true (EVERY P l) <-> (forall x, In x l -> is_true (P x)).
Proof. unfold is_true; rewrite EVERY_Forall, Forall_forall; reflexivity. Qed.

Lemma ALL_DISTINCT_iff {A} `{EqDecision A} (l : list A) : is_true (ALL_DISTINCT l) <-> NoDup l.
Proof.
  induction l as [|x l IH]; cbn [ALL_DISTINCT]; unfold is_true in *.
  - split; [constructor|reflexivity].
  - rewrite andb_true_iff, IH, negb_true_iff, NoDup_cons_iff.
    destruct (MEM x l) eqn:E.
    + apply MEM_In in E; split; [intros [? _]; discriminate|intros [? _]; contradiction].
    + split; intros [_ Hn]; split; auto. intros Hin; apply MEM_In in Hin; congruence.
Qed.

Lemma ltb_iff (a b : N) : is_true (a <? b) <-> a < b.
Proof. apply N.ltb_lt. Qed.

Lemma leb_iff (a b : N) : is_true (a <=? b) <-> a <= b.
Proof. apply N.leb_le. Qed.

Lemma andb_iff (a b : bool) : is_true (a && b) <-> is_true a /\ is_true b.
Proof. apply andb_true_iff. Qed.

Lemma orb_iff (a b : bool) : is_true (a || b) <-> is_true a \/ is_true b.
Proof. apply orb_true_iff. Qed.

Lemma bool_decide_iff (P : Prop) `{Decision P} : is_true (bool_decide P) <-> P.
Proof. apply bool_decide_spec. Qed.

Lemma IN_set_iff {A} (x : A) l : x IN set l <-> In x l.
Proof. apply IN_set. Qed.

Lemma IN_domain_iff {A} (t : spt A) x : x IN domain t <-> exists v, lookup x t = Some v.
Proof. apply domain_lookup. Qed.

(** ** HOL [SORTED] and the sortedness of [mllist$sort] *)

(** HOL's [sortingTheory.SORTED_DEF] ([sorting.v] does not have it yet). *)
Fixpoint SORTED {A} (R : A -> A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: rest => match rest with [] => true | y :: _ => R x y && SORTED R rest end
  end.

Lemma SORTED_Sorted {A} (R : A -> A -> bool) l :
  is_true (SORTED R l) <-> Sorted (fun x y => is_true (R x y)) l.
Proof.
  induction l as [|x [|y l] IH].
  - split; [constructor|reflexivity].
  - split; [repeat constructor|reflexivity].
  - cbn [SORTED] in *; rewrite andb_iff, IH; split.
    + intros [Hxy Hs]; constructor; [exact Hs|constructor; exact Hxy].
    + intros Hs; inversion Hs as [|? ? Hs' Hhd]; subst; inversion Hhd; auto.
Qed.

Lemma Sorted_nth {A} (R : A -> A -> Prop) (d : A) l :
  Sorted R l <-> (forall i, (S i < length l)%nat -> R (nth i l d) (nth (S i) l d)).
Proof.
  induction l as [|x l IH]; [split; [intros _ i Hi; cbn in Hi; lia|constructor]|].
  split.
  - intros Hs; inversion Hs as [|? ? Hl Hhd]; subst. intros [|i] Hi; cbn [nth].
    + destruct l as [|y l]; [cbn in Hi; lia|]. inversion Hhd; assumption.
    + apply IH; [exact Hl|cbn in Hi; lia].
  - intros H; constructor.
    + apply IH; intros i Hi; apply (H (S i)); cbn; lia.
    + destruct l as [|y l]; constructor. apply (H 0%nat); cbn; lia.
Qed.

Lemma Sorted_rev {A} (R : A -> A -> Prop) l :
  Sorted R l -> Sorted (fun x y => R y x) (rev l).
Proof.
  destruct l as [|d l']; [intros; constructor|].
  set (l := d :: l'). intros Hs; pose proof (proj1 (Sorted_nth R d l) Hs) as Hs2; clear Hs; rename Hs2 into Hs; apply (proj2 (Sorted_nth _ d _)).
  rewrite length_rev; intros i Hi.
  rewrite !rev_nth by lia.
  replace (length l - S i)%nat with (S (length l - S (S i)))%nat by lia.
  apply Hs; lia.
Qed.

Section SortSorted.
Context {A : Type} (R : A -> A -> bool) (Rtot : forall x y, R x y = true \/ R y x = true).

Definition Rn (neg : bool) (x y : A) : Prop := if neg then R y x = true else R x y = true.

(** The merge order of [merge_tail neg R]. *)
Fixpoint mrg (neg : bool) (l1 : list A) : list A -> list A :=
  fix aux (l2 : list A) : list A :=
    match l1, l2 with
    | [], l => l
    | l, [] => l
    | x :: l1', y :: l2' =>
        if bool_decide (R x y <> neg) then x :: mrg neg l1' (y :: l2') else y :: aux l2'
    end.

Lemma merge_tail_mrg neg l1 : forall l2 acc,
  merge_tail neg R l1 l2 acc = rev_append (mrg neg l1 l2) acc.
Proof.
  induction l1 as [|x l1 IH]; intros l2.
  - destruct l2; reflexivity.
  - induction l2 as [|y l2 IH2]; intros acc; [reflexivity|].
    cbn [merge_tail mrg]; destruct (bool_decide _); [apply IH|apply IH2].
Qed.

Lemma pick_l neg x y : bool_decide (R x y <> neg) = true -> Rn neg x y.
Proof.
  rewrite bool_decide_spec; unfold Rn; destruct neg, (R x y) eqn:E; try congruence.
  destruct (Rtot x y); congruence.
Qed.

Lemma pick_r neg x y : bool_decide (R x y <> neg) = false -> Rn neg y x.
Proof.
  unfold bool_decide; destruct (decide _) as [|Hn]; [discriminate|]; intros _.
  unfold Rn; destruct neg, (R x y) eqn:E; try tauto;
    first [exfalso; apply Hn; discriminate | destruct (Rtot x y); congruence].
Qed.

Lemma mrg_HdRel neg a l1 : forall l2,
  HdRel (Rn neg) a l1 -> HdRel (Rn neg) a l2 -> HdRel (Rn neg) a (mrg neg l1 l2).
Proof.
  destruct l1 as [|x l1]; intros [|y l2] H1 H2; cbn [mrg]; auto.
  destruct (bool_decide _); constructor; [inversion H1|inversion H2]; auto.
Qed.

Lemma mrg_sorted neg l1 : forall l2,
  Sorted (Rn neg) l1 -> Sorted (Rn neg) l2 -> Sorted (Rn neg) (mrg neg l1 l2).
Proof.
  induction l1 as [|x l1 IH]; intros l2; [destruct l2; auto|].
  induction l2 as [|y l2 IH2]; intros H1 H2; [exact H1|].
  cbn [mrg]; destruct (bool_decide _) eqn:E.
  - inversion H1 as [|? ? H1' Hh1]; subst. constructor; [apply IH; auto|].
    apply mrg_HdRel; [exact Hh1|constructor; apply pick_l; exact E].
  - inversion H2 as [|? ? H2' Hh2]; subst. constructor; [apply IH2; auto|].
    exact (mrg_HdRel neg y (x :: l1) l2 ltac:(constructor; apply pick_r; exact E) Hh2).
Qed.

Lemma Rn_flip neg x y : Rn neg y x <-> Rn (negb neg) x y.
Proof. unfold Rn; destruct neg; reflexivity. Qed.

Lemma sort2_tail_sorted neg x y : Sorted (Rn neg) (sort2_tail neg R x y).
Proof.
  unfold sort2_tail; destruct (bool_decide _) eqn:E; repeat constructor.
  - apply pick_l, E.
  - apply pick_r, E.
Qed.

Lemma sort3_tail_sorted neg x y z : Sorted (Rn neg) (sort3_tail neg R x y z).
Proof.
  unfold sort3_tail.
  destruct (bool_decide (R x y <> neg)) eqn:Exy, (bool_decide (R y z <> neg)) eqn:Eyz,
    (bool_decide (R x z <> neg)) eqn:Exz;
    repeat (constructor || (apply pick_l; assumption) || (apply pick_r; assumption)).
Qed.

Lemma Sorted_Rn_change neg l : Sorted (Rn neg) l -> Sorted (fun x y => Rn (negb neg) y x) l.
Proof. apply Sorted_ind; intros; constructor; auto; destruct H1; constructor; unfold Rn in *; destruct neg; auto. Qed.

Lemma mergesortN_tail_f_sorted : forall fuel negate n l,
  Sorted (Rn negate) (mergesortN_tail_f fuel negate R n l).
Proof.
  induction fuel as [|fuel IH]; intros negate n l; cbn [mergesortN_tail_f]; [constructor|].
  destruct (N.lt_ge_cases n 4) as [hn|hn].
  - assert (h : n = 0 \/ n = 1 \/ n = 2 \/ n = 3) by lia.
    destruct h as [-> | [-> | [-> | ->]]].
    + constructor.
    + destruct l; repeat constructor.
    + destruct l as [|x [|y l]]; try (repeat constructor); apply sort2_tail_sorted.
    + destruct l as [|x [|y [|z l]]]; try (repeat constructor);
        [apply sort2_tail_sorted|apply sort3_tail_sorted].
  - assert (Hm : Sorted (Rn negate)
      (merge_tail (negb negate) R (mergesortN_tail_f fuel (negb negate) R (n DIV 2) l)
         (mergesortN_tail_f fuel (negb negate) R (n - n DIV 2) (DROP (n DIV 2) l)) [])).
    { rewrite merge_tail_mrg, rev_append_rev, app_nil_r.
      pose proof (Sorted_rev _ _ (mrg_sorted (negb negate) _ _ (IH (negb negate) (n DIV 2) l) (IH (negb negate) (n - n DIV 2) (DROP (n DIV 2) l)))) as Hr.
      clear -Hr. induction Hr; constructor; auto. destruct H; constructor.
      unfold Rn in *; destruct negate; exact H. }
    destruct n as [|p]; [lia|].
    destruct p as [[[p|p|]|[p|p|]|]|[[p|p|]|[p|p|]|]|]; try lia; exact Hm.
Qed.

Lemma sort_Sorted l : Sorted (fun x y => is_true (R x y)) (mllist.sort R l).
Proof.
  pose proof (mergesortN_tail_f_sorted (S (N.to_nat (LENGTH l))) false (LENGTH l) l) as H.
  exact H.
Qed.

End SortSorted.

(** [mllistTheory.sort_SORTED] for a total relation (untagged; HOL also
    assumes transitivity). *)
Theorem sort_SORTED {A} (R : A -> A -> bool) L :
  (forall x y, R x y = true \/ R y x = true) -> is_true (SORTED R (mllist.sort R L)).
Proof. intros Ht; apply SORTED_Sorted, sort_Sorted, Ht. Qed.

(** ** Record updates (HOL [s with f := v]) *)

Definition with_adj_ls (s : ra_state) v : ra_state :=
  mk_ra_state v s.(node_tag) s.(degrees) s.(dim) s.(simp_wl) s.(spill_wl) s.(freeze_wl)
    s.(avail_moves_wl) s.(unavail_moves_wl) s.(coalesced) s.(move_related) s.(stack).
Definition with_node_tag (s : ra_state) v : ra_state :=
  mk_ra_state s.(adj_ls) v s.(degrees) s.(dim) s.(simp_wl) s.(spill_wl) s.(freeze_wl)
    s.(avail_moves_wl) s.(unavail_moves_wl) s.(coalesced) s.(move_related) s.(stack).
Definition with_degrees (s : ra_state) v : ra_state :=
  mk_ra_state s.(adj_ls) s.(node_tag) v s.(dim) s.(simp_wl) s.(spill_wl) s.(freeze_wl)
    s.(avail_moves_wl) s.(unavail_moves_wl) s.(coalesced) s.(move_related) s.(stack).
Definition with_coalesced (s : ra_state) v : ra_state :=
  mk_ra_state s.(adj_ls) s.(node_tag) s.(degrees) s.(dim) s.(simp_wl) s.(spill_wl) s.(freeze_wl)
    s.(avail_moves_wl) s.(unavail_moves_wl) v s.(move_related) s.(stack).
Definition with_move_related (s : ra_state) v : ra_state :=
  mk_ra_state s.(adj_ls) s.(node_tag) s.(degrees) s.(dim) s.(simp_wl) s.(spill_wl) s.(freeze_wl)
    s.(avail_moves_wl) s.(unavail_moves_wl) s.(coalesced) v s.(stack).
Definition with_stack (s : ra_state) v : ra_state :=
  mk_ra_state s.(adj_ls) s.(node_tag) s.(degrees) s.(dim) s.(simp_wl) s.(spill_wl) s.(freeze_wl)
    s.(avail_moves_wl) s.(unavail_moves_wl) s.(coalesced) s.(move_related) v.
Definition with_avail_moves_wl (s : ra_state) v : ra_state :=
  mk_ra_state s.(adj_ls) s.(node_tag) s.(degrees) s.(dim) s.(simp_wl) s.(spill_wl) s.(freeze_wl)
    v s.(unavail_moves_wl) s.(coalesced) s.(move_related) s.(stack).
Definition with_unavail_moves_wl (s : ra_state) v : ra_state :=
  mk_ra_state s.(adj_ls) s.(node_tag) s.(degrees) s.(dim) s.(simp_wl) s.(spill_wl) s.(freeze_wl)
    s.(avail_moves_wl) v s.(coalesced) s.(move_related) s.(stack).

Ltac rs := cbn [with_adj_ls with_node_tag with_degrees with_coalesced with_move_related
  with_stack with_avail_moves_wl with_unavail_moves_wl
  adj_ls node_tag degrees dim simp_wl spill_wl freeze_wl avail_moves_wl unavail_moves_wl
  coalesced move_related stack] in *.

(** ** Monadic bind lemmas *)

Lemma bind_ok {S A B E} (m : M S A E) (f : A -> M S B E) s x s' :
  m s = (M_success x, s') -> st_ex_bind m f s = f x s'.
Proof. intros H; unfold st_ex_bind; rewrite H; reflexivity. Qed.

Lemma ibind_ok {S A B E} (m : M S A E) (f : M S B E) s x s' :
  m s = (M_success x, s') -> st_ex_ignore_bind m f s = f s'.
Proof. intros H; unfold st_ex_ignore_bind; rewrite H; reflexivity. Qed.

Lemma bind_fail {S A B E} (m : M S A E) (f : A -> M S B E) s e s' :
  m s = (M_failure e, s') -> st_ex_bind m f s = (M_failure e, s').
Proof. intros H; unfold st_ex_bind; rewrite H; reflexivity. Qed.

Lemma ibind_fail {S A B E} (m : M S A E) (f : M S B E) s e s' :
  m s = (M_failure e, s') -> st_ex_ignore_bind m f s = (M_failure e, s').
Proof. intros H; unfold st_ex_ignore_bind; rewrite H; reflexivity. Qed.

Lemma return_eq {S A E} (x : A) (s : S) : @st_ex_return S A E x s = (M_success x, s).
Proof. reflexivity. Qed.


(** The generated getters. *)
Lemma get_dim_eq {E} s : @get_dim E s = (M_success s.(dim), s). Proof. reflexivity. Qed.
Lemma get_simp_wl_eq {E} s : @get_simp_wl E s = (M_success s.(simp_wl), s). Proof. reflexivity. Qed.
Lemma get_spill_wl_eq {E} s : @get_spill_wl E s = (M_success s.(spill_wl), s). Proof. reflexivity. Qed.
Lemma get_freeze_wl_eq {E} s : @get_freeze_wl E s = (M_success s.(freeze_wl), s). Proof. reflexivity. Qed.
Lemma get_stack_eq {E} s : @get_stack E s = (M_success s.(stack), s). Proof. reflexivity. Qed.
Lemma get_avail_moves_wl_eq {E} s : @get_avail_moves_wl E s = (M_success s.(avail_moves_wl), s).
Proof. reflexivity. Qed.
Lemma get_unavail_moves_wl_eq {E} s : @get_unavail_moves_wl E s = (M_success s.(unavail_moves_wl), s).
Proof. reflexivity. Qed.

(** Step through a bind whose first computation is described by [H]. *)
Ltac mstep H :=
  first [ rewrite (bind_ok _ _ _ _ _ H) | rewrite (ibind_ok _ _ _ _ _ H)
        | rewrite (bind_fail _ _ _ _ _ H) | rewrite (ibind_fail _ _ _ _ _ H) ].

(** ** The invariants *)

(** Edge from node [x] to node [y], in terms of an adjacency list. *)
(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "has_edge_def" *)
Definition has_edge (adjls : list (list N)) (x y : N) : Prop :=
  x < LENGTH adjls /\ y < LENGTH adjls /\ MEM y (EL x adjls).

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "undirected_def" *)
Definition undirected (adjls : list (list N)) : Prop :=
  forall x y, has_edge adjls x y -> has_edge adjls y x.

(** All arrays have the right dimensions and the worklists contain legal
    nodes. *)
(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "good_ra_state_def" *)
Definition good_ra_state (s : ra_state) : Prop :=
  LENGTH s.(adj_ls) = s.(dim) /\
  LENGTH s.(node_tag) = s.(dim) /\
  LENGTH s.(degrees) = s.(dim) /\
  LENGTH s.(coalesced) = s.(dim) /\
  LENGTH s.(move_related) = s.(dim) /\
  EVERY (fun v => v <? s.(dim)) s.(coalesced) /\
  EVERY (fun ls => EVERY (fun v => v <? s.(dim)) ls) s.(adj_ls) /\
  EVERY (fun ls => SORTED (fun x y => y <? x) ls) s.(adj_ls) /\
  EVERY (fun v => v <? s.(dim)) s.(simp_wl) /\
  EVERY (fun v => v <? s.(dim)) s.(spill_wl) /\
  EVERY (fun v => v <? s.(dim)) s.(freeze_wl) /\
  EVERY (fun '(p, (x, y)) => (x <? s.(dim)) && (y <? s.(dim))) s.(avail_moves_wl) /\
  EVERY (fun '(p, (x, y)) => (x <? s.(dim)) && (y <? s.(dim))) s.(unavail_moves_wl) /\
  undirected s.(adj_ls).

(** No two adjacent nodes have the same colour. *)
(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "no_clash_def" *)
Definition no_clash (adj_ls : list (list N)) (node_tag : list tag) : Prop :=
  forall x y, has_edge adj_ls x y ->
    match EL x node_tag, EL y node_tag with
    | Fixed n, Fixed m => n = m -> x = y
    | _, _ => True
    end.

(** A good preference oracle only inspects the state, and selects a member
    of its input list. *)
(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "good_pref_def" *)
Definition good_pref (pref : N -> list N -> RA (option N)) : Prop :=
  forall n ks s, good_ra_state s ->
    exists res, pref n ks s = (M_success res, s) /\
      match res with None => True | Some k => is_true (MEM k ks) end.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "tag_case_st" *)
Theorem tag_case_st : forall {S B} (t : tag) (a : N -> S -> B) (b c : S -> B) (f : S),
  (match t with Fixed n => a n | Atemp => b | Stemp => c end) f =
  (match t with Fixed n => a n f | Atemp => b f | Stemp => c f end).
Proof. intros S B [] *; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "list_case_st" *)
Theorem list_case_st : forall {S B C} (t : list C) (a : S -> B) (b : C -> list C -> S -> B) (f : S),
  (match t with [] => a | x :: y => b x y end) f =
  (match t with [] => a f | x :: y => b x y f end).
Proof. intros S B C [|? ?] *; reflexivity. Qed.

(** ** Rewriting lemmas for the array accessors *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "Msub_eqn" *)
Theorem Msub_eqn : forall {A E} `{Inhabited A} (e : E) n (ls : list A),
  Msub e n ls = if n <? LENGTH ls then M_success (EL n ls) else M_failure e.
Proof.
  intros A E IA e n ls; revert n; induction ls as [|x ls IH]; intros n; cbn [Msub LENGTH]; [destruct (N.ltb_spec n 0); [lia|reflexivity]|].
  rewrite EL_cons; destruct (N.eqb_spec n 0) as [->|Hn]; [destruct (N.ltb_spec 0 (N.succ (LENGTH ls))); [reflexivity|lia]|].
  rewrite IH; destruct (N.ltb_spec (n - 1) (LENGTH ls)), (N.ltb_spec n (SUC (LENGTH ls))); try lia; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "adj_ls_sub_eqn" *)
Theorem adj_ls_sub_eqn : forall n s,
  adj_ls_sub n s =
  if n <? LENGTH s.(adj_ls) then (M_success (EL n s.(adj_ls)), s) else (M_failure Subscript, s).
Proof. intros; unfold adj_ls_sub, Marray_sub; rewrite Msub_eqn; destruct (_ <? _); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "node_tag_sub_eqn" *)
Theorem node_tag_sub_eqn : forall n s,
  node_tag_sub n s =
  if n <? LENGTH s.(node_tag) then (M_success (EL n s.(node_tag)), s) else (M_failure Subscript, s).
Proof. intros; unfold node_tag_sub, Marray_sub; rewrite Msub_eqn; destruct (_ <? _); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "degrees_sub_eqn" *)
Theorem degrees_sub_eqn : forall n s,
  degrees_sub n s =
  if n <? LENGTH s.(degrees) then (M_success (EL n s.(degrees)), s) else (M_failure Subscript, s).
Proof. intros; unfold degrees_sub, Marray_sub; rewrite Msub_eqn; destruct (_ <? _); reflexivity. Qed.

(** HOL's theorem [coalesced_sub] (named [_thm]: the constant has its name). *)
(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "coalesced_sub" *)
Theorem coalesced_sub_thm : forall n s,
  coalesced_sub n s =
  if n <? LENGTH s.(coalesced) then (M_success (EL n s.(coalesced)), s) else (M_failure Subscript, s).
Proof. intros; unfold coalesced_sub, Marray_sub; rewrite Msub_eqn; destruct (_ <? _); reflexivity. Qed.

(** HOL's theorem [move_related_sub] (named [_thm]). *)
(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "move_related_sub" *)
Theorem move_related_sub_thm : forall n s,
  move_related_sub n s =
  if n <? LENGTH s.(move_related) then (M_success (EL n s.(move_related)), s) else (M_failure Subscript, s).
Proof. intros; unfold move_related_sub, Marray_sub; rewrite Msub_eqn; destruct (_ <? _); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "Mupdate_eqn" *)
Theorem Mupdate_eqn : forall {A E} (e : E) (x : A) n ls,
  Mupdate e x n ls = if n <? LENGTH ls then M_success (LUPDATE x n ls) else M_failure e.
Proof.
  intros A E e x n ls; revert n; induction ls as [|y ls IH]; intros n; cbn [Mupdate LENGTH LUPDATE]; [destruct (N.ltb_spec n 0); [lia|reflexivity]|].
  destruct (N.eqb_spec n 0) as [->|Hn]; [destruct (N.ltb_spec 0 (N.succ (LENGTH ls))); [reflexivity|lia]|].
  rewrite IH; rewrite <- ?N.sub_1_r.
  destruct (N.ltb_spec (n - 1) (LENGTH ls)), (N.ltb_spec n (SUC (LENGTH ls))); try lia; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "update_adj_ls_eqn" *)
Theorem update_adj_ls_eqn : forall n t s,
  update_adj_ls n t s =
  if n <? LENGTH s.(adj_ls) then (M_success tt, with_adj_ls s (LUPDATE t n s.(adj_ls)))
  else (M_failure Subscript, s).
Proof. intros; unfold update_adj_ls, Marray_update; rewrite Mupdate_eqn; destruct (_ <? _); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "update_node_tag_eqn" *)
Theorem update_node_tag_eqn : forall n t s,
  update_node_tag n t s =
  if n <? LENGTH s.(node_tag) then (M_success tt, with_node_tag s (LUPDATE t n s.(node_tag)))
  else (M_failure Subscript, s).
Proof. intros; unfold update_node_tag, Marray_update; rewrite Mupdate_eqn; destruct (_ <? _); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "update_degrees_eqn" *)
Theorem update_degrees_eqn : forall n t s,
  update_degrees n t s =
  if n <? LENGTH s.(degrees) then (M_success tt, with_degrees s (LUPDATE t n s.(degrees)))
  else (M_failure Subscript, s).
Proof. intros; unfold update_degrees, Marray_update; rewrite Mupdate_eqn; destruct (_ <? _); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "update_coalesced_eqn" *)
Theorem update_coalesced_eqn : forall n t s,
  update_coalesced n t s =
  if n <? LENGTH s.(coalesced) then (M_success tt, with_coalesced s (LUPDATE t n s.(coalesced)))
  else (M_failure Subscript, s).
Proof. intros; unfold update_coalesced, Marray_update; rewrite Mupdate_eqn; destruct (_ <? _); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "update_move_related_eqn" *)
Theorem update_move_related_eqn : forall n t s,
  update_move_related n t s =
  if n <? LENGTH s.(move_related) then (M_success tt, with_move_related s (LUPDATE t n s.(move_related)))
  else (M_failure Subscript, s).
Proof. intros; unfold update_move_related, Marray_update; rewrite Mupdate_eqn; destruct (_ <? _); reflexivity. Qed.

(** In-range versions used by the proofs. *)
Lemma adj_ls_sub_ok n s : n < LENGTH s.(adj_ls) -> adj_ls_sub n s = (M_success (EL n s.(adj_ls)), s).
Proof. intros H; rewrite adj_ls_sub_eqn; apply N.ltb_lt in H; rewrite H; reflexivity. Qed.
Lemma node_tag_sub_ok n s : n < LENGTH s.(node_tag) -> node_tag_sub n s = (M_success (EL n s.(node_tag)), s).
Proof. intros H; rewrite node_tag_sub_eqn; apply N.ltb_lt in H; rewrite H; reflexivity. Qed.
Lemma degrees_sub_ok n s : n < LENGTH s.(degrees) -> degrees_sub n s = (M_success (EL n s.(degrees)), s).
Proof. intros H; rewrite degrees_sub_eqn; apply N.ltb_lt in H; rewrite H; reflexivity. Qed.
Lemma coalesced_sub_ok n s : n < LENGTH s.(coalesced) -> coalesced_sub n s = (M_success (EL n s.(coalesced)), s).
Proof. intros H; rewrite coalesced_sub_thm; apply N.ltb_lt in H; rewrite H; reflexivity. Qed.
Lemma move_related_sub_ok n s : n < LENGTH s.(move_related) ->
  move_related_sub n s = (M_success (EL n s.(move_related)), s).
Proof. intros H; rewrite move_related_sub_thm; apply N.ltb_lt in H; rewrite H; reflexivity. Qed.
Lemma update_adj_ls_ok n t s : n < LENGTH s.(adj_ls) ->
  update_adj_ls n t s = (M_success tt, with_adj_ls s (LUPDATE t n s.(adj_ls))).
Proof. intros H; rewrite update_adj_ls_eqn; apply N.ltb_lt in H; rewrite H; reflexivity. Qed.
Lemma update_node_tag_ok n t s : n < LENGTH s.(node_tag) ->
  update_node_tag n t s = (M_success tt, with_node_tag s (LUPDATE t n s.(node_tag))).
Proof. intros H; rewrite update_node_tag_eqn; apply N.ltb_lt in H; rewrite H; reflexivity. Qed.
Lemma update_degrees_ok n t s : n < LENGTH s.(degrees) ->
  update_degrees n t s = (M_success tt, with_degrees s (LUPDATE t n s.(degrees))).
Proof. intros H; rewrite update_degrees_eqn; apply N.ltb_lt in H; rewrite H; reflexivity. Qed.
Lemma update_coalesced_ok n t s : n < LENGTH s.(coalesced) ->
  update_coalesced n t s = (M_success tt, with_coalesced s (LUPDATE t n s.(coalesced))).
Proof. intros H; rewrite update_coalesced_eqn; apply N.ltb_lt in H; rewrite H; reflexivity. Qed.
Lemma update_move_related_ok n t s : n < LENGTH s.(move_related) ->
  update_move_related n t s = (M_success tt, with_move_related s (LUPDATE t n s.(move_related))).
Proof. intros H; rewrite update_move_related_eqn; apply N.ltb_lt in H; rewrite H; reflexivity. Qed.

(** ** Monadic maps of the accessors *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "st_ex_MAP_node_tag_sub" *)
Theorem st_ex_MAP_node_tag_sub : forall ls s,
  EVERY (fun v => v <? LENGTH s.(node_tag)) ls ->
  st_ex_MAP node_tag_sub ls s = (M_success (MAP (fun i => EL i s.(node_tag)) ls), s).
Proof.
  induction ls as [|x ls IH]; intros s H; [reflexivity|].
  cbn [EVERY] in H; apply andb_iff in H as [Hx H]; apply ltb_iff in Hx.
  cbn [st_ex_MAP]; mstep (node_tag_sub_ok _ _ Hx); mstep (IH _ H); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "st_ex_MAP_adj_ls_sub" *)
Theorem st_ex_MAP_adj_ls_sub : forall ls s,
  EVERY (fun v => v <? LENGTH s.(adj_ls)) ls ->
  st_ex_MAP adj_ls_sub ls s = (M_success (MAP (fun i => EL i s.(adj_ls)) ls), s).
Proof.
  induction ls as [|x ls IH]; intros s H; [reflexivity|].
  cbn [EVERY] in H; apply andb_iff in H as [Hx H]; apply ltb_iff in Hx.
  cbn [st_ex_MAP]; mstep (adj_ls_sub_ok _ _ Hx); mstep (IH _ H); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "st_ex_MAP_degrees_sub" *)
Theorem st_ex_MAP_degrees_sub : forall ls s,
  EVERY (fun v => v <? LENGTH s.(degrees)) ls ->
  st_ex_MAP degrees_sub ls s = (M_success (MAP (fun i => EL i s.(degrees)) ls), s).
Proof.
  induction ls as [|x ls IH]; intros s H; [reflexivity|].
  cbn [EVERY] in H; apply andb_iff in H as [Hx H]; apply ltb_iff in Hx.
  cbn [st_ex_MAP]; mstep (degrees_sub_ok _ _ Hx); mstep (IH _ H); reflexivity.
Qed.
