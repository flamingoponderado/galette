(** * CakeML [linear_scanProof]: the monadic linear-scan allocator

    Part of the [linear_scanProofScript] counterpart (HOL lines 2020-4574):
    the array access lemmas, register exchange, the state invariant
    [good_linear_scan_state] and its preservation by the allocation steps,
    and the correctness of the in-place quicksorts.

    Local helpers (untagged, Galette infrastructure): list lemmas on [EL] and
    [LUPDATE] over [N] indices, and HOL's [sorting$SORTED], [sorting$PERM],
    [pair$LEX] and [relation$total], which are not ported in their own
    counterpart files yet; they are defined here with HOL's definitions
    ([PERM] as [!x. FILTER ($= x) L1 = FILTER ($= x) L2], decided
    classically), so the statements using them read as in HOL. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.relation Require Import relation.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.basis.pure Require Import mllist.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc linear_scan.
From Galette.cakeml.compiler.backend.reg_alloc.proofs.reg_allocProof Require Import check_clash_tree.
From Galette.cakeml.compiler.backend.reg_alloc.proofs.linear_scanProof Require Import intervals.
From Stdlib Require Import Permutation Sorting.Sorted.
Open Scope N_scope.
Open Scope monad_scope.

(** ** List helpers (Galette infrastructure) *)

Ltac nsplit :=
  repeat match goal with
  | |- context [N.eqb ?a ?b] => destruct (N.eqb_spec a b)
  | |- context [N.ltb ?a ?b] => destruct (N.ltb_spec a b)
  end; cbn [andb] in *.

Section ListHelpers.
Context {A : Type} `{Inhabited A}.

Lemma EL_cons (i : N) (x : A) l : EL i (x :: l) = if i =? 0 then x else EL (i - 1) l.
Proof.
  destruct (N.eqb_spec i 0) as [->|Hi]; [reflexivity|].
  rewrite <- (N.succ_pred i Hi) at 1; rewrite EL_SUC, N.sub_1_r; reflexivity.
Qed.

Lemma EL_0 (x : A) l : EL 0 (x :: l) = x.
Proof. reflexivity. Qed.

Lemma EL_out (i : N) (l : list A) : LENGTH l <= i -> EL i l = ARB.
Proof.
  revert i; induction l as [|x l IH]; intros i Hi.
  - induction i as [|i IHi] using N.peano_ind; [reflexivity|]. rewrite EL_SUC; cbn [TL]; apply IHi; cbn [LENGTH]; lia.
  - cbn [LENGTH] in Hi. rewrite EL_cons. destruct (N.eqb_spec i 0); [lia|]. apply IH; lia.
Qed.

Lemma LENGTH_LUPDATE (x : A) n l : LENGTH (LUPDATE x n l) = LENGTH l.
Proof.
  revert n; induction l as [|y l IH]; intros n; cbn [LUPDATE LENGTH]; [reflexivity|].
  destruct (n =? 0); cbn [LENGTH]; rewrite ?IH; reflexivity.
Qed.

Lemma EL_LUPDATE (x : A) n l i :
  EL i (LUPDATE x n l) = if (i =? n) && (n <? LENGTH l) then x else EL i l.
Proof.
  revert n i; induction l as [|y l IH]; intros n i; cbn [LUPDATE LENGTH].
  - nsplit; try lia; reflexivity.
  - rewrite !EL_cons. destruct (N.eqb_spec n 0) as [->|Hn].
    + rewrite !EL_cons; nsplit; try lia; reflexivity.
    + rewrite EL_cons, IH, <- N.sub_1_r. nsplit; try lia; try reflexivity.
      all: exfalso; lia.
Qed.

Lemma EL_LUPDATE_same (x : A) n l : n < LENGTH l -> EL n (LUPDATE x n l) = x.
Proof. intros; rewrite EL_LUPDATE, N.eqb_refl; destruct (N.ltb_spec n (LENGTH l)); [reflexivity|lia]. Qed.

Lemma EL_LUPDATE_other (x : A) n l i : i <> n -> EL i (LUPDATE x n l) = EL i l.
Proof. intros; rewrite EL_LUPDATE; destruct (N.eqb_spec i n); [lia|reflexivity]. Qed.

Lemma In_EL (x : A) l : In x l <-> exists i, i < LENGTH l /\ x = EL i l.
Proof.
  induction l as [|y l IH]; cbn [In LENGTH].
  - split; [intros []|intros (i & Hi & _); lia].
  - rewrite IH; split.
    + intros [<-|(i & Hi & ->)]; [exists 0; split; [lia|reflexivity]|].
      exists (i + 1); split; [lia|]. rewrite EL_cons; destruct (N.eqb_spec (i + 1) 0); [lia|].
      f_equal; lia.
    + intros (i & Hi & ->). rewrite EL_cons. destruct (N.eqb_spec i 0); [left; reflexivity|].
      right; exists (i - 1); split; [lia|reflexivity].
Qed.

Lemma EL_In (i : N) l : i < LENGTH l -> In (EL i l) l.
Proof. intros Hi; apply In_EL; eauto. Qed.

Lemma LENGTH_app (l1 l2 : list A) : LENGTH (l1 ++ l2) = LENGTH l1 + LENGTH l2.
Proof. induction l1; cbn [app LENGTH]; lia. Qed.

Lemma EL_app (i : N) (l1 l2 : list A) :
  EL i (l1 ++ l2) = if i <? LENGTH l1 then EL i l1 else EL (i - LENGTH l1) l2.
Proof.
  revert i; induction l1 as [|x l1 IH]; intros i; cbn [app LENGTH].
  - destruct (N.ltb_spec i 0); [lia|]; f_equal; lia.
  - rewrite !EL_cons, IH. nsplit; try lia; try reflexivity. f_equal; lia.
Qed.

Lemma LIST_EQ (l1 l2 : list A) :
  LENGTH l1 = LENGTH l2 -> (forall i, i < LENGTH l1 -> EL i l1 = EL i l2) -> l1 = l2.
Proof.
  revert l2; induction l1 as [|x l1 IH]; intros [|y l2] Hl He; cbn [LENGTH] in *; try lia; [reflexivity|].
  f_equal; [exact (He 0 ltac:(lia))|]. apply IH; [lia|]. intros i Hi.
  specialize (He (i + 1) ltac:(lia)); rewrite !EL_cons in He.
  destruct (N.eqb_spec (i + 1) 0); [lia|]. replace (i + 1 - 1) with i in He by lia; exact He.
Qed.

Lemma LENGTH_TAKE' n (l : list A) : LENGTH (TAKE n l) = N.min n (LENGTH l).
Proof.
  revert n; induction l as [|x l IH]; intros n; cbn [TAKE LENGTH]; [lia|].
  destruct (N.eqb_spec n 0) as [->|Hn]; cbn [LENGTH]; [lia|]. rewrite IH; lia.
Qed.

Lemma EL_TAKE n i (l : list A) : i < n -> EL i (TAKE n l) = EL i l.
Proof.
  revert n i; induction l as [|x l IH]; intros n i Hi; cbn [TAKE]; [reflexivity|].
  destruct (N.eqb_spec n 0); [lia|]. rewrite !EL_cons. destruct (N.eqb_spec i 0); [reflexivity|]. apply IH; lia.
Qed.

Lemma LENGTH_DROP n (l : list A) : LENGTH (DROP n l) = LENGTH l - n.
Proof.
  revert n; induction l as [|x l IH]; intros n; cbn [DROP LENGTH]; [lia|].
  destruct (N.eqb_spec n 0) as [->|Hn]; cbn [LENGTH]; [lia|]. rewrite IH; lia.
Qed.

Lemma EL_DROP n i (l : list A) : EL i (DROP n l) = EL (i + n) l.
Proof.
  revert n i; induction l as [|x l IH]; intros n i; cbn [DROP].
  - rewrite !EL_out; cbn; [reflexivity|lia|lia].
  - destruct (N.eqb_spec n 0) as [->|Hn]; [f_equal; lia|].
    rewrite IH, EL_cons. destruct (N.eqb_spec (i + n) 0); [lia|]. f_equal; lia.
Qed.

Lemma TAKE_LENGTH_ID (l : list A) : TAKE (LENGTH l) l = l.
Proof. induction l as [|x l IH]; cbn [TAKE LENGTH]; [reflexivity|]. destruct (N.eqb_spec (SUC (LENGTH l)) 0); [lia|].
  rewrite N.sub_1_r, N.pred_succ, IH; reflexivity. Qed.

End ListHelpers.

Lemma EL_MAP {A B} `{Inhabited A} `{Inhabited B} (f : A -> B) i l :
  i < LENGTH l -> EL i (MAP f l) = f (EL i l).
Proof.
  revert i; induction l as [|x l IH]; intros i Hi; cbn [LENGTH] in Hi; [lia|].
  cbn [MAP List.map]; rewrite !EL_cons. destruct (N.eqb_spec i 0); [reflexivity|]. apply IH; lia.
Qed.

Lemma LENGTH_MAP {A B} (f : A -> B) l : LENGTH (MAP f l) = LENGTH l.
Proof. induction l; cbn; lia. Qed.

Lemma MEM_iff {A} `{EqDecision A} (x : A) l : is_true (MEM x l) <-> In x l.
Proof. apply MEM_In. Qed.

Lemma EVERY_iff {A} (P : A -> bool) l : is_true (EVERY P l) <-> forall x, In x l -> is_true (P x).
Proof. unfold is_true; rewrite EVERY_Forall, Forall_forall; reflexivity. Qed.

Lemma EVERY_bd {A} (P : A -> Prop) l : is_true (EVERY (fun x => ⌜P x⌝) l) <-> forall x, In x l -> P x.
Proof.
  rewrite EVERY_iff; split; intros Hh x Hx; specialize (Hh x Hx);
    [apply bool_decide_spec in Hh|apply bool_decide_spec]; exact Hh.
Qed.

Lemma ALL_DISTINCT_iff {A} `{EqDecision A} (l : list A) : is_true (ALL_DISTINCT l) <-> NoDup l.
Proof. apply ALL_DISTINCT_NoDup. Qed.

(** HOL [sorting$SORTED] (sortingTheory [SORTED_DEF]); the relation is a
    predicate. *)
Fixpoint SORTED {A} (R : A -> A -> Prop) (l : list A) : Prop :=
  match l with
  | [] => True
  | x :: rest => match rest with [] => True | y :: _ => R x y /\ SORTED R rest end
  end.

Lemma SORTED_Sorted {A} (R : A -> A -> Prop) l : SORTED R l <-> Sorted R l.
Proof.
  induction l as [|x [|y l] IH].
  - split; [constructor|intros; exact I].
  - split; [repeat constructor|intros; exact I].
  - cbn [SORTED] in *; rewrite IH; split.
    + intros [Hxy Hs]; constructor; [exact Hs|constructor; exact Hxy].
    + intros Hs; inversion Hs as [|? ? Hs' Hhd]; subst; inversion Hhd; auto.
Qed.

Lemma SORTED_EQ {A} (R : A -> A -> Prop) x l :
  transitive R -> (SORTED R (x :: l) <-> SORTED R l /\ forall y, In y l -> R x y).
Proof.
  intros T; rewrite !SORTED_Sorted; split.
  - intros Hs; apply Sorted_StronglySorted in Hs; [|intros a b c; intros; eapply T; eauto].
    inversion Hs as [|? ? Hs' Hf]; subst; split; [apply StronglySorted_Sorted; exact Hs'|].
    apply Forall_forall, Hf.
  - intros [Hs Hf]; constructor; [exact Hs|]. destruct l as [|y l]; constructor; apply Hf; left; reflexivity.
Qed.

(** HOL [sorting$PERM] (sortingTheory [PERM_DEF]). *)
Definition PERM {A} (L1 L2 : list A) : Prop :=
  forall x, FILTER (fun y => ⌜x = y⌝) L1 = FILTER (fun y => ⌜x = y⌝) L2.

Lemma PERM_Permutation {A} (l1 l2 : list A) : PERM l1 l2 <-> Permutation l1 l2.
Proof.
  set (dec := fun a b : A => classical_dec (a = b)).
  assert (F : forall x l, FILTER (fun y => ⌜x = y⌝) l = repeat x (count_occ dec l x)).
  { intros x l; induction l as [|y l IH]; [reflexivity|]. cbn [List.filter count_occ].
    destruct (dec y x) as [e|e]; subst.
    - rewrite (proj2 (bool_decide_spec (x = x)) eq_refl); cbn [repeat]; rewrite IH; reflexivity.
    - assert (bool_decide (x = y) = false) as ->
        by (destruct (bool_decide (x = y)) eqn:B; [apply bool_decide_spec in B; congruence|reflexivity]).
      exact IH. }
  unfold PERM; rewrite (Permutation_count_occ dec); split.
  - intros Hp x; specialize (Hp x); rewrite !F in Hp.
    apply (f_equal (@length A)) in Hp; rewrite !repeat_length in Hp; exact Hp.
  - intros Hp x; rewrite !F, Hp; reflexivity.
Qed.

(** HOL [pair$LEX] ([pairTheory.LEX_DEF]). *)
Definition LEX {A B} (R1 : A -> A -> Prop) (R2 : B -> B -> Prop) (p q : A * B) : Prop :=
  let '(s, t) := p in let '(u, v) := q in R1 s u \/ (s = u /\ R2 t v).

(** HOL [relation$total] ([relationTheory.total_def]). *)
Definition total {A} (R : A -> A -> Prop) : Prop := forall x y, R x y \/ R y x.

(** ** Monad helpers *)

Lemma Msub_eqn {A E} `{Inhabited A} (e : E) n (l : list A) :
  Msub e n l = if n <? LENGTH l then M_success (EL n l) else M_failure e.
Proof.
  revert n; induction l as [|x l IH]; intros n; cbn [Msub LENGTH]; [nsplit; try lia; reflexivity|].
  rewrite EL_cons, IH. nsplit; try lia; reflexivity.
Qed.

Lemma Mupdate_eqn {A E} (e : E) (x : A) n (l : list A) :
  Mupdate e x n l = if n <? LENGTH l then M_success (LUPDATE x n l) else M_failure e.
Proof.
  revert n; induction l as [|y l IH]; intros n; cbn [Mupdate LENGTH LUPDATE]; [nsplit; try lia; reflexivity|].
  rewrite IH, <- N.sub_1_r. nsplit; try lia; reflexivity.
Qed.

Ltac msimp :=
  unfold st_ex_bind, st_ex_ignore_bind, st_ex_return in *; cbv beta iota zeta in *.

(** ** Array access lemmas *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "colors_sub_eqn" *)
Theorem colors_sub_eqn : forall n s,
  colors_sub n s =
  if n <? LENGTH s.(colors) then (M_success (EL n s.(colors)), s)
  else (M_failure Subscript, s).
Proof. intros; unfold colors_sub, Marray_sub; rewrite Msub_eqn; destruct (n <? _); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "update_colors_eqn" *)
Theorem update_colors_eqn : forall n t s,
  update_colors n t s =
  if n <? LENGTH s.(colors) then
    (M_success tt, {| colors := LUPDATE t n s.(colors); int_beg := s.(int_beg); int_end := s.(int_end);
                      sorted_regs := s.(sorted_regs); sorted_moves := s.(sorted_moves) |})
  else (M_failure Subscript, s).
Proof. intros; unfold update_colors, Marray_update; rewrite Mupdate_eqn; destruct (n <? _); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "int_beg_sub_eqn" *)
Theorem int_beg_sub_eqn : forall n s,
  int_beg_sub n s =
  if n <? LENGTH s.(int_beg) then (M_success (EL n s.(int_beg)), s)
  else (M_failure Subscript, s).
Proof. intros; unfold int_beg_sub, Marray_sub; rewrite Msub_eqn; destruct (n <? _); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "update_int_beg_eqn" *)
Theorem update_int_beg_eqn : forall n t s,
  update_int_beg n t s =
  if n <? LENGTH s.(int_beg) then
    (M_success tt, {| colors := s.(colors); int_beg := LUPDATE t n s.(int_beg); int_end := s.(int_end);
                      sorted_regs := s.(sorted_regs); sorted_moves := s.(sorted_moves) |})
  else (M_failure Subscript, s).
Proof. intros; unfold update_int_beg, Marray_update; rewrite Mupdate_eqn; destruct (n <? _); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "int_end_sub_eqn" *)
Theorem int_end_sub_eqn : forall n s,
  int_end_sub n s =
  if n <? LENGTH s.(int_end) then (M_success (EL n s.(int_end)), s)
  else (M_failure Subscript, s).
Proof. intros; unfold int_end_sub, Marray_sub; rewrite Msub_eqn; destruct (n <? _); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "update_int_end_eqn" *)
Theorem update_int_end_eqn : forall n t s,
  update_int_end n t s =
  if n <? LENGTH s.(int_end) then
    (M_success tt, {| colors := s.(colors); int_beg := s.(int_beg); int_end := LUPDATE t n s.(int_end);
                      sorted_regs := s.(sorted_regs); sorted_moves := s.(sorted_moves) |})
  else (M_failure Subscript, s).
Proof. intros; unfold update_int_end, Marray_update; rewrite Mupdate_eqn; destruct (n <? _); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "sorted_regs_sub_eqn" *)
Theorem sorted_regs_sub_eqn : forall n s,
  sorted_regs_sub n s =
  if n <? LENGTH s.(sorted_regs) then (M_success (EL n s.(sorted_regs)), s)
  else (M_failure Subscript, s).
Proof. intros; unfold sorted_regs_sub, Marray_sub; rewrite Msub_eqn; destruct (n <? _); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "update_sorted_regs_eqn" *)
Theorem update_sorted_regs_eqn : forall n t s,
  update_sorted_regs n t s =
  if n <? LENGTH s.(sorted_regs) then
    (M_success tt, {| colors := s.(colors); int_beg := s.(int_beg); int_end := s.(int_end);
                      sorted_regs := LUPDATE t n s.(sorted_regs); sorted_moves := s.(sorted_moves) |})
  else (M_failure Subscript, s).
Proof. intros; unfold update_sorted_regs, Marray_update; rewrite Mupdate_eqn; destruct (n <? _); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "sorted_moves_sub_eqn" *)
Theorem sorted_moves_sub_eqn : forall n s,
  sorted_moves_sub n s =
  if n <? LENGTH s.(sorted_moves) then (M_success (EL n s.(sorted_moves)), s)
  else (M_failure Subscript, s).
Proof. intros; unfold sorted_moves_sub, Marray_sub; rewrite Msub_eqn; destruct (n <? _); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "update_sorted_moves_eqn" *)
Theorem update_sorted_moves_eqn : forall n t s,
  update_sorted_moves n t s =
  if n <? LENGTH s.(sorted_moves) then
    (M_success tt, {| colors := s.(colors); int_beg := s.(int_beg); int_end := s.(int_end);
                      sorted_regs := s.(sorted_regs); sorted_moves := LUPDATE t n s.(sorted_moves) |})
  else (M_failure Subscript, s).
Proof. intros; unfold update_sorted_moves, Marray_update; rewrite Mupdate_eqn; destruct (n <? _); reflexivity. Qed.

(** ** Register exchange *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "lookup_default_id_def" *)
Definition lookup_default_id (s : num_map N) (x : N) : N :=
  match lookup x s with None => x | Some x => x end.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "find_reg_exchange_step_def" *)
Definition find_reg_exchange_step (colors : list N) (r : N) (p : num_map N * num_map N)
    : num_map N * num_map N :=
  let '(exch, invexch) := p in
  let col1 := EL r colors in
  let fcol1 := r DIV 2 in
  let col2 := lookup_default_id invexch fcol1 in
  let fcol2 := lookup_default_id exch col1 in
  (insert col1 fcol1 (insert col2 fcol2 exch), insert fcol1 col1 (insert fcol2 col2 invexch)).

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "find_reg_exchange_FOLDL" *)
Theorem find_reg_exchange_FOLDL : forall l (colors : list N) exch invexch sth,
  (forall r, MEM r l -> r < LENGTH sth.(linear_scan.colors)) ->
  find_reg_exchange l exch invexch sth =
    (M_success (FOLDL (fun a b => find_reg_exchange_step sth.(linear_scan.colors) b a) (exch, invexch) l), sth).
Proof.
  induction l as [|h l IH]; intros colors0 exch invexch sth Hl; cbn [find_reg_exchange FOLDL]; [reflexivity|].
  msimp. rewrite colors_sub_eqn.
  assert (Hh : h < LENGTH sth.(linear_scan.colors)) by (apply Hl; cbn; rewrite (proj2 (bool_decide_spec (h = h)) eq_refl); reflexivity).
  destruct (N.ltb_spec h (LENGTH sth.(linear_scan.colors))); [|lia].
  rewrite IH; [reflexivity|exact colors0|].
  intros r Hr; apply Hl; cbn [MEM]; rewrite Hr, orb_true_r; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "lookup_default_id_insert" *)
Theorem lookup_default_id_insert : forall s k1 k2 v,
  lookup_default_id (insert k2 v s) k1 = if decide (k1 = k2) then v else lookup_default_id s k1.
Proof. intros; unfold lookup_default_id; rewrite lookup_insert; destruct (decide (k1 = k2)); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "id_def" *)
Definition id {A} (x : A) : A := x.

Lemma phy_div2 r : is_true (is_phy_var r) -> r = 2 * (r / 2).
Proof.
  unfold is_phy_var, is_true; intros H; apply N.eqb_eq in H.
  pose proof (N.div_mod r 2 ltac:(lia)) as D; rewrite H in D; lia.
Qed.

Lemma ldi_LN x : lookup_default_id LN x = x.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "find_reg_exchange_FOLDR_correct" *)
Theorem find_reg_exchange_FOLDR_correct : forall l colors exch invexch k,
  ALL_DISTINCT (MAP (fun r => EL r colors) l) /\
  (forall r, MEM r l -> is_phy_var r) /\
  (exch, invexch) = FOLDR (fun a b => find_reg_exchange_step colors a b) (LN, LN) l ->
  ((lookup_default_id exch ∘ lookup_default_id invexch) = (fun x => x) /\
   (lookup_default_id invexch ∘ lookup_default_id exch) = (fun x => x)) /\
  (forall r, MEM r l -> lookup_default_id exch (EL r colors) = r DIV 2) /\
  ((forall r, MEM r l -> (k <= EL r colors <-> k <= r DIV 2)) ->
    (forall c, id (k <= c <-> k <= lookup_default_id exch c))) /\
  ((forall r, MEM r l -> r DIV 2 < k) ->
    (forall c, k <= c /\ (forall r, MEM r l -> c <> EL r colors) -> k <= lookup_default_id exch c)) /\
  ((forall r, MEM r l -> (k <= EL r colors /\ k <= r DIV 2)) ->
    (forall c, c < k -> lookup_default_id exch c = c)).
Proof.
  induction l as [|h l IH]; intros colors exch invexch k (Hd & Hp & Hf).
  - cbn [FOLDR] in Hf; inv_opt. unfold id.
    repeat split; try (apply functional_extensionality; intros; reflexivity);
      intros; try discriminate; rewrite ?ldi_LN; try tauto; lia.
  - cbn [FOLDR] in Hf.
    destruct (FOLDR (fun a b => find_reg_exchange_step colors a b) (LN, LN) l) as [e1 i1] eqn:Ef.
    cbn [MAP List.map ALL_DISTINCT] in Hd. unfold is_true in Hd; apply andb_prop in Hd as [Hn Hd].
    assert (Hp' : forall r, MEM r l -> is_phy_var r).
    { intros r Hr; apply Hp; cbn [MEM]; rewrite Hr, orb_true_r; reflexivity. }
    assert (Hph : is_phy_var h) by (apply Hp; cbn [MEM]; rewrite (proj2 (bool_decide_spec (h = h)) eq_refl); reflexivity).
    destruct (IH colors e1 i1 k (conj Hd (conj Hp' (eq_sym Ef)))) as ((EI & IE) & Hc & H3 & H4 & H5).
    clear IH. unfold find_reg_exchange_step in Hf. inv_opt.
    set (E := lookup_default_id e1) in *. set (I := lookup_default_id i1) in *.
    assert (EI' : forall y, E (I y) = y) by (intros y; exact (equal_f EI y)).
    assert (IE' : forall x, I (E x) = x) by (intros x; exact (equal_f IE x)).
    assert (Einj : forall x y, E x = E y -> x = y) by (intros x y Hxy; rewrite <- (IE' x), <- (IE' y), Hxy; reflexivity).
    set (col1 := EL h colors) in *. set (fcol1 := h / 2) in *.
    set (tau := fun y => if decide (y = fcol1) then E col1 else if decide (y = E col1) then fcol1 else y).
    assert (Hnot : forall r, MEM r l -> EL r colors <> col1).
    { intros r Hr Hc'; apply negb_true_iff in Hn. rewrite <- Hc' in Hn.
      assert (In (EL r colors) (MAP (fun r => EL r colors) l)) by (apply (in_map (fun r => EL r colors)); apply MEM_iff, Hr).
      apply MEM_iff in H; congruence. }
    assert (E' : forall x, lookup_default_id (insert col1 fcol1 (insert (I fcol1) (E col1) e1)) x = tau (E x)).
    { intros x; rewrite !lookup_default_id_insert; fold E; unfold tau.
      destruct (decide (x = col1)) as [->|n1].
      - destruct (decide (col1 = col1)) as [_|nn]; [|congruence].
        destruct (decide (E col1 = fcol1)) as [e|e]; [congruence|].
        destruct (decide (E col1 = E col1)); [reflexivity|congruence].
      - destruct (decide (x = I fcol1)) as [->|n2].
        + rewrite EI'. destruct (decide (fcol1 = fcol1)); [|congruence]. reflexivity.
        + destruct (decide (E x = fcol1)) as [e|e]; [exfalso; apply n2; rewrite <- e, IE'; reflexivity|].
          destruct (decide (E x = E col1)) as [e'|e']; [exfalso; apply n1, Einj, e'|reflexivity]. }
    assert (I' : forall y, lookup_default_id (insert fcol1 col1 (insert (E col1) (I fcol1) i1)) y = I (tau y)).
    { intros y; rewrite !lookup_default_id_insert; fold I; unfold tau.
      destruct (decide (y = fcol1)) as [->|n1]; [rewrite IE'; reflexivity|].
      destruct (decide (y = E col1)) as [->|n2]; reflexivity. }
    assert (TT : forall y, tau (tau y) = y).
    { intros y; unfold tau. destruct (decide (y = fcol1)) as [->|n1].
      - destruct (decide (E col1 = fcol1)) as [e|e]; [congruence|].
        destruct (decide (E col1 = E col1)); [reflexivity|congruence].
      - destruct (decide (y = E col1)) as [->|n2].
        + destruct (decide (fcol1 = fcol1)); [reflexivity|congruence].
        + destruct (decide (y = fcol1)); [congruence|]. destruct (decide (y = E col1)); [congruence|reflexivity]. }
    assert (Tid : forall y, y <> fcol1 -> y <> E col1 -> tau y = y).
    { intros y n1 n2; unfold tau; destruct (decide (y = fcol1)); [congruence|].
      destruct (decide (y = E col1)); [congruence|reflexivity]. }
    split; [split|]; [apply functional_extensionality; intros y; rewrite E', I', EI', TT; reflexivity
                     |apply functional_extensionality; intros x; rewrite E', I', TT, IE'; reflexivity|].
    split.
    { intros r Hr; rewrite E'. cbn [MEM] in Hr; apply orb_true_iff in Hr as [Hr|Hr].
      - apply bool_decide_spec in Hr; subst r. change (EL h colors) with col1. unfold tau.
        destruct (decide (E col1 = fcol1)) as [e|e]; [exact e|].
        destruct (decide (E col1 = E col1)); [reflexivity|congruence].
      - rewrite (Hc r Hr). apply Tid.
        + intros e. pose proof (phy_div2 r (Hp' r Hr)); pose proof (phy_div2 h Hph).
          unfold fcol1 in e. assert (r = h) by lia. subst r; apply (Hnot h Hr); reflexivity.
        + intros e. rewrite <- (Hc r Hr) in e. apply Einj in e. apply (Hnot r Hr e). }
    split.
    { intros Hk c; unfold id in *. rewrite E'.
      assert (Hk' : forall r, MEM r l -> (k <= EL r colors <-> k <= r / 2)).
      { intros r Hr; apply Hk; cbn [MEM]; rewrite Hr, orb_true_r; reflexivity. }
      specialize (H3 Hk').
      assert (Kh : k <= col1 <-> k <= fcol1).
      { apply Hk; cbn [MEM]; rewrite (proj2 (bool_decide_spec (h = h)) eq_refl); reflexivity. }
      assert (Kt : forall y, k <= tau y <-> k <= y).
      { intros y; unfold tau. specialize (H3 col1).
        destruct (decide (y = fcol1)) as [->|n1]; [tauto|].
        destruct (decide (y = E col1)) as [->|n2]; [tauto|reflexivity]. }
      rewrite Kt; apply H3. }
    split.
    { intros Hk c [Hkc Hcr]; rewrite E'.
      assert (Hk' : forall r, MEM r l -> r / 2 < k).
      { intros r Hr; apply Hk; cbn [MEM]; rewrite Hr, orb_true_r; reflexivity. }
      assert (Hcr' : forall r, MEM r l -> c <> EL r colors).
      { intros r Hr; apply Hcr; cbn [MEM]; rewrite Hr, orb_true_r; reflexivity. }
      assert (Hh : h / 2 < k) by (apply Hk; cbn [MEM]; rewrite (proj2 (bool_decide_spec (h = h)) eq_refl); reflexivity).
      assert (Hc1 : c <> col1) by (apply Hcr; cbn [MEM]; rewrite (proj2 (bool_decide_spec (h = h)) eq_refl); reflexivity).
      specialize (H4 Hk' c (conj Hkc Hcr')).
      rewrite Tid; [exact H4| |].
      - intros e; unfold fcol1 in e; lia.
      - intros e; apply Hc1, Einj, e. }
    { intros Hk c Hc'. rewrite E'.
      assert (Hk' : forall r, MEM r l -> k <= EL r colors /\ k <= r / 2).
      { intros r Hr; apply Hk; cbn [MEM]; rewrite Hr, orb_true_r; reflexivity. }
      assert (Hh : k <= col1 /\ k <= h / 2) by (apply Hk; cbn [MEM]; rewrite (proj2 (bool_decide_spec (h = h)) eq_refl); reflexivity).
      pose proof (H5 Hk' c Hc') as Ec. rewrite Ec. apply Tid.
      - unfold fcol1; lia.
      - intros e. rewrite <- Ec in e. apply Einj in e. lia. }
Qed.

Lemma MEM_rev {A} `{EqDecision A} (x : A) l : MEM x (REVERSE l) = MEM x l.
Proof.
  destruct (MEM x (REVERSE l)) eqn:E1, (MEM x l) eqn:E2; auto;
    [apply MEM_In in E1; rewrite <- in_rev in E1; apply MEM_In in E1; congruence
    |apply MEM_In in E2; rewrite in_rev in E2; apply MEM_In in E2; congruence].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "find_reg_exchange_correct" *)
Theorem find_reg_exchange_correct : forall l sth k,
  ALL_DISTINCT (MAP (fun r => EL r sth.(colors)) l) /\
  (forall r, MEM r l -> is_phy_var r) /\
  (forall r, MEM r l -> r < LENGTH sth.(colors)) ->
  exists exch invexch, find_reg_exchange l LN LN sth = (M_success (exch, invexch), sth) /\
  ((lookup_default_id exch ∘ lookup_default_id invexch) = (fun x => x) /\
   (lookup_default_id invexch ∘ lookup_default_id exch) = (fun x => x)) /\
  (forall r, MEM r l -> lookup_default_id exch (EL r sth.(colors)) = r DIV 2) /\
  ((forall r, MEM r l -> (k <= EL r sth.(colors) <-> k <= r DIV 2)) ->
    (forall c, id (k <= c <-> k <= lookup_default_id exch c))) /\
  ((forall r, MEM r l -> r DIV 2 < k) ->
    (forall c, k <= c /\ (forall r, MEM r l -> c <> EL r sth.(colors)) -> k <= lookup_default_id exch c)) /\
  ((forall r, MEM r l -> (k <= EL r sth.(colors) /\ k <= r DIV 2)) ->
    (forall c, c < k -> lookup_default_id exch c = c)).
Proof.
  intros l sth k (Hd & Hp & Hl).
  rewrite (find_reg_exchange_FOLDL l [] LN LN sth Hl), FOLDL_fold_left, <- fold_left_rev_right.
  destruct (fold_right (fun y x => find_reg_exchange_step (colors sth) y x) (LN, LN) (rev l)) as [exch invexch] eqn:E.
  exists exch, invexch; split; [reflexivity|].
  assert (H := find_reg_exchange_FOLDR_correct (REVERSE l) sth.(colors) exch invexch k).
  rewrite <- FOLDR_fold_right in E. setoid_rewrite MEM_rev in H. apply H.
  split; [|split; [exact Hp|symmetry; exact E]].
  unfold is_true in *; rewrite ALL_DISTINCT_NoDup in *. rewrite map_rev. apply NoDup_rev, Hd.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "MAP_colors_eq_lemma" *)
Theorem MAP_colors_eq_lemma : forall sth n f,
  n <= LENGTH sth.(colors) ->
  exists sthout, (M_success tt, sthout) = MAP_colors f n sth /\
  LENGTH sth.(colors) = LENGTH sthout.(colors) /\
  sthout.(int_beg) = sth.(int_beg) /\ sthout.(int_end) = sth.(int_end) /\
  (forall n', n' < n -> EL n' sthout.(colors) = f (EL n' sth.(colors))) /\
  (forall n', n <= n' -> EL n' sthout.(colors) = EL n' sth.(colors)).
Proof.
  intros sth n f; revert sth; induction n as [|n IH] using N.peano_ind; intros sth Hn.
  - exists sth; rewrite (proj1 (MAP_colors_def f 0)). repeat split; intros; first [lia|reflexivity].
  - rewrite (proj2 (MAP_colors_def f n)). msimp. rewrite colors_sub_eqn.
    destruct (N.ltb_spec n (LENGTH sth.(colors))); [|lia]. rewrite update_colors_eqn.
    destruct (N.ltb_spec n (LENGTH sth.(colors))); [|lia].
    set (sth' := {| colors := LUPDATE (f (EL n sth.(colors))) n sth.(colors); int_beg := sth.(int_beg);
                    int_end := sth.(int_end); sorted_regs := sth.(sorted_regs); sorted_moves := sth.(sorted_moves) |}).
    assert (Ln : LENGTH sth'.(colors) = LENGTH sth.(colors)) by apply LENGTH_LUPDATE.
    destruct (IH sth' ltac:(lia)) as (so & E & L & B & En & Lt & Ge).
    exists so. split; [exact E|]. cbn [sth' int_beg int_end colors] in *.
    split; [lia|split; [exact B|split; [exact En|split]]].
    + intros n' Hn'. destruct (N.eq_dec n' n) as [->|Hne].
      * rewrite Ge by lia. apply EL_LUPDATE_same; lia.
      * rewrite Lt by lia. rewrite EL_LUPDATE_other by exact Hne. reflexivity.
    + intros n' Hn'. rewrite Ge by lia. apply EL_LUPDATE_other; lia.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "MAP_colors_eq" *)
Theorem MAP_colors_eq : forall sth f,
  exists sthout, (M_success tt, sthout) = MAP_colors f (LENGTH sth.(colors)) sth /\
  (forall n, n < LENGTH sth.(colors) -> EL n sthout.(colors) = f (EL n sth.(colors))) /\
  LENGTH sth.(colors) = LENGTH sthout.(colors) /\
  sthout.(int_beg) = sth.(int_beg) /\ sthout.(int_end) = sth.(int_end).
Proof.
  intros sth f; destruct (MAP_colors_eq_lemma sth (LENGTH sth.(colors)) f ltac:(lia)) as (so & E & L & B & En & Lt & _).
  exists so; repeat split; auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "apply_reg_exchange_correct" *)
Theorem apply_reg_exchange_correct : forall l sth k,
  ALL_DISTINCT (MAP (fun r => EL r sth.(colors)) l) /\
  (forall r, MEM r l -> is_phy_var r) /\
  (forall r, MEM r l -> r < LENGTH sth.(colors)) ->
  exists sthout, (M_success tt, sthout) = apply_reg_exchange l sth /\
  LENGTH sthout.(colors) = LENGTH sth.(colors) /\
  sthout.(int_beg) = sth.(int_beg) /\ sthout.(int_end) = sth.(int_end) /\
  (forall r1 r2, r1 < LENGTH sth.(colors) /\ r2 < LENGTH sth.(colors) ->
     EL r1 sthout.(colors) = EL r2 sthout.(colors) -> EL r1 sth.(colors) = EL r2 sth.(colors)) /\
  (forall r, MEM r l -> EL r sthout.(colors) = r DIV 2) /\
  ((forall r, MEM r l -> (k <= EL r sth.(colors) <-> k <= r DIV 2)) ->
    (forall r, r < LENGTH sth.(colors) -> (k <= EL r sth.(colors) <-> k <= EL r sthout.(colors)))) /\
  ((forall r, MEM r l -> r DIV 2 < k) ->
    (forall r, r < LENGTH sth.(colors) /\ k <= EL r sth.(colors) /\
       (forall r', MEM r' l -> EL r sth.(colors) <> EL r' sth.(colors)) -> k <= EL r sthout.(colors))) /\
  ((forall r, MEM r l -> (k <= EL r sth.(colors) /\ k <= r DIV 2)) ->
    (forall r, r < LENGTH sth.(colors) /\ EL r sth.(colors) < k -> EL r sthout.(colors) = EL r sth.(colors))).
Proof.
  intros l sth k H. pose proof H as (Hd & Hp & Hl).
  destruct (find_reg_exchange_correct l sth k H) as (exch & invexch & Ef & (EI & IE) & Hc & H3 & H4 & H5).
  unfold apply_reg_exchange; msimp. rewrite Ef. cbn beta iota.
  unfold colors_length, Marray_length.
  destruct (MAP_colors_eq sth (lookup_default_id exch)) as (so & E & Hel & L & B & En).
  exists so. split; [exact E|]. split; [lia|split; [exact B|split; [exact En|]]].
  split.
  { intros r1 r2 [H1 H2] Heq. rewrite !Hel in Heq by assumption.
    apply (f_equal (lookup_default_id invexch)) in Heq.
    rewrite (equal_f IE (EL r1 _)), (equal_f IE (EL r2 _)) in Heq; exact Heq. }
  split; [intros r Hr; rewrite Hel by (apply Hl, Hr); apply Hc, Hr|].
  split.
  { intros Hk r Hr; rewrite Hel by exact Hr. exact (H3 Hk (EL r sth.(colors))). }
  split.
  { intros Hk r (Hr & Hkr & Hne); rewrite Hel by exact Hr. apply H4; [exact Hk|]. split; [exact Hkr|].
    intros r' Hr'; apply Hne, Hr'. }
  { intros Hk r (Hr & Hlt); rewrite Hel by exact Hr. apply H5; assumption. }
Qed.

(** ** The state invariant *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "less_FST_def" *)
Definition less_FST (x y : Z * N) : Prop := (FST x <= FST y)%Z.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "transitive_less_FST" *)
Theorem transitive_less_FST : transitive less_FST.
Proof. unfold transitive, less_FST; intros x y z [H1 H2]; lia. Qed.

(** HOL's set-builder [{EL r sth.colors | r | P r}] is the predicate
    [fun c => exists r, c = EL r sth.(colors) /\ P r]. *)
(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "good_linear_scan_state_def" *)
Definition good_linear_scan_state (st : linear_scan_state) (sth : linear_scan_hidden_state) (l : list N)
    (pos : Z) (forced : list (N * N)) (mincol : N) : Prop :=
  LENGTH sth.(int_beg) = LENGTH sth.(colors) /\ LENGTH sth.(int_end) = LENGTH sth.(colors) /\
  ALL_DISTINCT (st.(colorpool) ++ MAP (fun '(e, r) => EL r sth.(colors)) st.(active)) /\
  EVERY (fun r => r <? LENGTH sth.(colors)) l /\
  EVERY (fun r => EL r sth.(colors) <? st.(stacknum)) l /\
  domain st.(phyregs) = (fun c => exists r, c = EL r sth.(colors) /\
    (MEM r l /\ is_phy_var r /\ EL r sth.(colors) < st.(colormax))) /\
  ALL_DISTINCT (MAP (fun r => EL r sth.(colors)) (FILTER is_phy_var l)) /\
  EVERY (fun c => c <? st.(colornum)) st.(colorpool) /\
  EVERY (fun '(e, r) => EL r sth.(colors) <? st.(colornum)) st.(active) /\
  st.(colornum) <= st.(colormax) /\
  st.(colormax) <= st.(stacknum) /\
  EVERY (fun r => implb (EL r sth.(colors) <? st.(colormax)) (EL r sth.(colors) <? st.(colornum))) l /\
  EVERY (fun r => (EL r sth.(int_beg) <=? pos)%Z) l /\
  EVERY (fun r => implb ((pos <=? EL r sth.(int_end))%Z && (EL r sth.(colors) <? st.(colormax)))
                        (MEM (EL r sth.(int_end), r) st.(active))) l /\
  EVERY (fun r => implb (MEM (EL r sth.(int_end), r) st.(active)) (pos <=? 1 + EL r sth.(int_end))%Z) l /\
  (forall r1 r2, MEM r1 l /\ MEM r2 l /\
     interval_intersect (EL r1 sth.(int_beg), EL r1 sth.(int_end)) (EL r2 sth.(int_beg), EL r2 sth.(int_end)) /\
     EL r1 sth.(colors) = EL r2 sth.(colors) -> r1 = r2) /\
  SORTED less_FST st.(active) /\
  EVERY (fun '(e, r) => (e =? EL r sth.(int_end))%Z) st.(active) /\
  EVERY (fun '(e, r) => MEM r l) st.(active) /\
  EVERY (fun '(r1, r2) => implb (MEM r1 l && MEM r2 l && (EL r1 sth.(colors) =? EL r2 sth.(colors))) (r1 =? r2))
    forced /\
  mincol <= st.(colornum) /\
  EVERY (fun c => mincol <=? c) (st.(colorpool) ++ MAP (fun r => EL r sth.(colors)) l).

(** The invariant with every component stated propositionally (Galette
    helper). *)
Record gls (st : linear_scan_state) (sth : linear_scan_hidden_state) (l : list N)
    (pos : Z) (forced : list (N * N)) (mincol : N) : Prop := {
  g_len_beg : LENGTH sth.(int_beg) = LENGTH sth.(colors);
  g_len_end : LENGTH sth.(int_end) = LENGTH sth.(colors);
  g_distinct : NoDup (st.(colorpool) ++ List.map (fun '(e, r) => EL r sth.(colors)) st.(active));
  g_lt : forall r, In r l -> r < LENGTH sth.(colors);
  g_stack : forall r, In r l -> EL r sth.(colors) < st.(stacknum);
  g_phyregs : forall c, domain st.(phyregs) c <->
    exists r, c = EL r sth.(colors) /\ In r l /\ is_phy_var r /\ EL r sth.(colors) < st.(colormax);
  g_phydistinct : NoDup (List.map (fun r => EL r sth.(colors)) (List.filter is_phy_var l));
  g_pool : forall c, In c st.(colorpool) -> c < st.(colornum);
  g_active_col : forall e r, In (e, r) st.(active) -> EL r sth.(colors) < st.(colornum);
  g_num_max : st.(colornum) <= st.(colormax);
  g_max_stack : st.(colormax) <= st.(stacknum);
  g_maxnum : forall r, In r l -> EL r sth.(colors) < st.(colormax) -> EL r sth.(colors) < st.(colornum);
  g_beg : forall r, In r l -> (EL r sth.(int_beg) <= pos)%Z;
  g_active_in : forall r, In r l -> (pos <= EL r sth.(int_end))%Z -> EL r sth.(colors) < st.(colormax) ->
    In (EL r sth.(int_end), r) st.(active);
  g_active_pos : forall r, In r l -> In (EL r sth.(int_end), r) st.(active) -> (pos <= 1 + EL r sth.(int_end))%Z;
  g_inj : forall r1 r2, In r1 l -> In r2 l ->
    interval_intersect (EL r1 sth.(int_beg), EL r1 sth.(int_end)) (EL r2 sth.(int_beg), EL r2 sth.(int_end)) ->
    EL r1 sth.(colors) = EL r2 sth.(colors) -> r1 = r2;
  g_sorted : SORTED less_FST st.(active);
  g_active_end : forall e r, In (e, r) st.(active) -> e = EL r sth.(int_end);
  g_active_l : forall e r, In (e, r) st.(active) -> In r l;
  g_forced : forall r1 r2, In (r1, r2) forced -> In r1 l -> In r2 l ->
    EL r1 sth.(colors) = EL r2 sth.(colors) -> r1 = r2;
  g_mincol : mincol <= st.(colornum);
  g_mincol_pool : forall c, In c st.(colorpool) -> mincol <= c;
  g_mincol_l : forall r, In r l -> mincol <= EL r sth.(colors)
}.

Lemma implb_iff (a b : bool) : implb a b = true <-> (a = true -> b = true).
Proof. destruct a, b; cbn; intuition congruence. Qed.

Lemma gls_iff st sth l pos forced mincol :
  good_linear_scan_state st sth l pos forced mincol <-> gls st sth l pos forced mincol.
Proof.
  unfold good_linear_scan_state, is_true.
  rewrite !ALL_DISTINCT_NoDup, !EVERY_Forall, !Forall_forall.
  split.
  - intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 &
            H18 & H19 & H20 & H21 & H22).
    constructor; try assumption.
    + intros r Hr; apply N.ltb_lt, H4, Hr.
    + intros r Hr; apply N.ltb_lt, H5, Hr.
    + intros c; rewrite H6. split; intros (r & -> & Hr & Hp & Hc); exists r; repeat split; auto;
        apply MEM_iff; auto.
    + intros c Hc; apply N.ltb_lt, H8, Hc.
    + intros e r Hr; apply N.ltb_lt, (H9 _ Hr).
    + intros r Hr Hc; specialize (H12 r Hr); rewrite implb_iff, !N.ltb_lt in H12; auto.
    + intros r Hr; apply Z.leb_le, H13, Hr.
    + intros r Hr Hp Hc; specialize (H14 r Hr); rewrite implb_iff, andb_true_iff, Z.leb_le, N.ltb_lt in H14.
      apply MEM_iff, H14; auto.
    + intros r Hr Ha; specialize (H15 r Hr); rewrite implb_iff, Z.leb_le in H15; apply H15, MEM_iff, Ha.
    + intros r1 r2 Hr1 Hr2 Hi He; apply H16; repeat split; auto; apply MEM_iff; auto.
    + intros e r Hr; apply Z.eqb_eq, (H18 _ Hr).
    + intros e r Hr; apply MEM_iff, (H19 _ Hr).
    + intros r1 r2 Hf Hr1 Hr2 He; specialize (H20 _ Hf); cbn beta iota in H20.
      rewrite implb_iff, !andb_true_iff, N.eqb_eq, N.eqb_eq in H20. apply H20; repeat split; auto; apply MEM_iff; auto.
    + intros c Hc; apply N.leb_le, H22, in_or_app; auto.
    + intros r Hr; apply N.leb_le, H22, in_or_app; right; apply (in_map (fun r => EL r sth.(colors))), Hr.
  - intros G; destruct G.
    repeat split; try assumption.
    + intros r Hr; apply N.ltb_lt; auto.
    + intros r Hr; apply N.ltb_lt; auto.
    + apply set_ext; intros c; rewrite g_phyregs0. split; intros (r & -> & Hr & Hp & Hc); exists r; repeat split; auto;
        apply MEM_iff; auto.
    + intros c Hc; apply N.ltb_lt; auto.
    + intros [e r] Hr; apply N.ltb_lt; eauto.
    + intros r Hr; rewrite implb_iff, !N.ltb_lt; auto.
    + intros r Hr; apply Z.leb_le; auto.
    + intros r Hr; rewrite implb_iff, andb_true_iff, Z.leb_le, N.ltb_lt; intros [Hp Hc]; apply MEM_iff; auto.
    + intros r Hr; rewrite implb_iff, Z.leb_le; intros Ha; apply MEM_iff in Ha; auto.
    + intros r1 r2 (Hr1 & Hr2 & Hi & He); apply MEM_iff in Hr1, Hr2; auto.
    + intros [e r] Hr; apply Z.eqb_eq; eauto.
    + intros [e r] Hr; apply MEM_iff; eauto.
    + intros [r1 r2] Hf; rewrite implb_iff, !andb_true_iff, !N.eqb_eq; intros ((Hr1 & Hr2) & He).
      apply MEM_iff in Hr1, Hr2; eauto.
    + intros c Hc; apply in_app_or in Hc as [Hc|Hc]; apply N.leb_le; auto.
      apply in_map_iff in Hc as (r & <- & Hr); auto.
Qed.

Lemma In_cons_iff {A} (x y : A) l : In x (y :: l) <-> y = x \/ In x l.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "remove_inactive_intervals_invariants" *)
Theorem remove_inactive_intervals_invariants : forall beg st sth l pos forced mincol,
  good_linear_scan_state st sth l pos forced mincol /\
  (pos <= beg)%Z ->
  exists stout, (M_success stout, sth) = remove_inactive_intervals beg st sth /\
  good_linear_scan_state stout sth l beg forced mincol /\
  stout.(colormax) = st.(colormax).
Proof.
  intros beg st sth l pos forced mincol [G Hpb]; apply gls_iff in G.
  setoid_rewrite gls_iff. unfold remove_inactive_intervals.
  remember (active st) as act eqn:Ha. revert st pos Ha G Hpb.
  induction act as [|[e r] tl IH]; intros st pos Ha G Hpb; cbn [remove_inactive_intervals_aux].
  - exists st; split; [reflexivity|]; split; [|reflexivity].
    destruct G; constructor; auto.
    + intros r Hr; specialize (g_beg0 r Hr); lia.
    + intros r Hr Hb Hc; apply g_active_in0; auto; lia.
    + intros r Hr Ha'; rewrite <- Ha in Ha'; destruct Ha'.
  - assert (Hin : In (e, r) (active st)) by (rewrite <- Ha; left; reflexivity).
    assert (Hs := g_sorted _ _ _ _ _ _ G); rewrite <- Ha in Hs.
    apply (SORTED_EQ _ _ _ transitive_less_FST) in Hs as [Hs Hhd].
    assert (Ee : e = EL r sth.(int_end)) by (eapply g_active_end; eauto).
    destruct (Z.ltb_spec e beg) as [Hlt|Hge].
    + msimp. rewrite colors_sub_eqn.
      assert (Hr : r < LENGTH sth.(colors)) by (eapply g_lt; [exact G|]; eapply g_active_l; eauto).
      destruct (N.ltb_spec r (LENGTH sth.(colors))); [|lia].
      set (col := EL r sth.(colors)).
      set (st' := {| active := tl; colorpool := col :: colorpool st; phyregs := phyregs st;
                     colornum := colornum st; colormax := colormax st; stacknum := stacknum st |}).
      assert (Hrl : In r l) by (eapply g_active_l; eauto).
      assert (Hpe : (pos <= 1 + e)%Z) by (rewrite Ee; eapply g_active_pos; eauto; rewrite <- Ee; exact Hin).
      assert (G' : gls st' sth l (e + 1) forced mincol).
      { destruct G; constructor; cbn [st' active colorpool phyregs colornum colormax stacknum]; auto.
        - rewrite <- Ha in g_distinct0; cbn [List.map] in g_distinct0.
          refine (Permutation_NoDup _ g_distinct0). symmetry; apply Permutation_middle.
        - intros c [<-|Hc]; [eapply g_active_col0; eauto|auto].
        - intros e' r' Hr'; eapply g_active_col0; rewrite <- Ha; right; exact Hr'.
        - intros r' Hr'; specialize (g_beg0 r' Hr'); lia.
        - intros r' Hr' Hb Hc. assert (In (EL r' sth.(int_end), r') (active st)) as Hx by (apply g_active_in0; auto; lia).
          rewrite <- Ha in Hx; destruct Hx as [Hx|Hx]; [inversion Hx; subst; lia|exact Hx].
        - intros r' Hr' Hx. specialize (Hhd _ Hx); unfold less_FST in Hhd; cbn [FST fst] in Hhd; lia.
        - intros e' r' Hx; apply g_active_end0; rewrite <- Ha; right; exact Hx.
        - intros e' r' Hx; eapply g_active_l0; rewrite <- Ha; right; exact Hx.
        - intros c [<-|Hc]; [apply g_mincol_l0, Hrl|auto]. }
      destruct (IH st' (e + 1)%Z eq_refl G' ltac:(lia)) as (so & E & G'' & M).
      exists so; split; [exact E|split; [exact G''|exact M]].
    + exists st; split; [reflexivity|]; split; [|reflexivity].
      destruct G; constructor; auto.
      * intros r' Hr'; specialize (g_beg0 r' Hr'); lia.
      * intros r' Hr' Hb Hc; apply g_active_in0; auto; lia.
      * intros r' Hr' Hx. rewrite <- Ha in Hx; destruct Hx as [Hx|Hx].
        -- inversion Hx; subst. lia.
        -- specialize (Hhd _ Hx); unfold less_FST in Hhd; cbn [FST fst] in Hhd; lia.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "add_active_interval_output" *)
Theorem add_active_interval_output : forall {A} lin (x : A) lout e r,
  SORTED less_FST lin /\
  lout = add_active_interval (e, r) lin ->
  SORTED less_FST lout /\
  exists l1 l2, lin = l1 ++ l2 /\ lout = l1 ++ (e, r) :: l2.
Proof.
  intros A lin x lout e r [Hs ->]. induction lin as [|h lin IH]; cbn [add_active_interval].
  - split; [exact I|exists [], []; split; reflexivity].
  - cbn [FST fst]. destruct (Z.leb_spec e (fst h)) as [Hle|Hgt].
    + split; [|exists [], (h :: lin); split; reflexivity].
      apply (SORTED_EQ _ _ _ transitive_less_FST); split; [exact Hs|].
      apply (SORTED_EQ _ _ _ transitive_less_FST) in Hs as [_ Hh].
      intros y [<-|Hy]; unfold less_FST; cbn [FST]; [lia|specialize (Hh _ Hy); unfold less_FST in Hh; lia].
    + apply (SORTED_EQ _ _ _ transitive_less_FST) in Hs as [Hs Hh].
      destruct (IH Hs) as [Hs' (l1 & l2 & E1 & E2)].
      split.
      * apply (SORTED_EQ _ _ _ transitive_less_FST); split; [exact Hs'|].
        rewrite E2; intros y Hy; apply in_app_or in Hy as [Hy|[<-|Hy]];
          [apply Hh; rewrite E1; apply in_or_app; auto|unfold less_FST; cbn [FST]; lia
          |apply Hh; rewrite E1; apply in_or_app; auto].
      * exists (h :: l1), l2; rewrite E2, E1; split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "find_color_in_list_output" *)
Theorem find_color_in_list_output : forall forbidden col l rest,
  find_color_in_list l forbidden = Some (col, rest) ->
  MEM col l /\ col NOTIN domain forbidden /\
  exists l1 l2, rest = l1 ++ l2 /\ l = l1 ++ col :: l2.
Proof.
  intros forbidden col l; induction l as [|h l IH]; intros rest H; cbn [find_color_in_list] in H; [discriminate|].
  destruct (bool_decide (lookup h forbidden = None)) eqn:B.
  - apply bool_decide_spec in B. injection H as Hc Hr; subst col rest.
    split; [cbn [MEM]; rewrite (proj2 (bool_decide_spec (h = h)) eq_refl); reflexivity|].
    split; [apply notdom_lookup, B|]. exists [], l; split; reflexivity.
  - destruct (find_color_in_list l forbidden) as [[c r]|] eqn:E; [|discriminate].
    injection H as Hc Hr; subst c rest.
    destruct (IH r eq_refl) as (Hm & Hn & l1 & l2 & -> & ->).
    split; [cbn [MEM]; rewrite Hm, orb_true_r; reflexivity|split; [exact Hn|]].
    exists (h :: l1), l2; split; reflexivity.
Qed.

(** HOL's record updates of [linear_scan_state] (Galette helpers). *)
Definition set_active (st : linear_scan_state) a : linear_scan_state :=
  {| active := a; colorpool := st.(colorpool); phyregs := st.(phyregs); colornum := st.(colornum);
     colormax := st.(colormax); stacknum := st.(stacknum) |}.
Definition set_colorpool (st : linear_scan_state) c : linear_scan_state :=
  {| active := st.(active); colorpool := c; phyregs := st.(phyregs); colornum := st.(colornum);
     colormax := st.(colormax); stacknum := st.(stacknum) |}.
Definition set_colornum (st : linear_scan_state) n : linear_scan_state :=
  {| active := st.(active); colorpool := st.(colorpool); phyregs := st.(phyregs); colornum := n;
     colormax := st.(colormax); stacknum := st.(stacknum) |}.

Lemma gls_perm_pool st sth l pos forced mincol cp :
  gls st sth l pos forced mincol -> Permutation st.(colorpool) cp ->
  gls (set_colorpool st cp) sth l pos forced mincol.
Proof.
  intros G P; destruct G; constructor; cbn [set_colorpool active colorpool phyregs colornum colormax stacknum]; auto.
  - eapply Permutation_NoDup; [|exact g_distinct0]. apply Permutation_app_tail, P.
  - intros c Hc; apply g_pool0. eapply Permutation_in; [symmetry; exact P|exact Hc].
  - intros c Hc; apply g_mincol_pool0. eapply Permutation_in; [symmetry; exact P|exact Hc].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "find_color_in_colornum_invariants" *)
Theorem find_color_in_colornum_invariants : forall st forbidden sth l pos forced mincol stout col,
  good_linear_scan_state st sth l pos forced mincol /\
  domain forbidden SUBSET (fun c => exists r, c = EL r sth.(colors) /\ MEM r l) /\
  find_color_in_colornum st forbidden = (stout, Some col) ->
  good_linear_scan_state (set_colorpool stout (col :: stout.(colorpool))) sth l pos forced mincol /\
  st.(colornum) <= col /\ col < stout.(colornum) /\
  st.(colornum) <= stout.(colornum) /\
  col NOTIN domain forbidden /\
  st = set_colornum (set_colorpool stout st.(colorpool)) st.(colornum).
Proof.
  intros st forbidden sth l pos forced mincol stout col (G & Hs & Hf); apply gls_iff in G.
  unfold find_color_in_colornum in Hf. destruct (N.leb_spec (colormax st) (colornum st)) as [Hle|Hlt]; [discriminate|].
  injection Hf as <- <-. cbn [colornum colorpool].
  split; [|split; [lia|split; [lia|split; [lia|split]]]].
  - apply gls_iff. destruct G; constructor; cbn [set_colorpool active colorpool phyregs colornum colormax stacknum]; auto.
    + constructor; [|exact g_distinct0]. intros Hin; apply in_app_or in Hin as [Hin|Hin].
      * specialize (g_pool0 _ Hin); lia.
      * apply in_map_iff in Hin as ([e r] & E & Hr). specialize (g_active_col0 _ _ Hr); lia.
    + intros c [<-|Hc]; [lia|specialize (g_pool0 c Hc); lia].
    + intros e r Hr; specialize (g_active_col0 _ _ Hr); lia.
    + lia.
    + intros r Hr Hc; specialize (g_maxnum0 r Hr Hc); lia.
    + lia.
    + intros c [<-|Hc]; [lia|auto].
  - intros Hin. destruct (Hs _ Hin) as (r & E & Hr). apply MEM_iff in Hr. destruct G.
    specialize (g_maxnum0 r Hr ltac:(lia)); lia.
  - destruct st; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "find_color_invariants" *)
Theorem find_color_invariants : forall st forbidden stout col sth l pos forced mincol,
  good_linear_scan_state st sth l pos forced mincol /\
  domain forbidden SUBSET (fun c => exists r, c = EL r sth.(colors) /\ MEM r l) /\
  find_color st forbidden = (stout, Some col) ->
  good_linear_scan_state (set_colorpool stout (col :: stout.(colorpool))) sth l pos forced mincol /\
  col < stout.(colornum) /\
  col NOTIN domain forbidden /\
  st = set_colornum (set_colorpool stout st.(colorpool)) st.(colornum).
Proof.
  intros st forbidden stout col sth l pos forced mincol (G & Hs & Hf).
  unfold find_color in Hf. destruct (find_color_in_list (colorpool st) forbidden) as [[c rest]|] eqn:E.
  - injection Hf as <- <-. destruct (find_color_in_list_output _ _ _ _ E) as (Hm & Hn & l1 & l2 & -> & Ep).
    apply gls_iff in G. split; [|split; [|split; [exact Hn|destruct st; cbn in *; reflexivity]]].
    + apply gls_iff. assert (P : Permutation (colorpool st) (c :: l1 ++ l2)).
      { rewrite Ep; symmetry; apply Permutation_middle. }
      pose proof (gls_perm_pool _ _ _ _ _ _ _ G P) as G'. destruct st; exact G'.
    + cbn. apply (g_pool _ _ _ _ _ _ G). apply MEM_iff, Hm.
  - destruct (find_color_in_colornum_invariants st forbidden sth l pos forced mincol stout col (conj G (conj Hs Hf)))
      as (G' & _ & H2 & _ & H4 & H5). auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "update_color_active_colors_same" *)
Theorem update_color_active_colors_same : forall {A B C} `{Inhabited B} (e : C) reg (active : list (A * N))
    (regcol : B) colors,
  MAP (fun '(e, r) => EL r (LUPDATE regcol reg colors)) (FILTER (fun '(e, r) => negb (r =? reg)) active) =
  MAP (fun '(e, r) => EL r colors) (FILTER (fun '(e, r) => negb (r =? reg)) active).
Proof.
  intros A B C IB e reg active regcol colors; induction active as [|[e' r] tl IH]; [reflexivity|].
  cbn [FILTER List.filter]. destruct (N.eqb_spec r reg); cbn [negb]; [exact IH|].
  cbn [MAP List.map]; rewrite IH, EL_LUPDATE_other by assumption; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "forced_update_stack_color_lemma" *)
Theorem forced_update_stack_color_lemma : forall (colors : list N) (stacknum : N) l r2 r1,
  EVERY (fun r => EL r colors <? stacknum) l /\
  MEM r2 l /\
  r1 < LENGTH colors /\
  EL r1 (LUPDATE stacknum r1 colors) = EL r2 (LUPDATE stacknum r1 colors) ->
  r1 = r2.
Proof.
  intros colors stacknum l r2 r1 (Hl & Hm & Hr & He).
  destruct (N.eq_dec r2 r1) as [->|Hne]; [reflexivity|].
  rewrite EL_LUPDATE_same in He by exact Hr. rewrite EL_LUPDATE_other in He by exact Hne.
  apply EVERY_iff with (x := r2) in Hl; [|apply MEM_iff, Hm]. apply N.ltb_lt in Hl. lia.
Qed.

(** "TODO: this should be part of the standard library, but I couldn't find it" *)
(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "IS_SPARSE_SUBLIST_def" *)
Fixpoint IS_SPARSE_SUBLIST {A} (l1 l2 : list A) {struct l2} : Prop :=
  match l1, l2 with
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => (x = y /\ IS_SPARSE_SUBLIST xs ys) \/ IS_SPARSE_SUBLIST (x :: xs) ys
  end.

Lemma ISS_nil {A} (l : list A) : IS_SPARSE_SUBLIST [] l.
Proof. destruct l; exact I. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "FILTER_IS_SPARSE_SUBLIST" *)
Theorem FILTER_IS_SPARSE_SUBLIST : forall {A} l (P : A -> bool), IS_SPARSE_SUBLIST (FILTER P l) l.
Proof.
  intros A l P; induction l as [|x l IH]; [exact I|]. cbn [FILTER List.filter].
  destruct (P x).
  - cbn; left; split; [reflexivity|exact IH].
  - destruct (List.filter P l) as [|y fl] eqn:E; [apply ISS_nil|]. cbn; right; exact IH.
Qed.

Lemma ISS_In {A} (l1 l2 : list A) x : IS_SPARSE_SUBLIST l1 l2 -> In x l1 -> In x l2.
Proof.
  revert l1; induction l2 as [|y l2 IH]; intros [|z l1] H Hx; cbn in *; try tauto.
  destruct H as [[-> H]|H].
  - destruct Hx as [->|Hx]; [left; reflexivity|right; eapply IH; eauto].
  - right; eapply IH; [exact H|exact Hx].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "MEM_SPARSE_SUBLIST" *)
Theorem MEM_SPARSE_SUBLIST : forall {A} `{EqDecision A} (l1 l2 : list A) x,
  IS_SPARSE_SUBLIST l1 l2 /\ MEM x l1 -> MEM x l2.
Proof. intros A EA l1 l2 x [H Hx]; apply MEM_iff in Hx; apply MEM_iff; eapply ISS_In; eauto. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "IS_SPARSE_SUBLIST_APPEND_LEFT" *)
Theorem IS_SPARSE_SUBLIST_APPEND_LEFT : forall {A} (l1 l2 l : list A),
  IS_SPARSE_SUBLIST l1 l2 -> IS_SPARSE_SUBLIST (l ++ l1) (l ++ l2).
Proof. intros A l1 l2 l H; induction l as [|x l IH]; [exact H|]. cbn; left; split; [reflexivity|exact IH]. Qed.

Lemma ISS_cons_r {A} (l1 l2 : list A) y : IS_SPARSE_SUBLIST l1 l2 -> IS_SPARSE_SUBLIST l1 (y :: l2).
Proof. destruct l1; [intros; exact I|intros H; right; exact H]. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "IS_SPARSE_SUBLIST_APPEND_RIGHT" *)
Theorem IS_SPARSE_SUBLIST_APPEND_RIGHT : forall {A} (l1 l2 l : list A),
  IS_SPARSE_SUBLIST l1 l2 -> IS_SPARSE_SUBLIST (l1 ++ l) (l2 ++ l).
Proof.
  intros A l1 l2 l; revert l1; induction l2 as [|y l2 IH]; intros l1 H.
  - destruct l1; [|destruct H]. cbn. clear. induction l as [|x l IH]; [exact I|]. cbn; left; auto.
  - destruct l1 as [|x l1].
    + cbn [app]. specialize (IH [] (ISS_nil _)). cbn [app] in IH. apply ISS_cons_r, IH.
    + cbn in H |- *. destruct H as [[-> H]|H]; [left; split; [reflexivity|apply IH, H]|right].
      exact (IH (x :: l1) H).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "MAP_IS_SPARSE_SUBLIST" *)
Theorem MAP_IS_SPARSE_SUBLIST : forall {A B} (l1 l2 : list A) (f : A -> B),
  IS_SPARSE_SUBLIST l1 l2 -> IS_SPARSE_SUBLIST (MAP f l1) (MAP f l2).
Proof.
  intros A B l1 l2 f; revert l1; induction l2 as [|y l2 IH]; intros [|x l1] H; cbn in *; try tauto; try apply ISS_nil.
  destruct H as [[-> H]|H]; [left; split; [reflexivity|apply IH, H]|right; exact (IH (x :: l1) H)].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "ALL_DISTINCT_IS_SPARSE_SUBLIST" *)
Theorem ALL_DISTINCT_IS_SPARSE_SUBLIST : forall {A} `{EqDecision A} (l1 l2 : list A),
  ALL_DISTINCT l2 /\ IS_SPARSE_SUBLIST l1 l2 -> ALL_DISTINCT l1.
Proof.
  intros A EA l1 l2 [Hd H]. apply ALL_DISTINCT_iff in Hd; apply ALL_DISTINCT_iff.
  revert l1 Hd H; induction l2 as [|y l2 IH]; intros l1 Hd H.
  - destruct l1; [constructor|destruct H].
  - destruct l1 as [|x l1]; [constructor|]. cbn in H.
  inversion Hd as [|? ? Hn Hd']; subst. destruct H as [[-> H]|H].
  + constructor; [intros Hx; apply Hn; eapply ISS_In; eauto|apply IH; auto].
  + exact (IH (x :: l1) Hd' H).
Qed.

Lemma In_tl {A} (x y : A) l : In x (y :: l) -> x <> y -> In x l.
Proof. intros [->|H] Hn; [congruence|exact H]. Qed.

Lemma NoDup_app_disj {A} (l1 l2 : list A) x : NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|y l1 IH]; intros D H1 H2; [destruct H1|]. inversion D as [|? ? Hn D']; subst.
  destruct H1 as [->|H1]; [apply Hn, in_or_app; auto|eauto].
Qed.

Lemma ISS_NoDup {A} (l1 l2 : list A) : IS_SPARSE_SUBLIST l1 l2 -> NoDup l2 -> NoDup l1.
Proof.
  revert l1; induction l2 as [|y l2 IH]; intros l1 H Hd.
  - destruct l1; [constructor|destruct H].
  - destruct l1 as [|x l1]; [constructor|]. cbn in H.
    inversion Hd as [|? ? Hn Hd']; subst. destruct H as [[-> H]|H].
    + constructor; [intros Hx; apply Hn; eapply ISS_In; eauto|apply IH; auto].
    + exact (IH (x :: l1) H Hd').
Qed.

Lemma SORTED_filter {A} (R : A -> A -> Prop) (p : A -> bool) l :
  transitive R -> SORTED R l -> SORTED R (List.filter p l).
Proof.
  intros T; induction l as [|x l IH]; [intros; exact I|]. intros Hs.
  apply (SORTED_EQ _ _ _ T) in Hs as [Hs Hh]. cbn [List.filter]. destruct (p x); [|apply IH, Hs].
  apply (SORTED_EQ _ _ _ T); split; [apply IH, Hs|]. intros y Hy; apply filter_In in Hy as [Hy _]; auto.
Qed.

Lemma EL_LUPDATE_dec {A} `{Inhabited A} (x : A) n l i :
  n < LENGTH l -> EL i (LUPDATE x n l) = if decide (i = n) then x else EL i l.
Proof.
  intros Hn; destruct (decide (i = n)) as [->|Hne]; [apply EL_LUPDATE_same, Hn|apply EL_LUPDATE_other, Hne].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "spill_register_FILTER_invariants_hidden" *)
Theorem spill_register_FILTER_invariants_hidden : forall st sth l pos forced reg mincol,
  id (~ is_phy_var reg \/ ~ MEM reg l) /\
  good_linear_scan_state st sth l pos forced mincol /\
  reg < LENGTH sth.(colors) /\
  (EL reg sth.(int_beg) <= pos)%Z ->
  exists stout sthout,
    (M_success stout, sthout) =
      spill_register (set_active st (FILTER (fun '(e, r) => negb (r =? reg)) st.(active))) reg sth /\
    good_linear_scan_state stout sthout (reg :: l) pos forced mincol /\
    LENGTH sthout.(colors) = LENGTH sth.(colors) /\
    (forall r, r <> reg -> EL r sth.(colors) = EL r sthout.(colors)) /\
    stout.(colormax) = st.(colormax) /\
    sthout.(int_beg) = sth.(int_beg) /\ sthout.(int_end) = sth.(int_end) /\
    st.(colormax) <= EL reg sthout.(colors).
Proof.
  intros st sth l pos forced reg mincol (Hid & G & Hr & Hb). unfold id in Hid. apply gls_iff in G.
  unfold spill_register; msimp. rewrite update_colors_eqn. destruct (N.ltb_spec reg (LENGTH sth.(colors))); [|lia].
  cbn [set_active active colorpool phyregs colornum colormax stacknum].
  set (cs := LUPDATE (stacknum st) reg (colors sth)).
  assert (ELU : forall r, EL r cs = if decide (r = reg) then stacknum st else EL r (colors sth))
    by (intros; apply EL_LUPDATE_dec; exact Hr).
  eexists _, _; split; [reflexivity|]. cbn [colors int_beg int_end colormax].
  split; [|split; [apply LENGTH_LUPDATE|split; [intros r Hne; rewrite ELU; destruct (decide (r = reg)); congruence|
    split; [reflexivity|split; [reflexivity|split; [reflexivity|]]]]]].
  2:{ rewrite ELU; destruct (decide (reg = reg)); [|congruence]. exact (g_max_stack _ _ _ _ _ _ G). }
  apply gls_iff. destruct G.
  assert (Hrl : In reg l -> ~ is_phy_var reg) by (intros Hm; destruct Hid as [Hid|Hid]; [exact Hid|exfalso; apply Hid, MEM_iff, Hm]).
  assert (Hne : forall r, In r l -> r <> reg -> EL r cs = EL r (colors sth)).
  { intros r _ Hn; rewrite ELU; destruct (decide (r = reg)); congruence. }
  assert (Lcs : LENGTH cs = LENGTH (colors sth)) by apply LENGTH_LUPDATE.
  assert (Hreg : EL reg cs = stacknum st) by (rewrite ELU; destruct (decide (reg = reg)); congruence).
  assert (Hlts : forall r, In r l -> EL r (colors sth) < stacknum st) by exact g_stack0.
  assert (Hfa : forall e r, In (e, r) (List.filter (fun '(e, r) => negb (r =? reg)) (active st)) ->
                  In (e, r) (active st) /\ r <> reg).
  { intros e r Hx; apply filter_In in Hx as [Hx Hn]; split; [exact Hx|]. apply negb_true_iff, N.eqb_neq in Hn; exact Hn. }
  constructor; cbn [active colorpool phyregs colornum colormax stacknum colors int_beg int_end]; fold cs.
  - rewrite Lcs; auto.
  - rewrite Lcs; auto.
  - change (List.map (fun '(e, r) => EL r cs) (FILTER (fun '(e, r) => negb (r =? reg)) (active st)))
      with (MAP (fun '(e, r) => EL r (LUPDATE (stacknum st) reg (colors sth))) (FILTER (fun '(e, r) => negb (r =? reg)) (active st))).
    rewrite (update_color_active_colors_same 0%N). eapply ISS_NoDup; [|exact g_distinct0].
    apply IS_SPARSE_SUBLIST_APPEND_LEFT, MAP_IS_SPARSE_SUBLIST, FILTER_IS_SPARSE_SUBLIST.
  - rewrite Lcs; intros r [<-|Hr']; auto.
  - intros r [<-|Hr']; [rewrite Hreg; lia|]. rewrite ELU; destruct (decide (r = reg)); [lia|]. specialize (Hlts r Hr'); lia.
  - intros c; rewrite g_phyregs0. split.
    + intros (r & -> & Hr' & Hp & Hc). exists r. assert (r <> reg) by (intros ->; apply (Hrl Hr'), Hp).
      rewrite Hne by assumption. repeat split; auto. right; exact Hr'.
    + intros (r & -> & [<-|Hr'] & Hp & Hc).
      * rewrite Hreg in Hc. pose proof g_max_stack0; lia.
      * assert (r <> reg) by (intros ->; apply (Hrl Hr'), Hp). rewrite Hne in * by assumption. exists r; auto.
  - cbn [List.filter]. destruct (is_phy_var reg) eqn:Ep.
    + assert (Hnl : ~ In reg l) by (intros Hm; apply (Hrl Hm); reflexivity).
      cbn [List.map]. rewrite Hreg. constructor.
      * intros Hin; apply in_map_iff in Hin as (r & E & Hin). apply filter_In in Hin as [Hin _].
        rewrite Hne in E by (try exact Hin; intros ->; contradiction). specialize (Hlts r Hin); lia.
      * erewrite map_ext_in; [exact g_phydistinct0|]. intros r Hin; apply filter_In in Hin as [Hin _].
        apply Hne; [exact Hin|intros ->; contradiction].
    + erewrite map_ext_in; [exact g_phydistinct0|]. intros r Hin; apply filter_In in Hin as [Hin Hp].
      apply Hne; [exact Hin|intros ->; congruence].
  - auto.
  - intros e r Hx; destruct (Hfa _ _ Hx) as [Hx' Hn]. rewrite ELU; destruct (decide (r = reg)); [congruence|]. eauto.
  - auto.
  - lia.
  - intros r [<-|Hr'] Hc; [rewrite Hreg in Hc; lia|].
    rewrite ELU in *; destruct (decide (r = reg)); [lia|auto].
  - intros r [<-|Hr']; auto.
  - intros r [<-|Hr'] Hp Hc; [rewrite Hreg in Hc; lia|].
    rewrite ELU in Hc; destruct (decide (r = reg)) as [->|Hn]; [lia|].
    apply filter_In; split; [apply g_active_in0; auto|apply negb_true_iff, N.eqb_neq, Hn].
  - intros r [<-|Hr'] Hx; destruct (Hfa _ _ Hx) as [Hx' Hn]; [congruence|]. auto.
  - intros r1 r2 H1 H2 Hi Hc.
    destruct (N.eq_dec r1 reg) as [->|Hn1]; destruct (N.eq_dec r2 reg) as [->|Hn2]; [reflexivity| | |].
    + apply (In_tl _ _ _ H2) in Hn2 as H2'. rewrite Hreg, Hne in Hc by auto. specialize (Hlts r2 H2'); lia.
    + apply (In_tl _ _ _ H1) in Hn1 as H1'. rewrite Hreg, Hne in Hc by auto. specialize (Hlts r1 H1'); lia.
    + apply (In_tl _ _ _ H1) in Hn1 as H1'; apply (In_tl _ _ _ H2) in Hn2 as H2'.
      rewrite !Hne in Hc by auto. auto.
  - apply SORTED_filter; [exact transitive_less_FST|exact g_sorted0].
  - intros e r Hx; destruct (Hfa _ _ Hx) as [Hx' _]; auto.
  - intros e r Hx; destruct (Hfa _ _ Hx) as [Hx' _]; right; eauto.
  - intros r1 r2 Hf H1 H2 Hc.
    destruct (N.eq_dec r1 reg) as [->|Hn1]; destruct (N.eq_dec r2 reg) as [->|Hn2]; [reflexivity| | |].
    + apply (In_tl _ _ _ H2) in Hn2 as H2'. rewrite Hreg, Hne in Hc by auto. specialize (Hlts r2 H2'); lia.
    + apply (In_tl _ _ _ H1) in Hn1 as H1'. rewrite Hreg, Hne in Hc by auto. specialize (Hlts r1 H1'); lia.
    + apply (In_tl _ _ _ H1) in Hn1 as H1'; apply (In_tl _ _ _ H2) in Hn2 as H2'.
      rewrite !Hne in Hc by auto. eauto.
  - auto.
  - auto.
  - intros r [<-|Hr']; [rewrite Hreg; lia|]. rewrite ELU; destruct (decide (r = reg)); [lia|auto].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "spill_register_FILTER_invariants" *)
Theorem spill_register_FILTER_invariants : forall st sth l pos forced reg mincol,
  (~ is_phy_var reg \/ ~ MEM reg l) /\
  good_linear_scan_state st sth l pos forced mincol /\
  reg < LENGTH sth.(colors) /\
  (EL reg sth.(int_beg) <= pos)%Z ->
  exists stout sthout,
    (M_success stout, sthout) =
      spill_register (set_active st (FILTER (fun '(e, r) => negb (r =? reg)) st.(active))) reg sth /\
    good_linear_scan_state stout sthout (reg :: l) pos forced mincol /\
    LENGTH sthout.(colors) = LENGTH sth.(colors) /\
    (forall r, r <> reg -> EL r sth.(colors) = EL r sthout.(colors)) /\
    stout.(colormax) = st.(colormax) /\
    sthout.(int_beg) = sth.(int_beg) /\ sthout.(int_end) = sth.(int_end) /\
    st.(colormax) <= EL reg sthout.(colors).
Proof. exact spill_register_FILTER_invariants_hidden. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "FILTER_MEM_active" *)
Theorem FILTER_MEM_active : forall (reg : N) (l : list (Z * N)),
  (forall (e : Z), ~ MEM (e, reg) l) -> FILTER (fun '(e, r) => negb (r =? reg)) l = l.
Proof.
  intros reg l H; induction l as [|[e r] l IH]; [reflexivity|]. cbn [FILTER List.filter].
  destruct (N.eqb_spec r reg) as [->|Hn].
  - exfalso; apply (H e); cbn [MEM]; rewrite (proj2 (bool_decide_spec ((e, reg) = (e, reg))) eq_refl); reflexivity.
  - cbn [negb]; f_equal; apply IH; intros e' Hm; apply (H e'); cbn [MEM]; rewrite Hm, orb_true_r; reflexivity.
Qed.

Lemma set_active_same st : set_active st st.(active) = st.
Proof. destruct st; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "spill_register_invariants" *)
Theorem spill_register_invariants : forall st sth l pos forced reg mincol,
  (forall e, ~ MEM (e, reg) st.(active)) /\
  (~ is_phy_var reg \/ ~ MEM reg l) /\
  good_linear_scan_state st sth l pos forced mincol /\
  reg < LENGTH sth.(colors) /\
  (EL reg sth.(int_beg) <= pos)%Z ->
  exists stout sthout, (M_success stout, sthout) = spill_register st reg sth /\
    good_linear_scan_state stout sthout (reg :: l) pos forced mincol /\
    LENGTH sthout.(colors) = LENGTH sth.(colors) /\
    sthout.(int_beg) = sth.(int_beg) /\ sthout.(int_end) = sth.(int_end) /\
    (forall r, r <> reg -> EL r sth.(colors) = EL r sthout.(colors)) /\
    stout.(colormax) = st.(colormax) /\
    st.(colormax) <= EL reg sthout.(colors).
Proof.
  intros st sth l pos forced reg mincol (Ha & H).
  destruct (spill_register_FILTER_invariants st sth l pos forced reg mincol H) as (so & sho & E & R).
  rewrite FILTER_MEM_active, set_active_same in E by exact Ha.
  exists so, sho; tauto.
Qed.

(** ** Adjacency lists of forced edges *)

Lemma LEX_b (x y : Z) (a b : N) :
  ⌜LEX Z.lt N.le (x, a) (y, b)⌝ = ((x <? y)%Z || ((x =? y)%Z && (a <=? b))).
Proof.
  destruct (bool_decide _) eqn:B; [apply bool_decide_spec in B|];
    destruct (Z.ltb_spec x y), (Z.eqb_spec x y), (N.leb_spec a b); cbn; try reflexivity;
    unfold LEX in *; try lia.
  all: exfalso; apply not_true_iff_false in B; apply B, bool_decide_spec; unfold LEX; lia.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "edges_to_adjlist_step_def" *)
Definition edges_to_adjlist_step (sth : linear_scan_hidden_state) (p : N * N) (acc : num_map (list N))
    : num_map (list N) :=
  let '(a, b) := p in
  if decide (a = b) then acc
  else if ⌜LEX Z.lt N.le (EL a sth.(int_beg), a) (EL b sth.(int_beg), b)⌝ then
    insert b (a :: the [] (lookup b acc)) acc
  else
    insert a (b :: the [] (lookup a acc)) acc.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "edges_to_adjlist_FOLDL" *)
Theorem edges_to_adjlist_FOLDL : forall forced sth acc,
  EVERY (fun '(r1, r2) => (r1 <? LENGTH sth.(int_beg)) && (r2 <? LENGTH sth.(int_beg))) forced ->
  edges_to_adjlist forced acc sth =
    (M_success (FOLDL (fun acc pair => edges_to_adjlist_step sth pair acc) acc forced), sth).
Proof.
  induction forced as [|[a b] forced IH]; intros sth acc H; [reflexivity|].
  cbn [EVERY] in H; unfold is_true in H; apply andb_prop in H as [Hab H]; apply andb_prop in Hab as [Ha Hb].
  cbn [edges_to_adjlist FOLDL]. unfold edges_to_adjlist_step at 2.
  destruct (N.eqb_spec a b) as [->|Hne].
  - destruct (decide (b = b)); [|congruence]. apply IH, H.
  - destruct (decide (a = b)); [congruence|]. msimp. rewrite int_beg_sub_eqn, Ha; cbv beta iota.
    rewrite int_beg_sub_eqn, Hb; cbv beta iota.
    rewrite LEX_b. destruct (_ || _); apply IH, H.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "forbidden_is_from_forced_def" *)
Definition forbidden_is_from_forced (forced : list (N * N)) (int_beg : list Z) (reg : N) (forbidden : list N) : Prop :=
  forall reg2, (reg <> reg2 /\ (MEM (reg2, reg) forced \/ MEM (reg, reg2) forced) /\
    LEX Z.lt N.le (EL reg2 int_beg, reg2) (EL reg int_beg, reg)) <-> MEM reg2 forbidden.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "forbidden_is_from_forced_sublist_def" *)
Definition forbidden_is_from_forced_sublist (l : list N) (forced : list (N * N)) (int_beg : list Z) (reg : N)
    (forbidden : list N) : Prop :=
  forall reg2, (reg <> reg2 /\ (MEM (reg2, reg) forced \/ MEM (reg, reg2) forced) /\
    LEX Z.lt N.le (EL reg2 int_beg, reg2) (EL reg int_beg, reg)) <-> (MEM reg2 forbidden /\ MEM reg l).

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "forbidden_is_from_forced_list_def" *)
Definition forbidden_is_from_forced_list (forced : list (N * N)) (l : list N) (reg : N) (forbidden : list N) : Prop :=
  forall reg2, MEM reg2 l /\ (MEM (reg2, reg) forced \/ MEM (reg, reg2) forced) -> MEM reg2 forbidden.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "forbidden_is_from_map_color_forced_def" *)
Definition forbidden_is_from_map_color_forced (forced : list (N * N)) (l : list N) (colors : list N) (reg : N)
    (forbidden : num_set) : Prop :=
  forall reg2, MEM reg2 l /\ (MEM (reg2, reg) forced \/ MEM (reg, reg2) forced) ->
    EL reg2 colors IN domain forbidden.

Lemma MEM_cons_iff {A} `{EqDecision A} (x y : A) l : is_true (MEM x (y :: l)) <-> x = y \/ is_true (MEM x l).
Proof. cbn [MEM]; unfold is_true; rewrite orb_true_iff, bool_decide_spec; reflexivity. Qed.

Lemma LEX_antisym (x y : Z) (a b : N) :
  LEX Z.lt N.le (x, a) (y, b) -> LEX Z.lt N.le (y, b) (x, a) -> a = b.
Proof. unfold LEX; lia. Qed.

Lemma LEX_total (x y : Z) (a b : N) :
  ~ LEX Z.lt N.le (x, a) (y, b) -> LEX Z.lt N.le (y, b) (x, a).
Proof. unfold LEX; lia. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "edges_to_adjlist_FOLDR_output" *)
Theorem edges_to_adjlist_FOLDR_output : forall forced sth reg,
  forbidden_is_from_forced forced sth.(int_beg) reg
    (the [] (lookup reg (FOLDR (fun pair acc => edges_to_adjlist_step sth pair acc) LN forced))).
Proof.
  unfold forbidden_is_from_forced.
  induction forced as [|[h0 h1] forced IH]; intros sth reg reg2.
  - cbn [FOLDR]. rewrite lookup_LN. cbn [the MEM]. split; [intros (_ & [H|H] & _); discriminate|discriminate].
  - cbn [FOLDR]. specialize (IH sth reg reg2).
    set (acc := FOLDR (fun pair acc => edges_to_adjlist_step sth pair acc) LN forced) in *.
    unfold edges_to_adjlist_step.
    rewrite !MEM_cons_iff.
    set (L := fun a b => LEX Z.lt N.le (EL a (int_beg sth), a) (EL b (int_beg sth), b)) in *.
    change (LEX Z.lt N.le (EL reg2 (int_beg sth), reg2) (EL reg (int_beg sth), reg)) with (L reg2 reg) in *.
    destruct (decide (h0 = h1)) as [<-|Hne].
    + rewrite <- IH. split; [|tauto]. intros (Hn & [[E|E]|[E|E]] & Hl); try (inversion E; congruence); tauto.
    + assert (Asym : forall a b, L a b -> L b a -> a = b) by (intros a b; apply LEX_antisym).
      assert (Tot : forall a b, ~ L a b -> L b a) by (intros a b; apply LEX_total).
      change (bool_decide (LEX Z.lt N.le (EL h0 (int_beg sth), h0) (EL h1 (int_beg sth), h1)))
        with (bool_decide (L h0 h1)).
      destruct (bool_decide (L h0 h1)) eqn:B; [apply bool_decide_spec in B|apply not_true_iff_false in B;
        assert (B' : ~ L h0 h1) by (intros X; apply B, bool_decide_spec, X); clear B; apply Tot in B'].
      * rewrite lookup_insert. destruct (decide (reg = h1)) as [->|Hr].
        -- cbn [the]. rewrite MEM_cons_iff, <- IH. split.
           ++ intros (Hn & [[E|E]|[E|E]] & Hl); try (inversion E; subst; tauto); tauto.
           ++ intros [->|H]; [split; [congruence|split; [left; left; reflexivity|exact B]]|tauto].
        -- rewrite <- IH. split; [|tauto].
           intros (Hn & [[E|E]|[E|E]] & Hl); try tauto; inversion E; subst; [congruence|].
           exfalso; apply Hne; symmetry; apply Asym; assumption.
      * rewrite lookup_insert. destruct (decide (reg = h0)) as [->|Hr].
        -- cbn [the]. rewrite MEM_cons_iff, <- IH. split.
           ++ intros (Hn & [[E|E]|[E|E]] & Hl); try (inversion E; subst; tauto); tauto.
           ++ intros [->|H]; [split; [congruence|split; [right; left; reflexivity|exact B']]|tauto].
        -- rewrite <- IH. split; [|tauto].
           intros (Hn & [[E|E]|[E|E]] & Hl); try tauto; inversion E; subst; [|congruence].
           exfalso; apply Hne; apply Asym; assumption.
Qed.

Lemma MEM_rev_iff {A} `{EqDecision A} (x : A) l : is_true (MEM x (REVERSE l)) <-> is_true (MEM x l).
Proof. rewrite MEM_rev; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "edges_to_adjlist_output" *)
Theorem edges_to_adjlist_output : forall forced sth,
  EVERY (fun '(r1, r2) => (r1 <? LENGTH sth.(int_beg)) && (r2 <? LENGTH sth.(int_beg))) forced ->
  exists adjlist, edges_to_adjlist forced LN sth = (M_success adjlist, sth) /\
  forall reg, forbidden_is_from_forced forced sth.(int_beg) reg (the [] (lookup reg adjlist)).
Proof.
  intros forced sth H. rewrite (edges_to_adjlist_FOLDL _ _ _ H). eexists; split; [reflexivity|].
  intros reg. rewrite FOLDL_fold_left, <- fold_left_rev_right, <- FOLDR_fold_right.
  pose proof (edges_to_adjlist_FOLDR_output (REVERSE forced) sth reg) as F.
  unfold forbidden_is_from_forced in *. intros reg2; rewrite <- F, !MEM_rev_iff; reflexivity.
Qed.

Lemma gls_equiv_l st sth l1 l2 pos forced mincol :
  (forall x, In x l1 <-> In x l2) ->
  NoDup (List.map (fun r => EL r sth.(colors)) (List.filter is_phy_var l2)) ->
  gls st sth l1 pos forced mincol -> gls st sth l2 pos forced mincol.
Proof.
  intros E D G. destruct G. refine {|
    g_len_beg := g_len_beg0; g_len_end := g_len_end0; g_distinct := g_distinct0;
    g_phydistinct := D; g_pool := g_pool0; g_active_col := g_active_col0; g_num_max := g_num_max0;
    g_max_stack := g_max_stack0; g_sorted := g_sorted0; g_active_end := g_active_end0;
    g_mincol := g_mincol0; g_mincol_pool := g_mincol_pool0 |}.
  - intros r Hr; apply g_lt0, E, Hr.
  - intros r Hr; apply g_stack0, E, Hr.
  - intros c; rewrite g_phyregs0; split; intros (r & -> & Hr & Hp & Hc); exists r; repeat split; auto; apply E; auto.
  - intros r Hr; apply g_maxnum0, E, Hr.
  - intros r Hr; apply g_beg0, E, Hr.
  - intros r Hr; apply g_active_in0, E, Hr.
  - intros r Hr; apply g_active_pos0, E, Hr.
  - intros r1 r2 H1 H2; apply g_inj0; apply E; auto.
  - intros e r Hr; apply E; exact (g_active_l0 e r Hr).
  - intros r1 r2 Hf H1 H2; apply g_forced0; auto; apply E; auto.
  - intros r Hr; apply g_mincol_l0, E, Hr.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "state_invariants_remove_head" *)
Theorem state_invariants_remove_head : forall st sth reg l pos forced mincol,
  MEM reg l /\
  good_linear_scan_state st sth (reg :: l) pos forced mincol ->
  good_linear_scan_state st sth l pos forced mincol.
Proof.
  intros st sth reg l pos forced mincol [Hm G]; apply gls_iff in G; apply gls_iff.
  apply MEM_iff in Hm.
  assert (E : forall x, In x (reg :: l) <-> In x l) by (intros x; split; [intros [<-|H]; auto|intros H; right; exact H]).
  eapply gls_equiv_l; [exact E| |exact G].
  pose proof (g_phydistinct _ _ _ _ _ _ G) as D. cbn [List.filter] in D.
  destruct (is_phy_var reg); [inversion D; auto|auto].
Qed.

Lemma find_last_stealable_state active forbidden sth :
  snd (find_last_stealable active forbidden sth) = sth.
Proof.
  induction active as [|x xs IH]; [reflexivity|]. cbn [find_last_stealable]. msimp.
  destruct (find_last_stealable xs forbidden sth) as [[o|e] s'] eqn:E; cbn in IH; subst s'; [|reflexivity].
  destruct o as [[steal rest]|]; [reflexivity|]. rewrite colors_sub_eqn.
  destruct (_ <? _); [|reflexivity]. destruct (_ && _); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "find_last_stealable_success" *)
Theorem find_last_stealable_success : forall forbidden sth active,
  EVERY (fun '(e, r) => r <? LENGTH sth.(colors)) active ->
  exists optout, find_last_stealable active forbidden sth = (M_success optout, sth).
Proof.
  intros forbidden sth; induction active as [|[e r] xs IH]; intros H; [eexists; reflexivity|].
  cbn [EVERY] in H; unfold is_true in H; apply andb_prop in H as [Hr H].
  cbn [find_last_stealable]; msimp. destruct (IH H) as [o E]; rewrite E.
  destruct o as [[steal rest]|]; [eexists; reflexivity|]. cbn [snd]. rewrite colors_sub_eqn, Hr.
  destruct (_ && _); eexists; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "find_last_stealable_output" *)
Theorem find_last_stealable_output : forall forbidden sth active steal rest,
  find_last_stealable active forbidden sth = (M_success (Some (steal, rest)), sth) ->
  ~ is_phy_var (SND steal) /\ lookup (EL (SND steal) sth.(colors)) forbidden = None /\
  exists l1 l2, rest = l1 ++ l2 /\ active = l1 ++ steal :: l2.
Proof.
  intros forbidden sth; induction active as [|x xs IH]; intros steal rest H; [discriminate|].
  cbn [find_last_stealable] in H; msimp.
  pose proof (find_last_stealable_state xs forbidden sth) as Es.
  destruct (find_last_stealable xs forbidden sth) as [[o|e] s'] eqn:E; cbn in Es; subst s'; [|discriminate].
  destruct o as [[st' rs]|].
  - inversion H; subst. destruct (IH _ _ eq_refl) as (H1 & H2 & l1 & l2 & -> & ->).
    split; [exact H1|split; [exact H2|]]. exists (x :: l1), l2; split; reflexivity.
  - rewrite colors_sub_eqn in H. destruct (_ <? _); [|discriminate].
    destruct (negb (is_phy_var (SND x)) && _) eqn:B; [|discriminate].
    inversion H; subst. apply andb_prop in B as [B1 B2]. apply negb_true_iff in B1.
    apply bool_decide_spec in B2. split; [unfold is_true; rewrite B1; discriminate|split; [exact B2|]].
    exists [], rest; split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "good_linear_scan_state_active_length_colors" *)
Theorem good_linear_scan_state_active_length_colors : forall st sth l pos forced mincol,
  good_linear_scan_state st sth l pos forced mincol ->
  EVERY (fun '(e, r) => r <? LENGTH sth.(colors)) st.(active).
Proof.
  intros st sth l pos forced mincol G; apply gls_iff in G. apply EVERY_iff. intros [e r] Hr.
  apply N.ltb_lt. eapply g_lt; [exact G|]. eapply g_active_l; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "color_register_eq" *)
Theorem color_register_eq : forall st reg col rend,
  color_register st reg col rend =
    (update_colors reg col ;;
     st_ex_return
       {| active := add_active_interval (rend, reg) st.(active);
          colorpool := st.(colorpool);
          phyregs := if is_phy_var reg then insert col tt st.(phyregs) else st.(phyregs);
          colornum := st.(colornum); colormax := st.(colormax); stacknum := st.(stacknum) |}).
Proof. intros; unfold color_register; destruct (is_phy_var reg); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "color_register_invariants" *)
Theorem color_register_invariants : forall st sth l pos forced reg col forbidden mincol,
  good_linear_scan_state st sth l pos forced mincol /\
  forbidden_is_from_map_color_forced forced l sth.(colors) reg forbidden /\
  col NOTIN domain forbidden /\
  (is_phy_var reg -> domain st.(phyregs) SUBSET domain forbidden) /\
  ~ MEM col (st.(colorpool) ++ MAP (fun '(e, r) => EL r sth.(colors)) st.(active)) /\
  EL reg sth.(int_beg) = pos /\
  (EL reg sth.(int_beg) <= EL reg sth.(int_end))%Z /\
  col < st.(colornum) /\
  mincol <= col /\
  reg < LENGTH sth.(colors) /\
  ~ MEM reg l ->
  exists stout sthout, (M_success stout, sthout) = color_register st reg col (EL reg sth.(int_end)) sth /\
    good_linear_scan_state stout sthout (reg :: l) pos forced mincol /\
    LENGTH sthout.(colors) = LENGTH sth.(colors) /\
    sthout.(int_beg) = sth.(int_beg) /\ sthout.(int_end) = sth.(int_end) /\
    (forall r, r <> reg -> EL r sth.(colors) = EL r sthout.(colors)) /\
    stout.(colormax) = st.(colormax).
Proof.
  intros st sth l pos forced reg col forbidden mincol
    (G & Hfb & Hcf & Hph & Hcm & Hbeg & Hbe & Hcn & Hmc & Hr & Hrl).
  apply gls_iff in G. rewrite MEM_iff in Hcm, Hrl.
  rewrite color_register_eq; msimp. rewrite update_colors_eqn. destruct (N.ltb_spec reg (LENGTH sth.(colors))); [|lia].
  set (cs := LUPDATE col reg (colors sth)).
  assert (Lcs : LENGTH cs = LENGTH (colors sth)) by apply LENGTH_LUPDATE.
  assert (ELU : forall r, EL r cs = if decide (r = reg) then col else EL r (colors sth))
    by (intros; apply EL_LUPDATE_dec; exact Hr).
  assert (Hreg : EL reg cs = col) by (rewrite ELU; destruct (decide (reg = reg)); congruence).
  assert (Hne : forall r, r <> reg -> EL r cs = EL r (colors sth)) by (intros r Hn; rewrite ELU; destruct (decide (r = reg)); congruence).
  assert (Hna : forall e, ~ In (e, reg) (active st)) by (intros e Ha; apply Hrl; eapply g_active_l; eauto).
  destruct (add_active_interval_output (active st) tt _ (EL reg (int_end sth)) reg
              (conj (g_sorted _ _ _ _ _ _ G) eq_refl)) as [Hs' (l1 & l2 & E1 & E2)].
  set (act' := add_active_interval (EL reg (int_end sth), reg) (active st)) in *.
  assert (Hact : forall x, In x act' <-> x = (EL reg (int_end sth), reg) \/ In x (active st)).
  { intros x; rewrite E2, E1, !in_app_iff; cbn [In]; split; [intros [Hq|[Hq|Hq]]; auto|intros [Hq|[Hq|Hq]]; [subst x|..]; auto]. }
  assert (Hmapeq : forall (l' : list (Z * N)), (forall (e : Z), ~ In (e, reg) l') ->
    List.map (fun '(e, r) => EL r cs) l' = List.map (fun '(e, r) => EL r (colors sth)) l').
  { intros l' Hl'; apply map_ext_in; intros [e r] Hx; apply Hne; intros ->; exact (Hl' e Hx). }
  eexists _, _; split; [reflexivity|]. cbn [colors int_beg int_end colormax].
  split; [|split; [exact Lcs|split; [reflexivity|split; [reflexivity|split; [intros r Hn; symmetry; apply Hne, Hn|reflexivity]]]]].
  apply gls_iff. destruct G.
  assert (Hlts : forall r, In r l -> EL r (colors sth) < stacknum st) by exact g_stack0.
  refine {| g_len_beg := _ |}; cbn [active colorpool phyregs colornum colormax stacknum colors int_beg int_end];
    fold cs; fold act'.
  - rewrite Lcs; auto.
  - rewrite Lcs; auto.
  - rewrite E2, map_app; cbn [List.map].
    rewrite (Hmapeq l1), (Hmapeq l2), Hreg
      by (intros e Hx; apply (Hna e); rewrite E1; apply in_app_iff; auto).
    rewrite app_assoc. refine (Permutation_NoDup (Permutation_middle _ _ _) _).
    constructor.
    + intros Hin; apply Hcm. rewrite E1, map_app, app_assoc. exact Hin.
    + rewrite E1, map_app, app_assoc in g_distinct0; exact g_distinct0.
  - rewrite Lcs; intros r [<-|Hx]; auto.
  - intros r [<-|Hx]; [rewrite Hreg; lia|]. rewrite Hne by (intros ->; contradiction). auto.
  - intros c. destruct (is_phy_var reg) eqn:Ep.
    + rewrite domain_insert. split.
      * intros [->|Hc]; [exists reg; rewrite Hreg; repeat split; auto; [left; reflexivity|lia]|].
        apply g_phyregs0 in Hc as (r & -> & Hx & Hp & Hc). exists r. rewrite Hne by (intros ->; contradiction).
        repeat split; auto. right; exact Hx.
      * intros (r & -> & [<-|Hx] & Hp & Hc); [left; exact Hreg|right].
        rewrite Hne in * by (intros ->; contradiction). apply g_phyregs0; exists r; auto.
    + rewrite g_phyregs0. split.
      * intros (r & -> & Hx & Hp & Hc); exists r; rewrite Hne by (intros ->; contradiction). repeat split; auto; right; auto.
      * intros (r & -> & [<-|Hx] & Hp & Hc); [congruence|]. rewrite Hne in * by (intros ->; contradiction). exists r; auto.
  - cbn [List.filter]. assert (Hm : List.map (fun r => EL r cs) (List.filter is_phy_var l) =
                                 List.map (fun r => EL r (colors sth)) (List.filter is_phy_var l)).
    { apply map_ext_in; intros r Hx; apply filter_In in Hx as [Hx _]; apply Hne; intros ->; contradiction. }
    destruct (is_phy_var reg) eqn:Ep; cbn [List.map]; rewrite Hm; [|exact g_phydistinct0].
    constructor; [|exact g_phydistinct0]. rewrite Hreg. intros Hin.
    apply in_map_iff in Hin as (r & E & Hx). apply filter_In in Hx as [Hx Hp].
    apply Hcf. apply (Hph eq_refl). apply g_phyregs0. exists r; repeat split; auto.
    rewrite E. pose proof (g_maxnum0 r Hx). lia.
  - auto.
  - intros e r Hx. apply Hact in Hx as [Hx|Hx]; [injection Hx as He Hrr; subst e r; rewrite Hreg; exact Hcn|].
    rewrite Hne by (intros ->; exact (Hna e Hx)). eauto.
  - auto.
  - auto.
  - intros r [<-|Hx] Hc; [rewrite Hreg; exact Hcn|]. rewrite Hne in * by (intros ->; contradiction). auto.
  - intros r [<-|Hx]; [lia|auto].
  - intros r [<-|Hx] Hp Hc; apply Hact; [left; reflexivity|right; rewrite Hne in Hc by (intros ->; contradiction); auto].
  - intros r [<-|Hx] Ha; [lia|]. apply Hact in Ha as [Ha|Ha]; [injection Ha as Hrr; subst r; contradiction|auto].
  - assert (Hx2 : forall r2, In r2 l -> (EL reg (int_beg sth) <= EL r2 (int_end sth))%Z -> EL r2 (colors sth) <> col).
    { intros r2 H2 Hle Hc. apply Hcm. apply in_app_iff; right.
      apply in_map_iff. exists (EL r2 (int_end sth), r2). split; [exact Hc|].
      apply g_active_in0; auto; [lia|]. rewrite Hc. lia. }
    intros r1 r2 H1 H2 Hi Hc.
    destruct (N.eq_dec r1 reg) as [->|Hn1]; destruct (N.eq_dec r2 reg) as [->|Hn2]; [reflexivity| | |].
    + apply (In_tl _ _ _ H2) in Hn2 as H2'. rewrite Hreg, Hne in Hc by auto.
      unfold interval_intersect, is_true in Hi; rewrite andb_true_iff, !Z.leb_le in Hi.
      exfalso; apply (Hx2 r2 H2'); [lia|congruence].
    + apply (In_tl _ _ _ H1) in Hn1 as H1'. rewrite Hreg, Hne in Hc by auto.
      unfold interval_intersect, is_true in Hi; rewrite andb_true_iff, !Z.leb_le in Hi.
      exfalso; apply (Hx2 r1 H1'); [lia|congruence].
    + apply (In_tl _ _ _ H1) in Hn1 as H1'; apply (In_tl _ _ _ H2) in Hn2 as H2'.
      rewrite !Hne in Hc by auto. auto.
  - exact Hs'.
  - intros e r Hx; apply Hact in Hx as [Hx|Hx]; [injection Hx as He Hrr; subst e r; reflexivity|eauto].
  - intros e r Hx; apply Hact in Hx as [Hx|Hx]; [injection Hx as He Hrr; subst e r; left; reflexivity|right; eauto].
  - intros r1 r2 Hf H1 H2 Hc.
    destruct (N.eq_dec r1 reg) as [->|Hn1]; destruct (N.eq_dec r2 reg) as [->|Hn2]; [reflexivity| | |].
    + apply (In_tl _ _ _ H2) in Hn2 as H2'. rewrite Hreg, Hne in Hc by auto. exfalso; apply Hcf.
      rewrite Hc. apply Hfb. split; [apply MEM_iff, H2'|right; apply MEM_iff, Hf].
    + apply (In_tl _ _ _ H1) in Hn1 as H1'. rewrite Hreg, Hne in Hc by auto. exfalso; apply Hcf.
      rewrite <- Hc. apply Hfb. split; [apply MEM_iff, H1'|left; apply MEM_iff, Hf].
    + apply (In_tl _ _ _ H1) in Hn1 as H1'; apply (In_tl _ _ _ H2) in Hn2 as H2'.
      rewrite !Hne in Hc by auto. eauto.
  - auto.
  - auto.
  - intros r [<-|Hx]; [rewrite Hreg; exact Hmc|]. rewrite Hne by (intros ->; contradiction). auto.
Qed.

(** [reg_allocScript]'s [convention_partitions] (not yet in [reg_alloc.v];
    untagged copy). *)
Lemma convention_partitions' n :
  (is_stack_var n <-> ~ is_phy_var n /\ ~ is_alloc_var n) /\
  (is_phy_var n <-> ~ is_stack_var n /\ ~ is_alloc_var n) /\
  (is_alloc_var n <-> ~ is_phy_var n /\ ~ is_stack_var n).
Proof.
  unfold is_stack_var, is_phy_var, is_alloc_var, is_true.
  assert (M : n mod 4 = n mod 2 + 2 * ((n / 2) mod 2)).
  { replace 4 with (2 * 2) by reflexivity. apply N.Div0.mod_mul_r. }
  pose proof (N.mod_lt n 2 ltac:(lia)); pose proof (N.mod_lt (n / 2) 2 ltac:(lia)).
  rewrite !N.eqb_eq. lia.
Qed.

Lemma gls_sub_pool st sth l pos forced mincol cp :
  gls st sth l pos forced mincol -> (forall c, In c cp -> In c st.(colorpool)) ->
  NoDup (cp ++ List.map (fun '(e, r) => EL r sth.(colors)) st.(active)) ->
  gls (set_colorpool st cp) sth l pos forced mincol.
Proof.
  intros G Hs D; destruct G; constructor; cbn [set_colorpool active colorpool phyregs colornum colormax stacknum]; auto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "find_spill_invariants" *)
Theorem find_spill_invariants : forall st sth l forbidden forced reg force mincol,
  ~ MEM reg l /\
  good_linear_scan_state st sth l (EL reg sth.(int_beg)) forced mincol /\
  reg < LENGTH sth.(colors) /\
  forbidden_is_from_map_color_forced forced l sth.(colors) reg forbidden /\
  (is_phy_var reg -> domain st.(phyregs) SUBSET domain forbidden) /\
  (EL reg sth.(int_beg) <= EL reg sth.(int_end))%Z ->
  exists stout sthout,
    (M_success stout, sthout) = find_spill st forbidden reg (EL reg sth.(int_end)) force sth /\
    good_linear_scan_state stout sthout (reg :: l) (EL reg sth.(int_beg)) forced mincol /\
    LENGTH sthout.(colors) = LENGTH sth.(colors) /\
    sthout.(int_beg) = sth.(int_beg) /\ sthout.(int_end) = sth.(int_end) /\
    (forall r, ~ MEM r (reg :: l) -> EL r sthout.(colors) = EL r sth.(colors)) /\
    (forall r, MEM r l /\ is_phy_var r -> EL r sthout.(colors) = EL r sth.(colors)) /\
    stout.(colormax) = st.(colormax).
Proof.
  intros st sth l forbidden forced reg force mincol (Hrl & G & Hr & Hfb & Hph & Hbe).
  pose proof G as G0; apply gls_iff in G0.
  assert (Hna : forall e, ~ MEM (e, reg) st.(active)).
  { intros e Hm; apply MEM_iff in Hm. apply Hrl, MEM_iff. eapply g_active_l; eauto. }
  pose proof (good_linear_scan_state_active_length_colors _ _ _ _ _ _ G) as HL.
  destruct (find_last_stealable_success forbidden sth _ HL) as [opt Efls].
  (* the plain spill *)
  assert (Spill : exists stout sthout,
    (M_success stout, sthout) = spill_register st reg sth /\
    good_linear_scan_state stout sthout (reg :: l) (EL reg sth.(int_beg)) forced mincol /\
    LENGTH sthout.(colors) = LENGTH sth.(colors) /\
    sthout.(int_beg) = sth.(int_beg) /\ sthout.(int_end) = sth.(int_end) /\
    (forall r, ~ MEM r (reg :: l) -> EL r sthout.(colors) = EL r sth.(colors)) /\
    (forall r, MEM r l /\ is_phy_var r -> EL r sthout.(colors) = EL r sth.(colors)) /\
    stout.(colormax) = st.(colormax)).
  { destruct (spill_register_invariants st sth l (EL reg sth.(int_beg)) forced reg mincol
      (conj Hna (conj (or_intror Hrl) (conj G (conj Hr (Z.le_refl _))))))
      as (so & sho & E & G' & L & B & En & Hs & M & _).
    exists so, sho; split; [exact E|split; [exact G'|split; [exact L|split; [exact B|split; [exact En|split; [|split; [|exact M]]]]]]].
    - intros r Hm; symmetry; apply Hs. intros ->; apply Hm; cbn [MEM];
        rewrite (proj2 (bool_decide_spec (reg = reg)) eq_refl); reflexivity.
    - intros r [Hm _]; symmetry; apply Hs. intros ->; contradiction. }
  unfold find_spill; msimp. rewrite Efls.
  destruct opt as [[[stealend stealreg] rest]|]; [|exact Spill].
  destruct (force || (EL reg (int_end sth) <? stealend)%Z); [|exact Spill].
  destruct (find_last_stealable_output _ _ _ _ _ Efls) as (Hnp & Hlk & l1 & l2 & Er & Ea).
  cbn [SND snd] in Hnp, Hlk.
  assert (Hin : In (stealend, stealreg) st.(active)) by (rewrite Ea; apply in_app_iff; right; left; reflexivity).
  assert (Hsl : In stealreg l) by (eapply g_active_l; eauto).
  assert (Hsr : stealreg < LENGTH sth.(colors)) by (eapply g_lt; eauto).
  assert (Hse : stealend = EL stealreg sth.(int_end)) by (eapply g_active_end; eauto).
  set (col := EL stealreg sth.(colors)).
  assert (Hdist : NoDup (col :: st.(colorpool) ++ List.map (fun '(e, r) => EL r sth.(colors)) (l1 ++ l2))).
  { pose proof (g_distinct _ _ _ _ _ _ G0) as D. rewrite Ea, map_app in D. cbn [List.map] in D.
    rewrite app_assoc in D. rewrite map_app, app_assoc. refine (Permutation_NoDup _ D).
    symmetry; apply Permutation_middle. }
  assert (Hnsteal : forall e, ~ In (e, stealreg) (l1 ++ l2)).
  { intros e Hx. pose proof (proj1 (proj1 (NoDup_cons_iff _ _) Hdist)) as Hn. apply Hn. apply in_app_iff; right.
    apply in_map_iff. exists (e, stealreg); split; [reflexivity|exact Hx]. }
  assert (Hfilt : FILTER (fun '(e, r) => negb (r =? stealreg)) st.(active) = rest).
  { rewrite Er, Ea, filter_app. cbn [List.filter]. rewrite N.eqb_refl. cbn [negb].
    rewrite <- filter_app. apply FILTER_MEM_active. intros e Hm; apply MEM_iff in Hm; exact (Hnsteal e Hm). }
  msimp. rewrite colors_sub_eqn. destruct (N.ltb_spec stealreg (LENGTH sth.(colors))); [|lia]. cbv beta iota.
  destruct (spill_register_FILTER_invariants st sth l (EL reg sth.(int_beg)) forced stealreg mincol)
    as (st1 & sth1 & E1 & G1 & L1 & S1 & M1 & B1 & En1 & _).
  { split; [left; unfold is_true; destruct (is_phy_var stealreg); [exfalso; apply Hnp; reflexivity|discriminate]|].
    split; [exact G|split; [exact Hsr|]]. apply (g_beg _ _ _ _ _ _ G0), Hsl. }
  rewrite Hfilt in E1. unfold set_active in E1. rewrite <- E1. cbv beta iota.
  pose proof (state_invariants_remove_head _ _ _ _ _ _ _ (conj (proj2 (MEM_iff _ _) Hsl) G1)) as G1r.
  clear G1; rename G1r into G1.
  pose proof G1 as G1'; apply gls_iff in G1'.
  (* the spilled state *)
  assert (Hsp : spill_register {| active := rest; colorpool := colorpool st; phyregs := phyregs st;
      colornum := colornum st; colormax := colormax st; stacknum := stacknum st |} stealreg sth = (M_success st1, sth1))
    by (symmetry; exact E1).
  unfold spill_register in Hsp; msimp. rewrite update_colors_eqn in Hsp.
  destruct (N.ltb_spec stealreg (LENGTH sth.(colors))); [|lia]. injection Hsp as <- <-.
  cbn [colors int_beg int_end active colorpool phyregs colornum colormax stacknum] in *.
  set (cs1 := LUPDATE (stacknum st) stealreg (colors sth)) in *.
  assert (Hne1 : forall r, r <> stealreg -> EL r cs1 = EL r (colors sth)) by (intros; apply EL_LUPDATE_other; auto).
  destruct (color_register_invariants
    {| active := rest; colorpool := colorpool st; phyregs := phyregs st; colornum := colornum st;
       colormax := colormax st; stacknum := stacknum st + 1 |}
    {| colors := cs1; int_beg := int_beg sth; int_end := int_end sth; sorted_regs := sorted_regs sth;
       sorted_moves := sorted_moves sth |}
    l (EL reg sth.(int_beg)) forced reg col forbidden mincol) as (st2 & sth2 & E2 & G2 & L2 & B2 & En2 & S2 & M2).
  { cbn [colors int_beg int_end active colorpool phyregs colornum colormax stacknum].
    split; [exact G1|]. split.
    { intros reg2 (Hm & Hf). destruct (N.eq_dec reg2 stealreg) as [->|Hn].
      - exfalso. pose proof (Hfb stealreg (conj Hm Hf)) as X. apply notdom_lookup in Hlk. contradiction.
      - rewrite Hne1 by exact Hn. apply Hfb; auto. }
    split; [apply notdom_lookup, Hlk|]. split; [exact Hph|].
    split.
    { intros Hm; apply MEM_iff in Hm. pose proof (proj1 (proj1 (NoDup_cons_iff _ _) Hdist)) as Hn. apply Hn.
      rewrite Er in Hm. rewrite (map_ext_in _ (fun '(e, r) => EL r (colors sth))) in Hm; [exact Hm|].
      intros [e r] Hx. apply Hne1. intros ->. exact (Hnsteal e Hx). }
    split; [reflexivity|split; [exact Hbe|split; [eapply g_active_col; eauto|split; [apply (g_mincol_l _ _ _ _ _ _ G0), Hsl|
      split; [unfold cs1; rewrite LENGTH_LUPDATE; exact Hr|exact Hrl]]]]]. }
  cbn [colors int_beg int_end active colorpool phyregs colornum colormax stacknum] in *.
  exists st2, sth2. split; [exact E2|]. split; [exact G2|].
  split; [unfold cs1 in L2; rewrite LENGTH_LUPDATE in L2; exact L2|split; [exact B2|split; [exact En2|]]].
  split; [|split; [|exact M2]].
  - intros r Hm. assert (r <> reg) by (intros ->; apply Hm; apply MEM_cons_iff; left; reflexivity).
    assert (r <> stealreg) by (intros ->; apply Hm; apply MEM_cons_iff; right; apply MEM_iff, Hsl).
    rewrite <- S2 by assumption. apply Hne1; assumption.
  - intros r [Hm Hp]. assert (r <> reg) by (intros ->; contradiction).
    assert (r <> stealreg) by (intros ->; contradiction).
    rewrite <- S2 by assumption. apply Hne1; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "linear_reg_alloc_step_aux_invariants" *)
Theorem linear_reg_alloc_step_aux_invariants : forall st sth l preferred (forbidden : num_set) forced reg force mincol,
  ~ MEM reg l /\
  good_linear_scan_state st sth l (EL reg sth.(int_beg)) forced mincol /\
  reg < LENGTH sth.(colors) /\
  forbidden_is_from_map_color_forced forced l sth.(colors) reg forbidden /\
  (is_phy_var reg -> domain st.(phyregs) SUBSET domain forbidden) /\
  domain forbidden SUBSET (fun c => exists r, c = EL r sth.(colors) /\ MEM r l) /\
  (EL reg sth.(int_beg) <= EL reg sth.(int_end))%Z ->
  exists stout sthout,
    (M_success stout, sthout) = linear_reg_alloc_step_aux st forbidden preferred reg (EL reg sth.(int_end)) force sth /\
    good_linear_scan_state stout sthout (reg :: l) (EL reg sth.(int_beg)) forced mincol /\
    LENGTH sthout.(colors) = LENGTH sth.(colors) /\
    sthout.(int_beg) = sth.(int_beg) /\ sthout.(int_end) = sth.(int_end) /\
    (forall r, ~ MEM r (reg :: l) -> EL r sthout.(colors) = EL r sth.(colors)) /\
    (forall r, MEM r l /\ is_phy_var r -> EL r sthout.(colors) = EL r sth.(colors)) /\
    stout.(colormax) = st.(colormax).
Proof.
  intros st sth l preferred forbidden forced reg force mincol (Hrl & G & Hr & Hfb & Hph & Hsub & Hbe).
  pose proof G as G0; apply gls_iff in G0.
  (* turn a color_register result into the conclusion *)
  assert (Fin : forall stc col, good_linear_scan_state stc sth l (EL reg sth.(int_beg)) forced mincol ->
      col NOTIN domain forbidden -> (is_phy_var reg -> domain stc.(phyregs) SUBSET domain forbidden) ->
      ~ MEM col (stc.(colorpool) ++ MAP (fun '(e, r) => EL r sth.(colors)) stc.(active)) ->
      col < stc.(colornum) -> mincol <= col -> stc.(colormax) = st.(colormax) ->
      exists stout sthout, (M_success stout, sthout) = color_register stc reg col (EL reg sth.(int_end)) sth /\
        good_linear_scan_state stout sthout (reg :: l) (EL reg sth.(int_beg)) forced mincol /\
        LENGTH sthout.(colors) = LENGTH sth.(colors) /\
        sthout.(int_beg) = sth.(int_beg) /\ sthout.(int_end) = sth.(int_end) /\
        (forall r, ~ MEM r (reg :: l) -> EL r sthout.(colors) = EL r sth.(colors)) /\
        (forall r, MEM r l /\ is_phy_var r -> EL r sthout.(colors) = EL r sth.(colors)) /\
        stout.(colormax) = st.(colormax)).
  { intros stc col Gc Hc Hp Hm Hn Hmc Hmx.
    destruct (color_register_invariants stc sth l (EL reg sth.(int_beg)) forced reg col forbidden mincol
      (conj Gc (conj Hfb (conj Hc (conj Hp (conj Hm (conj eq_refl (conj Hbe (conj Hn (conj Hmc (conj Hr Hrl)))))))))))
      as (so & sho & E & G' & L & B & En & S & M).
    exists so, sho; split; [exact E|split; [exact G'|split; [exact L|split; [exact B|split; [exact En|split; [|split]]]]]].
    - intros r Hm'; symmetry; apply S; intros ->; apply Hm', MEM_cons_iff; left; reflexivity.
    - intros r [Hm' _]; symmetry; apply S; intros ->; contradiction.
    - congruence. }
  unfold linear_reg_alloc_step_aux.
  destruct (find_color_in_list (FILTER (fun c => MEM c (colorpool st)) preferred) forbidden) as [[col rst]|] eqn:Ef.
  - destruct (find_color_in_list_output _ _ _ _ Ef) as (Hm & Hn & _).
    apply MEM_iff, filter_In in Hm as [_ Hcp]. apply MEM_iff in Hcp.
    apply Fin.
    + apply gls_iff. apply (gls_sub_pool _ _ _ _ _ _ _ G0).
      * intros c Hc; apply filter_In in Hc as [Hc _]; exact Hc.
      * eapply ISS_NoDup; [|exact (g_distinct _ _ _ _ _ _ G0)].
        apply IS_SPARSE_SUBLIST_APPEND_RIGHT, FILTER_IS_SPARSE_SUBLIST.
    + exact Hn.
    + exact Hph.
    + intros Hm'; apply MEM_iff, in_app_or in Hm' as [Hm'|Hm'].
      * apply filter_In in Hm' as [_ X]; rewrite N.eqb_refl in X; discriminate.
      * exact (NoDup_app_disj _ _ _ (g_distinct _ _ _ _ _ _ G0) Hcp Hm').
    + exact (g_pool _ _ _ _ _ _ G0 col Hcp).
    + exact (g_mincol_pool _ _ _ _ _ _ G0 col Hcp).
    + reflexivity.
  - destruct (find_color st forbidden) as [st' [col|]] eqn:Ec.
    + destruct (find_color_invariants st forbidden st' col sth l (EL reg sth.(int_beg)) forced mincol
        (conj G (conj Hsub Ec))) as (G' & Hcn & Hcf & Est).
      apply gls_iff in G'.
      apply Fin.
      * apply gls_iff. replace st' with (set_colorpool (set_colorpool st' (col :: colorpool st')) (colorpool st'))
          by (destruct st'; reflexivity).
        apply (gls_sub_pool _ _ _ _ _ _ _ G'); [intros c Hc; right; exact Hc|].
        pose proof (g_distinct _ _ _ _ _ _ G') as D. cbn [set_colorpool colorpool active] in D |- *.
        inversion D; assumption.
      * exact Hcf.
      * rewrite Est in Hph. exact Hph.
      * pose proof (g_distinct _ _ _ _ _ _ G') as D. cbn [set_colorpool colorpool active] in D.
        inversion D as [|? ? Hn _]; subst. intros Hm; apply MEM_iff in Hm; contradiction.
      * exact Hcn.
      * apply (g_mincol_pool _ _ _ _ _ _ G'); left; reflexivity.
      * rewrite Est; reflexivity.
    + assert (st' = st).
      { unfold find_color in Ec. destruct (find_color_in_list (colorpool st) forbidden) as [[c r]|]; [discriminate|].
        unfold find_color_in_colornum in Ec. destruct (_ <=? _); congruence. }
      subst st'. apply find_spill_invariants; exact (conj Hrl (conj G (conj Hr (conj Hfb (conj Hph Hbe))))).
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "st_ex_MAP_colors_sub" *)
Theorem st_ex_MAP_colors_sub : forall l sth,
  EVERY (fun r => r <? LENGTH sth.(colors)) l ->
  st_ex_MAP colors_sub l sth = (M_success (MAP (fun r => EL r sth.(colors)) l), sth).
Proof.
  induction l as [|r l IH]; intros sth H; [reflexivity|].
  cbn [EVERY] in H; unfold is_true in H; apply andb_prop in H as [Hr H].
  cbn [st_ex_MAP]; msimp. rewrite colors_sub_eqn, Hr; cbv beta iota. rewrite IH by exact H. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "phystack_on_stack_def" *)
Definition phystack_on_stack (l : list N) (st : linear_scan_state) (sth : linear_scan_hidden_state) : Prop :=
  forall r, MEM r l /\ is_phy_var r /\ 2 * st.(colormax) <= r -> st.(colormax) <= EL r sth.(colors).

Lemma domain_fromAList_units (xs : list N) c :
  c IN domain (fromAList (MAP (fun c => (c, tt)) xs)) <-> In c xs.
Proof.
  unfold pred_set.IN; rewrite domain_fromAList; cbv beta; unfold is_true; rewrite MEM_In, List.map_map; cbn [fst].
  rewrite map_id; reflexivity.
Qed.

(** The common part of [linear_reg_alloc_step_pass1] and [pass2]: the
    forbidden colours computed from the forced adjacency list. *)
Lemma forced_forbidden_props st sth l forced reg pos mincol adj :
  gls st sth l pos forced mincol ->
  forbidden_is_from_forced_list forced l reg adj ->
  is_true (EVERY (fun r => MEM r l) adj) ->
  forbidden_is_from_map_color_forced forced l sth.(colors) reg
    (fromAList (MAP (fun c => (c, tt)) (MAP (fun r => EL r sth.(colors)) adj))) /\
  domain (fromAList (MAP (fun c => (c, tt)) (MAP (fun r => EL r sth.(colors)) adj)))
    SUBSET (fun c => exists r, c = EL r sth.(colors) /\ MEM r l).
Proof.
  intros G Hfl He. split.
  - intros reg2 H. apply domain_fromAList_units. apply (in_map (fun r => EL r sth.(colors))).
    apply MEM_iff, Hfl, H.
  - intros c Hc. apply domain_fromAList_units in Hc. apply in_map_iff in Hc as (r & <- & Hr).
    exists r; split; [reflexivity|]. apply EVERY_iff with (x := r) in He; [exact He|exact Hr].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "linear_reg_alloc_step_pass1_invariants" *)
Theorem linear_reg_alloc_step_pass1_invariants : forall st sth l moves forced_adj forced reg pos mincol,
  ~ MEM reg l /\
  good_linear_scan_state st sth l pos forced mincol /\
  (pos <= EL reg sth.(int_beg))%Z /\
  reg < LENGTH sth.(colors) /\
  forbidden_is_from_forced_list forced l reg (the [] (lookup reg forced_adj)) /\
  EVERY (fun r => MEM r l) (the [] (lookup reg forced_adj)) /\
  EVERY (fun r => r <? LENGTH sth.(colors)) (the [] (lookup reg forced_adj)) /\
  EVERY (fun r => r <? LENGTH sth.(colors)) (the [] (lookup reg moves)) /\
  (EL reg sth.(int_beg) <= EL reg sth.(int_end))%Z ->
  exists stout sthout,
    (M_success stout, sthout) = linear_reg_alloc_step_pass1 forced_adj moves st reg sth /\
    good_linear_scan_state stout sthout (reg :: l) (EL reg sth.(int_beg)) forced mincol /\
    LENGTH sthout.(colors) = LENGTH sth.(colors) /\
    sthout.(int_beg) = sth.(int_beg) /\ sthout.(int_end) = sth.(int_end) /\
    (forall r, ~ MEM r (reg :: l) -> EL r sthout.(colors) = EL r sth.(colors)) /\
    (forall r, MEM r l /\ is_phy_var r -> EL r sthout.(colors) = EL r sth.(colors)) /\
    (phystack_on_stack l st sth -> phystack_on_stack (reg :: l) stout sthout) /\
    stout.(colormax) = st.(colormax).
Proof.
  intros st sth l moves forced_adj forced reg pos mincol (Hrl & G & Hpb & Hr & Hfl & Hel & Hlf & Hlm & Hbe).
  pose proof G as G0; apply gls_iff in G0.
  destruct (remove_inactive_intervals_invariants (EL reg sth.(int_beg)) st sth l pos forced mincol (conj G Hpb))
    as (st0 & E0 & G1 & M0).
  pose proof G1 as G1'; apply gls_iff in G1'.
  assert (Hna : forall e, ~ MEM (e, reg) st0.(active)).
  { intros e Hm; apply MEM_iff in Hm. apply Hrl, MEM_iff. eapply g_active_l; eauto. }
  unfold linear_reg_alloc_step_pass1; msimp.
  rewrite int_beg_sub_eqn. destruct (N.ltb_spec reg (LENGTH sth.(int_beg))); [|pose proof (g_len_beg _ _ _ _ _ _ G0); lia].
  cbv beta iota. rewrite int_end_sub_eqn. destruct (N.ltb_spec reg (LENGTH sth.(int_end))); [|pose proof (g_len_end _ _ _ _ _ _ G0); lia].
  cbv beta iota. rewrite <- E0. cbv beta iota.
  (* conclusions from a step result *)
  assert (Fin : forall so sho,
      good_linear_scan_state so sho (reg :: l) (EL reg sth.(int_beg)) forced mincol ->
      LENGTH sho.(colors) = LENGTH sth.(colors) -> sho.(int_beg) = sth.(int_beg) -> sho.(int_end) = sth.(int_end) ->
      (forall r, ~ MEM r (reg :: l) -> EL r sho.(colors) = EL r sth.(colors)) ->
      (forall r, MEM r l /\ is_phy_var r -> EL r sho.(colors) = EL r sth.(colors)) ->
      so.(colormax) = st.(colormax) ->
      (is_phy_var reg -> 2 * st.(colormax) <= reg -> st.(colormax) <= EL reg sho.(colors)) ->
      exists stout sthout, (M_success stout, sthout) = (M_success so, sho) :> (exc linear_scan_state state_exn * linear_scan_hidden_state) /\
        good_linear_scan_state stout sthout (reg :: l) (EL reg sth.(int_beg)) forced mincol /\
        LENGTH sthout.(colors) = LENGTH sth.(colors) /\
        sthout.(int_beg) = sth.(int_beg) /\ sthout.(int_end) = sth.(int_end) /\
        (forall r, ~ MEM r (reg :: l) -> EL r sthout.(colors) = EL r sth.(colors)) /\
        (forall r, MEM r l /\ is_phy_var r -> EL r sthout.(colors) = EL r sth.(colors)) /\
        (phystack_on_stack l st sth -> phystack_on_stack (reg :: l) stout sthout) /\
        stout.(colormax) = st.(colormax)).
  { intros so sho Gs L B En S1 S2 M Hreg. exists so, sho.
    split; [reflexivity|split; [exact Gs|split; [exact L|split; [exact B|split; [exact En|split; [exact S1|split; [exact S2|split; [|exact M]]]]]]]].
    intros Hps r (Hm & Hp & Hle). rewrite M in *. apply MEM_cons_iff in Hm as [->|Hm]; [apply Hreg; auto|].
    rewrite S2 by auto. apply Hps; auto. }
  assert (Spl : forall (sho : linear_scan_hidden_state), (forall r, r <> reg -> EL r sth.(colors) = EL r sho.(colors)) ->
     (forall r, ~ MEM r (reg :: l) -> EL r sho.(colors) = EL r sth.(colors)) /\
     (forall r, MEM r l /\ is_phy_var r -> EL r sho.(colors) = EL r sth.(colors))).
  { intros sho S; split.
    - intros r Hm; symmetry; apply S; intros ->; apply Hm, MEM_cons_iff; left; reflexivity.
    - intros r [Hm _]; symmetry; apply S; intros ->; contradiction. }
  destruct (is_stack_var reg) eqn:Es.
  - assert (Hnp : ~ is_phy_var reg) by (intros Hp; apply (proj1 (proj2 (convention_partitions' reg))) in Hp as [Hn _]; apply Hn; exact Es).
    destruct (spill_register_invariants st0 sth l (EL reg sth.(int_beg)) forced reg mincol
      (conj Hna (conj (or_introl Hnp) (conj G1 (conj Hr (Z.le_refl _))))))
      as (so & sho & E & Gs & L & B & En & S & M & _).
    destruct (Spl sho S) as [S1 S2].
    rewrite <- E. apply Fin; auto; [congruence|intros Hp; contradiction].
  - rewrite st_ex_MAP_colors_sub by exact Hlf. cbv beta iota.
    destruct (forced_forbidden_props _ _ _ _ _ _ _ _ G1' Hfl Hel) as [Hfb Hsub].
    set (ff := fromAList (MAP (fun c => (c, tt)) (MAP (fun r => EL r sth.(colors)) (the [] (lookup reg forced_adj))))) in *.
    destruct (is_phy_var reg) eqn:Ep.
    + destruct (N.ltb_spec reg (2 * colormax st0)) as [Hlt|Hge].
      * destruct (linear_reg_alloc_step_aux_invariants st0 sth l [] (union (phyregs st0) ff) forced reg true mincol)
          as (so & sho & E & Gs & L & B & En & S1 & S2 & M).
        { split; [exact Hrl|split; [exact G1|split; [exact Hr|split; [|split; [|split; [|exact Hbe]]]]]].
          - intros reg2 Hq. unfold pred_set.IN; rewrite domain_union. right. apply Hfb, Hq.
          - intros _ c Hc. unfold pred_set.IN in *; rewrite domain_union. left. exact Hc.
          - intros c Hc. unfold pred_set.IN in Hc; rewrite domain_union in Hc. destruct Hc as [Hc|Hc]; [|apply Hsub, Hc].
            apply (g_phyregs _ _ _ _ _ _ G1') in Hc as (r & -> & Hx & _). exists r; split; [reflexivity|apply MEM_iff, Hx]. }
        rewrite <- E. apply Fin; auto; [congruence|intros _ Hle; lia].
      * destruct (spill_register_invariants st0 sth l (EL reg sth.(int_beg)) forced reg mincol
          (conj Hna (conj (or_intror Hrl) (conj G1 (conj Hr (Z.le_refl _))))))
          as (so & sho & E & Gs & L & B & En & S & M & Hm).
        destruct (Spl sho S) as [S1 S2].
        rewrite <- E. apply Fin; auto; [congruence|intros _ _; rewrite <- M0; exact Hm].
    + rewrite st_ex_MAP_colors_sub by exact Hlm. cbv beta iota.
      destruct (linear_reg_alloc_step_aux_invariants st0 sth l
          (MAP (fun r => EL r sth.(colors)) (the [] (lookup reg moves))) ff forced reg false mincol)
          as (so & sho & E & Gs & L & B & En & S1 & S2 & M).
      { split; [exact Hrl|split; [exact G1|split; [exact Hr|split; [exact Hfb|split; [intros X; unfold is_true in X; congruence|split; [exact Hsub|exact Hbe]]]]]]. }
      rewrite <- E. apply Fin; auto; [congruence|intros X; unfold is_true in X; congruence].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "linear_reg_alloc_step_pass2_invariants" *)
Theorem linear_reg_alloc_step_pass2_invariants : forall st sth l moves forced_adj forced reg pos mincol,
  ~ MEM reg l /\
  good_linear_scan_state st sth l pos forced mincol /\
  (pos <= EL reg sth.(int_beg))%Z /\
  reg < LENGTH sth.(colors) /\
  forbidden_is_from_forced_list forced l reg (the [] (lookup reg forced_adj)) /\
  EVERY (fun r => MEM r l) (the [] (lookup reg forced_adj)) /\
  EVERY (fun r => r <? LENGTH sth.(colors)) (the [] (lookup reg forced_adj)) /\
  EVERY (fun r => r <? LENGTH sth.(colors)) (the [] (lookup reg moves)) /\
  (EL reg sth.(int_beg) <= EL reg sth.(int_end))%Z ->
  exists stout sthout,
    (M_success stout, sthout) = linear_reg_alloc_step_pass2 forced_adj moves st reg sth /\
    good_linear_scan_state stout sthout (reg :: l) (EL reg sth.(int_beg)) forced mincol /\
    LENGTH sthout.(colors) = LENGTH sth.(colors) /\
    sthout.(int_beg) = sth.(int_beg) /\ sthout.(int_end) = sth.(int_end) /\
    (forall r, ~ MEM r (reg :: l) -> EL r sthout.(colors) = EL r sth.(colors)) /\
    (forall r, MEM r l /\ is_phy_var r -> EL r sthout.(colors) = EL r sth.(colors)) /\
    stout.(colormax) = st.(colormax).
Proof.
  intros st sth l moves forced_adj forced reg pos mincol (Hrl & G & Hpb & Hr & Hfl & Hel & Hlf & Hlm & Hbe).
  pose proof G as G0; apply gls_iff in G0.
  destruct (remove_inactive_intervals_invariants (EL reg sth.(int_beg)) st sth l pos forced mincol (conj G Hpb))
    as (st0 & E0 & G1 & M0).
  pose proof G1 as G1'; apply gls_iff in G1'.
  unfold linear_reg_alloc_step_pass2; msimp.
  rewrite int_beg_sub_eqn. destruct (N.ltb_spec reg (LENGTH sth.(int_beg))); [|pose proof (g_len_beg _ _ _ _ _ _ G0); lia].
  cbv beta iota. rewrite int_end_sub_eqn. destruct (N.ltb_spec reg (LENGTH sth.(int_end))); [|pose proof (g_len_end _ _ _ _ _ _ G0); lia].
  cbv beta iota. rewrite <- E0. cbv beta iota.
  rewrite st_ex_MAP_colors_sub by exact Hlf. cbv beta iota.
  rewrite st_ex_MAP_colors_sub by exact Hlm. cbv beta iota.
  destruct (forced_forbidden_props _ _ _ _ _ _ _ _ G1' Hfl Hel) as [Hfb Hsub].
  set (ff := fromAList (MAP (fun c => (c, tt)) (MAP (fun r => EL r sth.(colors)) (the [] (lookup reg forced_adj))))) in *.
  destruct (is_phy_var reg) eqn:Ep.
  - destruct (linear_reg_alloc_step_aux_invariants st0 sth l [] (union (phyregs st0) ff) forced reg false mincol)
      as (so & sho & E & Gs & L & B & En & S1 & S2 & M).
    { split; [exact Hrl|split; [exact G1|split; [exact Hr|split; [|split; [|split; [|exact Hbe]]]]]].
      - intros reg2 Hq. unfold pred_set.IN; rewrite domain_union. right. apply Hfb, Hq.
      - intros _ c Hc. unfold pred_set.IN in *; rewrite domain_union. left. exact Hc.
      - intros c Hc. unfold pred_set.IN in Hc; rewrite domain_union in Hc. destruct Hc as [Hc|Hc]; [|apply Hsub, Hc].
        apply (g_phyregs _ _ _ _ _ _ G1') in Hc as (r & -> & Hx & _). exists r; split; [reflexivity|apply MEM_iff, Hx]. }
    exists so, sho; split; [exact E|split; [exact Gs|split; [exact L|split; [exact B|split; [exact En|split; [exact S1|split; [exact S2|congruence]]]]]]].
  - destruct (linear_reg_alloc_step_aux_invariants st0 sth l
        (MAP (fun r => EL r sth.(colors)) (the [] (lookup reg moves))) ff forced reg false mincol)
        as (so & sho & E & Gs & L & B & En & S1 & S2 & M).
    { split; [exact Hrl|split; [exact G1|split; [exact Hr|split; [exact Hfb|split; [intros X; unfold is_true in X; congruence|split; [exact Hsub|exact Hbe]]]]]]. }
    exists so, sho; split; [exact E|split; [exact Gs|split; [exact L|split; [exact B|split; [exact En|split; [exact S1|split; [exact S2|congruence]]]]]]].
Qed.

Ltac ev H := let X := fresh in pose proof (proj1 (EVERY_iff _ _) H) as X; clear H; rename X into H.

(** "TODO: move" *)
(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "intbeg_less_def" *)
Definition intbeg_less (int_beg : list Z) (r1 r2 : N) : Prop :=
  LEX Z.lt N.le (EL r1 int_beg, r1) (EL r2 int_beg, r2).

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "intbeg_less_transitive" *)
Theorem intbeg_less_transitive : forall int_beg, transitive (intbeg_less int_beg).
Proof. unfold transitive, intbeg_less, LEX; intros; lia. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "intbeg_less_total" *)
Theorem intbeg_less_total : forall int_beg, total (intbeg_less int_beg).
Proof. unfold total, intbeg_less, LEX; intros; lia. Qed.

Lemma MEM_app_iff {A} `{EqDecision A} (x : A) l1 l2 : is_true (MEM x (l1 ++ l2)) <-> In x l1 \/ In x l2.
Proof. rewrite MEM_iff, in_app_iff; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "st_ex_FOLDL_linear_reg_alloc_step_passn_invariants_lemma" *)
Theorem st_ex_FOLDL_linear_reg_alloc_step_passn_invariants_lemma :
  forall regl st sth l pos (b : bool) moves forced_adj forced mincol,
  SORTED (intbeg_less sth.(int_beg)) regl /\
  (forall r1 r2, MEM r1 l /\ MEM r2 regl -> intbeg_less sth.(int_beg) r1 r2) /\
  ALL_DISTINCT regl /\
  EVERY (fun r => negb (MEM r regl)) l /\
  good_linear_scan_state st sth l pos forced mincol /\
  EVERY (fun r => (pos <=? EL r sth.(int_beg))%Z) regl /\
  EVERY (fun r => r <? LENGTH sth.(colors)) regl /\
  (forall r, forbidden_is_from_forced_sublist (l ++ regl) forced sth.(int_beg) r (the [] (lookup r forced_adj))) /\
  EVERY (fun '(r1, r2) => MEM r1 (l ++ regl) && MEM r2 (l ++ regl)) forced /\
  (forall r1, EVERY (fun r2 => r2 <? LENGTH sth.(colors)) (the [] (lookup r1 forced_adj))) /\
  (forall r1, EVERY (fun r2 => r2 <? LENGTH sth.(colors)) (the [] (lookup r1 moves))) /\
  EVERY (fun r => (EL r sth.(int_beg) <=? EL r sth.(int_end))%Z) regl ->
  exists stout sthout posout,
    (M_success stout, sthout) =
      st_ex_FOLDL ((if b then linear_reg_alloc_step_pass1 else linear_reg_alloc_step_pass2) forced_adj moves) st regl sth /\
    good_linear_scan_state stout sthout (REVERSE regl ++ l) posout forced mincol /\
    LENGTH sthout.(colors) = LENGTH sth.(colors) /\
    sthout.(int_beg) = sth.(int_beg) /\ sthout.(int_end) = sth.(int_end) /\
    (forall r, ~ MEM r (l ++ regl) -> EL r sthout.(colors) = EL r sth.(colors)) /\
    (b -> (phystack_on_stack l st sth -> phystack_on_stack (REVERSE regl ++ l) stout sthout)) /\
    stout.(colormax) = st.(colormax).
Proof.
  induction regl as [|h regl IH];
    intros st sth l pos b moves forced_adj forced mincol
      (Hs & Hlr & Hd & Hnl & G & Hpos & Hlt & Hfs & Hfm & Hfa & Hma & Hbe).
  - exists st, sth, pos. cbn [REVERSE rev app st_ex_FOLDL].
    split; [reflexivity|split; [exact G|split; [reflexivity|split; [reflexivity|split; [reflexivity|
      split; [reflexivity|split; [intros _ X; exact X|reflexivity]]]]]]].
  - pose proof (intbeg_less_transitive (int_beg sth)) as T.
    apply (SORTED_EQ _ _ _ T) in Hs as [Hs Hhd].
    apply ALL_DISTINCT_iff in Hd; inversion Hd as [|? ? Hhn Hd']; subst.
    ev Hnl; ev Hpos; ev Hlt; ev Hbe; ev Hfm.
    assert (Hhl : ~ In h l).
    { intros Hx; specialize (Hnl h Hx). cbn [MEM] in Hnl.
      rewrite (proj2 (bool_decide_spec (h = h)) eq_refl) in Hnl. discriminate. }
    assert (Hh1 : In h (h :: regl)) by (left; reflexivity).
    assert (Ladj : is_true (EVERY (fun r => MEM r l) (the [] (lookup h forced_adj)))).
    { apply EVERY_iff; intros r Hr. destruct (proj2 (Hfs h r) (conj (proj2 (MEM_iff _ _) Hr) (proj2 (MEM_iff _ _)
        (in_or_app _ _ _ (or_intror Hh1))))) as (Hn & Hp & Hl').
      assert (Hrin : In r (l ++ h :: regl)).
      { destruct Hp as [Hp|Hp]; apply MEM_iff in Hp; specialize (Hfm _ Hp); cbn beta iota in Hfm;
          apply andb_prop in Hfm as [H1 H2]; apply MEM_iff; assumption. }
      apply in_app_or in Hrin as [Hrin|[<-|Hrin]]; [apply MEM_iff, Hrin|congruence|].
      exfalso. pose proof (Hhd r Hrin) as Hhr. unfold intbeg_less, LEX in Hhr, Hl'. lia. }
    assert (Lfl : forbidden_is_from_forced_list forced l h (the [] (lookup h forced_adj))).
    { intros reg2 (Hm & Hp). apply MEM_iff in Hm.
      assert (Hn : h <> reg2) by (intros ->; contradiction).
      assert (Hil : intbeg_less (int_beg sth) reg2 h) by (apply Hlr; split; apply MEM_iff; [exact Hm|exact Hh1]).
      apply (proj1 (Hfs h reg2) (conj Hn (conj Hp Hil))). }
    assert (Hlt' : is_true (EVERY (fun r => r <? LENGTH sth.(colors)) (h :: regl))) by (apply EVERY_iff; exact Hlt).
    clear Hlt; rename Hlt' into Hlt.
    assert (Hstep : exists stmid sthmid,
      (M_success stmid, sthmid) = (if b then linear_reg_alloc_step_pass1 else linear_reg_alloc_step_pass2) forced_adj moves st h sth /\
      good_linear_scan_state stmid sthmid (h :: l) (EL h sth.(int_beg)) forced mincol /\
      LENGTH sthmid.(colors) = LENGTH sth.(colors) /\ sthmid.(int_beg) = sth.(int_beg) /\ sthmid.(int_end) = sth.(int_end) /\
      (forall r, ~ MEM r (h :: l) -> EL r sthmid.(colors) = EL r sth.(colors)) /\
      (b -> (phystack_on_stack l st sth -> phystack_on_stack (h :: l) stmid sthmid)) /\
      stmid.(colormax) = st.(colormax)).
    { assert (Hnm : ~ MEM h l) by (intros Hm; apply MEM_iff in Hm; contradiction).
      pose proof (Hpos h Hh1) as P; apply Z.leb_le in P.
      cbn [EVERY] in Hlt; unfold is_true in Hlt; apply andb_prop in Hlt as [Hlth _]; apply N.ltb_lt in Hlth.
      pose proof (Hbe h Hh1) as Be; apply Z.leb_le in Be.
      destruct b.
      - destruct (linear_reg_alloc_step_pass1_invariants st sth l moves forced_adj forced h pos mincol
          (conj Hnm (conj G (conj P (conj Hlth (conj Lfl (conj Ladj (conj (Hfa h) (conj (Hma h) Be)))))))))
          as (so & sho & E & Gs & L & B & En & S1 & _ & Ph & M).
        exists so, sho; repeat (split; [eassumption|]); split; [intros _; exact Ph|exact M].
      - destruct (linear_reg_alloc_step_pass2_invariants st sth l moves forced_adj forced h pos mincol
          (conj Hnm (conj G (conj P (conj Hlth (conj Lfl (conj Ladj (conj (Hfa h) (conj (Hma h) Be)))))))))
          as (so & sho & E & Gs & L & B & En & S1 & _ & M).
        exists so, sho; repeat (split; [eassumption|]); split; [intros X; discriminate X|exact M]. }
    destruct Hstep as (stm & shm & Em & Gm & Lm & Bm & Enm & Sm & Pm & Mm).
    cbn [EVERY] in Hlt; unfold is_true in Hlt; apply andb_prop in Hlt as [_ Hlt].
    destruct (IH stm shm (h :: l) (EL h sth.(int_beg)) b moves forced_adj forced mincol) as
      (so & sho & po & E & Gs & L & B & En & S & Ph & M).
    { rewrite Bm, Enm, Lm. split; [exact Hs|]. split.
      { intros r1 r2 [H1 H2]; apply MEM_iff in H1, H2. destruct H1 as [<-|H1]; [apply Hhd, H2|].
        apply Hlr; split; apply MEM_iff; [exact H1|right; exact H2]. }
      split; [apply ALL_DISTINCT_iff, Hd'|]. split.
      { apply EVERY_iff; intros r [<-|Hr]; apply negb_true_iff, not_true_iff_false; intros Hm; apply MEM_iff in Hm;
          [contradiction|]. specialize (Hnl r Hr); apply negb_true_iff, not_true_iff_false in Hnl; apply Hnl.
        apply MEM_cons_iff; right; apply MEM_iff, Hm. }
      split; [exact Gm|]. split.
      { apply EVERY_iff; intros r Hr. apply Z.leb_le. pose proof (Hhd r Hr) as X; unfold intbeg_less, LEX in X; lia. }
      split; [exact Hlt|]. split.
      { intros r reg2. rewrite (Hfs r reg2). rewrite !MEM_app_iff. cbn [In]. tauto. }
      split.
      { apply EVERY_iff; intros [r1 r2] Hx. specialize (Hfm _ Hx). cbn beta iota in Hfm |- *.
        apply andb_prop in Hfm as [F1 F2]. apply MEM_app_iff in F1, F2.
        apply andb_true_intro; split; apply MEM_app_iff; cbn [In] in *; tauto. }
      split; [exact Hfa|split; [exact Hma|]].
      apply EVERY_iff; intros r Hr; apply Hbe; right; exact Hr. }
    exists so, sho, po. cbn [st_ex_FOLDL]; msimp. rewrite <- Em. cbv beta iota.
    split; [exact E|]. split; [cbn [REVERSE rev]; rewrite <- app_assoc; exact Gs|].
    split; [congruence|split; [congruence|split; [congruence|split; [|split; [|congruence]]]]].
    + intros r Hm. rewrite S; [apply Sm|].
      * intros X; apply Hm. apply MEM_cons_iff in X; apply MEM_app_iff.
        destruct X as [->|X]; [right; left; reflexivity|left; apply MEM_iff, X].
      * intros X; apply Hm. apply MEM_app_iff in X; apply MEM_app_iff; cbn [In] in *; tauto.
    + intros Hb Hp. specialize (Ph Hb (Pm Hb Hp)). cbn [REVERSE rev]; rewrite <- app_assoc; exact Ph.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "st_ex_FOLDL_linear_reg_alloc_step_passn_invariants" *)
Theorem st_ex_FOLDL_linear_reg_alloc_step_passn_invariants :
  forall regl st sth pos (b : bool) moves forced_adj forced mincol,
  SORTED (intbeg_less sth.(int_beg)) regl /\
  ALL_DISTINCT regl /\
  good_linear_scan_state st sth [] pos forced mincol /\
  EVERY (fun r => (pos <=? EL r sth.(int_beg))%Z) regl /\
  EVERY (fun r => r <? LENGTH sth.(colors)) regl /\
  (forall r, forbidden_is_from_forced_sublist regl forced sth.(int_beg) r (the [] (lookup r forced_adj))) /\
  EVERY (fun '(r1, r2) => MEM r1 regl && MEM r2 regl) forced /\
  (forall r1, EVERY (fun r2 => r2 <? LENGTH sth.(colors)) (the [] (lookup r1 forced_adj))) /\
  (forall r1, EVERY (fun r2 => r2 <? LENGTH sth.(colors)) (the [] (lookup r1 moves))) /\
  EVERY (fun r => (EL r sth.(int_beg) <=? EL r sth.(int_end))%Z) regl ->
  exists stout sthout posout,
    (M_success stout, sthout) =
      st_ex_FOLDL ((if b then linear_reg_alloc_step_pass1 else linear_reg_alloc_step_pass2) forced_adj moves) st regl sth /\
    good_linear_scan_state stout sthout (REVERSE regl) posout forced mincol /\
    LENGTH sthout.(colors) = LENGTH sth.(colors) /\
    sthout.(int_beg) = sth.(int_beg) /\ sthout.(int_end) = sth.(int_end) /\
    (forall r, ~ MEM r regl -> EL r sthout.(colors) = EL r sth.(colors)) /\
    (b -> phystack_on_stack (REVERSE regl) stout sthout) /\
    stout.(colormax) = st.(colormax).
Proof.
  intros regl st sth pos b moves forced_adj forced mincol (Hs & Hd & G & Hp & Hl & Hf & Hfm & Ha & Hm & Hbe).
  destruct (st_ex_FOLDL_linear_reg_alloc_step_passn_invariants_lemma regl st sth [] pos b moves forced_adj forced mincol)
    as (so & sho & po & E & Gs & L & B & En & S & Ph & M).
  { split; [exact Hs|split; [intros r1 r2 [X _]; discriminate X|split; [exact Hd|split; [reflexivity|]]]].
    repeat (split; [eassumption|]). exact Hbe. }
  rewrite app_nil_r in Gs, Ph. exists so, sho, po.
  repeat (split; [eassumption|]). split; [|exact M].
  intros Hb; apply Ph; [exact Hb|]. intros r (X & _); discriminate X.
Qed.

(** ** In-place quicksorts *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "swap_regs_eq" *)
Theorem swap_regs_eq : forall sth i1 i2,
  i1 < LENGTH sth.(sorted_regs) /\ i2 < LENGTH sth.(sorted_regs) ->
  exists sthout, swap_regs i1 i2 sth = (M_success tt, sthout) /\
  sthout = {| colors := sth.(colors); int_beg := sth.(int_beg); int_end := sth.(int_end);
              sorted_regs := LUPDATE (EL i1 sth.(sorted_regs)) i2
                               (LUPDATE (EL i2 sth.(sorted_regs)) i1 sth.(sorted_regs));
              sorted_moves := sth.(sorted_moves) |}.
Proof.
  intros sth i1 i2 [H1 H2]; unfold swap_regs; msimp.
  rewrite sorted_regs_sub_eqn; destruct (N.ltb_spec i1 (LENGTH sth.(sorted_regs))); [|lia]; cbv beta iota.
  rewrite sorted_regs_sub_eqn; destruct (N.ltb_spec i2 (LENGTH sth.(sorted_regs))); [|lia]; cbv beta iota.
  rewrite update_sorted_regs_eqn; destruct (N.ltb_spec i1 (LENGTH sth.(sorted_regs))); [|lia]; cbv beta iota.
  rewrite update_sorted_regs_eqn; cbn [sorted_regs]. rewrite LENGTH_LUPDATE.
  destruct (N.ltb_spec i2 (LENGTH sth.(sorted_regs))); [|lia]. eexists; split; reflexivity.
Qed.

(** "TODO: move" *)
(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "if_thm" *)
Theorem if_thm : forall (b : bool) {A} (x y z : A), (if b then x else y) = z <-> ((b /\ x = z) \/ (~ b /\ y = z)).
Proof. intros [] A x y z; cbn; unfold is_true; intuition congruence. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "split_at_indice_sing" *)
Theorem split_at_indice_sing : forall {A} (l : list A) i,
  i < LENGTH l ->
  exists l1 x l2, l = l1 ++ [x] ++ l2 /\ LENGTH l1 = i.
Proof.
  intros A l; induction l as [|h l IH]; intros i Hi; cbn [LENGTH] in Hi; [lia|].
  destruct (N.eqb_spec i 0) as [->|Hn]; [exists [], h, l; split; reflexivity|].
  destruct (IH (i - 1) ltac:(lia)) as (l1 & x & l2 & -> & Hl).
  exists (h :: l1), x, l2; split; [reflexivity|cbn [LENGTH]; lia].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "split_at_indice" *)
Theorem split_at_indice : forall {A} (l : list A) i,
  i <= LENGTH l ->
  exists l1 l2, l = l1 ++ l2 /\ LENGTH l1 = i.
Proof.
  intros A l; induction l as [|h l IH]; intros i Hi; cbn [LENGTH] in Hi.
  - exists [], []; split; [reflexivity|cbn; lia].
  - destruct (N.eqb_spec i 0) as [->|Hn]; [exists [], (h :: l); split; reflexivity|].
    destruct (IH (i - 1) ltac:(lia)) as (l1 & l2 & -> & Hl).
    exists (h :: l1), l2; split; [reflexivity|cbn [LENGTH]; lia].
Qed.

Lemma EL_app_mid {A} `{Inhabited A} (a : list A) x r : EL (LENGTH a) (a ++ x :: r) = x.
Proof. induction a as [|y a IH]; [reflexivity|]. cbn [app LENGTH]. rewrite EL_SUC; exact IH. Qed.

Lemma LUPDATE_mid {A} (v : A) (a : list A) x r : LUPDATE v (LENGTH a) (a ++ x :: r) = a ++ v :: r.
Proof.
  induction a as [|y a IH]; [reflexivity|]. cbn [app LENGTH LUPDATE].
  destruct (N.eqb_spec (SUC (LENGTH a)) 0); [lia|]. rewrite N.pred_succ, IH; reflexivity.
Qed.

Lemma PERM_Perm {A} (l1 l2 : list A) : Permutation l1 l2 -> PERM l1 l2.
Proof. apply PERM_Permutation. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "swap_perm_lemma" *)
Theorem swap_perm_lemma : forall {A} `{Inhabited A} (l : list A) i1 i2,
  i1 < LENGTH l /\ i2 < LENGTH l ->
  PERM l (LUPDATE (EL i1 l) i2 (LUPDATE (EL i2 l) i1 l)).
Proof.
  intros A IA l i1 i2 [H1 H2]. apply PERM_Perm.
  assert (G : forall j1 j2, j1 < j2 -> j2 < LENGTH l ->
    Permutation l (LUPDATE (EL j1 l) j2 (LUPDATE (EL j2 l) j1 l))).
  { intros j1 j2 Hlt Hj2.
    destruct (split_at_indice_sing l j2 Hj2) as (m & y & c & -> & Hm). cbn [app] in *.
    assert (Hj1 : j1 < LENGTH m) by (rewrite Hm; lia).
    destruct (split_at_indice_sing m j1 Hj1) as (a & x & b & -> & Ha). cbn [app] in *.
    subst j1 j2. rewrite (EL_app_mid (a ++ x :: b)).
    replace ((a ++ x :: b) ++ y :: c) with (a ++ x :: (b ++ y :: c)) by (rewrite <- app_assoc; reflexivity).
    rewrite EL_app_mid, LUPDATE_mid.
    replace (LENGTH (a ++ x :: b)) with (LENGTH (a ++ y :: b)) by (rewrite !LENGTH_app; reflexivity).
    replace (a ++ y :: b ++ y :: c) with ((a ++ y :: b) ++ y :: c) by (rewrite <- app_assoc; reflexivity).
    rewrite LUPDATE_mid, <- app_assoc. cbn [app]. apply Permutation_app_head.
    rewrite <- Permutation_middle. rewrite perm_swap. apply perm_skip. apply Permutation_middle. }
  destruct (N.lt_trichotomy i1 i2) as [Hlt|[->|Hgt]].
  - apply G; assumption.
  - assert (E : LUPDATE (EL i2 l) i2 (LUPDATE (EL i2 l) i2 l) = l).
    { apply (LIST_EQ (LUPDATE (EL i2 l) i2 (LUPDATE (EL i2 l) i2 l)) l); [rewrite !LENGTH_LUPDATE; reflexivity|].
      intros i Hi. rewrite !LENGTH_LUPDATE in Hi. rewrite !EL_LUPDATE_dec by (rewrite ?LENGTH_LUPDATE; assumption).
      destruct (decide (i = i2)) as [->|]; reflexivity. }
    rewrite E; reflexivity.
  - assert (E : LUPDATE (EL i1 l) i2 (LUPDATE (EL i2 l) i1 l) = LUPDATE (EL i2 l) i1 (LUPDATE (EL i1 l) i2 l)).
    { apply (LIST_EQ (LUPDATE (EL i1 l) i2 (LUPDATE (EL i2 l) i1 l)) (LUPDATE (EL i2 l) i1 (LUPDATE (EL i1 l) i2 l)));
        [rewrite !LENGTH_LUPDATE; reflexivity|]. intros i Hi. rewrite !LENGTH_LUPDATE in Hi.
      rewrite !EL_LUPDATE_dec by (rewrite ?LENGTH_LUPDATE; assumption).
      destruct (decide (i = i2)), (decide (i = i1)); subst; try lia; reflexivity. }
    rewrite E. apply G; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "LUPDATE_TAKE" *)
Theorem LUPDATE_TAKE : forall {A} `{Inhabited A} n x (y : A) l,
  x < n /\ n <= LENGTH l -> TAKE n (LUPDATE y x l) = LUPDATE y x (TAKE n l).
Proof.
  intros A IA n x y l [H1 H2].
  apply (LIST_EQ (TAKE n (LUPDATE y x l)) (LUPDATE y x (TAKE n l))).
  - rewrite LENGTH_LUPDATE, !LENGTH_TAKE', LENGTH_LUPDATE; reflexivity.
  - intros i Hi. rewrite LENGTH_TAKE', LENGTH_LUPDATE in Hi.
    rewrite EL_TAKE by lia. rewrite !EL_LUPDATE, LENGTH_TAKE'. rewrite EL_TAKE by lia.
    nsplit; try lia; reflexivity.
Qed.

Definition with_sorted_regs (sth : linear_scan_hidden_state) x : linear_scan_hidden_state :=
  {| colors := sth.(colors); int_beg := sth.(int_beg); int_end := sth.(int_end);
     sorted_regs := x; sorted_moves := sth.(sorted_moves) |}.
Definition with_sorted_moves (sth : linear_scan_hidden_state) x : linear_scan_hidden_state :=
  {| colors := sth.(colors); int_beg := sth.(int_beg); int_end := sth.(int_end);
     sorted_regs := sth.(sorted_regs); sorted_moves := x |}.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "swap_regs_perm" *)
Theorem swap_regs_perm : forall sth i1 i2 sthout,
  swap_regs i1 i2 sth = (M_success tt, sthout) ->
  (forall n, i1 < n /\ i2 < n /\ n <= LENGTH sth.(sorted_regs) ->
     PERM (TAKE n sth.(sorted_regs)) (TAKE n sthout.(sorted_regs))).
Proof.
  intros sth i1 i2 sthout E n (H1 & H2 & H3).
  destruct (swap_regs_eq sth i1 i2 ltac:(lia)) as (so & E' & ->). rewrite E' in E. injection E as <-.
  cbn [sorted_regs]. rewrite !LUPDATE_TAKE by (rewrite ?LENGTH_LUPDATE; lia).
  rewrite <- (EL_TAKE n i1 (sorted_regs sth)), <- (EL_TAKE n i2 (sorted_regs sth)) by lia.
  apply swap_perm_lemma. rewrite LENGTH_TAKE'; lia.
Qed.

Lemma PERM_trans {A} (a b c : list A) : PERM a b -> PERM b c -> PERM a c.
Proof. rewrite !PERM_Permutation; apply Permutation_trans. Qed.

Lemma PERM_refl {A} (a : list A) : PERM a a.
Proof. intros x; reflexivity. Qed.

Lemma sorted_regs_sub_ok sth i : i < LENGTH sth.(sorted_regs) ->
  sorted_regs_sub i sth = (M_success (EL i sth.(sorted_regs)), sth).
Proof. intros H; rewrite sorted_regs_sub_eqn; destruct (N.ltb_spec i (LENGTH sth.(sorted_regs))); [reflexivity|lia]. Qed.

Lemma int_beg_sub_ok sth i : i < LENGTH sth.(int_beg) ->
  int_beg_sub i sth = (M_success (EL i sth.(int_beg)), sth).
Proof. intros H; rewrite int_beg_sub_eqn; destruct (N.ltb_spec i (LENGTH sth.(int_beg))); [reflexivity|lia]. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "partition_regs_correct" *)
Theorem partition_regs_correct : forall l rpiv begrpiv r sth,
  (forall i, l <= i /\ i < r -> EL i sth.(sorted_regs) < LENGTH sth.(int_beg)) /\
  l <= LENGTH sth.(sorted_regs) /\
  r <= LENGTH sth.(sorted_regs) ->
  exists mid sthout, partition_regs l rpiv begrpiv r sth = (M_success mid, sthout) /\
    sthout = with_sorted_regs sth sthout.(sorted_regs) /\
    LENGTH sthout.(sorted_regs) = LENGTH sth.(sorted_regs) /\
    (l <= r -> l <= mid /\ mid <= r) /\
    (forall n, l <= n /\ r <= n /\ n <= LENGTH sth.(sorted_regs) ->
       PERM (TAKE n sth.(sorted_regs)) (TAKE n sthout.(sorted_regs))) /\
    (forall ind, ind < l \/ r <= ind -> EL ind sthout.(sorted_regs) = EL ind sth.(sorted_regs)) /\
    (forall ind, l <= ind /\ ind < mid ->
       let reg := EL ind sthout.(sorted_regs) in
       LEX Z.lt N.le (EL reg sth.(int_beg), reg) (begrpiv, rpiv)) /\
    (forall ind, mid <= ind /\ ind < r ->
       let reg := EL ind sthout.(sorted_regs) in
       LEX Z.lt N.le (begrpiv, rpiv) (EL reg sth.(int_beg), reg)).
Proof.
  intros l rpiv begrpiv r sth. remember (r - l) as m eqn:Em. revert l r sth Em.
  induction m as [m IH] using (well_founded_induction N.lt_wf_0).
  intros l r sth Em (Hb & Hl & Hr). rewrite partition_regs_def.
  destruct (N.leb_spec r l) as [Hle|Hgt].
  - exists l, sth. split; [reflexivity|]. split; [destruct sth; reflexivity|].
    repeat split; try lia; intros; try (apply PERM_refl); try reflexivity; lia.
  - msimp. rewrite sorted_regs_sub_ok by lia. cbv beta iota.
    set (reg := EL l (sorted_regs sth)).
    rewrite int_beg_sub_ok by (apply Hb; lia). cbv beta iota.
    destruct ((EL reg (int_beg sth) <? begrpiv)%Z || ((EL reg (int_beg sth) =? begrpiv)%Z && (reg <=? rpiv))) eqn:C.
    + destruct (IH (r - (l + 1)) ltac:(lia) (l + 1) r sth eq_refl) as (mid & so & E & Es & L & Rg & P & U & Lt & Ge).
      { split; [intros i Hi; apply Hb; lia|split; lia]. }
      exists mid, so. split; [exact E|split; [exact Es|split; [exact L|]]].
      split; [intros _; specialize (Rg ltac:(lia)); lia|].
      split; [intros n Hn; apply P; lia|]. split; [intros ind Hi; apply U; lia|].
      split; [|intros ind Hi; apply Ge; lia].
      intros ind Hi. destruct (N.eq_dec ind l) as [->|Hn]; [|apply Lt; lia].
      cbv zeta. rewrite U by lia. fold reg. unfold LEX.
      apply orb_true_iff in C as [C|C]; [apply Z.ltb_lt in C; lia|].
      apply andb_true_iff in C as [C1 C2]; apply Z.eqb_eq in C1; apply N.leb_le in C2; lia.
    + destruct (swap_regs_eq sth l (r - 1) ltac:(lia)) as (sw & Esw & ->). rewrite Esw. cbv beta iota.
      set (sw := {| colors := colors sth; int_beg := int_beg sth; int_end := int_end sth;
        sorted_regs := LUPDATE (EL l (sorted_regs sth)) (r - 1) (LUPDATE (EL (r - 1) (sorted_regs sth)) l (sorted_regs sth));
        sorted_moves := sorted_moves sth |}).
      assert (Lsw : LENGTH (sorted_regs sw) = LENGTH (sorted_regs sth)) by (cbn; rewrite !LENGTH_LUPDATE; reflexivity).
      assert (ELsw : forall i, EL i (sorted_regs sw) =
        if decide (i = r - 1) then EL l (sorted_regs sth) else if decide (i = l) then EL (r - 1) (sorted_regs sth)
        else EL i (sorted_regs sth)).
      { intros i; cbn [sw sorted_regs]. rewrite !EL_LUPDATE_dec by (rewrite ?LENGTH_LUPDATE; lia). reflexivity. }
      destruct (IH (r - 1 - l) ltac:(lia) l (r - 1) sw eq_refl) as (mid & so & E & Es & L & Rg & P & U & Lt & Ge).
      { split; [|split; lia]. intros i Hi; cbn [sw int_beg]. rewrite ELsw.
        destruct (decide (i = r - 1)); [lia|]. destruct (decide (i = l)); apply Hb; lia. }
      exists mid, so. cbn [sw int_beg] in Lt, Ge.
      split; [exact E|split; [rewrite Es; reflexivity|split; [lia|]]].
      split; [intros _; specialize (Rg ltac:(lia)); lia|].
      split.
      { intros n Hn. apply (PERM_trans _ (TAKE n (sorted_regs sw))).
        - apply (swap_regs_perm sth l (r - 1) sw); [exact Esw|lia].
        - apply P; lia. }
      split.
      { intros ind Hi. rewrite U by lia. rewrite ELsw. destruct (decide (ind = r - 1)); [lia|].
        destruct (decide (ind = l)); [lia|reflexivity]. }
      split; [exact Lt|].
      intros ind Hi. destruct (N.eq_dec ind (r - 1)) as [->|Hn]; [|apply Ge; lia].
      cbv zeta. rewrite U by lia. rewrite ELsw. destruct (decide (r - 1 = r - 1)); [|congruence]. fold reg.
      unfold LEX. apply orb_false_iff in C as [C1 C2]. apply Z.ltb_ge in C1.
      apply andb_false_iff in C2 as [C2|C2]; [apply Z.eqb_neq in C2; lia|apply N.leb_gt in C2; lia].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "PERM_EVERY_EQ" *)
Theorem PERM_EVERY_EQ : forall {A} (P : A -> bool) l1 l2,
  PERM l1 l2 -> (EVERY P l1 <-> EVERY P l2).
Proof.
  intros A P l1 l2 Hp; apply PERM_Permutation in Hp. rewrite !EVERY_iff.
  split; intros H x Hx; apply H; [eapply Permutation_in; [symmetry; exact Hp|exact Hx]|eapply Permutation_in; [exact Hp|exact Hx]].
Qed.

Section Segments.
Context {A : Type} `{Inhabited A}.

Lemma TAKE_DROP (l : list A) a : TAKE a l ++ DROP a l = l.
Proof.
  revert a; induction l as [|x l IH]; intros a; cbn [TAKE DROP]; [reflexivity|].
  destruct (N.eqb_spec a 0); [reflexivity|]. cbn [app]; rewrite IH; reflexivity.
Qed.

Lemma DROP_DROP (l : list A) m n : DROP m (DROP n l) = DROP (m + n) l.
Proof.
  revert n; induction l as [|x l IH]; intros n; cbn [DROP].
  - destruct (m + n =? 0); reflexivity.
  - destruct (N.eqb_spec n 0) as [->|Hn]; [rewrite N.add_0_r; reflexivity|].
    rewrite IH. destruct (N.eqb_spec (m + n) 0); [lia|]. f_equal; lia.
Qed.

Lemma seg_decomp (l : list A) a b : a <= b ->
  l = TAKE a l ++ (TAKE (b - a) (DROP a l) ++ DROP b l).
Proof.
  intros Hab. replace (DROP b l) with (DROP (b - a) (DROP a l)) by (rewrite DROP_DROP; f_equal; lia).
  rewrite !TAKE_DROP. reflexivity.
Qed.

Lemma seg_prop (P : A -> Prop) (l1 l2 : list A) l r :
  l <= LENGTH l1 -> r <= LENGTH l1 ->
  (forall ind, ind < l \/ r <= ind -> EL ind l2 = EL ind l1) ->
  (forall ind, l <= ind /\ ind < r -> P (EL ind l1)) ->
  Permutation l1 l2 ->
  (forall ind, l <= ind /\ ind < r -> P (EL ind l2)).
Proof.
  intros Hl Hr Hout Hin Hp ind Hi.
  assert (Len : LENGTH l2 = LENGTH l1) by (rewrite !LENGTH_length; f_equal; symmetry; apply Permutation_length, Hp).
  assert (Hlr : l <= r) by lia.
  pose proof (seg_decomp l1 l r Hlr) as D1. pose proof (seg_decomp l2 l r Hlr) as D2.
  assert (EA : TAKE l l2 = TAKE l l1).
  { apply LIST_EQ; [rewrite !LENGTH_TAKE'; lia|]. intros i Hi'. rewrite LENGTH_TAKE' in Hi'.
    rewrite !EL_TAKE by lia. apply Hout; lia. }
  assert (EC : DROP r l2 = DROP r l1).
  { apply LIST_EQ; [rewrite !LENGTH_DROP; lia|]. intros i Hi'. rewrite !EL_DROP. apply Hout; lia. }
  rewrite D1, D2, EA, EC in Hp. apply Permutation_app_inv_l, Permutation_app_inv_r in Hp.
  set (M1 := TAKE (r - l) (DROP l l1)) in *. set (M2 := TAKE (r - l) (DROP l l2)) in *.
  assert (Ex : EL ind l2 = EL (ind - l) M2) by (unfold M2; rewrite EL_TAKE, EL_DROP by lia; f_equal; lia).
  assert (Hm2 : In (EL ind l2) M2).
  { rewrite Ex. apply EL_In. unfold M2. rewrite LENGTH_TAKE', LENGTH_DROP; lia. }
  apply (Permutation_in _ (Permutation_sym Hp)) in Hm2. apply In_EL in Hm2 as (j & Hj & Ej).
  unfold M1 in Hj, Ej. rewrite LENGTH_TAKE', LENGTH_DROP in Hj. rewrite EL_TAKE, EL_DROP in Ej by lia.
  rewrite Ej. apply Hin; lia.
Qed.

End Segments.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "sort_regs_prop_lemma" *)
Theorem sort_regs_prop_lemma : forall (P : N -> bool) l1 l2 l r,
  l <= LENGTH l1 /\
  r <= LENGTH l1 /\
  (forall ind, ind < l \/ r <= ind -> EL ind l2 = EL ind l1) /\
  (forall ind, l <= ind /\ ind < r -> P (EL ind l1)) /\
  PERM l1 l2 ->
  (forall ind, l <= ind /\ ind < r -> P (EL ind l2)).
Proof.
  intros P l1 l2 l r (H1 & H2 & H3 & H4 & H5). apply PERM_Permutation in H5.
  exact (seg_prop (fun x => is_true (P x)) l1 l2 l r H1 H2 H3 H4 H5).
Qed.

Lemma PERM_TAKE_full {A} (l1 l2 : list A) :
  LENGTH l2 = LENGTH l1 -> PERM (TAKE (LENGTH l1) l1) (TAKE (LENGTH l1) l2) -> Permutation l1 l2.
Proof. intros L P; apply PERM_Permutation in P. rewrite <- L in P at 2. rewrite !TAKE_LENGTH_ID in P. exact P. Qed.

Lemma LEX_trans' (x y z : Z * N) : LEX Z.lt N.le x y -> LEX Z.lt N.le y z -> LEX Z.lt N.le x z.
Proof. destruct x, y, z; unfold LEX; lia. Qed.

Lemma LEX_refl' (x : Z * N) : LEX Z.lt N.le x x.
Proof. destruct x; unfold LEX; lia. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "sort_regs_correct" *)
Theorem sort_regs_correct : forall l r sth,
  (forall i, l <= i /\ i < r -> EL i sth.(sorted_regs) < LENGTH sth.(int_beg)) /\
  l <= LENGTH sth.(sorted_regs) /\
  r <= LENGTH sth.(sorted_regs) ->
  exists sthout, sort_regs l r sth = (M_success tt, sthout) /\
    sthout = with_sorted_regs sth sthout.(sorted_regs) /\
    LENGTH sthout.(sorted_regs) = LENGTH sth.(sorted_regs) /\
    (forall n, l <= n /\ r <= n /\ n <= LENGTH sth.(sorted_regs) ->
       PERM (TAKE n sth.(sorted_regs)) (TAKE n sthout.(sorted_regs))) /\
    (forall ind, ind < l \/ r <= ind -> EL ind sthout.(sorted_regs) = EL ind sth.(sorted_regs)) /\
    (forall i1 i2, l <= i1 /\ i1 <= i2 /\ i2 < r ->
       let reg1 := EL i1 sthout.(sorted_regs) in
       let reg2 := EL i2 sthout.(sorted_regs) in
       LEX Z.lt N.le (EL reg1 sth.(int_beg), reg1) (EL reg2 sth.(int_beg), reg2)).
Proof.
  intros l r sth. remember (r - l) as m eqn:Em. revert l r sth Em.
  induction m as [m IH] using (well_founded_induction N.lt_wf_0).
  intros l r sth Em (Hb & Hl & Hr). rewrite sort_regs_def.
  destruct (N.leb_spec r (l + 1)) as [Hle|Hgt].
  - exists sth. split; [reflexivity|split; [destruct sth; reflexivity|split; [reflexivity|]]].
    split; [intros; apply PERM_refl|split; [reflexivity|]].
    intros i1 i2 Hi. assert (i1 = i2) as -> by lia. apply LEX_refl'.
  - msimp. rewrite sorted_regs_sub_ok by lia. cbv beta iota.
    set (rpiv := EL l (sorted_regs sth)).
    rewrite int_beg_sub_ok by (apply Hb; lia). cbv beta iota.
    set (begrpiv := EL rpiv (int_beg sth)).
    destruct (partition_regs_correct (l + 1) rpiv begrpiv r sth) as (mid & sp & Ep & Esp & Lp & Rp & Pp & Up & Ltp & Gep).
    { split; [intros i Hi; apply Hb; lia|split; lia]. }
    rewrite Ep. cbv beta iota. specialize (Rp ltac:(lia)).
    assert (Pp' : Permutation (sorted_regs sth) (sorted_regs sp)).
    { apply PERM_TAKE_full; [exact Lp|]. apply Pp; lia. }
    assert (Bp : forall i, l + 1 <= i /\ i < r -> EL i (sorted_regs sp) < LENGTH (int_beg sth)).
    { apply (seg_prop (fun x => x < LENGTH (int_beg sth)) (sorted_regs sth) (sorted_regs sp) (l + 1) r); try lia.
      - intros ind Hi; apply Up; lia.
      - intros ind Hi; apply Hb; lia.
      - exact Pp'. }
    destruct (swap_regs_eq sp l (mid - 1) ltac:(lia)) as (sw & Esw & Esw').
    rewrite Esw. cbv beta iota.
    assert (Ib : int_beg sw = int_beg sth) by (rewrite Esw', Esp; reflexivity).
    assert (Lsw : LENGTH (sorted_regs sw) = LENGTH (sorted_regs sth)) by (rewrite Esw'; cbn; rewrite !LENGTH_LUPDATE; exact Lp).
    assert (ELsw : forall i, EL i (sorted_regs sw) =
      if decide (i = mid - 1) then EL l (sorted_regs sp) else if decide (i = l) then EL (mid - 1) (sorted_regs sp)
      else EL i (sorted_regs sp)).
    { intros i; rewrite Esw'; cbn [sorted_regs]. rewrite !EL_LUPDATE_dec by (rewrite ?LENGTH_LUPDATE; lia). reflexivity. }
    assert (Hpiv : EL l (sorted_regs sp) = rpiv) by (rewrite Up by lia; reflexivity).
    destruct (N.leb_spec mid l) as [X|_]; [lia|]. destruct (N.ltb_spec r mid) as [X|_]; [lia|]. cbn [orb].
    assert (Psw : Permutation (sorted_regs sp) (sorted_regs sw)).
    { apply PERM_TAKE_full; [lia|]. apply (swap_regs_perm sp l (mid - 1) sw Esw); lia. }
    (* properties of the swapped array *)
    assert (Bsw : forall i, l <= i /\ i < r -> EL i (sorted_regs sw) < LENGTH (int_beg sw)).
    { intros i Hi. rewrite ELsw, Ib. destruct (decide (i = mid - 1)); [rewrite Hpiv; apply Hb; lia|].
      destruct (decide (i = l)); apply Bp; lia. }
    assert (Lsw' : forall ind, l <= ind /\ ind < mid - 1 ->
      LEX Z.lt N.le (EL (EL ind (sorted_regs sw)) (int_beg sth), EL ind (sorted_regs sw)) (begrpiv, rpiv)).
    { intros ind Hi. rewrite ELsw. destruct (decide (ind = mid - 1)); [lia|].
      destruct (decide (ind = l)); [apply (Ltp (mid - 1)); lia|apply (Ltp ind); lia]. }
    assert (Gsw' : forall ind, mid <= ind /\ ind < r ->
      LEX Z.lt N.le (begrpiv, rpiv) (EL (EL ind (sorted_regs sw)) (int_beg sth), EL ind (sorted_regs sw))).
    { intros ind Hi. rewrite ELsw. destruct (decide (ind = mid - 1)); [lia|].
      destruct (decide (ind = l)); [lia|apply (Gep ind); lia]. }
    assert (Msw : EL (mid - 1) (sorted_regs sw) = rpiv) by (rewrite ELsw; destruct (decide (mid - 1 = mid - 1)); [exact Hpiv|congruence]).
    (* first recursive sort *)
    destruct (IH (mid - 1 - l) ltac:(lia) l (mid - 1) sw eq_refl) as (sq & Eq & Esq & Lq & Pq & Uq & Sq).
    { split; [intros i Hi; apply Bsw; lia|split; lia]. }
    rewrite Eq. cbv beta iota.
    assert (Pq' : Permutation (sorted_regs sw) (sorted_regs sq)) by (apply PERM_TAKE_full; [lia|]; apply Pq; lia).
    assert (Ibq : int_beg sq = int_beg sth) by (rewrite Esq; cbn; exact Ib).
    assert (Lq' : forall ind, l <= ind /\ ind < mid - 1 ->
      LEX Z.lt N.le (EL (EL ind (sorted_regs sq)) (int_beg sth), EL ind (sorted_regs sq)) (begrpiv, rpiv)).
    { apply (seg_prop (fun x => LEX Z.lt N.le (EL x (int_beg sth), x) (begrpiv, rpiv)) (sorted_regs sw) (sorted_regs sq) l (mid - 1));
        try lia; [exact Uq|exact Lsw'|exact Pq']. }
    assert (Bq : forall i, mid <= i /\ i < r -> EL i (sorted_regs sq) < LENGTH (int_beg sq)).
    { intros i Hi; rewrite Uq by lia; rewrite Ibq, <- Ib; apply Bsw; lia. }
    (* second recursive sort *)
    destruct (IH (r - mid) ltac:(lia) mid r sq eq_refl) as (so & Eo & Eso & Lo & Po & Uo & So).
    { split; [exact Bq|split; lia]. }
    exists so. rewrite Eo. split; [reflexivity|].
    assert (Ibo : int_beg so = int_beg sth) by (rewrite Eso; cbn; exact Ibq).
    split; [rewrite Eso, Esq, Esw', Esp; reflexivity|]. split; [lia|].
    split.
    { intros n Hn. eapply PERM_trans; [apply Pp; lia|]. eapply PERM_trans; [apply (swap_regs_perm sp l (mid - 1) sw Esw); lia|].
      eapply PERM_trans; [apply Pq; lia|]. apply Po; lia. }
    split.
    { intros ind Hi. rewrite Uo by lia. rewrite Uq by lia. rewrite ELsw.
      destruct (decide (ind = mid - 1)); [lia|]. destruct (decide (ind = l)); [lia|]. apply Up; lia. }
    (* sortedness *)
    assert (Mo : EL (mid - 1) (sorted_regs so) = rpiv) by (rewrite Uo, Uq by lia; exact Msw).
    assert (Lo' : forall ind, l <= ind /\ ind < mid - 1 ->
      LEX Z.lt N.le (EL (EL ind (sorted_regs so)) (int_beg sth), EL ind (sorted_regs so)) (begrpiv, rpiv)).
    { intros ind Hi; rewrite Uo by lia; apply Lq'; lia. }
    assert (Go' : forall ind, mid <= ind /\ ind < r ->
      LEX Z.lt N.le (begrpiv, rpiv) (EL (EL ind (sorted_regs so)) (int_beg sth), EL ind (sorted_regs so))).
    { apply (seg_prop (fun x => LEX Z.lt N.le (begrpiv, rpiv) (EL x (int_beg sth), x)) (sorted_regs sq) (sorted_regs so) mid r);
        try lia; [exact Uo| |apply PERM_TAKE_full; [lia|]; apply Po; lia].
      intros ind Hi; rewrite Uq by lia; apply Gsw'; lia. }
    assert (Piv : (begrpiv, rpiv) = (EL (EL (mid - 1) (sorted_regs so)) (int_beg sth), EL (mid - 1) (sorted_regs so)))
      by (rewrite Mo; reflexivity).
    intros i1 i2 Hi; cbv zeta.
    destruct (N.lt_ge_cases i2 (mid - 1)) as [A2|A2].
    + pose proof (Sq i1 i2 ltac:(lia)) as X; cbv zeta in X. rewrite ?Ib, ?Ibq in X. rewrite !(Uo i1), !(Uo i2) by lia. exact X.
    + destruct (N.eq_dec i2 (mid - 1)) as [->|B2].
      * rewrite <- Piv. destruct (N.eq_dec i1 (mid - 1)) as [->|B1]; [rewrite <- Piv; apply LEX_refl'|apply Lo'; lia].
      * destruct (N.lt_ge_cases i1 mid) as [A1|A1].
        -- eapply LEX_trans'; [|apply Go'; lia].
           destruct (N.eq_dec i1 (mid - 1)) as [->|B1]; [rewrite <- Piv; apply LEX_refl'|apply Lo'; lia].
        -- pose proof (So i1 i2 ltac:(lia)) as X; cbv zeta in X. rewrite ?Ib, ?Ibq in X. exact X.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "swap_moves_eq" *)
Theorem swap_moves_eq : forall sth i1 i2,
  i1 < LENGTH sth.(sorted_moves) /\ i2 < LENGTH sth.(sorted_moves) ->
  exists sthout, swap_moves i1 i2 sth = (M_success tt, sthout) /\
  sthout = with_sorted_moves sth (LUPDATE (EL i1 sth.(sorted_moves)) i2
                                   (LUPDATE (EL i2 sth.(sorted_moves)) i1 sth.(sorted_moves))).
Proof.
  intros sth i1 i2 [H1 H2]; unfold swap_moves; msimp.
  rewrite sorted_moves_sub_eqn; destruct (N.ltb_spec i1 (LENGTH sth.(sorted_moves))); [|lia]; cbv beta iota.
  rewrite sorted_moves_sub_eqn; destruct (N.ltb_spec i2 (LENGTH sth.(sorted_moves))); [|lia]; cbv beta iota.
  rewrite update_sorted_moves_eqn; destruct (N.ltb_spec i1 (LENGTH sth.(sorted_moves))); [|lia]; cbv beta iota.
  rewrite update_sorted_moves_eqn; cbn [sorted_moves]. rewrite LENGTH_LUPDATE.
  destruct (N.ltb_spec i2 (LENGTH sth.(sorted_moves))); [|lia]. eexists; split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "swap_moves_correct" *)
Theorem swap_moves_correct : forall sth i1 i2,
  i1 < LENGTH sth.(sorted_moves) /\ i2 < LENGTH sth.(sorted_moves) ->
  exists sthout, swap_moves i1 i2 sth = (M_success tt, sthout) /\
  sthout = with_sorted_moves sth sthout.(sorted_moves) /\
  LENGTH sthout.(sorted_moves) = LENGTH sth.(sorted_moves) /\
  (forall n, i1 < n /\ i2 < n /\ n <= LENGTH sth.(sorted_moves) ->
     PERM (TAKE n sth.(sorted_moves)) (TAKE n sthout.(sorted_moves))).
Proof.
  intros sth i1 i2 H. destruct (swap_moves_eq sth i1 i2 H) as (so & E & ->). exists (with_sorted_moves sth
    (LUPDATE (EL i1 sth.(sorted_moves)) i2 (LUPDATE (EL i2 sth.(sorted_moves)) i1 sth.(sorted_moves)))).
  split; [exact E|split; [reflexivity|split; [cbn; rewrite !LENGTH_LUPDATE; reflexivity|]]].
  intros n (H1 & H2 & H3). cbn [with_sorted_moves sorted_moves].
  rewrite !LUPDATE_TAKE by (rewrite ?LENGTH_LUPDATE; lia).
  rewrite <- (EL_TAKE n i1 (sorted_moves sth)), <- (EL_TAKE n i2 (sorted_moves sth)) by lia.
  apply swap_perm_lemma. rewrite LENGTH_TAKE'; lia.
Qed.

Lemma sorted_moves_sub_ok sth i : i < LENGTH sth.(sorted_moves) ->
  sorted_moves_sub i sth = (M_success (EL i sth.(sorted_moves)), sth).
Proof. intros H; rewrite sorted_moves_sub_eqn; destruct (N.ltb_spec i (LENGTH sth.(sorted_moves))); [reflexivity|lia]. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "partition_moves_correct" *)
Theorem partition_moves_correct : forall l ppiv r sth,
  l <= LENGTH sth.(sorted_moves) /\
  r <= LENGTH sth.(sorted_moves) ->
  exists mid sthout, partition_moves l ppiv r sth = (M_success mid, sthout) /\
    (l <= r -> l <= mid /\ mid <= r) /\
    sthout = with_sorted_moves sth sthout.(sorted_moves) /\
    LENGTH sthout.(sorted_moves) = LENGTH sth.(sorted_moves) /\
    (forall n, l <= n /\ r <= n /\ n <= LENGTH sth.(sorted_moves) ->
       PERM (TAKE n sth.(sorted_moves)) (TAKE n sthout.(sorted_moves))).
Proof.
  intros l ppiv r sth. remember (r - l) as m eqn:Em. revert l r sth Em.
  induction m as [m IH] using (well_founded_induction N.lt_wf_0).
  intros l r sth Em (Hl & Hr). rewrite partition_moves_def.
  destruct (N.leb_spec r l) as [Hle|Hgt].
  - exists l, sth. split; [reflexivity|split; [lia|split; [destruct sth; reflexivity|split; [reflexivity|]]]].
    intros; apply PERM_refl.
  - msimp. rewrite sorted_moves_sub_ok by lia. cbv beta iota.
    destruct (FST (EL l (sorted_moves sth)) <? ppiv).
    + destruct (IH (r - (l + 1)) ltac:(lia) (l + 1) r sth eq_refl ltac:(lia)) as (mid & so & E & Rg & Es & L & P).
      exists mid, so. split; [exact E|split; [intros _; specialize (Rg ltac:(lia)); lia|split; [exact Es|split; [exact L|]]]].
      intros n Hn; apply P; lia.
    + destruct (swap_moves_correct sth l (r - 1) ltac:(lia)) as (sw & Esw & Esw' & Lsw & Psw).
      rewrite Esw. cbv beta iota.
      destruct (IH (r - 1 - l) ltac:(lia) l (r - 1) sw eq_refl ltac:(lia)) as (mid & so & E & Rg & Es & L & P).
      exists mid, so. split; [exact E|split; [intros _; specialize (Rg ltac:(lia)); lia|]].
      split; [rewrite Es, Esw'; reflexivity|split; [lia|]].
      intros n Hn. eapply PERM_trans; [apply Psw; lia|apply P; lia].
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "sort_moves_correct" *)
Theorem sort_moves_correct : forall l r sth,
  l <= LENGTH sth.(sorted_moves) /\
  r <= LENGTH sth.(sorted_moves) ->
  exists sthout, sort_moves l r sth = (M_success tt, sthout) /\
    sthout = with_sorted_moves sth sthout.(sorted_moves) /\
    LENGTH sthout.(sorted_moves) = LENGTH sth.(sorted_moves) /\
    (forall n, l <= n /\ r <= n /\ n <= LENGTH sth.(sorted_moves) ->
       PERM (TAKE n sth.(sorted_moves)) (TAKE n sthout.(sorted_moves))).
Proof.
  intros l r sth. remember (r - l) as m eqn:Em. revert l r sth Em.
  induction m as [m IH] using (well_founded_induction N.lt_wf_0).
  intros l r sth Em (Hl & Hr). rewrite sort_moves_def.
  destruct (N.leb_spec r (l + 1)) as [Hle|Hgt].
  - exists sth. split; [reflexivity|split; [destruct sth; reflexivity|split; [reflexivity|]]]. intros; apply PERM_refl.
  - msimp. rewrite sorted_moves_sub_ok by lia. cbv beta iota.
    destruct (partition_moves_correct (l + 1) (FST (EL l (sorted_moves sth))) r sth ltac:(lia))
      as (mid & sp & Ep & Rp & Esp & Lp & Pp).
    rewrite Ep. cbv beta iota. specialize (Rp ltac:(lia)).
    destruct (swap_moves_correct sp l (mid - 1) ltac:(lia)) as (sw & Esw & Esw' & Lsw & Psw).
    rewrite Esw. cbv beta iota.
    destruct (N.leb_spec mid l) as [X|_]; [lia|]. destruct (N.ltb_spec r mid) as [X|_]; [lia|]. cbn [orb].
    destruct (IH (mid - 1 - l) ltac:(lia) l (mid - 1) sw eq_refl ltac:(lia)) as (sq & Eq & Esq & Lq & Pq).
    rewrite Eq. cbv beta iota.
    destruct (IH (r - mid) ltac:(lia) mid r sq eq_refl ltac:(lia)) as (so & Eo & Eso & Lo & Po).
    exists so. rewrite Eo. split; [reflexivity|].
    split; [rewrite Eso, Esq, Esw', Esp; reflexivity|split; [lia|]].
    intros n Hn. eapply PERM_trans; [apply Pp; lia|]. eapply PERM_trans; [apply Psw; lia|].
    eapply PERM_trans; [apply Pq; lia|]. apply Po; lia.
Qed.

(** ** Initial states and remaining helpers *)

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "list_minimum" *)
Theorem list_minimum : forall (f : N -> Z) (l : list N), exists (x : Z), EVERY (fun y => (x <=? f y)%Z) l.
Proof.
  intros f; induction l as [|h l [x IH]]; [exists 0%Z; reflexivity|].
  exists (Z.min x (f h)). cbn [EVERY]. apply andb_true_intro; split; [apply Z.leb_le; lia|].
  apply EVERY_iff; intros y Hy. pose proof (proj1 (EVERY_iff _ _) IH y Hy) as X. apply Z.leb_le in X; apply Z.leb_le; lia.
Qed.

Lemma gls_empty st sth pos forced mincol :
  LENGTH sth.(int_beg) = LENGTH sth.(colors) -> LENGTH sth.(int_end) = LENGTH sth.(colors) ->
  st.(active) = [] -> st.(colorpool) = [] -> st.(phyregs) = LN ->
  st.(colornum) <= st.(colormax) -> st.(colormax) <= st.(stacknum) -> mincol <= st.(colornum) ->
  gls st sth [] pos forced mincol.
Proof.
  intros L1 L2 Ea Ep Eph H1 H2 H3. refine {| g_len_beg := L1; g_len_end := L2; g_num_max := H1;
    g_max_stack := H2; g_mincol := H3 |}; rewrite ?Ea, ?Ep, ?Eph; cbn [List.map List.filter app In];
    try (intros; contradiction); try constructor.
  all: try (intros []; fail); try (intros (r & _ & [] & _); fail); try exact I.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "linear_reg_alloc_pass1_initial_state_invariants" *)
Theorem linear_reg_alloc_pass1_initial_state_invariants : forall {A} sth (reglist : list N) forced k (st : A),
  LENGTH sth.(int_beg) = LENGTH sth.(colors) /\ LENGTH sth.(int_end) = LENGTH sth.(colors) ->
  exists pos,
    good_linear_scan_state (linear_reg_alloc_pass1_initial_state k) sth [] pos forced 0 /\
    EVERY (fun r => (pos <=? EL r sth.(int_beg))%Z) reglist.
Proof.
  intros A sth reglist forced k st [L1 L2]. destruct (list_minimum (fun r => EL r sth.(int_beg)) reglist) as [x Hx].
  exists x; split; [|exact Hx]. apply gls_iff, gls_empty; cbn; auto; lia.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "linear_reg_alloc_pass2_initial_state_invariants" *)
Theorem linear_reg_alloc_pass2_initial_state_invariants : forall {A} sth (reglist : list N) forced k nreg (st : A),
  LENGTH sth.(int_beg) = LENGTH sth.(colors) /\ LENGTH sth.(int_end) = LENGTH sth.(colors) ->
  exists pos,
    good_linear_scan_state (linear_reg_alloc_pass2_initial_state k nreg) sth [] pos forced k /\
    EVERY (fun r => (pos <=? EL r sth.(int_beg))%Z) reglist.
Proof.
  intros A sth reglist forced k nreg st [L1 L2]. destruct (list_minimum (fun r => EL r sth.(int_beg)) reglist) as [x Hx].
  exists x; split; [|exact Hx]. apply gls_iff, gls_empty; cbn; auto; lia.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "st_ex_FILTER_good_stack" *)
Theorem st_ex_FILTER_good_stack : forall reglist sth k,
  EVERY (fun r => r <? LENGTH sth.(colors)) reglist ->
  st_ex_FILTER_good (fun r => col <- colors_sub r ;; st_ex_return (is_stack_var r || (k <=? col))) reglist sth =
    (M_success (FILTER (fun r => is_stack_var r || (k <=? EL r sth.(colors))) reglist), sth).
Proof.
  induction reglist as [|r l IH]; intros sth k H; [reflexivity|].
  cbn [EVERY] in H; unfold is_true in H; apply andb_prop in H as [Hr H].
  cbn [st_ex_FILTER_good FILTER List.filter]; msimp. rewrite colors_sub_eqn, Hr; cbv beta iota.
  destruct (is_stack_var r || (k <=? EL r (colors sth))); rewrite IH by exact H; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "lookup_fromAList_MAP_not_NONE" *)
Theorem lookup_fromAList_MAP_not_NONE : forall r l,
  lookup r (fromAList (MAP (fun r => (r, tt)) l)) <> None <-> MEM r l.
Proof.
  intros r l. rewrite <- notdom_lookup, MEM_iff, domain_fromAList_units. tauto.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "PERM_PARTITION" *)
Theorem PERM_PARTITION : forall {A} (P : A -> bool) l,
  PERM l (FILTER (fun x => P x) l ++ FILTER (fun x => negb (P x)) l).
Proof.
  intros A P l; apply PERM_Permutation. induction l as [|x l IH]; [constructor|]. cbn [FILTER List.filter].
  destruct (P x); cbn [negb app].
  - constructor; exact IH.
  - apply Permutation_cons_app, IH.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "forbidden_is_from_forced_take_sublist" *)
Theorem forbidden_is_from_forced_take_sublist : forall l forced int_beg forced_adj,
  EVERY (fun '(r1, r2) => MEM r1 l && MEM r2 l) forced /\
  (forall r, forbidden_is_from_forced forced int_beg r (the [] (lookup r forced_adj))) ->
  (forall r, forbidden_is_from_forced_sublist l forced int_beg r (the [] (lookup r forced_adj))).
Proof.
  intros l forced int_beg forced_adj [He Hf] r reg2. rewrite <- (Hf r reg2). split; [|tauto].
  intros H; split; [exact H|]. destruct H as (_ & [Hm|Hm] & _); apply MEM_iff in Hm;
    pose proof (proj1 (EVERY_iff _ _) He _ Hm) as X; cbn beta iota in X; apply andb_prop in X as [H1 H2];
    assumption.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "good_linear_scan_state_REVERSE" *)
Theorem good_linear_scan_state_REVERSE : forall st sth l pos forced mincol,
  good_linear_scan_state st sth (REVERSE l) pos forced mincol <->
  good_linear_scan_state st sth l pos forced mincol.
Proof.
  intros st sth l pos forced mincol; rewrite !gls_iff; split; intros G; eapply gls_equiv_l; try exact G.
  - intros x; rewrite <- in_rev; reflexivity.
  - pose proof (g_phydistinct _ _ _ _ _ _ G) as D. rewrite filter_rev, map_rev in D. apply NoDup_rev in D.
    rewrite rev_involutive in D; exact D.
  - intros x; rewrite <- in_rev; reflexivity.
  - pose proof (g_phydistinct _ _ _ _ _ _ G) as D. rewrite filter_rev, map_rev. apply NoDup_rev, D.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "phystack_on_stack_REVERSE" *)
Theorem phystack_on_stack_REVERSE : forall l st sth,
  phystack_on_stack (REVERSE l) st sth <-> phystack_on_stack l st sth.
Proof. intros; unfold phystack_on_stack; setoid_rewrite MEM_rev; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "FILTER_remove_MEM_l" *)
Theorem FILTER_remove_MEM_l : forall {A} `{EqDecision A} (P : A -> bool) l,
  FILTER (fun x => P x && MEM x l) l = FILTER (fun x => P x) l.
Proof.
  intros A EA P l. apply filter_ext_in. intros x Hx.
  assert (MEM x l = true) as -> by (apply MEM_iff, Hx). apply andb_true_r.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "le_div_2" *)
Theorem le_div_2 : forall k r, k <= r DIV 2 <-> 2 * k <= r.
Proof. intros k r; pose proof (N.div_mod r 2 ltac:(lia)); pose proof (N.mod_lt r 2 ltac:(lia)); lia. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "lt_div_2" *)
Theorem lt_div_2 : forall k r, r DIV 2 < k <-> r < 2 * k.
Proof. intros k r; pose proof (N.div_mod r 2 ltac:(lia)); pose proof (N.mod_lt r 2 ltac:(lia)); lia. Qed.

Lemma DROP_cons_EL {A} `{Inhabited A} n (l : list A) : n < LENGTH l -> DROP n l = EL n l :: DROP (n + 1) l.
Proof.
  revert n; induction l as [|x l IH]; intros n Hn; cbn [LENGTH] in Hn; [lia|]. cbn [DROP].
  rewrite EL_cons. destruct (N.eqb_spec n 0) as [->|Hn0]; cbn [N.add].
  - destruct (N.eqb_spec 1 0); [lia|]. cbn [N.sub]. destruct l; reflexivity.
  - destruct (N.eqb_spec (n + 1) 0); [lia|]. rewrite IH by lia. f_equal. f_equal; lia.
Qed.

Lemma TAKE_cons {A} k (x : A) l : 0 < k -> TAKE k (x :: l) = x :: TAKE (k - 1) l.
Proof. intros H; cbn [TAKE]; destruct (N.eqb_spec k 0); [lia|reflexivity]. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "sorted_regs_to_list_correct" *)
Theorem sorted_regs_to_list_correct : forall n last sth,
  last <= LENGTH sth.(sorted_regs) ->
  sorted_regs_to_list n last sth = (M_success (TAKE (last - n) (DROP n sth.(sorted_regs))), sth).
Proof.
  intros n last sth. remember (last - n) as m eqn:Em. revert n Em.
  induction m as [m IH] using (well_founded_induction N.lt_wf_0). intros n Em Hl.
  rewrite sorted_regs_to_list_def. destruct (N.leb_spec last n) as [Hle|Hgt].
  - rewrite Em; replace (last - n) with 0 by lia. destruct (DROP n (sorted_regs sth)); reflexivity.
  - msimp. rewrite sorted_regs_sub_ok by lia. cbv beta iota. rewrite (IH (last - (n + 1)) ltac:(lia) (n + 1) eq_refl Hl).
    cbv beta iota. rewrite (DROP_cons_EL n) by lia. rewrite TAKE_cons by lia.
    replace (m - 1) with (last - (n + 1)) by lia; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "sorted_moves_to_list_correct" *)
Theorem sorted_moves_to_list_correct : forall n last sth,
  last <= LENGTH sth.(sorted_moves) ->
  sorted_moves_to_list n last sth = (M_success (TAKE (last - n) (DROP n sth.(sorted_moves))), sth).
Proof.
  intros n last sth. remember (last - n) as m eqn:Em. revert n Em.
  induction m as [m IH] using (well_founded_induction N.lt_wf_0). intros n Em Hl.
  rewrite sorted_moves_to_list_def. destruct (N.leb_spec last n) as [Hle|Hgt].
  - rewrite Em; replace (last - n) with 0 by lia. destruct (DROP n (sorted_moves sth)); reflexivity.
  - msimp. rewrite sorted_moves_sub_ok by lia. cbv beta iota. rewrite (IH (last - (n + 1)) ltac:(lia) (n + 1) eq_refl Hl).
    cbv beta iota. rewrite (DROP_cons_EL n) by lia. rewrite TAKE_cons by lia.
    replace (m - 1) with (last - (n + 1)) by lia; reflexivity.
Qed.

Lemma TAKE_0 {A} (l : list A) : TAKE 0 l = [].
Proof. destruct l; reflexivity. Qed.

Lemma EL_TAKE_eq {A} `{Inhabited A} n (l1 l2 : list A) i : TAKE n l1 = TAKE n l2 -> i < n -> EL i l1 = EL i l2.
Proof. intros E Hi. rewrite <- (EL_TAKE n i l1), <- (EL_TAKE n i l2) by exact Hi. rewrite E; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "list_to_sorted_regs_correct" *)
Theorem list_to_sorted_regs_correct : forall l n sth,
  n + LENGTH l <= LENGTH sth.(sorted_regs) ->
  exists sthout, (M_success tt, sthout) = list_to_sorted_regs l n sth /\
    LENGTH sthout.(sorted_regs) = LENGTH sth.(sorted_regs) /\
    sthout = with_sorted_regs sth sthout.(sorted_regs) /\
    TAKE n sthout.(sorted_regs) = TAKE n sth.(sorted_regs) /\
    TAKE (LENGTH l) (DROP n sthout.(sorted_regs)) = l.
Proof.
  induction l as [|h l IH]; intros n sth Hl.
  - exists sth. split; [reflexivity|split; [reflexivity|split; [destruct sth; reflexivity|split; [reflexivity|apply TAKE_0]]]].
  - cbn [LENGTH] in Hl. cbn [list_to_sorted_regs]; msimp. rewrite update_sorted_regs_eqn.
    destruct (N.ltb_spec n (LENGTH (sorted_regs sth))); [|lia]. cbv beta iota.
    set (sth1 := {| colors := colors sth; int_beg := int_beg sth; int_end := int_end sth;
                    sorted_regs := LUPDATE h n (sorted_regs sth); sorted_moves := sorted_moves sth |}).
    assert (L1 : LENGTH (sorted_regs sth1) = LENGTH (sorted_regs sth)) by apply LENGTH_LUPDATE.
    destruct (IH (n + 1) sth1 ltac:(lia)) as (so & E & L & Es & T1 & T2).
    exists so. split; [exact E|split; [lia|split; [rewrite Es; reflexivity|split]]].
    + apply LIST_EQ; [rewrite !LENGTH_TAKE'; lia|]. intros i Hi. rewrite LENGTH_TAKE' in Hi.
      rewrite !EL_TAKE by lia. rewrite (EL_TAKE_eq (n + 1) _ _ i T1) by lia.
      cbn [sth1 sorted_regs]. apply EL_LUPDATE_other; lia.
    + rewrite (DROP_cons_EL n) by lia. cbn [LENGTH]. rewrite TAKE_cons by lia.
      replace (SUC (LENGTH l) - 1) with (LENGTH l) by lia. rewrite T2. f_equal.
      rewrite (EL_TAKE_eq (n + 1) _ _ n T1) by lia. cbn [sth1 sorted_regs]. apply EL_LUPDATE_same; lia.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "list_to_sorted_moves_correct" *)
Theorem list_to_sorted_moves_correct : forall l n sth,
  n + LENGTH l <= LENGTH sth.(sorted_moves) ->
  exists sthout, (M_success tt, sthout) = list_to_sorted_moves l n sth /\
    LENGTH sthout.(sorted_moves) = LENGTH sth.(sorted_moves) /\
    sthout = with_sorted_moves sth sthout.(sorted_moves) /\
    TAKE n sthout.(sorted_moves) = TAKE n sth.(sorted_moves) /\
    TAKE (LENGTH l) (DROP n sthout.(sorted_moves)) = l.
Proof.
  induction l as [|h l IH]; intros n sth Hl.
  - exists sth. split; [reflexivity|split; [reflexivity|split; [destruct sth; reflexivity|split; [reflexivity|apply TAKE_0]]]].
  - cbn [LENGTH] in Hl. cbn [list_to_sorted_moves]; msimp. rewrite update_sorted_moves_eqn.
    destruct (N.ltb_spec n (LENGTH (sorted_moves sth))); [|lia]. cbv beta iota.
    set (sth1 := {| colors := colors sth; int_beg := int_beg sth; int_end := int_end sth;
                    sorted_regs := sorted_regs sth; sorted_moves := LUPDATE h n (sorted_moves sth) |}).
    assert (L1 : LENGTH (sorted_moves sth1) = LENGTH (sorted_moves sth)) by apply LENGTH_LUPDATE.
    destruct (IH (n + 1) sth1 ltac:(lia)) as (so & E & L & Es & T1 & T2).
    exists so. split; [exact E|split; [lia|split; [rewrite Es; reflexivity|split]]].
    + apply LIST_EQ; [rewrite !LENGTH_TAKE'; lia|]. intros i Hi. rewrite LENGTH_TAKE' in Hi.
      rewrite !EL_TAKE by lia. rewrite (EL_TAKE_eq (n + 1) _ _ i T1) by lia.
      cbn [sth1 sorted_moves]. apply EL_LUPDATE_other; lia.
    + rewrite (DROP_cons_EL n) by lia. cbn [LENGTH]. rewrite TAKE_cons by lia.
      replace (SUC (LENGTH l) - 1) with (LENGTH l) by lia. rewrite T2. f_equal.
      rewrite (EL_TAKE_eq (n + 1) _ _ n T1) by lia. cbn [sth1 sorted_moves]. apply EL_LUPDATE_same; lia.
Qed.
