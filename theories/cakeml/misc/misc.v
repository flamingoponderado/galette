(** * CakeML [misc]: miscellaneous definitions used throughout CakeML

    [miscScript.sml] is a large grab-bag.  This port contains the executable
    definitions used by the Pancake compiler and the backend passes it
    reaches (and the semantics-level helpers that are cheap to state), with
    their main theorems.  Remaining definitions and why they are not ported:

    - need [sptree] ([theories/HOL/src/finite_maps/sptree.v]):
      [fromList2_def], [zlookup_def],
      [eq_shape_def], [copy_shape_def], [range_def] (and the [num_set] /
      [num_map] type abbreviations);
    - need finite maps: [fmap_linv_def], [fmap_update_def];
    - need [listTheory.oEL]: the [LLOOKUP] overload and its theorems;
    - need [rich_list] ([REPLICATE], [SPLITP]/[FIELDS]):
      [update_resize_def], [splitlines_def];
    - non-executable / need [llist], [path], [LEAST]: [Lnext_def],
      [Lnext_pos_def], [least_from_def], [steps_rel_okpath],
      [steps_rel_LRC];
    - word-shift helpers not used by the compiler (their [_rwt] theorems need
      word-shift composition lemmas not yet in [words.v]): [shift_left_def],
      [shift_right_def], [arith_shift_right_def], [any_word64_ror_def];
    - the many lemmas about HOL library constants only (list, pred_set,
      alist, sptree, finite_map, words, ...).

    HOL [num] is [N]; definitions recursing on [SUC n] ([read_bytearray],
    [all_words]) use [num_rec] and HOL's equations are the tagged [_def]
    theorems. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.combin Require combin.
From Galette.HOL.src.coretypes Require pair.
From Galette.HOL.src.sort Require Import ternaryComparisons.
From Galette.HOL.src.finite_maps Require sptree.
From Galette.HOL.src.n_bit Require byte.
From Galette.HOL.examples.machine_code.hoare_triple Require set_sep.
Open Scope N_scope.

(** ** Options and lists *)

Section Defs.
Context {A B : Type}.

(** Total version of [THE]. *)
(*! HOL "cakeml/misc/miscScript.sml" "the_def" *)
Definition the (d : A) (o_ : option A) : A :=
  match o_ with Some x => x | None => d end.

(*! HOL "cakeml/misc/miscScript.sml" "opt_bind_def" *)
Definition opt_bind (n : option A) (v : B) (e : list (A * B)) : list (A * B) :=
  match n with None => e | Some n' => (n', v) :: e end.

(*! HOL "cakeml/misc/miscScript.sml" "shift_seq_def" *)
Definition shift_seq (k : N) (s : N -> A) : N -> A := fun i => s (i + k).

(*! HOL "cakeml/misc/miscScript.sml" "any_el_def" *)
Fixpoint any_el (n : N) (l : list A) (d : A) : A :=
  match l with
  | [] => d
  | x :: xs => if n =? 0 then x else any_el (n - 1) xs d
  end.

(*! HOL "cakeml/misc/miscScript.sml" "list_inter_def" *)
Definition list_inter `{EqDecision A} (xs ys : list A) : list A :=
  FILTER (fun y => MEM y xs) ys.

(*! HOL "cakeml/misc/miscScript.sml" "anub_def" *)
Fixpoint anub `{EqDecision A} (l : list (A * B)) (acc : list A) : list (A * B) :=
  match l with
  | [] => []
  | (k, v) :: ls => if MEM k acc then anub ls acc else (k, v) :: anub ls (k :: acc)
  end.

(*! HOL "cakeml/misc/miscScript.sml" "find_index_def" *)
Fixpoint find_index `{EqDecision A} (y : A) (l : list A) (n : N) : option N :=
  match l with
  | [] => None
  | x :: xs => if decide (x = y) then Some n else find_index y xs (n + 1)
  end.

(*! HOL "cakeml/misc/miscScript.sml" "lookup_vars_def" *)
Fixpoint lookup_vars `{Inhabited A} (vs : list N) (env : list A) : option (list A) :=
  match vs with
  | [] => Some []
  | v :: vs =>
      if v <? LENGTH env then
        match lookup_vars vs env with
        | Some xs => Some (EL v env :: xs)
        | None => None
        end
      else None
  end.

(*! HOL "cakeml/misc/miscScript.sml" "enumerate_def" *)
Fixpoint enumerate (n : N) (l : list A) : list (N * A) :=
  match l with [] => [] | x :: xs => (n, x) :: enumerate (n + 1) xs end.

(*! HOL "cakeml/misc/miscScript.sml" "option_fold_def" *)
Definition option_fold (f : A -> B -> B) (x : B) (o_ : option A) : B :=
  match o_ with None => x | Some y => f y x end.

(*! HOL "cakeml/misc/miscScript.sml" "list_subset_def" *)
Definition list_subset `{EqDecision A} (l1 l2 : list A) : bool :=
  EVERY (fun x => MEM x l2) l1.

(*! HOL "cakeml/misc/miscScript.sml" "list_set_eq_def" *)
Definition list_set_eq `{EqDecision A} (l1 l2 : list A) : bool :=
  list_subset l1 l2 && list_subset l2 l1.

(*! HOL "cakeml/misc/miscScript.sml" "insert_atI_def" *)
Definition insert_atI (l1 : list A) (n : N) (l2 : list A) : list A :=
  TAKE n l2 ++ l1 ++ DROP (n + LENGTH l1) l2.

(*! HOL "cakeml/misc/miscScript.sml" "is_subseq_def" *)
Fixpoint is_subseq `{EqDecision A} (l1 l2 : list A) : bool :=
  match l2 with
  | [] => true
  | x :: xs =>
      match l1 with
      | [] => false
      | y :: ys => bool_decide (x = y) && is_subseq ys xs || is_subseq ys (x :: xs)
      end
  end.

(*! HOL "cakeml/misc/miscScript.sml" "steps_def" *)
Fixpoint steps (f : A -> B -> A) (x : A) (l : list B) : list (B * A) :=
  match l with
  | [] => []
  | j :: js => let y := f x j in let tr := steps f y js in (j, y) :: tr
  end.

(*! HOL "cakeml/misc/miscScript.sml" "steps_rel_def" *)
Fixpoint steps_rel (R : A -> B -> A -> Prop) (x : A) (l : list (B * A)) : Prop :=
  match l with
  | [] => True
  | (j, y) :: tr => R x j y /\ steps_rel R y tr
  end.

(** HOL [UPDATE_LIST], written [f =++ l]. *)
(*! HOL "cakeml/misc/miscScript.sml" "UPDATE_LIST_def" *)
Definition UPDATE_LIST `{EqDecision A} : (A -> B) -> list (A * B) -> A -> B :=
  FOLDL (combin.C (pair.UNCURRY combin.UPDATE)).

End Defs.

(*! HOL "cakeml/misc/miscScript.sml" "max3_def" *)
Definition max3 (x y z : N) : N :=
  if y <? x then (if x <? z then z else x) else (if y <? z then z else y).

(*! HOL "cakeml/misc/miscScript.sml" "between_def" *)
Definition between (x y z : N) : bool := (x <=? z) && (z <? y).

(*! HOL "cakeml/misc/miscScript.sml" "make_even_def" *)
Definition make_even (n : N) : N := if EVEN n then n else n + 1.

(*! HOL "cakeml/misc/miscScript.sml" "sum_cmp_def" *)
Definition sum_cmp {A B} (c1 : A -> A -> ordering) (c2 : B -> B -> ordering)
  (x1 x2 : A + B) : ordering :=
  match x1 with
  | inl n1 => match x2 with inl n2 => c1 n1 n2 | inr _ => LESS end
  | inr n1 => match x2 with inl _ => GREATER | inr n2 => c2 n1 n2 end
  end.

(** ** Theorems *)

(*! HOL "cakeml/misc/miscScript.sml" "the_OPTION_MAP" *)
Theorem the_OPTION_MAP : forall {A} (f : A -> A) d opt,
  f d = d -> the d (option_map f opt) = f (the d opt).
Proof. intros A f d [x|] H; cbn; auto. Qed.

(*! HOL "cakeml/misc/miscScript.sml" "the_nil_eq_cons" *)
Theorem the_nil_eq_cons : forall {A} (x : option (list A)) y z,
  the [] x = y :: z <-> x = Some (y :: z).
Proof. intros A [l|] y z; cbn; split; congruence. Qed.

(*! HOL "cakeml/misc/miscScript.sml" "LENGTH_enumerate" *)
Theorem LENGTH_enumerate : forall {A} (xs : list A) k, LENGTH (enumerate k xs) = LENGTH xs.
Proof. intros A xs; induction xs as [|x xs IH]; intros k; cbn [enumerate LENGTH]; [reflexivity|rewrite IH; reflexivity]. Qed.

(*! HOL "cakeml/misc/miscScript.sml" "EL_enumerate" *)
Theorem EL_enumerate : forall {A} `{Inhabited A} (xs : list A) n k,
  n < LENGTH xs -> EL n (enumerate k xs) = (n + k, EL n xs).
Proof.
  intros A HA0 xs; induction xs as [|x xs IH]; intros n k Hn; cbn [LENGTH] in Hn; [lia|].
  destruct (N.zero_or_succ n) as [->|[m ->]]; [reflexivity|].
  rewrite !EL_SUC; cbn [TL enumerate]; rewrite IH by lia; f_equal; lia.
Qed.

(*! HOL "cakeml/misc/miscScript.sml" "MEM_enumerate_IMP" *)
Theorem MEM_enumerate_IMP : forall {A} `{EqDecision A} i (e : A) ls k,
  MEM (i, e) (enumerate k ls) -> MEM e ls.
Proof.
  intros A HA0 i e ls; induction ls as [|x ls IH]; intros k; cbn; [discriminate|].
  unfold is_true; rewrite !orb_true_iff, !bool_decide_spec.
  intros [H|H]; [injection H as -> ->; auto|right; eapply IH; eauto].
Qed.

(*! HOL "cakeml/misc/miscScript.sml" "MAP_FST_enumerate" *)
Theorem MAP_FST_enumerate : forall {A} k (ls : list A),
  MAP fst (enumerate k ls) = GENLIST (N.add k) (LENGTH ls).
Proof.
  intros A k ls; revert k; induction ls as [|x ls IH] using rev_ind; intros k; [reflexivity|].
  assert (E : forall k, enumerate k (ls ++ [x]) = enumerate k ls ++ [(k + LENGTH ls, x)]).
  { clear IH; induction ls as [|y ls IHl]; intros k'; cbn [enumerate app LENGTH].
    - rewrite N.add_0_r; reflexivity.
    - rewrite IHl; cbn [app]; replace (k' + 1 + LENGTH ls) with (k' + SUC (LENGTH ls)) by lia; reflexivity. }
  rewrite E, map_app, IH.
  replace (LENGTH (ls ++ [x])) with (SUC (LENGTH ls))
    by (rewrite !LENGTH_length, length_app; cbn [length]; lia).
  rewrite (proj2 (GENLIST_thm _ _)), SNOC_app; reflexivity.
Qed.

(*! HOL "cakeml/misc/miscScript.sml" "find_index_INDEX_FIND" *)
Theorem find_index_INDEX_FIND : forall {A} `{EqDecision A} (y : A) xs n,
  find_index y xs n = option_map fst (INDEX_FIND n (fun x => bool_decide (y = x)) xs).
Proof.
  intros A HA0 y xs; induction xs as [|x xs IH]; intros n; [reflexivity|]; cbn.
  unfold bool_decide; destruct (decide (x = y)), (decide (y = x)); subst; try congruence.
  - reflexivity.
  - rewrite IH, N.add_1_r; reflexivity.
Qed.

(*! HOL "cakeml/misc/miscScript.sml" "find_index_INDEX_OF" *)
Theorem find_index_INDEX_OF : forall {A} `{EqDecision A} (y : A) xs,
  find_index y xs 0 = INDEX_OF y xs.
Proof. intros; rewrite find_index_INDEX_FIND; reflexivity. Qed.

(*! HOL "cakeml/misc/miscScript.sml" "find_index_NOT_MEM" *)
Theorem find_index_NOT_MEM : forall {A} `{EqDecision A} ls (x : A) n,
  ~ MEM x ls <-> find_index x ls n = None.
Proof.
  intros A HA0 ls; induction ls as [|h ls IH]; intros x n; cbn; [split; auto; discriminate|].
  unfold is_true; rewrite orb_true_iff, bool_decide_spec.
  destruct (decide (h = x)) as [->|Hne].
  - split; [intros H; exfalso; auto|discriminate].
  - rewrite <- IH; split; intros H; [intros Hm; apply H; auto|intros [E|E]; [congruence|auto]].
Qed.

(*! HOL "cakeml/misc/miscScript.sml" "find_index_MEM" *)
Theorem find_index_MEM : forall {A} `{EqDecision A} `{Inhabited A} ls (x : A) n,
  MEM x ls -> exists i, find_index x ls n = Some (n + i) /\ i < LENGTH ls /\ EL i ls = x.
Proof.
  intros A Heq Hinh ls; induction ls as [|h ls IH]; intros x n; cbn; [discriminate|].
  unfold is_true; rewrite orb_true_iff, bool_decide_spec.
  destruct (decide (h = x)) as [->|Hne].
  - intros _; exists 0; split; [f_equal; lia|split; [lia|reflexivity]].
  - intros [E|E]; [congruence|].
    destruct (IH x (n + 1) E) as (i & H1 & H2 & H3).
    exists (SUC i); rewrite H1; split; [f_equal; lia|split; [lia|rewrite EL_SUC; exact H3]].
Qed.

(*! HOL "cakeml/misc/miscScript.sml" "find_index_LESS_LENGTH" *)
Theorem find_index_LESS_LENGTH : forall {A} `{EqDecision A} ls (n : A) m i,
  find_index n ls m = Some i -> m <= i /\ i < m + LENGTH ls.
Proof.
  intros A HA0 ls; induction ls as [|h ls IH]; intros n m i; cbn; [discriminate|].
  destruct (decide (h = n)); [intros H; injection H as <-; lia|].
  intros H; apply IH in H; lia.
Qed.

(*! HOL "cakeml/misc/miscScript.sml" "EVERY_lookup_vars" *)
Theorem EVERY_lookup_vars : forall {A} `{Inhabited A} (P : A -> bool) vs env env',
  EVERY P env /\ lookup_vars vs env = Some env' -> EVERY P env'.
Proof.
  intros A HA0 P vs; induction vs as [|v vs IH]; intros env env' [Henv H]; cbn [lookup_vars] in H.
  - injection H as <-; reflexivity.
  - destruct (v <? LENGTH env) eqn:Hv; [|discriminate].
    destruct (lookup_vars vs env) as [xs|] eqn:Hx; [|discriminate].
    injection H as <-; cbn; apply andb_true_iff; split; [|eapply IH; eauto].
    apply N.ltb_lt in Hv; rewrite EL_nth by exact Hv.
    apply EVERY_Forall in Henv; rewrite Forall_forall in Henv; apply Henv, nth_In.
    rewrite LENGTH_length in Hv; lia.
Qed.

(*! HOL "cakeml/misc/miscScript.sml" "EVEN_make_even" *)
Theorem EVEN_make_even : forall x, EVEN (make_even x).
Proof.
  intros x; unfold make_even; destruct (N.even x) eqn:E; [exact E|].
  rewrite N.add_1_r, N.even_succ, <- N.negb_even, E; reflexivity.
Qed.

(*! HOL "cakeml/misc/miscScript.sml" "LAST_MAP_SND_steps_FOLDL" *)
Theorem LAST_MAP_SND_steps_FOLDL : forall {A B} `{Inhabited A} (f : A -> B -> A) x ls,
  LAST (x :: MAP snd (steps f x ls)) = FOLDL f x ls.
Proof.
  intros A B HA0 f x ls; revert x; induction ls as [|j ls IH]; intros x; [reflexivity|].
  cbn [steps MAP FOLDL]; rewrite <- IH; reflexivity.
Qed.

(*! HOL "cakeml/misc/miscScript.sml" "list_subset_LENGTH" *)
Theorem list_subset_LENGTH : forall {A} `{EqDecision A} (l1 l2 : list A),
  ALL_DISTINCT l1 /\ list_subset l1 l2 -> LENGTH l1 <= LENGTH l2.
Proof.
  intros A HA0 l1 l2 [Hd Hs]; rewrite !LENGTH_length.
  enough (length l1 <= length l2)%nat by lia.
  apply NoDup_incl_length.
  - clear Hs; induction l1 as [|h t IH]; constructor; cbn in Hd;
      apply andb_true_iff in Hd as [Hh Ht]; auto.
    intros Hin; apply MEM_In in Hin; rewrite Hin in Hh; discriminate.
  - intros x Hx; unfold list_subset in Hs; apply EVERY_Forall in Hs.
    rewrite Forall_forall in Hs; apply MEM_In, Hs, Hx.
Qed.

(** ** [app_list] *)

(*! HOL "cakeml/misc/miscScript.sml" "app_list" *)
Inductive app_list (A : Type) : Type :=
| List (l : list A)
| Append (l1 l2 : app_list A)
| Nil.
Arguments List {A} l.
Arguments Append {A} l1 l2.
Arguments Nil {A}.

#[global] Instance app_list_inhabited {A} : Inhabited (app_list A) := Nil.

#[global] Instance app_list_eq_dec {A} `{EqDecision A} : EqDecision (app_list A).
Proof.
  intros x; induction x as [l|x1 IH1 x2 IH2|]; intros [l'|y1 y2|];
    try (right; discriminate).
  - destruct (decide (l = l')) as [->|n]; [left; reflexivity|right; congruence].
  - destruct (IH1 y1) as [->|n]; [|right; congruence].
    destruct (IH2 y2) as [->|n]; [left; reflexivity|right; congruence].
  - left; reflexivity.
Defined.

(** Deciding [l = Nil] needs no equality on the elements. *)
#[global] Instance app_list_eq_Nil_dec {A} (l : app_list A) : Decision (l = Nil).
Proof. destruct l; [right|right|left]; congruence. Defined.

(*! HOL "cakeml/misc/miscScript.sml" "append_aux_def" *)
Fixpoint append_aux {A} (l : app_list A) (aux : list A) : list A :=
  match l with
  | Nil => aux
  | List xs => xs ++ aux
  | Append l1 l2 => append_aux l1 (append_aux l2 aux)
  end.

(*! HOL "cakeml/misc/miscScript.sml" "append_def" *)
Definition append {A} (l : app_list A) : list A := append_aux l [].

(*! HOL "cakeml/misc/miscScript.sml" "append_aux_thm" *)
Theorem append_aux_thm : forall {A} (l : app_list A) xs, append_aux l xs = append_aux l [] ++ xs.
Proof.
  intros A l; induction l as [l|l1 IH1 l2 IH2|]; intros xs; cbn.
  - rewrite app_nil_r; reflexivity.
  - rewrite IH2, IH1, (IH1 (append_aux l2 [])), app_assoc; reflexivity.
  - reflexivity.
Qed.

(*! HOL "cakeml/misc/miscScript.sml" "append_thm" *)
Theorem append_thm : forall {A} (l1 l2 : app_list A) (xs : list A),
  append (Append l1 l2) = append l1 ++ append l2 /\
  append (List xs) = xs /\
  append (@Nil A) = [].
Proof.
  intros; unfold append; cbn; repeat split.
  - apply append_aux_thm.
  - apply app_nil_r.
Qed.

(*! HOL "cakeml/misc/miscScript.sml" "SmartAppend_def" *)
Definition SmartAppend {A} (l1 l2 : app_list A) : app_list A :=
  match l1, l2 with
  | Nil, _ => l2
  | _, Nil => l1
  | _, _ => Append l1 l2
  end.

(*! HOL "cakeml/misc/miscScript.sml" "SmartAppend_thm" *)
Theorem SmartAppend_thm : forall {A} (l1 l2 : app_list A),
  SmartAppend l1 l2 =
    if decide (l1 = Nil) then l2 else
    if decide (l2 = Nil) then l1 else Append l1 l2.
Proof. intros A [] []; reflexivity. Qed.

(*! HOL "cakeml/misc/miscScript.sml" "SmartAppend_Nil" *)
Theorem SmartAppend_Nil : forall {A} (l : app_list A),
  SmartAppend l Nil = l /\ SmartAppend Nil l = l.
Proof. intros A []; split; reflexivity. Qed.

(*! HOL "cakeml/misc/miscScript.sml" "append_SmartAppend" *)
Theorem append_SmartAppend : forall {A} (l1 l2 : app_list A),
  append (SmartAppend l1 l2) = append l1 ++ append l2.
Proof.
  intros A l1 l2; rewrite SmartAppend_thm.
  destruct (decide (l1 = Nil)) as [->|n1]; [reflexivity|].
  destruct (decide (l2 = Nil)) as [->|n2].
  - change (append (@Nil A)) with (@nil A); rewrite app_nil_r; reflexivity.
  - exact (proj1 (append_thm l1 l2 [])).
Qed.

(** ** Memory helpers over words *)

Section Words.
Context {a : N}.
Local Open Scope word_scope.

(** HOL [read_bytearray] recurses on [SUC n]; [read_bytearray_def] gives
    HOL's equations. *)
Definition read_bytearray {B} (w : word a) (n : N) (get_byte : word a -> option B)
  : option (list B) :=
  num_rec (fun _ => Some [])
    (fun _ r w =>
       match get_byte w with
       | None => None
       | Some b => match r (w + n2w 1) with None => None | Some bs => Some (b :: bs) end
       end) n w.

(*! HOL "cakeml/misc/miscScript.sml" "read_bytearray_def" *)
Theorem read_bytearray_def : forall {B} (w : word a) (get_byte : word a -> option B) n,
  read_bytearray w 0 get_byte = Some [] /\
  read_bytearray w (SUC n) get_byte =
    match get_byte w with
    | None => None
    | Some b =>
        match read_bytearray (w + n2w 1) n get_byte with
        | None => None
        | Some bs => Some (b :: bs)
        end
    end.
Proof. intros; split; [reflexivity|]. unfold read_bytearray; rewrite num_rec_SUC; reflexivity. Qed.

(*! HOL "cakeml/misc/miscScript.sml" "read_bytearray_LENGTH" *)
Theorem read_bytearray_LENGTH : forall {B} n (w : word a) (f : word a -> option B) x,
  read_bytearray w n f = Some x -> LENGTH x = n.
Proof.
  intros B n; induction n as [|n IH] using N.peano_ind; intros w f x.
  - intros H; injection H as <-; reflexivity.
  - rewrite (proj2 (read_bytearray_def w f n)).
    destruct (f w); [|discriminate].
    destruct (read_bytearray (w + n2w 1) n f) eqn:E; [|discriminate].
    intros H; injection H as <-; cbn [LENGTH]; f_equal; eapply IH; eauto.
Qed.

(** [all_words base n] is the set [{base; base+1; ...; base+(n-1)}]. *)
Definition all_words (base : word a) (n : N) : word a -> Prop :=
  num_rec (fun _ _ => False) (fun _ r base x => x = base \/ r (base + n2w 1) x) n base.

(*! HOL "cakeml/misc/miscScript.sml" "all_words_def" *)
Theorem all_words_def : forall base n,
  all_words base 0 = (fun _ => False) /\
  all_words base (SUC n) = (fun x => x = base \/ all_words (base + n2w 1) n x).
Proof. intros; split; [reflexivity|]. unfold all_words; rewrite num_rec_SUC; reflexivity. Qed.

(*! HOL "cakeml/misc/miscScript.sml" "asm_write_bytearray_def" *)
Fixpoint asm_write_bytearray (w : word a) (l : list word8) (m : word a -> word8) : word a -> word8 :=
  match l with
  | [] => m
  | x :: xs => combin.UPDATE w x (asm_write_bytearray (w + n2w 1) xs m)
  end.

(*! HOL "cakeml/misc/miscScript.sml" "bytes_in_memory_def" *)
Fixpoint bytes_in_memory (w : word a) (l : list word8) (m : word a -> word8)
  (dm : word a -> Prop) : Prop :=
  match l with
  | [] => True
  | x :: xs => m w = x /\ dm w /\ bytes_in_memory (w + n2w 1) xs m dm
  end.

(*! HOL "cakeml/misc/miscScript.sml" "bytes_in_mem_def" *)
Fixpoint bytes_in_mem {B} (w : word a) (l : list B) (m : word a -> B)
  (md k : word a -> Prop) : Prop :=
  match l with
  | [] => True
  | b :: bs => md w /\ ~ k w /\ m w = b /\ bytes_in_mem (w + n2w 1) bs m md k
  end.

(*! HOL "cakeml/misc/miscScript.sml" "bytes_in_mem_IMP" *)
Theorem bytes_in_mem_IMP : forall m dm dm1 xs (p : word a),
  bytes_in_mem p xs m dm dm1 -> bytes_in_memory p xs m dm.
Proof.
  intros m dm dm1 xs; induction xs as [|x xs IH]; intros p; cbn; [auto|].
  intros (H1 & _ & H3 & H4); auto.
Qed.

(*! HOL "cakeml/misc/miscScript.sml" "mem_eq_imp_asm_write_bytearray_eq" *)
Theorem mem_eq_imp_asm_write_bytearray_eq : forall m1 m2 k (w : word a) bs,
  m1 k = m2 k -> asm_write_bytearray w bs m1 k = asm_write_bytearray w bs m2 k.
Proof.
  intros m1 m2 k w bs; revert w; induction bs as [|x bs IH]; intros w H; cbn; [exact H|].
  unfold combin.UPDATE; destruct (decide (w = k)); auto.
Qed.

End Words.

(** HOL [good_dimindex(:'a)]: the word width is 32 or 64. *)
(*! HOL "cakeml/misc/miscScript.sml" "good_dimindex_def" *)
Definition good_dimindex (a : N) : Prop := dimindex a = 32 \/ dimindex a = 64.

(** ** Lookups in [sptree]s *)

(*! HOL "cakeml/misc/miscScript.sml" "lookup_any_def" *)
Definition lookup_any {A} (x : N) (sp : sptree.spt A) (d : A) : A :=
  match sptree.lookup x sp with
  | None => d
  | Some m => m
  end.

(*! HOL "cakeml/misc/miscScript.sml" "tlookup_def" *)
Definition tlookup (m : sptree.spt N) (k : N) : N :=
  match sptree.lookup k m with
  | None => k
  | Some k => k
  end.

(** [word_list a xs]: the words [xs] stored from address [a] on, as a
    [set_sep] assertion. *)
Section WordList.
Context {a : N} {B : Type}.

(*! HOL "cakeml/misc/miscScript.sml" "word_list_def" *)
Fixpoint word_list (ad : word a) (xs : list B) : (word a * B -> Prop) -> Prop :=
  match xs with
  | [] => set_sep.emp
  | x :: xs => set_sep.STAR (set_sep.one (ad, x)) (word_list (ad + byte.bytes_in_word)%w xs)
  end.

(*! HOL "cakeml/misc/miscScript.sml" "word_list_exists_def" *)
Definition word_list_exists (ad : word a) (n : N) : (word a * B -> Prop) -> Prop :=
  set_sep.SEP_EXISTS (fun xs => set_sep.STAR (word_list ad xs) (set_sep.cond (LENGTH xs = n))).

End WordList.
