(** * CakeML [word_unreachProof]: correctness of [word_unreach]

    Port of [cakeml/compiler/backend/proofs/word_unreachProofScript.sml].

    Notes:
    - HOL's free variables ([p], [s], [n1], [n2], [m], ...) are quantified
      explicitly.  HOL [s with locals := l] is [set_locals l s].
    - [copy_vars] is polymorphic in the value type (HOL's ['a]); [THE]
      needs an [Inhabited] instance.  HOL's [λx. n ≠ x] in [FILTER] is
      [fun x => bool_decide (n <> x)].
    - [copy_vars_anub] is HOL's equation between (curried) functions.
    - [push_env_handler]: HOL's free variable [handler] is [h] (it would
      shadow the state field [handler]).
    - Proofs: [evaluate_Seq_assoc_right_lemma] is by induction on the
      program ([prog_nested_ind]) instead of [Seq_assoc_right_ind];
      [evaluate_Loop_body_eq] by well-founded induction on the clock.  The
      Galette-only helpers (the [evaluate] equations used for rewriting,
      the simulation lemmas [sim_*]) have no HOL original. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common wordLang word_unreach.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem wordConvs.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import
  consts consts_with clock dec_clock.
Open Scope N_scope.

(** ** Galette-only helpers *)

Lemma bd_true (P : Prop) `{Decision P} : P -> bool_decide P = true.
Proof. apply bool_decide_spec. Qed.
Lemma bd_false (P : Prop) `{Decision P} : ~ P -> bool_decide P = false.
Proof. intros HP; destruct (bool_decide P) eqn:E; [|reflexivity]. apply bool_decide_spec in E; tauto. Qed.

Section Eqns.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

Lemma evaluate_Skip_eq s : evaluate (Skip, s) = (NONE, s).
Proof. rewrite (evaluate_eqn Skip s); reflexivity. Qed.

Lemma evaluate_Seq_eq (p1 p2 : prog a) s :
  evaluate (Seq p1 p2, s) =
  let '(res, s1) := evaluate (p1, s) in
  if bool_decide (res = NONE) then evaluate (p2, s1) else (res, s1).
Proof. rewrite (evaluate_eqn (Seq p1 p2) s); cbn [evaluate_body]. rewrite fix_clock_evaluate. reflexivity. Qed.

Lemma evaluate_Move_eq pri moves s :
  evaluate (@Move a pri moves, s) =
  if ALL_DISTINCT (MAP FST moves) then
    match get_vars (MAP SND moves) s with
    | NONE => (SOME Error, s)
    | SOME vs => (NONE, set_vars (MAP FST moves) vs s)
    end
  else (SOME Error, s).
Proof. rewrite (evaluate_eqn (Move pri moves) s); reflexivity. Qed.

Lemma evaluate_Loop_eq names (p : prog a) exit_names s s' :
  cut_state (names, LN) s = SOME s' ->
  evaluate (Loop names p exit_names, s) =
  let '(res, s1) := evaluate (p, s') in
  if cont_loop res then
    (if clock s1 =? 0 then (SOME TimeOut, flush_state true s1)
     else evaluate (STOP (Loop names p exit_names), dec_clock s1))
  else if bool_decide (res = SOME (Break 0)) then
    match cut_state (exit_names, LN) s1 with
    | NONE => (SOME Error, s1)
    | SOME s2 => (NONE, s2)
    end
  else (exit_loop res, s1).
Proof.
  intros E. rewrite (evaluate_eqn (Loop names p exit_names) s); cbn [evaluate_body].
  rewrite E. rewrite fix_clock_evaluate. reflexivity.
Qed.

Lemma evaluate_Loop_None names (p : prog a) exit_names s :
  cut_state (names, LN) s = NONE ->
  evaluate (Loop names p exit_names, s) = (SOME Error, s).
Proof. intros E. rewrite (evaluate_eqn (Loop names p exit_names) s); cbn [evaluate_body]. rewrite E. reflexivity. Qed.

End Eqns.

(** ** Semantics *)

Section Sem.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

(*! HOL "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "evaluate_Skip_Seq" *)
Theorem evaluate_Skip_Seq : forall (p : prog a) s,
  evaluate (Seq Skip p, s) = evaluate (p, s).
Proof. intros; rewrite evaluate_Seq_eq, evaluate_Skip_eq, bd_true by reflexivity; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "evaluate_Seq_Skip" *)
Theorem evaluate_Seq_Skip : forall (p1 : prog a) s,
  evaluate (Seq p1 Skip, s) = evaluate (p1, s).
Proof.
  intros; rewrite evaluate_Seq_eq. destruct (evaluate (p1, s)) as [r t].
  destruct (bool_decide (r = NONE)) eqn:E; [|reflexivity].
  apply bool_decide_spec in E; subst r. apply evaluate_Skip_eq.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "evaluate_Seq_assoc" *)
Theorem evaluate_Seq_assoc : forall (p1 p2 p3 : prog a) s,
  evaluate (Seq p1 (Seq p2 p3), s) = evaluate (Seq (Seq p1 p2) p3, s).
Proof.
  intros; rewrite !evaluate_Seq_eq. destruct (evaluate (p1, s)) as [r t].
  destruct (bool_decide (r = NONE)) eqn:E.
  - rewrite evaluate_Seq_eq. reflexivity.
  - rewrite E. reflexivity.
Qed.

End Sem.

(** ** [merge_moves] *)

(** Galette-only: HOL's [miscTheory.anub_all_distinct_keys] (not ported in
    [misc]), stated with [NoDup]. *)
Lemma anub_NoDup {B} (ls : list (N * B)) acc :
  NoDup acc -> NoDup (List.map fst (anub ls acc) ++ acc).
Proof.
  revert acc; induction ls as [|[k v] ls IH]; intros acc Hacc; cbn [anub]; [exact Hacc|].
  destruct (MEM k acc) eqn:E; [apply IH, Hacc|].
  cbn [List.map fst]. apply (Permutation.Permutation_NoDup (Permutation.Permutation_sym
    (Permutation.Permutation_middle _ _ _))).
  apply IH. constructor; [|exact Hacc].
  intros Hin. apply MEM_In in Hin. rewrite Hin in E. discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "ALL_DISTINCT_merge_moves" *)
Theorem ALL_DISTINCT_merge_moves : forall l1 l2,
  ALL_DISTINCT (MAP FST (merge_moves l1 l2)).
Proof.
  intros l1 l2; unfold is_true; apply ALL_DISTINCT_NoDup_list.
  unfold merge_moves; cbn zeta.
  pose proof (anub_NoDup (MAP (fun '(x, y) => match ALOOKUP l1 y with
                                              | None => (x, y)
                                              | Some v => (x, v)
                                              end) l2 ++ l1) [] (NoDup_nil _)) as H.
  rewrite app_nil_r in H. exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "copy_vars_def" *)
Fixpoint copy_vars {A} `{Inhabited A} (moves : list (N * N)) (from to : num_map A) : num_map A :=
  match moves with
  | [] => to
  | (l, r) :: rest => insert l (THE (lookup r from)) (copy_vars rest from to)
  end.

Section CopyVars.
Context {A : Type} `{Inhabited A}.

(*! HOL "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "copy_vars_append" *)
Theorem copy_vars_append : forall xs ys (from to : num_map A),
  copy_vars (xs ++ ys) from to = copy_vars xs from (copy_vars ys from to).
Proof.
  induction xs as [|[l r] xs IH]; intros ys from to; cbn; [reflexivity|]. rewrite IH; reflexivity.
Qed.

(** Galette-only: [anub] depends on [acc] only through membership. *)
Lemma anub_ext {B} (xs : list (N * B)) acc1 acc2 :
  (forall k, In k acc1 <-> In k acc2) -> anub xs acc1 = anub xs acc2.
Proof.
  revert acc1 acc2; induction xs as [|[k v] xs IH]; intros acc1 acc2 Hs; cbn [anub]; [reflexivity|].
  destruct (MEM k acc1) eqn:E1, (MEM k acc2) eqn:E2.
  - apply IH, Hs.
  - apply MEM_In, Hs, MEM_In in E1. congruence.
  - apply MEM_In, Hs, MEM_In in E2. congruence.
  - f_equal. apply IH. intros x; cbn; rewrite Hs; reflexivity.
Qed.

Lemma insert_insert_same (n : N) (w v : A) t : insert n w (insert n v t) = insert n w t.
Proof. rewrite insert_insert. destruct (decide (n = n)); [reflexivity|congruence]. Qed.

Lemma insert_insert_swap (n k : N) (w v : A) t :
  n <> k -> insert n w (insert k v t) = insert k v (insert n w t).
Proof. intros Hne. rewrite insert_insert. destruct (decide (n = k)); [congruence|reflexivity]. Qed.

(** Galette-only generalisation of [copy_vars_MEM_acc]. *)
Lemma copy_vars_anub_agree (s t : num_map A) xs acc1 acc2 n w :
  (forall k, k <> n -> (In k acc1 <-> In k acc2)) ->
  insert n w (copy_vars (anub xs acc1) s t) = insert n w (copy_vars (anub xs acc2) s t).
Proof.
  revert acc1 acc2; induction xs as [|[k v] xs IH]; intros acc1 acc2 Hs; cbn [anub]; [reflexivity|].
  destruct (decide (k = n)) as [->|Hkn].
  - assert (G : forall acc : list N, exists acc' : list N, (forall k, k <> n -> (In k acc <-> In k acc')) /\
        insert n w (copy_vars (if MEM n acc then anub xs acc else (n, v) :: anub xs (n :: acc)) s t) =
        insert n w (copy_vars (anub xs acc') s t)).
    { intros acc. destruct (MEM n acc).
      - exists acc; split; [tauto|reflexivity].
      - exists (n :: acc); split; [intros k Hk; cbn; split; [tauto|intros [->|H']; [congruence|exact H']]|].
        cbn [copy_vars]. apply insert_insert_same. }
    destruct (G acc1) as [a1 [Ha1 ->]], (G acc2) as [a2 [Ha2 ->]].
    apply IH. intros k Hk. rewrite <- Ha1, <- Ha2 by exact Hk. apply Hs, Hk.
  - assert (Hk : In k acc1 <-> In k acc2) by (apply Hs, Hkn).
    destruct (MEM k acc1) eqn:E1, (MEM k acc2) eqn:E2.
    + apply IH, Hs.
    + apply MEM_In, Hk, MEM_In in E1. congruence.
    + apply MEM_In, Hk, MEM_In in E2. congruence.
    + cbn [copy_vars]. rewrite !(insert_insert_swap n k) by congruence. f_equal.
      apply IH. intros x Hx; cbn. rewrite Hs by exact Hx. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "copy_vars_MEM_acc" *)
Theorem copy_vars_MEM_acc : forall (s t : num_map A) xs acc n w,
  MEM n acc ->
  insert n w (copy_vars (anub xs acc) s t) =
  insert n w (copy_vars (anub xs (FILTER (fun x => bool_decide (n <> x)) acc)) s t).
Proof.
  intros s t xs acc n w _. apply copy_vars_anub_agree.
  intros k Hk. rewrite filter_In. split; [intros H'; split; [exact H'|apply bool_decide_spec; congruence]|tauto].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "copy_vars_anub" *)
Theorem copy_vars_anub : forall xs, @copy_vars A _ (anub xs []) = copy_vars xs.
Proof.
  intros xs. apply functional_extensionality; intros from.
  apply functional_extensionality; intros to.
  induction xs as [|[k v] xs IH]; [reflexivity|]. cbn [anub MEM copy_vars].
  rewrite (copy_vars_anub_agree from to xs [k] [] k) by (intros x Hx; cbn; split; [intros [->|[]]; congruence|intros []]).
  rewrite IH. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "lookup_copy_vars_ignore" *)
Theorem lookup_copy_vars_ignore : forall l1 h1 (x y : num_map A),
  ALOOKUP l1 h1 = NONE -> lookup h1 (copy_vars l1 x y) = lookup h1 y.
Proof.
  induction l1 as [|[l r] l1 IH]; intros h1 x y H'; cbn [copy_vars]; [reflexivity|].
  cbn [ALOOKUP] in H'. rewrite lookup_insert.
  destruct (decide (l = h1)) as [->|Hne]; [discriminate|].
  destruct (decide (h1 = l)) as [->|]; [congruence|]. apply IH, H'.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "lookup_copy_vars" *)
Theorem lookup_copy_vars : forall l1 h1 y (s t : num_map A) z,
  ALOOKUP l1 h1 = SOME y /\ lookup h1 (copy_vars l1 s t) = SOME z ->
  THE (lookup y s) = z.
Proof.
  induction l1 as [|[l r] l1 IH]; intros h1 y s t z [H1 H2]; cbn [ALOOKUP] in H1; [discriminate|].
  cbn [copy_vars] in H2. rewrite lookup_insert in H2.
  destruct (decide (l = h1)) as [->|Hne].
  - injection H1 as <-. destruct (decide (h1 = h1)); [|congruence]. injection H2 as <-. reflexivity.
  - destruct (decide (h1 = l)) as [->|]; [congruence|]. eapply IH; split; eassumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "IMP_EVERY_MAP_SND_anub" *)
Theorem IMP_EVERY_MAP_SND_anub : forall (xs : list (N * A)) acc p,
  EVERY p (MAP SND xs) -> EVERY p (MAP SND (anub xs acc)).
Proof.
  induction xs as [|[k v] xs IH]; intros acc p H'; cbn [anub]; [exact H'|].
  cbn [MAP List.map SND snd EVERY] in H'. unfold is_true in *. apply andb_prop in H' as [H1 H2].
  destruct (MEM k acc); [apply IH, H2|]. cbn [List.map snd EVERY]. rewrite H1; apply IH, H2.
Qed.

(** Galette-only: the core of [merge_moves_Skip]. *)
Lemma copy_vars_merge (l1 l2 : list (N * N)) (L : num_map A) :
  EVERY (fun x => IS_SOME (lookup x (copy_vars l1 L L))) (MAP SND l2) ->
  forall t,
    copy_vars (MAP (fun '(x, y) => match ALOOKUP l1 y with
                                   | None => (x, y)
                                   | Some v => (x, v)
                                   end) l2) L t =
    copy_vars l2 (copy_vars l1 L L) t.
Proof.
  induction l2 as [|[x y] l2 IH]; intros Hev t; [reflexivity|].
  cbn [MAP List.map SND snd EVERY] in Hev. unfold is_true in Hev.
  apply andb_prop in Hev as [H1 H2].
  cbn [List.map]. destruct (ALOOKUP l1 y) as [v|] eqn:Ea; cbn [copy_vars]; rewrite IH by exact H2; f_equal.
  - destruct (lookup y (copy_vars l1 L L)) as [z|] eqn:El; [|discriminate].
    cbn [THE]. apply (lookup_copy_vars l1 y v L L z); split; assumption.
  - rewrite (lookup_copy_vars_ignore l1 y L L Ea). reflexivity.
Qed.

End CopyVars.

Section Moves.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

Lemma alist_insert_copy_vars moves s x (t : num_map (word_loc a)) :
  get_vars (MAP SND moves) s = SOME x ->
  alist_insert (MAP FST moves) x t = copy_vars moves (locals s) t.
Proof.
  revert x; induction moves as [|[l r] moves IH]; intros x Hg;
    cbn [List.map fst snd get_vars alist_insert copy_vars] in Hg |- *.
  - injection Hg as <-. reflexivity.
  - unfold get_var in Hg. destruct (lookup r (locals s)) as [v|] eqn:E; [|discriminate].
    destruct (get_vars (MAP SND moves) s) as [xs|] eqn:E2; [|discriminate].
    injection Hg as <-. cbn [alist_insert]. rewrite (IH xs eq_refl). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "evaluate_Move" *)
Theorem evaluate_Move : forall pri moves s,
  evaluate (@Move a pri moves, s) =
  if ALL_DISTINCT (MAP FST moves) then
    match get_vars (MAP SND moves) s with
    | NONE => (SOME Error, s)
    | SOME l => (NONE, set_locals (copy_vars moves (locals s) (locals s)) s)
    end
  else (SOME Error, s).
Proof.
  intros; rewrite evaluate_Move_eq. destruct (ALL_DISTINCT _); [|reflexivity].
  destruct (get_vars _ s) as [vs|] eqn:E; [|reflexivity].
  unfold set_vars; rewrite (alist_insert_copy_vars _ _ _ _ E). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "get_vars_IS_SOME_lookup" *)
Theorem get_vars_IS_SOME_lookup : forall xs s,
  (exists ws, get_vars xs s = SOME ws) <->
  EVERY (fun x => IS_SOME (lookup x (locals s))) xs.
Proof.
  induction xs as [|x xs IH]; intros s; cbn [get_vars EVERY].
  - split; [reflexivity|eauto].
  - unfold get_var. destruct (lookup x (locals s)) eqn:E; cbn.
    + rewrite <- IH. destruct (get_vars xs s); split; intros [ws Hw]; try discriminate; eauto.
    + split; [intros [ws Hw]; discriminate|intros Hf; discriminate Hf].
Qed.

End Moves.

Section MergeMoves.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

Lemma EVERY_In {B} (P : B -> bool) l : EVERY P l <-> (forall x, In x l -> P x = true).
Proof. unfold is_true; rewrite EVERY_Forall, Forall_forall; reflexivity. Qed.

(** HOL's free variables [n1], [n2] and [m] are quantified first. *)
(*! HOL "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "merge_moves_Skip" *)
Theorem merge_moves_Skip : forall n1 n2 m l1 l2 s res s1,
  evaluate (Seq (Move n1 l1) (Move n2 l2), s) = (res, s1) /\ res <> SOME Error ->
  evaluate (@Move a m (merge_moves l1 l2), s) = (res, s1).
Proof.
  intros n1 n2 m l1 l2 s res s1 [H Hr].
  rewrite evaluate_Seq_eq, evaluate_Move in H.
  destruct (ALL_DISTINCT (MAP FST l1)) eqn:D1; [|injection H as <- <-; exfalso; apply Hr; reflexivity].
  destruct (get_vars (MAP SND l1) s) as [v1|] eqn:G1;
    [|injection H as <- <-; exfalso; apply Hr; reflexivity].
  rewrite bd_true in H by reflexivity. rewrite evaluate_Move in H.
  destruct (ALL_DISTINCT (MAP FST l2)) eqn:D2; [|injection H as <- <-; exfalso; apply Hr; reflexivity].
  destruct (get_vars (MAP SND l2) _) as [v2|] eqn:G2;
    [|injection H as <- <-; exfalso; apply Hr; reflexivity].
  injection H as <- <-.
  assert (E2 : EVERY (fun x => IS_SOME (lookup x (copy_vars l1 (locals s) (locals s)))) (MAP SND l2))
    by (exact (proj1 (get_vars_IS_SOME_lookup _ _) (ex_intro _ _ G2))).
  assert (E1 : EVERY (fun x => IS_SOME (lookup x (locals s))) (MAP SND l1))
    by (exact (proj1 (get_vars_IS_SOME_lookup _ _) (ex_intro _ _ G1))).
  rewrite evaluate_Move, (ALL_DISTINCT_merge_moves l1 l2).
  assert (Hex : exists ws, get_vars (MAP SND (merge_moves l1 l2)) s = SOME ws).
  { apply get_vars_IS_SOME_lookup. unfold merge_moves; cbn zeta.
    apply IMP_EVERY_MAP_SND_anub. apply EVERY_In. intros z Hz.
    rewrite map_app in Hz. apply in_app_or in Hz as [Hz|Hz].
    - rewrite map_map in Hz. apply in_map_iff in Hz as [[x y] [Hzy Hin]].
      destruct (ALOOKUP l1 y) as [v|] eqn:Ea; cbn [snd] in Hzy; subst z.
      + apply ALOOKUP_In in Ea. apply (proj1 (EVERY_In _ _) E1).
        apply (in_map snd) in Ea; exact Ea.
      + rewrite <- (lookup_copy_vars_ignore l1 y (locals s) (locals s) Ea).
        apply (proj1 (EVERY_In _ _) E2). apply (in_map snd) in Hin; exact Hin.
    - apply (proj1 (EVERY_In _ _) E1), Hz. }
  destruct Hex as [ws Hws]. rewrite Hws. f_equal.
  change (set_locals ?x (set_locals ?y s)) with (set_locals x s). f_equal.
  unfold merge_moves; cbn zeta. rewrite copy_vars_anub, copy_vars_append.
  apply copy_vars_merge, E2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "merge_moves_thm" *)
Theorem merge_moves_thm : forall n1 n2 m (p : prog a) l1 l2 s res s1,
  evaluate (Seq (Move n1 l1) (Seq (Move n2 l2) p), s) = (res, s1) /\ res <> SOME Error ->
  evaluate (Seq (Move m (merge_moves l1 l2)) p, s) = (res, s1).
Proof.
  intros n1 n2 m p l1 l2 s res s1 [H Hr].
  rewrite evaluate_Seq_assoc in H. rewrite evaluate_Seq_eq in H |- *.
  destruct (evaluate (Seq (Move n1 l1) (Move n2 l2), s)) as [r2 s2] eqn:E.
  destruct (classical_dec (r2 = SOME Error)) as [->|Hn].
  - rewrite bd_false in H by discriminate. injection H as <- <-. exfalso; apply Hr; reflexivity.
  - rewrite (merge_moves_Skip n1 n2 m l1 l2 s r2 s2 (conj E Hn)). exact H.
Qed.

End MergeMoves.

Section SimpSeq.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

Lemma evaluate_not_NONE_Seq (p1 p2 : prog a) s :
  fst (evaluate (p1, s)) <> NONE -> evaluate (Seq p1 p2, s) = evaluate (p1, s).
Proof.
  intros Hn. rewrite evaluate_Seq_eq. destruct (evaluate (p1, s)) as [r t].
  cbn [fst] in Hn. rewrite bd_false by exact Hn. reflexivity.
Qed.

Ltac not_none p s :=
  rewrite (evaluate_eqn p s); cbn [evaluate_body];
  repeat match goal with
         | |- context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta
         end;
  cbn [fst]; congruence.

Lemma Raise_not_NONE n s : fst (evaluate (@Raise a n, s)) <> NONE.
Proof. not_none (@Raise a n) s. Qed.
Lemma Return_not_NONE n ns s : fst (evaluate (@Return a n ns, s)) <> NONE.
Proof. not_none (@Return a n ns) s. Qed.
Lemma Break_not_NONE n s : fst (evaluate (@wordLang.Break a n, s)) <> NONE.
Proof. not_none (@wordLang.Break a n) s. Qed.
Lemma Continue_not_NONE n s : fst (evaluate (@wordLang.Continue a n, s)) <> NONE.
Proof. not_none (@wordLang.Continue a n) s. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "evaluate_SimpSeq" *)
Theorem evaluate_SimpSeq : forall (p1 p2 : prog a) s res s1,
  evaluate (Seq p1 p2, s) = (res, s1) /\ res <> SOME Error ->
  evaluate (SimpSeq p1 p2, s) = (res, s1).
Proof.
  intros p1 p2 s res s1 [H Hr]. unfold SimpSeq; cbn zeta.
  destruct p2; cbn iota; [rewrite evaluate_Seq_Skip in H; exact H|..].
  all: destruct p1; try exact H.
  all: try (rewrite evaluate_Skip_Seq in H; exact H).
  all: try (rewrite evaluate_not_NONE_Seq in H;
            [exact H|first [apply Raise_not_NONE | apply Return_not_NONE
                           | apply Break_not_NONE | apply Continue_not_NONE]]).
  all: unfold dest_Seq_Move; cbn beta iota zeta; try exact H.
  - (* Move, Move *) exact (merge_moves_Skip _ _ _ _ _ _ _ _ (conj H Hr)).
  - (* Move, Seq *)
    match goal with |- context [match ?q with Move _ _ => _ | _ => _ end] => destruct q end;
      cbn beta iota zeta; try exact H.
    match goal with |- context [match ?q with Skip => _ | _ => _ end] => destruct q end;
      cbn beta iota zeta.
    1: rewrite evaluate_Seq_assoc, evaluate_Seq_Skip in H;
       exact (merge_moves_Skip _ _ _ _ _ _ _ _ (conj H Hr)).
    all: exact (merge_moves_thm _ _ _ _ _ _ _ _ _ (conj H Hr)).
Qed.

End SimpSeq.

(** ** [Seq_assoc_right] *)

Section AssocRight.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

(*! HOL "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "push_env_handler" *)
Theorem push_env_handler : forall x' (h : option (N * (prog a * (N * N)))) s,
  push_env x'
    (match h with
     | None => None
     | Some (y1, (q2, (y2, y3))) => Some (y1, (Seq_assoc_right q2 Skip, (y2, y3)))
     end) (dec_clock s) =
  push_env x' h (dec_clock s).
Proof. intros x' [[y1 [q2 [y2 y3]]]|] s; reflexivity. Qed.

(** Galette-only: the handler program does not matter to [push_env]. *)
Lemma push_env_SAR x' y1 (q2 : prog a) l s :
  push_env x' (SOME (y1, (Seq_assoc_right q2 Skip, l))) s = push_env x' (SOME (y1, (q2, l))) s.
Proof. destruct l; reflexivity. Qed.

(** Galette-only: [q] behaves as [p] whenever [p] does not fail. *)
Definition sim (p q : prog a) : Prop :=
  forall s res s1, evaluate (p, s) = (res, s1) /\ res <> SOME Error -> evaluate (q, s) = (res, s1).

Lemma sim_Seq p p' acc s res s1 :
  sim p p' -> evaluate (Seq p acc, s) = (res, s1) -> res <> SOME Error ->
  evaluate (Seq p' acc, s) = (res, s1).
Proof.
  intros Hs H Hr. rewrite evaluate_Seq_eq in H |- *.
  destruct (evaluate (p, s)) as [r t] eqn:E.
  destruct (classical_dec (r = SOME Error)) as [->|Hn].
  - rewrite bd_false in H by discriminate. injection H as <- <-. exfalso; apply Hr; reflexivity.
  - rewrite (Hs s r t (conj E Hn)). exact H.
Qed.

Ltac sim_split H :=
  revert H;
  repeat first
    [ progress (rewrite ?push_env_SAR, ?fix_clock_evaluate)
    | match goal with
      | |- ?P -> _ =>
          match P with
          | context [match ?x with _ => _ end] =>
              let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
          end
      end ];
  intros H.

Ltac sim_close H Hr :=
  first
    [ exact H
    | match goal with
      | HS : sim _ _ |- _ => apply HS; split; [exact H|exact Hr]
      end ].

Lemma sim_If cmp r ri (q1 q1' q2 q2' : prog a) :
  sim q1 q1' -> sim q2 q2' -> sim (If cmp r ri q1 q2) (If cmp r ri q1' q2').
Proof.
  intros S1 S2 s res s1 [H Hr]. rewrite evaluate_eqn in H |- *. cbn [evaluate_body] in H |- *.
  sim_split H; sim_close H Hr.
Qed.

Lemma sim_MustTerminate (q q' : prog a) : sim q q' -> sim (MustTerminate q) (MustTerminate q').
Proof.
  intros S s res s1 [H Hr]. rewrite evaluate_eqn in H |- *. cbn [evaluate_body] in H |- *.
  destruct (termdep s =? 0); [exact H|].
  destruct (evaluate (q, _)) as [r t] eqn:E.
  destruct (bool_decide (r = SOME TimeOut)) eqn:Et;
    [injection H as <- <-; exfalso; apply Hr; reflexivity|].
  injection H as <- <-. rewrite (S _ _ _ (conj E Hr)), Et. reflexivity.
Qed.

Lemma sim_Call x1 x2 (q1 : prog a) x3 x4 dest args h :
  sim q1 (Seq_assoc_right q1 Skip) ->
  match h with Some (_, (q2, _)) => sim q2 (Seq_assoc_right q2 Skip) | None => True end ->
  sim (Call (Some (x1, (x2, (q1, (x3, x4))))) dest args h)
      (Call (Some (x1, (x2, (Seq_assoc_right q1 Skip, (x3, x4))))) dest args
            (match h with
             | None => None
             | Some (y1, (q2, (y2, y3))) => Some (y1, (Seq_assoc_right q2 Skip, (y2, y3)))
             end)).
Proof.
  intros S1 S2 s res s1 [H Hr].
  destruct h as [[y1 [q2 [y2 y3]]]|];
    rewrite evaluate_eqn in H |- *; cbn [evaluate_body add_ret_loc] in H |- *;
    sim_split H; sim_close H Hr.
Qed.

Lemma Call_NONE_not_NONE dest args h s :
  fst (evaluate (@Call a NONE dest args h, s)) <> NONE.
Proof.
  rewrite evaluate_eqn; cbn [evaluate_body].
  repeat match goal with
         | |- context [match ?x with _ => _ end] =>
             let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
         end;
  cbn [fst bad_fun_return] in *; try congruence.
  all: match goal with o : option (result a) |- _ => destruct o as [[]|] end;
    cbn [bad_fun_return] in *; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "evaluate_Loop_body_eq" *)
Theorem evaluate_Loop_body_eq : forall names (p1 p2 : prog a) exit_names,
  (forall s res s1, evaluate (p1, s) = (res, s1) /\ res <> SOME Error ->
                    evaluate (p2, s) = (res, s1)) ->
  forall s res s1, evaluate (Loop names p1 exit_names, s) = (res, s1) /\ res <> SOME Error ->
                   evaluate (Loop names p2 exit_names, s) = (res, s1).
Proof.
  intros names p1 p2 exit_names Hs s.
  remember (N.to_nat (clock s)) as n eqn:Hn. revert s Hn.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros s Hn res s1 [H Hr].
  destruct (cut_state (names, LN) s) as [s'|] eqn:Ec.
  2:{ rewrite (evaluate_Loop_None _ p1 _ _ Ec) in H.
       rewrite (evaluate_Loop_None _ p2 _ _ Ec). exact H. }
  rewrite (evaluate_Loop_eq _ p1 _ _ _ Ec) in H. rewrite (evaluate_Loop_eq _ p2 _ _ _ Ec).
  destruct (evaluate (p1, s')) as [r t] eqn:E1.
  assert (Hr' : r <> SOME Error).
  { intros ->. cbn [cont_loop] in H. rewrite bd_false in H by discriminate.
    injection H as <- <-. apply Hr; reflexivity. }
  rewrite (Hs _ _ _ (conj E1 Hr')).
  destruct (cont_loop r); [|exact H].
  destruct (clock t =? 0) eqn:Ez; [exact H|].
  apply N.eqb_neq in Ez. unfold STOP in *.
  pose proof (evaluate_clock _ _ _ _ E1) as [Hc _].
  pose proof (cut_state_clock _ _ _ Ec) as [Hc' _].
  eapply (IHn (N.to_nat (clock (dec_clock t)))); [|reflexivity|split; [exact H|exact Hr]].
  unfold dec_clock; cbn [clock set_clock]. lia.
Qed.

Lemma IH_sim (q : prog a) :
  (forall p2 s res s1, evaluate (Seq q p2, s) = (res, s1) /\ res <> SOME Error ->
                       evaluate (Seq_assoc_right q p2, s) = (res, s1)) ->
  sim q (Seq_assoc_right q Skip).
Proof. intros IH s res s1 [H Hr]. apply IH. rewrite evaluate_Seq_Skip. split; assumption. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "evaluate_Seq_assoc_right_lemma" *)
Theorem evaluate_Seq_assoc_right_lemma : forall (p1 p2 : prog a) s res s1,
  evaluate (Seq p1 p2, s) = (res, s1) /\ res <> SOME Error ->
  evaluate (Seq_assoc_right p1 p2, s) = (res, s1).
Proof.
  intros p1; induction p1 as [ | | | | | | | q IHq | ret dest args h IHret IHh | q1 q2 IH1 IH2 | cmp r ri q1 q2 IH1 IH2 | n1 q n2 IHq | | | | | | | | | | | | | | ] using prog_nested_ind; intros acc st res s1 [H Hr];
    cbn [Seq_assoc_right];
    try solve [apply evaluate_SimpSeq; split; assumption].
  - (* Skip *) rewrite evaluate_Skip_Seq in H. exact H.
  - (* MustTerminate *)
    apply evaluate_SimpSeq; split; [|exact Hr].
    eapply sim_Seq; [apply sim_MustTerminate, IH_sim; assumption|exact H|exact Hr].
  - (* Call *)
    destruct ret as [[x1 [x2 [q1 [x3 x4]]]]|].
    + apply evaluate_SimpSeq; split; [|exact Hr].
      eapply sim_Seq; [|exact H|exact Hr].
      apply sim_Call; [apply IH_sim; assumption|].
      destruct h as [[y1 [q2 [y2 y3]]]|]; [apply IH_sim; assumption|exact Logic.I].
    + rewrite evaluate_not_NONE_Seq in H by apply Call_NONE_not_NONE. exact H.
  - (* Seq *)
    apply IH1. split; [|exact Hr].
    rewrite <- evaluate_Seq_assoc in H. rewrite evaluate_Seq_eq in H |- *.
    destruct (evaluate (q1, st)) as [r' t] eqn:E.
    destruct (bool_decide (r' = NONE)) eqn:En; [|exact H].
    apply IH2. split; assumption.
  - (* If *)
    apply evaluate_SimpSeq; split; [|exact Hr].
    eapply sim_Seq; [apply sim_If; apply IH_sim; assumption|exact H|exact Hr].
  - (* Loop *)
    apply evaluate_SimpSeq; split; [|exact Hr].
    eapply sim_Seq; [|exact H|exact Hr].
    intros s' r' t' Hrt. eapply evaluate_Loop_body_eq; [|exact Hrt].
    apply IH_sim; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "evaluate_remove_unreach" *)
Theorem evaluate_remove_unreach : forall (p : prog a) s res s1,
  evaluate (p, s) = (res, s1) /\ res <> SOME Error ->
  evaluate (remove_unreach p, s) = (res, s1).
Proof.
  intros p s res s1 [H Hr]. unfold remove_unreach. apply evaluate_Seq_assoc_right_lemma.
  rewrite evaluate_Seq_Skip. split; assumption.
Qed.

End AssocRight.
