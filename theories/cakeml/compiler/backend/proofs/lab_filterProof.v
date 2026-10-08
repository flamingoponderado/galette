(** * CakeML [lab_filterProof]: correctness of [lab_filter]

    Port of [cakeml/compiler/backend/proofs/lab_filterProofScript.sml].

    - [adjust_pc] (HOL: well-founded recursion on the sections, then on the
      lines of the first section) is a nested structural recursion; HOL's
      equation is the tagged [adjust_pc_def].
    - HOL's [s with f := v] is [set_<f> v s] ([labSem]).
    - The proof of [filter_correct] follows HOL's case analysis but is
      organised around a few Galette helpers (untagged): [loc_to_pc_filter]
      (combining HOL's [loc_to_pc_eq_NONE] and [loc_to_pc_eq_SOME]) and
      commutation lemmas of [asm_inst] and [share_mem_op] with the state
      updates.  HOL's [share_mem_op_*_filter_correct] are ported but not
      used by it.
    - [state_rel_IMP_sem_EQ_sem] goes through the untagged helper
      [semantics_sim] (equal semantics from a clock-extending simulation).
    - Not ported (HOL [local] lemmas superseded by the helpers):
      [is_Label_not_skip], [asm_fetch_not_skip_adjust_pc], [state_rw],
      [asm_fetch_aux_eq2], [all_skips_evaluate_rw], [all_skips_initial_adjust],
      [all_skips_get_lab_after]; the ML values [all_skips_evaluate_0],
      [same_inst_tac], [upd_pc_tac], [share_mem_load_filter_correct_tac],
      [share_mem_store_filter_correct_tac]. *)

From Galette Require Import Base Classical.
From Stdlib Require Import Setoid.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import labLang lab_filter.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend.semantics Require wordSem targetSem.
From Galette.cakeml.compiler.backend.semantics Require Import labSem labProps.
Import wordLang (word_loc, Word, Loc).
Import targetSem (machine_result(..)).
Open Scope N_scope.

Section Adjust.
Context {a : N}.
Implicit Types (l z : line a) (lines zs : list (line a)) (rest ys : list (sec a)).

(** HOL [adjust_pc]: nested structural recursion (sections, then lines). *)
Fixpoint adjust_pc (p : N) (xs : list (sec a)) {struct xs} : N :=
  if p =? 0 then 0 else
  match xs with
  | [] => p
  | Section_ n lines :: rest =>
      (fix go (p : N) (lines : list (line a)) {struct lines} : N :=
         if p =? 0 then 0 else
         match lines with
         | [] => adjust_pc p rest
         | l :: lines =>
             if is_Label l then go p lines
             else if not_skip l then go (p - 1) lines + 1
             else go (p - 1) lines
         end) p lines
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "adjust_pc_def" *)
Theorem adjust_pc_def : forall p xs,
  adjust_pc p xs =
    if p =? 0 then 0 else
      match xs with
      | [] => p
      | Section_ n [] :: rest => adjust_pc p rest
      | Section_ n (l :: lines) :: rest =>
          if is_Label l then
            adjust_pc p (Section_ n lines :: rest)
          else if not_skip l then
            adjust_pc (p - 1) (Section_ n lines :: rest) + 1
          else adjust_pc (p - 1) (Section_ n lines :: rest)
      end.
Proof.
  intros p [|[n [|l lines]] rest]; cbn [adjust_pc]; destruct (p =? 0) eqn:Ep; try reflexivity.
  destruct lines; cbn; rewrite Ep;
    destruct (is_Label l), (not_skip l); try reflexivity;
    destruct (p - 1 =? 0); reflexivity.
Qed.

Lemma adjust_pc_0 xs : adjust_pc 0 xs = 0.
Proof. destruct xs; reflexivity. Qed.

Lemma adjust_pc_nil_sec p n rest : adjust_pc p (Section_ n [] :: rest) = adjust_pc p rest.
Proof. rewrite adjust_pc_def. destruct (N.eqb_spec p 0); [subst; rewrite adjust_pc_0|]; reflexivity. Qed.

Lemma adjust_pc_label p n l lines rest :
  is_Label l = true ->
  adjust_pc p (Section_ n (l :: lines) :: rest) = adjust_pc p (Section_ n lines :: rest).
Proof.
  intros H. rewrite adjust_pc_def, H.
  destruct (N.eqb_spec p 0); [subst; rewrite adjust_pc_0|]; reflexivity.
Qed.

Lemma adjust_pc_nonlabel p n l lines rest :
  is_Label l = false -> p <> 0 ->
  adjust_pc p (Section_ n (l :: lines) :: rest) =
  adjust_pc (p - 1) (Section_ n lines :: rest) + (if not_skip l then 1 else 0).
Proof.
  intros H Hp. rewrite adjust_pc_def, H. rewrite (proj2 (N.eqb_neq p 0) Hp).
  destruct (not_skip l); lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "all_skips_def" *)
Definition all_skips (pc0 : N) (code0 : list (sec a)) (k : N) : Prop :=
  (forall x y, asm_fetch_aux (pc0 + k) code0 <> SOME (Asm (Asmi (Inst asm.Skip)) x y)) /\
  forall i, i < k ->
    exists x y,
    asm_fetch_aux (pc0 + i) code0 = SOME (Asm (Asmi (Inst asm.Skip)) x y).

Lemma fetch_label p n l lines rest :
  is_Label l = true ->
  asm_fetch_aux p (Section_ n (l :: lines) :: rest) = asm_fetch_aux p (Section_ n lines :: rest).
Proof. intros H. rewrite (proj2 (proj2 asm_fetch_aux_def)), H. reflexivity. Qed.

Lemma fetch_nonlabel p n l lines rest :
  is_Label l = false ->
  asm_fetch_aux p (Section_ n (l :: lines) :: rest) =
  if p =? 0 then SOME l else asm_fetch_aux (p - 1) (Section_ n lines :: rest).
Proof. intros H. rewrite (proj2 (proj2 asm_fetch_aux_def)), H. reflexivity. Qed.

Lemma fetch_nil_sec p n (rest : list (sec a)) :
  asm_fetch_aux p (Section_ n [] :: rest) = asm_fetch_aux p rest.
Proof. reflexivity. Qed.

Lemma not_skip_false l :
  not_skip l = false -> exists x y, l = Asm (Asmi (Inst asm.Skip)) x y.
Proof.
  destruct l as [| [a0| |] | ]; cbn; try discriminate.
  destruct a0 as [i| | | | |]; try discriminate. destruct i; try discriminate. eauto.
Qed.

Lemma label_not_skip l : is_Label l = true -> not_skip l = true.
Proof. destruct l; cbn; congruence. Qed.

Lemma skip_not_label l x y : l = Asm (Asmi (Inst asm.Skip)) x y -> is_Label l = false /\ not_skip l = false.
Proof. intros ->; split; reflexivity. Qed.

Lemma filter_skip_cons n l lines rest :
  filter_skip (Section_ n (l :: lines) :: rest) =
  if not_skip l then
    match filter_skip (Section_ n lines :: rest) with
    | Section_ n' ls :: r => Section_ n' (l :: ls) :: r
    | [] => []
    end
  else filter_skip (Section_ n lines :: rest).
Proof. cbn. destruct (not_skip l); reflexivity. Qed.

(** all_skips over the sub-list *)
Lemma all_skips_nil_sec p n rest k :
  all_skips p (Section_ n [] :: rest) k <-> all_skips p rest k.
Proof. reflexivity. Qed.

Lemma all_skips_label p n l lines rest k :
  is_Label l = true ->
  all_skips p (Section_ n (l :: lines) :: rest) k <-> all_skips p (Section_ n lines :: rest) k.
Proof.
  intros H. unfold all_skips. pose proof (fun p' => fetch_label p' n l lines rest H) as E.
  setoid_rewrite E. reflexivity.
Qed.

Lemma all_skips_nonlabel p n l lines rest k :
  is_Label l = false -> p <> 0 ->
  all_skips p (Section_ n (l :: lines) :: rest) k <-> all_skips (p - 1) (Section_ n lines :: rest) k.
Proof.
  intros H Hp. unfold all_skips.
  assert (E : forall i, asm_fetch_aux (p + i) (Section_ n (l :: lines) :: rest) =
                        asm_fetch_aux (p - 1 + i) (Section_ n lines :: rest)).
  { intros i. rewrite fetch_nonlabel by exact H.
    rewrite (proj2 (N.eqb_neq (p + i) 0)) by lia. f_equal. lia. }
  setoid_rewrite E. reflexivity.
Qed.

(** At pc 0, a skip line forces at least one skip. *)
Lemma all_skips_skip0 n l lines rest k :
  is_Label l = false -> not_skip l = false ->
  all_skips 0 (Section_ n (l :: lines) :: rest) k ->
  k <> 0 /\ all_skips 0 (Section_ n lines :: rest) (k - 1).
Proof.
  intros H Hs [A B]. destruct (not_skip_false l Hs) as (x & y & ->).
  assert (Hk : k <> 0).
  { intros ->. apply (A x y). rewrite fetch_nonlabel by exact H. reflexivity. }
  split; [exact Hk|]. split.
  - intros x' y'. specialize (A x' y'). rewrite fetch_nonlabel in A by exact H.
    rewrite (proj2 (N.eqb_neq (0 + k) 0)) in A by lia.
    replace (0 + k - 1) with (0 + (k - 1)) in A by lia. exact A.
  - intros i Hi. destruct (B (i + 1) ltac:(lia)) as (x' & y' & E).
    rewrite fetch_nonlabel in E by exact H.
    rewrite (proj2 (N.eqb_neq (0 + (i + 1)) 0)) in E by lia.
    replace (0 + (i + 1) - 1) with (0 + i) in E by lia. eauto.
Qed.

(** At pc 0, a real instruction allows no skips. *)
Lemma all_skips_inst0 n l lines rest k :
  is_Label l = false -> not_skip l = true ->
  all_skips 0 (Section_ n (l :: lines) :: rest) k -> k = 0.
Proof.
  intros H Hs [A B]. destruct (N.eqb_spec k 0) as [|Hk]; [assumption|].
  destruct (B 0 ltac:(lia)) as (x & y & E). rewrite fetch_nonlabel in E by exact H.
  cbn in E. injection E as ->. discriminate.
Qed.

(* 1) *)
(*! HOL "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "asm_fetch_aux_eq" *)
Theorem asm_fetch_aux_eq : forall pc0 code0,
  exists k,
    asm_fetch_aux (pc0 + k) code0 =
      asm_fetch_aux (adjust_pc pc0 code0) (filter_skip code0) /\
    all_skips pc0 code0 k.
Proof.
  intros pc0 code0; revert pc0.
  induction code0 as [|[n lines] rest IH]; intros pc0.
  { exists 0. rewrite adjust_pc_def. split.
    - destruct (pc0 =? 0); reflexivity.
    - split; [intros x y; discriminate|intros i Hi; lia]. }
  revert pc0; induction lines as [|l lines IHl]; intros pc0.
  { destruct (IH pc0) as (k & E & S). exists k. rewrite adjust_pc_nil_sec. split; [exact E|exact S]. }
  destruct (is_Label l) eqn:HL.
  { destruct (IHl pc0) as (k & E & S). exists k.
    rewrite fetch_label by exact HL. rewrite adjust_pc_label by exact HL.
    rewrite filter_skip_cons, (label_not_skip l HL).
    split; [|apply all_skips_label; assumption].
    rewrite E. destruct (filter_skip (Section_ n lines :: rest)) as [|[n' ls] r] eqn:F;
      [cbn in F; discriminate|].
    rewrite fetch_label by exact HL. reflexivity. }
  destruct (N.eqb_spec pc0 0) as [->|Hp].
  - destruct (not_skip l) eqn:HS.
    + exists 0. split.
      * rewrite adjust_pc_0, filter_skip_cons, HS.
        destruct (filter_skip (Section_ n lines :: rest)) as [|[n' ls] r] eqn:F;
          [cbn in F; discriminate|].
        rewrite !fetch_nonlabel by exact HL. reflexivity.
      * split; [|intros i Hi; lia]. intros x y. rewrite fetch_nonlabel by exact HL. cbn.
        intros E; injection E as El; subst l; discriminate HS.
    + destruct (IHl 0) as (k & E & S). exists (k + 1). split.
      * rewrite fetch_nonlabel by exact HL. rewrite (proj2 (N.eqb_neq (0 + (k + 1)) 0)) by lia.
        replace (0 + (k + 1) - 1) with (0 + k) by lia. rewrite E, !adjust_pc_0.
        rewrite filter_skip_cons, HS. reflexivity.
      * destruct S as [A B]. split.
        -- intros x y. rewrite fetch_nonlabel by exact HL.
           rewrite (proj2 (N.eqb_neq (0 + (k + 1)) 0)) by lia.
           replace (0 + (k + 1) - 1) with (0 + k) by lia. apply A.
        -- intros i Hi. rewrite fetch_nonlabel by exact HL.
           destruct (N.eqb_spec (0 + i) 0) as [Ei|Ei].
           ++ destruct (not_skip_false l HS) as (x & y & ->). eauto.
           ++ replace (0 + i - 1) with (0 + (i - 1)) by lia. apply B. lia.
  - destruct (IHl (pc0 - 1)) as (k & E & S). exists k. split.
    + rewrite fetch_nonlabel by exact HL. rewrite (proj2 (N.eqb_neq (pc0 + k) 0)) by lia.
      replace (pc0 + k - 1) with (pc0 - 1 + k) by lia. rewrite E.
      rewrite (adjust_pc_nonlabel _ _ _ _ _ HL Hp), filter_skip_cons.
      destruct (not_skip l) eqn:HS; [|rewrite N.add_0_r; reflexivity].
      destruct (filter_skip (Section_ n lines :: rest)) as [|[n' ls] r] eqn:F;
        [cbn in F; discriminate|].
      rewrite fetch_nonlabel by exact HL.
      rewrite (proj2 (N.eqb_neq _ 0)) by lia. f_equal. lia.
    + apply all_skips_nonlabel; assumption.
Qed.

Lemma filter_skip_cons' n l lines rest :
  filter_skip (Section_ n (l :: lines) :: rest) =
  Section_ n (if not_skip l then l :: FILTER not_skip lines else FILTER not_skip lines)
    :: filter_skip rest.
Proof. cbn. destruct (not_skip l); reflexivity. Qed.

Lemma loc_to_pc_cons n1 n2 k z zs ys :
  loc_to_pc n1 n2 (Section_ k (z :: zs) :: ys) =
  if andb (k =? n1) (n2 =? 0) then SOME 0 else
  if andb ⌜exists k, z = Label n1 n2 k⌝ (negb (n2 =? 0)) then SOME 0 else
  if is_Label z then loc_to_pc n1 n2 (Section_ k zs :: ys)
  else option_map (fun pos => pos + 1) (loc_to_pc n1 n2 (Section_ k zs :: ys)).
Proof.
  rewrite (proj2 loc_to_pc_def). destruct (andb _ _); [reflexivity|].
  destruct (andb ⌜_⌝ _); [reflexivity|]. destruct (is_Label z); [reflexivity|].
  destruct (loc_to_pc n1 n2 (Section_ k zs :: ys)); reflexivity.
Qed.

Lemma loc_to_pc_nil_sec n1 n2 k ys :
  loc_to_pc n1 n2 (Section_ k [] :: ys) =
  if andb (k =? n1) (n2 =? 0) then SOME 0 else loc_to_pc n1 n2 ys.
Proof. rewrite (proj2 loc_to_pc_def). reflexivity. Qed.

Lemma label_test_nonlabel n1 n2 z :
  is_Label z = false -> andb ⌜exists k, z = Label n1 n2 k⌝ (negb (n2 =? 0)) = false.
Proof.
  intros H. destruct (bool_decide_spec (exists k, z = Label n1 n2 k)) as [B _].
  destruct ⌜exists k, z = Label n1 n2 k⌝; [|reflexivity].
  destruct (B eq_refl) as [k ->]. discriminate.
Qed.

(** HOL's [loc_to_pc_eq_NONE] and [loc_to_pc_eq_SOME] as one equation
    (Galette helper). *)
Lemma loc_to_pc_filter n1 n2 (code0 : list (sec a)) :
  loc_to_pc n1 n2 (filter_skip code0) =
  option_map (fun p => adjust_pc p code0) (loc_to_pc n1 n2 code0).
Proof.
  induction code0 as [|[k lines] ys IH]; [reflexivity|].
  induction lines as [|z zs IHl].
  - cbn [filter_skip FILTER]. rewrite !loc_to_pc_nil_sec.
    destruct (andb _ _); [rewrite ?adjust_pc_0; reflexivity|].
    rewrite IH. destruct (loc_to_pc n1 n2 ys); cbn [option_map]; [rewrite adjust_pc_nil_sec|]; reflexivity.
  - rewrite filter_skip_cons'. cbn [filter_skip] in IHl.
    assert (Adj : is_Label z = false -> forall p,
              adjust_pc (p + 1) (Section_ k (z :: zs) :: ys) =
              adjust_pc p (Section_ k zs :: ys) + (if not_skip z then 1 else 0)).
    { intros HL p. rewrite adjust_pc_nonlabel by (exact HL || lia). rewrite N.add_sub. reflexivity. }
    rewrite (loc_to_pc_cons n1 n2 k z zs ys).
    destruct (not_skip z) eqn:HS.
    + rewrite (loc_to_pc_cons n1 n2 k z (FILTER not_skip zs) (filter_skip ys)), IHl.
      destruct (andb (k =? n1) (n2 =? 0)); [cbn [option_map]; rewrite ?adjust_pc_0; reflexivity|].
      destruct (andb ⌜exists k0, z = Label n1 n2 k0⌝ (negb (n2 =? 0)));
        [cbn [option_map]; rewrite ?adjust_pc_0; reflexivity|].
      destruct (is_Label z) eqn:HL.
      * destruct (loc_to_pc n1 n2 (Section_ k zs :: ys)); cbn [option_map]; [|reflexivity].
        rewrite adjust_pc_label by exact HL. reflexivity.
      * destruct (loc_to_pc n1 n2 (Section_ k zs :: ys)); cbn [option_map]; [|reflexivity].
        rewrite (Adj eq_refl), ?HS. reflexivity.
    + destruct (is_Label z) eqn:HL; [rewrite (label_not_skip z HL) in HS; discriminate|].
      rewrite IHl, (label_test_nonlabel n1 n2 z HL).
      destruct (andb (k =? n1) (n2 =? 0)) eqn:T1.
      * rewrite (proj2 loc_to_pc_def). destruct zs; rewrite T1; cbn [option_map]; rewrite ?adjust_pc_0;
          reflexivity.
      * destruct (loc_to_pc n1 n2 (Section_ k zs :: ys)); cbn [option_map]; [|reflexivity].
        rewrite (Adj eq_refl), ?HS, N.add_0_r. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "loc_to_pc_eq_NONE" *)
Theorem loc_to_pc_eq_NONE : forall n1 n2 (code0 : list (sec a)),
  loc_to_pc n1 n2 (filter_skip code0) = NONE ->
  loc_to_pc n1 n2 code0 = NONE.
Proof.
  intros n1 n2 code0. rewrite loc_to_pc_filter.
  destruct (loc_to_pc n1 n2 code0); [discriminate|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "loc_to_pc_eq_SOME" *)
Theorem loc_to_pc_eq_SOME : forall n1 n2 (code0 : list (sec a)) pc0,
  loc_to_pc n1 n2 (filter_skip code0) = SOME pc0 ->
  exists pc',
  loc_to_pc n1 n2 code0 = SOME pc' /\
  adjust_pc pc' code0 = pc0.
Proof.
  intros n1 n2 code0 pc0. rewrite loc_to_pc_filter.
  destruct (loc_to_pc n1 n2 code0) as [p|]; [|discriminate].
  intros E; injection E as <-. eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "next_label_filter_skip" *)
Theorem next_label_filter_skip : forall code0 : list (sec a),
  next_label code0 = next_label (filter_skip code0).
Proof.
  induction code0 as [|[k lines] ys IH]; [reflexivity|].
  induction lines as [|z zs IHl]; [exact IH|].
  rewrite filter_skip_cons'. cbn [filter_skip] in IHl.
  destruct z as [l1 l2 l3|z1 z2 z3|z1 z2 z3 z4]; [reflexivity| |];
    destruct (not_skip _); exact IHl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "get_lab_after_adjust" *)
Theorem get_lab_after_adjust : forall pc0 (code0 : list (sec a)) k,
  all_skips pc0 code0 k ->
  get_lab_after (pc0 + k) code0 = get_lab_after (adjust_pc pc0 code0) (filter_skip code0).
Proof.
  intros pc0 code0; revert pc0.
  induction code0 as [|[n lines] rest IH]; intros pc0 k S.
  { reflexivity. }
  revert pc0 k S; induction lines as [|l lines IHl]; intros pc0 k S.
  { rewrite adjust_pc_nil_sec. apply IH. exact S. }
  assert (GL : forall p, get_lab_after p (Section_ n (l :: lines) :: rest) =
                 if is_Label l then get_lab_after p (Section_ n lines :: rest)
                 else if p =? 0 then next_label (Section_ n lines :: rest)
                 else get_lab_after (p - 1) (Section_ n lines :: rest))
    by (intros; apply (proj2 (proj2 get_lab_after_def))).
  rewrite filter_skip_cons'. cbn [filter_skip] in IHl.
  destruct (is_Label l) eqn:HL.
  { rewrite GL, ?HL, (label_not_skip l HL), adjust_pc_label by exact HL.
    rewrite (proj2 (proj2 get_lab_after_def)), ?HL.
    apply IHl. apply all_skips_label in S; assumption. }
  destruct (N.eqb_spec pc0 0) as [->|Hp].
  - rewrite adjust_pc_0. destruct (not_skip l) eqn:HS.
    + pose proof (all_skips_inst0 _ _ _ _ _ HL HS S) as ->.
      rewrite GL, ?HL. cbn [N.add N.eqb].
      rewrite (proj2 (proj2 get_lab_after_def)), ?HL. cbn [N.eqb].
      rewrite (next_label_filter_skip (Section_ n lines :: rest)). reflexivity.
    + destruct (all_skips_skip0 _ _ _ _ _ HL HS S) as [Hk S'].
      rewrite GL, ?HL, (proj2 (N.eqb_neq (0 + k) 0)) by lia.
      replace (0 + k - 1) with (0 + (k - 1)) by lia.
      rewrite (IHl 0 (k - 1) S'), adjust_pc_0. reflexivity.
  - rewrite GL, ?HL, (proj2 (N.eqb_neq (pc0 + k) 0)) by lia.
    rewrite (adjust_pc_nonlabel _ _ _ _ _ HL Hp).
    apply all_skips_nonlabel in S; [|exact HL|exact Hp].
    replace (pc0 + k - 1) with (pc0 - 1 + k) by lia. rewrite (IHl _ _ S).
    destruct (not_skip l); [|rewrite N.add_0_r; reflexivity].
    rewrite (proj2 (proj2 get_lab_after_def)), ?HL.
    rewrite (proj2 (N.eqb_neq _ 0)) by lia. rewrite N.add_sub. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "loc_to_pc_adjust_pc_append" *)
Theorem loc_to_pc_adjust_pc_append : forall n1 n2 (code0 : list (sec a)) pc0 ls,
  loc_to_pc n1 n2 code0 = SOME pc0 ->
  adjust_pc pc0 code0 = adjust_pc pc0 (code0 ++ ls).
Proof.
  intros n1 n2 code0; induction code0 as [|[k lines] ys IH]; intros pc0 ls H; [discriminate|].
  revert pc0 H; induction lines as [|z zs IHl]; intros pc0 H.
  - rewrite loc_to_pc_nil_sec in H. cbn [app]. rewrite !adjust_pc_nil_sec.
    destruct (andb _ _); [injection H as <-; rewrite ?adjust_pc_0; reflexivity|].
    apply IH, H.
  - rewrite loc_to_pc_cons in H. cbn [app] in *.
    destruct (andb (k =? n1) (n2 =? 0)); [injection H as <-; rewrite ?adjust_pc_0; reflexivity|].
    destruct (andb ⌜_⌝ _); [injection H as <-; rewrite ?adjust_pc_0; reflexivity|].
    destruct (is_Label z) eqn:HL.
    + rewrite !adjust_pc_label by exact HL. apply IHl, H.
    + destruct (loc_to_pc n1 n2 (Section_ k zs :: ys)) as [p|] eqn:E; [|discriminate].
      injection H as <-.
      rewrite !adjust_pc_nonlabel by (exact HL || lia). rewrite N.add_sub, (IHl p eq_refl).
      reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "adjust_pc_all_skips" *)
Theorem adjust_pc_all_skips : forall k pc0 (code0 : list (sec a)),
  all_skips pc0 code0 k ->
  adjust_pc pc0 code0 + 1 = adjust_pc (pc0 + k + 1) code0.
Proof.
  intros k pc0 code0; revert pc0 k.
  induction code0 as [|[n lines] rest IH]; intros pc0 k S.
  { destruct S as [_ B]. destruct (N.eqb_spec k 0) as [->|Hk].
    - rewrite !adjust_pc_def. destruct (N.eqb_spec pc0 0); destruct (N.eqb_spec (pc0 + 0 + 1) 0);
        lia.
    - destruct (B 0 ltac:(lia)) as (x & y & E). discriminate. }
  revert pc0 k S; induction lines as [|l lines IHl]; intros pc0 k S.
  { rewrite !adjust_pc_nil_sec. apply IH, S. }
  destruct (is_Label l) eqn:HL.
  { rewrite !adjust_pc_label by exact HL. apply IHl. apply all_skips_label in S; assumption. }
  destruct (N.eqb_spec pc0 0) as [->|Hp].
  - rewrite adjust_pc_0. destruct (not_skip l) eqn:HS.
    + pose proof (all_skips_inst0 _ _ _ _ _ HL HS S) as ->.
      rewrite adjust_pc_nonlabel by (exact HL || lia). rewrite HS.
      replace (0 + 0 + 1 - 1) with 0 by lia. rewrite adjust_pc_0. reflexivity.
    + destruct (all_skips_skip0 _ _ _ _ _ HL HS S) as [Hk S'].
      rewrite adjust_pc_nonlabel by (exact HL || lia). rewrite HS, N.add_0_r.
      replace (0 + k + 1 - 1) with (0 + (k - 1) + 1) by lia.
      rewrite <- (IHl 0 (k - 1) S'), adjust_pc_0. reflexivity.
  - rewrite !adjust_pc_nonlabel by (exact HL || lia).
    apply all_skips_nonlabel in S; [|exact HL|exact Hp].
    rewrite <- N.add_assoc, (N.add_comm (if not_skip l then 1 else 0) 1), N.add_assoc.
    rewrite (IHl _ _ S). f_equal. f_equal. lia.
Qed.

End Adjust.

Lemma filter_skip_append {a : N} (xs ys : list (sec a)) :
  filter_skip (xs ++ ys) = filter_skip xs ++ filter_skip ys.
Proof. induction xs as [|[n l] xs IH]; cbn; [reflexivity|]. rewrite IH; reflexivity. Qed.

Section Sem.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s t : state a c ffi_t).

Ltac st_cbn :=
  cbn [regs fp_regs mem mem_domain shared_mem_domain pc be ffi io_regs cc_regs io_fp_regs
       cc_fp_regs code compile compile_oracle code_buffer clock failed ptr_reg len_reg
       ptr2_reg len2_reg link_reg
       set_regs set_fp_regs set_mem set_mem_domain set_shared_mem_domain set_pc set_be
       set_ffi set_io_regs set_cc_regs set_io_fp_regs set_cc_fp_regs set_code set_compile
       set_compile_oracle set_code_buffer set_clock set_failed set_ptr_reg set_len_reg
       set_ptr2_reg set_len2_reg set_link_reg
       upd_pc upd_reg upd_mem upd_fp_reg dec_clock inc_pc assert shift_seq fst snd
       filter_skip] in *.

Ltac split_goal :=
  match goal with
  | |- context [match ?x with _ => _ end] =>
      lazymatch x with
      | context [match _ with _ => _ end] => fail
      | _ => let E := fresh "E" in destruct x eqn:E
      end
  end.

Ltac unfold_ops :=
  unfold asm_inst, arith_upd, binop_upd, fp_upd, mem_op, mem_load, mem_store, mem_load32,
    mem_store32, mem_load_byte, mem_store_byte, addr, reg_imm, read_fp_reg in *.

Ltac comm_tac :=
  unfold_ops; st_cbn; repeat (split_goal; cbn beta iota zeta; st_cbn); reflexivity.

Lemma asm_inst_set_code i v s : asm_inst i (set_code v s) = set_code v (asm_inst i s).
Proof. destruct s; destruct i as [|? ?|[]|[] ? []|[]]; comm_tac. Qed.

Lemma asm_inst_set_pc i v s : asm_inst i (set_pc v s) = set_pc v (asm_inst i s).
Proof. destruct s; destruct i as [|? ?|[]|[] ? []|[]]; comm_tac. Qed.

Lemma asm_inst_set_compile i v s : asm_inst i (set_compile v s) = set_compile v (asm_inst i s).
Proof. destruct s; destruct i as [|? ?|[]|[] ? []|[]]; comm_tac. Qed.

Lemma asm_inst_set_compile_oracle i v s :
  asm_inst i (set_compile_oracle v s) = set_compile_oracle v (asm_inst i s).
Proof. destruct s; destruct i as [|? ?|[]|[] ? []|[]]; comm_tac. Qed.

Lemma asm_inst_frame i s :
  code (asm_inst i s) = code s /\ compile (asm_inst i s) = compile s /\
  compile_oracle (asm_inst i s) = compile_oracle s /\ pc (asm_inst i s) = pc s /\
  clock (asm_inst i s) = clock s.
Proof. destruct s; destruct i as [|? ?|[]|[] ? []|[]]; repeat split; comm_tac. Qed.

Ltac share_tac s m :=
  destruct s; destruct m; cbn [share_mem_op]; unfold share_mem_load, share_mem_store, addr;
  st_cbn; repeat (split_goal; cbn beta iota zeta; st_cbn); reflexivity.

Lemma share_mem_op_set_code m r ad v s :
  share_mem_op m r ad (set_code v s) =
  match share_mem_op m r ad s with SOME (res, s') => SOME (res, set_code v s') | NONE => NONE end.
Proof. share_tac s m. Qed.

Lemma share_mem_op_set_compile m r ad v s :
  share_mem_op m r ad (set_compile v s) =
  match share_mem_op m r ad s with SOME (res, s') => SOME (res, set_compile v s') | NONE => NONE end.
Proof. share_tac s m. Qed.

Lemma share_mem_op_set_compile_oracle m r ad v s :
  share_mem_op m r ad (set_compile_oracle v s) =
  match share_mem_op m r ad s with
  | SOME (res, s') => SOME (res, set_compile_oracle v s') | NONE => NONE end.
Proof. share_tac s m. Qed.

Lemma share_mem_op_set_pc m r ad v s :
  share_mem_op m r ad (set_pc v s) =
  match share_mem_op m r ad s with
  | SOME (FFI_return f l, s') => SOME (FFI_return f l, set_pc (v + 1) s')
  | SOME (FFI_final f, s') => SOME (FFI_final f, set_pc v s')
  | NONE => NONE
  end.
Proof. share_tac s m. Qed.

Lemma share_mem_op_return_frame m r ad s f l s' :
  share_mem_op m r ad s = SOME (FFI_return f l, s') ->
  code s' = code s /\ compile s' = compile s /\ compile_oracle s' = compile_oracle s /\
  pc s' = pc s + 1 /\ clock s' = clock s - 1 /\ failed s' = failed s.
Proof.
  destruct m; cbn [share_mem_op]; unfold share_mem_load, share_mem_store; intros H;
    repeat match type of H with
           | context [match ?z with _ => _ end] =>
               let E := fresh "E" in destruct z eqn:E; cbn beta iota zeta in H
           end; try discriminate; injection H as _ _ <-; st_cbn; repeat split.
Qed.

(* 2) all_skips allow swapping pc for clock *)
(*! HOL "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "all_skips_evaluate" *)
Theorem all_skips_evaluate : forall k s,
  all_skips (pc s) (code s) k /\ ~ failed s ->
  forall k',
  evaluate (set_clock (clock s + k' + k) s) =
  evaluate (set_clock (clock s + k') (set_pc (pc s + k) s)).
Proof.
  intros k; induction k as [|k IH] using N.peano_ind; intros s [S Hf] k'.
  { rewrite !N.add_0_r. destruct s; reflexivity. }
  destruct S as [A B].
  destruct (B 0 ltac:(lia)) as (x & y & F0). rewrite N.add_0_r in F0.
  rewrite evaluate_def. st_cbn.
  rewrite (proj2 (N.eqb_neq _ 0)) by lia.
  unfold asm_fetch. st_cbn. rewrite F0. cbn [asm_inst]. st_cbn.
  apply not_true_is_false in Hf. rewrite Hf.
  specialize (IH (set_pc (pc s + 1) s)). st_cbn.
  transitivity (evaluate (set_clock (clock s + k' + k) (set_pc (pc s + 1) s))).
  { f_equal. apply state_eq_intro; st_cbn; reflexivity || lia. }
  rewrite IH.
  - f_equal. apply state_eq_intro; st_cbn; reflexivity || lia.
  - split; [|st_cbn; rewrite Hf; discriminate]. split.
    + intros x' y'. replace (pc s + 1 + k) with (pc s + N.succ k) by lia. apply A.
    + intros i Hi. replace (pc s + 1 + i) with (pc s + (i + 1)) by lia. apply B. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "state_rel_def" *)
Definition state_rel (s1 t1 : state a c ffi_t) : Prop :=
  (exists s1compile,
     s1 = set_compile s1compile
            (set_compile_oracle (fun n => (fun '(a0, b) => (a0, filter_skip b)) (compile_oracle t1 n))
               (set_pc (adjust_pc (pc t1) (code t1))
                  (set_code (filter_skip (code t1)) t1))) /\
     compile t1 = (fun c0 p => s1compile c0 (filter_skip p))) /\
  ~ failed t1.

Lemma bd_some_none {A} (x : A) {d : Decision (SOME x = NONE)} : bool_decide (SOME x = NONE) = false.
Proof. unfold bool_decide; destruct (decide _); [discriminate|reflexivity]. Qed.

Lemma bd_none_none {A} {d : Decision (@NONE A = NONE)} : bool_decide (@NONE A = NONE) = true.
Proof. unfold bool_decide; destruct (decide _); [reflexivity|congruence]. Qed.

(** Rewriting (rather than [cbn]) keeps the kernel from unfolding
    [evaluate] when it re-checks the hypothesis. *)
Lemma option_map_SOME {A B} (f : A -> B) x : option_map f (SOME x) = SOME (f x).
Proof. reflexivity. Qed.

Lemma option_map_NONE {A B} (f : A -> B) : option_map f NONE = NONE.
Proof. reflexivity. Qed.

Ltac split_hyp H :=
  match type of H with
  | context [match ?x with _ => _ end] =>
      lazymatch x with
      | context [match _ with _ => _ end] => fail
      | filter_skip ?v => is_var v; destruct v as [|[? ?] ?]
      | context [option_map _ ?y] => let E := fresh "E" in destruct y eqn:E
      | _ => let E := fresh "E" in destruct x eqn:E
      end
  end.

Ltac norm_H H :=
  cbn beta iota zeta in H; st_cbn;
  rewrite ?asm_inst_set_compile, ?asm_inst_set_compile_oracle, ?asm_inst_set_pc,
    ?asm_inst_set_code, ?share_mem_op_set_compile, ?share_mem_op_set_compile_oracle,
    ?share_mem_op_set_pc, ?share_mem_op_set_code, ?loc_to_pc_filter in H;
  rewrite ?option_map_SOME, ?option_map_NONE in H; rewrite ?bd_some_none, ?bd_none_none in H;
  cbn beta iota zeta in H; st_cbn.

Ltac rw_eqs :=
  repeat (match goal with
          | E : ?x = _ |- context [?x] => progress rewrite E
          end; cbn beta iota zeta; st_cbn).

Ltac norm_goal :=
  cbn beta iota zeta; st_cbn;
  rewrite ?asm_inst_with_clock, ?asm_inst_set_pc, ?share_mem_op_set_clock, ?share_mem_op_set_pc;
  cbn beta iota zeta; st_cbn.

(** One step of the unfiltered run, symbolically in the extra clock (the
    run is the one taken by the filtered run in [H]). *)
Ltac step_goal Ec :=
  intros ?K; rewrite evaluate_def; st_cbn;
  rewrite (proj2 (N.eqb_neq _ 0)) by (apply N.eqb_neq in Ec; lia);
  unfold asm_fetch, get_pc_value, get_ret_Loc, reg_imm; st_cbn;
  repeat (norm_goal; rw_eqs; norm_goal;
          rewrite ?bd_some_none, ?bd_none_none; cbn beta iota zeta);
  first [ match goal with |- _ = evaluate (?R _) => unfold R; reflexivity end
        | match goal with |- _ = ?R _ => unfold R; reflexivity end ].

Lemma asm_inst_code i s : code (asm_inst i s) = code s.
Proof. apply asm_inst_frame. Qed.
Lemma asm_inst_compile i s : compile (asm_inst i s) = compile s.
Proof. apply asm_inst_frame. Qed.
Lemma asm_inst_compile_oracle i s : compile_oracle (asm_inst i s) = compile_oracle s.
Proof. apply asm_inst_frame. Qed.
Lemma asm_inst_pc i s : pc (asm_inst i s) = pc s.
Proof. apply asm_inst_frame. Qed.

Ltac frames :=
  rewrite ?asm_inst_code, ?asm_inst_compile, ?asm_inst_compile_oracle, ?asm_inst_pc,
    ?asm_inst_clock in *;
  repeat match goal with
         | E : share_mem_op _ _ _ _ = SOME (FFI_return _ _, ?s') |- _ =>
             lazymatch goal with
             | _ : code s' = _ |- _ => fail
             | _ => destruct (share_mem_op_return_frame _ _ _ _ _ _ _ E) as (? & ? & ? & ? & ? & ?)
             end
         end;
  repeat match goal with
         | F : ?p ?v = _ |- context [?p ?v] =>
             is_var v;
             lazymatch p with
             | code => idtac | compile => idtac | compile_oracle => idtac
             | pc => idtac | clock => idtac | failed => idtac
             end;
             progress rewrite F
         end.

Ltac field_tac S :=
  first [ reflexivity | assumption | lia
        | apply adjust_pc_all_skips; exact S
        | eapply loc_to_pc_adjust_pc_append; eassumption
        | rewrite filter_skip_append; reflexivity
        | apply functional_extensionality; intros; reflexivity ].

(*! HOL "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "filter_correct" *)
Theorem filter_correct : forall (s1 : state a c ffi_t) t1 res s2,
  evaluate s1 = (res, s2) /\ state_rel s1 t1 /\ ~ failed t1 ->
  exists k t2,
    evaluate (set_clock (clock s1 + k) t1) = (res, t2) /\
    ffi s2 = ffi t2.
Proof.
  intros s1; induction s1 as [s1 IH] using evaluate_clock_ind.
  intros t1 res s2 (H & ((s1c & -> & Hc) & Hf) & _).
  apply not_true_is_false in Hf.
  destruct (asm_fetch_aux_eq (pc t1) (code t1)) as (kk & E0 & S).
  assert (Hskip : forall K, evaluate (set_clock (clock t1 + (K + kk)) t1) =
                         evaluate (set_clock (clock t1 + K) (set_pc (pc t1 + kk) t1))).
  { intros K. rewrite N.add_assoc. apply all_skips_evaluate. split; [exact S|rewrite Hf; discriminate]. }
  rewrite evaluate_def in H. st_cbn.
  destruct (clock t1 =? 0) eqn:Ec.
  { injection H as <- <-. exists 0, (set_clock (clock t1 + 0) t1).
    rewrite evaluate_def. st_cbn. rewrite N.add_0_r, Ec. split; reflexivity. }
  unfold asm_fetch, get_pc_value, get_ret_Loc, reg_imm in H. st_cbn.
  rewrite <- E0 in H. clear E0.
  rewrite <- (get_lab_after_adjust _ _ _ S) in H.
  repeat (split_hyp H; norm_H H).
  all: first
    [ (* a final result *)
      injection H as <- <-;
      let RR := fresh "RR" in
      evar (RR : N -> machine_result * state a c ffi_t);
      let HY := fresh "HY" in
      assert (HY : forall K, evaluate (set_clock (clock t1 + K) (set_pc (pc t1 + kk) t1)) = RR K)
        by step_goal Ec;
      exists (0 + kk); eexists; rewrite Hskip, HY; unfold RR; split; [reflexivity|];
      repeat match goal with
             | E : share_mem_op _ _ _ _ = SOME (FFI_final _, _) |- _ =>
                 apply share_mem_op_final in E; subst
             end; st_cbn; reflexivity
    | (* a recursive call *)
      let YY := fresh "YY" in
      evar (YY : N -> state a c ffi_t);
      let HY := fresh "HY" in
      assert (HY : forall K, evaluate (set_clock (clock t1 + K) (set_pc (pc t1 + kk) t1)) =
                             evaluate (YY K))
        by step_goal Ec;
      apply N.eqb_neq in Ec;
      frames;
      match type of H with
      | evaluate ?s' = _ =>
          let k2 := fresh "k2" in let t2 := fresh "t2" in
          let Ek := fresh "Ek" in let Ef := fresh "Ef" in
          destruct (IH s' ltac:(st_cbn; frames; lia) (YY 0) res s2) as (k2 & t2 & Ek & Ef);
          [ split; [exact H|]; split;
            [ split; [exists s1c; split; [apply state_eq_intro; unfold YY; st_cbn; frames;
                                          field_tac S
                                         | unfold YY; st_cbn; frames; first [exact Hc | reflexivity]]
                     | unfold YY; st_cbn; frames; congruence]
            | unfold YY; st_cbn; frames; congruence ]
          | exists (k2 + kk), t2; rewrite Hskip, HY; split; [|exact Ef];
            rewrite <- Ek; f_equal; unfold YY; apply state_eq_intro; st_cbn; frames;
            reflexivity || lia ]
      end ].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "share_mem_op_NONE_filter_correct" *)
Theorem share_mem_op_NONE_filter_correct : forall (t1 : state a c ffi_t) k m r ad arb_compile
    arb_oracle,
  all_skips (pc t1) (code t1) k /\
  share_mem_op m r ad
    (set_compile_oracle arb_oracle (set_compile arb_compile
       (set_code (filter_skip (code t1)) (set_pc (adjust_pc (pc t1) (code t1)) t1)))) = NONE ->
  share_mem_op m r ad (set_pc (k + pc t1) t1) = NONE.
Proof.
  intros t1 k m r ad ac ao [_ H].
  rewrite share_mem_op_set_compile_oracle, share_mem_op_set_compile, share_mem_op_set_code,
    share_mem_op_set_pc in H.
  rewrite share_mem_op_set_pc.
  destruct (share_mem_op m r ad t1) as [[[f l|f] s']|]; [discriminate|discriminate|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "share_mem_op_FFI_return_filter_correct" *)
Theorem share_mem_op_FFI_return_filter_correct : forall (t1 : state a c ffi_t) k s1compile m r ad
    f l s,
  (all_skips (pc t1) (code t1) k /\ clock t1 <> 0 /\
   compile t1 = (fun c0 p => s1compile c0 (filter_skip p)) /\ ~ failed t1 /\
   share_mem_op m r ad
     (set_compile_oracle (fun n => (fun '(a0, b) => (a0, filter_skip b)) (compile_oracle t1 n))
        (set_compile s1compile
           (set_code (filter_skip (code t1)) (set_pc (adjust_pc (pc t1) (code t1)) t1)))) =
     SOME (FFI_return f l, s)) ->
  exists s2, forall k',
    share_mem_op m r ad (set_pc (k + pc t1) t1) = SOME (FFI_return f l, s2) /\
    state_rel s s2 /\ ~ failed s /\ ~ failed s2 /\
    share_mem_op m r ad (set_clock (k' + clock t1) (set_pc (k + pc t1) t1)) =
      SOME (FFI_return f l, set_clock (k' + clock s2) s2).
Proof.
  intros t1 k s1c m r ad f l s (S & Hc0 & Hc & Hf & H).
  apply not_true_is_false in Hf.
  rewrite share_mem_op_set_compile_oracle, share_mem_op_set_compile, share_mem_op_set_code,
    share_mem_op_set_pc in H.
  destruct (share_mem_op m r ad t1) as [[[f0 l0|f0] s0]|] eqn:E; try discriminate H.
  injection H as <- <- <-.
  destruct (share_mem_op_return_frame _ _ _ _ _ _ _ E) as (Ecd & Ecp & Eco & Epc & Eck & Efl).
  exists (set_pc (k + pc t1 + 1) s0). intros k'.
  rewrite share_mem_op_set_clock, share_mem_op_set_pc, E. st_cbn.
  repeat split.
  - exists s1c. split.
    + apply state_eq_intro; st_cbn; rewrite ?Ecd, ?Eco, ?Epc; try reflexivity.
      rewrite (adjust_pc_all_skips _ _ _ S). f_equal. lia.
    + st_cbn. rewrite Ecp. exact Hc.
  - st_cbn. rewrite Efl, Hf. discriminate.
  - st_cbn. rewrite Efl, Hf. discriminate.
  - st_cbn. rewrite Efl, Hf. discriminate.
  - f_equal. f_equal. apply state_eq_intro; st_cbn; reflexivity || lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "share_mem_op_FFI_final_filter_correct" *)
Theorem share_mem_op_FFI_final_filter_correct : forall (t1 : state a c ffi_t) k s1compile m r ad
    f s,
  (all_skips (pc t1) (code t1) k /\ clock t1 <> 0 /\
   compile t1 = (fun c0 p => s1compile c0 (filter_skip p)) /\ ~ failed t1 /\
   share_mem_op m r ad
     (set_compile_oracle (fun n => (fun '(a0, b) => (a0, filter_skip b)) (compile_oracle t1 n))
        (set_compile s1compile
           (set_code (filter_skip (code t1)) (set_pc (adjust_pc (pc t1) (code t1)) t1)))) =
     SOME (FFI_final f, s)) ->
  exists s2, share_mem_op m r ad (set_pc (k + pc t1) t1) = SOME (FFI_final f, s2) /\
    ffi s = ffi s2.
Proof.
  intros t1 k s1c m r ad f s (S & Hc0 & Hc & Hf & H).
  rewrite share_mem_op_set_compile_oracle, share_mem_op_set_compile, share_mem_op_set_code,
    share_mem_op_set_pc in H.
  destruct (share_mem_op m r ad t1) as [[[f0 l0|f0] s0]|] eqn:E; try discriminate H.
  injection H as <- <-.
  rewrite share_mem_op_set_pc, E. eexists; split; [reflexivity|].
  apply share_mem_op_final in E. subst. reflexivity.
Qed.

Lemma set_clock_set_clock k1 k2 (s : state a c ffi_t) : set_clock k1 (set_clock k2 s) = set_clock k1 s.
Proof. destruct s; reflexivity. Qed.

(** A run that does not time out is the result of every larger clock. *)
Lemma evaluate_clock_mono (t : state a c ffi_t) k1 k2 r t1' :
  evaluate (set_clock k1 t) = (r, t1') -> r <> TimeOut -> k1 <= k2 ->
  exists t2', evaluate (set_clock k2 t) = (r, t2') /\ ffi t2' = ffi t1'.
Proof.
  intros E Hr Hk. pose proof (evaluate_ADD_clock (set_clock k1 t) r t1' (k2 - k1) (conj E Hr)) as E2.
  cbn [clock set_clock] in E2. rewrite set_clock_set_clock in E2.
  replace (k1 + (k2 - k1)) with k2 in E2 by lia. eexists; split; [exact E2|reflexivity].
Qed.

Lemma io_events_mono (t : state a c ffi_t) k1 k2 :
  k1 <= k2 ->
  is_true (isPREFIX (io_events (ffi (SND (evaluate (set_clock k1 t)))))
                    (io_events (ffi (SND (evaluate (set_clock k2 t)))))).
Proof.
  intros Hk. pose proof (evaluate_add_clock_io_events_mono (k2 - k1) (set_clock k1 t)) as P.
  cbn [clock set_clock] in P. rewrite set_clock_set_clock in P.
  replace (k1 + (k2 - k1)) with k2 in P by lia. exact P.
Qed.

Lemma LNTH_fromList_prefix {A} `{EqDecision A} (l1 l2 : list A) n x :
  is_true (isPREFIX l1 l2) -> LNTH n (fromList l1) = SOME x -> LNTH n (fromList l2) = SOME x.
Proof.
  revert l2 n; induction l1 as [|h l1 IH]; intros [|h' l2] n Hp Hn; cbn [fromList isPREFIX] in *;
    unfold is_true in *; try discriminate; try (rewrite (proj1 LNTH_THM) in Hn; discriminate).
  apply andb_prop in Hp as [Hh Hp]. apply bool_decide_spec in Hh. subst h'.
  destruct n as [|n] using N.peano_ind.
  - rewrite (proj1 (proj2 LNTH_THM)) in *. exact Hn.
  - rewrite (proj2 (proj2 LNTH_THM)) in *. apply IH; assumption.
Qed.

Lemma io_chain (s : state a c ffi_t) :
  lprefix_chain (IMAGE (fun k => fromList (io_events (ffi (SND (evaluate (set_clock k s)))))) UNIV).
Proof.
  assert (E : IMAGE (fun k => fromList (io_events (ffi (SND (evaluate (set_clock k s)))))) UNIV =
              IMAGE fromList (IMAGE (fun k => io_events (ffi (SND (evaluate (set_clock k s))))) UNIV)).
  { apply functional_extensionality; intros y; apply propositional_extensionality.
    unfold IMAGE, UNIV. split.
    - intros (k & -> & _). eexists; split; [reflexivity|]. exists k. split; [reflexivity|exact Logic.I].
    - intros (l & -> & (k & -> & _)). exists k. split; [reflexivity|exact Logic.I]. }
  rewrite E. apply prefix_chain_lprefix_chain.
  intros l1 l2 [(k1 & -> & _) (k2 & -> & _)].
  destruct (N.le_ge_cases k1 k2); [left|right]; apply io_events_mono; assumption.
Qed.

(** Semantics are equal when every clocked run of [s] is matched by a run
    of [t] with more clock (Galette helper; the argument of HOL's
    [state_rel_IMP_sem_EQ_sem]). *)
Lemma semantics_sim (s t : state a c ffi_t) :
  (forall k r s', evaluate (set_clock k s) = (r, s') ->
     exists k' t', evaluate (set_clock (k + k') t) = (r, t') /\ ffi s' = ffi t') ->
  semantics s = semantics t.
Proof.
  intros FC. unfold semantics.
  assert (EE : (exists k, FST (evaluate (set_clock k s)) = Error) =
               (exists k, FST (evaluate (set_clock k t)) = Error)).
  { apply propositional_extensionality; split.
    - intros [k Hk]. destruct (evaluate (set_clock k s)) as [r s'] eqn:Ev. cbn in Hk; subst r.
      destruct (FC _ _ _ Ev) as (k' & t' & Et & _). exists (k + k'). rewrite Et. reflexivity.
    - intros [k Hk]. destruct (evaluate (set_clock k t)) as [r0 t0] eqn:Ev0. cbn in Hk. subst r0.
      exists k. destruct (evaluate (set_clock k s)) as [r s'] eqn:Ev.
      destruct (FC _ _ _ Ev) as (k' & t' & Et & _).
      destruct (evaluate_clock_mono t k (k + k') Error t0 Ev0 ltac:(discriminate) ltac:(lia))
        as (t2 & E2 & _).
      rewrite Et in E2. injection E2 as -> _. reflexivity. }
  rewrite EE. destruct (classical_dec _); [reflexivity|].
  assert (ET : (fun res => exists k t' outcome,
                  evaluate (set_clock k s) = (Halt outcome, t') /\
                  res = Terminate outcome (io_events (ffi t'))) =
               (fun res => exists k t' outcome,
                  evaluate (set_clock k t) = (Halt outcome, t') /\
                  res = Terminate outcome (io_events (ffi t')))).
  { apply functional_extensionality; intros res; apply propositional_extensionality; split.
    - intros (k & s' & o & Ev & ->). destruct (FC _ _ _ Ev) as (k' & t' & Et & Ef).
      exists (k + k'), t', o. rewrite Ef. split; [exact Et|reflexivity].
    - intros (k & t0 & o & Ev0 & ->). destruct (evaluate (set_clock k s)) as [r s'] eqn:Ev.
      destruct (FC _ _ _ Ev) as (k' & t' & Et & Ef).
      destruct (evaluate_clock_mono t k (k + k') (Halt o) t0 Ev0 ltac:(discriminate) ltac:(lia))
        as (t2 & E2 & Ef2).
      rewrite Et in E2. injection E2 as -> ->.
      exists k, s', o. rewrite Ef, Ef2. split; [exact Ev|reflexivity]. }
  rewrite ET. destruct (some _) as [b|]; [reflexivity|]. f_equal.
  set (L1 := IMAGE _ UNIV). set (L2 := IMAGE _ UNIV).
  assert (C1 : lprefix_chain L1) by apply io_chain.
  assert (C2 : lprefix_chain L2) by apply io_chain.
  assert (EQ : equiv_lprefix_chain L1 L2).
  { apply (equiv_lprefix_chain_thm L1 L2 (conj C1 C2)). unfold L1, L2, IMAGE, UNIV. split.
    - intros ll1 m x [(k & -> & _) Hx].
      destruct (evaluate (set_clock k s)) as [r s'] eqn:Ev.
      destruct (FC _ _ _ Ev) as (k' & t' & Et & Ef).
      eexists; split; [exists (k + k'); split; [reflexivity|exact Logic.I]|].
      rewrite Et. cbn [SND snd] in *. rewrite <- Ef. exact Hx.
    - intros ll2 m x [(k & -> & _) Hx].
      destruct (evaluate (set_clock k s)) as [r s'] eqn:Ev.
      destruct (FC _ _ _ Ev) as (k' & t' & Et & Ef).
      eexists; split; [exists k; split; [reflexivity|exact Logic.I]|].
      rewrite Ev. cbn [SND snd]. rewrite Ef.
      pose proof (io_events_mono t k (k + k') ltac:(lia)) as P. apply (LNTH_fromList_prefix _ _ m x P) in Hx.
      rewrite Et in Hx. exact Hx. }
  apply (unique_lprefix_lub L2). split.
  - apply (lprefix_lub_new_chain L1 L2). split; [exact C2|split; [exact EQ|]].
    apply build_lprefix_lub_thm, C1.
  - apply build_lprefix_lub_thm, C2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "state_rel_IMP_sem_EQ_sem" *)
Theorem state_rel_IMP_sem_EQ_sem : forall s t : state a c ffi_t,
  state_rel s t -> semantics s = semantics t.
Proof.
  intros s t [(s1c & -> & Hc) Hf]. apply semantics_sim. intros k r s' Ev.
  match type of Ev with
  | evaluate ?S = _ => assert (HR : state_rel S (set_clock k t))
  end.
  { split; [|exact Hf]. exists s1c. split; [apply state_eq_intro; reflexivity|exact Hc]. }
  destruct (filter_correct _ (set_clock k t) r s' (conj Ev (conj HR Hf))) as (k' & t' & Et & Ef).
  exists k', t'. split; [exact Et|exact Ef].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "filter_skip_semantics" *)
Theorem filter_skip_semantics : forall s t : state a c ffi_t,
  pc t = 0 /\ ~ failed t /\
  (exists scompile,
     s = set_compile scompile
           (set_compile_oracle ((fun '(a0, b) => (a0, filter_skip b)) ∘ compile_oracle t)
              (set_code (filter_skip (code t)) t)) /\
     compile t = (fun c0 p => scompile c0 (filter_skip p))) /\
  ~ failed t ->
  semantics s = semantics t.
Proof.
  intros s t (Hpc & Hf & (sc & -> & Hc) & _). apply state_rel_IMP_sem_EQ_sem.
  split; [|exact Hf]. exists sc. split; [|exact Hc].
  apply state_eq_intro; st_cbn; try reflexivity. rewrite Hpc, adjust_pc_0. reflexivity.
Qed.

End Sem.

Section EndsLabel.
Context {a : N}.

Lemma ends_label_FILTER (xs : list (line a)) :
  negb (NULL xs) && is_Label (LAST xs) = true ->
  negb (NULL (FILTER not_skip xs)) && is_Label (LAST (FILTER not_skip xs)) = true.
Proof.
  induction xs as [|x xs IH]; [discriminate|]. intros H.
  destruct xs as [|y ys].
  - change (is_Label x = true) in H. cbn [List.filter]. rewrite (label_not_skip x H). exact H.
  - change (negb (NULL (y :: ys)) && is_Label (LAST (y :: ys)) = true) in H.
    specialize (IH H).
    change (FILTER not_skip (x :: y :: ys)) with
      (if not_skip x then x :: FILTER not_skip (y :: ys) else FILTER not_skip (y :: ys)).
    destruct (FILTER not_skip (y :: ys)) as [|f fs]; [discriminate IH|].
    destruct (not_skip x); [|exact IH].
    change (negb (NULL (f :: fs)) && is_Label (LAST (f :: fs)) = true). exact IH.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "sec_ends_with_label_filter_skip" *)
Theorem sec_ends_with_label_filter_skip : forall code : list (sec a),
  EVERY sec_ends_with_label code ->
  EVERY sec_ends_with_label (filter_skip code).
Proof.
  unfold is_true. induction code as [|[n xs] code IH]; [reflexivity|].
  cbn [filter_skip EVERY]. intros H. apply andb_prop in H as [H1 H2].
  rewrite (IH H2), Bool.andb_true_r. apply ends_label_FILTER, H1.
Qed.

End EndsLabel.
