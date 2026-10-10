(** * stack_to_labProof: correctness of the stackLang -> labLang flattening pass

    Port of HOL4 [cakeml/compiler/backend/proofs/stack_to_labProofScript.sml].

    Status: PARTIAL port.  This file contains everything in the HOL script up
    to and including [flatten_semantics] (HOL line ~2990): the [code_installed]
    / [loc_to_pc] / [asm_fetch_aux] infrastructure, [state_rel], the per-case
    simulation proof [flatten_correct], [flatten_call_correct], [halt_assum]
    and [flatten_semantics], plus the early syntactic label lemmas
    ([stack_to_lab_lab_pres], [stack_to_lab_lab_pres_T],
    [prog_to_section_labels_ok], ...).

    NOT YET PORTED (everything from HOL line 3027 on): [make_init],
    [full_make_init], [full_make_init_buffer/_ffi/_compile],
    [memory_assumption], [state_rel_make_init], [stack_to_lab_compile_lab_pres],
    [good_code], [full_make_init_semantics], [stack_to_lab_compile_all_enc_ok],
    [IMP_init_store_ok], [IMP_init_state_ok], the get_code_labels /
    handler_labels lemmas and the no_shmemop / no_install lemmas.

    Mismatches with HOL:
    - [code_installed]: Prop-valued Fixpoint; the non-[Label] case of the
      [Section] branch is [True] as in HOL (structure kept).
    - [labels_ok] is a Prop conjunction; [labels_ok_labs_correct] uses
      [EVERY] of [⌜..⌝] instead of a bool predicate.
    - HOL's [result_view] datatype is renamed [result_view_ty] (the function
      keeps the name [result_view]).
    - [halt_assum (:'ffi # 'c) code] takes the two types as explicit
      arguments [halt_assum ffi_t c code].
    - [code_installed'_cons_non_label] is stated in the specialised
      [lines, 0] form used by HOL's proofs.
    - HOL's [Loc] overload is the wordLang constructor [Loc].
    - Omitted HOL [val] bindings (not stored theorems): [get_labels_def],
      [get_reg_value_def], [is_Label_def], [extract_labels_def],
      [extract_labels_append], [sextract_labels_def], [stack_asm_ok_def],
      [finish_tac], [s], [make_init_semantics].
*)

From Galette Require Import Base Classical.
From Stdlib Require Import Setoid.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.HOL.src.floating_point Require Import binary_ieee machine_ieee.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.semantics Require fpSem.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.encoders.asm Require asmSem.
From Galette.cakeml.compiler.backend Require Import backend_common labLang.
From Galette.cakeml.compiler.backend.semantics Require Import labSem labProps.
From Galette.cakeml.compiler.backend Require Import stack_to_lab.
From Galette.cakeml.compiler.backend Require Import stackLang.
From Galette.cakeml.compiler.backend Require wordLang stack_alloc stack_remove stack_names
  stack_rawcall data_to_word bvl_to_bvi.
From Galette.cakeml.compiler.backend.semantics Require wordSem targetSem backendProps.
From Galette.cakeml.compiler.backend.semantics Require Import stackSem stackProps.
From Galette.cakeml.compiler.backend.proofs Require stack_allocProof stack_removeProof
  stack_namesProof stack_rawcallProof.
From Galette.cakeml.compiler.backend.proofs Require lab_filterProof.
Import wordLang (word_loc, Word, Loc).
Import wordSem (buffer, buffer_flush, buffer_write, mem_load_byte_aux,
  mem_store_byte_aux, mem_load_32, mem_store_32, write_bytearray).
Open Scope N_scope.

(** ** Preliminaries *)

Lemma LENGTH_app {A} (l1 l2 : list A) : LENGTH (l1 ++ l2) = LENGTH l1 + LENGTH l2.
Proof. rewrite !LENGTH_length, length_app; lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "word_sh_word_shift" *)
Theorem word_sh_word_shift {a : N} : forall a0 (b : word a) c0 z,
  wordLang.word_sh a0 b c0 = SOME z -> c0 < dimindex a /\ z = asmSem.word_shift a0 b c0.
Proof.
  intros a0 b c0 z H. unfold wordLang.word_sh in H.
  destruct (negb (c0 =? 0) && (dimindex a <=? c0)) eqn:E; [discriminate|].
  apply Bool.andb_false_iff in E.
  split.
  - destruct E as [E|E].
    + apply Bool.negb_false_iff, N.eqb_eq in E; subst. pose proof (DIMINDEX_GT_0 a); lia.
    + apply N.leb_gt in E; exact E.
  - destruct a0; injection H as <-; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "assert_T" *)
Theorem assert_T {a : N} {c ffi_t : Type} : forall s : labSem.state a c ffi_t,
  labSem.assert true s = s.
Proof. intros []; reflexivity. Qed.

Section Fetch.
Context {a : N}.

Lemma afa_nil pos : asm_fetch_aux pos ([] : labLang.prog a) = NONE.
Proof. reflexivity. Qed.

Lemma afa_sec_nil pos k (code : labLang.prog a) : asm_fetch_aux pos (Section_ k [] :: code) = asm_fetch_aux pos code.
Proof. reflexivity. Qed.

Lemma afa_cons pos k (y : line a) ys (code : labLang.prog a) :
  asm_fetch_aux pos (Section_ k (y :: ys) :: code) =
  if is_Label y then asm_fetch_aux pos (Section_ k ys :: code)
  else if (pos =? 0)%N then SOME y
  else asm_fetch_aux (pos - 1) (Section_ k ys :: code).
Proof. reflexivity. Qed.

Lemma ltp_nil n1 n2 : loc_to_pc n1 n2 ([] : labLang.prog a) = NONE.
Proof. reflexivity. Qed.

Lemma ltp_cons n1 n2 k (xs : list (line a)) ys :
  loc_to_pc n1 n2 (Section_ k xs :: ys) =
  if andb (k =? n1) (n2 =? 0) then SOME 0 else
  match xs with
  | [] => loc_to_pc n1 n2 ys
  | z :: zs =>
      if andb ⌜exists k, z = Label n1 n2 k⌝ (negb (n2 =? 0)) then SOME 0 else
      if is_Label z then loc_to_pc n1 n2 (Section_ k zs :: ys)
      else
        match loc_to_pc n1 n2 (Section_ k zs :: ys) with
        | NONE => NONE
        | SOME pos => SOME (pos + 1)
        end
  end.
Proof. exact (proj2 loc_to_pc_def n1 n2 k xs ys). Qed.

Lemma lab_ex_eq (z : line a) n1 n2 :
  ⌜exists k, z = Label n1 n2 k⌝ =
  match z with Label l1 l2 _ => (l1 =? n1) && (l2 =? n2) | _ => false end.
Proof.
  destruct z as [l1 l2 k| |].
  - destruct (N.eqb_spec l1 n1), (N.eqb_spec l2 n2); subst; cbn.
    + apply bool_decide_spec. eauto.
    + destruct (bool_decide _) eqn:E; [|reflexivity].
      apply bool_decide_spec in E. destruct E as [? E]; injection E; congruence.
    + destruct (bool_decide _) eqn:E; [|reflexivity].
      apply bool_decide_spec in E. destruct E as [? E]; injection E; congruence.
    + destruct (bool_decide _) eqn:E; [|reflexivity].
      apply bool_decide_spec in E. destruct E as [? E]; injection E; congruence.
  - destruct (bool_decide _) eqn:E; [|reflexivity].
    apply bool_decide_spec in E. destruct E as [? E]; discriminate.
  - destruct (bool_decide _) eqn:E; [|reflexivity].
    apply bool_decide_spec in E. destruct E as [? E]; discriminate.
Qed.

Lemma isPREFIX_iff {A} `{EqDecision A} (l1 l2 : list A) :
  isPREFIX l1 l2 <-> exists l3, l2 = l1 ++ l3.
Proof.
  revert l2; induction l1 as [|x l1 IH]; intros l2; cbn.
  - split; [intros _; exists l2; reflexivity|intros _; reflexivity].
  - destruct l2 as [|y l2]; [split; [discriminate|intros [l3 E]; discriminate]|].
    unfold is_true; rewrite Bool.andb_true_iff, bool_decide_spec.
    change (isPREFIX l1 l2 = true) with (is_true (isPREFIX l1 l2)). rewrite IH.
    split.
    + intros [-> [l3 ->]]; exists l3; reflexivity.
    + intros [l3 E]; injection E as -> ->; eauto.
Qed.

End Fetch.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "asm_fetch_aux_no_label" *)
Theorem asm_fetch_aux_no_label {a : N} : forall l1 l2 x pc (code : labLang.prog a),
  asm_fetch_aux pc code = SOME (Label l1 l2 x) -> False.
Proof.
  intros l1 l2 x pc code; revert pc; induction code as [|[k lines] code IH]; intros pc H;
    [discriminate|].
  revert pc H; induction lines as [|y ys IHl]; intros pc H; [exact (IH pc H)|].
  rewrite afa_cons in H. destruct (is_Label y) eqn:Ey; [exact (IHl pc H)|].
  destruct (pc =? 0); [|exact (IHl _ H)].
  injection H as ->; discriminate.
Qed.

Section DestToLoc.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "dest_to_loc_def" *)
Definition dest_to_loc (regs : fmap N (word_loc a)) (dest : N + N) : N :=
  match dest with
  | inl p => p
  | inr r => match FAPPLY regs r with Loc loc _ => loc | _ => ARB end
  end.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "dest_to_loc'_def" *)
Definition dest_to_loc' (regs : N -> word_loc a) (dest : N + N) : N :=
  match dest with
  | inl p => p
  | inr r => match regs r with Loc loc _ => loc | _ => ARB end
  end.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "find_code_lookup" *)
Theorem find_code_lookup : forall dest regs (code : spt (prog a)) p,
  find_code dest regs code = SOME p ->
  lookup (dest_to_loc regs dest) code = SOME p /\
  (forall r, dest = inr r -> r IN FDOM regs).
Proof.
  intros [d|r] regs code p H; cbn in H |- *.
  - split; [exact H|intros r E; discriminate].
  - destruct (FLOOKUP regs r) as [[w|l n]|] eqn:E; try discriminate.
    destruct (n =? 0); [|discriminate].
    pose proof E as E'. rewrite FLOOKUP_DEF in E'.
    destruct (decide _) as [Hd|Hd]; [|discriminate]. injection E' as E'.
    split; [rewrite E'; exact H|].
    intros r' E2; injection E2 as <-; exact Hd.
Qed.

End DestToLoc.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "not_is_Label_compile_jump" *)
Theorem not_is_Label_compile_jump {a : N} : forall dest : N + N,
  is_Label (@compile_jump a dest) = false.
Proof. intros []; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "word_cmp_not_NONE" *)
Theorem word_cmp_not_NONE {a : N} : forall cmp (w1 w2 : word a),
  wordSem.word_cmp cmp (Word w1) (Word w2) <> NONE.
Proof. intros []; discriminate. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "word_cmp_negate_alt" *)
Theorem word_cmp_negate_alt {a : N} : forall cmp (w1 w2 : word a),
  asm.word_cmp (negate cmp) w1 w2 = negb (asm.word_cmp cmp w1 w2).
Proof. intros [] w1 w2; cbn; rewrite ?Bool.negb_involutive; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "word_cmp_negate" *)
Theorem word_cmp_negate {a : N} : forall cmp (w1 w2 : word_loc a),
  wordSem.word_cmp (negate cmp) w1 w2 = OPTION_MAP negb (wordSem.word_cmp cmp w1 w2).
Proof.
  intros [] [w1|l1 n1] [w2|l2 n2]; cbn; rewrite ?Bool.negb_involutive; try reflexivity;
    repeat (match goal with |- context [if ?b then _ else _] => destruct b end; cbn);
    reflexivity.
Qed.

(** ** [code_installed], [loc_to_pc] and [asm_fetch_aux] *)

Lemma append_Append {A} (l1 l2 : app_list A) : append (Append l1 l2) = append l1 ++ append l2.
Proof. exact (proj1 (append_thm l1 l2 [])). Qed.

Lemma append_List {A} (xs : list A) : append (List xs) = xs.
Proof. exact (proj1 (proj2 (append_thm Nil Nil xs))). Qed.

Section CodeInstalled.
Context {a : N}.

(** HOL's [case x of Label l1 l2 _ => ...] has no clause for the other
    lines (HOL: [ARB]); it is only reached when [is_Label x], and the other
    clauses are [True] here. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed_def" *)
Fixpoint code_installed (n : N) (xs : list (line a)) (code : labLang.prog a) : Prop :=
  match xs with
  | [] => True
  | x :: xs =>
      if is_Label x then
        (match x with Label l1 l2 _ => loc_to_pc l1 l2 code = SOME n | _ => True end) /\
        code_installed n xs code
      else
        asm_fetch_aux n code = SOME x /\ code_installed (n + 1) xs code
  end.

Lemma LENGTH_FILTER_cons_lab (x : line a) xs :
  is_Label x = true -> LENGTH (FILTER (negb ∘ is_Label) (x :: xs)) = LENGTH (FILTER (negb ∘ is_Label) xs).
Proof. intros E; cbn [List.filter]; rewrite E; reflexivity. Qed.

Lemma LENGTH_FILTER_cons_nonlab (x : line a) xs :
  is_Label x = false ->
  LENGTH (FILTER (negb ∘ is_Label) (x :: xs)) = LENGTH (FILTER (negb ∘ is_Label) xs) + 1.
Proof. intros E; cbn [List.filter]; rewrite E; cbn [negb LENGTH]; lia. Qed.

Lemma LENGTH_FILTER_app (xs ys : list (line a)) :
  LENGTH (FILTER (negb ∘ is_Label) (xs ++ ys)) =
  LENGTH (FILTER (negb ∘ is_Label) xs) + LENGTH (FILTER (negb ∘ is_Label) ys).
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  destruct (is_Label x) eqn:E; cbn [app].
  - rewrite !LENGTH_FILTER_cons_lab by exact E; exact IH.
  - rewrite !LENGTH_FILTER_cons_nonlab by exact E; rewrite IH; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed_append_imp" *)
Theorem code_installed_append_imp : forall (l1 : list (line a)) pc l2 code,
  code_installed pc (l1 ++ l2) code ->
  code_installed pc l1 code /\
  code_installed (pc + LENGTH (FILTER (negb ∘ is_Label) l1)) l2 code.
Proof.
  induction l1 as [|x l1 IH]; intros pc l2 code H; cbn [app] in H.
  - split; [exact Logic.I|]. cbn. rewrite N.add_0_r. exact H.
  - cbn [code_installed] in H |- *. destruct (is_Label x) eqn:E.
    + destruct H as [H1 H2]. apply IH in H2 as [H2 H3].
      rewrite LENGTH_FILTER_cons_lab by exact E. auto.
    + destruct H as [H1 H2]. apply IH in H2 as [H2 H3].
      rewrite LENGTH_FILTER_cons_nonlab by exact E.
      split; [auto|].
      replace (pc + (LENGTH (FILTER (negb ∘ is_Label) l1) + 1))
        with (pc + 1 + LENGTH (FILTER (negb ∘ is_Label) l1)) by lia. exact H3.
Qed.

(** Galette-only: the converse of [code_installed_append_imp]. *)
Lemma code_installed_append_intro (l1 : list (line a)) pc l2 code :
  code_installed pc l1 code ->
  code_installed (pc + LENGTH (FILTER (negb ∘ is_Label) l1)) l2 code ->
  code_installed pc (l1 ++ l2) code.
Proof.
  revert pc; induction l1 as [|x l1 IH]; intros pc H1 H2; cbn [app].
  - cbn in H2. rewrite N.add_0_r in H2. exact H2.
  - cbn [code_installed] in H1 |- *. destruct (is_Label x) eqn:E.
    + rewrite LENGTH_FILTER_cons_lab in H2 by exact E. destruct H1; auto.
    + rewrite LENGTH_FILTER_cons_nonlab in H2 by exact E. destruct H1 as [H1 H1'].
      split; [exact H1|]. apply IH; [exact H1'|].
      replace (pc + 1 + LENGTH (FILTER (negb ∘ is_Label) l1))
        with (pc + (LENGTH (FILTER (negb ∘ is_Label) l1) + 1)) by lia. exact H2.
Qed.

End CodeInstalled.

(** Splitting [code_installed] hypotheses on [append]ed line lists. *)
Ltac ci_norm_in H :=
  rewrite ?append_Append, ?append_List, <- ?app_assoc in H; cbn [app] in H.

Ltac ci_split :=
  repeat match goal with
  | H : code_installed _ (append _) _ |- _ => progress ci_norm_in H
  | H : code_installed _ (_ ++ _) _ |- _ =>
      let H1 := fresh "Hci" in let H2 := fresh "Hci" in
      apply code_installed_append_imp in H; destruct H as [H1 H2]
  | H : code_installed _ (_ :: _) _ |- _ =>
      let H1 := fresh "Hci" in let H2 := fresh "Hci" in
      cbn [code_installed is_Label] in H; rewrite ?not_is_Label_compile_jump in H; cbn beta iota in H;
      lazymatch type of H with _ /\ _ => destruct H as [H1 H2] end
  | H : code_installed _ [] _ |- _ => clear H
  | H : ?A /\ ?B |- _ =>
      lazymatch A with
      | context [code_installed] => destruct H
      | context [asm_fetch_aux] => destruct H
      | context [loc_to_pc] => destruct H
      end
  end.

Section CodeInstalled2.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed_get_labels_IMP" *)
Local Theorem code_installed_get_labels_IMP : forall c l1 l2 top (e : prog a) n q cs bs pc,
  code_installed pc (append (FST (flatten top e n q cs bs))) c /\
  (l1, l2) IN get_labels e ->
  exists v, loc_to_pc l1 l2 c = SOME v.
Proof.
  intros c l1 l2 top e. revert top.
  induction e as [ret dest h Hr Hh|p1 p2 IH1 IH2|c0 r ri p1 p2 IH1 IH2|p IH|p Hp]
    using prog_nested_ind; intros top n q cs bs pc [Hc Hl].
  - destruct ret as [[p1 [lr [k1 k2]]]|]; [|cbn in Hl; contradiction].
    specialize (Hr p1 _ eq_refl).
    cbn [flatten] in Hc. destruct (flatten false p1 n q cs bs) as [xs [nr1 m1]] eqn:E1.
    cbn [get_labels] in Hl. apply IN_INSERT in Hl.
    destruct h as [[p2 [h1 h2]]|].
    + specialize (Hh p2 _ eq_refl).
      destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:E2. cbn [FST fst] in Hc.
      ci_split.
      destruct Hl as [Hl|Hl]; [injection Hl as -> ->; eauto|].
      apply IN_UNION in Hl. destruct Hl as [Hl|Hl].
      * eapply (Hr false n q cs bs); split; [rewrite E1; cbn; eassumption|exact Hl].
      * apply IN_INSERT in Hl. destruct Hl as [Hl|Hl]; [injection Hl as -> ->; eauto|].
        eapply (Hh false n m1 cs bs); split; [rewrite E2; cbn; eassumption|exact Hl].
    + cbn [FST fst] in Hc. ci_split.
      destruct Hl as [Hl|Hl]; [injection Hl as -> ->; eauto|].
      apply IN_UNION in Hl. destruct Hl as [Hl|Hl]; [|contradiction].
      eapply (Hr false n q cs bs); split; [rewrite E1; cbn; eassumption|exact Hl].
  - cbn [flatten] in Hc. destruct (flatten false p1 n q cs bs) as [xs [nr1 m1]] eqn:E1.
    destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:E2.
    cbn [get_labels] in Hl. apply IN_UNION in Hl.
    destruct top; cbn [FST fst] in Hc; ci_split; destruct Hl as [Hl|Hl].
    + eapply (IH1 false n q cs bs); split; [rewrite E1; cbn; eassumption|exact Hl].
    + eapply (IH2 false n m1 cs bs); split; [rewrite E2; cbn; eassumption|exact Hl].
    + eapply (IH1 false n q cs bs); split; [rewrite E1; cbn; eassumption|exact Hl].
    + eapply (IH2 false n m1 cs bs); split; [rewrite E2; cbn; eassumption|exact Hl].
  - cbn [flatten] in Hc. destruct (flatten false p1 n q cs bs) as [xs [nr1 m1]] eqn:E1.
    destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:E2.
    cbn [get_labels] in Hl. apply IN_UNION in Hl.
    destruct (is_Skip p1) eqn:S1, (is_Skip p2) eqn:S2; cbn [andb] in Hc.
    + destruct p1; try discriminate; destruct p2; try discriminate.
      destruct Hl as [Hl|Hl]; contradiction.
    + destruct p1; try discriminate. destruct Hl as [Hl|Hl]; [contradiction|].
      cbn [FST fst] in Hc; ci_split.
      eapply (IH2 false n m1 cs bs); split; [rewrite E2; cbn; eassumption|exact Hl].
    + destruct p2; try discriminate. destruct Hl as [Hl|Hl]; [|contradiction].
      cbn [FST fst] in Hc; ci_split.
      eapply (IH1 false n q cs bs); split; [rewrite E1; cbn; eassumption|exact Hl].
    + destruct nr1; [|destruct nr2]; cbn [FST fst] in Hc; ci_split; destruct Hl as [Hl|Hl];
        first [ eapply (IH1 false n q cs bs); split; [rewrite E1; cbn; eassumption|exact Hl]
              | eapply (IH2 false n m1 cs bs); split; [rewrite E2; cbn; eassumption|exact Hl] ].
  - cbn [flatten] in Hc. destruct (flatten false p n (q + 2) (q :: cs) ((q + 1) :: bs)) as [xs [nr1 m1]] eqn:E1.
    cbn [get_labels] in Hl. cbn [FST fst] in Hc; ci_split.
    eapply (IH false n (q + 2) (q :: cs) ((q + 1) :: bs)); split; [rewrite E1; cbn; eassumption|exact Hl].
  - destruct p; try contradiction; cbn in Hl; contradiction.
Qed.

(** Appending code after: Galette helpers for the HOL lemmas below. *)
Lemma afa_append_gen (code2 : labLang.prog a) : forall code pc l,
  asm_fetch_aux pc code = SOME l -> asm_fetch_aux pc (code ++ code2) = SOME l.
Proof.
  induction code as [|[k lines] code IH]; intros pc l H; [discriminate|].
  revert pc H; induction lines as [|y ys IHl]; intros pc H; cbn [app].
  - rewrite afa_sec_nil in H |- *. exact (IH pc l H).
  - rewrite afa_cons in H |- *. destruct (is_Label y); [exact (IHl pc H)|].
    destruct (pc =? 0); [exact H|exact (IHl _ H)].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "asm_fetch_aux_SOME_append" *)
Local Theorem asm_fetch_aux_SOME_append : forall pc (code : labLang.prog a) l code2,
  asm_fetch_aux pc code = SOME l -> asm_fetch_aux pc (code ++ code2) = SOME l.
Proof. intros pc code l code2; apply afa_append_gen. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "asm_fetch_aux_SOME_isPREFIX" *)
Local Theorem asm_fetch_aux_SOME_isPREFIX : forall pc (code : labLang.prog a) l code2,
  asm_fetch_aux pc code = SOME l /\ isPREFIX code code2 ->
  asm_fetch_aux pc code2 = SOME l.
Proof.
  intros pc code l code2 [H Hp]. apply isPREFIX_iff in Hp. destruct Hp as [l3 ->].
  apply asm_fetch_aux_SOME_append, H.
Qed.

(** Galette: a non-local name for [asm_fetch_aux_SOME_isPREFIX]. *)
Lemma afa_isPREFIX pc (code : labLang.prog a) l code2 :
  asm_fetch_aux pc code = SOME l /\ isPREFIX code code2 -> asm_fetch_aux pc code2 = SOME l.
Proof. apply asm_fetch_aux_SOME_isPREFIX. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "loc_to_pc_APPEND" *)
Theorem loc_to_pc_APPEND : forall n m (code : labLang.prog a) pc code2,
  loc_to_pc n m code = SOME pc -> loc_to_pc n m (code ++ code2) = SOME pc.
Proof.
  intros n m code; induction code as [|[k lines] code IH]; intros pc code2 H; [discriminate|].
  revert pc H; induction lines as [|y ys IHl]; intros pc H; cbn [app].
  - rewrite ltp_cons in H |- *. destruct (andb _ _); [exact H|exact (IH _ _ H)].
  - rewrite ltp_cons in H |- *. destruct (andb (k =? n) (m =? 0)); [exact H|].
    destruct (andb _ _); [exact H|].
    destruct (is_Label y); [exact (IHl _ H)|].
    destruct (loc_to_pc n m (Section_ k ys :: code)) as [p|] eqn:E; [|discriminate].
    specialize (IHl p eq_refl). cbn [app] in IHl. rewrite IHl. exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed_APPEND" *)
Theorem code_installed_APPEND : forall (ls : list (line a)) pc code code2,
  code_installed pc ls code -> code_installed pc ls (code ++ code2).
Proof.
  induction ls as [|x ls IH]; intros pc code code2 H; [exact Logic.I|].
  cbn [code_installed] in H |- *. destruct (is_Label x).
  - destruct H as [H1 H2]. split; [|exact (IH _ _ _ H2)].
    destruct x; try exact Logic.I. apply loc_to_pc_APPEND, H1.
  - destruct H as [H1 H2]. split; [apply asm_fetch_aux_SOME_append, H1|exact (IH _ _ _ H2)].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed_isPREFIX" *)
Theorem code_installed_isPREFIX : forall (ls : list (line a)) pc code code2,
  code_installed pc ls code /\ isPREFIX code code2 -> code_installed pc ls code2.
Proof.
  intros ls pc code code2 [H Hp]. apply isPREFIX_iff in Hp. destruct Hp as [l3 ->].
  apply code_installed_APPEND, H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "loc_to_pc_isPREFIX" *)
Theorem loc_to_pc_isPREFIX : forall n m (code : labLang.prog a) pc code2,
  loc_to_pc n m code = SOME pc /\ isPREFIX code code2 -> loc_to_pc n m code2 = SOME pc.
Proof.
  intros n m code pc code2 [H Hp]. apply isPREFIX_iff in Hp. destruct Hp as [l3 ->].
  apply loc_to_pc_APPEND, H.
Qed.

End CodeInstalled2.

Section Sections.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "MAP_prog_to_section_FST" 228 *)
Local Theorem MAP_prog_to_section_FST : forall prog : list (N * stackLang.prog a),
  MAP (fun s => match s with Section_ n v => n end) (MAP prog_to_section prog) = MAP FST prog.
Proof.
  induction prog as [|[n p] prog IH]; [reflexivity|]. cbn [List.map].
  f_equal; try exact IH. unfold prog_to_section.
  destruct (flatten true p n (stack_alloc.next_lab p 2) [] []) as [xs [nr m]]; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "MAP_prog_to_section_Section_num" *)
Theorem MAP_prog_to_section_Section_num : forall prog : list (N * stackLang.prog a),
  MAP Section_num (MAP prog_to_section prog) = MAP FST prog.
Proof.
  intros prog; rewrite <- (MAP_prog_to_section_FST prog). apply map_ext. intros []; reflexivity.
Qed.

Lemma LENGTH_FLAT_sec_cons k (y : line a) ys code :
  LENGTH (FLAT (MAP (FILTER (negb ∘ is_Label) ∘ Section_lines) (Section_ k (y :: ys) :: code))) =
  (if is_Label y then 0 else 1) +
  LENGTH (FLAT (MAP (FILTER (negb ∘ is_Label) ∘ Section_lines) (Section_ k ys :: code))).
Proof.
  cbn [List.map Section_lines List.concat]. rewrite !LENGTH_app.
  destruct (is_Label y) eqn:E.
  - rewrite LENGTH_FILTER_cons_lab by exact E. lia.
  - rewrite LENGTH_FILTER_cons_nonlab by exact E. lia.
Qed.

Lemma LENGTH_FLAT_sec_nil k (code : labLang.prog a) :
  LENGTH (FLAT (MAP (FILTER (negb ∘ is_Label) ∘ Section_lines) (Section_ k [] :: code))) =
  LENGTH (FLAT (MAP (FILTER (negb ∘ is_Label) ∘ Section_lines) code)).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "asm_fetch_aux_SOME_append2" *)
Theorem asm_fetch_aux_SOME_append2 : forall pc (code : labLang.prog a) l code2,
  asm_fetch_aux pc code2 = SOME l ->
  asm_fetch_aux
    (LENGTH (FLAT (MAP (FILTER (negb ∘ is_Label) ∘ Section_lines) code)) + pc)
    (code ++ code2) = SOME l.
Proof.
  intros pc code; induction code as [|[k lines] code IH]; intros l code2 H; [exact H|].
  induction lines as [|y ys IHl]; cbn [app].
  - rewrite LENGTH_FLAT_sec_nil, afa_sec_nil. exact (IH l code2 H).
  - rewrite LENGTH_FLAT_sec_cons, afa_cons. destruct (is_Label y).
    + rewrite N.add_0_l. exact IHl.
    + replace ((1 + LENGTH (FLAT (MAP (FILTER (negb ∘ is_Label) ∘ Section_lines)
                  (Section_ k ys :: code))) + pc =? 0)) with false by (symmetry; apply N.eqb_neq; lia).
      replace (1 + LENGTH (FLAT (MAP (FILTER (negb ∘ is_Label) ∘ Section_lines)
                  (Section_ k ys :: code))) + pc - 1)
        with (LENGTH (FLAT (MAP (FILTER (negb ∘ is_Label) ∘ Section_lines)
                  (Section_ k ys :: code))) + pc) by lia.
      exact IHl.
Qed.

Lemma sec_label_ok_neq (k n : N) (y : line a) n2 :
  sec_label_ok n y = true -> n <> k -> ⌜exists k', y = Label k n2 k'⌝ = false.
Proof.
  intros Hy Hn. rewrite lab_ex_eq. destruct y as [l1 l2 kk| |]; [|reflexivity|reflexivity].
  cbn in Hy. apply Bool.andb_true_iff in Hy as [Hy _]. apply N.eqb_eq in Hy; subst.
  apply N.eqb_neq in Hn. rewrite Hn. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "loc_to_pc_append2" *)
Theorem loc_to_pc_append2 : forall k ll (code : labLang.prog a) code2 pc,
  ~ MEM k (MAP Section_num code) /\
  EVERY sec_labels_ok code /\
  loc_to_pc k ll code2 = SOME pc ->
  loc_to_pc k ll (code ++ code2) =
    SOME (pc + LENGTH (FLAT (MAP (FILTER (negb ∘ is_Label) ∘ Section_lines) code))).
Proof.
  intros k ll code; induction code as [|[n lines] code IH]; intros code2 pc (Hm & Hok & H).
  - cbn. rewrite N.add_0_r. exact H.
  - cbn [List.map Section_num MEM] in Hm. unfold is_true in Hm.
    rewrite Bool.orb_true_iff, bool_decide_spec in Hm.
    assert (Hnk : n <> k) by (intros ->; apply Hm; left; reflexivity).
    assert (Hm' : ~ MEM k (MAP Section_num code)) by (intros E; apply Hm; right; exact E).
    cbn [EVERY sec_labels_ok] in Hok. apply Bool.andb_true_iff in Hok as [Hl Hok].
    induction lines as [|y ys IHl]; cbn [app].
    + rewrite ltp_cons, LENGTH_FLAT_sec_nil.
      replace (andb (n =? k) (ll =? 0)) with false
        by (symmetry; apply Bool.andb_false_iff; left; apply N.eqb_neq; exact Hnk).
      exact (IH code2 pc (conj Hm' (conj Hok H))).
    + cbn [EVERY] in Hl. apply Bool.andb_true_iff in Hl as [Hy Hl].
      rewrite ltp_cons, LENGTH_FLAT_sec_cons.
      replace (andb (n =? k) (ll =? 0)) with false
        by (symmetry; apply Bool.andb_false_iff; left; apply N.eqb_neq; exact Hnk).
      rewrite (sec_label_ok_neq k n y ll Hy Hnk). cbn [andb].
      specialize (IHl Hl). cbn [app] in IHl.
      destruct (is_Label y); [rewrite N.add_0_l; exact IHl|].
      rewrite IHl. f_equal. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed_append2" *)
Theorem code_installed_append2 : forall (lines : list (line a)) pc c1 c2 k,
  ~ MEM k (MAP Section_num c1) /\
  EVERY sec_labels_ok c1 /\
  EVERY (sec_label_ok k) lines /\
  code_installed pc lines c2 ->
  code_installed
    (LENGTH (FLAT (MAP (FILTER (negb ∘ is_Label) ∘ Section_lines) c1)) + pc)
    lines (c1 ++ c2).
Proof.
  induction lines as [|x lines IH]; intros pc c1 c2 k (Hm & Hok & Hl & H); [exact Logic.I|].
  cbn [EVERY] in Hl. apply Bool.andb_true_iff in Hl as [Hx Hl].
  cbn [code_installed] in H |- *. destruct (is_Label x) eqn:Ex.
  - destruct H as [H1 H2]. split; [|exact (IH pc c1 c2 k (conj Hm (conj Hok (conj Hl H2))))].
    destruct x as [l1 l2 kk| |]; try discriminate.
    cbn in Hx. apply Bool.andb_true_iff in Hx as [Hx _]. apply N.eqb_eq in Hx; subst l1.
    rewrite (loc_to_pc_append2 k l2 c1 c2 pc (conj Hm (conj Hok H1))). f_equal. lia.
  - destruct H as [H1 H2]. split.
    + exact (asm_fetch_aux_SOME_append2 pc c1 x c2 H1).
    + rewrite <- N.add_assoc. exact (IH (pc + 1) c1 c2 k (conj Hm (conj Hok (conj Hl H2)))).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "ALOOKUP_PARTITION" *)
Theorem ALOOKUP_PARTITION {A B} `{EqDecision A} : forall (ls : list (A * B)) n v,
  ALOOKUP ls n = SOME v ->
  exists ls1 ls2, ls = ls1 ++ [(n, v)] ++ ls2 /\ ~ MEM n (MAP FST ls1).
Proof.
  induction ls as [|[q r] ls IH]; intros n v Hl; [discriminate|].
  cbn in Hl. destruct (decide (q = n)) as [->|Hne].
  - injection Hl as ->. exists [], ls. split; [reflexivity|discriminate].
  - destruct (IH n v Hl) as (ls1 & ls2 & -> & Hm). exists ((q, r) :: ls1), ls2.
    split; [reflexivity|]. cbn [List.map FST fst MEM]. unfold is_true.
    rewrite Bool.orb_true_iff, bool_decide_spec. intros [E|E]; [congruence|exact (Hm E)].
Qed.

End Sections.

Section CodeInstalledPrime.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed'_def" *)
Fixpoint code_installed' (n : N) (xs : list (line a)) (code : labLang.prog a) : Prop :=
  match xs with
  | [] => True
  | x :: xs =>
      if is_Label x then code_installed' n xs code
      else asm_fetch_aux n code = SOME x /\ code_installed' (n + 1) xs code
  end.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed'_cons_label" *)
Theorem code_installed'_cons_label : forall (h : line a) n xs other lines pos,
  is_Label h ->
  code_installed' pos lines (Section_ n (h :: xs) :: other) <->
  code_installed' pos lines (Section_ n xs :: other).
Proof.
  intros h n xs other lines; induction lines as [|y lines IH]; intros pos Hh; [tauto|].
  cbn [code_installed']. destruct (is_Label y); [apply IH, Hh|].
  rewrite afa_cons, Hh, IH by exact Hh. tauto.
Qed.

Lemma code_installed'_cons_non_label_gen (h : line a) n xs other : forall lines pos,
  ~ is_Label h ->
  code_installed' (pos + 1) lines (Section_ n (h :: xs) :: other) <->
  code_installed' pos lines (Section_ n xs :: other).
Proof.
  intros lines; induction lines as [|y lines IH]; intros pos Hh; [tauto|].
  cbn [code_installed']. destruct (is_Label y); [apply IH, Hh|].
  rewrite afa_cons. apply Bool.not_true_iff_false in Hh. rewrite Hh.
  replace (pos + 1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
  replace (pos + 1 - 1) with pos by lia.
  rewrite <- (IH (pos + 1)) by (rewrite Hh; discriminate). tauto.
Qed.

(** HOL states this lemma for [lines] and [0] ([Q.SPECL [`lines`,`0`]]). *)
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed'_cons_non_label" *)
Theorem code_installed'_cons_non_label : forall (h : line a) n xs other lines,
  ~ is_Label h ->
  code_installed' 1 lines (Section_ n (h :: xs) :: other) <->
  code_installed' 0 lines (Section_ n xs :: other).
Proof. intros h n xs other lines Hh. exact (code_installed'_cons_non_label_gen h n xs other lines 0 Hh). Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed'_simp" *)
Theorem code_installed'_simp : forall n (rest : list (line a)) other lines,
  code_installed' 0 lines (Section_ n (lines ++ rest) :: other).
Proof.
  intros n rest other lines; induction lines as [|h lines IH]; [exact Logic.I|].
  cbn [code_installed' app]. destruct (is_Label h) eqn:E.
  - apply code_installed'_cons_label; [rewrite E; reflexivity|exact IH].
  - split; [rewrite afa_cons, E; reflexivity|].
    apply code_installed'_cons_non_label; [rewrite E; discriminate|exact IH].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "loc_to_pc_skip_section" *)
Theorem loc_to_pc_skip_section : forall n p (xs : labLang.prog a) lines,
  n <> p ->
  loc_to_pc n 0 (Section_ p lines :: xs) =
  match loc_to_pc n 0 xs with
  | NONE => NONE
  | SOME k => SOME (k + LENGTH (FILTER (fun x => negb (is_Label x)) lines))
  end.
Proof.
  intros n p xs lines Hnp; induction lines as [|y lines IH].
  - rewrite ltp_cons.
    replace (andb (p =? n) (0 =? 0)) with false
      by (symmetry; apply Bool.andb_false_iff; left; apply N.eqb_neq; congruence).
    destruct (loc_to_pc n 0 xs); [cbn; rewrite N.add_0_r|]; reflexivity.
  - rewrite ltp_cons.
    replace (andb (p =? n) (0 =? 0)) with false
      by (symmetry; apply Bool.andb_false_iff; left; apply N.eqb_neq; congruence).
    rewrite Bool.andb_false_r. rewrite IH. cbn [List.filter].
    destruct (is_Label y); cbn [negb LENGTH];
      destruct (loc_to_pc n 0 xs); try reflexivity; f_equal; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "asm_fetch_aux_add" *)
Theorem asm_fetch_aux_add : forall (ys : list (line a)) pc pos rest,
  asm_fetch_aux (pc + LENGTH (FILTER (fun x => negb (is_Label x)) ys)) (Section_ pos ys :: rest) =
  asm_fetch_aux pc rest.
Proof.
  induction ys as [|y ys IH]; intros pc pos rest.
  - cbn [List.filter LENGTH]. rewrite N.add_0_r, afa_sec_nil. reflexivity.
  - rewrite afa_cons. cbn [List.filter]. destruct (is_Label y); cbn [negb LENGTH]; [apply IH|].
    replace (pc + SUC (LENGTH (FILTER (fun x => negb (is_Label x)) ys)) =? 0) with false
      by (symmetry; apply N.eqb_neq; lia).
    replace (pc + SUC (LENGTH (FILTER (fun x => negb (is_Label x)) ys)) - 1)
      with (pc + LENGTH (FILTER (fun x => negb (is_Label x)) ys)) by lia.
    apply IH.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "labs_correct_def" *)
Fixpoint labs_correct (n : N) (xs : list (line a)) (code : labLang.prog a) : Prop :=
  match xs with
  | [] => True
  | x :: xs =>
      if is_Label x then
        labs_correct n xs code /\
        match x with Label l1 l2 v2 => loc_to_pc l1 l2 code = SOME n | _ => True end
      else labs_correct (n + 1) xs code
  end.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed_eq" *)
Theorem code_installed_eq : forall pc (xs : list (line a)) code,
  code_installed pc xs code <-> code_installed' pc xs code /\ labs_correct pc xs code.
Proof.
  intros pc xs; revert pc; induction xs as [|x xs IH]; intros pc code; cbn; [tauto|].
  destruct (is_Label x); rewrite IH; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed_cons" *)
Theorem code_installed_cons : forall (rest : labLang.prog a) xs ys pos pc,
  code_installed' pc xs rest ->
  code_installed' (pc + LENGTH (FILTER (fun x => negb (is_Label x)) ys)) xs (Section_ pos ys :: rest).
Proof.
  intros rest xs; induction xs as [|x xs IH]; intros ys pos pc H; [exact Logic.I|].
  cbn [code_installed'] in H |- *. destruct (is_Label x); [apply IH, H|].
  destruct H as [H1 H2]. split; [rewrite asm_fetch_aux_add; exact H1|].
  replace (pc + LENGTH (FILTER (fun x => negb (is_Label x)) ys) + 1)
    with (pc + 1 + LENGTH (FILTER (fun x => negb (is_Label x)) ys)) by lia.
  apply IH, H2.
Qed.

End CodeInstalledPrime.

Section LabelsOk.
Context {a : N}.

Lemma ltp_label_hd n l2 k (extra : list (line a)) l (code : labLang.prog a) :
  l2 <> 0 -> ~ In (n, l2) (labProps.extract_labels extra) ->
  loc_to_pc n l2 (Section_ n (extra ++ Label n l2 k :: l) :: code) =
  SOME (LENGTH (FILTER (fun x => negb (is_Label x)) extra)).
Proof.
  intros Hl2 Hin; induction extra as [|y extra IH].
  - cbn [app]. rewrite ltp_cons. rewrite (proj2 (N.eqb_neq l2 0) Hl2), Bool.andb_false_r.
    rewrite lab_ex_eq, !N.eqb_refl. reflexivity.
  - cbn [app]. rewrite ltp_cons. rewrite (proj2 (N.eqb_neq l2 0) Hl2), Bool.andb_false_r.
    rewrite lab_ex_eq. cbn [negb andb].
    destruct y as [l1' l2' k'| |]; cbn [labProps.extract_labels In] in Hin.
    + replace ((l1' =? n) && (l2' =? l2)) with false.
      2:{ symmetry; apply Bool.andb_false_iff.
          destruct (N.eqb_spec l1' n); [|left; reflexivity].
          destruct (N.eqb_spec l2' l2); [|right; reflexivity]. subst. exfalso; apply Hin; left; reflexivity. }
      cbn [is_Label List.filter negb]. rewrite IH by (intros H; apply Hin; right; exact H). reflexivity.
    + cbn [is_Label List.filter negb LENGTH]. rewrite IH by exact Hin. cbn [andb]. f_equal; lia.
    + cbn [is_Label List.filter negb LENGTH]. rewrite IH by exact Hin. cbn [andb]. f_equal; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "labs_correct_hd" *)
Theorem labs_correct_hd : forall n (code : labLang.prog a) (extra : list (line a)) l,
  ALL_DISTINCT (labProps.extract_labels (extra ++ l)) /\
  EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0)) (labProps.extract_labels (extra ++ l)) ->
  labs_correct (LENGTH (FILTER (fun x => negb (is_Label x)) extra)) l (Section_ n (extra ++ l) :: code).
Proof.
  intros n code extra l; revert extra; induction l as [|h l IH]; intros extra [Hd He];
    [exact Logic.I|].
  cbn [labs_correct]. destruct (is_Label h) eqn:Eh.
  - split.
    + specialize (IH (extra ++ [h])). rewrite <- app_assoc in IH. cbn [app] in IH.
      rewrite filter_app in IH. cbn [List.filter] in IH. rewrite Eh in IH. cbn [negb] in IH.
      rewrite app_nil_r in IH. apply IH. split; assumption.
    + destruct h as [l1 l2 k| |]; try discriminate.
      rewrite labProps.extract_labels_append in Hd, He. cbn [labProps.extract_labels] in Hd, He.
      apply EVERY_Forall in He. apply Forall_app in He as [_ He]. inversion He as [|? ? Hx _]; subst.
      apply Bool.andb_true_iff in Hx as [Hx1 Hx2]. apply N.eqb_eq in Hx1; subst l1.
      apply Bool.negb_true_iff, N.eqb_neq in Hx2.
      apply ltp_label_hd; [exact Hx2|].
      intros Hin. apply ALL_DISTINCT_NoDup_list in Hd. apply NoDup_remove_2 in Hd.
      apply Hd. apply in_or_app; left; exact Hin.
  - specialize (IH (extra ++ [h])). rewrite <- app_assoc in IH. cbn [app] in IH.
    rewrite filter_app, LENGTH_app in IH. cbn [List.filter] in IH. rewrite Eh in IH. cbn [negb LENGTH] in IH.
    apply IH. split; assumption.
Qed.

(** HOL's [labels_ok] is a boolean conjunction; it is a [Prop] here. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "labels_ok_def" *)
Definition labels_ok (code : labLang.prog a) : Prop :=
  ALL_DISTINCT (MAP (fun s => match s with Section_ n _ => n end) code) /\
  EVERY (fun s => match s with Section_ n lines =>
    let labs := labProps.extract_labels lines in
    EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0)) labs && ALL_DISTINCT labs end) code.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "labels_ok_imp" *)
Theorem labels_ok_imp : forall code : labLang.prog a,
  labels_ok code ->
  EVERY sec_labels_ok code /\
  ALL_DISTINCT (MAP Section_num code) /\
  EVERY (ALL_DISTINCT ∘ labProps.extract_labels ∘ Section_lines) code.
Proof.
  intros code [Hd He]. unfold is_true in *.
  repeat split.
  - rewrite EVERY_Forall in He |- *. eapply Forall_impl; [|exact He].
    intros [n lines] H. cbn in H |- *. apply Bool.andb_true_iff in H as [H _].
    apply (proj1 (EVERY_sec_label_ok n lines)), H.
  - replace (MAP Section_num code) with (MAP (fun s => match s with Section_ n _ => n end) code);
      [exact Hd|apply map_ext; intros []; reflexivity].
  - rewrite EVERY_Forall in He |- *. eapply Forall_impl; [|exact He].
    intros [n lines] H. cbn in H |- *. apply Bool.andb_true_iff in H as [_ H]. exact H.
Qed.

(** Galette helper: skipping a section whose labels are all of another
    section name. *)
Lemma ltp_skip_sec n n' l2 (lines : list (line a)) (code : labLang.prog a) :
  n' <> n -> EVERY (sec_label_ok n') lines ->
  loc_to_pc n l2 (Section_ n' lines :: code) =
  match loc_to_pc n l2 code with
  | NONE => NONE
  | SOME k => SOME (k + LENGTH (FILTER (fun x => negb (is_Label x)) lines))
  end.
Proof.
  intros Hnn Hok; induction lines as [|y lines IH].
  - rewrite ltp_cons.
    replace (andb (n' =? n) (l2 =? 0)) with false
      by (symmetry; apply Bool.andb_false_iff; left; apply N.eqb_neq; exact Hnn).
    destruct (loc_to_pc n l2 code); [cbn; rewrite N.add_0_r|]; reflexivity.
  - cbn [EVERY] in Hok. apply Bool.andb_true_iff in Hok as [Hy Hok].
    rewrite ltp_cons.
    replace (andb (n' =? n) (l2 =? 0)) with false
      by (symmetry; apply Bool.andb_false_iff; left; apply N.eqb_neq; exact Hnn).
    rewrite (sec_label_ok_neq n n' y l2 Hy Hnn). cbn [andb].
    rewrite (IH Hok). cbn [List.filter].
    destruct (is_Label y); cbn [negb LENGTH];
      destruct (loc_to_pc n l2 code); try reflexivity; f_equal; lia.
Qed.

Lemma labs_correct_skip n n' (lines' lines : list (line a)) (code : labLang.prog a) : forall x,
  n' <> n -> EVERY (sec_label_ok n') lines' -> EVERY (sec_label_ok n) lines ->
  labs_correct x lines code ->
  labs_correct (x + LENGTH (FILTER (fun x => negb (is_Label x)) lines')) lines (Section_ n' lines' :: code).
Proof.
  induction lines as [|y lines IH]; intros x Hnn Hok' Hok H; [exact Logic.I|].
  cbn [EVERY] in Hok. apply Bool.andb_true_iff in Hok as [Hy Hok].
  cbn [labs_correct] in H |- *. destruct (is_Label y).
  - destruct H as [H1 H2]. split; [apply IH; assumption|].
    destruct y as [l1 l2 k| |]; try exact Logic.I.
    cbn in Hy. apply Bool.andb_true_iff in Hy as [Hy _]. apply N.eqb_eq in Hy; subst l1.
    rewrite (ltp_skip_sec n n' l2 lines' code Hnn Hok'), H2. reflexivity.
  - replace (x + LENGTH (FILTER (fun x => negb (is_Label x)) lines') + 1)
      with (x + 1 + LENGTH (FILTER (fun x => negb (is_Label x)) lines')) by lia.
    apply IH; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "labels_ok_labs_correct" *)
Theorem labels_ok_labs_correct : forall code : labLang.prog a,
  labels_ok code ->
  EVERY (fun s => ⌜match s with Section_ n lines =>
      match loc_to_pc n 0 code with
      | SOME pc => labs_correct pc lines code
      | _ => True
      end end⌝) code.
Proof.
  intros code Hok. apply EVERY_Forall, List.Forall_forall. intros s Hs. apply bool_decide_spec.
  revert s Hs. induction code as [|[n lines] code IH]; intros s Hs; [destruct Hs|].
  destruct Hok as [Hd He]. cbn [List.map ALL_DISTINCT EVERY] in Hd, He. unfold is_true in Hd, He.
  apply Bool.andb_true_iff in Hd as [Hn Hd]. apply Bool.andb_true_iff in He as [Hl He].
  apply Bool.andb_true_iff in Hl as [Hl1 Hl2].
  destruct Hs as [<-|Hs].
  - rewrite ltp_cons, N.eqb_refl. cbn [andb].
    exact (labs_correct_hd n code [] lines (conj Hl2 Hl1)).
  - specialize (IH (conj Hd He) s Hs). destruct s as [n' lines'].
    assert (Hnn : n <> n').
    { intros ->. apply Bool.negb_true_iff in Hn. rewrite <- Bool.not_true_iff_false in Hn.
      apply Hn. apply MEM_In, in_map_iff. exists (Section_ n' lines'); auto. }
    assert (Hok1 : EVERY (sec_label_ok n) lines) by (apply (proj1 (EVERY_sec_label_ok n lines)), Hl1).
    assert (Hok2 : EVERY (sec_label_ok n') lines').
    { apply EVERY_Forall, List.Forall_forall with (x := Section_ n' lines') in He; [|exact Hs].
      cbn in He. apply Bool.andb_true_iff in He as [He _]. apply (proj1 (EVERY_sec_label_ok n' lines')), He. }
    rewrite (ltp_skip_sec n' n 0 lines code Hnn Hok1).
    destruct (loc_to_pc n' 0 code) as [pc|]; [|exact Logic.I].
    exact (labs_correct_skip n' n lines lines' code pc Hnn Hok1 Hok2 IH).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "labs_correct_append" *)
Theorem labs_correct_append : forall (rest : list (line a)) (code : labLang.prog a) ls pc,
  labs_correct pc (ls ++ rest) code -> labs_correct pc ls code.
Proof.
  intros rest code ls; induction ls as [|x ls IH]; intros pc H; [exact Logic.I|].
  cbn [labs_correct app] in H |- *. destruct (is_Label x); [destruct H; split; [eapply IH|]; eauto|eapply IH; eauto].
Qed.

End LabelsOk.

Section ProgToSection.
Context {a : N}.

Lemma prog_to_section_eq n (p : prog a) :
  prog_to_section (n, p) =
  Section_ n (append (FST (flatten true p n (stack_alloc.next_lab p 2) [] [])) ++
              [Label n (if is_Seq p then SND (SND (flatten true p n (stack_alloc.next_lab p 2) [] [])) else 1) 0]).
Proof.
  unfold prog_to_section. destruct (flatten true p n (stack_alloc.next_lab p 2) [] []) as [xs [nr m]].
  cbn [FST SND fst snd]. rewrite append_Append, append_List. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed_prog_to_section_lemma" *)
Local Theorem code_installed_prog_to_section_lemma : forall (prog4 : list (N * prog a)) n prog3,
  ALOOKUP prog4 n = SOME prog3 ->
  exists pc,
    code_installed' pc (append (FST (flatten true prog3 n (stack_alloc.next_lab prog3 2) [] [])))
      (MAP prog_to_section prog4) /\
    loc_to_pc n 0 (MAP prog_to_section prog4) = SOME pc.
Proof.
  induction prog4 as [|[k p] prog4 IH]; intros n prog3 H; [discriminate|].
  cbn [ALOOKUP] in H. cbn [List.map]. rewrite prog_to_section_eq.
  destruct (decide (k = n)) as [->|Hkn].
  - injection H as ->. exists 0. split; [apply code_installed'_simp|].
    rewrite ltp_cons, N.eqb_refl. reflexivity.
  - destruct (IH n prog3 H) as (pc & H1 & H2).
    eexists. split; [apply code_installed_cons, H1|].
    rewrite loc_to_pc_skip_section by congruence. rewrite H2. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed_prog_to_section" *)
Theorem code_installed_prog_to_section : forall (prog4 : list (N * prog a)) n prog3,
  labels_ok (MAP prog_to_section prog4) /\
  ALOOKUP prog4 n = SOME prog3 ->
  exists pc,
    code_installed pc (append (FST (flatten true prog3 n (stack_alloc.next_lab prog3 2) [] [])))
      (MAP prog_to_section prog4) /\
    loc_to_pc n 0 (MAP prog_to_section prog4) = SOME pc.
Proof.
  intros prog4 n prog3 [Hok H].
  destruct (code_installed_prog_to_section_lemma prog4 n prog3 H) as (pc & H1 & H2).
  exists pc. split; [|exact H2]. apply code_installed_eq. split; [exact H1|].
  pose proof (labels_ok_labs_correct _ Hok) as HL.
  apply EVERY_Forall in HL. rewrite List.Forall_forall in HL.
  assert (Hm : In (prog_to_section (n, prog3)) (MAP prog_to_section prog4)).
  { apply in_map. clear -H. induction prog4 as [|[k p] prog4 IH]; [discriminate|].
    cbn in H. destruct (decide (k = n)) as [->|]; [injection H as ->; left; reflexivity|right; auto]. }
  specialize (HL _ Hm). apply bool_decide_spec in HL.
  rewrite prog_to_section_eq in HL. rewrite H2 in HL.
  eapply labs_correct_append; exact HL.
Qed.

End ProgToSection.

(** ** The state relation *)

Ltac lab_cbn :=
  cbn [labSem.regs labSem.fp_regs mem mem_domain shared_mem_domain pc labSem.be labSem.ffi
       io_regs cc_regs io_fp_regs cc_fp_regs labSem.code labSem.compile labSem.compile_oracle
       labSem.code_buffer labSem.clock failed ptr_reg len_reg ptr2_reg len2_reg link_reg
       labSem.set_regs labSem.set_fp_regs set_mem set_mem_domain set_shared_mem_domain set_pc
       labSem.set_be labSem.set_ffi set_io_regs set_cc_regs set_io_fp_regs set_cc_fp_regs
       labSem.set_code labSem.set_compile labSem.set_compile_oracle labSem.set_code_buffer
       labSem.set_clock set_failed set_ptr_reg set_len_reg set_ptr2_reg set_len2_reg set_link_reg
       upd_pc upd_reg upd_mem upd_fp_reg labSem.dec_clock inc_pc labSem.assert] in *.

Section StateRel.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : stackSem.state a c ffi_t) (t : labSem.state a c ffi_t).

(** HOL's [λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1] (a boolean in an [EVERY])
    is written with [=?]. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "state_rel_def" *)
Definition state_rel s t : Prop :=
  (forall n v, FLOOKUP (regs s) n = SOME v -> labSem.regs t n = v) /\
  (forall n v, FLOOKUP (fp_regs s) n = SOME v -> labSem.fp_regs t n = v) /\
  mem t = memory s /\
  mem_domain t = mdomain s /\
  shared_mem_domain t = sh_mdomain s /\
  labSem.be t = be s /\
  labSem.ffi t = ffi s /\
  labSem.clock t = clock s /\
  (forall n prog, lookup n (code s) = SOME prog ->
     call_args prog (ptr_reg t) (len_reg t) (ptr2_reg t) (len2_reg t) (link_reg t) /\
     exists pc, code_installed pc
                  (append (FST (flatten true prog n (stack_alloc.next_lab prog 2) [] [])))
                  (labSem.code t) /\
                loc_to_pc n 0 (labSem.code t) = SOME pc) /\
  domain (code s) = set (MAP Section_num (labSem.code t)) /\
  EVERY sec_labels_ok (labSem.code t) /\
  ~ failed t /\
  link_reg t <> len_reg t /\ link_reg t <> ptr_reg t /\
  link_reg t <> len2_reg t /\ link_reg t <> ptr2_reg t /\
  ~ (link_reg t IN ffi_save_regs s) /\
  (forall k i n, k IN ffi_save_regs s -> io_regs t n i k = NONE) /\
  (forall k n, k IN ffi_save_regs s -> cc_regs t n k = NONE) /\
  (forall x, x IN mdomain s -> w2n x MOD (dimindex a DIV 8) = 0) /\
  (forall x, x IN sh_mdomain s -> w2n x MOD (dimindex a DIV 8) = 0) /\
  code_buffer s = labSem.code_buffer t /\
  compile s = (fun cfg p => labSem.compile t cfg (MAP prog_to_section p)) /\
  labSem.compile_oracle t = (fun n => let '(cfg, (p, _)) := compile_oracle s n in
                                       (cfg, MAP prog_to_section p)) /\
  (forall k, let '(cfg, (ps, _)) := compile_oracle s k in
     EVERY (fun '(n, p) =>
        call_args p (ptr_reg t) (len_reg t) (ptr2_reg t) (len2_reg t) (link_reg t) &&
        EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0) && negb (l2 =? 1)) (extract_labels p) &&
        ALL_DISTINCT (extract_labels p)) ps /\
     ALL_DISTINCT (MAP FST ps)) /\
  ~ use_stack s /\
  ~ use_store s /\
  ~ use_alloc s /\
  good_dimindex a.

End StateRel.

Ltac sr_destruct H :=
  let Hregs := fresh "Hregs" in let Hfp := fresh "Hfp" in let Hmem := fresh "Hmem" in
  let Hmd := fresh "Hmd" in let Hsmd := fresh "Hsmd" in let Hbe := fresh "Hbe" in
  let Hffi := fresh "Hffi" in let Hclk := fresh "Hclk" in let Hcode := fresh "Hcode" in
  let Hdom := fresh "Hdom" in let Hsok := fresh "Hsok" in let Hfail := fresh "Hfail" in
  let Hl1 := fresh "Hl1" in let Hl2 := fresh "Hl2" in let Hl3 := fresh "Hl3" in
  let Hl4 := fresh "Hl4" in let Hlsr := fresh "Hlsr" in let Hio := fresh "Hio" in
  let Hcc := fresh "Hcc" in let Hal := fresh "Hal" in let Hsal := fresh "Hsal" in
  let Hcb := fresh "Hcb" in let Hcomp := fresh "Hcomp" in let Hco := fresh "Hco" in
  let Hcos := fresh "Hcos" in let Hus := fresh "Hus" in let Hust := fresh "Hust" in
  let Hua := fresh "Hua" in let Hgd := fresh "Hgd" in
  destruct H as (Hregs & Hfp & Hmem & Hmd & Hsmd & Hbe & Hffi & Hclk & Hcode & Hdom & Hsok &
                 Hfail & Hl1 & Hl2 & Hl3 & Hl4 & Hlsr & Hio & Hcc & Hal & Hsal & Hcb & Hcomp &
                 Hco & Hcos & Hus & Hust & Hua & Hgd).

(** Prove [state_rel] goals after the fields have been normalised:
    split the conjunction and close the conjuncts that are hypotheses. *)
Ltac sr_split :=
  unfold state_rel; lab_cbn; stk_fields;
  repeat (match goal with |- _ /\ _ => split end).

Section StateRelLemmas.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : stackSem.state a c ffi_t) (t : labSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "loc_check_IMP_loc_to_pc" *)
Theorem loc_check_IMP_loc_to_pc : forall s t1 l1 l2,
  loc_check (code s) (l1, l2) /\ state_rel s t1 ->
  exists v, loc_to_pc l1 l2 (labSem.code t1) = SOME v.
Proof.
  intros s t1 l1 l2 [Hl Hs]. sr_destruct Hs. cbn [loc_check] in Hl.
  destruct Hl as [[-> Hd]|(n & e & He & Hin)].
  - apply domain_lookup in Hd. destruct Hd as [p Hp].
    destruct (Hcode l1 p Hp) as [_ (pc & _ & Hpc)]. eauto.
  - destruct (Hcode n e He) as [_ (pc & Hci & _)].
    eapply code_installed_get_labels_IMP. split; [exact Hci|exact Hin].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "state_rel_dec_clock" *)
Theorem state_rel_dec_clock : forall s t,
  state_rel s t -> state_rel (dec_clock s) (labSem.dec_clock t).
Proof.
  intros s t H. sr_destruct H. sr_split; try assumption. rewrite Hclk; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "state_rel_with_pc" *)
Theorem state_rel_with_pc : forall pc s t, state_rel s t -> state_rel s (upd_pc pc t).
Proof. intros pc s t H. sr_destruct H. sr_split; assumption. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "state_rel_with_clock" *)
Theorem state_rel_with_clock : forall k s t,
  state_rel s t -> state_rel (set_clock k s) (labSem.set_clock k t).
Proof. intros k s t H. sr_destruct H. sr_split; try assumption; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "set_var_upd_reg" *)
Theorem set_var_upd_reg : forall a0 b s t,
  state_rel s t -> state_rel (set_var a0 b s) (upd_reg a0 b t).
Proof.
  intros a0 b s t H. sr_destruct H. sr_split; try assumption.
  intros n v Hn. rewrite FLOOKUP_UPDATE in Hn. rewrite APPLY_UPDATE_THM.
  destruct (decide (a0 = n)); [congruence|exact (Hregs n v Hn)].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "set_var_Word_upd_reg" *)
Theorem set_var_Word_upd_reg : forall a0 b s t,
  state_rel s t -> state_rel (set_var a0 (Word b) s) (upd_reg a0 (Word b) t).
Proof. intros; apply set_var_upd_reg; assumption. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "set_fp_var_upd_fp_reg" *)
Theorem set_fp_var_upd_fp_reg : forall a0 b s t,
  state_rel s t -> state_rel (set_fp_var a0 b s) (upd_fp_reg a0 b t).
Proof.
  intros a0 b s t H. sr_destruct H. sr_split; try assumption.
  intros n v Hn. rewrite FLOOKUP_UPDATE in Hn. rewrite APPLY_UPDATE_THM.
  destruct (decide (a0 = n)); [congruence|exact (Hfp n v Hn)].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "mem_store_upd_mem" *)
Theorem mem_store_upd_mem : forall x y s t s1,
  state_rel s t /\ stackSem.mem_store x y s = SOME s1 -> state_rel s1 (upd_mem x y t).
Proof.
  intros x y s t s1 [H Hm]. unfold stackSem.mem_store in Hm.
  destruct (classical_dec _); [|discriminate]. injection Hm as <-.
  sr_destruct H. sr_split; try assumption. rewrite Hmem; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "state_rel_read_reg_FLOOKUP_regs" *)
Theorem state_rel_read_reg_FLOOKUP_regs : forall s t x y,
  state_rel s t /\ FLOOKUP (regs s) x = SOME y -> y = read_reg x t.
Proof. intros s t x y [H Hx]. sr_destruct H. symmetry; exact (Hregs x y Hx). Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "state_rel_read_fp_reg_FLOOKUP_fp_regs" *)
Theorem state_rel_read_fp_reg_FLOOKUP_fp_regs : forall s t n x,
  state_rel s t /\ get_fp_var n s = SOME x -> x = read_fp_reg n t.
Proof. intros s t n x [H Hx]. sr_destruct H. symmetry; exact (Hfp n x Hx). Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "state_rel_get_var_imm" *)
Theorem state_rel_get_var_imm : forall s t r x,
  state_rel s t /\ get_var_imm r s = SOME x -> reg_imm r t = x.
Proof.
  intros s t [r|w] x [H Hx]; cbn in Hx |- *.
  - unfold get_var in Hx. symmetry; exact (state_rel_read_reg_FLOOKUP_regs s t r x (conj H Hx)).
  - congruence.
Qed.

End StateRelLemmas.

Section InstCorrect.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : stackSem.state a c ffi_t) (t : labSem.state a c ffi_t).
Local Open Scope word_scope.

Lemma word_exp_addr s ad (w : word a) :
  word_exp s (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w]) =
  match FLOOKUP (regs s) ad with SOME (Word v) => SOME (v + w) | _ => NONE end.
Proof.
  cbn [word_exp List.map EVERY IS_SOME]. destruct (FLOOKUP (regs s) ad) as [[v|l n]|]; cbn; try reflexivity.
  rewrite (proj1 WORD_ADD_0). reflexivity.
Qed.

Lemma binop_upd_word_op r1 bop (w1 w2 : word a) v t :
  wordLang.word_op bop [w1; w2] = SOME v -> binop_upd r1 bop w1 w2 t = upd_reg r1 (Word v) t.
Proof.
  destruct bop; cbn; intros H; injection H as <-; f_equal; f_equal.
  - rewrite (proj1 WORD_ADD_0). reflexivity.
  - rewrite WORD_NOT_0, (proj1 (proj2 (WORD_AND_CLAUSES w2))). reflexivity.
  - rewrite (proj1 (proj2 (proj2 (proj2 (WORD_OR_CLAUSES w2))))). reflexivity.
  - rewrite (proj1 (proj2 (proj2 (proj2 (WORD_XOR_CLAUSES w2))))). reflexivity.
Qed.

Lemma sr_regs s t x v : state_rel s t -> FLOOKUP (regs s) x = SOME v -> labSem.regs t x = v.
Proof. intros H Hx; symmetry; exact (state_rel_read_reg_FLOOKUP_regs s t x v (conj H Hx)). Qed.

Lemma sr_fp s t x v : state_rel s t -> get_fp_var x s = SOME v -> read_fp_reg x t = v.
Proof. intros H Hx; symmetry; exact (state_rel_read_fp_reg_FLOOKUP_fp_regs s t x v (conj H Hx)). Qed.

Lemma sr_align s t x :
  state_rel s t -> x IN mdomain s ->
  andb ((w2n x MOD (dimindex a DIV 8)) =? 0)%N ⌜x IN mem_domain t⌝ = true.
Proof.
  intros H Hx. pose proof H as H'. sr_destruct H'. rewrite (Hal x Hx), N.eqb_refl, Hmd.
  cbn [andb]. apply bool_decide_spec. exact Hx.
Qed.

Ltac rr Hs :=
  repeat match goal with
  | E : FLOOKUP (regs _) ?x = SOME ?v |- context [labSem.regs ?t ?x] =>
      rewrite (sr_regs _ t x v Hs E)
  | E : get_fp_var ?x _ = SOME ?v |- context [read_fp_reg ?x ?t] =>
      rewrite (sr_fp _ t x v Hs E)
  end.

Ltac inst_split H :=
  repeat match goal with
         | E0 : context [match ?x with _ => _ end] |- _ =>
             lazymatch type of E0 with _ = _ => idtac end;
             let E := fresh "E" in destruct x eqn:E; cbn [IS_SOME THE andb negb] in E0;
             cbn beta iota zeta in E0; try discriminate E0
         | E0 : _ = _ |- _ => progress (cbn [IS_SOME THE andb negb] in E0); try discriminate E0
         | E0 : SOME ?x = SOME ?y |- _ => is_var x; is_var y; injection E0 as E0; subst x
         end.

Ltac inj_all :=
  repeat match goal with
         | E : SOME _ = SOME _ |- _ => injection E; clear E; intros
         | E : _ :: _ = _ :: _ |- _ => injection E; clear E; intros
         end.

Ltac ifin Hs :=
  inj_all; subst; inj_all; subst; inj_all; subst; rr Hs;
  cbn beta iota zeta;
  repeat match goal with
         | E : ?b = true |- context [?b] => rewrite E; cbn beta iota
         | E : ?b = false |- context [?b] => rewrite E; cbn beta iota
         | E : ?x = SOME _ |- context [match ?x with _ => _ end] => rewrite E; cbn beta iota zeta
         end;
  rewrite ?assert_T;
  repeat first [exact Hs | apply set_var_upd_reg | apply set_fp_var_upd_fp_reg].

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "inst_correct" *)
Theorem inst_correct : forall i s1 s2 t1,
  inst i s1 = SOME s2 /\ state_rel s1 t1 -> state_rel s2 (asm_inst i t1).
Proof.
  intros i s1 s2 t1 [Hi Hs].
  destruct i as [|r w|[bop r1 r2 ri|sh r1 r2 ri|r1 r2 r3|r1 r2 r3 r4|r1 r2 r3 r4 r5|r1 r2 r3 r4|
                      r1 r2 r3 r4|r1 r2 r3 r4]|m r [ad w]|f].
  - (* Skip *) cbn in Hi. injection Hi as <-. exact Hs.
  - (* Const *) cbn in Hi. injection Hi as <-. apply set_var_upd_reg, Hs.
  - (* Binop *) cbn [inst] in Hi. cbn [asm_inst arith_upd].
    destruct (andb (bool_decide (bop = asm.Or)) (bool_decide (ri = Reg r2))) eqn:Eor.
    + apply Bool.andb_true_iff in Eor as [Eo Er]. apply bool_decide_spec in Eo, Er. subst bop ri.
      destruct (FLOOKUP (regs s1) r2) as [v|] eqn:E2; [|discriminate]. injection Hi as <-.
      cbn [reg_imm]. rr Hs. destruct v as [w1|l n].
      * cbn [binop_upd]. rewrite WORD_OR_IDEM. apply set_var_upd_reg, Hs.
      * cbn beta iota.
        apply set_var_upd_reg, Hs.
    + unfold assign in Hi. cbn [word_exp List.map EVERY IS_SOME] in Hi.
      destruct ri as [r3|v].
      * cbn [word_exp EVERY IS_SOME List.map] in Hi. inst_split Hi.
        injection Hi as <-. cbn [reg_imm]. rr Hs. cbn beta iota.
        erewrite binop_upd_word_op by eassumption; apply set_var_upd_reg, Hs.
      * cbn [word_exp EVERY IS_SOME List.map] in Hi. inst_split Hi.
        injection Hi as <-. cbn [reg_imm]. rr Hs. cbn beta iota.
        erewrite binop_upd_word_op by eassumption; apply set_var_upd_reg, Hs.
  - (* Shift *) cbn [inst] in Hi. unfold assign in Hi. cbn [asm_inst arith_upd].
    destruct ri as [r3|v]; cbn [word_exp] in Hi; inst_split Hi; injection Hi as <-;
      cbn [reg_imm]; rr Hs; cbn beta iota;
      match goal with E : wordLang.word_sh _ _ _ = SOME _ |- _ =>
        apply word_sh_word_shift in E; destruct E as [Elt ->] end;
      rewrite (proj2 (N.ltb_lt _ _) Elt), assert_T; apply set_var_upd_reg, Hs.
  - (* Div *) cbn [inst get_vars] in Hi. unfold get_var in Hi. cbn [asm_inst arith_upd].
    inst_split Hi. all: injection Hi as <-. all: ifin Hs.
  - (* LongMul *) cbn [inst get_vars] in Hi. unfold get_var in Hi. cbn [asm_inst arith_upd].
    inst_split Hi. all: injection Hi as <-. all: ifin Hs.
  - (* LongDiv *) cbn [inst get_vars] in Hi. unfold get_var in Hi. cbn [asm_inst arith_upd].
    inst_split Hi. all: injection Hi as <-. all: ifin Hs.
  - (* AddCarry *) cbn [inst get_vars] in Hi. unfold get_var in Hi. cbn [asm_inst arith_upd].
    inst_split Hi. all: injection Hi as <-. all: ifin Hs.
  - (* AddOverflow *) cbn [inst get_vars] in Hi. unfold get_var in Hi. cbn [asm_inst arith_upd].
    inst_split Hi. all: injection Hi as <-. all: ifin Hs.
  - (* SubOverflow *) cbn [inst get_vars] in Hi. unfold get_var in Hi. cbn [asm_inst arith_upd].
    inst_split Hi. all: injection Hi as <-. all: ifin Hs.
  - (* Mem *) pose proof Hs as Hs'. sr_destruct Hs'.
    destruct m; cbn [inst] in Hi; rewrite ?word_exp_addr in Hi; unfold get_var in Hi;
      cbn [asm_inst mem_op]; try discriminate Hi.
    + (* Load *) inst_split Hi. try (injection Hi as <-). inj_all; subst. unfold stackSem.mem_load in *.
      destruct (classical_dec _) as [Hin|]; [|discriminate]. inj_all; subst.
      unfold labSem.mem_load, addr. rr Hs. cbn beta iota.
      rewrite (sr_align s1 t1 _ Hs Hin), assert_T, Hmem. apply set_var_upd_reg, Hs.
    + (* Load8 *) inst_split Hi. try (injection Hi as <-). inj_all; subst.
      unfold mem_load_byte, addr. rr Hs. cbn beta iota. rewrite Hmem, Hmd, Hbe.
      match goal with E : mem_load_byte_aux _ _ _ _ = _ |- _ => rewrite E end.
      apply set_var_upd_reg, Hs.
    + (* Load32 *) inst_split Hi. try (injection Hi as <-). inj_all; subst.
      unfold mem_load32, addr. rr Hs. cbn beta iota. rewrite Hmem, Hmd, Hbe.
      match goal with E : mem_load_32 _ _ _ _ = _ |- _ => rewrite E end.
      apply set_var_upd_reg, Hs.
    + (* Store *) inst_split Hi. try (injection Hi as <-). inj_all; subst.
      unfold labSem.mem_store, addr. rr Hs. cbn beta iota.
      match goal with E : stackSem.mem_store _ _ _ = SOME _ |- _ =>
        pose proof E as E'; unfold stackSem.mem_store in E';
        destruct (classical_dec _) as [Hin|]; [|discriminate] end.
      rewrite (sr_align s1 t1 _ Hs Hin), assert_T.
      eapply mem_store_upd_mem. split; [exact Hs|eassumption].
    + (* Store8 *) inst_split Hi. try (injection Hi as <-). inj_all; subst.
      unfold mem_store_byte, addr. rr Hs. cbn beta iota. rewrite Hmem, Hmd, Hbe.
      match goal with E : mem_store_byte_aux _ _ _ _ _ = _ |- _ => rewrite E end.
      sr_destruct Hs. sr_split; try assumption; reflexivity.
    + (* Store32 *) inst_split Hi. try (injection Hi as <-). inj_all; subst.
      unfold mem_store32, addr. rr Hs. cbn beta iota. rewrite Hmem, Hmd, Hbe.
      match goal with E : mem_store_32 _ _ _ _ _ = _ |- _ => rewrite E end.
      sr_destruct Hs. sr_split; try assumption; reflexivity.
  - (* FP *) destruct f; cbn [inst] in Hi; cbn [asm_inst fp_upd];
      unfold get_var in Hi; inst_split Hi; try (injection Hi as <-); ifin Hs.
Qed.

End InstCorrect.

(** ** Properties of [flatten] *)

Section FlattenBasic.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_leq" *)
Theorem flatten_leq : forall t (x : prog a) y z cs bs, z <= SND (SND (flatten t x y z cs bs)).
Proof.
  intros t x; revert t.
  induction x as [ret dest h Hr Hh|p1 p2 IH1 IH2|c0 r ri p1 p2 IH1 IH2|p IH|p Hp]
    using prog_nested_ind; intros t y z cs bs; cbn [flatten].
  - destruct ret as [[p1 [lr [l1 l2]]]|]; [|reflexivity || (cbn; lia)].
    specialize (Hr p1 _ eq_refl). specialize (Hr false y z cs bs).
    destruct (flatten false p1 y z cs bs) as [xs [nr1 m1]] eqn:E1. cbn in Hr.
    destruct h as [[p2 [k1 k2]]|]; [|cbn; lia].
    specialize (Hh p2 _ eq_refl false y m1 cs bs).
    destruct (flatten false p2 y m1 cs bs) as [ys [nr2 m2]] eqn:E2. cbn in Hh |- *. lia.
  - specialize (IH1 false y z cs bs). destruct (flatten false p1 y z cs bs) as [xs [nr1 m1]].
    specialize (IH2 false y m1 cs bs). destruct (flatten false p2 y m1 cs bs) as [ys [nr2 m2]].
    cbn in IH1, IH2. destruct t; cbn; lia.
  - specialize (IH1 false y z cs bs). destruct (flatten false p1 y z cs bs) as [xs [nr1 m1]].
    specialize (IH2 false y m1 cs bs). destruct (flatten false p2 y m1 cs bs) as [ys [nr2 m2]].
    cbn in IH1, IH2. destruct (is_Skip p1), (is_Skip p2), nr1, nr2; cbn; lia.
  - specialize (IH false y (z + 2) (z :: cs) ((z + 1) :: bs)).
    destruct (flatten false p y (z + 2) (z :: cs) ((z + 1) :: bs)) as [xs [nr1 m1]].
    cbn in IH |- *. lia.
  - destruct p; try contradiction; cbn; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "NOT_bad_fun_return_IMP_SOME" *)
Local Theorem NOT_bad_fun_return_IMP_SOME : forall q : option (result a),
  ~ bad_fun_return q -> exists n, q = SOME n.
Proof. intros [n|] H; [eauto|exfalso; apply H; reflexivity]. Qed.

End FlattenBasic.

Section NoRet.
Context {a : N} {c ffi_t : Type}.

Lemma IS_SOME_bad_fun (r : option (result a)) (s : stackSem.state a c ffi_t) :
  IS_SOME (FST (if bad_fun_return r then (SOME Error, s) else (r, s))).
Proof. destruct r as [[]|]; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "no_ret_correct" *)
Theorem no_ret_correct : forall t (p : prog a) y z cs bs,
  FST (SND (flatten t p y z cs bs)) ->
  forall s : stackSem.state a c ffi_t, IS_SOME (FST (evaluate (p, s))).
Proof.
  intros t p; revert t.
  induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|c0 r ri p1 p2 IH1 IH2|p IH|p Hp]
    using prog_nested_ind; intros t y z cs bs Hnr s; cbn [flatten] in Hnr;
    rewrite evaluate_eqn; cbn [evaluate_body].
  - destruct ret as [[p1 [lr [l1 l2]]]|].
    + specialize (Hr p1 _ eq_refl).
      destruct (flatten false p1 y z cs bs) as [xs [nr1 m1]] eqn:E1.
      assert (H1 : forall s : stackSem.state a c ffi_t, IS_SOME (FST (evaluate (p1, s)))).
      { destruct h as [[p2 [k1 k2]]|]; cbn in Hnr.
        - destruct (flatten false p2 y m1 cs bs) as [ys [nr2 m2]]; cbn in Hnr.
          apply Bool.andb_true_iff in Hnr as [Hnr _].
          apply (Hr false y z cs bs); rewrite E1; exact Hnr.
        - apply (Hr false y z cs bs); rewrite E1; exact Hnr. }
      destruct (find_code _ _ _); [|reflexivity].
      destruct (clock s =? 0); [reflexivity|]. rewrite fix_clock_evaluate.
      destruct (evaluate (_, _)) as [[[]|] s2]; try reflexivity.
      * destruct (negb _); [reflexivity|apply H1].
      * destruct h as [[p2 [k1 k2]]|]; [|reflexivity].
        destruct (negb _); [reflexivity|].
        cbn in Hnr. destruct (flatten false p2 y m1 cs bs) as [ys [nr2 m2]] eqn:E2; cbn in Hnr.
        apply Bool.andb_true_iff in Hnr as [_ Hnr].
        apply (Hh p2 _ eq_refl false y m1 cs bs); rewrite E2; exact Hnr.
    + destruct (find_code _ _ _); [|reflexivity].
      destruct (negb _); [reflexivity|]. destruct (clock s =? 0); [reflexivity|].
      rewrite fix_clock_evaluate. destruct (evaluate (_, _)) as [r s2]. apply IS_SOME_bad_fun.
  - destruct (flatten false p1 y z cs bs) as [xs [nr1 m1]] eqn:E1.
    destruct (flatten false p2 y m1 cs bs) as [ys [nr2 m2]] eqn:E2.
    assert (Hor : nr1 || nr2 = true) by (destruct t; exact Hnr).
    rewrite fix_clock_evaluate.
    destruct (evaluate (p1, s)) as [[r1|] s1] eqn:Ev; [reflexivity|].
    apply Bool.orb_true_iff in Hor as [H1|H2].
    + exfalso. pose proof (IH1 false y z cs bs ltac:(rewrite E1; exact H1) s) as X.
      rewrite Ev in X. discriminate X.
    + apply (IH2 false y m1 cs bs); rewrite E2; exact H2.
  - destruct (flatten false p1 y z cs bs) as [xs [nr1 m1]] eqn:E1.
    destruct (flatten false p2 y m1 cs bs) as [ys [nr2 m2]] eqn:E2.
    destruct (get_var r s), (get_var_imm ri s); try reflexivity.
    destruct (wordSem.word_cmp _ _ _) as [[]|]; try reflexivity.
    + destruct (is_Skip p1), (is_Skip p2), nr1, nr2; cbn in Hnr; try discriminate;
        apply (IH1 false y z cs bs); rewrite E1; reflexivity.
    + destruct (is_Skip p1), (is_Skip p2), nr1, nr2; cbn in Hnr; try discriminate;
        apply (IH2 false y m1 cs bs); rewrite E2; reflexivity.
  - destruct (flatten false p y (z + 2) _ _) as [xs [nr1 m1]]. discriminate Hnr.
  - destruct p; try contradiction; cbn in Hnr; try discriminate Hnr; cbn [evaluate_body].
    + destruct (get_var _ s) as [[]|]; reflexivity.
    + destruct (get_var _ s) as [[]|]; reflexivity.
    + reflexivity.
    + reflexivity.
    + destruct (lookup _ _); [|reflexivity]. destruct (dest_Seq _) as [[]|]; [|reflexivity].
      destruct (clock s =? 0); [reflexivity|]. destruct (evaluate (_, _)) as [r s2]. apply IS_SOME_bad_fun.
    + destruct (get_var _ s); reflexivity.
Qed.

End NoRet.

Section CompileJump.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "compile_jump_correct" *)
Theorem compile_jump_correct : forall pc (code : labLang.prog a) dest pc' regs (s : labSem.state a c ffi_t),
  asm_fetch_aux pc code = SOME (compile_jump dest) /\
  loc_to_pc (dest_to_loc' regs dest) 0 code = SOME pc' /\
  (forall r, dest = inr r -> exists p, read_reg r s = Loc p 0) /\
  labSem.pc s = pc /\ labSem.code s = code /\ labSem.regs s = regs /\ labSem.clock s <> 0 ->
  labSem.evaluate s = labSem.evaluate (upd_pc pc' (labSem.dec_clock s)).
Proof.
  intros pc code dest pc' regs s (Hf & Hl & Hr & <- & <- & <- & Hc).
  rewrite (labSem.evaluate_def s). rewrite (proj2 (N.eqb_neq _ _) Hc). unfold asm_fetch. rewrite Hf.
  destruct dest as [n|r]; cbn [compile_jump dest_to_loc'] in *.
  - unfold get_pc_value. rewrite Hl. reflexivity.
  - destruct (Hr r eq_refl) as [p Hp]. rewrite Hp in *. rewrite Hl. reflexivity.
Qed.

End CompileJump.

(** ** Views of results *)

(** HOL's datatype [result_view] has the name of the function
    [result_view] below; the type is [result_view_ty]. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "result_view" 942 *)
Inductive result_view_ty : Type :=
| Vloc : N -> N -> result_view_ty
| Vcont : N -> N -> result_view_ty
| Vtimeout : result_view_ty
| Verr : result_view_ty.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "result_view_def" *)
Definition result_view {a : N} (r : result a) (l : N) (cs bs : list N) : result_view_ty :=
  match r with
  | Result (Loc n1 n2) => Vloc n1 n2
  | Exception (Loc n1 n2) => Vloc n1 n2
  | TimeOut => Vtimeout
  | Continue n => Vcont l (find_lab n cs)
  | Break n => Vloc l (find_lab n bs)
  | _ => Verr
  end.

(** HOL's first clause is for [Word 0w], the second for the other words. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "halt_word_view_def" *)
Definition halt_word_view {a : N} (w : word_loc a) : targetSem.machine_result :=
  match w with
  | Word w => if bool_decide (w = n2w 0) then targetSem.Halt Success
              else targetSem.Halt Resource_limit_hit
  | _ => targetSem.Error
  end.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "halt_view_def" *)
Definition halt_view {a : N} (r : option (result a)) : option targetSem.machine_result :=
  match r with
  | SOME (Halt w) => SOME (halt_word_view w)
  | SOME (FinalFFI outcome) => SOME (targetSem.Halt (FFI_outcome outcome))
  | _ => NONE
  end.

(** ** Labels produced by [flatten] *)

Section LabPres.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "next_lab_non_zero" 1022 *)
Theorem next_lab_non_zero : forall p : prog a, 2 <= stack_alloc.next_lab p 2.
Proof. intros p; rewrite stack_allocProof.next_lab_EQ_MAX, MAX_max; lia. Qed.

Lemma NoDup_app_sep {A} (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> In x l2 -> False) -> NoDup (l1 ++ l2).
Proof.
  induction l1 as [|x l1 IH]; intros H1 H2 Hd; [exact H2|].
  inversion H1; subst. cbn. constructor.
  - intros Hin. apply in_app_iff in Hin as [Hin|Hin]; [contradiction|].
    exact (Hd x (or_introl eq_refl) Hin).
  - apply IH; auto. intros y Hy1 Hy2. exact (Hd y (or_intror Hy1) Hy2).
Qed.

Lemma NoDup_app_inv {A} (l1 l2 : list A) :
  NoDup (l1 ++ l2) -> NoDup l1 /\ NoDup l2 /\ (forall x, In x l1 -> In x l2 -> False).
Proof.
  intros H. repeat split.
  - eapply NoDup_app_remove_r; exact H.
  - eapply NoDup_app_remove_l; exact H.
  - intros x H1 H2. induction l1 as [|y l1 IH]; [destruct H1|].
    cbn in H. inversion H as [|? ? Hy Hl]; subst. destruct H1 as [->|H1].
    + apply Hy. apply in_or_app; right; exact H2.
    + exact (IH Hl H1).
Qed.

(** Galette-only: [stack_to_lab_lab_pres] with [Prop] lists.  [LP L S lo
    hi]: the labels [L] are distinct and each one is in [S] or has its
    second component in [[lo, hi)]. *)
Definition lp_ok (n : N) (L : list (N * N)) : Prop :=
  Forall (fun '(l1, l2) => l1 = n /\ l2 <> 0 /\ l2 <> 1) L.

Definition LP (L S : list (N * N)) (lo hi : N) : Prop :=
  NoDup L /\ (forall x, In x L -> In x S \/ (lo <= SND x /\ SND x < hi)).

Lemma LP_nil S lo hi : LP [] S lo hi.
Proof. split; [constructor|intros ? []]. Qed.

Lemma LP_fresh x S lo hi : lo <= SND x -> SND x < hi -> LP [x] S lo hi.
Proof. intros H1 H2; split; [repeat constructor; intros []|intros y [<-|[]]; right; lia]. Qed.

Lemma LP_src x S lo hi : In x S -> LP [x] S lo hi.
Proof. intros H; split; [repeat constructor; intros []|intros y [<-|[]]; left; exact H]. Qed.

Lemma LP_mono L S S' lo hi lo' hi' :
  LP L S lo hi -> (forall x, In x S -> In x S') -> lo' <= lo -> hi <= hi' -> LP L S' lo' hi'.
Proof.
  intros [H1 H2] HS Hl Hh; split; [exact H1|]. intros x Hx.
  destruct (H2 x Hx) as [H|H]; [left; auto|right; lia].
Qed.

Lemma LP_app L1 L2 S1 S2 S lo1 hi1 lo2 hi2 lo hi B :
  LP L1 S1 lo1 hi1 -> LP L2 S2 lo2 hi2 ->
  (forall x, In x S1 -> In x S2 -> False) ->
  (forall x, In x S1 -> SND x < B) -> (forall x, In x S2 -> SND x < B) ->
  B <= lo1 -> B <= lo2 -> (hi1 <= lo2 \/ hi2 <= lo1) ->
  (forall x, In x S1 -> In x S) -> (forall x, In x S2 -> In x S) ->
  lo <= lo1 -> lo <= lo2 -> hi1 <= hi -> hi2 <= hi ->
  LP (L1 ++ L2) S lo hi.
Proof.
  intros [N1 C1] [N2 C2] Hd B1 B2 Hb1 Hb2 Hi S1S S2S Hl1 Hl2 Hh1 Hh2. split.
  - apply NoDup_app_sep; [exact N1|exact N2|]. intros x X1 X2.
    destruct (C1 x X1) as [Y1|Y1], (C2 x X2) as [Y2|Y2].
    + exact (Hd x Y1 Y2).
    + specialize (B1 x Y1); lia.
    + specialize (B2 x Y2); lia.
    + lia.
  - intros x Hx. apply in_app_iff in Hx as [Hx|Hx].
    + destruct (C1 x Hx) as [Y|Y]; [left; auto|right; lia].
    + destruct (C2 x Hx) as [Y|Y]; [left; auto|right; lia].
Qed.

Lemma lp_ok_app n L1 L2 : lp_ok n L1 -> lp_ok n L2 -> lp_ok n (L1 ++ L2).
Proof. intros; apply Forall_app; auto. Qed.

Lemma lp_ok_fresh n m : 2 <= m -> lp_ok n [(n, m)].
Proof. intros H; constructor; [split; [reflexivity|lia]|constructor]. Qed.

Lemma lp_ok_nil n : lp_ok n [].
Proof. constructor. Qed.

Lemma extract_labels_compile_jump (d : N + N) (rest : list (line a)) :
  labProps.extract_labels (@compile_jump a d :: rest) = labProps.extract_labels rest.
Proof. destruct d; reflexivity. Qed.

Lemma el_cj (d : N + N) (rest : list (line a)) :
  match @compile_jump a d with
  | Label l1 l2 _ => (l1, l2) :: labProps.extract_labels rest
  | _ => labProps.extract_labels rest
  end = labProps.extract_labels rest.
Proof. destruct d; reflexivity. Qed.

Lemma el_cj_nil (d : N + N) :
  match @compile_jump a d with Label l1 l2 _ => [(l1, l2)] | _ => [] end = [].
Proof. destruct d; reflexivity. Qed.

Lemma el_cons_cj (y : line a) (d : N + N) rest :
  labProps.extract_labels (y :: compile_jump d :: rest) = labProps.extract_labels (y :: rest).
Proof. destruct d, y; reflexivity. Qed.

Ltac lx_norm :=
  rewrite ?append_Append, ?append_List, ?labProps.extract_labels_append;
  rewrite ?el_cons_cj, ?extract_labels_compile_jump;
  cbn [labProps.extract_labels app];
  rewrite ?el_cj, ?el_cj_nil, ?labProps.extract_labels_append;
  cbn [labProps.extract_labels app].

Ltac lp_in_split :=
  repeat match goal with
  | H : In _ (_ ++ _) |- _ => apply in_app_iff in H; destruct H as [H|H]
  | H : In _ (_ :: _) |- _ => destruct H as [H|H]
  | H : In _ [] |- _ => destruct H
  | H : (_, _) = ?x |- _ => is_var x; subst x
  | H : (_, _) = (_, _) |- _ => injection H; clear H; intros
  end.

Ltac lp_classify :=
  repeat match goal with
  | H : In ?x (labProps.extract_labels (append ?c)), B : LP (labProps.extract_labels (append ?c)) _ _ _ |- _ =>
      let Y := fresh "Y" in destruct (proj2 B x H) as [Y|Y]; clear H
  end.

Ltac lp_finish Hnl :=
  first
    [ match goal with
      | Hd : forall x, In x ?A -> In x ?B -> False, H1 : In ?y ?A, H2 : In ?y ?B |- _ => exact (Hd y H1 H2)
      | Hd : forall x, In x ?A -> In x ?B -> False, H1 : In ?y ?B, H2 : In ?y ?A |- _ => exact (Hd y H2 H1)
      end
    | (repeat match goal with H : In ?x (extract_labels ?q) |- _ => pose proof (Hnl q x H); clear H end);
      cbn [SND snd] in *; lia ].

Ltac lp_nodup Hnl :=
  repeat first
    [ apply NoDup_nil
    | match goal with B : LP ?L _ _ _ |- NoDup ?L => exact (proj1 B) end
    | apply NoDup_cons; [intros ?; lp_in_split; lp_classify; lp_finish Hnl|]
    | apply NoDup_app_sep; [| |let x := fresh "x" in let H1 := fresh "H" in let H2 := fresh "H" in
                               intros x H1 H2; lp_in_split; lp_classify; lp_finish Hnl] ].

Ltac lp_cls Hnl :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; lp_in_split; lp_classify;
  first [ left; repeat (apply in_app_iff; first [left; assumption|right]); assumption
        | left; repeat (first [left; reflexivity | right]); fail
        | right; cbn [SND snd]; lia
        | exfalso; lp_finish Hnl ].

Ltac lp_ok_tac :=
  repeat first [ assumption | apply lp_ok_nil | apply lp_ok_app
               | apply Forall_cons; [split; [reflexivity|lia]|] ].

Lemma lab_pres_aux n : forall (p : prog a) nl cs bs,
  lp_ok n (extract_labels p) -> NoDup (extract_labels p) -> stack_alloc.next_lab p 2 <= nl ->
  forall cp nr nl', flatten false p n nl cs bs = (cp, (nr, nl')) ->
  lp_ok n (labProps.extract_labels (append cp)) /\
  LP (labProps.extract_labels (append cp)) (extract_labels p) nl nl' /\
  nl <= nl'.
Proof.
  assert (Hnl : forall (q : prog a) e, In e (extract_labels q) -> SND e < stack_alloc.next_lab q 2).
  { intros q e He; apply stack_allocProof.extract_labels_next_lab; unfold is_true; rewrite MEM_In; exact He. }
  intros p; induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|c0 r ri p1 p2 IH1 IH2|p IH|p Hp]
    using prog_nested_ind; intros nl cs bs HF HD HN cp nr nl' Ef;
    rewrite stack_allocProof.next_lab_thm in HN; rewrite ?MAX_max in HN;
    cbn [flatten] in Ef.
  - destruct ret as [[p1 [lr [l1 l2]]]|].
    2:{ injection Ef as <- <- <-. lx_norm. split; [apply lp_ok_nil|split; [apply LP_nil|lia]]. }
    specialize (Hr p1 _ eq_refl). cbn [extract_labels] in HF, HD |- *.
    destruct (flatten false p1 n nl cs bs) as [xs [nr1 m1]] eqn:E1.
    pose proof (Hnl p1) as Hn1.
    destruct h as [[p2 [k1 k2]]|]; cbn beta iota in HN, Ef |- *; rewrite ?MAX_max in HN.
    + specialize (Hh p2 _ eq_refl). pose proof (Hnl p2) as Hn2. cbn [app] in HF, HD.
      destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:E2.
      injection Ef as <- <- <-.
      inversion HF as [|? ? Hl1 HF1]; subst. inversion HF1 as [|? ? Hk1 HF2]; subst.
      apply Forall_app in HF2 as [HFp1 HFp2].
      inversion HD as [|? ? Hn1' HD1]; subst. inversion HD1 as [|? ? Hn2' HD2]; subst.
      destruct (NoDup_app_inv _ _ HD2) as (HDp1 & HDp2 & Hdis).
      destruct (Hr nl cs bs HFp1 HDp1 ltac:(lia) _ _ _ E1) as (A1 & B1 & D1).
      destruct (Hh m1 cs bs HFp2 HDp2 ltac:(lia) _ _ _ E2) as (A2 & B2 & D2).
      lx_norm.
      assert (Hnot1 : ~ In (l1, l2) (labProps.extract_labels (append xs) ++ (k1, k2) ::
                         labProps.extract_labels (append ys) ++ [(n, m2)])).
      { intros Hin. apply in_app_iff in Hin as [Hin|[Hin|Hin]].
        - destruct (proj2 B1 _ Hin) as [Y|Y]; [apply Hn1'; right; apply in_app_iff; auto|cbn in Y; lia].
        - apply Hn1'; left; exact Hin.
        - apply in_app_iff in Hin as [Hin|[Hin|[]]].
          + destruct (proj2 B2 _ Hin) as [Y|Y]; [apply Hn1'; right; apply in_app_iff; auto|cbn in Y; lia].
          + injection Hin as -> ->. lia. }
      assert (Hnot2 : ~ In (k1, k2) (labProps.extract_labels (append ys) ++ [(n, m2)])).
      { intros Hin. apply in_app_iff in Hin as [Hin|[Hin|[]]].
        - destruct (proj2 B2 _ Hin) as [Y|Y]; [apply Hn2'; apply in_app_iff; auto|cbn in Y; lia].
        - injection Hin as -> ->. lia. }
      assert (Hnot3 : forall x, In x (labProps.extract_labels (append xs)) ->
                In x ((k1, k2) :: labProps.extract_labels (append ys) ++ [(n, m2)]) -> False).
      { intros x X1 X2. destruct (proj2 B1 _ X1) as [Y1|Y1].
        - destruct X2 as [<-|X2]; [apply Hn2'; apply in_app_iff; auto|].
          apply in_app_iff in X2 as [X2|[<-|[]]].
          + destruct (proj2 B2 _ X2) as [Y2|Y2]; [exact (Hdis x Y1 Y2)|specialize (Hn1 x Y1); lia].
          + specialize (Hn1 _ Y1); cbn in Hn1; lia.
        - destruct X2 as [<-|X2]; [cbn in Y1; lia|].
          apply in_app_iff in X2 as [X2|[<-|[]]].
          + destruct (proj2 B2 _ X2) as [Y2|Y2]; [specialize (Hn2 x Y2); lia|lia].
          + cbn in Y1; lia. }
      assert (Hnot4 : ~ In (n, m2) (labProps.extract_labels (append ys))).
      { intros Hin. destruct (proj2 B2 _ Hin) as [Y|Y]; [specialize (Hn2 _ Y); cbn in Hn2; lia|cbn in Y; lia]. }
      repeat split.
      * constructor; [exact Hl1|]. apply lp_ok_app; [exact A1|]. constructor; [exact Hk1|].
        apply lp_ok_app; [exact A2|apply lp_ok_fresh; lia].
      * constructor; [exact Hnot1|]. apply NoDup_app_sep; [exact (proj1 B1)| |exact Hnot3].
        constructor; [exact Hnot2|]. apply NoDup_app_sep; [exact (proj1 B2)|repeat constructor; intros []|].
        intros x X1 [<-|[]]. exact (Hnot4 X1).
      * intros x Hx. destruct Hx as [<-|Hx]; [left; left; reflexivity|].
        apply in_app_iff in Hx as [Hx|[<-|Hx]].
        -- destruct (proj2 B1 _ Hx) as [Y|Y]; [left; right; right; apply in_app_iff; auto|right; lia].
        -- left; right; left; reflexivity.
        -- apply in_app_iff in Hx as [Hx|[<-|[]]].
           ++ destruct (proj2 B2 _ Hx) as [Y|Y]; [left; right; right; apply in_app_iff; auto|right; lia].
           ++ right; cbn; lia.
      * lia.
    + injection Ef as <- <- <-. cbn [app] in HF, HD.
      inversion HF as [|? ? Hl1 HFp1]; subst. inversion HD as [|? ? Hn1' HDp1]; subst.
      destruct (Hr nl cs bs HFp1 HDp1 ltac:(lia) _ _ _ E1) as (A1 & B1 & D1).
      lx_norm. repeat split.
      * constructor; [exact Hl1|exact A1].
      * constructor; [|exact (proj1 B1)]. intros Hin.
        destruct (proj2 B1 _ Hin) as [Y|Y]; [exact (Hn1' Y)|cbn in Y; lia].
      * intros x [<-|Hx]; [left; left; reflexivity|].
        destruct (proj2 B1 _ Hx) as [Y|Y]; [left; right; exact Y|right; exact Y].
      * exact D1.
  - (* Seq *)
    destruct (flatten false p1 n nl cs bs) as [xs [nr1 m1]] eqn:E1.
    destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:E2.
    injection Ef as <- <- <-. cbn [extract_labels] in HF, HD |- *.
    unfold lp_ok in HF. apply Forall_app in HF as [HF1 HF2].
    destruct (NoDup_app_inv _ _ HD) as (HD1 & HD2 & Hdis).
    destruct (IH1 nl cs bs HF1 HD1 ltac:(lia) _ _ _ E1) as (A1 & B1 & D1).
    destruct (IH2 m1 cs bs HF2 HD2 ltac:(lia) _ _ _ E2) as (A2 & B2 & D2).
    lx_norm. split; [apply lp_ok_app; assumption|]. split; [|lia].
    eapply (LP_app _ _ _ _ _ nl m1 m1 m2 nl m2 nl B1 B2 Hdis); try lia.
    + intros x Hx; specialize (Hnl p1 x Hx); lia.
    + intros x Hx; specialize (Hnl p2 x Hx); lia.
    + intros x Hx; apply in_app_iff; auto.
    + intros x Hx; apply in_app_iff; auto.
  - (* If *)
    destruct (flatten false p1 n nl cs bs) as [xs [nr1 m1]] eqn:E1.
    destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:E2.
    cbn [extract_labels] in HF, HD |- *.
    unfold lp_ok in HF. apply Forall_app in HF as [HF1 HF2].
    destruct (NoDup_app_inv _ _ HD) as (HD1 & HD2 & Hdis).
    destruct (IH1 nl cs bs HF1 HD1 ltac:(lia) _ _ _ E1) as (A1 & B1 & D1).
    destruct (IH2 m1 cs bs HF2 HD2 ltac:(lia) _ _ _ E2) as (A2 & B2 & D2).
    pose proof (next_lab_non_zero p1).
    destruct (is_Skip p1), (is_Skip p2), nr1, nr2; cbn in Ef; injection Ef as <- <- <-; lx_norm;
      (split; [lp_ok_tac|split; [split; [lp_nodup Hnl|lp_cls Hnl]|lia]]).
  - (* Loop *)
    destruct (flatten false p n (nl + 2) (nl :: cs) ((nl + 1) :: bs)) as [xs [nr1 m1]] eqn:E1.
    injection Ef as <- <- <-. cbn [extract_labels] in HF, HD |- *.
    destruct (IH (nl + 2) (nl :: cs) ((nl + 1) :: bs) HF HD ltac:(lia) _ _ _ E1) as (A1 & B1 & D1).
    pose proof (next_lab_non_zero p).
    lx_norm. split; [lp_ok_tac|split; [split; [lp_nodup Hnl|lp_cls Hnl]|lia]].
  - (* others *)
    destruct p; try contradiction; cbn [flatten] in Ef; injection Ef as <- <- <-; lx_norm;
      cbn [extract_labels] in *;
      (split; [lp_ok_tac|split; [split; [lp_nodup Hnl|lp_cls Hnl]|lia]]).
Qed.


Lemma lp_ok_EVERY n L :
  EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0) && negb (l2 =? 1)) L = true <-> lp_ok n L.
Proof.
  unfold lp_ok. rewrite EVERY_Forall. split; intros H; eapply Forall_impl; try exact H;
    intros [l1 l2]; cbn; rewrite !Bool.andb_true_iff, !Bool.negb_true_iff, N.eqb_eq, !N.eqb_neq; tauto.
Qed.

Lemma EVERY_ne0 n L :
  EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0)) L = true <->
  Forall (fun '(l1, l2) => l1 = n /\ l2 <> 0) L.
Proof.
  rewrite EVERY_Forall. split; intros H; eapply Forall_impl; try exact H;
    intros [l1 l2]; cbn; rewrite !Bool.andb_true_iff, !Bool.negb_true_iff, N.eqb_eq, !N.eqb_neq; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_to_lab_lab_pres" 1028 *)
Theorem stack_to_lab_lab_pres : forall (t : bool) (p : prog a) n nl cs bs,
  EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0) && negb (l2 =? 1)) (extract_labels p) /\
  ALL_DISTINCT (extract_labels p) /\ ~ t /\ stack_alloc.next_lab p 2 <= nl ->
  let '(cp, (nr, nl')) := flatten t p n nl cs bs in
    EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0) && negb (l2 =? 1))
      (labProps.extract_labels (append cp)) /\
    ALL_DISTINCT (labProps.extract_labels (append cp)) /\
    (forall lab, MEM lab (labProps.extract_labels (append cp)) ->
       MEM lab (extract_labels p) \/ (nl <= SND lab /\ SND lab < nl')) /\
    nl <= nl'.
Proof.
  intros t p n nl cs bs (H1 & H2 & H3 & H4). destruct t; [exfalso; apply H3; reflexivity|].
  destruct (flatten false p n nl cs bs) as [cp [nr nl']] eqn:E.
  apply lp_ok_EVERY in H1. apply ALL_DISTINCT_NoDup_list in H2.
  destruct (lab_pres_aux n p nl cs bs H1 H2 H4 cp nr nl' E) as (A & [B C] & D).
  split; [apply lp_ok_EVERY, A|]. split; [apply ALL_DISTINCT_NoDup_list, B|]. split; [|exact D].
  intros lab Hl. unfold is_true in *. rewrite MEM_In in Hl |- *. exact (C lab Hl).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_T_F" *)
Theorem flatten_T_F : forall (p_2 : prog a) p_1 m cs bs,
  ~ is_Seq p_2 -> flatten true p_2 p_1 m cs bs = flatten false p_2 p_1 m cs bs.
Proof. intros p_2 p_1 m cs bs H; destruct p_2; try reflexivity. exfalso; apply H; reflexivity. Qed.

Lemma lab_pres_T_aux n (p : prog a) nl cs bs :
  lp_ok n (extract_labels p) -> NoDup (extract_labels p) -> stack_alloc.next_lab p 2 <= nl ->
  forall cp nr nl', flatten true p n nl cs bs = (cp, (nr, nl')) ->
  Forall (fun '(l1, l2) => l1 = n /\ l2 <> 0) (labProps.extract_labels (append cp)) /\
  NoDup (labProps.extract_labels (append cp)) /\
  (forall lab, In lab (labProps.extract_labels (append cp)) ->
     In lab (extract_labels p) \/ SND lab < nl') /\
  nl <= nl' /\
  (is_Seq p = false -> forall lab, In lab (labProps.extract_labels (append cp)) ->
     In lab (extract_labels p) \/ nl <= SND lab).
Proof.
  intros HF HD HN cp nr nl' Ef.
  assert (Hnl : forall (q : prog a) e, In e (extract_labels q) -> SND e < stack_alloc.next_lab q 2).
  { intros q e He; apply stack_allocProof.extract_labels_next_lab; unfold is_true; rewrite MEM_In; exact He. }
  pose proof (next_lab_non_zero p) as Hnz.
  destruct (is_Seq p) eqn:Es.
  - destruct p; try discriminate. cbn [flatten] in Ef.
    rewrite stack_allocProof.next_lab_thm, MAX_max in HN.
    pose proof (next_lab_non_zero p1). pose proof (next_lab_non_zero p2).
    destruct (flatten false p1 n nl cs bs) as [xs [nr1 m1]] eqn:E1.
    destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:E2.
    injection Ef as <- <- <-. cbn [extract_labels] in HF, HD |- *.
    unfold lp_ok in HF. apply Forall_app in HF as [HF1 HF2].
    destruct (NoDup_app_inv _ _ HD) as (HD1 & HD2 & Hdis).
    destruct (lab_pres_aux n p1 nl cs bs HF1 HD1 ltac:(lia) _ _ _ E1) as (A1 & B1 & D1).
    destruct (lab_pres_aux n p2 m1 cs bs HF2 HD2 ltac:(lia) _ _ _ E2) as (A2 & B2 & D2).
    lx_norm. rewrite <- ?app_assoc; cbn [app].
    assert (Hd1 : ~ In (n, 1) (labProps.extract_labels (append xs))).
    { intros Hin. destruct (proj2 B1 _ Hin) as [Y|Y]; [|cbn in Y; lia].
      unfold lp_ok in HF1. rewrite List.Forall_forall in HF1. specialize (HF1 _ Y). cbn in HF1. lia. }
    assert (Hd2 : ~ In (n, 1) (labProps.extract_labels (append ys))).
    { intros Hin. destruct (proj2 B2 _ Hin) as [Y|Y]; [|cbn in Y; lia].
      unfold lp_ok in HF2. rewrite List.Forall_forall in HF2. specialize (HF2 _ Y). cbn in HF2. lia. }
    split; [|split; [|split; [|split; [lia|intros; discriminate]]]].
    + unfold lp_ok in A1, A2. apply Forall_app; split; [eapply Forall_impl; [|exact A1]; intros [];
        tauto|constructor; [split; [reflexivity|lia]|eapply Forall_impl; [|exact A2]; intros []; tauto]].
    + apply NoDup_app_sep; [exact (proj1 B1)|constructor; [exact Hd2|exact (proj1 B2)]|].
      intros x X1 [<-|X2]; [exact (Hd1 X1)|].
      destruct (proj2 B1 _ X1) as [Y1|Y1], (proj2 B2 _ X2) as [Y2|Y2].
      * exact (Hdis _ Y1 Y2).
      * specialize (Hnl _ _ Y1); lia.
      * specialize (Hnl _ _ Y2); lia.
      * lia.
    + intros lab Hl. apply in_app_iff in Hl as [Hl|[<-|Hl]].
      * destruct (proj2 B1 _ Hl) as [Y|Y]; [left; apply in_app_iff; auto|right; lia].
      * right; cbn; lia.
      * destruct (proj2 B2 _ Hl) as [Y|Y]; [left; apply in_app_iff; auto|right; lia].
  - rewrite flatten_T_F in Ef by (rewrite Es; discriminate).
    destruct (lab_pres_aux n p nl cs bs HF HD HN cp nr nl' Ef) as (A & [B C] & D).
    split; [|split; [exact B|split; [|split; [exact D|]]]].
    + eapply Forall_impl; [|exact A]; intros []; tauto.
    + intros lab Hl. destruct (C lab Hl) as [Y|Y]; [left; exact Y|right; lia].
    + intros _ lab Hl. destruct (C lab Hl) as [Y|Y]; [left; exact Y|right; lia].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_to_lab_lab_pres_T" *)
Theorem stack_to_lab_lab_pres_T : forall (t : bool) (p : prog a) n nl cs bs,
  EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0) && negb (l2 =? 1)) (extract_labels p) /\
  ALL_DISTINCT (extract_labels p) /\ t /\ stack_alloc.next_lab p 2 <= nl ->
  let '(cp, (nr, nl')) := flatten t p n nl cs bs in
    EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0)) (labProps.extract_labels (append cp)) /\
    ALL_DISTINCT (labProps.extract_labels (append cp)) /\
    (forall lab, MEM lab (labProps.extract_labels (append cp)) ->
       MEM lab (extract_labels p) \/ SND lab < nl') /\
    nl <= nl'.
Proof.
  intros t p n nl cs bs (H1 & H2 & H3 & H4). destruct t; [|discriminate H3].
  destruct (flatten true p n nl cs bs) as [cp [nr nl']] eqn:E.
  apply lp_ok_EVERY in H1. apply ALL_DISTINCT_NoDup_list in H2.
  destruct (lab_pres_T_aux n p nl cs bs H1 H2 H4 cp nr nl' E) as (A & B & C & D & _).
  split; [apply EVERY_ne0, A|]. split; [apply ALL_DISTINCT_NoDup_list, B|]. split; [|exact D].
  intros lab Hl. unfold is_true in *. rewrite MEM_In in Hl |- *. exact (C lab Hl).
Qed.

End LabPres.

Section LabelsOk2.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "prog_to_section_labels_ok" *)
Theorem prog_to_section_labels_ok : forall prog : list (N * stackLang.prog a),
  EVERY (fun '(n, p) =>
           let labs := extract_labels p in
           EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0) && negb (l2 =? 1)) labs &&
           ALL_DISTINCT labs) prog /\
  ALL_DISTINCT (MAP FST prog) ->
  labels_ok (MAP prog_to_section prog).
Proof.
  intros prog [He Hd]. split; [rewrite MAP_prog_to_section_FST; exact Hd|].
  unfold is_true in *. apply EVERY_Forall in He. apply EVERY_Forall. apply Forall_map.
  eapply Forall_impl; [|exact He]. intros [n p] H. cbn zeta in H.
  apply Bool.andb_true_iff in H as [H1 H2].
  apply lp_ok_EVERY in H1. apply ALL_DISTINCT_NoDup_list in H2.
  rewrite prog_to_section_eq.
  destruct (flatten true p n (stack_alloc.next_lab p 2) [] []) as [cp [nr m]] eqn:E.
  cbn [FST SND fst snd].
  destruct (lab_pres_T_aux n p (stack_alloc.next_lab p 2) [] [] H1 H2 ltac:(lia) cp nr m E)
    as (A & B & C & D & F).
  pose proof (next_lab_non_zero p) as Hnz.
  assert (Hnl : forall e, In e (extract_labels p) -> SND e < stack_alloc.next_lab p 2).
  { intros e He'; apply stack_allocProof.extract_labels_next_lab; unfold is_true; rewrite MEM_In; exact He'. }
  rewrite labProps.extract_labels_append. cbn [labProps.extract_labels].
  apply Bool.andb_true_iff. split.
  - apply EVERY_ne0. apply Forall_app. split; [exact A|].
    constructor; [|constructor]. destruct (is_Seq p); split; [reflexivity|lia|reflexivity|lia].
  - apply ALL_DISTINCT_NoDup_list. apply NoDup_app_sep; [exact B|repeat constructor; intros []|].
    intros x Hx [<-|[]].
    destruct (is_Seq p) eqn:Es.
    + destruct (C _ Hx) as [Y|Y]; [specialize (Hnl _ Y); cbn in Hnl; lia|cbn in Y; lia].
    + destruct (F eq_refl _ Hx) as [Y|Y].
      * unfold lp_ok in H1. rewrite List.Forall_forall in H1. specialize (H1 _ Y). cbn in H1. lia.
      * cbn in Y; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "NOT_MEM_find_lab_IMP" *)
Theorem NOT_MEM_find_lab_IMP : forall bs n, ~ MEM (find_lab n bs) bs -> find_lab n bs = 0.
Proof.
  intros bs n H. unfold find_lab in *. destruct (oEL n bs) as [k|] eqn:E; [|reflexivity].
  exfalso; apply H. clear H. unfold is_true; rewrite MEM_In.
  revert n E; induction bs as [|x bs IH]; intros n E; [discriminate|].
  cbn in E. destruct (n =? 0); [injection E as ->; left; reflexivity|right; exact (IH _ E)].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "is_some_loc_to_pc_prefix" *)
Theorem is_some_loc_to_pc_prefix : forall n k (c1 c2 : labLang.prog a),
  IS_SOME (loc_to_pc n k c1) /\ isPREFIX c1 c2 -> IS_SOME (loc_to_pc n k c2).
Proof.
  intros n k c1 c2 [H Hp]. destruct (loc_to_pc n k c1) as [v|] eqn:E; [|discriminate].
  rewrite (loc_to_pc_isPREFIX n k c1 v c2 (conj E Hp)). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "every_is_some_loc_to_pc_prefix" *)
Theorem every_is_some_loc_to_pc_prefix : forall n cs (c1 c2 : labLang.prog a),
  EVERY (fun k => IS_SOME (loc_to_pc n k c1)) cs /\ isPREFIX c1 c2 ->
  EVERY (fun k => IS_SOME (loc_to_pc n k c2)) cs.
Proof.
  intros n cs c1 c2 [H Hp]. unfold is_true in *. rewrite EVERY_Forall in H |- *.
  eapply Forall_impl; [|exact H]. intros k Hk. exact (is_some_loc_to_pc_prefix n k c1 c2 (conj Hk Hp)).
Qed.

End LabelsOk2.


(** ** Correctness of [flatten] *)

Section LabSteps.
Context {a : N} {c ffi_t : Type}.
Implicit Types (t : labSem.state a c ffi_t).

Lemma lev_fetch t x : asm_fetch t = SOME x -> asm_fetch_aux (pc t) (labSem.code t) = SOME x.
Proof. exact (fun H => H). Qed.

Lemma lev_inst t i b l0 :
  labSem.clock t <> 0 -> asm_fetch t = SOME (Asm (Asmi (asm.Inst i)) b l0) ->
  labSem.evaluate t =
  if failed (asm_inst i t) then (targetSem.Error, t)
  else labSem.evaluate (inc_pc (labSem.dec_clock (asm_inst i t))).
Proof. intros Hc Hf. rewrite labSem.evaluate_def, (proj2 (N.eqb_neq _ _) Hc), Hf. reflexivity. Qed.

Lemma lev_jumpreg t r b l0 :
  labSem.clock t <> 0 -> asm_fetch t = SOME (Asm (Asmi (JumpReg r)) b l0) ->
  labSem.evaluate t =
  match read_reg r t with
  | Loc n1 n2 =>
      match loc_to_pc n1 n2 (labSem.code t) with
      | NONE => (targetSem.Error, t)
      | SOME p => labSem.evaluate (upd_pc p (labSem.dec_clock t))
      end
  | _ => (targetSem.Error, t)
  end.
Proof. intros Hc Hf. rewrite labSem.evaluate_def, (proj2 (N.eqb_neq _ _) Hc), Hf. reflexivity. Qed.

Lemma lev_jump t l1 l2 w b l0 :
  labSem.clock t <> 0 -> asm_fetch t = SOME (LabAsm (Jump (Lab l1 l2)) w b l0) ->
  labSem.evaluate t =
  match loc_to_pc l1 l2 (labSem.code t) with
  | NONE => (targetSem.Error, t)
  | SOME p => labSem.evaluate (upd_pc p (labSem.dec_clock t))
  end.
Proof. intros Hc Hf. rewrite labSem.evaluate_def, (proj2 (N.eqb_neq _ _) Hc), Hf. reflexivity. Qed.

Lemma lev_jumpcmp t c0 r ri l1 l2 w b l0 :
  labSem.clock t <> 0 -> asm_fetch t = SOME (LabAsm (JumpCmp c0 r ri (Lab l1 l2)) w b l0) ->
  labSem.evaluate t =
  match wordSem.word_cmp c0 (read_reg r t) (reg_imm ri t) with
  | NONE => (targetSem.Error, t)
  | SOME false => labSem.evaluate (inc_pc (labSem.dec_clock t))
  | SOME true =>
      match loc_to_pc l1 l2 (labSem.code t) with
      | NONE => (targetSem.Error, t)
      | SOME p => labSem.evaluate (upd_pc p (labSem.dec_clock t))
      end
  end.
Proof. intros Hc Hf. rewrite labSem.evaluate_def, (proj2 (N.eqb_neq _ _) Hc), Hf. reflexivity. Qed.

Lemma lev_locvalue t r l1 l2 w b l0 :
  labSem.clock t <> 0 -> asm_fetch t = SOME (LabAsm (labLang.LocValue r (Lab l1 l2)) w b l0) ->
  labSem.evaluate t =
  match loc_to_pc l1 l2 (labSem.code t) with
  | NONE => (targetSem.Error, t)
  | SOME _ => labSem.evaluate (inc_pc (labSem.dec_clock (upd_reg r (Loc l1 l2) t)))
  end.
Proof.
  intros Hc Hf. rewrite labSem.evaluate_def, (proj2 (N.eqb_neq _ _) Hc), Hf. cbn [get_pc_value lab_to_loc].
  destruct (loc_to_pc l1 l2 (labSem.code t)); reflexivity.
Qed.

Lemma lev_halt t w b l0 :
  labSem.clock t <> 0 -> asm_fetch t = SOME (LabAsm labLang.Halt w b l0) ->
  labSem.evaluate t =
  match labSem.regs t (ptr_reg t) with
  | Word w => if bool_decide (w = n2w 0) then (targetSem.Halt Success, t)
              else (targetSem.Halt Resource_limit_hit, t)
  | _ => (targetSem.Error, t)
  end.
Proof. intros Hc Hf. rewrite labSem.evaluate_def, (proj2 (N.eqb_neq _ _) Hc), Hf. reflexivity. Qed.

Lemma lset_clock_fetch t k : asm_fetch (labSem.set_clock k t) = asm_fetch t.
Proof. reflexivity. Qed.

Lemma lset_clock_clock t k : labSem.clock (labSem.set_clock k t) = k.
Proof. reflexivity. Qed.

Lemma lset_clock_set_clock t k k' : labSem.set_clock k (labSem.set_clock k' t) = labSem.set_clock k t.
Proof. reflexivity. Qed.

Lemma lset_clock_same t : labSem.set_clock (labSem.clock t) t = t.
Proof. destruct t; reflexivity. Qed.

Lemma lupd_pc_clock t p k :
  upd_pc p (labSem.dec_clock (labSem.set_clock k t)) = labSem.set_clock (k - 1) (upd_pc p t).
Proof. reflexivity. Qed.

Lemma lupd_reg_clock t r v k :
  upd_reg r v (labSem.set_clock k t) = labSem.set_clock k (upd_reg r v t).
Proof. reflexivity. Qed.

Lemma lset_cb_clock t cb k :
  labSem.set_code_buffer cb (labSem.set_clock k t) = labSem.set_clock k (labSem.set_code_buffer cb t).
Proof. reflexivity. Qed.

Lemma linc_pc_clock t k :
  inc_pc (labSem.dec_clock (labSem.set_clock k t)) = labSem.set_clock (k - 1) (inc_pc t).
Proof. reflexivity. Qed.

End LabSteps.

Section FlattenCorrect.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : stackSem.state a c ffi_t) (t : labSem.state a c ffi_t).

(** Galette-only: the conclusion of [flatten_correct] for given [ck], [t2]. *)
Definition fc_post (r : option (result a)) s2 t1 t2 (ck : N) (lines : list (line a))
    (n : N) (cs bs : list N) : Prop :=
  match halt_view r with
  | SOME res =>
      labSem.evaluate (labSem.set_clock (labSem.clock t1 + ck) t1) = (res, t2) /\
      labSem.ffi t2 = ffi s2
  | NONE =>
      (forall ck1, labSem.evaluate (labSem.set_clock (labSem.clock t1 + ck + ck1) t1) =
                   labSem.evaluate (labSem.set_clock (labSem.clock t2 + ck1) t2)) /\
      len_reg t2 = len_reg t1 /\
      ptr_reg t2 = ptr_reg t1 /\
      len2_reg t2 = len2_reg t1 /\
      ptr2_reg t2 = ptr2_reg t1 /\
      link_reg t2 = link_reg t1 /\
      isPREFIX (labSem.code t1) (labSem.code t2) /\
      match OPTION_MAP (fun w => result_view w n cs bs) r with
      | NONE =>
          pc t2 = pc t1 + LENGTH (FILTER (negb ∘ is_Label) lines) /\
          state_rel s2 t2
      | SOME (Vloc n1 n2) =>
          (forall n, IS_SOME (lookup n (code s2)) -> IS_SOME (loc_to_pc n 0 (labSem.code t2))) /\
          forall w, loc_to_pc n1 n2 (labSem.code t2) = SOME w -> w = pc t2 /\ state_rel s2 t2
      | SOME (Vcont n1 n2) =>
          state_rel s2 t2 /\
          code_installed (pc t2) [LabAsm (Jump (Lab n1 n2)) (n2w 0) [] 0] (labSem.code t2)
      | SOME Vtimeout => labSem.ffi t2 = ffi s2 /\ labSem.clock t2 = 0
      | _ => False
      end
  end.

Definition FC (x : prog a * stackSem.state a c ffi_t) : Prop :=
  forall (t : bool) r s2 n l cs bs t1,
    evaluate x = (r, s2) -> r <> SOME Error -> state_rel (snd x) t1 ->
    call_args (fst x) (ptr_reg t1) (len_reg t1) (ptr2_reg t1) (len2_reg t1) (link_reg t1) ->
    code_installed (pc t1) (append (FST (flatten t (fst x) n l cs bs))) (labSem.code t1) ->
    EVERY (fun k => IS_SOME (loc_to_pc n k (labSem.code t1))) (cs ++ bs ++ [0]) ->
    exists ck t2, fc_post r s2 t1 t2 ck (append (FST (flatten t (fst x) n l cs bs))) n cs bs.

Ltac post_split :=
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).

Ltac fc_intro :=
  let t := fresh "t" in let r := fresh "r" in let s2 := fresh "s2" in let n := fresh "n" in
  let l := fresh "l" in let cs := fresh "cs" in let bs := fresh "bs" in let t1 := fresh "t1" in
  intros t r s2 n l cs bs t1 He Hr Hs Hca Hci Hev; cbn [fst snd] in *.

Lemma sr_clock s t : state_rel s t -> labSem.clock t = clock s.
Proof. intros H; sr_destruct H; exact Hclk. Qed.

Lemma sr_failed s t : state_rel s t -> failed t = false.
Proof. intros H; sr_destruct H; apply Bool.not_true_iff_false; exact Hfail. Qed.

Lemma sr_use s t : state_rel s t -> use_stack s = false /\ use_store s = false /\ use_alloc s = false.
Proof. intros H; sr_destruct H; repeat split; apply Bool.not_true_iff_false; assumption. Qed.

(** Programs that need [use_stack], [use_store] or [use_alloc] fail. *)
Lemma fc_error p s :
  match p with
  | Alloc _ | StoreConsts _ _ _ | Get _ _ | Set_ _ _ | OpCurrHeap _ _ _ | DataBufferWrite _ _
  | StackAlloc _ | StackFree _ | StackStore _ _ | StackStoreAny _ _ | StackLoad _ _
  | StackLoadAny _ _ | StackGetSize _ | StackSetSize _ | BitmapLoad _ _ => True
  | _ => False
  end -> FC (p, s).
Proof.
  intros Hp. fc_intro. destruct (sr_use _ _ Hs) as (Hus & Hust & Hua).
  rewrite evaluate_eqn in He.
  destruct p; try contradiction; cbn [evaluate_body] in He;
    rewrite ?Hus, ?Hust, ?Hua in He; cbn [negb orb andb] in He;
    injection He as <- <-; congruence.
Qed.

Lemma fc_Skip s : FC (Skip, s).
Proof.
  fc_intro. rewrite evaluate_eqn in He. cbn [evaluate_body] in He. injection He as <- <-.
  exists 0, t1. cbn [fc_post halt_view OPTION_MAP]. post_split;
    try reflexivity; try apply isPREFIX_REFL.
  - intros ck1; rewrite N.add_0_r; reflexivity.
  - split; [|exact Hs]. cbn [flatten FST fst]. rewrite append_List. cbn. lia.
Qed.


Ltac fl_norm H := cbn [flatten FST SND fst snd] in H; rewrite ?append_Append, ?append_List in H.

Lemma fc_Halt v s : FC (stackLang.Halt v, s).
Proof.
  fc_intro. rewrite evaluate_eqn in He. cbn [evaluate_body] in He.
  destruct (get_var v s) as [w|] eqn:Ev; injection He as <- <-; [|congruence].
  fl_norm Hci. ci_split.
  cbn [call_args] in Hca. apply bool_decide_spec in Hca. subst v.
  exists 1, (labSem.set_clock (labSem.clock t1 + 1) t1). cbn [fc_post halt_view].
  split.
  - rewrite (lev_halt _ (n2w 0) [] 0); [|cbn; lia|eassumption].
    cbn [labSem.regs labSem.set_clock ptr_reg]. unfold get_var in Ev. rewrite (sr_regs _ _ _ _ Hs Ev).
    destruct w as [w|]; cbn [halt_word_view]; [destruct (bool_decide _)|]; reflexivity.
  - sr_destruct Hs. lab_cbn. stk_fields. exact Hffi.
Qed.

Lemma fc_Inst i s : FC (stackLang.Inst i, s).
Proof.
  fc_intro. rewrite evaluate_eqn in He. cbn [evaluate_body] in He.
  destruct (inst i s) as [s'|] eqn:Ei; injection He as <- <-; [|congruence].
  fl_norm Hci. ci_split.
  pose proof (inst_correct i s s' t1 (conj Ei Hs)) as Hs'.
  pose proof (sr_failed _ _ Hs') as Hf.
  pose proof (asm_inst_consts i t1) as (Ip & Icd & Ick & Iffi & _ & _ & _ & _ & Iptr & Ilen & Iptr2 & Ilen2 & Ilink).
  exists 1, (inc_pc (asm_inst i t1)). cbn [fc_post halt_view OPTION_MAP]. post_split.
  - intros ck1. rewrite (lev_inst _ i [] 0); [|cbn; lia|eassumption].
    rewrite asm_inst_with_clock. cbn [failed labSem.set_clock]. rewrite Hf.
    rewrite linc_pc_clock. f_equal. cbn [inc_pc set_pc labSem.set_clock labSem.clock]. rewrite Ick.
    f_equal; lia.
  - exact Ilen.
  - exact Iptr.
  - exact Ilen2.
  - exact Iptr2.
  - exact Ilink.
  - cbn [inc_pc set_pc labSem.code]. rewrite Icd. apply isPREFIX_REFL.
  - split.
    + cbn [inc_pc set_pc pc]. rewrite Ip. cbn. lia.
    + sr_destruct Hs'. sr_split; try assumption.
Qed.


Lemma sr_code_loc s t n0 :
  state_rel s t -> IS_SOME (lookup n0 (code s)) -> IS_SOME (loc_to_pc n0 0 (labSem.code t)).
Proof.
  intros H Hl. sr_destruct H. destruct (lookup n0 (code s)) as [p|] eqn:E; [|discriminate].
  destruct (Hcode n0 p E) as [_ (pc0 & _ & Hpc)]. rewrite Hpc. reflexivity.
Qed.

(** A jump to [(L1, L2)] (Galette helper for [Return], [Raise], [Break]). *)
Lemma jump_post s t1 r lines n0 cs bs L1 L2 :
  state_rel s t1 ->
  OPTION_MAP (fun w => result_view w n0 cs bs) r = SOME (Vloc L1 L2) -> halt_view r = NONE ->
  (forall K, K <> 0 -> labSem.evaluate (labSem.set_clock K t1) =
     match loc_to_pc L1 L2 (labSem.code t1) with
     | NONE => (targetSem.Error, labSem.set_clock K t1)
     | SOME p => labSem.evaluate (upd_pc p (labSem.dec_clock (labSem.set_clock K t1)))
     end) ->
  exists ck t2, fc_post r s t1 t2 ck lines n0 cs bs.
Proof.
  intros Hs Hv Hh Hstep. unfold fc_post. rewrite Hh, Hv.
  destruct (loc_to_pc L1 L2 (labSem.code t1)) as [p|] eqn:El.
  - exists 1, (upd_pc p t1). post_split; try reflexivity; try apply isPREFIX_REFL.
    + intros ck1. rewrite Hstep by lia. rewrite lupd_pc_clock. f_equal. cbn. f_equal. lia.
    + split; [intros n1 Hn1; exact (sr_code_loc _ _ _ Hs Hn1)|].
      intros w Hw. cbn [upd_pc set_pc labSem.code pc] in Hw |- *. rewrite El in Hw. injection Hw as <-.
      split; [reflexivity|apply state_rel_with_pc, Hs].
  - exists 1, (labSem.set_clock (labSem.clock t1 + 1) t1). post_split; try reflexivity; try apply isPREFIX_REFL.
    + split; [intros n1 Hn1; exact (sr_code_loc _ _ _ Hs Hn1)|].
      intros w Hw. cbn [labSem.code labSem.set_clock] in Hw. rewrite El in Hw. discriminate.
Qed.

Lemma fc_Return n0 s : FC (Return n0, s).
Proof.
  fc_intro. rewrite evaluate_eqn in He. cbn [evaluate_body] in He.
  destruct (get_var n0 s) as [[w|l1 l2]|] eqn:Ev; injection He as <- <-; try congruence.
  fl_norm Hci. ci_split. unfold get_var in Ev. pose proof (sr_regs _ _ _ _ Hs Ev) as Er.
  apply (jump_post _ _ _ _ _ _ _ l1 l2 Hs); [reflexivity|reflexivity|].
  intros K HK. rewrite (lev_jumpreg _ n0 [] 0); [|exact HK|eassumption]. cbn [labSem.regs labSem.set_clock].
  rewrite Er. reflexivity.
Qed.

Lemma fc_Raise n0 s : FC (Raise n0, s).
Proof.
  fc_intro. rewrite evaluate_eqn in He. cbn [evaluate_body] in He.
  destruct (get_var n0 s) as [[w|l1 l2]|] eqn:Ev; injection He as <- <-; try congruence.
  fl_norm Hci. ci_split. unfold get_var in Ev. pose proof (sr_regs _ _ _ _ Hs Ev) as Er.
  apply (jump_post _ _ _ _ _ _ _ l1 l2 Hs); [reflexivity|reflexivity|].
  intros K HK. rewrite (lev_jumpreg _ n0 [] 0); [|exact HK|eassumption]. cbn [labSem.regs labSem.set_clock].
  rewrite Er. reflexivity.
Qed.

Lemma fc_Break k s : FC (stackLang.Break k, s).
Proof.
  fc_intro. rewrite evaluate_eqn in He. cbn [evaluate_body] in He. injection He as <- <-.
  fl_norm Hci. ci_split.
  apply (jump_post _ _ _ _ _ _ _ n (find_lab k bs) Hs); [reflexivity|reflexivity|].
  intros K HK. rewrite (lev_jump _ n (find_lab k bs) (n2w 0) [] 0); [|exact HK|eassumption].
  reflexivity.
Qed.

Lemma fc_Continue k s : FC (stackLang.Continue k, s).
Proof.
  fc_intro. rewrite evaluate_eqn in He. cbn [evaluate_body] in He. injection He as <- <-.
  fl_norm Hci.
  exists 0, t1. unfold fc_post. cbn [halt_view OPTION_MAP result_view].
  post_split; try reflexivity; try apply isPREFIX_REFL.
  - intros ck1. rewrite N.add_0_r. reflexivity.
  - split; [exact Hs|exact Hci].
Qed.

Lemma fc_Tick s : FC (Tick, s).
Proof.
  fc_intro. rewrite evaluate_eqn in He. cbn [evaluate_body] in He.
  fl_norm Hci. ci_split. pose proof (sr_clock _ _ Hs) as Hc. pose proof (sr_failed _ _ Hs) as Hf.
  destruct (clock s =? 0) eqn:Ec; injection He as <- <-.
  - apply N.eqb_eq in Ec. exists 1, (inc_pc t1). unfold fc_post. cbn [halt_view OPTION_MAP result_view].
    post_split; try reflexivity; try apply isPREFIX_REFL.
    + intros ck1. rewrite (lev_inst _ asm.Skip [] 0); [|cbn; lia|eassumption].
      cbn [asm_inst failed labSem.set_clock]. rewrite Hf. rewrite linc_pc_clock.
      f_equal. cbn. f_equal. lia.
    + split; [|cbn; lia]. sr_destruct Hs. lab_cbn. stk_fields. exact Hffi.
  - apply N.eqb_neq in Ec. exists 0, (inc_pc (labSem.dec_clock t1)). unfold fc_post.
    cbn [halt_view OPTION_MAP]. post_split; try reflexivity; try apply isPREFIX_REFL.
    + intros ck1. rewrite (lev_inst _ asm.Skip [] 0); [|cbn; lia|eassumption].
      cbn [asm_inst failed labSem.set_clock]. rewrite Hf. rewrite linc_pc_clock.
      change (labSem.set_clock (labSem.clock (inc_pc (labSem.dec_clock t1)) + ck1) (inc_pc (labSem.dec_clock t1)))
        with (labSem.set_clock (labSem.clock t1 - 1 + ck1) (inc_pc t1)).
      f_equal. f_equal. lia.
    + split; [cbn; lia|]. apply (state_rel_with_pc (pc t1 + 1)), state_rel_dec_clock, Hs.
Qed.


Lemma fc_LocValue r0 l1 l2 s : FC (stackLang.LocValue r0 l1 l2, s).
Proof.
  fc_intro. rewrite evaluate_eqn in He. cbn [evaluate_body] in He.
  destruct (classical_dec _) as [Hlc|]; injection He as <- <-; [|congruence].
  fl_norm Hci. ci_split.
  destruct (loc_check_IMP_loc_to_pc s t1 l1 l2 (conj Hlc Hs)) as [v Hv].
  exists 1, (inc_pc (upd_reg r0 (Loc l1 l2) t1)). unfold fc_post. cbn [halt_view OPTION_MAP].
  post_split; try reflexivity; try apply isPREFIX_REFL.
  - intros ck1. rewrite (lev_locvalue _ r0 l1 l2 (n2w 0) [] 0); [|cbn; lia|eassumption].
    cbn [labSem.code labSem.set_clock]. rewrite Hv, lupd_reg_clock, linc_pc_clock. f_equal. cbn. f_equal. lia.
  - split; [cbn; lia|]. apply (state_rel_with_pc (pc t1 + 1)), set_var_upd_reg, Hs.
Qed.

Lemma lev_cbw t r1 r2 b l0 :
  labSem.clock t <> 0 -> asm_fetch t = SOME (Asm (Cbw r1 r2) b l0) ->
  labSem.evaluate t =
  match read_reg r1 t, read_reg r2 t with
  | Word w1, Word w2 =>
      match buffer_write (labSem.code_buffer t) w1 (w2w w2) with
      | SOME new_cb => labSem.evaluate (inc_pc (labSem.dec_clock (labSem.set_code_buffer new_cb t)))
      | _ => (targetSem.Error, t)
      end
  | _, _ => (targetSem.Error, t)
  end.
Proof. intros Hc Hf. rewrite labSem.evaluate_def, (proj2 (N.eqb_neq _ _) Hc), Hf. reflexivity. Qed.

Lemma fc_CodeBufferWrite r1 r2 s : FC (CodeBufferWrite r1 r2, s).
Proof.
  fc_intro. rewrite evaluate_eqn in He. cbn [evaluate_body] in He. unfold get_var in He.
  destruct (FLOOKUP (regs s) r1) as [[w1|]|] eqn:E1; try (injection He as <- <-; congruence).
  destruct (FLOOKUP (regs s) r2) as [[w2|]|] eqn:E2; try (injection He as <- <-; congruence).
  destruct (buffer_write (code_buffer s) w1 (w2w w2)) as [cb|] eqn:Eb; injection He as <- <-; [|congruence].
  fl_norm Hci. ci_split.
  pose proof (sr_regs _ _ _ _ Hs E1) as R1. pose proof (sr_regs _ _ _ _ Hs E2) as R2.
  exists 1, (inc_pc (labSem.set_code_buffer cb t1)). unfold fc_post. cbn [halt_view OPTION_MAP].
  post_split; try reflexivity; try apply isPREFIX_REFL.
  - intros ck1. rewrite (lev_cbw _ r1 r2 [] 0); [|cbn; lia|eassumption].
    cbn [labSem.regs labSem.set_clock labSem.code_buffer]. rewrite R1, R2.
    replace (labSem.code_buffer t1) with (code_buffer s) by (sr_destruct Hs; exact Hcb).
    rewrite Eb, lset_cb_clock, linc_pc_clock. f_equal. cbn. f_equal. lia.
  - split; [cbn; lia|]. sr_destruct Hs. sr_split; try assumption; reflexivity.
Qed.


Lemma isPREFIX_trans' {A} `{EqDecision A} (x y z : list A) :
  isPREFIX x y -> isPREFIX y z -> isPREFIX x z.
Proof. intros H1 H2; apply (isPREFIX_TRANS x y z); split; assumption. Qed.

(** Galette-only: composing a simulation prefix with [fc_post]. *)
Lemma post_step r s2 t1 t1' t2 ck k0 (L L' : list (line a)) n cs bs :
  (forall K, labSem.evaluate (labSem.set_clock (labSem.clock t1 + k0 + K) t1) =
             labSem.evaluate (labSem.set_clock (labSem.clock t1' + K) t1')) ->
  fc_post r s2 t1' t2 ck L' n cs bs ->
  len_reg t1' = len_reg t1 -> ptr_reg t1' = ptr_reg t1 -> len2_reg t1' = len2_reg t1 ->
  ptr2_reg t1' = ptr2_reg t1 -> link_reg t1' = link_reg t1 ->
  isPREFIX (labSem.code t1) (labSem.code t1') ->
  pc t1' + LENGTH (FILTER (negb ∘ is_Label) L') = pc t1 + LENGTH (FILTER (negb ∘ is_Label) L) ->
  fc_post r s2 t1 t2 (k0 + ck) L n cs bs.
Proof.
  intros Hstep Hp E1 E2 E3 E4 E5 Hpre Hpc. unfold fc_post in *.
  destruct (halt_view r) as [res|].
  - destruct Hp as [Hev Hffi]. split; [|exact Hffi].
    replace (labSem.clock t1 + (k0 + ck)) with (labSem.clock t1 + k0 + ck) by lia.
    rewrite Hstep. exact Hev.
  - destruct Hp as (Hev & F1 & F2 & F3 & F4 & F5 & Hpre' & Hm). post_split.
    + intros ck1. replace (labSem.clock t1 + (k0 + ck) + ck1) with (labSem.clock t1 + k0 + (ck + ck1)) by lia.
      rewrite Hstep. rewrite N.add_assoc. apply Hev.
    + congruence.
    + congruence.
    + congruence.
    + congruence.
    + congruence.
    + exact (isPREFIX_trans' _ _ _ Hpre Hpre').
    + destruct (OPTION_MAP _ r) as [[]|]; try exact Hm. destruct Hm as [Hm1 Hm2]. split; [lia|exact Hm2].
Qed.

Lemma post_trans r s1 s2 t1 t2 t3 ck ck' (L1 L2 L : list (line a)) n cs bs :
  fc_post NONE s1 t1 t2 ck L1 n cs bs ->
  fc_post r s2 t2 t3 ck' L2 n cs bs ->
  LENGTH (FILTER (negb ∘ is_Label) L) =
    LENGTH (FILTER (negb ∘ is_Label) L1) + LENGTH (FILTER (negb ∘ is_Label) L2) ->
  fc_post r s2 t1 t3 (ck + ck') L n cs bs.
Proof.
  intros H1 H2 HL. cbn [fc_post halt_view OPTION_MAP] in H1.
  destruct H1 as (Hev & F1 & F2 & F3 & F4 & F5 & Hpre & Hpc & _).
  apply (post_step _ _ _ t2 _ _ _ _ L2); try assumption; try congruence. lia.
Qed.

Lemma post_lines r s2 t1 t2 ck (L L' : list (line a)) n cs bs :
  r <> NONE -> fc_post r s2 t1 t2 ck L n cs bs -> fc_post r s2 t1 t2 ck L' n cs bs.
Proof.
  intros Hr Hp. unfold fc_post in *. destruct (halt_view r); [exact Hp|].
  destruct r as [r|]; [|congruence]. exact Hp.
Qed.

Lemma fc_Seq c1 c2 s :
  (forall y, eval_lt y (Seq c1 c2, s) -> FC y) -> FC (Seq c1 c2, s).
Proof.
  intros IH. fc_intro. rewrite evaluate_eqn in He. cbn [evaluate_body] in He.
  rewrite fix_clock_evaluate in He.
  destruct (evaluate (c1, s)) as [res1 s1] eqn:E1.
  cbn [call_args] in Hca. apply Bool.andb_true_iff in Hca as [Hca1 Hca2].
  cbn [flatten] in Hci.
  destruct (flatten false c1 n l cs bs) as [xs [nr1 m1]] eqn:F1.
  destruct (flatten false c2 n m1 cs bs) as [ys [nr2 m2]] eqn:F2.
  assert (Hlt1 : eval_lt (c1, s) (Seq c1 c2, s)) by (right; cbn [fst snd psize]; split; [reflexivity|lia]).
  assert (Hci1 : code_installed (pc t1) (append xs) (labSem.code t1) /\
                 code_installed (pc t1 + LENGTH (FILTER (negb ∘ is_Label) (append xs))) (append ys) (labSem.code t1) /\
                 LENGTH (FILTER (negb ∘ is_Label) (append (FST (if t then
                     (Append (Append xs (List [Label n 1 0])) ys, (nr1 || nr2, m2))
                   else (Append xs ys, (nr1 || nr2, m2)))))) =
                 LENGTH (FILTER (negb ∘ is_Label) (append xs)) + LENGTH (FILTER (negb ∘ is_Label) (append ys))).
  { destruct t; cbn [FST fst] in Hci |- *; rewrite ?append_Append, ?append_List in Hci |- *;
      rewrite <- ?app_assoc in Hci |- *; cbn [app] in Hci |- *;
      apply code_installed_append_imp in Hci as [Hx Hy]; (split; [exact Hx|]);
      [cbn [code_installed is_Label] in Hy; destruct Hy as [_ Hy]|];
      (split; [exact Hy|]); rewrite LENGTH_FILTER_app; [rewrite LENGTH_FILTER_cons_lab by reflexivity|]; reflexivity. }
  destruct Hci1 as (Hx & Hy & Hlen).
  destruct res1 as [x|].
  - injection He as <- <-.
    destruct (IH _ Hlt1 false (SOME x) s1 n l cs bs t1 E1 Hr Hs Hca1 ltac:(cbn [fst snd]; rewrite F1; exact Hx) Hev)
      as (ck & t2 & Hp).
    exists ck, t2. cbn [fst snd] in Hp. rewrite F1 in Hp. eapply post_lines; [discriminate|exact Hp].
  - destruct (IH _ Hlt1 false NONE s1 n l cs bs t1 E1 ltac:(discriminate) Hs Hca1 ltac:(cbn [fst snd]; rewrite F1; exact Hx) Hev)
      as (ck & t2 & Hp1).
    cbn [fst snd] in Hp1. rewrite F1 in Hp1. cbn [FST fst] in Hp1. pose proof Hp1 as Hp1'.
    cbn [fc_post halt_view OPTION_MAP] in Hp1'.
    destruct Hp1' as (_ & F1' & F2' & F3' & F4' & F5' & Hpre & Hpc & Hs1).
    pose proof (evaluate_clock c1 s NONE s1 E1) as Hc1.
    assert (Hlt2 : eval_lt (c2, s1) (Seq c1 c2, s)).
    { destruct (N.eq_dec (clock s1) (clock s)) as [Ec|Ec];
        [right; cbn [fst snd psize]; split; [exact Ec|lia]|left; cbn [snd]; lia]. }
    assert (Hci2 : code_installed (pc t2) (append ys) (labSem.code t2)).
    { rewrite Hpc. exact (code_installed_isPREFIX _ _ _ _ (conj Hy Hpre)). }
    assert (Hev2 : EVERY (fun k => IS_SOME (loc_to_pc n k (labSem.code t2))) (cs ++ bs ++ [0])).
    { exact (every_is_some_loc_to_pc_prefix n _ _ _ (conj Hev Hpre)). }
    rewrite <- F1', <- F2', <- F3', <- F4', <- F5' in Hca2.
    destruct (IH _ Hlt2 false r s2 n m1 cs bs t2 He Hr Hs1 Hca2 ltac:(cbn [fst snd]; rewrite F2; exact Hci2) Hev2)
      as (ck' & t3 & Hp2).
    cbn [fst snd] in Hp2. rewrite F2 in Hp2. cbn [FST fst] in Hp2.
    exists (ck + ck'), t3. eapply post_trans; [exact Hp1|exact Hp2|]. cbn [fst flatten]. rewrite F1, F2. exact Hlen.
Qed.


Lemma post_refl s t n cs bs : state_rel s t -> fc_post NONE s t t 0 [] n cs bs.
Proof.
  intros Hs. cbn [fc_post halt_view OPTION_MAP]. post_split; try reflexivity; try apply isPREFIX_REFL.
  - intros ck1; rewrite N.add_0_r; reflexivity.
  - split; [cbn; lia|exact Hs].
Qed.

Lemma jc_taken t1 cmp r1 ri L1 L2 w b l0 p :
  asm_fetch t1 = SOME (LabAsm (JumpCmp cmp r1 ri (Lab L1 L2)) w b l0) ->
  wordSem.word_cmp cmp (read_reg r1 t1) (reg_imm ri t1) = SOME true ->
  loc_to_pc L1 L2 (labSem.code t1) = SOME p ->
  forall K, labSem.evaluate (labSem.set_clock (labSem.clock t1 + 1 + K) t1) =
            labSem.evaluate (labSem.set_clock (labSem.clock (upd_pc p t1) + K) (upd_pc p t1)).
Proof.
  intros Hf Hc Hl K. rewrite (lev_jumpcmp _ cmp r1 ri L1 L2 w b l0); [|cbn; lia|exact Hf].
  cbn [labSem.regs labSem.set_clock labSem.code]. change (reg_imm ri (labSem.set_clock (labSem.clock t1 + 1 + K) t1)) with (reg_imm ri t1).
  rewrite Hc, Hl, lupd_pc_clock. f_equal. cbn. f_equal. lia.
Qed.

Lemma jc_not_taken t1 cmp r1 ri lb w b l0 :
  asm_fetch t1 = SOME (LabAsm (JumpCmp cmp r1 ri lb) w b l0) ->
  wordSem.word_cmp cmp (read_reg r1 t1) (reg_imm ri t1) = SOME false ->
  forall K, labSem.evaluate (labSem.set_clock (labSem.clock t1 + 1 + K) t1) =
            labSem.evaluate (labSem.set_clock (labSem.clock (upd_pc (pc t1 + 1) t1) + K) (upd_pc (pc t1 + 1) t1)).
Proof.
  intros Hf Hc K. destruct lb as [L1 L2]. rewrite (lev_jumpcmp _ cmp r1 ri L1 L2 w b l0); [|cbn; lia|exact Hf].
  cbn [labSem.regs labSem.set_clock labSem.code]. change (reg_imm ri (labSem.set_clock (labSem.clock t1 + 1 + K) t1)) with (reg_imm ri t1).
  rewrite Hc, linc_pc_clock. f_equal. cbn. f_equal. lia.
Qed.

Lemma jump_taken t1 L1 L2 w b l0 p :
  asm_fetch t1 = SOME (LabAsm (Jump (Lab L1 L2)) w b l0) ->
  loc_to_pc L1 L2 (labSem.code t1) = SOME p ->
  forall K, labSem.evaluate (labSem.set_clock (labSem.clock t1 + 1 + K) t1) =
            labSem.evaluate (labSem.set_clock (labSem.clock (upd_pc p t1) + K) (upd_pc p t1)).
Proof.
  intros Hf Hl K. rewrite (lev_jump _ L1 L2 w b l0); [|cbn; lia|exact Hf].
  cbn [labSem.code labSem.set_clock]. rewrite Hl, lupd_pc_clock. f_equal. cbn. f_equal. lia.
Qed.

(** Galette-only: run a sub-program from [upd_pc p t1] after a one-step
    jump, given the induction hypothesis. *)
Lemma post_jump_sub r s2 t1 p ck t2 (L' L : list (line a)) n cs bs :
  (forall K, labSem.evaluate (labSem.set_clock (labSem.clock t1 + 1 + K) t1) =
             labSem.evaluate (labSem.set_clock (labSem.clock (upd_pc p t1) + K) (upd_pc p t1))) ->
  fc_post r s2 (upd_pc p t1) t2 ck L' n cs bs ->
  p + LENGTH (FILTER (negb ∘ is_Label) L') = pc t1 + LENGTH (FILTER (negb ∘ is_Label) L) ->
  fc_post r s2 t1 t2 (1 + ck) L n cs bs.
Proof.
  intros Hstep Hp Hpc. apply (post_step _ _ _ _ _ _ _ _ L' _ _ _ Hstep Hp); try reflexivity.
  - apply isPREFIX_REFL.
  - exact Hpc.
Qed.


Ltac len_tac :=
  timeout 20 (repeat (progress (rewrite ?LENGTH_FILTER_app; cbn [List.filter is_Label negb LENGTH app];
                                rewrite ?not_is_Label_compile_jump)); lia).

Ltac ci_at :=
  cbn [pc upd_pc set_pc labSem.code FST fst];
  match goal with
  | |- code_installed ?P ?L ?C =>
      match goal with H : code_installed ?Q L C |- _ => replace P with Q by (cbn; lia); exact H end
  end.

Lemma evaluate_Skip s : evaluate (Skip, s) = (NONE, s).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma is_Skip_true (p : prog a) : is_Skip p = true -> p = Skip.
Proof. destruct p; try discriminate; reflexivity. Qed.

Lemma fc_If cmp r1 ri c1 c2 s :
  (forall y, eval_lt y (If cmp r1 ri c1 c2, s) -> FC y) -> FC (If cmp r1 ri c1 c2, s).
Proof.
  intros IH. fc_intro. rewrite evaluate_eqn in He. cbn [evaluate_body] in He.
  destruct (get_var r1 s) as [x|] eqn:Ex; [|injection He as <- <-; congruence].
  destruct (get_var_imm ri s) as [y|] eqn:Ey; [|injection He as <- <-; congruence].
  destruct (wordSem.word_cmp cmp x y) as [b|] eqn:Eb; [|injection He as <- <-; congruence].
  assert (Rx : read_reg r1 t1 = x) by (unfold get_var in Ex; exact (sr_regs _ _ _ _ Hs Ex)).
  assert (Ry : reg_imm ri t1 = y) by exact (state_rel_get_var_imm _ _ _ _ (conj Hs Ey)).
  assert (Ecmp : wordSem.word_cmp cmp (read_reg r1 t1) (reg_imm ri t1) = SOME b) by (rewrite Rx, Ry; exact Eb).
  assert (Encmp : wordSem.word_cmp (negate cmp) (read_reg r1 t1) (reg_imm ri t1) = SOME (negb b))
    by (rewrite word_cmp_negate, Ecmp; reflexivity).
  cbn [call_args] in Hca. apply Bool.andb_true_iff in Hca as [Hca1 Hca2].
  assert (Hlt1 : eval_lt (c1, s) (If cmp r1 ri c1 c2, s)) by (right; cbn [fst snd psize]; split; [reflexivity|lia]).
  assert (Hlt2 : eval_lt (c2, s) (If cmp r1 ri c1 c2, s)) by (right; cbn [fst snd psize]; split; [reflexivity|lia]).
  cbn [fst flatten] in Hci |- *.
  destruct (flatten false c1 n l cs bs) as [xs [nr1 m1]] eqn:F1.
  destruct (flatten false c2 n m1 cs bs) as [ys [nr2 m2]] eqn:F2.
  assert (IH1 : forall t1', state_rel s t1' -> link_reg t1' = link_reg t1 -> len_reg t1' = len_reg t1 ->
            ptr_reg t1' = ptr_reg t1 -> len2_reg t1' = len2_reg t1 -> ptr2_reg t1' = ptr2_reg t1 ->
            code_installed (pc t1') (append xs) (labSem.code t1') ->
            EVERY (fun k => IS_SOME (loc_to_pc n k (labSem.code t1'))) (cs ++ bs ++ [0]) ->
            evaluate (c1, s) = (r, s2) ->
            exists ck t2, fc_post r s2 t1' t2 ck (append xs) n cs bs).
  { intros t1' Hs' L1 L2 L3 L4 L5 Hc' Hv' Hev1.
    destruct (IH _ Hlt1 false r s2 n l cs bs t1' Hev1 Hr Hs'
               ltac:(cbn [fst]; rewrite L1, L2, L3, L4, L5; exact Hca1)
               ltac:(cbn [fst]; rewrite F1; exact Hc') Hv') as (ck & t2 & Hp).
    cbn [fst] in Hp. rewrite F1 in Hp. eauto. }
  assert (IH2 : forall t1', state_rel s t1' -> link_reg t1' = link_reg t1 -> len_reg t1' = len_reg t1 ->
            ptr_reg t1' = ptr_reg t1 -> len2_reg t1' = len2_reg t1 -> ptr2_reg t1' = ptr2_reg t1 ->
            code_installed (pc t1') (append ys) (labSem.code t1') ->
            EVERY (fun k => IS_SOME (loc_to_pc n k (labSem.code t1'))) (cs ++ bs ++ [0]) ->
            evaluate (c2, s) = (r, s2) ->
            exists ck t2, fc_post r s2 t1' t2 ck (append ys) n cs bs).
  { intros t1' Hs' L1 L2 L3 L4 L5 Hc' Hv' Hev1.
    destruct (IH _ Hlt2 false r s2 n m1 cs bs t1' Hev1 Hr Hs'
               ltac:(cbn [fst]; rewrite L1, L2, L3, L4, L5; exact Hca2)
               ltac:(cbn [fst]; rewrite F2; exact Hc') Hv') as (ck & t2 & Hp).
    cbn [fst] in Hp. rewrite F2 in Hp. eauto. }
  clear IH.
  destruct (is_Skip c1) eqn:S1, (is_Skip c2) eqn:S2; cbn [andb FST fst] in Hci |- *.
  - (* both Skip *)
    apply is_Skip_true in S1, S2; subst c1 c2.
    destruct b; rewrite evaluate_Skip in He; injection He as <- <-;
      exists 0, t1; rewrite append_List; exact (post_refl _ _ _ _ _ Hs).
  - (* c1 = Skip *)
    apply is_Skip_true in S1; subst c1.
    rewrite ?append_Append, ?append_List in Hci |- *. rewrite <- ?app_assoc in Hci |- *. cbn [app] in Hci |- *.
    ci_split. destruct b.
    + rewrite evaluate_Skip in He; injection He as <- <-.
      exists (1 + 0), (upd_pc (pc t1 + 1 + LENGTH (FILTER (negb ∘ is_Label) (append ys))) t1).
      eapply post_jump_sub.
      * eapply jc_taken; [eassumption|exact Ecmp|]. eassumption.
      * apply post_refl, state_rel_with_pc, Hs.
      * len_tac.
    + destruct (IH2 (upd_pc (pc t1 + 1) t1) (state_rel_with_pc _ _ _ Hs)
                  eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(ci_at) Hev He) as (ck & t2 & Hp).
      exists (1 + ck), t2. eapply post_jump_sub.
      * eapply jc_not_taken; [eassumption|exact Ecmp].
      * exact Hp.
      * cbn [pc upd_pc set_pc]. len_tac.
  - (* c2 = Skip *)
    apply is_Skip_true in S2; subst c2.
    rewrite ?append_Append, ?append_List in Hci |- *. rewrite <- ?app_assoc in Hci |- *. cbn [app] in Hci |- *.
    ci_split. destruct b.
    + destruct (IH1 (upd_pc (pc t1 + 1) t1) (state_rel_with_pc _ _ _ Hs)
                  eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(ci_at) Hev He) as (ck & t2 & Hp).
      exists (1 + ck), t2. eapply post_jump_sub.
      * eapply jc_not_taken; [eassumption|exact Encmp].
      * exact Hp.
      * cbn [pc upd_pc set_pc]. len_tac.
    + rewrite evaluate_Skip in He; injection He as <- <-.
      exists (1 + 0), (upd_pc (pc t1 + 1 + LENGTH (FILTER (negb ∘ is_Label) (append xs))) t1).
      eapply post_jump_sub.
      * eapply jc_taken; [eassumption|exact Encmp|]. eassumption.
      * apply post_refl, state_rel_with_pc, Hs.
      * len_tac.
  - (* neither is Skip *)
    pose proof (@no_ret_correct a c ffi_t false c1 n l cs bs) as NR1. rewrite F1 in NR1. cbn [FST SND fst snd] in NR1.
    pose proof (@no_ret_correct a c ffi_t false c2 n m1 cs bs) as NR2. rewrite F2 in NR2. cbn [FST SND fst snd] in NR2.
    destruct nr1; [|destruct nr2]; cbn [FST fst] in Hci |- *;
      rewrite ?append_Append, ?append_List in Hci |- *; rewrite <- ?app_assoc in Hci |- *; cbn [app] in Hci |- *;
      ci_split.
    + (* nr1 *) destruct b.
      * assert (Hrn : r <> NONE) by (intros ->; specialize (NR1 eq_refl s); rewrite He in NR1; discriminate).
        destruct (IH1 (upd_pc (pc t1 + 1) t1) (state_rel_with_pc _ _ _ Hs)
                    eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(ci_at) Hev He) as (ck & t2 & Hp).
        exists (1 + ck), t2. eapply post_jump_sub.
        -- eapply jc_not_taken; [eassumption|exact Encmp].
        -- apply (post_lines _ _ _ _ _ (append xs) (append xs ++ Label n m2 0 :: append ys)); [exact Hrn|exact Hp].
        -- cbn [pc upd_pc set_pc]. len_tac.
      * destruct (IH2 (upd_pc (pc t1 + 1 + LENGTH (FILTER (negb ∘ is_Label) (append xs))) t1)
                    (state_rel_with_pc _ _ _ Hs)
                    eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(ci_at) Hev He) as (ck & t2 & Hp).
        exists (1 + ck), t2. eapply post_jump_sub.
        -- eapply jc_taken; [eassumption|exact Encmp|]. eassumption.
        -- exact Hp.
        -- len_tac.
    + (* nr2 *) destruct b.
      * destruct (IH1 (upd_pc (pc t1 + 1 + LENGTH (FILTER (negb ∘ is_Label) (append ys))) t1)
                    (state_rel_with_pc _ _ _ Hs)
                    eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(ci_at) Hev He) as (ck & t2 & Hp).
        exists (1 + ck), t2. eapply post_jump_sub.
        -- eapply jc_taken; [eassumption|exact Ecmp|]. eassumption.
        -- exact Hp.
        -- len_tac.
      * assert (Hrn : r <> NONE) by (intros ->; specialize (NR2 eq_refl s); rewrite He in NR2; discriminate).
        destruct (IH2 (upd_pc (pc t1 + 1) t1) (state_rel_with_pc _ _ _ Hs)
                    eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(ci_at) Hev He) as (ck & t2 & Hp).
        exists (1 + ck), t2. eapply post_jump_sub.
        -- eapply jc_not_taken; [eassumption|exact Ecmp].
        -- apply (post_lines _ _ _ _ _ (append ys) (append ys ++ Label n m2 0 :: append xs)); [exact Hrn|exact Hp].
        -- cbn [pc upd_pc set_pc]. len_tac.
    + (* general *) destruct b.
      * destruct (IH1 (upd_pc (pc t1 + 1 + LENGTH (FILTER (negb ∘ is_Label) (append ys)) + 1) t1)
                    (state_rel_with_pc _ _ _ Hs)
                    eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(ci_at) Hev He) as (ck & t2 & Hp).
        exists (1 + ck), t2. eapply post_jump_sub.
        -- eapply jc_taken; [eassumption|exact Ecmp|]. eassumption.
        -- exact Hp.
        -- len_tac.
      * destruct (IH2 (upd_pc (pc t1 + 1) t1) (state_rel_with_pc _ _ _ Hs)
                    eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(ci_at) Hev He) as (ck & t2 & Hp).
        destruct r as [r'|].
        -- exists (1 + ck), t2. eapply post_jump_sub.
           ++ eapply jc_not_taken; [eassumption|exact Ecmp].
           ++ apply (post_lines _ _ _ _ _ (append ys) (append ys ++ LabAsm (Jump (Lab n (m2 + 1))) (n2w 0) [] 0 ::
                 Label n m2 0 :: append xs ++ [Label n (m2 + 1) 0])); [discriminate|exact Hp].
           ++ cbn [pc upd_pc set_pc]. len_tac.
        -- pose proof Hp as Hp'. cbn [fc_post halt_view OPTION_MAP] in Hp'.
           destruct Hp' as (_ & _ & _ & _ & _ & _ & Hpre & Hpc & Hs2).
           cbn [pc upd_pc set_pc] in Hpc. cbn [labSem.code upd_pc set_pc] in Hpre.
           match goal with
           | Hj : asm_fetch_aux _ _ = SOME (LabAsm (Jump (Lab n (m2 + 1))) _ _ _),
             Hl : loc_to_pc n (m2 + 1) _ = SOME ?E |- _ =>
               pose proof (afa_isPREFIX _ _ _ _ (conj Hj Hpre)) as Hj';
               pose proof (loc_to_pc_isPREFIX _ _ _ _ _ (conj Hl Hpre)) as Hl';
               exists (1 + (ck + (1 + 0))), (upd_pc E t2)
           end.
           set (JT := LabAsm (Jump (Lab n (m2 + 1))) (n2w 0) [] 0 :: Label n m2 0 ::
                        append xs ++ [Label n (m2 + 1) 0]).
           eapply (post_jump_sub _ _ _ _ _ _ (append ys ++ JT)).
           ++ eapply jc_not_taken; [eassumption|exact Ecmp].
           ++ eapply (post_trans _ _ _ _ _ _ _ _ (append ys) JT (append ys ++ JT)); [exact Hp| |].
              ** eapply (post_jump_sub _ _ _ _ _ _ [] JT).
                 --- eapply jump_taken; [|exact Hl']. unfold asm_fetch. rewrite Hpc. exact Hj'.
                 --- apply post_refl, state_rel_with_pc, Hs2.
                 --- rewrite Hpc. subst JT. len_tac.
              ** rewrite LENGTH_FILTER_app. reflexivity.
           ++ subst JT. cbn [pc upd_pc set_pc]. len_tac.
Qed.


Lemma jump_taken0 t L1 L2 w b l0 p :
  labSem.clock t <> 0 ->
  asm_fetch t = SOME (LabAsm (Jump (Lab L1 L2)) w b l0) ->
  loc_to_pc L1 L2 (labSem.code t) = SOME p ->
  forall K, labSem.evaluate (labSem.set_clock (labSem.clock t + K) t) =
            labSem.evaluate (labSem.set_clock (labSem.clock (upd_pc p (labSem.dec_clock t)) + K)
                                (upd_pc p (labSem.dec_clock t))).
Proof.
  intros Hc Hf Hl K. rewrite (lev_jump _ L1 L2 w b l0); [|cbn; lia|exact Hf].
  cbn [labSem.code labSem.set_clock]. rewrite Hl, lupd_pc_clock.
  change (labSem.set_clock (labSem.clock (upd_pc p (labSem.dec_clock t)) + K) (upd_pc p (labSem.dec_clock t)))
    with (labSem.set_clock (labSem.clock t - 1 + K) (upd_pc p t)).
  f_equal. f_equal. lia.
Qed.

Lemma post_view r r' s t1 t2 ck (L L' : list (line a)) n cs bs cs' bs' :
  r <> NONE -> r' <> NONE -> halt_view r = halt_view r' ->
  OPTION_MAP (fun w => result_view w n cs bs) r' = OPTION_MAP (fun w => result_view w n cs' bs') r ->
  fc_post r s t1 t2 ck L n cs' bs' -> fc_post r' s t1 t2 ck L' n cs bs.
Proof.
  intros H1 H2 Hh Hv Hp. unfold fc_post in *. rewrite <- Hh. destruct (halt_view r); [exact Hp|].
  rewrite Hv. destruct Hp as (A & B & C & D & E & F & G & Hm). post_split; try assumption.
  destruct r as [r|]; [|congruence]. exact Hm.
Qed.

Lemma find_lab_cons_S k x (bs : list N) : find_lab (k + 1) (x :: bs) = find_lab k bs.
Proof. unfold find_lab. cbn [oEL]. replace (k + 1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
  replace (k + 1 - 1) with k by lia. reflexivity. Qed.

Lemma find_lab_cons_0 x (bs : list N) : find_lab 0 (x :: bs) = x.
Proof. reflexivity. Qed.

Lemma fc_Loop c1 s :
  (forall y, eval_lt y (Loop c1, s) -> FC y) -> FC (Loop c1, s).
Proof.
  intros IH. fc_intro. pose proof He as He0. rewrite evaluate_eqn in He. cbn [evaluate_body] in He.
  rewrite fix_clock_evaluate in He. unfold STOP in He.
  destruct (evaluate (c1, s)) as [res s1] eqn:E1.
  cbn [call_args] in Hca.
  cbn [flatten] in Hci |- *.
  destruct (flatten false c1 n (l + 2) (l :: cs) ((l + 1) :: bs)) as [xs [nr1 m1]] eqn:F1.
  cbn [FST fst] in Hci |- *. rewrite ?append_Append, ?append_List in Hci |- *.
  rewrite <- ?app_assoc in Hci |- *. cbn [app] in Hci |- *.
  assert (Hci_all : True -> code_installed (pc t1) (Label n l 0 :: append xs ++
            [LabAsm (Jump (Lab n l)) (n2w 0) [] 0; Label n (l + 1) 0]) (labSem.code t1)) by (intros _; exact Hci).
  ci_split.
  assert (Hlt1 : eval_lt (c1, s) (Loop c1, s)) by (right; cbn [fst snd psize]; split; [reflexivity|lia]).
  match goal with
  | H1 : loc_to_pc n l _ = SOME ?P1, H2 : loc_to_pc n (l + 1) _ = SOME ?P2 |- _ =>
      rename H1 into Ll; rename H2 into Ll1
  end.
  assert (Hev1 : EVERY (fun k => IS_SOME (loc_to_pc n k (labSem.code t1))) ((l :: cs) ++ ((l + 1) :: bs) ++ [0])).
  { unfold is_true in *. rewrite EVERY_Forall in Hev |- *. cbn [app]. constructor; [rewrite Ll; reflexivity|].
    apply Forall_app in Hev as [Hc Hbs]. apply Forall_app; split; [exact Hc|].
    constructor; [rewrite Ll1; reflexivity|exact Hbs]. }
  destruct (IH _ Hlt1 false res s1 n (l + 2) (l :: cs) ((l + 1) :: bs) t1 E1
              ltac:(intros ->; destruct (cont_loop (SOME Error)) eqn:X; [discriminate X|];
                    injection He as <- <-; exact (Hr eq_refl))
              Hs Hca ltac:(cbn [fst]; rewrite F1; ci_at) Hev1) as (ck & t2 & Hp).
  cbn [fst] in Hp. rewrite F1 in Hp. cbn [FST fst] in Hp.
  match goal with
  | H : asm_fetch_aux _ _ = SOME (LabAsm (Jump (Lab n l)) _ _ _) |- _ => rename H into Hjmp
  end.
  destruct (cont_loop res) eqn:Ecl.
  - (* the loop continues *)
    assert (J : (forall ck1, labSem.evaluate (labSem.set_clock (labSem.clock t1 + ck + ck1) t1) =
                             labSem.evaluate (labSem.set_clock (labSem.clock t2 + ck1) t2)) /\
                len_reg t2 = len_reg t1 /\ ptr_reg t2 = ptr_reg t1 /\ len2_reg t2 = len2_reg t1 /\
                ptr2_reg t2 = ptr2_reg t1 /\ link_reg t2 = link_reg t1 /\
                isPREFIX (labSem.code t1) (labSem.code t2) /\ state_rel s1 t2 /\
                asm_fetch_aux (pc t2) (labSem.code t2) = SOME (LabAsm (Jump (Lab n l)) (n2w 0) [] 0)).
    { apply cont_loop_IMP in Ecl. destruct Ecl as [->| ->].
      - cbn [fc_post halt_view OPTION_MAP] in Hp. destruct Hp as (A & B & C & D & E & F & G & Hpc & Hs1).
        repeat (split; [assumption|]).
        rewrite Hpc. exact (afa_isPREFIX _ _ _ _ (conj Hjmp G)).
      - cbn [fc_post halt_view OPTION_MAP result_view] in Hp. rewrite find_lab_cons_0 in Hp.
        destruct Hp as (A & B & C & D & E & F & G & Hs1 & Hj). cbn [code_installed is_Label] in Hj.
        repeat (split; [assumption|]). exact (proj1 Hj). }
    destruct J as (Hev2 & R1 & R2 & R3 & R4 & R5 & Hpre & Hs1 & Hj).
    pose proof (sr_clock _ _ Hs1) as Hc2.
    destruct (clock s1 =? 0) eqn:Ec0.
    + injection He as <- <-. apply N.eqb_eq in Ec0. exists ck, t2. cbn [fc_post halt_view OPTION_MAP result_view].
      post_split; try assumption. split; [|lia]. sr_destruct Hs1. lab_cbn. stk_fields. exact Hffi.
    + apply N.eqb_neq in Ec0.
      pose proof (evaluate_clock c1 s res s1 E1) as Hc1.
      assert (Hlt2 : eval_lt (Loop c1, dec_clock s1) (Loop c1, s)) by (left; cbn [snd clock dec_clock set_clock]; lia).
      set (t1' := upd_pc (pc t1) (labSem.dec_clock t2)).
      assert (Hs1' : state_rel (dec_clock s1) t1') by (apply state_rel_with_pc, state_rel_dec_clock, Hs1).
      assert (Ll' : loc_to_pc n l (labSem.code t2) = SOME (pc t1)) by exact (loc_to_pc_isPREFIX _ _ _ _ _ (conj Ll Hpre)).
      destruct (IH _ Hlt2 false r s2 n l cs bs t1' He Hr Hs1'
                  ltac:(cbn [fst call_args]; subst t1'; cbn [upd_pc set_pc labSem.dec_clock labSem.set_clock
                          ptr_reg len_reg ptr2_reg len2_reg link_reg]; rewrite R1, R2, R3, R4, R5; exact Hca)
                  ltac:(cbn [fst flatten]; rewrite F1; cbn [FST fst]; rewrite ?append_Append, ?append_List;
                        rewrite <- ?app_assoc; cbn [app]; subst t1'; cbn [pc upd_pc set_pc labSem.code labSem.dec_clock labSem.set_clock];
                        exact (code_installed_isPREFIX _ _ _ _ (conj (Hci_all Logic.I) Hpre)))
                  ltac:(subst t1'; exact (every_is_some_loc_to_pc_prefix _ _ _ _ (conj Hev Hpre))))
        as (ck3 & t3 & Hp3).
      cbn [fst flatten] in Hp3. rewrite F1 in Hp3. cbn [FST fst] in Hp3.
      rewrite ?append_Append, ?append_List in Hp3. rewrite <- ?app_assoc in Hp3. cbn [app] in Hp3.
      exists (ck + ck3), t3.
      apply (post_step _ _ _ t1' _ _ _ _ (Label n l 0 :: append xs ++
               [LabAsm (Jump (Lab n l)) (n2w 0) [] 0; Label n (l + 1) 0]) _ _ _); [| exact Hp3 | | | | | | |].
      * intros K. rewrite Hev2. subst t1'. apply (jump_taken0 t2 n l (n2w 0) [] 0); [lia|exact Hj|exact Ll'].
      * exact R1.
      * exact R2.
      * exact R3.
      * exact R4.
      * exact R5.
      * exact Hpre.
      * reflexivity.
  - (* the loop exits *)
    injection He as <- <-.
    destruct res as [x|]; [|discriminate Ecl].
    destruct x as [w|w|k|k|w| |f|]; cbn [exit_loop cont_loop] in Ecl |- *.
    + exists ck, t2. apply (fun H1 H2 H3 H4 => post_view _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 Hp); [discriminate|discriminate|reflexivity|]. reflexivity.
    + exists ck, t2. apply (fun H1 H2 H3 H4 => post_view _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 Hp); [discriminate|discriminate|reflexivity|]. reflexivity.
    + destruct (k =? 0) eqn:Ek.
      * apply N.eqb_eq in Ek; subst k. exists ck, t2.
        cbn [fc_post halt_view OPTION_MAP result_view] in Hp |- *.
        rewrite find_lab_cons_0 in Hp. destruct Hp as (A & B & C & D & E & F & G & _ & Hw).
        pose proof (loc_to_pc_isPREFIX _ _ _ _ _ (conj Ll1 G)) as Ll1'.
        destruct (Hw _ Ll1') as [Hw1 Hw2].
        post_split; try assumption. split; [|exact Hw2]. rewrite <- Hw1. len_tac.
      * exists ck, t2. apply (fun H1 H2 H3 H4 => post_view _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 Hp); [discriminate|discriminate|reflexivity|].
        cbn [OPTION_MAP result_view]. f_equal. f_equal.
        apply N.eqb_neq in Ek. replace k with ((k - 1) + 1) at 2 by lia. rewrite find_lab_cons_S. reflexivity.
    + apply N.eqb_neq in Ecl.
      exists ck, t2. apply (fun H1 H2 H3 H4 => post_view _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 Hp); [discriminate|discriminate|reflexivity|].
      cbn [OPTION_MAP result_view]. f_equal. f_equal.
      replace k with ((k - 1) + 1) at 2 by lia. rewrite find_lab_cons_S. reflexivity.
    + exists ck, t2. apply (fun H1 H2 H3 H4 => post_view _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 Hp); [discriminate|discriminate|reflexivity|]. reflexivity.
    + exists ck, t2. apply (fun H1 H2 H3 H4 => post_view _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 Hp); [discriminate|discriminate|reflexivity|]. reflexivity.
    + exists ck, t2. apply (fun H1 H2 H3 H4 => post_view _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 Hp); [discriminate|discriminate|reflexivity|]. reflexivity.
    + exfalso; exact (Hr eq_refl).
Qed.


Lemma post_tail res s' t1 t1' ck0 (L L' : list (line a)) n cs bs n' cs' bs' :
  bad_fun_return res = false ->
  (forall K, labSem.evaluate (labSem.set_clock (labSem.clock t1 + ck0 + K) t1) =
             labSem.evaluate (labSem.set_clock (labSem.clock t1' + K) t1')) ->
  len_reg t1' = len_reg t1 -> ptr_reg t1' = ptr_reg t1 -> len2_reg t1' = len2_reg t1 ->
  ptr2_reg t1' = ptr2_reg t1 -> link_reg t1' = link_reg t1 ->
  isPREFIX (labSem.code t1) (labSem.code t1') ->
  (exists ck t2, fc_post res s' t1' t2 ck L' n' cs' bs') ->
  exists ck t2, fc_post res s' t1 t2 ck L n cs bs.
Proof.
  intros Hb Hstep E1 E2 E3 E4 E5 Hpre (ck & t2 & Hp).
  destruct res as [x|]; [|discriminate Hb].
  assert (Hv : forall nn cc bb, result_view x nn cc bb = result_view x n' cs' bs')
    by (destruct x; try discriminate Hb; reflexivity).
  exists (ck0 + ck), t2. unfold fc_post in *. destruct (halt_view (SOME x)) as [res|].
  - destruct Hp as [Hev Hffi]. split; [|exact Hffi].
    replace (labSem.clock t1 + (ck0 + ck)) with (labSem.clock t1 + ck0 + ck) by lia.
    rewrite Hstep. exact Hev.
  - cbn [OPTION_MAP] in *. rewrite Hv. destruct Hp as (Hev & F1 & F2 & F3 & F4 & F5 & Hpre' & Hm).
    post_split; try congruence; try exact Hm.
    + intros ck1. replace (labSem.clock t1 + (ck0 + ck) + ck1) with (labSem.clock t1 + ck0 + (ck + ck1)) by lia.
      rewrite Hstep, N.add_assoc. apply Hev.
    + exact (isPREFIX_trans' _ _ _ Hpre Hpre').
Qed.

Lemma jc_taken0 t cmp r1 ri L1 L2 w b l0 p :
  labSem.clock t <> 0 ->
  asm_fetch t = SOME (LabAsm (JumpCmp cmp r1 ri (Lab L1 L2)) w b l0) ->
  wordSem.word_cmp cmp (read_reg r1 t) (reg_imm ri t) = SOME true ->
  loc_to_pc L1 L2 (labSem.code t) = SOME p ->
  forall K, labSem.evaluate (labSem.set_clock (labSem.clock t + K) t) =
            labSem.evaluate (labSem.set_clock (labSem.clock (upd_pc p (labSem.dec_clock t)) + K)
                                (upd_pc p (labSem.dec_clock t))).
Proof.
  intros Hc Hf Hcmp Hl K. rewrite (lev_jumpcmp _ cmp r1 ri L1 L2 w b l0); [|cbn; lia|exact Hf].
  cbn [labSem.regs labSem.set_clock labSem.code].
  change (reg_imm ri (labSem.set_clock (labSem.clock t + K) t)) with (reg_imm ri t).
  rewrite Hcmp, Hl, lupd_pc_clock.
  change (labSem.set_clock (labSem.clock (upd_pc p (labSem.dec_clock t)) + K) (upd_pc p (labSem.dec_clock t)))
    with (labSem.set_clock (labSem.clock t - 1 + K) (upd_pc p t)).
  f_equal. f_equal. lia.
Qed.

Lemma word_cmp_Word cmp (x y : word a) :
  wordSem.word_cmp cmp (Word x) (Word y) = SOME (asm.word_cmp cmp x y).
Proof. destruct cmp; reflexivity. Qed.

Lemma sr_code s t loc prog0 :
  state_rel s t -> lookup loc (code s) = SOME prog0 ->
  call_args prog0 (ptr_reg t) (len_reg t) (ptr2_reg t) (len2_reg t) (link_reg t) /\
  exists pc0, code_installed pc0 (append (FST (flatten true prog0 loc (stack_alloc.next_lab prog0 2) [] [])))
                (labSem.code t) /\ loc_to_pc loc 0 (labSem.code t) = SOME pc0.
Proof. intros H Hl. sr_destruct H. exact (Hcode loc prog0 Hl). Qed.

Lemma fc_JumpLower r1 r2 dest s :
  (forall y, eval_lt y (JumpLower r1 r2 dest, s) -> FC y) -> FC (JumpLower r1 r2 dest, s).
Proof.
  intros IH. fc_intro. rewrite evaluate_eqn in He. cbn [evaluate_body] in He. unfold get_var in He.
  destruct (FLOOKUP (regs s) r1) as [[x|]|] eqn:E1; try (injection He as <- <-; congruence).
  destruct (FLOOKUP (regs s) r2) as [[y|]|] eqn:E2; try (injection He as <- <-; congruence).
  pose proof (sr_regs _ _ _ _ Hs E1) as R1. pose proof (sr_regs _ _ _ _ Hs E2) as R2.
  fl_norm Hci. ci_split.
  destruct (asm.word_cmp Lower x y) eqn:Elw.
  - cbn [find_code] in He. destruct (lookup dest (code s)) as [prog0|] eqn:El; [|injection He as <- <-; congruence].
    pose proof (sr_clock _ _ Hs) as Hc.
    destruct (clock s =? 0) eqn:Ec0.
    + injection He as <- <-. apply N.eqb_eq in Ec0. exists 0, t1.
      cbn [fc_post halt_view OPTION_MAP result_view]. post_split; try reflexivity; try apply isPREFIX_REFL.
      * intros ck1; rewrite N.add_0_r; reflexivity.
      * split; [|lia]. sr_destruct Hs. lab_cbn. stk_fields. exact Hffi.
    + apply N.eqb_neq in Ec0.
      destruct (evaluate (prog0, dec_clock s)) as [res s'] eqn:Ep.
      destruct (bad_fun_return res) eqn:Eb; injection He as <- <-; [congruence|].
      destruct (sr_code _ _ _ _ Hs El) as (Hca0 & pc0 & Hcp0 & Hl0).
      assert (Hlt : eval_lt (prog0, dec_clock s) (JumpLower r1 r2 dest, s)) by (left; cbn [snd clock dec_clock set_clock]; lia).
      set (t1' := upd_pc pc0 (labSem.dec_clock t1)).
      apply (post_tail _ _ t1 t1' 0 _ (append (FST (flatten true prog0 dest (stack_alloc.next_lab prog0 2) [] [])))
               _ _ _ dest [] [] Eb); try reflexivity; try apply isPREFIX_REFL.
      * intros K. rewrite N.add_0_r. subst t1'.
        apply (jc_taken0 _ Lower r1 (Reg r2) dest 0 (n2w 0) [] 0); [lia|eassumption| |exact Hl0].
        cbn [reg_imm]. rewrite R1, R2, word_cmp_Word, Elw. reflexivity.
      * exact (IH _ Hlt true res s' dest (stack_alloc.next_lab prog0 2) [] [] t1' Ep Hr
                 ltac:(subst t1'; apply state_rel_with_pc, state_rel_dec_clock, Hs) Hca0 Hcp0
                 ltac:(subst t1'; cbn; rewrite Hl0; reflexivity)).
  - injection He as <- <-.
    exists (1 + 0), (upd_pc (pc t1 + 1) t1). eapply post_jump_sub.
    + eapply jc_not_taken; [eassumption|]. cbn [reg_imm]. rewrite R1, R2, word_cmp_Word, Elw. reflexivity.
    + apply post_refl, state_rel_with_pc, Hs.
    + cbn. lia.
Qed.


Lemma fc_RawCall dest s :
  (forall y, eval_lt y (RawCall dest, s) -> FC y) -> FC (RawCall dest, s).
Proof.
  intros IH. fc_intro. rewrite evaluate_eqn in He. cbn [evaluate_body] in He.
  destruct (lookup dest (code s)) as [prog0|] eqn:El; [|injection He as <- <-; congruence].
  destruct prog0 as [| | | | | | p1 body | | | | | | | | | | | | | | | | | | | | | | | | | | | ];
    cbn [dest_Seq] in He; try (injection He as <- <-; congruence).
  pose proof (sr_clock _ _ Hs) as Hc.
  fl_norm Hci. ci_split.
  destruct (clock s =? 0) eqn:Ec0.
  - injection He as <- <-. apply N.eqb_eq in Ec0. exists 0, t1.
    cbn [fc_post halt_view OPTION_MAP result_view]. post_split; try reflexivity; try apply isPREFIX_REFL.
    + intros ck1; rewrite N.add_0_r; reflexivity.
    + split; [|lia]. sr_destruct Hs. lab_cbn. stk_fields. exact Hffi.
  - apply N.eqb_neq in Ec0.
    destruct (evaluate (body, dec_clock s)) as [res s'] eqn:Ep.
    destruct (bad_fun_return res) eqn:Eb; injection He as <- <-; [congruence|].
    destruct (sr_code _ _ _ _ Hs El) as (Hca0 & pc0 & Hcp0 & Hl0).
    cbn [call_args] in Hca0. apply Bool.andb_true_iff in Hca0 as [_ Hcab].
    cbn [flatten] in Hcp0.
    destruct (flatten false p1 dest (stack_alloc.next_lab (Seq p1 body) 2) [] []) as [xs [nr1 m1]] eqn:F1.
    destruct (flatten false body dest m1 [] []) as [ys [nr2 m2]] eqn:F2.
    cbn [FST fst] in Hcp0. rewrite ?append_Append, ?append_List in Hcp0.
    rewrite <- ?app_assoc in Hcp0. cbn [app] in Hcp0.
    apply code_installed_append_imp in Hcp0 as [_ Hcp0]. cbn [code_installed is_Label] in Hcp0.
    destruct Hcp0 as [Hl1 Hcy].
    assert (Hlt : eval_lt (body, dec_clock s) (RawCall dest, s)) by (left; cbn [snd clock dec_clock set_clock]; lia).
    set (P1 := pc0 + LENGTH (FILTER (negb ∘ is_Label) (append xs))).
    set (t1' := upd_pc P1 (labSem.dec_clock t1)).
    apply (post_tail _ _ t1 t1' 0 _ (append ys) _ _ _ dest [] [] Eb); try reflexivity; try apply isPREFIX_REFL.
    + intros K. rewrite N.add_0_r. subst t1'.
      apply (jump_taken0 _ dest 1 (n2w 0) [] 0); [lia|eassumption|exact Hl1].
    + destruct (IH _ Hlt false res s' dest m1 [] [] t1' Ep Hr
                 ltac:(subst t1'; apply state_rel_with_pc, state_rel_dec_clock, Hs) Hcab
                 ltac:(cbn [fst]; rewrite F2; exact Hcy)
                 ltac:(subst t1'; cbn; rewrite Hl0; reflexivity)) as (ck & t2 & Hp).
      cbn [fst] in Hp. rewrite F2 in Hp. eauto.
Qed.


Lemma jumpreg_taken0 t r b l0 L1 p :
  labSem.clock t <> 0 ->
  asm_fetch t = SOME (Asm (Asmi (JumpReg r)) b l0) ->
  read_reg r t = Loc L1 0 ->
  loc_to_pc L1 0 (labSem.code t) = SOME p ->
  forall K, labSem.evaluate (labSem.set_clock (labSem.clock t + K) t) =
            labSem.evaluate (labSem.set_clock (labSem.clock (upd_pc p (labSem.dec_clock t)) + K)
                                (upd_pc p (labSem.dec_clock t))).
Proof.
  intros Hc Hf Hr Hl K. rewrite (lev_jumpreg _ r b l0); [|cbn; lia|exact Hf].
  cbn [labSem.regs labSem.code labSem.set_clock]. rewrite Hr, Hl, lupd_pc_clock.
  change (labSem.set_clock (labSem.clock (upd_pc p (labSem.dec_clock t)) + K) (upd_pc p (labSem.dec_clock t)))
    with (labSem.set_clock (labSem.clock t - 1 + K) (upd_pc p t)).
  f_equal. f_equal. lia.
Qed.

(** The jump of a [Call] (Galette helper): [compile_jump dest] reaches the
    code of the called function. *)
Lemma call_jump s t1 dest regs0 prog0 :
  state_rel s t1 -> labSem.clock t1 <> 0 ->
  (forall r, dest = inr r -> FLOOKUP regs0 r = FLOOKUP (regs s) r) ->
  find_code dest regs0 (code s) = SOME prog0 ->
  asm_fetch_aux (pc t1) (labSem.code t1) = SOME (compile_jump dest) ->
  exists loc pc0,
    lookup loc (code s) = SOME prog0 /\ loc_to_pc loc 0 (labSem.code t1) = SOME pc0 /\
    forall K, labSem.evaluate (labSem.set_clock (labSem.clock t1 + K) t1) =
              labSem.evaluate (labSem.set_clock (labSem.clock (upd_pc pc0 (labSem.dec_clock t1)) + K)
                                  (upd_pc pc0 (labSem.dec_clock t1))).
Proof.
  intros Hs Hc Hreg Hf Hfe. destruct dest as [d|r]; cbn [find_code compile_jump] in Hf, Hfe.
  - destruct (sr_code _ _ _ _ Hs Hf) as (_ & pc0 & _ & Hl).
    exists d, pc0. split; [exact Hf|]. split; [exact Hl|].
    apply (jump_taken0 _ d 0 (n2w 0) [] 0); [exact Hc|exact Hfe|exact Hl].
  - rewrite (Hreg r eq_refl) in Hf.
    destruct (FLOOKUP (regs s) r) as [[w|loc k]|] eqn:Er; try discriminate.
    destruct (k =? 0) eqn:Ek; [|discriminate]. apply N.eqb_eq in Ek; subst k.
    destruct (sr_code _ _ _ _ Hs Hf) as (_ & pc0 & _ & Hl).
    exists loc, pc0. split; [exact Hf|]. split; [exact Hl|].
    apply (jumpreg_taken0 _ r [] 0 loc); [exact Hc|exact Hfe|exact (sr_regs _ _ _ _ Hs Er)|exact Hl].
Qed.

Lemma fc_Call_none dest handler s :
  (forall y, eval_lt y (Call NONE dest handler, s) -> FC y) -> FC (Call NONE dest handler, s).
Proof.
  intros IH. fc_intro. rewrite evaluate_eqn in He. cbn [evaluate_body] in He.
  destruct (find_code dest (regs s) (code s)) as [prog0|] eqn:Ef; [|injection He as <- <-; congruence].
  destruct handler as [h|]; cbn [negb bool_decide decide option_eq_dec] in He.
  { replace (negb (bool_decide (SOME h = NONE))) with true in He
      by (symmetry; apply Bool.negb_true_iff; destruct (bool_decide _) eqn:X; [apply bool_decide_spec in X; discriminate|reflexivity]).
    injection He as <- <-; congruence. }
  replace (negb (bool_decide (@NONE (prog a * (N * N)) = NONE))) with false in He
    by (symmetry; apply Bool.negb_false_iff, bool_decide_spec; reflexivity).
  pose proof (sr_clock _ _ Hs) as Hc.
  fl_norm Hci. ci_split.
  destruct (clock s =? 0) eqn:Ec0.
  - injection He as <- <-. apply N.eqb_eq in Ec0. exists 0, t1.
    cbn [fc_post halt_view OPTION_MAP result_view]. post_split; try reflexivity; try apply isPREFIX_REFL.
    + intros ck1; rewrite N.add_0_r; reflexivity.
    + split; [|lia]. sr_destruct Hs. lab_cbn. stk_fields. exact Hffi.
  - apply N.eqb_neq in Ec0. rewrite fix_clock_evaluate in He.
    destruct (evaluate (prog0, dec_clock s)) as [res s'] eqn:Ep.
    destruct (bad_fun_return res) eqn:Eb; injection He as <- <-; [congruence|].
    destruct (call_jump s t1 dest (regs s) prog0 Hs ltac:(lia) (fun _ _ => eq_refl) Ef ltac:(eassumption))
      as (loc & pc0 & El & Hl & Hstep).
    destruct (sr_code _ _ _ _ Hs El) as (Hca0 & pc0' & Hcp0 & Hl0). rewrite Hl in Hl0. injection Hl0 as <-.
    assert (Hlt : eval_lt (prog0, dec_clock s) (Call NONE dest NONE, s)) by (left; cbn [snd clock dec_clock set_clock]; lia).
    set (t1' := upd_pc pc0 (labSem.dec_clock t1)).
    apply (post_tail _ _ t1 t1' 0 _ (append (FST (flatten true prog0 loc (stack_alloc.next_lab prog0 2) [] [])))
             _ _ _ loc [] [] Eb); try reflexivity; try apply isPREFIX_REFL.
    + intros K. rewrite N.add_0_r. apply Hstep.
    + exact (IH _ Hlt true res s' loc (stack_alloc.next_lab prog0 2) [] [] t1' Ep Hr
               ltac:(subst t1'; apply state_rel_with_pc, state_rel_dec_clock, Hs) Hca0 Hcp0
               ltac:(subst t1'; cbn; rewrite Hl; reflexivity)).
Qed.


Lemma fc_Call_some ret_handler lr l1 l2 dest handler s :
  (forall y, eval_lt y (Call (SOME (ret_handler, (lr, (l1, l2)))) dest handler, s) -> FC y) ->
  FC (Call (SOME (ret_handler, (lr, (l1, l2)))) dest handler, s).
Proof.
  intros IH. fc_intro. rewrite evaluate_eqn in He. cbn [evaluate_body] in He.
  destruct (find_code dest (regs s \\ lr) (code s)) as [prog0|] eqn:Ef; [|injection He as <- <-; congruence].
  pose proof (sr_clock _ _ Hs) as Hc.
  cbn [call_args] in Hca. apply Bool.andb_true_iff in Hca as [Hca Hcah].
  apply Bool.andb_true_iff in Hca as [Hcar Hlr]. apply bool_decide_spec in Hlr. subst lr.
  cbn [fst flatten] in Hci |- *.
  destruct (flatten false ret_handler n l cs bs) as [xs [nr1 m1]] eqn:F1.
  assert (Hci_pre : True -> code_installed (pc t1)
            ([LabAsm (labLang.LocValue (link_reg t1) (Lab l1 l2)) (n2w 0) [] 0; compile_jump dest; Label l1 l2 0]
             ++ append xs) (labSem.code t1)).
  { intros _. destruct handler as [[p2 [k1 k2]]|].
    - destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]]. cbn [FST fst] in Hci.
      rewrite !append_Append, !append_List in Hci. apply code_installed_append_imp in Hci as [Hci _].
      exact Hci.
    - cbn [FST fst] in Hci. rewrite !append_Append, !append_List in Hci. exact Hci. }
  pose proof (Hci_pre Logic.I) as Hcp. cbn [app] in Hcp. rename Hci into HciAll. revert HciAll. ci_split. intros HciAll.
  destruct (clock s =? 0) eqn:Ec0.
  { injection He as <- <-. apply N.eqb_eq in Ec0. exists 0, t1.
    cbn [fc_post halt_view OPTION_MAP result_view]. post_split; try reflexivity; try apply isPREFIX_REFL.
    + intros ck1; rewrite N.add_0_r; reflexivity.
    + split; [|lia]. sr_destruct Hs. lab_cbn. stk_fields. exact Hffi. }
  apply N.eqb_neq in Ec0. rewrite fix_clock_evaluate in He.
  set (s' := set_var (link_reg t1) (Loc l1 l2) s).
  set (ta := inc_pc (upd_reg (link_reg t1) (Loc l1 l2) t1)).
  assert (Hsa : state_rel s' ta) by (apply (state_rel_with_pc (pc t1 + 1)), set_var_upd_reg, Hs).
  assert (Ef' : find_code dest (regs s') (code s') = SOME prog0).
  { destruct dest as [d|rr]; [exact Ef|]. cbn [find_code] in Ef |- *. rewrite DOMSUB_FLOOKUP_THM in Ef.
    destruct (decide (link_reg t1 = rr)) as [E|Hne]; [discriminate Ef|].
    subst s'. unfold set_var. cbn [regs set_regs code]. rewrite FLOOKUP_UPDATE.
    destruct (decide (link_reg t1 = rr)); [contradiction|exact Ef]. }
  match goal with Hl : loc_to_pc l1 l2 (labSem.code t1) = SOME ?P |- _ => rename Hl into Hll end.
  destruct (call_jump s' ta dest (regs s') prog0 Hsa ltac:(subst ta; cbn; lia) (fun _ _ => eq_refl) Ef'
              ltac:(subst ta; cbn [pc inc_pc set_pc upd_reg labSem.set_regs labSem.code]; eassumption))
    as (loc & pc0 & El & Hl0 & Hstep).
  assert (Hl0t : loc_to_pc loc 0 (labSem.code t1) = SOME pc0) by exact Hl0.
  set (t1' := upd_pc pc0 (labSem.dec_clock ta)).
  assert (Hpre_sim : forall K, labSem.evaluate (labSem.set_clock (labSem.clock t1 + 1 + K) t1) =
                               labSem.evaluate (labSem.set_clock (labSem.clock t1' + K) t1')).
  { intros K. rewrite (lev_locvalue _ (link_reg t1) l1 l2 (n2w 0) [] 0); [|cbn; lia|eassumption].
    cbn [labSem.code labSem.set_clock]. rewrite Hll, lupd_reg_clock, linc_pc_clock.
    replace (labSem.clock t1 + 1 + K - 1) with (labSem.clock ta + K) by (subst ta; cbn; lia).
    exact (Hstep K). }
  assert (Hs1' : state_rel (dec_clock s') t1') by (apply state_rel_with_pc, state_rel_dec_clock, Hsa).
  destruct (sr_code _ _ _ _ Hsa El) as (Hca0 & pc0' & Hcp0 & Hl0'). rewrite Hl0 in Hl0'. injection Hl0' as <-.
  destruct (evaluate (prog0, dec_clock s')) as [res sP] eqn:Ep.
  assert (Hclt : clock (dec_clock s') < clock s) by (subst s'; cbn; lia).
  assert (HltP : eval_lt (prog0, dec_clock s') (Call (SOME (ret_handler, (link_reg t1, (l1, l2)))) dest handler, s))
    by (left; exact Hclt).
  assert (HPa : res <> SOME Error -> exists ck t2, fc_post res sP t1' t2 ck
            (append (FST (flatten true prog0 loc (stack_alloc.next_lab prog0 2) [] []))) loc [] []).
  { intros Hre. exact (IH _ HltP true res sP loc (stack_alloc.next_lab prog0 2) [] [] t1' Ep Hre Hs1'
      ltac:(subst t1' ta; exact Hca0) ltac:(subst t1' ta; exact Hcp0)
      ltac:(subst t1' ta; cbn; rewrite Hl0t; reflexivity)). }
  pose proof (evaluate_clock prog0 (dec_clock s') res sP Ep) as HcP.
  assert (T : len_reg t1' = len_reg t1 /\ ptr_reg t1' = ptr_reg t1 /\ len2_reg t1' = len2_reg t1 /\
              ptr2_reg t1' = ptr2_reg t1 /\ link_reg t1' = link_reg t1 /\ labSem.code t1' = labSem.code t1)
    by (subst t1' ta; repeat split).
  destruct T as (T1 & T2 & T3 & T4 & T5 & T6).
  (* the facts about the handler part of the code *)
  assert (Hhd : forall p2 k1 k2 ys nr2 m2, handler = SOME (p2, (k1, k2)) ->
            flatten false p2 n m1 cs bs = (ys, (nr2, m2)) ->
            asm_fetch_aux (pc t1 + 1 + 1 + LENGTH (FILTER (negb ∘ is_Label) (append xs))) (labSem.code t1) =
              SOME (LabAsm (Jump (Lab n m2)) (n2w 0) [] 0) /\
            loc_to_pc k1 k2 (labSem.code t1) =
              SOME (pc t1 + 1 + 1 + LENGTH (FILTER (negb ∘ is_Label) (append xs)) + 1) /\
            code_installed (pc t1 + 1 + 1 + LENGTH (FILTER (negb ∘ is_Label) (append xs)) + 1)
              (append ys) (labSem.code t1) /\
            loc_to_pc n m2 (labSem.code t1) =
              SOME (pc t1 + 1 + 1 + LENGTH (FILTER (negb ∘ is_Label) (append xs)) + 1 +
                    LENGTH (FILTER (negb ∘ is_Label) (append ys)))).
  { intros p2 k1 k2 ys nr2 m2 -> F2. clear -HciAll F2. rewrite F2 in HciAll. cbn [FST fst] in HciAll.
    rewrite ?append_Append, ?append_List in HciAll. rewrite <- ?app_assoc in HciAll. cbn [app] in HciAll.
    ci_split. repeat split; assumption. }
  change (evaluate (prog0, dec_clock (set_var (link_reg t1) (Loc l1 l2) s))) with (evaluate (prog0, dec_clock s')) in He.
  rewrite Ep in He. cbn beta iota zeta in He.
  assert (HltR : forall p', eval_lt (p', sP) (Call (SOME (ret_handler, (link_reg t1, (l1, l2)))) dest handler, s))
    by (intros p'; left; cbn [snd]; lia).
  destruct res as [x|]; [|injection He as <- <-; congruence].
  destruct x as [w|w|k|k|w| |f|].
  - (* Result *)
    destruct (negb (bool_decide (w = Loc l1 l2))) eqn:Ew; [injection He as <- <-; congruence|].
    apply Bool.negb_false_iff, bool_decide_spec in Ew. subst w.
    destruct (HPa ltac:(discriminate)) as (ckP & tP & HpP).
    cbn [fc_post halt_view OPTION_MAP result_view] in HpP.
    destruct HpP as (HevP & P1 & P2 & P3 & P4 & P5 & HpreP & _ & HwP).
    rewrite T6 in HpreP. rewrite T1 in P1. rewrite T2 in P2. rewrite T3 in P3. rewrite T4 in P4. rewrite T5 in P5.
    pose proof (loc_to_pc_isPREFIX _ _ _ _ _ (conj Hll HpreP)) as HllP.
    destruct (HwP _ HllP) as [HpcP HsP].
    assert (HsimP : forall K, labSem.evaluate (labSem.set_clock (labSem.clock t1 + (1 + ckP) + K) t1) =
                              labSem.evaluate (labSem.set_clock (labSem.clock tP + K) tP)).
    { intros K. replace (labSem.clock t1 + (1 + ckP) + K) with (labSem.clock t1 + 1 + (ckP + K)) by lia.
      rewrite Hpre_sim, N.add_assoc. apply HevP. }
    destruct (IH _ (HltR ret_handler) false r s2 n l cs bs tP He Hr HsP
                ltac:(cbn [fst]; rewrite P1, P2, P3, P4, P5; exact Hcar)
                ltac:(cbn [fst]; rewrite F1; cbn [FST fst]; rewrite <- HpcP;
                      exact (code_installed_isPREFIX _ _ _ _ (conj H1 HpreP)))
                (every_is_some_loc_to_pc_prefix _ _ _ _ (conj Hev HpreP))) as (ckR & tR & HpR).
    cbn [fst] in HpR. rewrite F1 in HpR. cbn [FST fst] in HpR.
    destruct handler as [[p2 [k1 k2]]|].
    + destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:F2.
      destruct (Hhd p2 k1 k2 ys nr2 m2 eq_refl F2) as (Hj & Hlk & Hcy & Hlm).
      cbn [FST fst]. rewrite ?append_Append, ?append_List. rewrite <- ?app_assoc. cbn [app].
      set (TAIL := LabAsm (Jump (Lab n m2)) (n2w 0) [] 0 :: Label k1 k2 0 :: append ys ++ [Label n m2 0]).
      destruct r as [r'|].
      * exists ((1 + ckP) + ckR), tR.
        apply (post_step _ _ t1 tP _ _ (1 + ckP) _ (append xs ++ TAIL) _ _ _ HsimP); try congruence; try exact HpreP.
        -- apply (post_lines _ _ _ _ _ (append xs)); [discriminate|exact HpR].
        -- rewrite <- HpcP. subst TAIL. len_tac.
      * pose proof HpR as HpR'. cbn [fc_post halt_view OPTION_MAP] in HpR'.
        destruct HpR' as (_ & _ & _ & _ & _ & _ & HpreR & HpcR & HsR).
        pose proof (isPREFIX_trans' _ _ _ HpreP HpreR) as Hpre1R.
        pose proof (afa_isPREFIX _ _ _ _ (conj Hj Hpre1R)) as Hj'.
        pose proof (loc_to_pc_isPREFIX _ _ _ _ _ (conj Hlm Hpre1R)) as Hlm'.
        exists ((1 + ckP) + (ckR + (1 + 0))),
          (upd_pc (pc t1 + 1 + 1 + LENGTH (FILTER (negb ∘ is_Label) (append xs)) + 1 +
                   LENGTH (FILTER (negb ∘ is_Label) (append ys))) tR).
        apply (post_step _ _ t1 tP _ _ (1 + ckP) _ (append xs ++ TAIL) _ _ _ HsimP); try congruence; try exact HpreP.
        -- eapply (post_trans _ _ _ _ _ _ _ _ (append xs) TAIL (append xs ++ TAIL)); [exact HpR| |].
           ++ eapply (post_jump_sub _ _ _ _ _ _ [] TAIL).
              ** eapply jump_taken; [|exact Hlm']. unfold asm_fetch. rewrite HpcR, <- HpcP. exact Hj'.
              ** apply post_refl, state_rel_with_pc, HsR.
              ** rewrite HpcR, <- HpcP. subst TAIL. len_tac.
           ++ rewrite LENGTH_FILTER_app. reflexivity.
        -- rewrite <- HpcP. len_tac.
    + exists ((1 + ckP) + ckR), tR. cbn [FST fst]. rewrite ?append_Append, ?append_List. cbn [app].
      apply (post_step _ _ t1 tP _ _ (1 + ckP) _ (append xs) _ _ _ HsimP HpR); try congruence; try exact HpreP.
      * rewrite <- HpcP. len_tac.
  - (* Exception *)
    destruct handler as [[p2 [k1 k2]]|].
    + destruct (negb (bool_decide (w = Loc k1 k2))) eqn:Ew; [injection He as <- <-; congruence|].
      apply Bool.negb_false_iff, bool_decide_spec in Ew. subst w.
      destruct (HPa ltac:(discriminate)) as (ckP & tP & HpP).
      cbn [fc_post halt_view OPTION_MAP result_view] in HpP.
      destruct HpP as (HevP & P1 & P2 & P3 & P4 & P5 & HpreP & _ & HwP).
      rewrite T6 in HpreP. rewrite T1 in P1. rewrite T2 in P2. rewrite T3 in P3. rewrite T4 in P4. rewrite T5 in P5.
      destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:F2.
      destruct (Hhd p2 k1 k2 ys nr2 m2 eq_refl F2) as (Hj & Hlk & Hcy & Hlm).
      pose proof (loc_to_pc_isPREFIX _ _ _ _ _ (conj Hlk HpreP)) as HlkP.
      destruct (HwP _ HlkP) as [HpcP HsP].
      assert (HsimP : forall K, labSem.evaluate (labSem.set_clock (labSem.clock t1 + (1 + ckP) + K) t1) =
                                labSem.evaluate (labSem.set_clock (labSem.clock tP + K) tP)).
      { intros K. replace (labSem.clock t1 + (1 + ckP) + K) with (labSem.clock t1 + 1 + (ckP + K)) by lia.
        rewrite Hpre_sim, N.add_assoc. apply HevP. }
      cbn [call_args] in Hcah.
      destruct (IH _ (HltR p2) false r s2 n m1 cs bs tP He Hr HsP
                  ltac:(cbn [fst]; rewrite P1, P2, P3, P4, P5; exact Hcah)
                  ltac:(cbn [fst]; rewrite F2; cbn [FST fst]; rewrite <- HpcP;
                        exact (code_installed_isPREFIX _ _ _ _ (conj Hcy HpreP)))
                  (every_is_some_loc_to_pc_prefix _ _ _ _ (conj Hev HpreP))) as (ckH & tH & HpH).
      cbn [fst] in HpH. rewrite F2 in HpH. cbn [FST fst] in HpH.
      exists ((1 + ckP) + ckH), tH. cbn [FST fst].
      rewrite ?append_Append, ?append_List. rewrite <- ?app_assoc. cbn [app].
      apply (post_step _ _ t1 tP _ _ (1 + ckP) _ (append ys) _ _ _ HsimP HpH); try congruence; try exact HpreP.
      * rewrite <- HpcP. len_tac.
    + injection He as <- <-.
      apply (post_tail _ _ t1 t1' 1 _ (append (FST (flatten true prog0 loc (stack_alloc.next_lab prog0 2) [] []))) _ _ _ loc [] []); [reflexivity|exact Hpre_sim| | | | | | |];
        try congruence; [rewrite T6; apply isPREFIX_REFL|exact (HPa ltac:(discriminate))].
  - injection He as <- <-; congruence.
  - injection He as <- <-; congruence.
  - injection He as <- <-.
    apply (post_tail _ _ t1 t1' 1 _ (append (FST (flatten true prog0 loc (stack_alloc.next_lab prog0 2) [] []))) _ _ _ loc [] []); [reflexivity|exact Hpre_sim| | | | | | |];
      try congruence; [rewrite T6; apply isPREFIX_REFL|exact (HPa ltac:(discriminate))].
  - injection He as <- <-.
    apply (post_tail _ _ t1 t1' 1 _ (append (FST (flatten true prog0 loc (stack_alloc.next_lab prog0 2) [] []))) _ _ _ loc [] []); [reflexivity|exact Hpre_sim| | | | | | |];
      try congruence; [rewrite T6; apply isPREFIX_REFL|exact (HPa ltac:(discriminate))].
  - injection He as <- <-.
    apply (post_tail _ _ t1 t1' 1 _ (append (FST (flatten true prog0 loc (stack_alloc.next_lab prog0 2) [] []))) _ _ _ loc [] []); [reflexivity|exact Hpre_sim| | | | | | |];
      try congruence; [rewrite T6; apply isPREFIX_REFL|exact (HPa ltac:(discriminate))].
  - injection He as <- <-; congruence.
Qed.


Lemma lev_callffi t idx w0 b l0 :
  labSem.clock t <> 0 -> asm_fetch t = SOME (LabAsm (CallFFI idx) w0 b l0) ->
  labSem.evaluate t =
  match labSem.regs t (len_reg t), labSem.regs t (ptr_reg t), labSem.regs t (len2_reg t),
        labSem.regs t (ptr2_reg t), labSem.regs t (link_reg t) with
  | Word w, Word w2, Word w3, Word w4, Loc n1 n2 =>
      match read_bytearray w2 (w2n w) (mem_load_byte_aux (mem t) (mem_domain t) (labSem.be t)),
            read_bytearray w4 (w2n w3) (mem_load_byte_aux (mem t) (mem_domain t) (labSem.be t)),
            loc_to_pc n1 n2 (labSem.code t) with
      | SOME bytes, SOME bytes2, SOME new_pc =>
          match call_FFI (labSem.ffi t) (ExtCall idx) bytes bytes2 with
          | FFI_final outcome => (targetSem.Halt (FFI_outcome outcome), t)
          | FFI_return new_ffi new_bytes =>
              labSem.evaluate (labSem.mk_state
                     (fun a0 => targetSem.get_reg_value (io_regs t 0 (ExtCall idx) a0) (labSem.regs t a0) Word)
                     (fun n => io_fp_regs t 0 n)
                     (write_bytearray w4 new_bytes (mem t) (mem_domain t) (labSem.be t))
                     (mem_domain t) (shared_mem_domain t) new_pc (labSem.be t) new_ffi
                     (shift_seq 1 (io_regs t)) (cc_regs t) (shift_seq 1 (io_fp_regs t)) (cc_fp_regs t)
                     (labSem.code t) (labSem.compile t) (labSem.compile_oracle t) (labSem.code_buffer t)
                     (labSem.clock t - 1) (failed t) (ptr_reg t) (len_reg t) (ptr2_reg t) (len2_reg t)
                     (link_reg t))
          end
      | _, _, _ => (targetSem.Error, t)
      end
  | _, _, _, _, _ => (targetSem.Error, t)
  end.
Proof. intros Hc Hf. rewrite labSem.evaluate_def, (proj2 (N.eqb_neq _ _) Hc), Hf. reflexivity. Qed.

Lemma fc_FFI idx ptr len ptr2 len2 ret s : FC (FFI idx ptr len ptr2 len2 ret, s).
Proof.
  fc_intro. rewrite evaluate_eqn in He. cbn [evaluate_body] in He. unfold get_var in He.
  cbn [call_args] in Hca. repeat (apply Bool.andb_true_iff in Hca as [Hca ?]).
  repeat match goal with H : bool_decide (_ = _) = true |- _ => apply bool_decide_spec in H; subst end.
  pose proof Hs as Hs'. sr_destruct Hs'.
  destruct (FLOOKUP (regs s) (len_reg t1)) as [[w|]|] eqn:E1; try (injection He as <- <-; congruence).
  destruct (FLOOKUP (regs s) (ptr_reg t1)) as [[w2|]|] eqn:E2; try (injection He as <- <-; congruence).
  destruct (FLOOKUP (regs s) (len2_reg t1)) as [[w3|]|] eqn:E3; try (injection He as <- <-; congruence).
  destruct (FLOOKUP (regs s) (ptr2_reg t1)) as [[w4|]|] eqn:E4; try (injection He as <- <-; congruence).
  destruct (read_bytearray w2 (w2n w) (mem_load_byte_aux (memory s) (mdomain s) (be s))) as [bytes|] eqn:B1;
    [|injection He as <- <-; congruence].
  destruct (read_bytearray w4 (w2n w3) (mem_load_byte_aux (memory s) (mdomain s) (be s))) as [bytes2|] eqn:B2;
    [|injection He as <- <-; congruence].
  fl_norm Hci. ci_split.
  match goal with Hl : loc_to_pc n l (labSem.code t1) = SOME ?P |- _ => rename Hl into Hll end.
  set (ta := inc_pc (upd_reg (link_reg t1) (Loc n l) t1)).
  assert (Hst1 : forall K, labSem.evaluate (labSem.set_clock (labSem.clock t1 + 1 + K) t1) =
                           labSem.evaluate (labSem.set_clock (labSem.clock t1 + K) ta)).
  { intros K. rewrite (lev_locvalue _ (link_reg t1) n l (n2w 0) [] 0); [|cbn; lia|eassumption].
    cbn [labSem.code labSem.set_clock]. rewrite Hll, lupd_reg_clock, linc_pc_clock.
    f_equal. f_equal. lia. }
  assert (Rta : forall k, k <> link_reg t1 -> labSem.regs ta k = labSem.regs t1 k).
  { intros k Hk. subst ta. cbn [inc_pc set_pc upd_reg labSem.set_regs labSem.regs].
    rewrite APPLY_UPDATE_THM. destruct (decide (link_reg t1 = k)); [congruence|reflexivity]. }
  assert (Hlink : labSem.regs ta (link_reg t1) = Loc n l).
  { subst ta. cbn [inc_pc set_pc upd_reg labSem.set_regs labSem.regs]. rewrite APPLY_UPDATE_THM.
    destruct (decide (link_reg t1 = link_reg t1)); [reflexivity|congruence]. }
  assert (Hstep2 : forall K, labSem.evaluate (labSem.set_clock (labSem.clock t1 + 1 + K) ta) =
     match call_FFI (ffi s) (ExtCall idx) bytes bytes2 with
     | FFI_final outcome => (targetSem.Halt (FFI_outcome outcome), labSem.set_clock (labSem.clock t1 + 1 + K) ta)
     | FFI_return new_ffi new_bytes =>
         labSem.evaluate (labSem.mk_state
            (fun a0 => targetSem.get_reg_value (io_regs t1 0 (ExtCall idx) a0) (labSem.regs ta a0) Word)
            (fun n => io_fp_regs t1 0 n)
            (write_bytearray w4 new_bytes (memory s) (mdomain s) (be s))
            (mdomain s) (shared_mem_domain t1) (pc t1 + 1 + 1) (be s) new_ffi
            (shift_seq 1 (io_regs t1)) (cc_regs t1) (shift_seq 1 (io_fp_regs t1)) (cc_fp_regs t1)
            (labSem.code t1) (labSem.compile t1) (labSem.compile_oracle t1) (labSem.code_buffer t1)
            (labSem.clock t1 + K) (failed t1) (ptr_reg t1) (len_reg t1) (ptr2_reg t1) (len2_reg t1)
            (link_reg t1))
     end).
  { intros K. rewrite (lev_callffi _ idx (n2w 0) [] 0); [|cbn; lia|subst ta; cbn; eassumption].
    cbn [labSem.regs labSem.set_clock len_reg ptr_reg len2_reg ptr2_reg link_reg].
    change (len_reg ta) with (len_reg t1). change (ptr_reg ta) with (ptr_reg t1).
    change (len2_reg ta) with (len2_reg t1). change (ptr2_reg ta) with (ptr2_reg t1).
    change (link_reg ta) with (link_reg t1).
    rewrite (Rta _ (not_eq_sym Hl1)), (Rta _ (not_eq_sym Hl2)), (Rta _ (not_eq_sym Hl3)), (Rta _ (not_eq_sym Hl4)), Hlink.
    rewrite (sr_regs _ _ _ _ Hs E1), (sr_regs _ _ _ _ Hs E2), (sr_regs _ _ _ _ Hs E3), (sr_regs _ _ _ _ Hs E4).
    change (mem (labSem.set_clock (labSem.clock t1 + 1 + K) ta)) with (mem t1).
    change (mem_domain (labSem.set_clock (labSem.clock t1 + 1 + K) ta)) with (mem_domain t1).
    change (labSem.be (labSem.set_clock (labSem.clock t1 + 1 + K) ta)) with (labSem.be t1).
    change (labSem.code (labSem.set_clock (labSem.clock t1 + 1 + K) ta)) with (labSem.code t1).
    change (labSem.ffi (labSem.set_clock (labSem.clock t1 + 1 + K) ta)) with (labSem.ffi t1).
    rewrite Hmem, Hmd, Hbe, Hffi, B1, B2, Hll.
    destruct (call_FFI (ffi s) (ExtCall idx) bytes bytes2); [|reflexivity].
    apply (f_equal labSem.evaluate). apply state_eq_intro.
    all: try (cbn [labSem.clock labSem.set_clock]; lia).
    all: reflexivity. }
  destruct (call_FFI (ffi s) (ExtCall idx) bytes bytes2) as [new_ffi new_bytes|outcome] eqn:Ecf;
    injection He as <- <-.
  - set (t2 := labSem.mk_state
            (fun a0 => targetSem.get_reg_value (io_regs t1 0 (ExtCall idx) a0) (labSem.regs ta a0) Word)
            (fun n => io_fp_regs t1 0 n)
            (write_bytearray w4 new_bytes (memory s) (mdomain s) (be s))
            (mdomain s) (shared_mem_domain t1) (pc t1 + 1 + 1) (be s) new_ffi
            (shift_seq 1 (io_regs t1)) (cc_regs t1) (shift_seq 1 (io_fp_regs t1)) (cc_fp_regs t1)
            (labSem.code t1) (labSem.compile t1) (labSem.compile_oracle t1) (labSem.code_buffer t1)
            (labSem.clock t1) (failed t1) (ptr_reg t1) (len_reg t1) (ptr2_reg t1) (len2_reg t1)
            (link_reg t1)).
    exists (1 + 1), t2. cbn [fc_post halt_view OPTION_MAP]. post_split; try reflexivity; try apply isPREFIX_REFL.
    + intros ck1. replace (labSem.clock t1 + (1 + 1) + ck1) with (labSem.clock t1 + 1 + (1 + ck1)) by lia.
      rewrite Hst1. replace (labSem.clock t1 + (1 + ck1)) with (labSem.clock t1 + 1 + ck1) by lia.
      rewrite Hstep2. reflexivity.
    + split; [cbn; lia|].
      subst t2. unfold state_rel. lab_cbn. stk_fields.
      refine (conj _ (conj _ (conj eq_refl (conj eq_refl (conj Hsmd (conj eq_refl (conj eq_refl (conj Hclk
        (conj Hcode (conj Hdom (conj Hsok (conj Hfail (conj Hl1 (conj Hl2 (conj Hl3 (conj Hl4 (conj Hlsr
        (conj _ (conj Hcc (conj Hal (conj Hsal (conj Hcb (conj Hcomp (conj Hco (conj Hcos (conj Hus
        (conj Hust (conj Hua Hgd)))))))))))))))))))))))))))).
      * intros k v Hk. rewrite FLOOKUP_DRESTRICT in Hk. destruct (classical_dec _) as [Hin|]; [|discriminate].
        rewrite (Hio k (ExtCall idx) 0 Hin). cbn [targetSem.get_reg_value].
        rewrite Rta by (intros ->; exact (Hlsr Hin)). exact (Hregs k v Hk).
      * intros k v Hk. discriminate Hk.
      * intros k i n0 Hk. unfold shift_seq. exact (Hio k i (n0 + 1) Hk).
  - exists (1 + 1), (labSem.set_clock (labSem.clock t1 + 1 + 0) ta). cbn [fc_post halt_view].
    split.
    + replace (labSem.clock t1 + (1 + 1)) with (labSem.clock t1 + 1 + (1 + 0)) by lia.
      rewrite Hst1. replace (labSem.clock t1 + (1 + 0)) with (labSem.clock t1 + 1 + 0) by lia.
      rewrite Hstep2. reflexivity.
    + subst ta. cbn. exact Hffi.
Qed.


Lemma word_to_bytes_aux_hd n (w : word a) be :
  n <> 0 -> exists rest, word_to_bytes_aux n w be = get_byte (n2w 0) w be :: rest.
Proof.
  induction n as [|n IH] using N.peano_ind; intros Hn; [congruence|].
  rewrite (proj2 (word_to_bytes_aux_def n w be)).
  destruct (N.eq_dec n 0) as [->|Hn0].
  - exists []. rewrite (proj1 (word_to_bytes_aux_def 0 w be)). reflexivity.
  - destruct (IH Hn0) as [rest ->]. eexists. reflexivity.
Qed.

Lemma TAKE1_word_to_bytes (w : word a) be :
  good_dimindex a -> TAKE 1 (word_to_bytes w be) = [get_byte (n2w 0) w be].
Proof.
  intros Hg. unfold word_to_bytes.
  destruct (word_to_bytes_aux_hd (dimindex a DIV 8) w be) as [rest ->].
  - destruct Hg as [Hg|Hg]; rewrite Hg; discriminate.
  - destruct rest; reflexivity.
Qed.

Lemma lev_shm t op r ad b l0 :
  labSem.clock t <> 0 -> asm_fetch t = SOME (Asm (ShareMem op r ad) b l0) ->
  labSem.evaluate t =
  match share_mem_op op r ad t with
  | SOME (FFI_final outcome, s') => (targetSem.Halt (FFI_outcome outcome), s')
  | SOME (FFI_return _ _, s') =>
      labSem.evaluate (set_io_fp_regs (shift_seq 1 (io_fp_regs s'))
                         (set_io_regs (shift_seq 1 (io_regs s')) s'))
  | NONE => (targetSem.Error, t)
  end.
Proof. intros Hc Hf. rewrite labSem.evaluate_def, (proj2 (N.eqb_neq _ _) Hc), Hf. reflexivity. Qed.

Ltac hsplit H :=
  repeat match type of H with
         | context [match ?x with _ => _ end] =>
             let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H; try discriminate H
         end.

Definition shm_ok (res : option (result a)) s s' t (op : memop) r ad w : Prop :=
  match res with
  | SOME (FinalFFI o) => share_mem_op op r (Addr ad w) t = SOME (FFI_final o, t) /\ ffi s' = ffi s
  | NONE => exists f l t', share_mem_op op r (Addr ad w) t = SOME (FFI_return f l, t') /\
              state_rel s' (set_io_fp_regs (shift_seq 1 (io_fp_regs t'))
                              (set_io_regs (shift_seq 1 (io_regs t')) t')) /\
              pc t' = pc t + 1 /\ labSem.code t' = labSem.code t /\
              labSem.clock t' = labSem.clock t - 1 /\
              len_reg t' = len_reg t /\ ptr_reg t' = ptr_reg t /\ len2_reg t' = len2_reg t /\
              ptr2_reg t' = ptr2_reg t /\ link_reg t' = link_reg t
  | _ => False
  end.

Lemma shm_sim op r ad (w v : word a) s t res s' :
  state_rel s t -> FLOOKUP (regs s) ad = SOME (Word v) ->
  sh_mem_op op r (v + w)%w (dec_clock s) = (res, s') -> res <> SOME Error ->
  shm_ok res s s' t op r ad w.
Proof.
  intros Hs Ead Hop Hres. pose proof Hs as Hs'. sr_destruct Hs'.
  pose proof (sr_regs _ _ _ _ Hs Ead) as Rad.
  assert (Haddr : addr (Addr ad w) t = SOME (v + w)%w) by (cbn; rewrite Rad; reflexivity).
  destruct op; cbn [sh_mem_op share_mem_op] in Hop |- *;
    unfold sh_mem_load, sh_mem_store, sh_mem_load_byte, sh_mem_store_byte, sh_mem_load16,
      sh_mem_store16, sh_mem_load32, sh_mem_store32 in Hop;
    unfold share_mem_load, share_mem_store.
  all: unfold get_var in Hop; cbn [dec_clock regs set_clock sh_mdomain ffi] in Hop.
  all: hsplit Hop; injection Hop as <- <-; try congruence.
  all: unfold shm_ok.
  all: cbn [share_mem_op]; unfold share_mem_load, share_mem_store; rewrite Haddr; cbn beta iota.
  all: repeat match goal with
       | E : FLOOKUP (regs ?ss) ?rr = SOME (Word ?w') |- context [labSem.regs ?tt ?rr] =>
           rewrite (sr_regs _ _ _ _ Hs E)
       end; cbn beta iota.
  all: rewrite ?Hsmd, ?Hffi.
  all: repeat match goal with
       | i : ?x IN sh_mdomain ?ss |- context [w2n ?x MOD (dimindex ?aa DIV 8) =? 0] => rewrite (Hsal _ i), N.eqb_refl
       end; cbn [andb].
  all: repeat match goal with
       | |- context [bool_decide ?P] => replace (bool_decide P) with true by (symmetry; apply bool_decide_spec; assumption)
       end; cbn beta iota.
  all: cbn [N.eqb Pos.eqb]; rewrite ?(TAKE1_word_to_bytes _ _ Hgd).
  all: match goal with E : call_FFI _ _ _ _ = _ |- _ => rewrite E end; cbn beta iota.
  all: try (split; [reflexivity|stk_fields; reflexivity]).
  all: eexists _, _, _; split; [reflexivity|].
  all: split; [|repeat split; cbn; try lia].
  all: sr_split; try assumption; try reflexivity; try (rewrite Hclk; reflexivity).
  all: try (intros k i0 n0 Hk; unfold shift_seq; exact (Hio k i0 (n0 + 1) Hk)).
  all: try (intros n0 v0 Hn0; rewrite FLOOKUP_UPDATE in Hn0; rewrite APPLY_UPDATE_THM;
            match goal with |- context [decide (?rr = n0)] =>
              destruct (decide (rr = n0)); [congruence|exact (Hregs n0 v0 Hn0)] end).
Qed.


Lemma lset_io_clock t x y k :
  set_io_fp_regs x (set_io_regs y (labSem.set_clock k t)) = labSem.set_clock k (set_io_fp_regs x (set_io_regs y t)).
Proof. reflexivity. Qed.

Lemma fc_ShMemOp op r0 ad0 s : FC (ShMemOp op r0 ad0, s).
Proof.
  fc_intro. destruct ad0 as [ad w]. rewrite evaluate_eqn in He. cbn [evaluate_body] in He.
  rewrite word_exp_addr in He.
  destruct (FLOOKUP (regs s) ad) as [[v|]|] eqn:Ead; try (injection He as <- <-; congruence).
  fl_norm Hci. ci_split. pose proof (sr_clock _ _ Hs) as Hc.
  destruct (clock s =? 0) eqn:Ec0.
  - injection He as <- <-. apply N.eqb_eq in Ec0. exists 0, t1.
    cbn [fc_post halt_view OPTION_MAP result_view]. post_split; try reflexivity; try apply isPREFIX_REFL.
    + intros ck1; rewrite N.add_0_r; reflexivity.
    + split; [|lia]. sr_destruct Hs. lab_cbn. stk_fields. exact Hffi.
  - apply N.eqb_neq in Ec0. pose proof (shm_sim op r0 ad w v s t1 r s2 Hs Ead He Hr) as Hok.
    unfold shm_ok in Hok. destruct r as [x|].
    + destruct x; try contradiction. destruct Hok as [Hsh Hf].
      exists 0, t1. cbn [fc_post halt_view]. split.
      * rewrite N.add_0_r, lset_clock_same. rewrite (lev_shm _ op r0 (Addr ad w) [] 0); [|lia|eassumption].
        rewrite Hsh. reflexivity.
      * rewrite Hf. sr_destruct Hs. exact Hffi.
    + destruct Hok as (f & l' & t' & Hsh & Hsr & Hpc & Hcd & Hck & R1 & R2 & R3 & R4 & R5).
      exists 0, (set_io_fp_regs (shift_seq 1 (io_fp_regs t')) (set_io_regs (shift_seq 1 (io_regs t')) t')).
      cbn [fc_post halt_view OPTION_MAP]. post_split; try assumption.
      * intros ck1. rewrite (lev_shm _ op r0 (Addr ad w) [] 0); [|cbn; lia|eassumption].
        rewrite share_mem_op_set_clock, Hsh. cbn beta iota. rewrite lset_io_clock.
        cbn [io_fp_regs io_regs labSem.set_clock].
        change (labSem.clock (set_io_fp_regs (shift_seq 1 (io_fp_regs t')) (set_io_regs (shift_seq 1 (io_regs t')) t')))
          with (labSem.clock t').
        f_equal. f_equal. lia.
      * cbn. rewrite Hcd. apply isPREFIX_REFL.
      * split; [|exact Hsr]. cbn [pc set_io_fp_regs set_io_regs]. rewrite Hpc. cbn. lia.
Qed.


Lemma lev_install t w0 b l0 :
  labSem.clock t <> 0 -> asm_fetch t = SOME (LabAsm labLang.Install w0 b l0) ->
  labSem.evaluate t =
  match labSem.regs t (ptr_reg t), labSem.regs t (len_reg t), labSem.regs t (link_reg t) with
  | Word w1, Word w2, Loc n1 n2 =>
      match buffer_flush (labSem.code_buffer t) w1 w2, loc_to_pc n1 n2 (labSem.code t) with
      | SOME (bytes, cb), SOME new_pc =>
          let '(cfg, prog0) := labSem.compile_oracle t 0 in
          let new_oracle := shift_seq 1 (labSem.compile_oracle t) in
          match labSem.compile t cfg prog0, prog0 with
          | SOME (bytes', cfg'), Section_ k _ :: _ =>
              if andb (bool_decide (bytes = bytes')) ⌜FST (new_oracle 0) = cfg'⌝ then
                labSem.evaluate (labSem.mk_state
                       ((ptr_reg t =+ Loc k 0)
                          (fun a0 => targetSem.get_reg_value (cc_regs t 0 a0) (labSem.regs t a0) Word))
                       (fun n => cc_fp_regs t 0 n)
                       (mem t) (mem_domain t) (shared_mem_domain t) new_pc (labSem.be t) (labSem.ffi t)
                       (io_regs t) (shift_seq 1 (cc_regs t)) (io_fp_regs t)
                       (shift_seq 1 (cc_fp_regs t)) (labSem.code t ++ prog0) (labSem.compile t) new_oracle
                       cb (labSem.clock t - 1) (failed t) (ptr_reg t) (len_reg t) (ptr2_reg t)
                       (len2_reg t) (link_reg t))
              else (targetSem.Error, t)
          | _, _ => (targetSem.Error, t)
          end
      | _, _ => (targetSem.Error, t)
      end
  | _, _, _ => (targetSem.Error, t)
  end.
Proof. intros Hc Hf. rewrite labSem.evaluate_def, (proj2 (N.eqb_neq _ _) Hc), Hf. reflexivity. Qed.

Lemma fc_Install ptr len dptr dlen ret s : FC (stackLang.Install ptr len dptr dlen ret, s).
Proof.
  fc_intro. pose proof Hs as Hs'. sr_destruct Hs'.
  cbn [call_args] in Hca. repeat (apply Bool.andb_true_iff in Hca as [Hca ?]).
  repeat match goal with H : bool_decide (_ = _) = true |- _ => apply bool_decide_spec in H; subst end.
  rewrite evaluate_eqn in He. cbn [evaluate_body] in He. unfold get_var in He.
  apply Bool.not_true_iff_false in Hus. rewrite Hus in He.
  destruct (FLOOKUP (regs s) (ptr_reg t1)) as [[w1|]|] eqn:E1; try (injection He as <- <-; congruence).
  destruct (FLOOKUP (regs s) (len_reg t1)) as [[w2|]|] eqn:E2; try (injection He as <- <-; congruence).
  destruct (FLOOKUP (regs s) dptr) as [[w3|]|] eqn:E3; try (injection He as <- <-; congruence).
  destruct (FLOOKUP (regs s) dlen) as [[w4|]|] eqn:E4; try (injection He as <- <-; congruence).
  destruct (compile_oracle s 0) as [cfg [progs bm]] eqn:Eo.
  destruct (buffer_flush (code_buffer s) w1 w2) as [[bytes cb]|] eqn:Eb; [|injection He as <- <-; congruence].
  cbn beta iota zeta in He.
  destruct (compile s cfg progs) as [[bytes' cfg']|] eqn:Ec; [|injection He as <- <-; congruence].
  destruct progs as [|[k prog0] progs']; [injection He as <- <-; congruence|].
  destruct (andb (andb (bool_decide (bytes = bytes')) (bool_decide (bm = bm)))
            ⌜FST (shift_seq 1 (compile_oracle s) 0) = cfg'⌝) eqn:Econd; [|injection He as <- <-; congruence].
  injection He as <- <-.
  apply Bool.andb_true_iff in Econd as [Econd Ecfg]. apply Bool.andb_true_iff in Econd as [Ebytes _].
  apply bool_decide_spec in Ebytes. subst bytes'.
  fl_norm Hci. ci_split.
  match goal with Hl : loc_to_pc n l (labSem.code t1) = SOME ?P |- _ => rename Hl into Hll end.
  set (ta := inc_pc (upd_reg (link_reg t1) (Loc n l) t1)).
  assert (Hst1 : forall K, labSem.evaluate (labSem.set_clock (labSem.clock t1 + 1 + K) t1) =
                           labSem.evaluate (labSem.set_clock (labSem.clock t1 + K) ta)).
  { intros K. rewrite (lev_locvalue _ (link_reg t1) n l (n2w 0) [] 0); [|cbn; lia|eassumption].
    cbn [labSem.code labSem.set_clock]. rewrite Hll, lupd_reg_clock, linc_pc_clock.
    f_equal. f_equal. lia. }
  assert (Rta : forall k0, k0 <> link_reg t1 -> labSem.regs ta k0 = labSem.regs t1 k0).
  { intros k0 Hk. subst ta. cbn [inc_pc set_pc upd_reg labSem.set_regs labSem.regs].
    rewrite APPLY_UPDATE_THM. destruct (decide (link_reg t1 = k0)); [congruence|reflexivity]. }
  assert (Hlink : labSem.regs ta (link_reg t1) = Loc n l).
  { subst ta. cbn [inc_pc set_pc upd_reg labSem.set_regs labSem.regs]. rewrite APPLY_UPDATE_THM.
    destruct (decide (link_reg t1 = link_reg t1)); [reflexivity|congruence]. }
  assert (Hsec : exists lines, prog_to_section (k, prog0) = Section_ k lines).
  { rewrite prog_to_section_eq. eauto. }
  destruct Hsec as [lines Hsec].
  destruct (compile_oracle s (0 + 1)) as [cfg1 [progs1 bm1]] eqn:Eo1.
  assert (Ecfg' : cfg1 = cfg').
  { apply bool_decide_spec in Ecfg. unfold shift_seq in Ecfg. rewrite Eo1 in Ecfg. exact Ecfg. }
  assert (Hcompile : labSem.compile t1 cfg (MAP prog_to_section ((k, prog0) :: progs')) = SOME (bytes, cfg')).
  { rewrite <- Ec, Hcomp. reflexivity. }
  set (NC := labSem.code t1 ++ MAP prog_to_section ((k, prog0) :: progs')).
  assert (Hstep2 : forall K, labSem.evaluate (labSem.set_clock (labSem.clock t1 + 1 + K) ta) =
     labSem.evaluate (labSem.mk_state
        ((ptr_reg t1 =+ Loc k 0)
           (fun a0 => targetSem.get_reg_value (cc_regs t1 0 a0) (labSem.regs ta a0) Word))
        (fun n => cc_fp_regs t1 0 n)
        (mem t1) (mem_domain t1) (shared_mem_domain t1) (pc t1 + 1 + 1) (labSem.be t1) (labSem.ffi t1)
        (io_regs t1) (shift_seq 1 (cc_regs t1)) (io_fp_regs t1)
        (shift_seq 1 (cc_fp_regs t1)) NC (labSem.compile t1) (shift_seq 1 (labSem.compile_oracle t1))
        cb (labSem.clock t1 + K) (failed t1) (ptr_reg t1) (len_reg t1) (ptr2_reg t1)
        (len2_reg t1) (link_reg t1))).
  { intros K. rewrite (lev_install _ (n2w 0) [] 0); [|cbn; lia|subst ta; cbn; eassumption].
    cbn [labSem.regs labSem.set_clock ptr_reg len_reg link_reg labSem.code_buffer labSem.code
         labSem.compile_oracle labSem.compile].
    change (ptr_reg ta) with (ptr_reg t1). change (len_reg ta) with (len_reg t1).
    change (link_reg ta) with (link_reg t1).
    rewrite (Rta _ (not_eq_sym Hl2)), (Rta _ (not_eq_sym Hl1)), Hlink.
    rewrite (sr_regs _ _ _ _ Hs E1), (sr_regs _ _ _ _ Hs E2).
    change (labSem.code_buffer ta) with (labSem.code_buffer t1). rewrite <- Hcb, Eb.
    change (labSem.code ta) with (labSem.code t1). rewrite Hll.
    change (labSem.compile_oracle ta) with (labSem.compile_oracle t1).
    rewrite Hco. cbn beta. rewrite Eo. cbn beta iota zeta.
    change (labSem.compile ta) with (labSem.compile t1). rewrite Hcompile.
    cbn [List.map]. rewrite Hsec. cbn beta iota.
    match goal with |- context [@bool_decide (bytes = bytes) ?d] =>
      replace (@bool_decide (bytes = bytes) d) with true by (symmetry; apply bool_decide_spec; reflexivity) end.
    match goal with |- context [@bool_decide (FST ?X = cfg') ?d] =>
      replace (@bool_decide (FST X = cfg') d) with true
        by (symmetry; apply bool_decide_spec; unfold shift_seq; cbn beta; rewrite Eo1; cbn; exact Ecfg') end.
    cbn [andb]. apply (f_equal labSem.evaluate). apply state_eq_intro.
    all: try (cbn [labSem.clock labSem.set_clock]; lia).
    all: try reflexivity.
    subst NC. cbn [List.map]. rewrite Hsec. reflexivity. }
  set (t2 := labSem.mk_state
        ((ptr_reg t1 =+ Loc k 0)
           (fun a0 => targetSem.get_reg_value (cc_regs t1 0 a0) (labSem.regs ta a0) Word))
        (fun n => cc_fp_regs t1 0 n)
        (mem t1) (mem_domain t1) (shared_mem_domain t1) (pc t1 + 1 + 1) (labSem.be t1) (labSem.ffi t1)
        (io_regs t1) (shift_seq 1 (cc_regs t1)) (io_fp_regs t1)
        (shift_seq 1 (cc_fp_regs t1)) NC (labSem.compile t1) (shift_seq 1 (labSem.compile_oracle t1))
        cb (labSem.clock t1) (failed t1) (ptr_reg t1) (len_reg t1) (ptr2_reg t1)
        (len2_reg t1) (link_reg t1)).
  (* facts about the new code *)
  pose proof (Hcos 0) as Hc0. rewrite Eo in Hc0. destruct Hc0 as [Hc0e Hc0d].
  assert (Hlok : labels_ok (MAP prog_to_section ((k, prog0) :: progs'))).
  { apply prog_to_section_labels_ok. split; [|exact Hc0d].
    unfold is_true in *. rewrite EVERY_Forall in Hc0e |- *. eapply Forall_impl; [|exact Hc0e].
    intros [n1 p1] Hx. cbn zeta. apply Bool.andb_true_iff in Hx as [Hx Hx']. apply Bool.andb_true_iff in Hx as [_ Hx].
    rewrite Hx, Hx'. reflexivity. }
  destruct (labels_ok_imp _ Hlok) as (Hlok1 & Hlok2 & _).
  exists (1 + 1), t2. cbn [fc_post halt_view OPTION_MAP]. post_split; try reflexivity.
  - intros ck1. replace (labSem.clock t1 + (1 + 1) + ck1) with (labSem.clock t1 + 1 + (1 + ck1)) by lia.
    rewrite Hst1. replace (labSem.clock t1 + (1 + ck1)) with (labSem.clock t1 + 1 + ck1) by lia.
    rewrite Hstep2. reflexivity.
  - subst t2 NC. cbn. apply isPREFIX_iff. eexists; reflexivity.
  - split; [cbn; lia|].
    assert (Hus' : ~ use_stack s) by (rewrite Hus; discriminate).
    subst t2. unfold state_rel. lab_cbn. stk_fields.
    refine (conj _ (conj _ (conj Hmem (conj Hmd (conj Hsmd (conj Hbe (conj Hffi (conj Hclk
      (conj _ (conj _ (conj _ (conj Hfail (conj Hl1 (conj Hl2 (conj Hl3 (conj Hl4 (conj Hlsr
      (conj Hio (conj _ (conj Hal (conj Hsal (conj eq_refl (conj Hcomp (conj _ (conj _ (conj Hus'
      (conj Hust (conj Hua Hgd)))))))))))))))))))))))))))).
    + (* regs *)
      intros n0 v0 Hn0. rewrite FLOOKUP_UPDATE in Hn0. rewrite APPLY_UPDATE_THM.
      destruct (decide (ptr_reg t1 = n0)) as [<-|Hne]; [injection Hn0; auto|].
      rewrite FLOOKUP_DRESTRICT in Hn0. destruct (classical_dec _) as [Hin|]; [|discriminate].
      rewrite (Hcc n0 0 Hin). cbn [targetSem.get_reg_value].
      rewrite Rta by (intros ->; exact (Hlsr Hin)). exact (Hregs n0 v0 Hn0).
    + intros n0 v0 Hn0. discriminate Hn0.
    + (* code *)
      intros n0 p0 Hn0. rewrite lookup_union in Hn0.
      destruct (lookup n0 (code s)) as [p1|] eqn:Eold.
      * injection Hn0 as <-. destruct (Hcode n0 p1 Eold) as (Hca1 & pc1 & Hci1 & Hl1').
        split; [exact Hca1|]. exists pc1. subst NC.
        split; [apply code_installed_APPEND, Hci1|apply loc_to_pc_APPEND, Hl1'].
      * change (lookup n0 (insert k prog0 (fromAList progs'))) with (lookup n0 (fromAList ((k, prog0) :: progs'))) in Hn0.
        rewrite lookup_fromAList in Hn0.
        assert (Hin0 : In (n0, p0) ((k, prog0) :: progs')) by (apply ALOOKUP_In; exact Hn0).
        split.
        { unfold is_true in Hc0e. rewrite EVERY_Forall, List.Forall_forall in Hc0e.
          specialize (Hc0e _ Hin0). cbn in Hc0e. apply Bool.andb_true_iff in Hc0e as [Hc0e _].
          apply Bool.andb_true_iff in Hc0e as [Hc0e _]. exact Hc0e. }
        destruct (code_installed_prog_to_section _ n0 p0 (conj Hlok Hn0)) as (pc1 & Hci1 & Hl1').
        assert (Hnm : ~ MEM n0 (MAP Section_num (labSem.code t1))).
        { intros Hm. unfold is_true in Hm. rewrite MEM_In in Hm.
          assert (Hd : domain (code s) n0) by (rewrite Hdom; apply IN_set; exact Hm).
          apply domain_lookup in Hd. destruct Hd as [? Hd]. congruence. }
        assert (Hlines : EVERY (sec_label_ok n0)
                  (append (FST (flatten true p0 n0 (stack_alloc.next_lab p0 2) [] [])))).
        { unfold is_true in Hlok1. rewrite EVERY_Forall, List.Forall_forall in Hlok1.
          specialize (Hlok1 (prog_to_section (n0, p0)) (in_map _ _ _ Hin0)).
          rewrite prog_to_section_eq in Hlok1. cbn [sec_labels_ok] in Hlok1.
          apply EVERY_Forall in Hlok1. apply Forall_app in Hlok1 as [Hlok1 _].
          apply EVERY_Forall. exact Hlok1. }
        exists (LENGTH (FLAT (MAP (FILTER (negb ∘ is_Label) ∘ Section_lines) (labSem.code t1))) + pc1).
        subst NC. split.
        { apply code_installed_append2 with (k := n0). repeat split; assumption. }
        { rewrite (loc_to_pc_append2 _ _ _ _ _ (conj Hnm (conj Hsok Hl1'))). f_equal. lia. }
    + (* domain *)
      subst NC. change (insert k prog0 (fromAList progs')) with (fromAList ((k, prog0) :: progs')).
      rewrite domain_union, domain_fromAList, Hdom. apply set_ext. intros x. cbn beta.
      rewrite map_app, MAP_prog_to_section_Section_num.
      split; intros Hx.
      * apply IN_set. apply in_app_iff. destruct Hx as [Hx|Hx].
        -- left. apply IN_set in Hx. exact Hx.
        -- right. unfold is_true in Hx. rewrite MEM_In in Hx. exact Hx.
      * apply IN_set in Hx. apply in_app_iff in Hx as [Hx|Hx].
        -- left. apply IN_set. exact Hx.
        -- right. unfold is_true. rewrite MEM_In. exact Hx.
    + (* sec_labels_ok *)
      subst NC. unfold is_true in *. rewrite EVERY_Forall in Hsok, Hlok1 |- *. apply Forall_app. auto.
    + (* cc_regs *)
      intros k0 n0 Hk. unfold shift_seq. exact (Hcc k0 (n0 + 1) Hk).
    + (* compile_oracle *)
      apply functional_extensionality. intros n0. unfold shift_seq. rewrite Hco. reflexivity.
    + (* oracle properties *)
      intros k0. unfold shift_seq. exact (Hcos (k0 + 1)).
Qed.


Lemma fc_all : forall x, FC x.
Proof.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  destruct p; try (apply fc_error; exact Logic.I).
  - apply fc_Skip.
  - apply fc_Inst.
  - destruct o as [[p1 [lr [l1 l2]]]|]; [apply fc_Call_some, IH|apply fc_Call_none, IH].
  - apply fc_Seq, IH.
  - apply fc_If, IH.
  - apply fc_Loop, IH.
  - apply fc_JumpLower, IH.
  - apply fc_Raise.
  - apply fc_Return.
  - apply fc_Break.
  - apply fc_Continue.
  - apply fc_FFI.
  - apply fc_Tick.
  - apply fc_LocValue.
  - apply fc_Install.
  - apply fc_ShMemOp.
  - apply fc_CodeBufferWrite.
  - apply fc_RawCall, IH.
  - apply fc_Halt.
Qed.

End FlattenCorrect.

Section FlattenCorrectThm.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_correct" *)
Theorem flatten_correct : forall (prog : prog a) (s1 : stackSem.state a c ffi_t) t r s2 n l cs bs
    (t1 : labSem.state a c ffi_t),
  evaluate (prog, s1) = (r, s2) /\ r <> SOME Error /\
  state_rel s1 t1 /\
  call_args prog (ptr_reg t1) (len_reg t1) (ptr2_reg t1) (len2_reg t1) (link_reg t1) /\
  code_installed (pc t1) (append (FST (flatten t prog n l cs bs))) (labSem.code t1) /\
  EVERY (fun k => IS_SOME (loc_to_pc n k (labSem.code t1))) (cs ++ bs ++ [0]) ->
  exists ck t2,
    match halt_view r with
    | SOME res =>
        labSem.evaluate (labSem.set_clock (labSem.clock t1 + ck) t1) = (res, t2) /\
        labSem.ffi t2 = ffi s2
    | NONE =>
        (forall ck1, labSem.evaluate (labSem.set_clock (labSem.clock t1 + ck + ck1) t1) =
                     labSem.evaluate (labSem.set_clock (labSem.clock t2 + ck1) t2)) /\
        len_reg t2 = len_reg t1 /\
        ptr_reg t2 = ptr_reg t1 /\
        len2_reg t2 = len2_reg t1 /\
        ptr2_reg t2 = ptr2_reg t1 /\
        link_reg t2 = link_reg t1 /\
        isPREFIX (labSem.code t1) (labSem.code t2) /\
        match OPTION_MAP (fun w => result_view w n cs bs) r with
        | NONE =>
            pc t2 = pc t1 + LENGTH (FILTER (negb ∘ is_Label)
                                      (append (FST (flatten t prog n l cs bs)))) /\
            state_rel s2 t2
        | SOME (Vloc n1 n2) =>
            (forall n, IS_SOME (lookup n (code s2)) -> IS_SOME (loc_to_pc n 0 (labSem.code t2))) /\
            forall w, loc_to_pc n1 n2 (labSem.code t2) = SOME w -> w = pc t2 /\ state_rel s2 t2
        | SOME (Vcont n1 n2) =>
            state_rel s2 t2 /\
            code_installed (pc t2) [LabAsm (Jump (Lab n1 n2)) (n2w 0) [] 0] (labSem.code t2)
        | SOME Vtimeout => labSem.ffi t2 = ffi s2 /\ labSem.clock t2 = 0
        | _ => False
        end
    end.
Proof.
  intros prog s1 t r s2 n l cs bs t1 (He & Hr & Hs & Hca & Hci & Hev).
  exact (fc_all (prog, s1) t r s2 n l cs bs t1 He Hr Hs Hca Hci Hev).
Qed.

End FlattenCorrectThm.


















(** ** The semantics of [flatten] *)

Section FlattenCall.
Context {a : N} {c ffi_t : Type}.

Lemma sset_clock_same (s : stackSem.state a c ffi_t) : set_clock (clock s) s = s.
Proof. destruct s; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_call_correct" *)
Theorem flatten_call_correct : forall start (s1 : stackSem.state a c ffi_t) res s2
    (t1 : labSem.state a c ffi_t),
  evaluate (Call NONE (inl start) NONE, s1) = (res, s2) /\
  state_rel s1 t1 /\
  loc_to_pc start 0 (labSem.code t1) = SOME (pc t1) /\
  res <> SOME Error /\
  (res <> SOME TimeOut ->
     (exists w, res = SOME (Halt (Word w))) \/
     (exists f, res = SOME (FinalFFI f)) \/
     (exists n, res = SOME (Result (Loc n 0)) /\
        (forall s : stackSem.state a c ffi_t, subspt (code s1) (code s) /\ clock s <> 0 ->
           exists t, evaluate (Call NONE (inl n) NONE, s) = (SOME (Halt (Word (n2w 0))), t) /\
                     ffi t = ffi s /\ clock t = clock s - 1))) ->
  exists ck r2 t2,
    labSem.evaluate (labSem.set_clock (labSem.clock t1 - 1 + ck) t1) = (r2, t2) /\
    (forall f, res = SOME (FinalFFI f) -> r2 = targetSem.Halt (FFI_outcome f)) /\
    (forall w, res = SOME (Halt w) ->
       r2 = match w with
            | Word w => if bool_decide (w = n2w 0) then targetSem.Halt Success
                        else targetSem.Halt Resource_limit_hit
            | _ => targetSem.Error
            end) /\
    (forall n, res = SOME (Result (Loc n 0)) -> r2 = targetSem.Halt Success) /\
    labSem.ffi t2 = ffi s2 /\
    r2 <> targetSem.Error /\ (res = SOME TimeOut -> r2 = targetSem.TimeOut).
Proof.
  intros start s1 res s2 t1 (He & Hs & Hpc & Hr & Hhyp).
  pose proof He as He0.
  rewrite evaluate_eqn in He. cbn [evaluate_body find_code] in He.
  destruct (lookup start (code s1)) as [prog|] eqn:El; [|injection He as <- <-; congruence].
  replace (negb (bool_decide (@NONE (stackLang.prog a * (N * N)) = NONE))) with false in He
    by (symmetry; apply Bool.negb_false_iff, bool_decide_spec; reflexivity).
  pose proof (sr_clock _ _ Hs) as Hc.
  destruct (clock s1 =? 0) eqn:Ec0.
  { injection He as <- <-. apply N.eqb_eq in Ec0.
    exists 0, targetSem.TimeOut, (labSem.set_clock 0 t1).
    split; [|split; [intros f E; discriminate|split; [intros w E; discriminate|
            split; [intros n E; discriminate|split; [|split; [discriminate|reflexivity]]]]]].
    - replace (labSem.clock t1 - 1 + 0) with 0 by lia.
      rewrite labSem.evaluate_def. reflexivity.
    - sr_destruct Hs. cbn. exact Hffi. }
  apply N.eqb_neq in Ec0. rewrite fix_clock_evaluate in He.
  destruct (evaluate (prog, dec_clock s1)) as [res' s'] eqn:Ep.
  destruct (bad_fun_return res') eqn:Eb; injection He as <- <-; [congruence|].
  destruct (sr_code _ _ _ _ Hs El) as (Hca & pc0 & Hci & Hl0). rewrite Hpc in Hl0. injection Hl0 as <-.
  set (t1' := labSem.set_clock (labSem.clock t1 - 1) t1).
  assert (Hs1 : state_rel (dec_clock s1) t1') by exact (state_rel_dec_clock _ _ Hs).
  assert (Hev1 : EVERY (fun k => IS_SOME (loc_to_pc start k (labSem.code t1'))) ([] ++ [] ++ [0]))
    by (cbn [EVERY app]; change (labSem.code t1') with (labSem.code t1); rewrite Hpc; reflexivity).
  destruct (flatten_correct prog (dec_clock s1) true res' s' start (stack_alloc.next_lab prog 2) [] [] t1'
              (conj Ep (conj Hr (conj Hs1 (conj Hca (conj Hci Hev1))))))
    as (ck & t2 & Hp).
  assert (Ht1' : forall K, labSem.set_clock (labSem.clock t1' + K) t1' = labSem.set_clock (labSem.clock t1 - 1 + K) t1)
    by reflexivity.
  destruct res' as [x|]; [|discriminate Eb].
  destruct x as [w|w|k|k|w| |f|]; cbn [halt_view OPTION_MAP result_view] in Hp; try discriminate Eb.
  - (* Result *)
    destruct (Hhyp ltac:(discriminate)) as [[w0 E]|[[f E]|(n & E & Hh)]]; try discriminate.
    injection E as ->.
    destruct Hp as (Hev & _ & _ & _ & _ & _ & Hpre & HA & HB).
    destruct (evaluate_mono _ _ _ _ He0) as [_ Hsub].
    assert (Hck : clock (set_clock (clock s' + 1) s') <> 0) by (cbn; lia).
    destruct (Hh (set_clock (clock s' + 1) s') (conj Hsub Hck)) as (tt & Ett & Hfft & _).
    rewrite evaluate_eqn in Ett. cbn [evaluate_body find_code] in Ett.
    cbn [code set_clock] in Ett.
    destruct (lookup n (code s')) as [prog'|] eqn:El'; [|discriminate Ett].
    replace (negb (bool_decide (@NONE (stackLang.prog a * (N * N)) = NONE))) with false in Ett
      by (symmetry; apply Bool.negb_false_iff, bool_decide_spec; reflexivity).
    cbn [clock set_clock] in Ett.
    replace (clock s' + 1 =? 0) with false in Ett by (symmetry; apply N.eqb_neq; lia).
    rewrite fix_clock_evaluate in Ett.
    change (dec_clock (set_clock (clock s' + 1) s')) with (set_clock (clock s' + 1 - 1) s') in Ett.
    replace (clock s' + 1 - 1) with (clock s') in Ett by lia. rewrite sset_clock_same in Ett.
    destruct (evaluate (prog', s')) as [r'' s''] eqn:Ep'.
    destruct (bad_fun_return r'') eqn:Eb'; [discriminate Ett|]. injection Ett as -> ->.
    assert (Hsome : IS_SOME (lookup n (code s'))) by (rewrite El'; reflexivity).
    pose proof (HA n Hsome) as Hsome2.
    destruct (loc_to_pc n 0 (labSem.code t2)) as [w2|] eqn:Ew2; [|discriminate Hsome2].
    destruct (HB w2 eq_refl) as [-> Hs2].
    destruct (sr_code _ _ _ _ Hs2 El') as (Hca' & pc0' & Hci' & Hl0'). rewrite Ew2 in Hl0'. injection Hl0' as <-.
    assert (Hne0 : SOME (Halt (Word (n2w 0 : word a))) <> SOME Error) by discriminate.
    assert (Hev2 : EVERY (fun k => IS_SOME (loc_to_pc n k (labSem.code t2))) ([] ++ [] ++ [0]))
      by (cbn [EVERY app]; rewrite Ew2; reflexivity).
    destruct (flatten_correct prog' s' true (SOME (Halt (Word (n2w 0)))) tt n (stack_alloc.next_lab prog' 2) [] [] t2
                (conj Ep' (conj Hne0 (conj Hs2 (conj Hca' (conj Hci' Hev2))))))
      as (ck' & t3 & Hp').
    cbn [halt_view halt_word_view] in Hp'. destruct Hp' as [Ev' Hf'].
    exists (ck + ck'), (targetSem.Halt Success), t3.
    split; [|split; [intros f0 E; discriminate|split; [intros w0 E; discriminate|
            split; [intros n0 _; reflexivity|split; [|split; [discriminate|intros E; discriminate]]]]]].
    + rewrite <- Ht1'. rewrite N.add_assoc, Hev. rewrite Ev'.
      replace (⌜(n2w 0 : word a) = n2w 0⌝) with true by (symmetry; apply bool_decide_spec; reflexivity).
      reflexivity.
    + rewrite Hf'. exact Hfft.
  - (* Exception *)
    destruct (Hhyp ltac:(discriminate)) as [[w0 E]|[[f E]|(n & E & _)]]; discriminate.
  - (* Halt *)
    destruct Hp as [Hev Hf].
    exists ck, (halt_word_view w), t2. rewrite <- Ht1'.
    split; [exact Hev|].
    split; [intros f0 E; discriminate|].
    split; [intros w0 E; injection E as <-; destruct w as [w|]; reflexivity|].
    split; [intros n0 E; discriminate|].
    split; [exact Hf|]. split; [|intros E; discriminate].
    destruct (Hhyp ltac:(discriminate)) as [[w0 E]|[[f E]|(n & E & _)]]; try discriminate.
    injection E as ->. cbn. destruct (bool_decide _); discriminate.
  - (* TimeOut *)
    destruct Hp as (Hev & _ & _ & _ & _ & _ & _ & Hf & Hc2).
    exists ck, targetSem.TimeOut, (labSem.set_clock 0 t2). rewrite <- Ht1'.
    split.
    + specialize (Hev 0). rewrite N.add_0_r in Hev. rewrite Hev, Hc2. rewrite labSem.evaluate_def. reflexivity.
    + split; [intros f0 E; discriminate|]. split; [intros w0 E; discriminate|].
      split; [intros n0 E; discriminate|]. split; [cbn; exact Hf|]. split; [discriminate|reflexivity].
  - (* FinalFFI *)
    destruct Hp as [Hev Hff].
    exists ck, (targetSem.Halt (FFI_outcome f)), t2. rewrite <- Ht1'.
    split; [exact Hev|]. split; [intros f0 E; injection E as ->; reflexivity|].
    split; [intros w0 E; discriminate|]. split; [intros n0 E; discriminate|].
    split; [exact Hff|]. split; [discriminate|intros E; discriminate].
  - (* Error *) exfalso; exact (Hr eq_refl).
Qed.

End FlattenCall.

(** HOL's [halt_assum (:'ffi # 'c) code] takes the type [ffi # c] as its
    first argument; here the two types [ffi_t] and [c]. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "halt_assum_def" *)
Definition halt_assum (ffi_t c : Type) {a : N} (code0 : spt (stackLang.prog a)) : Prop :=
  forall s : stackSem.state a c ffi_t,
    subspt code0 (code s) /\ clock s <> 0 ->
    exists t, evaluate (Call NONE (inl 1) NONE, s) = (SOME (Halt (Word (n2w 0))), t) /\
              ffi t = ffi s /\ clock t = clock s - 1.

Section FlattenSemantics.
Context {a : N} {c ffi_t : Type}.

(** Galette-only: the outcome of a terminating stack run. *)
Definition stack_outcome (r : result a) : option outcome :=
  match r with
  | FinalFFI e => SOME (FFI_outcome e)
  | Halt w => SOME (if bool_decide (w = Word (n2w 0)) then Success else Resource_limit_hit)
  | Result _ => SOME Success
  | _ => NONE
  end.

Lemma stack_outcome_iff (r : result a) o :
  stack_outcome r = SOME o <->
  match r with
  | FinalFFI e => o = FFI_outcome e
  | Halt w => o = if bool_decide (w = Word (n2w 0)) then Success else Resource_limit_hit
  | Result _ => o = Success
  | _ => False
  end.
Proof. destruct r; cbn; split; intros H; try discriminate; try contradiction; try (injection H; auto); congruence. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_semantics" *)
Theorem flatten_semantics : forall start (s1 : stackSem.state a c ffi_t) (s2 : labSem.state a c ffi_t),
  halt_assum ffi_t c (code s1) /\
  state_rel s1 s2 /\
  loc_to_pc start 0 (labSem.code s2) = SOME (pc s2) /\
  semantics start s1 <> Fail ->
  labSem.semantics s2 = semantics start s1.
Proof.
  intros start s1 t (Hh & Hs & Hpc & HF).
  set (P := @Call a NONE (inl start) NONE).
  set (bad := fun res : option (result a) =>
         res <> SOME TimeOut /\ res <> SOME (Result (Loc 1 0)) /\
         (forall w, res <> SOME (Halt (Word w))) /\ forall f, res <> SOME (FinalFFI f)).
  assert (OKs : forall k, ~ bad (FST (evaluate (P, set_clock k s1)))).
  { intros k Hk; apply HF; unfold semantics; cbv zeta.
    destruct (classical_dec _) as [_|Hn]; [reflexivity|exfalso; apply Hn; exists k; exact Hk]. }
  (* the simulation of each run *)
  assert (SIM : forall k, exists ck r2 t2,
            labSem.evaluate (labSem.set_clock (k - 1 + ck) t) = (r2, t2) /\
            labSem.ffi t2 = ffi (SND (evaluate (P, set_clock k s1))) /\
            r2 <> targetSem.Error /\
            match FST (evaluate (P, set_clock k s1)) with
            | SOME TimeOut => r2 = targetSem.TimeOut
            | SOME r => exists o, stack_outcome r = SOME o /\ r2 = targetSem.Halt o
            | NONE => False
            end).
  { intros k. destruct (evaluate (P, set_clock k s1)) as [res s1'] eqn:E. cbn [FST SND].
    pose proof (OKs k) as Hok. rewrite E in Hok. cbn [FST] in Hok.
    assert (Hne : res <> SOME Error) by (intros ->; apply Hok; unfold bad; repeat split; congruence).
    assert (Hhyp : res <> SOME TimeOut ->
       (exists w, res = SOME (Halt (Word w))) \/
       (exists f, res = SOME (FinalFFI f)) \/
       (exists n, res = SOME (Result (Loc n 0)) /\
          (forall s : stackSem.state a c ffi_t, subspt (code (set_clock k s1)) (code s) /\ clock s <> 0 ->
             exists t, evaluate (Call NONE (inl n) NONE, s) = (SOME (Halt (Word (n2w 0))), t) /\
                       ffi t = ffi s /\ clock t = clock s - 1))).
    { intros HT. destruct (classical_dec (exists w, res = SOME (Halt (Word w)))) as [Hw|Hw]; [left; exact Hw|].
      destruct (classical_dec (exists f, res = SOME (FinalFFI f))) as [Hf|Hf]; [right; left; exact Hf|].
      destruct (classical_dec (res = SOME (Result (Loc 1 0)))) as [Hr|Hr].
      - right; right. exists 1. split; [exact Hr|]. exact Hh.
      - exfalso. apply Hok. split; [exact HT|]. split; [exact Hr|].
        split; [intros w E'; apply Hw; eauto|intros f E'; apply Hf; eauto]. }
    destruct (flatten_call_correct start (set_clock k s1) res s1' (labSem.set_clock k t)
                (conj E (conj (state_rel_with_clock k _ _ Hs) (conj Hpc (conj Hne Hhyp)))))
      as (ck & r2 & t2 & Ev & H1 & H2 & H3 & H4 & H5 & H6).
    exists ck, r2, t2. cbn [labSem.clock labSem.set_clock] in Ev. rewrite lset_clock_set_clock in Ev.
    split; [exact Ev|]. split; [exact H4|]. split; [exact H5|].
    destruct res as [r|]; [|exfalso; apply Hok; unfold bad; repeat split; congruence].
    destruct r as [w|w|n|n|w| |f|].
    - destruct (Hhyp ltac:(discriminate)) as [[w0 Ew]|[[f Ef]|(n & En & _)]]; try discriminate.
      injection En as ->. exists Success. split; [reflexivity|exact (H3 n eq_refl)].
    - exfalso. destruct (Hhyp ltac:(discriminate)) as [[w0 Ew]|[[f Ef]|(n & En & _)]]; discriminate.
    - exfalso. destruct (Hhyp ltac:(discriminate)) as [[w0 Ew]|[[f Ef]|(n0 & En & _)]]; discriminate.
    - exfalso. destruct (Hhyp ltac:(discriminate)) as [[w0 Ew]|[[f Ef]|(n0 & En & _)]]; discriminate.
    - pose proof (H2 w eq_refl) as Hw. destruct w as [w|l1 l2]; [|subst r2; contradiction].
      cbn [stack_outcome]. destruct (bool_decide (w = n2w 0)) eqn:Ew.
      + exists Success. split; [|exact Hw]. apply bool_decide_spec in Ew; subst w.
        replace (bool_decide (Word (n2w 0 : word a) = Word (n2w 0))) with true by (symmetry; apply bool_decide_spec; reflexivity).
        reflexivity.
      + exists Resource_limit_hit. split; [|exact Hw].
        replace (bool_decide (Word w = Word (n2w 0))) with false; [reflexivity|].
        symmetry. destruct (bool_decide (Word w = Word (n2w 0))) eqn:E2; [|reflexivity].
        apply bool_decide_spec in E2. injection E2 as ->.
        exfalso. assert (Hc : bool_decide ((n2w 0 : word a) = n2w 0) = true) by (apply bool_decide_spec; reflexivity).
        congruence.
    - exact (H6 eq_refl).
    - exists (FFI_outcome f). split; [reflexivity|exact (H1 f eq_refl)].
    - exfalso; exact (Hne eq_refl). }
  unfold labSem.semantics.
  destruct (classical_dec (exists k, FST (labSem.evaluate (labSem.set_clock k t)) = targetSem.Error))
    as [[k Hk]|HnE].
  { exfalso. destruct (labSem.evaluate (labSem.set_clock k t)) as [r t'] eqn:Ev; cbn in Hk; subst r.
    destruct (SIM (k + 1)) as (ck & r2 & t2 & Ev2 & _ & Hr2 & _).
    destruct (lab_filterProof.evaluate_clock_mono t k (k + 1 - 1 + ck) targetSem.Error t' Ev
                ltac:(discriminate) ltac:(lia)) as (t'' & Ev'' & _).
    rewrite Ev2 in Ev''. injection Ev'' as E _. rewrite E in Hr2. exact (Hr2 eq_refl). }
  unfold semantics. cbv zeta. fold P.
  destruct (classical_dec _) as [[k Hk]|_]; [exfalso; exact (OKs k Hk)|].
  match goal with |- match some ?Q1 with _ => _ end = match some ?Q2 with _ => _ end =>
    assert (EQ : Q1 = Q2) end.
  { apply functional_extensionality; intros res; apply propositional_extensionality; split.
    - intros (k & t' & o & Ev & ->).
      destruct (SIM (k + 1)) as (ck & r2 & t2 & Ev2 & Hf2 & Hr2 & Hm).
      destruct (lab_filterProof.evaluate_clock_mono t k (k + 1 - 1 + ck) (targetSem.Halt o) t' Ev
                  ltac:(discriminate) ltac:(lia)) as (t'' & Ev'' & Hf'').
      rewrite Ev2 in Ev''. injection Ev'' as E1 E2. subst r2 t2.
      destruct (evaluate (P, set_clock (k + 1) s1)) as [[r|] s'] eqn:Es; cbn [FST SND] in Hm, Hf2;
        [|contradiction].
      destruct r as [w|w|nn|nn|w| |f|]; try (discriminate Hm); try (destruct Hm as (o' & Ho & _); discriminate Ho).
      all: destruct Hm as (o' & Ho & Eo); injection Eo as Eo; subst o'.
      all: exists (k + 1), s'; eexists; exists o; split; [exact Es|]; split; [exact (proj1 (stack_outcome_iff _ _) Ho)|].
      all: rewrite <- Hf'', Hf2; reflexivity.
    - intros (k & s' & r & o & Es & Hm & ->).
      apply stack_outcome_iff in Hm.
      destruct (SIM k) as (ck & r2 & t2 & Ev2 & Hf2 & Hr2 & Hm2).
      rewrite Es in Hm2, Hf2. cbn [FST SND] in Hm2, Hf2.
      assert (Hm3 : r2 = targetSem.Halt o).
      { destruct r; try discriminate Hm; destruct Hm2 as (o' & Ho & ->); congruence. }
      subst r2. exists (k - 1 + ck), t2, o. split; [exact Ev2|]. rewrite Hf2. reflexivity. }
  rewrite EQ. destruct (some _); [reflexivity|].
  f_equal.
  set (Xt := IMAGE (fun k => fromList (io_events (labSem.ffi (SND (labSem.evaluate (labSem.set_clock k t)))))) UNIV).
  set (Xs := IMAGE (fun k => fromList (io_events (ffi (SND (evaluate (P, set_clock k s1)))))) UNIV).
  assert (Ct : lprefix_chain Xt) by exact (lab_filterProof.io_chain t).
  assert (Cs : lprefix_chain Xs) by exact (io_chain_stack start s1).
  assert (EQV : equiv_lprefix_chain Xs Xt).
  { apply (equiv_lprefix_chain_thm _ _ (conj Cs Ct)); split.
    - intros ll1 n x [[k [-> _]] Hx].
      destruct (SIM k) as (ck & r2 & t2 & Ev2 & Hf2 & _).
      exists (fromList (io_events (labSem.ffi (SND (labSem.evaluate (labSem.set_clock (k - 1 + ck) t)))))).
      split; [exists (k - 1 + ck); split; [reflexivity|exact Logic.I]|].
      rewrite Ev2; cbn [SND]; rewrite Hf2; exact Hx.
    - intros ll2 n x [[k [-> _]] Hx].
      destruct (SIM (k + 1)) as (ck & r2 & t2 & Ev2 & Hf2 & _).
      exists (fromList (io_events (ffi (SND (evaluate (P, set_clock (k + 1) s1)))))).
      split; [exists (k + 1); split; [reflexivity|exact Logic.I]|].
      pose proof (lab_filterProof.io_events_mono t k (k + 1 - 1 + ck) ltac:(lia)) as M.
      rewrite Ev2 in M. cbn [SND] in M. rewrite Hf2 in M.
      exact (lab_filterProof.LNTH_fromList_prefix _ _ n x M Hx). }
  apply (unique_lprefix_lub Xs); split.
  - apply (lprefix_lub_new_chain Xt Xs). split; [exact Cs|split; [|exact (build_lprefix_lub_thm _ Ct)]].
    apply (equiv_lprefix_chain_thm _ _ (conj Ct Cs)).
    apply (equiv_lprefix_chain_thm _ _ (conj Cs Ct)) in EQV. destruct EQV as [E1 E2]. split; assumption.
  - exact (build_lprefix_lub_thm _ Cs).
Qed.

End FlattenSemantics.
