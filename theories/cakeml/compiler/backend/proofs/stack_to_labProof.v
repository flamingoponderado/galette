(** * stack_to_labProof: correctness of the stackLang -> labLang flattening pass

    Port of HOL4 [cakeml/compiler/backend/proofs/stack_to_labProofScript.sml].

    Status: PARTIAL port.  This file contains everything in the HOL script up
    to and including [flatten_semantics] (HOL line ~2990): the [code_installed]
    / [loc_to_pc] / [asm_fetch_aux] infrastructure, [state_rel], the per-case
    simulation proof [flatten_correct], [flatten_call_correct], [halt_assum]
    and [flatten_semantics], plus the early syntactic label lemmas
    ([stack_to_lab_lab_pres], [stack_to_lab_lab_pres_T],
    [prog_to_section_labels_ok], ...).

    Also ported: [make_init], [full_make_init] and
    [full_make_init_buffer/_ffi/_compile], [memory_assumption],
    [halt_assum_lemma], [FLOOKUP_regs], [state_rel_make_init],
    [MAP_FST_compile_compile], the rebound [next_lab_non_zero],
    [extract_label_store_list_code], [stack_to_lab_compile_lab_pres] and
    [good_code], [full_make_init_semantics], the encoder line preconditions
    and [stack_to_lab_compile_all_enc_ok], plus flattening, section and
    handler label preservation through [stack_to_lab_stack_good_handler_labels_incr],
    [full_make_init_has_fp_ops], and the complete no_shmemop / no_install chains.

    Also ported: [IMP_init_store_ok] and [IMP_init_state_ok].

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
From Galette.HOL.examples.machine_code.hoare_triple Require Import set_sep.
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
  stack_namesProof stack_rawcallProof word_gcFunctions.
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
Definition dest_to_loc {K} `{EqDecision K} (regs : fmap K (word_loc a)) (dest : N + K) : N :=
  match dest with
  | inl p => p
  | inr r => match FAPPLY regs r with Loc loc _ => loc | _ => ARB end
  end.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "dest_to_loc'_def" *)
Definition dest_to_loc' {K} (regs : K -> word_loc a) (dest : N + K) : N :=
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

Section Initialization.
Context {a : N} {c ffi_t : Type}.
Local Opaque stackSem.evaluate.

#[local] Instance init_store_inhabited : Inhabited (fmap store_name (word_loc a)) := FEMPTY.
#[local] Instance init_data_buffer_inhabited : Inhabited (buffer a a) :=
  wordSem.mk_buffer (n2w 0) [] 0.

(** Fields omitted from HOL's record literal have value [ARB]. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "make_init_def" *)
Definition make_init (code0 : spt (prog a))
    (coracle : N -> c * (list (N * prog a) * list (word a)))
    (regs0 : list N) (save_regs : N -> Prop) (s : labSem.state a c ffi_t)
    : stackSem.state a c ffi_t :=
  stackSem.mk_state
    (FEMPTY |++ MAP (fun r => (r, read_reg r s)) regs0) FEMPTY
    ARB ARB ARB (labSem.mem s) (labSem.mem_domain s) (labSem.shared_mem_domain s)
    ARB (fun c0 p => labSem.compile s c0 (MAP prog_to_section p)) coracle
    (labSem.code_buffer s) ARB ARB false false false (labSem.clock s) code0
    (labSem.ffi s) save_regs (labSem.be s).

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "full_make_init_def" *)
Definition full_make_init (stack_conf : stack_to_lab.config) (data_conf : data_to_word.config)
    (max_heap sp : N) (offset : word a * word a) (bitmaps0 : list (word a))
    (code0 : list (N * prog a)) (s4 : labSem.state a c ffi_t) (save_regs : N -> Prop)
    (data_sp : N) (coracle : N -> c * (list (N * prog a) * list (word a)))
    : stackSem.state a c ffi_t * option (stackSem.state a c ffi_t) :=
  let ggc := is_gen_gc (data_to_word.gc_kind data_conf) in
  let jump0 := stack_to_lab.jump stack_conf in
  let code1 : list (N * prog a) := stack_alloc.compile data_conf (stack_rawcall.compile code0) in
  let code2 : list (N * prog a) := stack_remove.compile jump0 offset ggc max_heap sp bvl_to_bvi.InitGlobals_location code1 in
  let code3 : spt (prog a) := fromAList (stack_names.compile (reg_names stack_conf) code2) in
  let coracle1 : N -> c * (list (N * prog a) * list (word a)) := (I ## (MAP stack_alloc.prog_comp ## I)) ∘ coracle in
  let coracle2 : N -> c * (list (N * prog a) * list (word a)) := (I ## (MAP (stack_remove.prog_comp jump0 offset sp) ## I)) ∘ coracle1 in
  let coracle3 : N -> c * (list (N * prog a) * list (word a)) := (I ## (stack_names.compile (reg_names stack_conf) ## I)) ∘ coracle2 in
  let s3 : stackSem.state a c ffi_t := make_init code3 coracle3 (MAP (stack_names.find_name (reg_names stack_conf)) [2;3;4]) save_regs s4 in
  let s2 : stackSem.state a c ffi_t := stack_namesProof.make_init (reg_names stack_conf) (fromAList code2) coracle2 s3 in
  let s1 : stackSem.state a c ffi_t := stack_removeProof.make_init_any ggc max_heap bitmaps0 data_sp coracle1 jump0 offset sp (fromAList code1) s2 in
  (stack_allocProof.make_init data_conf (fromAList code0) coracle s1,
   stack_removeProof.make_init_opt ggc max_heap bitmaps0 data_sp coracle1 jump0 offset sp (fromAList code1) s2).

(** Projection helpers keep case analysis independent of the concrete compiler pipeline. *)
Local Lemma make_init_any_buffers ggc mh bm dsp co jump0 off sp cd
    (s : stackSem.state a c ffi_t) :
  wordSem.buffer_buffer (code_buffer (stack_removeProof.make_init_any ggc mh bm dsp co jump0 off sp cd s)) = [] /\
  wordSem.buffer_buffer (data_buffer (stack_removeProof.make_init_any ggc mh bm dsp co jump0 off sp cd s)) = [].
Proof.
  unfold stack_removeProof.make_init_any, stack_removeProof.make_init_opt.
  destruct (evaluate _) as [[r|] t] eqn:E; [split; reflexivity|].
  destruct (classical_dec _) as [H|H]; [|split; reflexivity].
  unfold stack_removeProof.init_prop in H. destruct H as (? & ? & ? & ? & H).
  intuition.
Qed.

Local Lemma make_init_any_compile ggc mh bm dsp co jump0 off sp cd
    (s : stackSem.state a c ffi_t) :
  stackSem.compile (stack_removeProof.make_init_any ggc mh bm dsp co jump0 off sp cd s) =
    (fun c0 p => stackSem.compile s c0 (MAP (stack_remove.prog_comp jump0 off sp) p)).
Proof.
  unfold stack_removeProof.make_init_any, stack_removeProof.make_init_opt.
  destruct (evaluate _) as [[r|] t] eqn:E; [reflexivity|].
  destruct (classical_dec _); [|reflexivity].
  unfold stack_removeProof.init_reduce; cbv zeta; cbn [stackSem.compile].
  pose proof (evaluate_consts _ _ _ _ E) as H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & H). rewrite H. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "full_make_init_buffer" *)
Theorem full_make_init_buffer : forall sc dc mh sp off bm cd s sr dsp co,
  wordSem.buffer_buffer (code_buffer (FST (full_make_init sc dc mh sp off bm cd s sr dsp co))) = [] /\
  wordSem.buffer_buffer (data_buffer (FST (full_make_init sc dc mh sp off bm cd s sr dsp co))) = [].
Proof.
  intros. unfold full_make_init, stack_allocProof.make_init; cbv zeta.
  cbn [FST code_buffer data_buffer set_compile_oracle set_compile set_gc_fun set_use_stack set_use_alloc set_code].
  apply make_init_any_buffers.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "full_make_init_ffi" *)
Theorem full_make_init_ffi : forall sc dc mh sp off bm cd s sr dsp co,
  ffi (FST (full_make_init sc dc mh sp off bm cd s sr dsp co)) = labSem.ffi s.
Proof.
  intros. unfold full_make_init, stack_allocProof.make_init; cbv zeta.
  cbn [FST ffi set_compile_oracle set_compile set_gc_fun set_use_stack set_use_alloc set_code].
  rewrite stack_removeProof.make_init_any_ffi. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "full_make_init_compile" *)
Theorem full_make_init_compile : forall sc dc mh sp off bm cd s sr dsp co,
  stackSem.compile (FST (full_make_init sc dc mh sp off bm cd s sr dsp co)) =
  (fun c0 => (fun p => labSem.compile s c0
    (MAP prog_to_section (MAP (stack_names.prog_comp (reg_names sc))
      (MAP (stack_remove.prog_comp (stack_to_lab.jump sc) off sp) p)))) ∘ MAP stack_alloc.prog_comp).
Proof.
  intros. unfold full_make_init, stack_allocProof.make_init; cbv zeta.
  cbn [FST stackSem.compile set_compile_oracle set_compile set_gc_fun set_use_stack set_use_alloc set_code].
  rewrite make_init_any_compile. reflexivity.
Qed.

Local Open Scope word_scope.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "memory_assumption_def" *)
Definition memory_assumption (rnames : spt N) (bitmaps0 : list (word a)) (data_sp : N)
    (t : labSem.state a c ffi_t) : Prop :=
  exists ptr2 ptr3 ptr4 bitmap_ptr,
    read_reg (stack_names.find_name rnames 2) t = Word ptr2 /\
    read_reg (stack_names.find_name rnames 3) t = Word ptr3 /\
    read_reg (stack_names.find_name rnames 4) t = Word ptr4 /\
    labSem.mem t ptr2 = Word bitmap_ptr /\
    labSem.mem t (ptr2 + bytes_in_word)%w =
      Word (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps0))%w /\
    labSem.mem t (ptr2 + n2w 2 * bytes_in_word)%w =
      Word (bitmap_ptr + bytes_in_word * n2w data_sp + bytes_in_word * n2w (LENGTH bitmaps0))%w /\
    labSem.mem t (ptr2 + n2w 3 * bytes_in_word)%w = Word (wordSem.position (labSem.code_buffer t)) /\
    labSem.mem t (ptr2 + n2w 4 * bytes_in_word)%w =
      Word (wordSem.position (labSem.code_buffer t) + n2w (wordSem.space_left (labSem.code_buffer t)))%w /\
    wordSem.buffer_buffer (labSem.code_buffer t) = [] /\
    ptr2 <=+ ptr4 /\ byte_aligned ptr2 /\ byte_aligned ptr4 /\ byte_aligned bitmap_ptr /\
    n2w 1024 * bytes_in_word <=+ ptr4 - ptr2 /\
    STAR (STAR (word_list bitmap_ptr (MAP Word bitmaps0))
       (word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps0))%w data_sp))
      (word_list_exists ptr2 (w2n (- n2w 1 * ptr2 + ptr4)%w DIV w2n (bytes_in_word : word a)))
      (fun2set (labSem.mem t, labSem.mem_domain t)).

Local Close Scope word_scope.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "halt_assum_lemma" *)
Local Theorem halt_assum_lemma : forall f jump0 off gen max_heap k l (code0 : list (N * prog a)),
  halt_assum ffi_t c (fromAList (stack_names.compile f
    (stack_remove.compile jump0 off gen max_heap k l code0))).
Proof.
  intros f jump0 off gen max_heap k l code0 s (Hs & Hclk).
  assert (Hl : lookup 1 (code s) =
    SOME (Seq (Inst (Const (stack_names.find_name f 1) (n2w 0)))
               (stackLang.Halt (stack_names.find_name f 1)))).
  { apply (proj1 (subspt_lookup _ _) Hs).
    rewrite lookup_fromAList. reflexivity. }
  rewrite evaluate_eqn. cbn [evaluate_body find_code]. rewrite Hl.
  assert (Ec : (clock s =? 0) = false) by (apply N.eqb_neq; exact Hclk).
  match goal with |- context [bool_decide ?P] =>
    replace (bool_decide P) with true by (symmetry; apply bool_decide_spec; reflexivity) end.
  rewrite Ec; cbn [negb]. rewrite fix_clock_evaluate.
  rewrite evaluate_eqn; cbn [evaluate_body]. rewrite fix_clock_evaluate.
  rewrite evaluate_eqn; cbn [evaluate_body inst stackSem.assign stackSem.word_exp].
  rewrite evaluate_eqn; cbn [evaluate_body].
  unfold stackSem.get_var, stackSem.set_var. cbn [stackSem.set_regs stackSem.regs].
  rewrite FLOOKUP_UPDATE. destruct (decide (stack_names.find_name f 1 = stack_names.find_name f 1)); [|contradiction].
  cbn [bad_fun_return]. eexists. split; [reflexivity|]. split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "FLOOKUP_regs" *)
Local Theorem FLOOKUP_regs {B : Type} : forall regs0 n v (f : B) (s : labSem.state a c ffi_t),
  FLOOKUP (FEMPTY |++ MAP (fun r => (r, read_reg r s)) regs0) n = SOME v -> read_reg n s = v.
Proof.
  intros regs0. induction regs0 using List.rev_ind; intros n v f s H.
  - discriminate H.
  - rewrite map_app, FUPDATE_LIST_APPEND in H.
    change (FLOOKUP ((FEMPTY |++ MAP (fun r => (r, read_reg r s)) regs0) |+ (x, read_reg x s)) n = SOME v) in H.
    rewrite FLOOKUP_UPDATE in H. destruct (decide (x = n)) as [->|Hne].
    + injection H as <-. reflexivity.
    + exact (IHregs0 n v f s H).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "state_rel_make_init" *)
Theorem state_rel_make_init : forall code0 coracle regs0 save_regs (s : labSem.state a c ffi_t),
  state_rel (make_init code0 coracle regs0 save_regs s) s <->
  (forall n prog0, lookup n code0 = SOME prog0 ->
    call_args prog0 (ptr_reg s) (len_reg s) (ptr2_reg s) (len2_reg s) (link_reg s) /\
    exists pc0, code_installed pc0
      (append (FST (flatten true prog0 n (stack_alloc.next_lab prog0 2) [] []))) (labSem.code s) /\
      loc_to_pc n 0 (labSem.code s) = SOME pc0) /\
  ~ failed s /\
  labSem.compile_oracle s = (fun n => let '(cfg, (p, _)) := coracle n in (cfg, MAP prog_to_section p)) /\
  (forall k, let '(cfg, (ps, _)) := coracle k in
    EVERY (fun '(n, p) =>
      call_args p (ptr_reg s) (len_reg s) (ptr2_reg s) (len2_reg s) (link_reg s) &&
      EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0) && negb (l2 =? 1)) (extract_labels p) &&
      ALL_DISTINCT (extract_labels p)) ps /\ ALL_DISTINCT (MAP FST ps)) /\
  link_reg s <> len_reg s /\ link_reg s <> ptr_reg s /\
  link_reg s <> len2_reg s /\ link_reg s <> ptr2_reg s /\
  ~ (link_reg s IN save_regs) /\
  domain code0 = set (MAP Section_num (labSem.code s)) /\
  EVERY sec_labels_ok (labSem.code s) /\
  (forall k i n, k IN save_regs -> io_regs s n i k = NONE) /\
  (forall k n, k IN save_regs -> cc_regs s n k = NONE) /\
  (forall x, x IN mem_domain s -> w2n x MOD (dimindex a DIV 8) = 0) /\
  (forall x, x IN shared_mem_domain s -> w2n x MOD (dimindex a DIV 8) = 0) /\
  good_dimindex a.
Proof.
  intros. unfold state_rel, make_init.
  cbn [stackSem.regs stackSem.fp_regs stackSem.memory stackSem.mdomain stackSem.sh_mdomain
    stackSem.be stackSem.ffi stackSem.clock stackSem.code stackSem.ffi_save_regs
    stackSem.code_buffer stackSem.compile stackSem.compile_oracle stackSem.use_stack
    stackSem.use_store stackSem.use_alloc].
  assert (Hr : forall n v, FLOOKUP (FEMPTY |++ MAP (fun r => (r, read_reg r s)) regs0) n = SOME v ->
      labSem.regs s n = v).
  { intros n v H. exact (FLOOKUP_regs regs0 n v tt s H). }
  assert (Hfp : forall n v, FLOOKUP (FEMPTY : fmap N word64) n = SOME v -> labSem.fp_regs s n = v).
  { intros n v H. discriminate H. }
  intuition; discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "MAP_FST_compile_compile" *)
Local Lemma MAP_FST_compile_compile : forall jump0 off gen max_heap k dc (cd : list (N * prog a)),
 MAP FST (stack_remove.compile jump0 off gen max_heap k bvl_to_bvi.InitGlobals_location
   (stack_alloc.compile dc (stack_rawcall.compile cd))) = 0 :: 1 :: 2 :: gc_stub_location :: MAP FST cd.
Proof.
 intros. unfold stack_remove.compile, stack_remove.init_stubs, stack_alloc.compile, stack_alloc.stubs,
   stack_rawcall.compile. cbv zeta.
 rewrite !map_app, !map_map. cbn [MAP FST stack_remove.prog_comp stack_alloc.prog_comp APPEND].
 do 4 f_equal. apply map_ext. intros [n p]. reflexivity.
Qed.
(** HOL rebinds [next_lab_non_zero]; retain the earlier Rocq declaration. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "next_lab_non_zero" 3211 *)
Local Lemma next_lab_non_zero_rebound : forall p : prog a,
  1 <= stack_alloc.next_lab p 1 /\ 2 <= stack_alloc.next_lab p 2.
Proof. intros; split; rewrite stack_allocProof.next_lab_EQ_MAX, MAX_max; lia. Qed.
(** HOL repeats [MAP_prog_to_section_FST] here; reuse its earlier port. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "extract_label_store_list_code" *)
Local Lemma extract_label_store_list_code : forall ad t (ls : list (word a + N)),
 extract_labels (stack_remove.store_list_code ad t ls) = [].
Proof.
 intros ad t ls. induction ls as [|[w|i] ls IH];
  cbn [stack_remove.store_list_code extract_labels list_Seq]; rewrite ?IH; reflexivity.
Qed.
Local Lemma gc_code_labels_empty (dc : data_to_word.config) : extract_labels (@stack_alloc.word_gc_code a dc) = [].
Proof. unfold stack_alloc.word_gc_code. destruct (data_to_word.gc_kind dc) as [| |sizes]; try destruct sizes; cbn [stack_alloc.memcpy_code stack_alloc.clear_top_inst stack_alloc.word_gc_move_code stack_alloc.word_gc_move_list_code stack_alloc.word_gc_move_loop_code stack_alloc.word_gc_move_bitmap_code stack_alloc.word_gc_move_bitmaps_code stack_alloc.word_gc_move_roots_bitmaps_code stack_alloc.word_gen_gc_move_code stack_alloc.word_gen_gc_partial_move_code stack_alloc.word_gen_gc_move_bitmap_code stack_alloc.word_gen_gc_partial_move_bitmap_code stack_alloc.word_gen_gc_move_bitmaps_code stack_alloc.word_gen_gc_partial_move_bitmaps_code stack_alloc.word_gen_gc_move_roots_bitmaps_code stack_alloc.word_gen_gc_partial_move_roots_bitmaps_code stack_alloc.word_gen_gc_move_list_code stack_alloc.word_gen_gc_partial_move_list_code stack_alloc.word_gen_gc_move_data_code stack_alloc.word_gen_gc_partial_move_ref_list_code stack_alloc.word_gen_gc_partial_move_data_code stack_alloc.word_gen_gc_move_refs_code stack_alloc.word_gen_gc_move_loop_code stack_alloc.word_gc_partial_or_full stack_alloc.SetNewTrigger stack_alloc.word_gc_code extract_labels list_Seq APPEND]; reflexivity. Qed.

Local Lemma init_code_labels_empty gen mh k : extract_labels (@stack_remove.init_code a gen mh k) = [].
Proof.
 unfold stack_remove.init_code; cbv zeta.
 cbn [extract_labels list_Seq stack_remove.init_memory].
 rewrite extract_label_store_list_code. reflexivity.
Qed.
Definition initial_prog_labels (np : N * prog a) : bool :=
 let (n,p) := np in EVERY (fun '(l1,l2) => (l1 =? n) && negb (l2 =? 0) && negb (l2 =? 1)) (extract_labels p) && ALL_DISTINCT (extract_labels p).
Local Lemma initial_prog_labels_alloc np : initial_prog_labels np -> initial_prog_labels (stack_alloc.prog_comp np).
Proof.
 destruct np as [n p]. unfold initial_prog_labels, stack_alloc.prog_comp.
 intros H. apply Bool.andb_true_iff in H as [H1 H2].
 pose proof (stack_allocProof.stack_alloc_lab_pres n (stack_alloc.next_lab p 2) p (conj H1 (conj H2 (N.le_refl _)))) as H.
 destruct (stack_alloc.comp n (stack_alloc.next_lab p 2) p) as [cp nl]. cbn [FST] in *.
 destruct H as (H & H' & _). apply Bool.andb_true_iff; auto.
Qed.

Local Lemma every_initial_map {B : Type} (f : B -> N * prog a) (P : B -> bool) xs :
 (forall x, P x -> initial_prog_labels (f x)) -> EVERY P xs -> EVERY initial_prog_labels (MAP f xs).
Proof.
 intros Hf Hxs. apply EVERY_Forall. apply Forall_map.
 eapply Forall_impl; [exact Hf|]. apply EVERY_Forall; exact Hxs.
Qed.
Local Lemma initial_labels_pipeline f jump0 off gen mh sp start dc (cd : list (N * prog a)) :
 EVERY initial_prog_labels cd ->
 EVERY initial_prog_labels (stack_names.compile f (stack_remove.compile jump0 off gen mh sp start
    (stack_alloc.compile dc (stack_rawcall.compile cd)))).
Proof.
 intros H.
 assert (HR : EVERY initial_prog_labels (stack_rawcall.compile cd)).
 { unfold stack_rawcall.compile; cbv zeta. eapply every_initial_map; [|exact H].
   intros [n p] Hp. unfold initial_prog_labels in *.
   rewrite (proj2 (stack_rawcallProof.extract_labels_comp _ _)). exact Hp. }
 assert (HA : EVERY initial_prog_labels (stack_alloc.compile dc (stack_rawcall.compile cd))).
 { unfold stack_alloc.compile, stack_alloc.stubs. apply EVERY_Forall; apply Forall_app; split.
   - constructor; [|constructor]. unfold initial_prog_labels; cbn [extract_labels].
     rewrite gc_code_labels_empty. reflexivity.
   - apply EVERY_Forall. eapply every_initial_map; [|exact HR]. intros np Hp. apply initial_prog_labels_alloc, Hp. }
 assert (HM : EVERY initial_prog_labels (stack_remove.compile jump0 off gen mh sp start
    (stack_alloc.compile dc (stack_rawcall.compile cd)))).
 { unfold stack_remove.compile, stack_remove.init_stubs. apply EVERY_Forall; apply Forall_app; split.
   - repeat constructor; unfold initial_prog_labels; cbn [extract_labels stack_remove.halt_inst];
      rewrite ?init_code_labels_empty; reflexivity.
   - apply EVERY_Forall. eapply every_initial_map; [|exact HA]. intros [n p] Hp.
     unfold initial_prog_labels, stack_remove.prog_comp in *.
     rewrite <- stack_removeProof.stack_remove_lab_pres. exact Hp. }
 unfold stack_names.compile. eapply every_initial_map; [|exact HM]. intros [n p] Hp.
 unfold initial_prog_labels, stack_names.prog_comp in *.
 rewrite <- stack_namesProof.stack_names_lab_pres. exact Hp.
Qed.

Local Lemma map_fst_names f (ps : list (N * prog a)) :
 MAP FST (stack_names.compile f ps) = MAP FST ps.
Proof. unfold stack_names.compile. rewrite map_map. apply map_ext. intros [n p]; reflexivity. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_to_lab_compile_lab_pres" *)
Theorem stack_to_lab_compile_lab_pres : forall sc dc mh sp off (ps : list (N * prog a)),
 EVERY (fun n => negb (n =? 0) && negb (n =? 1) && negb (n =? 2) && negb (n =? gc_stub_location)) (MAP FST ps) /\
 EVERY (fun '(n,p) =>
  EVERY (fun '(l1,l2) => (l1 =? n) && negb (l2 =? 0) && negb (l2 =? 1)) (extract_labels p) &&
  ALL_DISTINCT (extract_labels p)) ps /\ ALL_DISTINCT (MAP FST ps) ->
 labels_ok (stack_to_lab.compile sc dc mh sp off ps).
Proof.
 intros sc dc mh sp off ps (HN & HL & HD).
 unfold stack_to_lab.compile. apply prog_to_section_labels_ok. split.
 - apply initial_labels_pipeline; exact HL.
 - rewrite map_fst_names, MAP_FST_compile_compile.
   apply ALL_DISTINCT_NoDup_list. apply ALL_DISTINCT_NoDup_list in HD.
   change (NoDup ([0;1;2;gc_stub_location] ++ MAP FST ps)).
   apply NoDup_app_sep.
   + change (NoDup [0;1;2;4]). repeat constructor; simpl; intuition congruence.
   + exact HD.
   + intros x Hpre Hpost. apply EVERY_Forall in HN. rewrite Forall_forall in HN.
     specialize (HN x Hpost). unfold is_true in HN.
     rewrite !Bool.andb_true_iff, !Bool.negb_true_iff, !N.eqb_neq in HN.
     simpl in Hpre. destruct Hpre as [Hx|[Hx|[Hx|[Hx|[]]]]]; subst x; tauto.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "good_code_def" *)
Definition good_code (sp : N) (code0 : list (N * prog a)) : Prop :=
  ALL_DISTINCT (MAP FST code0) /\
  EVERY (fun '(k, p) => (stack_num_stubs <=? k) && stackProps.alloc_arg p) code0 /\
  EVERY (fun p => call_args p 1 2 3 4 0) (MAP SND code0) /\
  EVERY (fun p => reg_bound p sp) (MAP SND code0) /\
  EVERY (fun '(n, p) =>
    EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0) && negb (l2 =? 1)) (extract_labels p) &&
    ALL_DISTINCT (extract_labels p)) code0.

(** Local helpers for the composition of the initialisation correctness proofs. *)
Local Lemma initial_regs_lookup (s : labSem.state a c ffi_t) (rs : list N) n :
 In n rs -> FLOOKUP (FEMPTY |++ MAP (fun r => (r, read_reg r s)) rs) n = SOME (read_reg n s).
Proof.
 induction rs using List.rev_ind; intros Hin; [contradiction|].
 rewrite map_app, FUPDATE_LIST_APPEND.
 change (FLOOKUP ((FEMPTY |++ MAP (fun r => (r, read_reg r s)) rs) |+ (x, read_reg x s)) n = SOME (read_reg n s)).
 rewrite FLOOKUP_UPDATE. destruct (decide (x = n)) as [->|Hne]; [reflexivity|].
 apply IHrs. apply in_app_or in Hin. destruct Hin as [H|[H|[]]]; [exact H|congruence].
Qed.
Local Lemma initial_renamed_regs f cd co cd3 co3 save (s : labSem.state a c ffi_t) r :
 BIJ (stack_names.find_name f) UNIV UNIV -> In r [2;3;4] ->
 FLOOKUP (regs (stack_namesProof.make_init f cd co
   (make_init cd3 co3 (MAP (stack_names.find_name f) [2;3;4]) save s))) r =
 SOME (read_reg (stack_names.find_name f r) s).
Proof.
 intros HB Hin.
 unfold stack_namesProof.make_init. cbn [stackSem.set_ffi_save_regs stackSem.set_compile_oracle
  stackSem.set_compile stackSem.set_regs stackSem.set_code stackSem.regs make_init].
 rewrite <- (LINV_DEF (stack_names.find_name f) UNIV UNIV (proj1 HB) r Logic.I) at 1.
 rewrite FLOOKUP_MAP_KEYS_MAPPED by exact (proj1 (BIJ_LINV_BIJ _ _ _ HB)).
 apply initial_regs_lookup. apply in_map, Hin.
Qed.

Local Lemma memory_assumption_propagates f cd co cd3 co3 save (s : labSem.state a c ffi_t) bm dsp :
 BIJ (stack_names.find_name f) UNIV UNIV -> good_dimindex a -> memory_assumption f bm dsp s ->
 stack_removeProof.propagate_these (stack_namesProof.make_init f cd co
   (make_init cd3 co3 (MAP (stack_names.find_name f) [2;3;4]) save s)) bm dsp.
Proof.
 intros HB Hg (p2 & p3 & p4 & bp & R2 & R3 & R4 & M0 & M1 & M2 & M3 & M4 & Hcb & Hle & Ha2 & Ha4 & Hab & Hlen & Hmem).
 unfold stack_removeProof.propagate_these. split; [exact Hg|]. exists p2,p3,p4,bp.
 split; [rewrite initial_renamed_regs by (assumption || simpl; tauto); rewrite R2; reflexivity|].
 split; [rewrite initial_renamed_regs by (assumption || simpl; tauto); rewrite R3; reflexivity|].
 split; [rewrite initial_renamed_regs by (assumption || simpl; tauto); rewrite R4; reflexivity|].
 cbn [stack_namesProof.make_init make_init stackSem.set_ffi_save_regs stackSem.set_compile_oracle
  stackSem.set_compile stackSem.set_regs stackSem.set_code stackSem.memory stackSem.mdomain stackSem.code_buffer].
 do 2 (split; [assumption|]). split.
 - rewrite M2. f_equal. rewrite <- !WORD_ADD_ASSOC. f_equal. apply WORD_ADD_COMM.
 - repeat split; assumption.
Qed.

Local Lemma inverse_saved_regs f save sp :
 BIJ (stack_names.find_name f) UNIV UNIV -> 2 <= sp ->
 EVERY (fun r => bool_decide (stack_names.find_name f (r + sp - 2) IN save)) [2;3;4] ->
 (sp INSERT ((sp + 1) INSERT ((sp + 2) INSERT EMPTY))) SUBSET
    IMAGE (LINV (stack_names.find_name f) UNIV) save.
Proof.
 intros HB Hsp Hsave. unfold pred_set.SUBSET. intros x Hx.
 change (x = sp \/ x = sp + 1 \/ x = sp + 2 \/ False) in Hx.
 apply EVERY_Forall in Hsave. inversion Hsave as [|r rs H2 Hrest]; subst.
 inversion Hrest as [|r rs H3 Hrest2]; subst. inversion Hrest2 as [|r rs H4 Hnil]; subst.
 apply bool_decide_spec in H2. apply bool_decide_spec in H3. apply bool_decide_spec in H4.
 exists (stack_names.find_name f x). split.
 - symmetry. exact (LINV_DEF (stack_names.find_name f) UNIV UNIV (proj1 HB) x Logic.I).
 - destruct Hx as [->|[->|[->|[]]]].
   + replace (2 + sp - 2) with sp in H2 by lia; exact H2.
   + replace (3 + sp - 2) with (sp+1) in H3 by lia; exact H3.
   + replace (4 + sp - 2) with (sp+2) in H4 by lia; exact H4.
Qed.

Local Lemma good_code_names sp (ps : list (N * prog a)) : good_code sp ps ->
 EVERY (fun n => (stack_num_stubs <=? n)) (MAP FST ps).
Proof.
 intros (_ & H & _). apply EVERY_Forall. apply Forall_map. apply EVERY_Forall in H.
 eapply Forall_impl; [|exact H]. intros [n p] Hnp. apply Bool.andb_true_iff in Hnp; exact (proj1 Hnp).
Qed.
Local Lemma reg_names_combine (ps : list (N * prog a)) sp :
 EVERY (fun p => reg_bound p sp) (MAP SND ps) ->
 EVERY (fun n => (stack_num_stubs <=? n + 1)) (MAP FST ps) ->
 EVERY (fun '(n,p) => reg_bound p sp && (stack_num_stubs <=? n + 1)) ps.
Proof.
 intros HR HN. apply EVERY_Forall in HR. apply EVERY_Forall in HN.
 rewrite Forall_map, Forall_forall in HR,HN. apply EVERY_Forall. rewrite Forall_forall.
 intros [n p] Hp. apply Bool.andb_true_iff. split; [exact (HR (n,p) Hp)|exact (HN (n,p) Hp)].
Qed.
Local Lemma alloc_comp_reg_bound (dc : data_to_word.config) sp (ps : list (N * prog a)) :
 10 <= sp -> EVERY (fun p => reg_bound p sp) (MAP SND ps) ->
 EVERY (fun p => reg_bound p sp) (MAP SND (MAP stack_alloc.prog_comp ps)).
Proof.
 intros Hsp H. pose proof (stack_allocProof.stack_alloc_reg_bound sp ps dc (conj Hsp H)) as Hreg.
 unfold stack_alloc.compile in Hreg. rewrite map_app in Hreg. apply EVERY_Forall in Hreg. apply Forall_app in Hreg.
 apply EVERY_Forall. exact (proj2 Hreg).
Qed.
Local Lemma map_fst_alloc (ps : list (N * prog a)) : MAP FST (MAP stack_alloc.prog_comp ps) = MAP FST ps.
Proof. rewrite map_map. apply map_ext. intros [n p]; reflexivity. Qed.
Local Lemma alloc_code_names dc (ps : list (N * prog a)) :
 MAP FST (stack_alloc.compile dc (stack_rawcall.compile ps)) = gc_stub_location :: MAP FST ps.
Proof.
 unfold stack_alloc.compile, stack_alloc.stubs. rewrite map_app, map_fst_alloc,
 stack_rawcallProof.MAP_FST_compile. reflexivity.
Qed.
Local Lemma good_code_alloc_pre dc sp (ps : list (N * prog a)) :
 10 <= sp -> good_code sp ps ->
 EVERY (fun '(n,p) => reg_bound p sp && (stack_num_stubs <=? n+1))
  (stack_alloc.compile dc (stack_rawcall.compile ps)).
Proof.
 intros Hsp H. apply reg_names_combine.
 - apply stack_allocProof.stack_alloc_reg_bound. split; [exact Hsp|].
   rewrite stack_rawcallProof.stack_rawcall_reg_bound. exact (proj1 (proj2 (proj2 (proj2 H)))).
 - rewrite alloc_code_names. cbn [EVERY].
   change ((stack_num_stubs <=? gc_stub_location + 1) && EVERY (fun n => stack_num_stubs <=? n+1) (MAP FST ps) = true).
   apply Bool.andb_true_iff; split; [reflexivity|].
   pose proof (good_code_names _ _ H) as Hn. apply EVERY_Forall in Hn.
   apply EVERY_Forall. eapply Forall_impl; [|exact Hn]. intros n Hle. apply N.leb_le in Hle; apply N.leb_le; lia.
Qed.

Local Lemma good_code_alloc_map_pre (dc : data_to_word.config) sp (ps : list (N * prog a)) :
 10 <= sp -> good_code sp ps ->
 EVERY (fun '(n,p) => reg_bound p sp && (stack_num_stubs <=? n+1)) (MAP stack_alloc.prog_comp ps).
Proof.
 intros Hsp H. apply reg_names_combine.
 - apply (alloc_comp_reg_bound dc); [exact Hsp|exact (proj1 (proj2 (proj2 (proj2 H))))].
 - rewrite map_fst_alloc. pose proof (good_code_names _ _ H) as Hn. apply EVERY_Forall in Hn.
   apply EVERY_Forall. eapply Forall_impl; [|exact Hn]. intros n Hle. apply N.leb_le in Hle; apply N.leb_le; lia.
Qed.

Local Lemma initialization_discharge f dc jump0 off gen mh sp start (ps : list (N * prog a))
    co cd3 co3 save (t : labSem.state a c ffi_t) :
 good_code sp ps -> (forall n, good_code sp (FST (SND (co n)))) ->
 10 <= sp -> stack_remove.max_stack_alloc <= mh -> BIJ (stack_names.find_name f) UNIV UNIV ->
 EVERY (fun r => bool_decide (stack_names.find_name f (r+sp-2) IN save)) [2;3;4] ->
 let co1 := (I ## (MAP stack_alloc.prog_comp ## I)) ∘ co in
 let co2 := (I ## (MAP (stack_remove.prog_comp jump0 off sp) ## I)) ∘ co1 in
 let cd1 := stack_alloc.compile dc (stack_rawcall.compile ps) in
 let cd2 := stack_remove.compile jump0 off gen mh sp start cd1 in
 stack_removeProof.discharge_these jump0 off gen mh sp start co1 cd1
  (stack_namesProof.make_init f (fromAList cd2) co2
    (make_init cd3 co3 (MAP (stack_names.find_name f) [2;3;4]) save t)).
Proof.
 intros Hcode Hor Hsp Hmh HB Hsave. cbv zeta. unfold stack_removeProof.discharge_these.
 split; [apply good_code_alloc_pre; assumption|]. split.
 - intros n i p Hmem. destruct (co n) as [cfg [pr bm]] eqn:E.
   specialize (Hor n). rewrite E in Hor. cbn [FST SND] in Hor.
   cbn [PAIR_MAP I FST SND fst snd] in Hmem.
   pose proof (good_code_alloc_map_pre dc sp pr Hsp Hor) as H.
   apply EVERY_Forall in H. rewrite Forall_forall in H. unfold is_true in Hmem. rewrite MEM_In in Hmem.
   specialize (H (i,p) Hmem). apply Bool.andb_true_iff in H. split; [exact (proj1 H)|].
   apply N.leb_le; exact (proj2 H).
 - cbn [stack_namesProof.make_init make_init stackSem.set_ffi_save_regs stackSem.set_compile_oracle
    stackSem.set_compile stackSem.set_regs stackSem.set_code stackSem.code stackSem.compile_oracle
    stackSem.ffi_save_regs stackSem.use_stack stackSem.use_store stackSem.use_alloc].
   split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split.
   + apply domain_lookup. eexists. rewrite lookup_fromAList. reflexivity.
   + split; [apply inverse_saved_regs; [exact HB|lia|exact Hsave]|].
     split; [discriminate|]. split; [discriminate|]. split; [discriminate|exact Hmh].
Qed.


Local Lemma initialized_alloc_bound gen mh bm dsp co jp off sp cd (s si : stackSem.state a c ffi_t) :
 stack_removeProof.make_init_opt gen mh bm dsp co jp off sp cd s = SOME si ->
 LENGTH (bitmaps si) + LENGTH (wordSem.buffer_buffer (data_buffer si)) + wordSem.space_left (data_buffer si) < dimword a - 1.
Proof.
 unfold stack_removeProof.make_init_opt.
 destruct (evaluate _) as [[r|] st] eqn:E; [discriminate|].
 destruct (classical_dec _) as [Hprop|Hprop]; [|discriminate].
 intros Hsi. injection Hsi as <-.
 unfold stack_removeProof.init_prop in Hprop. destruct Hprop as (curr & other & bp & len & Hprop).
 cbn [stack_removeProof.init_reduce bitmaps data_buffer wordSem.buffer_buffer wordSem.space_left] in *.
 assert (Hlen : LENGTH bm + dsp + 1 < dimword a) by tauto.
 change (LENGTH bm + 0 + dsp < dimword a - 1). lia.
Qed.


Local Lemma good_code_entry sp (ps : list (N * prog a)) : good_code sp ps -> forall n p, In (n,p) ps ->
 n <> gc_stub_location /\ alloc_arg p.
Proof.
 intros (_ & H & _) n p Hin. apply EVERY_Forall in H. rewrite Forall_forall in H.
 specialize (H (n,p) Hin). apply Bool.andb_true_iff in H as [Hn Hp]. split; [|exact Hp].
 apply N.leb_le in Hn. change (5 <= n) in Hn. change (n <> 4). lia.
Qed.
Local Lemma good_code_rawcall_entry sp (ps : list (N * prog a)) : good_code sp ps ->
 forall k p, ALOOKUP (stack_rawcall.compile ps) k = SOME p -> k <> gc_stub_location /\ alloc_arg p.
Proof.
 intros Hgood k p Hlook. apply ALOOKUP_MEM in Hlook. unfold is_true in Hlook; rewrite MEM_In in Hlook.
 unfold stack_rawcall.compile in Hlook; cbv zeta in Hlook.
 apply in_map_iff in Hlook. destruct Hlook as ([n q] & Eq & Hin).
 injection Eq as En Ep. subst n p.
 rewrite (proj2 (stack_rawcallProof.call_arg_comp _ _)). exact (good_code_entry _ _ Hgood k q Hin).
Qed.


Local Lemma good_code_label_pres sc dc mh sp off (ps : list (N * prog a)) :
 good_code sp ps -> labels_ok (stack_to_lab.compile sc dc mh sp off ps).
Proof.
 intros H. apply stack_to_lab_compile_lab_pres. split.
 - pose proof (good_code_names _ _ H) as Hn. apply EVERY_Forall in Hn.
   apply EVERY_Forall. eapply Forall_impl; [|exact Hn]. intros n Hle.
   apply N.leb_le in Hle. change (5 <= n) in Hle.
   unfold is_true. rewrite !Bool.andb_true_iff, !Bool.negb_true_iff, !N.eqb_neq.
   unfold gc_stub_location, stack_num_stubs. cbn. lia.
 - split; [exact (proj2 (proj2 (proj2 (proj2 H))))|exact (proj1 H)].
Qed.
Local Lemma labels_no_stubs f jp off sp (ps : list (N * prog a)) :
 EVERY initial_prog_labels ps ->
 EVERY initial_prog_labels
   (stack_names.compile f (MAP (stack_remove.prog_comp jp off sp) (MAP stack_alloc.prog_comp ps))).
Proof.
 intros H. unfold stack_names.compile. eapply (every_initial_map _ initial_prog_labels _).
 - intros [n p] Hp. unfold initial_prog_labels, stack_names.prog_comp in *.
   rewrite <- stack_namesProof.stack_names_lab_pres; exact Hp.
 - eapply (every_initial_map _ initial_prog_labels _).
   + intros [n p] Hp. unfold initial_prog_labels, stack_remove.prog_comp in *.
     rewrite <- stack_removeProof.stack_remove_lab_pres; exact Hp.
   + eapply (every_initial_map _ initial_prog_labels _); [|exact H].
     intros np Hp. apply initial_prog_labels_alloc, Hp.
Qed.
Local Lemma call_args_no_stubs f jp off sp (ps : list (N * prog a)) :
 EVERY (fun p => call_args p 1 2 3 4 0) (MAP SND ps) ->
 EVERY (fun p => call_args p (stack_names.find_name f 1) (stack_names.find_name f 2)
   (stack_names.find_name f 3) (stack_names.find_name f 4) (stack_names.find_name f 0))
 (MAP SND (stack_names.compile f (MAP (stack_remove.prog_comp jp off sp) (MAP stack_alloc.prog_comp ps)))).
Proof.
 intros H. apply EVERY_Forall in H. rewrite Forall_map in H.
 unfold stack_names.compile. rewrite !map_map. apply EVERY_Forall. apply Forall_map.
 eapply Forall_impl; [|exact H]. intros [n p] Hp. cbn [SND stack_alloc.prog_comp stack_remove.prog_comp stack_names.prog_comp].
 apply stack_namesProof.call_args_comp. apply stack_removeProof.call_args_comp.
 apply stack_allocProof.comp_call_args. exact Hp.
Qed.
Local Lemma map_fst_remove jp off sp (ps : list (N * prog a)) :
 MAP FST (MAP (stack_remove.prog_comp jp off sp) ps) = MAP FST ps.
Proof. rewrite map_map. apply map_ext. intros [n p]; reflexivity. Qed.


Local Lemma oracle_labels_call_args f jp off sp (ps : list (N * prog a)) : good_code sp ps ->
 let qs := stack_names.compile f (MAP (stack_remove.prog_comp jp off sp) (MAP stack_alloc.prog_comp ps)) in
 EVERY (fun '(n,p) =>
   call_args p (stack_names.find_name f 1) (stack_names.find_name f 2) (stack_names.find_name f 3)
     (stack_names.find_name f 4) (stack_names.find_name f 0) &&
   EVERY (fun '(l1,l2) => (l1 =? n) && negb (l2 =? 0) && negb (l2 =? 1)) (extract_labels p) &&
   ALL_DISTINCT (extract_labels p)) qs /\ ALL_DISTINCT (MAP FST qs).
Proof.
 intros Hgood; cbv zeta. split.
 - pose proof (call_args_no_stubs f jp off sp ps (proj1 (proj2 (proj2 Hgood)))) as Hca.
   pose proof (labels_no_stubs f jp off sp ps (proj2 (proj2 (proj2 (proj2 Hgood))))) as HL.
   apply EVERY_Forall in Hca. rewrite Forall_map, Forall_forall in Hca.
   apply EVERY_Forall in HL. rewrite Forall_forall in HL.
   apply EVERY_Forall. rewrite Forall_forall. intros [n p] Hin.
   specialize (Hca (n,p) Hin). specialize (HL (n,p) Hin).
   unfold initial_prog_labels in HL. apply Bool.andb_true_iff in HL as [HL HD].
   apply Bool.andb_true_iff. split; [apply Bool.andb_true_iff; split; assumption|exact HD].
 - rewrite map_fst_names, map_fst_remove, map_fst_alloc. exact (proj1 Hgood).
Qed.

(** HOL rebinds this theorem after removing its proof-only [Abbrev] marker. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "full_make_init_semantics" 3617 *)
Theorem full_make_init_semantics : forall sc dc mh sp off (bm : list (word a)) cd
 (t : labSem.state a c ffi_t) save dsp co s opt,
 full_make_init sc dc mh sp off bm cd t save dsp co = (s,opt) /\
 good_dimindex a /\
 labSem.code t = stack_to_lab.compile sc dc mh sp off cd /\
 labSem.compile_oracle t = (fun n => let '(cfg,(ps,_)) := co n in
   (cfg, compile_no_stubs (reg_names sc) (stack_to_lab.jump sc) off sp ps)) /\
 ~ failed t /\ memory_assumption (reg_names sc) bm dsp t /\
 stack_remove.max_stack_alloc <= mh /\ ~ (link_reg t IN save) /\ pc t = 0 /\
 (forall k i n, k IN save -> io_regs t n i k = NONE) /\
 (forall k n, k IN save -> cc_regs t n k = NONE) /\
 (forall x, x IN mem_domain t -> w2n x MOD (dimindex a DIV 8) = 0) /\
 (forall x, x IN shared_mem_domain t -> w2n x MOD (dimindex a DIV 8) = 0) /\
 good_code sp cd /\ (forall n, good_code sp (FST (SND (co n)))) /\ 10 <= sp /\
 EVERY (fun r => bool_decide (stack_names.find_name (reg_names sc) (r+sp-2) IN save)) [2;3;4] /\
 stack_names.find_name (reg_names sc) 4 = len2_reg t /\
 stack_names.find_name (reg_names sc) 3 = ptr2_reg t /\
 stack_names.find_name (reg_names sc) 2 = len_reg t /\
 stack_names.find_name (reg_names sc) 1 = ptr_reg t /\
 stack_names.find_name (reg_names sc) 0 = link_reg t /\
 BIJ (stack_names.find_name (reg_names sc)) UNIV UNIV ->
 opt <> NONE /\ (semantics bvl_to_bvi.InitGlobals_location s <> Fail ->
    labSem.semantics t = semantics bvl_to_bvi.InitGlobals_location s).
Proof.
 intros sc dc mh sp off bm cd t save dsp co s opt
  (E & Hg & Hcode & Hor & Hfail & Hmem & Hmh & Hlink & Hpc & Hio & Hcc & Hmd & Hsmd & Hgood & Horgood & Hsp & Hsave & R4 & R3 & R2 & R1 & R0 & HB).
 set (ggc := is_gen_gc (data_to_word.gc_kind dc)).
 set (jp := stack_to_lab.jump sc).
 set (f := reg_names sc).
 set (cd1 := stack_alloc.compile dc (stack_rawcall.compile cd)).
 set (cd2 := stack_remove.compile jp off ggc mh sp bvl_to_bvi.InitGlobals_location cd1).
 set (cd3 := fromAList (stack_names.compile f cd2)).
 set (co1 := (I ## (MAP (@stack_alloc.prog_comp a) ## I)) ∘ co).
 set (co2 := (I ## (MAP (stack_remove.prog_comp jp off sp) ## I)) ∘ co1).
 set (co3 := (I ## (stack_names.compile f ## I)) ∘ co2).
 set (s3 := make_init cd3 co3 (MAP (stack_names.find_name f) [2;3;4]) save t).
 set (s2 := stack_namesProof.make_init f (fromAList cd2) co2 s3).
 set (s1 := stack_removeProof.make_init_any ggc mh bm dsp co1 jp off sp (fromAList cd1) s2).
 change ((stack_allocProof.make_init dc (fromAList cd) co s1,
   stack_removeProof.make_init_opt ggc mh bm dsp co1 jp off sp (fromAList cd1) s2) = (s,opt)) in E.
 injection E as Es Eopt. subst s opt.
 assert (HD : stack_removeProof.discharge_these jp off ggc mh sp bvl_to_bvi.InitGlobals_location co1 cd1 s2).
 { apply initialization_discharge; assumption. }
 assert (HP : stack_removeProof.propagate_these s2 bm dsp).
 { apply memory_assumption_propagates; assumption. }
 destruct (stack_removeProof.make_init_semantics jp off ggc mh sp bvl_to_bvi.InitGlobals_location co1 cd1 s2 bm dsp (conj HD HP)) as (si & Hsi & Hsem).
 assert (Es1 : s1 = si).
 { unfold s1, stack_removeProof.make_init_any. rewrite Hsi. reflexivity. }
 split; [change (stack_removeProof.make_init_opt ggc mh bm dsp co1 jp off sp (fromAList cd1) s2 <> NONE); rewrite Hsi; discriminate|].
 rewrite Es1. intros HF.
 assert (Hraw : semantics bvl_to_bvi.InitGlobals_location
   (stack_allocProof.make_init dc (fromAList (stack_rawcall.compile cd)) co si) =
   semantics bvl_to_bvi.InitGlobals_location (stack_allocProof.make_init dc (fromAList cd) co si)).
 { apply (stack_rawcallProof.compile_semantics cd
     (stack_allocProof.make_init dc (fromAList cd) co si) bvl_to_bvi.InitGlobals_location).
   split; [exact (proj1 Hgood)|]. split; [reflexivity|]. split; [reflexivity|exact HF]. }
 assert (HA : semantics bvl_to_bvi.InitGlobals_location si =
   semantics bvl_to_bvi.InitGlobals_location (stack_allocProof.make_init dc
     (fromAList (stack_rawcall.compile cd)) co si)).
 { apply stack_allocProof.make_init_semantics.
   split; [apply good_code_rawcall_entry with sp; exact Hgood|]. split.
   - intros n k p Hmp. apply (good_code_entry sp (FST (SND (co n))) (Horgood n)).
     unfold is_true in Hmp; rewrite MEM_In in Hmp; exact Hmp.
   - split; [rewrite <- Es1; apply stack_removeProof.make_init_any_use_stack|].
     split; [rewrite <- Es1; apply stack_removeProof.make_init_any_use_store|].
     split; [rewrite <- Es1; apply stack_removeProof.make_init_any_use_alloc|].
     split; [rewrite <- Es1; apply stack_removeProof.make_init_any_code|].
     split; [rewrite <- Es1; apply stack_removeProof.make_init_any_compile_oracle|].
     split; [eapply initialized_alloc_bound; exact Hsi|].
     split; [rewrite <- Es1; apply stack_removeProof.make_init_any_stack_limit|].
     split; [rewrite stack_rawcallProof.MAP_FST_compile; exact (proj1 Hgood)|].
     rewrite Hraw. exact HF. }
 assert (HNF : semantics bvl_to_bvi.InitGlobals_location si <> Fail) by (rewrite HA, Hraw; exact HF).
 specialize (Hsem HNF).
 rewrite <- Hraw, <- HA, <- Hsem.
 assert (Hct : labSem.code t = MAP prog_to_section (stack_names.compile f cd2)) by exact Hcode.
 assert (HL : labels_ok (labSem.code t)).
 { rewrite Hcode. apply good_code_label_pres; exact Hgood. }
 assert (HD2 : ALL_DISTINCT (MAP FST cd2)).
 { pose proof (proj1 (proj2 (labels_ok_imp _ HL))) as H.
   rewrite Hct, MAP_prog_to_section_Section_num, map_fst_names in H. exact H. }
 assert (Hnames : semantics 0 s3 = semantics 0 s2).
 { apply stack_namesProof.make_init_semantics.
   split; [discriminate|]. split; [discriminate|]. split; [discriminate|].
   split; [exact HB|]. split; [exact HD2|]. split; reflexivity. }
 rewrite <- Hnames.
 assert (Hca : EVERY (fun p => call_args p (ptr_reg t) (len_reg t) (ptr2_reg t) (len2_reg t) (link_reg t))
   (MAP SND (stack_names.compile f cd2))).
 { rewrite <- R1, <- R2, <- R3, <- R4, <- R0.
   apply (stack_namesProof.stack_names_call_args f cd2 (stack_names.compile f cd2)). split; [reflexivity|].
   apply (stack_removeProof.stack_remove_call_args jp off ggc mh sp bvl_to_bvi.InitGlobals_location cd1 cd2). split; [reflexivity|].
   apply (stack_allocProof.stack_alloc_call_args (stack_rawcall.compile cd) dc). rewrite stack_rawcallProof.stack_alloc_call_args.
   exact (proj1 (proj2 (proj2 Hgood))). }
 assert (HSR : state_rel s3 t).
 { unfold s3. apply state_rel_make_init. split.
   - intros n p Hlook. unfold cd3 in Hlook. rewrite lookup_fromAList in Hlook. split.
     + pose proof Hca as Hc. apply EVERY_Forall in Hc. rewrite Forall_map, Forall_forall in Hc.
       apply ALOOKUP_MEM in Hlook. unfold is_true in Hlook; rewrite MEM_In in Hlook. exact (Hc (n,p) Hlook).
     + rewrite Hct. apply code_installed_prog_to_section. split; [rewrite <-Hct; exact HL|exact Hlook].
   - split; [exact Hfail|]. split.
     + rewrite Hor. apply functional_extensionality; intros n.
       unfold co3,co2,co1. destruct (co n) as [cfg [ps bms]]. reflexivity.
     + split.
       * intros k. unfold co3,co2,co1. destruct (co k) as [cfg [ps bms]] eqn:Ek.
         cbn [PAIR_MAP I].
         pose proof (Horgood k) as Hk. rewrite Ek in Hk; cbn [FST SND] in Hk.
         rewrite <- R1, <- R2, <- R3, <- R4, <- R0. apply oracle_labels_call_args; exact Hk.
       * assert (Hinj : forall x y, stack_names.find_name f x = stack_names.find_name f y -> x = y).
         { intros x y Hxy. exact (proj2 (proj1 HB) x y (conj Logic.I Logic.I) Hxy). }
         split; [rewrite <- R0, <- R2; intros E0; apply Hinj in E0; discriminate|].
         split; [rewrite <- R0, <- R1; intros E0; apply Hinj in E0; discriminate|].
         split; [rewrite <- R0, <- R4; intros E0; apply Hinj in E0; discriminate|].
         split; [rewrite <- R0, <- R3; intros E0; apply Hinj in E0; discriminate|].
         split; [exact Hlink|]. split.
         -- unfold cd3. rewrite domain_fromAList, Hct, MAP_prog_to_section_Section_num.
            apply set_ext; intros n. apply MEM_set.
         -- split; [exact (proj1 (labels_ok_imp _ HL))|].
            split; [exact Hio|]. split; [exact Hcc|]. split; [exact Hmd|]. split; [exact Hsmd|exact Hg]. }
 apply (flatten_semantics 0 s3 t). split.
 - change (halt_assum ffi_t c cd3). unfold cd3, cd2. apply halt_assum_lemma.
 - split; [exact HSR|]. split.
   + rewrite Hct, Hpc. unfold cd2, stack_remove.compile, stack_remove.init_stubs, stack_names.compile.
     cbn [MAP stack_names.prog_comp APPEND]. rewrite prog_to_section_eq at 1. rewrite ltp_cons. reflexivity.
   + rewrite Hnames, Hsem; exact HNF.
Qed.
Local Lemma alloc_init_has_fp_ops : forall dc b1 b2 (cd : spt (prog a)) co (s : stackSem.state a c ffi_t),
 stack_allocProof.make_init {| data_to_word.tag_bits := data_to_word.tag_bits dc;
             data_to_word.len_bits := data_to_word.len_bits dc;
             data_to_word.pad_bits := data_to_word.pad_bits dc;
             data_to_word.len_size := data_to_word.len_size dc;
             data_to_word.has_div := data_to_word.has_div dc;
             data_to_word.has_longdiv := data_to_word.has_longdiv dc;
             data_to_word.has_fp_ops := b1;
             data_to_word.has_fp_tern := b2;
             data_to_word.be := data_to_word.be dc;
             data_to_word.call_empty_ffi := data_to_word.call_empty_ffi dc;
             data_to_word.gc_kind := data_to_word.gc_kind dc |} cd co s = stack_allocProof.make_init dc cd co s.
Proof. intros; unfold stack_allocProof.make_init; rewrite word_gcFunctions.word_gc_fun_has_fp_ops; reflexivity. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "full_make_init_has_fp_ops" *)
Theorem full_make_init_has_fp_ops : forall sc dc b1 b2 mh sp off bm (cd : list (N * prog a)) (s : labSem.state a c ffi_t) save dsp co,
 full_make_init sc {| data_to_word.tag_bits := data_to_word.tag_bits dc;
             data_to_word.len_bits := data_to_word.len_bits dc;
             data_to_word.pad_bits := data_to_word.pad_bits dc;
             data_to_word.len_size := data_to_word.len_size dc;
             data_to_word.has_div := data_to_word.has_div dc;
             data_to_word.has_longdiv := data_to_word.has_longdiv dc;
             data_to_word.has_fp_ops := b1;
             data_to_word.has_fp_tern := b2;
             data_to_word.be := data_to_word.be dc;
             data_to_word.call_empty_ffi := data_to_word.call_empty_ffi dc;
             data_to_word.gc_kind := data_to_word.gc_kind dc |} mh sp off bm cd s save dsp co =
 full_make_init sc dc mh sp off bm cd s save dsp co.
Proof. intros sc dc b1 b2 mh sp off bm cd s save dsp co.
 unfold full_make_init. rewrite stack_allocProof.compile_has_fp_ops.
 cbn [data_to_word.gc_kind]. rewrite alloc_init_has_fp_ops. reflexivity. Qed.
End Initialization.

Section EncoderSyntax.
Context {a : N}.
Local Lemma LAST_app_singleton {B} `{Inhabited B} (ls : list B) x : LAST (ls ++ [x]) = x.
Proof. induction ls as [|h ls IH]; [reflexivity|]. destruct ls; [reflexivity|exact IH]. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "EVERY_sec_ends_with_label_MAP_prog_to_section" *)
Theorem EVERY_sec_ends_with_label_MAP_prog_to_section : forall ps : list (N * prog a),
 EVERY sec_ends_with_label (MAP prog_to_section ps).
Proof.
 intros ps. apply EVERY_Forall. apply Forall_map. apply Forall_forall. intros [n p] Hin.
 unfold prog_to_section. destruct (flatten true p n (stack_alloc.next_lab p 2) [] []) as [xs [nr nl]].
 cbn [FST SND sec_ends_with_label]. rewrite append_Append, append_List. rewrite LAST_app_singleton.
 destruct (append xs); reflexivity.
Qed.

Local Ltac enc_norm :=
 cbn [FST andb orb];
 repeat rewrite append_Append; repeat rewrite append_List; repeat rewrite stack_allocProof.EVERY_app;
 cbn [EVERY line_ok_pre lab_to_target.cbw_to_asm asm_ok reg_ok];
 rewrite ?Bool.andb_true_r, ?Bool.andb_true_l.
Local Lemma flatten_lines_ok (cfg : asm_config a) : forall p : prog a,
 forall t n m cs bs, byte_offset_ok cfg (n2w 0) /\ stack_asm_ok cfg p ->
 EVERY (line_ok_pre cfg) (append (FST (flatten t p n m cs bs))).
Proof.
 intros p. induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind;
 intros t n m cs bs (Hbyte & Hok).
 - destruct ret as [[p1 [lr [l1 l2]]]|].
   + destruct h as [[p2 [k1 k2]]|].
     * cbn [stack_asm_ok] in Hok.
       apply Bool.andb_true_iff in Hok as [Hd Hps]. apply Bool.andb_true_iff in Hps as [H1 H2].
       pose proof (Hr p1 _ eq_refl false n m cs bs (conj Hbyte H1)) as E1.
       cbn [flatten]. destruct (flatten false p1 n m cs bs) as [xs [nr1 m1]] eqn:F1.
       pose proof (Hh p2 _ eq_refl false n m1 cs bs (conj Hbyte H2)) as E2.
       destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:F2.
       cbn [FST] in E1,E2 |- *. destruct dest; enc_norm;
       cbn [compile_jump line_ok_pre lab_to_target.cbw_to_asm asm_ok reg_ok] in *;
       unfold is_true in *; cbn [reg_ok] in *; rewrite ?Bool.andb_true_r in *; rewrite E1,E2; cbn; try reflexivity; unfold reg_ok; rewrite !Bool.andb_true_r; exact Hd.
     * cbn [stack_asm_ok] in Hok. apply Bool.andb_true_iff in Hok as [Hd Hps].
       apply Bool.andb_true_iff in Hps as [H1 _].
       pose proof (Hr p1 _ eq_refl false n m cs bs (conj Hbyte H1)) as E1.
       cbn [flatten]. destruct (flatten false p1 n m cs bs) as [xs [nr1 m1]] eqn:F1.
       cbn [FST] in E1 |- *. destruct dest; enc_norm;
       cbn [compile_jump line_ok_pre lab_to_target.cbw_to_asm asm_ok reg_ok] in *;
       unfold is_true in *; cbn [reg_ok] in *; rewrite ?Bool.andb_true_r in *; rewrite E1; cbn; try reflexivity; unfold reg_ok; rewrite !Bool.andb_true_r; exact Hd.
   + destruct dest; cbn [stack_asm_ok] in Hok; cbn [flatten FST]; enc_norm;
       cbn [compile_jump line_ok_pre lab_to_target.cbw_to_asm asm_ok reg_ok] in *;
       unfold is_true in *; unfold reg_ok; rewrite !Bool.andb_true_r in *; exact Hok.
 - cbn [stack_asm_ok] in Hok. apply Bool.andb_true_iff in Hok as [H1 H2].
   pose proof (IH1 false n m cs bs (conj Hbyte H1)) as E1.
   cbn [flatten]. destruct (flatten false p1 n m cs bs) as [xs [nr1 m1]] eqn:F1.
   pose proof (IH2 false n m1 cs bs (conj Hbyte H2)) as E2.
   destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:F2.
   cbn [FST] in E1,E2 |- *. destruct t; enc_norm; rewrite E1,E2; reflexivity.
 - cbn [stack_asm_ok] in Hok. apply Bool.andb_true_iff in Hok as [H1 H2].
   pose proof (IH1 false n m cs bs (conj Hbyte H1)) as E1.
   cbn [flatten]. destruct (flatten false p1 n m cs bs) as [xs [nr1 m1]] eqn:F1.
   pose proof (IH2 false n m1 cs bs (conj Hbyte H2)) as E2.
   destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:F2.
   cbn [FST] in E1,E2 |- *.
   destruct (is_Skip p1), (is_Skip p2), nr1, nr2; enc_norm; rewrite ?E1,?E2; reflexivity.
 - cbn [stack_asm_ok] in Hok.
   pose proof (IH false n (m+2) (m::cs) ((m+1)::bs) (conj Hbyte Hok)) as E.
   cbn [flatten]. destruct (flatten false p n (m+2) (m::cs) ((m+1)::bs)) as [xs [nr m1]].
   cbn [FST] in E |- *. enc_norm; rewrite E; reflexivity.
 - destruct p; try contradiction; cbn [stack_asm_ok] in Hok; cbn [flatten FST]; enc_norm;
   cbn [inst_ok addr_ok lab_to_target.cbw_to_asm reg_ok] in *; rewrite ?Bool.andb_true_r in *; try exact Hok; try reflexivity.
   + destruct a0. unfold addr_ok in Hok. unfold is_true in *.
     rewrite !Bool.andb_true_iff in *. tauto.
   + repeat match goal with |- context [MEM Store8 ?ls] =>
       replace (MEM Store8 ls) with false by (symmetry; apply Bool.not_true_iff_false;
         rewrite MEM_In; simpl; intuition congruence) end.
     cbn [ifb]. unfold is_true in *. unfold reg_ok. rewrite !Bool.andb_true_iff in *. tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_line_ok_pre" *)
Local Theorem flatten_line_ok_pre : forall t (p : prog a) n m cs bs ls nr nl cfg,
 byte_offset_ok cfg (n2w 0) /\ stack_asm_ok cfg p /\ flatten t p n m cs bs = (ls,(nr,nl)) ->
 EVERY (line_ok_pre cfg) (append ls).
Proof.
 intros t p n m cs bs ls nr nl cfg (Hb & Hp & E).
 pose proof (flatten_lines_ok cfg p t n m cs bs (conj Hb Hp)) as H. rewrite E in H. exact H.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "compile_all_enc_ok_pre" *)
Theorem compile_all_enc_ok_pre : forall cfg (ps : list (N * prog a)),
 byte_offset_ok cfg (n2w 0) /\ EVERY (fun '(n,p) => stack_asm_ok cfg p) ps ->
 all_enc_ok_pre cfg (MAP prog_to_section ps).
Proof.
 intros cfg ps (Hb & Hp). apply EVERY_Forall in Hp. rewrite Forall_forall in Hp.
 apply EVERY_Forall. apply Forall_map. apply Forall_forall. intros [n p] Hin.
 specialize (Hp (n,p) Hin).
 unfold prog_to_section. destruct (flatten true p n (stack_alloc.next_lab p 2) [] []) as [ls [nr nl]] eqn:E.
 cbn [sec_ok_pre]. rewrite append_Append, append_List, stack_allocProof.EVERY_app.
 apply Bool.andb_true_iff; split; [apply (flatten_line_ok_pre true p n (stack_alloc.next_lab p 2) [] [] ls nr nl cfg); repeat split; assumption|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_to_lab_compile_all_enc_ok" *)
Theorem stack_to_lab_compile_all_enc_ok : forall sc dc mh sp (cfg : asm_config a) (ps : list (N * prog a)),
 EVERY (fun '(n,p) => stack_asm_name cfg p) ps /\
 EVERY (fun '(n,p) => stack_asm_remove cfg p) ps /\
 stack_names.names_ok (reg_names sc) (reg_count cfg) (avoid_regs cfg) /\
 stackProps.fixed_names (reg_names sc) cfg /\
 addr_offset_ok cfg (n2w 0) /\ good_dimindex a /\ byte_offset_ok cfg (n2w 0) /\
 (forall n, n <= stack_remove.max_stack_alloc ->
  valid_imm cfg (inl asm.Sub) (n2w (n * (dimindex a DIV 8))) /\
  valid_imm cfg (inl asm.Add) (n2w (n * (dimindex a DIV 8)))) /\
 valid_imm cfg (inl asm.Add) (n2w 1) /\ valid_imm cfg (inl asm.Sub) (n2w 1) /\
 valid_imm cfg (inl asm.Add) (n2w 4) /\ valid_imm cfg (inl asm.Add) (n2w 8) /\
 (forall s, addr_offset_ok cfg (stack_remove.store_offset s)) /\ reg_name 10 cfg /\
 reg_name (sp+2) cfg /\ reg_name (sp+1) cfg /\ reg_name sp cfg /\ data_to_word.conf_ok a dc /\ sp <> 0 ->
 all_enc_ok_pre cfg (stack_to_lab.compile sc dc mh sp (addr_offset cfg) ps).
Proof.
 intros sc dc mh sp cfg ps (HN & HR & Hnames & Hfixed & Haddr & Hdim & Hbyte & Himm & H1a & H1s & H4 & H8 & Hstore & H10 & Hsp2 & Hsp1 & Hsp & Hconf & Hsp0).
 unfold stack_to_lab.compile. apply compile_all_enc_ok_pre. split; [exact Hbyte|].
 apply stack_namesProof.stack_names_stack_asm_ok. split; [|split; assumption].
 apply stack_removeProof.stack_remove_stack_asm_name.
 assert (H7 : reg_name 7 cfg).
 { unfold reg_name in H10 |- *. apply N.ltb_lt in H10; apply N.ltb_lt; lia. }
 destruct (stack_rawcallProof.stack_alloc_stack_asm_convs cfg ps) as [ERn ERr].
 assert (HA : EVERY (fun '(n,p) => stack_asm_name cfg p) (stack_alloc.compile dc (stack_rawcall.compile ps)) /\
  EVERY (fun '(n,p) => stack_asm_remove cfg p) (stack_alloc.compile dc (stack_rawcall.compile ps))).
 { apply stack_allocProof.stack_alloc_stack_asm_convs. rewrite ERn,ERr. repeat (first [assumption|split]). }
 destruct HA as [HAn HAr]. repeat (first [assumption|split]).
Qed.
End EncoderSyntax.

Section CodeLabels.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "complex_get_code_labels_def" *)
Fixpoint complex_get_code_labels (p : prog a) : N * N -> Prop :=
  match p with
  | Seq p1 p2 => complex_get_code_labels p1 UNION complex_get_code_labels p2
  | If _ _ _ p1 p2 => complex_get_code_labels p1 UNION complex_get_code_labels p2
  | Call ret dest handler =>
      (match dest with inl x => (x,0) INSERT {} | _ => {} end) UNION
      (match ret with
       | None => {}
       | Some (r, (_, (l1,l2))) =>
           ((l1,l2) INSERT complex_get_code_labels r) UNION
           (match handler with
            | None => {}
            | Some (r,(l1,l2)) => (l1,l2) INSERT complex_get_code_labels r
            end)
       end)
  | Loop p => complex_get_code_labels p
  | LocValue _ l1 l2 => (l1,l2) INSERT {}
  | RawCall l => (l,1) INSERT {}
  | JumpLower _ _ l => (l,0) INSERT {}
  | _ => {}
  end.

Local Definition emitted_labels (ls : list (line a)) (x : N * N) : Prop :=
 exists y, In y ls /\ x IN line_get_labels y.
Local Definition declared_labels (n : N) (ls : list (line a)) (x : N * N) : Prop :=
 exists k z, In (Label n k z) ls /\ x = (n,k).
Local Lemma emitted_app ls1 ls2 x :
 emitted_labels (ls1 ++ ls2) x <-> emitted_labels ls1 x \/ emitted_labels ls2 x.
Proof. unfold emitted_labels; setoid_rewrite in_app_iff; firstorder. Qed.
Local Lemma declared_app n ls1 ls2 x :
 declared_labels n (ls1 ++ ls2) x <-> declared_labels n ls1 x \/ declared_labels n ls2 x.
Proof. unfold declared_labels; setoid_rewrite in_app_iff; firstorder. Qed.
Local Lemma declared_one n k x : declared_labels n [Label n k 0] x <-> x = (n,k).
Proof. unfold declared_labels; cbn; split. - intros (k1 & z & [E|E] & H); [injection E as <- <-; exact H|contradiction]. - intros H; exists k,0; auto. Qed.
Local Lemma emitted_one lab x : emitted_labels [lab] x <-> x IN line_get_labels lab.
Proof. unfold emitted_labels; cbn; firstorder congruence. Qed.
Local Lemma emitted_nil x : emitted_labels [] x <-> False.
Proof. unfold emitted_labels; cbn; firstorder. Qed.
Local Lemma emitted_cons lab ls x : emitted_labels (lab :: ls) x <-> x IN line_get_labels lab \/ emitted_labels ls x.
Proof. unfold emitted_labels; cbn; firstorder congruence. Qed.
Local Lemma declared_empty n x : declared_labels n [] x <-> False.
Proof. unfold declared_labels; cbn; firstorder. Qed.
Local Lemma declared_LabAsm n op w bytes len ls x :
 declared_labels n (LabAsm op w bytes len :: ls) x <-> declared_labels n ls x.
Proof. unfold declared_labels; cbn; split; intros (k & z & H & E); exists k,z; split; auto; destruct H as [H|H]; [discriminate|exact H]. Qed.
Local Lemma declared_label n k z ls x :
 declared_labels n (Label n k z :: ls) x <-> x = (n,k) \/ declared_labels n ls x.
Proof. unfold declared_labels; cbn; split.
 - intros (k1 & z1 & [E|E] & H); [injection E as <- <-; auto|right; eauto].
 - intros [H|(k1 & z1 & E & H)]; [exists k,z|exists k1,z1]; auto.
Qed.
Local Lemma oEL_in {A} (ls : list A) k y : oEL k ls = Some y -> In y ls.
Proof.
 revert k; induction ls as [|z ls IH]; intros k H; cbn [oEL] in H; [discriminate|].
 destruct (k =? 0); [injection H as <-; left; reflexivity|right; eauto].
Qed.
Local Lemma find_lab_in k ls : find_lab k ls = 0 \/ In (find_lab k ls) ls.
Proof. unfold find_lab; destruct (oEL k ls) eqn:E; [right; eapply oEL_in; eauto|auto]. Qed.
Local Ltac label_norm :=
 cbn [FST fst snd]; rewrite ?append_Append, ?append_List;
 rewrite ?emitted_app, ?declared_app, ?emitted_cons, ?declared_LabAsm, ?declared_label, ?declared_one, ?emitted_nil, ?declared_empty;
 cbn [line_get_labels labs_of complex_get_code_labels compile_jump];
 cbv beta delta [pred_set.IN pred_set.UNION pred_set.INSERT pred_set.EMPTY] in *;
 cbn [andb orb] in *; rewrite ?Bool.andb_false_r in *.
Local Lemma complex_flatten_aux : forall p : prog a,
 forall t n m cs bs x,
 emitted_labels (append (FST (flatten t p n m cs bs))) x ->
 x = (n,0) \/ x = (n, if t && is_Seq p then 1 else 0) \/
 In x (List.map (fun k => (n,k)) (cs ++ bs)) \/
 declared_labels n (append (FST (flatten t p n m cs bs))) x \/
 x IN complex_get_code_labels p.
Proof.
 intros p. induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind;
 intros t n m cs bs x.
 - destruct ret as [[p1 [lr [l1 l2]]]|].
   + destruct h as [[p2 [k1 k2]]|].
     * pose proof (Hr p1 _ eq_refl false n m cs bs x) as E1.
       cbn [flatten]. destruct (flatten false p1 n m cs bs) as [xs [nr1 m1]] eqn:F1.
       pose proof (Hh p2 _ eq_refl false n m1 cs bs x) as E2.
       destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:F2.
       cbn [FST is_Seq] in E1,E2 |- *. destruct dest; label_norm; label_norm; tauto.
     * pose proof (Hr p1 _ eq_refl false n m cs bs x) as E1.
       cbn [flatten]. destruct (flatten false p1 n m cs bs) as [xs [nr1 m1]] eqn:F1.
       cbn [FST is_Seq] in E1 |- *. destruct dest; label_norm; label_norm; tauto.
   + destruct dest; cbn [flatten FST is_Seq]; label_norm; tauto.
 - pose proof (IH1 false n m cs bs x) as E1.
   cbn [flatten]. destruct (flatten false p1 n m cs bs) as [xs [nr1 m1]] eqn:F1.
   pose proof (IH2 false n m1 cs bs x) as E2.
   destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:F2.
   cbn [FST] in E1,E2 |- *. destruct t; label_norm; cbn [is_Seq] in *; tauto.
 - pose proof (IH1 false n m cs bs x) as E1.
   cbn [flatten]. destruct (flatten false p1 n m cs bs) as [xs [nr1 m1]] eqn:F1.
   pose proof (IH2 false n m1 cs bs x) as E2.
   destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:F2.
   cbn [FST] in E1,E2 |- *.
   destruct (is_Skip p1 && is_Skip p2); [label_norm; tauto|].
   destruct (is_Skip p1); [label_norm; label_norm; tauto|].
   destruct (is_Skip p2); [label_norm; label_norm; tauto|].
   destruct nr1; [label_norm; label_norm; tauto|].
   destruct nr2; label_norm; label_norm; tauto.
 - pose proof (IH false n (m+2) (m::cs) ((m+1)::bs) x) as E.
   cbn [flatten]. destruct (flatten false p n (m+2) (m::cs) ((m+1)::bs)) as [xs [nr m1]] eqn:F.
   cbn [FST] in E |- *. label_norm; label_norm.
   cbn [APPEND List.app List.map] in E. rewrite map_app in E; cbn in E; rewrite in_app_iff in E.
   rewrite map_app, in_app_iff. cbn in E. intuition congruence.
 - destruct p; cbn in Hp; try contradiction; cbn [flatten FST is_Seq]; label_norm; try tauto.
   all: try (pose proof (find_lab_in n0 bs) as E; intros H; destruct H as [[->|H]|H]; [|contradiction|contradiction];
      destruct E as [E|E]; [left; congruence|right; right; left; apply in_map; apply in_app_iff; auto]).
   all: try (pose proof (find_lab_in n0 cs) as E; intros H; destruct H as [[->|H]|H]; [|contradiction|contradiction];
      destruct E as [E|E]; [left; congruence|right; right; left; apply in_map; apply in_app_iff; auto]).
Qed.
Local Lemma seq_cond t (p : prog a) :
 (if t && is_Seq p then 1 else 0) =
 (if decide (is_true t /\ exists p1 p2, p = Seq p1 p2) then 1 else 0).
Proof.
 destruct t; destruct p; cbn [andb is_Seq];
 destruct (decide _) as [[Ht [q1 [q2 Hpeq]]]|H]; try discriminate; try reflexivity;
 exfalso; apply H; split; [reflexivity|eauto].
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "complex_flatten_labels" *)
Local Theorem complex_flatten_labels : forall t (p : prog a) n m cs bs,
 let pp := set (append (FST (flatten t p n m cs bs))) in
 BIGUNION (IMAGE line_get_labels pp) SUBSET
 ((n,0) INSERT
  (n,if decide (is_true t /\ exists p1 p2, p = Seq p1 p2) then 1 else 0) INSERT
  set (MAP (fun l => (n,l)) (cs ++ bs))) UNION
 IMAGE (fun n2 => (n,n2)) (BIGUNION (IMAGE line_get_code_labels pp)) UNION
 complex_get_code_labels p.
Proof.
 intros t p n m cs bs; cbn zeta. unfold pred_set.SUBSET; intros x H.
 apply IN_BIGUNION_IMAGE_set in H.
 pose proof (complex_flatten_aux p t n m cs bs x H) as E.
 rewrite seq_cond in E.
 rewrite !IN_UNION, !IN_INSERT, IN_set.
 destruct E as [E|[E|[E|[E|E]]]]; try tauto.
 left; right. destruct E as (k & z & Hl & ->).
 apply IN_IMAGE. exists k; split; [reflexivity|].
 apply IN_BIGUNION_IMAGE_set. exists (Label n k z); split; [exact Hl|].
 cbn [line_get_code_labels]; apply IN_SING; reflexivity.
Qed.
Local Definition valid_labels n (ls : list (line a)) :=
 forall n1 k z, In (Label n1 k z) ls -> n1 = n.
Local Lemma valid_app n xs ys : valid_labels n (xs ++ ys) <-> valid_labels n xs /\ valid_labels n ys.
Proof. unfold valid_labels; setoid_rewrite in_app_iff; firstorder. Qed.
Local Lemma valid_label n n1 k z ls :
 valid_labels n (Label n1 k z :: ls) <-> n1 = n /\ valid_labels n ls.
Proof. unfold valid_labels; cbn; split.
 - intros H; split; [apply (H n1 k z); auto|intros n2 k2 z2 H2; apply (H n2 k2 z2); auto].
 - intros [E H] n2 k2 z2 [H2|H2]; [injection H2 as <- <- <-; exact E|eauto].
Qed.
Local Lemma valid_LabAsm n op w bytes len ls :
 valid_labels n (LabAsm op w bytes len :: ls) <-> valid_labels n ls.
Proof. unfold valid_labels; cbn; split; intros H n1 k z Hl; apply (H n1 k z); auto; destruct Hl; [discriminate|assumption]. Qed.
Local Lemma valid_Asm n op bytes len ls :
 valid_labels n (Asm op bytes len :: ls) <-> valid_labels n ls.
Proof. unfold valid_labels; cbn; split; intros H n1 k z Hl; apply (H n1 k z); auto; destruct Hl; [discriminate|assumption]. Qed.
Local Lemma declared_Asm n op bytes len ls x :
 declared_labels n (Asm op bytes len :: ls) x <-> declared_labels n ls x.
Proof. unfold declared_labels; cbn; split; intros (k & z & H & E); exists k,z; split; auto; destruct H as [H|H]; [discriminate|exact H]. Qed.
Local Lemma valid_nil n : valid_labels n [] <-> True.
Proof. unfold valid_labels; cbn; tauto. Qed.
Local Ltac valid_norm :=
 cbn [FST fst snd] in *; rewrite ?append_Append, ?append_List in *;
 rewrite ?valid_app, ?valid_LabAsm, ?valid_Asm, ?valid_label, ?valid_nil in *;
 rewrite ?declared_Asm;
 cbn [stackProps.get_code_labels] in *.
Local Lemma flatten_labels_aux : forall p : prog a,
 forall t n m cs bs x,
 valid_labels n (append (FST (flatten t p n m cs bs))) ->
 emitted_labels (append (FST (flatten t p n m cs bs))) x ->
 x = (n,0) \/
 In x (List.map (fun k => (n,k)) (cs ++ bs)) \/
 declared_labels n (append (FST (flatten t p n m cs bs))) x \/
 x IN stackProps.get_code_labels p.
Proof.
 intros p. induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind;
 intros t n m cs bs x.
 - destruct ret as [[p1 [lr [l1 l2]]]|].
   + destruct h as [[p2 [k1 k2]]|].
     * pose proof (Hr p1 _ eq_refl false n m cs bs x) as E1.
       cbn [flatten]. destruct (flatten false p1 n m cs bs) as [xs [nr1 m1]] eqn:F1.
       pose proof (Hh p2 _ eq_refl false n m1 cs bs x) as E2.
       destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:F2.
       cbn [FST is_Seq] in E1,E2 |- *. destruct dest; valid_norm; label_norm; valid_norm; label_norm; intros HV HE; decompose [and] HV; subst; valid_norm; label_norm; tauto.
     * pose proof (Hr p1 _ eq_refl false n m cs bs x) as E1.
       cbn [flatten]. destruct (flatten false p1 n m cs bs) as [xs [nr1 m1]] eqn:F1.
       cbn [FST is_Seq] in E1 |- *. destruct dest; valid_norm; label_norm; valid_norm; label_norm; intros HV HE; decompose [and] HV; subst; valid_norm; label_norm; tauto.
   + destruct dest; cbn [flatten FST is_Seq]; valid_norm; label_norm; intros HV HE; decompose [and] HV; subst; valid_norm; label_norm; tauto.
 - pose proof (IH1 false n m cs bs x) as E1.
   cbn [flatten]. destruct (flatten false p1 n m cs bs) as [xs [nr1 m1]] eqn:F1.
   pose proof (IH2 false n m1 cs bs x) as E2.
   destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:F2.
   cbn [FST] in E1,E2 |- *. destruct t; valid_norm; label_norm; cbn [is_Seq] in *; intros HV HE; decompose [and] HV; subst; valid_norm; label_norm; tauto.
 - pose proof (IH1 false n m cs bs x) as E1.
   cbn [flatten]. destruct (flatten false p1 n m cs bs) as [xs [nr1 m1]] eqn:F1.
   pose proof (IH2 false n m1 cs bs x) as E2.
   destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:F2.
   cbn [FST] in E1,E2 |- *.
   destruct (is_Skip p1 && is_Skip p2); [valid_norm; label_norm; tauto|].
   destruct (is_Skip p1); [valid_norm; label_norm; valid_norm; label_norm; tauto|].
   destruct (is_Skip p2); [valid_norm; label_norm; valid_norm; label_norm; tauto|].
   destruct nr1; [valid_norm; label_norm; valid_norm; label_norm; tauto|].
   destruct nr2; valid_norm; label_norm; valid_norm; label_norm; intros HV HE; decompose [and] HV; subst; valid_norm; label_norm; tauto.
 - pose proof (IH false n (m+2) (m::cs) ((m+1)::bs) x) as E.
   cbn [flatten]. destruct (flatten false p n (m+2) (m::cs) ((m+1)::bs)) as [xs [nr m1]] eqn:F.
   cbn [FST] in E |- *. valid_norm; label_norm; label_norm.
   cbn [APPEND List.app List.map] in E. rewrite map_app in E; cbn in E; rewrite in_app_iff in E.
   rewrite map_app, in_app_iff. cbn in E. intuition congruence.
 - destruct p; cbn in Hp; try contradiction; cbn [flatten FST is_Seq]; valid_norm; label_norm; try (intros HV HE; decompose [and] HV; subst; valid_norm; label_norm; tauto).
   all: try (pose proof (find_lab_in n0 bs) as E; intros HV H; destruct H as [[->|H]|H]; [|contradiction|contradiction];
      destruct E as [E|E]; [left; congruence|right; left; apply in_map; apply in_app_iff; auto]).
   all: try (pose proof (find_lab_in n0 cs) as E; intros HV H; destruct H as [[->|H]|H]; [|contradiction|contradiction];
      destruct E as [E|E]; [left; congruence|right; left; apply in_map; apply in_app_iff; auto]).
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_labels" *)
Local Theorem flatten_labels : forall t (m : prog a) n p cs bs l x y,
 flatten t m n p cs bs = (l,(x,y)) /\ EVERY (sec_label_ok n) (append l) ->
 BIGUNION (IMAGE line_get_labels (set (append l))) SUBSET
 set (MAP (fun l => (n,l)) (cs ++ bs)) UNION
 sec_get_code_labels (Section_ n (append l)) UNION stackProps.get_code_labels m.
Proof.
 intros t m n p cs bs l x y [Hf Hv].
 assert (Hvalid : valid_labels n (append l)).
 { apply EVERY_Forall in Hv; rewrite Forall_forall in Hv.
   intros n1 k z Hl. specialize (Hv _ Hl). cbn [sec_label_ok] in Hv.
   apply Bool.andb_true_iff in Hv as [He _]; apply N.eqb_eq in He; exact He. }
 unfold pred_set.SUBSET; intros q Hq. apply IN_BIGUNION_IMAGE_set in Hq.
 pose proof (flatten_labels_aux m t n p cs bs q) as E.
 rewrite Hf in E; cbn [FST] in E. specialize (E Hvalid Hq).
 rewrite !IN_UNION, IN_set. cbn [sec_get_code_labels]. rewrite IN_INSERT.
 destruct E as [->|[E|[E|E]]]; try tauto.
 left; right; right. destruct E as (k & z & Hl & ->).
 apply IN_IMAGE; exists k; split; [reflexivity|].
 apply IN_BIGUNION_IMAGE_set; exists (Label n k z); split; [exact Hl|].
 cbn [line_get_code_labels]; apply IN_SING; reflexivity.
Qed.
Local Lemma sec_code_mono n (ls1 ls2 : list (line a)) :
 (forall y, In y ls1 -> In y ls2) ->
 sec_get_code_labels (Section_ n ls1) SUBSET sec_get_code_labels (Section_ n ls2).
Proof.
 intros H q Hq; cbn [sec_get_code_labels] in *; rewrite IN_INSERT in *.
 destruct Hq as [Hq|Hq]; [auto|right]. apply IN_IMAGE in Hq; destruct Hq as (k & -> & Hq).
 apply IN_IMAGE; exists k; split; [reflexivity|].
 apply IN_BIGUNION_IMAGE_set in Hq; destruct Hq as (y & Hy & Hq).
 apply IN_BIGUNION_IMAGE_set; exists y; auto.
Qed.
Local Lemma section_code_labels n (p : prog a) :
 sec_labels_ok (prog_to_section (n,p)) ->
 sec_get_labels (prog_to_section (n,p)) SUBSET
 sec_get_code_labels (prog_to_section (n,p)) UNION stackProps.get_code_labels p.
Proof.
 unfold prog_to_section. destruct (flatten true p n (stack_alloc.next_lab p 2) [] []) as [ls [nr m]] eqn:F.
 rewrite append_Append, append_List. cbn [sec_labels_ok].
 rewrite stack_allocProof.EVERY_app. intros Hv. apply Bool.andb_true_iff in Hv as [Hv _].
 pose proof (flatten_labels true p n (stack_alloc.next_lab p 2) [] [] ls nr m (conj F Hv)) as E.
 unfold pred_set.SUBSET in *. intros q Hq; rewrite IN_UNION.
 cbn [sec_get_labels] in Hq. apply IN_BIGUNION_IMAGE_set in Hq; destruct Hq as (y & Hy & Hq).
 apply in_app_iff in Hy; destruct Hy as [Hy|Hy].
 - assert (H0 : q IN BIGUNION (IMAGE line_get_labels (set (append ls)))).
   { apply IN_BIGUNION_IMAGE_set; exists y; auto. }
   specialize (E q H0). rewrite !IN_UNION in E; cbn [MAP APPEND LIST_TO_SET] in E.
   destruct E as [[E|E]|E]; [contradiction|left|right; exact E].
   eapply sec_code_mono; [intros y0 H; apply in_app_iff; left; exact H|exact E].
 - cbn in Hy; destruct Hy as [<-|Hy]; [cbn [line_get_labels] in Hq; contradiction|contradiction].
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma" *)
Theorem get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma : forall (p : list (N * prog a)),
 EVERY sec_labels_ok (MAP prog_to_section p) ->
 labProps.get_labels (MAP prog_to_section p) SUBSET
 labProps.get_code_labels (MAP prog_to_section p) UNION
 BIGUNION (IMAGE stackProps.get_code_labels (set (MAP SND p))).
Proof.
 induction p as [|[n p] ps IH]; cbn [MAP EVERY].
 - intros _ q Hq; cbn [labProps.get_labels] in Hq.
   apply IN_BIGUNION_IMAGE_set in Hq; destruct Hq as (y & Hy & _); contradiction.
 - intros Hv; apply Bool.andb_true_iff in Hv as [Hv Hvs]. specialize (IH Hvs).
   pose proof (section_code_labels n p Hv) as E.
   rewrite get_labels_cons, get_code_labels_cons. cbn [MAP SND]. rewrite BIGUNION_IMAGE_cons.
   unfold pred_set.SUBSET in *; intros q Hq; rewrite !IN_UNION in Hq |- *.
   destruct Hq as [Hq|Hq]; [specialize (E q Hq); rewrite IN_UNION in E|specialize (IH q Hq); rewrite IN_UNION in IH]; cbv beta delta [pred_set.IN pred_set.UNION] in *; tauto.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "prog_to_section_preserves_MAP_FST" *)
Local Theorem prog_to_section_preserves_MAP_FST : forall (p : list (N * prog a)),
 IMAGE (fun n => (n,0)) (set (MAP FST p)) SUBSET labProps.get_code_labels (MAP prog_to_section p).
Proof.
 intros ps q Hq. apply IN_IMAGE_set in Hq; destruct Hq as (n & -> & Hn).
 apply in_map_iff in Hn; destruct Hn as ([k p] & E & Hp); cbn [FST] in E; subst k.
 unfold labProps.get_code_labels. apply IN_BIGUNION_IMAGE_set.
 exists (prog_to_section (n,p)); split; [apply in_map; exact Hp|].
 unfold prog_to_section. destruct (flatten true p n (stack_alloc.next_lab p 2) [] []) as [ls [nr m]].
 cbn [sec_get_code_labels]; apply IN_INSERT; left; reflexivity.
Qed.
Local Lemma declared_to_sec n (ls : list (line a)) q :
 declared_labels n ls q -> q IN sec_get_code_labels (Section_ n ls).
Proof.
 intros (k & z & Hl & ->). cbn [sec_get_code_labels]; apply IN_INSERT; right.
 apply IN_IMAGE; exists k; split; [reflexivity|].
 apply IN_BIGUNION_IMAGE_set; exists (Label n k z); split; [exact Hl|].
 cbn [line_get_code_labels]; apply IN_SING; reflexivity.
Qed.
Local Lemma seq_label (p : prog a) n m cs bs : is_Seq p = true ->
 declared_labels n (append (FST (flatten true p n m cs bs))) (n,1).
Proof.
 destruct p; cbn [is_Seq]; try discriminate; intros _.
 cbn [flatten]. destruct (flatten false p1 n m cs bs) as [xs [nr m1]].
 destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]].
 label_norm; tauto.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "prog_to_section_labels" *)
Theorem prog_to_section_labels : forall n (p : prog a) pp,
 prog_to_section (n,p) = pp ->
 sec_get_labels pp SUBSET sec_get_code_labels pp UNION complex_get_code_labels p.
Proof.
 intros n p pp <-. unfold prog_to_section.
 destruct (flatten true p n (stack_alloc.next_lab p 2) [] []) as [ls [nr m]] eqn:F.
 rewrite append_Append, append_List. intros q Hq. rewrite IN_UNION.
 cbn [sec_get_labels] in Hq. apply IN_BIGUNION_IMAGE_set in Hq; destruct Hq as (y & Hy & Hq).
 apply in_app_iff in Hy; destruct Hy as [Hy|Hy].
 - assert (H0 : emitted_labels (append ls) q) by (exists y; auto).
   pose proof (complex_flatten_aux p true n (stack_alloc.next_lab p 2) [] [] q) as E.
   rewrite F in E; cbn [FST] in E. specialize (E H0).
   cbn [andb APPEND List.map] in E.
   destruct E as [->|[E|[E|[E|E]]]]; [left; cbn [sec_get_code_labels]; apply IN_INSERT; auto| |contradiction| |auto].
   + left. destruct (is_Seq p) eqn:S; cbn in E; subst q.
     * apply declared_to_sec. apply declared_app; left.
       pose proof (seq_label p n (stack_alloc.next_lab p 2) [] [] S) as Hs; rewrite F in Hs; exact Hs.
     * cbn [sec_get_code_labels]; apply IN_INSERT; auto.
   + left; apply declared_to_sec; apply declared_app; auto.
 - cbn in Hy; destruct Hy as [<-|Hy]; [cbn [line_get_labels] in Hq; contradiction|contradiction].
Qed.
Local Ltac handler_norm := cbn [stack_get_handler_labels] in *; rewrite ?declared_Asm; label_norm; label_norm.
Local Lemma skip_handler n (p : prog a) : is_Skip p = true -> stack_get_handler_labels n p = {}.
Proof. destruct p; cbn [is_Skip]; intros H; try discriminate; reflexivity. Qed.
Local Lemma handler_flatten_aux : forall p : prog a,
 forall t n m cs bs q,
 q IN stack_get_handler_labels n p ->
 q = (n,0) \/ declared_labels n (append (FST (flatten t p n m cs bs))) q.
Proof.
 intros p. induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind;
 intros t n m cs bs q.
 - destruct ret as [[p1 [lr [l1 l2]]]|].
   + destruct h as [[p2 [k1 k2]]|].
     * pose proof (Hr p1 _ eq_refl false n m cs bs q) as E1.
       cbn [flatten]. destruct (flatten false p1 n m cs bs) as [xs [nr1 m1]] eqn:F1.
       pose proof (Hh p2 _ eq_refl false n m1 cs bs q) as E2.
       destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:F2.
       cbn [FST stack_get_handler_labels] in E1,E2 |- *. destruct (decide (k1 = n)) as [->|Hk]; destruct dest; handler_norm; tauto.
     * pose proof (Hr p1 _ eq_refl false n m cs bs q) as E1.
       cbn [flatten]. destruct (flatten false p1 n m cs bs) as [xs [nr1 m1]] eqn:F1.
       cbn [FST is_Seq] in E1 |- *. destruct dest; handler_norm; tauto.
   + destruct dest; cbn [flatten FST is_Seq]; handler_norm; tauto.
 - pose proof (IH1 false n m cs bs q) as E1.
   cbn [flatten]. destruct (flatten false p1 n m cs bs) as [xs [nr1 m1]] eqn:F1.
   pose proof (IH2 false n m1 cs bs q) as E2.
   destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:F2.
   cbn [FST] in E1,E2 |- *. destruct t; handler_norm; cbn [is_Seq] in *; tauto.
 - pose proof (IH1 false n m cs bs q) as E1.
   cbn [flatten]. destruct (flatten false p1 n m cs bs) as [xs [nr1 m1]] eqn:F1.
   pose proof (IH2 false n m1 cs bs q) as E2.
   destruct (flatten false p2 n m1 cs bs) as [ys [nr2 m2]] eqn:F2.
   cbn [FST] in E1,E2 |- *.
   destruct (is_Skip p1) eqn:S1, (is_Skip p2) eqn:S2; cbn [andb stack_get_handler_labels] in *;
   try rewrite (skip_handler n p1 S1) in *;
   try rewrite (skip_handler n p2 S2) in *;
   destruct nr1,nr2; handler_norm; tauto.
 - pose proof (IH false n (m+2) (m::cs) ((m+1)::bs) q) as E.
   cbn [flatten]. destruct (flatten false p n (m+2) (m::cs) ((m+1)::bs)) as [xs [nr m1]] eqn:F.
   cbn [FST] in E |- *. handler_norm; tauto.
 - destruct p; cbn in Hp; try contradiction; cbn [flatten FST]; handler_norm; tauto.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_preserves_handler_labels" *)
Theorem flatten_preserves_handler_labels : forall t (m : prog a) n p cs bs l x y,
 flatten t m n p cs bs = (l,(x,y)) ->
 stack_get_handler_labels n m SUBSET sec_get_code_labels (Section_ n (append l)).
Proof.
 intros t m n p cs bs l x y Hf q Hq.
 pose proof (handler_flatten_aux m t n p cs bs q Hq) as E.
 rewrite Hf in E; cbn [FST] in E.
 destruct E as [->|E]; [cbn [sec_get_code_labels]; apply IN_INSERT; auto|apply declared_to_sec; exact E].
Qed.
Local Lemma section_handler_labels n (p : prog a) :
 stack_get_handler_labels n p SUBSET sec_get_code_labels (prog_to_section (n,p)).
Proof.
 unfold prog_to_section. destruct (flatten true p n (stack_alloc.next_lab p 2) [] []) as [ls [nr m]] eqn:F.
 rewrite append_Append, append_List. intros q Hq.
 pose proof (flatten_preserves_handler_labels true p n (stack_alloc.next_lab p 2) [] [] ls nr m F q Hq) as H.
 eapply sec_code_mono; [intros y Hy; apply in_app_iff; left; exact Hy|exact H].
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "MAP_prog_to_section_preserves_handler_labels" *)
Theorem MAP_prog_to_section_preserves_handler_labels : forall (p : list (N * prog a)),
 BIGUNION (set (MAP (fun '(n,pp) => stack_get_handler_labels n pp) p)) SUBSET
 labProps.get_code_labels (MAP prog_to_section p).
Proof.
 intros ps q Hq. apply IN_BIGUNION in Hq; destruct Hq as (s & Hq & Hs).
 apply IN_set in Hs; apply in_map_iff in Hs; destruct Hs as ([n p] & <- & Hp).
 unfold labProps.get_code_labels. apply IN_BIGUNION_IMAGE_set.
 exists (prog_to_section (n,p)); split; [apply in_map; exact Hp|].
 apply section_handler_labels; exact Hq.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "one_prog_section" *)
Theorem one_prog_section : forall (p : list (N * prog a)),
 IMAGE (fun n => (n,1)) (set (MAP FST p)) SUBSET labProps.get_code_labels (MAP prog_to_section p).
Proof.
 intros ps q Hq. apply IN_IMAGE_set in Hq; destruct Hq as (n & -> & Hn).
 apply in_map_iff in Hn; destruct Hn as ([k p] & E & Hp); cbn [FST] in E; subst k.
 unfold labProps.get_code_labels. apply IN_BIGUNION_IMAGE_set.
 exists (prog_to_section (n,p)); split; [apply in_map; exact Hp|].
 unfold prog_to_section. destruct (flatten true p n (stack_alloc.next_lab p 2) [] []) as [ls [nr m]] eqn:F.
 rewrite append_Append, append_List. apply declared_to_sec; apply declared_app.
 destruct (is_Seq p) eqn:S.
 - left. pose proof (seq_label p n (stack_alloc.next_lab p 2) [] [] S) as H; rewrite F in H; exact H.
 - right. apply declared_one; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "get_labels_MAP_prog_to_section_SUBSET_code_labels" *)
Theorem get_labels_MAP_prog_to_section_SUBSET_code_labels : forall (p : list (N * prog a)) elabs,
 EVERY sec_labels_ok (MAP prog_to_section p) /\ stack_good_code_labels p elabs ->
 labProps.get_labels (MAP prog_to_section p) SUBSET
 labProps.get_code_labels (MAP prog_to_section p) UNION
 IMAGE (fun n => (n,0)) elabs UNION IMAGE (fun n => (n,1)) elabs.
Proof.
 intros ps elabs [Hv Hg] q Hq.
 pose proof (get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma ps Hv q Hq) as E.
 apply IN_UNION in E; destruct E as [E|E].
 - cbv beta delta [pred_set.IN pred_set.UNION]; tauto.
 - unfold stack_good_code_labels in Hg. specialize (Hg q E).
   cbv beta delta [pred_set.IN pred_set.UNION] in Hg |- *.
   pose proof (MAP_prog_to_section_preserves_handler_labels ps q) as Hh.
   pose proof (prog_to_section_preserves_MAP_FST ps q) as H0.
   pose proof (one_prog_section ps q) as H1.
   cbv beta delta [pred_set.IN pred_set.UNION pred_set.SUBSET] in Hh,H0,H1.
   tauto.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "get_code_labels_comp" 4090 *)
Local Theorem get_code_labels_comp : forall f (p : prog a),
 complex_get_code_labels (stack_names.comp f p) = complex_get_code_labels p.
Proof.
 intros f p. induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind.
 - destruct ret as [[p1 [lr [l1 l2]]]|].
   + specialize (Hr p1 _ eq_refl). destruct h as [[p2 [k1 k2]]|].
     * specialize (Hh p2 _ eq_refl). destruct dest; cbn [stack_names.comp stack_names.dest_find_name complex_get_code_labels]; rewrite Hr,Hh; reflexivity.
     * destruct dest; cbn [stack_names.comp stack_names.dest_find_name complex_get_code_labels]; rewrite Hr; reflexivity.
   + destruct dest; cbn [stack_names.comp stack_names.dest_find_name complex_get_code_labels]; reflexivity.
 - cbn [stack_names.comp complex_get_code_labels]; rewrite IH1,IH2; reflexivity.
 - cbn [stack_names.comp complex_get_code_labels]; rewrite IH1,IH2; reflexivity.
 - cbn [stack_names.comp complex_get_code_labels]; exact IH.
 - destruct p; cbn in Hp; try contradiction; cbn [stack_names.comp complex_get_code_labels]; try reflexivity.
   destruct a0; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_names_get_code_labels" *)
Theorem stack_names_get_code_labels : forall {K : Type} f (prog0 : list (K * prog a)),
 LIST_REL (fun cp p => complex_get_code_labels cp = complex_get_code_labels p)
 (MAP SND (stack_names.compile f prog0)) (MAP SND prog0).
Proof.
 intros K f ps; unfold stack_names.compile; induction ps as [|[n p] ps IH]; cbn [MAP SND stack_names.prog_comp].
 - constructor.
 - constructor; [apply get_code_labels_comp|exact IH].
Qed.
Local Ltac remove_label_norm :=
 cbn [stackProps.get_code_labels stack_remove.single_stack_alloc stack_remove.single_stack_free
 stack_remove.halt_inst stackLang.list_Seq] in *;
 rewrite ?stack_removeProof.EMPTY_UNION_EMPTY in *.
Local Lemma remove_alloc_labels : forall fuel jump k n,
 stackProps.get_code_labels (@stack_remove.stack_alloc_f a fuel jump k n) SUBSET
 (stack_remove.stack_err_lab,0) INSERT {}.
Proof.
 induction fuel as [|fuel IH]; intros jump k n; cbn [stack_remove.stack_alloc_f];
 unfold pred_set.SUBSET in *; intros q Hq.
 - cbn [stackProps.get_code_labels] in Hq; contradiction.
 - destruct (n =? 0); [cbn [stackProps.get_code_labels] in Hq; contradiction|]. destruct (n <=? stack_remove.max_stack_alloc);
   destruct jump; remove_label_norm;
   cbv beta delta [pred_set.IN pred_set.UNION pred_set.INSERT pred_set.EMPTY] in *;
   try tauto; first [specialize (IH true k (n-stack_remove.max_stack_alloc) q); tauto|specialize (IH false k (n-stack_remove.max_stack_alloc) q); tauto].
Qed.
Local Lemma remove_free_labels : forall fuel k n,
 stackProps.get_code_labels (@stack_remove.stack_free_f a fuel k n) = {}.
Proof.
 induction fuel as [|fuel IH]; intros k n; cbn [stack_remove.stack_free_f]; [reflexivity|].
 destruct (n =? 0); [reflexivity|]. destruct (n <=? stack_remove.max_stack_alloc); remove_label_norm;
 rewrite ?IH, ?stack_removeProof.EMPTY_UNION_EMPTY; reflexivity.
Qed.
Local Lemma remove_upshift_labels : forall fuel r n,
 stackProps.get_code_labels (@stack_remove.upshift_f a fuel r n) = {}.
Proof.
 induction fuel as [|fuel IH]; intros r n; cbn [stack_remove.upshift_f]; [reflexivity|].
 destruct (n <=? stack_remove.max_stack_alloc); remove_label_norm;
 rewrite ?IH, ?stack_removeProof.EMPTY_UNION_EMPTY; reflexivity.
Qed.
Local Lemma remove_downshift_labels : forall fuel r n,
 stackProps.get_code_labels (@stack_remove.downshift_f a fuel r n) = {}.
Proof.
 induction fuel as [|fuel IH]; intros r n; cbn [stack_remove.downshift_f]; [reflexivity|].
 destruct (n <=? stack_remove.max_stack_alloc); remove_label_norm;
 rewrite ?IH, ?stack_removeProof.EMPTY_UNION_EMPTY; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "get_code_labels_comp" 4110 *)
(** HOL rebinds [get_code_labels_comp]; the suffix distinguishes its second use. *)
Local Theorem get_code_labels_comp_remove : forall jump off k (p : prog a),
 stackProps.get_code_labels (stack_remove.comp jump off k p) SUBSET
 (stack_remove.stack_err_lab,0) INSERT stackProps.get_code_labels p.
Proof.
 intros jump off k p. induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind;
 unfold pred_set.SUBSET in *; intros q.
 - destruct ret as [[p1 [lr [l1 l2]]]|]; destruct h as [[p2 [k1 k2]]|]; destruct dest;
   cbn [stack_remove.comp stackProps.get_code_labels];
   cbv beta delta [pred_set.IN pred_set.UNION pred_set.INSERT pred_set.EMPTY];
   try specialize (Hr p1 _ eq_refl q); try specialize (Hh p2 _ eq_refl q);
   cbv beta delta [pred_set.IN pred_set.UNION pred_set.INSERT pred_set.EMPTY] in Hr,Hh; tauto.
 - cbn [stack_remove.comp stackProps.get_code_labels];
   specialize (IH1 q); specialize (IH2 q);
   cbv beta delta [pred_set.IN pred_set.UNION pred_set.INSERT] in *; tauto.
 - cbn [stack_remove.comp stackProps.get_code_labels];
   specialize (IH1 q); specialize (IH2 q);
   cbv beta delta [pred_set.IN pred_set.UNION pred_set.INSERT] in *; tauto.
 - cbn [stack_remove.comp stackProps.get_code_labels];
   specialize (IH q); cbv beta delta [pred_set.IN pred_set.INSERT] in *; tauto.
 - destruct p; cbn in Hp; try contradiction; cbn [stack_remove.comp];
   remove_label_norm; cbv beta delta [pred_set.IN pred_set.UNION pred_set.INSERT pred_set.EMPTY] in *; try tauto.
   + destruct (decide (s = CurrHeap)); remove_label_norm; cbv beta delta [pred_set.IN pred_set.EMPTY]; tauto.
   + destruct (decide (s = CurrHeap)); remove_label_norm; cbv beta delta [pred_set.IN pred_set.EMPTY]; tauto.
   + unfold stack_remove.copy_loop, stack_remove.copy_each; remove_label_norm;
     cbv beta delta [pred_set.IN pred_set.UNION pred_set.EMPTY]; tauto.
   + unfold stack_remove.stack_alloc. pose proof (remove_alloc_labels (Datatypes.S (N.to_nat n)) jump k n q) as E.
     cbv beta delta [pred_set.IN pred_set.INSERT pred_set.EMPTY] in E; exact E.
   + unfold stack_remove.stack_free; rewrite remove_free_labels.
     cbv beta delta [pred_set.IN pred_set.EMPTY]; tauto.
   + destruct (offset_ok 0 off (stack_remove.word_offset n0)); remove_label_norm;
     [cbv beta delta [pred_set.IN pred_set.EMPTY]; tauto|].
     unfold stack_remove.stack_store, stack_remove.upshift, stack_remove.downshift.
     remove_label_norm; rewrite remove_upshift_labels, remove_downshift_labels.
     cbv beta delta [pred_set.IN pred_set.UNION pred_set.EMPTY]; tauto.
   + destruct (offset_ok 0 off (stack_remove.word_offset n0)); remove_label_norm;
     [cbv beta delta [pred_set.IN pred_set.EMPTY]; tauto|].
     unfold stack_remove.stack_load, stack_remove.upshift.
     remove_label_norm; rewrite remove_upshift_labels.
     cbv beta delta [pred_set.IN pred_set.UNION pred_set.EMPTY]; tauto.
Qed.
Local Lemma store_list_code_code_labels ad t (ls : list (word a + N)) :
 stackProps.get_code_labels (stack_remove.store_list_code ad t ls) = {}.
Proof.
 induction ls as [|[w|r] ls IH]; cbn [stack_remove.store_list_code stackProps.get_code_labels stackLang.list_Seq];
 rewrite ?IH; apply EXTENSION; intros q; cbv beta delta [pred_set.IN pred_set.UNION pred_set.EMPTY]; tauto.
Qed.
Local Opaque stack_remove.store_list_code.
Local Lemma init_code_code_labels ggc mh k :
 stackProps.get_code_labels (@stack_remove.init_code a ggc mh k) = (1,0) INSERT {}.
Proof.
 unfold stack_remove.init_code; cbv zeta; remove_label_norm; unfold stack_remove.init_memory; remove_label_norm.
 rewrite store_list_code_code_labels; apply EXTENSION; intros q;
 cbv beta delta [pred_set.IN pred_set.UNION pred_set.INSERT pred_set.EMPTY]; tauto.
Qed.
Local Opaque stack_remove.init_code.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "init_stubs_labels" *)
Local Theorem init_stubs_labels : forall ggc mh k start,
 EVERY (fun p => bool_decide (stackProps.get_code_labels p SUBSET set [(1,0);(start,0)]))
 (MAP SND (@stack_remove.init_stubs a ggc mh k start)).
Proof.
 intros ggc mh k start; apply EVERY_Forall; unfold stack_remove.init_stubs; cbn [MAP SND].
 rewrite Forall_forall; intros p Hp; cbn in Hp; destruct Hp as [<-|[<-|[<-|Hp]]]; [| | |contradiction].
 all: apply bool_decide_spec; intros q Hq;
 remove_label_norm; rewrite ?init_code_code_labels in Hq;
 cbv beta delta [pred_set.IN pred_set.UNION pred_set.INSERT pred_set.EMPTY] in Hq;
 rewrite IN_set; cbn; intuition congruence.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_names_get_code_labels_comp" *)
Local Theorem stack_names_get_code_labels_comp : forall f (p : prog a),
 stackProps.get_code_labels (stack_names.comp f p) = stackProps.get_code_labels p.
Proof.
 intros f p. induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind.
 - destruct ret as [[p1 [lr [l1 l2]]]|].
   + specialize (Hr p1 _ eq_refl). destruct h as [[p2 [k1 k2]]|].
     * specialize (Hh p2 _ eq_refl). destruct dest; cbn [stack_names.comp stack_names.dest_find_name stackProps.get_code_labels]; rewrite Hr,Hh; reflexivity.
     * destruct dest; cbn [stack_names.comp stack_names.dest_find_name stackProps.get_code_labels]; rewrite Hr; reflexivity.
   + destruct h as [[p2 [k1 k2]]|].
     * specialize (Hh p2 _ eq_refl). destruct dest; cbn [stack_names.comp stack_names.dest_find_name stackProps.get_code_labels]; rewrite Hh; reflexivity.
     * destruct dest; cbn [stack_names.comp stack_names.dest_find_name stackProps.get_code_labels]; reflexivity.
 - cbn [stack_names.comp stackProps.get_code_labels]; rewrite IH1,IH2; reflexivity.
 - cbn [stack_names.comp stackProps.get_code_labels]; rewrite IH1,IH2; reflexivity.
 - cbn [stack_names.comp stackProps.get_code_labels]; exact IH.
 - destruct p; cbn in Hp; try contradiction; cbn [stack_names.comp stackProps.get_code_labels]; try reflexivity.
   destruct a0; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_names_stack_get_handler_labels_comp" *)
Local Theorem stack_names_stack_get_handler_labels_comp : forall f (p : prog a) n,
 stack_get_handler_labels n (stack_names.comp f p) = stack_get_handler_labels n p.
Proof.
 intros f p. induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind; intros n.
 - destruct ret as [[p1 [lr [l1 l2]]]|].
   + specialize (Hr p1 _ eq_refl n). destruct h as [[p2 [k1 k2]]|].
     * specialize (Hh p2 _ eq_refl n). cbn [stack_names.comp stack_get_handler_labels]; rewrite Hr,Hh; reflexivity.
     * cbn [stack_names.comp stack_get_handler_labels]; rewrite Hr; reflexivity.
   + cbn [stack_names.comp stack_get_handler_labels]; reflexivity.
 - cbn [stack_names.comp stack_get_handler_labels]; rewrite IH1,IH2; reflexivity.
 - cbn [stack_names.comp stack_get_handler_labels]; rewrite IH1,IH2; reflexivity.
 - cbn [stack_names.comp stack_get_handler_labels]; apply IH.
 - destruct p; cbn in Hp; try contradiction; cbn [stack_names.comp stack_get_handler_labels]; try reflexivity.
   destruct a0; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "UNCURRY_PAIR_ETA" *)
Local Theorem UNCURRY_PAIR_ETA {A B C} (f : A -> B -> C) :
 UNCURRY f = fun '(p1,p2) => f p1 p2.
Proof. apply functional_extensionality; intros []; reflexivity. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_names_stack_good_code_labels" *)
Theorem stack_names_stack_good_code_labels : forall (prog0 : list (N * prog a)) f elabs,
 stack_good_code_labels prog0 elabs -> stack_good_code_labels (stack_names.compile f prog0) elabs.
Proof.
 intros ps f elabs H. unfold stack_good_code_labels, stack_names.compile in *.
 rewrite !LIST_TO_SET_MAP, !IMAGE_IMAGE in *.
 cbn.
 assert (Eg : (fun x : N * prog a => stackProps.get_code_labels (SND (stack_names.prog_comp f x))) =
              (fun x => stackProps.get_code_labels (SND x))).
 { apply functional_extensionality; intros [n p]; cbn [stack_names.prog_comp SND]; apply stack_names_get_code_labels_comp. }
 assert (Eh : (fun x : N * prog a => let '(n,p) := stack_names.prog_comp f x in stack_get_handler_labels n p) =
              (fun x => let '(n,p) := x in stack_get_handler_labels n p)).
 { apply functional_extensionality; intros [n p]; cbn [stack_names.prog_comp]; apply stack_names_stack_get_handler_labels_comp. }
 assert (En : forall k : N, (fun x : N * prog a => (FST (stack_names.prog_comp f x),k)) = (fun x => (FST x,k))).
 { intros k; apply functional_extensionality; intros [n p]; reflexivity. }
 rewrite Eg,Eh,En,En. exact H.
Qed.
Local Lemma handler_labels_subset n : forall p : prog a,
 stack_get_handler_labels n p SUBSET stackSem.get_labels p.
Proof.
 intros p; induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind;
 unfold pred_set.SUBSET in *; intros q.
 - destruct ret as [[p1 [lr [l1 l2]]]|].
   + specialize (Hr p1 _ eq_refl q). destruct h as [[p2 [k1 k2]]|].
     * specialize (Hh p2 _ eq_refl q). cbn [stack_get_handler_labels stackSem.get_labels].
       destruct (decide (k1=n)); cbv beta delta [pred_set.IN pred_set.UNION pred_set.INSERT pred_set.EMPTY] in *; tauto.
     * cbn [stack_get_handler_labels stackSem.get_labels]; cbv beta delta [pred_set.IN pred_set.UNION pred_set.INSERT pred_set.EMPTY] in *; tauto.
   + cbn [stack_get_handler_labels stackSem.get_labels]; cbv beta delta [pred_set.IN pred_set.EMPTY]; tauto.
 - cbn [stack_get_handler_labels stackSem.get_labels]; specialize (IH1 q); specialize (IH2 q);
   cbv beta delta [pred_set.IN pred_set.UNION] in *; tauto.
 - cbn [stack_get_handler_labels stackSem.get_labels]; specialize (IH1 q); specialize (IH2 q);
   cbv beta delta [pred_set.IN pred_set.UNION] in *; tauto.
 - cbn [stack_get_handler_labels stackSem.get_labels]; apply IH.
 - destruct p; cbn in Hp; try contradiction; cbn [stack_get_handler_labels stackSem.get_labels]; cbv beta delta [pred_set.IN pred_set.EMPTY]; tauto.
Qed.
Local Lemma handler_labels_empty n (p : prog a) : stackSem.get_labels p = {} -> stack_get_handler_labels n p = {}.
Proof.
 intros H; apply EXTENSION; intros q; split; [intros Hq|intros Hq; exfalso; exact Hq].
 apply (handler_labels_subset n p) in Hq; rewrite H in Hq; exact Hq.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_remove_get_code_labels_comp" *)
Local Theorem stack_remove_get_code_labels_comp : forall jump off k (p : prog a),
 stackProps.get_code_labels (stack_remove.comp jump off k p) SUBSET
 (stack_remove.stack_err_lab,0) INSERT stackProps.get_code_labels p.
Proof. apply get_code_labels_comp_remove. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_remove_stack_get_handler_labels_comp" *)
Local Theorem stack_remove_stack_get_handler_labels_comp : forall jump off k (p : prog a) m,
 stack_get_handler_labels m (stack_remove.comp jump off k p) = stack_get_handler_labels m p.
Proof.
 intros jump off k p; induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind; intros m.
 - destruct ret as [[p1 [lr [l1 l2]]]|]; [|reflexivity].
   specialize (Hr p1 _ eq_refl m). destruct h as [[p2 [k1 k2]]|]; cbn [stack_remove.comp stack_get_handler_labels]; rewrite Hr;
   [rewrite (Hh p2 _ eq_refl m)|]; reflexivity.
 - cbn [stack_remove.comp stack_get_handler_labels]; rewrite IH1,IH2; reflexivity.
 - cbn [stack_remove.comp stack_get_handler_labels]; rewrite IH1,IH2; reflexivity.
 - cbn [stack_remove.comp stack_get_handler_labels]; apply IH.
 - destruct p; cbn in Hp; try contradiction; cbn [stack_get_handler_labels]; apply handler_labels_empty;
   rewrite stack_removeProof.get_labels_comp; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_remove_init_code_labels" *)
Local Theorem stack_remove_init_code_labels : forall x ggc mh sp,
 x IN stackProps.get_code_labels (@stack_remove.init_code a ggc mh sp) -> x = (1,0).
Proof. intros x ggc mh sp H; rewrite init_code_code_labels in H; apply IN_SING in H; exact H. Qed.
Local Definition code_label_context (ps : list (N * prog a)) elabs : N * N -> Prop :=
 BIGUNION (set (MAP (fun '(n,p) => stack_get_handler_labels n p) ps)) UNION
 IMAGE (fun n => (n,0)) (set (MAP FST ps)) UNION IMAGE (fun n => (n,0)) elabs UNION
 IMAGE (fun n => (n,1)) (set (MAP FST ps)) UNION IMAGE (fun n => (n,1)) elabs.
Local Lemma good_code_labels_pointwise ps elabs : stack_good_code_labels ps elabs <->
 forall n p q, In (n,p) ps -> q IN stackProps.get_code_labels p -> code_label_context ps elabs q.
Proof.
 unfold stack_good_code_labels, pred_set.SUBSET; split.
 - intros H n p q Hp Hq; apply H. apply IN_BIGUNION_IMAGE_set.
   exists p; split; [apply in_map_iff; exists (n,p); split; [reflexivity|exact Hp]|exact Hq].
 - intros H q Hq; apply IN_BIGUNION_IMAGE_set in Hq; destruct Hq as (p & Hp & Hq).
   apply in_map_iff in Hp; destruct Hp as ([n p1] & E & Hp); cbn [SND] in E; subst p1.
   apply (H n p q Hp Hq).
Qed.
Local Lemma context_handler ps elabs n p q : In (n,p) ps -> stack_get_handler_labels n p q -> code_label_context ps elabs q.
Proof.
 intros Hp Hq; unfold code_label_context; cbv beta delta [pred_set.IN pred_set.UNION]; left; left; left; left.
 apply IN_BIGUNION; exists (stack_get_handler_labels n p); split; [exact Hq|].
 apply IN_set; apply in_map_iff; exists (n,p); split; [reflexivity|exact Hp].
Qed.
Local Lemma context_entry0 ps elabs n p : In (n,p) ps -> code_label_context ps elabs (n,0).
Proof.
 intros Hp; unfold code_label_context; cbv beta delta [pred_set.IN pred_set.UNION]; left; left; left; right.
 apply IN_IMAGE; exists n; split; [reflexivity|].
 apply IN_set; apply in_map_iff; exists (n,p); split; [reflexivity|exact Hp].
Qed.
Local Lemma context_entry1 ps elabs n p : In (n,p) ps -> code_label_context ps elabs (n,1).
Proof.
 intros Hp; unfold code_label_context; cbv beta delta [pred_set.IN pred_set.UNION]; left; right.
 apply IN_IMAGE; exists n; split; [reflexivity|].
 apply IN_set; apply in_map_iff; exists (n,p); split; [reflexivity|exact Hp].
Qed.
Local Lemma context_external0 ps elabs n : n IN elabs -> code_label_context ps elabs (n,0).
Proof.
 intros H; unfold code_label_context; cbv beta delta [pred_set.IN pred_set.UNION]; left; left; right.
 apply IN_IMAGE; exists n; auto.
Qed.
Local Lemma context_transport ps qs elabs (f : N * prog a -> N * prog a) :
 (forall n p, In (n,p) ps -> In (f (n,p)) qs) ->
 (forall n p, FST (f (n,p)) = n) ->
 (forall n p, stack_get_handler_labels n (SND (f (n,p))) = stack_get_handler_labels n p) ->
 forall q, code_label_context ps elabs q -> code_label_context qs elabs q.
Proof.
 intros Hi Hn Hh q Hq; unfold code_label_context in Hq; cbv beta delta [pred_set.IN pred_set.UNION] in Hq.
 destruct Hq as [[[[Hq|Hq]|Hq]|Hq]|Hq].
 - apply IN_BIGUNION in Hq; destruct Hq as (s & Hq & Hs).
   apply IN_set in Hs; apply in_map_iff in Hs; destruct Hs as ([n p] & <- & Hp).
   pose proof (Hi n p Hp) as Hfp. destruct (f (n,p)) as [n1 p1] eqn:F.
   specialize (Hn n p); rewrite F in Hn; cbn [FST] in Hn; subst n1.
   specialize (Hh n p); rewrite F in Hh; cbn [SND] in Hh; rewrite <- Hh in Hq.
   eapply context_handler; eauto.
 - apply IN_IMAGE_set in Hq; destruct Hq as (n & -> & Hp).
   apply in_map_iff in Hp; destruct Hp as ([n1 p] & E & Hp); cbn [FST] in E; subst n1.
   pose proof (Hi n p Hp) as Hfp. destruct (f (n,p)) as [n1 p1] eqn:F.
   specialize (Hn n p); rewrite F in Hn; cbn [FST] in Hn; subst n1.
   eapply context_entry0; exact Hfp.
 - unfold code_label_context; cbv beta delta [pred_set.IN pred_set.UNION]; tauto.
 - apply IN_IMAGE_set in Hq; destruct Hq as (n & -> & Hp).
   apply in_map_iff in Hp; destruct Hp as ([n1 p] & E & Hp); cbn [FST] in E; subst n1.
   pose proof (Hi n p Hp) as Hfp. destruct (f (n,p)) as [n1 p1] eqn:F.
   specialize (Hn n p); rewrite F in Hn; cbn [FST] in Hn; subst n1.
   eapply context_entry1; exact Hfp.
 - unfold code_label_context; cbv beta delta [pred_set.IN pred_set.UNION]; tauto.
Qed.
Local Lemma transformed_code_labels ps qs elabs (f : N * prog a -> N * prog a) err :
 stack_good_code_labels ps elabs ->
 (forall n p, In (n,p) ps -> In (f (n,p)) qs) ->
 (forall n p, FST (f (n,p)) = n) ->
 (forall n p, stack_get_handler_labels n (SND (f (n,p))) = stack_get_handler_labels n p) ->
 (forall n p, stackProps.get_code_labels (SND (f (n,p))) SUBSET (err,0) INSERT stackProps.get_code_labels p) ->
 code_label_context qs elabs (err,0) ->
 forall n p q, In (n,p) (MAP f ps) -> q IN stackProps.get_code_labels p -> code_label_context qs elabs q.
Proof.
 intros Hg Hi Hn Hh Hcode Herr n p q Hp Hq.
 apply in_map_iff in Hp; destruct Hp as ([n0 p0] & E & Hp).
 assert (He : q IN stackProps.get_code_labels (SND (f (n0,p0)))).
 { rewrite E; exact Hq. }
 apply (Hcode n0 p0) in He; apply IN_INSERT in He; destruct He as [->|He]; [exact Herr|].
 eapply context_transport; [exact Hi|exact Hn|exact Hh|].
 exact (proj1 (good_code_labels_pointwise ps elabs) Hg n0 p0 q Hp He).
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_remove_stack_good_code_labels" *)
Theorem stack_remove_stack_good_code_labels : forall (prog0 : list (N * prog a)) loc elabs jump off ggc mh sp,
 MEM loc (MAP FST prog0) /\ stack_good_code_labels prog0 elabs ->
 stack_good_code_labels (stack_remove.compile jump off ggc mh sp loc prog0) elabs.
Proof.
 intros ps loc elabs jump off ggc mh sp [Hloc Hg].
 apply MEM_In, in_map_iff in Hloc; destruct Hloc as ([n p] & E & Hp); cbn [FST] in E; subst n.
 unfold stack_remove.compile. apply good_code_labels_pointwise.
 assert (Ht : forall n p q, In (n,p) (MAP (stack_remove.prog_comp jump off sp) ps) ->
   q IN stackProps.get_code_labels p ->
   code_label_context (stack_remove.init_stubs ggc mh sp loc ++ MAP (stack_remove.prog_comp jump off sp) ps) elabs q).
 { eapply transformed_code_labels; [exact Hg| | | | |].
   - intros n p0 Hin; apply in_app_iff; right; apply in_map; exact Hin.
   - intros n p0; reflexivity.
   - intros n p0; cbn [stack_remove.prog_comp SND]; apply stack_remove_stack_get_handler_labels_comp.
   - intros n p0; cbn [stack_remove.prog_comp SND]; apply stack_remove_get_code_labels_comp.
   - unfold stack_remove.stack_err_lab. eapply context_entry0.
     apply in_app_iff; left; unfold stack_remove.init_stubs; cbn; right; right; left; reflexivity. }
 intros n p0 q Hin Hq; apply in_app_iff in Hin; destruct Hin as [Hin|Hin]; [|eapply Ht; eauto].
 pose proof (init_stubs_labels ggc mh sp loc) as Hv; apply EVERY_Forall in Hv; rewrite Forall_forall in Hv.
 assert (Hi : In p0 (MAP SND (stack_remove.init_stubs ggc mh sp loc))).
 { apply in_map_iff; exists (n,p0); split; [reflexivity|exact Hin]. }
 specialize (Hv _ Hi); apply bool_decide_spec in Hv. specialize (Hv q Hq).
 apply IN_set in Hv; cbn in Hv; destruct Hv as [<-|[<-|Hv]]; [| |contradiction].
 - eapply context_entry0; apply in_app_iff; left; unfold stack_remove.init_stubs; cbn; right; left; reflexivity.
 - eapply context_entry0; apply in_app_iff; right.
   apply in_map_iff; exists (loc,p); split; [reflexivity|exact Hp].
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_remove_stack_good_code_labels_incr" *)
Theorem stack_remove_stack_good_code_labels_incr : forall (prog0 : list (N * prog a)) elabs jump offset sp,
 stack_remove.stack_err_lab IN elabs /\ stack_good_code_labels prog0 elabs ->
 stack_good_code_labels (MAP (stack_remove.prog_comp jump offset sp) prog0) elabs.
Proof.
 intros ps elabs jump off sp [Herr Hg]. apply good_code_labels_pointwise.
 eapply transformed_code_labels; [exact Hg| | | | |].
 - intros n p Hin; apply in_map; exact Hin.
 - intros n p; reflexivity.
 - intros n p; cbn [stack_remove.prog_comp SND]; apply stack_remove_stack_get_handler_labels_comp.
 - intros n p; cbn [stack_remove.prog_comp SND]; apply stack_remove_get_code_labels_comp.
 - apply context_external0; exact Herr.
Qed.
Local Lemma alloc_labels n : forall p : prog a, forall m,
 (stackProps.get_code_labels (FST (stack_alloc.comp n m p)) SUBSET
  (stackLang.gc_stub_location,0) INSERT stackProps.get_code_labels p) /\
 (forall i, stack_get_handler_labels i (FST (stack_alloc.comp n m p)) = stack_get_handler_labels i p).
Proof.
 intros p; induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind; intros m.
 - destruct ret as [[p1 [lr [l1 l2]]]|].
   + pose proof (Hr p1 _ eq_refl m) as [HC1 HH1].
     cbn [stack_alloc.comp]. destruct (stack_alloc.comp n m p1) as [q1 m1] eqn:F1.
     cbn [FST] in HC1,HH1 |- *. destruct h as [[p2 [k1 k2]]|].
     * pose proof (Hh p2 _ eq_refl m1) as [HC2 HH2].
       destruct (stack_alloc.comp n m1 p2) as [q2 m2] eqn:F2.
       cbn [FST] in HC2,HH2 |- *. split.
       -- intros q Hq; specialize (HC1 q); specialize (HC2 q); destruct dest;
          cbn [stackProps.get_code_labels] in Hq |- *;
          cbv beta delta [pred_set.IN pred_set.UNION pred_set.INSERT pred_set.EMPTY] in *; tauto.
       -- intros i; cbn [stack_get_handler_labels]; rewrite HH1,HH2; reflexivity.
     * split.
       -- intros q Hq; specialize (HC1 q); destruct dest;
          cbn [FST stackProps.get_code_labels] in Hq |- *;
          cbv beta delta [pred_set.IN pred_set.UNION pred_set.INSERT pred_set.EMPTY] in *; tauto.
       -- intros i; cbn [FST stack_get_handler_labels]; rewrite HH1; reflexivity.
   + split; [intros q Hq; destruct dest; cbn [stack_alloc.comp FST stackProps.get_code_labels] in Hq |- *;
     cbv beta delta [pred_set.IN pred_set.UNION pred_set.INSERT pred_set.EMPTY] in *; tauto|intros i; reflexivity].
 - pose proof (IH1 m) as [HC1 HH1]. cbn [stack_alloc.comp].
   destruct (stack_alloc.comp n m p1) as [q1 m1] eqn:F1.
   pose proof (IH2 m1) as [HC2 HH2]. destruct (stack_alloc.comp n m1 p2) as [q2 m2] eqn:F2.
   cbn [FST] in HC1,HH1,HC2,HH2 |- *. split.
   + intros q Hq; specialize (HC1 q); specialize (HC2 q); cbn [stackProps.get_code_labels] in Hq |- *;
     cbv beta delta [pred_set.IN pred_set.UNION pred_set.INSERT pred_set.EMPTY] in *; tauto.
   + intros i; cbn [stack_get_handler_labels]; rewrite HH1,HH2; reflexivity.
 - pose proof (IH1 m) as [HC1 HH1]. cbn [stack_alloc.comp].
   destruct (stack_alloc.comp n m p1) as [q1 m1] eqn:F1.
   pose proof (IH2 m1) as [HC2 HH2]. destruct (stack_alloc.comp n m1 p2) as [q2 m2] eqn:F2.
   cbn [FST] in HC1,HH1,HC2,HH2 |- *. split.
   + intros q Hq; specialize (HC1 q); specialize (HC2 q); cbn [stackProps.get_code_labels] in Hq |- *;
     cbv beta delta [pred_set.IN pred_set.UNION pred_set.INSERT pred_set.EMPTY] in *; tauto.
   + intros i; cbn [stack_get_handler_labels]; rewrite HH1,HH2; reflexivity.
 - pose proof (IH m) as [HC HH]. cbn [stack_alloc.comp].
   destruct (stack_alloc.comp n m p) as [q m1] eqn:F; cbn [FST] in HC,HH |- *.
   split; [exact HC|exact HH].
 - destruct p; cbn in Hp; try contradiction; cbn [stack_alloc.comp FST];
   try (split; [intros q Hq; apply IN_INSERT; right; exact Hq|reflexivity]).
   all: try (split; [intros q Hq; cbn [stackProps.get_code_labels] in Hq |- *;
    cbv beta delta [pred_set.IN pred_set.UNION pred_set.INSERT pred_set.EMPTY] in *; tauto|intros i; apply EXTENSION; intros q; cbn [stack_get_handler_labels]; cbv beta delta [pred_set.IN pred_set.UNION pred_set.EMPTY]; tauto]).
   destruct o; cbn [FST]; (split; [intros q Hq; cbn [stackProps.get_code_labels] in Hq |- *;
    cbv beta delta [pred_set.IN pred_set.UNION pred_set.INSERT pred_set.EMPTY] in *; tauto|intros i; apply EXTENSION; intros q; cbn [stack_get_handler_labels]; cbv beta delta [pred_set.IN pred_set.UNION pred_set.EMPTY]; tauto]).
Qed.
(** HOL quantifies unused [pp] and [mm]; their polymorphic carriers are retained. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_alloc_get_code_labels_comp" *)
Local Theorem stack_alloc_get_code_labels_comp {pp_ty mm_ty : Type} :
 forall n m (p : prog a) (pp : pp_ty) (mm : mm_ty),
 get_code_labels (FST (stack_alloc.comp n m p)) SUBSET
 (stackLang.gc_stub_location,0) INSERT get_code_labels p.
Proof. intros; apply (proj1 (alloc_labels n p m)). Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_alloc_stack_get_handler_labels_comp" *)
Local Theorem stack_alloc_stack_get_handler_labels_comp {pp_ty mm_ty : Type} :
 forall i n m (p : prog a) (pp : pp_ty) (mm : mm_ty),
 stack_get_handler_labels i (FST (stack_alloc.comp n m p)) = stack_get_handler_labels i p.
Proof. intros; apply (proj2 (alloc_labels n p m)). Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_alloc_init_code_labels" *)
Local Theorem stack_alloc_init_code_labels : forall dc : data_to_word.config, stackProps.get_code_labels (@stack_alloc.word_gc_code a dc) = {}.
Proof. intros dc; unfold stack_alloc.word_gc_code. destruct (data_to_word.gc_kind dc) as [| |sizes]; try destruct sizes; cbn [stack_alloc.memcpy_code stack_alloc.clear_top_inst stack_alloc.word_gc_move_code stack_alloc.word_gc_move_list_code stack_alloc.word_gc_move_loop_code stack_alloc.word_gc_move_bitmap_code stack_alloc.word_gc_move_bitmaps_code stack_alloc.word_gc_move_roots_bitmaps_code stack_alloc.word_gen_gc_move_code stack_alloc.word_gen_gc_partial_move_code stack_alloc.word_gen_gc_move_bitmap_code stack_alloc.word_gen_gc_partial_move_bitmap_code stack_alloc.word_gen_gc_move_bitmaps_code stack_alloc.word_gen_gc_partial_move_bitmaps_code stack_alloc.word_gen_gc_move_roots_bitmaps_code stack_alloc.word_gen_gc_partial_move_roots_bitmaps_code stack_alloc.word_gen_gc_move_list_code stack_alloc.word_gen_gc_partial_move_list_code stack_alloc.word_gen_gc_move_data_code stack_alloc.word_gen_gc_partial_move_ref_list_code stack_alloc.word_gen_gc_partial_move_data_code stack_alloc.word_gen_gc_move_refs_code stack_alloc.word_gen_gc_move_loop_code stack_alloc.word_gc_partial_or_full stack_alloc.SetNewTrigger stack_alloc.word_gc_code stackProps.get_code_labels list_Seq APPEND]; apply EXTENSION; intros q; cbv beta delta [pred_set.IN pred_set.UNION pred_set.EMPTY]; tauto. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_alloc_stack_good_code_labels" *)
Theorem stack_alloc_stack_good_code_labels : forall (ps : list (N * prog a)) dc elabs,
 stack_good_code_labels ps elabs -> stack_good_code_labels (stack_alloc.compile dc ps) elabs.
Proof.
 intros ps dc elabs Hg; unfold stack_alloc.compile; apply good_code_labels_pointwise.
 assert (Ht : forall n p q, In (n,p) (MAP stack_alloc.prog_comp ps) -> q IN get_code_labels p ->
 code_label_context (stack_alloc.stubs dc ++ MAP stack_alloc.prog_comp ps) elabs q).
 { eapply transformed_code_labels; [exact Hg| | | | |].
 - intros n p Hin; apply in_app_iff; right; apply in_map; exact Hin.
 - intros n p; reflexivity.
 - intros n p; cbn [stack_alloc.prog_comp SND]; apply (proj2 (alloc_labels n p (stack_alloc.next_lab p 2))).
 - intros n p; cbn [stack_alloc.prog_comp SND]; apply (proj1 (alloc_labels n p (stack_alloc.next_lab p 2))).
 - eapply context_entry0; apply in_app_iff; left; unfold stack_alloc.stubs; cbn; left; reflexivity. }
 intros n p q Hin Hq; apply in_app_iff in Hin; destruct Hin as [Hin|Hin]; [|eapply Ht; eauto].
 unfold stack_alloc.stubs in Hin; cbn in Hin; destruct Hin as [E|Hin]; [injection E as <- <-|contradiction].
 cbn [get_code_labels] in Hq; rewrite stack_alloc_init_code_labels in Hq.
 cbv beta delta [pred_set.IN pred_set.UNION pred_set.EMPTY] in Hq; tauto.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_alloc_stack_good_code_labels_incr" *)
Theorem stack_alloc_stack_good_code_labels_incr : forall (ps : list (N * prog a)) elabs,
 stackLang.gc_stub_location IN elabs /\ stack_good_code_labels ps elabs ->
 stack_good_code_labels (MAP stack_alloc.prog_comp ps) elabs.
Proof.
 intros ps elabs [Herr Hg]; apply good_code_labels_pointwise.
 eapply transformed_code_labels; [exact Hg| | | | |].
 - intros n p Hin; apply in_map; exact Hin.
 - intros n p; reflexivity.
 - intros n p; cbn [stack_alloc.prog_comp SND]; apply (proj2 (alloc_labels n p (stack_alloc.next_lab p 2))).
 - intros n p; cbn [stack_alloc.prog_comp SND]; apply (proj1 (alloc_labels n p (stack_alloc.next_lab p 2))).
 - apply context_external0; exact Herr.
Qed.
Local Definition raw_label_rel (i : spt N) (p : prog a) n l :=
 exists k, (n,k) IN get_code_labels p /\ (l <> k -> l = 1 /\ k = 0 /\ n IN domain i).
Local Lemma raw_comp_labels i : forall p : prog a, forall n l,
 (n,l) IN get_code_labels (stack_rawcall.comp i p) -> raw_label_rel i p n l.
Proof.
 intros p; induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind; intros n l H.
 - destruct ret as [[p1 [lr [l1 l2]]]|]; [destruct h as [[p2 [k1 k2]]|]|];
   try pose proof (Hr p1 _ eq_refl n l) as IHr;
   try pose proof (Hh p2 _ eq_refl n l) as IHh; clear Hr Hh; destruct dest;
   cbn [stack_rawcall.comp get_code_labels] in H |- *; unfold raw_label_rel;
   cbv beta delta [pred_set.IN pred_set.UNION pred_set.INSERT pred_set.EMPTY] in H |- *.
   all: try (exists l; split; [exact H|tauto]).
   all: firstorder.
 - cbn [stack_rawcall.comp] in H; unfold stack_rawcall.comp_seq in H.
   destruct (stack_rawcall.dest_case p1 p2) as [[k d]|] eqn:Ed.
   + apply stack_rawcallProof.dest_case_SOME in Ed; destruct Ed as [-> ->].
     destruct (lookup d i) as [j|] eqn:E; [destruct (j =? k); [|destruct (j <? k)]|];
     cbn [get_code_labels stack_rawcall.comp] in H; unfold raw_label_rel;
     cbn [get_code_labels]; cbv beta delta [pred_set.IN pred_set.UNION pred_set.INSERT pred_set.EMPTY] in H |- *.
     all: try (exists l; split; [exact H|tauto]).
     all: exists 0; split; [firstorder congruence|]; intros; repeat split; try firstorder congruence.
     all: assert (n = d) by (intuition congruence); subst n; apply domain_lookup; exists j; exact E.
   + cbn [get_code_labels] in H; apply IN_UNION in H; destruct H as [H|H].
     * destruct (IH1 _ _ H) as [k [Hk Hrest]]; exists k; split; [apply IN_UNION; left; exact Hk|exact Hrest].
     * destruct (IH2 _ _ H) as [k [Hk Hrest]]; exists k; split; [apply IN_UNION; right; exact Hk|exact Hrest].
 - cbn [stack_rawcall.comp get_code_labels] in H; apply IN_UNION in H; destruct H as [H|H].
   + destruct (IH1 _ _ H) as [k [Hk Hrest]]; exists k; split; [apply IN_UNION; left; exact Hk|exact Hrest].
   + destruct (IH2 _ _ H) as [k [Hk Hrest]]; exists k; split; [apply IN_UNION; right; exact Hk|exact Hrest].
 - cbn [stack_rawcall.comp get_code_labels] in H; exact (IH _ _ H).
 - destruct p; cbn in Hp; try contradiction; cbn [stack_rawcall.comp] in H; (exists l; split; [exact H|tauto]).
Qed.

Local Lemma raw_top_labels i : forall p : prog a, forall n l,
 (n,l) IN get_code_labels (stack_rawcall.comp_top i p) -> raw_label_rel i p n l.
Proof.
 intros p n l H; unfold stack_rawcall.comp_top in H; destruct p; try (apply raw_comp_labels; exact H).
 cbn [get_code_labels] in H; apply IN_UNION in H; destruct H as [H|H].
 - destruct (raw_comp_labels i p1 n l H) as [k [Hk Hr]]; exists k; split; [apply IN_UNION; left; exact Hk|exact Hr].
 - destruct (raw_comp_labels i p2 n l H) as [k [Hk Hr]]; exists k; split; [apply IN_UNION; right; exact Hk|exact Hr].
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "IN_get_code_labels_comp_top_lemma" *)
Theorem IN_get_code_labels_comp_top_lemma : forall i (q : prog a) p_1 p_2,
 ((p_1,p_2) IN get_code_labels (stack_rawcall.comp i q) ->
 exists k, (p_1,k) IN get_code_labels q /\ (p_2 <> k -> p_2 = 1 /\ k = 0 /\ p_1 IN domain i)) /\
 ((p_1,p_2) IN get_code_labels (stack_rawcall.comp_top i q) ->
 exists k, (p_1,k) IN get_code_labels q /\ (p_2 <> k -> p_2 = 1 /\ k = 0 /\ p_1 IN domain i)).
Proof. intros; split; [apply raw_comp_labels|apply raw_top_labels]. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "IN_domain_collect_info" *)
Theorem IN_domain_collect_info : forall (ps : list (N * prog a)) f p_1,
 p_1 IN domain (stack_rawcall.collect_info ps f) -> MEM p_1 (MAP FST ps) \/ p_1 IN domain f.
Proof.
 induction ps as [|[n p] ps IH]; intros f q H; cbn [stack_rawcall.collect_info] in H; [right; exact H|].
 destruct (stack_rawcall.seq_stack_alloc p) as [k|] eqn:E.
 - apply IH in H; destruct H as [H|H].
   + left; apply MEM_In; cbn [MAP FST]; right; apply MEM_In; exact H.
   + rewrite domain_insert in H; cbv beta delta [pred_set.IN] in H; destruct H as [H|H]; [left; apply MEM_In; cbn [MAP FST]; left; congruence|right; exact H].
 - apply IH in H; destruct H as [H|H]; [left; apply MEM_In; cbn [MAP FST]; right; apply MEM_In; exact H|right; exact H].
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "IN_get_code_labels_comp_top" *)
Theorem IN_get_code_labels_comp_top : forall (ps : list (N * prog a)) (q : prog a) p_1 p_2,
 (p_1,p_2) IN get_code_labels (stack_rawcall.comp_top (stack_rawcall.collect_info ps LN) q) ->
 exists k, (p_1,k) IN get_code_labels q /\ (p_2 <> k -> p_2 = 1 /\ k = 0 /\ MEM p_1 (MAP FST ps)).
Proof.
 intros ps q n l H; destruct (raw_top_labels _ _ _ _ H) as [k [Hk Hr]].
 exists k; split; [exact Hk|]. intros Hne; specialize (Hr Hne); destruct Hr as [Hl [Hk0 Hd]].
 apply IN_domain_collect_info in Hd; destruct Hd as [Hd|Hd]; [repeat split; assumption|].
 unfold pred_set.IN, domain in Hd; contradiction.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_rawcall_stack_good_code_labels" *)
Theorem stack_rawcall_stack_good_code_labels : forall (ps : list (N * prog a)) elabs,
 stack_good_code_labels ps elabs -> stack_good_code_labels (stack_rawcall.compile ps) elabs.
Proof.
 intros ps elabs Hg; unfold stack_rawcall.compile.
 set (i := stack_rawcall.collect_info ps LN).
 set (f := fun np : N * prog a => let '(n,p) := np in (n,stack_rawcall.comp_top i p)).
 apply good_code_labels_pointwise; intros n p q Hin Hq.
 apply in_map_iff in Hin; destruct Hin as ([n0 p0] & E & Hin); unfold f in E; injection E as <- <-.
 destruct q as [n1 l]; unfold i in Hq.
 destruct (IN_get_code_labels_comp_top ps p0 n1 l Hq) as [k [Hk Hr]].
 destruct (N.eq_dec l k) as [->|Hne].
 - eapply context_transport with (ps := ps) (f := f).
   + intros n p H; apply in_map; exact H.
   + intros; reflexivity.
   + intros; cbn [f SND]; apply (proj2 (stack_rawcallProof.stack_get_handler_labels_comp i p n)).
   + exact (proj1 (good_code_labels_pointwise ps elabs) Hg n0 p0 (n1,k) Hin Hk).
 - specialize (Hr Hne); destruct Hr as [-> [_ Hmem]].
   apply MEM_In, in_map_iff in Hmem; destruct Hmem as ([n2 p2] & E & Hp); cbn [FST] in E; subst n2.
   eapply context_entry1; apply in_map_iff; exists (n1,p2); split; [reflexivity|exact Hp].
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_to_lab_stack_good_code_labels" *)
Theorem stack_to_lab_stack_good_code_labels : forall sc dc mh sp off (ps : list (N * prog a)) ps' elabs,
 stack_to_lab.compile sc dc mh sp off ps = ps' /\
 MEM bvl_to_bvi.InitGlobals_location (MAP FST ps) /\ stack_good_code_labels ps elabs /\
 EVERY sec_labels_ok ps' -> labProps.get_labels ps' SUBSET
 labProps.get_code_labels ps' UNION IMAGE (fun n => (n,0)) elabs UNION IMAGE (fun n => (n,1)) elabs.
Proof.
 intros sc dc mh sp off ps ps' elabs [<- [Hi [Hg Hv]]]; unfold stack_to_lab.compile in *.
 apply get_labels_MAP_prog_to_section_SUBSET_code_labels; split; [exact Hv|].
 apply stack_names_stack_good_code_labels; apply stack_remove_stack_good_code_labels; split.
 - apply MEM_In in Hi; unfold stack_alloc.compile, stack_rawcall.compile; cbv zeta; rewrite map_app, !map_map.
   apply MEM_In; apply in_app_iff; right.
   apply in_map_iff in Hi; destruct Hi as ([n p] & E & Hin); cbn [FST] in E; subst n.
   apply in_map_iff; exists (bvl_to_bvi.InitGlobals_location,p); split; [reflexivity|exact Hin].
 - apply stack_alloc_stack_good_code_labels; apply stack_rawcall_stack_good_code_labels; exact Hg.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_to_lab_stack_good_code_labels_incr" *)
Theorem stack_to_lab_stack_good_code_labels_incr : forall f jump off sp (ps : list (N * prog a)) ps' elabs,
 stack_remove.stack_err_lab IN elabs /\ stackLang.gc_stub_location IN elabs /\
 stack_to_lab.compile_no_stubs f jump off sp ps = ps' /\ stack_good_code_labels ps elabs /\
 EVERY sec_labels_ok ps' -> labProps.get_labels ps' SUBSET
 labProps.get_code_labels ps' UNION IMAGE (fun n => (n,0)) elabs UNION IMAGE (fun n => (n,1)) elabs.
Proof.
 intros f jump off sp ps ps' elabs [He [Hgc [<- [Hg Hv]]]]; unfold stack_to_lab.compile_no_stubs in *.
 apply get_labels_MAP_prog_to_section_SUBSET_code_labels; split; [exact Hv|].
 apply stack_names_stack_good_code_labels; apply stack_remove_stack_good_code_labels_incr; split; [exact He|].
 apply stack_alloc_stack_good_code_labels_incr; auto.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels" *)
Theorem nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels : forall ps : list (N * prog a),
 EVERY sec_labels_ok (MAP prog_to_section ps) /\ stack_good_handler_labels ps ->
 backendProps.restrict_nonzero (labProps.get_labels (MAP prog_to_section ps)) SUBSET labProps.get_code_labels (MAP prog_to_section ps).
Proof.
 intros ps [Hv Hg] q [Hq Hnz].
 pose proof (get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma ps Hv q Hq) as E.
 apply IN_UNION in E; destruct E as [E|E]; [exact E|].
 specialize (Hg q (conj E Hnz)). apply IN_UNION in Hg; destruct Hg as [Hg|Hg].
 - exact (MAP_prog_to_section_preserves_handler_labels ps q Hg).
 - exact (one_prog_section ps q Hg).
Qed.
Local Definition handler_context (ps : list (N * prog a)) :=
 BIGUNION (set (MAP (fun '(n,p) => stack_get_handler_labels n p) ps)) UNION
 IMAGE (fun n => (n,1)) (set (MAP FST ps)).
Local Lemma good_handler_pointwise ps : stack_good_handler_labels ps <->
 forall n p q, In (n,p) ps -> q IN get_code_labels p -> SND q <> 0 -> q IN handler_context ps.
Proof.
 unfold stack_good_handler_labels, handler_context, backendProps.restrict_nonzero, pred_set.SUBSET; split.
 - intros H n p q Hp Hq Hnz; apply H; split; [|exact Hnz].
   apply IN_BIGUNION; exists (get_code_labels p); split; [exact Hq|].
   apply IN_IMAGE; exists p; split; [reflexivity|apply IN_set, in_map_iff; exists (n,p); split; [reflexivity|exact Hp]].
 - intros H q [Hq Hnz]; apply IN_BIGUNION in Hq; destruct Hq as (v & Hq & Hv).
   apply IN_IMAGE in Hv; destruct Hv as (p & He & Hp); subst v.
   apply IN_set, in_map_iff in Hp; destruct Hp as ([n p0] & E & Hp); cbn [SND] in E; subst p0.
   exact (H n p q Hp Hq Hnz).
Qed.
Local Lemma handler_context_map ps (f : N * prog a -> N * prog a) :
 (forall n p, FST (f (n,p)) = n) ->
 (forall n p, stack_get_handler_labels n (SND (f (n,p))) = stack_get_handler_labels n p) ->
 handler_context (MAP f ps) = handler_context ps.
Proof.
 intros Hn Hh; unfold handler_context; rewrite !map_map.
 assert (E1 : MAP (fun np => let '(n,p) := f np in stack_get_handler_labels n p) ps =
 MAP (fun '(n,p) => stack_get_handler_labels n p) ps).
 { apply map_ext; intros [n p]; pose proof (Hn n p) as En; pose proof (Hh n p) as Eh;
   destruct (f (n,p)) as [n1 p1]; cbn [FST SND] in En,Eh; subst n1; exact Eh. }
 assert (E2 : MAP (fun np => FST (f np)) ps = MAP FST ps).
 { apply map_ext; intros [n p]; apply Hn. }
 rewrite E1,E2; reflexivity.
Qed.
Local Lemma handler_context_mono ps qs :
 (forall np, In np ps -> In np qs) -> handler_context ps SUBSET handler_context qs.
Proof.
 intros Hi q Hq; apply IN_UNION in Hq; destruct Hq as [Hq|Hq]; apply IN_UNION; [left|right].
 - apply IN_BIGUNION in Hq; destruct Hq as (s & Hq & Hs).
   apply IN_BIGUNION; exists s; split; [exact Hq|].
   apply IN_set, in_map_iff in Hs; destruct Hs as (np & <- & Hp).
   apply IN_set, in_map_iff; exists np; split; [reflexivity|apply Hi; exact Hp].
 - apply IN_IMAGE in Hq; destruct Hq as (n & -> & Hn).
   apply IN_IMAGE; exists n; split; [reflexivity|].
   apply IN_set, in_map_iff in Hn; destruct Hn as (np & <- & Hp).
   apply IN_set, in_map_iff; exists np; split; [reflexivity|apply Hi; exact Hp].
Qed.
Local Lemma good_handler_transform ps (f : N * prog a -> N * prog a) :
 stack_good_handler_labels ps ->
 (forall n p, FST (f (n,p)) = n) ->
 (forall n p, stack_get_handler_labels n (SND (f (n,p))) = stack_get_handler_labels n p) ->
 (forall n p q, q IN get_code_labels (SND (f (n,p))) -> SND q <> 0 -> q IN get_code_labels p) ->
 stack_good_handler_labels (MAP f ps).
Proof.
 intros Hg Hn Hh Hc; apply good_handler_pointwise; intros n p q Hp Hq Hnz.
 apply in_map_iff in Hp; destruct Hp as ([n0 p0] & E & Hp).
 pose proof (Hc n0 p0 q) as Hc0; rewrite E in Hc0; cbn [SND] in Hc0.
 rewrite (handler_context_map ps f Hn Hh).
 exact (proj1 (good_handler_pointwise ps) Hg n0 p0 q Hp (Hc0 Hq Hnz) Hnz).
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_names_stack_good_handler_labels" *)
Theorem stack_names_stack_good_handler_labels : forall (ps : list (N * prog a)) f,
 stack_good_handler_labels ps -> stack_good_handler_labels (stack_names.compile f ps).
Proof.
 intros ps f Hg; unfold stack_names.compile; apply good_handler_transform; [exact Hg| | |].
 - intros; reflexivity.
 - intros; cbn [stack_names.prog_comp SND]; apply stack_names_stack_get_handler_labels_comp.
 - intros n p q Hq Hnz; cbn [stack_names.prog_comp SND] in Hq; rewrite stack_names_get_code_labels_comp in Hq; exact Hq.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "restrict_nonzero_union" *)
Theorem restrict_nonzero_union : forall A B : N * N -> Prop,
 backendProps.restrict_nonzero (A UNION B) = backendProps.restrict_nonzero A UNION backendProps.restrict_nonzero B.
Proof. intros; apply EXTENSION; intros q; unfold backendProps.restrict_nonzero;
 cbv beta delta [pred_set.IN pred_set.UNION]; tauto. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "restrict_nonzero_IN" *)
Theorem restrict_nonzero_IN : forall x (s : N * N -> Prop),
 x IN backendProps.restrict_nonzero s <-> x IN s /\ SND x <> 0.
Proof. reflexivity. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_good_handler_labels_append" *)
Theorem stack_good_handler_labels_append : forall xs ys : list (N * prog a),
 stack_good_handler_labels xs /\ stack_good_handler_labels ys -> stack_good_handler_labels (xs ++ ys).
Proof.
 intros xs ys [Hx Hy]; apply good_handler_pointwise; intros n p q Hp Hq Hnz.
 apply in_app_iff in Hp; destruct Hp as [Hp|Hp].
 - apply handler_context_mono with (ps := xs); [intros np H; apply in_app_iff; left; exact H|].
   exact (proj1 (good_handler_pointwise xs) Hx n p q Hp Hq Hnz).
 - apply handler_context_mono with (ps := ys); [intros np H; apply in_app_iff; right; exact H|].
   exact (proj1 (good_handler_pointwise ys) Hy n p q Hp Hq Hnz).
Qed.
Local Lemma drop_zero_insert err (src out : N * N -> Prop) q :
 out SUBSET (err,0) INSERT src -> q IN out -> SND q <> 0 -> q IN src.
Proof. intros H Hq Hnz; specialize (H q Hq); apply IN_INSERT in H;
 destruct H as [->|H]; [cbn [SND] in Hnz; contradiction|exact H]. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_remove_stack_good_handler_labels_incr" *)
Theorem stack_remove_stack_good_handler_labels_incr : forall (ps : list (N * prog a)) jump off sp,
 stack_good_handler_labels ps -> stack_good_handler_labels (MAP (stack_remove.prog_comp jump off sp) ps).
Proof.
 intros ps jump off sp Hg; apply good_handler_transform; [exact Hg| | |].
 - intros; reflexivity.
 - intros; cbn [stack_remove.prog_comp SND]; apply stack_remove_stack_get_handler_labels_comp.
 - intros n p q Hq Hnz; cbn [stack_remove.prog_comp SND] in Hq;
   eapply drop_zero_insert; [apply stack_remove_get_code_labels_comp|exact Hq|exact Hnz].
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_remove_stack_good_handler_labels" *)
Theorem stack_remove_stack_good_handler_labels : forall (ps : list (N * prog a)) jump off ggc mh sp loc,
 stack_good_handler_labels ps -> stack_good_handler_labels (stack_remove.compile jump off ggc mh sp loc ps).
Proof.
 intros ps jump off ggc mh sp loc Hg; unfold stack_remove.compile.
 apply stack_good_handler_labels_append; split; [|apply stack_remove_stack_good_handler_labels_incr; exact Hg].
 apply good_handler_pointwise; intros n p q Hp Hq Hnz.
 pose proof (init_stubs_labels ggc mh sp loc) as Hv; apply EVERY_Forall in Hv; rewrite Forall_forall in Hv.
 assert (Hi : In p (MAP SND (stack_remove.init_stubs ggc mh sp loc))).
 { apply in_map_iff; exists (n,p); split; [reflexivity|exact Hp]. }
 specialize (Hv _ Hi); apply bool_decide_spec in Hv; specialize (Hv q Hq).
 apply IN_set in Hv; cbn in Hv; destruct Hv as [<-|[<-|Hv]]; cbn [SND] in Hnz; contradiction.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_alloc_stack_good_handler_labels_incr" *)
Theorem stack_alloc_stack_good_handler_labels_incr : forall ps : list (N * prog a),
 stack_good_handler_labels ps -> stack_good_handler_labels (MAP stack_alloc.prog_comp ps).
Proof.
 intros ps Hg; apply good_handler_transform; [exact Hg| | |].
 - intros; reflexivity.
 - intros n p; cbn [stack_alloc.prog_comp SND]; apply (proj2 (alloc_labels n p (stack_alloc.next_lab p 2))).
 - intros n p q Hq Hnz; cbn [stack_alloc.prog_comp SND] in Hq;
   eapply drop_zero_insert; [apply (proj1 (alloc_labels n p (stack_alloc.next_lab p 2)))|exact Hq|exact Hnz].
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_alloc_stack_good_handler_labels" *)
Theorem stack_alloc_stack_good_handler_labels : forall (ps : list (N * prog a)) dc,
 stack_good_handler_labels ps -> stack_good_handler_labels (stack_alloc.compile dc ps).
Proof.
 intros ps dc Hg; unfold stack_alloc.compile; apply stack_good_handler_labels_append; split;
 [|apply stack_alloc_stack_good_handler_labels_incr; exact Hg].
 apply good_handler_pointwise; intros n p q Hp Hq Hnz.
 unfold stack_alloc.stubs in Hp; cbn in Hp; destruct Hp as [E|Hp]; [injection E as <- <-|contradiction].
 cbn [get_code_labels] in Hq; rewrite stack_alloc_init_code_labels in Hq;
 cbv beta delta [pred_set.IN pred_set.UNION pred_set.EMPTY] in Hq; tauto.
Qed.
Local Lemma handler_context_entry1 ps n p : In (n,p) ps -> (n,1) IN handler_context ps.
Proof.
 intros Hp; apply IN_UNION; right; apply IN_IMAGE; exists n; split; [reflexivity|].
 apply IN_set, in_map_iff; exists (n,p); split; [reflexivity|exact Hp].
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_rawcall_stack_good_handler_labels" *)
Theorem stack_rawcall_stack_good_handler_labels : forall ps : list (N * prog a),
 stack_good_handler_labels ps -> stack_good_handler_labels (stack_rawcall.compile ps).
Proof.
 intros ps Hg; unfold stack_rawcall.compile.
 set (i := stack_rawcall.collect_info ps LN).
 set (f := fun np : N * prog a => let '(n,p) := np in (n,stack_rawcall.comp_top i p)).
 apply good_handler_pointwise; intros n p q Hin Hq Hnz.
 apply in_map_iff in Hin; destruct Hin as ([n0 p0] & E & Hin); unfold f in E; injection E as <- <-.
 destruct q as [n1 l]; unfold i in Hq.
 destruct (IN_get_code_labels_comp_top ps p0 n1 l Hq) as [k [Hk Hr]].
 destruct (N.eq_dec l k) as [->|Hne].
 - rewrite (handler_context_map ps f).
   + exact (proj1 (good_handler_pointwise ps) Hg n0 p0 (n1,k) Hin Hk Hnz).
   + intros; reflexivity.
   + intros; cbn [f SND]; apply (proj2 (stack_rawcallProof.stack_get_handler_labels_comp i p n)).
 - specialize (Hr Hne); destruct Hr as [-> [_ Hmem]].
   apply MEM_In, in_map_iff in Hmem; destruct Hmem as ([n2 p2] & E & Hp); cbn [FST] in E; subst n2.
   eapply handler_context_entry1; apply in_map_iff; exists (n1,p2); split; [reflexivity|exact Hp].
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_to_lab_stack_good_handler_labels" *)
Theorem stack_to_lab_stack_good_handler_labels : forall sc dc mh sp off (ps : list (N * prog a)) ps',
 stack_to_lab.compile sc dc mh sp off ps = ps' /\ stack_good_handler_labels ps /\ EVERY sec_labels_ok ps' ->
 backendProps.restrict_nonzero (labProps.get_labels ps') SUBSET labProps.get_code_labels ps'.
Proof.
 intros sc dc mh sp off ps ps' [<- [Hg Hv]]; unfold stack_to_lab.compile in *.
 apply nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels; split; [exact Hv|].
 apply stack_names_stack_good_handler_labels; apply stack_remove_stack_good_handler_labels;
 apply stack_alloc_stack_good_handler_labels; apply stack_rawcall_stack_good_handler_labels; exact Hg.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_to_lab_stack_good_handler_labels_incr" *)
Theorem stack_to_lab_stack_good_handler_labels_incr : forall f jump off sp (ps : list (N * prog a)) ps',
 stack_to_lab.compile_no_stubs f jump off sp ps = ps' /\ stack_good_handler_labels ps /\ EVERY sec_labels_ok ps' ->
 backendProps.restrict_nonzero (labProps.get_labels ps') SUBSET labProps.get_code_labels ps'.
Proof.
 intros f jump off sp ps ps' [<- [Hg Hv]]; unfold stack_to_lab.compile_no_stubs in *.
 apply nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels; split; [exact Hv|].
 apply stack_names_stack_good_handler_labels; apply stack_remove_stack_good_handler_labels_incr;
 apply stack_alloc_stack_good_handler_labels_incr; exact Hg.
Qed.
End CodeLabels.




(** Absence of shared-memory operations and installation instructions.
    HOL predicates with quantified arguments are reflected by [bool_decide]
    under [EVERY]; [safety_every] exposes their proposition-valued form. *)
Section Safety.
Context {a : N}.
Local Lemma rawcall_no_shmemop_eq i : forall p : prog a,
 no_shmemop (stack_rawcall.comp i p) = no_shmemop p.
Proof.
 intros p; induction p as [p IH] using stack_rawcallProof.psz_ind.
 stack_rawcallProof.syn_cases IH; cbn [no_shmemop]; stack_rawcallProof.rw_ih IH; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_rawcall_comp_no_shmemop" *)
Theorem stack_rawcall_comp_no_shmemop : forall i (p : prog a), no_shmemop p -> no_shmemop (stack_rawcall.comp i p).
Proof. intros; rewrite rawcall_no_shmemop_eq; assumption. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_rawcall_comp_top_no_shmemop" *)
Theorem stack_rawcall_comp_top_no_shmemop : forall i (p : prog a), no_shmemop p -> no_shmemop (stack_rawcall.comp_top i p).
Proof. intros i p H; unfold stack_rawcall.comp_top; destruct p; cbn [no_shmemop] in *; rewrite ?rawcall_no_shmemop_eq; exact H. Qed.
Local Lemma names_no_shmemop_eq f : forall p : prog a, no_shmemop (stack_names.comp f p) = no_shmemop p.
Proof.
 intros p; induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind.
 - destruct ret as [[p1 [lr [l1 l2]]]|]; destruct h as [[p2 [k1 k2]]|];
   cbn [stack_names.comp no_shmemop]; try rewrite (Hr p1 _ eq_refl); try rewrite (Hh p2 _ eq_refl); reflexivity.
 - cbn [stack_names.comp no_shmemop]; rewrite IH1,IH2; reflexivity.
 - cbn [stack_names.comp no_shmemop]; rewrite IH1,IH2; reflexivity.
 - cbn [stack_names.comp no_shmemop]; exact IH.
 - destruct p; cbn in Hp; try contradiction; try reflexivity; match goal with ad : asm.addr _ |- _ => destruct ad end; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_names_comp_no_shmemop" *)
Theorem stack_names_comp_no_shmemop : forall f (p : prog a), no_shmemop p -> no_shmemop (stack_names.comp f p).
Proof. intros; rewrite names_no_shmemop_eq; assumption. Qed.
Local Lemma rawcall_no_install_eq i : forall p : prog a,
 no_install (stack_rawcall.comp i p) = no_install p.
Proof.
 intros p; induction p as [p IH] using stack_rawcallProof.psz_ind.
 stack_rawcallProof.syn_cases IH; cbn [no_install]; stack_rawcallProof.rw_ih IH; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_rawcall_comp_no_install" *)
Theorem stack_rawcall_comp_no_install : forall i (p : prog a), no_install p -> no_install (stack_rawcall.comp i p).
Proof. intros; rewrite rawcall_no_install_eq; assumption. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_rawcall_comp_top_no_install" *)
Theorem stack_rawcall_comp_top_no_install : forall i (p : prog a), no_install p -> no_install (stack_rawcall.comp_top i p).
Proof. intros i p H; unfold stack_rawcall.comp_top; destruct p; cbn [no_install] in *; rewrite ?rawcall_no_install_eq; exact H. Qed.
Local Lemma names_no_install_eq f : forall p : prog a, no_install (stack_names.comp f p) = no_install p.
Proof.
 intros p; induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind.
 - destruct ret as [[p1 [lr [l1 l2]]]|]; destruct h as [[p2 [k1 k2]]|];
   cbn [stack_names.comp no_install]; try rewrite (Hr p1 _ eq_refl); try rewrite (Hh p2 _ eq_refl); reflexivity.
 - cbn [stack_names.comp no_install]; rewrite IH1,IH2; reflexivity.
 - cbn [stack_names.comp no_install]; rewrite IH1,IH2; reflexivity.
 - cbn [stack_names.comp no_install]; exact IH.
 - destruct p; cbn in Hp; try contradiction; try reflexivity; match goal with ad : asm.addr _ |- _ => destruct ad end; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_names_comp_no_install" *)
Theorem stack_names_comp_no_install : forall f (p : prog a), no_install p -> no_install (stack_names.comp f p).
Proof. intros; rewrite names_no_install_eq; assumption. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_alloc_comp_no_shmemop" *)
Theorem stack_alloc_comp_no_shmemop : forall n m (p : prog a), no_shmemop p -> no_shmemop (FST (stack_alloc.comp n m p)).
Proof.
 intros n m p; revert m; induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind; intros m H.
 - destruct ret as [[p1 [lr [l1 l2]]]|].
   + cbn [no_shmemop] in H; apply Bool.andb_true_iff in H as [H1 H2].
     pose proof (Hr p1 _ eq_refl m H1) as Hq1; cbn [stack_alloc.comp].
     destruct (stack_alloc.comp n m p1) as [q1 m1]; cbn [FST] in Hq1.
     destruct h as [[p2 [k1 k2]]|].
     * pose proof (Hh p2 _ eq_refl m1 H2) as Hq2;
       destruct (stack_alloc.comp n m1 p2) as [q2 m2]; cbn [FST] in Hq2;
       cbn [FST no_shmemop]; rewrite Hq1,Hq2; reflexivity.
     * cbn [FST no_shmemop]; rewrite Hq1; reflexivity.
   + cbn [stack_alloc.comp FST no_shmemop]; reflexivity.
 - cbn [no_shmemop] in H; apply Bool.andb_true_iff in H as [H1 H2];
   pose proof (IH1 m H1) as Hq1; cbn [stack_alloc.comp].
   destruct (stack_alloc.comp n m p1) as [q1 m1]; cbn [FST] in Hq1.
   pose proof (IH2 m1 H2) as Hq2; destruct (stack_alloc.comp n m1 p2) as [q2 m2];
   cbn [FST] in Hq2; cbn [FST no_shmemop]; rewrite Hq1,Hq2; reflexivity.
 - cbn [no_shmemop] in H; apply Bool.andb_true_iff in H as [H1 H2];
   pose proof (IH1 m H1) as Hq1; cbn [stack_alloc.comp].
   destruct (stack_alloc.comp n m p1) as [q1 m1]; cbn [FST] in Hq1.
   pose proof (IH2 m1 H2) as Hq2; destruct (stack_alloc.comp n m1 p2) as [q2 m2];
   cbn [FST] in Hq2; cbn [FST no_shmemop]; rewrite Hq1,Hq2; reflexivity.
 - pose proof (IH m H) as Hq; cbn [stack_alloc.comp];
   destruct (stack_alloc.comp n m p) as [q m1]; exact Hq.
 - destruct p; cbn in Hp; try contradiction; cbn [stack_alloc.comp FST no_shmemop] in H |- *; try exact H; try reflexivity.
   destruct o; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_alloc_comp_no_install" *)
Theorem stack_alloc_comp_no_install : forall n m (p : prog a), no_install p -> no_install (FST (stack_alloc.comp n m p)).
Proof.
 intros n m p; revert m; induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind; intros m H.
 - destruct ret as [[p1 [lr [l1 l2]]]|].
   + cbn [no_install] in H; apply Bool.andb_true_iff in H as [H1 H2].
     pose proof (Hr p1 _ eq_refl m H1) as Hq1; cbn [stack_alloc.comp].
     destruct (stack_alloc.comp n m p1) as [q1 m1]; cbn [FST] in Hq1.
     destruct h as [[p2 [k1 k2]]|].
     * pose proof (Hh p2 _ eq_refl m1 H2) as Hq2;
       destruct (stack_alloc.comp n m1 p2) as [q2 m2]; cbn [FST] in Hq2;
       cbn [FST no_install]; rewrite Hq1,Hq2; reflexivity.
     * cbn [FST no_install]; rewrite Hq1; reflexivity.
   + cbn [stack_alloc.comp FST no_install]; reflexivity.
 - cbn [no_install] in H; apply Bool.andb_true_iff in H as [H1 H2];
   pose proof (IH1 m H1) as Hq1; cbn [stack_alloc.comp].
   destruct (stack_alloc.comp n m p1) as [q1 m1]; cbn [FST] in Hq1.
   pose proof (IH2 m1 H2) as Hq2; destruct (stack_alloc.comp n m1 p2) as [q2 m2];
   cbn [FST] in Hq2; cbn [FST no_install]; rewrite Hq1,Hq2; reflexivity.
 - cbn [no_install] in H; apply Bool.andb_true_iff in H as [H1 H2];
   pose proof (IH1 m H1) as Hq1; cbn [stack_alloc.comp].
   destruct (stack_alloc.comp n m p1) as [q1 m1]; cbn [FST] in Hq1.
   pose proof (IH2 m1 H2) as Hq2; destruct (stack_alloc.comp n m1 p2) as [q2 m2];
   cbn [FST] in Hq2; cbn [FST no_install]; rewrite Hq1,Hq2; reflexivity.
 - pose proof (IH m H) as Hq; cbn [stack_alloc.comp];
   destruct (stack_alloc.comp n m p) as [q m1]; exact Hq.
 - destruct p; cbn in Hp; try contradiction; cbn [stack_alloc.comp FST no_install] in H |- *; try exact H; try reflexivity.
   destruct o; reflexivity.
Qed.

Local Lemma upshift_f_no_shmemop : forall fuel k n, no_shmemop (@stack_remove.upshift_f a fuel k n).
Proof.
 induction fuel as [|fuel IH]; intros k n; cbn [stack_remove.upshift_f]; [reflexivity|].
 destruct (n <=? stack_remove.max_stack_alloc); cbn [stack_remove.single_stack_alloc stack_remove.single_stack_free stack_remove.halt_inst no_shmemop]; rewrite ?IH; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "upshift_no_shmemop" *)
Theorem upshift_no_shmemop : forall k n, no_shmemop (@stack_remove.upshift a k n).
Proof. intros; apply upshift_f_no_shmemop. Qed.
Local Lemma downshift_f_no_shmemop : forall fuel k n, no_shmemop (@stack_remove.downshift_f a fuel k n).
Proof.
 induction fuel as [|fuel IH]; intros k n; cbn [stack_remove.downshift_f]; [reflexivity|].
 destruct (n <=? stack_remove.max_stack_alloc); cbn [stack_remove.single_stack_alloc stack_remove.single_stack_free stack_remove.halt_inst no_shmemop]; rewrite ?IH; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "downshift_no_shmemop" *)
Theorem downshift_no_shmemop : forall k n, no_shmemop (@stack_remove.downshift a k n).
Proof. intros; apply downshift_f_no_shmemop. Qed.
Local Lemma stack_free_f_no_shmemop : forall fuel k n, no_shmemop (@stack_remove.stack_free_f a fuel k n).
Proof.
 induction fuel as [|fuel IH]; intros k n; cbn [stack_remove.stack_free_f]; [reflexivity|].
 destruct (n =? 0); [reflexivity|].
 destruct (n <=? stack_remove.max_stack_alloc); cbn [stack_remove.single_stack_alloc stack_remove.single_stack_free stack_remove.halt_inst no_shmemop]; rewrite ?IH; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_free_no_shmemop" *)
Theorem stack_free_no_shmemop : forall k n, no_shmemop (@stack_remove.stack_free a k n).
Proof. intros; apply stack_free_f_no_shmemop. Qed.
Local Lemma stack_alloc_f_no_shmemop : forall fuel jump k n, no_shmemop (@stack_remove.stack_alloc_f a fuel jump k n).
Proof.
 induction fuel as [|fuel IH]; intros jump k n; cbn [stack_remove.stack_alloc_f]; [reflexivity|].
 destruct (n =? 0); [reflexivity|].
 destruct (n <=? stack_remove.max_stack_alloc); destruct jump; cbn [stack_remove.single_stack_alloc stack_remove.single_stack_free stack_remove.halt_inst no_shmemop]; rewrite ?IH; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_alloc_no_shmemop" *)
Theorem stack_alloc_no_shmemop : forall jump k n, no_shmemop (@stack_remove.stack_alloc a jump k n).
Proof. intros; apply stack_alloc_f_no_shmemop. Qed.
Local Lemma upshift_f_no_install : forall fuel k n, no_install (@stack_remove.upshift_f a fuel k n).
Proof.
 induction fuel as [|fuel IH]; intros k n; cbn [stack_remove.upshift_f]; [reflexivity|].
 destruct (n <=? stack_remove.max_stack_alloc); cbn [stack_remove.single_stack_alloc stack_remove.single_stack_free stack_remove.halt_inst no_install]; rewrite ?IH; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "upshift_no_install" *)
Theorem upshift_no_install : forall k n, no_install (@stack_remove.upshift a k n).
Proof. intros; apply upshift_f_no_install. Qed.
Local Lemma downshift_f_no_install : forall fuel k n, no_install (@stack_remove.downshift_f a fuel k n).
Proof.
 induction fuel as [|fuel IH]; intros k n; cbn [stack_remove.downshift_f]; [reflexivity|].
 destruct (n <=? stack_remove.max_stack_alloc); cbn [stack_remove.single_stack_alloc stack_remove.single_stack_free stack_remove.halt_inst no_install]; rewrite ?IH; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "downshift_no_install" *)
Theorem downshift_no_install : forall k n, no_install (@stack_remove.downshift a k n).
Proof. intros; apply downshift_f_no_install. Qed.
Local Lemma stack_free_f_no_install : forall fuel k n, no_install (@stack_remove.stack_free_f a fuel k n).
Proof.
 induction fuel as [|fuel IH]; intros k n; cbn [stack_remove.stack_free_f]; [reflexivity|].
 destruct (n =? 0); [reflexivity|].
 destruct (n <=? stack_remove.max_stack_alloc); cbn [stack_remove.single_stack_alloc stack_remove.single_stack_free stack_remove.halt_inst no_install]; rewrite ?IH; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_free_no_install" *)
Theorem stack_free_no_install : forall k n, no_install (@stack_remove.stack_free a k n).
Proof. intros; apply stack_free_f_no_install. Qed.
Local Lemma stack_alloc_f_no_install : forall fuel jump k n, no_install (@stack_remove.stack_alloc_f a fuel jump k n).
Proof.
 induction fuel as [|fuel IH]; intros jump k n; cbn [stack_remove.stack_alloc_f]; [reflexivity|].
 destruct (n =? 0); [reflexivity|].
 destruct (n <=? stack_remove.max_stack_alloc); destruct jump; cbn [stack_remove.single_stack_alloc stack_remove.single_stack_free stack_remove.halt_inst no_install]; rewrite ?IH; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_alloc_no_install" *)
Theorem stack_alloc_no_install : forall jump k n, no_install (@stack_remove.stack_alloc a jump k n).
Proof. intros; apply stack_alloc_f_no_install. Qed.

Local Lemma remove_no_shmemop_eq jump off k : forall p : prog a, no_shmemop (stack_remove.comp jump off k p) = no_shmemop p.
Proof.
 intros p; induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind.
 - destruct ret as [[p1 [lr [l1 l2]]]|]; destruct h as [[p2 [k1 k2]]|];
   cbn [stack_remove.comp no_shmemop]; try rewrite (Hr p1 _ eq_refl); try rewrite (Hh p2 _ eq_refl); reflexivity.
 - cbn [stack_remove.comp no_shmemop]; rewrite IH1,IH2; reflexivity.
 - cbn [stack_remove.comp no_shmemop]; rewrite IH1,IH2; reflexivity.
 - cbn [stack_remove.comp no_shmemop]; exact IH.
 - destruct p; cbn in Hp; try contradiction;
   cbn [stack_remove.comp stack_remove.copy_loop stack_remove.copy_each stack_remove.stack_store stack_remove.stack_load list_Seq no_shmemop];
   repeat match goal with |- context [if ?b then _ else _] => destruct b end;
   cbn [stack_remove.stack_store stack_remove.stack_load no_shmemop no_install];
   rewrite ?upshift_no_shmemop, ?downshift_no_shmemop, ?stack_free_no_shmemop, ?stack_alloc_no_shmemop; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_remove_comp_no_shmemop" *)
Theorem stack_remove_comp_no_shmemop : forall jump off k (p : prog a), no_shmemop p -> no_shmemop (stack_remove.comp jump off k p).
Proof. intros; rewrite remove_no_shmemop_eq; assumption. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_remove_prog_comp_no_shmemop" *)
Theorem stack_remove_prog_comp_no_shmemop : forall {K : Type} jump off k (n : K) (p : prog a),
 no_shmemop p -> no_shmemop (SND (stack_remove.prog_comp jump off k (n,p))).
Proof. intros; apply stack_remove_comp_no_shmemop; assumption. Qed.
Local Lemma remove_no_install_eq jump off k : forall p : prog a, no_install (stack_remove.comp jump off k p) = no_install p.
Proof.
 intros p; induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind.
 - destruct ret as [[p1 [lr [l1 l2]]]|]; destruct h as [[p2 [k1 k2]]|];
   cbn [stack_remove.comp no_install]; try rewrite (Hr p1 _ eq_refl); try rewrite (Hh p2 _ eq_refl); reflexivity.
 - cbn [stack_remove.comp no_install]; rewrite IH1,IH2; reflexivity.
 - cbn [stack_remove.comp no_install]; rewrite IH1,IH2; reflexivity.
 - cbn [stack_remove.comp no_install]; exact IH.
 - destruct p; cbn in Hp; try contradiction;
   cbn [stack_remove.comp stack_remove.copy_loop stack_remove.copy_each stack_remove.stack_store stack_remove.stack_load list_Seq no_install];
   repeat match goal with |- context [if ?b then _ else _] => destruct b end;
   cbn [stack_remove.stack_store stack_remove.stack_load no_shmemop no_install];
   rewrite ?upshift_no_install, ?downshift_no_install, ?stack_free_no_install, ?stack_alloc_no_install; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_remove_comp_no_install" *)
Theorem stack_remove_comp_no_install : forall jump off k (p : prog a), no_install p -> no_install (stack_remove.comp jump off k p).
Proof. intros; rewrite remove_no_install_eq; assumption. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_remove_prog_comp_no_install" *)
Theorem stack_remove_prog_comp_no_install : forall {K : Type} jump off k (n : K) (p : prog a),
 no_install p -> no_install (SND (stack_remove.prog_comp jump off k (n,p))).
Proof. intros; apply stack_remove_comp_no_install; assumption. Qed.

Local Lemma safety_map {K : Type} (P : prog a -> bool) (f : K * prog a -> K * prog a) ps :
 (forall n p, P p -> P (SND (f (n,p)))) ->
 EVERY (fun '(n,p) => P p) ps -> EVERY (fun '(n,p) => P p) (MAP f ps).
Proof.
 intros Hf H; apply EVERY_Forall; rewrite Forall_map.
 eapply Forall_impl; [|apply EVERY_Forall; exact H].
 intros [n p] Hp; pose proof (Hf n p Hp) as Hq; destruct (f (n,p)); exact Hq.
Qed.
Local Lemma safety_append (P : prog a -> bool) (xs ys : list (N * prog a)) :
 EVERY (fun '(n,p) => P p) xs -> EVERY (fun '(n,p) => P p) ys -> EVERY (fun '(n,p) => P p) (xs ++ ys).
Proof. intros; apply EVERY_Forall, Forall_app; split; apply EVERY_Forall; assumption. Qed.
Local Lemma gc_code_no_shmemop dc : no_shmemop (@stack_alloc.word_gc_code a dc).
Proof. unfold stack_alloc.word_gc_code. destruct (data_to_word.gc_kind dc) as [| |sizes]; try destruct sizes; cbn [stack_alloc.memcpy_code stack_alloc.clear_top_inst stack_alloc.word_gc_move_code stack_alloc.word_gc_move_list_code stack_alloc.word_gc_move_loop_code stack_alloc.word_gc_move_bitmap_code stack_alloc.word_gc_move_bitmaps_code stack_alloc.word_gc_move_roots_bitmaps_code stack_alloc.word_gen_gc_move_code stack_alloc.word_gen_gc_partial_move_code stack_alloc.word_gen_gc_move_bitmap_code stack_alloc.word_gen_gc_partial_move_bitmap_code stack_alloc.word_gen_gc_move_bitmaps_code stack_alloc.word_gen_gc_partial_move_bitmaps_code stack_alloc.word_gen_gc_move_roots_bitmaps_code stack_alloc.word_gen_gc_partial_move_roots_bitmaps_code stack_alloc.word_gen_gc_move_list_code stack_alloc.word_gen_gc_partial_move_list_code stack_alloc.word_gen_gc_move_data_code stack_alloc.word_gen_gc_partial_move_ref_list_code stack_alloc.word_gen_gc_partial_move_data_code stack_alloc.word_gen_gc_move_refs_code stack_alloc.word_gen_gc_move_loop_code stack_alloc.word_gc_partial_or_full stack_alloc.SetNewTrigger stack_alloc.word_gc_code no_shmemop list_Seq APPEND]; reflexivity. Qed.
Local Transparent stack_remove.init_code stack_remove.store_list_code.
Local Lemma stores_no_shmemop ad t (ls : list (word a + N)) : no_shmemop (stack_remove.store_list_code ad t ls).
Proof. induction ls as [|[w|r] ls IH]; cbn [stack_remove.store_list_code no_shmemop list_Seq]; rewrite ?IH; reflexivity. Qed.
Local Opaque stack_remove.store_list_code.
Local Lemma init_no_shmemop ggc mh k : no_shmemop (@stack_remove.init_code a ggc mh k).
Proof. unfold stack_remove.init_code; cbv zeta; cbn [no_shmemop list_Seq];
 unfold stack_remove.init_memory; cbn [no_shmemop list_Seq]; rewrite stores_no_shmemop; reflexivity. Qed.
Local Opaque stack_remove.init_code.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_rawcall_compile_no_shmemop" *)
Theorem stack_rawcall_compile_no_shmemop : forall ps : list (N * prog a),
 EVERY (fun '(n,p) => no_shmemop p) ps -> EVERY (fun '(n,p) => no_shmemop p) (stack_rawcall.compile ps).
Proof. intros; unfold stack_rawcall.compile; apply safety_map; [intros; apply stack_rawcall_comp_top_no_shmemop; assumption|assumption]. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_alloc_prog_comp_no_shmemop" *)
Theorem stack_alloc_prog_comp_no_shmemop : forall ps : list (N * prog a),
 EVERY (fun '(n,p) => no_shmemop p) ps -> EVERY (fun '(n,p) => no_shmemop p) (MAP stack_alloc.prog_comp ps).
Proof. intros; apply safety_map; [intros; apply stack_alloc_comp_no_shmemop; assumption|assumption]. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_alloc_compile_no_shmemop" *)
Theorem stack_alloc_compile_no_shmemop : forall dc (ps : list (N * prog a)),
 EVERY (fun '(n,p) => no_shmemop p) ps -> EVERY (fun '(n,p) => no_shmemop p) (stack_alloc.compile dc ps).
Proof.
 intros dc ps H; unfold stack_alloc.compile; apply safety_append; [|apply stack_alloc_prog_comp_no_shmemop; exact H].
 unfold stack_alloc.stubs; cbn [EVERY no_shmemop]; rewrite gc_code_no_shmemop; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_remove_prog_comp_no_shmemop_MAP" *)
Theorem stack_remove_prog_comp_no_shmemop_MAP : forall {K : Type} jump off sp (ps : list (K * prog a)),
 EVERY (fun '(n,p) => no_shmemop p) ps -> EVERY (fun '(n,p) => no_shmemop p) (MAP (stack_remove.prog_comp jump off sp) ps).
Proof. intros; apply safety_map; [intros; apply stack_remove_comp_no_shmemop; assumption|assumption]. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_remove_compile_no_shmemop" *)
Theorem stack_remove_compile_no_shmemop : forall jump off ggc mh sp loc (ps : list (K * prog a)),
 EVERY (fun '(n,p) => no_shmemop p) ps -> EVERY (fun '(n,p) => no_shmemop p) (stack_remove.compile jump off ggc mh sp loc ps).
Proof.
 intros jump off ggc mh sp loc ps H; unfold stack_remove.compile; apply safety_append; [|apply stack_remove_prog_comp_no_shmemop_MAP; exact H].
 unfold stack_remove.init_stubs; cbn [EVERY no_shmemop stack_remove.halt_inst]; rewrite init_no_shmemop; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_names_prog_comp_no_shmemop" *)
Theorem stack_names_prog_comp_no_shmemop : forall {K : Type} f (ps : list (K * prog a)),
 EVERY (fun '(n,p) => no_shmemop p) ps -> EVERY (fun '(n,p) => no_shmemop p) (MAP (stack_names.prog_comp f) ps).
Proof. intros; apply safety_map; [intros; apply stack_names_comp_no_shmemop; assumption|assumption]. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_names_compile_no_shmemop" *)
Theorem stack_names_compile_no_shmemop : forall {K : Type} f (ps : list (K * prog a)),
 EVERY (fun '(n,p) => no_shmemop p) ps -> EVERY (fun '(n,p) => no_shmemop p) (stack_names.compile f ps).
Proof. intros; apply stack_names_prog_comp_no_shmemop; assumption. Qed.
Local Lemma gc_code_no_install dc : no_install (@stack_alloc.word_gc_code a dc).
Proof. unfold stack_alloc.word_gc_code. destruct (data_to_word.gc_kind dc) as [| |sizes]; try destruct sizes; cbn [stack_alloc.memcpy_code stack_alloc.clear_top_inst stack_alloc.word_gc_move_code stack_alloc.word_gc_move_list_code stack_alloc.word_gc_move_loop_code stack_alloc.word_gc_move_bitmap_code stack_alloc.word_gc_move_bitmaps_code stack_alloc.word_gc_move_roots_bitmaps_code stack_alloc.word_gen_gc_move_code stack_alloc.word_gen_gc_partial_move_code stack_alloc.word_gen_gc_move_bitmap_code stack_alloc.word_gen_gc_partial_move_bitmap_code stack_alloc.word_gen_gc_move_bitmaps_code stack_alloc.word_gen_gc_partial_move_bitmaps_code stack_alloc.word_gen_gc_move_roots_bitmaps_code stack_alloc.word_gen_gc_partial_move_roots_bitmaps_code stack_alloc.word_gen_gc_move_list_code stack_alloc.word_gen_gc_partial_move_list_code stack_alloc.word_gen_gc_move_data_code stack_alloc.word_gen_gc_partial_move_ref_list_code stack_alloc.word_gen_gc_partial_move_data_code stack_alloc.word_gen_gc_move_refs_code stack_alloc.word_gen_gc_move_loop_code stack_alloc.word_gc_partial_or_full stack_alloc.SetNewTrigger stack_alloc.word_gc_code no_install list_Seq APPEND]; reflexivity. Qed.
Local Transparent stack_remove.init_code stack_remove.store_list_code.
Local Lemma stores_no_install ad t (ls : list (word a + N)) : no_install (stack_remove.store_list_code ad t ls).
Proof. induction ls as [|[w|r] ls IH]; cbn [stack_remove.store_list_code no_install list_Seq]; rewrite ?IH; reflexivity. Qed.
Local Opaque stack_remove.store_list_code.
Local Lemma init_no_install ggc mh k : no_install (@stack_remove.init_code a ggc mh k).
Proof. unfold stack_remove.init_code; cbv zeta; cbn [no_install list_Seq];
 unfold stack_remove.init_memory; cbn [no_install list_Seq]; rewrite stores_no_install; reflexivity. Qed.
Local Opaque stack_remove.init_code.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_rawcall_compile_no_install" *)
Theorem stack_rawcall_compile_no_install : forall ps : list (K * prog a),
 EVERY (fun '(n,p) => no_install p) ps -> EVERY (fun '(n,p) => no_install p) (stack_rawcall.compile ps).
Proof. intros; unfold stack_rawcall.compile; apply safety_map; [intros; apply stack_rawcall_comp_top_no_install; assumption|assumption]. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_alloc_prog_comp_no_install" *)
Theorem stack_alloc_prog_comp_no_install : forall ps : list (K * prog a),
 EVERY (fun '(n,p) => no_install p) ps -> EVERY (fun '(n,p) => no_install p) (MAP stack_alloc.prog_comp ps).
Proof. intros; apply safety_map; [intros; apply stack_alloc_comp_no_install; assumption|assumption]. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_alloc_compile_no_install" *)
Theorem stack_alloc_compile_no_install : forall dc (ps : list (K * prog a)),
 EVERY (fun '(n,p) => no_install p) ps -> EVERY (fun '(n,p) => no_install p) (stack_alloc.compile dc ps).
Proof.
 intros dc ps H; unfold stack_alloc.compile; apply safety_append; [|apply stack_alloc_prog_comp_no_install; exact H].
 unfold stack_alloc.stubs; cbn [EVERY no_install]; rewrite gc_code_no_install; reflexivity.
Qed.
Local Lemma stack_remove_prog_comp_no_install_MAP : forall jump off sp (ps : list (N * prog a)),
 EVERY (fun '(n,p) => no_install p) ps -> EVERY (fun '(n,p) => no_install p) (MAP (stack_remove.prog_comp jump off sp) ps).
Proof. intros; apply safety_map; [intros; apply stack_remove_comp_no_install; assumption|assumption]. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_remove_compile_no_install" *)
Theorem stack_remove_compile_no_install : forall jump off ggc mh sp loc (ps : list (N * prog a)),
 EVERY (fun '(n,p) => no_install p) ps -> EVERY (fun '(n,p) => no_install p) (stack_remove.compile jump off ggc mh sp loc ps).
Proof.
 intros jump off ggc mh sp loc ps H; unfold stack_remove.compile; apply safety_append; [|apply stack_remove_prog_comp_no_install_MAP; exact H].
 unfold stack_remove.init_stubs; cbn [EVERY no_install stack_remove.halt_inst]; rewrite init_no_install; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_names_prog_comp_no_install" *)
Theorem stack_names_prog_comp_no_install : forall {K : Type} f (ps : list (K * prog a)),
 EVERY (fun '(n,p) => no_install p) ps -> EVERY (fun '(n,p) => no_install p) (MAP (stack_names.prog_comp f) ps).
Proof. intros; apply safety_map; [intros; apply stack_names_comp_no_install; assumption|assumption]. Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_names_compile_no_install" *)
Theorem stack_names_compile_no_install : forall {K : Type} f (ps : list (K * prog a)),
 EVERY (fun '(n,p) => no_install p) ps -> EVERY (fun '(n,p) => no_install p) (stack_names.compile f ps).
Proof. intros; apply stack_names_prog_comp_no_install; assumption. Qed.

Local Definition no_share_line (ln : line a) := forall op re ad inst len, ln <> Asm (ShareMem op re ad) inst len.
Local Definition no_install_line (ln : line a) := forall w bytes l, ln <> LabAsm labLang.Install w bytes l.
Local Lemma safety_every (P : line a -> Prop) xs :
 EVERY (fun ln => bool_decide (P ln)) xs <-> Forall P xs.
Proof. change (EVERY (fun ln => bool_decide (P ln)) xs = true <-> Forall P xs); rewrite EVERY_Forall; split.
 - intro H; eapply Forall_impl; [|exact H]; intros ln Hl; exact (proj1 (bool_decide_spec (P ln)) Hl).
 - intro H; eapply Forall_impl; [|exact H]; intros ln Hl; exact (proj2 (bool_decide_spec (P ln)) Hl).
Qed.
Local Ltac safety_lines := cbn [FST andb]; rewrite ?append_Append, ?append_List; rewrite ?Forall_app;
 repeat split; try assumption; repeat constructor; unfold no_share_line, no_install_line; intros; discriminate.
Local Lemma flatten_no_shmemop_safe : forall p : prog a, forall t n m cs bs,
 no_shmemop p -> Forall no_share_line (append (FST (flatten t p n m cs bs))).
Proof.
 intros p; induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind; intros t n m cs bs H.
 - destruct ret as [[p1 [lr [l1 l2]]]|].
   + cbn [no_shmemop] in H; apply Bool.andb_true_iff in H as [H1 H2].
     pose proof (Hr p1 _ eq_refl false n m cs bs H1) as Hq1; cbn [flatten].
     destruct (flatten false p1 n m cs bs) as [q1 [nr1 m1]]; cbn [FST] in Hq1.
     destruct h as [[p2 [k1 k2]]|].
     * pose proof (Hh p2 _ eq_refl false n m1 cs bs H2) as Hq2;
       destruct (flatten false p2 n m1 cs bs) as [q2 [nr2 m2]]; cbn [FST] in Hq2;
       destruct dest; unfold compile_jump; safety_lines.
     * destruct dest; unfold compile_jump; safety_lines.
   + cbn [flatten]; destruct dest; unfold compile_jump; safety_lines.
 - cbn [no_shmemop] in H; apply Bool.andb_true_iff in H as [H1 H2];
   pose proof (IH1 false n m cs bs H1) as Hq1; cbn [flatten].
   destruct (flatten false p1 n m cs bs) as [q1 [nr1 m1]]; cbn [FST] in Hq1.
   pose proof (IH2 false n m1 cs bs H2) as Hq2;
   destruct (flatten false p2 n m1 cs bs) as [q2 [nr2 m2]]; cbn [FST] in Hq2;
   destruct t; safety_lines.
 - cbn [no_shmemop] in H; apply Bool.andb_true_iff in H as [H1 H2];
   pose proof (IH1 false n m cs bs H1) as Hq1; cbn [flatten].
   destruct (flatten false p1 n m cs bs) as [q1 [nr1 m1]]; cbn [FST] in Hq1.
   pose proof (IH2 false n m1 cs bs H2) as Hq2;
   destruct (flatten false p2 n m1 cs bs) as [q2 [nr2 m2]]; cbn [FST] in Hq2;
   destruct (is_Skip p1), (is_Skip p2), nr1,nr2; safety_lines.
 - pose proof (IH false n (m+2) (m::cs) ((m+1)::bs) H) as Hq;
   cbn [flatten]; destruct (flatten false p n (m+2) (m::cs) ((m+1)::bs)) as [q [nr m1]];
   cbn [FST] in Hq; safety_lines.
 - destruct p; cbn in Hp; try contradiction; cbn [no_shmemop] in H; try discriminate;
   cbn [flatten]; safety_lines.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_no_share_mem_inst" *)
Theorem flatten_no_share_mem_inst : forall t (p : prog a) n m cs bs,
 no_shmemop p -> EVERY (fun ln => bool_decide (forall op re ad inst len, ln <> Asm (ShareMem op re ad) inst len)) (append (FST (flatten t p n m cs bs))).
Proof. intros; apply safety_every; apply flatten_no_shmemop_safe; assumption. Qed.
Local Lemma flatten_no_install_safe : forall p : prog a, forall t n m cs bs,
 no_install p -> Forall no_install_line (append (FST (flatten t p n m cs bs))).
Proof.
 intros p; induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind; intros t n m cs bs H.
 - destruct ret as [[p1 [lr [l1 l2]]]|].
   + cbn [no_install] in H; apply Bool.andb_true_iff in H as [H1 H2].
     pose proof (Hr p1 _ eq_refl false n m cs bs H1) as Hq1; cbn [flatten].
     destruct (flatten false p1 n m cs bs) as [q1 [nr1 m1]]; cbn [FST] in Hq1.
     destruct h as [[p2 [k1 k2]]|].
     * pose proof (Hh p2 _ eq_refl false n m1 cs bs H2) as Hq2;
       destruct (flatten false p2 n m1 cs bs) as [q2 [nr2 m2]]; cbn [FST] in Hq2;
       destruct dest; unfold compile_jump; safety_lines.
     * destruct dest; unfold compile_jump; safety_lines.
   + cbn [flatten]; destruct dest; unfold compile_jump; safety_lines.
 - cbn [no_install] in H; apply Bool.andb_true_iff in H as [H1 H2];
   pose proof (IH1 false n m cs bs H1) as Hq1; cbn [flatten].
   destruct (flatten false p1 n m cs bs) as [q1 [nr1 m1]]; cbn [FST] in Hq1.
   pose proof (IH2 false n m1 cs bs H2) as Hq2;
   destruct (flatten false p2 n m1 cs bs) as [q2 [nr2 m2]]; cbn [FST] in Hq2;
   destruct t; safety_lines.
 - cbn [no_install] in H; apply Bool.andb_true_iff in H as [H1 H2];
   pose proof (IH1 false n m cs bs H1) as Hq1; cbn [flatten].
   destruct (flatten false p1 n m cs bs) as [q1 [nr1 m1]]; cbn [FST] in Hq1.
   pose proof (IH2 false n m1 cs bs H2) as Hq2;
   destruct (flatten false p2 n m1 cs bs) as [q2 [nr2 m2]]; cbn [FST] in Hq2;
   destruct (is_Skip p1), (is_Skip p2), nr1,nr2; safety_lines.
 - pose proof (IH false n (m+2) (m::cs) ((m+1)::bs) H) as Hq;
   cbn [flatten]; destruct (flatten false p n (m+2) (m::cs) ((m+1)::bs)) as [q [nr m1]];
   cbn [FST] in Hq; safety_lines.
 - destruct p; cbn in Hp; try contradiction; cbn [no_install] in H; try discriminate;
   cbn [flatten]; safety_lines.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_no_install" *)
Theorem flatten_no_install : forall t (p : prog a) n m cs bs,
 no_install p -> EVERY (fun ln => bool_decide (forall w bytes l, ln <> LabAsm labLang.Install w bytes l)) (append (FST (flatten t p n m cs bs))).
Proof. intros; apply safety_every; apply flatten_no_install_safe; assumption. Qed.

Local Lemma fetch_safe_cons (P : line a -> Prop) xs k ls :
 Forall P xs -> (forall pos ln, asm_fetch_aux pos ls = SOME ln -> P ln) ->
 forall pos ln, asm_fetch_aux pos (Section_ k xs :: ls) = SOME ln -> P ln.
Proof.
 intros Hp Hls; induction Hp as [|x xs Hx Hxs IH]; intros pos ln E.
 - apply (Hls pos ln); exact E.
 - cbn [asm_fetch_aux] in E; destruct (is_Label x); [apply (IH pos ln); exact E|].
   destruct (pos =? 0); [injection E as <-; exact Hx|apply (IH (pos-1) ln); exact E].
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "asm_fetch_aux_no_share_mem_inst_CONS" *)
Theorem asm_fetch_aux_no_share_mem_inst_CONS : forall (xs : list (line a)) k ls,
 EVERY (fun ln => bool_decide (forall op re ad inst len, ln <> Asm (ShareMem op re ad) inst len)) xs /\ labProps.no_share_mem_inst ls -> labProps.no_share_mem_inst (Section_ k xs :: ls).
Proof.
 intros xs k ls [Hp Hls] pos op re ad inst len E; apply safety_every in Hp.
 assert (Ht : forall pos ln, asm_fetch_aux pos ls = SOME ln -> no_share_line ln).
 { intros pos0 ln El op0 re0 ad0 inst0 len0 He; subst ln; exact (Hls pos0 op0 re0 ad0 inst0 len0 El). }
 pose proof (fetch_safe_cons no_share_line xs k ls Hp Ht pos _ E) as Hbad.
 exact (Hbad op re ad inst len eq_refl).
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "prog_to_section_no_share_mem_inst" *)
Theorem prog_to_section_no_share_mem_inst : forall ps : list (N * prog a),
 EVERY (fun '(n,p) => no_shmemop p) ps -> labProps.no_share_mem_inst (MAP prog_to_section ps).
Proof.
 induction ps as [|[n p] ps IH]; intros H; cbn [EVERY MAP] in H |- *.
 - unfold labProps.no_share_mem_inst; intros; discriminate.
 - apply Bool.andb_true_iff in H as [Hp Hps]; specialize (IH Hps).
   unfold prog_to_section; destruct (flatten true p n (stack_alloc.next_lab p 2) [] []) as [ls [nr m]] eqn:E.
   apply asm_fetch_aux_no_share_mem_inst_CONS; split; [|exact IH].
   apply safety_every; rewrite append_Append, append_List; apply Forall_app; split.
   + pose proof (flatten_no_shmemop_safe p true n (stack_alloc.next_lab p 2) [] [] Hp) as Hf.
     rewrite E in Hf; exact Hf.
   + constructor; [unfold no_share_line; intros; discriminate|constructor].
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "compile_no_share_mem_inst" *)
Theorem compile_no_share_mem_inst : forall sc dc mh sp off (ps : list (N * prog a)) ps',
 EVERY (fun '(n,p) => no_shmemop p) ps /\ stack_to_lab.compile sc dc mh sp off ps = ps' -> labProps.no_share_mem_inst ps'.
Proof.
 intros sc dc mh sp off ps ps' [H <-]; unfold stack_to_lab.compile; apply prog_to_section_no_share_mem_inst;
 apply stack_names_compile_no_shmemop; apply stack_remove_compile_no_shmemop; apply stack_alloc_compile_no_shmemop; apply stack_rawcall_compile_no_shmemop; exact H.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "compile_no_stubs_no_share_mem_inst" *)
Theorem compile_no_stubs_no_share_mem_inst : forall f jump off sp (ps : list (N * prog a)) ps',
 EVERY (fun '(n,p) => no_shmemop p) ps /\ stack_to_lab.compile_no_stubs f jump off sp ps = ps' -> labProps.no_share_mem_inst ps'.
Proof.
 intros f jump off sp ps ps' [H <-]; unfold stack_to_lab.compile_no_stubs; apply prog_to_section_no_share_mem_inst;
 apply stack_names_compile_no_shmemop; apply stack_remove_prog_comp_no_shmemop_MAP; apply stack_alloc_prog_comp_no_shmemop; exact H.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "asm_fetch_aux_no_install_CONS" *)
Theorem asm_fetch_aux_no_install_CONS : forall (xs : list (line a)) k ls,
 EVERY (fun ln => bool_decide (forall w bytes l, ln <> LabAsm labLang.Install w bytes l)) xs /\ labProps.no_install ls -> labProps.no_install (Section_ k xs :: ls).
Proof.
 intros xs k ls [Hp Hls] pos w bytes l E; apply safety_every in Hp.
 assert (Ht : forall pos ln, asm_fetch_aux pos ls = SOME ln -> no_install_line ln).
 { intros pos0 ln El w0 bytes0 l0 He; subst ln; exact (Hls pos0 w0 bytes0 l0 El). }
 pose proof (fetch_safe_cons no_install_line xs k ls Hp Ht pos _ E) as Hbad.
 exact (Hbad w bytes l eq_refl).
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "prog_to_section_no_install" *)
Theorem prog_to_section_no_install : forall ps : list (N * prog a),
 EVERY (fun '(n,p) => no_install p) ps -> labProps.no_install (MAP prog_to_section ps).
Proof.
 induction ps as [|[n p] ps IH]; intros H; cbn [EVERY MAP] in H |- *.
 - unfold labProps.no_install; intros; discriminate.
 - apply Bool.andb_true_iff in H as [Hp Hps]; specialize (IH Hps).
   unfold prog_to_section; destruct (flatten true p n (stack_alloc.next_lab p 2) [] []) as [ls [nr m]] eqn:E.
   apply asm_fetch_aux_no_install_CONS; split; [|exact IH].
   apply safety_every; rewrite append_Append, append_List; apply Forall_app; split.
   + pose proof (flatten_no_install_safe p true n (stack_alloc.next_lab p 2) [] [] Hp) as Hf.
     rewrite E in Hf; exact Hf.
   + constructor; [unfold no_install_line; intros; discriminate|constructor].
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_to_lab_compile_no_install" *)
Theorem stack_to_lab_compile_no_install : forall sc dc mh sp off (ps : list (N * prog a)) ps',
 EVERY (fun '(n,p) => no_install p) ps /\ stack_to_lab.compile sc dc mh sp off ps = ps' -> labProps.no_install ps'.
Proof.
 intros sc dc mh sp off ps ps' [H <-]; unfold stack_to_lab.compile; apply prog_to_section_no_install;
 apply stack_names_compile_no_install; apply stack_remove_compile_no_install; apply stack_alloc_compile_no_install; apply stack_rawcall_compile_no_install; exact H.
Qed.
End Safety.

From Galette.cakeml.compiler.backend.proofs Require Import data_to_word_gcProof.
From Galette.cakeml.compiler.backend.proofs.word_to_stackProof Require Import comp_semantics.
From Galette.cakeml.compiler.backend Require Import wordConvs.

Import data_to_word (max_heap_limit, gc_kind).
Import stack_removeProof (init_prop, word_list_exists_ADD, word_list_exists_thm, fun2set_EMPTY_eq).
Import wordSem (position, space_left, buffer_buffer, mk_buffer).
Import word_gcFunctions (word_gc_fun).

(** ** GC and word-to-stack initialization invariants *)
Section InitDependencies.
Context {a : N} {c ffi_t : Type}.
Local Opaque stackSem.evaluate.
Local Lemma init_store_from_prop gen mh dsp lim (s : stackSem.state a c ffi_t) dc :
 mh = 2 * max_heap_limit a dc - 1 -> gen = is_gen_gc (gc_kind dc) ->
 init_prop gen mh dsp lim s ->
 init_store_ok dc (stackSem.store s \\ Handler) (stackSem.memory s) (stackSem.mdomain s) (stackSem.code_buffer s) (stackSem.data_buffer s).
Proof.
 intros HM HG (curr & other & bm & len & HP).
 unfold init_store_ok; exists len, curr.
 unfold init_prop in *.
 repeat rewrite DOMSUB_FLOOKUP_THM.
 repeat match goal with |- context [decide ?P] => destruct (decide P); try discriminate end.
 destruct HP as (Hcurr & Hnext & Htrig & Hend & Hother & Hbm & Hlen & Hprog & Halloc & Hglob & Hgreal & Hhand & Hgen & Hcb & Hce & Hbb & Hbe & Hrest).
 destruct Hrest as (Hlim & Hcb0 & Hdb0 & Hus & Hst & Hr & Hb & Hstk & HotherEq & Hal & Hlast & Hspace & HstackBound & Hheap & Hmem).
 subst other gen; rewrite <- word_list_exists_ADD in Hmem.
 repeat split; try assumption; try lia.
 - congruence.
 - destruct (gc_kind dc); cbn [is_gen_gc] in Htrig; exact Htrig.
 - rewrite Hlen; f_equal; f_equal; apply WORD_MULT_COMM.
Qed.


Local Lemma lookup_zero_list : forall ns (fm : fmap store_name (word_loc a)) k,
 FLOOKUP fm k = SOME (Word (n2w 0 : word a)) \/ In k ns ->
 FLOOKUP (fm |++ MAP (fun x => (x, Word (n2w 0 : word a))) ns) k = SOME (Word (n2w 0 : word a)).
Proof.
 induction ns as [|x ns IH]; intros fm k H; [cbn in H; tauto|].
 cbn [MAP map] in *; change (FLOOKUP ((fm |+ (x, Word (n2w 0 : word a))) |++ MAP (fun x => (x, Word (n2w 0 : word a))) ns) k = SOME (Word (n2w 0 : word a))).
 apply IH; destruct H as [H|[H|H]].
 - left; rewrite FLOOKUP_UPDATE; destruct (decide (x=k)); auto.
 - subst k; left; rewrite FLOOKUP_UPDATE; destruct (decide (x=x)); [reflexivity|contradiction].
 - right; exact H.
Qed.
Local Lemma init_store_zero dc (m : word a -> word_loc a) :
 init_store_ok dc
 ((FEMPTY |++ MAP (fun x => (x, Word (n2w 0 : word a))) (CurrHeap :: stack_remove.store_list)) \\ Handler)
 m EMPTY (mk_buffer (n2w 0) [] 0 : buffer a 8) (mk_buffer (n2w 0) [] 0 : buffer a a).
Proof.
 unfold init_store_ok; exists 0, (n2w 0).
 cbn [position space_left buffer_buffer]; rewrite !N.add_0_r.
 assert (Hmul : ((bytes_in_word : word a) * n2w 0 = n2w 0)%w) by stack_removeProof.wring.
 rewrite Hmul; repeat rewrite WORD_ADD_0; try reflexivity.
 assert (Hlookup : forall k, In k (CurrHeap :: stack_remove.store_list) -> k <> Handler ->
   FLOOKUP ((FEMPTY |++ MAP (fun x => (x, Word (n2w 0 : word a))) (CurrHeap :: stack_remove.store_list)) \\ Handler) k = SOME (Word (n2w 0 : word a))).
 { intros k HK Hk; rewrite DOMSUB_FLOOKUP_THM; destruct (decide (Handler = k)); [congruence|].
   apply lookup_zero_list; right; exact HK. }
 repeat rewrite Hlookup by (unfold stack_remove.store_list; cbn [In]; intuition discriminate).
 repeat split; try reflexivity; try lia.
 - destruct (gc_kind dc); reflexivity.
 - rewrite (proj1 (word_list_exists_thm (n2w 0 : word a) 0)).
   rewrite fun2set_EMPTY_eq. reflexivity.
Qed.
Local Lemma init_store_any dc mh bm dsp co jump off sp cd (s : stackSem.state a c ffi_t) :
 mh = 2 * max_heap_limit a dc - 1 ->
 let t := stack_removeProof.make_init_any (is_gen_gc (gc_kind dc)) mh bm dsp co jump off sp cd s in
 init_store_ok dc (stackSem.store t \\ Handler) (stackSem.memory t) (stackSem.mdomain t)
 (stackSem.code_buffer t) (stackSem.data_buffer t).
Proof.
 intros HM; cbv zeta; unfold stack_removeProof.make_init_any.
 destruct (stack_removeProof.make_init_opt _ _ _ _ _ _ _ _ _ _) as [t|] eqn:ET.
 - unfold stack_removeProof.make_init_opt in ET.
   destruct (stackSem.evaluate _) as [[r|] t0]; [discriminate|].
   destruct (classical_dec _) as [HP|HP]; [|discriminate].
   injection ET as <-; eapply init_store_from_prop; [exact HM|reflexivity|exact HP].
 - apply init_store_zero.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "IMP_init_store_ok" *)
Theorem IMP_init_store_ok : forall max_heap c1 fmis xxx stack_conf sp offset bitmaps code
 (s : labSem.state a c ffi_t) save_regs data_sp coracle,
 max_heap = 2 * max_heap_limit a c1 - 1 /\
 (fmis,xxx) = full_make_init stack_conf c1 max_heap sp offset bitmaps code s save_regs data_sp coracle ->
 init_store_ok c1 (stackSem.store fmis \\ Handler) (stackSem.memory fmis) (stackSem.mdomain fmis)
 (stackSem.code_buffer fmis) (stackSem.data_buffer fmis).
Proof.
 intros mh dc fmis xxx sc sp off bm cd s sr dsp co [HM H].
 unfold full_make_init in H; cbv zeta in H.
 apply (f_equal fst) in H; cbn [fst] in H; subst fmis.
 unfold stack_allocProof.make_init.
 cbn [stackSem.store stackSem.memory stackSem.mdomain stackSem.code_buffer stackSem.data_buffer
 stackSem.set_compile_oracle stackSem.set_compile stackSem.set_gc_fun stackSem.set_use_stack stackSem.set_use_alloc stackSem.set_code].
 apply init_store_any; exact HM.
Qed.

Local Lemma drop_last_one : forall (xs : list (word_loc a)) n,
 LENGTH xs = N.succ n -> DROP n xs = [LAST xs].
Proof.
 induction xs as [|x xs IH]; intros n HL; [rewrite LENGTH_length in HL; cbn in HL; lia|].
 destruct xs as [|y ys].
 - assert (n=0) by (rewrite LENGTH_length in HL; cbn in HL; lia); subst; reflexivity.
 - assert (HN : n <> 0) by (rewrite LENGTH_length in HL; cbn in HL; lia).
   cbn [DROP]; rewrite (proj2 (N.eqb_neq n 0) HN).
   cbn [LAST]; apply IH; rewrite !LENGTH_length in HL |- *; cbn [length] in HL |- *; rewrite !Nat2N.inj_succ in HL |- *; lia.
Qed.
Local Lemma init_state_from_prop (ac : asm_config a) k dc cd wo so
 (s : stackSem.state a c ffi_t) gen mh dsp lim tl :
 4 < k -> good_dimindex a -> init_prop gen mh dsp lim s ->
 stackSem.bitmaps s = n2w 4 :: tl -> space_left (stackSem.data_buffer s) = dsp ->
 (forall n, let '((bm0,cfg),progs) := wo n in
  EVERY (fun y => post_alloc_conventions k (SND (SND y))) progs /\
  EVERY (fun y => flat_exp_conventions (SND (SND y))) progs /\
  EVERY (fun y => negb (wordLang.raise_stub_location =? FST y)) progs /\
  EVERY (fun y => negb (wordLang.store_consts_stub_location =? FST y)) progs /\
  (n = 0 -> bm0 = LENGTH (stackSem.bitmaps s))) ->
 so = (fun n => let '((bm0,cfg),progs) := wo n in
  let '(progs,(fs,bm)) := word_to_stack.compile_word_to_stack ac false k progs (Nil,bm0) in
  (cfg,(progs,append (FST bm)))) ->
 comp_semantics.init_state_ok ac k (stack_allocProof.make_init dc cd so s) wo.
Proof.
 intros HK HG HP HB HD HO HS; unfold init_prop in HP.
 destruct HP as (curr & other & bm & len & HP).
 destruct HP as (Hcurr & Hnext & Htrig & Hend & Hother & Hbm & Hlen & Hprog & Halloc & Hglob & Hgreal & Hhand & Hgen & Hcb & Hce & Hbb & Hbe & Hrest).
 destruct Hrest as (Hlim & Hcb0 & Hdb0 & Hus & Hst & Hr & Hb & Hstk & HotherEq & Hal & Hlast & Hspace & HstackBound & Hheap & Hmem).
 unfold stack_allocProof.make_init, comp_semantics.init_state_ok.
 cbn [stackSem.store stackSem.memory stackSem.mdomain stackSem.code_buffer stackSem.data_buffer
 stackSem.set_compile_oracle stackSem.set_compile stackSem.set_gc_fun stackSem.set_use_stack stackSem.set_use_alloc stackSem.set_code
 stackSem.use_stack stackSem.use_alloc stackSem.use_store stackSem.gc_fun stackSem.compile_oracle stackSem.bitmaps
 stackSem.regs stackSem.stack stackSem.stack_space].
 rewrite Hdb0, HD; cbn [LENGTH length]; repeat match goal with |- _ /\ _ => split end; try assumption; try lia; try reflexivity.
 - unfold good_dimindex in HG; unfold dimindex in *; lia.
 - apply data_to_word_gcProof.gc_fun_ok_word_gc_fun.
 - rewrite HB; cbn [isPREFIX]; apply andb_true_intro; split; [apply bool_decide_spec; reflexivity|reflexivity].
 - rewrite (drop_last_one _ _ Hspace), Hlast; reflexivity.
 - unfold pred_set.IN, FDOM; rewrite Hhand; discriminate.
Qed.


Local Lemma init_state_opt (ac : asm_config a) k dc cd wo so gen mh bm tl dsp co jump off sp code0
 (s : stackSem.state a c ffi_t) t :
 4 < k -> good_dimindex a -> bm = n2w 4 :: tl ->
 (forall n, let '((bm0,cfg),progs) := wo n in
  EVERY (fun y => post_alloc_conventions k (SND (SND y))) progs /\
  EVERY (fun y => flat_exp_conventions (SND (SND y))) progs /\
  EVERY (fun y => negb (wordLang.raise_stub_location =? FST y)) progs /\
  EVERY (fun y => negb (wordLang.store_consts_stub_location =? FST y)) progs /\
  (n = 0 -> bm0 = LENGTH bm)) ->
 so = (fun n => let '((bm0,cfg),progs) := wo n in
  let '(progs,(fs,bm)) := word_to_stack.compile_word_to_stack ac false k progs (Nil,bm0) in
  (cfg,(progs,append (FST bm)))) ->
 stack_removeProof.make_init_opt gen mh bm dsp co jump off sp code0 s = SOME t ->
 comp_semantics.init_state_ok ac k (stack_allocProof.make_init dc cd so t) wo.
Proof.
 intros HK HG HB HO HS ET; unfold stack_removeProof.make_init_opt in ET.
 destruct (stackSem.evaluate _) as [[r|] s0]; [discriminate|].
 destruct (classical_dec _) as [HP|HP]; [|discriminate].
 injection ET as <-; eapply init_state_from_prop; try eassumption; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "IMP_init_state_ok" *)
Theorem IMP_init_state_ok : forall (ac : asm_config a) kkk (bitmaps : list (word a)) t
 word_oracle stack_oracle scc dc max_heap stk stoff p6 (lab_st : labSem.state a c ffi_t) save_regs data_sp fmis xxx,
 4 < kkk /\ bitmaps = n2w 4 :: t /\ good_dimindex a /\
 (forall n, let '((bm0,cfg),progs) := word_oracle n in
  EVERY (fun y => post_alloc_conventions kkk (SND (SND y))) progs /\
  EVERY (fun y => flat_exp_conventions (SND (SND y))) progs /\
  EVERY (fun y => negb (wordLang.raise_stub_location =? FST y)) progs /\
  EVERY (fun y => negb (wordLang.store_consts_stub_location =? FST y)) progs /\
  (n = 0 -> bm0 = LENGTH bitmaps)) /\
 stack_oracle = (fun n => let '((bm0,cfg),progs) := word_oracle n in
  let '(progs,(fs,bm)) := word_to_stack.compile_word_to_stack ac false kkk progs (Nil,bm0) in
  (cfg,(progs,append (FST bm)))) /\
 full_make_init scc dc max_heap stk stoff bitmaps p6 lab_st save_regs data_sp stack_oracle = (fmis,SOME xxx) ->
 comp_semantics.init_state_ok ac kkk fmis word_oracle.
Proof.
 intros ac k bm tl wo so sc dc mh stk off p6 lab_st sr dsp fmis xxx (HK & Hbm & Hdim & HO & HS & HI).
 unfold full_make_init in HI; cbv zeta in HI.
 pose proof (f_equal snd HI) as ET; cbn [snd] in ET.
 pose proof (f_equal fst HI) as HF; cbn [fst] in HF; rewrite <- HF.
 unfold stack_removeProof.make_init_any; rewrite ET.
 eapply init_state_opt; eassumption.
Qed.

End InitDependencies.
