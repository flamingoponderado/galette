(** * CakeML [stack_allocProof]: correctness of [stack_alloc]

    Port of [cakeml/compiler/backend/proofs/stack_allocProofScript.sml].

    Notes:
    - HOL's [s with f := v] is [set_f v s] ([stackSem]); HOL tuples nest to
      the right ([(a,b,c)] is [(a, (b, c))]); HOL's [ARB] is [Base.ARB].
    - HOL's boolean lambdas [λ(l1,l2). l1 = n ∧ ...] under [EVERY] are
      boolean functions ([=?], [negb]); HOL conditions mixing a [Prop] and a
      boolean ([if word_gc_fun_assum conf s /\ c then ...]) use [⌜_⌝] and
      [andb].
    - HOL statements quantifying a vacuous variable omit it:
      [next_lab_EQ_MAX]'s [n], [extract_labels_next_lab]'s and
      [stack_alloc_lab_pres]'s [aux], the [a1] of the [*_bitmap(s)_code_thm]s,
      [*_roots_bitmaps_code_thm]s and [word_gc_move_list_code_thm], the
      existential [r9] of [word_gc_move_roots_bitmaps_code_thm] (register 9
      is [Word 0w]), [r2a2 ib1 pb1 c1 ib2 pb2] of
      [word_gen_gc_partial_move_ref_list_code_thm] and the existential
      [t0 t1] of [word_gen_gc_partial_move_data_code_thm].  HOL's free
      variables ([conf], [init], [gs], [rs], [compile_rest], [anything], ...)
      are quantified explicitly.
    - HOL's recursions on a word or a [num] counter (the [*_code_thm]s proved
      by [Induct], [recInduct bit_length_ind] or [completeInduct_on]) are
      proved by Galette-only [*_n] / [*_f] lemmas by induction on a bound or
      on the fuel of the [word_gcFunctions] definitions.
    - The two HOL theorems named [word_gc_fun_thm] and [gc_thm] (one for the
      simple and one for the generational collector) are
      [word_gc_fun_thm_Simple]/[word_gc_fun_thm_Gen] and
      [gc_thm_Simple]/[gc_thm_Gen]; HOL's arithmetic normal forms
      ([-1w * x + y]) are kept in their statements.
    - [comp_correct_gen]/[compile_semantics_gen] (Galette-only) prove
      [comp_correct]/[compile_semantics] for the state translation [tr]
      under [alloc_ok], which [alloc_ok_holds] discharges from
      [alloc_correct].
    - Not ported (HOL [val] bindings, not stored theorems): [nine_less],
      [tac], [tac1], [word_gc_fun_lemma], [gc_lemma], [kind], the
      [*_bitmaps_Loc] conversions and [comp_correct_thm] (an instance of
      [comp_correct]).  [map_bitmap_APPEND_APPEND] (a [Q.prove] value) is an
      untagged lemma. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words byte alignment.
From Galette.HOL.src.n_bit.words Require Import lemmas fcp_defs.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist.
From Galette.HOL.src.finite_maps Require sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang data_to_word.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend.semantics Require wordSem.
From Galette.cakeml.compiler.backend.semantics Require Import stackSem stackProps.
From Galette.cakeml.compiler.backend Require Import stack_alloc.
From Galette.cakeml.compiler.backend.proofs Require Import word_gcFunctions.
Import wordLang (word_loc, Word, Loc).
Import sptree (spt, LN, lookup, domain, fromAList, toAList, insert, union, subspt).
Open Scope N_scope.

(** ** Syntactic properties *)

Section Syntax.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "next_lab_EQ_MAX" *)
Theorem next_lab_EQ_MAX : forall (q : prog a) aux, next_lab q aux = MAX aux (next_lab q 0).
Proof.
  enough (G : forall (q : prog a) aux, next_lab q aux = N.max aux (next_lab q 0))
    by (intros q aux; rewrite MAX_max; apply G).
  intros q; induction q as [ret dest h Hr Hh|p1 p2 IH1 IH2|c0 r ri p1 p2 IH1 IH2|p IH|p Hp]
    using prog_nested_ind; intros aux.
  - destruct ret as [[p1 [lr [l1 l2]]]|]; destruct h as [[p2 [k1 k2]]|]; cbn [next_lab];
      rewrite ?MAX_max;
      repeat match goal with
             | H : forall p1 x, Some (?q, ?y) = Some (p1, x) -> _ |- _ =>
                 specialize (H q y eq_refl)
             | H : forall p2 x, None = Some (p2, x) -> _ |- _ => clear H
             end;
      repeat match goal with
             | H : forall aux, next_lab ?q aux = _ |- context [next_lab ?q ?x] =>
                 lazymatch x with 0 => fail | _ => rewrite (H x) end
             end; lia.
  - cbn [next_lab]. rewrite (IH1 (next_lab p2 aux)), (IH1 (next_lab p2 0)), (IH2 aux); lia.
  - cbn [next_lab]. rewrite (IH1 (next_lab p2 aux)), (IH1 (next_lab p2 0)), (IH2 aux); lia.
  - cbn [next_lab]. rewrite (IH aux); lia.
  - destruct p; try contradiction; cbn [next_lab]; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "MAX_SIMP" *)
Local Theorem MAX_SIMP : forall n m, MAX n (MAX n m) = MAX n m.
Proof. intros n m; rewrite !MAX_max; lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "next_lab_thm" *)
Theorem next_lab_thm : forall (p : prog a),
  next_lab p 2 =
  match p with
  | Seq p1 p2 => MAX (next_lab p1 2) (next_lab p2 2)
  | If _ _ _ p1 p2 => MAX (next_lab p1 2) (next_lab p2 2)
  | Loop p => next_lab p 2
  | Call None _ None => 2
  | Call None _ (Some (_, (_, l2))) => MAX (l2 + 2) 2
  | Call (Some (p, (_, (_, l2)))) _ None => MAX (next_lab p 2) (l2 + 2)
  | Call (Some (p, (_, (_, l2)))) _ (Some (p', (_, l3))) =>
      MAX (MAX (next_lab p 2) (next_lab p' 2)) (MAX l2 l3 + 2)
  | _ => 2
  end.
Proof.
  intros p; destruct p; cbn [next_lab]; try reflexivity;
    try (destruct o as [[p1 [lr [l1 l2]]]|]; destruct o0 as [[p2 [k1 k2]]|]; cbn [next_lab]);
    repeat match goal with
           | |- context [next_lab ?q ?x] =>
               lazymatch x with 0 => fail | _ => rewrite (next_lab_EQ_MAX q x) end
           end;
    rewrite ?MAX_max; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "extract_labels_next_lab" *)
Theorem extract_labels_next_lab : forall (p : prog a) e,
  MEM e (extract_labels p) -> SND e < next_lab p 2.
Proof.
  intros p; induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|c0 r ri p1 p2 IH1 IH2|p IH|p Hp]
    using prog_nested_ind; intros e He; unfold is_true in He; rewrite MEM_In in He;
    rewrite next_lab_thm; rewrite ?MAX_max.
  - destruct ret as [[p1 [lr [l1 l2]]]|]; [|contradiction].
    specialize (Hr p1 _ eq_refl).
    destruct h as [[p2 [k1 k2]]|]; cbn [extract_labels app] in He; cbn beta iota; rewrite ?MAX_max.
    + specialize (Hh p2 _ eq_refl).
      destruct He as [<-|[<-|He]]; cbn [SND fst snd]; [lia|lia|].
      apply in_app_iff in He as [He|He].
      * specialize (Hr e); unfold is_true in Hr; rewrite MEM_In in Hr; specialize (Hr He); lia.
      * specialize (Hh e); unfold is_true in Hh; rewrite MEM_In in Hh; specialize (Hh He); lia.
    + destruct He as [<-|He]; cbn [SND fst snd]; [lia|].
      specialize (Hr e); unfold is_true in Hr; rewrite MEM_In in Hr; specialize (Hr He); lia.
  - cbn [extract_labels] in He; apply in_app_iff in He as [He|He];
      [specialize (IH1 e)|specialize (IH2 e)]; unfold is_true in *; rewrite MEM_In in *;
      [specialize (IH1 He)|specialize (IH2 He)]; lia.
  - cbn [extract_labels] in He; apply in_app_iff in He as [He|He];
      [specialize (IH1 e)|specialize (IH2 e)]; unfold is_true in *; rewrite MEM_In in *;
      [specialize (IH1 He)|specialize (IH2 He)]; lia.
  - cbn [extract_labels] in He; specialize (IH e); unfold is_true in IH; rewrite MEM_In in IH;
      exact (IH He).
  - destruct p; try contradiction; cbn [extract_labels] in He; contradiction.
Qed.

Local Lemma NoDup_app_iff {A} (l1 l2 : list A) :
  NoDup (l1 ++ l2) <-> NoDup l1 /\ NoDup l2 /\ (forall x, In x l1 -> In x l2 -> False).
Proof.
  split.
  - intros H; split; [eapply NoDup_app_remove_r; exact H|split; [eapply NoDup_app_remove_l; exact H|]].
    induction l1 as [|y l1 IH]; [intros x []|]. cbn in H; inversion H as [|? ? Hn Hd]; subst.
    intros x [<-|Hx] Hx2; [apply Hn, in_app_iff; right; exact Hx2|exact (IH Hd x Hx Hx2)].
  - intros (H1 & H2 & H3); apply NoDup_app; [exact H1|exact H2|intros x Hx Hx2; exact (H3 x Hx Hx2)].
Qed.

(** Galette-only: [stack_alloc_lab_pres] with [Prop] lists. *)
Local Lemma lab_pres_aux n : forall (p : prog a) nl,
  Forall (fun '(l1, l2) => l1 = n /\ l2 <> 0 /\ l2 <> 1) (extract_labels p) ->
  NoDup (extract_labels p) -> next_lab p 2 <= nl ->
  Forall (fun '(l1, l2) => l1 = n /\ l2 <> 0 /\ l2 <> 1) (extract_labels (fst (comp n nl p))) /\
  NoDup (extract_labels (fst (comp n nl p))) /\
  (forall lab, In lab (extract_labels (fst (comp n nl p))) ->
     In lab (extract_labels p) \/ (nl <= SND lab /\ SND lab < snd (comp n nl p))) /\
  nl <= snd (comp n nl p).
Proof.
  assert (Hnl : forall (q : prog a) e, In e (extract_labels q) -> SND e < next_lab q 2).
  { intros q e He; apply extract_labels_next_lab; unfold is_true; rewrite MEM_In; exact He. }
  intros p; induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|c0 r ri p1 p2 IH1 IH2|p IH|p Hp]
    using prog_nested_ind; intros nl HF HD HN; rewrite next_lab_thm in HN.
  - destruct ret as [[p1 [lr [l1 l2]]]|].
    2:{ cbn [comp fst snd extract_labels]. repeat split; try (intros lb [] ; fail); try constructor; lia. }
    specialize (Hr p1 _ eq_refl).
    destruct h as [[p2 [k1 k2]]|]; cbn beta iota in HN; rewrite ?MAX_max in HN;
      cbn [comp]; cbn [extract_labels app] in HF, HD |- *.
    + specialize (Hh p2 _ eq_refl).
      destruct (comp n nl p1) as [q1 m1] eqn:E1.
      destruct (comp n m1 p2) as [q2 m2] eqn:E2. cbn [fst snd extract_labels app].
      inversion HF as [|? ? Hl1 HF1]; subst. inversion HF1 as [|? ? Hk1 HF2]; subst.
      apply Forall_app in HF2 as [HFp1 HFp2].
      inversion HD as [|? ? Hn1 HD1]; subst. inversion HD1 as [|? ? Hn2 HD2]; subst.
      pose proof (proj1 (NoDup_app_iff _ _) HD2) as (HDp1 & HDp2 & Hdis).
      destruct (Hr nl HFp1 HDp1 ltac:(lia)) as (A1 & B1 & C1 & D1). rewrite E1 in A1, B1, C1, D1.
      cbn [fst snd] in A1, B1, C1, D1.
      destruct (Hh m1 HFp2 HDp2 ltac:(lia)) as (A2 & B2 & C2 & D2). rewrite E2 in A2, B2, C2, D2.
      cbn [fst snd] in A2, B2, C2, D2.
      repeat split; try lia.
      * constructor; [exact Hl1|constructor; [exact Hk1|apply Forall_app; split; assumption]].
      * constructor.
        { intros Hin. cbn in Hin. destruct Hin as [Hin|Hin]; [apply Hn1; left; exact Hin|].
          apply in_app_iff in Hin as [Hin|Hin].
          - destruct (C1 _ Hin) as [Hin'|[Hle _]]; [apply Hn1; right; apply in_app_iff; left; exact Hin'|cbn in Hle; lia].
          - destruct (C2 _ Hin) as [Hin'|[Hle _]]; [apply Hn1; right; apply in_app_iff; right; exact Hin'|cbn in Hle; lia]. }
        constructor.
        { intros Hin. apply in_app_iff in Hin as [Hin|Hin].
          - destruct (C1 _ Hin) as [Hin'|[Hle _]]; [apply Hn2; apply in_app_iff; left; exact Hin'|cbn in Hle; lia].
          - destruct (C2 _ Hin) as [Hin'|[Hle _]]; [apply Hn2; apply in_app_iff; right; exact Hin'|cbn in Hle; lia]. }
        apply NoDup_app_iff; split; [exact B1|split; [exact B2|]].
        intros x Hx1 Hx2.
        destruct (C1 _ Hx1) as [Hy1|[Hy1 Hy1']], (C2 _ Hx2) as [Hy2|[Hy2 Hy2']].
        -- exact (Hdis _ Hy1 Hy2).
        -- pose proof (Hnl _ _ Hy1); lia.
        -- pose proof (Hnl _ _ Hy2); lia.
        -- lia.
      * intros lb Hin. cbn in Hin. destruct Hin as [<-|[<-|Hin]]; [left; left; reflexivity|left; right; left; reflexivity|].
        apply in_app_iff in Hin as [Hin|Hin].
        -- destruct (C1 _ Hin) as [H'|H']; [left; right; right; apply in_app_iff; left; exact H'|right; lia].
        -- destruct (C2 _ Hin) as [H'|H']; [left; right; right; apply in_app_iff; right; exact H'|right; lia].
    + destruct (comp n nl p1) as [q1 m1] eqn:E1. cbn [fst snd extract_labels app].
      inversion HF as [|? ? Hl1 HFp1]; subst.
      inversion HD as [|? ? Hn1 HDp1]; subst.
      destruct (Hr nl HFp1 HDp1 ltac:(lia)) as (A1 & B1 & C1 & D1). rewrite E1 in A1, B1, C1, D1.
      cbn [fst snd] in A1, B1, C1, D1.
      repeat split; try lia.
      * constructor; assumption.
      * constructor; [|exact B1]. intros Hin.
        destruct (C1 _ Hin) as [Hin'|[Hle _]]; [exact (Hn1 Hin')|cbn in Hle; lia].
      * intros lb Hin. destruct Hin as [<-|Hin]; [left; left; reflexivity|].
        destruct (C1 _ Hin) as [H'|H']; [left; right; exact H'|right; lia].
  - cbn [comp]. destruct (comp n nl p1) as [q1 m1] eqn:E1. destruct (comp n m1 p2) as [q2 m2] eqn:E2.
    cbn [fst snd extract_labels] in *. rewrite MAX_max in HN.
    apply Forall_app in HF as [HFp1 HFp2].
    pose proof (proj1 (NoDup_app_iff _ _) HD) as (HDp1 & HDp2 & Hdis).
    destruct (IH1 nl HFp1 HDp1 ltac:(lia)) as (A1 & B1 & C1 & D1). rewrite E1 in A1, B1, C1, D1.
    cbn [fst snd] in A1, B1, C1, D1.
    destruct (IH2 m1 HFp2 HDp2 ltac:(lia)) as (A2 & B2 & C2 & D2). rewrite E2 in A2, B2, C2, D2.
    cbn [fst snd] in A2, B2, C2, D2.
    repeat split; try lia.
    + apply Forall_app; split; assumption.
    + apply NoDup_app_iff; split; [exact B1|split; [exact B2|]].
      intros x Hx1 Hx2.
      destruct (C1 _ Hx1) as [Hy1|[Hy1 Hy1']], (C2 _ Hx2) as [Hy2|[Hy2 Hy2']].
      * exact (Hdis _ Hy1 Hy2).
      * pose proof (Hnl _ _ Hy1); lia.
      * pose proof (Hnl _ _ Hy2); lia.
      * lia.
    + intros lb Hin. apply in_app_iff in Hin as [Hin|Hin].
      * destruct (C1 _ Hin) as [H'|H']; [left; apply in_app_iff; left; exact H'|right; lia].
      * destruct (C2 _ Hin) as [H'|H']; [left; apply in_app_iff; right; exact H'|right; lia].
  - cbn [comp]. destruct (comp n nl p1) as [q1 m1] eqn:E1. destruct (comp n m1 p2) as [q2 m2] eqn:E2.
    cbn [fst snd extract_labels] in *. rewrite MAX_max in HN.
    apply Forall_app in HF as [HFp1 HFp2].
    pose proof (proj1 (NoDup_app_iff _ _) HD) as (HDp1 & HDp2 & Hdis).
    destruct (IH1 nl HFp1 HDp1 ltac:(lia)) as (A1 & B1 & C1 & D1). rewrite E1 in A1, B1, C1, D1.
    cbn [fst snd] in A1, B1, C1, D1.
    destruct (IH2 m1 HFp2 HDp2 ltac:(lia)) as (A2 & B2 & C2 & D2). rewrite E2 in A2, B2, C2, D2.
    cbn [fst snd] in A2, B2, C2, D2.
    repeat split; try lia.
    + apply Forall_app; split; assumption.
    + apply NoDup_app_iff; split; [exact B1|split; [exact B2|]].
      intros x Hx1 Hx2.
      destruct (C1 _ Hx1) as [Hy1|[Hy1 Hy1']], (C2 _ Hx2) as [Hy2|[Hy2 Hy2']].
      * exact (Hdis _ Hy1 Hy2).
      * pose proof (Hnl _ _ Hy1); lia.
      * pose proof (Hnl _ _ Hy2); lia.
      * lia.
    + intros lb Hin. apply in_app_iff in Hin as [Hin|Hin].
      * destruct (C1 _ Hin) as [H'|H']; [left; apply in_app_iff; left; exact H'|right; lia].
      * destruct (C2 _ Hin) as [H'|H']; [left; apply in_app_iff; right; exact H'|right; lia].
  - cbn [comp]. destruct (comp n nl p) as [q1 m1] eqn:E1. cbn [fst snd extract_labels] in *.
    destruct (IH nl HF HD HN) as (A1 & B1 & C1 & D1). rewrite E1 in A1, B1, C1, D1. exact (conj A1 (conj B1 (conj C1 D1))).
  - destruct p; try contradiction; cbn [comp fst snd extract_labels] in *;
      try (repeat split; try (intros lb [] ; fail); try constructor; lia; fail).
    + repeat split; [constructor; [repeat split; lia|constructor]|constructor; [intros []|constructor]| |lia].
      intros lb [<-|[]]; right; cbn; lia.
    + destruct o as [loc|]; cbn [comp fst snd extract_labels];
        [|repeat split; try (intros lb [] ; fail); try constructor; lia].
      repeat split; [constructor; [repeat split; lia|constructor]|constructor; [intros []|constructor]| |lia].
      intros lb [<-|[]]; right; cbn; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "stack_alloc_lab_pres" *)
Theorem stack_alloc_lab_pres : forall n nl (p : prog a),
  EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0) && negb (l2 =? 1)) (extract_labels p) /\
  ALL_DISTINCT (extract_labels p) /\
  next_lab p 2 <= nl ->
  let '(cp, nl') := comp n nl p in
  EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0) && negb (l2 =? 1)) (extract_labels cp) /\
  ALL_DISTINCT (extract_labels cp) /\
  (forall lab, MEM lab (extract_labels cp) -> MEM lab (extract_labels p) \/ (nl <= SND lab /\ SND lab < nl')) /\
  nl <= nl'.
Proof.
  intros n nl p (HF & HD & HN).
  assert (Hc : forall l, is_true (EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0) && negb (l2 =? 1)) l) <->
                         Forall (fun '(l1, l2) => l1 = n /\ l2 <> 0 /\ l2 <> 1) l).
  { intros l; unfold is_true; rewrite EVERY_Forall; split; apply Forall_impl; intros [l1 l2] H;
      [apply andb_prop in H as [H H3]; apply andb_prop in H as [H1 H2];
       apply N.eqb_eq in H1; apply negb_true_iff, N.eqb_neq in H2; apply negb_true_iff, N.eqb_neq in H3;
       auto
      |destruct H as (-> & H2 & H3); rewrite N.eqb_refl; apply N.eqb_neq in H2, H3; rewrite H2, H3; reflexivity]. }
  apply Hc in HF. unfold is_true in HD; rewrite ALL_DISTINCT_NoDup_list in HD.
  destruct (lab_pres_aux n p nl HF HD HN) as (A & B & C & D).
  destruct (comp n nl p) as [cp nl'] eqn:E; cbn [fst snd] in *.
  repeat split.
  - apply Hc, A.
  - unfold is_true; rewrite ALL_DISTINCT_NoDup_list; exact B.
  - intros lb Hl; unfold is_true in *; rewrite !MEM_In in *; destruct (C lb Hl) as [H|H];
      [left; exact H|right; exact H].
  - exact D.
Qed.

(** HOL's free variable [c] is quantified first. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "stack_alloc_comp_stack_asm_name" *)
Theorem stack_alloc_comp_stack_asm_name : forall (c : asm_config a) n m (p : prog a),
  stack_asm_name c p /\ stack_asm_remove c p ->
  let '(p', m') := comp n m p in
  stack_asm_name c p' /\ stack_asm_remove c p'.
Proof.
  intros c n m p; revert m.
  induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|c0 r ri p1 p2 IH1 IH2|p IH|p Hp]
    using prog_nested_ind; intros m [H1 H2].
  - destruct ret as [[p1 [lr [l1 l2]]]|].
    2:{ cbn [comp stack_asm_name stack_asm_remove] in *. split; [|reflexivity].
        destruct dest; [reflexivity|]. apply andb_prop in H1 as [H1 _]; rewrite H1; reflexivity. }
    specialize (Hr p1 _ eq_refl).
    cbn [comp stack_asm_name stack_asm_remove] in *.
    apply andb_prop in H1 as [Hd H1]; apply andb_prop in H1 as [H1a H1b].
    apply andb_prop in H2 as [H2a H2b].
    specialize (Hr m (conj H1a H2a)). destruct (comp n m p1) as [q1 m1] eqn:E1. destruct Hr as [Hq1 Hq2].
    destruct h as [[p2 [k1 k2]]|].
    + specialize (Hh p2 _ eq_refl m1 (conj H1b H2b)). destruct (comp n m1 p2) as [q2 m2] eqn:E2.
      destruct Hh as [Hq3 Hq4]. cbn [stack_asm_name stack_asm_remove].
      rewrite Hd, Hq1, Hq2, Hq3, Hq4; split; reflexivity.
    + cbn [stack_asm_name stack_asm_remove]. rewrite Hd, Hq1, Hq2; split; reflexivity.
  - cbn [comp stack_asm_name stack_asm_remove] in *.
    apply andb_prop in H1 as [H1a H1b]; apply andb_prop in H2 as [H2a H2b].
    specialize (IH1 m (conj H1a H2a)). destruct (comp n m p1) as [q1 m1] eqn:E1.
    specialize (IH2 m1 (conj H1b H2b)). destruct (comp n m1 p2) as [q2 m2] eqn:E2.
    destruct IH1 as [A1 B1], IH2 as [A2 B2]. cbn [stack_asm_name stack_asm_remove].
    rewrite A1, B1, A2, B2; split; reflexivity.
  - cbn [comp stack_asm_name stack_asm_remove] in *.
    apply andb_prop in H1 as [H1a H1b]; apply andb_prop in H2 as [H2a H2b].
    specialize (IH1 m (conj H1a H2a)). destruct (comp n m p1) as [q1 m1] eqn:E1.
    specialize (IH2 m1 (conj H1b H2b)). destruct (comp n m1 p2) as [q2 m2] eqn:E2.
    destruct IH1 as [A1 B1], IH2 as [A2 B2]. cbn [stack_asm_name stack_asm_remove].
    rewrite A1, B1, A2, B2; split; reflexivity.
  - cbn [comp stack_asm_name stack_asm_remove] in *.
    specialize (IH m (conj H1 H2)). destruct (comp n m p) as [q1 m1] eqn:E1. exact IH.
  - destruct p; try contradiction; cbn [comp stack_asm_name stack_asm_remove] in *;
      try (split; assumption); try (split; reflexivity).
    destruct o; cbn [comp stack_asm_name stack_asm_remove]; [split; reflexivity|split; assumption].
Qed.

(** Galette-only: [comp] preserves [reg_bound] and [call_args]. *)
Local Lemma comp_reg_bound sp n : 10 <= sp -> forall (p : prog a) m,
  reg_bound p sp -> reg_bound (fst (comp n m p)) sp.
Proof.
  intros Hsp p; induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|c0 r ri p1 p2 IH1 IH2|p IH|p Hp]
    using prog_nested_ind; intros m H; unfold is_true in *.
  - destruct ret as [[p1 [lr [l1 l2]]]|]; cbn [comp reg_bound fst] in *; [|exact H].
    specialize (Hr p1 _ eq_refl).
    repeat match goal with H : (_ && _) = true |- _ => apply andb_prop in H as [? ?] end.
    specialize (Hr m ltac:(assumption)). destruct (comp n m p1) as [q1 m1] eqn:E1. cbn [fst] in Hr.
    destruct h as [[p2 [k1 k2]]|].
    + specialize (Hh p2 _ eq_refl m1 ltac:(assumption)). destruct (comp n m1 p2) as [q2 m2] eqn:E2.
      cbn [fst reg_bound] in *. repeat (apply andb_true_intro; split); assumption.
    + cbn [fst reg_bound]. repeat (apply andb_true_intro; split); try assumption; reflexivity.
  - cbn [comp reg_bound] in *. apply andb_prop in H as [H1 H2].
    specialize (IH1 m H1). destruct (comp n m p1) as [q1 m1].
    specialize (IH2 m1 H2). destruct (comp n m1 p2) as [q2 m2]. cbn [fst reg_bound] in *.
    rewrite IH1, IH2; reflexivity.
  - cbn [comp reg_bound] in *.
    repeat match goal with H : (_ && _) = true |- _ => apply andb_prop in H as [? ?] end.
    specialize (IH1 m ltac:(assumption)). destruct (comp n m p1) as [q1 m1].
    specialize (IH2 m1 ltac:(assumption)). destruct (comp n m1 p2) as [q2 m2]. cbn [fst reg_bound] in *.
    repeat (apply andb_true_intro; split); assumption.
  - cbn [comp reg_bound] in *. specialize (IH m H). destruct (comp n m p) as [q1 m1]. exact IH.
  - destruct p; try contradiction; cbn [comp reg_bound fst] in *; try exact H.
    + rewrite (proj2 (N.ltb_lt 0 sp) ltac:(lia)); reflexivity.
    + destruct o; cbn [comp reg_bound fst]; [rewrite (proj2 (N.ltb_lt 0 sp) ltac:(lia)); reflexivity|exact H].
Qed.

Local Lemma comp_call_args n : forall (p : prog a) m,
  call_args p 1 2 3 4 0 -> call_args (fst (comp n m p)) 1 2 3 4 0.
Proof.
  intros p; induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|c0 r ri p1 p2 IH1 IH2|p IH|p Hp]
    using prog_nested_ind; intros m H; unfold is_true in *.
  - destruct ret as [[p1 [lr [l1 l2]]]|]; cbn [comp call_args fst] in *; [|exact H].
    specialize (Hr p1 _ eq_refl).
    repeat match goal with H : (_ && _) = true |- _ => apply andb_prop in H as [? ?] end.
    specialize (Hr m ltac:(assumption)). destruct (comp n m p1) as [q1 m1] eqn:E1. cbn [fst] in Hr.
    destruct h as [[p2 [k1 k2]]|].
    + specialize (Hh p2 _ eq_refl m1 ltac:(assumption)). destruct (comp n m1 p2) as [q2 m2] eqn:E2.
      cbn [fst call_args] in *. repeat (apply andb_true_intro; split); assumption.
    + cbn [fst call_args]. repeat (apply andb_true_intro; split); try assumption; reflexivity.
  - cbn [comp call_args] in *. apply andb_prop in H as [H1 H2].
    specialize (IH1 m H1). destruct (comp n m p1) as [q1 m1].
    specialize (IH2 m1 H2). destruct (comp n m1 p2) as [q2 m2]. cbn [fst call_args] in *.
    rewrite IH1, IH2; reflexivity.
  - cbn [comp call_args] in *. apply andb_prop in H as [H1 H2].
    specialize (IH1 m H1). destruct (comp n m p1) as [q1 m1].
    specialize (IH2 m1 H2). destruct (comp n m1 p2) as [q2 m2]. cbn [fst call_args] in *.
    rewrite IH1, IH2; reflexivity.
  - cbn [comp call_args] in *. specialize (IH m H). destruct (comp n m p) as [q1 m1]. exact IH.
  - destruct p; try contradiction; cbn [comp call_args fst] in *; try exact H; try reflexivity.
    destruct o; cbn [comp call_args fst]; [reflexivity|exact H].
Qed.

Local Ltac unfold_gc_code :=
  unfold stubs, word_gc_code, word_gc_partial_or_full, SetNewTrigger, memcpy_code, clear_top_inst,
    word_gc_move_code, word_gc_move_list_code, word_gc_move_loop_code, word_gc_move_bitmap_code,
    word_gc_move_bitmaps_code, word_gc_move_roots_bitmaps_code, word_gen_gc_move_code,
    word_gen_gc_partial_move_code, word_gen_gc_move_bitmap_code, word_gen_gc_partial_move_bitmap_code,
    word_gen_gc_move_bitmaps_code, word_gen_gc_partial_move_bitmaps_code,
    word_gen_gc_move_roots_bitmaps_code, word_gen_gc_partial_move_roots_bitmaps_code,
    word_gen_gc_move_list_code, word_gen_gc_partial_move_list_code, word_gen_gc_move_data_code,
    word_gen_gc_partial_move_ref_list_code, word_gen_gc_partial_move_data_code,
    word_gen_gc_move_refs_code, word_gen_gc_move_loop_code.

Local Ltac bd_false :=
  repeat match goal with
         | |- context [bool_decide (?x = ?y)] =>
             let E := fresh in
             assert (E : bool_decide (x = y) = false)
               by (apply Bool.not_true_iff_false; rewrite bool_decide_spec; discriminate);
             rewrite E; clear E
         end.

Local Lemma EVERY_app {A} (P : A -> bool) l1 l2 : EVERY P (l1 ++ l2) = EVERY P l1 && EVERY P l2.
Proof. induction l1 as [|x l1 IH]; cbn; [reflexivity|]. rewrite IH, Bool.andb_assoc; reflexivity. Qed.

Local Lemma stubs_reg_bound sp (dc : data_to_word.config) : 10 <= sp ->
  EVERY (fun p => reg_bound p sp) (MAP SND (@stubs a dc)).
Proof.
  intros Hsp; repeat progress unfold_gc_code; cbn [MAP SND snd EVERY].
  destruct (gc_kind dc) as [| |gs]; [ | | destruct gs ];
    cbn [list_Seq app reg_bound reg_bound_inst andb];
    repeat match goal with |- context [?x <? sp] => rewrite (proj2 (N.ltb_lt x sp) ltac:(lia)) end;
    bd_false; cbn [andb negb]; reflexivity.
Qed.

Local Lemma stubs_call_args (dc : data_to_word.config) :
  EVERY (fun p => call_args p 1 2 3 4 0) (MAP SND (@stubs a dc)).
Proof.
  repeat progress unfold_gc_code; cbn [MAP SND snd EVERY].
  destruct (gc_kind dc) as [| |gs]; [ | | destruct gs ];
    cbn [list_Seq app call_args andb]; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "stack_alloc_reg_bound" *)
Theorem stack_alloc_reg_bound : forall sp (prog1 : list (N * prog a)) dc,
  10 <= sp /\ EVERY (fun p => reg_bound p sp) (MAP SND prog1) ->
  EVERY (fun p => reg_bound p sp) (MAP SND (compile dc prog1)).
Proof.
  intros sp prog1 dc [Hsp H]; unfold compile; rewrite map_app, EVERY_app.
  unfold is_true; apply andb_true_intro; split; [apply stubs_reg_bound, Hsp|].
  induction prog1 as [|[n p] prog1 IH]; [reflexivity|].
  cbn [MAP EVERY SND snd] in *; unfold is_true in *. apply andb_prop in H as [H1 H2].
  apply andb_true_intro; split; [|exact (IH H2)].
  unfold prog_comp; cbn [snd]. apply comp_reg_bound; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "stack_alloc_call_args" *)
Theorem stack_alloc_call_args : forall (prog1 : list (N * prog a)) dc,
  EVERY (fun p => call_args p 1 2 3 4 0) (MAP SND prog1) ->
  EVERY (fun p => call_args p 1 2 3 4 0) (MAP SND (compile dc prog1)).
Proof.
  intros prog1 dc H; unfold compile; rewrite map_app, EVERY_app.
  unfold is_true; apply andb_true_intro; split; [apply stubs_call_args|].
  induction prog1 as [|[n p] prog1 IH]; [reflexivity|].
  cbn [MAP EVERY SND snd] in *; unfold is_true in *. apply andb_prop in H as [H1 H2].
  apply andb_true_intro; split; [|exact (IH H2)].
  unfold prog_comp; cbn [snd]. apply comp_call_args; assumption.
Qed.

Local Lemma dimindex_lt_dimword' : dimindex a < dimword a.
Proof.
  unfold dimword. pose proof (DIMINDEX_GT_0 a).
  apply N.pow_gt_lin_r; lia.
Qed.

Local Lemma w2n_n2w_lt x : x < dimindex a -> w2n (n2w x : word a) = x.
Proof. intros H; rewrite w2n_n2w; apply N.mod_small; pose proof dimindex_lt_dimword'; lia. Qed.

Local Lemma n2w_ne0 x : 0 < x -> x < dimindex a -> (n2w x : word a) <> n2w 0.
Proof.
  intros H0 H1 E; apply (f_equal w2n) in E. rewrite w2n_n2w_lt in E by exact H1.
  rewrite w2n_n2w, N.mod_0_l in E by (pose proof (ZERO_LT_dimword a); lia). lia.
Qed.

Local Lemma reg_name_le (c : asm_config a) r : reg_name 10 c -> r <= 10 -> reg_name r c.
Proof. unfold is_true, reg_name; intros H Hle; apply N.ltb_lt in H; apply N.ltb_lt; lia. Qed.

Local Lemma conf_ok_facts conf : conf_ok a conf -> good_dimindex a ->
  0 < dimindex a - (small_shift_length conf - 1) - 1 < dimindex a /\
  0 < dimindex a - len_size conf < dimindex a /\ 0 < shift_length conf < dimindex a /\
  0 < word_shift a < dimindex a /\ 0 < dimindex a - 1 < dimindex a /\ 2 < dimindex a.
Proof.
  unfold conf_ok, shift_length, small_shift_length, word_shift; intros (H1 & H2 & H3 & H4) Hg.
  destruct Hg as [Hg|Hg]; rewrite Hg in *; cbn [N.eqb Pos.eqb]; lia.
Qed.

Local Ltac asm_leaf c Hr Hg Hc :=
  first
    [ reflexivity | assumption
    | apply (reg_name_le c); [exact Hr|lia]
    | (apply N.ltb_lt; pose proof (conf_ok_facts _ Hc Hg); rewrite w2n_n2w_lt; lia)
    | (apply Bool.implb_true_iff; intros _; apply bool_decide_spec; reflexivity)
    | (apply Bool.implb_true_iff; intros Hx; apply bool_decide_spec in Hx; exfalso;
       revert Hx; pose proof (conf_ok_facts _ Hc Hg); apply n2w_ne0; lia)
    | (destruct (two_reg_arith c); cbn [implb]; [|reflexivity];
       first [ apply Bool.orb_true_iff; left; apply bool_decide_spec; reflexivity
             | apply Bool.orb_true_iff; right; apply andb_true_iff; split; apply bool_decide_spec; reflexivity
             | apply bool_decide_spec; reflexivity ])
    | (unfold bytes_in_word; destruct Hg as [Hg|Hg]; rewrite Hg; cbn; assumption) ].

Local Lemma stubs_asm (c : asm_config a) conf :
  conf_ok a conf -> addr_offset_ok c (n2w 0) -> reg_name 10 c -> good_dimindex a ->
  valid_imm c (inl asm.Add) (n2w 8) -> valid_imm c (inl asm.Add) (n2w 4) ->
  valid_imm c (inl asm.Add) (n2w 1) -> valid_imm c (inl asm.Sub) (n2w 1) ->
  EVERY (fun '(n, p) => stack_asm_name c p) (@stubs a conf) /\
  EVERY (fun '(n, p) => stack_asm_remove c p) (@stubs a conf).
Proof.
  intros Hc Ho Hr Hg H8 H4 H1 Hs1.
  repeat progress unfold_gc_code; cbn [EVERY].
  destruct (gc_kind conf) as [| |gs]; [ | | destruct gs ];
    cbn [list_Seq app stack_asm_name stack_asm_remove inst_name arith_name reg_imm_name addr_name
         MEM andb orb];
    unfold is_true; rewrite ?Bool.andb_true_r;
    repeat match goal with
           | |- _ /\ _ => split
           | |- (_ && _) = true => apply andb_true_iff; split
           end; asm_leaf c Hr Hg Hc.
Qed.

(** HOL's free variables are quantified first, in order of appearance;
    HOL's [prog] is [prog0] (the type [prog] would be shadowed). *)
(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "stack_alloc_stack_asm_convs" *)
Theorem stack_alloc_stack_asm_convs : forall (c : asm_config a) (prog0 : list (N * prog a)) conf,
  EVERY (fun '(n, p) => stack_asm_name c p) prog0 /\
  EVERY (fun '(n, p) => stack_asm_remove c p) prog0 /\
  conf_ok a conf /\
  addr_offset_ok c (n2w 0) /\
  reg_name 10 c /\ good_dimindex a /\
  valid_imm c (inl asm.Add) (n2w 8) /\
  valid_imm c (inl asm.Add) (n2w 4) /\
  valid_imm c (inl asm.Add) (n2w 1) /\
  valid_imm c (inl asm.Sub) (n2w 1) ->
  EVERY (fun '(n, p) => stack_asm_name c p) (compile conf prog0) /\
  EVERY (fun '(n, p) => stack_asm_remove c p) (compile conf prog0).
Proof.
  intros c prog0 conf (H1 & H2 & Hc & Ho & Hr & Hg & H8 & H4 & Ha1 & Hs1).
  destruct (stubs_asm c conf Hc Ho Hr Hg H8 H4 Ha1 Hs1) as [S1 S2].
  unfold compile; rewrite !EVERY_app; unfold is_true in *; rewrite S1, S2; cbn [andb].
  induction prog0 as [|[n p] prog0 IH]; [split; reflexivity|].
  cbn [MAP EVERY] in *. apply andb_prop in H1 as [H1a H1b]; apply andb_prop in H2 as [H2a H2b].
  destruct (IH H1b H2b) as [IHa IHb].
  pose proof (stack_alloc_comp_stack_asm_name c n (next_lab p 2) p (conj H1a H2a)) as Hp.
  cbn [prog_comp]. destruct (comp n (next_lab p 2) p) as [q m]. destruct Hp as [Hq1 Hq2].
  cbn [fst]. rewrite Hq1, Hq2, IHa, IHb; split; reflexivity.
Qed.

(** HOL [dconf with <| has_fp_ops := b1; has_fp_tern := b2 |>] is written
    as a record literal. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "compile_has_fp_ops" *)
Theorem compile_has_fp_ops : forall dconf b1 b2 (code : list (N * prog a)),
  compile {| data_to_word.tag_bits := data_to_word.tag_bits dconf;
             data_to_word.len_bits := data_to_word.len_bits dconf;
             data_to_word.pad_bits := data_to_word.pad_bits dconf;
             data_to_word.len_size := data_to_word.len_size dconf;
             data_to_word.has_div := data_to_word.has_div dconf;
             data_to_word.has_longdiv := data_to_word.has_longdiv dconf;
             data_to_word.has_fp_ops := b1;
             data_to_word.has_fp_tern := b2;
             data_to_word.be := data_to_word.be dconf;
             data_to_word.call_empty_ffi := data_to_word.call_empty_ffi dconf;
             data_to_word.gc_kind := data_to_word.gc_kind dconf |} code =
  compile dconf code.
Proof. intros dconf b1 b2 code; destruct dconf; reflexivity. Qed.

End Syntax.


(** ** Words and bitmaps *)

Section Words.
Context {a : N}.
Local Open Scope word_scope.

(** HOL's shift amount [a] is [k] here ([a] is the word-width index). *)
(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "lsl_lsr" *)
Theorem lsl_lsr : forall (n : word a) k, (w2n n * 2 ** k < dimword a)%N -> n << k >>> k = n.
Proof.
  intros n k H. apply word_eq_w2n. rewrite w2n_lsr, WORD_MUL_LSL.
  rewrite <- (n2w_w2n n) at 1. rewrite word_mul_n2w, w2n_n2w, N.mod_small by lia.
  rewrite N.mul_comm, N.div_mul; [reflexivity|]. apply N.pow_nonzero; lia.
Qed.

Lemma bytes_in_word_shift (Hg : good_dimindex a) : (bytes_in_word : word a) = n2w (2 ** word_shift a).
Proof. unfold bytes_in_word, word_shift. destruct Hg as [E|E]; rewrite E; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "bytes_in_word_word_shift" *)
Theorem bytes_in_word_word_shift : forall n : word a,
  good_dimindex a /\ (w2n (bytes_in_word : word a) * w2n n < dimword a)%N ->
  (bytes_in_word * n) >>> word_shift a = n.
Proof.
  intros n [Hg Hb]. rewrite (bytes_in_word_shift Hg) in *.
  assert (Hp : (2 ** word_shift a < dimword a)%N).
  { rewrite dimword_pow. apply N.pow_lt_mono_r; [lia|]. unfold word_shift.
    destruct Hg as [E|E]; rewrite E; cbn; lia. }
  rewrite w2n_n2w, N.mod_small in Hb by exact Hp.
  apply word_eq_w2n. rewrite w2n_lsr. unfold word_mul. rewrite w2n_n2w, (w2n_n2w (2 ** word_shift a)).
  rewrite (N.mod_small (2 ** word_shift a)) by exact Hp.
  rewrite N.mod_small by exact Hb. rewrite N.mul_comm, N.div_mul; [reflexivity|].
  apply N.pow_nonzero; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "get_bits_def" *)
Definition get_bits (w : word a) : list bool := GENLIST (fun i => w ' i) (bit_length w - 1).

Lemma w2n_ne0 (w : word a) : w <> n2w 0 -> w2n w <> 0%N.
Proof. intros H E; apply H, w2n_eq_0, E. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "bit_length_thm" *)
Theorem bit_length_thm : forall w : word a,
  (w >>> bit_length w = n2w 0) /\ (forall n, (n < bit_length w)%N -> w >>> n <> n2w 0).
Proof.
  intros w; unfold bit_length; split.
  - apply word_eq_w2n. rewrite w2n_lsr, w2n_n2w, N.mod_0_l by (pose proof (ZERO_LT_dimword a); lia).
    apply N.div_small. destruct (N.eq_dec (w2n w) 0) as [E|E]; [rewrite E; cbn; lia|].
    apply N.size_gt.
  - intros n Hn E. apply (f_equal w2n) in E. rewrite w2n_lsr, w2n_n2w, N.mod_0_l in E
      by (pose proof (ZERO_LT_dimword a); lia).
    destruct (N.eq_dec (w2n w) 0) as [Z|Z]; [rewrite Z in Hn; cbn in Hn; lia|].
    rewrite N.size_log2 in Hn by exact Z.
    destruct (N.log2_spec (w2n w) ltac:(lia)) as [Hle _].
    apply N.div_small_iff in E; [|apply N.pow_nonzero; lia].
    assert (2 ^ n <= 2 ^ N.log2 (w2n w))%N by (apply N.pow_le_mono_r; lia).
    lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_lsr_dimindex" *)
Local Theorem word_lsr_dimindex : forall w : word a, w >>> dimindex a = n2w 0.
Proof. intros w; apply LSR_LIMIT; lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "bit_length_LESS_EQ_dimindex" *)
Theorem bit_length_LESS_EQ_dimindex : forall w : word a, (bit_length w <= dimindex a)%N.
Proof.
  intros w; unfold bit_length. destruct (N.eq_dec (w2n w) 0) as [E|E]; [rewrite E; cbn; lia|].
  rewrite N.size_log2 by exact E. pose proof (w2n_lt w) as Hl; rewrite dimword_pow in Hl.
  apply N.log2_lt_pow2 in Hl; lia.
Qed.

Lemma w2n_n2w_small n : (n < dimword a)%N -> w2n (n2w n : word a) = n.
Proof. intros H; rewrite w2n_n2w; apply N.mod_small, H. Qed.

Lemma dimword_ge2 : (2 <= dimword a)%N.
Proof. rewrite dimword_pow. pose proof (DIMINDEX_GT_0 a). replace 2%N with (2 ^ 1)%N by reflexivity.
  apply N.pow_le_mono_r; lia. Qed.

Lemma word_msb_ge (w : word a) : word_msb w = true <-> (2 ^ (dimindex a - 1) <= w2n w)%N.
Proof.
  unfold word_msb; rewrite BIT_testbit. pose proof (w2n_lt w) as Hl; rewrite dimword_pow in Hl.
  pose proof (DIMINDEX_GT_0 a) as Hd.
  replace (dimindex a) with (N.succ (dimindex a - 1))%N in Hl by lia.
  split.
  - intros Ht. destruct (N.lt_ge_cases (w2n w) (2 ^ (dimindex a - 1))) as [Hlt|]; [|assumption].
    destruct (N.eq_dec (w2n w) 0) as [Z|Z]; [rewrite Z, N.bits_0 in Ht; discriminate|].
    rewrite N.bits_above_log2 in Ht; [discriminate|].
    apply N.log2_lt_pow2; lia.
  - intros Hge. assert (Hlog : (N.log2 (w2n w) = dimindex a - 1)%N).
    { apply N.log2_unique; [lia|split; [exact Hge|exact Hl]]. }
    rewrite <- Hlog. apply N.bit_log2. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "shift_to_zero_word_msb" *)
Theorem shift_to_zero_word_msb : forall (w : word a) n,
  w >>> n = n2w 0 /\ word_msb w -> (dimindex a <= n)%N.
Proof.
  intros w n [E Hm]. apply word_msb_ge in Hm. apply (f_equal w2n) in E.
  rewrite w2n_lsr, w2n_n2w, N.mod_0_l in E by (pose proof (ZERO_LT_dimword a); lia).
  apply N.div_small_iff in E; [|apply N.pow_nonzero; lia].
  destruct (N.le_gt_cases (dimindex a) n) as [|Hlt]; [assumption|].
  assert (Hpp : (2 ^ n <= 2 ^ (dimindex a - 1))%N) by (apply N.pow_le_mono_r; lia). lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_msb_IMP_bit_length" *)
Local Theorem word_msb_IMP_bit_length : forall h : word a, word_msb h -> bit_length h = dimindex a.
Proof.
  intros h Hm. apply word_msb_ge in Hm. unfold bit_length.
  pose proof (w2n_lt h) as Hl; rewrite dimword_pow in Hl. pose proof (DIMINDEX_GT_0 a).
  assert (Z : w2n h <> 0%N) by (pose proof (N.pow_nonzero 2 (dimindex a - 1)); lia).
  rewrite N.size_log2 by exact Z.
  rewrite (N.log2_unique (w2n h) (dimindex a - 1)%N); [lia|lia|].
  split; [exact Hm|]. replace (N.succ (dimindex a - 1))%N with (dimindex a) by lia.
  exact Hl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "get_bits_intro" *)
Local Theorem get_bits_intro : forall h : word a,
  word_msb h -> GENLIST (fun i => h ' i) (dimindex a - 1) = get_bits h.
Proof. intros h Hm; unfold get_bits; rewrite (word_msb_IMP_bit_length h Hm); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "bit_length_minus_1" *)
Theorem bit_length_minus_1 : forall w : word a, w <> n2w 0 -> (bit_length w - 1 = bit_length (w >>> 1))%N.
Proof.
  intros w H. rewrite (bit_length_def w). destruct (bool_decide _) eqn:E; [apply bool_decide_spec in E; contradiction|].
  lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "bit_length_eq_1" *)
Theorem bit_length_eq_1 : forall w : word a, bit_length w = 1%N <-> w = n2w 1.
Proof.
  intros w; unfold bit_length; split.
  - intros H. apply word_eq_w2n. rewrite w2n_n2w_small by (pose proof dimword_ge2; lia).
    destruct (N.eq_dec (w2n w) 0) as [Z|Z]; [rewrite Z in H; discriminate|].
    rewrite N.size_log2 in H by exact Z. destruct (N.log2_spec (w2n w) ltac:(lia)) as [_ Hu].
    assert (E : (N.log2 (w2n w) = 0)%N) by lia. rewrite E in Hu. cbn in Hu. lia.
  - intros ->. rewrite w2n_n2w_small by (pose proof dimword_ge2; lia). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_and_one_eq_0_iff" *)
Theorem word_and_one_eq_0_iff : forall w : word a, (w && n2w 1) = n2w 0 <-> ~ is_true (w ' 0).
Proof.
  intros w. unfold word_and, fcp_index. rewrite BIT_testbit.
  rewrite (w2n_n2w_small 1) by (pose proof dimword_ge2; lia).
  replace (N.land (w2n w) 1) with (w2n w mod 2)%N
    by (change (w2n w mod 2)%N with (w2n w mod 2 ^ 1)%N; rewrite <- (N.land_ones (w2n w) 1); reflexivity).
  pose proof (N.bit0_mod (w2n w)) as Hb.
  destruct (N.testbit (w2n w) 0) eqn:Et; cbn [N.b2n] in Hb; split.
  - intros E. apply (f_equal w2n) in E. rewrite <- Hb, !w2n_n2w_small in E by (pose proof dimword_ge2; lia).
    discriminate.
  - intros Hn; exfalso; apply Hn; reflexivity.
  - intros _ H; discriminate H.
  - intros _. rewrite <- Hb; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "split_num_forall_to_10" *)
Local Theorem split_num_forall_to_10 : forall P : N -> Prop,
  (forall x, P x) <-> P 0%N /\ P 1%N /\ P 2%N /\ P 3%N /\ P 4%N /\ P 5%N /\ P 6%N /\ P 7%N /\ P 8%N /\
                      P 9%N /\ (forall x, (9 < x)%N -> P x).
Proof.
  intros P; split; [intros H; repeat split; auto|].
  intros (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H) x.
  destruct (N.lt_ge_cases 9 x) as [Hx|Hx]; [exact (H x Hx)|].
  assert (x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9)%N as Hc by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_shift_not_0" *)
Theorem word_shift_not_0 : word_shift a <> 0%N.
Proof. unfold word_shift; destruct (dimindex a =? 32); discriminate. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "is_fwd_ptr_iff" *)
Local Theorem is_fwd_ptr_iff : forall w : word_loc a,
  wordSem.is_fwd_ptr w <-> exists v, w = Word v /\ (v && n2w 3) = n2w 0.
Proof.
  intros [v|l1 l2]; cbn [wordSem.is_fwd_ptr]; unfold is_true; split.
  - intros H; apply bool_decide_spec in H; eexists; split; [reflexivity|exact H].
  - intros (v' & E & H); injection E as <-; apply bool_decide_spec, H.
  - discriminate.
  - intros (v' & E & _); discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "isWord_thm" *)
Local Theorem isWord_thm : forall w : word_loc a, wordSem.isWord w <-> exists v, w = Word v.
Proof. intros [v|l1 l2]; cbn; split; try (intros; eexists; reflexivity); try discriminate; intros [? ?]; discriminate. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "lower_2w_eq" *)
Local Theorem lower_2w_eq : forall w : word a, good_dimindex a -> (w <+ n2w 2 <-> w = n2w 0 \/ w = n2w 1).
Proof.
  intros w Hg. unfold is_true. rewrite word_lo_w2n.
  assert (H4 : (4 <= dimword a)%N).
  { rewrite dimword_pow. destruct Hg as [E|E]; rewrite E; cbn; lia. }
  rewrite (w2n_n2w_small 2) by lia. rewrite N.ltb_lt. split.
  - intros H. destruct (N.eq_dec (w2n w) 0) as [Z|Z]; [left; apply word_eq_w2n; rewrite Z, w2n_n2w_small by lia; reflexivity|].
    right; apply word_eq_w2n; rewrite w2n_n2w_small by lia; lia.
  - intros [->| ->]; rewrite w2n_n2w_small; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_msb_IFF_lsr_EQ_0" *)
Theorem word_msb_IFF_lsr_EQ_0 : forall h : word a, word_msb h <-> h >>> (dimindex a - 1) <> n2w 0.
Proof.
  intros h. unfold is_true. rewrite word_msb_ge. split.
  - intros H E. apply (f_equal w2n) in E. rewrite w2n_lsr, w2n_n2w, N.mod_0_l in E
      by (pose proof (ZERO_LT_dimword a); lia).
    apply N.div_small_iff in E; [lia|apply N.pow_nonzero; lia].
  - intros H. destruct (N.lt_ge_cases (w2n h) (2 ^ (dimindex a - 1))) as [Hl|]; [|assumption].
    exfalso; apply H. apply word_eq_w2n. rewrite w2n_lsr, w2n_n2w, N.mod_0_l
      by (pose proof (ZERO_LT_dimword a); lia). apply N.div_small, Hl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "lt_dimindex_MOD_dimword" *)
Local Theorem lt_dimindex_MOD_dimword : forall n, (n < dimindex a)%N -> (n mod dimword a = n)%N.
Proof.
  intros n H; apply N.mod_small. rewrite dimword_pow.
  apply N.lt_trans with (dimindex a); [exact H|]. apply N.pow_gt_lin_r; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "bytes_in_word_word_shift_n2w" *)
Theorem bytes_in_word_word_shift_n2w : forall n,
  good_dimindex a /\ (dimindex a DIV 8 * n < dimword a)%N ->
  (bytes_in_word * n2w n : word a) >>> word_shift a = n2w n.
Proof.
  intros n [Hg H]. apply bytes_in_word_word_shift; split; [exact Hg|].
  assert (Hb : (dimindex a DIV 8 < dimword a)%N /\ (n < dimword a)%N).
  { assert (H8 : (1 <= dimindex a DIV 8)%N) by (destruct Hg as [E|E]; rewrite E; cbn; lia).
    assert (Hd : (dimindex a DIV 8 <= dimindex a)%N) by (apply N.div_le_upper_bound; lia).
    assert (Hdw : (dimindex a < dimword a)%N) by (rewrite dimword_pow; apply N.pow_gt_lin_r; lia).
    split; [lia|]. nia. }
  unfold bytes_in_word. rewrite !w2n_n2w_small by lia. exact H.
Qed.

Lemma tb_BITS h l x i : N.testbit (BITS h l x) i = ((i <? SUC h - l) && N.testbit x (i + l))%bool.
Proof.
  unfold BITS, MOD_2EXP, DIV_2EXP. destruct (N.ltb_spec i (SUC h - l)).
  - rewrite N.mod_pow2_bits_low, N.div_pow2_bits by lia. reflexivity.
  - rewrite N.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma tb_mul_pow x k j : N.testbit (x * 2 ^ k) j = ((k <=? j) && N.testbit x (j - k))%bool.
Proof.
  rewrite <- N.shiftl_mul_pow2. destruct (N.leb_spec k j).
  - rewrite N.shiftl_spec_high'; [reflexivity|lia].
  - rewrite N.shiftl_spec_low by lia. reflexivity.
Qed.

Lemma w2n_bits h l (w : word a) : w2n ((h -- l) w) = BITS (MIN h (dimindex a - 1)) l (w2n w).
Proof.
  unfold word_bits. rewrite w2n_n2w, N.mod_small; [reflexivity|].
  rewrite dimword_pow. eapply N.lt_le_trans; [apply BITS_lt|]. apply N.pow_le_mono_r; [lia|].
  rewrite MIN_min. pose proof (DIMINDEX_GT_0 a).
  destruct (N.min_spec h (dimindex a - 1)) as [[Hh ->]|[Hh ->]]; lia.
Qed.

Lemma tb_w2n_high (w : word a) i : (dimindex a <= i)%N -> N.testbit (w2n w) i = false.
Proof.
  intros H. destruct (N.eq_dec (w2n w) 0) as [Z|Z]; [rewrite Z; apply N.bits_0|].
  apply N.bits_above_log2. pose proof (w2n_lt w) as Hl; rewrite dimword_pow in Hl.
  apply N.log2_lt_pow2 in Hl; lia.
Qed.

Lemma w2n_lsl (w : word a) k : w2n (w << k) = if dimindex a - 1 <? k then 0%N else (w2n w * 2 ^ k mod dimword a)%N.
Proof. unfold word_lsl. destruct (_ <? _); [rewrite w2n_n2w_small; [reflexivity|pose proof dimword_ge2; lia]|].
  apply w2n_n2w. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "select_lower_lemma" *)
Theorem select_lower_lemma : forall n (w : word a),
  (n -- 0) w = (w << (dimindex a - n - 1)) >>> (dimindex a - n - 1).
Proof.
  intros n w. apply word_eq_w2n. rewrite word_lsr_n2w, !w2n_bits, w2n_lsl.
  pose proof (DIMINDEX_GT_0 a) as Hd. rewrite !MIN_min.
  replace (N.min (dimindex a - 1) (dimindex a - 1)) with (dimindex a - 1)%N by lia.
  destruct (N.ltb_spec (dimindex a - 1) (dimindex a - n - 1)) as [Hlt|Hge]; [lia|].
  apply N.bits_inj; intros i. rewrite !tb_BITS, N.add_0_r, dimword_pow.
  set (k := (dimindex a - n - 1)%N).
  destruct (N.ltb_spec (i + k) (dimindex a)) as [Hik|Hik].
  - rewrite N.mod_pow2_bits_low by exact Hik. rewrite tb_mul_pow.
    replace (i + k - k)%N with i by lia. rewrite (proj2 (N.leb_le k (i + k)) ltac:(lia)). cbn [andb].
    destruct (N.min_spec n (dimindex a - 1)) as [[Hn ->]|[Hn ->]];
      destruct (N.ltb_spec i (SUC n - 0)), (N.ltb_spec i (SUC (dimindex a - 1) - k)),
        (N.ltb_spec i (SUC (dimindex a - 1) - 0)); try reflexivity; try lia;
      subst k; try lia; rewrite tb_w2n_high by lia; reflexivity.
  - rewrite N.mod_pow2_bits_high by exact Hik. rewrite Bool.andb_false_r.
    destruct (N.min_spec n (dimindex a - 1)) as [[Hn ->]|[Hn ->]];
      destruct (N.ltb_spec i (SUC n - 0)); try (cbn [andb]; reflexivity);
      try (destruct (N.ltb_spec i (SUC (dimindex a - 1) - 0)); [|reflexivity]);
      subst k; rewrite tb_w2n_high by lia; rewrite Bool.andb_false_r; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "select_eq_select_0" *)
Theorem select_eq_select_0 : forall k n (w : word a),
  (k <= n)%N -> (n -- k) w = (n - k -- 0) (w >>> k).
Proof.
  intros k n w Hkn. apply word_eq_w2n. rewrite word_lsr_n2w, !w2n_bits, !MIN_min.
  pose proof (DIMINDEX_GT_0 a) as Hd.
  apply N.bits_inj; intros i. rewrite !tb_BITS, N.add_0_r.
  destruct (N.min_spec n (dimindex a - 1)) as [[Hn ->]|[Hn ->]];
    destruct (N.min_spec (n - k) (dimindex a - 1)) as [[Hn2 ->]|[Hn2 ->]];
    destruct (N.min_spec (dimindex a - 1) (dimindex a - 1)) as [[Hn3 ->]|[Hn3 ->]]; try lia;
    repeat match goal with |- context [(?x <? ?y)%N] => destruct (N.ltb_spec x y) end;
    cbn [andb]; try reflexivity; try lia;
    repeat (rewrite tb_w2n_high by lia); try reflexivity.
Qed.



End Words.

Section Lists.

(** HOL's free variable [q'] is quantified first. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "map_bitmap_APPEND" *)
Local Theorem map_bitmap_APPEND : forall {A} (q' : list A) x q stack p0 p1,
  filter_bitmap x stack = SOME (p0, p1) /\ LENGTH q = LENGTH p0 ->
  map_bitmap x (q ++ q') stack =
  match map_bitmap x q stack with
  | NONE => NONE
  | SOME (hd, (ts, ws)) => SOME (hd, (ts ++ q', ws))
  end.
Proof.
  intros A q' x; induction x as [|b x IH]; intros q stack p0 p1 [Hf Hl].
  - cbn in Hf |- *. injection Hf as <- <-. destruct q; [reflexivity|].
    rewrite !LENGTH_length in Hl; cbn in Hl; lia.
  - destruct stack as [|r stack]; [destruct b; discriminate|].
    destruct b; cbn in Hf |- *.
    + destruct (filter_bitmap x stack) as [[ts rs']|] eqn:E; [|discriminate]. injection Hf as <- <-.
      destruct q as [|t q]; [rewrite !LENGTH_length in Hl; cbn in Hl; lia|].
      cbn [app]. rewrite (IH q stack ts rs') by (split; [exact E|rewrite !LENGTH_length in *; cbn in Hl; lia]).
      destruct (map_bitmap x q stack) as [[? [? ?]]|]; reflexivity.
    + rewrite (IH q stack p0 p1) by (split; assumption).
      destruct (map_bitmap x q stack) as [[? [? ?]]|]; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "filter_bitmap_map_bitmap" *)
Theorem filter_bitmap_map_bitmap : forall {A} x (t q : list A) xs xs1 z ys ys1,
  filter_bitmap x t = SOME (xs, xs1) /\ LENGTH q = LENGTH xs /\ map_bitmap x q t = SOME (ys, (z, ys1)) ->
  z = [] /\ ys1 = xs1.
Proof.
  intros A x; induction x as [|b x IH]; intros t q xs xs1 z ys ys1 (Hf & Hl & Hm).
  - cbn in Hf, Hm. injection Hf as <- <-. injection Hm as <- <- <-.
    destruct q; [split; reflexivity|rewrite !LENGTH_length in Hl; cbn in Hl; lia].
  - destruct t as [|r t]; [destruct b; discriminate|].
    destruct b; cbn in Hf, Hm.
    + destruct (filter_bitmap x t) as [[ts rs']|] eqn:E; [|discriminate]. injection Hf as <- <-.
      destruct q as [|u q]; [discriminate|].
      destruct (map_bitmap x q t) as [[xs' [ys' zs']]|] eqn:Em; [|discriminate]. injection Hm as <- <- <-.
      apply (IH t q ts rs' _ xs' _). repeat split; [exact E| |exact Em].
      rewrite !LENGTH_length in *; cbn in Hl; lia.
    + destruct (map_bitmap x q t) as [[xs' [ys' zs']]|] eqn:Em; [|discriminate]. injection Hm as <- <- <-.
      apply (IH t q xs xs1 _ xs' _). repeat split; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "filter_bitmap_APPEND" *)
Local Theorem filter_bitmap_APPEND : forall {A} xs (stack : list A) ys,
  filter_bitmap (xs ++ ys) stack =
  match filter_bitmap xs stack with
  | NONE => NONE
  | SOME (zs, rs) =>
      match filter_bitmap ys rs with
      | NONE => NONE
      | SOME (zs2, rs) => SOME (zs ++ zs2, rs)
      end
  end.
Proof.
  intros A xs; induction xs as [|b xs IH]; intros stack ys.
  - cbn [app filter_bitmap]. destruct (filter_bitmap ys stack) as [[? ?]|]; reflexivity.
  - destruct stack as [|r stack]; [destruct b; reflexivity|].
    destruct b; cbn [app filter_bitmap]; rewrite IH.
    + destruct (filter_bitmap xs stack) as [[zs rs]|]; [|reflexivity].
      destruct (filter_bitmap ys rs) as [[? ?]|]; reflexivity.
    + reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "map_bitmap_IMP_LENGTH" *)
Theorem map_bitmap_IMP_LENGTH : forall {A} x (wl stack : list A) xs ys,
  map_bitmap x wl stack = SOME (xs, ys) -> LENGTH xs = LENGTH x.
Proof.
  intros A x; induction x as [|b x IH]; intros wl stack xs ys H.
  - cbn in H; injection H as <- _; reflexivity.
  - destruct b; cbn in H.
    + destruct wl as [|w wl]; [discriminate|]. destruct stack as [|r stack]; [discriminate|].
      destruct (map_bitmap x wl stack) as [[xs' [y1 z1]]|] eqn:E; [|discriminate]. injection H as <- _.
      specialize (IH _ _ _ _ E). rewrite !LENGTH_length in *; cbn [length]; lia.
    + destruct stack as [|r stack]; [destruct wl; discriminate|].
      destruct (map_bitmap x wl stack) as [[xs' [y1 z1]]|] eqn:E; [|discriminate]. injection H as <- _.
      specialize (IH _ _ _ _ E). rewrite !LENGTH_length in *; cbn [length]; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "filter_bitmap_IMP_LENGTH" *)
Theorem filter_bitmap_IMP_LENGTH : forall {A} x (stack : list A) q r,
  filter_bitmap x stack = SOME (q, r) -> LENGTH stack = (LENGTH x + LENGTH r)%N.
Proof.
  intros A x; induction x as [|b x IH]; intros stack q r H.
  - cbn in H; injection H as <- <-. rewrite !LENGTH_length; cbn [length]; lia.
  - destruct stack as [|s stack]; [destruct b; discriminate|].
    destruct b; cbn in H.
    + destruct (filter_bitmap x stack) as [[ts rs]|] eqn:E; [|discriminate]. injection H as <- <-.
      specialize (IH _ _ _ E). rewrite !LENGTH_length in *; cbn [length]; lia.
    + specialize (IH _ _ _ H). rewrite !LENGTH_length in *; cbn [length]; lia.
Qed.

Lemma EL_app_len {A} `{Inhabited A} (xs : list A) y ys : EL (LENGTH xs) (xs ++ y :: ys) = y.
Proof.
  induction xs as [|x xs IH]; [reflexivity|]. cbn [app]. rewrite LENGTH_length; cbn [length].
  rewrite Nat2N.inj_succ, EL_SUC. cbn [TL]. rewrite <- LENGTH_length. exact IH.
Qed.

(** HOL's free variables are quantified. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "EL_LENGTH_ADD_LEMMA" 307 *)
Local Theorem EL_LENGTH_ADD_LEMMA : forall {A} `{Inhabited A} (init old : list A) x st1,
  EL (LENGTH init + LENGTH old) (init ++ old ++ [x] ++ st1) = x.
Proof.
  intros A HA init old x st1. rewrite app_assoc.
  replace (LENGTH init + LENGTH old)%N with (LENGTH (init ++ old)) by (rewrite !LENGTH_length, app_length; lia).
  exact (EL_app_len (init ++ old) x st1).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "LUPDATE_LENGTH_ADD_LEMMA" *)
Local Theorem LUPDATE_LENGTH_ADD_LEMMA : forall {A} (w : A) (init old : list A) x st1,
  LUPDATE w (LENGTH init + LENGTH old) (init ++ old ++ [x] ++ st1) = init ++ old ++ [w] ++ st1.
Proof.
  intros A w init old x st1. rewrite !app_assoc.
  replace (LENGTH init + LENGTH old)%N with (LENGTH (init ++ old)) by (rewrite !LENGTH_length, app_length; lia).
  generalize (init ++ old) as l; intros l. induction l as [|y l IH]; [cbn; reflexivity|].
  cbn [app LUPDATE]. rewrite LENGTH_length; cbn [length].
  replace (N.of_nat (Datatypes.S (length l)) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
  f_equal. rewrite <- IH. f_equal. rewrite LENGTH_length. rewrite Nat2N.inj_succ, N.pred_succ. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "EL_LENGTH_ADD_LEMMA" 347 *)
Local Theorem EL_LENGTH_ADD_LEMMA_2 : forall {A} `{Inhabited A} n (xs : list A) y ys,
  LENGTH xs = n -> EL n (xs ++ y :: ys) = y.
Proof. intros A HA n xs y ys <-; apply EL_app_len. Qed.

End Lists.

(** ** Code tables and register maps *)

Section Basics.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.

(** Galette-only: field-wise equality of states. *)
Lemma state_ext (s t : state) :
  regs s = regs t -> fp_regs s = fp_regs t -> store s = store t -> stack s = stack t ->
  stack_space s = stack_space t -> memory s = memory t -> mdomain s = mdomain t ->
  sh_mdomain s = sh_mdomain t -> bitmaps s = bitmaps t -> stackSem.compile s = stackSem.compile t ->
  compile_oracle s = compile_oracle t -> code_buffer s = code_buffer t ->
  data_buffer s = data_buffer t -> gc_fun s = gc_fun t -> use_stack s = use_stack t ->
  use_store s = use_store t -> use_alloc s = use_alloc t -> clock s = clock t ->
  code s = code t -> ffi s = ffi t -> ffi_save_regs s = ffi_save_regs t -> be s = be t ->
  s = t.
Proof. destruct s, t; cbn; intros; subst; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "get_var_imm_case" *)
Local Theorem get_var_imm_case : forall ri (s : state),
  get_var_imm ri s = match ri with Reg n => get_var n s | Imm w => SOME (Word w) end.
Proof. intros [] s; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "prog_comp_lemma" *)
Local Theorem prog_comp_lemma :
  @prog_comp a = fun '(n, p) => (n, FST (comp n (next_lab p 2) p)).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "FST_prog_comp" *)
Theorem FST_prog_comp : forall pp : N * prog a, FST (prog_comp pp) = FST pp.
Proof. intros [n p]; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "lookup_IMP_lookup_compile" *)
Local Theorem lookup_IMP_lookup_compile : forall dest (s : state) x c,
  lookup dest (code s) = SOME x /\ dest <> gc_stub_location ->
  exists m1 n1, lookup dest (fromAList (compile c (toAList (code s)))) = SOME (FST (comp m1 n1 x)).
Proof.
  intros dest s x c [H Hd]. rewrite sptree.lookup_fromAList; unfold compile.
  rewrite ALOOKUP_APPEND. unfold stubs; cbn [ALOOKUP].
  destruct (decide (gc_stub_location = dest)) as [E|E]; [congruence|]. cbn beta iota.
  rewrite prog_comp_lemma, ALOOKUP_MAP_2, sptree.ALOOKUP_toAList, H. cbn.
  exists dest, (next_lab x 2); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "find_code_IMP_lookup" *)
Local Theorem find_code_IMP_lookup : forall dest (regs0 : fmap N (word_loc a)) (s : sptree.spt (prog a)) x,
  find_code dest regs0 s = SOME x ->
  exists k, lookup k s = SOME x /\ find_code dest regs0 = lookup k.
Proof.
  intros [d|r] regs0 s x H; cbn [find_code] in *.
  - exists d; split; [exact H|reflexivity].
  - destruct (FLOOKUP regs0 r) as [[w|l1 l2]|] eqn:EF; try discriminate.
    destruct (l2 =? 0) eqn:E; [|discriminate]. exists l1; split; [exact H|].
    apply functional_extensionality; intros cd; cbn [find_code]; rewrite EF, E; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "find_code_regs_SUBMAP" *)
Theorem find_code_regs_SUBMAP : forall (r1 r2 : fmap N (word_loc a)) dest (c0 : sptree.spt (prog a)) x,
  r1 ⊑ r2 /\ find_code dest r1 c0 = SOME x -> find_code dest r2 c0 = SOME x.
Proof.
  intros r1 r2 [d|r] c0 x [Hs H]; cbn [find_code] in *; [exact H|].
  destruct (FLOOKUP r1 r) as [v|] eqn:E; [|discriminate].
  rewrite (FLOOKUP_SUBMAP r1 r2 r v (conj Hs E)); exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "get_labels_comp" *)
Theorem get_labels_comp : forall n p (e : prog a), get_labels e SUBSET get_labels (FST (comp n p e)).
Proof.
  intros n p e; revert p.
  induction e as [ret dest h Hr Hh|p1 p2 IH1 IH2|c0 r ri p1 p2 IH1 IH2|q IH|q Hq]
    using prog_nested_ind; intros m;
    repeat match goal with H : context [_ SUBSET _] |- _ => progress (unfold pred_set.SUBSET in H) end; red.
  - destruct ret as [[p1 [lr [l1 l2]]]|]; cbn [comp get_labels FST fst]; [|intros x Hx; apply NOT_IN_EMPTY in Hx; contradiction].
    specialize (Hr p1 _ eq_refl m). destruct (comp n m p1) as [q1 m1] eqn:E1. cbn [fst] in Hr.
    destruct h as [[p2 [k1 k2]]|].
    + specialize (Hh p2 _ eq_refl m1). destruct (comp n m1 p2) as [q2 m2] eqn:E2. cbn [fst get_labels] in *.
      intros x Hx; rewrite !IN_INSERT, !IN_UNION, !IN_INSERT in *; destruct Hx as [Hx|[Hx|[Hx|Hx]]]; auto.
    + cbn [fst get_labels]. intros x Hx; rewrite !IN_INSERT, !IN_UNION in *; destruct Hx as [Hx|[Hx|Hx]]; auto; apply NOT_IN_EMPTY in Hx; contradiction.
  - cbn [comp]. specialize (IH1 m). destruct (comp n m p1) as [q1 m1].
    specialize (IH2 m1). destruct (comp n m1 p2) as [q2 m2]. cbn [fst get_labels] in *.
    intros x Hx; rewrite !IN_UNION in *; destruct Hx as [Hx|Hx]; auto.
  - cbn [comp]. specialize (IH1 m). destruct (comp n m p1) as [q1 m1].
    specialize (IH2 m1). destruct (comp n m1 p2) as [q2 m2]. cbn [fst get_labels] in *.
    intros x Hx; rewrite !IN_UNION in *; destruct Hx as [Hx|Hx]; auto.
  - cbn [comp]. specialize (IH m). destruct (comp n m q) as [q1 m1]. exact IH.
  - destruct q; try contradiction; cbn [comp fst get_labels]; try (intros x Hx; exact Hx);
      intros x Hx; apply NOT_IN_EMPTY in Hx; contradiction.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "loc_check_compile" *)
Theorem loc_check_compile : forall (s : state) l1 l2 c,
  loc_check (code s) (l1, l2) /\
  (forall k prog0, lookup k (code s) = SOME prog0 -> k <> gc_stub_location) ->
  loc_check (fromAList (compile c (toAList (code s)))) (l1, l2).
Proof.
  intros s l1 l2 c [H Hk]; unfold loc_check in *.
  destruct H as [[-> Hd]|(n & e & He & Hl)].
  - left; split; [reflexivity|].
    apply sptree.domain_lookup in Hd as [v Hv].
    destruct (lookup_IMP_lookup_compile l1 s v c (conj Hv (Hk _ _ Hv))) as (m1 & n1 & E).
    apply sptree.domain_lookup; eexists; exact E.
  - right. destruct (lookup_IMP_lookup_compile n s e c (conj He (Hk _ _ He))) as (m1 & n1 & E).
    exists n, (FST (comp m1 n1 e)); split; [exact E|]. apply get_labels_comp, Hl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "SUBMAP_DOMSUB_both" *)
Local Theorem SUBMAP_DOMSUB_both : forall (A B : fmap N (word_loc a)) c0, A ⊑ B -> A \\ c0 ⊑ B \\ c0.
Proof.
  intros A B c0 H. apply (proj1 (SUBMAP_DOMSUB_gen A B c0)). eapply SUBMAP_TRANS; split; [apply SUBMAP_DOMSUB|exact H].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "SUBMAP_FUPDATE_both" *)
Local Theorem SUBMAP_FUPDATE_both : forall (A B : fmap N (word_loc a)) n v, A ⊑ B -> A |+ (n, v) ⊑ B |+ (n, v).
Proof. intros A B n v H; apply SUBMAP_mono_FUPDATE, SUBMAP_DOMSUB_both, H. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "ALOOKUP_prog_comp" *)
Theorem ALOOKUP_prog_comp : forall (xs : list (N * prog a)) a0 y,
  ALOOKUP xs a0 = SOME y -> ALOOKUP (MAP prog_comp xs) a0 = SOME (FST (comp a0 (next_lab y 2) y)).
Proof.
  intros xs a0 y H; rewrite prog_comp_lemma, ALOOKUP_MAP_2, H; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "lookup_fromAList_prog_comp" *)
Theorem lookup_fromAList_prog_comp : forall x (s : state) p,
  lookup x (code s) = SOME p ->
  lookup x (fromAList (MAP prog_comp (toAList (code s)))) = SOME (FST (comp x (next_lab p 2) p)).
Proof.
  intros x s p H; rewrite sptree.lookup_fromAList; apply ALOOKUP_prog_comp.
  rewrite sptree.ALOOKUP_toAList; exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "alloc_length_stack" *)
Theorem alloc_length_stack : forall (c0 : word a) (s : state) r t conf,
  alloc c0 s = (r, t) /\ gc_fun s = word_gc_fun conf /\ (forall w, r <> SOME (Halt w)) ->
  LENGTH (stack t) = LENGTH (stack s).
Proof.
  intros c0 s r t conf (H & Hg & Hr). unfold alloc, gc in H; cbv zeta in H.
  cbn [stack set_store set_store_fld bitmaps stack_space memory mdomain store gc_fun] in H.
  destruct (LENGTH (stack s) <? stack_space s) eqn:El; [injection H as <- <-; reflexivity|].
  destruct (enc_stack _ _) as [wl|] eqn:Ee; [|injection H as <- <-; reflexivity].
  rewrite Hg in H.
  destruct (word_gc_fun conf _) as [[wl2 [m st]]|] eqn:Eg; [|injection H as <- <-; reflexivity].
  destruct (dec_stack _ _ _) as [stk1|] eqn:Ed; [|injection H as <- <-; reflexivity].
  apply dec_stack_length in Ed.
  assert (Hlen : LENGTH (stack (set_memory m (set_regs FEMPTY (set_store_fld st
                   (set_stack (TAKE (stack_space s) (stack s) ++ stk1) s))))) = LENGTH (stack s)).
  { cbn [stack set_memory set_regs set_store_fld set_stack].
    apply N.ltb_ge in El. rewrite !LENGTH_length, app_length in *. rewrite TAKE_firstn, DROP_skipn in *.
    rewrite firstn_length, skipn_length in *. lia. }
  destruct (FLOOKUP _ AllocSize) as [w|]; [|injection H as <- <-; exact Hlen].
  destruct (has_space _ _) as [[]|]; injection H as <- <-; try exact Hlen.
  exfalso; eapply Hr; reflexivity.
Qed.

(** ** Instructions on bigger register maps (Galette-only helpers) *)

Lemma exp_nested_ind (P : wordLang.exp a -> Prop) :
  (forall w, P (wordLang.Const w)) -> (forall n, P (wordLang.Var n)) ->
  (forall nm, P (wordLang.Lookup nm)) -> (forall e, P e -> P (wordLang.Load e)) ->
  (forall op l, Forall P l -> P (wordLang.Op op l)) ->
  (forall sh e1 e2, P e1 -> P e2 -> P (wordLang.Shift sh e1 e2)) -> forall e, P e.
Proof.
  intros HC HV HL HLd HO HS.
  exact (fix IH e := match e with
    | wordLang.Const w => HC w | wordLang.Var n => HV n | wordLang.Lookup nm => HL nm
    | wordLang.Load e => HLd e (IH e)
    | wordLang.Op op l => HO op l ((fix go l : Forall P l :=
         match l with [] => Forall_nil _ | x :: l => Forall_cons _ (IH x) (go l) end) l)
    | wordLang.Shift sh e1 e2 => HS sh e1 e2 (IH e1) (IH e2) end).
Qed.

Lemma word_exp_mono : forall e (s t : state) w,
  word_exp s e = SOME w -> regs s ⊑ regs t -> store s = store t -> memory s = memory t ->
  mdomain s = mdomain t -> word_exp t e = SOME w.
Proof.
  intros e; induction e as [w0|n|nm|e IH|op l IH|sh e1 e2 IH1 IH2] using exp_nested_ind;
    intros s t w H Hr Hst Hm Hd; cbn [word_exp] in *; unfold mem_load in *.
  - exact H.
  - destruct (FLOOKUP (regs s) n) as [v|] eqn:E; [|discriminate].
    rewrite (FLOOKUP_SUBMAP _ _ _ _ (conj Hr E)); exact H.
  - rewrite <- Hst; exact H.
  - destruct (word_exp s e) as [x|] eqn:E; [|discriminate].
    rewrite (IH s t x E Hr Hst Hm Hd), <- Hm, <- Hd; exact H.
  - assert (HM : forall l, Forall (fun e => forall (s t : state) w, word_exp s e = SOME w -> regs s ⊑ regs t ->
               store s = store t -> memory s = memory t -> mdomain s = mdomain t -> word_exp t e = SOME w) l ->
               EVERY IS_SOME (MAP (word_exp s) l) = true ->
               MAP (word_exp t) l = MAP (word_exp s) l).
    { intros l0 HF; induction HF as [|x l0 Hx HF IHF]; [reflexivity|].
      cbn [MAP EVERY]; intros He; apply andb_prop in He as [He1 He2].
      destruct (word_exp s x) as [v|] eqn:Ex; [|discriminate].
      rewrite (Hx s t v Ex Hr Hst Hm Hd), (IHF He2); reflexivity. }
    destruct (EVERY IS_SOME (MAP (word_exp s) l)) eqn:Ev; [|discriminate].
    rewrite (HM l IH Ev), Ev; exact H.
  - destruct (word_exp s e1) as [x1|] eqn:E1; [|discriminate].
    destruct (word_exp s e2) as [x2|] eqn:E2; [|discriminate].
    rewrite (IH1 s t x1 E1 Hr Hst Hm Hd), (IH2 s t x2 E2 Hr Hst Hm Hd); exact H.
Qed.

Lemma get_vars_mono : forall vs (s t : state) xs,
  get_vars vs s = SOME xs -> regs s ⊑ regs t -> get_vars vs t = SOME xs.
Proof.
  induction vs as [|v vs IH]; intros s t xs H Hr; cbn [get_vars] in *; [exact H|].
  unfold get_var in *. destruct (FLOOKUP (regs s) v) as [x|] eqn:E; [|discriminate].
  rewrite (FLOOKUP_SUBMAP _ _ _ _ (conj Hr E)).
  destruct (get_vars vs s) as [ys|] eqn:E2; [|discriminate]. rewrite (IH s t ys E2 Hr); exact H.
Qed.

Lemma inst_regs : forall (i : asm.inst a) (s t : state) R,
  inst i s = SOME t -> regs s ⊑ R ->
  exists R', inst i (set_regs R s) = SOME (set_regs R' t) /\ regs t ⊑ R'.
Proof.
  intros i s t R H Hs.
  destruct i as [| | x | m r [ad w] | f]; [| | destruct x as [? ? ? ri|? ? ? ri| | | | | |] |
    destruct m | destruct f];
    try (destruct ri);
    cbn [inst] in H |- *; unfold assign, mem_store, mem_load, get_var, get_fp_var in *;
    stk_split H; try discriminate H;
    repeat match goal with
           | E : (if classical_dec _ then _ else _) = SOME _ |- _ =>
               destruct (classical_dec _); [injection E as E|discriminate]
           end;
    try (injection H as <-);
    repeat match goal with
           | E : word_exp s ?e = SOME ?w |- _ =>
               rewrite (word_exp_mono e s (set_regs R s) w E Hs eq_refl eq_refl eq_refl); clear E
           | E : get_vars ?l s = SOME ?w |- _ =>
               rewrite (get_vars_mono l s (set_regs R s) w E Hs); clear E
           | E : FLOOKUP (regs s) ?r = SOME ?v |- _ =>
               cbn [regs set_regs]; rewrite (FLOOKUP_SUBMAP _ _ _ _ (conj Hs E)); clear E
           end;
    cbn [regs fp_regs memory mdomain be set_regs] in *;
    repeat match goal with
           | E : ?X = ?v |- context [?X] =>
               lazymatch v with SOME _ => idtac | NONE => idtac | true => idtac | false => idtac
                 | left _ => idtac | right _ => idtac end;
               rewrite E; cbn beta iota zeta
           end;
    try (eexists; split; [reflexivity|]);
    cbn [regs set_var set_fp_var set_regs set_fp_regs set_memory];
    repeat (first [apply SUBMAP_FUPDATE_both | exact Hs]).
  all: destruct (classical_dec _) as [?|Hn]; [|contradiction]; cbn beta iota; subst;
    eexists; (split; [reflexivity|]); cbn [regs set_var set_regs set_memory];
    repeat (first [apply SUBMAP_FUPDATE_both | exact Hs]).
Qed.

Lemma inst_stack_data : forall (i : asm.inst a) (s t : state),
  inst i s = SOME t -> stack t = stack s /\ data_buffer t = data_buffer s /\ code t = code s /\
  compile_oracle t = compile_oracle s /\ bitmaps t = bitmaps s.
Proof.
  intros i s t H.
  destruct i as [| | x | m r [ad w] | f]; [| | destruct x | destruct m | destruct f];
    cbn [inst] in H; unfold assign, mem_store in H; stk_split H; try discriminate;
    repeat match goal with
           | E : (if classical_dec _ then _ else _) = SOME _ |- _ =>
               destruct (classical_dec _); [injection E as <-|discriminate]
           end;
    injection H as <-; stk_fields; repeat split.
Qed.

(** Galette-only: the fields that [stack_alloc] changes (except the
    registers). *)
Definition frame (K : sptree.spt (prog a)) (Cr : cfg_t -> list (N * prog a) -> option (list word8 * cfg_t))
    (O : N -> cfg_t * (list (N * prog a) * list (word a))) (g : wordSem.gc_fun_type a) (X : state) : state :=
  set_code K (set_compile Cr (set_compile_oracle O (set_use_alloc false (set_use_store true
    (set_use_stack true (set_gc_fun g X)))))).

Lemma inst_frame : forall (i : asm.inst a) X K Cr O g,
  inst i (frame K Cr O g X) = OPTION_MAP (frame K Cr O g) (inst i X).
Proof.
  intros i X K Cr O g.
  assert (Hw : forall e, word_exp (frame K Cr O g X) e = word_exp X e) by (apply word_exp_cong; reflexivity).
  assert (Hv : forall l, get_vars l (frame K Cr O g X) = get_vars l X).
  { induction l as [|v l IH]; cbn [get_vars]; [reflexivity|]. rewrite IH; reflexivity. }
  destruct i as [| | x | m r [ad w] | f]; [| | destruct x | destruct m | destruct f];
    cbn [inst]; unfold assign; rewrite ?Hw, ?Hv; try reflexivity;
    unfold get_var, mem_load, mem_store, get_fp_var; cbn [regs fp_regs memory mdomain be frame
      set_code set_compile set_compile_oracle set_use_alloc set_use_store set_use_stack set_gc_fun];
    repeat (match goal with
            | |- context [classical_dec ?P] => destruct (classical_dec P); cbn beta iota
            | |- context [match ?x with _ => _ end] => destruct x eqn:?; cbn beta iota zeta
            end);
    reflexivity.
Qed.

(** Galette-only: the state [stack_alloc]'s code runs in. *)
Definition tr (compile_rest : cfg_t -> list (N * prog a) -> option (list word8 * cfg_t))
    (anything : wordSem.gc_fun_type a) (c : config) (R : fmap N (word_loc a)) (s : state) : state :=
  frame (fromAList (compile c (toAList (code s)))) compile_rest
    ((I ## (MAP prog_comp ## I)) ∘ compile_oracle s) anything (set_regs R s).

(** HOL's free variables are quantified first. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "inst_correct" *)
Local Theorem inst_correct : forall (i : asm.inst a) (s t : state) regs0 compile_rest anything c,
  inst i s = SOME t /\
  LENGTH (stack s) * (dimindex a DIV 8) < dimword a /\
  LENGTH (wordSem.buffer_buffer (data_buffer s)) + (LENGTH (bitmaps s) + wordSem.space_left (data_buffer s)) <
    dimword a - 1 /\
  regs s ⊑ regs0 ->
  exists regs1,
    inst i (set_code (fromAList (compile c (toAList (code s))))
             (set_use_alloc false (set_use_store true (set_use_stack true (set_gc_fun anything
               (set_compile_oracle ((I ## (MAP prog_comp ## I)) ∘ compile_oracle s)
                 (set_compile compile_rest (set_regs regs0 s)))))))) =
    SOME (set_code (fromAList (compile c (toAList (code t))))
             (set_use_alloc false (set_use_store true (set_use_stack true (set_gc_fun anything
               (set_compile_oracle ((I ## (MAP prog_comp ## I)) ∘ compile_oracle t)
                 (set_compile compile_rest (set_regs regs1 t)))))))) /\
    regs t ⊑ regs1 /\
    LENGTH (stack t) * (dimindex a DIV 8) < dimword a /\
    LENGTH (wordSem.buffer_buffer (data_buffer t)) + (LENGTH (bitmaps t) + wordSem.space_left (data_buffer t)) <
      dimword a - 1.
Proof.
  intros i s t regs0 compile_rest anything c (H & H1 & H2 & Hs).
  destruct (inst_regs i s t regs0 H Hs) as (R' & HR & HR').
  pose proof (inst_stack_data i s t H) as (Est & Edb & Ecd & Eor & Ebm).
  exists R'.
  change (inst i (tr compile_rest anything c regs0 s) = SOME (tr compile_rest anything c R' t) /\
          regs t ⊑ R' /\ LENGTH (stack t) * (dimindex a DIV 8) < dimword a /\
          LENGTH (wordSem.buffer_buffer (data_buffer t)) + (LENGTH (bitmaps t) +
            wordSem.space_left (data_buffer t)) < dimword a - 1).
  unfold tr; rewrite inst_frame, HR; cbn [OPTION_MAP option_map].
  rewrite Ecd, Eor, Est, Edb, Ebm. repeat split; assumption.
Qed.

(** Rewriting the projections and updates of [tr] (Galette-only). *)
Lemma fp_regs_tr cr g c R s : fp_regs (tr cr g c R s) = fp_regs s. Proof. reflexivity. Qed.
Lemma store_tr cr g c R s : store (tr cr g c R s) = store s. Proof. reflexivity. Qed.
Lemma stack_tr cr g c R s : stack (tr cr g c R s) = stack s. Proof. reflexivity. Qed.
Lemma stack_space_tr cr g c R s : stack_space (tr cr g c R s) = stack_space s. Proof. reflexivity. Qed.
Lemma memory_tr cr g c R s : memory (tr cr g c R s) = memory s. Proof. reflexivity. Qed.
Lemma mdomain_tr cr g c R s : mdomain (tr cr g c R s) = mdomain s. Proof. reflexivity. Qed.
Lemma sh_mdomain_tr cr g c R s : sh_mdomain (tr cr g c R s) = sh_mdomain s. Proof. reflexivity. Qed.
Lemma bitmaps_tr cr g c R s : bitmaps (tr cr g c R s) = bitmaps s. Proof. reflexivity. Qed.
Lemma code_buffer_tr cr g c R s : code_buffer (tr cr g c R s) = code_buffer s. Proof. reflexivity. Qed.
Lemma data_buffer_tr cr g c R s : data_buffer (tr cr g c R s) = data_buffer s. Proof. reflexivity. Qed.
Lemma clock_tr cr g c R s : clock (tr cr g c R s) = clock s. Proof. reflexivity. Qed.
Lemma ffi_tr cr g c R s : ffi (tr cr g c R s) = ffi s. Proof. reflexivity. Qed.
Lemma ffi_save_regs_tr cr g c R s : ffi_save_regs (tr cr g c R s) = ffi_save_regs s. Proof. reflexivity. Qed.
Lemma be_tr cr g c R s : be (tr cr g c R s) = be s. Proof. reflexivity. Qed.
Lemma regs_tr cr g c R s : regs (tr cr g c R s) = R. Proof. reflexivity. Qed.
Lemma compile_tr cr g c R s : stackSem.compile (tr cr g c R s) = cr. Proof. reflexivity. Qed.
Lemma compile_oracle_tr cr g c R s : compile_oracle (tr cr g c R s) = (I ## (MAP prog_comp ## I)) ∘ compile_oracle s. Proof. reflexivity. Qed.
Lemma code_tr cr g c R s : code (tr cr g c R s) = fromAList (compile c (toAList (code s))). Proof. reflexivity. Qed.
Lemma gc_fun_tr cr g c R s : gc_fun (tr cr g c R s) = g. Proof. reflexivity. Qed.
Lemma use_stack_tr cr g c R s : use_stack (tr cr g c R s) = true. Proof. reflexivity. Qed.
Lemma use_store_tr cr g c R s : use_store (tr cr g c R s) = true. Proof. reflexivity. Qed.
Lemma use_alloc_tr cr g c R s : use_alloc (tr cr g c R s) = false. Proof. reflexivity. Qed.
Lemma set_clock_tr cr g c R s k : set_clock k (tr cr g c R s) = tr cr g c R (set_clock k s). Proof. reflexivity. Qed.
Lemma set_stack_tr cr g c R s k : set_stack k (tr cr g c R s) = tr cr g c R (set_stack k s). Proof. reflexivity. Qed.
Lemma set_stack_space_tr cr g c R s k : set_stack_space k (tr cr g c R s) = tr cr g c R (set_stack_space k s). Proof. reflexivity. Qed.
Lemma set_memory_tr cr g c R s k : set_memory k (tr cr g c R s) = tr cr g c R (set_memory k s). Proof. reflexivity. Qed.
Lemma set_store_fld_tr cr g c R s k : set_store_fld k (tr cr g c R s) = tr cr g c R (set_store_fld k s). Proof. reflexivity. Qed.
Lemma set_fp_regs_tr cr g c R s k : set_fp_regs k (tr cr g c R s) = tr cr g c R (set_fp_regs k s). Proof. reflexivity. Qed.
Lemma set_ffi_tr cr g c R s k : set_ffi k (tr cr g c R s) = tr cr g c R (set_ffi k s). Proof. reflexivity. Qed.
Lemma set_code_buffer_tr cr g c R s k : set_code_buffer k (tr cr g c R s) = tr cr g c R (set_code_buffer k s). Proof. reflexivity. Qed.
Lemma set_data_buffer_tr cr g c R s k : set_data_buffer k (tr cr g c R s) = tr cr g c R (set_data_buffer k s). Proof. reflexivity. Qed.
Lemma set_bitmaps_tr cr g c R s k : set_bitmaps k (tr cr g c R s) = tr cr g c R (set_bitmaps k s). Proof. reflexivity. Qed.
Lemma dec_clock_tr cr g c R s : dec_clock (tr cr g c R s) = tr cr g c R (dec_clock s). Proof. reflexivity. Qed.
Lemma set_store_tr cr g c R s v x : set_store v x (tr cr g c R s) = tr cr g c R (set_store v x s). Proof. reflexivity. Qed.
Lemma set_fp_var_tr cr g c R s v x : set_fp_var v x (tr cr g c R s) = tr cr g c R (set_fp_var v x s). Proof. reflexivity. Qed.
Lemma set_var_tr cr g c R s v x : set_var v x (tr cr g c R s) = tr cr g c (R |+ (v, x)) (set_var v x s). Proof. reflexivity. Qed.
Lemma set_regs_tr cr g c R s X : set_regs X (tr cr g c R s) = tr cr g c X (set_regs X s). Proof. reflexivity. Qed.
Lemma empty_env_tr cr g c R s : empty_env (tr cr g c R s) = tr cr g c FEMPTY (empty_env s). Proof. reflexivity. Qed.
Lemma unset_var_tr cr g c R s v : unset_var v (tr cr g c R s) = tr cr g c (R \\ v) (unset_var v s). Proof. reflexivity. Qed.


Lemma get_var_tr cr g c R (s : state) v x : get_var v s = SOME x -> regs s ⊑ R -> get_var v (tr cr g c R s) = SOME x.
Proof. intros H Hs; unfold get_var in *; rewrite regs_tr; exact (FLOOKUP_SUBMAP _ _ _ _ (conj Hs H)). Qed.

Lemma get_var_imm_tr cr g c R (s : state) ri x :
  get_var_imm ri s = SOME x -> regs s ⊑ R -> get_var_imm ri (tr cr g c R s) = SOME x.
Proof. destruct ri; cbn [get_var_imm]; [apply get_var_tr|intros H _; exact H]. Qed.

Lemma word_exp_tr cr g c R (s : state) e w :
  word_exp s e = SOME w -> regs s ⊑ R -> word_exp (tr cr g c R s) e = SOME w.
Proof. intros H Hs; exact (word_exp_mono e s (tr cr g c R s) w H Hs eq_refl eq_refl eq_refl). Qed.

Lemma get_vars_tr cr g c R (s : state) l xs :
  get_vars l s = SOME xs -> regs s ⊑ R -> get_vars l (tr cr g c R s) = SOME xs.
Proof. intros H Hs; exact (get_vars_mono l s (tr cr g c R s) xs H Hs). Qed.

End Basics.

Create HintDb tre.
#[global] Hint Rewrite @fp_regs_tr @store_tr @stack_tr @stack_space_tr @memory_tr @mdomain_tr @sh_mdomain_tr @bitmaps_tr @code_buffer_tr @data_buffer_tr @clock_tr @ffi_tr @ffi_save_regs_tr @be_tr @regs_tr @compile_tr @compile_oracle_tr @code_tr @gc_fun_tr @use_stack_tr @use_store_tr @use_alloc_tr @set_clock_tr @set_stack_tr @set_stack_space_tr @set_memory_tr @set_store_fld_tr @set_fp_regs_tr @set_ffi_tr @set_code_buffer_tr @set_data_buffer_tr @set_bitmaps_tr @dec_clock_tr @set_store_tr @set_fp_var_tr @set_var_tr @set_regs_tr @empty_env_tr @unset_var_tr : tre.

(** ** Symbolic execution of stackLang code (Galette-only) *)

Section Sym.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Implicit Types X Y : state.
Local Open Scope fmap_scope.

Lemma ev_seq (p1 p2 : prog a) X :
  evaluate (Seq p1 p2, X) =
  let '(res, s1) := evaluate (p1, X) in match res with NONE => evaluate (p2, s1) | _ => (res, s1) end.
Proof. rewrite evaluate_eqn; cbn [evaluate_body]; rewrite fix_clock_evaluate; reflexivity. Qed.

Lemma ev_inst (i : asm.inst a) X :
  evaluate (Inst i, X) = match inst i X with SOME s1 => (NONE, s1) | NONE => (SOME Error, X) end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_skip X : evaluate (Skip, X) = (NONE, X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_if cmp0 r1 ri (c1 c2 : prog a) X :
  evaluate (If cmp0 r1 ri c1 c2, X) =
  match get_var r1 X, get_var_imm ri X with
  | SOME x, SOME y =>
      match wordSem.word_cmp cmp0 x y with
      | SOME true => evaluate (c1, X)
      | SOME false => evaluate (c2, X)
      | NONE => (SOME Error, X)
      end
  | _, _ => (SOME Error, X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_loop (c1 : prog a) X :
  evaluate (Loop c1, X) =
  let '(res, s1) := evaluate (c1, X) in
  if cont_loop res then
    (if (clock s1 =? 0)%N then (SOME TimeOut, empty_env s1) else evaluate (Loop c1, dec_clock s1))
  else (exit_loop res, s1).
Proof. rewrite evaluate_eqn; cbn [evaluate_body]; rewrite fix_clock_evaluate; reflexivity. Qed.

Lemma ev_break n X : evaluate (stackLang.Break n, X) = (SOME (Break n), X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_get v name X :
  evaluate (Get v name, X) =
  if negb (use_store X) then (SOME Error, X) else
  match FLOOKUP (store X) name with SOME x => (NONE, set_var v x X) | NONE => (SOME Error, X) end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_set name v X :
  evaluate (Set_ name v, X) =
  if negb (use_store X) then (SOME Error, X) else
  match get_var v X with SOME w => (NONE, set_store name w X) | NONE => (SOME Error, X) end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma FLOOKUP_UPD (f : fmap N (word_loc a)) k1 v k2 :
  FLOOKUP (f |+ (k1, v)) k2 = if (k1 =? k2)%N then SOME v else FLOOKUP f k2.
Proof. rewrite FLOOKUP_UPDATE; destruct (decide (k1 = k2)) as [->|E]; [rewrite N.eqb_refl; reflexivity|].
  apply N.eqb_neq in E; rewrite E; reflexivity. Qed.

Lemma FLOOKUP_UPD_store (f : fmap store_name (word_loc a)) k1 v k2 :
  FLOOKUP (f |+ (k1, v)) k2 = if decide (k1 = k2) then SOME v else FLOOKUP f k2.
Proof. apply FLOOKUP_UPDATE. Qed.

Lemma sx_store_upd (f : fmap store_name (word_loc a)) k1 v k2 :
  FLOOKUP (f |+ (k1, v)) k2 = if decide (k1 = k2) then SOME v else FLOOKUP f k2.
Proof. apply FLOOKUP_UPDATE. Qed.

Lemma ev_halt v X :
  evaluate (stackLang.Halt v, X) =
  match get_var v X with SOME w => (SOME (Halt w), empty_env X) | NONE => (SOME Error, X) end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

End Sym.

(** Normalisation of states: [set_regs] outermost, then [set_memory],
    [set_store_fld], [set_stack], [set_clock]. *)
Lemma nf_mem_regs {a c f} M R (X : stackSem.state a c f) : set_memory M (set_regs R X) = set_regs R (set_memory M X). Proof. reflexivity. Qed.
Lemma nf_clock_regs {a c f} k R (X : stackSem.state a c f) : set_clock k (set_regs R X) = set_regs R (set_clock k X). Proof. reflexivity. Qed.
Lemma nf_clock_mem {a c f} k M (X : stackSem.state a c f) : set_clock k (set_memory M X) = set_memory M (set_clock k X). Proof. reflexivity. Qed.
Lemma nf_clock_store {a c f} k st (X : stackSem.state a c f) : set_clock k (set_store_fld st X) = set_store_fld st (set_clock k X). Proof. reflexivity. Qed.
Lemma nf_clock_stack {a c f} k st (X : stackSem.state a c f) : set_clock k (set_stack st X) = set_stack st (set_clock k X). Proof. reflexivity. Qed.
Lemma nf_store_regs {a c f} st R (X : stackSem.state a c f) : set_store_fld st (set_regs R X) = set_regs R (set_store_fld st X). Proof. reflexivity. Qed.
Lemma nf_store_mem {a c f} st M (X : stackSem.state a c f) : set_store_fld st (set_memory M X) = set_memory M (set_store_fld st X). Proof. reflexivity. Qed.
Lemma nf_stack_regs {a c f} st R (X : stackSem.state a c f) : set_stack st (set_regs R X) = set_regs R (set_stack st X). Proof. reflexivity. Qed.
Lemma nf_stack_mem {a c f} st M (X : stackSem.state a c f) : set_stack st (set_memory M X) = set_memory M (set_stack st X). Proof. reflexivity. Qed.
Lemma nf_stack_store {a c f} st M (X : stackSem.state a c f) : set_stack st (set_store_fld M X) = set_store_fld M (set_stack st X). Proof. reflexivity. Qed.
Lemma nf_regs_regs {a c f} R R' (X : stackSem.state a c f) : set_regs R (set_regs R' X) = set_regs R X. Proof. reflexivity. Qed.
Lemma nf_mem_mem {a c f} M M' (X : stackSem.state a c f) : set_memory M (set_memory M' X) = set_memory M X. Proof. reflexivity. Qed.
Lemma nf_clock_clock {a c f} k k' (X : stackSem.state a c f) : set_clock k (set_clock k' X) = set_clock k X. Proof. reflexivity. Qed.
Lemma nf_store_store {a c f} M M' (X : stackSem.state a c f) : set_store_fld M (set_store_fld M' X) = set_store_fld M X. Proof. reflexivity. Qed.
Lemma nf_stack_stack {a c f} M M' (X : stackSem.state a c f) : set_stack M (set_stack M' X) = set_stack M X. Proof. reflexivity. Qed.
Lemma nf_set_var {a c f} v x (X : stackSem.state a c f) : set_var v x X = set_regs (regs X |+ (v, x)) X. Proof. reflexivity. Qed.
Lemma nf_set_store {a c f} v x (X : stackSem.state a c f) : set_store v x X = set_store_fld (store X |+ (v, x)) X. Proof. reflexivity. Qed.
Lemma nf_dec_clock {a c f} (X : stackSem.state a c f) : dec_clock X = set_clock (clock X - 1) X. Proof. reflexivity. Qed.
Create HintDb nf.
#[global] Hint Rewrite @nf_mem_regs @nf_clock_regs @nf_clock_mem @nf_clock_store @nf_clock_stack @nf_store_regs
  @nf_store_mem @nf_stack_regs @nf_stack_mem @nf_stack_store @nf_regs_regs @nf_mem_mem @nf_clock_clock
  @nf_store_store @nf_stack_stack @nf_set_var @nf_set_store @nf_dec_clock : nf.

Ltac nf_fields :=
  cbn [regs fp_regs store stack stack_space memory mdomain sh_mdomain bitmaps stackSem.compile
       compile_oracle code_buffer data_buffer gc_fun use_stack use_store use_alloc clock code
       ffi ffi_save_regs be set_regs set_memory set_clock set_store_fld set_stack
       set_code set_gc_fun set_use_alloc set_use_stack set_use_store set_compile set_compile_oracle
       set_bitmaps set_data_buffer set_code_buffer set_ffi set_fp_regs set_stack_space set_mdomain
       set_sh_mdomain set_be set_ffi_save_regs].

Lemma w_add0 {a} (w : word a) : (w + n2w 0)%w = w. Proof. exact (proj1 WORD_ADD_0 w). Qed.
Lemma w_0add {a} (w : word a) : (n2w 0 + w)%w = w. Proof. exact (proj2 WORD_ADD_0 w). Qed.

Ltac sx_simp :=
  repeat progress (
    nf_fields; autorewrite with nf; nf_fields; unfold assign, get_var;
    cbn [IS_SOME THE andb orb negb wordLang.word_op FOLDR List.map EVERY word_exp inst
      get_var_imm wordSem.word_cmp];
    rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb];
    repeat match goal with H : FLOOKUP ?R ?k = SOME ?v |- context [FLOOKUP ?R ?k] => rewrite H end;
    rewrite ?w_add0, ?w_0add;
    repeat match goal with |- context [bool_decide (?x = ?y)] =>
      first [ rewrite (proj2 (bool_decide_spec (x = y)) eq_refl)
            | let E := fresh in
              assert (E : bool_decide (x = y) = false)
                by (apply Bool.not_true_iff_false; rewrite bool_decide_spec; discriminate);
              rewrite E; clear E ] end;
    unfold mem_load, mem_store;
    repeat match goal with |- context [classical_dec ?P] =>
      let Hc := fresh "Hc" in destruct (classical_dec P) as [Hc|Hc]; [clear Hc|exfalso; apply Hc; assumption] end).

(** One symbolic step (loops are unrolled explicitly with [ev_while]). *)
Ltac sx_step :=
  first
    [ rewrite ev_seq | rewrite ev_inst | rewrite ev_skip | rewrite ev_if
    | rewrite ev_break | rewrite ev_get | rewrite ev_set | rewrite ev_halt ].

Ltac sx_dec :=
  repeat match goal with
         | |- context [decide (?x = ?y)] =>
             first [ let E := fresh in destruct (decide (x = y)) as [E|_]; [discriminate E|]
                   | let E := fresh in destruct (decide (x = y)) as [_|E]; [|exfalso; apply E; reflexivity] ]
         | H : context [decide (?x = ?y)] |- _ =>
             first [ let E := fresh in destruct (decide (x = y)) as [E|_]; [discriminate E|]
                   | let E := fresh in destruct (decide (x = y)) as [_|E]; [|exfalso; apply E; reflexivity] ]
         end.

Ltac sx_all := repeat (sx_step; sx_simp; rewrite ?sx_store_upd; sx_dec; sx_simp).


Section Memcpy.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.
Local Open Scope word_scope.

Lemma ev_while cmp0 r ri (body : prog a) (X : state) :
  evaluate (While cmp0 r ri body, X) =
  match get_var r X, get_var_imm ri X with
  | SOME x, SOME y =>
      match wordSem.word_cmp cmp0 x y with
      | SOME true =>
          let '(res, s1) := evaluate (body, X) in
          if cont_loop res then
            (if (clock s1 =? 0)%N then (SOME TimeOut, empty_env s1) else evaluate (While cmp0 r ri body, dec_clock s1))
          else (exit_loop res, s1)
      | SOME false => (NONE, X)
      | NONE => (SOME Error, X)
      end
  | _, _ => (SOME Error, X)
  end.
Proof.
  rewrite ev_loop, ev_if. destruct (get_var r X), (get_var_imm ri X); try reflexivity.
  destruct (wordSem.word_cmp cmp0 _ _) as [[]|]; try reflexivity; rewrite ev_break; reflexivity.
Qed.




(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "memcpy_code_thm" 390 *)
Local Theorem memcpy_code_thm_n : forall n a0 b m dm b1 m1 (s : state),
  memcpy (n2w n) a0 b m dm = (b1, (m1, true)) /\ (n < dimword a)%N /\
  memory s = m /\ mdomain s = dm /\
  get_var 0 s = SOME (Word (n2w n)) /\ 1 IN FDOM (regs s) /\
  get_var 2 s = SOME (Word a0) /\ get_var 3 s = SOME (Word b) ->
  exists r1,
    evaluate (memcpy_code, set_clock (clock s + n) s) =
    (NONE, set_regs (regs s |++ [(0, Word (n2w 0)); (1, r1); (2, Word (a0 + n2w n * bytes_in_word));
                                 (3, Word b1)]) (set_memory m1 s)).
Proof.
  induction n as [|n IH] using N.peano_ind; intros a0 b m dm b1 m1 s (Hm & Hn & Hmem & Hdm & H0 & H1 & H2 & H3).
  - rewrite memcpy_def in Hm. destruct (decide _) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
    injection Hm as <- <-. assert (H1' : FLOOKUP (regs s) 1 <> None) by exact H1.
    destruct (FLOOKUP (regs s) 1) as [r1|] eqn:E1; [|contradiction].
    exists r1. unfold memcpy_code. rewrite ev_while. unfold get_var in *. sx_simp.
    rewrite N.add_0_r. subst m. f_equal. apply state_ext; nf_fields; try reflexivity.
    apply fmap_ext; intros k. cbn [FUPDATE_LIST FOLDL]. rewrite !FLOOKUP_UPD.
    repeat match goal with |- context [(?x =? ?y)%N] => destruct (N.eqb_spec x y) as [<-|?] end;
      try reflexivity; try congruence.
    replace (a0 + n2w 0 * bytes_in_word) with a0 by word_ring; exact H2.
  - assert (Hne : (n2w (N.succ n) : word a) <> n2w 0).
    { intros E; apply n2w_11 in E. rewrite !N.mod_small in E by (pose proof (ZERO_LT_dimword a); lia). lia. }
    rewrite memcpy_def in Hm. destruct (decide _) as [E|_]; [contradiction|].
    replace (n2w (N.succ n) - n2w 1 : word a) with (n2w n : word a) in Hm
      by (rewrite <- N.add_1_r, <- word_add_n2w; word_ring).
    destruct (memcpy (n2w n) _ _ _ _) as [b1' [m1' c1]] eqn:Ein.
    injection Hm as -> -> Hc. apply andb_prop in Hc as [-> Hc]; apply andb_prop in Hc as [Ha Hb].
    apply bool_decide_spec in Ha, Hb. subst m dm.
    unfold get_var in *.
    destruct (IH (a0 + bytes_in_word) (b + bytes_in_word) ((b =+ memory s a0) (memory s)) (mdomain s) b1 m1
       (set_regs (regs s |+ (1, memory s a0) |+ (2, Word (a0 + bytes_in_word)) |+ (0, Word (n2w n))
                   |+ (3, Word (b + bytes_in_word))) (set_memory ((b =+ memory s a0) (memory s)) s)))
      as [r1 Hr1].
    { repeat split; try reflexivity; try lia; try assumption; cbn [regs set_regs mdomain memory set_memory];
        rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; try reflexivity. unfold FDOM, pred_set.IN. rewrite FLOOKUP_UPD; cbn. discriminate. }
    exists r1. unfold memcpy_code. rewrite ev_while. sx_simp.
    rewrite (proj1 (Bool.not_true_iff_false (bool_decide (n2w (N.succ n) = n2w 0 :> word a)))
               ltac:(intros E; apply bool_decide_spec in E; exact (Hne E))); cbn [negb].
    sx_simp. cbn [list_Seq]. repeat (sx_step; sx_simp).
    cbn [cont_loop]. replace (clock s + N.succ n =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    replace (n2w (N.succ n) - n2w 1 : word a) with (n2w n : word a)
      by (rewrite <- N.add_1_r, <- word_add_n2w; word_ring).
    replace (clock s + N.succ n - 1)%N with (clock s + n)%N by lia.
    rewrite <- nf_clock_mem, <- nf_clock_regs.
    refine (eq_trans Hr1 _). f_equal. apply state_ext; nf_fields; try reflexivity.
    apply fmap_ext; intros k. cbn [FUPDATE_LIST FOLDL]. rewrite !FLOOKUP_UPD.
    repeat match goal with |- context [(?x =? ?y)%N] => destruct (N.eqb_spec x y) as [<-|?] end;
      try reflexivity; try congruence.
    f_equal; f_equal. rewrite <- N.add_1_r, <- word_add_n2w; word_ring.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "memcpy_code_thm" 444 *)
Theorem memcpy_code_thm : forall (w a0 b : word a) m dm b1 m1 (s : state),
  memcpy w a0 b m dm = (b1, (m1, true)) /\
  memory s = m /\ mdomain s = dm /\
  get_var 0 s = SOME (Word w) /\ 1 IN FDOM (regs s) /\
  get_var 2 s = SOME (Word a0) /\ get_var 3 s = SOME (Word b) ->
  exists r1,
    evaluate (memcpy_code, set_clock (clock s + w2n w) s) =
    (NONE, set_regs (regs s |++ [(0, Word (n2w 0)); (1, r1); (2, Word (a0 + w * bytes_in_word));
                                 (3, Word b1)]) (set_memory m1 s)).
Proof.
  intros w a0 b m dm b1 m1 s (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  destruct (memcpy_code_thm_n (w2n w) a0 b m dm b1 m1 s) as [r1 E].
  { rewrite !n2w_w2n. repeat split; try assumption. apply w2n_lt. }
  exists r1. rewrite n2w_w2n in E. exact E.
Qed.

End Memcpy.

(** ** The GC stub: no collector ([gc_kind_None]) *)

Section EncDec.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "filter_bitmap_map_bitmap_IMP" *)
Local Theorem filter_bitmap_map_bitmap_IMP : forall {A} x (ws : list A) q r x' q' q'' r'',
  filter_bitmap x ws = SOME (q, r) /\ map_bitmap x (q ++ x') ws = SOME (q', (q'', r'')) ->
  q'' = x' /\ r = r'' /\ ws = q' ++ r.
Proof.
  intros A x; induction x as [|b x IH]; intros ws q r x' q' q'' r'' [Hf Hm].
  - cbn in Hf, Hm. injection Hf as <- <-. injection Hm as <- <- <-. repeat split; reflexivity.
  - destruct ws as [|w ws]; [destruct b; discriminate|].
    destruct b; cbn in Hf, Hm.
    + destruct (filter_bitmap x ws) as [[ts rs]|] eqn:E; [|discriminate]. injection Hf as <- <-.
      cbn [app] in Hm. destruct (map_bitmap x (ts ++ x') ws) as [[xs' [ys' zs']]|] eqn:Em; [|discriminate].
      injection Hm as <- <- <-. destruct (IH ws ts rs x' xs' ys' zs' (conj E Em)) as (-> & -> & ->).
      repeat split; reflexivity.
    + destruct (map_bitmap x (q ++ x') ws) as [[xs' [ys' zs']]|] eqn:Em; [|discriminate].
      injection Hm as <- <- <-. destruct (IH ws q r x' xs' ys' zs' (conj Hf Em)) as (-> & -> & ->).
      repeat split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "enc_dec_stack" *)
Local Theorem enc_dec_stack : forall (bs : list (word a)) ys2 x1 x2,
  enc_stack bs ys2 = SOME x1 /\ dec_stack bs x1 ys2 = SOME x2 -> ys2 = x2.
Proof.
  intros bs ys2. remember (length ys2) as n eqn:Hn. revert ys2 Hn.
  induction n as [n IH] using (well_founded_induction lt_wf).
  intros ys2 Hn x1 x2 [He Hd].
  destruct ys2 as [|w ws]; [rewrite (proj1 enc_stack_def) in He; discriminate|].
  rewrite (proj2 enc_stack_def) in He. rewrite (proj2 dec_stack_def) in Hd.
  destruct (bool_decide (w = Word (n2w 0))) eqn:Ew.
  - apply bool_decide_spec in Ew; subst w.
    destruct (bool_decide (ws = [])) eqn:Ews; [|discriminate]. apply bool_decide_spec in Ews; subst ws.
    injection He as <-. cbn in Hd. injection Hd as <-. reflexivity.
  - destruct (full_read_bitmap bs w) as [b|] eqn:Eb; [|discriminate].
    destruct (filter_bitmap b ws) as [[ts ws']|] eqn:Ef; [|discriminate].
    destruct (enc_stack bs ws') as [rs|] eqn:Er; [|discriminate]. injection He as <-.
    destruct (map_bitmap b (ts ++ rs) ws) as [[hd [ts' ws'']]|] eqn:Em; [|discriminate].
    destruct (dec_stack bs ts' ws'') as [rest|] eqn:Edr; [|discriminate]. injection Hd as <-.
    destruct (filter_bitmap_map_bitmap_IMP b ws ts ws' rs hd ts' ws'' (conj Ef Em)) as (E1 & E2 & Hws).
    subst ts' ws''.
    pose proof (IH (length ws') ltac:(apply filter_bitmap_LENGTH in Ef; rewrite !LENGTH_length in Ef;
                                   subst n; cbn [length]; lia) ws' eq_refl rs rest (conj Er Edr)) as Hr.
    subst ws ws'. reflexivity.
Qed.

End EncDec.

Section AllocNone.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "alloc_correct_lemma_None" *)
Theorem alloc_correct_lemma_None : forall (w : word a) (s : state) r t conf l ret c anything,
  alloc w s = (r, t) /\ r <> SOME Error /\ gc_fun s = word_gc_fun conf /\ gc_kind conf = gc_kind_None /\
  LENGTH (bitmaps s) < dimword a - 1 /\ LENGTH (stack s) * (dimindex a DIV 8) < dimword a /\
  FLOOKUP l 0 = SOME ret /\ FLOOKUP l 1 = SOME (Word w) ->
  exists ck l2,
    evaluate (word_gc_code conf,
              set_code (fromAList (compile c (toAList (code s))))
                (set_gc_fun anything (set_regs l (set_clock (clock s + ck)
                  (set_use_alloc false (set_use_stack true (set_use_store true s))))))) =
    (r, set_gc_fun anything (set_regs l2 (set_code (fromAList (compile c (toAList (code s))))
          (set_use_alloc false (set_use_stack true (set_use_store true t)))))) /\
    (r <> NONE -> r = SOME (Halt (Word (n2w 1)))) /\ regs t ⊑ l2 /\ (r = NONE -> FLOOKUP l2 0 = SOME ret).
Proof.
  intros w s r t conf l ret c anything (H & Hr & Hgc & Hk & Hbm & Hst & Hl0 & Hl1).
  unfold alloc, gc, set_store in H. stk_fields. rewrite Hgc in H.
  destruct (LENGTH (stack s) <? stack_space s) eqn:Ess; [injection H as <- _; exfalso; apply Hr; reflexivity|].
  destruct (enc_stack _ _) as [wl|] eqn:Ee; [|injection H as <- _; exfalso; apply Hr; reflexivity].
  unfold word_gc_fun in H. rewrite Hk in H. cbv zeta in H.
  destruct (⌜word_gc_fun_assum conf _⌝) eqn:Ea; [|injection H as <- _; exfalso; apply Hr; reflexivity].
  apply bool_decide_spec in Ea.
  destruct Ea as (Hsub & _ & Hcurr & _).
  assert (Hc : exists old, FLOOKUP (store s) CurrHeap = SOME (Word old)).
  { assert (Hin : CurrHeap IN FDOM (store s |+ (AllocSize, Word w)))
      by (apply Hsub; rewrite !IN_INSERT; auto).
    unfold FDOM, pred_set.IN in Hin. rewrite sx_store_upd in Hin. sx_dec.
    unfold FAPPLY in Hcurr. rewrite sx_store_upd in Hcurr. sx_dec.
    destruct (FLOOKUP (store s) CurrHeap) as [[cv|l1 l2]|]; [eexists; reflexivity|discriminate|contradiction]. }
  destruct Hc as [old Hold].
  assert (Hfa : FAPPLY (store s |+ (AllocSize, Word w)) CurrHeap = Word old)
    by (unfold FAPPLY; rewrite sx_store_upd; sx_dec; rewrite Hold; reflexivity).
  rewrite Hfa in H. cbn [wordSem.theWord] in H.
  destruct (dec_stack _ _ _) as [stack1|] eqn:Ed; [|injection H as <- _; exfalso; apply Hr; reflexivity].
  pose proof (enc_dec_stack _ _ _ _ (conj Ee Ed)) as <-.
  rewrite TAKE_firstn, DROP_skipn, firstn_skipn in H. cbn beta iota in H.
  stk_fields. cbn [FUPDATE_LIST FOLDL] in H. rewrite !sx_store_upd in H. sx_dec.
  unfold has_space in H. rewrite !sx_store_upd in H. sx_dec.
  rewrite WORD_SUB_REFL, w2n_n2w, N.mod_0_l in H by (pose proof (ZERO_LT_dimword a); lia).
  unfold word_gc_code. rewrite Hk. cbn [list_Seq].
  destruct (N.leb_spec (w2n w) 0) as [Hw|Hw]; injection H as <- <-.
  - assert (Hw0 : w = n2w 0) by (apply w2n_eq_0; lia). subst w.
    exists 0, (l |+ (2, Word old)). rewrite N.add_0_r.
    sx_all. split; [f_equal; apply state_ext; nf_fields; reflexivity|].
    split; [intros E; contradiction|]. split; [intros k0 v0 Hk0; discriminate Hk0|]. intros _; reflexivity.
  - exists 0, FEMPTY. rewrite N.add_0_r. sx_all.
    rewrite (proj2 (proj2 (proj2 (proj2 (WORD_AND_CLAUSES w))))).
    assert (Hw0 : w <> n2w 0) by (intros ->; rewrite w2n_n2w, N.mod_0_l in Hw by (pose proof (ZERO_LT_dimword a); lia); lia).
    rewrite (proj1 (Bool.not_true_iff_false (bool_decide (w = n2w 0)))
               ltac:(intros E; apply bool_decide_spec in E; exact (Hw0 E))).
    try rewrite ev_halt. sx_simp.
    split; [f_equal; apply state_ext; unfold empty_env; nf_fields; reflexivity|].
    split; [reflexivity|]. split; [intros k0 v0 Hk0; discriminate Hk0|]. intros E; discriminate E.
Qed.

End AllocNone.

(** ** Correctness, assuming the GC stub is correct (Galette-only)

    [comp_correct_gen] is HOL's [comp_correct] for the Galette-only state
    translation [tr], given [alloc_ok] (the statement of HOL's local
    [alloc_correct]); [compile_semantics_gen] is [compile_semantics] under
    the same assumption. *)

Section CC.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.
Variables (compile_rest : cfg_t -> list (N * prog a) -> option (list word8 * cfg_t))
  (anything : wordSem.gc_fun_type a) (c : config).

Local Abbreviation TR := (tr compile_rest anything c).

Definition tr_alloc (l : fmap N (word_loc a)) (s : state) : state :=
  set_code (fromAList (compile c (toAList (code s))))
    (set_gc_fun anything (set_regs l (set_use_alloc false (set_use_stack true (set_use_store true s))))).

Definition alloc_ok : Prop :=
  forall (w : word a) (s : state) r t (l : fmap N (word_loc a)) n' m,
  alloc w s = (r, t) /\ r <> SOME Error /\ gc_fun s = word_gc_fun c /\
  LENGTH (bitmaps s) < dimword a - 1 /\ LENGTH (stack s) * (dimindex a DIV 8) < dimword a /\
  FLOOKUP l 1 = SOME (Word w) ->
  exists ck l2,
    evaluate (Call (SOME (Skip, (0, (n', m)))) (inl gc_stub_location) NONE,
              set_clock (clock s + ck) (tr_alloc l s)) = (r, tr_alloc l2 t) /\ regs t ⊑ l2.

Definition LST (s : state) : Prop := LENGTH (stack s) * (dimindex a DIV 8) < dimword a.
Definition LBD (s : state) : Prop :=
  LENGTH (bitmaps s) + LENGTH (wordSem.buffer_buffer (data_buffer s)) + wordSem.space_left (data_buffer s) <
  dimword a - 1.
Definition CI (s : state) : Prop :=
  (forall k prog0, lookup k (code s) = SOME prog0 -> k <> gc_stub_location /\ alloc_arg prog0) /\
  (forall n k p, MEM (k, p) (FST (SND (compile_oracle s n))) -> k <> gc_stub_location /\ alloc_arg p) /\
  gc_fun s = word_gc_fun c /\ use_alloc s /\ LST s /\ use_stack s /\ LBD s /\
  stackSem.compile s = (fun c0 => compile_rest c0 ∘ MAP prog_comp).

Hypothesis HA : alloc_ok.

Definition CIc (s : state) : Prop :=
  (forall k prog0, lookup k (code s) = SOME prog0 -> k <> gc_stub_location /\ alloc_arg prog0) /\
  (forall n k p, MEM (k, p) (FST (SND (compile_oracle s n))) -> k <> gc_stub_location /\ alloc_arg p).

Lemma lookup_FOLDL_union_IMP : forall (l : list (sptree.spt (prog a))) acc k v,
  lookup k (FOLDL sptree.union acc l) = SOME v -> lookup k acc = SOME v \/ exists t, In t l /\ lookup k t = SOME v.
Proof.
  induction l as [|x l IH]; intros acc k v H; cbn [FOLDL] in H; [left; exact H|].
  destruct (IH _ _ _ H) as [H1|(t & Ht & H2)].
  - rewrite sptree.lookup_union in H1. destruct (lookup k acc) eqn:E; [left; exact H1|].
    right; exists x; split; [left; reflexivity|exact H1].
  - right; exists t; split; [right; exact Ht|exact H2].
Qed.

Lemma CIc_evaluate (p : prog a) (s s1 : state) r :
  evaluate (p, s) = (r, s1) -> CIc s -> CIc s1.
Proof.
  intros H [H1 H2]. destruct (evaluate_code_bitmaps p s r s1 H) as (k & Eo & Ec & _).
  split.
  - intros k0 p0 Hl; rewrite Ec in Hl. apply lookup_FOLDL_union_IMP in Hl as [Hl|(t & Ht & Hl)];
      [exact (H1 _ _ Hl)|].
    apply in_map_iff in Ht as (x & <- & Hx).
    apply In_GENLIST_iff in Hx as (i & Hi & ->). cbn in Hl.
    rewrite sptree.lookup_fromAList in Hl. apply ALOOKUP_In in Hl.
    apply (H2 i); unfold is_true; rewrite MEM_In; exact Hl.
  - intros n0 k0 p0 Hm; rewrite Eo in Hm; unfold shift_seq in Hm. exact (H2 _ _ _ Hm).
Qed.


Lemma set_clock_same (s : state) : set_clock (clock s) s = s.
Proof. destruct s; reflexivity. Qed.

Ltac rw_reads Hs :=
  repeat match goal with
         | E : get_var ?v ?s = SOME ?x |- context [get_var ?v (TR ?R ?s)] =>
             rewrite (get_var_tr compile_rest anything c R s v x E Hs)
         | E : get_var_imm ?v ?s = SOME ?x |- context [get_var_imm ?v (TR ?R ?s)] =>
             rewrite (get_var_imm_tr compile_rest anything c R s v x E Hs)
         | E : word_exp ?s ?e = SOME ?x |- context [word_exp (TR ?R ?s) ?e] =>
             rewrite (word_exp_tr compile_rest anything c R s e x E Hs)
         | E : FLOOKUP (regs ?s) ?v = SOME ?x |- context [FLOOKUP ?R ?v] =>
             rewrite (FLOOKUP_SUBMAP _ _ _ _ (conj Hs E))
         end.

Ltac fin_sub Hs :=
  cbn [regs set_var set_regs set_store set_store_fld set_fp_var set_memory set_stack set_stack_space
       set_ffi set_fp_regs set_code_buffer set_data_buffer set_bitmaps set_clock dec_clock empty_env
       unset_var];
  repeat (first [exact Hs | apply SUBMAP_FUPDATE_both | apply SUBMAP_REFL | apply SUBMAP_DOMSUB_both
                 | apply SUBMAP_DRESTRICT_MONOTONE; split; [|intros ? ?; assumption]]).

Lemma LENGTH_LUPDATE' {B} (v : B) : forall l n, LENGTH (LUPDATE v n l) = LENGTH l.
Proof.
  induction l as [|x l IH]; intros n; [reflexivity|]. cbn [LUPDATE].
  destruct (n =? 0); rewrite !LENGTH_length in *; cbn [length]; [reflexivity|].
  specialize (IH (PRE n)); rewrite LENGTH_length in IH; lia.
Qed.

Lemma buffer_write_LBD {b} (db : wordSem.buffer a b) w x db' :
  wordSem.buffer_write db w x = SOME db' ->
  LENGTH (wordSem.buffer_buffer db') + wordSem.space_left db' =
  LENGTH (wordSem.buffer_buffer db) + wordSem.space_left db.
Proof.
  unfold wordSem.buffer_write; destruct (_ && _) eqn:E; [|discriminate]. intros H; injection H as <-.
  apply andb_prop in E as [_ E]. apply N.ltb_lt in E. cbn [wordSem.buffer_buffer wordSem.space_left].
  rewrite !LENGTH_length, length_app, Nat2N.inj_add. cbn [length]. lia.
Qed.

Ltac fin_len :=
  repeat match goal with E : wordSem.buffer_write _ _ _ = SOME _ |- _ =>
    apply buffer_write_LBD in E end;
  split; [unfold LBD in *; stk_fields; first [assumption | lia]|];
  intros Hh; first [exfalso; eapply Hh; reflexivity
                   | unfold LST in *; stk_fields;
                     first [ assumption | rewrite LENGTH_LUPDATE'; assumption
                           | cbn; pose proof (ZERO_LT_dimword a); lia]].

Lemma tr_set_regs R X (s : state) : TR R (set_regs X s) = TR R s.
Proof. reflexivity. Qed.
Hint Rewrite tr_set_regs : tre.

Lemma sh_mem_op_tr op r ad (s t : state) res R :
  sh_mem_op op r ad s = (res, t) -> res <> SOME Error -> regs s ⊑ R ->
  exists R', sh_mem_op op r ad (TR R s) = (res, TR R' t) /\ regs t ⊑ R' /\
    stack t = stack s /\ data_buffer t = data_buffer s /\ bitmaps t = bitmaps s.
Proof.
  intros H Hr Hs; destruct op; cbn [sh_mem_op] in *;
    unfold sh_mem_load, sh_mem_store, sh_mem_load_byte, sh_mem_store_byte, sh_mem_load16,
      sh_mem_store16, sh_mem_load32, sh_mem_store32 in *;
    stk_split H; try (injection H as <- _; exfalso; apply Hr; reflexivity); injection H as <- <-;
    rw_reads Hs; autorewrite with tre; cbn beta iota zeta;
    repeat match goal with E : ?X = ?v |- context [?X] =>
      lazymatch v with SOME _ => idtac | NONE => idtac | left _ => idtac | right _ => idtac
        | FFI_return _ _ => idtac | FFI_final _ => idtac end; rewrite E; cbn beta iota zeta end;
    autorewrite with tre; (eexists; split; [reflexivity|]); (split; [fin_sub Hs|]);
    stk_fields; repeat split.
Qed.

Lemma CI_step (p : prog a) (s s1 : state) r :
  evaluate (p, s) = (r, s1) -> CI s -> LBD s1 -> LST s1 -> CI s1.
Proof.
  intros H (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hb Hl.
  destruct (CIc_evaluate p s s1 r H (conj H1 H2)) as [C1 C2].
  pose proof (evaluate_consts p s r s1 H) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  refine (conj C1 (conj C2 _)). unfold is_true in *; repeat split; try assumption; congruence.
Qed.

Lemma CI_set_clock (s : state) k : CI s -> CI (set_clock k s).
Proof. unfold CI, LBD, LST; stk_fields; intros H; exact H. Qed.

Lemma CI_dec_clock (s : state) : CI s -> CI (dec_clock s).
Proof. apply CI_set_clock. Qed.

Lemma alloc_co (w : word a) (s : state) X Y :
  alloc w (set_compile X (set_compile_oracle Y s)) =
  (I ## (fun t => set_compile X (set_compile_oracle Y t))) (alloc w s).
Proof.
  unfold alloc.
  assert (Hg : gc (set_store AllocSize (Word w) (set_compile X (set_compile_oracle Y s))) =
               OPTION_MAP (fun t => set_compile X (set_compile_oracle Y t)) (gc (set_store AllocSize (Word w) s)))
    by (unfold gc; stk_fields; stk_split_goal; reflexivity).
  rewrite Hg; destruct (gc (set_store AllocSize (Word w) s)) as [s1|]; cbn [OPTION_MAP option_map];
    [|reflexivity].
  stk_fields; stk_split_goal; reflexivity.
Qed.

Ltac submap_tac Hs :=
  unfold SUBMAP in *; intros ?k ?v ?Hk;
  repeat (rewrite ?FLOOKUP_UPDATE, ?DOMSUB_FLOOKUP_THM in *;
          first [ match goal with |- context [decide ?P] => destruct (decide P) end
                | match goal with H : context [decide ?P] |- _ => destruct (decide P) end ]);
  try congruence; try discriminate; apply Hs; assumption.

Lemma store_const_sem_tr t1 t2 (s t : state) r R :
  store_const_sem t1 t2 s = (r, t) -> r <> SOME Error -> regs s ⊑ R -> use_alloc s = true ->
  exists R', store_const_sem t1 t2 (TR R s) = (r, TR R' t) /\ regs t ⊑ R' /\
    stack t = stack s /\ bitmaps t = bitmaps s /\ data_buffer t = data_buffer s.
Proof.
  intros H Hr Hs Hua. unfold store_const_sem in *.
  stk_split H; try (injection H as <- _; exfalso; apply Hr; reflexivity); try discriminate Hua.
  injection H as <- <-. subst.
  repeat match goal with E : get_var ?v s = SOME ?x |- _ =>
    rewrite (get_var_tr compile_rest anything c R s v x E Hs); clear E end.
  autorewrite with tre.
  repeat match goal with E : ?X = ?v |- context [?X] =>
    lazymatch v with SOME _ => idtac | NONE => idtac | true => idtac | false => idtac end;
    rewrite E; cbn beta iota zeta end.
  autorewrite with tre.
  cbn [combin.I]. eexists. unfold unset_var. rewrite tr_set_regs.
  split; [reflexivity|]. split; [|stk_fields; repeat split].
  cbn [regs set_regs set_var set_memory]. submap_tac Hs.
Qed.

Lemma compile_union_code (cd : sptree.spt (prog a)) progs :
  sptree.union (fromAList (compile c (toAList cd))) (fromAList (MAP prog_comp progs)) =
  fromAList (compile c (toAList (sptree.union cd (fromAList progs)))).
Proof.
  apply sptree.spt_eq_thm; [split; [apply sptree.wf_union; split; apply sptree.wf_fromAList|apply sptree.wf_fromAList]|].
  intros k. rewrite sptree.lookup_union, !sptree.lookup_fromAList. unfold compile; rewrite !ALOOKUP_APPEND.
  destruct (ALOOKUP (stubs c) k); [reflexivity|].
  rewrite (prog_comp_lemma), !ALOOKUP_MAP_2, !sptree.ALOOKUP_toAList, sptree.lookup_union,
    sptree.lookup_fromAList.
  destruct (lookup k cd); reflexivity.
Qed.

Lemma buffer_flush_eq {b} (db : wordSem.buffer a b) w1 w2 d db' :
  wordSem.buffer_flush db w1 w2 = SOME (d, db') ->
  d = wordSem.buffer_buffer db /\ wordSem.buffer_buffer db' = [] /\ wordSem.space_left db' = wordSem.space_left db.
Proof.
  unfold wordSem.buffer_flush; destruct (_ && _); [|discriminate]. intros H; injection H as <- <-.
  repeat split; reflexivity.
Qed.

Lemma CI_set_var (s : state) v x : CI s -> CI (set_var v x s).
Proof. unfold CI, LBD, LST; stk_fields; intros H; exact H. Qed.

Lemma dec_set_var_clock_tr R (s : state) ck lr v : clock s <> 0 ->
  dec_clock (set_var lr v (set_clock (clock s + ck) (TR R s))) =
  set_clock (clock (dec_clock (set_var lr v s)) + ck) (TR (R |+ (lr, v)) (dec_clock (set_var lr v s))).
Proof. intros H; apply state_ext; unfold tr, frame; stk_fields; try reflexivity; lia. Qed.

Lemma dec_set_var_clock_tr' R (s : state) ck lr v : clock s <> 0 ->
  TR (R |+ (lr, v)) (dec_clock (set_var lr v (set_clock (clock s + ck) s))) =
  set_clock (clock (dec_clock (set_var lr v s)) + ck) (TR (R |+ (lr, v)) (dec_clock (set_var lr v s))).
Proof. intros H; apply state_ext; unfold tr, frame; stk_fields; try reflexivity; lia. Qed.

Lemma add_clock_tr (p : prog a) (X Y : state) r k :
  evaluate (p, X) = (r, Y) -> r <> SOME TimeOut ->
  evaluate (p, set_clock (clock X + k) X) = (r, set_clock (clock Y + k) Y).
Proof. intros H Hr; exact (evaluate_add_clock k p X r Y (conj H Hr)). Qed.

Lemma dec_set_clock_tr R (s : state) ck : clock s <> 0 ->
  dec_clock (set_clock (clock s + ck) (TR R s)) = set_clock (clock (dec_clock s) + ck) (TR R (dec_clock s)).
Proof. intros H; apply state_ext; unfold tr, frame; stk_fields; try reflexivity; lia. Qed.

Lemma dec_set_clock_tr' R (s : state) ck : clock s <> 0 ->
  TR R (dec_clock (set_clock (clock s + ck) s)) = set_clock (clock (dec_clock s) + ck) (TR R (dec_clock s)).
Proof. intros H; apply state_ext; unfold tr, frame; stk_fields; try reflexivity; lia. Qed.

Ltac rd_clk := rewrite ?get_var_set_clock, ?get_var_imm_with_const, ?regs_set_clock, ?code_set_clock,
  ?clock_set_clock, ?use_stack_set_clock, ?use_store_set_clock, ?use_alloc_set_clock.

Ltac simple_pre Hs Hr H :=
  exists 0; rewrite N.add_0_r, set_clock_tr, set_clock_same;
  cbn [comp fst FST]; rewrite evaluate_eqn; cbn [evaluate_body];
  autorewrite with tre; cbn [negb andb orb]; cbn beta iota;
  stk_split H; try (injection H as <- _; exfalso; apply Hr; reflexivity);
  try (injection H as <- <-);
  repeat match goal with
         | E : orb _ _ = false |- _ => apply Bool.orb_false_iff in E as [? ?]
         | E : andb _ _ = true |- _ => apply andb_prop in E as [? ?]
         | E : negb _ = false |- _ => apply Bool.negb_false_iff in E
         | E : negb _ = true |- _ => apply Bool.negb_true_iff in E
         end;
  rw_reads Hs; autorewrite with tre; cbn beta iota zeta;
  repeat match goal with E : ?X = ?v |- context [?X] =>
    lazymatch v with SOME _ => idtac | NONE => idtac | true => idtac | false => idtac
      | left _ => idtac | right _ => idtac | FFI_return _ _ => idtac | FFI_final _ => idtac end;
    rewrite E; cbn beta iota zeta end;
  autorewrite with tre.

Ltac simple_case Hs Hr H :=
  simple_pre Hs Hr H; (eexists; split; [reflexivity|]; split; [fin_sub Hs|]; fin_len).


Lemma comp_correct_gen : forall (x : prog a * state) r t,
  evaluate x = (r, t) -> r <> SOME Error -> alloc_arg (fst x) -> CI (snd x) ->
  forall m n regs0, regs (snd x) ⊑ regs0 ->
  exists ck regs1,
    evaluate (FST (comp n m (fst x)), set_clock (clock (snd x) + ck) (TR regs0 (snd x))) = (r, TR regs1 t) /\
    regs t ⊑ regs1 /\ LBD t /\ ((forall w, r <> SOME (Halt w)) -> LST t).
Proof.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r t H Hr Ha Hci m n regs0 Hs; cbn [fst snd] in *.
  pose proof Hci as (Hcode & Hor & Hgc & Hua & Hlst & Hust & Hlbd & Hcomp).
  rewrite evaluate_eqn in H; destruct p; cbn [evaluate_body] in H.
  all: try (simple_case Hs Hr H; fail).
  1: { (* Inst *)
    destruct (inst i s) as [s1|] eqn:Ei; [|injection H as <- _; exfalso; apply Hr; reflexivity].
    injection H as <- <-. unfold LBD, LST in *.
    assert (Hlbd' : LENGTH (wordSem.buffer_buffer (data_buffer s)) + (LENGTH (bitmaps s) +
               wordSem.space_left (data_buffer s)) < dimword a - 1) by (clear -Hlbd; lia).
    destruct (inst_correct i s s1 regs0 compile_rest anything c
                (conj Ei (conj Hlst (conj Hlbd' Hs)))) as (R' & E & HR & Hl1 & Hl2).
    exists 0, R'. rewrite N.add_0_r, set_clock_tr, set_clock_same.
    cbn [comp fst FST]; rewrite evaluate_eqn; cbn [evaluate_body].
    replace (inst i (TR regs0 s)) with (SOME (TR R' s1)) by (symmetry; exact E).
    split; [reflexivity|]. split; [exact HR|]. split; [lia|intros _; exact Hl1]. }
  Ltac sg := match goal with |- ?g => idtac "GOAL" g end.
  10: { (* ShMemOp *)
    destruct a0 as [ad w]; cbn beta iota in H.
    destruct (word_exp s _) as [w0|] eqn:Ew; [|injection H as <- _; exfalso; apply Hr; reflexivity].
    destruct (clock s =? 0) eqn:Ec; [simple_case Hs Hr H|].
    destruct (sh_mem_op_tr m0 n0 w0 (dec_clock s) t r regs0 H Hr Hs) as (R' & E & HR & Hst & Hdb & Hbm).
    exists 0, R'. rewrite N.add_0_r, set_clock_tr, set_clock_same.
    cbn [comp fst FST]; rewrite evaluate_eqn; cbn [evaluate_body].
    rewrite (word_exp_tr compile_rest anything c regs0 s _ w0 Ew Hs); cbn beta iota.
    autorewrite with tre; rewrite Ec; cbn beta iota. rewrite E.
    split; [reflexivity|]; split; [exact HR|].
    unfold LBD, LST in *; rewrite Hst, Hdb, Hbm; stk_fields; split; [assumption|intros _; assumption]. }
  8: { (* LocValue *)
    destruct (classical_dec _) as [Hl|Hl]; [|injection H as <- _; exfalso; apply Hr; reflexivity].
    injection H as <- <-.
    assert (Hl' : loc_check (fromAList (compile c (toAList (code s)))) (n1, n2))
      by (apply loc_check_compile; split; [exact Hl|intros k p Hk; exact (proj1 (Hcode _ _ Hk))]).
    exists 0, (regs0 |+ (n0, Loc n1 n2)). rewrite N.add_0_r, set_clock_tr, set_clock_same.
    cbn [comp fst FST]; rewrite evaluate_eqn; cbn [evaluate_body].
    autorewrite with tre. destruct (classical_dec _) as [_|Hn]; [|contradiction].
    autorewrite with tre. split; [reflexivity|]. split; [fin_sub Hs|]. fin_len. }
  2: { (* Seq *)
    cbn [alloc_arg] in Ha; apply andb_prop in Ha as [Ha1 Ha2].
    rewrite fix_clock_evaluate in H. destruct (evaluate (p1, s)) as [r1 s1] eqn:E1.
    pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
    cbn [comp]. destruct (comp n m p1) as [q1 m1] eqn:Eq1. destruct (comp n m1 p2) as [q2 m2] eqn:Eq2.
    cbn [fst FST].
    destruct r1 as [r1|].
    - injection H as <- <-.
      destruct (IH (p1, s) ltac:(stk_eval_lt) _ s1 E1 Hr Ha1 Hci m n regs0 Hs) as (ck & R1 & Ev & HR & Hb & Hl).
      cbn [fst snd] in Ev; rewrite Eq1 in Ev; cbn [fst] in Ev.
      exists ck, R1. rewrite evaluate_eqn; cbn [evaluate_body]. rewrite fix_clock_evaluate, Ev.
      split; [reflexivity|]. split; [exact HR|]. split; [exact Hb|exact Hl].
    - destruct (IH (p1, s) ltac:(stk_eval_lt) NONE s1 E1 ltac:(discriminate) Ha1 Hci m n regs0 Hs)
        as (ck1 & R1 & Ev1 & HR1 & Hb1 & Hl1).
      cbn [fst snd] in Ev1; rewrite Eq1 in Ev1; cbn [fst] in Ev1.
      assert (Hci1 : CI s1) by (apply (CI_step p1 s s1 NONE E1 Hci Hb1); apply Hl1; discriminate).
      destruct (IH (p2, s1) ltac:(stk_eval_lt) r t H Hr Ha2 Hci1 m1 n R1 HR1)
        as (ck2 & R2 & Ev2 & HR2 & Hb2 & Hl2).
      cbn [fst snd] in Ev2; rewrite Eq2 in Ev2; cbn [fst] in Ev2.
      exists (ck1 + ck2), R2. rewrite evaluate_eqn; cbn [evaluate_body]. rewrite fix_clock_evaluate.
      pose proof (add_clock_tr q1 _ _ NONE ck2 Ev1 ltac:(discriminate)) as Ev1'.
      autorewrite with stkc tre in Ev1'. rewrite N.add_assoc, set_clock_tr, Ev1'; cbn beta iota.
      rewrite set_clock_tr in Ev2. rewrite Ev2.
      split; [reflexivity|]. split; [exact HR2|]. split; [exact Hb2|exact Hl2]. }
  8: { (* RawCall *)
    destruct (lookup n0 (code s)) as [prog0|] eqn:El; [|injection H as <- _; exfalso; apply Hr; reflexivity].
    destruct (dest_Seq prog0) as [[p0 body]|] eqn:Ed; [|injection H as <- _; exfalso; apply Hr; reflexivity].
    destruct prog0; try discriminate Ed. injection Ed as -> ->.
    destruct (Hcode _ _ El) as [Hng Hap]. cbn [alloc_arg] in Hap; apply andb_prop in Hap as [_ Hab].
    destruct (lookup_IMP_lookup_compile n0 s (Seq p0 body) c (conj El Hng)) as (m1 & n1 & Elc).
    cbn [comp] in Elc. destruct (comp m1 n1 p0) as [q0 m2] eqn:Eq0.
    destruct (comp m1 m2 body) as [qb m3] eqn:Eqb. cbn [fst FST] in Elc.
    destruct (clock s =? 0) eqn:Ec.
    - injection H as <- <-. exists 0, FEMPTY. rewrite N.add_0_r, set_clock_tr, set_clock_same.
      cbn [comp fst FST]; rewrite evaluate_eqn; cbn [evaluate_body].
      autorewrite with tre; rewrite Elc; cbn [dest_Seq]; cbn beta iota; rewrite Ec; autorewrite with tre.
      split; [reflexivity|]; split; [fin_sub Hs|]; fin_len.
    - destruct (evaluate (body, dec_clock s)) as [r1 s1] eqn:E1.
      destruct (bad_fun_return r1) eqn:Eb; [injection H as <- _; exfalso; apply Hr; reflexivity|].
      injection H as <- <-.
      destruct (IH (body, dec_clock s) ltac:(stk_eval_lt) r1 s1 E1 Hr Hab Hci m2 m1 regs0 Hs)
        as (ck & R1 & Ev & HR & Hb & Hl).
      cbn [fst snd] in Ev; rewrite Eqb in Ev; cbn [fst] in Ev.
      exists ck, R1.
      cbn [comp fst FST]; rewrite evaluate_eqn; cbn [evaluate_body].
      rd_clk; autorewrite with tre; rewrite Elc; cbn [dest_Seq]; cbn beta iota.
      replace ((clock s + ck =? 0)) with false by (symmetry; apply N.eqb_neq; apply N.eqb_neq in Ec; lia).
      rewrite ?dec_set_clock_tr, ?dec_set_clock_tr' by (apply N.eqb_neq in Ec; exact Ec).
      rewrite Ev, Eb. split; [reflexivity|]. split; [exact HR|]. split; [exact Hb|exact Hl]. }
  4: { (* JumpLower *)
    stk_split H; try (injection H as <- _; exfalso; apply Hr; reflexivity); subst.
    3:{ injection H as <- <-. exists 0, regs0. rewrite N.add_0_r, set_clock_tr, set_clock_same.
        cbn [comp fst FST]; rewrite evaluate_eqn; cbn [evaluate_body].
        rw_reads Hs; cbn beta iota. rewrite E3; cbn beta iota.
        split; [reflexivity|]; split; [exact Hs|]; fin_len. }
    all: cbn [find_code] in E4; destruct (Hcode _ _ E4) as [Hng Hap];
      destruct (lookup_IMP_lookup_compile n2 s p c (conj E4 Hng)) as (mm1 & nn1 & Elc);
      destruct (comp mm1 nn1 p) as [q m2] eqn:Eq; cbn [fst FST] in Elc.
    - injection H as <- <-. exists 0, FEMPTY. rewrite N.add_0_r, set_clock_tr, set_clock_same.
      cbn [comp fst FST]; rewrite evaluate_eqn; cbn [evaluate_body].
      rw_reads Hs; cbn beta iota. rewrite E3. cbn [find_code]. autorewrite with tre. rewrite Elc; cbn beta iota.
      rewrite E5. autorewrite with tre.
      split; [reflexivity|]; split; [fin_sub Hs|]; fin_len.
    - injection H as <- <-.
      destruct (IH (p, dec_clock s) ltac:(stk_eval_lt) o s0 E6 Hr Hap Hci nn1 mm1 regs0 Hs)
        as (ck & R1 & Ev & HR & Hb & Hl).
      cbn [fst snd] in Ev; rewrite Eq in Ev; cbn [fst] in Ev.
      exists ck, R1.
      cbn [comp fst FST]; rewrite evaluate_eqn; cbn [evaluate_body].
      rd_clk; rw_reads Hs; cbn beta iota. rewrite E3. cbn [find_code]. rd_clk; autorewrite with tre.
      rewrite Elc; cbn beta iota.
      replace ((clock s + ck =? 0)) with false by (symmetry; apply N.eqb_neq; apply N.eqb_neq in E5; lia).
      rewrite ?dec_set_clock_tr, ?dec_set_clock_tr' by (apply N.eqb_neq in E5; exact E5).
      rewrite Ev, E7. split; [reflexivity|]. split; [exact HR|]. split; [exact Hb|exact Hl]. }
  2: { (* If *)
    cbn [alloc_arg] in Ha; apply andb_prop in Ha as [Ha1 Ha2].
    cbn [comp]. destruct (comp n m p1) as [q1 m1] eqn:Eq1. destruct (comp n m1 p2) as [q2 m2] eqn:Eq2.
    cbn [fst FST].
    stk_split H; try (injection H as <- _; exfalso; apply Hr; reflexivity).
    - destruct (IH (p1, s) ltac:(stk_eval_lt) r t H Hr Ha1 Hci m n regs0 Hs) as (ck & R1 & Ev & HR & Hb & Hl).
      cbn [fst snd] in Ev; rewrite Eq1 in Ev; cbn [fst] in Ev.
      exists ck, R1. rewrite evaluate_eqn; cbn [evaluate_body]. rd_clk.
      rewrite (get_var_tr compile_rest anything c regs0 _ _ _ E Hs).
      rewrite (get_var_imm_tr compile_rest anything c regs0 _ _ _ E0 Hs). rewrite E1.
      split; [exact Ev|]. split; [exact HR|]. split; [exact Hb|exact Hl].
    - destruct (IH (p2, s) ltac:(stk_eval_lt) r t H Hr Ha2 Hci m1 n regs0 Hs) as (ck & R1 & Ev & HR & Hb & Hl).
      cbn [fst snd] in Ev; rewrite Eq2 in Ev; cbn [fst] in Ev.
      exists ck, R1. rewrite evaluate_eqn; cbn [evaluate_body]. rd_clk.
      rewrite (get_var_tr compile_rest anything c regs0 _ _ _ E Hs).
      rewrite (get_var_imm_tr compile_rest anything c regs0 _ _ _ E0 Hs). rewrite E1.
      split; [exact Ev|]. split; [exact HR|]. split; [exact Hb|exact Hl]. }
  2: { (* Loop *)
    cbn [alloc_arg] in Ha.
    rewrite fix_clock_evaluate in H. destruct (evaluate (p, s)) as [r1 s1] eqn:E1.
    pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
    cbn [comp]. destruct (comp n m p) as [q1 m1] eqn:Eq1. cbn [fst FST].
    destruct (cont_loop r1) eqn:Ecl.
    - assert (Hr1 : r1 <> SOME Error) by (destruct r1 as [[]|]; cbn in Ecl; congruence).
      destruct (IH (p, s) ltac:(stk_eval_lt) r1 s1 E1 Hr1 Ha Hci m n regs0 Hs) as (ck1 & R1 & Ev1 & HR1 & Hb1 & Hl1).
      cbn [fst snd] in Ev1; rewrite Eq1 in Ev1; cbn [fst] in Ev1.
      assert (Hnh : forall w, r1 <> SOME (Halt w)) by (intros w ->; discriminate Ecl).
      destruct (clock s1 =? 0) eqn:Ez.
      + injection H as <- <-. exists ck1, FEMPTY.
        rewrite evaluate_eqn; cbn [evaluate_body]. rewrite fix_clock_evaluate, Ev1; cbn beta iota.
        rewrite Ecl; autorewrite with tre; rewrite Ez. autorewrite with tre.
        split; [reflexivity|]. split; [fin_sub Hs|]. fin_len.
      + assert (Hci1 : CI s1) by (apply (CI_step p s s1 r1 E1 Hci Hb1 (Hl1 Hnh))).
        destruct (IH (STOP (Loop p), dec_clock s1) ltac:(stk_eval_lt) r t H Hr Ha
                    (CI_dec_clock s1 Hci1)
                    m n R1 HR1) as (ck2 & R2 & Ev2 & HR2 & Hb2 & Hl2).
        cbn [fst snd] in Ev2. unfold stackSem.STOP in Ev2 |- *. cbn [comp] in Ev2. rewrite Eq1 in Ev2. cbn [fst] in Ev2.
        exists (ck1 + ck2), R2. rewrite evaluate_eqn; cbn [evaluate_body]. rewrite fix_clock_evaluate.
        pose proof (add_clock_tr q1 _ _ r1 ck2 Ev1 ltac:(intros ->; discriminate Ecl)) as Ev1'.
        autorewrite with stkc tre in Ev1'. rewrite N.add_assoc, set_clock_tr, Ev1'; cbn beta iota.
        rewrite Ecl. autorewrite with tre. rewrite clock_set_clock.
        replace ((clock s1 + ck2 =? 0)) with false by (symmetry; apply N.eqb_neq; apply N.eqb_neq in Ez; lia).
        unfold stackSem.STOP. rewrite (dec_set_clock_tr' R1 s1 ck2) by (apply N.eqb_neq in Ez; exact Ez).
        rewrite Ev2. split; [reflexivity|]. split; [exact HR2|]. split; [exact Hb2|exact Hl2].
    - injection H as <- <-.
      assert (Hr1 : r1 <> SOME Error) by (intros ->; apply Hr; reflexivity).
      destruct (IH (p, s) ltac:(stk_eval_lt) r1 s1 E1 Hr1 Ha Hci m n regs0 Hs) as (ck1 & R1 & Ev1 & HR1 & Hb1 & Hl1).
      cbn [fst snd] in Ev1; rewrite Eq1 in Ev1; cbn [fst] in Ev1.
      exists ck1, R1. rewrite evaluate_eqn; cbn [evaluate_body]. rewrite fix_clock_evaluate, Ev1; cbn beta iota.
      rewrite Ecl. split; [reflexivity|]. split; [exact HR1|]. split; [exact Hb1|].
      intros Hh; apply Hl1; intros w ->; apply (Hh w); reflexivity. }
  2: { (* Alloc *)
    cbn [alloc_arg] in Ha. apply bool_decide_spec in Ha; subst n0.
    stk_split H; try (injection H as <- _; exfalso; apply Hr; reflexivity). subst.
    match goal with E : get_var 1 s = SOME (Word ?w) |- _ => rename E into Eg; rename w into w0 end.
    rename H into Ea.
    pose proof (alloc_co w0 s compile_rest ((I ## (MAP prog_comp ## I)) ∘ compile_oracle s)) as Eco.
    rewrite Ea in Eco; cbn [PAIR_MAP I fst snd] in Eco.
    assert (Hl1 : FLOOKUP regs0 1 = SOME (Word w0)) by exact (FLOOKUP_SUBMAP _ _ _ _ (conj Hs Eg)).
    unfold LBD, LST in Hlbd, Hlst.
    assert (Hbm0 : LENGTH (bitmaps s) < dimword a - 1) by lia.
    destruct (HA w0 _ r _ regs0 n m (conj Eco (conj Hr (conj Hgc (conj Hbm0 (conj Hlst Hl1))))))
      as (ck & l2 & Ev & Hl2).
    pose proof (alloc_const w0 s r t Ea) as (_ & _ & _ & _ & _ & Ecd & _ & _ & _ & _ & Ebm & _ & Edb & _ & Eor).
    exists ck, l2. cbn [comp fst FST].
    replace (TR l2 t) with (tr_alloc l2 (set_compile compile_rest
               (set_compile_oracle ((I ## (MAP prog_comp ## I)) ∘ compile_oracle s) t)))
      by (apply state_ext; unfold tr, frame, tr_alloc; stk_fields; try reflexivity; rewrite ?Ecd, ?Eor; reflexivity).
    split; [exact Ev|]. split; [exact Hl2|].
    unfold LBD, LST; rewrite Ebm, Edb. split; [lia|].
    intros Hh. rewrite (alloc_length_stack w0 s r t c (conj Ea (conj Hgc Hh))). exact Hlst. }
  2: { (* StoreConsts *)
    rename n0 into t1, n1 into t2.
    unfold is_true in Hua; rewrite Hua in H; cbn [negb andb] in H.
    destruct (use_store s) eqn:Eus; cbn [negb] in H; [|injection H as <- _; exfalso; apply Hr; reflexivity].
    destruct o as [loc|].
    - cbn [IS_SOME check_store_consts_opt] in H.
      destruct (bool_decide (lookup loc (code s) = SOME (Seq (StoreConsts t1 t2 NONE) (Return 0)))) eqn:Ech;
        cbn [negb] in H; [|injection H as <- _; exfalso; apply Hr; reflexivity].
      apply bool_decide_spec in Ech. destruct (Hcode _ _ Ech) as [Hng _].
      destruct (lookup_IMP_lookup_compile loc s _ c (conj Ech Hng)) as (m1 & n1 & Elc).
      cbn [comp fst FST] in Elc.
      unfold store_const_sem in H.
      stk_split H; try (injection H as <- _; exfalso; apply Hr; reflexivity); try discriminate Hua.
      injection H as <- <-. subst.
      exists 1, (regs0 |+ (0, Loc n m) |+ (2, Word w5) |+ (1, Word (n2w 1)) |+ (t2, Word (n2w 1))
                 |+ (t1, Word (n2w 1))).
      cbn [comp fst FST]; rewrite evaluate_eqn; cbn [evaluate_body].
      rd_clk; autorewrite with tre. cbn [find_code]. rewrite Elc; cbn beta iota.
      replace (clock s + 1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
      rewrite fix_clock_evaluate, evaluate_eqn; cbn [evaluate_body].
      rewrite fix_clock_evaluate, evaluate_eqn; cbn [evaluate_body].
      autorewrite with tre. cbn [negb andb IS_SOME check_store_consts_opt].
      unfold store_const_sem. rewrite E; cbn beta iota.
      apply Bool.negb_false_iff in E. apply ALL_DISTINCT_NoDup_list in E.
      assert (Hne : t1 <> 0 /\ t1 <> 1 /\ t1 <> 2 /\ t1 <> 3 /\ t2 <> 0 /\ t2 <> 1 /\ t2 <> 2 /\ t2 <> 3 /\ t1 <> t2).
      { inversion E as [|? ? N0 E1']; subst. inversion E1' as [|? ? N1 E2']; subst.
        inversion E2' as [|? ? N2 E3']; subst. inversion E3' as [|? ? N3 E4']; subst.
        inversion E4' as [|? ? N4 _]; subst. cbn in N0, N1, N2, N3, N4. intuition. }
      destruct Hne as (H10 & H11 & H12 & H13 & H20 & H21 & H22 & H23 & H12').
      unfold get_var; autorewrite with tre; cbn [regs set_regs set_var dec_clock set_clock].
      rewrite !FLOOKUP_UPDATE.
      repeat match goal with |- context [decide (?x = ?y)] =>
        let Hc := fresh in destruct (decide (x = y)) as [Hc|Hc];
          [try (exfalso; lia) | try (exfalso; apply Hc; reflexivity)] end.
      repeat match goal with E0 : get_var ?v s = SOME ?x |- _ =>
        unfold get_var in E0; rewrite (FLOOKUP_SUBMAP _ _ _ _ (conj Hs E0)); clear E0 end.
      cbn beta iota. cbn [bitmaps mdomain memory dec_clock set_var set_clock set_regs].
      rewrite E6. cbn beta iota zeta. cbn [combin.I]. autorewrite with tre.
      rewrite evaluate_eqn; cbn [evaluate_body]. unfold get_var; autorewrite with tre.
      unfold combin.I. autorewrite with tre. rewrite !FLOOKUP_UPDATE.
      repeat match goal with |- context [decide (?x = ?y)] =>
        let Hc := fresh in destruct (decide (x = y)) as [Hc|Hc];
          [try (exfalso; lia) | try (exfalso; apply Hc; reflexivity)] end.
      cbn beta iota.
      rewrite (proj2 (bool_decide_spec (Loc n m = Loc n m)) eq_refl); cbn [negb].
      rewrite evaluate_eqn; cbn [evaluate_body].
      split; [f_equal; apply state_ext; unfold tr, frame; stk_fields; try reflexivity; lia|].
      split; [unfold unset_var; cbn [regs set_regs set_var set_memory]; submap_tac Hs|].
      fin_len.
    - cbn [IS_SOME check_store_consts_opt negb] in H.
      destruct (store_const_sem_tr t1 t2 s t r regs0 H Hr Hs Hua) as (R' & E & HR & Hst & Hbm & Hdb).
      exists 0, R'. rewrite N.add_0_r, set_clock_tr, set_clock_same.
      cbn [comp fst FST]; rewrite evaluate_eqn; cbn [evaluate_body]. autorewrite with tre.
      cbn [negb andb IS_SOME check_store_consts_opt]. rewrite E.
      split; [reflexivity|]. split; [exact HR|]. unfold LBD, LST in *; rewrite Hst, Hbm, Hdb.
      split; [exact Hlbd|intros _; exact Hlst]. }
  2: { (* Install *)
    stk_split H; try (injection H as <- _; exfalso; apply Hr; reflexivity). subst.
    injection H as <- <-.
    unfold is_true in Hust; rewrite Hust in E11.
    apply andb_prop in E17 as [E17 E17c]; apply andb_prop in E17 as [E17a E17b].
    apply bool_decide_spec in E17a, E17b, E17c. subst l3 l2.
    exists 0, (DRESTRICT regs0 (ffi_save_regs s) |+ (n0, Loc n5 0)).
    rewrite N.add_0_r, set_clock_tr, set_clock_same.
    cbn [comp fst FST]; rewrite evaluate_eqn; cbn [evaluate_body].
    rw_reads Hs; cbn beta iota. autorewrite with tre.
    cbn beta; rewrite E7; cbn [PAIR_MAP combin.I MAP]. rewrite E9. rewrite E11.
    rewrite Hcomp in E13; cbn beta in E13; cbn [MAP] in E13. cbn [fst snd combin.I MAP]. rewrite E13.
    cbn [prog_comp]. unfold shift_seq in *; cbn beta in *; cbn [PAIR_MAP combin.I FST fst] in *.
    rewrite (proj2 (bool_decide_spec (l1 = l1)) eq_refl), (proj2 (bool_decide_spec (l0 = l0)) eq_refl).
    rewrite (proj2 (bool_decide_spec (fst (compile_oracle s (0 + 1)) = c1)) E17c). cbn [andb].
    split.
    { f_equal. apply state_ext; unfold tr, frame; stk_fields; try reflexivity.
      exact (compile_union_code (code s) ((n5, p4) :: l4)). }
    split; [fin_sub Hs|].
    destruct (buffer_flush_eq _ _ _ _ _ E11) as (Hd & Hb1 & Hb2).
    unfold LBD, LST in *; stk_fields. rewrite Hb1, Hb2, Hd. split; [|intros _; exact Hlst].
    rewrite !LENGTH_length, length_app, Nat2N.inj_add in *. cbn [length] in *. lia. }
  1: { (* Call *)
    rename o into ret, s0 into dest, o0 into h.
    destruct ret as [[ret_handler [lr [l1 l2]]]|].
    2:{ (* tail call *)
      destruct (find_code dest (regs s) (code s)) as [prog0|] eqn:Ef;
        [|injection H as <- _; exfalso; apply Hr; reflexivity].
      destruct (bool_decide (h = NONE)) eqn:Eh; cbn [negb] in H; [|injection H as <- _; exfalso; apply Hr; reflexivity].
      apply bool_decide_spec in Eh; subst h.
      destruct (find_code_IMP_lookup dest (regs s) (code s) prog0 Ef) as (k & Ek & Efk).
      destruct (Hcode _ _ Ek) as [Hng Hap].
      destruct (lookup_IMP_lookup_compile k s prog0 c (conj Ek Hng)) as (m1 & n1 & Elc).
      assert (Ef' : find_code dest regs0 (fromAList (compile c (toAList (code s)))) = SOME (FST (comp m1 n1 prog0))).
      { apply (find_code_regs_SUBMAP (regs s) regs0). split; [exact Hs|]. rewrite Efk; exact Elc. }
      destruct (comp m1 n1 prog0) as [q mq] eqn:Eq. cbn [fst FST] in Ef'.
      cbn [comp fst FST].
      destruct (clock s =? 0) eqn:Ec.
      - injection H as <- <-. exists 0, FEMPTY. rewrite N.add_0_r, set_clock_tr, set_clock_same.
        rewrite evaluate_eqn; cbn [evaluate_body]. autorewrite with tre. rewrite Ef'; cbn beta iota.
        rewrite (proj2 (bool_decide_spec (@NONE (prog a * (N * N)) = NONE)) eq_refl); cbn [negb].
        rewrite Ec. autorewrite with tre. split; [reflexivity|]. split; [fin_sub Hs|]. fin_len.
      - rewrite fix_clock_evaluate in H. destruct (evaluate (prog0, dec_clock s)) as [r1 s1] eqn:E1.
        destruct (bad_fun_return r1) eqn:Eb; [injection H as <- _; exfalso; apply Hr; reflexivity|].
        injection H as <- <-.
        destruct (IH (prog0, dec_clock s) ltac:(stk_eval_lt) r1 s1 E1 Hr Hap (CI_dec_clock s Hci) n1 m1 regs0 Hs)
          as (ck & R1 & Ev & HR & Hb & Hl).
        cbn [fst snd] in Ev; rewrite Eq in Ev; cbn [fst] in Ev.
        exists ck, R1. rewrite evaluate_eqn; cbn [evaluate_body]. rd_clk. autorewrite with tre.
        rewrite Ef'; cbn beta iota.
        rewrite (proj2 (bool_decide_spec (@NONE (prog a * (N * N)) = NONE)) eq_refl); cbn [negb].
        replace ((clock s + ck =? 0)) with false by (symmetry; apply N.eqb_neq; apply N.eqb_neq in Ec; lia).
        rewrite ?dec_set_clock_tr, ?dec_set_clock_tr' by (apply N.eqb_neq in Ec; exact Ec).
        rewrite fix_clock_evaluate, Ev, Eb.
        split; [reflexivity|]. split; [exact HR|]. split; [exact Hb|exact Hl]. }
    (* returning call *)
    cbn [alloc_arg] in Ha; apply andb_prop in Ha as [Har Hah].
    destruct (find_code dest (regs s \\ lr) (code s)) as [prog0|] eqn:Ef;
      [|injection H as <- _; exfalso; apply Hr; reflexivity].
    destruct (find_code_IMP_lookup dest (regs s \\ lr) (code s) prog0 Ef) as (k & Ek & Efk).
    destruct (Hcode _ _ Ek) as [Hng Hap].
    destruct (lookup_IMP_lookup_compile k s prog0 c (conj Ek Hng)) as (mc & nc & Elc).
    assert (Ef' : find_code dest (regs0 \\ lr) (fromAList (compile c (toAList (code s)))) =
                  SOME (FST (comp mc nc prog0))).
    { apply (find_code_regs_SUBMAP (regs s \\ lr) (regs0 \\ lr)). split; [apply SUBMAP_DOMSUB_both, Hs|].
      rewrite Efk; exact Elc. }
    destruct (comp mc nc prog0) as [q mq] eqn:Eq. cbn [fst FST] in Ef'.
    cbn [comp]. destruct (comp n m ret_handler) as [q1 m1] eqn:Eq1.
    assert (Hcomp_h : exists hq m2, (match h with
            | SOME (p2, (k1, k2)) => let '(q2, m0) := comp n m1 p2 in (Call (SOME (q1, (lr, (l1, l2)))) dest (SOME (q2, (k1, k2))), m0)
            | NONE => (Call (SOME (q1, (lr, (l1, l2)))) dest NONE, m1) end) = (Call (SOME (q1, (lr, (l1, l2)))) dest hq, m2) /\
            match h with NONE => hq = NONE | SOME (p2, (k1, k2)) => hq = SOME (FST (comp n m1 p2), (k1, k2)) end).
    { destruct h as [[p2 [k1 k2]]|]; [destruct (comp n m1 p2) as [q2 m2] eqn:Eq2; eexists _, _; split; reflexivity|].
      eexists _, _; split; reflexivity. }
    destruct Hcomp_h as (hq & m2 & Ecomp & Ehq). rewrite Ecomp; cbn [fst FST].
    destruct (clock s =? 0) eqn:Ec.
    { injection H as <- <-. exists 0, FEMPTY. rewrite N.add_0_r, set_clock_tr, set_clock_same.
      rewrite evaluate_eqn; cbn [evaluate_body]. autorewrite with tre. rewrite Ef'; cbn beta iota.
      rewrite Ec. autorewrite with tre. split; [reflexivity|]. split; [fin_sub Hs|]. fin_len. }
    rewrite fix_clock_evaluate in H.
    destruct (evaluate (prog0, dec_clock (set_var lr (Loc l1 l2) s))) as [r1 s2] eqn:E1.
    pose proof (evaluate_clock _ _ _ _ E1) as Hc1.
    assert (Hsv : regs (dec_clock (set_var lr (Loc l1 l2) s)) ⊑ regs0 |+ (lr, Loc l1 l2))
      by (cbn [regs dec_clock set_clock set_var set_regs]; apply SUBMAP_FUPDATE_both, Hs).
    pose proof (CI_dec_clock _ (CI_set_var s lr (Loc l1 l2) Hci)) as Hci0.
    destruct r1 as [r1|]; [|injection H as <- _; exfalso; apply Hr; reflexivity].
    assert (Hr1 : SOME r1 <> SOME Error)
      by (destruct r1; try discriminate; injection H as <- _; exfalso; apply Hr; reflexivity).
    destruct (IH (prog0, dec_clock (set_var lr (Loc l1 l2) s)) ltac:(stk_eval_lt) (SOME r1) s2 E1 Hr1 Hap Hci0
                 nc mc (regs0 |+ (lr, Loc l1 l2)) Hsv) as (ck1 & R1 & Ev1 & HR1 & Hb1 & Hl1).
    cbn [fst snd] in Ev1; rewrite Eq in Ev1; cbn [fst] in Ev1.
    Local Ltac call_pre Ef' Ec ck :=
      rewrite evaluate_eqn; cbn [evaluate_body]; rd_clk; autorewrite with tre; rewrite Ef'; cbn beta iota;
      replace ((clock _ + ck =? 0)) with false by (symmetry; apply N.eqb_neq; apply N.eqb_neq in Ec; lia);
      rewrite fix_clock_evaluate;
      rewrite ?dec_set_var_clock_tr, ?dec_set_var_clock_tr' by (apply N.eqb_neq in Ec; exact Ec).
    Local Ltac pass_through Ev1 Ef' Ec ck1 R1 HR1 Hb1 Hl1 :=
      exists ck1, R1; call_pre Ef' Ec ck1; rewrite Ev1; cbn beta iota;
      (split; [reflexivity|]); (split; [exact HR1|]); (split; [exact Hb1|exact Hl1]).
    Local Ltac compose_clk Ev1 ck2 :=
      let Ev1' := fresh "Ev1'" in
      pose proof (add_clock_tr _ _ _ _ ck2 Ev1 ltac:(discriminate)) as Ev1';
      rewrite ?clock_set_clock, ?set_clock_set_clock, ?clock_tr in Ev1';
      rewrite N.add_assoc, Ev1'; cbn beta iota.
    destruct r1 as [x|x|bn|bn|w| |f| ]; try (exfalso; apply Hr1; reflexivity);
      try (cbn beta iota in H; injection H as <- _; exfalso; apply Hr; reflexivity).
    - (* Result *)
      cbn beta iota in H.
      destruct (negb (bool_decide (x = Loc l1 l2))) eqn:Ex; [injection H as <- _; exfalso; apply Hr; reflexivity|].
      assert (Hci2 : CI s2) by (apply (CI_step _ _ s2 _ E1 Hci0 Hb1), Hl1; intros w0; discriminate).
      destruct (IH (ret_handler, s2) ltac:(stk_eval_lt) r t H Hr Har Hci2 m n R1 HR1)
        as (ck2 & R2 & Ev2 & HR2 & Hb2 & Hl2).
      cbn [fst snd] in Ev2; rewrite Eq1 in Ev2; cbn [fst] in Ev2.
      exists (ck1 + ck2), R2. call_pre Ef' Ec (ck1 + ck2). compose_clk Ev1 ck2.
      rewrite Ex; rewrite Ev2.
      split; [reflexivity|]. split; [exact HR2|]. split; [exact Hb2|exact Hl2].
    - (* Exception *)
      cbn beta iota in H. destruct h as [[hp [k1 k2]]|]; subst hq.
      + destruct (negb (bool_decide (x = Loc k1 k2))) eqn:Ex; [injection H as <- _; exfalso; apply Hr; reflexivity|].
        assert (Hci2 : CI s2) by (apply (CI_step _ _ s2 _ E1 Hci0 Hb1), Hl1; intros w0; discriminate).
        destruct (IH (hp, s2) ltac:(stk_eval_lt) r t H Hr Hah Hci2 m1 n R1 HR1)
          as (ck2 & R2 & Ev2 & HR2 & Hb2 & Hl2).
        cbn [fst snd] in Ev2.
        exists (ck1 + ck2), R2. call_pre Ef' Ec (ck1 + ck2). compose_clk Ev1 ck2.
        rewrite Ex; rewrite Ev2.
        split; [reflexivity|]. split; [exact HR2|]. split; [exact Hb2|exact Hl2].
      + injection H as <- <-. pass_through Ev1 Ef' Ec ck1 R1 HR1 Hb1 Hl1.
    - injection H as <- <-. pass_through Ev1 Ef' Ec ck1 R1 HR1 Hb1 Hl1.
    - injection H as <- <-. pass_through Ev1 Ef' Ec ck1 R1 HR1 Hb1 Hl1.
    - injection H as <- <-. pass_through Ev1 Ef' Ec ck1 R1 HR1 Hb1 Hl1. }
Qed.

Lemma compile_semantics_gen (s : state) start :
  CI s -> semantics start s <> Fail ->
  semantics start (TR (regs s) s) = semantics start s.
Proof.
  intros Hci HF. apply semantics_sim; [exact HF|].
  intros k r s1 E Hr.
  destruct (comp_correct_gen (Call NONE (inl start) NONE, set_clock k s) r s1 E Hr eq_refl
              (CI_set_clock s k Hci) 0 start (regs s) (SUBMAP_REFL _)) as (ck & R1 & Ev & _ & _ & _).
  cbn [fst snd comp FST] in Ev. exists ck, (TR R1 s1). split; [|reflexivity].
  rewrite <- Ev. f_equal; try (apply state_ext; unfold tr, frame; stk_fields; reflexivity).
Qed.

End CC.

(** ** The simple copying collector: code correctness *)

Ltac regs_fin :=
  apply fmap_ext; let k := fresh "k" in intros k; cbn [FUPDATE_LIST FOLDL]; rewrite ?FLOOKUP_UPD;
  repeat match goal with
    | |- context [(?x =? ?y)%N] => is_var x; destruct (N.eqb_spec x y) as [->|?]
    | |- context [(?x =? ?y)%N] => is_var y; destruct (N.eqb_spec x y) as [<-|?]
    | |- context [(?x =? ?y)%N] => let e := eval vm_compute in (x =? y)%N in change (x =? y)%N with e; cbn iota
    end;
  try reflexivity; try (symmetry; assumption); try assumption; try congruence.

Ltac st_fin := f_equal; apply state_ext; nf_fields; try reflexivity; try lia; try regs_fin.

Ltac fdom_val H r v Ev :=
  let E := fresh "E" in
  assert (E : FLOOKUP _ r <> None) by exact H;
  destruct (FLOOKUP _ r) as [v|] eqn:Ev; [clear E|contradiction].

Ltac splits := repeat match goal with |- _ /\ _ => split end.

Ltac rw_eval E :=
  lazymatch type of E with evaluate (?p, ?Y) = _ =>
    lazymatch goal with |- context [evaluate (p, ?X)] =>
      replace X with Y by (apply state_ext; nf_fields; try reflexivity; try lia; regs_fin); rewrite E end end.

Section Simple.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.

Lemma word_sh_lsr k (w : word a) : (k < dimindex a)%N -> wordLang.word_sh ast.Lsr w (w2n (n2w k : word a)) = Some (w >>> k)%w.
Proof.
  intros H. rewrite w2n_n2w_small by (rewrite dimword_pow; pose proof (N.pow_gt_lin_r 2 (dimindex a)); lia).
  unfold wordLang.word_sh. destruct (N.leb_spec (dimindex a) k); [lia|]. rewrite Bool.andb_false_r. reflexivity.
Qed.

Lemma word_sh_lsl k (w : word a) : (k < dimindex a)%N -> wordLang.word_sh ast.Lsl w (w2n (n2w k : word a)) = Some (w << k)%w.
Proof.
  intros H. rewrite w2n_n2w_small by (rewrite dimword_pow; pose proof (N.pow_gt_lin_r 2 (dimindex a)); lia).
  unfold wordLang.word_sh. destruct (N.leb_spec (dimindex a) k); [lia|]. rewrite Bool.andb_false_r. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_code_thm" *)
Theorem word_gc_move_code_thm : forall conf (w : word_loc a) (i pa old : word a) m dm w1 i1 pa1 m1 (s : state),
  word_gc_move conf (w, (i, (pa, (old, (m, dm))))) = (w1, (i1, (pa1, (m1, true)))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\ get_var 5 s = SOME w /\
  6 IN FDOM (regs s) ->
  exists ck r0 r1 r2 r6,
    evaluate (word_gc_move_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, w1); (6, r6)])
             (set_memory m1 s)).
Proof.
  intros conf w i pa old m dm w1 i1 pa1 m1 s
    (H & Hsl & Hws & H2 & Hls & Hsh & Hold & Hus & Hm & Hdm & H0 & H1 & H2r & H3 & H4 & H5 & H6).
  unfold get_var in *. subst m dm.
  fdom_val H0 0 v0 Ev0. fdom_val H1 1 v1 Ev1. fdom_val H2r 2 v2 Ev2. fdom_val H6 6 v6 Ev6.
  destruct w as [v|l1 l2].
  2:{ cbn in H. injection H as <- <- <- <- Hl2. apply N.eqb_eq in Hl2; subst l2.
      exists 0, v0, v1, v2, v6. rewrite N.add_0_r. unfold word_gc_move_code. sx_all.
      rewrite set_clock_same. st_fin. }
  cbn [word_gc_move] in H.
  destruct (decide ((v && n2w 1)%w = n2w 0)) as [Hev|Hodd].
  { injection H as <- <- <- <-. exists 0, v0, v1, v2, v6. rewrite N.add_0_r. unfold word_gc_move_code. sx_all.
    rewrite (proj2 (bool_decide_spec _) Hev). sx_all. rewrite set_clock_same. st_fin. }
  assert (Hoddb : bool_decide ((v && n2w 1)%w = n2w 0) = false)
    by (apply Bool.not_true_iff_false; intros E; apply bool_decide_spec in E; exact (Hodd E)).
  cbv zeta in H.
  assert (Ea : (v >>> shift_length conf << word_shift a + old)%w = ptr_to_addr conf old v)
    by (unfold ptr_to_addr; rewrite Hsh; apply WORD_ADD_COMM).
  destruct (wordSem.is_fwd_ptr (memory s (ptr_to_addr conf old v))) eqn:Ef.
  - injection H as <- <- <- <- Hc. apply bool_decide_spec in Hc.
    destruct (memory s (ptr_to_addr conf old v)) as [fv|] eqn:Em; [|discriminate].
    exists 0, (Word (ptr_to_addr conf old v)), (Word (fv >>> 2 << shift_length conf)), v2, v6. rewrite N.add_0_r. unfold word_gc_move_code. sx_all.
    rewrite Hoddb. cbn [list_Seq]. unfold is_true in Hus. sx_all. rewrite Hus. cbn [negb]. sx_all. rewrite word_sh_lsr by lia. sx_all. rewrite word_sh_lsl by lia. sx_all.
    rewrite Ea. destruct (classical_dec _) as [_|Hn]; [|contradiction]. cbn iota.
    cbn in Ef. rewrite Em. sx_all. rewrite Ef. rewrite word_sh_lsr by lia. sx_all. rewrite word_sh_lsl by lia. sx_all.
    unfold clear_top_inst. sx_all. rewrite word_sh_lsl by lia. sx_all. rewrite word_sh_lsr by lia. sx_all.
    sx_all. rewrite <- select_lower_lemma, (proj1 (proj2 (proj2 (proj2 (WORD_OR_CLAUSES _))))).
    rewrite WORD_OR_COMM. cbn [wordSem.theWord]. fold (update_addr conf (fv >>> 2) v).
    rewrite set_clock_same. st_fin.
  - destruct (memory s (ptr_to_addr conf old v)) as [hv|] eqn:Em.
    2:{ cbn [wordSem.isWord] in H. rewrite !Bool.andb_false_r in H. destruct (memcpy _ _ _ _ _) as (?, (?, ?)).
        injection H as _ _ _ _ Hc; discriminate. }
    cbn [wordSem.isWord wordSem.theWord] in H. cbn in Ef.
    destruct (memcpy (decode_length conf hv + n2w 1) (ptr_to_addr conf old v) pa (memory s) (mdomain s))
      as (pa1', (m1', c1)) eqn:Emc.
    injection H as <- <- <- <- Hc.
    rewrite !Bool.andb_true_r, !Bool.andb_true_iff in Hc. destruct Hc as (Hin & _ & Hc1). subst c1.
    destruct Hin as [Hin _]. apply bool_decide_spec in Hin.
    exists (w2n (decode_length conf hv + n2w 1)), (Word (i << 2)), (Word (i << shift_length conf)),
      (Word (ptr_to_addr conf old v)), (Word (decode_length conf hv + n2w 1)). unfold word_gc_move_code. sx_all.
    rewrite Hoddb. cbn [list_Seq]. unfold is_true in Hus. sx_all. rewrite Hus. cbn [negb]. sx_all.
    rewrite word_sh_lsr by lia. sx_all. rewrite word_sh_lsl by lia. sx_all.
    rewrite Ea. sx_simp. rewrite Em. sx_all. rewrite Ef. rewrite word_sh_lsr by lia. sx_all.
    change (hv >>> (dimindex a - len_size conf))%w with (decode_length conf hv).
    match goal with |- context [evaluate (memcpy_code, set_regs ?R (set_clock _ s))] =>
      destruct (memcpy_code_thm (decode_length conf hv + n2w 1) (ptr_to_addr conf old v) pa (memory s) (mdomain s)
                  pa1' m1' (set_regs R (set_clock (clock s) s))) as [r1' Emc'] end.
    { nf_fields. unfold get_var. rewrite ?FLOOKUP_UPD. cbn [N.eqb Pos.eqb].
      repeat split; try assumption; try reflexivity.
      unfold pred_set.IN, FDOM. rewrite ?FLOOKUP_UPD. cbn [N.eqb Pos.eqb]. discriminate. }
    autorewrite with nf in Emc'. cbn [clock regs memory set_regs set_clock set_memory] in Emc'. autorewrite with nf in Emc'. cbn [FUPDATE_LIST FOLDL] in Emc'. rewrite Emc'. sx_all.
    rewrite word_sh_lsl by lia. sx_all. rewrite word_sh_lsl by lia. sx_all.
    rewrite Hsh. replace (ptr_to_addr conf old v + (decode_length conf hv + n2w 1) * bytes_in_word -
      (decode_length conf hv + n2w 1) * bytes_in_word)%w with (ptr_to_addr conf old v) by word_ring.
    sx_all. destruct (classical_dec _) as [_|Hn]; [|contradiction]. cbn iota. sx_all.
    unfold clear_top_inst. sx_all. rewrite word_sh_lsl by lia. sx_all. rewrite word_sh_lsr by lia. sx_all.
    rewrite word_sh_lsl by lia. sx_all.
    rewrite <- select_lower_lemma, (proj1 (proj2 (proj2 (proj2 (WORD_OR_CLAUSES _))))).
    rewrite WORD_OR_COMM. fold (update_addr conf i v).
    replace (i + (decode_length conf hv + n2w 1))%w with (i + decode_length conf hv + n2w 1)%w by word_ring.
    st_fin.
Qed.


Lemma n2w_succ_sub1 n : (n2w (N.succ n) - n2w 1 : word a)%w = n2w n.
Proof. rewrite <- N.add_1_r, <- word_add_n2w; word_ring. Qed.

Lemma n2w_succ_ne0 n : (N.succ n < dimword a)%N -> (n2w (N.succ n) : word a) <> n2w 0.
Proof. intros H E; apply n2w_11 in E. rewrite !N.mod_small in E by (pose proof (ZERO_LT_dimword a); lia). lia. Qed.

Local Theorem word_gc_move_list_code_thm_n : forall n conf (a0 : word a) (s : state) pa1 pa old m1 m i1 i dm a1,
  word_gc_move_list conf (a0, (n2w n, (i, (pa, (old, (m, dm)))))) = (a1, (i1, (pa1, (m1, true)))) /\
  (n < dimword a)%N /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\
  get_var 7 s = SOME (Word (n2w n)) /\ get_var 8 s = SOME (Word a0) ->
  exists ck r0 r1 r2 r5 r6,
    evaluate (word_gc_move_list_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, Word (n2w 0)); (8, Word a1)])
             (set_memory m1 s)).
Proof.
  induction n as [|n IH] using N.peano_ind;
    intros conf a0 s pa1 pa old m1 m i1 i dm a1
      (H & Hn & Hsl & Hws & H2 & Hls & Hsh & Hold & Hus & Hm & Hdm & H0 & H1 & H2r & H3 & H4 & H5 & H6 & H7 & H8);
    unfold get_var in *; subst m dm;
    fdom_val H0 0 v0 Ev0; fdom_val H1 1 v1 Ev1; fdom_val H2r 2 v2 Ev2; fdom_val H5 5 v5 Ev5; fdom_val H6 6 v6 Ev6.
  - rewrite word_gc_move_list_def in H. destruct (decide _) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
    injection H as <- <- <- <-. exists 0, v0, v1, v2, v5, v6. rewrite N.add_0_r.
    unfold word_gc_move_list_code. rewrite ev_while. sx_simp. rewrite set_clock_same. st_fin.
  - pose proof (n2w_succ_ne0 n Hn) as Hne.
    rewrite word_gc_move_list_def in H. destruct (decide _) as [E|_]; [contradiction|].
    rewrite n2w_succ_sub1 in H. cbv zeta in H.
    destruct (word_gc_move conf (memory s a0, (i, (pa, (old, (memory s, mdomain s))))))
      as (w1, (i1', (pa1', (m1', c1)))) eqn:Emv.
    destruct (word_gc_move_list conf ((a0 + bytes_in_word)%w, (n2w n, (i1', (pa1', (old, ((a0 =+ w1) m1', mdomain s)))))))
      as (a2, (i2, (pa2, (m2, c2)))) eqn:Erec.
    injection H as <- <- <- <- Hc. apply andb_prop in Hc as [Ha Hc]; apply andb_prop in Hc as [-> ->].
    apply bool_decide_spec in Ha.
    set (s1 := set_regs (regs s |+ (5, memory s a0) |+ (7, Word (n2w n))) s).
    destruct (word_gc_move_code_thm conf (memory s a0) i pa old (memory s) (mdomain s) w1 i1' pa1' m1' s1)
      as (ck1 & q0 & q1 & q2 & q6 & Ev).
    { subst s1; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
      splits; try assumption; reflexivity. }
    set (s2 := set_regs ((regs s1 |++ [(0, q0); (1, q1); (2, q2); (3, Word pa1'); (4, Word i1'); (5, w1); (6, q6)])
                         |+ (8, Word (a0 + bytes_in_word)%w)) (set_memory ((a0 =+ w1) m1') s)).
    destruct (IH conf (a0 + bytes_in_word)%w s2 pa2 pa1' old m2 ((a0 =+ w1) m1') i2 i1' (mdomain s) a2)
      as (ck2 & p0 & p1 & p2 & p5 & p6 & Er).
    { subst s2 s1; unfold get_var; nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
      splits; try assumption; try reflexivity; try lia;
        unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
    
    pose proof (evaluate_add_clock (ck2 + 1) (word_gc_move_code conf) (set_clock (clock s1 + ck1) s1)) as Ev'.
    assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
    specialize (Ev' NONE _ (conj Ev NT)). subst s1. autorewrite with nf in Ev'.
    cbn [clock regs memory set_regs set_clock set_memory] in Ev'. autorewrite with nf in Ev'. cbn [FUPDATE_LIST FOLDL] in Ev'.
    exists (ck1 + ck2 + 1), p0, p1, p2, p5, p6.
    unfold word_gc_move_list_code. rewrite ev_while. sx_simp.
    rewrite (proj1 (Bool.not_true_iff_false (bool_decide (n2w (N.succ n) = n2w 0 :> word a)))
               ltac:(intros E; apply bool_decide_spec in E; exact (Hne E))); cbn [negb].
    cbn [list_Seq]. sx_all. rewrite n2w_succ_sub1. rw_eval Ev'. sx_all.
    cbn [cont_loop]. replace (clock s + (ck2 + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    subst s2. unfold word_gc_move_list_code in Er. cbn [list_Seq] in Er.
    autorewrite with nf in Er. cbn [clock regs memory set_regs set_clock set_memory] in Er.
    autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er.
    rw_eval Er. st_fin.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_list_code_thm" *)
Theorem word_gc_move_list_code_thm : forall (l a0 : word a) (s : state) pa1 pa old m1 m i1 i dm conf a1,
  word_gc_move_list conf (a0, (l, (i, (pa, (old, (m, dm)))))) = (a1, (i1, (pa1, (m1, true)))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) ->
  6 IN FDOM (regs s) ->
  get_var 7 s = SOME (Word l) /\ get_var 8 s = SOME (Word a0) ->
  exists ck r0 r1 r2 r5 r6,
    evaluate (word_gc_move_list_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, Word (n2w 0)); (8, Word a1)])
             (set_memory m1 s)).
Proof.
  intros l a0 s pa1 pa old m1 m i1 i dm conf a1 (H & Hr) H6 (H7 & H8).
  apply (word_gc_move_list_code_thm_n (w2n l) conf a0 s pa1 pa old m1 m i1 i dm a1). rewrite !n2w_w2n.
  splits; try assumption; apply w2n_lt || tauto.
Qed.


Lemma bd_F {P : Prop} {d : Decision P} : ~ P -> bool_decide P = false.
Proof. intros HP; apply Bool.not_true_iff_false; intros E; apply bool_decide_spec in E; exact (HP E). Qed.

Lemma word_gc_move_loop_f_F : forall f conf (pb i pa old : word a) m dm i1 pa1 m1 c1,
  word_gc_move_loop_f f conf pb i pa old m dm false = (i1, (pa1, (m1, c1))) -> c1 = false.
Proof.
  induction f as [|f IH]; intros conf pb i pa old m dm i1 pa1 m1 c1 H; cbn [word_gc_move_loop_f] in H;
    (destruct (decide (pb = pa)); [injection H as _ _ _ <-; reflexivity|]).
  - injection H as _ _ _ <-; reflexivity.
  - cbv zeta in H. rewrite Bool.andb_false_l in H. destruct (word_bit _ _).
    + exact (IH _ _ _ _ _ _ _ _ _ _ _ H).
    + destruct (word_gc_move_list _ _) as (?, (?, (?, (?, ?)))). exact (IH _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_loop_F" *)
Theorem word_gc_move_loop_F : forall k conf (pb i pa old : word a) m dm i1 pa1 m1 c1,
  word_gc_move_loop k conf (pb, (i, (pa, (old, (m, (dm, false)))))) = (i1, (pa1, (m1, c1))) -> ~ c1.
Proof.
  intros k conf pb i pa old m dm i1 pa1 m1 c1 H. apply word_gc_move_loop_f_F in H. subst c1. discriminate.
Qed.

Lemma word_gc_move_loop_f_ok f conf (pb i pa old : word a) m dm c i1 pa1 m1 c1 :
  word_gc_move_loop_f f conf pb i pa old m dm c = (i1, (pa1, (m1, c1))) -> c1 = true -> c = true.
Proof.
  destruct c; [reflexivity|]. intros H ->. apply word_gc_move_loop_f_F in H. discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_loop_ok" *)
Theorem word_gc_move_loop_ok : forall k conf (pb i pa old : word a) m dm c i1 pa1 m1 c1,
  word_gc_move_loop k conf (pb, (i, (pa, (old, (m, (dm, c)))))) = (i1, (pa1, (m1, c1))) -> c1 -> c.
Proof.
  intros k conf pb i pa old m dm c i1 pa1 m1 c1 H Hc. unfold is_true in *.
  exact (word_gc_move_loop_f_ok _ _ _ _ _ _ _ _ _ _ _ _ _ H Hc).
Qed.

Local Theorem word_gc_move_loop_code_thm_f : forall f conf pb1 i1 pa1 old1 m1 dm1 c1 i2 pa2 m2 (s : state),
  word_gc_move_loop_f f conf pb1 i1 pa1 old1 m1 dm1 c1 = (i2, (pa2, (m2, true))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ (len_size conf + 2 < dimindex a)%N /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old1) /\ use_store s /\
  memory s = m1 /\ mdomain s = dm1 /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa1) /\ get_var 4 s = SOME (Word i1) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\ 7 IN FDOM (regs s) /\
  get_var 8 s = SOME (Word pb1) /\ c1 = true ->
  exists ck r0 r1 r2 r5 r6 r7,
    evaluate (word_gc_move_loop_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa2); (4, Word i2); (5, r5); (6, r6);
                                 (7, r7); (8, Word pa2)])
             (set_memory m2 s)).
Proof.
  induction f as [|f IH];
    intros conf pb1 i1 pa1 old1 m1 dm1 c1 i2 pa2 m2 s
      (H & Hsl & Hws & H2 & Hls & Hls2 & Hsh & Hold & Hus & Hm & Hdm & H0 & H1 & H2r & H3 & H4 & H5 & H6 & H7 & H8 & ->);
    unfold get_var in *; subst m1 dm1;
    fdom_val H0 0 v0 Ev0; fdom_val H1 1 v1 Ev1; fdom_val H2r 2 v2 Ev2; fdom_val H5 5 v5 Ev5;
    fdom_val H6 6 v6 Ev6; fdom_val H7 7 v7 Ev7;
    cbn [word_gc_move_loop_f] in H;
    (destruct (decide (pb1 = pa1)) as [<-|Hne];
     [injection H as <- <- <-; exists 0, v0, v1, v2, v5, v6, v7; rewrite N.add_0_r;
      unfold word_gc_move_loop_code; rewrite ev_while; sx_simp; rewrite set_clock_same; st_fin|]).
  - discriminate.
  - cbv zeta in H. rewrite Bool.andb_true_l in H.
    destruct (memory s pb1) as [hv|l1 l2] eqn:Em.
    2:{ exfalso. cbn [wordSem.isWord wordSem.theWord] in H. rewrite Bool.andb_false_r in H.
        destruct (word_bit _ _) in H.
        - apply word_gc_move_loop_f_F in H; discriminate.
        - destruct (word_gc_move_list _ _) as (?, (?, (?, (?, ?)))). apply word_gc_move_loop_f_F in H; discriminate. }
    cbn [wordSem.isWord wordSem.theWord] in H. rewrite Bool.andb_true_r in H.
    assert (Hin : pb1 IN mdomain s).
    { destruct (word_bit _ _) in H.
      - apply word_gc_move_loop_f_ok in H; [|reflexivity]. apply bool_decide_spec in H; exact H.
      - destruct (word_gc_move_list _ _) as (?, (?, (?, (?, ?)))). apply word_gc_move_loop_f_ok in H; [|reflexivity].
        apply andb_prop in H as [H _]. apply bool_decide_spec in H; exact H. }
    rewrite (proj2 (bool_decide_spec _) Hin) in H. cbn [andb] in H.
    assert (Hne' : pa1 <> pb1) by congruence.
    destruct (word_bit 2 hv) eqn:Eb.
    + assert (Et : (hv && n2w 4)%w <> n2w 0) by (apply word_bit_test in Eb; exact Eb).
      set (L := decode_length conf hv) in H.
      destruct (IH conf (pb1 + (L + n2w 1) * bytes_in_word)%w i1 pa1 old1 (memory s) (mdomain s) true i2 pa2 m2
                  (set_regs (regs s |+ (7, Word ((L + n2w 1) * bytes_in_word)%w)
                                    |+ (8, Word (pb1 + (L + n2w 1) * bytes_in_word)%w)) s))
        as (ck & p0 & p1 & p2 & p5 & p6 & p7 & Er).
      { unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
        splits; try assumption; try reflexivity;
          unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
      exists (ck + 1), p0, p1, p2, p5, p6, p7.
      unfold word_gc_move_loop_code. rewrite ev_while. sx_simp.
      rewrite (bd_F Hne'). cbn [negb list_Seq]. sx_all. rewrite Em. sx_all. rewrite (bd_F Et). sx_all. rewrite word_sh_lsr by lia. sx_all. rewrite word_sh_lsl by lia. sx_all.
      cbn [cont_loop]. replace (clock s + (ck + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
      rewrite Hsh. unfold word_gc_move_loop_code in Er. cbn [list_Seq] in Er.
      autorewrite with nf in Er. cbn [clock regs memory set_regs set_clock set_memory] in Er.
      autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er.
      rw_eval Er. st_fin.
    + assert (Et : (hv && n2w 4)%w = n2w 0).
      { destruct (decide ((hv && n2w 4)%w = n2w 0)) as [E|E]; [exact E|].
        assert (Eb' : word_bit 2 hv) by (apply word_bit_test; exact E). unfold is_true in Eb'; congruence. }
      set (L := decode_length conf hv) in H.
      destruct (word_gc_move_list conf ((pb1 + bytes_in_word)%w, (L, (i1, (pa1, (old1, (memory s, mdomain s)))))))
        as (pb', (i1', (pa1', (m1', c1')))) eqn:Eml.
      assert (c1' = true) as -> by (apply word_gc_move_loop_f_ok in H; [exact H|reflexivity]).
      set (s5 := set_regs (regs s |+ (7, Word L) |+ (8, Word (pb1 + bytes_in_word)%w)) s).
      destruct (word_gc_move_list_code_thm L (pb1 + bytes_in_word)%w s5 pa1' pa1 old1 m1' (memory s) i1' i1
                  (mdomain s) conf pb') as (ck1 & q0 & q1 & q2 & q5 & q6 & Ev).
      { subst s5; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
        splits; try assumption; try reflexivity;
          unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
      { subst s5; unfold pred_set.IN, FDOM; nf_fields; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
      { subst s5; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]. split; reflexivity. }
      set (s6 := set_regs (regs s5 |++ [(0, q0); (1, q1); (2, q2); (3, Word pa1'); (4, Word i1'); (5, q5); (6, q6);
                                        (7, Word (n2w 0)); (8, Word pb')]) (set_memory m1' s5)).
      destruct (IH conf pb' i1' pa1' old1 m1' (mdomain s) true i2 pa2 m2 s6)
        as (ck2 & p0 & p1 & p2 & p5 & p6 & p7 & Er).
      { subst s6 s5; unfold get_var; nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
        splits; try assumption; try reflexivity; try lia;
          unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
      pose proof (evaluate_add_clock (ck2 + 1) (word_gc_move_list_code conf) (set_clock (clock s5 + ck1) s5)) as Ev'.
      assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
      specialize (Ev' NONE _ (conj Ev NT)). subst s5. autorewrite with nf in Ev'.
      cbn [clock regs memory set_regs set_clock set_memory] in Ev'. autorewrite with nf in Ev'. cbn [FUPDATE_LIST FOLDL] in Ev'.
      exists (ck1 + ck2 + 1), p0, p1, p2, p5, p6, p7.
      unfold word_gc_move_loop_code. rewrite ev_while. sx_simp.
      rewrite (bd_F Hne'). cbn [negb list_Seq]. sx_all. rewrite Em. sx_all. rewrite Et. sx_simp.
      sx_all.
      rewrite word_sh_lsr by lia. sx_all. rw_eval Ev'. sx_simp.
      cbn [cont_loop]. replace (clock s + (ck2 + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
      subst s6. unfold word_gc_move_loop_code in Er. cbn [list_Seq] in Er.
      autorewrite with nf in Er. cbn [clock regs memory set_regs set_clock set_memory] in Er.
      autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er.
      sx_simp. rw_eval Er. st_fin.
Qed.


(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_loop_code_thm" *)
Local Theorem word_gc_move_loop_code_thm : forall k conf pb1 i1 pa1 old1 m1 dm1 c1 i2 pa2 m2 (s : state),
  word_gc_move_loop k conf (pb1, (i1, (pa1, (old1, (m1, (dm1, c1)))))) = (i2, (pa2, (m2, true))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ (len_size conf + 2 < dimindex a)%N /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old1) /\ use_store s /\
  memory s = m1 /\ mdomain s = dm1 /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa1) /\ get_var 4 s = SOME (Word i1) /\
  5 IN FDOM (regs s) ->
  6 IN FDOM (regs s) ->
  7 IN FDOM (regs s) ->
  get_var 8 s = SOME (Word pb1) /\ c1 ->
  exists ck r0 r1 r2 r5 r6 r7,
    evaluate (word_gc_move_loop_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa2); (4, Word i2); (5, r5); (6, r6);
                                 (7, r7); (8, Word pa2)])
             (set_memory m2 s)).
Proof.
  intros k conf pb1 i1 pa1 old1 m1 dm1 c1 i2 pa2 m2 s H H6 H7 (H8 & Hc).
  apply (word_gc_move_loop_code_thm_f (N.to_nat k) conf pb1 i1 pa1 old1 m1 dm1 c1). unfold is_true in Hc.
  destruct H as (H & Hr). unfold word_gc_move_loop in H. tauto.
Qed.

End Simple.

(** ** The simple copying collector: stack scanning *)

Lemma DROP_0 {A} (l : list A) : DROP 0 l = l.
Proof. destruct l; reflexivity. Qed.

Lemma DROP_cons_succ {A} : forall (l : list A) k h t, DROP k l = h :: t -> DROP (k + 1) l = t /\ (k < LENGTH l)%N.
Proof.
  induction l as [|x xs IH]; intros k h t H; [discriminate|].
  cbn [DROP] in H |- *. rewrite LENGTH_length in *. cbn [length].
  destruct (N.eqb_spec k 0) as [->|Hk].
  - injection H as -> ->. cbn [N.add N.eqb]. replace (1 - 1)%N with 0%N by lia. rewrite DROP_0. split; [reflexivity|lia].
  - destruct (N.eqb_spec (k + 1) 0); [lia|]. replace (k + 1 - 1)%N with (k - 1 + 1)%N by lia.
    destruct (IH _ _ _ H) as [E Hl]. split; [exact E|lia].
Qed.

(* HOL [map_bitmap_APPEND_APPEND] (a [Q.prove] value, not a stored theorem). *)
Lemma map_bitmap_APPEND_APPEND {A} : forall vs1 (stack : list A) x0 x1 ws2 vs2 ws1,
  filter_bitmap vs1 stack = SOME (x0, x1) /\ LENGTH x0 = LENGTH ws1 ->
  map_bitmap (vs1 ++ vs2) (ws1 ++ ws2) stack =
  match map_bitmap vs1 ws1 stack with
  | NONE => NONE
  | SOME (ts1, (ts2, ts3)) =>
      match map_bitmap vs2 ws2 ts3 with
      | NONE => NONE
      | SOME (us1, (us2, us3)) => SOME (ts1 ++ us1, (ts2 ++ us2, us3))
      end
  end.
Proof.
  induction vs1 as [|b vs1 IH]; intros stack x0 x1 ws2 vs2 ws1 [Hf Hl].
  - cbn in Hf. injection Hf as <- <-. destruct ws1; [|rewrite !LENGTH_length in Hl; cbn in Hl; lia].
    cbn [app map_bitmap]. destruct (map_bitmap vs2 ws2 stack) as [[? [? ?]]|]; reflexivity.
  - destruct stack as [|r stack]; [destruct b; discriminate|].
    destruct b; cbn [filter_bitmap] in Hf.
    + destruct (filter_bitmap vs1 stack) as [[ts rs]|] eqn:E; [|discriminate]. injection Hf as <- <-.
      destruct ws1 as [|w ws1]; [rewrite !LENGTH_length in Hl; cbn in Hl; lia|].
      cbn [app map_bitmap]. rewrite (IH stack ts rs ws2 vs2 ws1) by (split; [exact E|rewrite !LENGTH_length in *; cbn in Hl; lia]).
      destruct (map_bitmap vs1 ws1 stack) as [[t1 [t2 t3]]|]; [|reflexivity].
      destruct (map_bitmap vs2 ws2 t3) as [[u1 [u2 u3]]|]; reflexivity.
    + cbn [app map_bitmap]. rewrite (IH stack x0 x1 ws2 vs2 ws1) by (split; assumption).
      destruct (map_bitmap vs1 ws1 stack) as [[t1 [t2 t3]]|]; [|reflexivity].
      destruct (map_bitmap vs2 ws2 t3) as [[u1 [u2 u3]]|]; reflexivity.
Qed.

Section GCdefs.
Context {a : N}.
Local Abbreviation mem := (word a -> word_loc a).
Local Abbreviation dom := (word a -> Prop).
Local Open Scope word_scope.
#[local] Instance word_inhabited' : Inhabited (word a) := n2w 0.
#[local] Instance word_loc_inhabited' : Inhabited (word_loc a) := Word (n2w 0).

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_roots_bitmaps_def" *)
Definition word_gc_move_roots_bitmaps (conf : config)
    (x : list (word_loc a) * (list (word a) * (word a * (word a * (word a * (mem * dom))))))
    : list (word_loc a) * (word a * (word a * (mem * bool))) :=
  let '(stack, (bitmaps, (i1, (pa1, (curr, (m, dm)))))) := x in
  match enc_stack bitmaps stack with
  | NONE => (ARB, (ARB, (ARB, (ARB, false))))
  | SOME wl_list =>
      let '(wl, (i2, (pa2, (m2, c2)))) := word_gc_move_roots conf (wl_list, (i1, (pa1, (curr, (m, dm))))) in
      match dec_stack bitmaps wl stack with
      | NONE => (ARB, (ARB, (ARB, (ARB, false))))
      | SOME stack => (stack, (i2, (pa2, (m2, c2))))
      end
  end.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_bitmaps_def" *)
Definition word_gc_move_bitmaps (conf : config)
    (x : word_loc a * (list (word_loc a) * (list (word a) * (word a * (word a * (word a * (mem * dom)))))))
    : option (list (word_loc a) * (list (word_loc a) * (word a * (word a * (mem * bool))))) :=
  let '(w, (stack, (bitmaps, (i1, (pa1, (curr, (m, dm))))))) := x in
  match full_read_bitmap bitmaps w with
  | NONE => NONE
  | SOME bs =>
      match filter_bitmap bs stack with
      | NONE => NONE
      | SOME (ts, ws) =>
          let '(wl, (i2, (pa2, (m2, c2)))) := word_gc_move_roots conf (ts, (i1, (pa1, (curr, (m, dm))))) in
          match map_bitmap bs wl stack with
          | NONE => NONE
          | SOME (hd, (ts1, ws')) => SOME (hd, (ws, (i2, (pa2, (m2, c2)))))
          end
      end
  end.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_roots_APPEND" *)
Local Theorem word_gc_move_roots_APPEND : forall conf curr dm xs ys (i1 pa1 : word a) (m : mem),
  word_gc_move_roots conf (xs ++ ys, (i1, (pa1, (curr, (m, dm))))) =
  let '(ws1, (i1, (pa1, (m1, c1)))) := word_gc_move_roots conf (xs, (i1, (pa1, (curr, (m, dm))))) in
  let '(ws2, (i2, (pa2, (m2, c2)))) := word_gc_move_roots conf (ys, (i1, (pa1, (curr, (m1, dm))))) in
  (ws1 ++ ws2, (i2, (pa2, (m2, andb c1 c2)))).
Proof.
  intros conf curr dm xs; induction xs as [|x xs IH]; intros ys i1 pa1 m.
  - cbn [app]. rewrite (proj1 (word_gc_move_roots_def conf i1 pa1 curr m dm (Word (n2w 0)) [])).
    destruct (word_gc_move_roots conf (ys, _)) as (ws2, (i2, (pa2, (m2, c2)))). reflexivity.
  - cbn [app]. rewrite !(proj2 (word_gc_move_roots_def _ _ _ _ _ _ _ _)).
    destruct (word_gc_move conf _) as (w1, (i1', (pa1', (m1', c1')))).
    rewrite IH.
    destruct (word_gc_move_roots conf (xs, _)) as (ws1, (i2, (pa2, (m2, c2)))).
    destruct (word_gc_move_roots conf (ys, _)) as (ws3, (i3, (pa3, (m3, c3)))).
    cbn [app]. rewrite Bool.andb_assoc. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_roots_IMP_LENGTH" *)
Theorem word_gc_move_roots_IMP_LENGTH : forall xs (r0 r1 curr : word a) r2 dm ys i2 pa2 m2 c conf,
  word_gc_move_roots conf (xs, (r0, (r1, (curr, (r2, dm))))) = (ys, (i2, (pa2, (m2, c)))) ->
  LENGTH ys = LENGTH xs.
Proof.
  induction xs as [|x xs IH]; intros r0 r1 curr r2 dm ys i2 pa2 m2 c conf H.
  - rewrite (proj1 (word_gc_move_roots_def conf r0 r1 curr r2 dm (Word (n2w 0)) [])) in H.
    injection H as <-; reflexivity.
  - rewrite (proj2 (word_gc_move_roots_def _ _ _ _ _ _ _ _)) in H.
    destruct (word_gc_move conf _) as (w1, (i1', (pa1', (m1', c1')))).
    destruct (word_gc_move_roots conf (xs, _)) as (ws1, (i3, (pa3, (m3, c3)))) eqn:E.
    injection H as <- _ _ _ _. apply IH in E. rewrite !LENGTH_length in *. cbn [length]. lia.
Qed.


(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_roots_bitmaps" 656 *)
Local Theorem word_gc_move_roots_bitmaps_unroll : forall conf bitmaps curr dm stack (i1 pa1 : word a) (m : mem)
    stack2 i2 pa2 m2,
  word_gc_move_roots_bitmaps conf (stack, (bitmaps, (i1, (pa1, (curr, (m, dm)))))) =
    (stack2, (i2, (pa2, (m2, true)))) ->
  word_gc_move_roots_bitmaps conf (stack, (bitmaps, (i1, (pa1, (curr, (m, dm)))))) =
  match stack with
  | [] => (ARB, (ARB, (ARB, (ARB, false))))
  | w :: ws =>
      if decide (w = Word (n2w 0)) then (stack, (i1, (pa1, (m, ⌜ws = []⌝)))) else
      match word_gc_move_bitmaps conf (w, (ws, (bitmaps, (i1, (pa1, (curr, (m, dm))))))) with
      | NONE => (ARB, (ARB, (ARB, (ARB, false))))
      | SOME (new, (stack, (i2, (pa2, (m2, c2))))) =>
          let '(stack, (i, (pa, (m, c3)))) :=
            word_gc_move_roots_bitmaps conf (stack, (bitmaps, (i2, (pa2, (curr, (m2, dm)))))) in
          (w :: new ++ stack, (i, (pa, (m, andb c2 c3))))
      end
  end.
Proof.
  intros conf bitmaps curr dm [|w ws] i1 pa1 m stack2 i2 pa2 m2 H; [reflexivity|].
  revert H. unfold word_gc_move_roots_bitmaps at 1 2. rewrite (proj2 enc_stack_def).
  destruct (decide (w = Word (n2w 0))) as [->|Hw].
  - rewrite (proj2 (bool_decide_spec _) eq_refl).
    destruct (decide (ws = [])) as [->|Hws].
    + rewrite (proj2 (bool_decide_spec _) eq_refl).
      rewrite (proj1 (word_gc_move_roots_def conf i1 pa1 curr m dm (Word (n2w 0)) [])).
      rewrite (proj2 dec_stack_def), (proj2 (bool_decide_spec _) eq_refl). cbn. reflexivity.
    + rewrite (bd_F Hws). discriminate.
  - rewrite (bd_F (fun E => Hw E)). unfold word_gc_move_bitmaps.
    destruct (full_read_bitmap bitmaps w) as [bs|] eqn:Ebs; [|reflexivity].
    destruct (filter_bitmap bs ws) as [[ts ws']|] eqn:Ef; [|reflexivity].
    destruct (enc_stack bitmaps ws') as [rest|] eqn:Ee.
    2:{ intros H. cbn beta iota zeta in H. injection H as _ _ _ _ E. discriminate. }
    rewrite word_gc_move_roots_APPEND.
    destruct (word_gc_move_roots conf (ts, _)) as (wl1, (i3, (pa3, (m3, c3)))) eqn:Er1.
    destruct (word_gc_move_roots conf (rest, _)) as (wl2, (i4, (pa4, (m4, c4)))) eqn:Er2.
    rewrite (proj2 dec_stack_def), (bd_F (fun E => Hw E)), Ebs.
    assert (Hl : LENGTH wl1 = LENGTH ts) by (eapply word_gc_move_roots_IMP_LENGTH; exact Er1).
    rewrite (map_bitmap_APPEND wl2 bs wl1 ws ts ws' (conj Ef Hl)).
    destruct (map_bitmap bs wl1 ws) as [[hd [ts0 ws0]]|] eqn:Em; [|reflexivity].
    destruct (filter_bitmap_map_bitmap bs ws wl1 ts ws' ts0 hd ws0 (conj Ef (conj Hl Em))) as [-> ->].
    cbn [app]. unfold word_gc_move_roots_bitmaps. rewrite Ee, Er2.
    destruct (dec_stack bitmaps wl2 ws') as [st|].
    + intros _. reflexivity.
    + intros H. injection H as _ _ _ _ E. discriminate.
Qed.


(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_bitmap_def" *)
Definition word_gc_move_bitmap (conf : config)
    (x : word a * (list (word_loc a) * (word a * (word a * (word a * (mem * dom))))))
    : option (list (word_loc a) * (list (word_loc a) * (word a * (word a * (mem * bool))))) :=
  let '(w, (stack, (i1, (pa1, (curr, (m, dm)))))) := x in
  let bs := get_bits w in
  match filter_bitmap bs stack with
  | NONE => NONE
  | SOME (ts, ws) =>
      let '(wl, (i2, (pa2, (m2, c2)))) := word_gc_move_roots conf (ts, (i1, (pa1, (curr, (m, dm))))) in
      match map_bitmap bs wl stack with
      | NONE => NONE
      | SOME (hd, v2) => SOME (hd, (ws, (i2, (pa2, (m2, c2)))))
      end
  end.

Lemma GENLIST_ext_lt {A} (f g : N -> A) n : (forall i, (i < n)%N -> f i = g i) -> GENLIST f n = GENLIST g n.
Proof.
  induction n as [|n IH] using N.peano_ind; intros H; [reflexivity|].
  rewrite !(proj2 (GENLIST_thm _ n)), IH by (intros i Hi; apply H; lia). f_equal. apply H; lia.
Qed.

Lemma get_bits_cons (w : word a) : w <> n2w 0 -> w <> n2w 1 -> get_bits w = w ' 0 :: get_bits (w >>> 1).
Proof.
  intros H0 H1. unfold get_bits. rewrite (bit_length_minus_1 w H0).
  assert (Hb : bit_length (w >>> 1) <> 0%N).
  { intros E. pose proof (bit_length_minus_1 w H0) as E'. rewrite E in E'.
    pose proof (bit_length_def w) as D. rewrite (bd_F H0) in D. apply H1, bit_length_eq_1. lia. }
  pose proof (bit_length_LESS_EQ_dimindex w) as Hd. rewrite (bit_length_def w), (bd_F H0) in Hd.
  replace (bit_length (w >>> 1)) with (SUC (bit_length (w >>> 1) - 1)) at 1 by lia.
  rewrite GENLIST_CONS_aux. f_equal.
  apply GENLIST_ext_lt. intros i Hi. rewrite fcp_index_word_lsr by lia.
  replace (N.succ i) with (i + 1)%N by lia.
  destruct (N.ltb_spec (i + 1) (dimindex a)); [reflexivity|lia].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_bitmap_unroll" *)
Local Theorem word_gc_move_bitmap_unroll : forall conf (w : word a) stack i1 pa1 curr m dm,
  word_gc_move_bitmap conf (w, (stack, (i1, (pa1, (curr, (m, dm)))))) =
  if decide (w = n2w 0) then SOME ([], (stack, (i1, (pa1, (m, true))))) else
  if decide (w = n2w 1) then SOME ([], (stack, (i1, (pa1, (m, true))))) else
  match stack with
  | [] => NONE
  | x :: xs =>
      if decide ((w && n2w 1) = n2w 0) then
        match word_gc_move_bitmap conf (w >>> 1, (xs, (i1, (pa1, (curr, (m, dm)))))) with
        | NONE => NONE
        | SOME (new, (stack, (i1, (pa1, (m, c))))) => SOME (x :: new, (stack, (i1, (pa1, (m, c)))))
        end
      else
        let '(x1, (i1, (pa1, (m1, c1)))) := word_gc_move conf (x, (i1, (pa1, (curr, (m, dm))))) in
        match word_gc_move_bitmap conf (w >>> 1, (xs, (i1, (pa1, (curr, (m1, dm)))))) with
        | NONE => NONE
        | SOME (new, (stack, (i1, (pa1, (m, c))))) => SOME (x1 :: new, (stack, (i1, (pa1, (m, andb c1 c)))))
        end
  end.
Proof.
  intros conf w stack i1 pa1 curr m dm.
  destruct (decide (w = n2w 0)) as [->|H0].
  { unfold word_gc_move_bitmap, get_bits. replace (bit_length (n2w 0 : word a)) with 0%N
      by (rewrite bit_length_def, (proj2 (bool_decide_spec _) eq_refl); reflexivity). reflexivity. }
  destruct (decide (w = n2w 1)) as [->|H1].
  { unfold word_gc_move_bitmap, get_bits. rewrite (proj2 (bit_length_eq_1 (n2w 1)) eq_refl). reflexivity. }
  unfold word_gc_move_bitmap at 1. rewrite (get_bits_cons w H0 H1).
  destruct stack as [|x xs]; [destruct (w ' 0); reflexivity|].
  destruct (decide ((w && n2w 1) = n2w 0)) as [Ha|Ha].
  - apply word_and_one_eq_0_iff in Ha. unfold is_true in Ha. apply Bool.not_true_iff_false in Ha. rewrite Ha.
    cbn [filter_bitmap map_bitmap]. unfold word_gc_move_bitmap.
    destruct (filter_bitmap (get_bits (w >>> 1)) xs) as [[ts ws]|]; [|reflexivity].
    destruct (word_gc_move_roots conf _) as (wl, (i2, (pa2, (m2, c2)))).
    destruct (map_bitmap (get_bits (w >>> 1)) wl xs) as [[hd [y z]]|]; reflexivity.
  - assert (Hb : w ' 0 = true).
    { destruct (w ' 0) eqn:E; [reflexivity|]. exfalso; apply Ha, word_and_one_eq_0_iff. unfold is_true; congruence. }
    rewrite Hb. cbn [filter_bitmap map_bitmap]. unfold word_gc_move_bitmap.
    destruct (filter_bitmap (get_bits (w >>> 1)) xs) as [[ts ws]|]; cbn beta iota.
    + rewrite (proj2 (word_gc_move_roots_def _ _ _ _ _ _ _ _)).
      destruct (word_gc_move conf _) as (x1, (i2, (pa2, (m2, c2)))).
      destruct (word_gc_move_roots conf (ts, _)) as (wl, (i3, (pa3, (m3, c3)))).
      cbn [map_bitmap]. destruct (map_bitmap (get_bits (w >>> 1)) wl xs) as [[hd [y z]]|]; reflexivity.
    + destruct (word_gc_move conf _) as (x1, (i2, (pa2, (m2, c2)))). reflexivity.
Qed.


(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_bitmaps_unroll" *)
Local Theorem word_gc_move_bitmaps_unroll : forall conf (w : word a) stack bitmaps i1 pa1 curr m dm x,
  word_gc_move_bitmaps conf (Word w, (stack, (bitmaps, (i1, (pa1, (curr, (m, dm))))))) = SOME x /\
  (LENGTH bitmaps < dimword a - 1)%N /\ good_dimindex a ->
  word_gc_move_bitmaps conf (Word w, (stack, (bitmaps, (i1, (pa1, (curr, (m, dm))))))) =
  match DROP (w2n (w - n2w 1)) bitmaps with
  | [] => NONE
  | y :: ys =>
      match word_gc_move_bitmap conf (y, (stack, (i1, (pa1, (curr, (m, dm)))))) with
      | NONE => NONE
      | SOME (hd, (ws, (i2, (pa2, (m2, c2))))) =>
          if negb (word_msb y) then SOME (hd, (ws, (i2, (pa2, (m2, c2))))) else
          match word_gc_move_bitmaps conf (Word (w + n2w 1), (ws, (bitmaps, (i2, (pa2, (curr, (m2, dm))))))) with
          | NONE => NONE
          | SOME (hd3, (ws3, (i3, (pa3, (m3, c3))))) => SOME (hd ++ hd3, (ws3, (i3, (pa3, (m3, andb c2 c3)))))
          end
      end
  end.
Proof.
  intros conf w stack bitmaps i1 pa1 curr m dm x (Hx & Hlen & Hg).
  destruct (decide (w = n2w 0)) as [->|Hw0].
  { unfold word_gc_move_bitmaps, full_read_bitmap in Hx. rewrite (proj2 (bool_decide_spec _) eq_refl) in Hx.
    discriminate. }
  clear Hx. unfold word_gc_move_bitmaps at 1. unfold full_read_bitmap at 1. rewrite (bd_F Hw0).
  destruct (DROP (w2n (w - n2w 1)) bitmaps) as [|h t] eqn:Ed; [reflexivity|].
  cbn [read_bitmap]. destruct (word_msb h) eqn:Hm.
  - destruct (DROP_cons_succ _ _ _ _ Ed) as [Ed' Hlt].
    rewrite (w2n_sub1 w Hw0) in Ed', Hlt.
    pose proof (w2n_ne0 w Hw0) as Hw0'.
    replace (w2n w - 1 + 1)%N with (w2n w) in Ed' by lia.
    assert (Hw1 : (w + n2w 1 : word a) <> n2w 0).
    { intros E. apply (f_equal w2n) in E. rewrite <- (n2w_w2n w), word_add_n2w, !w2n_n2w_small in E; lia. }
    unfold word_gc_move_bitmap at 1.
    destruct (read_bitmap t) as [bs'|] eqn:Er.
    + rewrite (get_bits_intro h Hm), filter_bitmap_APPEND.
      destruct (filter_bitmap (get_bits h) stack) as [[zs rs]|] eqn:Ef1; [|reflexivity].
      cbn beta iota.
      destruct (word_gc_move_roots conf (zs, _)) as (wl1, (i2, (pa2, (m2, c2)))) eqn:Er1.
      assert (Hl1 : LENGTH zs = LENGTH wl1) by (symmetry; eapply word_gc_move_roots_IMP_LENGTH; exact Er1).
      destruct (map_bitmap (get_bits h) wl1 stack) as [[t1 [t2 t3]]|] eqn:Em1.
      2:{ destruct (filter_bitmap bs' rs) as [[zs2 rs']|]; [|reflexivity]. cbn beta iota.
          rewrite word_gc_move_roots_APPEND, Er1.
          destruct (word_gc_move_roots conf (zs2, _)) as (wl2, (i3, (pa3, (m3, c3)))).
          rewrite (map_bitmap_APPEND_APPEND _ _ _ _ wl2 bs' _ (conj Ef1 Hl1)), Em1. reflexivity. }
      destruct (filter_bitmap_map_bitmap (get_bits h) stack wl1 zs rs t2 t1 t3 (conj Ef1 (conj (eq_sym Hl1) Em1)))
        as [-> ->].
      cbn [negb]. unfold word_gc_move_bitmaps, full_read_bitmap. rewrite (bd_F Hw1).
      replace (w + n2w 1 - n2w 1) with w by word_ring. rewrite Ed', Er.
      destruct (filter_bitmap bs' rs) as [[zs2 rs']|] eqn:Ef2; [|reflexivity]. cbn beta iota.
      rewrite word_gc_move_roots_APPEND, Er1.
      destruct (word_gc_move_roots conf (zs2, _)) as (wl2, (i3, (pa3, (m3, c3)))).
      rewrite (map_bitmap_APPEND_APPEND _ _ _ _ wl2 bs' _ (conj Ef1 Hl1)), Em1.
      destruct (map_bitmap bs' wl2 rs) as [[u1 [u2 u3]]|]; reflexivity.
    + destruct (filter_bitmap (get_bits h) stack) as [[zs rs]|]; [|reflexivity]. cbn beta iota.
      destruct (word_gc_move_roots conf (zs, _)) as (wl1, (i2, (pa2, (m2, c2)))).
      destruct (map_bitmap (get_bits h) wl1 stack) as [[t1 t2]|]; [|reflexivity]. cbn [negb].
      unfold word_gc_move_bitmaps, full_read_bitmap. rewrite (bd_F Hw1).
      replace (w + n2w 1 - n2w 1) with w by word_ring. rewrite Ed', Er. reflexivity.
  - cbn [negb]. unfold word_gc_move_bitmap. fold (get_bits h).
    destruct (filter_bitmap (get_bits h) stack) as [[zs rs]|]; [|reflexivity]. cbn beta iota.
    destruct (word_gc_move_roots conf (zs, _)) as (wl1, (i2, (pa2, (m2, c2)))).
    destruct (map_bitmap (get_bits h) wl1 stack) as [[t1 [t2 t3]]|]; reflexivity.
Qed.

End GCdefs.

Section BitmapCode.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.

Lemma ev_sla r rn (X : state) :
  evaluate (StackLoadAny r rn, X) =
  if negb (use_stack X) then (SOME Error, X) else
  match get_var rn X with
  | SOME (Word w) =>
      let i := (stack_space X + w2n (w >>> word_shift a))%N in
      if andb (i <? LENGTH (stack X))%N (bool_decide ((w >>> word_shift a) << word_shift a = w)%w)
      then (NONE, set_var r (EL i (stack X)) X)
      else (SOME Error, empty_env X)
  | _ => (SOME Error, empty_env X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_ssa r rn (X : state) :
  evaluate (StackStoreAny r rn, X) =
  if negb (use_stack X) then (SOME Error, X) else
  match get_var r X, get_var rn X with
  | SOME v, SOME (Word w) =>
      let i := (stack_space X + w2n (w >>> word_shift a))%N in
      if andb (i <? LENGTH (stack X))%N (bool_decide ((w >>> word_shift a) << word_shift a = w)%w)
      then (NONE, set_stack (LUPDATE v i (stack X)) X)
      else (SOME Error, empty_env X)
  | _, _ => (SOME Error, empty_env X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_bml r v (X : state) :
  evaluate (BitmapLoad r v, X) =
  if orb (negb (use_stack X)) (r =? v)%N then (SOME Error, X) else
  match get_var v X with
  | SOME (Word w) =>
      if (LENGTH (bitmaps X) <=? w2n w)%N then (SOME Error, X)
      else (NONE, set_var r (Word (EL (w2n w) (bitmaps X))) X)
  | _ => (SOME Error, X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

End BitmapCode.

Ltac sx_step2 := first [ sx_step | rewrite ev_sla | rewrite ev_ssa | rewrite ev_bml ].
Ltac sx_all2 := repeat (sx_step2; sx_simp; rewrite ?sx_store_upd; sx_dec; sx_simp).

Section BitmapThm.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.

Lemma lo2_false (w : word a) : good_dimindex a -> w <> n2w 0 -> w <> n2w 1 -> (w <+ n2w 2)%w = false.
Proof.
  intros Hg H0 H1. destruct (w <+ n2w 2)%w eqn:E; [|reflexivity].
  apply (lower_2w_eq w Hg) in E. destruct E; contradiction.
Qed.

Lemma lo2_true (w : word a) : good_dimindex a -> w = n2w 0 \/ w = n2w 1 -> (w <+ n2w 2)%w = true.
Proof. intros Hg H. apply (lower_2w_eq w Hg) in H. exact H. Qed.

Lemma w2n_lsr1_lt (w : word a) : w <> n2w 0 -> (w2n (w >>> 1) < w2n w)%N.
Proof. intros H. rewrite w2n_lsr. pose proof (w2n_ne0 w H). cbn [N.pow]. apply N.div_lt; lia. Qed.

Lemma bytes_n2w_succ (L : N) : ((bytes_in_word * n2w L + bytes_in_word : word a) = bytes_in_word * n2w (L + 1))%w.
Proof. rewrite <- word_add_n2w. word_ring. Qed.

Local Theorem word_gc_move_bitmap_code_thm_n : forall n (w : word a) stack (s : state) i pa curr m dm new stack1
    i1 pa1 m1 old init conf,
  (w2n w < n)%N ->
  word_gc_move_bitmap conf (w, (stack, (i, (pa, (curr, (m, dm)))))) = SOME (new, (stack1, (i1, (pa1, (m1, true))))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ good_dimindex a /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word curr) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ use_stack s /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\
  get_var 7 s = SOME (Word w) /\ get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
  stackSem.stack s = init ++ old ++ stack /\ stack_space s = LENGTH init /\
  (dimindex a DIV 8 * LENGTH (stackSem.stack s) < dimword a)%N ->
  exists ck r0 r1 r2 r5 r6 r7,
    evaluate (word_gc_move_bitmap_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, r7); (8, Word (bytes_in_word * n2w (LENGTH (old ++ new))))])
             (set_memory m1 (set_stack (init ++ old ++ new ++ stack1) s))).
Proof.
  induction n as [|n IH] using N.peano_ind; intros w stack s i pa curr m dm new stack1 i1 pa1 m1 old init conf Hn;
    [lia|].
  intros (H & Hsl & Hws & H2 & Hls & Hg & Hsh & Hold & Hus & Hm & Hdm & Hust & H0 & H1 & H2r & H3 & H4 & H5 & H6
          & H7 & H8 & Hst & Hss & Hlen).
  unfold get_var in *; subst m dm.
  fdom_val H0 0 v0 Ev0; fdom_val H1 1 v1 Ev1; fdom_val H2r 2 v2 Ev2; fdom_val H5 5 v5 Ev5; fdom_val H6 6 v6 Ev6.
  rewrite word_gc_move_bitmap_unroll in H.
  destruct (decide (w = n2w 0)) as [Hw0|Hw0].
  { injection H as <- <- <- <- <-. exists 0, v0, v1, v2, v5, v6, (Word w). rewrite N.add_0_r.
    unfold word_gc_move_bitmap_code. rewrite ev_while. sx_simp.
    rewrite (lo2_true w Hg (or_introl Hw0)). sx_simp. rewrite set_clock_same, app_nil_r. cbn [app].
    rewrite <- Hst. st_fin. }
  destruct (decide (w = n2w 1)) as [Hw1|Hw1].
  { injection H as <- <- <- <- <-. exists 0, v0, v1, v2, v5, v6, (Word w). rewrite N.add_0_r.
    unfold word_gc_move_bitmap_code. rewrite ev_while. sx_simp.
    rewrite (lo2_true w Hg (or_intror Hw1)). sx_simp. rewrite set_clock_same, app_nil_r. cbn [app].
    rewrite <- Hst. st_fin. }
  destruct stack as [|x xs]; [discriminate|].
  pose proof (w2n_lsr1_lt w Hw0) as Hlt.
  destruct (decide ((w && n2w 1)%w = n2w 0)) as [Ha|Ha].
  - destruct (word_gc_move_bitmap conf ((w >>> 1)%w, (xs, (i, (pa, (curr, (memory s, mdomain s)))))))
      as [[new' [st' [i' [pa' [m' c']]]]]|] eqn:Eb; [|discriminate].
    injection H as <- <- <- <- <- ->.
    destruct (IH (w >>> 1)%w xs
                (set_regs (regs s |+ (7, Word (w >>> 1)%w)
                                  |+ (8, Word (bytes_in_word * n2w (LENGTH (old ++ [x])))%w)) s)
                i pa curr (memory s) (mdomain s) new' st' i' pa' m' (old ++ [x]) init conf ltac:(lia))
      as (ck & p0 & p1 & p2 & p5 & p6 & p7 & Er).
    { unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
      splits; try assumption; try reflexivity;
        try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence).
      rewrite Hst, <- !app_assoc. reflexivity. }
    exists (ck + 1), p0, p1, p2, p5, p6, p7.
    unfold word_gc_move_bitmap_code. rewrite ev_while. sx_simp.
    rewrite (lo2_false w Hg Hw0 Hw1). cbn [negb]. sx_simp. sx_all. rewrite (proj2 (bool_decide_spec _) Ha).
    cbn [list_Seq].  sx_all. rewrite word_sh_lsr by lia. sx_all.
    rewrite bytes_n2w_succ.
    cbn [cont_loop]. replace (clock s + (ck + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    unfold word_gc_move_bitmap_code in Er. cbn [list_Seq] in Er.
    autorewrite with nf in Er. cbn [clock regs memory stackSem.stack set_regs set_clock set_memory set_stack] in Er.
    autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er.
    rewrite <- !app_assoc in Er. cbn [app] in Er. rewrite !LENGTH_length, app_length in Er |- *. cbn [length] in Er |- *.
    rewrite app_length in Er; cbn [length] in Er.
    replace (N.of_nat (length old) + 1)%N with (N.of_nat (length old + 1)) by lia.
    sx_simp. rw_eval Er. st_fin.
  - destruct (word_gc_move conf (x, (i, (pa, (curr, (memory s, mdomain s))))))
      as (x1, (i1', (pa1', (m1', c1)))) eqn:Emv.
    destruct (word_gc_move_bitmap conf ((w >>> 1)%w, (xs, (i1', (pa1', (curr, (m1', mdomain s)))))))
      as [[new' [st' [i' [pa' [m' c']]]]]|] eqn:Eb; [|discriminate].
    injection H as <- <- <- <- <- Hc. apply andb_prop in Hc as [-> ->].
    set (L := LENGTH old).
    assert (HL : (dimindex a DIV 8 * L < dimword a)%N).
    { eapply N.le_lt_trans; [|exact Hlen]. apply N.mul_le_mono_l. unfold L. rewrite Hst, !LENGTH_length, !app_length. lia. }
    assert (HLw : (L < dimword a)%N).
    { assert (Hk : (1 <= dimindex a DIV 8)%N) by (destruct Hg as [E|E]; rewrite E; cbn; lia). nia. }
    set (s4 := set_regs (regs s |+ (5, x) |+ (7, Word (w >>> 1)%w)) s).
    destruct (word_gc_move_code_thm conf x i pa curr (memory s) (mdomain s) x1 i1' pa1' m1' s4)
      as (ck1 & q0 & q1 & q2 & q6 & Ev).
    { subst s4; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
      splits; try assumption; try reflexivity; try lia;
        unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
    set (s5 := set_regs ((regs s4 |++ [(0, q0); (1, q1); (2, q2); (3, Word pa1'); (4, Word i1'); (5, x1); (6, q6)])
                         |+ (8, Word (bytes_in_word * n2w (LENGTH (old ++ [x1])))%w))
                 (set_memory m1' (set_stack (init ++ (old ++ [x1]) ++ xs) s))).
    destruct (IH (w >>> 1)%w xs s5 i1' pa1' curr m1' (mdomain s) new' st' i' pa' m' (old ++ [x1]) init conf
                ltac:(lia)) as (ck2 & p0 & p1 & p2 & p5 & p6 & p7 & Er).
    { subst s5 s4; unfold get_var; nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
      splits; try assumption; try reflexivity; try lia;
        try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence).
      rewrite Hst in Hlen. replace (LENGTH (init ++ (old ++ [x1]) ++ xs)) with (LENGTH (init ++ old ++ x :: xs)); [exact Hlen|]. rewrite !LENGTH_length, !app_length; cbn [length]; lia. }
    pose proof (evaluate_add_clock (ck2 + 1) (word_gc_move_code conf) (set_clock (clock s4 + ck1) s4)) as Ev'.
    assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
    specialize (Ev' NONE _ (conj Ev NT)). subst s4. autorewrite with nf in Ev'.
    cbn [clock regs memory set_regs set_clock set_memory] in Ev'. autorewrite with nf in Ev'. cbn [FUPDATE_LIST FOLDL] in Ev'.
    exists (ck1 + ck2 + 1), p0, p1, p2, p5, p6, p7.
    unfold word_gc_move_bitmap_code. rewrite ev_while. sx_simp.
    rewrite (lo2_false w Hg Hw0 Hw1). cbn [negb]. sx_all. rewrite (bd_F Ha).
    cbn [list_Seq]. sx_all2.
    unfold is_true in Hust. rewrite Hust. cbn [negb].
    fold L. rewrite (bytes_in_word_word_shift_n2w L (conj Hg HL)), (w2n_n2w_small L HLw).
    replace (n2w L << word_shift a)%w with (bytes_in_word * n2w L : word a)%w
      by (rewrite Hsh; apply WORD_MULT_COMM).
    rewrite (proj2 (bool_decide_spec _) eq_refl), Hss, Hst.
    replace (LENGTH init + L <? LENGTH (init ++ old ++ x :: xs))%N with true
      by (symmetry; apply N.ltb_lt; unfold L; rewrite !LENGTH_length, !app_length; cbn [length]; lia).
    cbn [andb]. replace (x :: xs) with ([x] ++ xs) by reflexivity. unfold L. rewrite EL_LENGTH_ADD_LEMMA. cbn [app].
    sx_all2. rewrite word_sh_lsr by lia. sx_all2. rw_eval Ev'. sx_simp. sx_all2.
    rewrite Hust. cbn [negb].
    fold L. rewrite (bytes_in_word_word_shift_n2w L (conj Hg HL)), (w2n_n2w_small L HLw).
    replace (n2w L << word_shift a)%w with (bytes_in_word * n2w L : word a)%w
      by (rewrite Hsh; apply WORD_MULT_COMM).
    rewrite (proj2 (bool_decide_spec _) eq_refl), Hss, Hst.
    replace (LENGTH init + L <? LENGTH (init ++ old ++ x :: xs))%N with true
      by (symmetry; apply N.ltb_lt; unfold L; rewrite !LENGTH_length, !app_length; cbn [length]; lia).
    cbn [andb]. replace (x :: xs) with ([x] ++ xs) by reflexivity. unfold L.
    rewrite LUPDATE_LENGTH_ADD_LEMMA. cbn [app].
    sx_all2. rewrite bytes_n2w_succ.
    cbn [cont_loop]. replace (clock s + (ck2 + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    subst s5. unfold word_gc_move_bitmap_code in Er. cbn [list_Seq] in Er.
    autorewrite with nf in Er. cbn [clock regs memory stackSem.stack set_regs set_clock set_memory set_stack] in Er.
    autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er.
    rewrite <- !app_assoc in Er. cbn [app] in Er. rewrite !LENGTH_length, !app_length in Er |- *. cbn [length] in Er |- *.
    replace (N.of_nat (length old) + 1)%N with (N.of_nat (length old + 1)) by lia.
    sx_simp. rw_eval Er. st_fin. rewrite app_length; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_bitmap_code_thm" *)
Theorem word_gc_move_bitmap_code_thm : forall (w : word a) stack (s : state) i pa curr m dm new stack1
    i1 pa1 m1 old init conf,
  word_gc_move_bitmap conf (w, (stack, (i, (pa, (curr, (m, dm)))))) = SOME (new, (stack1, (i1, (pa1, (m1, true))))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ good_dimindex a /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word curr) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ use_stack s /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\
  get_var 7 s = SOME (Word w) /\ get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
  stackSem.stack s = init ++ old ++ stack /\ stack_space s = LENGTH init /\
  (dimindex a DIV 8 * LENGTH (stackSem.stack s) < dimword a)%N ->
  exists ck r0 r1 r2 r5 r6 r7,
    evaluate (word_gc_move_bitmap_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, r7); (8, Word (bytes_in_word * n2w (LENGTH (old ++ new))))])
             (set_memory m1 (set_stack (init ++ old ++ new ++ stack1) s))).
Proof.
  intros w stack s i pa curr m dm new stack1 i1 pa1 m1 old init conf H.
  exact (word_gc_move_bitmap_code_thm_n (w2n w + 1) w stack s i pa curr m dm new stack1 i1 pa1 m1 old init conf
           ltac:(lia) H).
Qed.


Lemma DROP_EL {A} `{Inhabited A} : forall (l : list A) k h t, DROP k l = h :: t -> EL k l = h.
Proof.
  induction l as [|x xs IH]; intros k h t Hd; [discriminate|].
  cbn [DROP] in Hd. destruct (N.eqb_spec k 0) as [->|Hk].
  - injection Hd as -> _. reflexivity.
  - replace k with (SUC (k - 1)) by lia. rewrite EL_SUC. cbn [TL]. exact (IH _ _ _ Hd).
Qed.

Lemma word_gc_move_bitmap_LENGTH conf (h : word a) stack i pa curr m dm hd ws i2 pa2 m2 c2 :
  word_gc_move_bitmap conf (h, (stack, (i, (pa, (curr, (m, dm)))))) = SOME (hd, (ws, (i2, (pa2, (m2, c2))))) ->
  LENGTH stack = (LENGTH hd + LENGTH ws)%N.
Proof.
  unfold word_gc_move_bitmap. destruct (filter_bitmap (get_bits h) stack) as [[ts ws']|] eqn:Ef; [|discriminate].
  destruct (word_gc_move_roots conf _) as (wl, (i3, (pa3, (m3, c3)))).
  destruct (map_bitmap (get_bits h) wl stack) as [[hd' v2]|] eqn:Em; [|discriminate].
  intros E; injection E as <- <- _ _ _ _.
  apply filter_bitmap_IMP_LENGTH in Ef. apply map_bitmap_IMP_LENGTH in Em. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_bitmaps_LENGTH" *)
Theorem word_gc_move_bitmaps_LENGTH : forall conf (w : word_loc a) stack bitmaps i pa curr m dm xs stack1 i1 pa1 m1,
  word_gc_move_bitmaps conf (w, (stack, (bitmaps, (i, (pa, (curr, (m, dm))))))) =
    SOME (xs, (stack1, (i1, (pa1, (m1, true))))) ->
  LENGTH stack = (LENGTH xs + LENGTH stack1)%N.
Proof.
  intros conf w stack bitmaps i pa curr m dm xs stack1 i1 pa1 m1. unfold word_gc_move_bitmaps.
  destruct (full_read_bitmap bitmaps w) as [bs|]; [|discriminate].
  destruct (filter_bitmap bs stack) as [[ts ws']|] eqn:Ef; [|discriminate].
  destruct (word_gc_move_roots conf _) as (wl, (i3, (pa3, (m3, c3)))).
  destruct (map_bitmap bs wl stack) as [[hd' [t1 t2]]|] eqn:Em; [|discriminate].
  intros E; injection E as <- <- _ _ _ _.
  apply filter_bitmap_IMP_LENGTH in Ef. apply map_bitmap_IMP_LENGTH in Em. lia.
Qed.


Local Theorem word_gc_move_bitmaps_code_thm_n : forall n (w : word a) bitmaps z stack (s : state) i pa curr m dm
    new stack1 i1 pa1 m1 old init conf,
  (LENGTH bitmaps - w2n (w - n2w 1) < n)%N ->
  word_gc_move_bitmaps conf (Word w, (stack, (bitmaps, (i, (pa, (curr, (m, dm))))))) =
    SOME (new, (stack1, (i1, (pa1, (m1, true))))) /\
  (LENGTH bitmaps < dimword a - 1)%N /\ good_dimindex a /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ good_dimindex a /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word curr) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ stackSem.bitmaps s = bitmaps /\ use_stack s /\
  get_var 0 s = SOME (Word z) /\ z <> n2w 0 /\
  1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\ 7 IN FDOM (regs s) /\
  get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
  get_var 9 s = SOME (Word (w - n2w 1)) /\
  stackSem.stack s = init ++ old ++ stack /\ stack_space s = LENGTH init /\
  (dimindex a DIV 8 * LENGTH (stackSem.stack s) < dimword a)%N ->
  exists ck r0 r1 r2 r5 r6 r7 r9,
    evaluate (word_gc_move_bitmaps_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, r7); (8, Word (bytes_in_word * n2w (LENGTH (old ++ new)))); (9, r9)])
             (set_memory m1 (set_stack (init ++ old ++ new ++ stack1) s))).
Proof.
  induction n as [|n IH] using N.peano_ind;
    intros w bitmaps z stack s i pa curr m dm new stack1 i1 pa1 m1 old init conf Hn; [lia|].
  intros (H & Hlb & Hg & Hsl & Hws & H2 & Hls & _ & Hsh & Hold & Hus & Hm & Hdm & Hbm & Hust & H0 & Hz & H1 & H2r
          & H3 & H4 & H5 & H6 & H7 & H8 & H9 & Hst & Hss & Hlen).
  unfold get_var in *; subst m dm bitmaps.
  fdom_val H1 1 v1 Ev1; fdom_val H2r 2 v2 Ev2; fdom_val H5 5 v5 Ev5; fdom_val H6 6 v6 Ev6; fdom_val H7 7 v7 Ev7.
  rewrite (word_gc_move_bitmaps_unroll conf w stack (stackSem.bitmaps s) i pa curr (memory s) (mdomain s) _
             (conj H (conj Hlb Hg))) in H.
  destruct (DROP (w2n (w - n2w 1)) (stackSem.bitmaps s)) as [|h t] eqn:Ed; [discriminate|].
  pose proof (DROP_EL _ _ _ _ Ed) as Eel. destruct (DROP_cons_succ _ _ _ _ Ed) as [Ed' Hlt].
  destruct (word_gc_move_bitmap conf (h, (stack, (i, (pa, (curr, (memory s, mdomain s)))))))
    as [[hd [ws [i2 [pa2 [m2 c2]]]]]|] eqn:Eb; [|discriminate].
  assert (c2 = true) as ->.
  { destruct (negb (word_msb h)); [injection H as _ _ _ _ _ E; exact E|].
    destruct (word_gc_move_bitmaps conf _) as [[hd3 [ws3 [i3 [pa3 [m3 c3]]]]]|]; [|discriminate].
    injection H as _ _ _ _ _ E. apply andb_prop in E; tauto. }
  pose proof (word_gc_move_bitmap_LENGTH _ _ _ _ _ _ _ _ _ _ _ _ _ _ Eb) as HlenB.
  set (s2 := set_regs (regs s |+ (7, Word h)) s).
  destruct (word_gc_move_bitmap_code_thm h stack s2 i pa curr (memory s) (mdomain s) hd ws i2 pa2 m2 old init conf)
    as (ck1 & q0 & q1 & q2 & q5 & q6 & q7 & Ev).
  { subst s2; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
    splits; try assumption; try reflexivity;
      unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
  assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
  assert (Hlb' : (LENGTH (stackSem.bitmaps s) <=? w2n (w - n2w 1))%N = false) by (apply N.leb_gt; lia).
  destruct (word_msb h) eqn:Hmsb; cbn [negb] in H.
  - destruct (word_gc_move_bitmaps conf (Word (w + n2w 1)%w, (ws, (stackSem.bitmaps s, (i2, (pa2, (curr, (m2, mdomain s))))))))
      as [[hd3 [ws3 [i3 [pa3 [m3 c3]]]]]|] eqn:Eb3; [|discriminate].
    injection H as <- <- <- <- <- Hc3. cbn [andb] in Hc3. subst c3.
    assert (Hnz : (h >>> (dimindex a - 1))%w <> n2w 0) by (apply word_msb_IFF_lsr_EQ_0; exact Hmsb).
    assert (Ew : w = n2w (w2n (w - n2w 1) + 1)) by (rewrite <- word_add_n2w, n2w_w2n; word_ring).
    assert (Hk1 : (w2n (w - n2w 1) + 1 < dimword a)%N) by lia.
    assert (Hm1 : w2n (w + n2w 1 - n2w 1) = (w2n (w - n2w 1) + 1)%N)
      by (replace (w + n2w 1 - n2w 1)%w with w by word_ring; rewrite Ew at 1; apply w2n_n2w_small; exact Hk1).
    set (s5 := set_regs ((regs s2 |++ [(0, q0); (1, q1); (2, q2); (3, Word pa2); (4, Word i2); (5, q5); (6, q6);
                                       (7, q7); (8, Word (bytes_in_word * n2w (LENGTH (old ++ hd)))%w)])
                         |+ (0, Word h) |+ (9, Word w) |+ (0, Word (h >>> (dimindex a - 1))%w))
                 (set_memory m2 (set_stack (init ++ (old ++ hd) ++ ws) s))).
    destruct (IH (w + n2w 1)%w (stackSem.bitmaps s) (h >>> (dimindex a - 1))%w ws s5 i2 pa2 curr m2 (mdomain s)
                hd3 ws3 i3 pa3 m3 (old ++ hd) init conf ltac:(rewrite Hm1; lia))
      as (ck2 & p0 & p1 & p2 & p5 & p6 & p7 & p9 & Er).
    { subst s5 s2; unfold get_var; nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
      splits; try assumption; try reflexivity; try lia;
        try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence).
      - do 2 f_equal. word_ring.
      - rewrite Hst in Hlen. replace (LENGTH (init ++ (old ++ hd) ++ ws)) with (LENGTH (init ++ old ++ stack)); [exact Hlen|].
        rewrite !LENGTH_length, !app_length. rewrite !LENGTH_length in HlenB. lia. }
    pose proof (evaluate_add_clock (ck2 + 1) (word_gc_move_bitmap_code conf) (set_clock (clock s2 + ck1) s2)) as Ev'.
    specialize (Ev' NONE _ (conj Ev NT)). subst s2. autorewrite with nf in Ev'.
    cbn [clock regs memory set_regs set_clock set_memory set_stack] in Ev'. autorewrite with nf in Ev'.
    cbn [FUPDATE_LIST FOLDL] in Ev'.
    exists (ck1 + ck2 + 1), p0, p1, p2, p5, p6, p7, p9.
    unfold word_gc_move_bitmaps_code. rewrite ev_while. sx_simp. rewrite WORD_AND_IDEM, (bd_F Hz). cbn [negb].
    cbn [list_Seq]. sx_all2. rewrite Hust, Hlb', Eel. cbn [negb orb]. sx_all2.
    rw_eval Ev'. sx_simp. sx_all2. rewrite Hust, Hlb', Eel. cbn [negb orb]. sx_all2.
    rewrite word_sh_lsr by lia. sx_all2. sx_simp.
    cbn [cont_loop]. replace (clock s + (ck2 + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    sx_simp.
    subst s5. unfold word_gc_move_bitmaps_code in Er. cbn [list_Seq] in Er.
    autorewrite with nf in Er. cbn [clock regs memory stackSem.stack set_regs set_clock set_memory set_stack] in Er.
    autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er. rewrite <- !app_assoc in Er.
    replace (w - n2w 1 + n2w 1)%w with w by word_ring.
    rw_eval Er. st_fin. rewrite <- !app_assoc; reflexivity.
  - injection H as <- <- <- <- <-.
    pose proof (evaluate_add_clock 1 (word_gc_move_bitmap_code conf) (set_clock (clock s2 + ck1) s2)) as Ev'.
    specialize (Ev' NONE _ (conj Ev NT)). subst s2. autorewrite with nf in Ev'.
    cbn [clock regs memory set_regs set_clock set_memory set_stack] in Ev'. autorewrite with nf in Ev'.
    cbn [FUPDATE_LIST FOLDL] in Ev'.
    assert (Hz0 : (h >>> (dimindex a - 1))%w = n2w 0).
    { destruct (decide ((h >>> (dimindex a - 1))%w = n2w 0)) as [E|E]; [exact E|].
      apply word_msb_IFF_lsr_EQ_0 in E. unfold is_true in E. congruence. }
    exists (ck1 + 1), (Word (h >>> (dimindex a - 1))%w), q1, q2, q5, q6, q7, (Word w).
    unfold word_gc_move_bitmaps_code. rewrite ev_while. sx_simp. rewrite WORD_AND_IDEM, (bd_F Hz). cbn [negb].
    cbn [list_Seq]. sx_all2. rewrite Hust, Hlb', Eel. cbn [negb orb]. sx_all2.
    rw_eval Ev'. sx_simp. sx_all2. rewrite Hust, Hlb', Eel. cbn [negb orb]. sx_all2.
    rewrite word_sh_lsr by lia. sx_all2. rewrite Hz0.
    sx_simp. rewrite ev_while. sx_simp. rewrite ?WORD_AND_IDEM. sx_simp.
    cbn [cont_loop]. replace (clock s + 1 =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    replace (w - n2w 1 + n2w 1)%w with w by word_ring. replace (clock s + 1 - 1)%N with (clock s) by lia.
    st_fin.
Qed.


(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_bitmaps_code_thm" *)
Theorem word_gc_move_bitmaps_code_thm : forall (w : word a) bitmaps z stack (s : state) i pa curr m dm
    new stack1 i1 pa1 m1 old init conf,
  word_gc_move_bitmaps conf (Word w, (stack, (bitmaps, (i, (pa, (curr, (m, dm))))))) =
    SOME (new, (stack1, (i1, (pa1, (m1, true))))) /\
  (LENGTH bitmaps < dimword a - 1)%N /\ good_dimindex a /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ good_dimindex a /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word curr) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ stackSem.bitmaps s = bitmaps /\ use_stack s /\
  get_var 0 s = SOME (Word z) /\ z <> n2w 0 /\
  1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\ 7 IN FDOM (regs s) /\
  get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
  get_var 9 s = SOME (Word (w - n2w 1)) /\
  stackSem.stack s = init ++ old ++ stack /\ stack_space s = LENGTH init /\
  (dimindex a DIV 8 * LENGTH (stackSem.stack s) < dimword a)%N ->
  exists ck r0 r1 r2 r5 r6 r7 r9,
    evaluate (word_gc_move_bitmaps_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, r7); (8, Word (bytes_in_word * n2w (LENGTH (old ++ new)))); (9, r9)])
             (set_memory m1 (set_stack (init ++ old ++ new ++ stack1) s))).
Proof.
  intros w bitmaps z stack s i pa curr m dm new stack1 i1 pa1 m1 old init conf H.
  exact (word_gc_move_bitmaps_code_thm_n (LENGTH bitmaps - w2n (w - n2w 1) + 1) w bitmaps z stack s i pa curr m dm
           new stack1 i1 pa1 m1 old init conf ltac:(lia) H).
Qed.

End BitmapThm.

Ltac list_eq := repeat rewrite <- app_assoc; cbn [app]; repeat rewrite <- app_assoc; cbn [app]; reflexivity.

Ltac rw_eval2 E :=
  lazymatch type of E with evaluate (?p, ?Y) = _ =>
    lazymatch goal with |- context [evaluate (p, ?X)] =>
      replace X with Y by (apply state_ext; nf_fields; try reflexivity; try lia; try regs_fin; list_eq);
      rewrite E end end.

Section RootsThm.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.
#[local] Instance word_loc_inhabited'' : Inhabited (word_loc a) := Word (n2w 0).

Local Theorem word_gc_move_roots_bitmaps_code_thm_n : forall n stack bitmaps (s : state) i pa curr m dm
    stack1 i1 pa1 m1 old init conf,
  (LENGTH stack < n)%N ->
  word_gc_move_roots_bitmaps conf (stack, (bitmaps, (i, (pa, (curr, (m, dm)))))) =
    (stack1, (i1, (pa1, (m1, true)))) /\
  (LENGTH bitmaps < dimword a - 1)%N /\ good_dimindex a /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ good_dimindex a /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word curr) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ stackSem.bitmaps s = bitmaps /\ use_stack s /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\ 7 IN FDOM (regs s) /\
  get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
  get_var 9 s = SOME (HD stack) /\
  stackSem.stack s = init ++ old ++ stack /\ stack_space s = LENGTH init /\
  (dimindex a DIV 8 * LENGTH (stackSem.stack s) < dimword a)%N ->
  exists ck r0 r1 r2 r5 r6 r7 r8,
    evaluate (word_gc_move_roots_bitmaps_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, r7); (8, r8); (9, Word (n2w 0))])
             (set_memory m1 (set_stack (init ++ old ++ stack1) s))).
Proof.
  induction n as [|n IH] using N.peano_ind;
    intros stack bitmaps s i pa curr m dm stack1 i1 pa1 m1 old init conf Hn; [lia|].
  intros (H & Hlb & Hg & Hsl & Hws & H2 & Hls & _ & Hsh & Hold & Hus & Hm & Hdm & Hbm & Hust & H0 & H1 & H2r
          & H3 & H4 & H5 & H6 & H7 & H8 & H9 & Hst & Hss & Hlen).
  unfold get_var in *; subst m dm bitmaps.
  fdom_val H0 0 v0 Ev0; fdom_val H1 1 v1 Ev1; fdom_val H2r 2 v2 Ev2; fdom_val H5 5 v5 Ev5; fdom_val H6 6 v6 Ev6;
    fdom_val H7 7 v7 Ev7.
  rewrite (word_gc_move_roots_bitmaps_unroll _ _ _ _ _ _ _ _ _ _ _ _ H) in H.
  destruct stack as [|hd stack]; [injection H as _ _ _ _ E; discriminate|].
  cbn [HD] in H9.
  destruct (decide (hd = Word (n2w 0))) as [->|Hhd].
  { injection H as <- <- <- <- Hc. apply bool_decide_spec in Hc. subst stack.
    exists 0, v0, v1, v2, v5, v6, v7, (Word (bytes_in_word * n2w (LENGTH old))%w). rewrite N.add_0_r.
    unfold word_gc_move_roots_bitmaps_code. rewrite ev_while. sx_simp. rewrite ?WORD_AND_IDEM. sx_simp.
    rewrite set_clock_same, <- Hst. st_fin. }
  destruct (word_gc_move_bitmaps conf (hd, (stack, (stackSem.bitmaps s, (i, (pa, (curr, (memory s, mdomain s))))))))
    as [[x0 [x1 [x2 [x3 [x4 c2]]]]]|] eqn:Eb; [|injection H as _ _ _ _ E; discriminate].
  destruct (word_gc_move_roots_bitmaps conf (x1, (stackSem.bitmaps s, (x2, (x3, (curr, (x4, mdomain s)))))))
    as (st', (i', (pa', (m', c3)))) eqn:Er3.
  injection H as <- <- <- <- Hc. apply andb_prop in Hc as [-> ->].
  destruct hd as [c|l1 l2]; [|unfold word_gc_move_bitmaps, full_read_bitmap in Eb; discriminate].
  assert (Hc0 : c <> n2w 0) by (intros ->; exact (Hhd eq_refl)).
  pose proof (word_gc_move_bitmaps_LENGTH _ _ _ _ _ _ _ _ _ _ _ _ _ _ Eb) as HlenB.
  destruct x1 as [|h t].
  { unfold word_gc_move_roots_bitmaps in Er3.
    rewrite (proj1 enc_stack_def) in Er3. injection Er3 as _ _ _ _ E; discriminate. }
  set (s2 := set_regs (regs s |+ (0, Word c) |+ (9, Word (c - n2w 1))
                              |+ (8, Word (bytes_in_word * n2w (LENGTH old + 1)))) s).
  destruct (word_gc_move_bitmaps_code_thm c (stackSem.bitmaps s) c stack s2 i pa curr (memory s) (mdomain s)
              x0 (h :: t) x2 x3 x4 (old ++ [Word c]) init conf) as (ck1 & q0 & q1 & q2 & q5 & q6 & q7 & q9 & Ev).
  { subst s2; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
    splits; try assumption; try reflexivity;
      try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence).
    - rewrite !LENGTH_length, app_length. cbn [length]. do 4 f_equal. lia.
    - rewrite Hst, <- !app_assoc. reflexivity. }
  set (L1 := (LENGTH old + 1 + LENGTH x0)%N).
  assert (EL1 : LENGTH ((old ++ [Word c]) ++ x0) = L1) by (unfold L1; rewrite !LENGTH_length, !app_length; cbn [length]; lia).
  rewrite EL1 in Ev.
  assert (Hst' : LENGTH (stackSem.stack s) = (LENGTH init + L1 + LENGTH (h :: t))%N).
  { rewrite Hst. unfold L1. rewrite !LENGTH_length, !app_length in *. cbn [length] in *. lia. }
  assert (HL1 : (dimindex a DIV 8 * L1 < dimword a)%N).
  { eapply N.le_lt_trans; [|exact Hlen]. apply N.mul_le_mono_l. rewrite Hst'. lia. }
  assert (HL1w : (L1 < dimword a)%N).
  { assert (Hk : (1 <= dimindex a DIV 8)%N) by (destruct Hg as [E|E]; rewrite E; cbn; lia). nia. }
  assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
  set (s8 := set_regs ((regs s2 |++ [(0, q0); (1, q1); (2, q2); (3, Word x3); (4, Word x2); (5, q5); (6, q6);
                                     (7, q7); (8, Word (bytes_in_word * n2w L1)%w); (9, q9)]) |+ (9, h))
               (set_memory x4 (set_stack (init ++ (old ++ Word c :: x0) ++ h :: t) s))).
  destruct (IH (h :: t) (stackSem.bitmaps s) s8 x2 x3 curr x4 (mdomain s) st' i' pa' m' (old ++ Word c :: x0) init conf)
    as (ck2 & p0 & p1 & p2 & p5 & p6 & p7 & p8 & Er).
  { rewrite !LENGTH_length in *. cbn [length] in *. lia. }
  { subst s8 s2; unfold get_var; nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb HD].
    splits; try assumption; try reflexivity; try lia;
      try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence).
    - do 4 f_equal. unfold L1. rewrite !LENGTH_length, !app_length. cbn [length]. lia.
    - rewrite Hst in Hlen. replace (LENGTH (init ++ (old ++ Word c :: x0) ++ h :: t)) with (LENGTH (init ++ old ++ Word c :: stack));
        [exact Hlen|]. rewrite !LENGTH_length, !app_length in *. cbn [length] in *. lia. }
  pose proof (evaluate_add_clock (ck2 + 1) (word_gc_move_bitmaps_code conf) (set_clock (clock s2 + ck1) s2)) as Ev'.
  specialize (Ev' NONE _ (conj Ev NT)). subst s2. autorewrite with nf in Ev'.
  cbn [clock regs memory set_regs set_clock set_memory set_stack] in Ev'. autorewrite with nf in Ev'.
  cbn [FUPDATE_LIST FOLDL] in Ev'.
  exists (ck1 + ck2 + 1), p0, p1, p2, p5, p6, p7, p8.
  unfold word_gc_move_roots_bitmaps_code. rewrite ev_while. sx_simp. rewrite WORD_AND_IDEM, (bd_F Hc0). cbn [negb].
  cbn [list_Seq]. sx_all2. rewrite bytes_n2w_succ. rw_eval Ev'. sx_simp. sx_all2.
  unfold is_true in Hust. rewrite Hust. cbn [negb].
  rewrite (bytes_in_word_word_shift_n2w L1 (conj Hg HL1)), (w2n_n2w_small L1 HL1w).
  replace (n2w L1 << word_shift a)%w with (bytes_in_word * n2w L1 : word a)%w by (rewrite Hsh; apply WORD_MULT_COMM).
  rewrite (proj2 (bool_decide_spec _) eq_refl), Hss.
  replace (init ++ (old ++ [Word c]) ++ x0 ++ h :: t) with ((init ++ (old ++ [Word c]) ++ x0) ++ h :: t)
    by (rewrite <- !app_assoc; reflexivity).
  assert (Hl2 : LENGTH (init ++ (old ++ [Word c]) ++ x0) = (LENGTH init + L1)%N)
    by (rewrite <- EL1, !LENGTH_length, !app_length; lia).
  replace (LENGTH init + L1 <? LENGTH ((init ++ (old ++ [Word c]) ++ x0) ++ h :: t))%N with true
    by (symmetry; apply N.ltb_lt; rewrite !LENGTH_length, !app_length in *; cbn [length] in *; lia).
  cbn [andb]. rewrite (EL_LENGTH_ADD_LEMMA_2 _ _ h t Hl2).
  sx_all2. sx_simp.
  cbn [cont_loop]. replace (clock s + (ck2 + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
  sx_simp.
  subst s8. unfold word_gc_move_roots_bitmaps_code in Er. cbn [list_Seq] in Er.
  autorewrite with nf in Er. cbn [clock regs memory stackSem.stack set_regs set_clock set_memory set_stack] in Er.
  autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er. rewrite <- !app_assoc in Er |- *. cbn [app] in Er |- *.
  rw_eval2 Er. st_fin.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_roots_bitmaps_code_thm" *)
Theorem word_gc_move_roots_bitmaps_code_thm : forall stack bitmaps (s : state) i pa curr m dm
    stack1 i1 pa1 m1 old init conf,
  word_gc_move_roots_bitmaps conf (stack, (bitmaps, (i, (pa, (curr, (m, dm)))))) =
    (stack1, (i1, (pa1, (m1, true)))) /\
  (LENGTH bitmaps < dimword a - 1)%N /\ good_dimindex a /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ good_dimindex a /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word curr) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ stackSem.bitmaps s = bitmaps /\ use_stack s /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\ 7 IN FDOM (regs s) /\
  get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
  get_var 9 s = SOME (HD stack) /\
  stackSem.stack s = init ++ old ++ stack /\ stack_space s = LENGTH init /\
  (dimindex a DIV 8 * LENGTH (stackSem.stack s) < dimword a)%N ->
  exists ck r0 r1 r2 r5 r6 r7 r8,
    evaluate (word_gc_move_roots_bitmaps_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, r7); (8, r8); (9, Word (n2w 0))])
             (set_memory m1 (set_stack (init ++ old ++ stack1) s))).
Proof.
  intros stack bitmaps s i pa curr m dm stack1 i1 pa1 m1 old init conf H.
  exact (word_gc_move_roots_bitmaps_code_thm_n (LENGTH stack + 1) stack bitmaps s i pa curr m dm
           stack1 i1 pa1 m1 old init conf ltac:(lia) H).
Qed.

End RootsThm.

(** ** The simple copying collector: [alloc] *)

Section AllocSimple.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.

Lemma store_word_of (st : fmap store_name (word_loc a)) k w0 :
  k <> AllocSize -> k IN FDOM (st |+ (AllocSize, w0)) -> wordSem.isWord (FAPPLY (st |+ (AllocSize, w0)) k) ->
  exists v, FLOOKUP st k = SOME (Word v) /\ FAPPLY (st |+ (AllocSize, w0)) k = Word v.
Proof.
  intros Hk Hin Hw. unfold FDOM, pred_set.IN in Hin. unfold FAPPLY in *.
  rewrite sx_store_upd in Hin, Hw |- *. destruct (decide (AllocSize = k)) as [E|_]; [congruence|].
  destruct (FLOOKUP st k) as [[v|l1 l2]|]; [|discriminate|contradiction]. exists v; split; reflexivity.
Qed.

Lemma zero_lsr k : (n2w 0 >>> k : word a)%w = n2w 0.
Proof. apply word_eq_w2n. rewrite w2n_lsr, w2n_n2w, N.mod_0_l by (pose proof (ZERO_LT_dimword a); lia). apply N.div_0_l. apply N.pow_nonzero; lia. Qed.

Lemma zero_lsl k : (n2w 0 << k : word a)%w = n2w 0.
Proof. rewrite WORD_MUL_LSL. word_ring. Qed.

Lemma EL_DROP_HD {A} `{Inhabited A} (l : list A) k h t : DROP k l = h :: t -> EL k l = h.
Proof. apply DROP_EL. Qed.

Ltac store_fin :=
  apply fmap_ext; let k := fresh "k" in intros k; rewrite ?FLOOKUP_UPD_store;
  repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)); try subst end;
  try congruence; try reflexivity.

Lemma word_gc_move_Word conf (v : word a) x g i1 pa1 m1 c1 :
  word_gc_move conf (Word v, x) = (g, (i1, (pa1, (m1, c1)))) -> exists u, g = Word u.
Proof.
  destruct x as (i, (pa, (old, (m, dm)))). cbn [word_gc_move]. destruct (decide _).
  - intros E; injection E as <- _ _ _ _; eexists; reflexivity.
  - cbv zeta. destruct (wordSem.is_fwd_ptr _).
    + intros E; injection E as <- _ _ _ _; eexists; reflexivity.
    + destruct (memcpy _ _ _ _ _) as (?, (?, ?)). intros E; injection E as <- _ _ _ _; eexists; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "alloc_correct_lemma_Simple" *)
Theorem alloc_correct_lemma_Simple : forall (w : word a) (s : state) r t conf l ret c anything,
  alloc w s = (r, t) /\ r <> SOME Error /\ gc_fun s = word_gc_fun conf /\ gc_kind conf = Simple /\
  LENGTH (bitmaps s) < dimword a - 1 /\ LENGTH (stack s) * (dimindex a DIV 8) < dimword a /\
  FLOOKUP l 0 = SOME ret /\ FLOOKUP l 1 = SOME (Word w) ->
  exists ck l2,
    evaluate (word_gc_code conf,
              set_code (fromAList (compile c (toAList (code s))))
                (set_gc_fun anything (set_regs l (set_clock (clock s + ck)
                  (set_use_alloc false (set_use_stack true (set_use_store true s))))))) =
    (r, set_gc_fun anything (set_regs l2 (set_code (fromAList (compile c (toAList (code s))))
          (set_use_alloc false (set_use_stack true (set_use_store true t)))))) /\
    (r <> NONE -> r = SOME (Halt (Word (n2w 1)))) /\ regs t ⊑ l2 /\ (r = NONE -> FLOOKUP l2 0 = SOME ret).
Proof.
  intros w s r t conf l ret c anything (H & Hr & Hgc & Hk & Hbm & Hst & Hl0 & Hl1).
  unfold alloc, gc, set_store in H. stk_fields. rewrite Hgc in H.
  destruct (LENGTH (stack s) <? stack_space s) eqn:Ess; [injection H as <- _; exfalso; apply Hr; reflexivity|].
  destruct (enc_stack _ _) as [wl|] eqn:Ee; [|injection H as <- _; exfalso; apply Hr; reflexivity].
  unfold word_gc_fun in H. rewrite Hk in H. cbv zeta in H.
  destruct (⌜word_gc_fun_assum conf _⌝) eqn:Ea; [|cbn [andb] in H;
    destruct (word_full_gc _ _) as (?, (?, (?, (?, ?)))); injection H as <- _; exfalso; apply Hr; reflexivity].
  apply bool_decide_spec in Ea.
  destruct Ea as (Hsub & Hoth & Hcur & Htrig & Hlen & Hgs & Heoh & Hglob & Hg & Hls & Hls2 & Hsl).
  assert (Hin : forall k, k IN (Globals INSERT CurrHeap INSERT OtherHeap INSERT HeapLength INSERT
                   TriggerGC INSERT GenStart INSERT EndOfHeap INSERT {}) -> k IN FDOM (store s |+ (AllocSize, Word w)))
    by exact Hsub.
  destruct (store_word_of (store s) OtherHeap (Word w) ltac:(discriminate)
              ltac:(apply Hin; rewrite !IN_INSERT; tauto) Hoth) as (new & Enew & Fnew).
  destruct (store_word_of (store s) CurrHeap (Word w) ltac:(discriminate)
              ltac:(apply Hin; rewrite !IN_INSERT; tauto) Hcur) as (old & Eold & Fold).
  destruct (store_word_of (store s) HeapLength (Word w) ltac:(discriminate)
              ltac:(apply Hin; rewrite !IN_INSERT; tauto) Hlen) as (len & Elen & Flen).
  destruct (store_word_of (store s) Globals (Word w) ltac:(discriminate)
              ltac:(apply Hin; rewrite !IN_INSERT; tauto) Hglob) as (gw & Eglob & Fglob).
  rewrite Fnew, Fold, Flen, Fglob in H. cbn [wordSem.theWord] in H.
  unfold word_full_gc in H. rewrite (proj2 (word_gc_move_roots_def _ _ _ _ _ _ _ _)) in H.
  destruct (word_gc_move conf (Word gw, (n2w 0, (new, (old, (memory s, mdomain s))))))
    as (g1, (i1, (pa1, (m1, cg)))) eqn:Eg.
  destruct (word_gc_move_roots conf (wl, (i1, (pa1, (old, (m1, mdomain s))))))
    as (ws2, (i2, (pa2, (m2, cw)))) eqn:Ewl.
  destruct (word_gc_move_loop (dimword a) conf (new, (i2, (pa2, (old, (m2, (mdomain s, andb cg cw)))))))
    as (i3, (pa3, (m3, c3))) eqn:El.
  cbn [andb HD TL] in H.
  destruct c3; [|injection H as <- _; exfalso; apply Hr; reflexivity].
  pose proof (word_gc_move_loop_ok _ _ _ _ _ _ _ _ _ _ _ _ _ El eq_refl) as Hc12.
  unfold is_true in Hc12. apply andb_prop in Hc12 as [-> ->].
  destruct (dec_stack _ ws2 _) as [stack1|] eqn:Ed; [|injection H as <- _; exfalso; apply Hr; reflexivity].
  destruct (DROP (stack_space s) (stack s)) as [|h0 t0] eqn:Edrop; [rewrite (proj1 enc_stack_def) in Ee; discriminate|].
  destruct (DROP_cons_succ _ _ _ _ Edrop) as [_ Hsp].
  pose proof (DROP_EL _ _ _ _ Edrop) as Eh0.
  stk_fields. cbn [FUPDATE_LIST FOLDL] in H. rewrite !sx_store_upd in H. sx_dec. unfold has_space in H.
  rewrite !sx_store_upd in H. sx_dec.
  destruct (word_gc_move_Word _ _ _ _ _ _ _ _ Eg) as [g1w ->].
  assert (Hws : (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N)
    by (unfold word_shift; destruct Hg as [E|E]; rewrite E; cbn; lia).
  destruct Hws as [Hws H2].
  assert (Hsh : forall v : word a, (v << word_shift a = v * bytes_in_word)%w).
  { intros v. rewrite (bytes_in_word_shift Hg). rewrite WORD_MUL_LSL. apply WORD_MULT_COMM. }
  set (B := set_code (fromAList (compile c (toAList (code s))))
              (set_gc_fun anything (set_use_alloc false (set_use_stack true (set_use_store true s))))).
  set (R3 := l |+ (1, Word (n2w 0)) |+ (2, Word (n2w 0)) |+ (3, Word new)
               |+ (4, Word (n2w 0)) |+ (5, Word gw) |+ (6, Word (n2w 0)) |+ (8, Word (n2w 0))).
  set (S3 := set_regs R3 (set_store_fld (store s |+ (AllocSize, Word w) |+ (NextFree, ret)) B)).
  destruct (word_gc_move_code_thm conf (Word gw) (n2w 0) new old (memory s) (mdomain s) (Word g1w) i1 pa1 m1 S3)
    as (ck1 & q0 & q1 & q2 & q6 & Ev1).
  { subst S3 B R3. unfold get_var. nf_fields. rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]. sx_dec.
    splits; try assumption; try reflexivity;
      unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
  assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
  set (init := TAKE (stack_space s) (stack s)).
  assert (Hsplit : stack s = init ++ h0 :: t0)
    by (rewrite <- Edrop; unfold init; rewrite TAKE_firstn, DROP_skipn, firstn_skipn; reflexivity).
  assert (Hinit : stack_space s = LENGTH init).
  { unfold init. rewrite TAKE_firstn, LENGTH_length, firstn_length. rewrite LENGTH_length in Hsp. lia. }
  set (ST4 := store s |+ (AllocSize, Word w) |+ (NextFree, ret) |+ (Globals, Word g1w)
                |+ (GlobReal, Word ((g1w >>> shift_length conf << word_shift a) + new)%w)).
  set (R4 := (R3 |++ [(0, q0); (1, q1); (2, q2); (3, Word pa1); (4, Word i1); (5, Word g1w); (6, q6)])
               |+ (7, Word (n2w 0)) |+ (9, h0) |+ (8, Word (n2w 0))).
  set (S4 := set_regs R4 (set_memory m1 (set_store_fld ST4 B))).
  destruct (word_gc_move_roots_bitmaps_code_thm (h0 :: t0) (bitmaps s) S4 i1 pa1 old m1 (mdomain s)
              stack1 i2 pa2 m2 [] init conf) as (ck2 & u0 & u1 & u2 & u5 & u6 & u7 & u8 & Ev2).
  { subst S4 R4 R3 ST4 B. unfold get_var. nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD, ?sx_store_upd.
    cbn [N.eqb Pos.eqb HD]. sx_dec.
    splits; try assumption; try reflexivity;
      try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence).
    all: try (unfold word_gc_move_roots_bitmaps; rewrite Ee, Ewl, Ed; reflexivity).
    all: try (cbn [LENGTH]; do 2 f_equal; word_ring).
    all: try (rewrite Hsplit; reflexivity).
    all: rewrite N.mul_comm; exact Hst. }
  set (R5 := (regs S4 |++ [(0, u0); (1, u1); (2, u2); (3, Word pa2); (4, Word i2); (5, u5); (6, u6); (7, u7);
                          (8, u8); (9, Word (n2w 0))]) |+ (8, Word new)).
  set (S5 := set_regs R5 (set_memory m2 (set_stack (init ++ [] ++ stack1) (set_store_fld ST4 B)))).
  cbn [andb] in El.
  destruct (word_gc_move_loop_code_thm (dimword a) conf new i2 pa2 old m2 (mdomain s) true i3 pa3 m3 S5)
    as (ck3 & p0 & p1 & p2 & p5 & p6 & p7 & Ev3).
  { subst S5 R5 S4 R4 R3 ST4 B. unfold get_var. nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD, ?sx_store_upd.
    cbn [N.eqb Pos.eqb]. sx_dec.
    splits; try assumption; try reflexivity;
      try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence). }
  { subst S5 R5 S4 R4 R3 ST4 B. unfold pred_set.IN, FDOM. nf_fields. cbn [FUPDATE_LIST FOLDL].
    rewrite ?FLOOKUP_UPD. cbn [N.eqb Pos.eqb]. congruence. }
  { subst S5 R5 S4 R4 R3 ST4 B. unfold pred_set.IN, FDOM. nf_fields. cbn [FUPDATE_LIST FOLDL].
    rewrite ?FLOOKUP_UPD. cbn [N.eqb Pos.eqb]. congruence. }
  { subst S5 R5 S4 R4 R3 ST4 B. unfold get_var. nf_fields. cbn [FUPDATE_LIST FOLDL].
    rewrite ?FLOOKUP_UPD. cbn [N.eqb Pos.eqb]. split; reflexivity. }
  pose proof (evaluate_add_clock (ck2 + ck3) (word_gc_move_code conf) (set_clock (clock S3 + ck1) S3)) as Ev1'.
  specialize (Ev1' NONE _ (conj Ev1 NT)). clear Ev1.
  pose proof (evaluate_add_clock ck3 (word_gc_move_roots_bitmaps_code conf) (set_clock (clock S4 + ck2) S4)) as Ev2'.
  specialize (Ev2' NONE _ (conj Ev2 NT)). clear Ev2.
  set (R6 := R5 |++ [(0, p0); (1, p1); (2, p2); (3, Word pa3); (4, Word i3); (5, p5); (6, p6); (7, p7); (8, Word pa3)]).
  set (L2 := if (w2n w <=? w2n (new + len - pa3))%N
             then R6 |+ (0, Word old) |+ (1, Word new) |+ (2, Word len) |+ (0, ret) |+ (1, Word w)
                     |+ (2, Word (len + new - pa3))%w
             else FEMPTY).
  exists (ck1 + ck2 + ck3), L2.
  subst L2 R6 S5 R5 S4 R4 S3 R3 ST4 B.
  autorewrite with nf in Ev1', Ev2'. cbn [clock regs memory stackSem.stack store set_regs set_clock set_memory set_stack set_store_fld set_code set_gc_fun set_use_alloc set_use_stack set_use_store] in Ev1', Ev2'.
  autorewrite with nf in Ev1', Ev2'. cbn [FUPDATE_LIST FOLDL app] in Ev1', Ev2'.
  unfold word_gc_code. rewrite Hk. cbn [list_Seq].
  set (MC := word_gc_move_code conf). set (RC := word_gc_move_roots_bitmaps_code conf).
  set (LC := word_gc_move_loop_code conf).
  sx_all2. subst MC. rw_eval Ev1'. sx_simp. sx_all2.
  rewrite word_sh_lsr by lia. sx_all2. rewrite word_sh_lsl by lia. sx_all2.
  rewrite zero_lsr, zero_lsl, w2n_n2w, N.mod_0_l, N.add_0_r by (pose proof (ZERO_LT_dimword a); lia).
  rewrite (proj2 (bool_decide_spec _) eq_refl), (proj2 (N.ltb_lt _ _) Hsp), Eh0. cbn [andb]. sx_all2.
  subst RC. rw_eval Ev2'. sx_simp. sx_all2. subst LC. rw_eval Ev3. cbn [FUPDATE_LIST FOLDL]. sx_simp. sx_all2.
  replace (len + new)%w with (new + len)%w by apply WORD_ADD_COMM.
  rewrite word_lo_w2n. cbn [glob_real] in H.
  replace (new + (g1w >>> shift_length conf << word_shift a))%w
    with ((g1w >>> shift_length conf << word_shift a) + new)%w in H by apply WORD_ADD_COMM.
  destruct (N.leb_spec (w2n w) (w2n (new + len - pa3))) as [Hle|Hgt]; injection H as <- <-.
  - rewrite (proj2 (N.ltb_ge _ _) Hle). sx_simp.
    splits.
    + f_equal. apply state_ext; nf_fields; try reflexivity; try solve [regs_fin]; try solve [store_fin].
    + intros E; exfalso; apply E; reflexivity.
    + intros k0 v0 Hk0; discriminate Hk0.
    + intros _. rewrite ?FLOOKUP_UPD. reflexivity.
  - rewrite (proj2 (N.ltb_lt _ _) Hgt). sx_simp. rewrite ?ev_halt. sx_simp.
    splits.
    + f_equal. unfold empty_env. apply state_ext; nf_fields; try reflexivity; try solve [regs_fin]; try solve [store_fin].
    + intros _; reflexivity.
    + intros k0 v0 Hk0; discriminate Hk0.
    + intros E; discriminate E.
Qed.

End AllocSimple.

(** ** The generational collector: definitions and unrolling *)

Section GenDefs.
Context {a : N}.
Local Abbreviation mem := (word a -> word_loc a).
Local Abbreviation dom := (word a -> Prop).
Local Open Scope word_scope.
#[local] Instance word_inhabited_g : Inhabited (word a) := n2w 0.
#[local] Instance word_loc_inhabited_g : Inhabited (word_loc a) := Word (n2w 0).

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_move_roots_bitmaps_def" *)
Definition word_gen_gc_move_roots_bitmaps (conf : config)
    (x : list (word_loc a) * (list (word a) * (word a * (word a * (word a * (word a * (word a * (mem * dom))))))))
    : list (word_loc a) * (word a * (word a * (word a * (word a * (mem * bool))))) :=
  let '(stack, (bitmaps, (i1, (pa1, (ib1, (pb1, (curr, (m, dm)))))))) := x in
  match enc_stack bitmaps stack with
  | NONE => (ARB, (ARB, (ARB, (ARB, (ARB, (ARB, false))))))
  | SOME wl_list =>
      let '(wl, (i2, (pa2, (ib2, (pb2, (m2, c2)))))) :=
        word_gen_gc_move_roots conf (wl_list, (i1, (pa1, (ib1, (pb1, (curr, (m, dm))))))) in
      match dec_stack bitmaps wl stack with
      | NONE => (ARB, (ARB, (ARB, (ARB, (ARB, (ARB, false))))))
      | SOME stack => (stack, (i2, (pa2, (ib2, (pb2, (m2, c2))))))
      end
  end.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_partial_move_roots_bitmaps_def" *)
Definition word_gen_gc_partial_move_roots_bitmaps (conf : config)
    (x : list (word_loc a) * (list (word a) * (word a * (word a * (word a * (mem * (dom * (word a * word a))))))))
    : list (word_loc a) * (word a * (word a * (mem * bool))) :=
  let '(stack, (bitmaps, (i1, (pa1, (curr, (m, (dm, (gs, rs)))))))) := x in
  match enc_stack bitmaps stack with
  | NONE => (ARB, (ARB, (ARB, (ARB, false))))
  | SOME wl_list =>
      let '(wl, (i2, (pa2, (m2, c2)))) :=
        word_gen_gc_partial_move_roots conf (wl_list, (i1, (pa1, (curr, (m, (dm, (gs, rs))))))) in
      match dec_stack bitmaps wl stack with
      | NONE => (ARB, (ARB, (ARB, (ARB, false))))
      | SOME stack => (stack, (i2, (pa2, (m2, c2))))
      end
  end.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_move_bitmaps_def" *)
Definition word_gen_gc_move_bitmaps (conf : config)
    (x : word_loc a * (list (word_loc a) * (list (word a) * (word a * (word a * (word a * (word a * (word a * (mem * dom)))))))))
    : option (list (word_loc a) * (list (word_loc a) * (word a * (word a * (word a * (word a * (mem * bool))))))) :=
  let '(w, (stack, (bitmaps, (i1, (pa1, (ib1, (pb1, (curr, (m, dm))))))))) := x in
  match full_read_bitmap bitmaps w with
  | NONE => NONE
  | SOME bs =>
      match filter_bitmap bs stack with
      | NONE => NONE
      | SOME (ts, ws) =>
          let '(wl, (i2, (pa2, (ib2, (pb2, (m2, c2)))))) :=
            word_gen_gc_move_roots conf (ts, (i1, (pa1, (ib1, (pb1, (curr, (m, dm))))))) in
          match map_bitmap bs wl stack with
          | NONE => NONE
          | SOME (hd, (ts1, ws')) => SOME (hd, (ws, (i2, (pa2, (ib2, (pb2, (m2, c2)))))))
          end
      end
  end.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_partial_move_bitmaps_def" *)
Definition word_gen_gc_partial_move_bitmaps (conf : config)
    (x : word_loc a * (list (word_loc a) * (list (word a) * (word a * (word a * (word a * (mem * (dom * (word a * word a)))))))))
    : option (list (word_loc a) * (list (word_loc a) * (word a * (word a * (mem * bool))))) :=
  let '(w, (stack, (bitmaps, (i1, (pa1, (curr, (m, (dm, (gs, rs))))))))) := x in
  match full_read_bitmap bitmaps w with
  | NONE => NONE
  | SOME bs =>
      match filter_bitmap bs stack with
      | NONE => NONE
      | SOME (ts, ws) =>
          let '(wl, (i2, (pa2, (m2, c2)))) :=
            word_gen_gc_partial_move_roots conf (ts, (i1, (pa1, (curr, (m, (dm, (gs, rs))))))) in
          match map_bitmap bs wl stack with
          | NONE => NONE
          | SOME (hd, (ts1, ws')) => SOME (hd, (ws, (i2, (pa2, (m2, c2)))))
          end
      end
  end.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_move_roots_APPEND" *)
Local Theorem word_gen_gc_move_roots_APPEND : forall conf curr dm xs ys (i1 pa1 ib1 pb1 : word a) (m : mem),
  word_gen_gc_move_roots conf (xs ++ ys, (i1, (pa1, (ib1, (pb1, (curr, (m, dm))))))) =
  let '(ws1, (i1, (pa1, (ib1, (pb1, (m1, c1)))))) :=
    word_gen_gc_move_roots conf (xs, (i1, (pa1, (ib1, (pb1, (curr, (m, dm))))))) in
  let '(ws2, (i2, (pa2, (ib2, (pb2, (m2, c2)))))) :=
    word_gen_gc_move_roots conf (ys, (i1, (pa1, (ib1, (pb1, (curr, (m1, dm))))))) in
  (ws1 ++ ws2, (i2, (pa2, (ib2, (pb2, (m2, andb c1 c2)))))).
Proof.
  intros conf curr dm xs; induction xs as [|x xs IH]; intros ys i1 pa1 ib1 pb1 m.
  - cbn [app]. rewrite (proj1 (word_gen_gc_move_roots_def conf i1 pa1 ib1 pb1 curr m dm (Word (n2w 0)) [])).
    destruct (word_gen_gc_move_roots conf (ys, _)) as (ws2, (i2, (pa2, (ib2, (pb2, (m2, c2)))))). reflexivity.
  - cbn [app]. rewrite !(proj2 (word_gen_gc_move_roots_def _ _ _ _ _ _ _ _ _ _)).
    destruct (word_gen_gc_move conf _) as (w1, (i1', (pa1', (ib1', (pb1', (m1', c1')))))).
    rewrite IH.
    destruct (word_gen_gc_move_roots conf (xs, _)) as (ws1, (i2, (pa2, (ib2, (pb2, (m2, c2)))))).
    destruct (word_gen_gc_move_roots conf (ys, _)) as (ws3, (i3, (pa3, (ib3, (pb3, (m3, c3)))))).
    cbn [app]. rewrite Bool.andb_assoc. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_partial_move_roots_APPEND" *)
Local Theorem word_gen_gc_partial_move_roots_APPEND : forall conf curr dm gs rs xs ys (i1 pa1 : word a) (m : mem),
  word_gen_gc_partial_move_roots conf (xs ++ ys, (i1, (pa1, (curr, (m, (dm, (gs, rs))))))) =
  let '(ws1, (i1, (pa1, (m1, c1)))) :=
    word_gen_gc_partial_move_roots conf (xs, (i1, (pa1, (curr, (m, (dm, (gs, rs))))))) in
  let '(ws2, (i2, (pa2, (m2, c2)))) :=
    word_gen_gc_partial_move_roots conf (ys, (i1, (pa1, (curr, (m1, (dm, (gs, rs))))))) in
  (ws1 ++ ws2, (i2, (pa2, (m2, andb c1 c2)))).
Proof.
  intros conf curr dm gs rs xs; induction xs as [|x xs IH]; intros ys i1 pa1 m.
  - cbn [app]. rewrite (proj1 (word_gen_gc_partial_move_roots_def conf i1 pa1 curr m dm gs rs (Word (n2w 0)) [])).
    destruct (word_gen_gc_partial_move_roots conf (ys, _)) as (ws2, (i2, (pa2, (m2, c2)))). reflexivity.
  - cbn [app]. rewrite !(proj2 (word_gen_gc_partial_move_roots_def _ _ _ _ _ _ _ _ _ _)).
    destruct (word_gen_gc_partial_move conf _) as (w1, (i1', (pa1', (m1', c1')))).
    rewrite IH.
    destruct (word_gen_gc_partial_move_roots conf (xs, _)) as (ws1, (i2, (pa2, (m2, c2)))).
    destruct (word_gen_gc_partial_move_roots conf (ys, _)) as (ws3, (i3, (pa3, (m3, c3)))).
    cbn [app]. rewrite Bool.andb_assoc. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_move_roots_IMP_LENGTH" *)
Theorem word_gen_gc_move_roots_IMP_LENGTH : forall xs (r0 r1 r3 r4 curr : word a) r2 dm ys i2 pa2 m2 c conf ib2 pb2,
  word_gen_gc_move_roots conf (xs, (r0, (r1, (r3, (r4, (curr, (r2, dm))))))) = (ys, (i2, (pa2, (ib2, (pb2, (m2, c)))))) ->
  LENGTH ys = LENGTH xs.
Proof.
  induction xs as [|x xs IH]; intros r0 r1 r3 r4 curr r2 dm ys i2 pa2 m2 c conf ib2 pb2 H.
  - rewrite (proj1 (word_gen_gc_move_roots_def conf r0 r1 r3 r4 curr r2 dm (Word (n2w 0)) [])) in H.
    injection H as <-; reflexivity.
  - rewrite (proj2 (word_gen_gc_move_roots_def _ _ _ _ _ _ _ _ _ _)) in H.
    destruct (word_gen_gc_move conf _) as (w1, (i1', (pa1', (ib1', (pb1', (m1', c1')))))).
    destruct (word_gen_gc_move_roots conf (xs, _)) as (ws1, (i3, (pa3, (ib3, (pb3, (m3, c3)))))) eqn:E.
    injection H as <- _ _ _ _ _ _. apply IH in E. rewrite !LENGTH_length in *. cbn [length]. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_partial_move_roots_IMP_LENGTH" *)
Theorem word_gen_gc_partial_move_roots_IMP_LENGTH : forall xs (r0 r1 r3 r4 curr : word a) r2 dm ys i2 pa2 m2 c conf,
  word_gen_gc_partial_move_roots conf (xs, (r0, (r1, (curr, (r2, (dm, (r3, r4))))))) = (ys, (i2, (pa2, (m2, c)))) ->
  LENGTH ys = LENGTH xs.
Proof.
  induction xs as [|x xs IH]; intros r0 r1 r3 r4 curr r2 dm ys i2 pa2 m2 c conf H.
  - rewrite (proj1 (word_gen_gc_partial_move_roots_def conf r0 r1 curr r2 dm r3 r4 (Word (n2w 0)) [])) in H.
    injection H as <-; reflexivity.
  - rewrite (proj2 (word_gen_gc_partial_move_roots_def _ _ _ _ _ _ _ _ _ _)) in H.
    destruct (word_gen_gc_partial_move conf _) as (w1, (i1', (pa1', (m1', c1')))).
    destruct (word_gen_gc_partial_move_roots conf (xs, _)) as (ws1, (i3, (pa3, (m3, c3)))) eqn:E.
    injection H as <- _ _ _ _. apply IH in E. rewrite !LENGTH_length in *. cbn [length]. lia.
Qed.


(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_move_roots_bitmaps" 2091 *)
Local Theorem word_gen_gc_move_roots_bitmaps_unroll : forall conf bitmaps (ib1 pb1 curr : word a) dm stack
    (i1 pa1 : word a) (m : mem) stack2 i2 pa2 ib2 pb2 m2,
  word_gen_gc_move_roots_bitmaps conf (stack, (bitmaps, (i1, (pa1, (ib1, (pb1, (curr, (m, dm)))))))) =
    (stack2, (i2, (pa2, (ib2, (pb2, (m2, true)))))) ->
  word_gen_gc_move_roots_bitmaps conf (stack, (bitmaps, (i1, (pa1, (ib1, (pb1, (curr, (m, dm)))))))) =
  match stack with
  | [] => (ARB, (ARB, (ARB, (ARB, (ARB, (ARB, false))))))
  | w :: ws =>
      if decide (w = Word (n2w 0)) then (stack, (i1, (pa1, (ib1, (pb1, (m, ⌜ws = []⌝)))))) else
      match word_gen_gc_move_bitmaps conf (w, (ws, (bitmaps, (i1, (pa1, (ib1, (pb1, (curr, (m, dm))))))))) with
      | NONE => (ARB, (ARB, (ARB, (ARB, (ARB, (ARB, false))))))
      | SOME (new, (stack, (i2, (pa2, (ib2, (pb2, (m2, c2))))))) =>
          let '(stack, (i, (pa, (ib1, (pb1, (m, c3)))))) :=
            word_gen_gc_move_roots_bitmaps conf (stack, (bitmaps, (i2, (pa2, (ib2, (pb2, (curr, (m2, dm)))))))) in
          (w :: new ++ stack, (i, (pa, (ib1, (pb1, (m, andb c2 c3))))))
      end
  end.
Proof.
  intros conf bitmaps ib1 pb1 curr dm [|w ws] i1 pa1 m stack2 i2 pa2 ib2 pb2 m2 H; [reflexivity|].
  revert H. unfold word_gen_gc_move_roots_bitmaps at 1 2. rewrite (proj2 enc_stack_def).
  destruct (decide (w = Word (n2w 0))) as [->|Hw].
  - rewrite (proj2 (bool_decide_spec _) eq_refl).
    destruct (decide (ws = [])) as [->|Hws].
    + rewrite (proj2 (bool_decide_spec _) eq_refl).
      rewrite (proj1 (word_gen_gc_move_roots_def conf i1 pa1 ib1 pb1 curr m dm (Word (n2w 0)) [])).
      rewrite (proj2 dec_stack_def), (proj2 (bool_decide_spec _) eq_refl). cbn. reflexivity.
    + rewrite (bd_F Hws). discriminate.
  - rewrite (bd_F (fun E => Hw E)). unfold word_gen_gc_move_bitmaps.
    destruct (full_read_bitmap bitmaps w) as [bs|] eqn:Ebs; [|reflexivity].
    destruct (filter_bitmap bs ws) as [[ts ws']|] eqn:Ef; [|reflexivity].
    destruct (enc_stack bitmaps ws') as [rest|] eqn:Ee.
    2:{ intros H. cbn beta iota zeta in H. injection H as _ _ _ _ _ _ E. discriminate. }
    rewrite word_gen_gc_move_roots_APPEND.
    destruct (word_gen_gc_move_roots conf (ts, _)) as (wl1, (i3, (pa3, (ib3, (pb3, (m3, c3)))))) eqn:Er1.
    destruct (word_gen_gc_move_roots conf (rest, _)) as (wl2, (i4, (pa4, (ib4, (pb4, (m4, c4)))))) eqn:Er2.
    rewrite (proj2 dec_stack_def), (bd_F (fun E => Hw E)), Ebs.
    assert (Hl : LENGTH wl1 = LENGTH ts) by (eapply word_gen_gc_move_roots_IMP_LENGTH; exact Er1).
    rewrite (map_bitmap_APPEND wl2 bs wl1 ws ts ws' (conj Ef Hl)).
    destruct (map_bitmap bs wl1 ws) as [[hd [ts0 ws0]]|] eqn:Em; [|reflexivity].
    destruct (filter_bitmap_map_bitmap bs ws wl1 ts ws' ts0 hd ws0 (conj Ef (conj Hl Em))) as [-> ->].
    cbn [app]. unfold word_gen_gc_move_roots_bitmaps. rewrite Ee, Er2.
    destruct (dec_stack bitmaps wl2 ws') as [st|].
    + intros _. reflexivity.
    + intros H. injection H as _ _ _ _ _ _ E. discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_partial_move_roots_bitmaps" 2144 *)
Local Theorem word_gen_gc_partial_move_roots_bitmaps_unroll : forall conf bitmaps (curr gs rs : word a) dm stack
    (i1 pa1 : word a) (m : mem) stack2 i2 pa2 m2,
  word_gen_gc_partial_move_roots_bitmaps conf (stack, (bitmaps, (i1, (pa1, (curr, (m, (dm, (gs, rs)))))))) =
    (stack2, (i2, (pa2, (m2, true)))) ->
  word_gen_gc_partial_move_roots_bitmaps conf (stack, (bitmaps, (i1, (pa1, (curr, (m, (dm, (gs, rs)))))))) =
  match stack with
  | [] => (ARB, (ARB, (ARB, (ARB, false))))
  | w :: ws =>
      if decide (w = Word (n2w 0)) then (stack, (i1, (pa1, (m, ⌜ws = []⌝)))) else
      match word_gen_gc_partial_move_bitmaps conf (w, (ws, (bitmaps, (i1, (pa1, (curr, (m, (dm, (gs, rs))))))))) with
      | NONE => (ARB, (ARB, (ARB, (ARB, false))))
      | SOME (new, (stack, (i2, (pa2, (m2, c2))))) =>
          let '(stack, (i, (pa, (m, c3)))) :=
            word_gen_gc_partial_move_roots_bitmaps conf (stack, (bitmaps, (i2, (pa2, (curr, (m2, (dm, (gs, rs)))))))) in
          (w :: new ++ stack, (i, (pa, (m, andb c2 c3))))
      end
  end.
Proof.
  intros conf bitmaps curr gs rs dm [|w ws] i1 pa1 m stack2 i2 pa2 m2 H; [reflexivity|].
  revert H. unfold word_gen_gc_partial_move_roots_bitmaps at 1 2. rewrite (proj2 enc_stack_def).
  destruct (decide (w = Word (n2w 0))) as [->|Hw].
  - rewrite (proj2 (bool_decide_spec _) eq_refl).
    destruct (decide (ws = [])) as [->|Hws].
    + rewrite (proj2 (bool_decide_spec _) eq_refl).
      rewrite (proj1 (word_gen_gc_partial_move_roots_def conf i1 pa1 curr m dm gs rs (Word (n2w 0)) [])).
      rewrite (proj2 dec_stack_def), (proj2 (bool_decide_spec _) eq_refl). cbn. reflexivity.
    + rewrite (bd_F Hws). discriminate.
  - rewrite (bd_F (fun E => Hw E)). unfold word_gen_gc_partial_move_bitmaps.
    destruct (full_read_bitmap bitmaps w) as [bs|] eqn:Ebs; [|reflexivity].
    destruct (filter_bitmap bs ws) as [[ts ws']|] eqn:Ef; [|reflexivity].
    destruct (enc_stack bitmaps ws') as [rest|] eqn:Ee.
    2:{ intros H. cbn beta iota zeta in H. injection H as _ _ _ _ E. discriminate. }
    rewrite word_gen_gc_partial_move_roots_APPEND.
    destruct (word_gen_gc_partial_move_roots conf (ts, _)) as (wl1, (i3, (pa3, (m3, c3)))) eqn:Er1.
    destruct (word_gen_gc_partial_move_roots conf (rest, _)) as (wl2, (i4, (pa4, (m4, c4)))) eqn:Er2.
    rewrite (proj2 dec_stack_def), (bd_F (fun E => Hw E)), Ebs.
    assert (Hl : LENGTH wl1 = LENGTH ts) by (eapply word_gen_gc_partial_move_roots_IMP_LENGTH; exact Er1).
    rewrite (map_bitmap_APPEND wl2 bs wl1 ws ts ws' (conj Ef Hl)).
    destruct (map_bitmap bs wl1 ws) as [[hd [ts0 ws0]]|] eqn:Em; [|reflexivity].
    destruct (filter_bitmap_map_bitmap bs ws wl1 ts ws' ts0 hd ws0 (conj Ef (conj Hl Em))) as [-> ->].
    cbn [app]. unfold word_gen_gc_partial_move_roots_bitmaps. rewrite Ee, Er2.
    destruct (dec_stack bitmaps wl2 ws') as [st|].
    + intros _. reflexivity.
    + intros H. injection H as _ _ _ _ E. discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_move_bitmap_def" *)
Definition word_gen_gc_move_bitmap (conf : config)
    (x : word a * (list (word_loc a) * (word a * (word a * (word a * (word a * (word a * (mem * dom))))))))
    : option (list (word_loc a) * (list (word_loc a) * (word a * (word a * (word a * (word a * (mem * bool))))))) :=
  let '(w, (stack, (i1, (pa1, (ib1, (pb1, (curr, (m, dm)))))))) := x in
  let bs := get_bits w in
  match filter_bitmap bs stack with
  | NONE => NONE
  | SOME (ts, ws) =>
      let '(wl, (i2, (pa2, (ib2, (pb2, (m2, c2)))))) :=
        word_gen_gc_move_roots conf (ts, (i1, (pa1, (ib1, (pb1, (curr, (m, dm))))))) in
      match map_bitmap bs wl stack with
      | NONE => NONE
      | SOME (hd, v2) => SOME (hd, (ws, (i2, (pa2, (ib2, (pb2, (m2, c2)))))))
      end
  end.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_partial_move_bitmap_def" *)
Definition word_gen_gc_partial_move_bitmap (conf : config)
    (x : word a * (list (word_loc a) * (word a * (word a * (word a * (mem * (dom * (word a * word a))))))))
    : option (list (word_loc a) * (list (word_loc a) * (word a * (word a * (mem * bool))))) :=
  let '(w, (stack, (i1, (pa1, (curr, (m, (dm, (gs, rs)))))))) := x in
  let bs := get_bits w in
  match filter_bitmap bs stack with
  | NONE => NONE
  | SOME (ts, ws) =>
      let '(wl, (i2, (pa2, (m2, c2)))) :=
        word_gen_gc_partial_move_roots conf (ts, (i1, (pa1, (curr, (m, (dm, (gs, rs))))))) in
      match map_bitmap bs wl stack with
      | NONE => NONE
      | SOME (hd, v2) => SOME (hd, (ws, (i2, (pa2, (m2, c2)))))
      end
  end.


(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_move_bitmap_unroll" *)
Local Theorem word_gen_gc_move_bitmap_unroll : forall conf (w : word a) stack i1 pa1 ib1 pb1 curr m dm,
  word_gen_gc_move_bitmap conf (w, (stack, (i1, (pa1, (ib1, (pb1, (curr, (m, dm)))))))) =
  if decide (w = n2w 0) then SOME ([], (stack, (i1, (pa1, (ib1, (pb1, (m, true))))))) else
  if decide (w = n2w 1) then SOME ([], (stack, (i1, (pa1, (ib1, (pb1, (m, true))))))) else
  match stack with
  | [] => NONE
  | x :: xs =>
      if decide ((w && n2w 1) = n2w 0) then
        match word_gen_gc_move_bitmap conf (w >>> 1, (xs, (i1, (pa1, (ib1, (pb1, (curr, (m, dm)))))))) with
        | NONE => NONE
        | SOME (new, (stack, (i1, (pa1, (ib1, (pb1, (m, c))))))) =>
            SOME (x :: new, (stack, (i1, (pa1, (ib1, (pb1, (m, c)))))))
        end
      else
        let '(x1, (i1, (pa1, (ib1, (pb1, (m1, c1)))))) :=
          word_gen_gc_move conf (x, (i1, (pa1, (ib1, (pb1, (curr, (m, dm))))))) in
        match word_gen_gc_move_bitmap conf (w >>> 1, (xs, (i1, (pa1, (ib1, (pb1, (curr, (m1, dm)))))))) with
        | NONE => NONE
        | SOME (new, (stack, (i1, (pa1, (ib1, (pb1, (m, c))))))) =>
            SOME (x1 :: new, (stack, (i1, (pa1, (ib1, (pb1, (m, andb c1 c)))))))
        end
  end.
Proof.
  intros conf w stack i1 pa1 ib1 pb1 curr m dm.
  destruct (decide (w = n2w 0)) as [->|H0].
  { unfold word_gen_gc_move_bitmap, get_bits. replace (bit_length (n2w 0 : word a)) with 0%N
      by (rewrite bit_length_def, (proj2 (bool_decide_spec _) eq_refl); reflexivity). reflexivity. }
  destruct (decide (w = n2w 1)) as [->|H1].
  { unfold word_gen_gc_move_bitmap, get_bits. rewrite (proj2 (bit_length_eq_1 (n2w 1)) eq_refl). reflexivity. }
  unfold word_gen_gc_move_bitmap at 1. rewrite (get_bits_cons w H0 H1).
  destruct stack as [|x xs]; [destruct (w ' 0); reflexivity|].
  destruct (decide ((w && n2w 1) = n2w 0)) as [Ha|Ha].
  - apply word_and_one_eq_0_iff in Ha. unfold is_true in Ha. apply Bool.not_true_iff_false in Ha. rewrite Ha.
    cbn [filter_bitmap map_bitmap]. unfold word_gen_gc_move_bitmap.
    destruct (filter_bitmap (get_bits (w >>> 1)) xs) as [[ts ws]|]; [|reflexivity].
    destruct (word_gen_gc_move_roots conf _) as (wl, (i2, (pa2, (ib2, (pb2, (m2, c2)))))).
    destruct (map_bitmap (get_bits (w >>> 1)) wl xs) as [[hd [y z]]|]; reflexivity.
  - assert (Hb : w ' 0 = true).
    { destruct (w ' 0) eqn:E; [reflexivity|]. exfalso; apply Ha, word_and_one_eq_0_iff. unfold is_true; congruence. }
    rewrite Hb. cbn [filter_bitmap map_bitmap]. unfold word_gen_gc_move_bitmap.
    destruct (filter_bitmap (get_bits (w >>> 1)) xs) as [[ts ws]|]; cbn beta iota.
    + rewrite (proj2 (word_gen_gc_move_roots_def _ _ _ _ _ _ _ _ _ _)).
      destruct (word_gen_gc_move conf _) as (x1, (i2, (pa2, (ib2, (pb2, (m2, c2)))))).
      destruct (word_gen_gc_move_roots conf (ts, _)) as (wl, (i3, (pa3, (ib3, (pb3, (m3, c3)))))).
      cbn [map_bitmap]. destruct (map_bitmap (get_bits (w >>> 1)) wl xs) as [[hd [y z]]|]; reflexivity.
    + destruct (word_gen_gc_move conf _) as (x1, (i2, (pa2, (ib2, (pb2, (m2, c2)))))). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_partial_move_bitmap_unroll" *)
Local Theorem word_gen_gc_partial_move_bitmap_unroll : forall conf (w : word a) stack i1 pa1 curr m dm gs rs,
  word_gen_gc_partial_move_bitmap conf (w, (stack, (i1, (pa1, (curr, (m, (dm, (gs, rs)))))))) =
  if decide (w = n2w 0) then SOME ([], (stack, (i1, (pa1, (m, true))))) else
  if decide (w = n2w 1) then SOME ([], (stack, (i1, (pa1, (m, true))))) else
  match stack with
  | [] => NONE
  | x :: xs =>
      if decide ((w && n2w 1) = n2w 0) then
        match word_gen_gc_partial_move_bitmap conf (w >>> 1, (xs, (i1, (pa1, (curr, (m, (dm, (gs, rs)))))))) with
        | NONE => NONE
        | SOME (new, (stack, (i1, (pa1, (m, c))))) => SOME (x :: new, (stack, (i1, (pa1, (m, c)))))
        end
      else
        let '(x1, (i1, (pa1, (m1, c1)))) :=
          word_gen_gc_partial_move conf (x, (i1, (pa1, (curr, (m, (dm, (gs, rs))))))) in
        match word_gen_gc_partial_move_bitmap conf (w >>> 1, (xs, (i1, (pa1, (curr, (m1, (dm, (gs, rs)))))))) with
        | NONE => NONE
        | SOME (new, (stack, (i1, (pa1, (m, c))))) => SOME (x1 :: new, (stack, (i1, (pa1, (m, andb c1 c)))))
        end
  end.
Proof.
  intros conf w stack i1 pa1 curr m dm gs rs.
  destruct (decide (w = n2w 0)) as [->|H0].
  { unfold word_gen_gc_partial_move_bitmap, get_bits. replace (bit_length (n2w 0 : word a)) with 0%N
      by (rewrite bit_length_def, (proj2 (bool_decide_spec _) eq_refl); reflexivity). reflexivity. }
  destruct (decide (w = n2w 1)) as [->|H1].
  { unfold word_gen_gc_partial_move_bitmap, get_bits. rewrite (proj2 (bit_length_eq_1 (n2w 1)) eq_refl). reflexivity. }
  unfold word_gen_gc_partial_move_bitmap at 1. rewrite (get_bits_cons w H0 H1).
  destruct stack as [|x xs]; [destruct (w ' 0); reflexivity|].
  destruct (decide ((w && n2w 1) = n2w 0)) as [Ha|Ha].
  - apply word_and_one_eq_0_iff in Ha. unfold is_true in Ha. apply Bool.not_true_iff_false in Ha. rewrite Ha.
    cbn [filter_bitmap map_bitmap]. unfold word_gen_gc_partial_move_bitmap.
    destruct (filter_bitmap (get_bits (w >>> 1)) xs) as [[ts ws]|]; [|reflexivity].
    destruct (word_gen_gc_partial_move_roots conf _) as (wl, (i2, (pa2, (m2, c2)))).
    destruct (map_bitmap (get_bits (w >>> 1)) wl xs) as [[hd [y z]]|]; reflexivity.
  - assert (Hb : w ' 0 = true).
    { destruct (w ' 0) eqn:E; [reflexivity|]. exfalso; apply Ha, word_and_one_eq_0_iff. unfold is_true; congruence. }
    rewrite Hb. cbn [filter_bitmap map_bitmap]. unfold word_gen_gc_partial_move_bitmap.
    destruct (filter_bitmap (get_bits (w >>> 1)) xs) as [[ts ws]|]; cbn beta iota.
    + rewrite (proj2 (word_gen_gc_partial_move_roots_def _ _ _ _ _ _ _ _ _ _)).
      destruct (word_gen_gc_partial_move conf _) as (x1, (i2, (pa2, (m2, c2)))).
      destruct (word_gen_gc_partial_move_roots conf (ts, _)) as (wl, (i3, (pa3, (m3, c3)))).
      cbn [map_bitmap]. destruct (map_bitmap (get_bits (w >>> 1)) wl xs) as [[hd [y z]]|]; reflexivity.
    + destruct (word_gen_gc_partial_move conf _) as (x1, (i2, (pa2, (m2, c2)))). reflexivity.
Qed.


(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_move_bitmaps_unroll" *)
Local Theorem word_gen_gc_move_bitmaps_unroll : forall conf (w : word a) stack bitmaps i1 pa1 ib1 pb1 curr m dm x,
  word_gen_gc_move_bitmaps conf (Word w, (stack, (bitmaps, (i1, (pa1, (ib1, (pb1, (curr, (m, dm))))))))) = SOME x /\
  (LENGTH bitmaps < dimword a - 1)%N /\ good_dimindex a ->
  word_gen_gc_move_bitmaps conf (Word w, (stack, (bitmaps, (i1, (pa1, (ib1, (pb1, (curr, (m, dm))))))))) =
  match DROP (w2n (w - n2w 1)) bitmaps with
  | [] => NONE
  | y :: ys =>
      match word_gen_gc_move_bitmap conf (y, (stack, (i1, (pa1, (ib1, (pb1, (curr, (m, dm)))))))) with
      | NONE => NONE
      | SOME (hd, (ws, (i2, (pa2, (ib2, (pb2, (m2, c2))))))) =>
          if negb (word_msb y) then SOME (hd, (ws, (i2, (pa2, (ib2, (pb2, (m2, c2))))))) else
          match word_gen_gc_move_bitmaps conf (Word (w + n2w 1), (ws, (bitmaps, (i2, (pa2, (ib2, (pb2, (curr, (m2, dm))))))))) with
          | NONE => NONE
          | SOME (hd3, (ws3, (i3, (pa3, (ib3, (pb3, (m3, c3))))))) =>
              SOME (hd ++ hd3, (ws3, (i3, (pa3, (ib3, (pb3, (m3, andb c2 c3)))))))
          end
      end
  end.
Proof.
  intros conf w stack bitmaps i1 pa1 ib1 pb1 curr m dm x (Hx & Hlen & Hg).
  destruct (decide (w = n2w 0)) as [->|Hw0].
  { unfold word_gen_gc_move_bitmaps, full_read_bitmap in Hx. rewrite (proj2 (bool_decide_spec _) eq_refl) in Hx.
    discriminate. }
  clear Hx. unfold word_gen_gc_move_bitmaps at 1. unfold full_read_bitmap at 1. rewrite (bd_F Hw0).
  destruct (DROP (w2n (w - n2w 1)) bitmaps) as [|h t] eqn:Ed; [reflexivity|].
  cbn [read_bitmap]. destruct (word_msb h) eqn:Hm.
  - destruct (DROP_cons_succ _ _ _ _ Ed) as [Ed' Hlt].
    rewrite (w2n_sub1 w Hw0) in Ed', Hlt.
    pose proof (w2n_ne0 w Hw0) as Hw0'.
    replace (w2n w - 1 + 1)%N with (w2n w) in Ed' by lia.
    assert (Hw1 : (w + n2w 1 : word a) <> n2w 0).
    { intros E. apply (f_equal w2n) in E. rewrite <- (n2w_w2n w), word_add_n2w, !w2n_n2w_small in E; lia. }
    unfold word_gen_gc_move_bitmap at 1.
    destruct (read_bitmap t) as [bs'|] eqn:Er.
    + rewrite (get_bits_intro h Hm), filter_bitmap_APPEND.
      destruct (filter_bitmap (get_bits h) stack) as [[zs rs]|] eqn:Ef1; [|reflexivity].
      cbn beta iota.
      destruct (word_gen_gc_move_roots conf (zs, _)) as (wl1, (i2, (pa2, (ib2, (pb2, (m2, c2)))))) eqn:Er1.
      assert (Hl1 : LENGTH zs = LENGTH wl1) by (symmetry; eapply word_gen_gc_move_roots_IMP_LENGTH; exact Er1).
      destruct (map_bitmap (get_bits h) wl1 stack) as [[t1 [t2 t3]]|] eqn:Em1.
      2:{ destruct (filter_bitmap bs' rs) as [[zs2 rs']|]; [|reflexivity]. cbn beta iota.
          rewrite word_gen_gc_move_roots_APPEND, Er1.
          destruct (word_gen_gc_move_roots conf (zs2, _)) as (wl2, (i3, (pa3, (ib3, (pb3, (m3, c3)))))).
          rewrite (map_bitmap_APPEND_APPEND _ _ _ _ wl2 bs' _ (conj Ef1 Hl1)), Em1. reflexivity. }
      destruct (filter_bitmap_map_bitmap (get_bits h) stack wl1 zs rs t2 t1 t3 (conj Ef1 (conj (eq_sym Hl1) Em1)))
        as [-> ->].
      cbn [negb]. unfold word_gen_gc_move_bitmaps, full_read_bitmap. rewrite (bd_F Hw1).
      replace (w + n2w 1 - n2w 1) with w by word_ring. rewrite Ed', Er.
      destruct (filter_bitmap bs' rs) as [[zs2 rs']|] eqn:Ef2; [|reflexivity]. cbn beta iota.
      rewrite word_gen_gc_move_roots_APPEND, Er1.
      destruct (word_gen_gc_move_roots conf (zs2, _)) as (wl2, (i3, (pa3, (ib3, (pb3, (m3, c3)))))).
      rewrite (map_bitmap_APPEND_APPEND _ _ _ _ wl2 bs' _ (conj Ef1 Hl1)), Em1.
      destruct (map_bitmap bs' wl2 rs) as [[u1 [u2 u3]]|]; reflexivity.
    + destruct (filter_bitmap (get_bits h) stack) as [[zs rs]|]; [|reflexivity]. cbn beta iota.
      destruct (word_gen_gc_move_roots conf (zs, _)) as (wl1, (i2, (pa2, (ib2, (pb2, (m2, c2)))))).
      destruct (map_bitmap (get_bits h) wl1 stack) as [[t1 t2]|]; [|reflexivity]. cbn [negb].
      unfold word_gen_gc_move_bitmaps, full_read_bitmap. rewrite (bd_F Hw1).
      replace (w + n2w 1 - n2w 1) with w by word_ring. rewrite Ed', Er. reflexivity.
  - cbn [negb]. unfold word_gen_gc_move_bitmap. fold (get_bits h).
    destruct (filter_bitmap (get_bits h) stack) as [[zs rs]|]; [|reflexivity]. cbn beta iota.
    destruct (word_gen_gc_move_roots conf (zs, _)) as (wl1, (i2, (pa2, (ib2, (pb2, (m2, c2)))))).
    destruct (map_bitmap (get_bits h) wl1 stack) as [[t1 [t2 t3]]|]; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_partial_move_bitmaps_unroll" *)
Local Theorem word_gen_gc_partial_move_bitmaps_unroll : forall conf (w : word a) stack bitmaps i1 pa1 curr m dm gs0 rs0 x,
  word_gen_gc_partial_move_bitmaps conf (Word w, (stack, (bitmaps, (i1, (pa1, (curr, (m, (dm, (gs0, rs0))))))))) = SOME x /\
  (LENGTH bitmaps < dimword a - 1)%N /\ good_dimindex a ->
  word_gen_gc_partial_move_bitmaps conf (Word w, (stack, (bitmaps, (i1, (pa1, (curr, (m, (dm, (gs0, rs0))))))))) =
  match DROP (w2n (w - n2w 1)) bitmaps with
  | [] => NONE
  | y :: ys =>
      match word_gen_gc_partial_move_bitmap conf (y, (stack, (i1, (pa1, (curr, (m, (dm, (gs0, rs0)))))))) with
      | NONE => NONE
      | SOME (hd, (ws, (i2, (pa2, (m2, c2))))) =>
          if negb (word_msb y) then SOME (hd, (ws, (i2, (pa2, (m2, c2))))) else
          match word_gen_gc_partial_move_bitmaps conf (Word (w + n2w 1), (ws, (bitmaps, (i2, (pa2, (curr, (m2, (dm, (gs0, rs0))))))))) with
          | NONE => NONE
          | SOME (hd3, (ws3, (i3, (pa3, (m3, c3))))) => SOME (hd ++ hd3, (ws3, (i3, (pa3, (m3, andb c2 c3)))))
          end
      end
  end.
Proof.
  intros conf w stack bitmaps i1 pa1 curr m dm gs0 rs0 x (Hx & Hlen & Hg).
  destruct (decide (w = n2w 0)) as [->|Hw0].
  { unfold word_gen_gc_partial_move_bitmaps, full_read_bitmap in Hx. rewrite (proj2 (bool_decide_spec _) eq_refl) in Hx.
    discriminate. }
  clear Hx. unfold word_gen_gc_partial_move_bitmaps at 1. unfold full_read_bitmap at 1. rewrite (bd_F Hw0).
  destruct (DROP (w2n (w - n2w 1)) bitmaps) as [|h t] eqn:Ed; [reflexivity|].
  cbn [read_bitmap]. destruct (word_msb h) eqn:Hm.
  - destruct (DROP_cons_succ _ _ _ _ Ed) as [Ed' Hlt].
    rewrite (w2n_sub1 w Hw0) in Ed', Hlt.
    pose proof (w2n_ne0 w Hw0) as Hw0'.
    replace (w2n w - 1 + 1)%N with (w2n w) in Ed' by lia.
    assert (Hw1 : (w + n2w 1 : word a) <> n2w 0).
    { intros E. apply (f_equal w2n) in E. rewrite <- (n2w_w2n w), word_add_n2w, !w2n_n2w_small in E; lia. }
    unfold word_gen_gc_partial_move_bitmap at 1.
    destruct (read_bitmap t) as [bs'|] eqn:Er.
    + rewrite (get_bits_intro h Hm), filter_bitmap_APPEND.
      destruct (filter_bitmap (get_bits h) stack) as [[zs rs]|] eqn:Ef1; [|reflexivity].
      cbn beta iota.
      destruct (word_gen_gc_partial_move_roots conf (zs, _)) as (wl1, (i2, (pa2, (m2, c2)))) eqn:Er1.
      assert (Hl1 : LENGTH zs = LENGTH wl1) by (symmetry; eapply word_gen_gc_partial_move_roots_IMP_LENGTH; exact Er1).
      destruct (map_bitmap (get_bits h) wl1 stack) as [[t1 [t2 t3]]|] eqn:Em1.
      2:{ destruct (filter_bitmap bs' rs) as [[zs2 rs']|]; [|reflexivity]. cbn beta iota.
          rewrite word_gen_gc_partial_move_roots_APPEND, Er1.
          destruct (word_gen_gc_partial_move_roots conf (zs2, _)) as (wl2, (i3, (pa3, (m3, c3)))).
          rewrite (map_bitmap_APPEND_APPEND _ _ _ _ wl2 bs' _ (conj Ef1 Hl1)), Em1. reflexivity. }
      destruct (filter_bitmap_map_bitmap (get_bits h) stack wl1 zs rs t2 t1 t3 (conj Ef1 (conj (eq_sym Hl1) Em1)))
        as [-> ->].
      cbn [negb]. unfold word_gen_gc_partial_move_bitmaps, full_read_bitmap. rewrite (bd_F Hw1).
      replace (w + n2w 1 - n2w 1) with w by word_ring. rewrite Ed', Er.
      destruct (filter_bitmap bs' rs) as [[zs2 rs']|] eqn:Ef2; [|reflexivity]. cbn beta iota.
      rewrite word_gen_gc_partial_move_roots_APPEND, Er1.
      destruct (word_gen_gc_partial_move_roots conf (zs2, _)) as (wl2, (i3, (pa3, (m3, c3)))).
      rewrite (map_bitmap_APPEND_APPEND _ _ _ _ wl2 bs' _ (conj Ef1 Hl1)), Em1.
      destruct (map_bitmap bs' wl2 rs) as [[u1 [u2 u3]]|]; reflexivity.
    + destruct (filter_bitmap (get_bits h) stack) as [[zs rs]|]; [|reflexivity]. cbn beta iota.
      destruct (word_gen_gc_partial_move_roots conf (zs, _)) as (wl1, (i2, (pa2, (m2, c2)))).
      destruct (map_bitmap (get_bits h) wl1 stack) as [[t1 t2]|]; [|reflexivity]. cbn [negb].
      unfold word_gen_gc_partial_move_bitmaps, full_read_bitmap. rewrite (bd_F Hw1).
      replace (w + n2w 1 - n2w 1) with w by word_ring. rewrite Ed', Er. reflexivity.
  - cbn [negb]. unfold word_gen_gc_partial_move_bitmap. fold (get_bits h).
    destruct (filter_bitmap (get_bits h) stack) as [[zs rs]|]; [|reflexivity]. cbn beta iota.
    destruct (word_gen_gc_partial_move_roots conf (zs, _)) as (wl1, (i2, (pa2, (m2, c2)))).
    destruct (map_bitmap (get_bits h) wl1 stack) as [[t1 [t2 t3]]|]; reflexivity.
Qed.

End GenDefs.

(** ** The generational collector: moving one object *)

Lemma Temp_neq (i j : N) : (i < 32)%N -> (j < 32)%N -> i <> j -> Temp (n2w i) <> Temp (n2w j).
Proof.
  intros Hi Hj Hij E. injection E as E.
  rewrite (N.mod_small i), (N.mod_small j) in E by (rewrite dimword_pow; cbn; lia). contradiction.

Qed.

Ltac sx_temp :=
  repeat match goal with
  | |- context [decide (Temp (n2w ?i) = Temp (n2w ?j))] =>
      let E := fresh in destruct (decide (Temp (n2w i) = Temp (n2w j))) as [E|_];
      [exfalso; exact (Temp_neq i j ltac:(lia) ltac:(lia) ltac:(lia) E)|]
  | |- context [decide (Temp (n2w ?i) = ?k)] =>
      lazymatch k with Temp _ => fail | _ =>
      let E := fresh in destruct (decide (Temp (n2w i) = k)) as [E|_]; [discriminate E|] end
  | |- context [decide (?k = Temp (n2w ?i))] =>
      lazymatch k with Temp _ => fail | _ =>
      let E := fresh in destruct (decide (k = Temp (n2w i))) as [E|_]; [discriminate E|] end
  end.

Ltac sx_us := repeat match goal with H : use_store ?X = true |- context [use_store ?X] => rewrite H; cbn [negb] end.
Ltac sx_all3 := repeat (sx_step2; sx_simp; rewrite ?sx_store_upd; sx_dec; sx_temp; sx_simp; sx_us).

Ltac store_fin2 :=
  apply fmap_ext; let k := fresh "k" in intros k; cbn [FUPDATE_LIST FOLDL]; rewrite ?FLOOKUP_UPD_store;
  repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)); try subst end;
  try congruence; try reflexivity.

Ltac st_fin2 := f_equal; apply state_ext; nf_fields; try reflexivity; try lia; try solve [regs_fin];
  try solve [store_fin2].

Section GenMove.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.

Lemma and_not0 (x : word a) : (x && ¬ n2w 0)%w = x.
Proof. bitwise. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_move_code_thm" *)
Theorem word_gen_gc_move_code_thm : forall conf (w : word_loc a) (i pa ib pb old : word a) m dm w1 i1 pa1 ib1 pb1 m1
    (s : state),
  word_gen_gc_move conf (w, (i, (pa, (ib, (pb, (old, (m, dm))))))) = (w1, (i1, (pa1, (ib1, (pb1, (m1, true)))))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\ get_var 5 s = SOME w /\
  Temp (n2w 0) IN FDOM (store s) /\ Temp (n2w 1) IN FDOM (store s) /\
  FLOOKUP (store s) (Temp (n2w 2)) = SOME (Word pb) /\ FLOOKUP (store s) (Temp (n2w 3)) = SOME (Word ib) /\
  1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\ 6 IN FDOM (regs s) ->
  exists ck r0 r1 r2 r6 t0 t1,
    evaluate (word_gen_gc_move_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, w1); (6, r6)])
             (set_memory m1 (set_store_fld (store s |++ [(Temp (n2w 0), t0); (Temp (n2w 1), t1);
                                                          (Temp (n2w 2), Word pb1); (Temp (n2w 3), Word ib1)]) s))).
Proof.
  intros conf w i pa ib pb old m dm w1 i1 pa1 ib1 pb1 m1 s
    (H & Hsl & Hws & H2 & Hls & Hsh & Hold & Hus & Hm & Hdm & H0 & H1 & H2r & H3 & H4 & H5 & HT0 & HT1 & HT2 & HT3 & _ & _ & H6).
  unfold get_var in *. subst m dm.
  fdom_val H0 0 v0 Ev0. fdom_val H1 1 v1 Ev1. fdom_val H2r 2 v2 Ev2. fdom_val H6 6 v6 Ev6.
  assert (ET0 : FLOOKUP (store s) (Temp (n2w 0)) <> None) by exact HT0.
  destruct (FLOOKUP (store s) (Temp (n2w 0))) as [t0|] eqn:Et0; [clear ET0|contradiction].
  assert (ET1 : FLOOKUP (store s) (Temp (n2w 1)) <> None) by exact HT1.
  destruct (FLOOKUP (store s) (Temp (n2w 1))) as [t1|] eqn:Et1; [clear ET1|contradiction].
  unfold is_true in Hus.
  destruct w as [v|l1 l2].
  2:{ cbn in H. injection H as <- <- <- <- <- <- Hl2. apply N.eqb_eq in Hl2; subst l2.
      exists 0, v0, v1, v2, v6, t0, t1. rewrite N.add_0_r. unfold word_gen_gc_move_code. sx_all3.
      rewrite set_clock_same. st_fin2. }
  cbn [word_gen_gc_move] in H.
  rewrite WORD_AND_COMM in H.
  destruct (decide ((v && n2w 1)%w = n2w 0)) as [Hev|Hodd].
  { injection H as <- <- <- <- <- <-. exists 0, v0, v1, v2, v6, t0, t1. rewrite N.add_0_r.
    unfold word_gen_gc_move_code. sx_all3.
    rewrite (proj2 (bool_decide_spec _) Hev). sx_all3. rewrite set_clock_same. st_fin2. }
  assert (Hoddb : bool_decide ((v && n2w 1)%w = n2w 0) = false) by exact (bd_F Hodd).
  cbv zeta in H.
  assert (Ea : (v >>> shift_length conf << word_shift a + old)%w = ptr_to_addr conf old v)
    by (unfold ptr_to_addr; rewrite Hsh; apply WORD_ADD_COMM).
  destruct (memory s (ptr_to_addr conf old v)) as [hv|l1 l2] eqn:Em.
  2:{ exfalso. cbn [wordSem.isWord wordSem.is_fwd_ptr] in H. rewrite Bool.andb_false_r in H.
      destruct (is_ref_header _).
      - destruct (memcpy _ _ _ _ _) as (?, (?, ?)). injection H as _ _ _ _ _ _ Hc. rewrite ?Bool.andb_false_l, ?Bool.andb_false_r in Hc; discriminate.
      - destruct (memcpy _ _ _ _ _) as (?, (?, ?)). injection H as _ _ _ _ _ _ Hc. rewrite ?Bool.andb_false_l, ?Bool.andb_false_r in Hc; discriminate. }
  cbn [wordSem.isWord wordSem.theWord] in H. rewrite Bool.andb_true_r in H.
  destruct (wordSem.is_fwd_ptr (Word hv)) eqn:Ef.
  - injection H as <- <- <- <- <- <- Hc. apply bool_decide_spec in Hc.
    exists 0, (Word (ptr_to_addr conf old v)), (Word (hv >>> 2 << shift_length conf)), v2, v6, t0, t1.
    rewrite N.add_0_r. unfold word_gen_gc_move_code. sx_all3.
    rewrite Hoddb. cbn [list_Seq]. sx_all3. sx_us. sx_all3. rewrite word_sh_lsr by lia. sx_all3.
    rewrite word_sh_lsl by lia. sx_all3.
    rewrite Ea. destruct (classical_dec _) as [_|Hn]; [|contradiction]. cbn iota.
    cbn in Ef. rewrite Em. sx_all3. rewrite Ef. rewrite word_sh_lsr by lia. sx_all3. rewrite word_sh_lsl by lia. sx_all3.
    unfold clear_top_inst. sx_all3. rewrite word_sh_lsl by lia. sx_all3. rewrite word_sh_lsr by lia. sx_all3.
    rewrite <- select_lower_lemma, (proj1 (proj2 (proj2 (proj2 (WORD_OR_CLAUSES _))))).
    rewrite WORD_OR_COMM. cbn [wordSem.theWord]. fold (update_addr conf (hv >>> 2) v).
    rewrite set_clock_same. st_fin2.
  - cbn in Ef. set (L := decode_length conf hv) in H.
    destruct (is_ref_header hv) eqn:Eref.
    + destruct (memcpy (L + n2w 1) (ptr_to_addr conf old v) (pb - (L + n2w 1) * bytes_in_word)%w (memory s) (mdomain s))
        as (b1, (m1', c1)) eqn:Emc.
      injection H as <- <- <- <- <- <- Hc.
      rewrite !Bool.andb_true_iff in Hc. destruct Hc as ((Hin & _) & _ & Hc1). subst c1.
      apply bool_decide_spec in Hin.
      set (nv := (ib - (L + n2w 1))%w).
      exists (w2n (L + n2w 1)), (Word (nv << 2)), (Word (nv << shift_length conf)),
        (Word (ptr_to_addr conf old v + (L + n2w 1) * bytes_in_word)), (Word (L + n2w 1)), (Word pa), (Word i).
      unfold word_gen_gc_move_code. sx_all3.
      rewrite Hoddb. cbn [list_Seq]. sx_all3. sx_us. sx_all3.
      rewrite word_sh_lsr by lia. sx_all3. rewrite word_sh_lsl by lia. sx_all3.
      rewrite Ea. sx_simp. rewrite Em. sx_all3. rewrite Ef. rewrite word_sh_lsr by lia. sx_all3.
      unfold is_ref_header in Eref. rewrite and_not0, Eref. sx_all3.
      change (hv >>> (dimindex a - len_size conf))%w with L.
      rewrite word_sh_lsl by lia. sx_all3. rewrite !Hsh. fold nv.
      match goal with |- context [evaluate (memcpy_code, set_regs ?R (set_store_fld ?ST (set_clock _ s)))] =>
        destruct (memcpy_code_thm (L + n2w 1) (ptr_to_addr conf old v) (pb - (L + n2w 1) * bytes_in_word)%w
                    (memory s) (mdomain s) b1 m1' (set_regs R (set_store_fld ST (set_clock (clock s) s)))) as [r1' Emc'] end.
      { unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD. cbn [N.eqb Pos.eqb].
        splits; try assumption; try reflexivity;
          unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; discriminate. }
      autorewrite with nf in Emc'. cbn [clock regs memory store set_regs set_clock set_memory set_store_fld] in Emc'.
      autorewrite with nf in Emc'. cbn [FUPDATE_LIST FOLDL] in Emc'. rewrite Emc'. sx_all3.
      rewrite word_sh_lsl by lia. sx_all3.
      sx_all3.
      unfold clear_top_inst. sx_all3. rewrite word_sh_lsl by lia. sx_all3. rewrite word_sh_lsr by lia. sx_all3.
      rewrite word_sh_lsl by lia. sx_all3.
      rewrite <- select_lower_lemma, (proj1 (proj2 (proj2 (proj2 (WORD_OR_CLAUSES _))))).
      rewrite WORD_OR_COMM. fold (update_addr conf nv v).
      st_fin2.
    + destruct (memcpy (L + n2w 1) (ptr_to_addr conf old v) pa (memory s) (mdomain s))
        as (pa1', (m1', c1)) eqn:Emc.
      injection H as <- <- <- <- <- <- Hc.
      rewrite !Bool.andb_true_iff in Hc. destruct Hc as ((Hin & _) & _ & Hc1). subst c1.
      apply bool_decide_spec in Hin.
      exists (w2n (L + n2w 1)), (Word (i << 2)), (Word (i << shift_length conf)),
        (Word (ptr_to_addr conf old v)), (Word (L + n2w 1)), t0, t1. unfold word_gen_gc_move_code. sx_all3.
      rewrite Hoddb. cbn [list_Seq]. sx_all3. sx_us. sx_all3.
      rewrite word_sh_lsr by lia. sx_all3. rewrite word_sh_lsl by lia. sx_all3.
      rewrite Ea. sx_simp. rewrite Em. sx_all3. rewrite Ef. rewrite word_sh_lsr by lia. sx_all3.
      unfold is_ref_header in Eref. rewrite and_not0, Eref. sx_all3.
      change (hv >>> (dimindex a - len_size conf))%w with L.
      match goal with |- context [evaluate (memcpy_code, set_regs ?R (set_clock _ s))] =>
        destruct (memcpy_code_thm (L + n2w 1) (ptr_to_addr conf old v) pa (memory s) (mdomain s)
                    pa1' m1' (set_regs R (set_clock (clock s) s))) as [r1' Emc'] end.
      { nf_fields. unfold get_var. rewrite ?FLOOKUP_UPD. cbn [N.eqb Pos.eqb].
        splits; try assumption; try reflexivity.
        unfold pred_set.IN, FDOM. rewrite ?FLOOKUP_UPD. cbn [N.eqb Pos.eqb]. discriminate. }
      autorewrite with nf in Emc'. cbn [clock regs memory set_regs set_clock set_memory] in Emc'.
      autorewrite with nf in Emc'. cbn [FUPDATE_LIST FOLDL] in Emc'. rewrite Emc'. sx_all3.
      rewrite word_sh_lsl by lia. sx_all3. rewrite word_sh_lsl by lia. sx_all3.
      rewrite Hsh. replace (ptr_to_addr conf old v + (L + n2w 1) * bytes_in_word -
        (L + n2w 1) * bytes_in_word)%w with (ptr_to_addr conf old v) by word_ring.
      sx_all3. destruct (classical_dec _) as [_|Hn]; [|contradiction]. cbn iota. sx_all3.
      unfold clear_top_inst. sx_all3. rewrite word_sh_lsl by lia. sx_all3. rewrite word_sh_lsr by lia. sx_all3.
      rewrite word_sh_lsl by lia. sx_all3.
      rewrite <- select_lower_lemma, (proj1 (proj2 (proj2 (proj2 (WORD_OR_CLAUSES _))))).
      rewrite WORD_OR_COMM. fold (update_addr conf i v).
      replace (i + (L + n2w 1))%w with (i + L + n2w 1)%w by word_ring.
      st_fin2.
Qed.


(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_partial_move_code_thm" *)
Theorem word_gen_gc_partial_move_code_thm : forall conf (w : word_loc a) (i pa old gs rs : word a) m dm w1 i1 pa1 m1
    (s : state),
  word_gen_gc_partial_move conf (w, (i, (pa, (old, (m, (dm, (gs, rs))))))) = (w1, (i1, (pa1, (m1, true)))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ good_dimindex a /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\ get_var 5 s = SOME w /\
  FLOOKUP (store s) (Temp (n2w 0)) = SOME (Word gs) /\ FLOOKUP (store s) (Temp (n2w 1)) = SOME (Word rs) /\
  1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\ 6 IN FDOM (regs s) ->
  exists ck r0 r1 r2 r6,
    evaluate (word_gen_gc_partial_move_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, w1); (6, r6)])
             (set_memory m1 s)).
Proof.
  intros conf w i pa old gs rs m dm w1 i1 pa1 m1 s
    (H & Hsl & Hws & H2 & Hls & Hsh & Hold & Hus & Hm & Hdm & Hg & H0 & H1 & H2r & H3 & H4 & H5 & HT0 & HT1 & _ & _ & H6).
  unfold get_var in *. subst m dm.
  fdom_val H0 0 v0 Ev0. fdom_val H1 1 v1 Ev1. fdom_val H2r 2 v2 Ev2. fdom_val H6 6 v6 Ev6.
  unfold is_true in Hus.
  destruct w as [v|l1 l2].
  2:{ cbn in H. injection H as <- <- <- <- Hl2. apply N.eqb_eq in Hl2; subst l2.
      exists 0, v0, v1, v2, v6. rewrite N.add_0_r. unfold word_gen_gc_partial_move_code. sx_all3.
      rewrite set_clock_same. st_fin2. }
  cbn [word_gen_gc_partial_move] in H.
  destruct (decide ((v && n2w 1)%w = n2w 0)) as [Hev|Hodd].
  { injection H as <- <- <- <-. exists 0, v0, v1, v2, v6. rewrite N.add_0_r.
    unfold word_gen_gc_partial_move_code. sx_all3.
    rewrite (proj2 (bool_decide_spec _) Hev). sx_all3. rewrite set_clock_same. st_fin2. }
  assert (Hoddb : bool_decide ((v && n2w 1)%w = n2w 0) = false) by exact (bd_F Hodd).
  cbv zeta in H.
  assert (Ea : (v >>> shift_length conf << word_shift a + old)%w = ptr_to_addr conf old v)
    by (unfold ptr_to_addr; rewrite Hsh; apply WORD_ADD_COMM).
  assert (Et : (ptr_to_addr conf old v - old)%w = (v >>> shift_length conf << word_shift a)%w)
    by (unfold ptr_to_addr; rewrite Hsh; word_ring).
  rewrite Et in H.
  destruct ((v >>> shift_length conf << word_shift a) <+ gs)%w eqn:Elo.
  { cbn [orb] in H. injection H as <- <- <- <-.
    exists 0, (Word (v >>> shift_length conf << word_shift a)%w), (Word rs), v2, (Word gs). rewrite N.add_0_r.
    unfold word_gen_gc_partial_move_code. sx_all3. rewrite Hoddb. cbn [list_Seq]. sx_all3.
    rewrite word_sh_lsr by lia. sx_all3. rewrite word_sh_lsl by lia. sx_all3. rewrite Elo. sx_all3.
    rewrite set_clock_same. st_fin2. }
  cbn [orb] in H.
  destruct (rs <=+ (v >>> shift_length conf << word_shift a))%w eqn:Ehs.
  { injection H as <- <- <- <-.
    assert (Elo2 : ((v >>> shift_length conf << word_shift a) <+ rs)%w = false).
    { destruct ((v >>> shift_length conf << word_shift a) <+ rs)%w eqn:E; [|reflexivity].
      exfalso. apply (proj2 (WORD_NOT_LOWER _ _) Ehs). exact E. }
    exists 0, (Word (v >>> shift_length conf << word_shift a)%w), (Word rs), v2, (Word rs). rewrite N.add_0_r.
    unfold word_gen_gc_partial_move_code. sx_all3. rewrite Hoddb. cbn [list_Seq]. sx_all3.
    rewrite word_sh_lsr by lia. sx_all3. rewrite word_sh_lsl by lia. sx_all3. rewrite Elo. sx_all3.
    rewrite Elo2. sx_all3.
    cbn [negb]. rewrite set_clock_same. st_fin2. }
  assert (Elo2 : ((v >>> shift_length conf << word_shift a) <+ rs)%w = true).
  { destruct ((v >>> shift_length conf << word_shift a) <+ rs)%w eqn:E; [reflexivity|].
    exfalso. assert (Hn : ~ is_true ((v >>> shift_length conf << word_shift a) <+ rs)%w) by (unfold is_true; congruence).
    apply WORD_NOT_LOWER in Hn. unfold is_true in Hn. congruence. }
  destruct (wordSem.is_fwd_ptr (memory s (ptr_to_addr conf old v))) eqn:Ef.
  - injection H as <- <- <- <- Hc. apply bool_decide_spec in Hc.
    destruct (memory s (ptr_to_addr conf old v)) as [fv|] eqn:Em; [|discriminate].
    exists 0, (Word (ptr_to_addr conf old v)), (Word (fv >>> 2 << shift_length conf)), v2, (Word rs).
    rewrite N.add_0_r. unfold word_gen_gc_partial_move_code. sx_all3. rewrite Hoddb. cbn [list_Seq]. sx_all3.
    rewrite word_sh_lsr by lia. sx_all3. rewrite word_sh_lsl by lia. sx_all3. rewrite Elo. sx_all3.
    rewrite Elo2. cbn [negb]. sx_all3.
    rewrite Ea. destruct (classical_dec _) as [_|Hn]; [|contradiction]. cbn iota.
    cbn in Ef. rewrite Em. sx_all3. rewrite Ef. rewrite word_sh_lsr by lia. sx_all3. rewrite word_sh_lsl by lia. sx_all3.
    unfold clear_top_inst. sx_all3. rewrite word_sh_lsl by lia. sx_all3. rewrite word_sh_lsr by lia. sx_all3.
    rewrite <- select_lower_lemma, (proj1 (proj2 (proj2 (proj2 (WORD_OR_CLAUSES _))))).
    rewrite WORD_OR_COMM. cbn [wordSem.theWord]. fold (update_addr conf (fv >>> 2) v).
    rewrite set_clock_same. st_fin2.
  - destruct (memory s (ptr_to_addr conf old v)) as [hv|] eqn:Em.
    2:{ cbn [wordSem.isWord] in H. rewrite !Bool.andb_false_r in H. destruct (memcpy _ _ _ _ _) as (?, (?, ?)).
        injection H as _ _ _ _ Hc; rewrite ?Bool.andb_false_l, ?Bool.andb_false_r in Hc; discriminate. }
    cbn [wordSem.isWord wordSem.theWord] in H. cbn in Ef.
    set (L := decode_length conf hv) in H.
    destruct (memcpy (L + n2w 1) (ptr_to_addr conf old v) pa (memory s) (mdomain s))
      as (pa1', (m1', c1)) eqn:Emc.
    injection H as <- <- <- <- Hc.
    rewrite !Bool.andb_true_r, !Bool.andb_true_iff in Hc. destruct Hc as (Hin & _ & Hc1). subst c1.
    destruct Hin as [Hin _]. apply bool_decide_spec in Hin.
    exists (w2n (L + n2w 1)), (Word (i << 2)), (Word (i << shift_length conf)),
      (Word (ptr_to_addr conf old v)), (Word (L + n2w 1)). unfold word_gen_gc_partial_move_code. sx_all3. rewrite Hoddb. cbn [list_Seq]. sx_all3.
    rewrite word_sh_lsr by lia. sx_all3. rewrite word_sh_lsl by lia. sx_all3. rewrite Elo. sx_all3.
    rewrite Elo2. cbn [negb]. sx_all3.
    rewrite Ea. sx_simp. rewrite Em. sx_all3. rewrite Ef. rewrite word_sh_lsr by lia. sx_all3.
    change (hv >>> (dimindex a - len_size conf))%w with L.
    match goal with |- context [evaluate (memcpy_code, set_regs ?R (set_clock _ s))] =>
      destruct (memcpy_code_thm (L + n2w 1) (ptr_to_addr conf old v) pa (memory s) (mdomain s)
                  pa1' m1' (set_regs R (set_clock (clock s) s))) as [r1' Emc'] end.
    { unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD. cbn [N.eqb Pos.eqb].
      splits; try assumption; try reflexivity;
        unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; discriminate. }
    autorewrite with nf in Emc'. cbn [clock regs memory set_regs set_clock set_memory] in Emc'.
    autorewrite with nf in Emc'. cbn [FUPDATE_LIST FOLDL] in Emc'. rewrite Emc'. sx_all3.
    rewrite word_sh_lsl by lia. sx_all3. rewrite word_sh_lsl by lia. sx_all3.
    rewrite Hsh. replace (ptr_to_addr conf old v + (L + n2w 1) * bytes_in_word -
      (L + n2w 1) * bytes_in_word)%w with (ptr_to_addr conf old v) by word_ring.
    sx_all3. destruct (classical_dec _) as [_|Hn]; [|contradiction]. cbn iota. sx_all3.
    unfold clear_top_inst. sx_all3. rewrite word_sh_lsl by lia. sx_all3. rewrite word_sh_lsr by lia. sx_all3.
    rewrite word_sh_lsl by lia. sx_all3.
    rewrite <- select_lower_lemma, (proj1 (proj2 (proj2 (proj2 (WORD_OR_CLAUSES _))))).
    rewrite WORD_OR_COMM. fold (update_addr conf i v).
    replace (i + (L + n2w 1))%w with (i + L + n2w 1)%w by word_ring.
    st_fin2.
Qed.

End GenMove.

(** ** The generational collector: stack scanning *)

Section GenBitmap.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.

Local Theorem word_gen_gc_partial_move_bitmap_code_thm_n : forall n (w : word a) stack (s : state) i pa curr m dm new stack1
    i1 pa1 m1 old init conf gs rs,
  (w2n w < n)%N ->
  word_gen_gc_partial_move_bitmap conf (w, (stack, (i, (pa, (curr, (m, (dm, (gs, rs)))))))) = SOME (new, (stack1, (i1, (pa1, (m1, true))))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ good_dimindex a /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word curr) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ use_stack s /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\
  get_var 7 s = SOME (Word w) /\ get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
  FLOOKUP (store s) (Temp (n2w 0)) = SOME (Word gs) /\ FLOOKUP (store s) (Temp (n2w 1)) = SOME (Word rs) /\
  stackSem.stack s = init ++ old ++ stack /\ stack_space s = LENGTH init /\
  (dimindex a DIV 8 * LENGTH (stackSem.stack s) < dimword a)%N ->
  exists ck r0 r1 r2 r5 r6 r7,
    evaluate (word_gen_gc_partial_move_bitmap_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, r7); (8, Word (bytes_in_word * n2w (LENGTH (old ++ new))))])
             (set_memory m1 (set_stack (init ++ old ++ new ++ stack1) s))).
Proof.
  induction n as [|n IH] using N.peano_ind; intros w stack s i pa curr m dm new stack1 i1 pa1 m1 old init conf gs rs Hn;
    [lia|].
  intros (H & Hsl & Hws & H2 & Hls & Hg & Hsh & Hold & Hus & Hm & Hdm & Hust & H0 & H1 & H2r & H3 & H4 & H5 & H6
          & H7 & H8 & HT0 & HT1 & Hst & Hss & Hlen).
  unfold get_var in *; subst m dm.
  fdom_val H0 0 v0 Ev0; fdom_val H1 1 v1 Ev1; fdom_val H2r 2 v2 Ev2; fdom_val H5 5 v5 Ev5; fdom_val H6 6 v6 Ev6.
  rewrite word_gen_gc_partial_move_bitmap_unroll in H.
  destruct (decide (w = n2w 0)) as [Hw0|Hw0].
  { injection H as <- <- <- <- <-. exists 0, v0, v1, v2, v5, v6, (Word w). rewrite N.add_0_r.
    unfold word_gen_gc_partial_move_bitmap_code. rewrite ev_while. sx_simp.
    rewrite (lo2_true w Hg (or_introl Hw0)). sx_simp. rewrite set_clock_same, app_nil_r. cbn [app].
    rewrite <- Hst. st_fin. }
  destruct (decide (w = n2w 1)) as [Hw1|Hw1].
  { injection H as <- <- <- <- <-. exists 0, v0, v1, v2, v5, v6, (Word w). rewrite N.add_0_r.
    unfold word_gen_gc_partial_move_bitmap_code. rewrite ev_while. sx_simp.
    rewrite (lo2_true w Hg (or_intror Hw1)). sx_simp. rewrite set_clock_same, app_nil_r. cbn [app].
    rewrite <- Hst. st_fin. }
  destruct stack as [|x xs]; [discriminate|].
  pose proof (w2n_lsr1_lt w Hw0) as Hlt.
  destruct (decide ((w && n2w 1)%w = n2w 0)) as [Ha|Ha].
  - destruct (word_gen_gc_partial_move_bitmap conf ((w >>> 1)%w, (xs, (i, (pa, (curr, (memory s, (mdomain s, (gs, rs)))))))))
      as [[new' [st' [i' [pa' [m' c']]]]]|] eqn:Eb; [|discriminate].
    injection H as <- <- <- <- <- ->.
    destruct (IH (w >>> 1)%w xs
                (set_regs (regs s |+ (7, Word (w >>> 1)%w)
                                  |+ (8, Word (bytes_in_word * n2w (LENGTH (old ++ [x])))%w)) s)
                i pa curr (memory s) (mdomain s) new' st' i' pa' m' (old ++ [x]) init conf gs rs ltac:(lia))
      as (ck & p0 & p1 & p2 & p5 & p6 & p7 & Er).
    { unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
      splits; try assumption; try reflexivity;
        try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence).
      rewrite Hst, <- !app_assoc. reflexivity. }
    exists (ck + 1), p0, p1, p2, p5, p6, p7.
    unfold word_gen_gc_partial_move_bitmap_code. rewrite ev_while. sx_simp.
    rewrite (lo2_false w Hg Hw0 Hw1). cbn [negb]. sx_simp. sx_all3. rewrite (proj2 (bool_decide_spec _) Ha).
    cbn [list_Seq].  sx_all3. rewrite word_sh_lsr by lia. sx_all3.
    rewrite bytes_n2w_succ.
    cbn [cont_loop]. replace (clock s + (ck + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    unfold word_gen_gc_partial_move_bitmap_code in Er. cbn [list_Seq] in Er.
    autorewrite with nf in Er. cbn [clock regs memory stackSem.stack set_regs set_clock set_memory set_stack] in Er.
    autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er.
    rewrite <- !app_assoc in Er. cbn [app] in Er. rewrite !LENGTH_length, app_length in Er |- *. cbn [length] in Er |- *.
    rewrite app_length in Er; cbn [length] in Er.
    replace (N.of_nat (length old) + 1)%N with (N.of_nat (length old + 1)) by lia.
    sx_simp. rw_eval Er. st_fin.
  - destruct (word_gen_gc_partial_move conf (x, (i, (pa, (curr, (memory s, (mdomain s, (gs, rs))))))))
      as (x1, (i1', (pa1', (m1', c1)))) eqn:Emv.
    destruct (word_gen_gc_partial_move_bitmap conf ((w >>> 1)%w, (xs, (i1', (pa1', (curr, (m1', (mdomain s, (gs, rs)))))))))
      as [[new' [st' [i' [pa' [m' c']]]]]|] eqn:Eb; [|discriminate].
    injection H as <- <- <- <- <- Hc. apply andb_prop in Hc as [-> ->].
    set (L := LENGTH old).
    assert (HL : (dimindex a DIV 8 * L < dimword a)%N).
    { eapply N.le_lt_trans; [|exact Hlen]. apply N.mul_le_mono_l. unfold L. rewrite Hst, !LENGTH_length, !app_length. lia. }
    assert (HLw : (L < dimword a)%N).
    { assert (Hk : (1 <= dimindex a DIV 8)%N) by (destruct Hg as [E|E]; rewrite E; cbn; lia). nia. }
    set (s4 := set_regs (regs s |+ (5, x) |+ (7, Word (w >>> 1)%w)) s).
    destruct (word_gen_gc_partial_move_code_thm conf x i pa curr gs rs (memory s) (mdomain s) x1 i1' pa1' m1' s4)
      as (ck1 & q0 & q1 & q2 & q6 & Ev).
    { subst s4; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
      splits; try assumption; try reflexivity; try lia;
        unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
    set (s5 := set_regs ((regs s4 |++ [(0, q0); (1, q1); (2, q2); (3, Word pa1'); (4, Word i1'); (5, x1); (6, q6)])
                         |+ (8, Word (bytes_in_word * n2w (LENGTH (old ++ [x1])))%w))
                 (set_memory m1' (set_stack (init ++ (old ++ [x1]) ++ xs) s))).
    destruct (IH (w >>> 1)%w xs s5 i1' pa1' curr m1' (mdomain s) new' st' i' pa' m' (old ++ [x1]) init conf gs rs
                ltac:(lia)) as (ck2 & p0 & p1 & p2 & p5 & p6 & p7 & Er).
    { subst s5 s4; unfold get_var; nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
      splits; try assumption; try reflexivity; try lia;
        try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence).
      rewrite Hst in Hlen. replace (LENGTH (init ++ (old ++ [x1]) ++ xs)) with (LENGTH (init ++ old ++ x :: xs)); [exact Hlen|]. rewrite !LENGTH_length, !app_length; cbn [length]; lia. }
    pose proof (evaluate_add_clock (ck2 + 1) (word_gen_gc_partial_move_code conf) (set_clock (clock s4 + ck1) s4)) as Ev'.
    assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
    specialize (Ev' NONE _ (conj Ev NT)). subst s4. autorewrite with nf in Ev'.
    cbn [clock regs memory set_regs set_clock set_memory] in Ev'. autorewrite with nf in Ev'. cbn [FUPDATE_LIST FOLDL] in Ev'.
    exists (ck1 + ck2 + 1), p0, p1, p2, p5, p6, p7.
    unfold word_gen_gc_partial_move_bitmap_code. rewrite ev_while. sx_simp.
    rewrite (lo2_false w Hg Hw0 Hw1). cbn [negb]. sx_all3. rewrite (bd_F Ha).
    cbn [list_Seq]. sx_all3.
    unfold is_true in Hust. rewrite Hust. cbn [negb].
    fold L. rewrite (bytes_in_word_word_shift_n2w L (conj Hg HL)), (w2n_n2w_small L HLw).
    replace (n2w L << word_shift a)%w with (bytes_in_word * n2w L : word a)%w
      by (rewrite Hsh; apply WORD_MULT_COMM).
    rewrite (proj2 (bool_decide_spec _) eq_refl), Hss, Hst.
    replace (LENGTH init + L <? LENGTH (init ++ old ++ x :: xs))%N with true
      by (symmetry; apply N.ltb_lt; unfold L; rewrite !LENGTH_length, !app_length; cbn [length]; lia).
    cbn [andb]. replace (x :: xs) with ([x] ++ xs) by reflexivity. unfold L. rewrite EL_LENGTH_ADD_LEMMA. cbn [app].
    sx_all3. rewrite word_sh_lsr by lia. sx_all3. rw_eval Ev'. sx_simp. sx_all3.
    rewrite Hust. cbn [negb].
    fold L. rewrite (bytes_in_word_word_shift_n2w L (conj Hg HL)), (w2n_n2w_small L HLw).
    replace (n2w L << word_shift a)%w with (bytes_in_word * n2w L : word a)%w
      by (rewrite Hsh; apply WORD_MULT_COMM).
    rewrite (proj2 (bool_decide_spec _) eq_refl), Hss, Hst.
    replace (LENGTH init + L <? LENGTH (init ++ old ++ x :: xs))%N with true
      by (symmetry; apply N.ltb_lt; unfold L; rewrite !LENGTH_length, !app_length; cbn [length]; lia).
    cbn [andb]. replace (x :: xs) with ([x] ++ xs) by reflexivity. unfold L.
    rewrite LUPDATE_LENGTH_ADD_LEMMA. cbn [app].
    sx_all3. rewrite bytes_n2w_succ.
    cbn [cont_loop]. replace (clock s + (ck2 + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    subst s5. unfold word_gen_gc_partial_move_bitmap_code in Er. cbn [list_Seq] in Er.
    autorewrite with nf in Er. cbn [clock regs memory stackSem.stack set_regs set_clock set_memory set_stack] in Er.
    autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er.
    rewrite <- !app_assoc in Er. cbn [app] in Er. rewrite !LENGTH_length, !app_length in Er |- *. cbn [length] in Er |- *.
    replace (N.of_nat (length old) + 1)%N with (N.of_nat (length old + 1)) by lia.
    sx_simp. rw_eval Er. st_fin. rewrite app_length; reflexivity.
Qed.


(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_partial_move_bitmap_code_thm" *)
Theorem word_gen_gc_partial_move_bitmap_code_thm : forall (w : word a) stack (s : state) i pa curr m dm new stack1
    i1 pa1 m1 old init conf gs rs,
  word_gen_gc_partial_move_bitmap conf (w, (stack, (i, (pa, (curr, (m, (dm, (gs, rs)))))))) = SOME (new, (stack1, (i1, (pa1, (m1, true))))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ good_dimindex a /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word curr) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ use_stack s /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\
  get_var 7 s = SOME (Word w) /\ get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
  FLOOKUP (store s) (Temp (n2w 0)) = SOME (Word gs) /\ FLOOKUP (store s) (Temp (n2w 1)) = SOME (Word rs) /\
  stackSem.stack s = init ++ old ++ stack /\ stack_space s = LENGTH init /\
  (dimindex a DIV 8 * LENGTH (stackSem.stack s) < dimword a)%N ->
  exists ck r0 r1 r2 r5 r6 r7,
    evaluate (word_gen_gc_partial_move_bitmap_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, r7); (8, Word (bytes_in_word * n2w (LENGTH (old ++ new))))])
             (set_memory m1 (set_stack (init ++ old ++ new ++ stack1) s))).
Proof.
  intros w stack s i pa curr m dm new stack1 i1 pa1 m1 old init conf gs rs H.
  exact (word_gen_gc_partial_move_bitmap_code_thm_n (w2n w + 1) w stack s i pa curr m dm new stack1 i1 pa1 m1 old init conf
           gs rs ltac:(lia) H).
Qed.


Local Theorem word_gen_gc_move_bitmap_code_thm_n : forall n (w : word a) stack (s : state) i pa ib pb curr m dm new stack1
    i1 pa1 ib1 pb1 m1 old init conf,
  (w2n w < n)%N ->
  word_gen_gc_move_bitmap conf (w, (stack, (i, (pa, (ib, (pb, (curr, (m, dm)))))))) = SOME (new, (stack1, (i1, (pa1, (ib1, (pb1, (m1, true))))))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ good_dimindex a /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word curr) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ use_stack s /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\
  get_var 7 s = SOME (Word w) /\ get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
  Temp (n2w 0) IN FDOM (store s) /\ Temp (n2w 1) IN FDOM (store s) /\
  FLOOKUP (store s) (Temp (n2w 2)) = SOME (Word pb) /\ FLOOKUP (store s) (Temp (n2w 3)) = SOME (Word ib) /\
  stackSem.stack s = init ++ old ++ stack /\ stack_space s = LENGTH init /\
  (dimindex a DIV 8 * LENGTH (stackSem.stack s) < dimword a)%N ->
  exists ck r0 r1 r2 r5 r6 r7 t0 t1,
    evaluate (word_gen_gc_move_bitmap_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, r7); (8, Word (bytes_in_word * n2w (LENGTH (old ++ new))))])
             (set_memory m1 (set_store_fld (store s |++ [(Temp (n2w 0), t0); (Temp (n2w 1), t1);
                                                  (Temp (n2w 2), Word pb1); (Temp (n2w 3), Word ib1)])
               (set_stack (init ++ old ++ new ++ stack1) s)))).
Proof.
  induction n as [|n IH] using N.peano_ind; intros w stack s i pa ib pb curr m dm new stack1 i1 pa1 ib1 pb1 m1 old init conf Hn;
    [lia|].
  intros (H & Hsl & Hws & H2 & Hls & Hg & Hsh & Hold & Hus & Hm & Hdm & Hust & H0 & H1 & H2r & H3 & H4 & H5 & H6
          & H7 & H8 & HT0 & HT1 & HT2 & HT3 & Hst & Hss & Hlen).
  unfold get_var in *; subst m dm.
  fdom_val H0 0 v0 Ev0; fdom_val H1 1 v1 Ev1; fdom_val H2r 2 v2 Ev2; fdom_val H5 5 v5 Ev5; fdom_val H6 6 v6 Ev6.
  assert (ET0 : FLOOKUP (store s) (Temp (n2w 0)) <> None) by exact HT0.
  destruct (FLOOKUP (store s) (Temp (n2w 0))) as [t0|] eqn:Et0; [clear ET0|contradiction].
  assert (ET1 : FLOOKUP (store s) (Temp (n2w 1)) <> None) by exact HT1.
  destruct (FLOOKUP (store s) (Temp (n2w 1))) as [t1|] eqn:Et1; [clear ET1|contradiction].
  rewrite word_gen_gc_move_bitmap_unroll in H.
  destruct (decide (w = n2w 0)) as [Hw0|Hw0].
  { injection H as <- <- <- <- <- <- <-. exists 0, v0, v1, v2, v5, v6, (Word w), t0, t1. rewrite N.add_0_r.
    unfold word_gen_gc_move_bitmap_code. rewrite ev_while. sx_simp.
    rewrite (lo2_true w Hg (or_introl Hw0)). sx_simp. rewrite set_clock_same, app_nil_r. cbn [app].
    rewrite <- Hst. st_fin2. }
  destruct (decide (w = n2w 1)) as [Hw1|Hw1].
  { injection H as <- <- <- <- <- <- <-. exists 0, v0, v1, v2, v5, v6, (Word w), t0, t1. rewrite N.add_0_r.
    unfold word_gen_gc_move_bitmap_code. rewrite ev_while. sx_simp.
    rewrite (lo2_true w Hg (or_intror Hw1)). sx_simp. rewrite set_clock_same, app_nil_r. cbn [app].
    rewrite <- Hst. st_fin2. }
  destruct stack as [|x xs]; [discriminate|].
  pose proof (w2n_lsr1_lt w Hw0) as Hlt.
  destruct (decide ((w && n2w 1)%w = n2w 0)) as [Ha|Ha].
  - destruct (word_gen_gc_move_bitmap conf ((w >>> 1)%w, (xs, (i, (pa, (ib, (pb, (curr, (memory s, mdomain s)))))))))
      as [[new' [st' [i' [pa' [ib' [pb' [m' c']]]]]]]|] eqn:Eb; [|discriminate].
    injection H as <- <- <- <- <- <- <- ->.
    destruct (IH (w >>> 1)%w xs
                (set_regs (regs s |+ (7, Word (w >>> 1)%w)
                                  |+ (8, Word (bytes_in_word * n2w (LENGTH (old ++ [x])))%w)) s)
                i pa ib pb curr (memory s) (mdomain s) new' st' i' pa' ib' pb' m' (old ++ [x]) init conf ltac:(lia))
      as (ck & p0 & p1 & p2 & p5 & p6 & p7 & pt0 & pt1 & Er).
    { unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
      splits; try assumption; try reflexivity;
        try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence).
      rewrite Hst, <- !app_assoc. reflexivity. }
    exists (ck + 1), p0, p1, p2, p5, p6, p7, pt0, pt1.
    unfold word_gen_gc_move_bitmap_code. rewrite ev_while. sx_simp.
    rewrite (lo2_false w Hg Hw0 Hw1). cbn [negb]. sx_simp. sx_all3. rewrite (proj2 (bool_decide_spec _) Ha).
    cbn [list_Seq].  sx_all3. rewrite word_sh_lsr by lia. sx_all3.
    rewrite bytes_n2w_succ.
    cbn [cont_loop]. replace (clock s + (ck + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    unfold word_gen_gc_move_bitmap_code in Er. cbn [list_Seq] in Er.
    autorewrite with nf in Er. cbn [clock regs memory store stackSem.stack set_regs set_clock set_memory set_stack set_store_fld] in Er.
    autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er.
    rewrite <- !app_assoc in Er. cbn [app] in Er. rewrite !LENGTH_length, app_length in Er |- *. cbn [length] in Er |- *.
    rewrite app_length in Er; cbn [length] in Er.
    replace (N.of_nat (length old) + 1)%N with (N.of_nat (length old + 1)) by lia.
    sx_simp. rw_eval Er. st_fin2.
  - destruct (word_gen_gc_move conf (x, (i, (pa, (ib, (pb, (curr, (memory s, mdomain s))))))))
      as (x1, (i1', (pa1', (ib1', (pb1', (m1', c1)))))) eqn:Emv.
    destruct (word_gen_gc_move_bitmap conf ((w >>> 1)%w, (xs, (i1', (pa1', (ib1', (pb1', (curr, (m1', mdomain s)))))))))
      as [[new' [st' [i' [pa' [ib' [pb' [m' c']]]]]]]|] eqn:Eb; [|discriminate].
    injection H as <- <- <- <- <- <- <- Hc. apply andb_prop in Hc as [-> ->].
    set (L := LENGTH old).
    assert (HL : (dimindex a DIV 8 * L < dimword a)%N).
    { eapply N.le_lt_trans; [|exact Hlen]. apply N.mul_le_mono_l. unfold L. rewrite Hst, !LENGTH_length, !app_length. lia. }
    assert (HLw : (L < dimword a)%N).
    { assert (Hk : (1 <= dimindex a DIV 8)%N) by (destruct Hg as [E|E]; rewrite E; cbn; lia). nia. }
    set (s4 := set_regs (regs s |+ (5, x) |+ (7, Word (w >>> 1)%w)) s).
    destruct (word_gen_gc_move_code_thm conf x i pa ib pb curr (memory s) (mdomain s) x1 i1' pa1' ib1' pb1' m1' s4)
      as (ck1 & q0 & q1 & q2 & q6 & qt0 & qt1 & Ev).
    { subst s4; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
      splits; try assumption; try reflexivity; try lia;
        try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence). }
    set (s5 := set_regs ((regs s4 |++ [(0, q0); (1, q1); (2, q2); (3, Word pa1'); (4, Word i1'); (5, x1); (6, q6)])
                         |+ (8, Word (bytes_in_word * n2w (LENGTH (old ++ [x1])))%w))
                 (set_memory m1' (set_store_fld (store s |++ [(Temp (n2w 0), qt0); (Temp (n2w 1), qt1);
                                       (Temp (n2w 2), Word pb1'); (Temp (n2w 3), Word ib1')])
                   (set_stack (init ++ (old ++ [x1]) ++ xs) s)))).
    destruct (IH (w >>> 1)%w xs s5 i1' pa1' ib1' pb1' curr m1' (mdomain s) new' st' i' pa' ib' pb' m' (old ++ [x1]) init conf
                ltac:(lia)) as (ck2 & p0 & p1 & p2 & p5 & p6 & p7 & pt0 & pt1 & Er).
    { subst s5 s4; unfold get_var; nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb].
      sx_dec; sx_temp.
      splits; try assumption; try reflexivity; try lia;
        try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]; sx_dec; sx_temp; congruence).
      rewrite Hst in Hlen. replace (LENGTH (init ++ (old ++ [x1]) ++ xs)) with (LENGTH (init ++ old ++ x :: xs)); [exact Hlen|]. rewrite !LENGTH_length, !app_length; cbn [length]; lia. }
    pose proof (evaluate_add_clock (ck2 + 1) (word_gen_gc_move_code conf) (set_clock (clock s4 + ck1) s4)) as Ev'.
    assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
    specialize (Ev' NONE _ (conj Ev NT)). subst s4. autorewrite with nf in Ev'.
    cbn [clock regs memory store set_regs set_clock set_memory set_store_fld] in Ev'. autorewrite with nf in Ev'. cbn [FUPDATE_LIST FOLDL] in Ev'.
    exists (ck1 + ck2 + 1), p0, p1, p2, p5, p6, p7, pt0, pt1.
    unfold word_gen_gc_move_bitmap_code. rewrite ev_while. sx_simp.
    rewrite (lo2_false w Hg Hw0 Hw1). cbn [negb]. sx_all3. rewrite (bd_F Ha).
    cbn [list_Seq]. sx_all3.
    unfold is_true in Hust. rewrite Hust. cbn [negb].
    fold L. rewrite (bytes_in_word_word_shift_n2w L (conj Hg HL)), (w2n_n2w_small L HLw).
    replace (n2w L << word_shift a)%w with (bytes_in_word * n2w L : word a)%w
      by (rewrite Hsh; apply WORD_MULT_COMM).
    rewrite (proj2 (bool_decide_spec _) eq_refl), Hss, Hst.
    replace (LENGTH init + L <? LENGTH (init ++ old ++ x :: xs))%N with true
      by (symmetry; apply N.ltb_lt; unfold L; rewrite !LENGTH_length, !app_length; cbn [length]; lia).
    cbn [andb]. replace (x :: xs) with ([x] ++ xs) by reflexivity. unfold L. rewrite EL_LENGTH_ADD_LEMMA. cbn [app].
    sx_all3. rewrite word_sh_lsr by lia. sx_all3. rw_eval Ev'. sx_simp. sx_all3.
    rewrite Hust. cbn [negb].
    fold L. rewrite (bytes_in_word_word_shift_n2w L (conj Hg HL)), (w2n_n2w_small L HLw).
    replace (n2w L << word_shift a)%w with (bytes_in_word * n2w L : word a)%w
      by (rewrite Hsh; apply WORD_MULT_COMM).
    rewrite (proj2 (bool_decide_spec _) eq_refl), Hss, Hst.
    replace (LENGTH init + L <? LENGTH (init ++ old ++ x :: xs))%N with true
      by (symmetry; apply N.ltb_lt; unfold L; rewrite !LENGTH_length, !app_length; cbn [length]; lia).
    cbn [andb]. replace (x :: xs) with ([x] ++ xs) by reflexivity. unfold L.
    rewrite LUPDATE_LENGTH_ADD_LEMMA. cbn [app].
    sx_all3. rewrite bytes_n2w_succ.
    cbn [cont_loop]. replace (clock s + (ck2 + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    subst s5. unfold word_gen_gc_move_bitmap_code in Er. cbn [list_Seq] in Er.
    autorewrite with nf in Er. cbn [clock regs memory store stackSem.stack set_regs set_clock set_memory set_stack set_store_fld] in Er.
    autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er.
    rewrite <- !app_assoc in Er. cbn [app] in Er. rewrite !LENGTH_length, !app_length in Er |- *. cbn [length] in Er |- *.
    replace (N.of_nat (length old) + 1)%N with (N.of_nat (length old + 1)) by lia.
    sx_simp. rewrite ?LENGTH_length. rw_eval2 Er. st_fin2. all: rewrite ?app_length; cbn [length]; regs_fin.
Qed.


(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_move_bitmap_code_thm" *)
Theorem word_gen_gc_move_bitmap_code_thm : forall (w : word a) stack (s : state) i pa ib pb curr m dm new stack1
    i1 pa1 ib1 pb1 m1 old init conf,
  word_gen_gc_move_bitmap conf (w, (stack, (i, (pa, (ib, (pb, (curr, (m, dm)))))))) = SOME (new, (stack1, (i1, (pa1, (ib1, (pb1, (m1, true))))))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ good_dimindex a /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word curr) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ use_stack s /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\
  get_var 7 s = SOME (Word w) /\ get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
  Temp (n2w 0) IN FDOM (store s) /\ Temp (n2w 1) IN FDOM (store s) /\
  FLOOKUP (store s) (Temp (n2w 2)) = SOME (Word pb) /\ FLOOKUP (store s) (Temp (n2w 3)) = SOME (Word ib) /\
  stackSem.stack s = init ++ old ++ stack /\ stack_space s = LENGTH init /\
  (dimindex a DIV 8 * LENGTH (stackSem.stack s) < dimword a)%N ->
  exists ck r0 r1 r2 r5 r6 r7 t0 t1,
    evaluate (word_gen_gc_move_bitmap_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, r7); (8, Word (bytes_in_word * n2w (LENGTH (old ++ new))))])
             (set_memory m1 (set_store_fld (store s |++ [(Temp (n2w 0), t0); (Temp (n2w 1), t1);
                                                  (Temp (n2w 2), Word pb1); (Temp (n2w 3), Word ib1)])
               (set_stack (init ++ old ++ new ++ stack1) s)))).
Proof.
  intros w stack s i pa ib pb curr m dm new stack1 i1 pa1 ib1 pb1 m1 old init conf H.
  exact (word_gen_gc_move_bitmap_code_thm_n (w2n w + 1) w stack s i pa ib pb curr m dm new stack1 i1 pa1 ib1 pb1 m1
           old init conf ltac:(lia) H).
Qed.

End GenBitmap.

Section GenBitmapsP.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.
#[local] Instance word_loc_inhabited_gb1 : Inhabited (word_loc a) := Word (n2w 0).

Lemma word_gen_gc_partial_move_bitmap_LENGTH conf (h : word a) stack i pa curr m dm gs rs hd ws i2 pa2 m2 c2 :
  word_gen_gc_partial_move_bitmap conf (h, (stack, (i, (pa, (curr, (m, (dm, (gs, rs)))))))) = SOME (hd, (ws, (i2, (pa2, (m2, c2))))) ->
  LENGTH stack = (LENGTH hd + LENGTH ws)%N.
Proof.
  unfold word_gen_gc_partial_move_bitmap. destruct (filter_bitmap (get_bits h) stack) as [[ts ws']|] eqn:Ef; [|discriminate].
  destruct (word_gen_gc_partial_move_roots conf _) as (wl, (i3, (pa3, (m3, c3)))).
  destruct (map_bitmap (get_bits h) wl stack) as [[hd' v2]|] eqn:Em; [|discriminate].
  intros E; injection E as <- <- _ _ _ _.
  apply filter_bitmap_IMP_LENGTH in Ef. apply map_bitmap_IMP_LENGTH in Em. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_partial_move_bitmaps_LENGTH" *)
Theorem word_gen_gc_partial_move_bitmaps_LENGTH : forall conf (w : word_loc a) stack bitmaps i pa curr m dm gs rs xs stack1 i1 pa1 m1,
  word_gen_gc_partial_move_bitmaps conf (w, (stack, (bitmaps, (i, (pa, (curr, (m, (dm, (gs, rs))))))))) =
    SOME (xs, (stack1, (i1, (pa1, (m1, true))))) ->
  LENGTH stack = (LENGTH xs + LENGTH stack1)%N.
Proof.
  intros conf w stack bitmaps i pa curr m dm gs rs xs stack1 i1 pa1 m1. unfold word_gen_gc_partial_move_bitmaps.
  destruct (full_read_bitmap bitmaps w) as [bs|]; [|discriminate].
  destruct (filter_bitmap bs stack) as [[ts ws']|] eqn:Ef; [|discriminate].
  destruct (word_gen_gc_partial_move_roots conf _) as (wl, (i3, (pa3, (m3, c3)))).
  destruct (map_bitmap bs wl stack) as [[hd' [t1 t2]]|] eqn:Em; [|discriminate].
  intros E; injection E as <- <- _ _ _ _.
  apply filter_bitmap_IMP_LENGTH in Ef. apply map_bitmap_IMP_LENGTH in Em. lia.
Qed.

Local Theorem word_gen_gc_partial_move_bitmaps_code_thm_n : forall n (w : word a) bitmaps z stack (s : state) i pa curr m dm
    new stack1 i1 pa1 m1 old init conf gs rs,
  (LENGTH bitmaps - w2n (w - n2w 1) < n)%N ->
  word_gen_gc_partial_move_bitmaps conf (Word w, (stack, (bitmaps, (i, (pa, (curr, (m, (dm, (gs, rs))))))))) =
    SOME (new, (stack1, (i1, (pa1, (m1, true))))) /\
  (LENGTH bitmaps < dimword a - 1)%N /\ good_dimindex a /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ good_dimindex a /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word curr) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ stackSem.bitmaps s = bitmaps /\ use_stack s /\
  get_var 0 s = SOME (Word z) /\ z <> n2w 0 /\
  1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\ 7 IN FDOM (regs s) /\
  get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
  get_var 9 s = SOME (Word (w - n2w 1)) /\
  FLOOKUP (store s) (Temp (n2w 0)) = SOME (Word gs) /\ FLOOKUP (store s) (Temp (n2w 1)) = SOME (Word rs) /\
  stackSem.stack s = init ++ old ++ stack /\ stack_space s = LENGTH init /\
  (dimindex a DIV 8 * LENGTH (stackSem.stack s) < dimword a)%N ->
  exists ck r0 r1 r2 r5 r6 r7 r9,
    evaluate (word_gen_gc_partial_move_bitmaps_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, r7); (8, Word (bytes_in_word * n2w (LENGTH (old ++ new)))); (9, r9)])
             (set_memory m1 (set_stack (init ++ old ++ new ++ stack1) s))).
Proof.
  induction n as [|n IH] using N.peano_ind;
    intros w bitmaps z stack s i pa curr m dm new stack1 i1 pa1 m1 old init conf gs rs Hn; [lia|].
  intros (H & Hlb & Hg & Hsl & Hws & H2 & Hls & _ & Hsh & Hold & Hus & Hm & Hdm & Hbm & Hust & H0 & Hz & H1 & H2r
          & H3 & H4 & H5 & H6 & H7 & H8 & H9 & HT0 & HT1 & Hst & Hss & Hlen).
  unfold get_var in *; subst m dm bitmaps.
  fdom_val H1 1 v1 Ev1; fdom_val H2r 2 v2 Ev2; fdom_val H5 5 v5 Ev5; fdom_val H6 6 v6 Ev6; fdom_val H7 7 v7 Ev7.
  rewrite (word_gen_gc_partial_move_bitmaps_unroll conf w stack (stackSem.bitmaps s) i pa curr (memory s) (mdomain s) gs rs _
             (conj H (conj Hlb Hg))) in H.
  destruct (DROP (w2n (w - n2w 1)) (stackSem.bitmaps s)) as [|h t] eqn:Ed; [discriminate|].
  pose proof (DROP_EL _ _ _ _ Ed) as Eel. destruct (DROP_cons_succ _ _ _ _ Ed) as [Ed' Hlt].
  destruct (word_gen_gc_partial_move_bitmap conf (h, (stack, (i, (pa, (curr, (memory s, (mdomain s, (gs, rs)))))))))
    as [[hd [ws [i2 [pa2 [m2 c2]]]]]|] eqn:Eb; [|discriminate].
  assert (c2 = true) as ->.
  { destruct (negb (word_msb h)); [injection H as _ _ _ _ _ E; exact E|].
    destruct (word_gen_gc_partial_move_bitmaps conf _) as [[hd3 [ws3 [i3 [pa3 [m3 c3]]]]]|]; [|discriminate].
    injection H as _ _ _ _ _ E. apply andb_prop in E; tauto. }
  pose proof (word_gen_gc_partial_move_bitmap_LENGTH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Eb) as HlenB.
  set (s2 := set_regs (regs s |+ (7, Word h)) s).
  destruct (word_gen_gc_partial_move_bitmap_code_thm h stack s2 i pa curr (memory s) (mdomain s) hd ws i2 pa2 m2 old init conf gs rs)
    as (ck1 & q0 & q1 & q2 & q5 & q6 & q7 & Ev).
  { subst s2; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
    splits; try assumption; try reflexivity;
      unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
  assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
  assert (Hlb' : (LENGTH (stackSem.bitmaps s) <=? w2n (w - n2w 1))%N = false) by (apply N.leb_gt; lia).
  destruct (word_msb h) eqn:Hmsb; cbn [negb] in H.
  - destruct (word_gen_gc_partial_move_bitmaps conf (Word (w + n2w 1)%w, (ws, (stackSem.bitmaps s, (i2, (pa2, (curr, (m2, (mdomain s, (gs, rs))))))))))
      as [[hd3 [ws3 [i3 [pa3 [m3 c3]]]]]|] eqn:Eb3; [|discriminate].
    injection H as <- <- <- <- <- Hc3. cbn [andb] in Hc3. subst c3.
    assert (Hnz : (h >>> (dimindex a - 1))%w <> n2w 0) by (apply word_msb_IFF_lsr_EQ_0; exact Hmsb).
    assert (Ew : w = n2w (w2n (w - n2w 1) + 1)) by (rewrite <- word_add_n2w, n2w_w2n; word_ring).
    assert (Hk1 : (w2n (w - n2w 1) + 1 < dimword a)%N) by lia.
    assert (Hm1 : w2n (w + n2w 1 - n2w 1) = (w2n (w - n2w 1) + 1)%N)
      by (replace (w + n2w 1 - n2w 1)%w with w by word_ring; rewrite Ew at 1; apply w2n_n2w_small; exact Hk1).
    set (s5 := set_regs ((regs s2 |++ [(0, q0); (1, q1); (2, q2); (3, Word pa2); (4, Word i2); (5, q5); (6, q6);
                                       (7, q7); (8, Word (bytes_in_word * n2w (LENGTH (old ++ hd)))%w)])
                         |+ (0, Word h) |+ (9, Word w) |+ (0, Word (h >>> (dimindex a - 1))%w))
                 (set_memory m2 (set_stack (init ++ (old ++ hd) ++ ws) s))).
    destruct (IH (w + n2w 1)%w (stackSem.bitmaps s) (h >>> (dimindex a - 1))%w ws s5 i2 pa2 curr m2 (mdomain s)
                hd3 ws3 i3 pa3 m3 (old ++ hd) init conf gs rs ltac:(rewrite Hm1; lia))
      as (ck2 & p0 & p1 & p2 & p5 & p6 & p7 & p9 & Er).
    { subst s5 s2; unfold get_var; nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
      splits; try assumption; try reflexivity; try lia;
        try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence).
      - do 2 f_equal. word_ring.
      - rewrite Hst in Hlen. replace (LENGTH (init ++ (old ++ hd) ++ ws)) with (LENGTH (init ++ old ++ stack)); [exact Hlen|].
        rewrite !LENGTH_length, !app_length. rewrite !LENGTH_length in HlenB. lia. }
    pose proof (evaluate_add_clock (ck2 + 1) (word_gen_gc_partial_move_bitmap_code conf) (set_clock (clock s2 + ck1) s2)) as Ev'.
    specialize (Ev' NONE _ (conj Ev NT)). subst s2. autorewrite with nf in Ev'.
    cbn [clock regs memory set_regs set_clock set_memory set_stack] in Ev'. autorewrite with nf in Ev'.
    cbn [FUPDATE_LIST FOLDL] in Ev'.
    exists (ck1 + ck2 + 1), p0, p1, p2, p5, p6, p7, p9.
    unfold word_gen_gc_partial_move_bitmaps_code. rewrite ev_while. sx_simp. rewrite WORD_AND_IDEM, (bd_F Hz). cbn [negb].
    cbn [list_Seq]. sx_all3. rewrite Hust, Hlb', Eel. cbn [negb orb]. sx_all3.
    rw_eval Ev'. sx_simp. sx_all3. rewrite Hust, Hlb', Eel. cbn [negb orb]. sx_all3.
    rewrite word_sh_lsr by lia. sx_all3. sx_simp.
    cbn [cont_loop]. replace (clock s + (ck2 + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    sx_simp.
    subst s5. unfold word_gen_gc_partial_move_bitmaps_code in Er. cbn [list_Seq] in Er.
    autorewrite with nf in Er. cbn [clock regs memory stackSem.stack set_regs set_clock set_memory set_stack] in Er.
    autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er. rewrite <- !app_assoc in Er.
    replace (w - n2w 1 + n2w 1)%w with w by word_ring.
    rw_eval Er. st_fin. rewrite <- !app_assoc; reflexivity.
  - injection H as <- <- <- <- <-.
    pose proof (evaluate_add_clock 1 (word_gen_gc_partial_move_bitmap_code conf) (set_clock (clock s2 + ck1) s2)) as Ev'.
    specialize (Ev' NONE _ (conj Ev NT)). subst s2. autorewrite with nf in Ev'.
    cbn [clock regs memory set_regs set_clock set_memory set_stack] in Ev'. autorewrite with nf in Ev'.
    cbn [FUPDATE_LIST FOLDL] in Ev'.
    assert (Hz0 : (h >>> (dimindex a - 1))%w = n2w 0).
    { destruct (decide ((h >>> (dimindex a - 1))%w = n2w 0)) as [E|E]; [exact E|].
      apply word_msb_IFF_lsr_EQ_0 in E. unfold is_true in E. congruence. }
    exists (ck1 + 1), (Word (h >>> (dimindex a - 1))%w), q1, q2, q5, q6, q7, (Word w).
    unfold word_gen_gc_partial_move_bitmaps_code. rewrite ev_while. sx_simp. rewrite WORD_AND_IDEM, (bd_F Hz). cbn [negb].
    cbn [list_Seq]. sx_all3. rewrite Hust, Hlb', Eel. cbn [negb orb]. sx_all3.
    rw_eval Ev'. sx_simp. sx_all3. rewrite Hust, Hlb', Eel. cbn [negb orb]. sx_all3.
    rewrite word_sh_lsr by lia. sx_all3. rewrite Hz0.
    sx_simp. rewrite ev_while. sx_simp. rewrite ?WORD_AND_IDEM. sx_simp.
    cbn [cont_loop]. replace (clock s + 1 =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    replace (w - n2w 1 + n2w 1)%w with w by word_ring. replace (clock s + 1 - 1)%N with (clock s) by lia.
    st_fin.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_partial_move_bitmaps_code_thm" *)
Theorem word_gen_gc_partial_move_bitmaps_code_thm : forall (w : word a) bitmaps z stack (s : state) i pa curr m dm
    new stack1 i1 pa1 m1 old init conf gs rs,
  word_gen_gc_partial_move_bitmaps conf (Word w, (stack, (bitmaps, (i, (pa, (curr, (m, (dm, (gs, rs))))))))) =
    SOME (new, (stack1, (i1, (pa1, (m1, true))))) /\
  (LENGTH bitmaps < dimword a - 1)%N /\ good_dimindex a /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ good_dimindex a /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word curr) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ stackSem.bitmaps s = bitmaps /\ use_stack s /\
  get_var 0 s = SOME (Word z) /\ z <> n2w 0 /\
  1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\ 7 IN FDOM (regs s) /\
  get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
  get_var 9 s = SOME (Word (w - n2w 1)) /\
  FLOOKUP (store s) (Temp (n2w 0)) = SOME (Word gs) /\ FLOOKUP (store s) (Temp (n2w 1)) = SOME (Word rs) /\
  stackSem.stack s = init ++ old ++ stack /\ stack_space s = LENGTH init /\
  (dimindex a DIV 8 * LENGTH (stackSem.stack s) < dimword a)%N ->
  exists ck r0 r1 r2 r5 r6 r7 r9,
    evaluate (word_gen_gc_partial_move_bitmaps_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, r7); (8, Word (bytes_in_word * n2w (LENGTH (old ++ new)))); (9, r9)])
             (set_memory m1 (set_stack (init ++ old ++ new ++ stack1) s))).
Proof.
  intros w bitmaps z stack s i pa curr m dm new stack1 i1 pa1 m1 old init conf gs rs H.
  exact (word_gen_gc_partial_move_bitmaps_code_thm_n (LENGTH bitmaps - w2n (w - n2w 1) + 1) w bitmaps z stack s i pa curr m dm
           new stack1 i1 pa1 m1 old init conf gs rs ltac:(lia) H).
Qed.

Local Theorem word_gen_gc_partial_move_roots_bitmaps_code_thm_n : forall n stack bitmaps (s : state) i pa curr m dm
    stack1 i1 pa1 m1 old init conf gs rs,
  (LENGTH stack < n)%N ->
  word_gen_gc_partial_move_roots_bitmaps conf (stack, (bitmaps, (i, (pa, (curr, (m, (dm, (gs, rs)))))))) =
    (stack1, (i1, (pa1, (m1, true)))) /\
  (LENGTH bitmaps < dimword a - 1)%N /\ good_dimindex a /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ good_dimindex a /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word curr) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ stackSem.bitmaps s = bitmaps /\ use_stack s /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\ 7 IN FDOM (regs s) /\
  get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
  get_var 9 s = SOME (HD stack) /\
  FLOOKUP (store s) (Temp (n2w 0)) = SOME (Word gs) /\ FLOOKUP (store s) (Temp (n2w 1)) = SOME (Word rs) /\
  stackSem.stack s = init ++ old ++ stack /\ stack_space s = LENGTH init /\
  (dimindex a DIV 8 * LENGTH (stackSem.stack s) < dimword a)%N ->
  exists ck r0 r1 r2 r5 r6 r7 r8,
    evaluate (word_gen_gc_partial_move_roots_bitmaps_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, r7); (8, r8); (9, Word (n2w 0))])
             (set_memory m1 (set_stack (init ++ old ++ stack1) s))).
Proof.
  induction n as [|n IH] using N.peano_ind;
    intros stack bitmaps s i pa curr m dm stack1 i1 pa1 m1 old init conf gs rs Hn; [lia|].
  intros (H & Hlb & Hg & Hsl & Hws & H2 & Hls & _ & Hsh & Hold & Hus & Hm & Hdm & Hbm & Hust & H0 & H1 & H2r
          & H3 & H4 & H5 & H6 & H7 & H8 & H9 & HT0 & HT1 & Hst & Hss & Hlen).
  unfold get_var in *; subst m dm bitmaps.
  fdom_val H0 0 v0 Ev0; fdom_val H1 1 v1 Ev1; fdom_val H2r 2 v2 Ev2; fdom_val H5 5 v5 Ev5; fdom_val H6 6 v6 Ev6;
    fdom_val H7 7 v7 Ev7.
  rewrite (word_gen_gc_partial_move_roots_bitmaps_unroll _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) in H.
  destruct stack as [|hd stack]; [injection H as _ _ _ _ E; discriminate|].
  cbn [HD] in H9.
  destruct (decide (hd = Word (n2w 0))) as [->|Hhd].
  { injection H as <- <- <- <- Hc. apply bool_decide_spec in Hc. subst stack.
    exists 0, v0, v1, v2, v5, v6, v7, (Word (bytes_in_word * n2w (LENGTH old))%w). rewrite N.add_0_r.
    unfold word_gen_gc_partial_move_roots_bitmaps_code. rewrite ev_while. sx_simp. rewrite ?WORD_AND_IDEM. sx_simp.
    rewrite set_clock_same, <- Hst. st_fin. }
  destruct (word_gen_gc_partial_move_bitmaps conf (hd, (stack, (stackSem.bitmaps s, (i, (pa, (curr, (memory s, (mdomain s, (gs, rs))))))))))
    as [[x0 [x1 [x2 [x3 [x4 c2]]]]]|] eqn:Eb; [|injection H as _ _ _ _ E; discriminate].
  destruct (word_gen_gc_partial_move_roots_bitmaps conf (x1, (stackSem.bitmaps s, (x2, (x3, (curr, (x4, (mdomain s, (gs, rs)))))))))
    as (st', (i', (pa', (m', c3)))) eqn:Er3.
  injection H as <- <- <- <- Hc. apply andb_prop in Hc as [-> ->].
  destruct hd as [c|l1 l2]; [|unfold word_gen_gc_partial_move_bitmaps, full_read_bitmap in Eb; discriminate].
  assert (Hc0 : c <> n2w 0) by (intros ->; exact (Hhd eq_refl)).
  pose proof (word_gen_gc_partial_move_bitmaps_LENGTH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Eb) as HlenB.
  destruct x1 as [|h t].
  { unfold word_gen_gc_partial_move_roots_bitmaps in Er3.
    rewrite (proj1 enc_stack_def) in Er3. injection Er3 as _ _ _ _ E; discriminate. }
  set (s2 := set_regs (regs s |+ (0, Word c) |+ (9, Word (c - n2w 1))
                              |+ (8, Word (bytes_in_word * n2w (LENGTH old + 1)))) s).
  destruct (word_gen_gc_partial_move_bitmaps_code_thm c (stackSem.bitmaps s) c stack s2 i pa curr (memory s) (mdomain s)
              x0 (h :: t) x2 x3 x4 (old ++ [Word c]) init conf gs rs) as (ck1 & q0 & q1 & q2 & q5 & q6 & q7 & q9 & Ev).
  { subst s2; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
    splits; try assumption; try reflexivity;
      try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence).
    - rewrite !LENGTH_length, app_length. cbn [length]. do 4 f_equal. lia.
    - rewrite Hst, <- !app_assoc. reflexivity. }
  set (L1 := (LENGTH old + 1 + LENGTH x0)%N).
  assert (EL1 : LENGTH ((old ++ [Word c]) ++ x0) = L1) by (unfold L1; rewrite !LENGTH_length, !app_length; cbn [length]; lia).
  rewrite EL1 in Ev.
  assert (Hst' : LENGTH (stackSem.stack s) = (LENGTH init + L1 + LENGTH (h :: t))%N).
  { rewrite Hst. unfold L1. rewrite !LENGTH_length, !app_length in *. cbn [length] in *. lia. }
  assert (HL1 : (dimindex a DIV 8 * L1 < dimword a)%N).
  { eapply N.le_lt_trans; [|exact Hlen]. apply N.mul_le_mono_l. rewrite Hst'. lia. }
  assert (HL1w : (L1 < dimword a)%N).
  { assert (Hk : (1 <= dimindex a DIV 8)%N) by (destruct Hg as [E|E]; rewrite E; cbn; lia). nia. }
  assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
  set (s8 := set_regs ((regs s2 |++ [(0, q0); (1, q1); (2, q2); (3, Word x3); (4, Word x2); (5, q5); (6, q6);
                                     (7, q7); (8, Word (bytes_in_word * n2w L1)%w); (9, q9)]) |+ (9, h))
               (set_memory x4 (set_stack (init ++ (old ++ Word c :: x0) ++ h :: t) s))).
  destruct (IH (h :: t) (stackSem.bitmaps s) s8 x2 x3 curr x4 (mdomain s) st' i' pa' m' (old ++ Word c :: x0) init conf gs rs)
    as (ck2 & p0 & p1 & p2 & p5 & p6 & p7 & p8 & Er).
  { rewrite !LENGTH_length in *. cbn [length] in *. lia. }
  { subst s8 s2; unfold get_var; nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb HD].
    splits; try assumption; try reflexivity; try lia;
      try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence).
    - do 4 f_equal. unfold L1. rewrite !LENGTH_length, !app_length. cbn [length]. lia.
    - rewrite Hst in Hlen. replace (LENGTH (init ++ (old ++ Word c :: x0) ++ h :: t)) with (LENGTH (init ++ old ++ Word c :: stack));
        [exact Hlen|]. rewrite !LENGTH_length, !app_length in *. cbn [length] in *. lia. }
  pose proof (evaluate_add_clock (ck2 + 1) (word_gen_gc_partial_move_bitmaps_code conf) (set_clock (clock s2 + ck1) s2)) as Ev'.
  specialize (Ev' NONE _ (conj Ev NT)). subst s2. autorewrite with nf in Ev'.
  cbn [clock regs memory set_regs set_clock set_memory set_stack] in Ev'. autorewrite with nf in Ev'.
  cbn [FUPDATE_LIST FOLDL] in Ev'.
  exists (ck1 + ck2 + 1), p0, p1, p2, p5, p6, p7, p8.
  unfold word_gen_gc_partial_move_roots_bitmaps_code. rewrite ev_while. sx_simp. rewrite WORD_AND_IDEM, (bd_F Hc0). cbn [negb].
  cbn [list_Seq]. sx_all3. rewrite bytes_n2w_succ. rw_eval Ev'. sx_simp. sx_all3.
  unfold is_true in Hust. rewrite Hust. cbn [negb].
  rewrite (bytes_in_word_word_shift_n2w L1 (conj Hg HL1)), (w2n_n2w_small L1 HL1w).
  replace (n2w L1 << word_shift a)%w with (bytes_in_word * n2w L1 : word a)%w by (rewrite Hsh; apply WORD_MULT_COMM).
  rewrite (proj2 (bool_decide_spec _) eq_refl), Hss.
  replace (init ++ (old ++ [Word c]) ++ x0 ++ h :: t) with ((init ++ (old ++ [Word c]) ++ x0) ++ h :: t)
    by (rewrite <- !app_assoc; reflexivity).
  assert (Hl2 : LENGTH (init ++ (old ++ [Word c]) ++ x0) = (LENGTH init + L1)%N)
    by (rewrite <- EL1, !LENGTH_length, !app_length; lia).
  replace (LENGTH init + L1 <? LENGTH ((init ++ (old ++ [Word c]) ++ x0) ++ h :: t))%N with true
    by (symmetry; apply N.ltb_lt; rewrite !LENGTH_length, !app_length in *; cbn [length] in *; lia).
  cbn [andb]. rewrite (EL_LENGTH_ADD_LEMMA_2 _ _ h t Hl2).
  sx_all3. sx_simp.
  cbn [cont_loop]. replace (clock s + (ck2 + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
  sx_simp.
  subst s8. unfold word_gen_gc_partial_move_roots_bitmaps_code in Er. cbn [list_Seq] in Er.
  autorewrite with nf in Er. cbn [clock regs memory stackSem.stack set_regs set_clock set_memory set_stack] in Er.
  autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er. rewrite <- !app_assoc in Er |- *. cbn [app] in Er |- *.
  rw_eval2 Er. st_fin.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_partial_move_roots_bitmaps_code_thm" *)
Theorem word_gen_gc_partial_move_roots_bitmaps_code_thm : forall stack bitmaps (s : state) i pa curr m dm
    stack1 i1 pa1 m1 old init conf gs rs,
  word_gen_gc_partial_move_roots_bitmaps conf (stack, (bitmaps, (i, (pa, (curr, (m, (dm, (gs, rs)))))))) =
    (stack1, (i1, (pa1, (m1, true)))) /\
  (LENGTH bitmaps < dimword a - 1)%N /\ good_dimindex a /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ good_dimindex a /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word curr) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ stackSem.bitmaps s = bitmaps /\ use_stack s /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\ 7 IN FDOM (regs s) /\
  get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
  get_var 9 s = SOME (HD stack) /\
  FLOOKUP (store s) (Temp (n2w 0)) = SOME (Word gs) /\ FLOOKUP (store s) (Temp (n2w 1)) = SOME (Word rs) /\
  stackSem.stack s = init ++ old ++ stack /\ stack_space s = LENGTH init /\
  (dimindex a DIV 8 * LENGTH (stackSem.stack s) < dimword a)%N ->
  exists ck r0 r1 r2 r5 r6 r7 r8,
    evaluate (word_gen_gc_partial_move_roots_bitmaps_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, r7); (8, r8); (9, Word (n2w 0))])
             (set_memory m1 (set_stack (init ++ old ++ stack1) s))).
Proof.
  intros stack bitmaps s i pa curr m dm stack1 i1 pa1 m1 old init conf gs rs H.
  exact (word_gen_gc_partial_move_roots_bitmaps_code_thm_n (LENGTH stack + 1) stack bitmaps s i pa curr m dm
           stack1 i1 pa1 m1 old init conf gs rs ltac:(lia) H).
Qed.

End GenBitmapsP.

Section GenBitmapsG.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.
#[local] Instance word_loc_inhabited_gb2 : Inhabited (word_loc a) := Word (n2w 0).

Lemma word_gen_gc_move_bitmap_LENGTH conf (h : word a) stack i pa ib pb curr m dm hd ws i2 pa2 ib2 pb2 m2 c2 :
  word_gen_gc_move_bitmap conf (h, (stack, (i, (pa, (ib, (pb, (curr, (m, dm)))))))) =
    SOME (hd, (ws, (i2, (pa2, (ib2, (pb2, (m2, c2))))))) ->
  LENGTH stack = (LENGTH hd + LENGTH ws)%N.
Proof.
  unfold word_gen_gc_move_bitmap. destruct (filter_bitmap (get_bits h) stack) as [[ts ws']|] eqn:Ef; [|discriminate].
  destruct (word_gen_gc_move_roots conf _) as (wl, (i3, (pa3, (ib3, (pb3, (m3, c3)))))).
  destruct (map_bitmap (get_bits h) wl stack) as [[hd' v2]|] eqn:Em; [|discriminate].
  intros E; injection E as <- <- _ _ _ _ _ _.
  apply filter_bitmap_IMP_LENGTH in Ef. apply map_bitmap_IMP_LENGTH in Em. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_move_bitmaps_LENGTH" *)
Theorem word_gen_gc_move_bitmaps_LENGTH : forall conf (w : word_loc a) stack bitmaps i pa ib pb curr m dm xs stack1
    i1 pa1 ib1 pb1 m1,
  word_gen_gc_move_bitmaps conf (w, (stack, (bitmaps, (i, (pa, (ib, (pb, (curr, (m, dm))))))))) =
    SOME (xs, (stack1, (i1, (pa1, (ib1, (pb1, (m1, true))))))) ->
  LENGTH stack = (LENGTH xs + LENGTH stack1)%N.
Proof.
  intros conf w stack bitmaps i pa ib pb curr m dm xs stack1 i1 pa1 ib1 pb1 m1. unfold word_gen_gc_move_bitmaps.
  destruct (full_read_bitmap bitmaps w) as [bs|]; [|discriminate].
  destruct (filter_bitmap bs stack) as [[ts ws']|] eqn:Ef; [|discriminate].
  destruct (word_gen_gc_move_roots conf _) as (wl, (i3, (pa3, (ib3, (pb3, (m3, c3)))))).
  destruct (map_bitmap bs wl stack) as [[hd' [t1 t2]]|] eqn:Em; [|discriminate].
  intros E; injection E as <- <- _ _ _ _ _ _.
  apply filter_bitmap_IMP_LENGTH in Ef. apply map_bitmap_IMP_LENGTH in Em. lia.
Qed.

Local Theorem word_gen_gc_move_bitmaps_code_thm_n : forall n (w : word a) bitmaps z stack (s : state) i pa ib pb curr m dm
    new stack1 i1 pa1 ib1 pb1 m1 old init conf,
  (LENGTH bitmaps - w2n (w - n2w 1) < n)%N ->
  word_gen_gc_move_bitmaps conf (Word w, (stack, (bitmaps, (i, (pa, (ib, (pb, (curr, (m, dm))))))))) =
    SOME (new, (stack1, (i1, (pa1, (ib1, (pb1, (m1, true))))))) /\
  (LENGTH bitmaps < dimword a - 1)%N /\ good_dimindex a /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ good_dimindex a /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word curr) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ stackSem.bitmaps s = bitmaps /\ use_stack s /\
  get_var 0 s = SOME (Word z) /\ z <> n2w 0 /\
  1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\ 7 IN FDOM (regs s) /\
  get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
  get_var 9 s = SOME (Word (w - n2w 1)) /\
  Temp (n2w 0) IN FDOM (store s) /\ Temp (n2w 1) IN FDOM (store s) /\
  FLOOKUP (store s) (Temp (n2w 2)) = SOME (Word pb) /\ FLOOKUP (store s) (Temp (n2w 3)) = SOME (Word ib) /\
  stackSem.stack s = init ++ old ++ stack /\ stack_space s = LENGTH init /\
  (dimindex a DIV 8 * LENGTH (stackSem.stack s) < dimword a)%N ->
  exists ck r0 r1 r2 r5 r6 r7 r9 t0 t1,
    evaluate (word_gen_gc_move_bitmaps_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, r7); (8, Word (bytes_in_word * n2w (LENGTH (old ++ new)))); (9, r9)])
             (set_memory m1 (set_store_fld (store s |++ [(Temp (n2w 0), t0); (Temp (n2w 1), t1);
                                                  (Temp (n2w 2), Word pb1); (Temp (n2w 3), Word ib1)])
               (set_stack (init ++ old ++ new ++ stack1) s)))).
Proof.
  induction n as [|n IH] using N.peano_ind;
    intros w bitmaps z stack s i pa ib pb curr m dm new stack1 i1 pa1 ib1 pb1 m1 old init conf Hn; [lia|].
  intros (H & Hlb & Hg & Hsl & Hws & H2 & Hls & _ & Hsh & Hold & Hus & Hm & Hdm & Hbm & Hust & H0 & Hz & H1 & H2r
          & H3 & H4 & H5 & H6 & H7 & H8 & H9 & HT0 & HT1 & HT2 & HT3 & Hst & Hss & Hlen).
  unfold get_var in *; subst m dm bitmaps.
  fdom_val H1 1 v1 Ev1; fdom_val H2r 2 v2 Ev2; fdom_val H5 5 v5 Ev5; fdom_val H6 6 v6 Ev6; fdom_val H7 7 v7 Ev7.
  assert (ET0 : FLOOKUP (store s) (Temp (n2w 0)) <> None) by exact HT0.
  destruct (FLOOKUP (store s) (Temp (n2w 0))) as [t0|] eqn:Et0; [clear ET0|contradiction].
  assert (ET1 : FLOOKUP (store s) (Temp (n2w 1)) <> None) by exact HT1.
  destruct (FLOOKUP (store s) (Temp (n2w 1))) as [t1|] eqn:Et1; [clear ET1|contradiction].
  rewrite (word_gen_gc_move_bitmaps_unroll conf w stack (stackSem.bitmaps s) i pa ib pb curr (memory s) (mdomain s) _
             (conj H (conj Hlb Hg))) in H.
  destruct (DROP (w2n (w - n2w 1)) (stackSem.bitmaps s)) as [|h t] eqn:Ed; [discriminate|].
  pose proof (DROP_EL _ _ _ _ Ed) as Eel. destruct (DROP_cons_succ _ _ _ _ Ed) as [Ed' Hlt].
  destruct (word_gen_gc_move_bitmap conf (h, (stack, (i, (pa, (ib, (pb, (curr, (memory s, mdomain s)))))))))
    as [[hd [ws [i2 [pa2 [ib2 [pb2 [m2 c2]]]]]]]|] eqn:Eb; [|discriminate].
  assert (c2 = true) as ->.
  { destruct (negb (word_msb h)); [injection H as _ _ _ _ _ _ _ E; exact E|].
    destruct (word_gen_gc_move_bitmaps conf _) as [[hd3 [ws3 [i3 [pa3 [ib3 [pb3 [m3 c3]]]]]]]|]; [|discriminate].
    injection H as _ _ _ _ _ _ _ E. apply andb_prop in E; tauto. }
  pose proof (word_gen_gc_move_bitmap_LENGTH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Eb) as HlenB.
  set (s2 := set_regs (regs s |+ (7, Word h)) s).
  destruct (word_gen_gc_move_bitmap_code_thm h stack s2 i pa ib pb curr (memory s) (mdomain s) hd ws i2 pa2 ib2 pb2 m2 old init conf)
    as (ck1 & q0 & q1 & q2 & q5 & q6 & q7 & qt0 & qt1 & Ev).
  { subst s2; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
    splits; try assumption; try reflexivity;
      try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence). }
  assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
  assert (Hlb' : (LENGTH (stackSem.bitmaps s) <=? w2n (w - n2w 1))%N = false) by (apply N.leb_gt; lia).
  destruct (word_msb h) eqn:Hmsb; cbn [negb] in H.
  - destruct (word_gen_gc_move_bitmaps conf (Word (w + n2w 1)%w, (ws, (stackSem.bitmaps s, (i2, (pa2, (ib2, (pb2, (curr, (m2, mdomain s))))))))))
      as [[hd3 [ws3 [i3 [pa3 [ib3 [pb3 [m3 c3]]]]]]]|] eqn:Eb3; [|discriminate].
    injection H as <- <- <- <- <- <- <- Hc3. cbn [andb] in Hc3. subst c3.
    assert (Hnz : (h >>> (dimindex a - 1))%w <> n2w 0) by (apply word_msb_IFF_lsr_EQ_0; exact Hmsb).
    assert (Ew : w = n2w (w2n (w - n2w 1) + 1)) by (rewrite <- word_add_n2w, n2w_w2n; word_ring).
    assert (Hk1 : (w2n (w - n2w 1) + 1 < dimword a)%N) by lia.
    assert (Hm1 : w2n (w + n2w 1 - n2w 1) = (w2n (w - n2w 1) + 1)%N)
      by (replace (w + n2w 1 - n2w 1)%w with w by word_ring; rewrite Ew at 1; apply w2n_n2w_small; exact Hk1).
    set (s5 := set_regs ((regs s2 |++ [(0, q0); (1, q1); (2, q2); (3, Word pa2); (4, Word i2); (5, q5); (6, q6);
                                       (7, q7); (8, Word (bytes_in_word * n2w (LENGTH (old ++ hd)))%w)])
                         |+ (0, Word h) |+ (9, Word w) |+ (0, Word (h >>> (dimindex a - 1))%w))
                 (set_memory m2 (set_store_fld (store s |++ [(Temp (n2w 0), qt0); (Temp (n2w 1), qt1);
                                       (Temp (n2w 2), Word pb2); (Temp (n2w 3), Word ib2)])
                   (set_stack (init ++ (old ++ hd) ++ ws) s)))).
    destruct (IH (w + n2w 1)%w (stackSem.bitmaps s) (h >>> (dimindex a - 1))%w ws s5 i2 pa2 ib2 pb2 curr m2 (mdomain s)
                hd3 ws3 i3 pa3 ib3 pb3 m3 (old ++ hd) init conf ltac:(rewrite Hm1; lia))
      as (ck2 & p0 & p1 & p2 & p5 & p6 & p7 & p9 & pt0 & pt1 & Er).
    { subst s5 s2; unfold get_var; nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb].
      sx_dec; sx_temp.
      splits; try assumption; try reflexivity; try lia;
        try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]; sx_dec; sx_temp; congruence).
      - do 2 f_equal. word_ring.
      - rewrite Hst in Hlen. replace (LENGTH (init ++ (old ++ hd) ++ ws)) with (LENGTH (init ++ old ++ stack)); [exact Hlen|].
        rewrite !LENGTH_length, !app_length. rewrite !LENGTH_length in HlenB. lia. }
    pose proof (evaluate_add_clock (ck2 + 1) (word_gen_gc_move_bitmap_code conf) (set_clock (clock s2 + ck1) s2)) as Ev'.
    specialize (Ev' NONE _ (conj Ev NT)). subst s2. autorewrite with nf in Ev'.
    cbn [clock regs memory store set_regs set_clock set_memory set_stack set_store_fld] in Ev'. autorewrite with nf in Ev'.
    cbn [FUPDATE_LIST FOLDL] in Ev'.
    exists (ck1 + ck2 + 1), p0, p1, p2, p5, p6, p7, p9, pt0, pt1.
    unfold word_gen_gc_move_bitmaps_code. rewrite ev_while. sx_simp. rewrite WORD_AND_IDEM, (bd_F Hz). cbn [negb].
    cbn [list_Seq]. sx_all3. rewrite Hust, Hlb', Eel. cbn [negb orb]. sx_all3.
    rw_eval Ev'. sx_simp. sx_all3. rewrite Hust, Hlb', Eel. cbn [negb orb]. sx_all3.
    rewrite word_sh_lsr by lia. sx_all3. sx_simp.
    cbn [cont_loop]. replace (clock s + (ck2 + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    sx_simp.
    subst s5. unfold word_gen_gc_move_bitmaps_code in Er. cbn [list_Seq] in Er.
    autorewrite with nf in Er. cbn [clock regs memory store stackSem.stack set_regs set_clock set_memory set_stack set_store_fld] in Er.
    autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er. rewrite <- !app_assoc in Er.
    replace (w - n2w 1 + n2w 1)%w with w by word_ring.
    rw_eval2 Er. st_fin2. all: rewrite <- !app_assoc; reflexivity.
  - injection H as <- <- <- <- <- <- <-.
    pose proof (evaluate_add_clock 1 (word_gen_gc_move_bitmap_code conf) (set_clock (clock s2 + ck1) s2)) as Ev'.
    specialize (Ev' NONE _ (conj Ev NT)). subst s2. autorewrite with nf in Ev'.
    cbn [clock regs memory store set_regs set_clock set_memory set_stack set_store_fld] in Ev'. autorewrite with nf in Ev'.
    cbn [FUPDATE_LIST FOLDL] in Ev'.
    assert (Hz0 : (h >>> (dimindex a - 1))%w = n2w 0).
    { destruct (decide ((h >>> (dimindex a - 1))%w = n2w 0)) as [E|E]; [exact E|].
      apply word_msb_IFF_lsr_EQ_0 in E. unfold is_true in E. congruence. }
    exists (ck1 + 1), (Word (h >>> (dimindex a - 1))%w), q1, q2, q5, q6, q7, (Word w), qt0, qt1.
    unfold word_gen_gc_move_bitmaps_code. rewrite ev_while. sx_simp. rewrite WORD_AND_IDEM, (bd_F Hz). cbn [negb].
    cbn [list_Seq]. sx_all3. rewrite Hust, Hlb', Eel. cbn [negb orb]. sx_all3.
    rw_eval Ev'. sx_simp. sx_all3. rewrite Hust, Hlb', Eel. cbn [negb orb]. sx_all3.
    rewrite word_sh_lsr by lia. sx_all3. rewrite Hz0.
    sx_simp. rewrite ev_while. sx_simp. rewrite ?WORD_AND_IDEM. sx_simp.
    cbn [cont_loop]. replace (clock s + 1 =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    replace (w - n2w 1 + n2w 1)%w with w by word_ring. replace (clock s + 1 - 1)%N with (clock s) by lia.
    st_fin2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_move_bitmaps_code_thm" *)
Theorem word_gen_gc_move_bitmaps_code_thm : forall (w : word a) bitmaps z stack (s : state) i pa ib pb curr m dm
    new stack1 i1 pa1 ib1 pb1 m1 old init conf,
  word_gen_gc_move_bitmaps conf (Word w, (stack, (bitmaps, (i, (pa, (ib, (pb, (curr, (m, dm))))))))) =
    SOME (new, (stack1, (i1, (pa1, (ib1, (pb1, (m1, true))))))) /\
  (LENGTH bitmaps < dimword a - 1)%N /\ good_dimindex a /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ good_dimindex a /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word curr) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ stackSem.bitmaps s = bitmaps /\ use_stack s /\
  get_var 0 s = SOME (Word z) /\ z <> n2w 0 /\
  1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\ 7 IN FDOM (regs s) /\
  get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
  get_var 9 s = SOME (Word (w - n2w 1)) /\
  Temp (n2w 0) IN FDOM (store s) /\ Temp (n2w 1) IN FDOM (store s) /\
  FLOOKUP (store s) (Temp (n2w 2)) = SOME (Word pb) /\ FLOOKUP (store s) (Temp (n2w 3)) = SOME (Word ib) /\
  stackSem.stack s = init ++ old ++ stack /\ stack_space s = LENGTH init /\
  (dimindex a DIV 8 * LENGTH (stackSem.stack s) < dimword a)%N ->
  exists ck r0 r1 r2 r5 r6 r7 r9 t0 t1,
    evaluate (word_gen_gc_move_bitmaps_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, r7); (8, Word (bytes_in_word * n2w (LENGTH (old ++ new)))); (9, r9)])
             (set_memory m1 (set_store_fld (store s |++ [(Temp (n2w 0), t0); (Temp (n2w 1), t1);
                                                  (Temp (n2w 2), Word pb1); (Temp (n2w 3), Word ib1)])
               (set_stack (init ++ old ++ new ++ stack1) s)))).
Proof.
  intros w bitmaps z stack s i pa ib pb curr m dm new stack1 i1 pa1 ib1 pb1 m1 old init conf H.
  exact (word_gen_gc_move_bitmaps_code_thm_n (LENGTH bitmaps - w2n (w - n2w 1) + 1) w bitmaps z stack s i pa ib pb curr m dm
           new stack1 i1 pa1 ib1 pb1 m1 old init conf ltac:(lia) H).
Qed.


Local Theorem word_gen_gc_move_roots_bitmaps_code_thm_n : forall n stack bitmaps (s : state) i pa ib pb curr m dm
    stack1 i1 pa1 ib1 pb1 m1 old init conf,
  (LENGTH stack < n)%N ->
  word_gen_gc_move_roots_bitmaps conf (stack, (bitmaps, (i, (pa, (ib, (pb, (curr, (m, dm)))))))) =
    (stack1, (i1, (pa1, (ib1, (pb1, (m1, true)))))) /\
  (LENGTH bitmaps < dimword a - 1)%N /\ good_dimindex a /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ good_dimindex a /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word curr) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ stackSem.bitmaps s = bitmaps /\ use_stack s /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\ 7 IN FDOM (regs s) /\
  get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
  get_var 9 s = SOME (HD stack) /\
  Temp (n2w 0) IN FDOM (store s) /\ Temp (n2w 1) IN FDOM (store s) /\
  FLOOKUP (store s) (Temp (n2w 2)) = SOME (Word pb) /\ FLOOKUP (store s) (Temp (n2w 3)) = SOME (Word ib) /\
  stackSem.stack s = init ++ old ++ stack /\ stack_space s = LENGTH init /\
  (dimindex a DIV 8 * LENGTH (stackSem.stack s) < dimword a)%N ->
  exists ck r0 r1 r2 r5 r6 r7 r8 t0 t1,
    evaluate (word_gen_gc_move_roots_bitmaps_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, r7); (8, r8); (9, Word (n2w 0))])
             (set_memory m1 (set_store_fld (store s |++ [(Temp (n2w 0), t0); (Temp (n2w 1), t1);
                                                  (Temp (n2w 2), Word pb1); (Temp (n2w 3), Word ib1)])
               (set_stack (init ++ old ++ stack1) s)))).
Proof.
  induction n as [|n IH] using N.peano_ind;
    intros stack bitmaps s i pa ib pb curr m dm stack1 i1 pa1 ib1 pb1 m1 old init conf Hn; [lia|].
  intros (H & Hlb & Hg & Hsl & Hws & H2 & Hls & _ & Hsh & Hold & Hus & Hm & Hdm & Hbm & Hust & H0 & H1 & H2r
          & H3 & H4 & H5 & H6 & H7 & H8 & H9 & HT0 & HT1 & HT2 & HT3 & Hst & Hss & Hlen).
  unfold get_var in *; subst m dm bitmaps.
  fdom_val H0 0 v0 Ev0; fdom_val H1 1 v1 Ev1; fdom_val H2r 2 v2 Ev2; fdom_val H5 5 v5 Ev5; fdom_val H6 6 v6 Ev6;
    fdom_val H7 7 v7 Ev7.
  assert (ET0 : FLOOKUP (store s) (Temp (n2w 0)) <> None) by exact HT0.
  destruct (FLOOKUP (store s) (Temp (n2w 0))) as [t0|] eqn:Et0; [clear ET0|contradiction].
  assert (ET1 : FLOOKUP (store s) (Temp (n2w 1)) <> None) by exact HT1.
  destruct (FLOOKUP (store s) (Temp (n2w 1))) as [t1|] eqn:Et1; [clear ET1|contradiction].
  rewrite (word_gen_gc_move_roots_bitmaps_unroll _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) in H.
  destruct stack as [|hd stack]; [injection H as _ _ _ _ _ _ E; discriminate|].
  cbn [HD] in H9.
  destruct (decide (hd = Word (n2w 0))) as [->|Hhd].
  { injection H as <- <- <- <- <- <- Hc. apply bool_decide_spec in Hc. subst stack.
    exists 0, v0, v1, v2, v5, v6, v7, (Word (bytes_in_word * n2w (LENGTH old))%w), t0, t1. rewrite N.add_0_r.
    unfold word_gen_gc_move_roots_bitmaps_code. rewrite ev_while. sx_simp. rewrite ?WORD_AND_IDEM. sx_simp.
    rewrite set_clock_same, <- Hst. st_fin2. }
  destruct (word_gen_gc_move_bitmaps conf (hd, (stack, (stackSem.bitmaps s, (i, (pa, (ib, (pb, (curr, (memory s, mdomain s))))))))))
    as [[x0 [x1 [x2 [x3 [xib [xpb [x4 c2]]]]]]]|] eqn:Eb; [|injection H as _ _ _ _ _ _ E; discriminate].
  destruct (word_gen_gc_move_roots_bitmaps conf (x1, (stackSem.bitmaps s, (x2, (x3, (xib, (xpb, (curr, (x4, mdomain s)))))))))
    as (st', (i', (pa', (ib', (pb', (m', c3)))))) eqn:Er3.
  injection H as <- <- <- <- <- <- Hc. apply andb_prop in Hc as [-> ->].
  destruct hd as [c|l1 l2]; [|unfold word_gen_gc_move_bitmaps, full_read_bitmap in Eb; discriminate].
  assert (Hc0 : c <> n2w 0) by (intros ->; exact (Hhd eq_refl)).
  pose proof (word_gen_gc_move_bitmaps_LENGTH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Eb) as HlenB.
  destruct x1 as [|h t].
  { unfold word_gen_gc_move_roots_bitmaps in Er3.
    rewrite (proj1 enc_stack_def) in Er3. injection Er3 as _ _ _ _ _ _ E; discriminate. }
  set (s2 := set_regs (regs s |+ (0, Word c) |+ (9, Word (c - n2w 1))
                              |+ (8, Word (bytes_in_word * n2w (LENGTH old + 1)))) s).
  destruct (word_gen_gc_move_bitmaps_code_thm c (stackSem.bitmaps s) c stack s2 i pa ib pb curr (memory s) (mdomain s)
              x0 (h :: t) x2 x3 xib xpb x4 (old ++ [Word c]) init conf) as (ck1 & q0 & q1 & q2 & q5 & q6 & q7 & q9 & qt0 & qt1 & Ev).
  { subst s2; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
    splits; try assumption; try reflexivity;
      try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence).
    - rewrite !LENGTH_length, app_length. cbn [length]. do 4 f_equal. lia.
    - rewrite Hst, <- !app_assoc. reflexivity. }
  set (L1 := (LENGTH old + 1 + LENGTH x0)%N).
  assert (EL1 : LENGTH ((old ++ [Word c]) ++ x0) = L1) by (unfold L1; rewrite !LENGTH_length, !app_length; cbn [length]; lia).
  rewrite EL1 in Ev.
  assert (Hst' : LENGTH (stackSem.stack s) = (LENGTH init + L1 + LENGTH (h :: t))%N).
  { rewrite Hst. unfold L1. rewrite !LENGTH_length, !app_length in *. cbn [length] in *. lia. }
  assert (HL1 : (dimindex a DIV 8 * L1 < dimword a)%N).
  { eapply N.le_lt_trans; [|exact Hlen]. apply N.mul_le_mono_l. rewrite Hst'. lia. }
  assert (HL1w : (L1 < dimword a)%N).
  { assert (Hk : (1 <= dimindex a DIV 8)%N) by (destruct Hg as [E|E]; rewrite E; cbn; lia). nia. }
  assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
  set (s8 := set_regs ((regs s2 |++ [(0, q0); (1, q1); (2, q2); (3, Word x3); (4, Word x2); (5, q5); (6, q6);
                                     (7, q7); (8, Word (bytes_in_word * n2w L1)%w); (9, q9)]) |+ (9, h))
               (set_memory x4 (set_store_fld (store s |++ [(Temp (n2w 0), qt0); (Temp (n2w 1), qt1);
                                       (Temp (n2w 2), Word xpb); (Temp (n2w 3), Word xib)])
                 (set_stack (init ++ (old ++ Word c :: x0) ++ h :: t) s)))).
  destruct (IH (h :: t) (stackSem.bitmaps s) s8 x2 x3 xib xpb curr x4 (mdomain s) st' i' pa' ib' pb' m' (old ++ Word c :: x0) init conf)
    as (ck2 & p0 & p1 & p2 & p5 & p6 & p7 & p8 & pt0 & pt1 & Er).
  { rewrite !LENGTH_length in *. cbn [length] in *. lia. }
  { subst s8 s2; unfold get_var; nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb HD].
    sx_dec; sx_temp.
    splits; try assumption; try reflexivity; try lia;
      try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]; sx_dec; sx_temp; congruence).
    - do 4 f_equal. unfold L1. rewrite !LENGTH_length, !app_length. cbn [length]. lia.
    - rewrite Hst in Hlen. replace (LENGTH (init ++ (old ++ Word c :: x0) ++ h :: t)) with (LENGTH (init ++ old ++ Word c :: stack));
        [exact Hlen|]. rewrite !LENGTH_length, !app_length in *. cbn [length] in *. lia. }
  pose proof (evaluate_add_clock (ck2 + 1) (word_gen_gc_move_bitmaps_code conf) (set_clock (clock s2 + ck1) s2)) as Ev'.
  specialize (Ev' NONE _ (conj Ev NT)). subst s2. autorewrite with nf in Ev'.
  cbn [clock regs memory store set_regs set_clock set_memory set_stack set_store_fld] in Ev'. autorewrite with nf in Ev'.
  cbn [FUPDATE_LIST FOLDL] in Ev'.
  exists (ck1 + ck2 + 1), p0, p1, p2, p5, p6, p7, p8, pt0, pt1.
  unfold word_gen_gc_move_roots_bitmaps_code. rewrite ev_while. sx_simp. rewrite WORD_AND_IDEM, (bd_F Hc0). cbn [negb].
  cbn [list_Seq]. sx_all3. rewrite bytes_n2w_succ. rw_eval Ev'. sx_simp. sx_all3.
  unfold is_true in Hust. rewrite Hust. cbn [negb].
  rewrite (bytes_in_word_word_shift_n2w L1 (conj Hg HL1)), (w2n_n2w_small L1 HL1w).
  replace (n2w L1 << word_shift a)%w with (bytes_in_word * n2w L1 : word a)%w by (rewrite Hsh; apply WORD_MULT_COMM).
  rewrite (proj2 (bool_decide_spec _) eq_refl), Hss.
  replace (init ++ (old ++ [Word c]) ++ x0 ++ h :: t) with ((init ++ (old ++ [Word c]) ++ x0) ++ h :: t)
    by (rewrite <- !app_assoc; reflexivity).
  assert (Hl2 : LENGTH (init ++ (old ++ [Word c]) ++ x0) = (LENGTH init + L1)%N)
    by (rewrite <- EL1, !LENGTH_length, !app_length; lia).
  replace (LENGTH init + L1 <? LENGTH ((init ++ (old ++ [Word c]) ++ x0) ++ h :: t))%N with true
    by (symmetry; apply N.ltb_lt; rewrite !LENGTH_length, !app_length in *; cbn [length] in *; lia).
  cbn [andb]. rewrite (EL_LENGTH_ADD_LEMMA_2 _ _ h t Hl2).
  sx_all3. sx_simp.
  cbn [cont_loop]. replace (clock s + (ck2 + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
  sx_simp.
  subst s8. unfold word_gen_gc_move_roots_bitmaps_code in Er. cbn [list_Seq] in Er.
  autorewrite with nf in Er. cbn [clock regs memory store stackSem.stack set_regs set_clock set_memory set_stack set_store_fld] in Er.
  autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er. rewrite <- !app_assoc in Er |- *. cbn [app] in Er |- *.
  rw_eval2 Er. st_fin2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_move_roots_bitmaps_code_thm" *)
Theorem word_gen_gc_move_roots_bitmaps_code_thm : forall stack bitmaps (s : state) i pa ib pb curr m dm
    stack1 i1 pa1 ib1 pb1 m1 old init conf,
  word_gen_gc_move_roots_bitmaps conf (stack, (bitmaps, (i, (pa, (ib, (pb, (curr, (m, dm)))))))) =
    (stack1, (i1, (pa1, (ib1, (pb1, (m1, true)))))) /\
  (LENGTH bitmaps < dimword a - 1)%N /\ good_dimindex a /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ good_dimindex a /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word curr) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ stackSem.bitmaps s = bitmaps /\ use_stack s /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\ 7 IN FDOM (regs s) /\
  get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
  get_var 9 s = SOME (HD stack) /\
  Temp (n2w 0) IN FDOM (store s) /\ Temp (n2w 1) IN FDOM (store s) /\
  FLOOKUP (store s) (Temp (n2w 2)) = SOME (Word pb) /\ FLOOKUP (store s) (Temp (n2w 3)) = SOME (Word ib) /\
  stackSem.stack s = init ++ old ++ stack /\ stack_space s = LENGTH init /\
  (dimindex a DIV 8 * LENGTH (stackSem.stack s) < dimword a)%N ->
  exists ck r0 r1 r2 r5 r6 r7 r8 t0 t1,
    evaluate (word_gen_gc_move_roots_bitmaps_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, r7); (8, r8); (9, Word (n2w 0))])
             (set_memory m1 (set_store_fld (store s |++ [(Temp (n2w 0), t0); (Temp (n2w 1), t1);
                                                  (Temp (n2w 2), Word pb1); (Temp (n2w 3), Word ib1)])
               (set_stack (init ++ old ++ stack1) s)))).
Proof.
  intros stack bitmaps s i pa ib pb curr m dm stack1 i1 pa1 ib1 pb1 m1 old init conf H.
  exact (word_gen_gc_move_roots_bitmaps_code_thm_n (LENGTH stack + 1) stack bitmaps s i pa ib pb curr m dm
           stack1 i1 pa1 ib1 pb1 m1 old init conf ltac:(lia) H).
Qed.

End GenBitmapsG.

(** ** The generational collector: the Cheney scan *)

Section GenList.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.

Local Theorem word_gen_gc_move_list_code_thm_n : forall n conf (a0 : word a) (s : state) pa1 pa old m1 m i1 i dm a1 ib ib1 pb pb1,
  word_gen_gc_move_list conf (a0, (n2w n, (i, (pa, (ib, (pb, (old, (m, dm)))))))) = (a1, (i1, (pa1, (ib1, (pb1, (m1, true)))))) /\
  (n < dimword a)%N /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\
  Temp (n2w 0) IN FDOM (store s) /\ Temp (n2w 1) IN FDOM (store s) /\
  FLOOKUP (store s) (Temp (n2w 2)) = SOME (Word pb) /\ FLOOKUP (store s) (Temp (n2w 3)) = SOME (Word ib) /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\
  get_var 7 s = SOME (Word (n2w n)) /\ get_var 8 s = SOME (Word a0) ->
  exists ck r0 r1 r2 r5 r6 t0 t1,
    evaluate (word_gen_gc_move_list_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, Word (n2w 0)); (8, Word a1)])
             (set_memory m1 (set_store_fld (store s |++ [(Temp (n2w 0), t0); (Temp (n2w 1), t1);
                                                  (Temp (n2w 2), Word pb1); (Temp (n2w 3), Word ib1)]) s))).
Proof.
  induction n as [|n IH] using N.peano_ind;
    intros conf a0 s pa1 pa old m1 m i1 i dm a1 ib ib1 pb pb1
      (H & Hn & Hsl & Hws & H2 & Hls & Hsh & Hold & Hus & Hm & Hdm & HT0 & HT1 & HT2 & HT3 & H0 & H1 & H2r & H3 & H4 & H5 & H6 & H7 & H8);
    unfold get_var in *; subst m dm;
    fdom_val H0 0 v0 Ev0; fdom_val H1 1 v1 Ev1; fdom_val H2r 2 v2 Ev2; fdom_val H5 5 v5 Ev5; fdom_val H6 6 v6 Ev6;
    (assert (ET0 : FLOOKUP (store s) (Temp (n2w 0)) <> None) by exact HT0;
     destruct (FLOOKUP (store s) (Temp (n2w 0))) as [t0|] eqn:Et0; [clear ET0|contradiction]);
    (assert (ET1 : FLOOKUP (store s) (Temp (n2w 1)) <> None) by exact HT1;
     destruct (FLOOKUP (store s) (Temp (n2w 1))) as [t1|] eqn:Et1; [clear ET1|contradiction]).
  - rewrite word_gen_gc_move_list_def in H. destruct (decide _) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
    injection H as <- <- <- <- <- <-. exists 0, v0, v1, v2, v5, v6, t0, t1. rewrite N.add_0_r.
    unfold word_gen_gc_move_list_code. rewrite ev_while. sx_simp. rewrite set_clock_same. st_fin2.
  - pose proof (n2w_succ_ne0 n Hn) as Hne.
    rewrite word_gen_gc_move_list_def in H. destruct (decide _) as [E|_]; [contradiction|].
    rewrite n2w_succ_sub1 in H. cbv zeta in H.
    destruct (word_gen_gc_move conf (memory s a0, (i, (pa, (ib, (pb, (old, (memory s, mdomain s))))))))
      as (w1, (i1', (pa1', (ib1', (pb1', (m1', c1)))))) eqn:Emv.
    destruct (word_gen_gc_move_list conf ((a0 + bytes_in_word)%w, (n2w n, (i1', (pa1', (ib1', (pb1', (old, ((a0 =+ w1) m1', mdomain s)))))))))
      as (a2, (i2, (pa2, (ib2, (pb2, (m2, c2)))))) eqn:Erec.
    injection H as <- <- <- <- <- <- Hc. apply andb_prop in Hc as [Ha Hc]; apply andb_prop in Hc as [-> ->].
    apply bool_decide_spec in Ha.
    set (s1 := set_regs (regs s |+ (5, memory s a0) |+ (7, Word (n2w n))) s).
    destruct (word_gen_gc_move_code_thm conf (memory s a0) i pa ib pb old (memory s) (mdomain s) w1 i1' pa1' ib1' pb1' m1' s1)
      as (ck1 & q0 & q1 & q2 & q6 & qt0 & qt1 & Ev).
    { subst s1; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
      splits; try assumption; try reflexivity;
        unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
    set (s2 := set_regs ((regs s1 |++ [(0, q0); (1, q1); (2, q2); (3, Word pa1'); (4, Word i1'); (5, w1); (6, q6)])
                         |+ (8, Word (a0 + bytes_in_word)%w)) (set_memory ((a0 =+ w1) m1')
                 (set_store_fld (store s |++ [(Temp (n2w 0), qt0); (Temp (n2w 1), qt1);
                                     (Temp (n2w 2), Word pb1'); (Temp (n2w 3), Word ib1')]) s))).
    destruct (IH conf (a0 + bytes_in_word)%w s2 pa2 pa1' old m2 ((a0 =+ w1) m1') i2 i1' (mdomain s) a2 ib1' ib2 pb1' pb2)
      as (ck2 & p0 & p1 & p2 & p5 & p6 & pt0 & pt1 & Er).
    { subst s2 s1; unfold get_var; nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb].
      sx_dec; sx_temp.
      splits; try assumption; try reflexivity; try lia;
        unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]; sx_dec; sx_temp; congruence. }
    
    pose proof (evaluate_add_clock (ck2 + 1) (word_gen_gc_move_code conf) (set_clock (clock s1 + ck1) s1)) as Ev'.
    assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
    specialize (Ev' NONE _ (conj Ev NT)). subst s1. autorewrite with nf in Ev'.
    cbn [clock regs memory store set_regs set_clock set_memory set_store_fld] in Ev'. autorewrite with nf in Ev'. cbn [FUPDATE_LIST FOLDL] in Ev'.
    exists (ck1 + ck2 + 1), p0, p1, p2, p5, p6, pt0, pt1.
    unfold word_gen_gc_move_list_code. rewrite ev_while. sx_simp.
    rewrite (proj1 (Bool.not_true_iff_false (bool_decide (n2w (N.succ n) = n2w 0 :> word a)))
               ltac:(intros E; apply bool_decide_spec in E; exact (Hne E))); cbn [negb].
    cbn [list_Seq]. sx_all3. rewrite n2w_succ_sub1. rw_eval Ev'. sx_all3.
    cbn [cont_loop]. replace (clock s + (ck2 + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    subst s2. unfold word_gen_gc_move_list_code in Er. cbn [list_Seq] in Er.
    autorewrite with nf in Er. cbn [clock regs memory store set_regs set_clock set_memory set_store_fld] in Er.
    autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er.
    rw_eval Er. st_fin2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_move_list_code_thm" *)
Theorem word_gen_gc_move_list_code_thm : forall (l a0 : word a) (s : state) pa1 pa old m1 m i1 i dm conf a1 ib ib1 pb pb1,
  word_gen_gc_move_list conf (a0, (l, (i, (pa, (ib, (pb, (old, (m, dm)))))))) = (a1, (i1, (pa1, (ib1, (pb1, (m1, true)))))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\
  Temp (n2w 0) IN FDOM (store s) /\ Temp (n2w 1) IN FDOM (store s) /\
  FLOOKUP (store s) (Temp (n2w 2)) = SOME (Word pb) /\ FLOOKUP (store s) (Temp (n2w 3)) = SOME (Word ib) /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) ->
  6 IN FDOM (regs s) ->
  get_var 7 s = SOME (Word l) /\ get_var 8 s = SOME (Word a0) ->
  exists ck r0 r1 r2 r5 r6 t0 t1,
    evaluate (word_gen_gc_move_list_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, Word (n2w 0)); (8, Word a1)])
             (set_memory m1 (set_store_fld (store s |++ [(Temp (n2w 0), t0); (Temp (n2w 1), t1);
                                                  (Temp (n2w 2), Word pb1); (Temp (n2w 3), Word ib1)]) s))).
Proof.
  intros l a0 s pa1 pa old m1 m i1 i dm conf a1 ib ib1 pb pb1 (H & Hr) H6 (H7 & H8).
  apply (word_gen_gc_move_list_code_thm_n (w2n l) conf a0 s pa1 pa old m1 m i1 i dm a1 ib ib1 pb pb1). rewrite !n2w_w2n.
  splits; try assumption; apply w2n_lt || tauto.
Qed.

Local Theorem word_gen_gc_partial_move_list_code_thm_n : forall n conf (a0 : word a) (s : state) pa1 pa old m1 m i1 i dm a1 gs rs,
  word_gen_gc_partial_move_list conf (a0, (n2w n, (i, (pa, (old, (m, (dm, (gs, rs)))))))) = (a1, (i1, (pa1, (m1, true)))) /\
  (n < dimword a)%N /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ good_dimindex a /\
  FLOOKUP (store s) (Temp (n2w 0)) = SOME (Word gs) /\ FLOOKUP (store s) (Temp (n2w 1)) = SOME (Word rs) /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\
  get_var 7 s = SOME (Word (n2w n)) /\ get_var 8 s = SOME (Word a0) ->
  exists ck r0 r1 r2 r5 r6,
    evaluate (word_gen_gc_partial_move_list_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, Word (n2w 0)); (8, Word a1)])
             (set_memory m1 s)).
Proof.
  induction n as [|n IH] using N.peano_ind;
    intros conf a0 s pa1 pa old m1 m i1 i dm a1 gs rs
      (H & Hn & Hsl & Hws & H2 & Hls & Hsh & Hold & Hus & Hm & Hdm & Hg & HT0 & HT1 & H0 & H1 & H2r & H3 & H4 & H5 & H6 & H7 & H8);
    unfold get_var in *; subst m dm;
    fdom_val H0 0 v0 Ev0; fdom_val H1 1 v1 Ev1; fdom_val H2r 2 v2 Ev2; fdom_val H5 5 v5 Ev5; fdom_val H6 6 v6 Ev6.
  - rewrite word_gen_gc_partial_move_list_def in H. destruct (decide _) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
    injection H as <- <- <- <-. exists 0, v0, v1, v2, v5, v6. rewrite N.add_0_r.
    unfold word_gen_gc_partial_move_list_code. rewrite ev_while. sx_simp. rewrite set_clock_same. st_fin.
  - pose proof (n2w_succ_ne0 n Hn) as Hne.
    rewrite word_gen_gc_partial_move_list_def in H. destruct (decide _) as [E|_]; [contradiction|].
    rewrite n2w_succ_sub1 in H. cbv zeta in H.
    destruct (word_gen_gc_partial_move conf (memory s a0, (i, (pa, (old, (memory s, (mdomain s, (gs, rs))))))))
      as (w1, (i1', (pa1', (m1', c1)))) eqn:Emv.
    destruct (word_gen_gc_partial_move_list conf ((a0 + bytes_in_word)%w, (n2w n, (i1', (pa1', (old, ((a0 =+ w1) m1', (mdomain s, (gs, rs)))))))))
      as (a2, (i2, (pa2, (m2, c2)))) eqn:Erec.
    injection H as <- <- <- <- Hc. apply andb_prop in Hc as [Ha Hc]; apply andb_prop in Hc as [-> ->].
    apply bool_decide_spec in Ha.
    set (s1 := set_regs (regs s |+ (5, memory s a0) |+ (7, Word (n2w n))) s).
    destruct (word_gen_gc_partial_move_code_thm conf (memory s a0) i pa old gs rs (memory s) (mdomain s) w1 i1' pa1' m1' s1)
      as (ck1 & q0 & q1 & q2 & q6 & Ev).
    { subst s1; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
      splits; try assumption; try reflexivity;
        unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
    set (s2 := set_regs ((regs s1 |++ [(0, q0); (1, q1); (2, q2); (3, Word pa1'); (4, Word i1'); (5, w1); (6, q6)])
                         |+ (8, Word (a0 + bytes_in_word)%w)) (set_memory ((a0 =+ w1) m1') s)).
    destruct (IH conf (a0 + bytes_in_word)%w s2 pa2 pa1' old m2 ((a0 =+ w1) m1') i2 i1' (mdomain s) a2 gs rs)
      as (ck2 & p0 & p1 & p2 & p5 & p6 & Er).
    { subst s2 s1; unfold get_var; nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
      splits; try assumption; try reflexivity; try lia;
        unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
    
    pose proof (evaluate_add_clock (ck2 + 1) (word_gen_gc_partial_move_code conf) (set_clock (clock s1 + ck1) s1)) as Ev'.
    assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
    specialize (Ev' NONE _ (conj Ev NT)). subst s1. autorewrite with nf in Ev'.
    cbn [clock regs memory set_regs set_clock set_memory] in Ev'. autorewrite with nf in Ev'. cbn [FUPDATE_LIST FOLDL] in Ev'.
    exists (ck1 + ck2 + 1), p0, p1, p2, p5, p6.
    unfold word_gen_gc_partial_move_list_code. rewrite ev_while. sx_simp.
    rewrite (proj1 (Bool.not_true_iff_false (bool_decide (n2w (N.succ n) = n2w 0 :> word a)))
               ltac:(intros E; apply bool_decide_spec in E; exact (Hne E))); cbn [negb].
    cbn [list_Seq]. sx_all3. rewrite n2w_succ_sub1. rw_eval Ev'. sx_all3.
    cbn [cont_loop]. replace (clock s + (ck2 + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    subst s2. unfold word_gen_gc_partial_move_list_code in Er. cbn [list_Seq] in Er.
    autorewrite with nf in Er. cbn [clock regs memory set_regs set_clock set_memory] in Er.
    autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er.
    rw_eval Er. st_fin.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_partial_move_list_code_thm" *)
Theorem word_gen_gc_partial_move_list_code_thm : forall (l a0 : word a) (s : state) pa1 pa old m1 m i1 i dm conf a1 gs rs,
  word_gen_gc_partial_move_list conf (a0, (l, (i, (pa, (old, (m, (dm, (gs, rs)))))))) = (a1, (i1, (pa1, (m1, true)))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\ good_dimindex a /\
  FLOOKUP (store s) (Temp (n2w 0)) = SOME (Word gs) /\ FLOOKUP (store s) (Temp (n2w 1)) = SOME (Word rs) /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\
  5 IN FDOM (regs s) ->
  6 IN FDOM (regs s) ->
  get_var 7 s = SOME (Word l) /\ get_var 8 s = SOME (Word a0) ->
  exists ck r0 r1 r2 r5 r6,
    evaluate (word_gen_gc_partial_move_list_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, Word (n2w 0)); (8, Word a1)])
             (set_memory m1 s)).
Proof.
  intros l a0 s pa1 pa old m1 m i1 i dm conf a1 gs rs (H & Hr) H6 (H7 & H8).
  apply (word_gen_gc_partial_move_list_code_thm_n (w2n l) conf a0 s pa1 pa old m1 m i1 i dm a1 gs rs). rewrite !n2w_w2n.
  splits; try assumption; apply w2n_lt || tauto.
Qed.

End GenList.

Section GenRefList.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.

Lemma word_gen_gc_partial_move_ref_list_f_F : forall f conf (pb i pa old : word a) m dm gs rs re i1 pa1 m1 c1,
  word_gen_gc_partial_move_ref_list_f f conf pb i pa old m dm false gs rs re = (i1, (pa1, (m1, c1))) -> c1 = false.
Proof.
  induction f as [|f IH]; intros conf pb i pa old m dm gs rs re i1 pa1 m1 c1 H; cbn [word_gen_gc_partial_move_ref_list_f] in H;
    (destruct (decide (pb = re)); [injection H as _ _ _ <-; reflexivity|]).
  - injection H as _ _ _ <-; reflexivity.
  - cbv zeta in H. rewrite Bool.andb_false_l in H.
    destruct (word_gen_gc_partial_move_list _ _) as (?, (?, (?, (?, ?)))). exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

Lemma word_gen_gc_partial_move_ref_list_f_ok f conf (pb i pa old : word a) m dm c gs rs re i1 pa1 m1 :
  word_gen_gc_partial_move_ref_list_f f conf pb i pa old m dm c gs rs re = (i1, (pa1, (m1, true))) -> c = true.
Proof.
  destruct c; [reflexivity|]. intros H. apply word_gen_gc_partial_move_ref_list_f_F in H. discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_partial_move_ref_list_ok" *)
Local Theorem word_gen_gc_partial_move_ref_list_ok : forall k (rs re pb pa old : word a) m i gs dm conf c i1 pa1 m1,
  word_gen_gc_partial_move_ref_list k conf (pb, (i, (pa, (old, (m, (dm, (c, (gs, (rs, re))))))))) =
    (i1, (pa1, (m1, true))) -> c.
Proof.
  intros k rs re pb pa old m i gs dm conf c i1 pa1 m1 H. unfold is_true.
  exact (word_gen_gc_partial_move_ref_list_f_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

Local Theorem word_gen_gc_partial_move_ref_list_code_thm_f : forall f conf gs rs r2a1 r1a1 i1 pa1 old1 m1 dm1 i2 pa2 m2
    (s : state),
  word_gen_gc_partial_move_ref_list_f f conf r1a1 i1 pa1 old1 m1 dm1 true gs rs r2a1 = (i2, (pa2, (m2, true))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ (len_size conf + 2 < dimindex a)%N /\ good_dimindex a /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old1) /\ use_store s /\
  memory s = m1 /\ mdomain s = dm1 /\
  FLOOKUP (store s) (Temp (n2w 0)) = SOME (Word gs) /\ FLOOKUP (store s) (Temp (n2w 1)) = SOME (Word rs) /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa1) /\ get_var 4 s = SOME (Word i1) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\ 7 IN FDOM (regs s) /\
  get_var 8 s = SOME (Word r1a1) /\ get_var 9 s = SOME (Word r2a1) ->
  exists ck r0 r1 r2 r5 r6 r7 r8 r9,
    evaluate (word_gen_gc_partial_move_ref_list_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa2); (4, Word i2); (5, r5); (6, r6);
                                 (7, r7); (8, r8); (9, r9)])
             (set_memory m2 s)).
Proof.
  induction f as [|f IH];
    intros conf gs rs r2a1 r1a1 i1 pa1 old1 m1 dm1 i2 pa2 m2 s
      (H & Hsl & Hws & H2 & Hls & Hls2 & Hg & Hsh & Hold & Hus & Hm & Hdm & HT0 & HT1 & H0 & H1 & H2r & H3 & H4
       & H5 & H6 & H7 & H8 & H9);
    unfold get_var in *; subst m1 dm1;
    fdom_val H0 0 v0 Ev0; fdom_val H1 1 v1 Ev1; fdom_val H2r 2 v2 Ev2; fdom_val H5 5 v5 Ev5;
    fdom_val H6 6 v6 Ev6; fdom_val H7 7 v7 Ev7;
    cbn [word_gen_gc_partial_move_ref_list_f] in H;
    (destruct (decide (r1a1 = r2a1)) as [<-|Hne];
     [injection H as <- <- <-; exists 0, v0, v1, v2, v5, v6, v7, (Word r1a1), (Word r1a1); rewrite N.add_0_r;
      unfold word_gen_gc_partial_move_ref_list_code; rewrite ev_while; sx_simp; rewrite set_clock_same; st_fin|]).
  - discriminate.
  - cbv zeta in H. rewrite Bool.andb_true_l in H.
    destruct (memory s r1a1) as [hv|l1 l2] eqn:Em.
    2:{ exfalso. cbn [wordSem.isWord wordSem.theWord] in H. rewrite Bool.andb_false_r in H.
        destruct (word_gen_gc_partial_move_list _ _) as (?, (?, (?, (?, ?)))).
        apply word_gen_gc_partial_move_ref_list_f_F in H; discriminate. }
    cbn [wordSem.isWord wordSem.theWord] in H. rewrite Bool.andb_true_r in H.
    set (L := decode_length conf hv) in H.
    destruct (word_gen_gc_partial_move_list conf ((r1a1 + bytes_in_word)%w, (L, (i1, (pa1, (old1, (memory s, (mdomain s, (gs, rs)))))))))
      as (pb', (i1', (pa1', (m1', c1')))) eqn:Eml.
    pose proof (word_gen_gc_partial_move_ref_list_f_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as Hc.
    apply andb_prop in Hc as [Hin ->]. apply bool_decide_spec in Hin.
    rewrite (proj2 (bool_decide_spec _) Hin) in H. cbn [andb] in H.
    assert (Hne' : r2a1 <> r1a1) by congruence.
    set (s5 := set_regs (regs s |+ (7, Word L) |+ (8, Word (r1a1 + bytes_in_word)%w)) s).
    destruct (word_gen_gc_partial_move_list_code_thm L (r1a1 + bytes_in_word)%w s5 pa1' pa1 old1 m1' (memory s) i1' i1
                (mdomain s) conf pb' gs rs) as (ck1 & q0 & q1 & q2 & q5 & q6 & Ev).
    { subst s5; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
      splits; try assumption; try reflexivity;
        unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
    { subst s5; unfold pred_set.IN, FDOM; nf_fields; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
    { subst s5; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]. split; reflexivity. }
    set (s6 := set_regs (regs s5 |++ [(0, q0); (1, q1); (2, q2); (3, Word pa1'); (4, Word i1'); (5, q5); (6, q6);
                                      (7, Word (n2w 0)); (8, Word pb')]) (set_memory m1' s5)).
    destruct (IH conf gs rs r2a1 pb' i1' pa1' old1 m1' (mdomain s) i2 pa2 m2 s6)
      as (ck2 & p0 & p1 & p2 & p5 & p6 & p7 & p8 & p9 & Er).
    { subst s6 s5; unfold get_var; nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
      splits; try assumption; try reflexivity; try lia;
        unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
    pose proof (evaluate_add_clock (ck2 + 1) (word_gen_gc_partial_move_list_code conf) (set_clock (clock s5 + ck1) s5)) as Ev'.
    assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
    specialize (Ev' NONE _ (conj Ev NT)). subst s5. autorewrite with nf in Ev'.
    cbn [clock regs memory set_regs set_clock set_memory] in Ev'. autorewrite with nf in Ev'. cbn [FUPDATE_LIST FOLDL] in Ev'.
    exists (ck1 + ck2 + 1), p0, p1, p2, p5, p6, p7, p8, p9.
    unfold word_gen_gc_partial_move_ref_list_code. rewrite ev_while. sx_simp.
    rewrite (bd_F Hne'). cbn [negb list_Seq]. sx_all3. rewrite Em. sx_all3.
    rewrite word_sh_lsr by lia. sx_all3. rw_eval Ev'. sx_simp.
    cbn [cont_loop]. replace (clock s + (ck2 + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    subst s6. unfold word_gen_gc_partial_move_ref_list_code in Er. cbn [list_Seq] in Er.
    autorewrite with nf in Er. cbn [clock regs memory set_regs set_clock set_memory] in Er.
    autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er.
    sx_simp. rw_eval Er. st_fin.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_partial_move_ref_list_code_thm" *)
Local Theorem word_gen_gc_partial_move_ref_list_code_thm : forall conf gs rs k (r2a1 r1a1 : word a) i1 pa1
    old1 m1 dm1 i2 pa2 m2 (s : state),
  word_gen_gc_partial_move_ref_list k conf (r1a1, (i1, (pa1, (old1, (m1, (dm1, (true, (gs, (rs, r2a1))))))))) =
    (i2, (pa2, (m2, true))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ (len_size conf + 2 < dimindex a)%N /\ good_dimindex a /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old1) /\ use_store s /\
  memory s = m1 /\ mdomain s = dm1 /\
  FLOOKUP (store s) (Temp (n2w 0)) = SOME (Word gs) /\ FLOOKUP (store s) (Temp (n2w 1)) = SOME (Word rs) /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa1) /\ get_var 4 s = SOME (Word i1) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\ 7 IN FDOM (regs s) /\
  get_var 8 s = SOME (Word r1a1) /\ get_var 9 s = SOME (Word r2a1) ->
  exists ck r0 r1 r2 r5 r6 r7 r8 r9,
    evaluate (word_gen_gc_partial_move_ref_list_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa2); (4, Word i2); (5, r5); (6, r6);
                                 (7, r7); (8, r8); (9, r9)])
             (set_memory m2 s)).
Proof.
  intros conf gs rs k r2a1 r1a1 i1 pa1 old1 m1 dm1 i2 pa2 m2 s (H & Hr).
  apply (word_gen_gc_partial_move_ref_list_code_thm_f (N.to_nat k) conf gs rs r2a1 r1a1 i1 pa1 old1 m1 dm1 i2 pa2 m2 s).
  split; [exact H|exact Hr].
Qed.

End GenRefList.

Section GenData.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.

Local Theorem word_gen_gc_move_data_code_thm_f : forall f conf ha1 i1 pa1 ib1 pb1 old1 m1 dm1 i2 pa2 ib2 pb2 m2 (s : state),
  word_gen_gc_move_data_f conf f ha1 i1 pa1 ib1 pb1 old1 m1 dm1 = (i2, (pa2, (ib2, (pb2, (m2, true))))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ (len_size conf + 2 < dimindex a)%N /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old1) /\ use_store s /\
  memory s = m1 /\ mdomain s = dm1 /\
  Temp (n2w 0) IN FDOM (store s) /\ Temp (n2w 1) IN FDOM (store s) /\
  FLOOKUP (store s) (Temp (n2w 2)) = SOME (Word pb1) /\ FLOOKUP (store s) (Temp (n2w 3)) = SOME (Word ib1) /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa1) /\ get_var 4 s = SOME (Word i1) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\ 7 IN FDOM (regs s) /\
  get_var 8 s = SOME (Word ha1) ->
  exists ck r0 r1 r2 r5 r6 r7 t0 t1,
    evaluate (word_gen_gc_move_data_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa2); (4, Word i2); (5, r5); (6, r6);
                                 (7, r7); (8, Word pa2)])
             (set_memory m2 (set_store_fld (store s |++ [(Temp (n2w 0), t0); (Temp (n2w 1), t1);
                                                  (Temp (n2w 2), Word pb2); (Temp (n2w 3), Word ib2)]) s))).
Proof.
  induction f as [|f IH];
    intros conf ha1 i1 pa1 ib1 pb1 old1 m1 dm1 i2 pa2 ib2 pb2 m2 s
      (H & Hsl & Hws & H2 & Hls & Hls2 & Hsh & Hold & Hus & Hm & Hdm & HT0 & HT1 & HT2 & HT3 & H0 & H1 & H2r
       & H3 & H4 & H5 & H6 & H7 & H8);
    unfold get_var in *; subst m1 dm1;
    fdom_val H0 0 v0 Ev0; fdom_val H1 1 v1 Ev1; fdom_val H2r 2 v2 Ev2; fdom_val H5 5 v5 Ev5;
    fdom_val H6 6 v6 Ev6; fdom_val H7 7 v7 Ev7;
    (assert (ET0 : FLOOKUP (store s) (Temp (n2w 0)) <> None) by exact HT0;
     destruct (FLOOKUP (store s) (Temp (n2w 0))) as [t0|] eqn:Et0; [clear ET0|contradiction]);
    (assert (ET1 : FLOOKUP (store s) (Temp (n2w 1)) <> None) by exact HT1;
     destruct (FLOOKUP (store s) (Temp (n2w 1))) as [t1|] eqn:Et1; [clear ET1|contradiction]);
    cbn [word_gen_gc_move_data_f] in H;
    (destruct (decide (ha1 = pa1)) as [<-|Hne];
     [injection H as <- <- <- <- <-; exists 0, v0, v1, v2, v5, v6, v7, t0, t1; rewrite N.add_0_r;
      unfold word_gen_gc_move_data_code; rewrite ev_while; sx_simp; rewrite set_clock_same; st_fin2|]).
  - discriminate.
  - cbv zeta in H.
    assert (Hne' : pa1 <> ha1) by congruence.
    destruct (memory s ha1) as [hv|l1 l2] eqn:Em.
    2:{ exfalso. cbn [wordSem.isWord wordSem.theWord] in H. rewrite Bool.andb_false_r in H.
        destruct (word_bit _ _).
        - destruct (word_gen_gc_move_data_f _ _ _ _ _ _ _ _ _ _) as (?, (?, (?, (?, (?, ?))))).
          injection H as _ _ _ _ _ E; discriminate.
        - destruct (word_gen_gc_move_list _ _) as (?, (?, (?, (?, (?, (?, ?)))))).
          destruct (word_gen_gc_move_data_f _ _ _ _ _ _ _ _ _ _) as (?, (?, (?, (?, (?, ?))))).
          injection H as _ _ _ _ _ E; discriminate. }
    cbn [wordSem.isWord wordSem.theWord] in H. rewrite Bool.andb_true_r in H.
    set (L := decode_length conf hv) in H.
    destruct (word_bit 2 hv) eqn:Eb.
    + assert (Et : (hv && n2w 4)%w <> n2w 0) by (apply word_bit_test in Eb; exact Eb).
      destruct (word_gen_gc_move_data_f conf f (ha1 + (L + n2w 1) * bytes_in_word)%w i1 pa1 ib1 pb1 old1 (memory s) (mdomain s))
        as (i', (pa', (ib', (pb', (m', c2))))) eqn:Er0.
      injection H as <- <- <- <- <- Hc. apply andb_prop in Hc as [Hin ->]. apply bool_decide_spec in Hin.
      destruct (IH conf (ha1 + (L + n2w 1) * bytes_in_word)%w i1 pa1 ib1 pb1 old1 (memory s) (mdomain s) i' pa' ib' pb' m'
                  (set_regs (regs s |+ (7, Word ((L + n2w 1) * bytes_in_word)%w)
                                    |+ (8, Word (ha1 + (L + n2w 1) * bytes_in_word)%w)) s))
        as (ck & p0 & p1 & p2 & p5 & p6 & p7 & pt0 & pt1 & Er).
      { unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
        splits; try assumption; try reflexivity;
          unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
      exists (ck + 1), p0, p1, p2, p5, p6, p7, pt0, pt1.
      unfold word_gen_gc_move_data_code. rewrite ev_while. sx_simp.
      rewrite (bd_F Hne'). cbn [negb list_Seq]. sx_all3. rewrite Em. sx_all3. rewrite (bd_F Et). sx_all3.
      rewrite word_sh_lsr by lia. sx_all3. rewrite word_sh_lsl by lia. sx_all3.
      cbn [cont_loop]. replace (clock s + (ck + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
      rewrite Hsh. unfold word_gen_gc_move_data_code in Er. cbn [list_Seq] in Er.
      autorewrite with nf in Er. cbn [clock regs memory store set_regs set_clock set_memory set_store_fld] in Er.
      autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er.
      rw_eval Er. st_fin2.
    + assert (Et : (hv && n2w 4)%w = n2w 0).
      { destruct (decide ((hv && n2w 4)%w = n2w 0)) as [E|E]; [exact E|].
        assert (Eb' : word_bit 2 hv) by (apply word_bit_test; exact E). unfold is_true in Eb'; congruence. }
      destruct (word_gen_gc_move_list conf ((ha1 + bytes_in_word)%w, (L, (i1, (pa1, (ib1, (pb1, (old1, (memory s, mdomain s)))))))))
        as (hb', (i1', (pa1', (ib1', (pb1', (m1', c1')))))) eqn:Eml.
      destruct (word_gen_gc_move_data_f conf f hb' i1' pa1' ib1' pb1' old1 m1' (mdomain s))
        as (i', (pa', (ib', (pb', (m', c2))))) eqn:Er0.
      injection H as <- <- <- <- <- Hc. apply andb_prop in Hc as [Hin Hc]. apply andb_prop in Hc as [-> ->].
      apply bool_decide_spec in Hin.
      set (s5 := set_regs (regs s |+ (7, Word L) |+ (8, Word (ha1 + bytes_in_word)%w)) s).
      destruct (word_gen_gc_move_list_code_thm L (ha1 + bytes_in_word)%w s5 pa1' pa1 old1 m1' (memory s) i1' i1
                  (mdomain s) conf hb' ib1 ib1' pb1 pb1') as (ck1 & q0 & q1 & q2 & q5 & q6 & qt0 & qt1 & Ev).
      { subst s5; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
        splits; try assumption; try reflexivity;
          unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
      { subst s5; unfold pred_set.IN, FDOM; nf_fields; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
      { subst s5; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]. split; reflexivity. }
      set (s6 := set_regs (regs s5 |++ [(0, q0); (1, q1); (2, q2); (3, Word pa1'); (4, Word i1'); (5, q5); (6, q6);
                                        (7, Word (n2w 0)); (8, Word hb')])
                   (set_memory m1' (set_store_fld (store s5 |++ [(Temp (n2w 0), qt0); (Temp (n2w 1), qt1);
                                       (Temp (n2w 2), Word pb1'); (Temp (n2w 3), Word ib1')]) s5))).
      destruct (IH conf hb' i1' pa1' ib1' pb1' old1 m1' (mdomain s) i' pa' ib' pb' m' s6)
        as (ck2 & p0 & p1 & p2 & p5 & p6 & p7 & pt0 & pt1 & Er).
      { subst s6 s5; unfold get_var; nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb].
        sx_dec; sx_temp.
        splits; try assumption; try reflexivity; try lia;
          unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]; sx_dec; sx_temp; congruence. }
      pose proof (evaluate_add_clock (ck2 + 1) (word_gen_gc_move_list_code conf) (set_clock (clock s5 + ck1) s5)) as Ev'.
      assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
      specialize (Ev' NONE _ (conj Ev NT)). subst s5. autorewrite with nf in Ev'.
      cbn [clock regs memory store set_regs set_clock set_memory set_store_fld] in Ev'. autorewrite with nf in Ev'.
      cbn [FUPDATE_LIST FOLDL] in Ev'.
      exists (ck1 + ck2 + 1), p0, p1, p2, p5, p6, p7, pt0, pt1.
      unfold word_gen_gc_move_data_code. rewrite ev_while. sx_simp.
      rewrite (bd_F Hne'). cbn [negb list_Seq]. sx_all3. rewrite Em. sx_all3. rewrite Et. sx_simp.
      sx_all3.
      rewrite word_sh_lsr by lia. sx_all3. rw_eval Ev'. sx_simp.
      cbn [cont_loop]. replace (clock s + (ck2 + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
      subst s6. unfold word_gen_gc_move_data_code in Er. cbn [list_Seq] in Er.
      autorewrite with nf in Er. cbn [clock regs memory store set_regs set_clock set_memory set_store_fld] in Er.
      autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er.
      sx_simp. rw_eval Er. st_fin2.
Qed.


Local Theorem word_gen_gc_partial_move_data_code_thm_f : forall f conf gs rs ha1 i1 pa1 old1 m1 dm1 i2 pa2 m2 (s : state),
  word_gen_gc_partial_move_data_f conf f ha1 i1 pa1 old1 m1 dm1 gs rs = (i2, (pa2, (m2, true))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ (len_size conf + 2 < dimindex a)%N /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old1) /\ use_store s /\
  memory s = m1 /\ mdomain s = dm1 /\ good_dimindex a /\
  FLOOKUP (store s) (Temp (n2w 0)) = SOME (Word gs) /\ FLOOKUP (store s) (Temp (n2w 1)) = SOME (Word rs) /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa1) /\ get_var 4 s = SOME (Word i1) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\ 7 IN FDOM (regs s) /\
  get_var 8 s = SOME (Word ha1) ->
  exists ck r0 r1 r2 r5 r6 r7,
    evaluate (word_gen_gc_partial_move_data_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa2); (4, Word i2); (5, r5); (6, r6);
                                 (7, r7); (8, Word pa2)])
             (set_memory m2 s)).
Proof.
  induction f as [|f IH];
    intros conf gs rs ha1 i1 pa1 old1 m1 dm1 i2 pa2 m2 s
      (H & Hsl & Hws & H2 & Hls & Hls2 & Hsh & Hold & Hus & Hm & Hdm & Hg & HT0 & HT1 & H0 & H1 & H2r
       & H3 & H4 & H5 & H6 & H7 & H8);
    unfold get_var in *; subst m1 dm1;
    fdom_val H0 0 v0 Ev0; fdom_val H1 1 v1 Ev1; fdom_val H2r 2 v2 Ev2; fdom_val H5 5 v5 Ev5;
    fdom_val H6 6 v6 Ev6; fdom_val H7 7 v7 Ev7;
    cbn [word_gen_gc_partial_move_data_f] in H;
    (destruct (decide (ha1 = pa1)) as [<-|Hne];
     [injection H as <- <- <-; exists 0, v0, v1, v2, v5, v6, v7; rewrite N.add_0_r;
      unfold word_gen_gc_partial_move_data_code; rewrite ev_while; sx_simp; rewrite set_clock_same; st_fin2|]).
  - discriminate.
  - cbv zeta in H.
    assert (Hne' : pa1 <> ha1) by congruence.
    destruct (memory s ha1) as [hv|l1 l2] eqn:Em.
    2:{ exfalso. cbn [wordSem.isWord wordSem.theWord] in H. rewrite Bool.andb_false_r in H.
        destruct (word_bit _ _).
        - destruct (word_gen_gc_partial_move_data_f _ _ _ _ _ _ _ _ _ _) as (?, (?, (?, ?))).
          injection H as _ _ _ E; discriminate.
        - destruct (word_gen_gc_partial_move_list _ _) as (?, (?, (?, (?, ?)))).
          destruct (word_gen_gc_partial_move_data_f _ _ _ _ _ _ _ _ _ _) as (?, (?, (?, ?))).
          injection H as _ _ _ E; discriminate. }
    cbn [wordSem.isWord wordSem.theWord] in H. rewrite Bool.andb_true_r in H.
    set (L := decode_length conf hv) in H.
    destruct (word_bit 2 hv) eqn:Eb.
    + assert (Et : (hv && n2w 4)%w <> n2w 0) by (apply word_bit_test in Eb; exact Eb).
      destruct (word_gen_gc_partial_move_data_f conf f (ha1 + (L + n2w 1) * bytes_in_word)%w i1 pa1 old1 (memory s) (mdomain s) gs rs)
        as (i', (pa', (m', c2))) eqn:Er0.
      injection H as <- <- <- Hc. apply andb_prop in Hc as [Hin ->]. apply bool_decide_spec in Hin.
      destruct (IH conf gs rs (ha1 + (L + n2w 1) * bytes_in_word)%w i1 pa1 old1 (memory s) (mdomain s) i' pa' m'
                  (set_regs (regs s |+ (7, Word ((L + n2w 1) * bytes_in_word)%w)
                                    |+ (8, Word (ha1 + (L + n2w 1) * bytes_in_word)%w)) s))
        as (ck & p0 & p1 & p2 & p5 & p6 & p7 & Er).
      { unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
        splits; try assumption; try reflexivity;
          unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
      exists (ck + 1), p0, p1, p2, p5, p6, p7.
      unfold word_gen_gc_partial_move_data_code. rewrite ev_while. sx_simp.
      rewrite (bd_F Hne'). cbn [negb list_Seq]. sx_all3. rewrite Em. sx_all3. rewrite (bd_F Et). sx_all3.
      rewrite word_sh_lsr by lia. sx_all3. rewrite word_sh_lsl by lia. sx_all3.
      cbn [cont_loop]. replace (clock s + (ck + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
      rewrite Hsh. unfold word_gen_gc_partial_move_data_code in Er. cbn [list_Seq] in Er.
      autorewrite with nf in Er. cbn [clock regs memory store set_regs set_clock set_memory set_store_fld] in Er.
      autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er.
      rw_eval Er. st_fin2.
    + assert (Et : (hv && n2w 4)%w = n2w 0).
      { destruct (decide ((hv && n2w 4)%w = n2w 0)) as [E|E]; [exact E|].
        assert (Eb' : word_bit 2 hv) by (apply word_bit_test; exact E). unfold is_true in Eb'; congruence. }
      destruct (word_gen_gc_partial_move_list conf ((ha1 + bytes_in_word)%w, (L, (i1, (pa1, (old1, (memory s, (mdomain s, (gs, rs)))))))))
        as (hb', (i1', (pa1', (m1', c1')))) eqn:Eml.
      destruct (word_gen_gc_partial_move_data_f conf f hb' i1' pa1' old1 m1' (mdomain s) gs rs)
        as (i', (pa', (m', c2))) eqn:Er0.
      injection H as <- <- <- Hc. apply andb_prop in Hc as [Hin Hc]. apply andb_prop in Hc as [-> ->].
      apply bool_decide_spec in Hin.
      set (s5 := set_regs (regs s |+ (7, Word L) |+ (8, Word (ha1 + bytes_in_word)%w)) s).
      destruct (word_gen_gc_partial_move_list_code_thm L (ha1 + bytes_in_word)%w s5 pa1' pa1 old1 m1' (memory s) i1' i1
                  (mdomain s) conf hb' gs rs) as (ck1 & q0 & q1 & q2 & q5 & q6 & Ev).
      { subst s5; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
        splits; try assumption; try reflexivity;
          unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
      { subst s5; unfold pred_set.IN, FDOM; nf_fields; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
      { subst s5; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]. split; reflexivity. }
      set (s6 := set_regs (regs s5 |++ [(0, q0); (1, q1); (2, q2); (3, Word pa1'); (4, Word i1'); (5, q5); (6, q6);
                                        (7, Word (n2w 0)); (8, Word hb')])
                   (set_memory m1' s5)).
      destruct (IH conf gs rs hb' i1' pa1' old1 m1' (mdomain s) i' pa' m' s6)
        as (ck2 & p0 & p1 & p2 & p5 & p6 & p7 & Er).
      { subst s6 s5; unfold get_var; nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb].
        sx_dec; sx_temp.
        splits; try assumption; try reflexivity; try lia;
          unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]; sx_dec; sx_temp; congruence. }
      pose proof (evaluate_add_clock (ck2 + 1) (word_gen_gc_partial_move_list_code conf) (set_clock (clock s5 + ck1) s5)) as Ev'.
      assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
      specialize (Ev' NONE _ (conj Ev NT)). subst s5. autorewrite with nf in Ev'.
      cbn [clock regs memory store set_regs set_clock set_memory set_store_fld] in Ev'. autorewrite with nf in Ev'.
      cbn [FUPDATE_LIST FOLDL] in Ev'.
      exists (ck1 + ck2 + 1), p0, p1, p2, p5, p6, p7.
      unfold word_gen_gc_partial_move_data_code. rewrite ev_while. sx_simp.
      rewrite (bd_F Hne'). cbn [negb list_Seq]. sx_all3. rewrite Em. sx_all3. rewrite Et. sx_simp.
      sx_all3.
      rewrite word_sh_lsr by lia. sx_all3. rw_eval Ev'. sx_simp.
      cbn [cont_loop]. replace (clock s + (ck2 + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
      subst s6. unfold word_gen_gc_partial_move_data_code in Er. cbn [list_Seq] in Er.
      autorewrite with nf in Er. cbn [clock regs memory store set_regs set_clock set_memory set_store_fld] in Er.
      autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er.
      sx_simp. rw_eval Er. st_fin2.
Qed.

End GenData.

Section GenRefs.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.

Local Theorem word_gen_gc_move_refs_code_thm_f : forall f conf r2a1 r1a1 r2a2 i1 pa1 ib1 pb1 old1 m1 dm1 i2 pa2 ib2 pb2 m2
    (s : state),
  word_gen_gc_move_refs_f conf f r2a1 r1a1 i1 pa1 ib1 pb1 old1 m1 dm1 = (r2a2, (i2, (pa2, (ib2, (pb2, (m2, true)))))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ (len_size conf + 2 < dimindex a)%N /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old1) /\ use_store s /\
  memory s = m1 /\ mdomain s = dm1 /\
  Temp (n2w 0) IN FDOM (store s) /\ Temp (n2w 1) IN FDOM (store s) /\
  FLOOKUP (store s) (Temp (n2w 2)) = SOME (Word pb1) /\ FLOOKUP (store s) (Temp (n2w 3)) = SOME (Word ib1) /\
  FLOOKUP (store s) (Temp (n2w 4)) = SOME (Word r1a1) /\
  get_var 0 s = SOME (Word r1a1) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa1) /\ get_var 4 s = SOME (Word i1) /\
  5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\ 7 IN FDOM (regs s) /\
  get_var 8 s = SOME (Word r2a1) ->
  exists ck r1 r2 r5 r6 r7 t0 t1,
    evaluate (word_gen_gc_move_refs_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, Word r1a1); (1, r1); (2, r2); (3, Word pa2); (4, Word i2); (5, r5); (6, r6);
                                 (7, r7); (8, Word r2a2)])
             (set_memory m2 (set_store_fld (store s |++ [(Temp (n2w 0), t0); (Temp (n2w 1), t1);
                                                  (Temp (n2w 2), Word pb2); (Temp (n2w 3), Word ib2)]) s))).
Proof.
  induction f as [|f IH];
    intros conf r2a1 r1a1 r2a2 i1 pa1 ib1 pb1 old1 m1 dm1 i2 pa2 ib2 pb2 m2 s
      (H & Hsl & Hws & H2 & Hls & Hls2 & Hsh & Hold & Hus & Hm & Hdm & HT0 & HT1 & HT2 & HT3 & HT4 & H0 & H1 & H2r
       & H3 & H4 & H5 & H6 & H7 & H8);
    unfold get_var in *; subst m1 dm1; unfold is_true in Hus;
    fdom_val H1 1 v1 Ev1; fdom_val H2r 2 v2 Ev2; fdom_val H5 5 v5 Ev5;
    fdom_val H6 6 v6 Ev6; fdom_val H7 7 v7 Ev7;
    (assert (ET0 : FLOOKUP (store s) (Temp (n2w 0)) <> None) by exact HT0;
     destruct (FLOOKUP (store s) (Temp (n2w 0))) as [t0|] eqn:Et0; [clear ET0|contradiction]);
    (assert (ET1 : FLOOKUP (store s) (Temp (n2w 1)) <> None) by exact HT1;
     destruct (FLOOKUP (store s) (Temp (n2w 1))) as [t1|] eqn:Et1; [clear ET1|contradiction]);
    cbn [word_gen_gc_move_refs_f] in H;
    (destruct (decide (r2a1 = r1a1)) as [<-|Hne];
     [injection H as <- <- <- <- <- <-; exists 0, v1, v2, v5, v6, v7, t0, t1; rewrite N.add_0_r;
      unfold word_gen_gc_move_refs_code; rewrite ev_while; sx_simp; rewrite set_clock_same; st_fin2|]).
  - discriminate.
  - cbv zeta in H.
    destruct (memory s r2a1) as [hv|l1 l2] eqn:Em.
    2:{ exfalso. cbn [wordSem.isWord wordSem.theWord] in H. rewrite Bool.andb_false_r in H.
        destruct (word_gen_gc_move_list _ _) as (?, (?, (?, (?, (?, (?, ?)))))).
        destruct (word_gen_gc_move_refs_f _ _ _ _ _ _ _ _ _ _ _) as (?, (?, (?, (?, (?, (?, ?)))))).
        injection H as _ _ _ _ _ _ E; discriminate. }
    cbn [wordSem.isWord wordSem.theWord] in H. rewrite Bool.andb_true_r in H.
    set (L := decode_length conf hv) in H.
    destruct (word_gen_gc_move_list conf ((r2a1 + bytes_in_word)%w, (L, (i1, (pa1, (ib1, (pb1, (old1, (memory s, mdomain s)))))))))
      as (hb', (i1', (pa1', (ib1', (pb1', (m1', c1')))))) eqn:Eml.
    destruct (word_gen_gc_move_refs_f conf f hb' r1a1 i1' pa1' ib1' pb1' old1 m1' (mdomain s))
      as (r', (i', (pa', (ib', (pb', (m', c2)))))) eqn:Er0.
    injection H as <- <- <- <- <- <- Hc. apply andb_prop in Hc as [Hin Hc]. apply andb_prop in Hc as [-> ->].
    apply bool_decide_spec in Hin.
    assert (Hne' : r1a1 <> r2a1) by congruence.
    set (s5 := set_regs (regs s |+ (7, Word L) |+ (8, Word (r2a1 + bytes_in_word)%w)) s).
    destruct (word_gen_gc_move_list_code_thm L (r2a1 + bytes_in_word)%w s5 pa1' pa1 old1 m1' (memory s) i1' i1
                (mdomain s) conf hb' ib1 ib1' pb1 pb1') as (ck1 & q0 & q1 & q2 & q5 & q6 & qt0 & qt1 & Ev).
    { subst s5; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
      splits; try assumption; try reflexivity;
        unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
    { subst s5; unfold pred_set.IN, FDOM; nf_fields; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
    { subst s5; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]. split; reflexivity. }
    set (s6 := set_regs ((regs s5 |++ [(0, q0); (1, q1); (2, q2); (3, Word pa1'); (4, Word i1'); (5, q5); (6, q6);
                                       (7, Word (n2w 0)); (8, Word hb')]) |+ (0, Word r1a1))
                 (set_memory m1' (set_store_fld (store s5 |++ [(Temp (n2w 0), qt0); (Temp (n2w 1), qt1);
                                     (Temp (n2w 2), Word pb1'); (Temp (n2w 3), Word ib1')]) s5))).
    destruct (IH conf hb' r1a1 r' i1' pa1' ib1' pb1' old1 m1' (mdomain s) i' pa' ib' pb' m' s6)
      as (ck2 & p1 & p2 & p5 & p6 & p7 & pt0 & pt1 & Er).
    { subst s6 s5; unfold get_var; nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb].
      sx_dec; sx_temp.
      splits; try assumption; try reflexivity; try lia;
        unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]; sx_dec; sx_temp; congruence. }
    pose proof (evaluate_add_clock (ck2 + 1) (word_gen_gc_move_list_code conf) (set_clock (clock s5 + ck1) s5)) as Ev'.
    assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
    specialize (Ev' NONE _ (conj Ev NT)). subst s5. autorewrite with nf in Ev'.
    cbn [clock regs memory store set_regs set_clock set_memory set_store_fld] in Ev'. autorewrite with nf in Ev'.
    cbn [FUPDATE_LIST FOLDL] in Ev'.
    exists (ck1 + ck2 + 1), p1, p2, p5, p6, p7, pt0, pt1.
    unfold word_gen_gc_move_refs_code. rewrite ev_while. sx_simp.
    rewrite (bd_F Hne'). cbn [negb list_Seq]. sx_all3. rewrite Em. sx_all3.
    rewrite word_sh_lsr by lia. sx_all3. rw_eval Ev'. sx_simp. sx_all3. sx_us. sx_simp.
    cbn [cont_loop]. replace (clock s + (ck2 + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    sx_simp.
    subst s6. unfold word_gen_gc_move_refs_code in Er. cbn [list_Seq] in Er.
    autorewrite with nf in Er. cbn [clock regs memory store set_regs set_clock set_memory set_store_fld] in Er.
    autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er.
    rw_eval Er. st_fin2.
Qed.

End GenRefs.

Section GenWrap.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_move_data_code_thm" *)
Local Theorem word_gen_gc_move_data_code_thm : forall conf k ha1 i1 pa1 ib1 pb1 old1 m1 dm1 (c1 : bool) i2 pa2 ib2 pb2 m2
    (s : state),
  word_gen_gc_move_data conf k (ha1, (i1, (pa1, (ib1, (pb1, (old1, (m1, dm1))))))) = (i2, (pa2, (ib2, (pb2, (m2, true))))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ (len_size conf + 2 < dimindex a)%N /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old1) /\ use_store s /\
  memory s = m1 /\ mdomain s = dm1 /\
  Temp (n2w 0) IN FDOM (store s) /\ Temp (n2w 1) IN FDOM (store s) /\
  FLOOKUP (store s) (Temp (n2w 2)) = SOME (Word pb1) /\ FLOOKUP (store s) (Temp (n2w 3)) = SOME (Word ib1) /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa1) /\ get_var 4 s = SOME (Word i1) /\
  5 IN FDOM (regs s) ->
  6 IN FDOM (regs s) ->
  7 IN FDOM (regs s) ->
  get_var 8 s = SOME (Word ha1) /\ c1 ->
  exists ck r0 r1 r2 r5 r6 r7 t0 t1,
    evaluate (word_gen_gc_move_data_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa2); (4, Word i2); (5, r5); (6, r6);
                                 (7, r7); (8, Word pa2)])
             (set_memory m2 (set_store_fld (store s |++ [(Temp (n2w 0), t0); (Temp (n2w 1), t1);
                                                  (Temp (n2w 2), Word pb2); (Temp (n2w 3), Word ib2)]) s))).
Proof.
  intros conf k ha1 i1 pa1 ib1 pb1 old1 m1 dm1 c1 i2 pa2 ib2 pb2 m2 s H H6 H7 (H8 & _).
  apply (word_gen_gc_move_data_code_thm_f (N.to_nat k) conf ha1 i1 pa1 ib1 pb1 old1 m1 dm1 i2 pa2 ib2 pb2 m2 s).
  unfold word_gen_gc_move_data in H. tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_partial_move_data_code_thm" *)
Local Theorem word_gen_gc_partial_move_data_code_thm : forall conf gs rs k ha1 i1 pa1 old1 m1 dm1 (c1 : bool) i2 pa2 m2
    (s : state),
  word_gen_gc_partial_move_data conf k (ha1, (i1, (pa1, (old1, (m1, (dm1, (gs, rs))))))) = (i2, (pa2, (m2, true))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ (len_size conf + 2 < dimindex a)%N /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old1) /\ use_store s /\
  memory s = m1 /\ mdomain s = dm1 /\ good_dimindex a /\
  FLOOKUP (store s) (Temp (n2w 0)) = SOME (Word gs) /\ FLOOKUP (store s) (Temp (n2w 1)) = SOME (Word rs) /\
  0 IN FDOM (regs s) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa1) /\ get_var 4 s = SOME (Word i1) /\
  5 IN FDOM (regs s) ->
  6 IN FDOM (regs s) ->
  7 IN FDOM (regs s) ->
  get_var 8 s = SOME (Word ha1) /\ c1 ->
  exists ck r0 r1 r2 r5 r6 r7,
    evaluate (word_gen_gc_partial_move_data_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa2); (4, Word i2); (5, r5); (6, r6);
                                 (7, r7); (8, Word pa2)])
             (set_memory m2 s)).
Proof.
  intros conf gs rs k ha1 i1 pa1 old1 m1 dm1 c1 i2 pa2 m2 s H H6 H7 (H8 & _).
  apply (word_gen_gc_partial_move_data_code_thm_f (N.to_nat k) conf gs rs ha1 i1 pa1 old1 m1 dm1 i2 pa2 m2 s).
  unfold word_gen_gc_partial_move_data in H. tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_move_refs_code_thm" *)
Local Theorem word_gen_gc_move_refs_code_thm : forall conf k r2a1 r1a1 r2a2 i1 pa1 ib1 pb1 old1 m1 dm1 (c1 : bool)
    i2 pa2 ib2 pb2 m2 (s : state),
  word_gen_gc_move_refs conf k (r2a1, (r1a1, (i1, (pa1, (ib1, (pb1, (old1, (m1, dm1)))))))) =
    (r2a2, (i2, (pa2, (ib2, (pb2, (m2, true)))))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ (len_size conf + 2 < dimindex a)%N /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old1) /\ use_store s /\
  memory s = m1 /\ mdomain s = dm1 /\
  Temp (n2w 0) IN FDOM (store s) /\ Temp (n2w 1) IN FDOM (store s) /\
  FLOOKUP (store s) (Temp (n2w 2)) = SOME (Word pb1) /\ FLOOKUP (store s) (Temp (n2w 3)) = SOME (Word ib1) /\
  FLOOKUP (store s) (Temp (n2w 4)) = SOME (Word r1a1) /\
  get_var 0 s = SOME (Word r1a1) /\ 1 IN FDOM (regs s) /\ 2 IN FDOM (regs s) /\
  get_var 3 s = SOME (Word pa1) /\ get_var 4 s = SOME (Word i1) /\
  5 IN FDOM (regs s) ->
  6 IN FDOM (regs s) ->
  7 IN FDOM (regs s) ->
  get_var 8 s = SOME (Word r2a1) /\ c1 ->
  exists ck r1 r2 r5 r6 r7 t0 t1,
    evaluate (word_gen_gc_move_refs_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, Word r1a1); (1, r1); (2, r2); (3, Word pa2); (4, Word i2); (5, r5); (6, r6);
                                 (7, r7); (8, Word r2a2)])
             (set_memory m2 (set_store_fld (store s |++ [(Temp (n2w 0), t0); (Temp (n2w 1), t1);
                                                  (Temp (n2w 2), Word pb2); (Temp (n2w 3), Word ib2)]) s))).
Proof.
  intros conf k r2a1 r1a1 r2a2 i1 pa1 ib1 pb1 old1 m1 dm1 c1 i2 pa2 ib2 pb2 m2 s H H6 H7 (H8 & _).
  apply (word_gen_gc_move_refs_code_thm_f (N.to_nat k) conf r2a1 r1a1 r2a2 i1 pa1 ib1 pb1 old1 m1 dm1 i2 pa2 ib2 pb2 m2 s).
  unfold word_gen_gc_move_refs in H. tauto.
Qed.

End GenWrap.

(** ** The generational collector: the main loop *)

Section GenLoop.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.

Lemma word_or_eq_0 (x y : word a) : (x || y)%w = n2w 0 <-> x = n2w 0 /\ y = n2w 0.
Proof.
  split.
  - intros E. assert (Ex : ((x || y) && x)%w = x) by bitwise. assert (Ey : ((x || y) && y)%w = y) by bitwise.
    rewrite E in Ex, Ey. rewrite (proj1 (proj2 (proj2 (WORD_AND_CLAUSES x)))) in Ex.
    rewrite (proj1 (proj2 (proj2 (WORD_AND_CLAUSES y)))) in Ey. split; symmetry; assumption.
  - intros [-> ->]. exact (proj2 (proj2 (proj2 (proj2 (WORD_OR_CLAUSES (n2w 0)))))).
Qed.

Local Theorem word_gen_gc_move_loop_code_thm_f : forall f conf (pax i pa ib pb pbx old : word a) m dm i1 pa1 ib1 pb1 m1
    (tt : word a) (s : state),
  word_gen_gc_move_loop_f conf f pax i pa ib pb pbx old m dm = (i1, (pa1, (ib1, (pb1, (m1, true))))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ (len_size conf + 2 < dimindex a)%N /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\
  (tt = n2w 0 <-> pbx = pb /\ pax = pa) /\
  Temp (n2w 0) IN FDOM (store s) /\ Temp (n2w 1) IN FDOM (store s) /\
  Temp (n2w 5) IN FDOM (store s) /\ Temp (n2w 6) IN FDOM (store s) /\
  FLOOKUP (store s) (Temp (n2w 2)) = SOME (Word pb) /\ FLOOKUP (store s) (Temp (n2w 3)) = SOME (Word ib) /\
  FLOOKUP (store s) (Temp (n2w 4)) = SOME (Word pbx) /\
  0 IN FDOM (regs s) /\ get_var 1 s = SOME (Word pbx) /\ get_var 2 s = SOME (Word pb) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\ get_var 7 s = SOME (Word tt) /\
  get_var 8 s = SOME (Word pax) /\ 5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) ->
  exists ck r0 r1 r2 r5 r6 r7 r8 t0 t1 t4 t5 t6,
    evaluate (word_gen_gc_move_loop_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, r7); (8, r8)])
             (set_memory m1 (set_store_fld (store s |++ [(Temp (n2w 0), t0); (Temp (n2w 1), t1);
                (Temp (n2w 2), Word pb1); (Temp (n2w 3), Word ib1); (Temp (n2w 4), t4); (Temp (n2w 5), t5);
                (Temp (n2w 6), t6)]) s))).
Proof.
  induction f as [|f IH];
    intros conf pax i pa ib pb pbx old m dm i1 pa1 ib1 pb1 m1 tt s
      (H & Hsl & Hws & H2 & Hls & Hls2 & Hsh & Hold & Hus & Hm & Hdm & Htt & HT0 & HT1 & HT5 & HT6 & HT2 & HT3 & HT4
       & H0 & H1 & H2r & H3 & H4 & H7 & H8 & H5 & H6);
    unfold get_var in *; subst m dm; unfold is_true in Hus;
    fdom_val H0 0 v0 Ev0; fdom_val H5 5 v5 Ev5; fdom_val H6 6 v6 Ev6;
    (assert (ET0 : FLOOKUP (store s) (Temp (n2w 0)) <> None) by exact HT0;
     destruct (FLOOKUP (store s) (Temp (n2w 0))) as [t0|] eqn:Et0; [clear ET0|contradiction]);
    (assert (ET1 : FLOOKUP (store s) (Temp (n2w 1)) <> None) by exact HT1;
     destruct (FLOOKUP (store s) (Temp (n2w 1))) as [t1|] eqn:Et1; [clear ET1|contradiction]);
    (assert (ET5 : FLOOKUP (store s) (Temp (n2w 5)) <> None) by exact HT5;
     destruct (FLOOKUP (store s) (Temp (n2w 5))) as [t5|] eqn:Et5; [clear ET5|contradiction]);
    (assert (ET6 : FLOOKUP (store s) (Temp (n2w 6)) <> None) by exact HT6;
     destruct (FLOOKUP (store s) (Temp (n2w 6))) as [t6|] eqn:Et6; [clear ET6|contradiction]);
    cbn [word_gen_gc_move_loop_f] in H;
    (destruct (decide (pbx = pb)) as [Epb|Npb];
     [destruct (decide (pax = pa)) as [Epa|Npa];
      [injection H as <- <- <- <- <-;
       assert (Ht0 : tt = n2w 0) by (apply Htt; split; assumption); subst tt;
       exists 0, v0, (Word pbx), (Word pb), v5, v6, (Word (n2w 0)), (Word pax), t0, t1, (Word pbx), t5, t6;
       rewrite N.add_0_r; unfold word_gen_gc_move_loop_code; rewrite ev_while; sx_simp; rewrite ?WORD_AND_IDEM;
       sx_simp; rewrite set_clock_same; st_fin2|]|]).
  - destruct (word_gen_gc_move_data _ _ _) as (?, (?, (?, (?, (?, ?))))). injection H as _ _ _ _ _ E; discriminate.
  - destruct (word_gen_gc_move_refs _ _ _) as (?, (?, (?, (?, (?, (?, ?)))))). injection H as _ _ _ _ _ E; discriminate.
  - (* data branch *)
    destruct (word_gen_gc_move_data conf (dimword a) (pax, (i, (pa, (ib, (pb, (old, (memory s, mdomain s))))))))
      as (i', (pa', (ib', (pb', (m', c1))))) eqn:Ed.
    destruct (word_gen_gc_move_loop_f conf f pa' i' pa' ib' pb' pbx old m' (mdomain s))
      as (i'', (pa'', (ib'', (pb'', (m'', c2))))) eqn:Er0.
    injection H as <- <- <- <- <- Hc. apply andb_prop in Hc as [-> ->]. subst pbx.
    assert (Ht0 : tt <> n2w 0) by (intros E; apply Htt in E; tauto).
    assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
    destruct (word_gen_gc_move_data_code_thm conf (dimword a) pax i pa ib pb old (memory s) (mdomain s) true
                i' pa' ib' pb' m' s) as (ck1 & q0 & q1 & q2 & q5 & q6 & q7 & qt0 & qt1 & Evd).
    { unfold get_var. splits; try assumption; try reflexivity;
        unfold pred_set.IN, FDOM; congruence. }
    { unfold pred_set.IN, FDOM; congruence. }
    { unfold pred_set.IN, FDOM; congruence. }
    { unfold get_var. split; [exact H8|reflexivity]. }
    set (s2 := set_regs ((regs s |++ [(0, q0); (1, q1); (2, q2); (3, Word pa'); (4, Word i'); (5, q5); (6, q6);
                                      (7, q7); (8, Word pa')])
                         |+ (5, Word pb') |+ (7, Word pb) |+ (1, Word pb) |+ (2, Word pb') |+ (7, Word (pb - pb')%w))
                 (set_memory m' (set_store_fld (store s |++ [(Temp (n2w 0), qt0); (Temp (n2w 1), qt1);
                                      (Temp (n2w 2), Word pb'); (Temp (n2w 3), Word ib')]) s))).
    destruct (IH conf pa' i' pa' ib' pb' pb old m' (mdomain s) i'' pa'' ib'' pb'' m'' (pb - pb')%w s2)
      as (ck2 & p0 & p1 & p2 & p5 & p6 & p7 & p8 & pt0 & pt1 & pt4 & pt5 & pt6 & Er).
    { subst s2; unfold get_var; nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb].
      sx_dec; sx_temp.
      splits; try assumption; try reflexivity; try lia;
        try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]; sx_dec; sx_temp; congruence).
      rewrite WORD_EQ_SUB_ZERO. tauto. }
    pose proof (evaluate_add_clock (ck2 + 1) (word_gen_gc_move_data_code conf) (set_clock (clock s + ck1) s)) as Evd'.
    specialize (Evd' NONE _ (conj Evd NT)). autorewrite with nf in Evd'.
    cbn [clock regs memory store set_regs set_clock set_memory set_store_fld] in Evd'. autorewrite with nf in Evd'.
    cbn [FUPDATE_LIST FOLDL] in Evd'.
    exists (ck1 + ck2 + 1), p0, p1, p2, p5, p6, p7, p8, pt0, pt1, pt4, pt5, pt6.
    unfold word_gen_gc_move_loop_code. rewrite ev_while. sx_simp. rewrite WORD_AND_IDEM, (bd_F Ht0). cbn [negb].
    sx_all3. cbn [list_Seq]. sx_all3. rw_eval Evd'. sx_simp. sx_all3. sx_simp.
    cbn [cont_loop]. replace (clock s + (ck2 + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    sx_simp.
    subst s2. unfold word_gen_gc_move_loop_code in Er. cbn [list_Seq] in Er.
    autorewrite with nf in Er. cbn [clock regs memory store set_regs set_clock set_memory set_store_fld] in Er.
    autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er.
    rw_eval Er. st_fin2.
  - (* refs branch *)
    destruct (word_gen_gc_move_refs conf (dimword a) (pb, (pbx, (i, (pa, (ib, (pb, (old, (memory s, mdomain s)))))))))
      as (pbx', (i', (pa', (ib', (pb', (m', c1)))))) eqn:Erf.
    destruct (word_gen_gc_move_loop_f conf f pax i' pa' ib' pb' pb old m' (mdomain s))
      as (i'', (pa'', (ib'', (pb'', (m'', c2))))) eqn:Er0.
    injection H as <- <- <- <- <- Hc. apply andb_prop in Hc as [-> ->].
    assert (Ht0 : tt <> n2w 0) by (intros E; apply Htt in E; tauto).
    assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
    set (s1 := set_regs (regs s |+ (0, Word pbx) |+ (8, Word pb))
                 (set_store_fld (store s |+ (Temp (n2w 6), Word pax) |+ (Temp (n2w 5), Word pb)) s)).
    destruct (word_gen_gc_move_refs_code_thm conf (dimword a) pb pbx pbx' i pa ib pb old (memory s) (mdomain s)
                true i' pa' ib' pb' m' s1) as (ck1 & u1 & u2 & u5 & u6 & u7 & ut0 & ut1 & Evr).
    { subst s1; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]. sx_dec; sx_temp.
      splits; try assumption; try reflexivity;
        try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]; sx_dec; sx_temp; congruence). }
    { subst s1; unfold pred_set.IN, FDOM; nf_fields; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
    { subst s1; unfold pred_set.IN, FDOM; nf_fields; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence. }
    { subst s1; unfold get_var; nf_fields. rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]. split; reflexivity. }
    set (s4 := set_regs ((regs s1 |++ [(0, Word pbx); (1, u1); (2, u2); (3, Word pa'); (4, Word i'); (5, u5); (6, u6);
                                       (7, u7); (8, Word pbx')])
                         |+ (1, Word pb) |+ (2, Word pb') |+ (7, Word ((pb - pb') || (pax - pa'))%w)
                         |+ (8, Word pax) |+ (5, Word (pax - pa')%w))
                 (set_memory m' (set_store_fld ((store s1 |++ [(Temp (n2w 0), ut0); (Temp (n2w 1), ut1);
                                      (Temp (n2w 2), Word pb'); (Temp (n2w 3), Word ib')]) |+ (Temp (n2w 4), Word pb)) s1))).
    destruct (IH conf pax i' pa' ib' pb' pb old m' (mdomain s) i'' pa'' ib'' pb'' m'' ((pb - pb') || (pax - pa'))%w s4)
      as (ck2 & p0 & p1 & p2 & p5 & p6 & p7 & p8 & pt0 & pt1 & pt4 & pt5 & pt6 & Er).
    { subst s4 s1; unfold get_var; nf_fields. cbn [FUPDATE_LIST FOLDL]. rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb].
      sx_dec; sx_temp.
      splits; try assumption; try reflexivity; try lia;
        try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]; sx_dec; sx_temp; congruence).
      rewrite word_or_eq_0, !WORD_EQ_SUB_ZERO. tauto. }
    pose proof (evaluate_add_clock (ck2 + 1) (word_gen_gc_move_refs_code conf) (set_clock (clock s1 + ck1) s1)) as Evr'.
    specialize (Evr' NONE _ (conj Evr NT)). subst s1. autorewrite with nf in Evr'.
    cbn [clock regs memory store set_regs set_clock set_memory set_store_fld] in Evr'. autorewrite with nf in Evr'.
    cbn [FUPDATE_LIST FOLDL] in Evr'.
    exists (ck1 + ck2 + 1), p0, p1, p2, p5, p6, p7, p8, pt0, pt1, pt4, pt5, pt6.
    unfold word_gen_gc_move_loop_code. rewrite ev_while. sx_simp. rewrite WORD_AND_IDEM, (bd_F Ht0). cbn [negb].
    sx_all3. rewrite (bd_F Npb). cbn [list_Seq]. sx_all3. rw_eval Evr'. sx_simp. sx_all3. sx_simp.
    cbn [cont_loop]. replace (clock s + (ck2 + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    sx_simp.
    subst s4. unfold word_gen_gc_move_loop_code in Er. cbn [list_Seq] in Er.
    autorewrite with nf in Er. cbn [clock regs memory store set_regs set_clock set_memory set_store_fld] in Er.
    autorewrite with nf in Er. cbn [FUPDATE_LIST FOLDL] in Er.
    rewrite (proj1 (proj2 (proj2 (proj2 (WORD_OR_CLAUSES (pax - pa')%w))))). rw_eval Er. st_fin2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gen_gc_move_loop_code_thm" *)
Local Theorem word_gen_gc_move_loop_code_thm : forall conf k (pax i pa ib pb pbx old : word a) m dm i1 pa1 ib1 pb1 m1
    (tt : word a) (c1 : bool) (s : state),
  word_gen_gc_move_loop conf k (pax, (i, (pa, (ib, (pb, (pbx, (old, (m, dm)))))))) = (i1, (pa1, (ib1, (pb1, (m1, true))))) /\
  (shift_length conf < dimindex a)%N /\ (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N /\
  len_size conf <> 0%N /\ (len_size conf + 2 < dimindex a)%N /\
  (forall w : word a, (w << word_shift a = w * bytes_in_word)%w) /\
  FLOOKUP (store s) CurrHeap = SOME (Word old) /\ use_store s /\
  memory s = m /\ mdomain s = dm /\
  (tt = n2w 0 <-> pbx = pb /\ pax = pa) /\
  Temp (n2w 0) IN FDOM (store s) /\ Temp (n2w 1) IN FDOM (store s) /\
  Temp (n2w 5) IN FDOM (store s) /\ Temp (n2w 6) IN FDOM (store s) /\
  FLOOKUP (store s) (Temp (n2w 2)) = SOME (Word pb) /\ FLOOKUP (store s) (Temp (n2w 3)) = SOME (Word ib) /\
  FLOOKUP (store s) (Temp (n2w 4)) = SOME (Word pbx) /\
  0 IN FDOM (regs s) /\ get_var 1 s = SOME (Word pbx) /\ get_var 2 s = SOME (Word pb) /\
  get_var 3 s = SOME (Word pa) /\ get_var 4 s = SOME (Word i) /\ get_var 7 s = SOME (Word tt) /\
  get_var 8 s = SOME (Word pax) /\ 5 IN FDOM (regs s) /\ 6 IN FDOM (regs s) /\ c1 ->
  exists ck r0 r1 r2 r5 r6 r7 r8 t0 t1 t4 t5 t6,
    evaluate (word_gen_gc_move_loop_code conf, set_clock (clock s + ck) s) =
    (NONE, set_regs (regs s |++ [(0, r0); (1, r1); (2, r2); (3, Word pa1); (4, Word i1); (5, r5); (6, r6);
                                 (7, r7); (8, r8)])
             (set_memory m1 (set_store_fld (store s |++ [(Temp (n2w 0), t0); (Temp (n2w 1), t1);
                (Temp (n2w 2), Word pb1); (Temp (n2w 3), Word ib1); (Temp (n2w 4), t4); (Temp (n2w 5), t5);
                (Temp (n2w 6), t6)]) s))).
Proof.
  intros conf k pax i pa ib pb pbx old m dm i1 pa1 ib1 pb1 m1 tt c1 s H.
  apply (word_gen_gc_move_loop_code_thm_f (N.to_nat k) conf pax i pa ib pb pbx old m dm i1 pa1 ib1 pb1 m1 tt s).
  unfold word_gen_gc_move_loop in H. tauto.
Qed.

End GenLoop.

(** ** The generational collector: [alloc] *)

Ltac sx_simpE :=
  repeat progress (
    nf_fields; autorewrite with nf; nf_fields; unfold assign, get_var;
    cbn [IS_SOME THE andb orb negb wordLang.word_op FOLDR List.map EVERY word_exp inst
      get_var_imm wordSem.word_cmp];
    rewrite ?FLOOKUP_UPD;
    repeat match goal with H : (?x =? ?y)%N = false |- context [(?x =? ?y)%N] => rewrite H end;
    cbn [N.eqb Pos.eqb];
    repeat match goal with H : FLOOKUP ?R ?k = SOME ?v |- context [FLOOKUP ?R ?k] => rewrite H end;
    rewrite ?w_add0, ?w_0add;
    repeat match goal with |- context [bool_decide (?x = ?y)] =>
      first [ rewrite (proj2 (bool_decide_spec (x = y)) eq_refl)
            | let E := fresh in
              assert (E : bool_decide (x = y) = false)
                by (apply Bool.not_true_iff_false; rewrite bool_decide_spec; discriminate);
              rewrite E; clear E ] end;
    unfold mem_load, mem_store;
    repeat match goal with |- context [classical_dec ?P] =>
      let Hc := fresh "Hc" in destruct (classical_dec P) as [Hc|Hc]; [clear Hc|exfalso; apply Hc; assumption] end).
Ltac sx_allE := repeat (sx_step2; sx_simpE; rewrite ?sx_store_upd; sx_dec; sx_temp; sx_simpE; sx_us).

Section GenMisc.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_sub_0_eq" *)
Local Theorem word_sub_0_eq : forall w v : word a,
  ((- n2w 1 * w + v = n2w 0)%w <-> w = v) /\ ((v + - n2w 1 * w = n2w 0)%w <-> w = v).
Proof.
  intros w v. replace (- n2w 1 * w + v)%w with (v - w)%w by word_ring.
  replace (v + - n2w 1 * w)%w with (v - w)%w by word_ring.
  rewrite WORD_EQ_SUB_ZERO. split; split; intros; symmetry; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "good_dimindex_byte_aligned_eq" *)
Theorem good_dimindex_byte_aligned_eq : forall w : word a,
  good_dimindex a ->
  (byte_aligned w <-> (w && (if (dimindex a =? 32)%N then n2w 3 else n2w 7))%w = n2w 0).
Proof.
  intros w [E|E]; unfold byte_aligned; rewrite aligned_bitwise_and, E; reflexivity.
Qed.


(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "evaluate_SetNewTrigger" *)
Local Theorem evaluate_SetNewTrigger : forall endh_reg ib_reg gen_sizes (s5 : state) res new_s,
  evaluate (SetNewTrigger endh_reg ib_reg gen_sizes, s5) = (res, new_s) ->
  forall ib endh (w : word a),
    good_dimindex a /\ use_store s5 /\ ALL_DISTINCT [1; 4; 7; ib_reg; endh_reg] /\
    FLOOKUP (regs s5) ib_reg = SOME (Word ib) /\ FLOOKUP (regs s5) endh_reg = SOME (Word endh) /\
    FLOOKUP (store s5) AllocSize = SOME (Word w) ->
    exists r7 r1 r4, res = NONE /\
      new_s = set_regs (regs s5 |+ (1, r1) |+ (7, r7) |+ (4, r4))
                (set_store_fld (store s5 |+ (TriggerGC, Word (ib + new_trig (endh - ib) w gen_sizes)%w)) s5).
Proof.
  intros endh_reg ib_reg gen_sizes s5 res new_s H ib endh w (Hg & Hus & Hd & Hib & Hen & Hw).
  revert H. unfold is_true in Hus.
  cbn [ALL_DISTINCT MEM] in Hd. unfold is_true in Hd.
  rewrite !Bool.andb_true_iff, !Bool.negb_true_iff, !Bool.orb_false_iff in Hd.
  destruct Hd as ((_ & _ & H1i & H1e & _) & (_ & H4i & H4e & _) & (H7i & H7e & _) & (Hie & _) & _).
  apply bool_decide_false in H1i, H1e, H4i, H4e, H7i, H7e, Hie.
  assert (E1i : (1 =? ib_reg)%N = false) by (apply N.eqb_neq; exact H1i).
  assert (E1e : (1 =? endh_reg)%N = false) by (apply N.eqb_neq; exact H1e).
  assert (E4i : (4 =? ib_reg)%N = false) by (apply N.eqb_neq; exact H4i).
  assert (E4e : (4 =? endh_reg)%N = false) by (apply N.eqb_neq; exact H4e).
  assert (E7i : (7 =? ib_reg)%N = false) by (apply N.eqb_neq; exact H7i).
  assert (E7e : (7 =? endh_reg)%N = false) by (apply N.eqb_neq; exact H7e).
  unfold SetNewTrigger. cbn [list_Seq]. sx_allE.
  set (g := get_gen_size gen_sizes : word a). set (h := (endh - ib)%w).
  assert (Eh : (ib + n2w (w2n h) = endh)%w) by (unfold h; rewrite n2w_w2n; word_ring).
  unfold new_trig. fold g. fold h. rewrite !word_lo_w2n.
  destruct (N.ltb_spec (w2n g) (w2n w)) as [Hgw|Hgw].
  - replace (w2n w <=? w2n g)%N with false by (symmetry; apply N.leb_gt; lia).
    destruct (N.ltb_spec (w2n h) (w2n w)) as [Hhw|Hhw].
    + intros E; injection E as <- <-.
      exists (Word w), (Word g), (Word h). split; [reflexivity|].
      apply state_ext; nf_fields; try reflexivity; try solve [regs_fin]. all: rewrite Eh; reflexivity.
    + destruct (byte_aligned w) eqn:Eal.
      * assert (Ew : bool_decide ((w && (if (dimindex a =? 32)%N then n2w 3 else n2w 7))%w = n2w 0) = true)
          by (apply bool_decide_spec; apply (proj1 (good_dimindex_byte_aligned_eq w Hg)); unfold is_true; exact Eal).
        rewrite Ew. intros E; injection E as <- <-.
        exists (Word (w + ib)%w), (Word g), (Word h). split; [reflexivity|].
        apply state_ext; nf_fields; try reflexivity; try solve [regs_fin].
        all: rewrite (WORD_ADD_COMM ib w); reflexivity.
      * assert (Ew : bool_decide ((w && (if (dimindex a =? 32)%N then n2w 3 else n2w 7))%w = n2w 0) = false).
        { apply Bool.not_true_iff_false. intros E. apply bool_decide_spec, (proj2 (good_dimindex_byte_aligned_eq w Hg)) in E. unfold is_true in E. congruence. }
        rewrite Ew. intros E; injection E as <- <-.
        exists (Word w), (Word g), (Word h). split; [reflexivity|].
        apply state_ext; nf_fields; try reflexivity; try solve [regs_fin]. all: rewrite Eh; reflexivity.
  - replace (w2n w <=? w2n g)%N with true by (symmetry; apply N.leb_le; lia).
    unfold MIN. destruct (N.ltb_spec (w2n h) (w2n g)) as [Hhg|Hhg].
    + intros E; injection E as <- <-.
      exists (Word w), (Word g), (Word h). split; [reflexivity|].
      apply state_ext; nf_fields; try reflexivity; try solve [regs_fin]. all: rewrite Eh; reflexivity.
    + intros E; injection E as <- <-.
      exists (Word w), (Word (g + ib)%w), (Word h). split; [reflexivity|].
      apply state_ext; nf_fields; try reflexivity; try solve [regs_fin].
      all: rewrite n2w_w2n, (WORD_ADD_COMM ib g); reflexivity.
Qed.

End GenMisc.

Section AllocGenAux.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.
End AllocGenAux.

Section AllocGen.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.

Lemma word_gen_gc_move_Word conf (v : word a) x g i1 pa1 ib1 pb1 m1 c1 :
  word_gen_gc_move conf (Word v, x) = (g, (i1, (pa1, (ib1, (pb1, (m1, c1)))))) -> exists u, g = Word u.
Proof.
  destruct x as (i, (pa, (ib, (pb, (old, (m, dm)))))). cbn [word_gen_gc_move]. destruct (decide _).
  - intros E; injection E as <- _ _ _ _ _ _; eexists; reflexivity.
  - cbv zeta. destruct (wordSem.is_fwd_ptr _).
    + intros E; injection E as <- _ _ _ _ _ _; eexists; reflexivity.
    + destruct (is_ref_header _); destruct (memcpy _ _ _ _ _) as (?, (?, ?));
        intros E; injection E as <- _ _ _ _ _ _; eexists; reflexivity.
Qed.

Lemma word_gen_gc_partial_move_Word conf (v : word a) x g i1 pa1 m1 c1 :
  word_gen_gc_partial_move conf (Word v, x) = (g, (i1, (pa1, (m1, c1)))) -> exists u, g = Word u.
Proof.
  destruct x as (i, (pa, (old, (m, (dm, (gs, rs)))))). cbn [word_gen_gc_partial_move]. destruct (decide _).
  - intros E; injection E as <- _ _ _ _; eexists; reflexivity.
  - cbv zeta. destruct (_ || _)%bool.
    + intros E; injection E as <- _ _ _ _; eexists; reflexivity.
    + destruct (wordSem.is_fwd_ptr _).
      * intros E; injection E as <- _ _ _ _; eexists; reflexivity.
      * destruct (memcpy _ _ _ _ _) as (?, (?, ?)). intros E; injection E as <- _ _ _ _; eexists; reflexivity.
Qed.

Lemma pof_full gs (P F : list (prog a)) (X : state) trig endh w :
  F <> [] -> FLOOKUP (store X) TriggerGC = SOME (Word trig) -> FLOOKUP (store X) EndOfHeap = SOME (Word endh) ->
  FLOOKUP (regs X) 1 = SOME (Word w) -> use_store X = true -> ~ (gs <> [] /\ is_true (w <=+ endh - trig)%w) ->
  evaluate (word_gc_partial_or_full gs P F, X) =
  evaluate (list_Seq F, set_regs (regs X |+ (8, Word trig) |+ (7, Word endh) |+ (7, Word (endh - trig)%w)) X).
Proof.
  intros HF Ht He H1 Hus Hn. destruct F as [|f F]; [contradiction|].
  destruct gs as [|g gs]; unfold word_gc_partial_or_full; cbn [app list_Seq].
  - sx_all3. reflexivity.
  - sx_all3. rewrite word_ls_w2n in Hn.
    destruct (N.leb_spec (w2n w) (w2n (endh - trig))) as [Hle|Hlt].
    + exfalso. apply Hn. split; [discriminate|]. reflexivity.
    + rewrite word_lo_w2n. replace (w2n (endh - trig) <? w2n w)%N with true by (symmetry; apply N.ltb_lt; lia).
      cbn [negb]. sx_all3. reflexivity.
Qed.

Lemma pof_partial gs (P F : list (prog a)) (X : state) trig endh w :
  P <> [] -> FLOOKUP (store X) TriggerGC = SOME (Word trig) -> FLOOKUP (store X) EndOfHeap = SOME (Word endh) ->
  FLOOKUP (regs X) 1 = SOME (Word w) -> use_store X = true -> gs <> [] -> is_true (w <=+ endh - trig)%w ->
  evaluate (word_gc_partial_or_full gs P F, X) =
  evaluate (list_Seq P, set_regs (regs X |+ (8, Word trig) |+ (7, Word endh) |+ (7, Word (endh - trig)%w)) X).
Proof.
  intros HP Ht He H1 Hus Hgs Hle. destruct gs as [|g gs]; [contradiction|].
  unfold word_gc_partial_or_full; cbn [app list_Seq].
  sx_all3. rewrite word_lo_w2n. rewrite word_ls_w2n in Hle. unfold is_true in Hle. apply N.leb_le in Hle.
  replace (w2n (endh - trig) <? w2n w)%N with false by (symmetry; apply N.ltb_ge; lia).
  cbn [negb]. sx_all3. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "alloc_correct_lemma_Generational" *)
Theorem alloc_correct_lemma_Generational : forall gen_sizes (w : word a) (s : state) r t conf l ret c anything,
  alloc w s = (r, t) /\ r <> SOME Error /\ gc_fun s = word_gc_fun conf /\ gc_kind conf = Generational gen_sizes /\
  LENGTH (bitmaps s) < dimword a - 1 /\ LENGTH (stack s) * (dimindex a DIV 8) < dimword a /\
  FLOOKUP l 0 = SOME ret /\ FLOOKUP l 1 = SOME (Word w) ->
  exists ck l2,
    evaluate (word_gc_code conf,
              set_code (fromAList (compile c (toAList (code s))))
                (set_gc_fun anything (set_regs l (set_clock (clock s + ck)
                  (set_use_alloc false (set_use_stack true (set_use_store true s))))))) =
    (r, set_gc_fun anything (set_regs l2 (set_code (fromAList (compile c (toAList (code s))))
          (set_use_alloc false (set_use_stack true (set_use_store true t)))))) /\
    (r <> NONE -> r = SOME (Halt (Word (n2w 1)))) /\ regs t ⊑ l2 /\ (r = NONE -> FLOOKUP l2 0 = SOME ret).
Proof.
  intros gen_sizes w s r t conf l ret c anything (H & Hr & Hgc & Hk & Hbm & Hst & Hl0 & Hl1).
  unfold alloc, gc, set_store in H. stk_fields. rewrite Hgc in H.
  destruct (LENGTH (stack s) <? stack_space s) eqn:Ess; [injection H as <- _; exfalso; apply Hr; reflexivity|].
  destruct (enc_stack _ _) as [wl|] eqn:Ee; [|injection H as <- _; exfalso; apply Hr; reflexivity].
  unfold word_gc_fun in H. rewrite Hk in H. cbv zeta in H.
  destruct (⌜word_gc_fun_assum conf _⌝) eqn:Ea; [|cbn [negb] in H; injection H as <- _; exfalso; apply Hr; reflexivity].
  cbn [negb] in H. apply bool_decide_spec in Ea.
  destruct Ea as (Hsub & Hoth & Hcur & Htrig & Hlen & Hgs & Heoh & Hglob & Hg & Hls & Hls2 & Hsl).
  assert (Hin : forall k, k IN (Globals INSERT CurrHeap INSERT OtherHeap INSERT HeapLength INSERT
                   TriggerGC INSERT GenStart INSERT EndOfHeap INSERT {}) -> k IN FDOM (store s |+ (AllocSize, Word w)))
    by exact Hsub.
  destruct (store_word_of (store s) OtherHeap (Word w) ltac:(discriminate)
              ltac:(apply Hin; rewrite !IN_INSERT; tauto) Hoth) as (other & Eother & Fother).
  destruct (store_word_of (store s) CurrHeap (Word w) ltac:(discriminate)
              ltac:(apply Hin; rewrite !IN_INSERT; tauto) Hcur) as (curr & Ecurr & Fcurr).
  destruct (store_word_of (store s) HeapLength (Word w) ltac:(discriminate)
              ltac:(apply Hin; rewrite !IN_INSERT; tauto) Hlen) as (len & Elen & Flen).
  destruct (store_word_of (store s) TriggerGC (Word w) ltac:(discriminate)
              ltac:(apply Hin; rewrite !IN_INSERT; tauto) Htrig) as (trig & Etrig & Ftrig).
  destruct (store_word_of (store s) EndOfHeap (Word w) ltac:(discriminate)
              ltac:(apply Hin; rewrite !IN_INSERT; tauto) Heoh) as (endh & Eendh & Fendh).
  destruct (store_word_of (store s) GenStart (Word w) ltac:(discriminate)
              ltac:(apply Hin; rewrite !IN_INSERT; tauto) Hgs) as (gsv & Egsv & Fgsv).
  destruct (store_word_of (store s) Globals (Word w) ltac:(discriminate)
              ltac:(apply Hin; rewrite !IN_INSERT; tauto) Hglob) as (gw & Eglob & Fglob).
  assert (Fall : FAPPLY (store s |+ (AllocSize, Word w)) AllocSize = Word w)
    by (unfold FAPPLY; rewrite sx_store_upd; sx_dec; reflexivity).
  assert (Hws : (word_shift a < dimindex a)%N /\ (2 < dimindex a)%N)
    by (unfold word_shift; destruct Hg as [E|E]; rewrite E; cbn; lia).
  destruct Hws as [Hws H2].
  assert (Hsh : forall v : word a, (v << word_shift a = v * bytes_in_word)%w).
  { intros v. rewrite (bytes_in_word_shift Hg). rewrite WORD_MUL_LSL. apply WORD_MULT_COMM. }
  destruct (DROP (stack_space s) (stack s)) as [|h0 t0] eqn:Edrop; [rewrite (proj1 enc_stack_def) in Ee; discriminate|].
  destruct (DROP_cons_succ _ _ _ _ Edrop) as [_ Hsp].
  pose proof (DROP_EL _ _ _ _ Edrop) as Eh0.
  set (init := TAKE (stack_space s) (stack s)).
  assert (Hsplit : stack s = init ++ h0 :: t0)
    by (rewrite <- Edrop; unfold init; rewrite TAKE_firstn, DROP_skipn, firstn_skipn; reflexivity).
  assert (Hinit : stack_space s = LENGTH init).
  { unfold init. rewrite TAKE_firstn, LENGTH_length, firstn_length. rewrite LENGTH_length in Hsp. lia. }
  assert (NT : @NONE (result a) <> SOME TimeOut) by discriminate.
  destruct (⌜word_gen_gc_can_do_partial gen_sizes _⌝) eqn:Ecp;
    rewrite ?Fother, ?Fcurr, ?Flen, ?Fendh, ?Fgsv, ?Fglob, ?Fall in H; cbn [wordSem.theWord] in H.
  2:{ (* full collection *)
    rewrite ?Edrop in H.
    unfold word_gen_gc in H. rewrite (proj2 (word_gen_gc_move_roots_def _ _ _ _ _ _ _ _ _ _)) in H.
    destruct (word_gen_gc_move conf (Word gw, (n2w 0, (other, (len >>> word_shift a, (other + len, (curr, (memory s, mdomain s))))))))%w
      as (g1, (i1, (pa1, (ib1, (pb1, (m1, cg)))))) eqn:Eg.
    destruct (word_gen_gc_move_roots conf (wl, (i1, (pa1, (ib1, (pb1, (curr, (m1, mdomain s))))))))
      as (ws2, (i2, (pa2, (ib2, (pb2, (m2, cw)))))) eqn:Ewl.
    destruct (word_gen_gc_move_loop conf (w2n (len >>> word_shift a)) (other, (i2, (pa2, (ib2, (pb2, (other + len, (curr, (m2, mdomain s)))))))))%w
      as (i3, (pa3, (ib3, (pb3, (m3, cl))))) eqn:El.
    cbn [HD TL] in H.
    destruct (andb (andb cg cw) cl) eqn:Ec; [|injection H as <- _; exfalso; apply Hr; reflexivity].
    apply andb_prop in Ec as [Ec ->]. apply andb_prop in Ec as [-> ->].
    destruct (dec_stack _ ws2 _) as [stack1|] eqn:Ed; [|injection H as <- _; exfalso; apply Hr; reflexivity].
    stk_fields. cbn [FUPDATE_LIST FOLDL] in H. rewrite !sx_store_upd in H. sx_dec. sx_temp. unfold has_space in H.
    rewrite !sx_store_upd in H. sx_dec. sx_temp.
    destruct (word_gen_gc_move_Word _ _ _ _ _ _ _ _ _ _ Eg) as [g1w ->].
    assert (Hncp : ~ (gen_sizes <> [] /\ is_true (w <=+ endh - trig)%w)).
    { intros Hc. apply bool_decide_false in Ecp. apply Ecp. unfold word_gen_gc_can_do_partial.
      rewrite Fall, Ftrig, Fendh. exact Hc. }
    replace (other + len)%w with (len + other)%w in Eg, El by apply WORD_ADD_COMM.
    set (B := set_code (fromAList (compile c (toAList (code s))))
                (set_gc_fun anything (set_use_alloc false (set_use_stack true (set_use_store true s))))).
    set (R3 := l |+ (8, Word trig) |+ (7, Word endh) |+ (7, Word (endh - trig)%w) |+ (1, Word (n2w 0))
                 |+ (2, Word (n2w 0)) |+ (3, Word other) |+ (4, Word len) |+ (4, Word (len + other)%w)
                 |+ (4, Word len) |+ (4, Word (len >>> word_shift a)%w) |+ (4, Word (n2w 0)) |+ (5, Word gw)
                 |+ (6, Word (n2w 0)) |+ (8, Word (n2w 0))).
    set (ST3 := store s |+ (AllocSize, Word w) |+ (NextFree, ret)
            |+ (Temp (n2w 0), Word (len + other)%w) |+ (Temp (n2w 1), Word (len + other)%w)
            |+ (Temp (n2w 2), Word (len + other)%w) |+ (Temp (n2w 4), Word (len + other)%w)
            |+ (Temp (n2w 5), Word (len + other)%w) |+ (Temp (n2w 6), Word (len + other)%w)
            |+ (Temp (n2w 3), Word (len >>> word_shift a)%w)).
    set (S3 := set_regs R3 (set_store_fld ST3 B)).
    destruct (word_gen_gc_move_code_thm conf (Word gw) (n2w 0) other (len >>> word_shift a)%w (len + other)%w curr
                (memory s) (mdomain s) (Word g1w) i1 pa1 ib1 pb1 m1 S3)
      as (ck1 & q0 & q1 & q2 & q6 & qt0 & qt1 & Ev1).
    { subst S3 R3 ST3 B. unfold get_var. nf_fields. rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb].
      sx_dec; sx_temp.
      splits; try assumption; try reflexivity;
        try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]; sx_dec; sx_temp; congruence). }
    set (R4 := (R3 |++ [(0, q0); (1, q1); (2, q2); (3, Word pa1); (4, Word i1); (5, Word g1w); (6, q6)])
                 |+ (7, Word g1w) |+ (9, Word other)
                 |+ (7, Word (g1w >>> shift_length conf)%w)
                 |+ (7, Word (g1w >>> shift_length conf << word_shift a)%w)
                 |+ (7, Word (g1w >>> shift_length conf << word_shift a + other)%w)
                 |+ (7, Word (n2w 0)) |+ (9, h0) |+ (8, Word (n2w 0))).
    set (ST4 := (ST3 |++ [(Temp (n2w 0), qt0); (Temp (n2w 1), qt1); (Temp (n2w 2), Word pb1); (Temp (n2w 3), Word ib1)])
                 |+ (Globals, Word g1w)
                 |+ (GlobReal, Word (g1w >>> shift_length conf << word_shift a + other)%w)).
    set (S4 := set_regs R4 (set_memory m1 (set_store_fld ST4 B))).
    destruct (word_gen_gc_move_roots_bitmaps_code_thm (h0 :: t0) (bitmaps s) S4 i1 pa1 ib1 pb1 curr m1 (mdomain s)
                stack1 i2 pa2 ib2 pb2 m2 [] init conf)
      as (ck2 & u0 & u1 & u2 & u5 & u6 & u7 & u8 & ut0 & ut1 & Ev2).
    { subst S4 R4 ST4 S3 R3 ST3 B. unfold get_var. nf_fields. cbn [FUPDATE_LIST FOLDL].
      rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb HD]. sx_dec; sx_temp.
      splits; try assumption; try reflexivity;
        try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]; sx_dec; sx_temp; congruence).
      all: try (unfold word_gen_gc_move_roots_bitmaps; rewrite Ee, Ewl, Ed; reflexivity).
      all: try (cbn [LENGTH]; do 2 f_equal; word_ring).
      all: try (rewrite Hsplit; reflexivity).
      all: rewrite N.mul_comm; exact Hst. }
    set (NE := (len + other)%w).
    set (ttv := ((pa2 - other) || (pb2 - NE))%w).
    set (R5 := (R4 |++ [(0, u0); (1, u1); (2, u2); (3, Word pa2); (4, Word i2); (5, u5); (6, u6); (7, u7); (8, u8);
                        (9, Word (n2w 0))])
                 |+ (2, Word pb2) |+ (8, Word other) |+ (1, Word NE) |+ (6, Word (pb2 - NE)%w) |+ (7, Word ttv)).
    set (ST5 := ST4 |++ [(Temp (n2w 0), ut0); (Temp (n2w 1), ut1); (Temp (n2w 2), Word pb2); (Temp (n2w 3), Word ib2)]).
    set (S5 := set_regs R5 (set_memory m2 (set_store_fld ST5 (set_stack (init ++ [] ++ stack1) B)))).
    destruct (word_gen_gc_move_loop_code_thm conf (w2n (len >>> word_shift a)%w) other i2 pa2 ib2 pb2 NE curr m2 (mdomain s)
                i3 pa3 ib3 pb3 m3 ttv true S5)
      as (ck3 & p0 & p1 & p2 & p5 & p6 & p7 & p8 & pt0 & pt1 & pt4 & pt5 & pt6 & Ev3).
    { subst S5 R5 ST5 S4 R4 ST4 S3 R3 ST3 B. unfold get_var. nf_fields. cbn [FUPDATE_LIST FOLDL].
      rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]. sx_dec; sx_temp.
      splits; try assumption; try reflexivity;
        try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]; sx_dec; sx_temp; congruence).
      all: try (unfold ttv; rewrite word_or_eq_0, !WORD_EQ_SUB_ZERO; split; intros [E1 E2]; split; symmetry; assumption).
    }
    pose proof (evaluate_add_clock (ck2 + ck3) (word_gen_gc_move_code conf) (set_clock (clock S3 + ck1) S3)) as Ev1'.
    specialize (Ev1' NONE _ (conj Ev1 NT)). clear Ev1.
    pose proof (evaluate_add_clock ck3 (word_gen_gc_move_roots_bitmaps_code conf) (set_clock (clock S4 + ck2) S4)) as Ev2'.
    specialize (Ev2' NONE _ (conj Ev2 NT)). clear Ev2.
    subst S5 R5 ST5 S4 R4 ST4 S3 R3 ST3 B.
    autorewrite with nf in Ev1'. cbn [clock regs memory stackSem.stack store set_regs set_clock set_memory set_stack set_store_fld set_code set_gc_fun set_use_alloc set_use_stack set_use_store] in Ev1'.
    autorewrite with nf in Ev1'. cbn [FUPDATE_LIST FOLDL app] in Ev1'.
    exists (ck1 + ck2 + ck3).
    match goal with |- exists l2, evaluate ?E = _ /\ _ =>
      let RES := fresh "RES" in let ER := fresh "ER" in remember (evaluate E) as RES eqn:ER; revert ER end.
    unfold word_gc_code. rewrite Hk.
    rewrite (pof_full gen_sizes _ _ _ trig endh w); [|discriminate|nf_fields; first [assumption|reflexivity]..].
    cbn [list_Seq].
    set (MC := word_gen_gc_move_code conf). set (RC := word_gen_gc_move_roots_bitmaps_code conf).
    set (LC := word_gen_gc_move_loop_code conf).
    unfold is_true in *. sx_all3. rewrite word_sh_lsr by lia. sx_all3.
    subst MC. rw_eval Ev1'. sx_simp. sx_all3.
    rewrite word_sh_lsr by lia. sx_all3. rewrite word_sh_lsl by lia. sx_all3.
    rewrite zero_lsr, zero_lsl, w2n_n2w, N.mod_0_l, N.add_0_r by (pose proof (ZERO_LT_dimword a); lia).
    rewrite (proj2 (bool_decide_spec _) eq_refl), (proj2 (N.ltb_lt _ _) Hsp), Eh0. cbn [andb]. sx_all3.
    subst RC. rw_eval Ev2'. cbn [FUPDATE_LIST FOLDL]. sx_simp. sx_all3.
    rewrite (proj1 (proj2 (proj2 (proj2 (WORD_OR_CLAUSES (pb2 - (len + other))%w))))).
    subst LC. rw_eval Ev3. cbn [FUPDATE_LIST FOLDL]. sx_simp.
    set (SNT := SetNewTrigger 2 3 gen_sizes : prog a). sx_all3.
    match goal with |- context [evaluate (SNT, ?X)] =>
      destruct (evaluate (SetNewTrigger 2 3 gen_sizes, X)) as [rs ns] eqn:Es;
      destruct (evaluate_SetNewTrigger _ _ _ _ _ _ Es pa3 pb3 w) as (r7 & r1 & r4 & -> & ->) end.
    { nf_fields. rewrite ?FLOOKUP_UPD, ?sx_store_upd. cbn [N.eqb Pos.eqb]. sx_dec; sx_temp.
      splits; try assumption; try reflexivity. }
    subst SNT. rewrite Es. sx_simp. sx_all3.
    intros ER. subst RES. rewrite word_lo_w2n.
    cbn [glob_real] in H.
    replace (other + (g1w >>> shift_length conf << word_shift a))%w
      with ((g1w >>> shift_length conf << word_shift a) + other)%w in H by apply WORD_ADD_COMM.
    destruct (N.leb_spec (w2n w) (w2n (pa3 + new_trig (pb3 - pa3) w gen_sizes - pa3))) as [Hle|Hgt];
      injection H as <- <-.
    - rewrite (proj2 (N.ltb_ge _ _) Hle). eexists. splits.
      + f_equal. apply state_ext; nf_fields; try reflexivity; try solve [store_fin2].
       
      + intros E; exfalso; apply E; reflexivity.
      + intros k0 v0 Hk0; discriminate Hk0.
      + intros _. rewrite ?FLOOKUP_UPD. reflexivity.
    - rewrite (proj2 (N.ltb_lt _ _) Hgt). eexists. splits.
      + f_equal. unfold empty_env. apply state_ext; nf_fields; try reflexivity; try solve [store_fin2].
       
      + intros _; reflexivity.
      + intros k0 v0 Hk0; discriminate Hk0.
      + intros E; discriminate E. }
  (* partial collection *)
  unfold word_gen_gc_partial_full, word_gen_gc_partial in H.
  rewrite (proj2 (word_gen_gc_partial_move_roots_def _ _ _ _ _ _ _ _ _ _)) in H.
  destruct (word_gen_gc_partial_move conf (Word gw, (gsv >>> word_shift a, (other, (curr, (memory s, (mdomain s, (gsv, (endh - curr)))))))))%w
    as (g1, (i1, (pa1, (m1, cg)))) eqn:Eg.
  destruct (word_gen_gc_partial_move_roots conf (wl, (i1, (pa1, (curr, (m1, (mdomain s, (gsv, (endh - curr)%w))))))))
    as (ws2, (i2, (pa2, (m2, cw)))) eqn:Ewl.
  destruct (word_gen_gc_partial_move_ref_list (dimword a) conf ((curr + (endh - curr))%w, (i2, (pa2, (curr, (m2, (mdomain s, (andb cg cw, (gsv, ((endh - curr)%w, (curr + len)%w))))))))))
    as (i3, (pa3, (m3, cr))) eqn:Erl.
  destruct (word_gen_gc_partial_move_data conf (dimword a) (other, (i3, (pa3, (curr, (m3, (mdomain s, (gsv, (endh - curr)%w))))))))
    as (i4, (pa4, (m4, cd))) eqn:Edt.
  destruct (memcpy ((pa4 - other) >>> word_shift a)%w other (curr + gsv)%w m4 (mdomain s)) as (b1, (m5, cm)) eqn:Emc.
  cbn [HD TL] in H.
  destruct (andb (andb cr cd) cm && ((w <=+ endh - b1)%w && (w <=+ new_trig (endh - b1) w gen_sizes)%w)) eqn:Ec;
    [|injection H as <- _; exfalso; apply Hr; reflexivity].
  apply andb_prop in Ec as [Ec Hc3]. apply andb_prop in Ec as [Ec ->]. apply andb_prop in Ec as [-> ->].
  apply andb_prop in Hc3 as [Hc3a Hc3b].
  pose proof (word_gen_gc_partial_move_ref_list_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Erl) as Hcgw.
  unfold is_true in Hcgw. apply andb_prop in Hcgw as [-> ->].
  destruct (dec_stack _ ws2 _) as [stack1|] eqn:Ed; [|injection H as <- _; exfalso; apply Hr; reflexivity].
  stk_fields. cbn [FUPDATE_LIST FOLDL] in H. rewrite !sx_store_upd in H. sx_dec. sx_temp. unfold has_space in H.
  rewrite !sx_store_upd in H. sx_dec. sx_temp.
  replace (b1 + new_trig (endh - b1) w gen_sizes - b1)%w with (new_trig (endh - b1) w gen_sizes) in H by word_ring.
  rewrite word_ls_w2n in Hc3b. unfold is_true in Hc3b. rewrite Hc3b in H.
  injection H as <- <-.
  destruct (word_gen_gc_partial_move_Word _ _ _ _ _ _ _ _ Eg) as [g1w ->].
  assert (Hcp : gen_sizes <> [] /\ is_true (w <=+ endh - trig)%w).
  { apply bool_decide_spec in Ecp. unfold word_gen_gc_can_do_partial in Ecp. rewrite Fall, Ftrig, Fendh in Ecp. exact Ecp. }
  replace (curr + (endh - curr))%w with endh in Erl by word_ring.
  rewrite (WORD_ADD_COMM curr len) in Erl. cbn [andb] in Erl.
  rewrite (WORD_ADD_COMM curr gsv) in Emc.
  set (B := set_code (fromAList (compile c (toAList (code s))))
              (set_gc_fun anything (set_use_alloc false (set_use_stack true (set_use_store true s))))).
  set (R3 := l |+ (8, Word trig) |+ (7, Word endh) |+ (7, Word (endh - trig)%w) |+ (4, Word gsv) |+ (5, Word endh)
               |+ (2, Word curr) |+ (5, Word (endh - curr)%w) |+ (7, Word len) |+ (5, Word gw) |+ (3, Word other)
               |+ (4, Word (gsv >>> word_shift a)%w) |+ (6, Word other)).
  set (ST3 := store s |+ (AllocSize, Word w) |+ (NextFree, ret) |+ (Temp (n2w 0), Word gsv)
                |+ (Temp (n2w 1), Word (endh - curr)%w)).
  set (S3 := set_regs R3 (set_store_fld ST3 B)).
  destruct (word_gen_gc_partial_move_code_thm conf (Word gw) (gsv >>> word_shift a)%w other curr gsv (endh - curr)%w
              (memory s) (mdomain s) (Word g1w) i1 pa1 m1 S3) as (ck1 & q0 & q1 & q2 & q6 & Ev1).
  { subst S3 R3 ST3 B. unfold get_var. nf_fields. rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb].
    sx_dec; sx_temp.
    splits; try assumption; try reflexivity;
      try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]; sx_dec; sx_temp; congruence). }
  set (ST4 := ST3 |+ (Globals, Word g1w) |+ (GlobReal, Word (g1w >>> shift_length conf << word_shift a + curr)%w)).
  set (R4 := (R3 |++ [(0, q0); (1, q1); (2, q2); (3, Word pa1); (4, Word i1); (5, Word g1w); (6, q6)])
               |+ (9, Word curr) |+ (8, Word (n2w 0)) |+ (9, h0)).
  set (S4 := set_regs R4 (set_memory m1 (set_store_fld ST4 B))).
  destruct (word_gen_gc_partial_move_roots_bitmaps_code_thm (h0 :: t0) (bitmaps s) S4 i1 pa1 curr m1 (mdomain s)
              stack1 i2 pa2 m2 [] init conf gsv (endh - curr)%w)
    as (ck2 & u0 & u1 & u2 & u5 & u6 & u7 & u8 & Ev2).
  { subst S4 R4 ST4 S3 R3 ST3 B. unfold get_var. nf_fields. cbn [FUPDATE_LIST FOLDL].
    rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb HD]. sx_dec; sx_temp.
    splits; try assumption; try reflexivity;
      try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]; sx_dec; sx_temp; congruence).
    all: try (unfold word_gen_gc_partial_move_roots_bitmaps; rewrite Ee, Ewl, Ed; reflexivity).
    all: try (cbn [LENGTH]; do 2 f_equal; word_ring).
    all: try (rewrite Hsplit; reflexivity).
    all: rewrite N.mul_comm; exact Hst. }
  set (R5 := (R4 |++ [(0, u0); (1, u1); (2, u2); (3, Word pa2); (4, Word i2); (5, u5); (6, u6); (7, u7); (8, u8);
                      (9, Word (n2w 0))]) |+ (9, Word (len + curr)%w) |+ (8, Word endh)).
  set (S5 := set_regs R5 (set_memory m2 (set_store_fld ST4 (set_stack (init ++ [] ++ stack1) B)))).
  destruct (word_gen_gc_partial_move_ref_list_code_thm conf gsv (endh - curr)%w (dimword a) (len + curr)%w endh
              i2 pa2 curr m2 (mdomain s) i3 pa3 m3 S5) as (ck3 & v0 & v1 & v2 & v5 & v6 & v7 & v8 & v9 & Ev3).
  { subst S5 R5 S4 R4 ST4 S3 R3 ST3 B. unfold get_var. nf_fields. cbn [FUPDATE_LIST FOLDL].
    rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]. sx_dec; sx_temp.
    splits; try assumption; try reflexivity;
      try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]; sx_dec; sx_temp; congruence). }
  set (R6 := (R5 |++ [(0, v0); (1, v1); (2, v2); (3, Word pa3); (4, Word i3); (5, v5); (6, v6); (7, v7); (8, v8); (9, v9)])
               |+ (8, Word other)).
  set (S6 := set_regs R6 (set_memory m3 (set_store_fld ST4 (set_stack (init ++ [] ++ stack1) B)))).
  destruct (word_gen_gc_partial_move_data_code_thm conf gsv (endh - curr)%w (dimword a) other i3 pa3 curr m3
              (mdomain s) true i4 pa4 m4 S6) as (ck4 & x0 & x1 & x2 & x5 & x6 & x7 & Ev4).
  { subst S6 R6 S5 R5 S4 R4 ST4 S3 R3 ST3 B. unfold get_var. nf_fields. cbn [FUPDATE_LIST FOLDL].
    rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]. sx_dec; sx_temp.
    splits; try assumption; try reflexivity;
      try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD, ?sx_store_upd; cbn [N.eqb Pos.eqb]; sx_dec; sx_temp; congruence). }
  1-2: subst S6 R6 S5 R5 S4 R4 ST4 S3 R3 ST3 B; unfold pred_set.IN, FDOM; nf_fields; cbn [FUPDATE_LIST FOLDL];
    rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; try congruence.
  { subst S6 R6. unfold get_var. nf_fields. rewrite FLOOKUP_UPD. split; reflexivity. }
  set (len0 := ((pa4 - other) >>> word_shift a)%w).
  set (R7 := (R6 |++ [(0, x0); (1, x1); (2, x2); (3, Word pa4); (4, Word i4); (5, x5); (6, x6); (7, x7); (8, Word pa4)])
               |+ (2, Word other) |+ (0, Word len0) |+ (3, Word (gsv + curr)%w) |+ (1, Word curr)).
  set (S7 := set_regs R7 (set_memory m4 (set_store_fld ST4 (set_stack (init ++ [] ++ stack1) B)))).
  destruct (memcpy_code_thm len0 other (gsv + curr)%w m4 (mdomain s) b1 m5 S7) as [r1' Ev5].
  { subst S7 R7 S6 R6 S5 R5 S4 R4 ST4 S3 R3 ST3 B. unfold get_var. nf_fields. cbn [FUPDATE_LIST FOLDL].
    rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb].
    splits; try assumption; try reflexivity;
      try (unfold pred_set.IN, FDOM; rewrite ?FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; congruence). }
  pose proof (evaluate_add_clock (ck2 + ck3 + ck4 + w2n len0) (word_gen_gc_partial_move_code conf) (set_clock (clock S3 + ck1) S3)) as Ev1'.
  specialize (Ev1' NONE _ (conj Ev1 NT)). clear Ev1.
  pose proof (evaluate_add_clock (ck3 + ck4 + w2n len0) (word_gen_gc_partial_move_roots_bitmaps_code conf) (set_clock (clock S4 + ck2) S4)) as Ev2'.
  specialize (Ev2' NONE _ (conj Ev2 NT)). clear Ev2.
  pose proof (evaluate_add_clock (ck4 + w2n len0) (word_gen_gc_partial_move_ref_list_code conf) (set_clock (clock S5 + ck3) S5)) as Ev3'.
  specialize (Ev3' NONE _ (conj Ev3 NT)). clear Ev3.
  pose proof (evaluate_add_clock (w2n len0) (word_gen_gc_partial_move_data_code conf) (set_clock (clock S6 + ck4) S6)) as Ev4'.
  specialize (Ev4' NONE _ (conj Ev4 NT)). clear Ev4.
  subst S7 R7 S6 R6 S5 R5 S4 R4 ST4 S3 R3 ST3 B.
  autorewrite with nf in Ev1'. cbn [clock regs memory store set_regs set_clock set_memory set_store_fld set_code set_gc_fun set_use_alloc set_use_stack set_use_store] in Ev1'.
  autorewrite with nf in Ev1'. cbn [FUPDATE_LIST FOLDL] in Ev1'.
  exists (ck1 + ck2 + ck3 + ck4 + w2n len0).
  match goal with |- exists l2, evaluate ?E = _ /\ _ =>
    let RES := fresh "RES" in let ER := fresh "ER" in remember (evaluate E) as RES eqn:ER; revert ER end.
  unfold word_gc_code. rewrite Hk.
  rewrite (pof_partial gen_sizes _ _ _ trig endh w); [|discriminate|nf_fields; first [assumption|reflexivity|tauto]..].
  cbn [list_Seq].
  set (MC := word_gen_gc_partial_move_code conf). set (RC := word_gen_gc_partial_move_roots_bitmaps_code conf).
  set (FC := word_gen_gc_partial_move_ref_list_code conf). set (DC := word_gen_gc_partial_move_data_code conf).
  set (CC := @memcpy_code a). set (SNT := SetNewTrigger 8 3 gen_sizes : prog a).
  unfold is_true in *. sx_all3. rewrite word_sh_lsr by lia. sx_all3.
  subst MC. rw_eval Ev1'. sx_simp. sx_all3.
  rewrite word_sh_lsr by lia. sx_all3. rewrite word_sh_lsl by lia. sx_all3.
  rewrite zero_lsr, zero_lsl, w2n_n2w, N.mod_0_l, N.add_0_r by (pose proof (ZERO_LT_dimword a); lia).
  rewrite (proj2 (bool_decide_spec _) eq_refl), (proj2 (N.ltb_lt _ _) Hsp), Eh0. cbn [andb]. sx_all3.
  subst RC. rw_eval Ev2'. cbn [FUPDATE_LIST FOLDL]. sx_simp. sx_all3.
  subst FC. rw_eval Ev3'. cbn [FUPDATE_LIST FOLDL]. sx_simp. sx_all3.
  subst DC. rw_eval Ev4'. cbn [FUPDATE_LIST FOLDL]. sx_simp. sx_all3.
  rewrite word_sh_lsr by lia. sx_all3.
  subst CC. rw_eval Ev5. cbn [FUPDATE_LIST FOLDL]. sx_simp. sx_all3.
  match goal with |- context [evaluate (SNT, ?X)] =>
    destruct (evaluate (SetNewTrigger 8 3 gen_sizes, X)) as [rs0 ns] eqn:Es;
    destruct (evaluate_SetNewTrigger _ _ _ _ _ _ Es b1 endh w) as (r7 & r1 & r4 & -> & ->) end.
  { nf_fields. rewrite ?FLOOKUP_UPD, ?sx_store_upd. cbn [N.eqb Pos.eqb]. sx_dec; sx_temp.
    splits; try assumption; try reflexivity. }
  subst SNT. rewrite Es. sx_simp. sx_all3.
  intros ER. subst RES.
  cbn [glob_real].
  replace (curr + (g1w >>> shift_length conf << word_shift a))%w
    with ((g1w >>> shift_length conf << word_shift a) + curr)%w by apply WORD_ADD_COMM.
  eexists. splits.
  - f_equal. apply state_ext; nf_fields; try reflexivity; try solve [store_fin2].
   
  - intros E; exfalso; apply E; reflexivity.
  - intros k0 vv0 Hk0; discriminate Hk0.
  - intros _. rewrite ?FLOOKUP_UPD. reflexivity.
Qed.

End AllocGen.

(** ** [alloc], [comp_correct] and the semantics theorems *)

Section AllocAll.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "alloc_correct_lemma" *)
Theorem alloc_correct_lemma : forall (w : word a) (s : state) r t conf l ret c anything,
  alloc w s = (r, t) /\ r <> SOME Error /\ gc_fun s = word_gc_fun conf /\
  LENGTH (bitmaps s) < dimword a - 1 /\ LENGTH (stack s) * (dimindex a DIV 8) < dimword a /\
  FLOOKUP l 0 = SOME ret /\ FLOOKUP l 1 = SOME (Word w) ->
  exists ck l2,
    evaluate (word_gc_code conf,
              set_code (fromAList (compile c (toAList (code s))))
                (set_gc_fun anything (set_regs l (set_clock (clock s + ck)
                  (set_use_alloc false (set_use_stack true (set_use_store true s))))))) =
    (r, set_gc_fun anything (set_regs l2 (set_code (fromAList (compile c (toAList (code s))))
          (set_use_alloc false (set_use_stack true (set_use_store true t)))))) /\
    (r <> NONE -> r = SOME (Halt (Word (n2w 1)))) /\ regs t ⊑ l2 /\ (r = NONE -> FLOOKUP l2 0 = SOME ret).
Proof.
  intros w s r t conf l ret c anything (H & Hr & Hgc & Hbm & Hst & Hl0 & Hl1).
  destruct (gc_kind conf) as [ | | gs] eqn:Hk.
  - exact (alloc_correct_lemma_None w s r t conf l ret c anything (conj H (conj Hr (conj Hgc (conj Hk (conj Hbm (conj Hst (conj Hl0 Hl1)))))))).
  - exact (alloc_correct_lemma_Simple w s r t conf l ret c anything (conj H (conj Hr (conj Hgc (conj Hk (conj Hbm (conj Hst (conj Hl0 Hl1)))))))).
  - exact (alloc_correct_lemma_Generational gs w s r t conf l ret c anything (conj H (conj Hr (conj Hgc (conj Hk (conj Hbm (conj Hst (conj Hl0 Hl1)))))))).
Qed.


Lemma lookup_gc_stub c (X : list (N * prog a)) :
  lookup gc_stub_location (fromAList (compile c X)) = SOME (Seq (word_gc_code c) (Return 0)).
Proof.
  rewrite sptree.lookup_fromAList. unfold compile, stubs. cbn [app ALOOKUP].
  destruct (decide (gc_stub_location = gc_stub_location)) as [_|E]; [reflexivity|contradiction].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "alloc_correct" *)
Local Theorem alloc_correct : forall (w : word a) (s : state) r t c (l : fmap N (word_loc a)) n' m anything,
  alloc w s = (r, t) /\ r <> SOME Error /\ gc_fun s = word_gc_fun c /\
  LENGTH (bitmaps s) < dimword a - 1 /\ LENGTH (stack s) * (dimindex a DIV 8) < dimword a /\
  FLOOKUP l 1 = SOME (Word w) ->
  exists ck l2,
    evaluate (Call (SOME (Skip, (0, (n', m)))) (inl gc_stub_location) NONE,
              set_code (fromAList (compile c (toAList (code s))))
                (set_gc_fun anything (set_regs l (set_clock (clock s + ck)
                  (set_use_alloc false (set_use_stack true (set_use_store true s))))))) =
    (r, set_code (fromAList (compile c (toAList (code s))))
          (set_gc_fun anything (set_regs l2 (set_use_alloc false (set_use_stack true (set_use_store true t)))))) /\
    regs t ⊑ l2.
Proof.
  intros w s r t c l n' m anything (H & Hr & Hgc & Hbm & Hst & Hl1).
  destruct (alloc_correct_lemma w s r t c (l |+ (0, Loc n' m)) (Loc n' m) c anything) as (ck & l2 & Ev & Hh & Hsub & H0).
  { splits; try assumption. all: rewrite FLOOKUP_UPD; cbn [N.eqb Pos.eqb]; first [reflexivity | exact Hl1]. }
  exists (ck + 1), l2. split; [|exact Hsub].
  rewrite evaluate_eqn. cbn [evaluate_body]. stk_fields. unfold find_code. rewrite lookup_gc_stub.
  replace (clock s + (ck + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
  rewrite fix_clock_evaluate. rewrite ev_seq. autorewrite with nf. nf_fields. rw_eval Ev.
  destruct r as [res|].
  - assert (Hres : res = Halt (Word (n2w 1))) by (specialize (Hh ltac:(discriminate)); congruence). subst res.
    cbn beta iota. try (f_equal; apply state_ext; nf_fields; reflexivity).
  - specialize (H0 eq_refl). cbn beta iota. rewrite evaluate_eqn. cbn [evaluate_body]. unfold get_var. stk_fields.
    rewrite H0. cbn beta iota. rewrite (proj2 (bool_decide_spec _) eq_refl). cbn [negb].
    rewrite evaluate_eqn. cbn [evaluate_body]. try (f_equal; apply state_ext; nf_fields; reflexivity).
Qed.


Lemma alloc_ok_holds anything c : alloc_ok anything c (a := a) (cfg_t := cfg_t) (ffi_t := ffi_t).
Proof.
  intros w s r t l n' m H. destruct (alloc_correct w s r t c l n' m anything H) as (ck & l2 & E & Hs).
  destruct H as (Ha & _). destruct (alloc_const _ _ _ _ Ha) as (_ & _ & _ & _ & _ & Hcode & _).
  exists ck, l2. split; [|exact Hs]. unfold tr_alloc. rw_eval E. rewrite Hcode. reflexivity.
Qed.


(** HOL's free variables [compile_rest] and [anything] are quantified last. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "comp_correct" *)
Theorem comp_correct : forall p (s : state) r t m n c regs0 compile_rest anything,
  evaluate (p, s) = (r, t) /\ r <> SOME Error /\ alloc_arg p /\
  (forall k prog0, lookup k (code s) = SOME prog0 -> k <> gc_stub_location /\ alloc_arg prog0) /\
  (forall n k p, MEM (k, p) (FST (SND (compile_oracle s n))) -> k <> gc_stub_location /\ alloc_arg p) /\
  gc_fun s = word_gc_fun c /\ use_alloc s /\
  LENGTH (stack s) * (dimindex a DIV 8) < dimword a /\ regs s ⊑ regs0 /\ use_stack s /\
  LENGTH (bitmaps s) + LENGTH (wordSem.buffer_buffer (data_buffer s)) + wordSem.space_left (data_buffer s) <
    dimword a - 1 /\
  stackSem.compile s = (fun c0 => compile_rest c0 ∘ MAP prog_comp) ->
  exists ck regs1,
    evaluate (FST (comp n m p),
      set_code (fromAList (compile c (toAList (code s)))) (set_compile compile_rest
        (set_compile_oracle ((I ## (MAP prog_comp ## I)) ∘ compile_oracle s) (set_gc_fun anything
          (set_regs regs0 (set_clock (clock s + ck)
            (set_use_alloc false (set_use_stack true (set_use_store true s))))))))) =
    (r, set_code (fromAList (compile c (toAList (code t)))) (set_compile compile_rest
          (set_compile_oracle ((I ## (MAP prog_comp ## I)) ∘ compile_oracle t) (set_gc_fun anything
            (set_regs regs1 (set_use_alloc false (set_use_stack true (set_use_store true t)))))))) /\
    regs t ⊑ regs1 /\
    LENGTH (bitmaps t) + LENGTH (wordSem.buffer_buffer (data_buffer t)) + wordSem.space_left (data_buffer t) <
      dimword a - 1 /\
    ((forall w, r <> SOME (Halt w)) -> LENGTH (stack t) * (dimindex a DIV 8) < dimword a).
Proof.
  intros p s r t m n c regs0 compile_rest anything
    (H & Hr & Ha & Hcode & Hor & Hgc & Hua & Hst & Hsub & Hus & Hlbd & Hcomp).
  assert (Hci : CI compile_rest c s) by (unfold CI, LST, LBD; splits; assumption).
  destruct (comp_correct_gen compile_rest anything c (alloc_ok_holds anything c) (p, s) r t H Hr Ha Hci m n regs0 Hsub)
    as (ck & regs1 & Ev & Hs1 & Hb1 & Hl1).
  exists ck, regs1. splits; [|exact Hs1|exact Hb1|exact Hl1].
  cbn [fst snd] in Ev. rw_eval Ev. unfold tr, frame. try (f_equal; apply state_ext; nf_fields; reflexivity).
Qed.


(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "with_same_regs_lemma" *)
Local Theorem with_same_regs_lemma : forall (s : state) cc oracle anything k c0,
  set_regs (regs s) (set_compile cc (set_compile_oracle oracle (set_gc_fun anything (set_use_stack true
    (set_use_store true (set_use_alloc false (set_clock k (set_code c0 s)))))))) =
  set_compile cc (set_compile_oracle oracle (set_gc_fun anything (set_use_stack true
    (set_use_store true (set_use_alloc false (set_clock k (set_code c0 s))))))).
Proof. intros. apply state_ext; nf_fields; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "compile_semantics" *)
Theorem compile_semantics : forall (s : state) c compile_rest anything start,
  (forall k prog0, lookup k (code s) = SOME prog0 -> k <> gc_stub_location /\ alloc_arg prog0) /\
  (forall n k p, MEM (k, p) (FST (SND (compile_oracle s n))) -> k <> gc_stub_location /\ alloc_arg p) /\
  gc_fun s = word_gc_fun c /\
  LENGTH (bitmaps s) + LENGTH (wordSem.buffer_buffer (data_buffer s)) + wordSem.space_left (data_buffer s) <
    dimword a - 1 /\
  LENGTH (stack s) * (dimindex a DIV 8) < dimword a /\
  use_stack s /\ use_alloc s /\
  stackSem.compile s = (fun c0 => compile_rest c0 ∘ MAP prog_comp) /\
  semantics start s <> Fail ->
  semantics start (set_use_alloc false (set_use_stack true (set_use_store true
    (set_compile_oracle ((I ## (MAP prog_comp ## I)) ∘ compile_oracle s) (set_compile compile_rest
      (set_gc_fun anything (set_code (fromAList (compile c (toAList (code s)))) s))))))) =
  semantics start s.
Proof.
  intros s c compile_rest anything start (Hcode & Hor & Hgc & Hlbd & Hst & Hus & Hua & Hcomp & HF).
  assert (Hci : CI compile_rest c s) by (unfold CI, LST, LBD; splits; assumption).
  rewrite <- (compile_semantics_gen compile_rest anything c (alloc_ok_holds anything c) s start Hci HF).
  try (f_equal; unfold tr, frame; apply state_ext; nf_fields; reflexivity).
Qed.


(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "make_init_def" *)
Definition make_init (c : config) (code0 : spt (prog a)) (oracle : N -> cfg_t * (list (N * prog a) * list (word a)))
    (s : state) : state :=
  set_compile_oracle oracle (set_compile (fun c0 => stackSem.compile s c0 ∘ MAP prog_comp)
    (set_gc_fun (word_gc_fun c) (set_use_stack true (set_use_alloc true (set_code code0 s))))).

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "prog_comp_lambda" *)
Theorem prog_comp_lambda : @prog_comp a = (fun '(n, p) => (n, FST (comp n (next_lab p 2) p))).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "make_init_semantics" *)
Theorem make_init_semantics : forall code0 oracle (s : state) c start,
  (forall k prog0, ALOOKUP code0 k = SOME prog0 -> k <> gc_stub_location /\ alloc_arg prog0) /\
  (forall n k p, MEM (k, p) (FST (SND (oracle n))) -> k <> gc_stub_location /\ alloc_arg p) /\
  use_stack s /\ use_store s /\ ~ use_alloc s /\ code s = fromAList (compile c code0) /\
  compile_oracle s = (I ## (MAP prog_comp ## I)) ∘ oracle /\
  LENGTH (bitmaps s) + LENGTH (wordSem.buffer_buffer (data_buffer s)) + wordSem.space_left (data_buffer s) <
    dimword a - 1 /\
  LENGTH (stack s) * (dimindex a DIV 8) < dimword a /\
  ALL_DISTINCT (MAP FST code0) /\
  semantics start (make_init c (fromAList code0) oracle s) <> Fail ->
  semantics start s = semantics start (make_init c (fromAList code0) oracle s).
Proof.
  intros code0 oracle s c start (Hcode & Hor & Hus & Hust & Hua & Hc & Ho & Hlbd & Hst & _ & HF).
  rewrite <- (compile_semantics (make_init c (fromAList code0) oracle s) c (stackSem.compile s) (gc_fun s) start).
  2:{ unfold make_init. nf_fields. splits; try assumption; try reflexivity.
      intros k p0 Hl. rewrite sptree.lookup_fromAList in Hl. exact (Hcode k p0 Hl). }
  f_equal. unfold make_init. apply state_ext; nf_fields; try reflexivity.
  - exact Ho.
  - exact Hus.
  - exact Hust.
  - apply Bool.not_true_iff_false. exact Hua.
  - rewrite Hc. apply sptree.spt_eq_thm; [split; apply sptree.wf_fromAList|]. intros k.
    rewrite !sptree.lookup_fromAList. unfold compile. rewrite !ALOOKUP_APPEND.
    destruct (ALOOKUP (stubs c) k); [reflexivity|].
    rewrite !prog_comp_lemma, !ALOOKUP_MAP_2, sptree.ALOOKUP_toAList, sptree.lookup_fromAList. reflexivity.
Qed.

End AllocAll.

(** ** The HOL restatements of [word_gc_fun] and [gc] for each collector *)

Section GcThms.
Context {a : N} {cfg_t ffi_t : Type}.
Local Abbreviation state := (stackSem.state a cfg_t ffi_t).
Local Open Scope fmap_scope.

(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_fun_thm" 481 *)
Local Theorem word_gc_fun_thm_Simple : forall conf roots (m : word a -> word_loc a) dm s,
  gc_kind conf = Simple ->
  word_gc_fun conf (roots, (m, (dm, s))) =
  let '(w1, (i1, (pa1, (m1, c1)))) :=
    word_gc_move conf (FAPPLY s Globals, (n2w 0, (wordSem.theWord (FAPPLY s OtherHeap), (wordSem.theWord (FAPPLY s CurrHeap), (m, dm))))) in
  let '(ws2, (i2, (pa2, (m2, c2)))) :=
    word_gc_move_roots conf (roots, (i1, (pa1, (wordSem.theWord (FAPPLY s CurrHeap), (m1, dm))))) in
  let '(i1, (pa1, (m1, c2))) :=
    word_gc_move_loop (dimword a) conf
      (wordSem.theWord (FAPPLY s OtherHeap), (i2, (pa2, (wordSem.theWord (FAPPLY s CurrHeap), (m2, (dm, andb c1 c2)))))) in
  let s1 := s |++ [(CurrHeap, Word (wordSem.theWord (FAPPLY s OtherHeap)));
                   (OtherHeap, Word (wordSem.theWord (FAPPLY s CurrHeap)));
                   (NextFree, Word pa1);
                   (TriggerGC, Word (wordSem.theWord (FAPPLY s OtherHeap) + wordSem.theWord (FAPPLY s HeapLength))%w);
                   (EndOfHeap, Word (wordSem.theWord (FAPPLY s OtherHeap) + wordSem.theWord (FAPPLY s HeapLength))%w);
                   (Globals, w1);
                   (GlobReal, glob_real conf (wordSem.theWord (FAPPLY s OtherHeap)) w1)] in
  if andb ⌜word_gc_fun_assum conf s⌝ c2 then SOME (ws2, (m1, s1)) else NONE.
Proof.
  intros conf roots m dm s Hk. unfold word_gc_fun. rewrite Hk. cbv zeta. unfold word_full_gc.
  rewrite (proj2 (word_gc_move_roots_def _ _ _ _ _ _ _ _)).
  destruct (word_gc_move conf _) as (w1, (i1, (pa1, (m1, c1)))).
  destruct (word_gc_move_roots conf _) as (ws2, (i2, (pa2, (m2, c2)))).
  destruct (word_gc_move_loop _ _ _) as (i3, (pa3, (m3, c3))). reflexivity.
Qed.


(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "gc_thm" 554 *)
Local Theorem gc_thm_Simple : forall (s : state) conf,
  gc_fun s = word_gc_fun conf /\ gc_kind conf = Simple ->
  gc s =
  if (LENGTH (stack s) <? stack_space s)%N then NONE else
  let unused := TAKE (stack_space s) (stack s) in
  let stack0 := DROP (stack_space s) (stack s) in
  let '(w1, (i1, (pa1, (m1, c1)))) :=
    word_gc_move conf (FAPPLY (store s) Globals, (n2w 0, (wordSem.theWord (FAPPLY (store s) OtherHeap),
      (wordSem.theWord (FAPPLY (store s) CurrHeap), (memory s, mdomain s))))) in
  let '(stack1, (i2, (pa2, (m2, c2)))) :=
    word_gc_move_roots_bitmaps conf (stack0, (bitmaps s, (i1, (pa1,
      (wordSem.theWord (FAPPLY (store s) CurrHeap), (m1, mdomain s)))))) in
  let '(i1, (pa1, (m1, c2))) :=
    word_gc_move_loop (dimword a) conf (wordSem.theWord (FAPPLY (store s) OtherHeap), (i2, (pa2,
      (wordSem.theWord (FAPPLY (store s) CurrHeap), (m2, (mdomain s, andb c1 c2)))))) in
  let s1 := store s |++ [(CurrHeap, Word (wordSem.theWord (FAPPLY (store s) OtherHeap)));
                         (OtherHeap, Word (wordSem.theWord (FAPPLY (store s) CurrHeap)));
                         (NextFree, Word pa1);
                         (TriggerGC, Word (wordSem.theWord (FAPPLY (store s) OtherHeap) +
                                           wordSem.theWord (FAPPLY (store s) HeapLength))%w);
                         (EndOfHeap, Word (wordSem.theWord (FAPPLY (store s) OtherHeap) +
                                           wordSem.theWord (FAPPLY (store s) HeapLength))%w);
                         (Globals, w1);
                         (GlobReal, glob_real conf (wordSem.theWord (FAPPLY (store s) OtherHeap)) w1)] in
  if andb ⌜word_gc_fun_assum conf (store s)⌝ c2
  then SOME (set_memory m1 (set_regs FEMPTY (set_store_fld s1 (set_stack (unused ++ stack1) s))))
  else NONE.
Proof.
  intros s conf [Hgc Hk]. unfold gc. destruct (LENGTH (stack s) <? stack_space s)%N; [reflexivity|].
  cbv zeta. rewrite Hgc. unfold word_gc_move_roots_bitmaps.
  destruct (enc_stack (bitmaps s) (DROP (stack_space s) (stack s))) as [wl|] eqn:Ee.
  - rewrite (word_gc_fun_thm_Simple conf wl (memory s) (mdomain s) (store s) Hk). cbv zeta.
    destruct (word_gc_move conf _) as (w1, (i1, (pa1, (m1, c1)))).
    destruct (word_gc_move_roots conf _) as (ws2, (i2, (pa2, (m2, c2)))). cbn [HD TL].
    destruct (dec_stack (bitmaps s) ws2 _) as [stack1|] eqn:Ed; rewrite ?Ed.
    + destruct (word_gc_move_loop _ _ _) as (i3, (pa3, (m3, c3))).
      destruct (⌜word_gc_fun_assum conf (store s)⌝ && c3); [|reflexivity]. rewrite Ed. reflexivity.
    + cbn beta iota zeta.
      destruct (word_gc_move_loop (dimword a) conf (_, (i2, (pa2, (_, (m2, (mdomain s, andb c1 c2)))))))
        as (iL, (paL, (mL, cL))).
      destruct (andb _ cL); cbn beta iota; rewrite ?Ed.
      all: destruct (word_gc_move_loop _ _ _) as (i3, (pa3, (m3, c3))) eqn:El;
        rewrite ?Bool.andb_false_r in El; apply word_gc_move_loop_F in El;
        destruct c3; [exfalso; apply El; reflexivity|]; rewrite Bool.andb_false_r; reflexivity.
  - destruct (word_gc_move conf _) as (w1, (i1, (pa1, (m1, c1)))).
    destruct (word_gc_move_loop _ _ _) as (i3, (pa3, (m3, c3))) eqn:El.
    rewrite ?Bool.andb_false_r in El. apply word_gc_move_loop_F in El.
    destruct c3; [exfalso; apply El; reflexivity|]. rewrite Bool.andb_false_r. reflexivity.
Qed.


(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_fun_thm" 1731 *)
Local Theorem word_gc_fun_thm_Gen : forall conf gen_sizes roots (m : word a -> word_loc a) dm s,
  gc_kind conf = Generational gen_sizes ->
  word_gc_fun conf (roots, (m, (dm, s))) =
  if negb ⌜word_gc_fun_assum conf s⌝ then NONE else
  if ⌜word_gen_gc_can_do_partial gen_sizes s⌝ then
    let '(roots1, (i1, (pa1, (m1, c2)))) :=
      (let '(roots, (i, (pa, (m, c1)))) :=
         (let '(roots, (i, (pa, (m, c1)))) :=
            word_gen_gc_partial_move_roots conf (FAPPLY s Globals :: roots, ((wordSem.theWord (FAPPLY s GenStart)) >>> word_shift a, ((wordSem.theWord (FAPPLY s OtherHeap)), ((wordSem.theWord (FAPPLY s CurrHeap)),
              (m, (dm, ((wordSem.theWord (FAPPLY s GenStart)), - n2w 1 * (wordSem.theWord (FAPPLY s CurrHeap)) + (wordSem.theWord (FAPPLY s EndOfHeap)))))))))%w in
          let '(i, (pa, (m, c2))) :=
            word_gen_gc_partial_move_ref_list (dimword a) conf ((wordSem.theWord (FAPPLY s EndOfHeap)), (i, (pa, ((wordSem.theWord (FAPPLY s CurrHeap)), (m, (dm, (c1, ((wordSem.theWord (FAPPLY s GenStart)),
              ((- n2w 1 * (wordSem.theWord (FAPPLY s CurrHeap)) + (wordSem.theWord (FAPPLY s EndOfHeap)))%w, ((wordSem.theWord (FAPPLY s CurrHeap)) + (wordSem.theWord (FAPPLY s HeapLength)))%w))))))))) in
          let '(i, (pa, (m, c3))) :=
            word_gen_gc_partial_move_data conf (dimword a) ((wordSem.theWord (FAPPLY s OtherHeap)), (i, (pa, ((wordSem.theWord (FAPPLY s CurrHeap)), (m, (dm, ((wordSem.theWord (FAPPLY s GenStart)),
              (- n2w 1 * (wordSem.theWord (FAPPLY s CurrHeap)) + (wordSem.theWord (FAPPLY s EndOfHeap)))%w))))))) in
          (roots, (i, (pa, (m, andb c2 c3))))) in
       let '(b1, (m, c2)) := memcpy ((pa + - n2w 1 * (wordSem.theWord (FAPPLY s OtherHeap))) >>> word_shift a)%w (wordSem.theWord (FAPPLY s OtherHeap)) ((wordSem.theWord (FAPPLY s CurrHeap)) + (wordSem.theWord (FAPPLY s GenStart)))%w m dm in
       (roots, (i, (b1, (m, andb c1 c2))))) in
    if andb c2 (andb ((wordSem.theWord (FAPPLY s AllocSize)) <=+ - n2w 1 * pa1 + (wordSem.theWord (FAPPLY s EndOfHeap)))%w ((wordSem.theWord (FAPPLY s AllocSize)) <=+ new_trig ((wordSem.theWord (FAPPLY s EndOfHeap)) - pa1)%w (wordSem.theWord (FAPPLY s AllocSize)) gen_sizes)%w)
    then SOME (TL roots1, (m1, s |++ [(CurrHeap, Word (wordSem.theWord (FAPPLY s CurrHeap))); (OtherHeap, Word (wordSem.theWord (FAPPLY s OtherHeap))); (NextFree, Word pa1);
                                      (GenStart, Word (pa1 + - n2w 1 * (wordSem.theWord (FAPPLY s CurrHeap)))%w);
                                      (TriggerGC, Word (pa1 + new_trig ((wordSem.theWord (FAPPLY s EndOfHeap)) - pa1) (wordSem.theWord (FAPPLY s AllocSize)) gen_sizes)%w);
                                      (Globals, HD roots1); (GlobReal, glob_real conf (wordSem.theWord (FAPPLY s CurrHeap)) (HD roots1));
                                      (Temp (n2w 0), Word (n2w 0)); (Temp (n2w 1), Word (n2w 0))]))
    else NONE
  else
    let new_end := ((wordSem.theWord (FAPPLY s OtherHeap)) + (wordSem.theWord (FAPPLY s HeapLength)))%w in
    let len := ((wordSem.theWord (FAPPLY s HeapLength)) >>> word_shift a)%w in
    let '(w1, (i1, (pa1, (ib', (pb', (m1, c1)))))) :=
      word_gen_gc_move conf (FAPPLY s Globals, (n2w 0, ((wordSem.theWord (FAPPLY s OtherHeap)), (len, (new_end, ((wordSem.theWord (FAPPLY s CurrHeap)), (m, dm))))))) in
    let '(ws2, (i2, (pa2, (ib2, (pb2, (m2, c2)))))) :=
      word_gen_gc_move_roots conf (roots, (i1, (pa1, (ib', (pb', ((wordSem.theWord (FAPPLY s CurrHeap)), (m1, dm))))))) in
    let '(i3, (pa3, (ib3, (pb3, (m3, c3))))) :=
      word_gen_gc_move_loop conf (w2n len) ((wordSem.theWord (FAPPLY s OtherHeap)), (i2, (pa2, (ib2, (pb2, (new_end, ((wordSem.theWord (FAPPLY s CurrHeap)), (m2, dm)))))))) in
    let a0 := (wordSem.theWord (FAPPLY s AllocSize)) in
    let s1 := s |++ [(CurrHeap, Word (wordSem.theWord (FAPPLY s OtherHeap))); (OtherHeap, Word (wordSem.theWord (FAPPLY s CurrHeap))); (NextFree, Word pa3);
                     (GenStart, Word (pa3 - (wordSem.theWord (FAPPLY s OtherHeap)))%w); (TriggerGC, Word (pa3 + new_trig (pb3 - pa3) a0 gen_sizes)%w);
                     (EndOfHeap, Word pb3); (Globals, w1); (GlobReal, glob_real conf (wordSem.theWord (FAPPLY s OtherHeap)) w1);
                     (Temp (n2w 0), Word (n2w 0)); (Temp (n2w 1), Word (n2w 0)); (Temp (n2w 2), Word (n2w 0));
                     (Temp (n2w 3), Word (n2w 0)); (Temp (n2w 4), Word (n2w 0)); (Temp (n2w 5), Word (n2w 0));
                     (Temp (n2w 6), Word (n2w 0))] in
    if andb ⌜word_gc_fun_assum conf s⌝ (andb c1 (andb c2 c3)) then SOME (ws2, (m3, s1)) else NONE.
Proof.
  intros conf gen_sizes roots m dm s Hk. unfold word_gc_fun. rewrite Hk. cbv zeta.
  destruct ⌜word_gc_fun_assum conf s⌝ eqn:Ea; cbn [negb]; [|reflexivity].
  destruct ⌜word_gen_gc_can_do_partial gen_sizes s⌝ eqn:Ecp.
  - unfold word_gen_gc_partial_full, word_gen_gc_partial. cbv zeta.
    replace ((wordSem.theWord (FAPPLY s EndOfHeap)) - (wordSem.theWord (FAPPLY s CurrHeap)))%w with (- n2w 1 * (wordSem.theWord (FAPPLY s CurrHeap)) + (wordSem.theWord (FAPPLY s EndOfHeap)))%w by word_ring.
    replace ((wordSem.theWord (FAPPLY s CurrHeap)) + (- n2w 1 * (wordSem.theWord (FAPPLY s CurrHeap)) + (wordSem.theWord (FAPPLY s EndOfHeap))))%w with (wordSem.theWord (FAPPLY s EndOfHeap)) by word_ring.
    destruct (word_gen_gc_partial_move_roots conf _) as (r1, (i1, (pa1, (m1, c1)))).
    destruct (word_gen_gc_partial_move_ref_list _ _ _) as (i2, (pa2, (m2, c2))).
    destruct (word_gen_gc_partial_move_data _ _ _) as (i3, (pa3, (m3, c3))).
    replace (pa3 - (wordSem.theWord (FAPPLY s OtherHeap)))%w with (pa3 + - n2w 1 * (wordSem.theWord (FAPPLY s OtherHeap)))%w by word_ring.
    destruct (memcpy _ _ _ _ _) as (b1, (m4, c4)).
    replace ((wordSem.theWord (FAPPLY s EndOfHeap)) - b1)%w with (- n2w 1 * b1 + (wordSem.theWord (FAPPLY s EndOfHeap)))%w at 1 by word_ring.
    replace (b1 - (wordSem.theWord (FAPPLY s CurrHeap)))%w with (b1 + - n2w 1 * (wordSem.theWord (FAPPLY s CurrHeap)))%w by word_ring.
    reflexivity.
  - unfold word_gen_gc. cbv zeta.
    rewrite (proj2 (word_gen_gc_move_roots_def _ _ _ _ _ _ _ _ _ _)).
    destruct (word_gen_gc_move conf _) as (w1, (i1, (pa1, (ib1, (pb1, (m1, c1)))))).
    destruct (word_gen_gc_move_roots conf _) as (ws2, (i2, (pa2, (ib2, (pb2, (m2, c2)))))).
    destruct (word_gen_gc_move_loop _ _ _) as (i3, (pa3, (ib3, (pb3, (m3, c3))))).
    cbn [HD TL andb]. rewrite Bool.andb_assoc. destruct (c1 && c2 && c3); reflexivity.
Qed.


(*! HOL "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "gc_thm" 1884 *)
Lemma add_neg1 (x y : word a) : (x + - n2w 1 * y)%w = (x - y)%w.
Proof. word_ring. Qed.

Ltac gc_destr :=
  repeat match goal with
  | |- context [word_gen_gc_partial_move_ref_list ?k ?c ?x] =>
      let E := fresh "E" in destruct (word_gen_gc_partial_move_ref_list k c x) as (?, (?, (?, ?))) eqn:E;
      try (rewrite ?Bool.andb_false_r in E; unfold word_gen_gc_partial_move_ref_list in E;
           apply word_gen_gc_partial_move_ref_list_f_F in E;
           match type of E with ?v = false => subst v end)
  | |- context [word_gen_gc_partial_move_data ?c ?k ?x] =>
      destruct (word_gen_gc_partial_move_data c k x) as (?, (?, (?, ?)))
  | |- context [memcpy ?a1 ?a2 ?a3 ?a4 ?a5] => destruct (memcpy a1 a2 a3 a4 a5) as (?, (?, ?))
  | |- context [word_gen_gc_move_loop ?c ?k ?x] =>
      destruct (word_gen_gc_move_loop c k x) as (?, (?, (?, (?, (?, ?)))))
  | |- context [word_gen_gc_move ?cf ?x] =>
      destruct (word_gen_gc_move cf x) as (?, (?, (?, (?, (?, (?, ?))))))
  | |- context [word_gen_gc_move_roots ?c ?x] =>
      destruct (word_gen_gc_move_roots c x) as (?, (?, (?, (?, (?, (?, ?))))))
  | |- context [word_gen_gc_partial_move ?cf ?x] =>
      destruct (word_gen_gc_partial_move cf x) as (?, (?, (?, (?, ?))))
  end;
  repeat (cbn beta iota zeta; cbn [HD TL andb];
          rewrite ?Bool.andb_false_r, ?Bool.andb_true_r;
          first [ match goal with |- context [if ?b then _ else _] => is_var b; destruct b end
                | match goal with |- context [andb ?b _] => is_var b; destruct b end
                | match goal with |- context [if ?b then _ else _] => destruct b end ]);
  cbn beta iota; cbn [HD TL]; try reflexivity.

Local Theorem gc_thm_Gen : forall (s : state) conf gen_sizes,
  gc_fun s = word_gc_fun conf /\ gc_kind conf = Generational gen_sizes ->
  gc s =
  if (LENGTH (stack s) <? stack_space s)%N then NONE else
  if negb ⌜word_gc_fun_assum conf (store s)⌝ then NONE else
  if ⌜word_gen_gc_can_do_partial gen_sizes (store s)⌝ then
    let unused := TAKE (stack_space s) (stack s) in
    let stack0 := DROP (stack_space s) (stack s) in
    let '(w1, (i1, (pa1, (m1, c1)))) :=
      word_gen_gc_partial_move conf (FAPPLY (store s) Globals, ((wordSem.theWord (FAPPLY (store s) GenStart)) >>> word_shift a, ((wordSem.theWord (FAPPLY (store s) OtherHeap)), ((wordSem.theWord (FAPPLY (store s) CurrHeap)),
        (memory s, (mdomain s, ((wordSem.theWord (FAPPLY (store s) GenStart)), (wordSem.theWord (FAPPLY (store s) EndOfHeap)) - (wordSem.theWord (FAPPLY (store s) CurrHeap)))))))))%w in
    let '(ws2, (i1, (pa1, (m1, c2)))) :=
      word_gen_gc_partial_move_roots_bitmaps conf (stack0, (bitmaps s, (i1, (pa1, ((wordSem.theWord (FAPPLY (store s) CurrHeap)), (m1, (mdomain s,
        ((wordSem.theWord (FAPPLY (store s) GenStart)), ((wordSem.theWord (FAPPLY (store s) EndOfHeap)) - (wordSem.theWord (FAPPLY (store s) CurrHeap)))%w)))))))) in
    let '(i1, (pa1, (m1, c3))) :=
      word_gen_gc_partial_move_ref_list (dimword a) conf ((wordSem.theWord (FAPPLY (store s) EndOfHeap)), (i1, (pa1, ((wordSem.theWord (FAPPLY (store s) CurrHeap)), (m1, (mdomain s,
        (andb c1 c2, ((wordSem.theWord (FAPPLY (store s) GenStart)), (((wordSem.theWord (FAPPLY (store s) EndOfHeap)) - (wordSem.theWord (FAPPLY (store s) CurrHeap)))%w, ((wordSem.theWord (FAPPLY (store s) CurrHeap)) + (wordSem.theWord (FAPPLY (store s) HeapLength)))%w))))))))) in
    let '(i1, (pa1, (m1, c4))) :=
      word_gen_gc_partial_move_data conf (dimword a) ((wordSem.theWord (FAPPLY (store s) OtherHeap)), (i1, (pa1, ((wordSem.theWord (FAPPLY (store s) CurrHeap)), (m1, (mdomain s,
        ((wordSem.theWord (FAPPLY (store s) GenStart)), ((wordSem.theWord (FAPPLY (store s) EndOfHeap)) - (wordSem.theWord (FAPPLY (store s) CurrHeap)))%w))))))) in
    let '(b1, (m1, c5)) := memcpy ((pa1 - (wordSem.theWord (FAPPLY (store s) OtherHeap))) >>> word_shift a)%w (wordSem.theWord (FAPPLY (store s) OtherHeap)) ((wordSem.theWord (FAPPLY (store s) CurrHeap)) + (wordSem.theWord (FAPPLY (store s) GenStart)))%w m1 (mdomain s) in
    let s1 := store s |++ [(CurrHeap, Word (wordSem.theWord (FAPPLY (store s) CurrHeap))); (OtherHeap, Word (wordSem.theWord (FAPPLY (store s) OtherHeap))); (NextFree, Word b1);
                           (GenStart, Word (b1 - (wordSem.theWord (FAPPLY (store s) CurrHeap)))%w);
                           (TriggerGC, Word (b1 + new_trig ((wordSem.theWord (FAPPLY (store s) EndOfHeap)) - b1) (wordSem.theWord (FAPPLY (store s) AllocSize)) gen_sizes)%w);
                           (Globals, w1); (GlobReal, glob_real conf (wordSem.theWord (FAPPLY (store s) CurrHeap)) w1);
                           (Temp (n2w 0), Word (n2w 0)); (Temp (n2w 1), Word (n2w 0))] in
    let c6 := andb ((wordSem.theWord (FAPPLY (store s) AllocSize)) <=+ (wordSem.theWord (FAPPLY (store s) EndOfHeap)) - b1)%w ((wordSem.theWord (FAPPLY (store s) AllocSize)) <=+ new_trig ((wordSem.theWord (FAPPLY (store s) EndOfHeap)) - b1) (wordSem.theWord (FAPPLY (store s) AllocSize)) gen_sizes)%w in
    if andb ⌜word_gc_fun_assum conf (store s)⌝ (andb c3 (andb c4 (andb c5 c6)))
    then SOME (set_memory m1 (set_regs FEMPTY (set_store_fld s1 (set_stack (unused ++ ws2) s))))
    else NONE
  else
    let unused := TAKE (stack_space s) (stack s) in
    let stack0 := DROP (stack_space s) (stack s) in
    let new_end := ((wordSem.theWord (FAPPLY (store s) OtherHeap)) + (wordSem.theWord (FAPPLY (store s) HeapLength)))%w in
    let len := ((wordSem.theWord (FAPPLY (store s) HeapLength)) >>> word_shift a)%w in
    let '(w1, (i1, (pa1, (ib', (pb', (m1, c1)))))) :=
      word_gen_gc_move conf (FAPPLY (store s) Globals, (n2w 0, ((wordSem.theWord (FAPPLY (store s) OtherHeap)), (len, (new_end, ((wordSem.theWord (FAPPLY (store s) CurrHeap)), (memory s, mdomain s))))))) in
    let '(ws2, (i2, (pa2, (ib2, (pb2, (m2, c2)))))) :=
      word_gen_gc_move_roots_bitmaps conf (stack0, (bitmaps s, (i1, (pa1, (ib', (pb', ((wordSem.theWord (FAPPLY (store s) CurrHeap)), (m1, mdomain s)))))))) in
    let '(i3, (pa3, (ib3, (pb3, (m3, c3))))) :=
      word_gen_gc_move_loop conf (w2n len) ((wordSem.theWord (FAPPLY (store s) OtherHeap)), (i2, (pa2, (ib2, (pb2, (new_end, ((wordSem.theWord (FAPPLY (store s) CurrHeap)), (m2, mdomain s)))))))) in
    let s1 := store s |++ [(CurrHeap, Word (wordSem.theWord (FAPPLY (store s) OtherHeap))); (OtherHeap, Word (wordSem.theWord (FAPPLY (store s) CurrHeap))); (NextFree, Word pa3);
                           (GenStart, Word (pa3 + - n2w 1 * (wordSem.theWord (FAPPLY (store s) OtherHeap)))%w);
                           (TriggerGC, Word (pa3 + new_trig (pb3 - pa3) (wordSem.theWord (FAPPLY (store s) AllocSize)) gen_sizes)%w);
                           (EndOfHeap, Word pb3); (Globals, w1); (GlobReal, glob_real conf (wordSem.theWord (FAPPLY (store s) OtherHeap)) w1);
                           (Temp (n2w 0), Word (n2w 0)); (Temp (n2w 1), Word (n2w 0)); (Temp (n2w 2), Word (n2w 0));
                           (Temp (n2w 3), Word (n2w 0)); (Temp (n2w 4), Word (n2w 0)); (Temp (n2w 5), Word (n2w 0));
                           (Temp (n2w 6), Word (n2w 0))] in
    if andb ⌜word_gc_fun_assum conf (store s)⌝ (andb c1 (andb c2 c3))
    then SOME (set_memory m3 (set_regs FEMPTY (set_store_fld s1 (set_stack (unused ++ ws2) s))))
    else NONE.
Proof.
  intros s conf gen_sizes [Hgc Hk]. unfold gc. destruct (LENGTH (stack s) <? stack_space s)%N; [reflexivity|].
  cbv zeta. rewrite Hgc.
  set (OTHER := wordSem.theWord (FAPPLY (store s) OtherHeap)).
  set (CURR := wordSem.theWord (FAPPLY (store s) CurrHeap)).
  set (GSV := wordSem.theWord (FAPPLY (store s) GenStart)).
  set (ENDH := wordSem.theWord (FAPPLY (store s) EndOfHeap)).
  set (LEN := wordSem.theWord (FAPPLY (store s) HeapLength)).
  set (ALLOC := wordSem.theWord (FAPPLY (store s) AllocSize)).
  unfold word_gen_gc_partial_move_roots_bitmaps, word_gen_gc_move_roots_bitmaps.
  destruct (enc_stack (bitmaps s) (DROP (stack_space s) (stack s))) as [wl|] eqn:Ee.
  - rewrite (word_gc_fun_thm_Gen conf gen_sizes wl (memory s) (mdomain s) (store s) Hk). fold OTHER CURR GSV ENDH LEN ALLOC.
    destruct ⌜word_gc_fun_assum conf (store s)⌝ eqn:Ea; cbn [negb andb]; [|reflexivity].
    destruct ⌜word_gen_gc_can_do_partial gen_sizes (store s)⌝ eqn:Ecp.
    + rewrite (proj2 (word_gen_gc_partial_move_roots_def _ _ _ _ _ _ _ _ _ _)).
      replace (- n2w 1 * CURR + ENDH)%w with (ENDH - CURR)%w by word_ring.
      destruct (word_gen_gc_partial_move conf _) as (w1, (i1, (pa1, (m1, c1)))).
      destruct (word_gen_gc_partial_move_roots conf _) as (ws2, (i2, (pa2, (m2, c2)))).
      cbn [HD TL].
      destruct (dec_stack (bitmaps s) ws2 _) as [stack1|] eqn:Ed; rewrite ?Ed.
      * destruct (word_gen_gc_partial_move_ref_list _ _ _) as (i3, (pa3, (m3, c3))).
        destruct (word_gen_gc_partial_move_data _ _ _) as (i4, (pa4, (m4, c4))).
        replace (pa4 + - n2w 1 * OTHER)%w with (pa4 - OTHER)%w by word_ring.
        destruct (memcpy _ _ _ _ _) as (b1, (m5, c5)).
        replace (- n2w 1 * b1 + ENDH)%w with (ENDH - b1)%w by word_ring.
        replace (b1 + - n2w 1 * CURR)%w with (b1 - CURR)%w by word_ring.
        destruct c3, c4, c5; cbn [andb]; try reflexivity;
          destruct (ALLOC <=+ ENDH - b1)%w, (ALLOC <=+ new_trig (ENDH - b1) ALLOC gen_sizes)%w; cbn [andb];
          cbn beta iota; cbn [HD TL]; rewrite ?Ed; try reflexivity.
      * gc_destr. all: rewrite ?Ed; try reflexivity.
    +
      destruct (word_gen_gc_move conf _) as (w1, (i1, (pa1, (ib1, (pb1, (m1, c1)))))).
      destruct (word_gen_gc_move_roots conf _) as (ws2, (i2, (pa2, (ib2, (pb2, (m2, c2)))))).
      cbn [HD TL].
      destruct (dec_stack (bitmaps s) ws2 _) as [stack1|] eqn:Ed; rewrite ?Ed.
      * gc_destr. all: rewrite ?add_neg1, ?Ed; try reflexivity.
      * gc_destr. all: rewrite ?Ed; try reflexivity.
  - destruct ⌜word_gc_fun_assum conf (store s)⌝; cbn [negb]; [|reflexivity].
    destruct ⌜word_gen_gc_can_do_partial gen_sizes (store s)⌝; gc_destr. all: cbn [andb]; rewrite ?Bool.andb_false_r, ?Bool.andb_false_l; cbn beta iota; try reflexivity.
Qed.

End GcThms.