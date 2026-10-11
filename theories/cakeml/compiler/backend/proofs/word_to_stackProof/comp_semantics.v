(** * CakeML [word_to_stackProof]: the semantics theorems

    Part of the port of
    [cakeml/compiler/backend/proofs/word_to_stackProofScript.sml] (HOL lines
    10066-10760): [comp_Call], [state_rel_IMP_semantics],
    [state_rel_IMP_semantics'], [init_state_ok], [make_init] and
    [compile_semantics].

    Left out (ML bindings, not stored theorems): [comp_Call_lemma]
    (inlined in [comp_Call]), [clock_simps], the term bindings [s], [s'],
    [t], the tactic [drule0], and [init_state_ok_semantics] /
    [init_state_ok_semantics'] (inlined in [compile_semantics]).

    HOL proves the two [state_rel_IMP_semantics] theorems by two long
    scripts of the same shape; here their common part is the Galette-only
    [sem_core]: either the stack semantics equals the word semantics, or
    the stack run ends with [Halt (Word 2w)] (stack overflow) with a prefix
    of the word trace while the word run's [stack_max] exceeds its limit.
    Other Galette-only helpers: [some_SOME], [some_NONE], [some_unique]
    (the HOL [some] binder), [wrun_stable]/[srun_stable] (adding clock to a
    finished run), [wio_mono]/[sio_mono]/[io_chain_word] (the io-event
    chains), [wterm_unique], [state_rel_ffi_clock], [n2w_neq0],
    [compile_prog_f].

    Notes: HOL's [{x}] is [x INSERT {}]; HOL's [extend_with_resource_limit']
    takes a [bool], so the [word_lang_safe_for_space] argument of
    [compile_semantics] is [⌜_⌝]; HOL's [EVERY (λn,m,prog. P /\ Q)] over a
    list of triples is an [EVERY] of [P && Q] on the boolean conventions;
    [Fail] (of [behaviour]) is written fully qualified since another
    [Fail] is in scope. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words byte.
From Galette.HOL.src.n_bit.words Require Import lemmas fcp_defs.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.misc.misc Require Import fromList2.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc parmove.
From Galette.cakeml.compiler.backend.reg_alloc.parmove Require proofs.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend Require Import word_to_stack.
From Galette.cakeml.compiler.backend.semantics Require Import wordConvs.
From Galette.cakeml.compiler.backend.semantics Require wordSem.
From Galette.cakeml.compiler.backend.semantics.wordProps Require stack_swap stack_max clock dec_clock.
From Galette.cakeml.compiler.backend.semantics Require Import stackSem stackProps.
From Galette.cakeml.compiler.backend.proofs.word_to_stackProof Require Import basic compile_props state_rel gc stack_rel moves inst comp_lemmas syntax.
From Galette.cakeml.compiler.backend.proofs.word_to_stackProof Require Import comp_correct comp_call.
From Galette.cakeml.compiler.backend.semantics.wordProps Require consts.
From Galette.cakeml.semantics.proofs Require Import semanticsProps.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.HOL.src.coalgebras Require Import llist.
Import wordLang (word_loc, Word, Loc).
Import wordSem (stack_frame, StackFrame).
Open Scope N_scope.

Section Sem1.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_Seq_Skip" *)
Theorem evaluate_Seq_Skip : forall (p : prog a) (s : stackSem.state a c ffi_t),
  evaluate (Seq Skip p, s) = evaluate (p, s).
Proof. intros p s. rewrite ev_seq, ev_skip. reflexivity. Qed.

(** Galette-only. *)
Lemma state_rel_ffi_clock ac k f f' (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t) lens extra :
  state_rel ac k f f' s t lens extra -> wordSem.ffi s = ffi t /\ wordSem.clock s = clock t.
Proof. intros H. sr_destr H. split; [symmetry; exact Hffi|exact Hclock]. Qed.

Lemma n2w_neq0 n : good_dimindex a -> 0 < n -> n < 4 -> (n2w n : word a) <> n2w 0.
Proof.
  intros Hg H1 H2 E. apply n2w_11 in E.
  assert (H : 4 < dimword a) by (unfold dimword; destruct Hg as [Hg|Hg]; rewrite Hg; reflexivity).
  rewrite !N.mod_small in E by lia. lia.
Qed.

(** HOL's [comp_Call_lemma] (an ML binding) is inlined in [comp_Call]. *)
(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_Call" *)
Theorem comp_Call : forall ac start (s : wordSem.state a (N * c) ffi_t) k res s1 (t : stackSem.state a c ffi_t) lens,
  wordSem.evaluate (wordLang.Call NONE (SOME start) [0] NONE, s) = (res, s1) /\
  res <> SOME wordSem.Error /\ state_rel ac k 0 0 s t lens 0 ->
  exists ck (t1 : stackSem.state a c ffi_t) res1,
    evaluate (Call NONE (inl start) NONE, set_clock (clock t + ck) t) = (res1, t1) /\
    (n2w 1 : word a) <> n2w 0 /\ (n2w 2 : word a) <> n2w 0 /\
    if ⌜OPTION_MAP compile_result res = res1⌝ then
      wordSem.ffi s1 = ffi t1 /\ wordSem.clock s1 = clock t1
    else
      res1 = SOME (Halt (Word (n2w 2))) /\
      isPREFIX (io_events (ffi t1)) (io_events (wordSem.ffi s1)) /\
      the (wordSem.stack_limit s1 + 1) (wordSem.stack_max s1) > wordSem.stack_limit s1.
Proof.
  intros ac start s k res s1 t lens (Hev & Hres & H).
  pose proof H as HS. sr_destr HS.
  destruct (comp_correct ac (wordLang.Call NONE (SOME start) [0] NONE) s k 0 0 res s1 t Nil (LENGTH (bitmaps t)) Nil
              (LENGTH (bitmaps t)) (Seq Skip (Call NONE (inl start) NONE)) lens) as (ck & t1 & res1 & Ev & HR).
  { split; [exact Hev|]. split; [exact Hres|]. split; [exact H|]. split; [reflexivity|]. split; [reflexivity|].
    split; [cbn; reflexivity|]. split; [cbn; lia|]. split; [cbn; lia|]. split; [cbn; reflexivity|].
    split; [intros z Hz; cbn in Hz; cbv [pred_set.IN pred_set.UNION pred_set.EMPTY] in Hz; tauto|]. cbn [wordLang.max_var MAX_LIST]. rewrite ?MAX_max. lia. }
  exists ck, t1, res1. rewrite evaluate_Seq_Skip in Ev. split; [exact Ev|].
  split; [apply n2w_neq0; [exact Hgd|lia|lia]|]. split; [apply n2w_neq0; [exact Hgd|lia|lia]|].
  destruct (decide (OPTION_MAP compile_result res = res1)) as [E|E].
  - rewrite bd_true' by exact E. rewrite bd_false' in HR by (intros C; exact (C E)).
    destruct res as [[x ys|x y|bn|cn| | |fe|]|];
      first [ exact HR
            | exact (state_rel_ffi_clock _ _ _ _ _ _ _ _ HR)
            | exact (state_rel_ffi_clock _ _ _ _ _ _ _ _ (proj1 HR))
            | destruct HR as (l0 & l & HR0 & _); exact (state_rel_ffi_clock _ _ _ _ _ _ _ _ HR0) ].
  - rewrite bd_false' by exact E. rewrite bd_true' in HR by exact E. exact HR.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_with_clock" *)
Theorem state_rel_with_clock : forall ac a0 (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t) lens extra k,
  state_rel ac a0 0 0 s t lens extra ->
  state_rel ac a0 0 0 (wordSem.set_clock k s) (set_clock k t) lens extra.
Proof.
  intros ac a0 s t lens extra k H. sr_destr H. sr_split; ws_fields; stk_fields; try assumption; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_Call_NONE_not_Break_Continue" *)
Theorem word_Call_NONE_not_Break_Continue : forall dest args handler (s : wordSem.state a c ffi_t) res s',
  wordSem.evaluate (wordLang.Call NONE dest args handler, s) = (res, s') ->
  (forall n, res <> SOME (wordSem.Break n)) /\ (forall n, res <> SOME (wordSem.Continue n)).
Proof.
  intros dest args handler s res s' Hev. rewrite wordSem.evaluate_eqn in Hev. cbn [wordSem.evaluate_body] in Hev.
  destruct (wordSem.get_vars args s); [|injection Hev as <- _; split; intros n0; discriminate].
  destruct (wordSem.bad_dest_args dest args); [injection Hev as <- _; split; intros n0; discriminate|].
  destruct (wordSem.find_code _ _ _ _) as [[args1 [prog ss]]|]; [|injection Hev as <- _; split; intros n0; discriminate].
  destruct (⌜handler = NONE⌝); [|injection Hev as <- _; split; intros n0; discriminate].
  destruct (wordSem.clock s =? 0); [injection Hev as <- _; split; intros n0; discriminate|].
  match type of Hev with context [wordSem.evaluate ?X] => destruct (wordSem.evaluate X) as [r s2] end. destruct (wordSem.bad_fun_return r) eqn:Eb.
  - injection Hev as <- _; split; intros n0; discriminate.
  - injection Hev as <- _. split; intros n0 ->; discriminate Eb.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_Call_NONE_not_Break_Continue" *)
Theorem stack_Call_NONE_not_Break_Continue : forall dest handler (s : stackSem.state a c ffi_t) res s',
  evaluate (Call NONE dest handler, s) = (res, s') ->
  (forall n, res <> SOME (Break n)) /\ (forall n, res <> SOME (Continue n)).
Proof.
  intros dest handler s res s' Hev. rewrite evaluate_eqn in Hev. cbn [evaluate_body] in Hev.
  destruct (find_code _ _ _); [|injection Hev as <- _; split; intros n0; discriminate].
  destruct (negb _); [injection Hev as <- _; split; intros n0; discriminate|].
  destruct (clock s =? 0); [injection Hev as <- _; split; intros n0; discriminate|].
  destruct (fix_clock _ _) as [r s2]. destruct (bad_fun_return r) eqn:Eb.
  - injection Hev as <- _; split; intros n0; discriminate.
  - injection Hev as <- _. split; intros n0 ->; discriminate Eb.
Qed.

End Sem1.

(** ** Galette-only helpers for the semantics theorems *)

Lemma some_SOME {A} `{Inhabited A} (P : A -> Prop) x : some P = SOME x -> P x.
Proof.
  unfold some. destruct (classical_dec _) as [Hx|_]; [|discriminate]. intros E. injection E as <-.
  exact (select_spec P Hx).
Qed.

Lemma some_NONE {A} `{Inhabited A} (P : A -> Prop) : some P = NONE -> forall x, ~ P x.
Proof. unfold some. destruct (classical_dec _) as [_|Hn]; [discriminate|]. intros _ x Hx. apply Hn. eauto. Qed.

Lemma some_unique {A} `{Inhabited A} (P : A -> Prop) x :
  (forall y z, P y -> P z -> y = z) -> P x -> some P = SOME x.
Proof.
  intros U Hx. unfold some. destruct (classical_dec _) as [He|Hn]; [|exfalso; apply Hn; eauto].
  f_equal. apply U; [apply select_spec, He|exact Hx].
Qed.

Lemma wset_clock_set_clock {a C F} x y (s : wordSem.state a C F) : wordSem.set_clock x (wordSem.set_clock y s) = wordSem.set_clock x s.
Proof. destruct s; reflexivity. Qed.

Lemma wrun_stable {a C F} (p : wordLang.prog a) (s : wordSem.state a C F) k1 k2 r s1 :
  wordSem.evaluate (p, wordSem.set_clock k1 s) = (r, s1) -> r <> SOME wordSem.TimeOut -> k1 <= k2 ->
  exists s2, wordSem.evaluate (p, wordSem.set_clock k2 s) = (r, s2) /\ wordSem.ffi s2 = wordSem.ffi s1.
Proof.
  intros E Hr Hk. pose proof (clock.evaluate_add_clock (k2 - k1) p _ r s1 (conj E Hr)) as E2.
  cbn [wordSem.clock wordSem.set_clock] in E2. rewrite wset_clock_set_clock in E2.
  replace (k1 + (k2 - k1)) with k2 in E2 by lia. eexists; split; [exact E2|reflexivity].
Qed.

Lemma srun_stable {a C F} (p : prog a) (s : stackSem.state a C F) k1 k2 r s1 :
  evaluate (p, set_clock k1 s) = (r, s1) -> r <> SOME TimeOut -> k1 <= k2 ->
  exists s2, evaluate (p, set_clock k2 s) = (r, s2) /\ ffi s2 = ffi s1.
Proof.
  intros E Hr Hk. pose proof (evaluate_add_clock (k2 - k1) p _ r s1 (conj E Hr)) as E2.
  stk_fields. rewrite set_clock_set_clock in E2.
  replace (k1 + (k2 - k1)) with k2 in E2 by lia. eexists; split; [exact E2|reflexivity].
Qed.

Lemma wio_mono {a C F} (p : wordLang.prog a) (s : wordSem.state a C F) k1 k2 : k1 <= k2 ->
  is_true (isPREFIX (io_events (wordSem.ffi (snd (wordSem.evaluate (p, wordSem.set_clock k1 s)))))
                    (io_events (wordSem.ffi (snd (wordSem.evaluate (p, wordSem.set_clock k2 s)))))).
Proof.
  intros Hk. pose proof (clock.evaluate_add_clock_io_events_mono p (wordSem.set_clock k1 s) (k2 - k1)) as M.
  cbn [wordSem.clock wordSem.set_clock] in M. rewrite wset_clock_set_clock in M.
  replace (k1 + (k2 - k1)) with k2 in M by lia. exact M.
Qed.

Lemma sio_mono {a C F} (p : prog a) (s : stackSem.state a C F) k1 k2 : k1 <= k2 ->
  is_true (isPREFIX (io_events (ffi (SND (evaluate (p, set_clock k1 s)))))
                    (io_events (ffi (SND (evaluate (p, set_clock k2 s)))))).
Proof.
  intros Hk. pose proof (evaluate_add_clock_io_events_mono (k2 - k1) p (set_clock k1 s)) as M.
  stk_fields. rewrite set_clock_set_clock in M.
  replace (k1 + (k2 - k1)) with k2 in M by lia. exact M.
Qed.

Lemma io_chain_word {a C F} (p : wordLang.prog a) (s : wordSem.state a C F) :
  lprefix_chain (IMAGE (fun k => fromList (io_events (wordSem.ffi (snd (wordSem.evaluate (p, wordSem.set_clock k s)))))) UNIV).
Proof.
  set (g := fun k => io_events (wordSem.ffi (snd (wordSem.evaluate (p, wordSem.set_clock k s))))).
  replace (IMAGE _ UNIV) with (IMAGE fromList (IMAGE g UNIV)) by (rewrite <- IMAGE_COMPOSE; reflexivity).
  apply prefix_chain_lprefix_chain.
  intros l1 l2 [[k1 [-> _]] [k2 [-> _]]].
  destruct (N.le_ge_cases k1 k2) as [Hle|Hle]; [left|right]; apply wio_mono; exact Hle.
Qed.

Lemma LPREFIX_fromList_iff {A} `{EqDecision A} `{Inhabited A} (l1 l2 : list A) :
  LPREFIX (fromList l1) (fromList l2) <-> is_true (isPREFIX l1 l2).
Proof. rewrite LPREFIX_fromList, toList_fromList. reflexivity. Qed.

Lemma LNTH_fromList_prefix' {A} `{EqDecision A} `{Inhabited A} (l1 l2 : list A) n x :
  is_true (isPREFIX l1 l2) -> LNTH n (fromList l1) = SOME x -> LNTH n (fromList l2) = SOME x.
Proof.
  revert l2 n; induction l1 as [|h l1 IH]; intros [|h' l2] n Hp Hn; cbn [fromList isPREFIX] in *;
    unfold is_true in *; try discriminate; try (rewrite (proj1 LNTH_THM) in Hn; discriminate).
  apply andb_prop in Hp as [Hh Hp]. apply bool_decide_spec in Hh. subst h'.
  destruct n as [|n] using N.peano_ind.
  - rewrite (proj1 (proj2 LNTH_THM)) in *. exact Hn.
  - rewrite (proj2 (proj2 LNTH_THM)) in *. apply IH; assumption.
Qed.

Section SemCore.
Context {a : N} {c ffi_t : Type}.

#[local] Instance behaviour_inhabited_ws : Inhabited behaviour := ffi.Fail.

(** Galette-only: the terminating behaviour of a word run is unique. *)
Lemma wterm_unique (p : wordLang.prog a) (s : wordSem.state a (N * c) ffi_t) y z :
  (exists k t r outcome, wordSem.evaluate (p, wordSem.set_clock k s) = (r, t) /\
     match r with
     | SOME (wordSem.FinalFFI e) => outcome = FFI_outcome e
     | SOME (wordSem.Result _ _) => outcome = Success
     | SOME wordSem.NotEnoughSpace => outcome = Resource_limit_hit
     | _ => False
     end /\ y = Terminate outcome (io_events (wordSem.ffi t))) ->
  (exists k t r outcome, wordSem.evaluate (p, wordSem.set_clock k s) = (r, t) /\
     match r with
     | SOME (wordSem.FinalFFI e) => outcome = FFI_outcome e
     | SOME (wordSem.Result _ _) => outcome = Success
     | SOME wordSem.NotEnoughSpace => outcome = Resource_limit_hit
     | _ => False
     end /\ z = Terminate outcome (io_events (wordSem.ffi t))) ->
  y = z.
Proof.
  intros (k1 & t1 & r1 & o1 & E1 & M1 & ->) (k2 & t2 & r2 & o2 & E2 & M2 & ->).
  assert (N1 : r1 <> SOME wordSem.TimeOut) by (intros ->; exact M1).
  assert (N2 : r2 <> SOME wordSem.TimeOut) by (intros ->; exact M2).
  destruct (N.le_ge_cases k1 k2) as [Hk|Hk].
  - destruct (wrun_stable _ _ _ _ _ _ E1 N1 Hk) as (t3 & E3 & F3). rewrite E2 in E3. injection E3 as Er Et.
    subst r2 t2. rewrite F3. f_equal. destruct r1 as [[]|]; try contradiction; congruence.
  - destruct (wrun_stable _ _ _ _ _ _ E2 N2 Hk) as (t3 & E3 & F3). rewrite E1 in E3. injection E3 as Er Et.
    subst r1 t1. rewrite F3. f_equal. destruct r2 as [[]|]; try contradiction; congruence.
Qed.

(** Galette-only: the common part of [state_rel_IMP_semantics] and
    [state_rel_IMP_semantics']. *)
Lemma sem_core ac k (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t) lens start :
  state_rel ac k 0 0 s t lens 0 -> wordSem.semantics s start <> Galette.cakeml.semantics.ffi.ffi.Fail ->
  semantics start t = wordSem.semantics s start \/
  exists k0 (t1 : stackSem.state a c ffi_t),
    semantics start t = Terminate Resource_limit_hit (io_events (ffi t1)) /\
    is_true (isPREFIX (io_events (ffi t1))
       (io_events (wordSem.ffi (snd (wordSem.evaluate (wordLang.Call NONE (SOME start) [0] NONE, wordSem.set_clock k0 s)))))) /\
    (let s1 := snd (wordSem.evaluate (wordLang.Call NONE (SOME start) [0] NONE, wordSem.set_clock k0 s)) in
     the (wordSem.stack_limit s1 + 1) (wordSem.stack_max s1) > wordSem.stack_limit s1).
Proof.
  intros H HF.
  set (Pw := @wordLang.Call a NONE (SOME start) [0] NONE).
  set (Ps := @Call a NONE (inl start) NONE).
  pose proof H as HS. sr_destr HS.
  assert (OKw : forall k0, ~ match fst (wordSem.evaluate (Pw, wordSem.set_clock k0 s)) with
       | SOME (wordSem.Exception _ _) => True | SOME (wordSem.Result ret _) => ret <> Loc 1 0
       | SOME wordSem.Error => True | NONE => True | _ => False end).
  { intros k0 Hkb. apply HF. unfold wordSem.semantics. cbv zeta.
    destruct (classical_dec _) as [_|Hn]; [reflexivity|exfalso; apply Hn; exists k0; exact Hkb]. }
  assert (CLw : forall k0, let '(r, s1) := wordSem.evaluate (Pw, wordSem.set_clock k0 s) in
             r = SOME wordSem.TimeOut \/ (exists ys, r = SOME (wordSem.Result (Loc 1 0) ys)) \/
             r = SOME wordSem.NotEnoughSpace \/ (exists f, r = SOME (wordSem.FinalFFI f))).
  { intros k0. pose proof (OKw k0) as Ok. destruct (wordSem.evaluate (Pw, _)) as [r s1] eqn:E. cbn [fst] in Ok.
    destruct (word_Call_NONE_not_Break_Continue _ _ _ _ _ _ E) as [NB NC].
    destruct r as [[x ys|x y|bn|cn| | |fe|]|].
    - right; left. exists ys. destruct (decide (x = Loc 1 0)) as [->|Hx]; [reflexivity|exfalso; exact (Ok Hx)].
    - exfalso; apply Ok; exact Logic.I.
    - exfalso; exact (NB bn eq_refl).
    - exfalso; exact (NC cn eq_refl).
    - left; reflexivity.
    - right; right; left; reflexivity.
    - right; right; right; eauto.
    - exfalso; apply Ok; exact Logic.I.
    - exfalso; apply Ok; exact Logic.I. }
  assert (SIM : forall k0, exists ck,
     let '(r, s1) := wordSem.evaluate (Pw, wordSem.set_clock k0 s) in
     let '(r1, t1) := evaluate (Ps, set_clock (k0 + ck) t) in
     (r1 = OPTION_MAP compile_result r /\ wordSem.ffi s1 = ffi t1) \/
     (r1 = SOME (Halt (Word (n2w 2))) /\ is_true (isPREFIX (io_events (ffi t1)) (io_events (wordSem.ffi s1))) /\
      the (wordSem.stack_limit s1 + 1) (wordSem.stack_max s1) > wordSem.stack_limit s1)).
  { intros k0. pose proof (OKw k0) as Ok. destruct (wordSem.evaluate (Pw, wordSem.set_clock k0 s)) as [r s1] eqn:E.
    cbn [fst] in Ok.
    assert (Hr : r <> SOME wordSem.Error) by (intros ->; apply Ok; exact Logic.I).
    destruct (comp_Call ac start (wordSem.set_clock k0 s) k r s1 (set_clock k0 t) lens) as (ck & t1 & r1 & Ev & _ & _ & Hif).
    { split; [exact E|]. split; [exact Hr|]. apply state_rel_with_clock, H. }
    exists ck. stk_fields. rewrite set_clock_set_clock in Ev. fold Ps in Ev. rewrite Ev.
    destruct (decide (OPTION_MAP compile_result r = r1)) as [Eq|Ne].
    - rewrite bd_true' in Hif by exact Eq. left. split; [symmetry; exact Eq|exact (proj1 Hif)].
    - rewrite bd_false' in Hif by exact Ne. right. exact Hif. }
  assert (OKs : forall k0, ~ (let res := FST (evaluate (Ps, set_clock k0 t)) in
       res <> SOME TimeOut /\ res <> SOME (Result (Loc 1 0)) /\
       (forall w, res <> SOME (Halt (Word w))) /\ forall f, res <> SOME (FinalFFI f))).
  { intros k0 Hb. cbv zeta in Hb. destruct (evaluate (Ps, set_clock k0 t)) as [r t'] eqn:Et. cbn [FST] in Hb.
    destruct Hb as (HT & HR & HHt & HF').
    destruct (SIM k0) as [ck Hs]. pose proof (CLw k0) as Cl.
    destruct (wordSem.evaluate (Pw, wordSem.set_clock k0 s)) as [rw s1] eqn:Ew.
    destruct (srun_stable Ps t k0 (k0 + ck) r t' Et HT ltac:(lia)) as (t2 & Et2 & _). rewrite Et2 in Hs.
    destruct Hs as [(-> & _)|(-> & _)].
    - destruct Cl as [->|[[ys ->]|[->|[f ->]]]]; cbn in *;
        [exact (HT eq_refl)|exact (HR eq_refl)|exact (HHt _ eq_refl)|exact (HF' _ eq_refl)].
    - exact (HHt _ eq_refl). }
  remember (semantics start t) as T eqn:ET. unfold semantics in ET. cbv zeta in ET. fold Ps in ET.
  destruct (classical_dec _) as [[k0 Hkb]|_]; [exfalso; exact (OKs k0 Hkb)|].
  assert (EW : wordSem.semantics s start =
    match some (fun res => exists k t r outcome,
             wordSem.evaluate (Pw, wordSem.set_clock k s) = (r, t) /\
             match r with
             | SOME (wordSem.FinalFFI e) => outcome = FFI_outcome e
             | SOME (wordSem.Result _ _) => outcome = Success
             | SOME wordSem.NotEnoughSpace => outcome = Resource_limit_hit
             | _ => False
             end /\
             res = Terminate outcome (io_events (wordSem.ffi t))) with
    | SOME res => res
    | NONE => Diverge (build_lprefix_lub
                 (IMAGE (fun k => fromList (io_events (wordSem.ffi (snd (wordSem.evaluate (Pw, wordSem.set_clock k s)))))) UNIV))
    end).
  { unfold wordSem.semantics. cbv zeta. fold Pw.
    destruct (classical_dec _) as [[k0 Hkb]|_]; [exfalso; exact (OKw k0 Hkb)|reflexivity]. }
  rewrite EW. clear EW.
  match type of ET with _ = match some ?Q with _ => _ end => destruct (some Q) as [b|] eqn:Esome end.
  - (* the stack run terminates *)
    apply some_SOME in Esome. destruct Esome as (k0 & t' & r & o & Et & Ho & ->). subst T.
    assert (HrT : SOME r <> SOME TimeOut) by (intros E; injection E as ->; exact Ho).
    destruct (SIM k0) as [ck Hs]. pose proof (CLw k0) as Cl.
    destruct (wordSem.evaluate (Pw, wordSem.set_clock k0 s)) as [rw s1] eqn:Ew.
    destruct (srun_stable Ps t k0 (k0 + ck) _ _ Et HrT ltac:(lia)) as (t2 & Et2 & Hf2). rewrite Et2 in Hs.
    destruct Hs as [(Er & Ef)|(Er & Hio & Hslm)].
    + left. symmetry.
      match goal with |- match some ?Q with _ => _ end = _ =>
        assert (Eq : some Q = SOME (Terminate o (io_events (ffi t')))); [|rewrite Eq; reflexivity] end.
      apply some_unique; [apply wterm_unique|].
      exists k0, s1, rw, o. split; [exact Ew|]. rewrite Ef, Hf2. split; [|reflexivity].
      destruct Cl as [->|[[ys ->]|[->|[f ->]]]]; cbn in Er; injection Er as ->; cbn in Ho.
      * exfalso. exact (HrT eq_refl).
      * exact Ho.
      * rewrite Ho. rewrite bool_decide_eq_false_2; [reflexivity|].
        intros E. apply (n2w_neq0 1 Hgd ltac:(lia) ltac:(lia)). congruence.
      * exact Ho.
    + right. exists k0, t'. injection Er as ->. cbn in Ho.
      rewrite bool_decide_eq_false_2 in Ho by (intros E; apply (n2w_neq0 2 Hgd ltac:(lia) ltac:(lia)); congruence).
      subst o. split; [reflexivity|]. rewrite Ew. cbn [snd]. rewrite <- Hf2. split; [exact Hio|exact Hslm].
  - (* the stack run diverges *)
    pose proof (some_NONE _ Esome) as NoS. clear Esome. subst T. left.
    assert (NoW : forall k0, fst (wordSem.evaluate (Pw, wordSem.set_clock k0 s)) = SOME wordSem.TimeOut /\
                  exists ck, evaluate (Ps, set_clock (k0 + ck) t) = (SOME TimeOut, SND (evaluate (Ps, set_clock (k0 + ck) t))) /\
                    wordSem.ffi (snd (wordSem.evaluate (Pw, wordSem.set_clock k0 s))) = ffi (SND (evaluate (Ps, set_clock (k0 + ck) t)))).
    { intros k0. destruct (SIM k0) as [ck Hs]. pose proof (CLw k0) as Cl.
      destruct (wordSem.evaluate (Pw, wordSem.set_clock k0 s)) as [rw s1] eqn:Ew.
      destruct (evaluate (Ps, set_clock (k0 + ck) t)) as [r1 t1] eqn:Et. cbn [fst snd FST SND].
      destruct Hs as [(-> & Ef)|(-> & _)].
      - destruct Cl as [->|[[ys ->]|[->|[f ->]]]].
        + split; [reflexivity|]. exists ck. rewrite Et. split; [reflexivity|exact Ef].
        + exfalso. apply (NoS (Terminate Success (io_events (ffi t1)))). exists (k0 + ck), t1, (Result (Loc 1 0)), Success. auto.
        + exfalso. apply (NoS (Terminate Resource_limit_hit (io_events (ffi t1)))).
          exists (k0 + ck), t1, (Halt (Word (n2w 1))), Resource_limit_hit. split; [exact Et|]. split; [|reflexivity].
          rewrite bool_decide_eq_false_2; [reflexivity|].
          intros E. apply (n2w_neq0 1 Hgd ltac:(lia) ltac:(lia)). congruence.
        + exfalso. apply (NoS (Terminate (FFI_outcome f) (io_events (ffi t1)))). exists (k0 + ck), t1, (FinalFFI f), (FFI_outcome f). auto.
      - exfalso. apply (NoS (Terminate Resource_limit_hit (io_events (ffi t1)))).
        exists (k0 + ck), t1, (Halt (Word (n2w 2))), Resource_limit_hit. split; [exact Et|]. split; [|reflexivity].
        rewrite bool_decide_eq_false_2; [reflexivity|].
        intros E. apply (n2w_neq0 2 Hgd ltac:(lia) ltac:(lia)). congruence. }
    match goal with |- _ = match some ?Q with _ => _ end => destruct (some Q) as [w|] eqn:Ew end.
    { exfalso. apply some_SOME in Ew. destruct Ew as (k0 & s1 & rw & o & Ew & Ho & _).
      destruct (NoW k0) as [HT _]. rewrite Ew in HT. cbn in HT. subst rw. exact Ho. }
    f_equal.
    set (Xs := IMAGE (fun k0 => fromList (io_events (ffi (SND (evaluate (Ps, set_clock k0 t)))))) UNIV).
    set (Xw := IMAGE (fun k0 => fromList (io_events (wordSem.ffi (snd (wordSem.evaluate (Pw, wordSem.set_clock k0 s)))))) UNIV).
    assert (Cs : lprefix_chain Xs) by exact (io_chain_stack start t).
    assert (Cw : lprefix_chain Xw) by exact (io_chain_word Pw s).
    assert (EQV : equiv_lprefix_chain Xw Xs).
    { apply (equiv_lprefix_chain_thm _ _ (conj Cw Cs)); split.
      - intros ll1 n0 x [[k0 [-> _]] Hx].
        destruct (NoW k0) as [_ (ck & _ & Hf)].
        exists (fromList (io_events (ffi (SND (evaluate (Ps, set_clock (k0 + ck) t)))))).
        split; [exists (k0 + ck); split; [reflexivity|exact Logic.I]|]. rewrite <- Hf. exact Hx.
      - intros ll2 n0 x [[k0 [-> _]] Hx].
        destruct (NoW k0) as [_ (ck & _ & Hf)].
        exists (fromList (io_events (wordSem.ffi (snd (wordSem.evaluate (Pw, wordSem.set_clock k0 s)))))).
        split; [exists k0; split; [reflexivity|exact Logic.I]|].
        rewrite Hf. apply (LNTH_fromList_prefix' _ _ n0 x (sio_mono Ps t k0 (k0 + ck) ltac:(lia)) Hx). }
    apply (unique_lprefix_lub Xs); split.
    + exact (build_lprefix_lub_thm _ Cs).
    + apply (lprefix_lub_new_chain Xw Xs). split; [exact Cs|split; [exact EQV|exact (build_lprefix_lub_thm _ Cw)]].
Qed.

End SemCore.

Section SemThms.
Context {a : N} {c ffi_t : Type}.

#[local] Instance behaviour_inhabited_ws2 : Inhabited behaviour := ffi.Fail.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_IMP_semantics" *)
Theorem state_rel_IMP_semantics : forall ac k (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t) lens start,
  state_rel ac k 0 0 s t lens 0 /\ wordSem.semantics s start <> Galette.cakeml.semantics.ffi.ffi.Fail ->
  semantics start t IN extend_with_resource_limit (wordSem.semantics s start INSERT {}).
Proof.
  intros ac k s t lens start [H HF].
  unfold extend_with_resource_limit, pred_set.UNION, pred_set.INSERT, pred_set.IN, pred_set.EMPTY.
  destruct (sem_core ac k s t lens start H HF) as [E|(k0 & t1 & E & Hio & _)]; [left; left; left; exact E|].
  rewrite E. clear E.
  set (Pw := @wordLang.Call a NONE (SOME start) [0] NONE) in *.
  remember (wordSem.semantics s start) as W eqn:EW. unfold wordSem.semantics in EW. cbv zeta in EW. fold Pw in EW.
  destruct (classical_dec _) as [_|_]; [subst W; exfalso; exact (HF eq_refl)|].
  match type of EW with _ = match some ?Q with _ => _ end => destruct (some Q) as [b|] eqn:Esome end.
  - apply some_SOME in Esome. destruct Esome as (k2 & s2 & r2 & o2 & E2 & M2 & ->). subst W.
    left; right. exists (io_events (ffi t1)). split; [reflexivity|].
    exists o2, (io_events (wordSem.ffi s2)). split; [left; reflexivity|].
    assert (N2 : r2 <> SOME wordSem.TimeOut) by (intros ->; exact M2).
    eapply isPREFIX_TRANS; split; [exact Hio|].
    destruct (N.le_ge_cases k0 k2) as [Hk|Hk].
    + pose proof (wio_mono Pw s k0 k2 Hk) as M. rewrite E2 in M. exact M.
    + destruct (wrun_stable _ _ _ _ _ _ E2 N2 Hk) as (s3 & E3 & F3). rewrite E3. cbn [snd]. rewrite F3.
      apply isPREFIX_REFL.
  - subst W. right. exists (io_events (ffi t1)). split; [reflexivity|].
    eexists. split; [left; reflexivity|].
    set (Xw := IMAGE (fun k0 => fromList (io_events (wordSem.ffi (snd (wordSem.evaluate (Pw, wordSem.set_clock k0 s)))))) UNIV).
    eapply LPREFIX_TRANS. split; [apply LPREFIX_fromList_iff; exact Hio|].
    apply (proj1 (build_lprefix_lub_thm Xw (io_chain_word Pw s))). exists k0. split; [reflexivity|exact Logic.I].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_IMP_semantics'" *)
Theorem state_rel_IMP_semantics' : forall ac k (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t) lens start,
  state_rel ac k 0 0 s t lens 0 /\ wordSem.semantics s start <> Galette.cakeml.semantics.ffi.ffi.Fail /\
  wordSem.word_lang_safe_for_space s start ->
  semantics start t = wordSem.semantics s start.
Proof.
  intros ac k s t lens start (H & HF & Hsafe).
  destruct (sem_core ac k s t lens start H HF) as [E|(k0 & t1 & E & Hio & Hgt)]; [exact E|].
  exfalso. cbv zeta in Hgt.
  destruct (wordSem.evaluate (wordLang.Call NONE (SOME start) [0] NONE, wordSem.set_clock k0 s)) as [r s1] eqn:Ew.
  cbn [snd] in Hgt. destruct (Hsafe k0 r s1 Ew) as (mx & Emx & Hle). rewrite Emx in Hgt. cbn in Hgt. lia.
Qed.

End SemThms.

Section Init.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "init_state_ok_def" *)
Definition init_state_ok (ac : asm_config a) (k : N) (t : stackSem.state a c ffi_t)
    (coracle : N -> (N * c) * list (N * (N * wordLang.prog a))) : Prop :=
  4 < k /\ good_dimindex a /\ 8 <= dimindex a /\
  use_stack t /\ use_store t /\ use_alloc t /\ stack_max.gc_fun_ok (gc_fun t) /\
  stack_space t <= LENGTH (stackSem.stack t) /\
  FLOOKUP (regs t) 0 = SOME (Loc 1 0) /\
  LENGTH (bitmaps t) + 1 < dimword a /\
  isPREFIX [n2w 4] (bitmaps t) /\
  LENGTH (stackSem.stack t) < dimword a /\
  DROP (stack_space t) (stackSem.stack t) = [Word (n2w 0)] /\
  Handler IN FDOM (store t) /\
  LENGTH (bitmaps t) + LENGTH (wordSem.buffer_buffer (data_buffer t)) +
    wordSem.space_left (data_buffer t) + 1 < dimword a /\
  compile_oracle t = (fun n =>
    let '((bm0, cfg), progs) := coracle n in
    let '(progs, (fs, bm)) := compile_word_to_stack ac false k progs (Nil, bm0) in
    (cfg, (progs, append (FST bm)))) /\
  (forall n, let '((bm0, cfg), progs) := coracle n in
    EVERY (fun p => post_alloc_conventions k (SND (SND p))) progs /\
    EVERY (fun p => flat_exp_conventions (SND (SND p))) progs /\
    EVERY (fun p => negb (wordLang.raise_stub_location =? FST p)) progs /\
    EVERY (fun p => negb (wordLang.store_consts_stub_location =? FST p)) progs /\
    (n = 0 -> bm0 = LENGTH (bitmaps t))).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "make_init_def" *)
Definition make_init (ac : asm_config a) (k : N) (t : stackSem.state a c ffi_t)
    (code : num_map (N * wordLang.prog a)) (coracle : N -> (N * c) * list (N * (N * wordLang.prog a)))
    : wordSem.state a (N * c) ffi_t :=
  {| wordSem.locals := insert 0 (Loc 1 0) LN;
     wordSem.locals_size := SOME 0;
     wordSem.fp_regs := fp_regs t;
     wordSem.store := store t \\ Handler;
     wordSem.stack := [];
     wordSem.stack_limit := LENGTH (stackSem.stack t);
     wordSem.stack_max := @wordSem.stack_size a [];
     wordSem.state_stack_size :=
       mapi (fun n '(arg_count, prog) => FST (SND (compile_prog ac false prog arg_count k (Nil, 0)))) code;
     wordSem.memory := memory t;
     wordSem.mdomain := mdomain t;
     wordSem.sh_mdomain := sh_mdomain t;
     wordSem.permute := K I;
     wordSem.compile := (fun '(bm0, cfg) progs =>
       let '(progs, (fs, bm)) := compile_word_to_stack ac false k progs (Nil, bm0) in
       OPTION_MAP (fun '(bytes, cfg) => (bytes, (append (FST bm), (SND bm, cfg)))) (stackSem.compile t cfg progs));
     wordSem.compile_oracle := coracle;
     wordSem.code_buffer := code_buffer t;
     wordSem.data_buffer := data_buffer t;
     wordSem.gc_fun := gc_fun t;
     wordSem.handler := 0;
     wordSem.clock := clock t;
     wordSem.termdep := 0;
     wordSem.code := code;
     wordSem.be := be t;
     wordSem.ffi := ffi t |}.

Lemma compile_prog_f ac perf (p : wordLang.prog a) n k bm bm' :
  FST (SND (compile_prog ac perf p n k bm)) = FST (SND (compile_prog ac perf p n k bm')).
Proof.
  unfold compile_prog. cbv zeta.
  destruct (comp _ _ _ bm _) as [q1 b1]. destruct (comp _ _ _ bm' _) as [q2 b2]. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "init_state_ok_IMP_state_rel" *)
Theorem init_state_ok_IMP_state_rel : forall ac k (t : stackSem.state a c ffi_t) code coracle,
  lookup wordLang.raise_stub_location (stackSem.code t) = SOME (raise_stub false k) /\
  lookup wordLang.store_consts_stub_location (stackSem.code t) = SOME (store_consts_stub k) /\
  (forall n word_prog arg_count,
     lookup n code = SOME (arg_count, word_prog) ->
     post_alloc_conventions k word_prog /\
     flat_exp_conventions word_prog /\
     exists bs i bs2 i2 f stack_prog,
       compile_prog ac false word_prog arg_count k (bs, i) = (stack_prog, (f, (bs2, i2))) /\
       LENGTH (append bs) <= i /\ i - LENGTH (append bs) <= LENGTH (bitmaps t) /\
       isPREFIX (append bs2) (DROP (i - LENGTH (append bs)) (bitmaps t)) /\
       lookup n (stackSem.code t) = SOME stack_prog) /\
  domain (stackSem.code t) =
    wordLang.raise_stub_location INSERT wordLang.store_consts_stub_location INSERT domain code /\
  init_state_ok ac k t coracle ->
  state_rel ac k 0 0 (make_init ac k t code coracle) t [] 0.
Proof.
  intros ac k t code coracle (Hr & Hs & Hc & Hd & Hi).
  unfold init_state_ok in Hi.
  destruct Hi as (Hk & Hgd & H8 & Hus & Hust & Hua & Hgc & Hsp & Hr0 & Hlb & Hpre & Hls & Hdrop & HH & Hlen & Hco & Hcon).
  assert (Hbm : exists bl, bitmaps t = n2w 4 :: bl).
  { destruct (bitmaps t) as [|b bl]; cbn in Hpre; [discriminate|]. unfold is_true in Hpre.
    apply andb_prop in Hpre as [Hb _]. apply bool_decide_spec in Hb. subst b. eauto. }
  destruct Hbm as [bl Ebl].
  assert (HLd : LENGTH (stackSem.stack t) - stack_space t = 1).
  { pose proof (f_equal LENGTH Hdrop) as E. rewrite LENGTH_DROP' in E. exact E. }
  unfold make_init. sr_split; ws_fields; try assumption; try reflexivity.
  - intros n wp ac' Hl. destruct (Hc n wp ac' Hl) as (P1 & P2 & bs & i & bs2 & i2 & f & sp & Ecp & B1 & B2 & B3 & B4).
    split; [exact P1|]. split; [exact P2|]. exists bs, i, bs2, i2, f, sp.
    split; [exact Ecp|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
    rewrite lookup_mapi, Hl. cbn [option_map the].
    rewrite (compile_prog_f ac false wp ac' k (Nil, 0) (bs, i)), Ecp. reflexivity.
  - rewrite Ebl, LENGTH_cons'. lia.
  - rewrite Ebl. reflexivity.
  - lia.
  - unfold stack_size_rel. split; [intros C; lia|]. split; [reflexivity|].
    intros sm Hsm. cbn in Hsm. injection Hsm as <-. split; [lia|]. split; [reflexivity|].
    exists 1. split; [reflexivity|lia].
  - unfold stack_rel. split; [reflexivity|]. exists []. rewrite N.add_0_r, DROP_DROP_EQ, N.add_0_l, Hdrop.
    split; [cbn; try rewrite decide_True by reflexivity; reflexivity|]. split; [|exact Logic.I].
    intros [C _]. cbn in C. lia.
  - intros n v Hn. rewrite lookup_insert in Hn. destruct (decide (n = 0)) as [->|Hn0]; [|discriminate].
    injection Hn as <-. split; [reflexivity|]. replace (0 DIV 2) with 0 by reflexivity.
    rewrite (proj2 (N.ltb_lt 0 k)) by lia. exact Hr0.
Qed.

End Init.

Section CompileSem.
Context {a : N} {c ffi_t : Type}.

(** HOL's [init_state_ok_semantics] and [init_state_ok_semantics'] (ML
    bindings) are inlined in [compile_semantics]. *)
(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "compile_semantics" *)
Theorem compile_semantics : forall (asm_conf : asm_config a) (code : list (N * (N * wordLang.prog a)))
    (t : stackSem.state a c ffi_t) k coracle start,
  stackSem.code t = fromAList (SND (SND (SND (word_to_stack.compile asm_conf false code)))) /\
  k = reg_count asm_conf - (5 + LENGTH (avoid_regs asm_conf)) /\
  init_state_ok asm_conf k t coracle /\
  ALOOKUP code wordLang.raise_stub_location = NONE /\
  ALOOKUP code wordLang.store_consts_stub_location = NONE /\
  isPREFIX (FST (word_to_stack.compile asm_conf false code)) (bitmaps t) /\
  EVERY (fun '(n, (m, prog)) => flat_exp_conventions prog &&
     post_alloc_conventions (reg_count asm_conf - (5 + LENGTH (avoid_regs asm_conf))) prog) code /\
  wordSem.semantics (make_init asm_conf k t (fromAList code) coracle) start <> Galette.cakeml.semantics.ffi.ffi.Fail ->
  semantics start t IN
    extend_with_resource_limit' ⌜wordSem.word_lang_safe_for_space (make_init asm_conf k t (fromAList code) coracle) start⌝
      (wordSem.semantics (make_init asm_conf k t (fromAList code) coracle) start INSERT {}).
Proof.
  intros asm_conf code t k coracle start (Hcode & Ek & Hi & Hr & Hs & Hpre & Hev & HF).
  unfold word_to_stack.compile in Hcode, Hpre. cbv zeta in Hcode, Hpre. rewrite <- Ek in Hcode, Hpre, Hev.
  destruct (compile_word_to_stack asm_conf false k code (List [n2w 4], 1)) as [progs [fs [bms i']]] eqn:Ecw.
  cbn [FST SND fst snd] in Hcode, Hpre.
  assert (HR : state_rel asm_conf k 0 0 (make_init asm_conf k t (fromAList code) coracle) t [] 0).
  { apply init_state_ok_IMP_state_rel. split; [|split; [|split; [|split]]].
    - rewrite Hcode, lookup_fromAList. cbn [ALOOKUP]. rewrite decide_True by reflexivity. reflexivity.
    - rewrite Hcode, lookup_fromAList. cbn [ALOOKUP].
      rewrite decide_False by (cbv; discriminate). rewrite decide_True by reflexivity. reflexivity.
    - intros n wp ac' Hl. rewrite lookup_fromAList in Hl.
      pose proof (ALOOKUP_In _ _ _ Hl) as Hin. pose proof (EVERY_In _ _ _ Hev Hin) as Hc. cbn in Hc.
      apply andb_prop in Hc as [Hf Hp].
      split; [exact Hp|]. split; [exact Hf|].
      destruct (compile_word_to_stack_IMP_ALOOKUP asm_conf false code k (List [n2w 4]) 1 progs fs bms i' n ac' wp (bitmaps t))
        as (bs & i & bs2 & i2 & f & sp & Ecp & B1 & B2 & B3 & B4).
      { split; [exact Ecw|]. split; [exact Hl|]. cbn. split; [lia|]. split; [lia|].
        replace (1 - 1) with 0 by reflexivity. rewrite DROP_0_eq. exact Hpre. }
      exists bs, i, bs2, i2, f, sp. split; [exact Ecp|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
      rewrite Hcode, lookup_fromAList. cbn [ALOOKUP].
      assert (Hn1 : n <> wordLang.raise_stub_location) by (intros ->; congruence).
      assert (Hn2 : n <> wordLang.store_consts_stub_location) by (intros ->; congruence).
      rewrite !decide_False by congruence. exact B4.
    - rewrite Hcode, !domain_fromAList. cbn [MAP List.map fst].
      rewrite (MAP_FST_compile_word_to_stack _ _ _ _ _ _ _ Ecw).
      apply set_ext. intros x. unfold pred_set.INSERT, pred_set.IN. unfold is_true. rewrite !MEM_In. cbn [In].
      split; intros H; (destruct H as [H|[H|H]]; [left; congruence|right; left; congruence|right; right; exact H]).
    - exact Hi. }
  unfold extend_with_resource_limit'.
  destruct (⌜wordSem.word_lang_safe_for_space _ start⌝) eqn:Esafe.
  - apply bool_decide_spec in Esafe. left.
    exact (state_rel_IMP_semantics' asm_conf k _ t [] start (conj HR (conj HF Esafe))).
  - exact (state_rel_IMP_semantics asm_conf k _ t [] start (conj HR HF)).
Qed.

End CompileSem.
