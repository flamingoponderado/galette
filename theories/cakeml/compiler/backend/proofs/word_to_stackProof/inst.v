(** * CakeML [word_to_stackProof]: instructions

    Part of the port of
    [cakeml/compiler/backend/proofs/word_to_stackProofScript.sml] (HOL lines
    3720-5594): [wRegWrite1]/[wRegWrite2], loading operands from the stack
    ([wStackLoad]) and storing results ([wStackStore]), [evaluate_wInst],
    and the lemmas about [stack_move], [PushHandler] and [PopHandler] used
    by [comp_correct].

    Notes: as in [state_rel.v].  The commented-out HOL theorems in this
    range are not ported.  HOL's antiquoted [^s]/[^t] are the word and
    stack states.  [word_exp_Op_SOME_Word], [get_vars_fromList2_eq] and
    [get_vars_fromList2_eq_cons] hold for word states of any
    compiler-configuration and ffi types, as in HOL. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.misc.misc Require Import fromList2.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend Require Import word_to_stack.
From Galette.cakeml.compiler.backend.semantics Require Import wordConvs.
From Galette.cakeml.compiler.backend.semantics Require wordSem.
From Galette.cakeml.compiler.backend.semantics Require Import stackSem stackProps.
From Galette.cakeml.compiler.backend.proofs.word_to_stackProof Require Import basic compile_props state_rel gc stack_rel moves syntax.
Import wordLang (word_loc, Word, Loc).
Import wordSem (stack_frame, StackFrame).
Open Scope N_scope.

(** ** Galette-only helpers *)

Lemma sget_var_set_var_eq {a c ffi_t} r w (t : stackSem.state a c ffi_t) :
  stackSem.get_var r (stackSem.set_var r w t) = SOME w.
Proof.
  unfold stackSem.get_var, stackSem.set_var. stk_fields. rewrite FLOOKUP_UPDATE.
  destruct (decide (r = r)); [reflexivity|congruence].
Qed.

Lemma sget_var_set_var_neq {a c ffi_t} r r' w (t : stackSem.state a c ffi_t) :
  r <> r' -> stackSem.get_var r' (stackSem.set_var r w t) = stackSem.get_var r' t.
Proof.
  intros H. unfold stackSem.get_var, stackSem.set_var. stk_fields. rewrite FLOOKUP_UPDATE.
  destruct (decide (r = r')); [contradiction|reflexivity].
Qed.

Lemma set_stack_set_var {a c ffi_t} X r w (t : stackSem.state a c ffi_t) :
  set_stack X (stackSem.set_var r w t) = stackSem.set_var r w (set_stack X t).
Proof. destruct t; reflexivity. Qed.

Section WRegWrite.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wRegWrite1_thm1" *)
Theorem wRegWrite1_thm1 : forall ac k f f' s t lens m (kont : N -> prog a) v,
  state_rel ac k f f' s t lens 0 /\
  m < f' + k /\
  (forall n, n <= k -> evaluate (kont n, t) = (NONE, stackSem.set_var n v t)) ->
  exists t',
    evaluate (wRegWrite1 kont (2 * m) (k, (f, f')), t) = (NONE, t') /\
    state_rel ac k f f' (wordSem.set_var (2 * m) v s) t' lens 0 /\
    LENGTH (stackSem.stack t') = LENGTH (stackSem.stack t) /\ stack_space t' = stack_space t.
Proof.
  intros ac k f f' s t lens m kont v (H & Hm & Hk). unfold wRegWrite1. rewrite mul2_div2.
  destruct (m <? k) eqn:Em; to_prop.
  - rewrite Hk by lia. eexists; split; [reflexivity|]. split; [apply state_rel_set_var; auto|].
    split; reflexivity.
  - rewrite ev_seq, Hk by lia.
    assert (H1 : state_rel ac k f f' s (stackSem.set_var k v t) lens 0) by (apply state_rel_set_var_k; exact H).
    rewrite (ev_store_slot ac k f f' s _ lens m v k H1) by (try lia; apply sget_var_set_var_eq).
    eexists; split; [reflexivity|].
    split; [apply state_rel_set_var2; split; [exact H1|]; split; [lia|]; split; [lia|]; split; reflexivity|].
    stk_fields. rewrite LENGTH_LUPDATE'. split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wRegWrite1_thm1_weak" *)
Theorem wRegWrite1_thm1_weak : forall ac k f f' s t lens m (kont : N -> prog a) v,
  state_rel ac k f f' s t lens 0 /\
  m < f' + k /\
  (forall n, n <= k -> evaluate (kont n, t) = (NONE, stackSem.set_var n v t)) ->
  exists t',
    evaluate (wRegWrite1 kont (2 * m) (k, (f, f')), t) = (NONE, t') /\
    state_rel ac k f f' (wordSem.set_var (2 * m) v s) t' lens 0.
Proof.
  intros ac k f f' s t lens m kont v H. destruct (wRegWrite1_thm1 ac k f f' s t lens m kont v H) as (t' & ? & ? & _).
  eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wRegWrite1_thm2" *)
Theorem wRegWrite1_thm2 : forall ac k f f' s t lens m (kont : N -> prog a) v v',
  state_rel ac k f f' s t lens 0 /\
  m < f' + k /\
  (forall n, n <= k -> evaluate (kont n, t) = (NONE, stackSem.set_var 0 v' (stackSem.set_var n v t))) ->
  exists t',
    evaluate (wRegWrite1 kont (2 * m) (k, (f, f')), t) = (NONE, t') /\
    state_rel ac k f f' (wordSem.set_var 0 v' (wordSem.set_var (2 * m) v s)) t' lens 0 /\
    LENGTH (stackSem.stack t') = LENGTH (stackSem.stack t) /\ stack_space t' = stack_space t.
Proof.
  intros ac k f f' s t lens m kont v v' (H & Hm & Hk).
  assert (Hk4 : 4 < k) by (sr_destr H; exact Hk0).
  unfold wRegWrite1. rewrite mul2_div2.
  destruct (m <? k) eqn:Em; to_prop.
  - rewrite Hk by lia. eexists; split; [reflexivity|].
    split; [|split; reflexivity].
    replace 0 with (2 * 0) at 1 by reflexivity. apply state_rel_set_var. split; [|lia].
    apply state_rel_set_var. auto.
  - rewrite ev_seq, Hk by lia.
    assert (H1 : state_rel ac k f f' s (stackSem.set_var k v t) lens 0) by (apply state_rel_set_var_k; exact H).
    assert (H2 : state_rel ac k f f' (wordSem.set_var 0 v' s) (stackSem.set_var 0 v' (stackSem.set_var k v t)) lens 0).
    { replace 0 with (2 * 0) at 1 by reflexivity. apply state_rel_set_var. split; [exact H1|lia]. }
    rewrite (ev_store_slot ac k f f' _ _ lens m v k H2)
      by (try lia; rewrite sget_var_set_var_neq by lia; apply sget_var_set_var_eq).
    eexists; split; [reflexivity|]. split.
    + stk_fields. fold (stackSem.set_var 0 v' (stackSem.set_var k v t)).
      rewrite set_stack_set_var.
      replace 0 with (2 * 0) at 1 by reflexivity. apply state_rel_set_var. split; [|lia].
      replace (LUPDATE v (stack_space t + (f + k - (m + 1))) (stackSem.stack t))
        with (LUPDATE v (stack_space (stackSem.set_var k v t) + (f + k - (m + 1)))
                (stackSem.stack (stackSem.set_var k v t))) by reflexivity.
      apply state_rel_set_var2. split; [exact H1|]. split; [lia|]. split; [lia|]. split; reflexivity.
    + stk_fields. rewrite LENGTH_LUPDATE'. split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wRegWrite2_thm1" *)
Theorem wRegWrite2_thm1 : forall ac k f f' s t lens m (kont : N -> prog a) v,
  state_rel ac k f f' s t lens 0 /\
  m < f' + k /\
  (forall n, n <= k + 1 -> evaluate (kont n, t) = (NONE, stackSem.set_var n v t)) ->
  exists t',
    evaluate (wRegWrite2 kont (2 * m) (k, (f, f')), t) = (NONE, t') /\
    state_rel ac k f f' (wordSem.set_var (2 * m) v s) t' lens 0.
Proof.
  intros ac k f f' s t lens m kont v (H & Hm & Hk). unfold wRegWrite2. rewrite mul2_div2.
  destruct (m <? k) eqn:Em; to_prop.
  - rewrite Hk by lia. eexists; split; [reflexivity|]. apply state_rel_set_var; auto.
  - rewrite ev_seq, Hk by lia.
    assert (H1 : state_rel ac k f f' s (stackSem.set_var (k + 1) v t) lens 0) by (apply state_rel_set_var_k; exact H).
    rewrite (ev_store_slot ac k f f' s _ lens m v (k + 1) H1) by (try lia; apply sget_var_set_var_eq).
    eexists; split; [reflexivity|].
    apply state_rel_set_var2. split; [exact H1|]. split; [lia|]. split; [lia|]. split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_mem_store" *)
Theorem state_rel_mem_store : forall ac k f f' s t lens extra (ad : word a) b s',
  state_rel ac k f f' s t lens extra /\
  wordSem.mem_store ad b s = SOME s' ->
  exists t',
    stackSem.mem_store ad b t = SOME t' /\
    state_rel ac k f f' s' t' lens extra.
Proof.
  intros ac k f f' s t lens extra ad b s' (H & Hm). unfold wordSem.mem_store in Hm.
  destruct (classical_dec _) as [Hin|]; [|discriminate]. injection Hm as <-.
  pose proof H as H0. sr_destr H0. unfold stackSem.mem_store. rewrite Hmd.
  destruct (classical_dec _) as [_|C]; [|contradiction].
  eexists; split; [reflexivity|].
  sr_split; ws_fields; stk_fields; try assumption.
  rewrite Hmem. reflexivity.
Qed.

End WRegWrite.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "map_var_def" *)
Fixpoint map_var {a} (f : N -> N) (e : wordLang.exp a) : wordLang.exp a :=
  match e with
  | wordLang.Var num => wordLang.Var (f num)
  | wordLang.Load exp => wordLang.Load (map_var f exp)
  | wordLang.Op wop ls => wordLang.Op wop (MAP (map_var f) ls)
  | wordLang.Shift sh e1 e2 => wordLang.Shift sh (map_var f e1) (map_var f e2)
  | wordLang.Const c => wordLang.Const c
  | wordLang.Lookup v => wordLang.Lookup v
  end.

Section TheWords.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "the_words_EVERY_IS_SOME_Word" *)
Theorem the_words_EVERY_IS_SOME_Word : forall (ls : list (option (word_loc a))) x,
  wordSem.the_words ls = SOME x -> forall a0, MEM a0 ls -> exists w, a0 = SOME (Word w).
Proof.
  induction ls as [|y ls IH]; intros x H a0 Hm; [discriminate|]. cbn [MEM] in Hm.
  cbn [wordSem.the_words] in H.
  destruct y as [[w|]|]; try discriminate. destruct (wordSem.the_words ls) as [xs|] eqn:E; [|discriminate].
  apply orb_true_iff in Hm as [Hm|Hm].
  - apply bool_decide_spec in Hm. subst a0. eauto.
  - eapply IH; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "the_words_SOME_eq" *)
Theorem the_words_SOME_eq : forall (ls : list (option (word_loc a))) x,
  wordSem.the_words ls = SOME x ->
  x = MAP (fun x => match x with SOME (Word y) => y | _ => ARB end) ls.
Proof.
  induction ls as [|y ls IH]; intros x H; cbn [wordSem.the_words] in H; [injection H as <-; reflexivity|].
  destruct y as [[w|]|]; try discriminate. destruct (wordSem.the_words ls) as [xs|] eqn:E; [|discriminate].
  injection H as <-. cbn [List.map]. f_equal. apply IH. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "the_words_MAP_exists" *)
Theorem the_words_MAP_exists : forall {B} `{EqDecision B} (ls : list B) x a0 (f : B -> option (word_loc a)),
  wordSem.the_words (MAP f ls) = SOME x /\ MEM a0 ls -> exists w, f a0 = SOME (Word w).
Proof.
  intros B HB ls; induction ls as [|y ls IH]; intros x a0 f (H & Hm); [discriminate|].
  cbn [List.map wordSem.the_words] in H. cbn [MEM] in Hm.
  destruct (f y) as [[w|]|] eqn:Ey; try discriminate. destruct (wordSem.the_words (MAP f ls)) as [xs|] eqn:E; [|discriminate].
  apply orb_true_iff in Hm as [Hm|Hm].
  - apply bool_decide_spec in Hm. subst a0. eauto.
  - eapply IH; eauto.
Qed.

End TheWords.

Section Operands.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_with_memory" *)
Theorem state_rel_with_memory : forall ac k f f' s t lens extra m,
  state_rel ac k f f' s t lens extra ->
  state_rel ac k f f' (wordSem.set_memory m s) (stackSem.set_memory m t) lens extra.
Proof. intros ac k f f' s t lens extra m H. sr_destr H. sr_split; ws_fields; stk_fields; try assumption; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_exp_Op_SOME_Word" *)
Theorem word_exp_Op_SOME_Word : forall {C F : Type} (s : wordSem.state a C F) op wexps x,
  wordSem.word_exp s (wordLang.Op op wexps) = SOME x -> exists w, x = Word w.
Proof.
  intros C F s op wexps x H. cbn [wordSem.word_exp] in H.
  destruct (wordSem.the_words _); [|discriminate]. destruct (wordLang.word_op op _); [|discriminate].
  injection H as <-. eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_get_fp_var" *)
Theorem state_rel_get_fp_var : forall ac k f f' s t lens extra n,
  state_rel ac k f f' s t lens extra -> wordSem.get_fp_var n s = stackSem.get_fp_var n t.
Proof.
  intros ac k f f' s t lens extra n H. sr_destr H. unfold wordSem.get_fp_var, stackSem.get_fp_var.
  rewrite Hfp. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_set_fp_var" *)
Theorem state_rel_set_fp_var : forall ac k f f' s t lens extra n v,
  state_rel ac k f f' s t lens extra ->
  state_rel ac k f f' (wordSem.set_fp_var n v s) (stackSem.set_fp_var n v t) lens extra.
Proof.
  intros ac k f f' s t lens extra n v H. sr_destr H. unfold wordSem.set_fp_var, stackSem.set_fp_var.
  sr_split; ws_fields; stk_fields; try assumption. rewrite Hfp. reflexivity.
Qed.

Lemma wStackLoad_nil (p : prog a) : wStackLoad [] p = p.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wStackLoad_wReg1" *)
Theorem evaluate_wStackLoad_wReg1 : forall ac k f f' r x r' s t lens c0,
  wReg1 r (k, (f, f')) = (x, r') /\
  EVEN r /\
  wordSem.get_var r s = SOME c0 /\
  state_rel ac k f f' s t lens 0 ->
  exists t' : stackSem.state a c ffi_t,
    evaluate (wStackLoad x Skip, t) = (NONE, t') /\
    clock t = clock t' /\
    state_rel ac k f f' s t' lens 0 /\
    LENGTH (stackSem.stack t') = LENGTH (stackSem.stack t) /\ stack_space t' = stack_space t /\
    bitmaps t' = bitmaps t /\
    (forall r, r <> k -> stackSem.get_var r t' = stackSem.get_var r t) /\
    r' <> k + 1 /\
    stackSem.get_var r' t' = SOME c0.
Proof.
  intros ac k f f' r x r' s t lens c0 (Hw & He & Hg & H). unfold wReg1 in Hw. cbv zeta in Hw.
  pose proof (even_div2 r He) as Er.
  destruct (r DIV 2 <? k) eqn:Ek; to_prop; injection Hw as <- <-.
  - exists t. rewrite wStackLoad_nil, ev_skip. split; [reflexivity|]. split; [reflexivity|].
    split; [exact H|]. do 4 (split; [reflexivity|]). split; [lia|].
    apply (state_rel_get_var_imp' ac k f f' s t lens 0 r c0). auto.
  - cbn [wStackLoad]. rewrite ev_seq.
    rewrite (ev_load_slot ac k f f' s t lens (r DIV 2) c0 k H) by (try lia; rewrite <- Er; exact Hg).
    rewrite ev_skip. eexists; split; [reflexivity|].
    split; [reflexivity|]. split; [apply state_rel_set_var_k; exact H|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [intros r0 Hr0; apply sget_var_set_var_neq; lia|]. split; [lia|]. apply sget_var_set_var_eq.
Qed.

Lemma word_exp_add_const s r c0 w :
  wordSem.word_exp s (wordLang.Op asm.Add [wordLang.Var r; wordLang.Const c0]) = SOME (Word w) ->
  exists x, wordSem.get_var r s = SOME (Word x) /\ w = FOLDR word_add (n2w 0) [x; c0].
Proof.
  intros H. cbn [wordSem.word_exp List.map wordSem.the_words] in H.
  destruct (wordSem.get_var r s) as [[x|]|]; try discriminate. cbn in H. injection H as <-. eauto.
Qed.

Lemma sword_exp_add_const t r x c0 :
  stackSem.get_var r t = SOME (Word x) ->
  stackSem.word_exp t (wordLang.Op asm.Add [wordLang.Var r; wordLang.Const c0]) = SOME (FOLDR word_add (n2w 0) [x; c0]).
Proof. intros H. unfold stackSem.get_var in H. cbn [stackSem.word_exp List.map]. rewrite H. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wStackLoad_wReg1_with_const" *)
Theorem evaluate_wStackLoad_wReg1_with_const : forall ac k f f' r x r' s t lens c0 w,
  wReg1 r (k, (f, f')) = (x, r') /\
  EVEN r /\
  wordSem.word_exp s (wordLang.Op asm.Add [wordLang.Var r; wordLang.Const c0]) = SOME (Word w) /\
  state_rel ac k f f' s t lens 0 ->
  exists t' : stackSem.state a c ffi_t,
    evaluate (wStackLoad x Skip, t) = (NONE, t') /\
    clock t = clock t' /\
    state_rel ac k f f' s t' lens 0 /\
    LENGTH (stackSem.stack t') = LENGTH (stackSem.stack t) /\ stack_space t' = stack_space t /\
    r' <> k + 1 /\
    stackSem.word_exp t' (wordLang.Op asm.Add [wordLang.Var r'; wordLang.Const c0]) = SOME w.
Proof.
  intros ac k f f' r x r' s t lens c0 w (Hw & He & Hx & H).
  destruct (word_exp_add_const _ _ _ _ Hx) as (x0 & Hg & ->).
  destruct (evaluate_wStackLoad_wReg1 ac k f f' r x r' s t lens (Word x0) (conj Hw (conj He (conj Hg H))))
    as (t' & E & Hc & Hs & Hl & Hsp & _ & _ & Hk & Hg').
  exists t'. do 5 (split; [assumption|]). split; [exact Hk|]. apply sword_exp_add_const, Hg'.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wStackLoad_clock" *)
Theorem evaluate_wStackLoad_clock : forall clk x t,
  evaluate (wStackLoad x Skip, set_clock clk t) =
  (I ## (fun st => set_clock clk st)) (evaluate (wStackLoad x Skip, t)).
Proof.
  intros clk x. induction x as [|[r i] x IH]; intros t.
  - rewrite !wStackLoad_nil, !ev_skip. reflexivity.
  - cbn [wStackLoad]. rewrite !ev_seq, !ev_stackload. stk_fields.
    destruct (use_stack t); cbn [negb]; [|reflexivity].
    destruct (_ <? _); [|destruct t; reflexivity].
    replace (stackSem.set_var r (EL (stack_space t + i) (stackSem.stack t)) (set_clock clk t))
      with (set_clock clk (stackSem.set_var r (EL (stack_space t + i) (stackSem.stack t)) t)) by (destruct t; reflexivity).
    apply IH.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wStackLoad_wReg2" *)
Theorem evaluate_wStackLoad_wReg2 : forall ac k f f' r x r' s t lens c0,
  wReg2 r (k, (f, f')) = (x, r') /\
  EVEN r /\
  wordSem.get_var r s = SOME c0 /\
  state_rel ac k f f' s t lens 0 ->
  exists t' : stackSem.state a c ffi_t,
    evaluate (wStackLoad x Skip, t) = (NONE, t') /\
    clock t = clock t' /\
    bitmaps t = bitmaps t' /\
    state_rel ac k f f' s t' lens 0 /\
    LENGTH (stackSem.stack t') = LENGTH (stackSem.stack t) /\ stack_space t' = stack_space t /\
    (forall r, r <> k + 1 -> stackSem.get_var r t' = stackSem.get_var r t) /\
    (forall r c0, r <> k + 1 ->
       stackSem.word_exp t' (wordLang.Op asm.Add [wordLang.Var r; wordLang.Const c0]) =
       stackSem.word_exp t (wordLang.Op asm.Add [wordLang.Var r; wordLang.Const c0])) /\
    stackSem.get_var r' t' = SOME c0.
Proof.
  intros ac k f f' r x r' s t lens c0 (Hw & He & Hg & H). unfold wReg2 in Hw. cbv zeta in Hw.
  pose proof (even_div2 r He) as Er.
  destruct (r DIV 2 <? k) eqn:Ek; to_prop; injection Hw as <- <-.
  - exists t. rewrite wStackLoad_nil, ev_skip. do 3 (split; [reflexivity|]).
    split; [exact H|]. do 4 (split; [reflexivity|]).
    apply (state_rel_get_var_imp' ac k f f' s t lens 0 r c0). auto.
  - cbn [wStackLoad]. rewrite ev_seq.
    rewrite (ev_load_slot ac k f f' s t lens (r DIV 2) c0 (k + 1) H) by (try lia; rewrite <- Er; exact Hg).
    rewrite ev_skip. eexists; split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [apply state_rel_set_var_k; exact H|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [intros r0 Hr0; apply sget_var_set_var_neq; lia|].
    split; [|apply sget_var_set_var_eq].
    intros r0 c1 Hr0. cbn [stackSem.word_exp List.map]. unfold stackSem.set_var. stk_fields.
    rewrite FLOOKUP_UPDATE. destruct (decide (k + 1 = r0)); [lia|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wStackLoad_seq" *)
Theorem evaluate_wStackLoad_seq : forall ls (prog0 : prog a) t,
  evaluate (wStackLoad ls prog0, t) = evaluate (Seq (wStackLoad ls Skip) prog0, t).
Proof.
  induction ls as [|[r i] ls IH]; intros prog0 t.
  - rewrite !wStackLoad_nil, ev_seq, ev_skip. reflexivity.
  - cbn [wStackLoad]. rewrite !ev_seq. destruct (evaluate (StackLoad r i, t)) as [[res|] t1].
    + reflexivity.
    + rewrite IH, ev_seq. reflexivity.
Qed.

Lemma wStackStore_nil (p : prog a) : wStackStore [] p = p.
Proof. reflexivity. Qed.

Lemma EVEN_lt_div2 r f' k : EVEN r -> r < 2 * f' + 2 * k -> r DIV 2 < f' + k.
Proof. intros He Hr. pose proof (even_div2 r He). lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wStackStore_wReg1" *)
Theorem evaluate_wStackStore_wReg1 : forall ac k f f' r x r' s t lens c0 LENGTH_t_stack t_stack_space,
  wReg1 r (k, (f, f')) = (x, r') /\
  EVEN r /\
  r < 2 * f' + 2 * k /\
  state_rel ac k f f' s t lens 0 /\
  LENGTH (stackSem.stack t) = LENGTH_t_stack /\
  stack_space t = t_stack_space ->
  exists t' : stackSem.state a c ffi_t,
    evaluate (wStackStore x Skip, stackSem.set_var r' c0 t) = (NONE, t') /\
    state_rel ac k f f' (wordSem.set_var r c0 s) t' lens 0 /\
    LENGTH (stackSem.stack t') = LENGTH_t_stack /\ stack_space t' = t_stack_space.
Proof.
  intros ac k f f' r x r' s t lens c0 L SP (Hw & He & Hr & H & <- & <-). unfold wReg1 in Hw. cbv zeta in Hw.
  pose proof (even_div2 r He) as Er. pose proof (EVEN_lt_div2 _ _ _ He Hr) as Hr2.
  destruct (r DIV 2 <? k) eqn:Ek; to_prop; injection Hw as <- <-.
  - rewrite wStackStore_nil, ev_skip. eexists; split; [reflexivity|].
    split; [|split; reflexivity]. rewrite Er at 1. apply state_rel_set_var. auto.
  - cbn [wStackStore]. rewrite ev_seq, ?wStackStore_nil, ev_skip.
    assert (H1 : state_rel ac k f f' s (stackSem.set_var k c0 t) lens 0) by (apply state_rel_set_var_k; exact H).
    rewrite (ev_store_slot ac k f f' s _ lens (r DIV 2) c0 k H1) by (try lia; apply sget_var_set_var_eq).
    eexists; split; [reflexivity|]. split.
    + rewrite Er at 1. apply state_rel_set_var2. split; [exact H1|]. split; [lia|]. split; [lia|]. split; reflexivity.
    + stk_fields. rewrite LENGTH_LUPDATE'. split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wStackStore_wReg1_strong" *)
Theorem evaluate_wStackStore_wReg1_strong : forall ac k f f' r x r' s t lens c0,
  wReg1 r (k, (f, f')) = (x, r') /\
  EVEN r /\
  r < 2 * f' + 2 * k /\
  state_rel ac k f f' s t lens 0 ->
  exists t' : stackSem.state a c ffi_t,
    evaluate (wStackStore x Skip, stackSem.set_var r' c0 t) = (NONE, stackSem.set_var r' c0 t') /\
    state_rel ac k f f' (wordSem.set_var r c0 s) (stackSem.set_var r' c0 t') lens 0 /\
    LENGTH (stackSem.stack t') = LENGTH (stackSem.stack t) /\ stack_space t' = stack_space t.
Proof.
  intros ac k f f' r x r' s t lens c0 (Hw & He & Hr & H). unfold wReg1 in Hw. cbv zeta in Hw.
  pose proof (even_div2 r He) as Er. pose proof (EVEN_lt_div2 _ _ _ He Hr) as Hr2.
  destruct (r DIV 2 <? k) eqn:Ek; to_prop; injection Hw as <- <-.
  - rewrite wStackStore_nil, ev_skip. exists t. split; [reflexivity|].
    split; [|split; reflexivity]. rewrite Er at 1. apply state_rel_set_var. auto.
  - cbn [wStackStore]. rewrite ev_seq, ?wStackStore_nil, ev_skip.
    assert (H1 : state_rel ac k f f' s (stackSem.set_var k c0 t) lens 0) by (apply state_rel_set_var_k; exact H).
    rewrite (ev_store_slot ac k f f' s _ lens (r DIV 2) c0 k H1) by (try lia; apply sget_var_set_var_eq).
    exists (set_stack (LUPDATE c0 (stack_space t + (f + k - (r DIV 2 + 1))) (stackSem.stack t)) t).
    split; [stk_fields; rewrite <- set_stack_set_var; reflexivity|]. split.
    + rewrite <- set_stack_set_var. rewrite Er at 1.
      replace (LUPDATE c0 (stack_space t + (f + k - (r DIV 2 + 1))) (stackSem.stack t))
        with (LUPDATE c0 (stack_space (stackSem.set_var k c0 t) + (f + k - (r DIV 2 + 1)))
                (stackSem.stack (stackSem.set_var k c0 t))) by reflexivity.
      apply state_rel_set_var2. split; [exact H1|]. split; [lia|]. split; [lia|]. split; reflexivity.
    + stk_fields. rewrite LENGTH_LUPDATE'. split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wStackStore_wReg1_new" *)
Theorem evaluate_wStackStore_wReg1_new : forall ac k f f' r x r' s t lens c0 (kont : prog a) LENGTH_t_stack t_stack_space,
  wReg1 r (k, (f, f')) = (x, r') /\
  EVEN r /\
  r < 2 * f' + 2 * k /\
  (exists t',
    evaluate (kont, t) = (NONE, stackSem.set_var r' c0 t') /\
    state_rel ac k f f' s t' lens 0 /\
    LENGTH (stackSem.stack t') = LENGTH_t_stack /\ stack_space t' = t_stack_space) ->
  exists t' : stackSem.state a c ffi_t,
    evaluate (Seq kont (wStackStore x Skip), t) = (NONE, t') /\
    state_rel ac k f f' (wordSem.set_var r c0 s) t' lens 0 /\
    LENGTH (stackSem.stack t') = LENGTH_t_stack /\ stack_space t' = t_stack_space.
Proof.
  intros ac k f f' r x r' s t lens c0 kont L SP (Hw & He & Hr & t1 & E1 & H1 & HL & HS).
  rewrite ev_seq, E1. apply (evaluate_wStackStore_wReg1 ac k f f' r x r' s t1 lens c0 L SP). auto 10.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wStackStore_wReg2_new" *)
Theorem evaluate_wStackStore_wReg2_new : forall ac k f f' r x r' s t lens c0 (kont : prog a) LENGTH_t_stack t_stack_space,
  wReg2 r (k, (f, f')) = (x, r') /\
  EVEN r /\
  r < 2 * f' + 2 * k /\
  (exists t',
    evaluate (kont, t) = (NONE, stackSem.set_var r' c0 t') /\
    state_rel ac k f f' s t' lens 0 /\
    LENGTH (stackSem.stack t') = LENGTH_t_stack /\ stack_space t' = t_stack_space) ->
  exists t' : stackSem.state a c ffi_t,
    evaluate (Seq kont (wStackStore x Skip), t) = (NONE, t') /\
    state_rel ac k f f' (wordSem.set_var r c0 s) t' lens 0 /\
    LENGTH (stackSem.stack t') = LENGTH_t_stack /\ stack_space t' = t_stack_space.
Proof.
  intros ac k f f' r x r' s t lens c0 kont L SP (Hw & He & Hr & t1 & E1 & H & <- & <-).
  rewrite ev_seq, E1. unfold wReg2 in Hw. cbv zeta in Hw.
  pose proof (even_div2 r He) as Er. pose proof (EVEN_lt_div2 _ _ _ He Hr) as Hr2.
  destruct (r DIV 2 <? k) eqn:Ek; to_prop; injection Hw as <- <-.
  - rewrite wStackStore_nil, ev_skip. eexists; split; [reflexivity|].
    split; [|split; reflexivity]. rewrite Er at 1. apply state_rel_set_var. auto.
  - cbn [wStackStore]. rewrite ev_seq, ?wStackStore_nil, ev_skip.
    assert (H1 : state_rel ac k f f' s (stackSem.set_var (k + 1) c0 t1) lens 0) by (apply state_rel_set_var_k; exact H).
    rewrite (ev_store_slot ac k f f' s _ lens (r DIV 2) c0 (k + 1) H1) by (try lia; apply sget_var_set_var_eq).
    eexists; split; [reflexivity|]. split.
    + rewrite Er at 1. apply state_rel_set_var2. split; [exact H1|]. split; [lia|]. split; [lia|]. split; reflexivity.
    + stk_fields. rewrite LENGTH_LUPDATE'. split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wStackStore_wReg1_0" *)
Theorem evaluate_wStackStore_wReg1_0 : forall ac k f f' r x r' s t lens c0 c1 LENGTH_t_stack t_stack_space,
  wReg1 r (k, (f, f')) = (x, r') /\
  EVEN r /\
  r < 2 * f' + 2 * k /\
  state_rel ac k f f' s t lens 0 /\
  LENGTH (stackSem.stack t) = LENGTH_t_stack /\
  stack_space t = t_stack_space ->
  exists t' : stackSem.state a c ffi_t,
    evaluate (wStackStore x Skip, stackSem.set_var 0 c1 (stackSem.set_var r' c0 t)) = (NONE, t') /\
    state_rel ac k f f' (wordSem.set_var 0 c1 (wordSem.set_var r c0 s)) t' lens 0 /\
    LENGTH (stackSem.stack t') = LENGTH_t_stack /\ stack_space t' = t_stack_space.
Proof.
  intros ac k f f' r x r' s t lens c0 c1 L SP (Hw & He & Hr & H & HL & HS).
  assert (Hk : 4 < k) by (sr_destr H; exact Hk).
  destruct (N.eq_dec r 0) as [->|Hr0].
  - assert (r' = 0) as -> by (unfold wReg1 in Hw; cbv zeta in Hw; destruct (0 DIV 2 <? k) eqn:E;
      [injection Hw as _ <-; reflexivity|apply N.ltb_ge in E; rewrite N.Div0.div_0_l in E; lia]).
    rewrite set_var_cancel, set_var_cancel_word.
    apply (evaluate_wStackStore_wReg1 ac k f f' 0 x 0 s t lens c1 L SP). auto 10.
  - assert (Hr'0 : r' <> 0).
    { unfold wReg1 in Hw; cbv zeta in Hw. pose proof (even_div2 r He).
      destruct (r DIV 2 <? k); injection Hw as _ <-; lia. }
    rewrite (set_var_swap 0 r') by congruence. rewrite (set_var_swap_word 0 r) by congruence.
    apply (evaluate_wStackStore_wReg1 ac k f f' r x r' (wordSem.set_var 0 c1 s) (stackSem.set_var 0 c1 t) lens c0 L SP).
    split; [exact Hw|]. split; [exact He|]. split; [exact Hr|]. split; [|split; assumption].
    replace 0 with (2 * 0) at 1 by reflexivity. apply state_rel_set_var. split; [exact H|lia].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wRegWrite1_seq" *)
Theorem evaluate_wRegWrite1_seq : forall (g : N -> prog a) r k f f' t,
  evaluate (wRegWrite1 g r (k, (f, f')), t) =
  (let '(l, n) := wReg1 r (k, (f, f')) in evaluate (Seq (g n) (wStackStore l Skip), t)).
Proof.
  intros g r k f f' t. unfold wRegWrite1, wReg1. cbv zeta.
  destruct (r DIV 2 <? k); cbv beta iota.
  - rewrite wStackStore_nil, ev_seq. destruct (evaluate (g _, t)) as [[res|] t1]; [reflexivity|].
    rewrite ev_skip. reflexivity.
  - cbn [wStackStore]. rewrite !ev_seq. destruct (evaluate (g k, t)) as [[res|] t1]; [reflexivity|].
    rewrite (ev_seq Skip), ev_skip. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wRegWrite2_seq" *)
Theorem evaluate_wRegWrite2_seq : forall (g : N -> prog a) r k f f' t,
  evaluate (wRegWrite2 g r (k, (f, f')), t) =
  (let '(l, n) := wReg2 r (k, (f, f')) in evaluate (Seq (g n) (wStackStore l Skip), t)).
Proof.
  intros g r k f f' t. unfold wRegWrite2, wReg2. cbv zeta.
  destruct (r DIV 2 <? k); cbv beta iota.
  - rewrite wStackStore_nil, ev_seq. destruct (evaluate (g _, t)) as [[res|] t1]; [reflexivity|].
    rewrite ev_skip. reflexivity.
  - cbn [wStackStore]. rewrite !ev_seq. destruct (evaluate (g (k + 1), t)) as [[res|] t1]; [reflexivity|].
    rewrite (ev_seq Skip), ev_skip. reflexivity.
Qed.

End Operands.

(** ** Galette-only building blocks for [evaluate_wInst] *)

Section WInstPatterns.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

Lemma load1 ac k f f' s t lens r l n w (P : prog a) :
  state_rel ac k f f' s t lens 0 -> wReg1 r (k, (f, f')) = (l, n) -> EVEN r -> wordSem.get_var r s = SOME w ->
  exists t1, evaluate (wStackLoad l P, t) = evaluate (P, t1) /\ state_rel ac k f f' s t1 lens 0 /\
    stackSem.get_var n t1 = SOME w /\ n <> k + 1 /\
    LENGTH (stackSem.stack t1) = LENGTH (stackSem.stack t) /\ stack_space t1 = stack_space t /\
    (forall r0, r0 <> k -> stackSem.get_var r0 t1 = stackSem.get_var r0 t).
Proof.
  intros H Hw He Hg.
  destruct (evaluate_wStackLoad_wReg1 ac k f f' r l n s t lens w (conj Hw (conj He (conj Hg H))))
    as (t1 & E & _ & H1 & Hl & Hs & _ & Hr & Hk & Hg1).
  exists t1. rewrite evaluate_wStackLoad_seq, ev_seq, E. auto 10.
Qed.

Lemma load2 ac k f f' s t lens r l n w (P : prog a) :
  state_rel ac k f f' s t lens 0 -> wReg2 r (k, (f, f')) = (l, n) -> EVEN r -> wordSem.get_var r s = SOME w ->
  exists t1, evaluate (wStackLoad l P, t) = evaluate (P, t1) /\ state_rel ac k f f' s t1 lens 0 /\
    stackSem.get_var n t1 = SOME w /\
    LENGTH (stackSem.stack t1) = LENGTH (stackSem.stack t) /\ stack_space t1 = stack_space t /\
    (forall r0, r0 <> k + 1 -> stackSem.get_var r0 t1 = stackSem.get_var r0 t).
Proof.
  intros H Hw He Hg.
  destruct (evaluate_wStackLoad_wReg2 ac k f f' r l n s t lens w (conj Hw (conj He (conj Hg H))))
    as (t1 & E & _ & _ & H1 & Hl & Hs & Hr & _ & Hg1).
  exists t1. rewrite evaluate_wStackLoad_seq, ev_seq, E. auto 10.
Qed.

Lemma load12 ac k f f' s t lens r2 r3 l l' n2 n3 w2 w3 (P : prog a) :
  state_rel ac k f f' s t lens 0 ->
  wReg1 r2 (k, (f, f')) = (l, n2) -> EVEN r2 -> wordSem.get_var r2 s = SOME w2 ->
  wReg2 r3 (k, (f, f')) = (l', n3) -> EVEN r3 -> wordSem.get_var r3 s = SOME w3 ->
  exists t1, evaluate (wStackLoad (l ++ l') P, t) = evaluate (P, t1) /\ state_rel ac k f f' s t1 lens 0 /\
    stackSem.get_var n2 t1 = SOME w2 /\ stackSem.get_var n3 t1 = SOME w3 /\
    LENGTH (stackSem.stack t1) = LENGTH (stackSem.stack t) /\ stack_space t1 = stack_space t /\
    (forall r0, r0 <> k -> r0 <> k + 1 -> stackSem.get_var r0 t1 = stackSem.get_var r0 t).
Proof.
  intros H Hw2 He2 Hg2 Hw3 He3 Hg3. rewrite wStackLoad_append.
  destruct (load1 ac k f f' s t lens r2 l n2 w2 (wStackLoad l' P) H Hw2 He2 Hg2)
    as (t1 & E1 & H1 & G1 & Hn2 & L1 & S1 & R1).
  destruct (load2 ac k f f' s t1 lens r3 l' n3 w3 P H1 Hw3 He3 Hg3)
    as (t2 & E2 & H2 & G2 & L2 & S2 & R2).
  exists t2. cbv beta. rewrite E1, E2. split; [reflexivity|]. split; [exact H2|].
  split; [rewrite R2 by exact Hn2; exact G1|]. split; [exact G2|].
  split; [congruence|]. split; [congruence|]. intros r0 Hk Hk1. rewrite R2, R1 by assumption. reflexivity.
Qed.

Lemma write1 ac k f f' s t lens r1 (G : N -> prog a) v :
  state_rel ac k f f' s t lens 0 -> EVEN r1 -> r1 < 2 * f' + 2 * k ->
  (forall n1, evaluate (G n1, t) = (NONE, stackSem.set_var n1 v t)) ->
  exists t', evaluate (wRegWrite1 G r1 (k, (f, f')), t) = (NONE, t') /\
    state_rel ac k f f' (wordSem.set_var r1 v s) t' lens 0 /\
    LENGTH (stackSem.stack t') = LENGTH (stackSem.stack t) /\ stack_space t' = stack_space t.
Proof.
  intros H He Hr HG. rewrite evaluate_wRegWrite1_seq. destruct (wReg1 r1 (k, (f, f'))) as [l1 n1] eqn:Ew.
  rewrite ev_seq, HG. apply (evaluate_wStackStore_wReg1 ac k f f' r1 l1 n1 s t lens v _ _). auto 10.
Qed.

Lemma write1_0 ac k f f' s t lens r1 (G : N -> prog a) v v0 :
  state_rel ac k f f' s t lens 0 -> EVEN r1 -> r1 < 2 * f' + 2 * k ->
  (forall n1, evaluate (G n1, t) = (NONE, stackSem.set_var 0 v0 (stackSem.set_var n1 v t))) ->
  exists t', evaluate (wRegWrite1 G r1 (k, (f, f')), t) = (NONE, t') /\
    state_rel ac k f f' (wordSem.set_var 0 v0 (wordSem.set_var r1 v s)) t' lens 0 /\
    LENGTH (stackSem.stack t') = LENGTH (stackSem.stack t) /\ stack_space t' = stack_space t.
Proof.
  intros H He Hr HG. rewrite evaluate_wRegWrite1_seq. destruct (wReg1 r1 (k, (f, f'))) as [l1 n1] eqn:Ew.
  rewrite ev_seq, HG. apply (evaluate_wStackStore_wReg1_0 ac k f f' r1 l1 n1 s t lens v v0 _ _). auto 10.
Qed.

Lemma state_rel_mem_eqs ac k f f' s t lens extra :
  state_rel ac k f f' s t lens extra ->
  stackSem.memory t = wordSem.memory s /\ stackSem.mdomain t = wordSem.mdomain s /\ stackSem.be t = wordSem.be s.
Proof. intros H. sr_destr H. auto. Qed.

Lemma state_rel_mem_load ac k f f' s t lens extra w :
  state_rel ac k f f' s t lens extra -> stackSem.mem_load w t = wordSem.mem_load w s.
Proof.
  intros H. destruct (state_rel_mem_eqs _ _ _ _ _ _ _ _ H) as (Hm & Hd & _).
  unfold stackSem.mem_load, wordSem.mem_load. rewrite Hm, Hd. reflexivity.
Qed.

End WInstPatterns.

Lemma MAX_lt_iff m n x : MAX m n < x <-> m < x /\ n < x.
Proof. unfold MAX. destruct (m <? n) eqn:E; to_prop; lia. Qed.

Lemma max3_lt_iff m n p x : max3 m n p < x <-> m < x /\ n < x /\ p < x.
Proof. unfold max3. destruct (n <? m) eqn:E1, (m <? p) eqn:E2, (n <? p) eqn:E3; to_prop; lia. Qed.

Lemma is_phy_var_EVEN n : is_true (is_phy_var n) -> EVEN n.
Proof.
  unfold is_phy_var, is_true. intros H. apply N.eqb_eq in H. apply N.even_spec. exists (n DIV 2).
  pose proof (N.div_mod n 2 ltac:(lia)). lia.
Qed.

Lemma Zeqb_bool_decide (x y : Z) : Z.eqb x y = bool_decide (x = y).
Proof. destruct (Z.eqb_spec x y); [rewrite bd_true'|rewrite bd_false']; auto. Qed.

Lemma mod2_EVEN n : n MOD 2 = 0 -> is_true (EVEN n).
Proof. intros H. apply N.even_spec. exists (n DIV 2). pose proof (N.div_mod n 2 ltac:(lia)). lia. Qed.

Ltac winst_prep :=
  repeat match goal with
  | H : is_true (is_phy_var ?n) |- _ => apply is_phy_var_EVEN in H
  | H : context [MAX _ _ < _] |- _ => rewrite MAX_lt_iff in H
  | H : context [max3 _ _ _ < _] |- _ => rewrite max3_lt_iff in H
  end; to_prop;
  repeat match goal with H : ?n MOD 2 = 0 |- _ => apply mod2_EVEN in H end.

Ltac inv_hi H :=
  unfold option_map in H;
  repeat match type of H with
  | SOME _ = SOME _ => fail 1
  | context [match ?x with _ => _ end] =>
      lazymatch x with context [match _ with _ => _ end] => fail | _ => idtac end;
      tryif is_var x then (destruct x; cbn beta iota zeta in H; try discriminate H)
      else (let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H; try discriminate H)
  end.

Ltac wfin E' H' :=
  eexists; split; [rewrite E'; reflexivity|]; split; [exact H'|]; split; congruence.

Ltac sinst := cbv beta; rewrite ev_inst; unfold inst, assign; cbn [stackSem.word_exp stackSem.get_vars List.map];
  unfold stackSem.get_var in *.

Ltac fp_pure H :=
  rewrite ev_inst; unfold inst;
  repeat match goal with |- context [stackSem.get_fp_var ?n _] =>
    erewrite <- (state_rel_get_fp_var _ _ _ _ _ _ _ _ n H) end;
  repeat match goal with Hb : bool_decide _ = true |- _ => apply bool_decide_spec in Hb end;
  repeat (match goal with
          | Hp : ?x = ?y |- context [Z.eqb ?x ?y] => rewrite (proj2 (Z.eqb_eq x y) Hp)
          | Hp : ?x = ?y |- context [N.eqb ?x ?y] => rewrite (proj2 (N.eqb_eq x y) Hp)
          | Hp : ?x <> ?y |- context [N.eqb ?x ?y] => rewrite (proj2 (N.eqb_neq x y) Hp)
          | Hx : ?x = SOME _ |- context [?x] => rewrite Hx
          | Hx : ?x = true |- context [?x] => rewrite Hx
          | Hx : ?x = false |- context [?x] => rewrite Hx
          end; cbv beta iota zeta).

Section WInst.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst" *)
Theorem evaluate_wInst : forall ac k f f' lens i s t s',
  wordSem.inst i s = SOME s' /\
  wordLang.every_var_inst is_phy_var i /\
  wordLang.max_var_inst i < 2 * f' + 2 * k /\
  inst_arg_convention i /\
  state_rel ac k f f' s t lens 0 ->
  exists t',
    evaluate (wInst i (k, (f, f')), t) = (NONE, t') /\
    state_rel ac k f f' s' t' lens 0 /\
    LENGTH (stackSem.stack t') = LENGTH (stackSem.stack t) /\ stack_space t' = stack_space t.
Proof.
  intros ac k f f' lens i s t s' (Hi & Hev & Hmax & Hconv & H).
  assert (Hk : 4 < k) by (sr_destr H; exact Hk).
  destruct i as [|r w|ar|op r [a0 off]|fop].
  - (* Skip *)
    cbn in Hi. injection Hi as <-. exists t. cbn [wInst]. rewrite ev_inst. cbn [inst]. auto.
  - (* Const *)
    cbn [wordSem.inst wordSem.assign wordSem.word_exp] in Hi. injection Hi as <-.
    cbn [wordLang.every_var_inst wordLang.max_var_inst] in Hev, Hmax. winst_prep.
    cbn [wInst]. apply write1; [exact H|exact Hev|lia|].
    intros n1. rewrite ev_inst, inst_const. reflexivity.
  - (* Arith *)
    destruct ar as [bop r1 r2 [r3|imm]|sh r1 r2 [r3|imm]|r1 r2 r3|r1 r2 r3 r4|r1 r2 r3 r4 r5|r1 r2 r3 r4|r1 r2 r3 r4|r1 r2 r3 r4];
      cbn [wordLang.every_var_inst wordLang.max_var_inst wordLang.every_var_imm inst_arg_convention] in Hev, Hmax, Hconv;
      winst_prep;
      cbn [wordSem.inst] in Hi; unfold wordSem.assign in Hi;
      cbn [wordSem.word_exp wordSem.get_vars List.map wordSem.the_words] in Hi;
      inv_hi Hi; try (injection Hi as <-); cbn [wInst].
    + (* Binop Reg *)
      destruct (wReg1 r2 _) as [l n2] eqn:Ew2. destruct (wReg2 r3 _) as [l' n3] eqn:Ew3.
      destruct (load12 ac k f f' s t lens r2 r3 l l' n2 n3 _ _ (wRegWrite1 (fun n1 => Inst (Arith (Binop bop n1 n2 (Reg n3)))) r1 (k, (f, f')))
                  H Ew2 ltac:(assumption) ltac:(eassumption) Ew3 ltac:(assumption) ltac:(eassumption)) as (t1 & E1' & HS1 & G2 & G3 & L1 & S1 & _).
      rewrite E1'.
      edestruct (write1 ac k f f' s t1 lens r1) as (t' & E' & H' & L' & S'); [exact HS1|assumption|lia| |wfin E' H'].
      intros n1. sinst. rewrite G2.
      destruct (bool_decide (bop = asm.Or) && bool_decide (Reg n3 = Reg n2)) eqn:Eb.
      * apply andb_prop in Eb as [Eb1 Eb2]. apply bool_decide_spec in Eb1, Eb2. subst bop. injection Eb2 as ->.
        rewrite G2 in G3. injection G3 as <-. match goal with Hop : wordLang.word_op _ _ = SOME _ |- _ => cbn in Hop; injection Hop as <- end.
        rewrite (proj1 (proj2 (proj2 (proj2 (WORD_OR_CLAUSES _))))), WORD_OR_IDEM. reflexivity.
      * rewrite G3. cbn [EVERY IS_SOME andb List.map THE]. match goal with Hop : wordLang.word_op _ _ = SOME _ |- _ => rewrite Hop end. reflexivity.
    + (* Binop Imm *)
      destruct (wReg1 r2 _) as [l n2] eqn:Ew2.
      destruct (load1 ac k f f' s t lens r2 l n2 _ (wRegWrite1 (fun n1 => Inst (Arith (Binop bop n1 n2 (Imm imm)))) r1 (k, (f, f')))
                  H Ew2 ltac:(assumption) ltac:(eassumption)) as (t1 & E1' & HS1 & G2 & _ & L1 & S1 & _).
      rewrite E1'.
      edestruct (write1 ac k f f' s t1 lens r1) as (t' & E' & H' & L' & S'); [exact HS1|assumption|lia| |wfin E' H'].
      intros n1. sinst. rewrite G2.
      rewrite (bd_false' (Imm imm = Reg n2)) by discriminate. rewrite andb_false_r.
      cbn [EVERY IS_SOME andb List.map THE]. match goal with Hop : wordLang.word_op _ _ = SOME _ |- _ => rewrite Hop end. reflexivity.
    + (* Shift Reg *)
      destruct (wReg1 r2 _) as [l n2] eqn:Ew2. destruct (wReg2 r3 _) as [l' n3] eqn:Ew3.
      destruct (load12 ac k f f' s t lens r2 r3 l l' n2 n3 _ _ (wRegWrite1 (fun n1 => Inst (Arith (asm.Shift sh n1 n2 (Reg n3)))) r1 (k, (f, f')))
                  H Ew2 ltac:(assumption) ltac:(eassumption) Ew3 ltac:(assumption) ltac:(eassumption)) as (t1 & E1' & HS1 & G2 & G3 & L1 & S1 & _).
      rewrite E1'.
      edestruct (write1 ac k f f' s t1 lens r1) as (t' & E' & H' & L' & S'); [exact HS1|assumption|lia| |wfin E' H'].
      intros n1. sinst. rewrite G2, G3. match goal with Hop : wordLang.word_sh _ _ _ = SOME _ |- _ => rewrite Hop end. reflexivity.
    + (* Shift Imm *)
      destruct (wReg1 r2 _) as [l n2] eqn:Ew2.
      destruct (load1 ac k f f' s t lens r2 l n2 _ (wRegWrite1 (fun n1 => Inst (Arith (asm.Shift sh n1 n2 (Imm imm)))) r1 (k, (f, f')))
                  H Ew2 ltac:(assumption) ltac:(eassumption)) as (t1 & E1' & HS1 & G2 & _ & L1 & S1 & _).
      rewrite E1'.
      edestruct (write1 ac k f f' s t1 lens r1) as (t' & E' & H' & L' & S'); [exact HS1|assumption|lia| |wfin E' H'].
      intros n1. sinst. rewrite G2. match goal with Hop : wordLang.word_sh _ _ _ = SOME _ |- _ => rewrite Hop end. reflexivity.
    + (* Div *)
      destruct (wReg1 r2 _) as [l n2] eqn:Ew2. destruct (wReg2 r3 _) as [l' n3] eqn:Ew3.
      destruct (load12 ac k f f' s t lens r2 r3 l l' n2 n3 _ _ (wRegWrite1 (fun n1 => Inst (Arith (Div n1 n2 n3))) r1 (k, (f, f')))
                  H Ew2 ltac:(assumption) ltac:(eassumption) Ew3 ltac:(assumption) ltac:(eassumption)) as (t1 & E1' & HS1 & G2 & G3 & L1 & S1 & _).
      rewrite E1'.
      edestruct (write1 ac k f f' s t1 lens r1) as (t' & E' & H' & L' & S'); [exact HS1|assumption|lia| |wfin E' H'].
      intros n1. sinst. rewrite G2, G3.
      match goal with Hb : negb (bool_decide (?q = n2w 0)) = true |- _ =>
        apply negb_true_iff, bdf in Hb; rewrite (bd_false' (q = n2w 0)) by exact Hb end.
      reflexivity.
    + (* LongMul *)
      subst r1 r2 r3 r4.
      assert (G0 : FLOOKUP (regs t) 0 = SOME (Word w)) by (eapply state_rel_get_var_imp; split; [exact H|]; split; [eassumption|lia]).
      assert (G2 : FLOOKUP (regs t) 2 = SOME (Word w0)) by (eapply state_rel_get_var_imp; split; [exact H|]; split; [eassumption|lia]).
      eexists; split; [sinst; rewrite G0, G2; reflexivity|].
      split; [|split; reflexivity].
      apply state_rel_set_var'. split; [|split; [lia|reflexivity]].
      apply state_rel_set_var'. split; [exact H|]. split; [lia|reflexivity].
    + (* LongDiv *)
      subst r1 r2 r3 r4.
      destruct (wReg1 r5 _) as [l n5] eqn:Ew5.
      destruct (load1 ac k f f' s t lens r5 l n5 _ (Inst (Arith (LongDiv 0 3 3 0 n5))) H Ew5 ltac:(assumption) ltac:(eassumption))
        as (t1 & E1' & HS1 & G5 & _ & L1 & S1 & R1).
      rewrite E1'.
      assert (G3 : FLOOKUP (regs t1) 3 = SOME (Word w)) by (eapply state_rel_get_var_imp; split; [exact HS1|]; split; [eassumption|lia]).
      assert (G0 : FLOOKUP (regs t1) 0 = SOME (Word w0)) by (eapply state_rel_get_var_imp; split; [exact HS1|]; split; [eassumption|lia]).
      eexists; split.
      { sinst. rewrite G3, G0, G5. match goal with Hb : _ && _ = true |- _ => rewrite Hb end. reflexivity. }
      split; [|split; [stk_fields; congruence|stk_fields; congruence]].
      apply state_rel_set_var'. split; [|split; [lia|reflexivity]].
      apply state_rel_set_var'. split; [exact HS1|]. split; [lia|reflexivity].
    + (* AddCarry *)
      subst r4.
      destruct (wReg1 r2 _) as [l n2] eqn:Ew2. destruct (wReg2 r3 _) as [l' n3] eqn:Ew3.
      destruct (load12 ac k f f' s t lens r2 r3 l l' n2 n3 _ _ (wRegWrite1 (fun n1 => Inst (Arith (AddCarry n1 n2 n3 0))) r1 (k, (f, f')))
                  H Ew2 ltac:(assumption) ltac:(eassumption) Ew3 ltac:(assumption) ltac:(eassumption)) as (t1 & E1' & HS1 & G2 & G3 & L1 & S1 & _).
      rewrite E1'.
      assert (G0 : FLOOKUP (regs t1) 0 = SOME (Word w1)) by (eapply state_rel_get_var_imp; split; [exact HS1|]; split; [eassumption|lia]).
      edestruct (write1_0 ac k f f' s t1 lens r1) as (t' & E' & H' & L' & S'); [exact HS1|assumption|lia| |wfin E' H'].
      intros n1. sinst. rewrite G2, G3, G0.
      match goal with Hc : word_add_carry _ _ _ = _ |- _ => unfold word_add_carry in Hc; injection Hc as <- <- end.
      destruct (decide (w1 = n2w 0)) as [Ez|Ez]; [rewrite (bd_true' (w1 = n2w 0)) by exact Ez|rewrite (bd_false' (w1 = n2w 0)) by exact Ez];
        reflexivity.
    + (* AddOverflow *)
      subst r4.
      destruct (wReg1 r2 _) as [l n2] eqn:Ew2. destruct (wReg2 r3 _) as [l' n3] eqn:Ew3.
      destruct (load12 ac k f f' s t lens r2 r3 l l' n2 n3 _ _ (wRegWrite1 (fun n1 => Inst (Arith (AddOverflow n1 n2 n3 0))) r1 (k, (f, f')))
                  H Ew2 ltac:(assumption) ltac:(eassumption) Ew3 ltac:(assumption) ltac:(eassumption)) as (t1 & E1' & HS1 & G2 & G3 & L1 & S1 & _).
      rewrite E1'.
      edestruct (write1_0 ac k f f' s t1 lens r1) as (t' & E' & H' & L' & S'); [exact HS1|assumption|lia| |wfin E' H'].
      intros n1. sinst. rewrite G2, G3, Zeqb_bool_decide. reflexivity.
    + (* SubOverflow *)
      subst r4.
      destruct (wReg1 r2 _) as [l n2] eqn:Ew2. destruct (wReg2 r3 _) as [l' n3] eqn:Ew3.
      destruct (load12 ac k f f' s t lens r2 r3 l l' n2 n3 _ _ (wRegWrite1 (fun n1 => Inst (Arith (SubOverflow n1 n2 n3 0))) r1 (k, (f, f')))
                  H Ew2 ltac:(assumption) ltac:(eassumption) Ew3 ltac:(assumption) ltac:(eassumption)) as (t1 & E1' & HS1 & G2 & G3 & L1 & S1 & _).
      rewrite E1'.
      edestruct (write1_0 ac k f f' s t1 lens r1) as (t' & E' & H' & L' & S'); [exact HS1|assumption|lia| |wfin E' H'].
      intros n1. sinst. rewrite G2, G3, Zeqb_bool_decide. reflexivity.
  - (* Mem *)
    destruct op; cbn [wordLang.every_var_inst wordLang.max_var_inst] in Hev, Hmax; winst_prep;
      cbn [wordSem.inst] in Hi; try discriminate Hi;
      cbn [wordSem.word_exp wordSem.get_vars List.map wordSem.the_words] in Hi;
      inv_hi Hi; try (injection Hi as <-); cbn [wInst].
    + (* Load *)
      destruct (wReg1 a0 _) as [l n2] eqn:Ew2.
      destruct (load1 ac k f f' s t lens a0 l n2 _ (wRegWrite1 (fun n1 => Inst (Mem asm.Load n1 (Addr n2 off))) r (k, (f, f')))
                  H Ew2 ltac:(assumption) ltac:(eassumption)) as (t1 & E1' & HS1 & G2 & _ & L1 & S1 & _).
      rewrite E1'.
      edestruct (write1 ac k f f' s t1 lens r) as (t' & E' & H' & L' & S'); [exact HS1|assumption|lia| |wfin E' H'].
      intros n1. sinst. rewrite G2. cbn [EVERY IS_SOME andb List.map THE].
      match goal with Hop : wordLang.word_op _ _ = SOME _ |- _ => rewrite Hop end.
      rewrite (state_rel_mem_load _ _ _ _ _ _ _ _ _ HS1). match goal with Hl : wordSem.mem_load _ _ = SOME _ |- _ => rewrite Hl end.
      reflexivity.
    + (* Load8 *)
      destruct (wReg1 a0 _) as [l n2] eqn:Ew2.
      destruct (load1 ac k f f' s t lens a0 l n2 _ (wRegWrite1 (fun n1 => Inst (Mem Load8 n1 (Addr n2 off))) r (k, (f, f')))
                  H Ew2 ltac:(assumption) ltac:(eassumption)) as (t1 & E1' & HS1 & G2 & _ & L1 & S1 & _).
      rewrite E1'.
      edestruct (write1 ac k f f' s t1 lens r) as (t' & E' & H' & L' & S'); [exact HS1|assumption|lia| |wfin E' H'].
      intros n1. sinst. rewrite G2. cbn [EVERY IS_SOME andb List.map THE].
      match goal with Hop : wordLang.word_op _ _ = SOME _ |- _ => rewrite Hop end.
      destruct (state_rel_mem_eqs _ _ _ _ _ _ _ _ HS1) as (-> & -> & ->).
      match goal with Hl : wordSem.mem_load_byte_aux _ _ _ _ = SOME _ |- _ => rewrite Hl end.
      reflexivity.
    + (* Load32 *)
      destruct (wReg1 a0 _) as [l n2] eqn:Ew2.
      destruct (load1 ac k f f' s t lens a0 l n2 _ (wRegWrite1 (fun n1 => Inst (Mem Load32 n1 (Addr n2 off))) r (k, (f, f')))
                  H Ew2 ltac:(assumption) ltac:(eassumption)) as (t1 & E1' & HS1 & G2 & _ & L1 & S1 & _).
      rewrite E1'.
      edestruct (write1 ac k f f' s t1 lens r) as (t' & E' & H' & L' & S'); [exact HS1|assumption|lia| |wfin E' H'].
      intros n1. sinst. rewrite G2. cbn [EVERY IS_SOME andb List.map THE].
      match goal with Hop : wordLang.word_op _ _ = SOME _ |- _ => rewrite Hop end.
      destruct (state_rel_mem_eqs _ _ _ _ _ _ _ _ HS1) as (-> & -> & ->).
      match goal with Hl : wordSem.mem_load_32 _ _ _ _ = SOME _ |- _ => rewrite Hl end.
      reflexivity.
    + (* Store *)
      destruct (wReg1 a0 _) as [l1 n2] eqn:Ew2. destruct (wReg2 r _) as [l2 n1] eqn:Ew1.
      destruct (load12 ac k f f' s t lens a0 r l1 l2 n2 n1 _ _ (Inst (Mem asm.Store n1 (Addr n2 off)))
                  H Ew2 ltac:(assumption) ltac:(eassumption) Ew1 ltac:(assumption) ltac:(eassumption)) as (t1 & E1' & HS1 & G2 & G1 & L1 & S1 & _).
      rewrite E1'.
      match goal with Hst : wordSem.mem_store _ _ _ = SOME _ |- _ =>
        destruct (state_rel_mem_store ac k f f' s t1 lens 0 _ _ _ (conj HS1 Hst)) as (t2 & Ht2 & HS2) end.
      exists t2. split.
      { sinst. rewrite G2, G1. cbn [EVERY IS_SOME andb List.map THE].
        match goal with Hop : wordLang.word_op _ _ = SOME _ |- _ => rewrite Hop end. rewrite Ht2. reflexivity. }
      split; [exact HS2|]. unfold stackSem.mem_store in Ht2. destruct (classical_dec _); [|discriminate].
      injection Ht2 as <-. stk_fields. split; congruence.
    + (* Store8 *)
      destruct (wReg1 a0 _) as [l1 n2] eqn:Ew2. destruct (wReg2 r _) as [l2 n1] eqn:Ew1.
      destruct (load12 ac k f f' s t lens a0 r l1 l2 n2 n1 _ _ (Inst (Mem Store8 n1 (Addr n2 off)))
                  H Ew2 ltac:(assumption) ltac:(eassumption) Ew1 ltac:(assumption) ltac:(eassumption)) as (t1 & E1' & HS1 & G2 & G1 & L1 & S1 & _).
      rewrite E1'. eexists. split.
      { sinst. rewrite G2, G1. cbn [EVERY IS_SOME andb List.map THE].
        match goal with Hop : wordLang.word_op _ _ = SOME _ |- _ => rewrite Hop end.
        destruct (state_rel_mem_eqs _ _ _ _ _ _ _ _ HS1) as (-> & -> & ->).
        match goal with Hl : wordSem.mem_store_byte_aux _ _ _ _ _ = SOME _ |- _ => rewrite Hl end. reflexivity. }
      split; [apply state_rel_with_memory, HS1|]. stk_fields. split; congruence.
    + (* Store32 *)
      destruct (wReg1 a0 _) as [l1 n2] eqn:Ew2. destruct (wReg2 r _) as [l2 n1] eqn:Ew1.
      destruct (load12 ac k f f' s t lens a0 r l1 l2 n2 n1 _ _ (Inst (Mem Store32 n1 (Addr n2 off)))
                  H Ew2 ltac:(assumption) ltac:(eassumption) Ew1 ltac:(assumption) ltac:(eassumption)) as (t1 & E1' & HS1 & G2 & G1 & L1 & S1 & _).
      rewrite E1'. eexists. split.
      { sinst. rewrite G2, G1. cbn [EVERY IS_SOME andb List.map THE].
        match goal with Hop : wordLang.word_op _ _ = SOME _ |- _ => rewrite Hop end.
        destruct (state_rel_mem_eqs _ _ _ _ _ _ _ _ HS1) as (-> & -> & ->).
        match goal with Hl : wordSem.mem_store_32 _ _ _ _ _ = SOME _ |- _ => rewrite Hl end. reflexivity. }
      split; [apply state_rel_with_memory, HS1|]. stk_fields. split; congruence.
  - (* FP *)
    destruct fop as [r d1 d2|r d1 d2|r d1 d2|d1 d2|d1 d2|d1 d2|d1 d2 d3|d1 d2 d3|d1 d2 d3|d1 d2 d3|d1 d2 d3|d1 d2|r1 r2 d|d r1 r2|d1 d2|d1 d2];
      cbn [wordLang.every_var_inst wordLang.max_var_inst] in Hev, Hmax;
      cbn [wordSem.inst] in Hi.
    1-3: winst_prep; inv_hi Hi; injection Hi as <-; cbn [wInst];
      (edestruct (write1 ac k f f' s t lens r) as (t' & E' & H' & L' & S'); [exact H|assumption|lia| |wfin E' H']);
      intros n1; cbv beta; fp_pure H; reflexivity.
    1-9: inv_hi Hi; injection Hi as <-; cbn [wInst];
      eexists; (split; [fp_pure H; reflexivity|]); (split; [apply state_rel_set_fp_var, H|split; reflexivity]).
    3-4: inv_hi Hi; injection Hi as <-; cbn [wInst];
      eexists; (split; [fp_pure H; reflexivity|]); (split; [apply state_rel_set_fp_var, H|split; reflexivity]).
    + (* FPMovToReg *)
      cbn [wInst]. destruct (dimindex a =? 64) eqn:Ed.
      * winst_prep. inv_hi Hi. injection Hi as <-.
        edestruct (write1 ac k f f' s t lens r1) as (t' & E' & H' & L' & S'); [exact H|assumption|lia| |wfin E' H'].
        intros n1; cbv beta; fp_pure H; reflexivity.
      * winst_prep. inv_hi Hi. injection Hi as <-.
        rename w into v.
        rewrite evaluate_wRegWrite2_seq. destruct (wReg2 r2 (k, (f, f'))) as [l2 n2] eqn:Ew2. cbv beta iota.
        assert (Hn2 : (n2 = k + 1 /\ l2 <> []) \/ (n2 < k /\ 2 * n2 = r2 /\ l2 = [])).
        { unfold wReg2 in Ew2. cbv zeta in Ew2. pose proof (even_div2 r2 ltac:(assumption)).
          destruct (r2 DIV 2 <? k) eqn:E2; to_prop; injection Ew2 as <- <-; [right|left]; repeat split; try lia; try discriminate; reflexivity. }
        edestruct (evaluate_wStackStore_wReg2_new ac k f f' r2 l2 n2 (wordSem.set_var r1 (Word ((31 >< 0) v)) s) t lens
                     (Word ((63 >< 32) v)) (wRegWrite1 (fun r0 => Inst (FP (FPMovToReg r0 n2 d))) r1 (k, (f, f')))
                     (LENGTH (stackSem.stack t)) (stack_space t)) as (t' & E' & H' & L' & S'); [|wfin E' H'].
        split; [exact Ew2|]. split; [assumption|]. split; [lia|].
        rewrite evaluate_wRegWrite1_seq. destruct (wReg1 r1 (k, (f, f'))) as [l1 n1] eqn:Ew1. cbv beta iota.
        rewrite ev_seq.
        assert (Ei : evaluate (Inst (FP (FPMovToReg n1 n2 d)), t) =
                     (NONE, stackSem.set_var n2 (Word ((63 >< 32) v)) (stackSem.set_var n1 (Word ((31 >< 0) v)) t)))
          by (fp_pure H; reflexivity).
        rewrite Ei. clear Ei.
        unfold wReg1 in Ew1. cbv zeta in Ew1. pose proof (even_div2 r1 ltac:(assumption)) as Er1.
        destruct (r1 DIV 2 <? k) eqn:E1; to_prop; injection Ew1 as <- <-.
        -- rewrite wStackStore_nil, ev_skip. eexists; split; [reflexivity|].
           split; [rewrite Er1 at 1; apply state_rel_set_var; split; [exact H|lia]|split; reflexivity].
        -- cbn [wStackStore]. rewrite ev_seq, ?wStackStore_nil, ev_skip.
           rewrite (set_var_swap n2 k) by lia.
           assert (H0' : exists s0, state_rel ac k f f' s0 (stackSem.set_var k (Word ((31 >< 0) v)) (stackSem.set_var n2 (Word ((63 >< 32) v)) t)) lens 0).
           { destruct Hn2 as [[-> _]|[Hn2 [Hr2 _]]].
             - exists s. apply state_rel_set_var_k. apply state_rel_set_var_k. exact H.
             - exists (wordSem.set_var (2 * n2) (Word ((63 >< 32) v)) s). apply state_rel_set_var_k.
               apply state_rel_set_var. split; [exact H|exact Hn2]. }
           destruct H0' as [s0 H0'].
           rewrite (ev_store_slot ac k f f' s0 _ lens (r1 DIV 2) (Word ((31 >< 0) v)) k H0')
             by (try lia; apply sget_var_set_var_eq).
           exists (set_stack (LUPDATE (Word ((31 >< 0) v)) (stack_space t + (f + k - (r1 DIV 2 + 1))) (stackSem.stack t))
                     (stackSem.set_var k (Word ((31 >< 0) v)) t)).
           split.
           { f_equal. stk_fields. rewrite !set_stack_set_var. rewrite (set_var_swap n2 k) by lia. reflexivity. }
           split; [|stk_fields; rewrite LENGTH_LUPDATE'; split; reflexivity].
           rewrite Er1 at 1.
           replace (LUPDATE (Word ((31 >< 0) v)) (stack_space t + (f + k - (r1 DIV 2 + 1))) (stackSem.stack t))
             with (LUPDATE (Word ((31 >< 0) v)) (stack_space (stackSem.set_var k (Word ((31 >< 0) v)) t) + (f + k - (r1 DIV 2 + 1)))
                     (stackSem.stack (stackSem.set_var k (Word ((31 >< 0) v)) t))) by reflexivity.
           apply state_rel_set_var2. split; [apply state_rel_set_var_k; exact H|]. split; [lia|]. split; [lia|]. split; reflexivity.
    + (* FPMovFromReg *)
      cbn [wInst]. destruct (wReg1 r1 (k, (f, f'))) as [l n1] eqn:Ew1.
      destruct (dimindex a =? 64) eqn:Ed.
      * winst_prep. inv_hi Hi. injection Hi as <-. cbv beta iota. rewrite app_nil_r.
        destruct (load1 ac k f f' s t lens r1 l n1 _ (Inst (FP (FPMovFromReg d n1 0))) H Ew1 ltac:(assumption) ltac:(eassumption))
          as (t1 & E1' & HS1 & G1 & _ & L1 & S1 & _).
        rewrite E1'. eexists; split.
        { rewrite ev_inst. unfold inst. rewrite Ed. unfold stackSem.get_var in G1 |- *. rewrite G1. reflexivity. }
        split; [apply state_rel_set_fp_var, HS1|]. stk_fields. split; congruence.
      * winst_prep. inv_hi Hi. injection Hi as <-.
        destruct (wReg2 r2 (k, (f, f'))) as [l' n2] eqn:Ew2. cbv beta iota.
        destruct (load12 ac k f f' s t lens r1 r2 l l' n1 n2 _ _ (Inst (FP (FPMovFromReg d n1 n2)))
                    H Ew1 ltac:(assumption) ltac:(eassumption) Ew2 ltac:(assumption) ltac:(eassumption)) as (t1 & E1' & HS1 & G1 & G2 & L1 & S1 & _).
        rewrite E1'. eexists; split.
        { rewrite ev_inst. unfold inst. rewrite (proj2 (N.eqb_neq _ _) Ed). unfold stackSem.get_var in G1, G2 |- *. rewrite G1, G2. reflexivity. }
        split; [apply state_rel_set_fp_var, HS1|]. stk_fields. split; congruence.
Qed.

End WInst.

(** ** Calls, stack moves and handlers (HOL lines 5132-5594) *)

(** Galette-only: lookups in [fromList2] (as in [loop_to_wordProof]). *)
Lemma fromList2_aux' {A} : forall (l : list A) i (t : num_map A) n,
  lookup n (snd (FOLDL (fun '(i, t) a0 => (i + 2, insert i a0 t)) (i, t) l)) =
  if decide (i <= n /\ N.even (n - i) = true /\ (n - i) / 2 < LENGTH l)
  then nth_error l (N.to_nat ((n - i) / 2)) else lookup n t.
Proof.
  induction l as [|x l IH]; intros i t n; cbn [FOLDL LENGTH].
  - destruct (decide _) as [(_ & _ & H)|]; [lia|reflexivity].
  - rewrite IH, lookup_insert.
    destruct (decide (i + 2 <= n /\ N.even (n - (i + 2)) = true /\ (n - (i + 2)) / 2 < LENGTH l))
      as [(H1 & H2 & H3)|Hn1];
    destruct (decide (i <= n /\ N.even (n - i) = true /\ (n - i) / 2 < N.succ (LENGTH l)))
      as [(G1 & G2 & G3)|Hn2].
    + replace ((n - i) / 2) with (N.succ ((n - (i + 2)) / 2)).
      * rewrite N2Nat.inj_succ; reflexivity.
      * replace (n - i) with ((n - (i + 2)) + 1 * 2) by lia. rewrite N.div_add by lia. lia.
    + exfalso; apply Hn2. split; [lia|]. split.
      * replace (n - i) with ((n - (i + 2)) + 2) by lia. rewrite N.even_add, H2; reflexivity.
      * replace (n - i) with ((n - (i + 2)) + 1 * 2) by lia. rewrite N.div_add by lia. lia.
    + destruct (decide (n = i)) as [->|Hne].
      * rewrite N.sub_diag; reflexivity.
      * exfalso; apply Hn1. split; [|split].
        -- destruct (N.lt_ge_cases n (i + 2)) as [Hl|Hl]; [|exact Hl].
           assert (n = i + 1) by lia. subst n. rewrite N.add_sub_swap, N.sub_diag in G2 by lia.
           discriminate.
        -- destruct (N.lt_ge_cases n (i + 2)) as [Hl|Hl].
           ++ assert (n = i + 1) by lia. subst n. rewrite N.add_sub_swap, N.sub_diag in G2 by lia.
              discriminate.
           ++ replace (n - i) with ((n - (i + 2)) + 2) in G2 by lia.
              rewrite N.even_add in G2. destruct (N.even (n - (i + 2))); [reflexivity|discriminate].
        -- destruct (N.lt_ge_cases n (i + 2)) as [Hl|Hl].
           ++ assert (n = i + 1) by lia. subst n. rewrite N.add_sub_swap, N.sub_diag in G2 by lia.
              discriminate.
           ++ replace (n - i) with ((n - (i + 2)) + 1 * 2) in G3 by lia.
              rewrite N.div_add in G3 by lia. lia.
    + destruct (decide (n = i)) as [->|Hne]; [|reflexivity].
      exfalso; apply Hn2. rewrite N.sub_diag. split; [lia|split; [reflexivity|]].
      rewrite N.Div0.div_0_l. lia.
Qed.

Lemma lookup_fromList2' {A} (l : list A) n :
  lookup n (fromList2 l) =
  if decide (N.even n = true /\ n / 2 < LENGTH l) then nth_error l (N.to_nat (n / 2)) else NONE.
Proof.
  unfold fromList2. rewrite fromList2_aux', N.sub_0_r.
  destruct (decide (0 <= n /\ _)) as [(_ & H1 & H2)|Hn];
    destruct (decide (N.even n = true /\ _)) as [[G1 G2]|Gn].
  - reflexivity.
  - exfalso; apply Gn; auto.
  - exfalso; apply Hn; split; [lia|]; auto.
  - reflexivity.
Qed.

Lemma get_vars_EL {a C F} (s : wordSem.state a C F) : forall ls z i,
  wordSem.get_vars ls s = SOME z -> (N.to_nat i < length ls)%nat ->
  exists v, nth_error z (N.to_nat i) = SOME v /\ lookup (EL i ls) (wordSem.locals s) = SOME v.
Proof.
  induction ls as [|x ls IH]; intros z i H Hi; [cbn in Hi; lia|]. cbn [wordSem.get_vars] in H.
  unfold wordSem.get_var in H. destruct (lookup x (wordSem.locals s)) as [v|] eqn:Ex; [|discriminate].
  destruct (wordSem.get_vars ls s) as [zs|] eqn:Ezs; [|discriminate]. injection H as <-.
  rewrite EL_nth'. destruct (N.to_nat i) as [|j] eqn:Ei.
  - exists v. split; [reflexivity|exact Ex].
  - destruct (IH zs (N.of_nat j) eq_refl) as (w & H1 & H2); [cbn in Hi; lia|].
    rewrite Nat2N.id in H1. rewrite EL_nth', Nat2N.id in H2. exists w. split; [exact H1|exact H2].
Qed.

Section Calls.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_set_store" *)
Theorem state_rel_set_store : forall ac k f f' s t lens extra v x,
  state_rel ac k f f' s t lens extra /\ v <> Handler ->
  state_rel ac k f f' (wordSem.set_store v x s) (stackSem.set_store v x t) lens extra.
Proof.
  intros ac k f f' s t lens extra v x [H Hv]. sr_destr H. unfold wordSem.set_store, stackSem.set_store.
  sr_split; ws_fields; stk_fields; try assumption.
  - rewrite Hstore. apply fmap_ext. intros y. rewrite FLOOKUP_UPDATE, !DOMSUB_FLOOKUP_THM, FLOOKUP_UPDATE.
    destruct (decide (v = y)) as [<-|]; destruct (decide (Handler = v)); try congruence; reflexivity.
  - rewrite FDOM_FUPDATE. right; exact HH.
  - rewrite FLOOKUP_UPDATE. destruct (decide (v = Handler)); [congruence|exact Hsr].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "get_vars_fromList2_eq" *)
Theorem get_vars_fromList2_eq : forall {A C F} (args : list A) (s : wordSem.state a C F) x n y,
  wordSem.get_vars (GENLIST (fun x => 2 * x) (LENGTH args)) s = SOME x /\
  lookup n (fromList2 x) = SOME y ->
  lookup n (wordSem.locals s) = SOME y.
Proof.
  intros A C F args s x n y [Hg Hl]. rewrite lookup_fromList2' in Hl.
  destruct (decide _) as [(He & Hn)|]; [|discriminate].
  pose proof (dec_clock.get_vars_length_lemma _ _ _ Hg) as HL. rewrite LENGTH_GENLIST_N in HL.
  destruct (get_vars_EL s _ _ (n / 2) Hg) as (v & H1 & H2).
  { pose proof (LENGTH_GENLIST_N (fun x => 2 * x) (LENGTH args)) as G. rewrite LENGTH_length in G. lia. }
  rewrite Hl in H1. injection H1 as <-. rewrite EL_GENLIST_N in H2 by lia.
  rewrite (even_div2 n He). exact H2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "get_vars_fromList2_eq_cons" *)
Theorem get_vars_fromList2_eq_cons : forall {A C F} (args : list A) (s : wordSem.state a C F) x n y x3 x4,
  wordSem.get_vars (GENLIST (fun x => 2 * (x + 1)) (LENGTH args)) s = SOME x /\
  lookup n (fromList2 (Loc x3 x4 :: x)) = SOME y /\ n <> 0 ->
  lookup n (wordSem.locals s) = SOME y.
Proof.
  intros A C F args s x n y x3 x4 (Hg & Hl & Hn0). rewrite lookup_fromList2' in Hl.
  destruct (decide _) as [(He & Hn)|]; [|discriminate].
  pose proof (dec_clock.get_vars_length_lemma _ _ _ Hg) as HL. rewrite LENGTH_GENLIST_N in HL.
  pose proof (even_div2 n He) as En. rewrite LENGTH_cons' in Hn.
  assert (H1 : 1 <= n / 2) by lia.
  replace (N.to_nat (n / 2)) with (Datatypes.S (N.to_nat (n / 2 - 1))) in Hl by lia. cbn [nth_error] in Hl.
  destruct (get_vars_EL s _ _ (n / 2 - 1) Hg) as (v & G1 & G2).
  { pose proof (LENGTH_GENLIST_N (fun x => 2 * (x + 1)) (LENGTH args)) as G. rewrite LENGTH_length in G. lia. }
  rewrite Hl in G1. injection G1 as <-. rewrite EL_GENLIST_N in G2 by lia.
  replace (2 * (n / 2 - 1 + 1)) with n in G2 by lia. exact G2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "lookup_fromList2_prefix" *)
Theorem lookup_fromList2_prefix : forall {A} `{EqDecision A} n (x z : list A) y,
  isPREFIX x z /\ lookup n (fromList2 x) = SOME y ->
  lookup n (fromList2 z) = SOME y.
Proof.
  intros A HA n x z y [Hp Hl]. apply isPREFIX_iff in Hp as [l ->]. rewrite lookup_fromList2' in Hl |- *.
  destruct (decide _) as [(He & Hn)|]; [|discriminate].
  rewrite decide_True by (split; [exact He|rewrite LENGTH_app'; lia]).
  rewrite nth_error_app1; [exact Hl|rewrite LENGTH_length in Hn; lia].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_call_dest_clock" *)
Theorem evaluate_call_dest_clock : forall dest args k f f' q0 dest' t clk,
  call_dest dest args (k, (f, f')) = (q0, dest') ->
  evaluate (q0, set_clock clk t) = (I ## (fun t => set_clock clk t)) (evaluate (q0, t)).
Proof.
  intros dest args k f f' q0 dest' t clk H. destruct dest as [pos|]; cbn [call_dest] in H.
  - injection H as <- <-. rewrite !ev_skip. reflexivity.
  - destruct (LENGTH args =? 0); [injection H as <- <-; rewrite !ev_skip; reflexivity|].
    destruct (wReg2 (LAST args) (k, (f, f'))) as [x1 r]. injection H as <- <-.
    apply evaluate_wStackLoad_clock.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wLive_clock" *)
Theorem evaluate_wLive_clock : forall kf clk x t q bs bs',
  wLive x bs kf = (q, bs') ->
  evaluate (q, set_clock clk t) = (FST (evaluate (q, t)), set_clock clk (SND (evaluate (q, t)))).
Proof.
  intros [k [f f']] clk x t q bs bs' H. unfold wLive in H.
  destruct (f =? 0); [injection H as <- <-; rewrite !ev_skip; reflexivity|].
  destruct (insert_bitmap _ bs) as [nb i]. injection H as <- <-.
  rewrite !ev_seq, !ev_inst, !inst_const, !ev_stackstore. unfold stackSem.get_var, stackSem.set_var.
  destruct t; stk_fields. destruct use_stack; cbn [negb]; [|reflexivity].
  destruct (_ <=? _); [reflexivity|]. rewrite !FLOOKUP_UPDATE. destruct (decide (k = k)); [|congruence]. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_IMP_LENGTH" *)
Theorem state_rel_IMP_LENGTH : forall ac k f f' s t lens extra,
  state_rel ac k f f' s t lens extra -> LENGTH lens = LENGTH (wordSem.stack s).
Proof.
  intros ac k f f' s t lens extra H. sr_destr H. destruct Hsr as (_ & stack & Habs & _).
  apply abs_stack_IMP_LENGTH in Habs. lia.
Qed.

End Calls.

Lemma EL_LUPDATE_eq' {A} `{Inhabited A} (v : A) i l : i < LENGTH l -> EL i (LUPDATE v i l) = v.
Proof.
  intros H0. apply oEL_SOME_EL. apply oEL_LUPDATE_eq, H0.
Qed.

Lemma EL_LUPDATE_neq' {A} `{Inhabited A} (v : A) i j l : j <> i -> EL j (LUPDATE v i l) = EL j l.
Proof.
  intros Hne. rewrite !EL_nth'. revert i j Hne; induction l as [|y l IH]; intros i j Hne; [rewrite LUPDATE_nil; reflexivity|].
  rewrite LUPDATE_cons_eq. destruct (N.eqb_spec i 0) as [->|Hi].
  - destruct (N.to_nat j) eqn:Ej; [lia|reflexivity].
  - destruct (N.to_nat j) as [|j'] eqn:Ej; [reflexivity|]. cbn [nth].
    pose proof (IH (i - 1) (N.of_nat j') ltac:(lia)) as G. rewrite Nat2N.id in G. exact G.
Qed.

Lemma EL_LUPDATE_if {A} `{Inhabited A} (v : A) i j l :
  i < LENGTH l -> EL j (LUPDATE v i l) = if decide (j = i) then v else EL j l.
Proof.
  intros Hi. destruct (decide (j = i)) as [->|Hne]; [apply EL_LUPDATE_eq', Hi|apply EL_LUPDATE_neq', Hne].
Qed.

Lemma EL_DROP_eq {A} `{Inhabited A} m (l1 l2 : list A) j :
  DROP m l1 = DROP m l2 -> m <= j -> EL j l1 = EL j l2.
Proof.
  intros E Hj. replace j with (m + (j - m)) by lia. rewrite <- !EL_DROP_add, E. reflexivity.
Qed.

Lemma ev_seq_assoc {a c ffi_t} (p q r : prog a) (t : stackSem.state a c ffi_t) :
  evaluate (Seq (Seq p q) r, t) = evaluate (Seq p (Seq q r), t).
Proof.
  rewrite !ev_seq. destruct (evaluate (p, t)) as [[res|] t1]; [reflexivity|].
  rewrite ev_seq. reflexivity.
Qed.

Section StackMove.
Context {a : N} {c ffi_t : Type}.
Implicit Types (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_stack_move" *)
Theorem evaluate_stack_move : forall k n tar t offset,
  use_stack t /\
  stack_space t + tar + n + offset <= LENGTH (stackSem.stack t) /\
  n <= offset ->
  exists t',
    evaluate (stack_move n tar offset k Skip, t) = (NONE, t') /\
    exists t'_stack t'_regs,
      t' = set_regs t'_regs (set_stack t'_stack t) /\
      (forall i, i <> k -> stackSem.get_var i t' = stackSem.get_var i t) /\
      LENGTH (stackSem.stack t) = LENGTH t'_stack /\
      stack_space t' = stack_space t /\
      DROP (stack_space t' + tar + n) t'_stack = DROP (stack_space t + tar + n) (stackSem.stack t) /\
      let stack' := DROP (stack_space t' + tar) t'_stack in
      let stack := DROP (stack_space t + tar) (stackSem.stack t) in
      forall x, x < n -> EL (x + offset) stack = EL x stack'.
Proof.
  intros k n. induction n as [|n IH] using N.peano_ind; intros tar t offset (Hu & Hl & Hn).
  - exists t. split; [rewrite (proj1 (stack_move_def 0 tar offset k Skip)); apply ev_skip|].
    exists (stackSem.stack t), (regs t). split; [destruct t; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    cbv zeta. intros x Hx. lia.
  - rewrite (proj2 (stack_move_def n tar offset k Skip)). rewrite ev_seq.
    destruct (IH (tar + 1) t offset) as (t1 & E1 & S1 & R1 & -> & HR1 & HL1 & HS1 & HD1 & HE1); [split; [exact Hu|]; split; lia|].
    rewrite E1. cbv zeta in HE1. stk_fields.
    set (v := EL (stack_space t + (tar + offset)) S1).
    assert (Hv : v = EL (stack_space t + (tar + offset)) (stackSem.stack t)).
    { unfold v. apply (EL_DROP_eq (stack_space t + (tar + 1) + n)); [exact HD1|lia]. }
    rewrite ev_seq, ev_stackload. stk_fields. unfold is_true in Hu. rewrite Hu. cbn [negb].
    rewrite (proj2 (N.ltb_lt _ _)) by lia. fold v.
    rewrite ev_stackstore. unfold stackSem.set_var. stk_fields. rewrite Hu. cbn [negb].
    rewrite (proj2 (N.leb_gt _ _)) by lia. unfold stackSem.get_var. stk_fields.
    rewrite FLOOKUP_UPDATE. rewrite decide_True by reflexivity.
    eexists; split; [reflexivity|].
    exists (LUPDATE v (stack_space t + tar) S1), (R1 |+ (k, v)).
    split; [destruct t; reflexivity|]. stk_fields.
    split.
    { intros i Hi. unfold stackSem.get_var. stk_fields. rewrite FLOOKUP_UPDATE.
      rewrite decide_False by congruence. specialize (HR1 i Hi). unfold stackSem.get_var in HR1. stk_fields. exact HR1. }
    split; [rewrite LENGTH_LUPDATE'; exact HL1|]. split; [reflexivity|].
    split.
    { rewrite DROP_LUPDATE_lt by lia. replace (stack_space t + tar + N.succ n) with (stack_space t + (tar + 1) + n) by lia. exact HD1. }
    cbv zeta. intros x Hx. rewrite !EL_DROP_add.
    destruct (N.eq_dec x 0) as [->|Hx0].
    + rewrite N.add_0_r, EL_LUPDATE_eq' by lia. rewrite Hv. f_equal. lia.
    + rewrite EL_LUPDATE_neq' by lia.
      specialize (HE1 (x - 1) ltac:(lia)). rewrite !EL_DROP_add in HE1.
      replace (stack_space t + tar + (x + offset)) with (stack_space t + (tar + 1) + (x - 1 + offset)) by lia.
      rewrite HE1. f_equal. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_stack_move_seq" *)
Theorem evaluate_stack_move_seq : forall a0 b c0 d (prog0 : prog a) t,
  evaluate (stack_move a0 b c0 d prog0, t) = evaluate (Seq prog0 (stack_move a0 b c0 d Skip), t).
Proof.
  intros a0. induction a0 as [|a0 IH] using N.peano_ind; intros b c0 d prog0 t.
  - rewrite !(proj1 (stack_move_def 0 b c0 d _)). rewrite ev_seq. destruct (evaluate (prog0, t)) as [[r|] t1]; [reflexivity|].
    rewrite ev_skip. reflexivity.
  - rewrite !(proj2 (stack_move_def a0 b c0 d _)). rewrite ev_seq, IH, <- ev_seq, ev_seq_assoc. reflexivity.
Qed.

(** HOL's ML binding [evaluate_stack_move_clock] (not a stored theorem;
    Galette-only). *)
Lemma evaluate_stack_move_clock clk : forall a0 b c0 d t,
  evaluate (stack_move a0 b c0 d Skip, set_clock clk t) =
  (FST (evaluate (stack_move a0 b c0 d Skip, t)), set_clock clk (SND (evaluate (stack_move a0 b c0 d Skip, t)))).
Proof.
  intros a0. induction a0 as [|a0 IH] using N.peano_ind; intros b c0 d t.
  - rewrite !(proj1 (stack_move_def 0 b c0 d _)), !ev_skip. reflexivity.
  - rewrite !(proj2 (stack_move_def a0 b c0 d _)), !ev_seq, IH.
    destruct (evaluate (stack_move a0 (b + 1) c0 d Skip, t)) as [[r|] t1]; cbn [FST SND fst snd]; [reflexivity|].
    rewrite !ev_seq, !ev_stackload. unfold stackSem.set_var, stackSem.get_var.
    stk_fields. destruct (use_stack t1) eqn:Eu; cbn [negb]; [|destruct t1; reflexivity].
    destruct (_ <? _); [|destruct t1; reflexivity]. rewrite !ev_stackstore. stk_fields. rewrite Eu. cbn [negb].
    destruct (_ <=? _); [destruct t1; reflexivity|]. unfold stackSem.get_var. stk_fields.
    rewrite !FLOOKUP_UPDATE, decide_True by reflexivity. destruct t1; reflexivity.
Qed.

End StackMove.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "pop_env_ffi" *)
Theorem pop_env_ffi : forall {a C F} (s s' : wordSem.state a C F),
  wordSem.pop_env s = SOME s' -> wordSem.ffi s = wordSem.ffi s'.
Proof.
  intros a C F s s' H. unfold wordSem.pop_env in H.
  destruct (wordSem.stack s) as [|[m e0 e [[n ?]|]] xs]; try discriminate; injection H as <-; reflexivity.
Qed.

Section StackRelDrop.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_DROP_NONE" *)
Theorem stack_rel_DROP_NONE : forall k whandler n l0 l (wstack : list (stack_frame a)) shandler sstack len bs f' lens,
  stack_rel k whandler (StackFrame n l0 l NONE :: wstack) shandler sstack len bs (f' :: lens) ->
  stack_rel k whandler wstack shandler (DROP (f' + 1) sstack) len bs lens.
Proof.
  intros k wh n l0 l wstack sh sstack len bs f' lens (Hs & stack & Habs & Hh & Hr).
  cbn [EVERY] in Hs. apply andb_prop in Hs as [_ Hs].
  apply abs_stack_NONE_inv in Habs as (w & st & len' & lens' & bits & ys & -> & E & _ & _ & Hl & Hy & ->).
  injection E as <- <-. cbn [stack_rel_aux] in Hr. destruct Hr as (_ & _ & _ & Hr).
  pose proof (abs_stack_IMP_LENGTH _ _ _ _ _ Hy) as [Ey _].
  split; [exact Hs|]. exists ys. split.
  { rewrite DROP_skipn, N2Nat.inj_add. replace (N.to_nat f' + N.to_nat 1)%nat with (Datatypes.S (N.to_nat f')) by lia.
    cbn [skipn]. rewrite <- DROP_skipn. exact Hy. }
  split; [|exact Hr].
  intros [H1 H2]. rewrite LASTN_cons_lt in Hh by lia. apply Hh. split; [rewrite LENGTH_cons'; lia|].
  rewrite LENGTH_cons'. replace (LENGTH wstack + 1 - (wh + 1)) with (LENGTH wstack - (wh + 1) + 1) by lia.
  rewrite EL_nth' in H2 |- *. replace (N.to_nat (LENGTH wstack - (wh + 1) + 1)) with (Datatypes.S (N.to_nat (LENGTH wstack - (wh + 1)))) by lia.
  exact H2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_DROP_SOME" *)
Theorem stack_rel_DROP_SOME : forall k whandler n l0 l whandler' b c0 (wstack : list (stack_frame a)) shandler sstack len bs f' lens,
  stack_rel k whandler (StackFrame n l0 l (SOME (whandler', (b, c0))) :: wstack) shandler sstack len bs (f' :: lens) ->
  stack_rel k whandler' wstack (SOME (EL 2 sstack)) (DROP (f' + 4) sstack) len bs lens.
Proof.
  intros k wh n l0 l wh' b c0 wstack sh sstack len bs f' lens (Hs & stack & Habs & Hh & Hr).
  cbn [EVERY] in Hs. apply andb_prop in Hs as [_ Hs].
  apply abs_stack_SOME_inv in Habs as (loc & hv & w & st & len' & lens' & bits & ys & -> & E & _ & _ & Hl & Hy & ->).
  injection E as <- <-. cbn [stack_rel_aux] in Hr. destruct Hr as (Hhv & _ & _ & _ & _ & Hr).
  pose proof (abs_stack_IMP_LENGTH _ _ _ _ _ Hy) as [Ey _].
  split; [exact Hs|]. exists ys. split.
  { rewrite DROP_skipn, N2Nat.inj_add. replace (N.to_nat f' + N.to_nat 4)%nat with (N.to_nat f' + 4)%nat by lia.
    rewrite <- skipn_skipn. cbn [skipn]. rewrite <- DROP_skipn. exact Hy. }
  split; [|exact Hr].
  intros [H1 H2]. rewrite EL_nth'. cbn [nth N.to_nat Pos.to_nat Pos.iter_op Nat.add]. f_equal. apply Hhv.
  rewrite Ey. split; assumption.
Qed.

End StackRelDrop.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LAST_GENLIST_evens" *)
Theorem LAST_GENLIST_evens : forall n,
  n <> 0 ->
  let reg := LAST (GENLIST (fun x => 2 * (x + 1)) n) in
  reg <> 0 /\ EVEN reg.
Proof.
  intros n Hn. cbv zeta.
  replace n with (SUC (N.pred n)) by lia. rewrite (proj2 (GENLIST_thm _ _)), SNOC_app.
  assert (L : forall {A} `{Inhabited A} (l : list A) (x : A), LAST (l ++ [x]) = x).
  { intros A HA l0 x. induction l0 as [|y l0 IH]; [reflexivity|]. cbn [app LAST]. rewrite IH.
    destruct l0; reflexivity. }
  rewrite L. split; [lia|]. apply N.even_spec. exists (N.pred n + 1). lia.
Qed.

Section StackRelCons.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_cons_LEN_NONE" *)
Theorem stack_rel_cons_LEN_NONE : forall k whandler n l0 l (wstack : list (stack_frame a)) shandler sstack len bs f' lens,
  stack_rel k whandler (StackFrame n l0 l NONE :: wstack) shandler sstack len bs (f' :: lens) ->
  f' + 1 <= LENGTH sstack.
Proof.
  intros k wh n l0 l wstack sh sstack len bs f' lens (_ & stack & Habs & _).
  apply abs_stack_NONE_inv in Habs as (w & st & len' & lens' & bits & ys & -> & E & _ & _ & Hl & _).
  injection E as <- <-. rewrite LENGTH_cons'. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_cons_LEN_SOME" *)
Theorem stack_rel_cons_LEN_SOME : forall k whandler n l0 l a0 b c0 (wstack : list (stack_frame a)) shandler sstack len bs f' lens,
  stack_rel k whandler (StackFrame n l0 l (SOME (a0, (b, c0))) :: wstack) shandler sstack len bs (f' :: lens) ->
  f' + 4 <= LENGTH sstack.
Proof.
  intros k wh n l0 l a0 b c0 wstack sh sstack len bs f' lens (_ & stack & Habs & _).
  apply abs_stack_SOME_inv in Habs as (loc & hv & w & st & len' & lens' & bits & ys & -> & E & _ & _ & Hl & _).
  injection E as <- <-. rewrite !LENGTH_cons'. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_cons_locals_size" *)
Theorem stack_rel_cons_locals_size : forall k whandler n l0 l opt (t'' : list (stack_frame a)) shandler rest_of_stack len bitmaps0 f' lens,
  stack_rel k whandler (StackFrame n l0 l opt :: t'') shandler rest_of_stack len bitmaps0 (f' :: lens) ->
  the (f' + 1) n = f' + 1.
Proof.
  intros k wh n l0 l [[h1 [l1 l2]]|] t'' sh rest len bm f' lens (_ & stack & Habs & _ & Hr).
  - apply abs_stack_SOME_inv in Habs as (loc & hv & w & st & len' & lens' & bits & ys & -> & E & _ & HLb & Hl & _ & ->).
    injection E as <- <-. cbn [stack_rel_aux] in Hr. destruct Hr as (_ & _ & _ & _ & Hthe & _).
    rewrite LENGTH_TAKE_le in Hthe by exact Hl. exact Hthe.
  - apply abs_stack_NONE_inv in Habs as (w & st & len' & lens' & bits & ys & -> & E & _ & HLb & Hl & _ & ->).
    injection E as <- <-. cbn [stack_rel_aux] in Hr. destruct Hr as (_ & _ & Hthe & _).
    rewrite LENGTH_TAKE_le in Hthe by exact Hl. exact Hthe.
Qed.

End StackRelCons.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "IS_SOME_OPTION_MAP2_EQ" *)
Theorem IS_SOME_OPTION_MAP2_EQ : forall {A B C} `{Inhabited A} `{Inhabited B} (f : A -> B -> C) x y,
  IS_SOME (OPTION_MAP2 f x y) = IS_SOME x && IS_SOME y.
Proof. intros A B C HA HB f [x|] [y|]; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DROP_SUB" *)
Theorem DROP_SUB : forall {A} (ls : list A) a0 b,
  a0 <= LENGTH ls /\ b <= a0 ->
  DROP (a0 - b) ls = DROP (a0 - b) (TAKE a0 ls) ++ DROP a0 ls.
Proof.
  intros A ls a0 b [H1 H2]. rewrite !DROP_skipn, TAKE_firstn.
  rewrite <- (firstn_skipn (N.to_nat a0) ls) at 1. rewrite skipn_app.
  rewrite length_firstn. rewrite LENGTH_length in H1.
  replace (N.to_nat (a0 - b) - Nat.min (N.to_nat a0) (length ls))%nat with 0%nat by lia. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DROP_SUB2" *)
Theorem DROP_SUB2 : forall {A} a0 (ls : list A) b,
  b <= a0 /\ a0 = LENGTH ls -> exists rest, DROP (a0 - b) ls = rest /\ LENGTH rest = b.
Proof.
  intros A a0 ls b [H1 ->]. eexists; split; [reflexivity|]. rewrite LENGTH_DROP'. lia.
Qed.

(** Galette-only: more stackLang evaluation equations. *)
Section EvalEqs2.
Context {a : N} {c ffi_t : Type}.
Implicit Types X : stackSem.state a c ffi_t.

Lemma ev_locvalue r l1 l2 X :
  evaluate (LocValue r l1 l2, X) =
  if classical_dec (loc_check (code X) (l1, l2)) then (NONE, stackSem.set_var r (Loc l1 l2) X) else (SOME Error, X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_get r name X :
  evaluate (Get r name, X) =
  if negb (use_store X) then (SOME Error, X) else
  match FLOOKUP (store X) name with SOME x => (NONE, stackSem.set_var r x X) | NONE => (SOME Error, X) end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_set name r X :
  evaluate (Set_ name r, X) =
  if negb (use_store X) then (SOME Error, X) else
  match stackSem.get_var r X with SOME w => (NONE, stackSem.set_store name w X) | NONE => (SOME Error, X) end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_stackgetsize r X :
  evaluate (StackGetSize r, X) =
  if negb (use_stack X) then (SOME Error, X) else (NONE, stackSem.set_var r (Word (n2w (stack_space X))) X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

End EvalEqs2.

Lemma om2_some {A B C} `{Inhabited A} `{Inhabited B} (f : A -> B -> C) x y : OPTION_MAP2 f (SOME x) (SOME y) = SOME (f x y).
Proof. reflexivity. Qed.
Lemma some_inj {A} (x y : A) : SOME x = SOME y -> x = y.
Proof. congruence. Qed.
Lemma om_some {A B} (f : A -> B) x : OPTION_MAP f (SOME x) = SOME (f x).
Proof. reflexivity. Qed.

Section PushHandler.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_PushHandler" *)
Theorem evaluate_PushHandler : forall ac k f f' s t lens x' x0 x1 l1 l2,
  3 <= stack_space t /\
  state_rel ac k 0 0 (wordSem.set_locals_size (SOME 0) (wordSem.set_locals LN (wordSem.push_env x' NONE s))) t (f' :: lens) 0 /\
  loc_check (code t) (l1, l2) ->
  exists t' : stackSem.state a c ffi_t,
    evaluate (PushHandler false l1 l2 (k, (f, f')), t) = (NONE, t') /\
    t' = set_store_fld (store t') (set_stack (stackSem.stack t') (set_regs (regs t') (set_stack_space (stack_space t') t))) /\
    (forall n, n < LENGTH (stackSem.stack t) - stack_space t ->
       EL n (DROP (stack_space t) (stackSem.stack t)) = EL (n + 3) (DROP (stack_space t') (stackSem.stack t'))) /\
    (forall i, i <> k -> stackSem.get_var i t' = stackSem.get_var i t) /\
    stack_space t' + 3 = stack_space t /\
    LENGTH (stackSem.stack t') = LENGTH (stackSem.stack t) /\
    state_rel ac k 0 0 (wordSem.set_locals_size (SOME 0) (wordSem.set_locals LN (wordSem.push_env x' (SOME (x0, (x1, (l1, l2)))) s))) t' (f' :: lens) 0.
Proof.
  intros ac k f f' s t lens x' x0 x1 l1 l2 (Hsp3 & H & Hlc).
  pose proof H as H0. sr_destr H0.
  assert (Hh : exists h, FLOOKUP (store t) Handler = SOME h).
  { rewrite FLOOKUP_DEF. destruct (decide _) as [_|C]; [eexists; reflexivity|contradiction]. }
  destruct Hh as [h Hh].
  unfold is_true in Hus, Hust.
  rewrite PushHandler_F.
  rewrite ev_seq, ev_stackalloc, Hus. cbn [negb]. rewrite (proj2 (N.ltb_ge _ _)) by lia.
  rewrite ev_seq, ev_inst, inst_const.
  rewrite ev_seq, ev_stackstore. unfold stackSem.set_var, stackSem.get_var. stk_fields. rewrite Hus. cbn [negb].
  rewrite (proj2 (N.leb_gt _ _)) by lia. rewrite FLOOKUP_UPDATE, decide_True by reflexivity.
  rewrite ev_seq, ev_locvalue. stk_fields. destruct (classical_dec _) as [_|C]; [|contradiction].
  rewrite ev_seq, ev_stackstore. unfold stackSem.set_var, stackSem.get_var. stk_fields. rewrite Hus. cbn [negb].
  rewrite LENGTH_LUPDATE'. rewrite (proj2 (N.leb_gt _ _)) by lia. rewrite FLOOKUP_UPDATE, decide_True by reflexivity.
  rewrite ev_seq, ev_get. stk_fields. rewrite Hust. cbn [negb]. rewrite Hh.
  rewrite ev_seq, ev_stackstore. unfold stackSem.set_var, stackSem.get_var. stk_fields. rewrite Hus. cbn [negb].
  rewrite !LENGTH_LUPDATE'. rewrite (proj2 (N.leb_gt _ _)) by lia. rewrite FLOOKUP_UPDATE, decide_True by reflexivity.
  rewrite ev_seq, ev_skip.
  rewrite ev_seq, ev_stackgetsize. stk_fields. rewrite Hus. cbn [negb].
  rewrite ev_set. unfold stackSem.set_var, stackSem.get_var. stk_fields. rewrite Hust. cbn [negb].
  rewrite FLOOKUP_UPDATE, decide_True by reflexivity.
  eexists; split; [reflexivity|].
  split; [destruct t; reflexivity|].
  unfold stackSem.set_store. stk_fields.
  split.
  { intros n Hn. rewrite !EL_DROP_add. rewrite !EL_LUPDATE_neq' by lia. f_equal. lia. }
  split.
  { intros i Hi. unfold stackSem.get_var. stk_fields. rewrite !FLOOKUP_UPDATE. rewrite !decide_False by congruence. reflexivity. }
  split; [lia|]. split; [rewrite !LENGTH_LUPDATE'; reflexivity|].
  unfold wordSem.push_env in *. cbv zeta in *.
  destruct (wordSem.env_to_list (SND x') (wordSem.permute s)) as [l perm] eqn:Eenv.
  ws_fields. clear H.
  set (sp := stack_space t) in *.
  set (S' := LUPDATE h (sp - 3 + 2) (LUPDATE (Loc l1 l2) (sp - 3 + 1) (LUPDATE (Word (n2w 1)) (sp - 3 + 0) (stackSem.stack t)))).
  assert (HL' : LENGTH S' = LENGTH (stackSem.stack t)) by (unfold S'; rewrite !LENGTH_LUPDATE'; reflexivity).
  assert (HD : DROP (sp - 3) S' = Word (n2w 1) :: Loc l1 l2 :: h :: DROP sp (stackSem.stack t)).
  { rewrite (DROP_EL_cons (sp - 3)) by lia. rewrite (DROP_EL_cons (sp - 3 + 1)) by lia.
    rewrite (DROP_EL_cons (sp - 3 + 1 + 1)) by lia.
    unfold S'. rewrite !EL_LUPDATE_if by (rewrite ?LENGTH_LUPDATE'; lia).
    repeat (first [rewrite decide_True by lia | rewrite decide_False by lia]).
    rewrite !DROP_LUPDATE_lt by lia. replace (sp - 3 + 1 + 1 + 1) with sp by lia. reflexivity. }
  sr_split; ws_fields; stk_fields; rewrite ?HL'; try assumption.
  - rewrite Hstore, DOMSUB_FUPDATE. reflexivity.
  - rewrite FDOM_FUPDATE. apply IN_INSERT. left; reflexivity.
  - lia.
  - unfold stack_size_rel in *. rewrite HL'. destruct Hssr as (_ & Hl & Hm). split; [intros C; lia|]. split; [exact Hl|].
    intros sm Hsm.
    change (wordSem.stack_size (StackFrame (wordSem.locals_size s) (toAList (FST x')) l NONE :: wordSem.stack s))
      with (OPTION_MAP2 N.add (wordSem.locals_size s) (wordSem.stack_size (wordSem.stack s))) in Hm.
    change (wordSem.stack_size (StackFrame (wordSem.locals_size s) (toAList (FST x')) l (SOME (wordSem.handler s, (l1, l2))) :: wordSem.stack s))
      with (OPTION_MAP2 N.add (OPTION_MAP (N.add 3) (wordSem.locals_size s)) (wordSem.stack_size (wordSem.stack s))) in Hsm |- *.
    destruct (wordSem.locals_size s) as [ls|]; destruct (wordSem.stack_size (wordSem.stack s)) as [z|];
      destruct (wordSem.stack_max s) as [m|]; repeat (rewrite ?om_some, ?om2_some in Hsm); repeat (rewrite ?om_some, ?om2_some in Hm); repeat (rewrite ?om_some, ?om2_some); try discriminate Hsm.
    apply some_inj in Hsm. subst sm. specialize (Hm _ eq_refl). destruct Hm as (Hm1 & _ & ss & Ess & Ess2).
    apply some_inj in Ess. subst ss. split; [|split; [reflexivity|eexists; split; [reflexivity|]]]; unfold MAX in *;
      repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:? end;
      repeat match goal with H : context [if ?b then _ else _] |- _ => destruct b eqn:? end; to_prop; lia.
  - rewrite DROP_0_eq, N.add_0_r in *. rewrite HD.
    destruct Hsr as (Hsrt & stack & Habs & Hhnd & Hrel).
    pose proof Habs as Habs0.
    apply abs_stack_NONE_inv in Habs as (w & st & len & lens' & bits & ys & Ed & El & Hb & Hlb & Hl & Hy & ->).
    injection El as <- <-. rewrite Ed.
    pose proof (abs_stack_IMP_LENGTH _ _ _ _ _ Hy) as [Ey _].
    pose proof (abs_stack_to_stack_LENGTH _ _ _ _ _ Habs0) as Hv0. rewrite Ed in Hv0.
    assert (HLsp : LENGTH (DROP sp (stackSem.stack t)) = LENGTH (stackSem.stack t) - sp) by apply LENGTH_DROP'.
    rewrite Ed in HLsp.
    split; [exact Hsrt|].
    exists ((SOME (Loc l1 l2, h), (bits, TAKE f' st)) :: ys). split.
    { rewrite (abs_stack_SOME_eq _ _ _ _ _ _ _ _ w bits st f' lens Hb Hlb Hl). rewrite Hy. reflexivity. }
    split.
    { intros _. rewrite FLOOKUP_UPDATE, decide_True by reflexivity.
      rewrite LASTN_all by (rewrite LENGTH_cons'; lia).
      cbn [handler_val] in Hv0 |- *. rewrite LENGTH_cons' in HLsp, Hv0. rewrite LENGTH_TAKE_le in Hv0 |- * by exact Hl. do 3 f_equal. lia. }
    cbn [stack_rel_aux] in Hrel |- *. destruct Hrel as (Hr1 & Hr2 & Hr3 & Hr4).
    split.
    { intros [Hh1 Hhf]. rewrite Hh in Hhnd. symmetry. apply some_inj. symmetry.
      rewrite LASTN_cons_lt in Hhnd by lia. apply Hhnd. split; [rewrite LENGTH_cons'; lia|].
      rewrite LENGTH_cons'. replace (LENGTH (wordSem.stack s) + 1 - (wordSem.handler s + 1))
        with (LENGTH (wordSem.stack s) - (wordSem.handler s + 1) + 1) by lia.
      rewrite EL_nth' in Hhf |- *.
      replace (N.to_nat (LENGTH (wordSem.stack s) - (wordSem.handler s + 1) + 1))
        with (Datatypes.S (N.to_nat (LENGTH (wordSem.stack s) - (wordSem.handler s + 1)))) by lia.
      rewrite <- Ey. exact Hhf. }
    split; [reflexivity|]. exact (conj Hr1 (conj Hr2 (conj Hr3 Hr4))).
  - intros n v Hn. cbn in Hn. discriminate.
Qed.

End PushHandler.

(** Galette-only: unfold straight-line stackLang code and case-split on the
    conditions it tests. *)
Ltac clk_tac :=
  repeat (first
    [ progress (rewrite ?ev_seq, ?ev_stackalloc, ?ev_stackfree, ?ev_inst, ?inst_const, ?ev_stackstore,
                 ?ev_stackload, ?ev_locvalue, ?ev_get, ?ev_set, ?ev_stackgetsize, ?ev_skip)
    | progress (unfold stackSem.get_var, stackSem.set_var, stackSem.set_store, empty_env)
    | progress stk_fields
    | rewrite FLOOKUP_UPDATE, decide_True by reflexivity
    | match goal with
      | |- context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E
      | |- context [match ?x with _ => _ end] =>
          lazymatch x with context [match _ with _ => _ end] => fail | _ => idtac end;
          let E := fresh "E" in destruct x eqn:E
      end ]).

Lemma ev_seq_congr {a c ffi_t} (p q q' : prog a) (t : stackSem.state a c ffi_t) :
  (forall t' : stackSem.state a c ffi_t, evaluate (q, t') = evaluate (q', t')) -> evaluate (Seq p q, t) = evaluate (Seq p q', t).
Proof. intros H. rewrite !ev_seq. destruct (evaluate (p, t)) as [[r|] t1]; [reflexivity|apply H]. Qed.

Section HandlerClock.
Context {a : N} {c ffi_t : Type}.
Implicit Types (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_PushHandler_clock" *)
Theorem evaluate_PushHandler_clock : forall clk a0 b k f f' t,
  evaluate (@PushHandler a false a0 b (k, (f, f')), set_clock clk t) =
  (FST (evaluate (PushHandler false a0 b (k, (f, f')), t)),
   set_clock clk (SND (evaluate (PushHandler false a0 b (k, (f, f')), t)))).
Proof.
  intros clk a0 b k f f' t. rewrite PushHandler_F. clk_tac; destruct t; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_PopHandler_clock" *)
Theorem evaluate_PopHandler_clock : forall clk k f f' t,
  let prog0 := @PopHandler a false (k, (f, f')) Skip in
  evaluate (prog0, set_clock clk t) =
  (FST (evaluate (prog0, t)), set_clock clk (SND (evaluate (prog0, t)))).
Proof.
  intros clk k f f' t. cbv zeta. rewrite PopHandler_F. clk_tac; destruct t; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_PopHandler_seq" *)
Theorem evaluate_PopHandler_seq : forall k f f' (prog0 : prog a) t,
  evaluate (PopHandler false (k, (f, f')) prog0, t) =
  evaluate (Seq (PopHandler false (k, (f, f')) Skip) prog0, t).
Proof.
  intros k f f' prog0 t. rewrite !PopHandler_F. rewrite ev_seq_assoc. apply ev_seq_congr. intros t1.
  rewrite ev_seq_assoc. apply ev_seq_congr. intros t2. rewrite ev_seq_assoc. apply ev_seq_congr. intros t3.
  rewrite ev_seq, ev_skip. reflexivity.
Qed.

End HandlerClock.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "ALL_DISTINCT_MEM_toAList_fromAList" *)
Theorem ALL_DISTINCT_MEM_toAList_fromAList : forall {B} `{EqDecision B} (ls : list (N * B)) x,
  ALL_DISTINCT (MAP FST ls) ->
  (MEM x (toAList (fromAList ls)) <-> MEM x ls).
Proof.
  intros B HB ls [q r] H. split; intros Hm.
  - apply (ALOOKUP_IFF_MEM ls q r H). apply MEM_toAList in Hm. rewrite lookup_fromAList in Hm. exact Hm.
  - apply MEM_toAList. rewrite lookup_fromAList. apply (ALOOKUP_IFF_MEM ls q r H), Hm.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_code_domain" *)
Theorem state_rel_code_domain : forall {a c ffi_t} ac k f f' (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t) lens extra,
  state_rel ac k f f' s t lens extra -> domain (wordSem.code s) SUBSET domain (code t).
Proof.
  intros a c ffi_t ac k f f' s t lens extra H. sr_destr H. intros x Hx. rewrite Hdom.
  apply IN_INSERT; right; apply IN_INSERT; right; exact Hx.
Qed.
