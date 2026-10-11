(** * CakeML [word_to_stackProof]: correctness of [comp]

    Part of the port of
    [cakeml/compiler/backend/proofs/word_to_stackProofScript.sml] (HOL lines
    5719-10063): the cases of [comp_correct], the simulation of a wordLang
    program by its stackLang translation.  The [Call_returning] case and
    the assembled [comp_correct] are in [comp_call.v].

    HOL proves [comp_correct] by [evaluate_ind] (with one [Resume] block per
    case); wordSem's [evaluate_ind] is not ported (see [wordSem.v]), so here
    the goal is the Galette-only [comp_goal], each case is a lemma
    [comp_correct_X] that assumes the goal for all [eval_lt]-smaller pairs,
    and [comp_correct] is assembled (in [comp_call.v]) by well-founded
    induction on [eval_lt].
    The case lemmas carry HOL's case names.

    Notes: as in [state_rel.v].  HOL's [if P then A else B] on a
    proposition [P] is [if ⌜P⌝ then A else B]; HOL's [LLOOKUP] is [oEL];
    HOL's [t with clock := t.clock + ck] is [set_clock (clock t + ck) t]. *)

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
Import wordLang (word_loc, Word, Loc).
Import wordSem (stack_frame, StackFrame).
Open Scope N_scope.

(** Galette-only: the result part of HOL's [goal]. *)
Abbreviation comp_res ac k f f' s res s1 t1 res1 lens :=
  (if ⌜OPTION_MAP compile_result res <> res1⌝ then
     res1 = SOME (Halt (Word (n2w 2))) /\
     isPREFIX (io_events (ffi t1)) (io_events (wordSem.ffi s1)) /\
     the (wordSem.stack_limit s1 + 1) (wordSem.stack_max s1) > wordSem.stack_limit s1
   else
     match res with
     | NONE => state_rel ac k f f' s1 t1 lens 0
     | SOME (wordSem.Result _ ys) =>
         state_rel ac k 0 0 s1 t1 lens (LENGTH ys - (k - 1)) /\
         (forall i, i < LENGTH ys ->
           if i + 1 <? k then FLOOKUP (regs t1) (i + 1) = SOME (EL i ys)
           else oEL (LENGTH ys - (i + 1)) (DROP (stack_space t1) (stackSem.stack t1)) = SOME (EL i ys))
     | SOME (wordSem.Exception _ y) =>
         exists l0 l,
           state_rel ac k 0 0 (push_locals l0 l s1) t1 (LASTN (wordSem.handler s + 1) lens) 0 /\
           wordSem.locals s1 = union (fromAList l) (fromAList l0) /\
           FLOOKUP (regs t1) 1 = SOME y
     | SOME (wordSem.Break _) => state_rel ac k f f' s1 t1 lens 0
     | SOME (wordSem.Continue _) => state_rel ac k f f' s1 t1 lens 0
     | SOME _ => wordSem.ffi s1 = ffi t1 /\ wordSem.clock s1 = clock t1
     end).

Section Goal.
Context {a : N} {c ffi_t : Type}.

(** HOL's [goal] (an ML binding): the statement proved by induction. *)
Definition comp_goal (ac : asm_config a) (x : wordLang.prog a * wordSem.state a (N * c) ffi_t) : Prop :=
  let '(prog0, s) := x in
  forall k f f' res s1 (t : stackSem.state a c ffi_t) bs n bs' n' sprog lens,
    wordSem.evaluate (prog0, s) = (res, s1) /\ res <> SOME wordSem.Error /\
    state_rel ac k f f' s t lens 0 /\
    post_alloc_conventions k prog0 /\
    flat_exp_conventions prog0 /\
    comp ac false prog0 (bs, n) (k, (f, f')) = (sprog, (bs', n')) /\
    LENGTH (append bs) <= n /\ n - LENGTH (append bs) <= LENGTH (bitmaps t) /\
    isPREFIX (append bs') (DROP (n - LENGTH (append bs)) (bitmaps t)) /\
    get_labels sprog SUBSET loc_check (code t) /\
    wordLang.max_var prog0 < 2 * f' + 2 * k ->
    exists ck (t1 : stackSem.state a c ffi_t) res1,
      evaluate (sprog, set_clock (clock t + ck) t) = (res1, t1) /\
      comp_res ac k f f' s res s1 t1 res1 lens.

End Goal.

(** Galette-only: the result part of [comp_goal] when the stackLang result is
    [OPTION_MAP compile_result res]. *)
Lemma bd_neq_false {A} (x : A) : ⌜x <> x⌝ = false.
Proof. apply bd_false'. intros C; apply C; reflexivity. Qed.

Lemma set_clock_add0 {a c ffi_t} (t : stackSem.state a c ffi_t) : set_clock (clock t + 0) t = t.
Proof. rewrite N.add_0_r. apply state_with_const. Qed.

Lemma ev_tick {a c ffi_t} (X : stackSem.state a c ffi_t) :
  evaluate (Tick, X) = if (clock X =? 0)%N then (SOME TimeOut, empty_env X) else (NONE, dec_clock X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_break {a c ffi_t} n (X : stackSem.state a c ffi_t) : evaluate (stackLang.Break n, X) = (SOME (Break n), X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_continue {a c ffi_t} n (X : stackSem.state a c ffi_t) : evaluate (stackLang.Continue n, X) = (SOME (Continue n), X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

(** Galette-only: introduce the hypotheses of [comp_goal]. *)
Ltac goal_intro :=
  let k := fresh "k" in let f := fresh "f" in let f' := fresh "f'" in
  let res := fresh "res" in let s1 := fresh "s1" in let t := fresh "t" in
  let bs := fresh "bs" in let n := fresh "n" in let bs' := fresh "bs'" in let n' := fresh "n'" in
  let sprog := fresh "sprog" in let lens := fresh "lens" in
  intros k f f' res s1 t bs n bs' n' sprog lens
    (Hev & Hres & H & Hpac & Hflat & Hcomp & Hbs1 & Hbs2 & Hpre & Hlab & Hmax).

Ltac wev H := rewrite wordSem.evaluate_eqn in H; cbn [wordSem.evaluate_body] in H.

Section SimpleCases.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "Skip" *)
Lemma comp_correct_Skip ac s : comp_goal ac (wordLang.Skip, s).
Proof.
  goal_intro. wev Hev. injection Hev as <- <-. cbn [comp] in Hcomp. injection Hcomp as <- <- <-.
  exists 0, t, NONE. rewrite set_clock_add0, ev_skip. split; [reflexivity|].
  cbn [option_map]. rewrite bd_neq_false. exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "Assign" *)
Lemma comp_correct_Assign ac v exp s : comp_goal ac (wordLang.Assign v exp, s).
Proof. goal_intro. cbn in Hflat. discriminate. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "Store" *)
Lemma comp_correct_Store ac exp v s : comp_goal ac (wordLang.Store exp v, s).
Proof. goal_intro. cbn in Hflat. discriminate. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "Break" *)
Lemma comp_correct_Break ac m s : comp_goal ac (wordLang.Break m, s).
Proof.
  goal_intro. wev Hev. injection Hev as <- <-. cbn [comp] in Hcomp. injection Hcomp as <- <- <-.
  exists 0, t, (SOME (Break m)). rewrite set_clock_add0, ev_break. split; [reflexivity|].
  cbn [option_map compile_result]. rewrite bd_neq_false. exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "Continue" *)
Lemma comp_correct_Continue ac m s : comp_goal ac (wordLang.Continue m, s).
Proof.
  goal_intro. wev Hev. injection Hev as <- <-. cbn [comp] in Hcomp. injection Hcomp as <- <- <-.
  exists 0, t, (SOME (Continue m)). rewrite set_clock_add0, ev_continue. split; [reflexivity|].
  cbn [option_map compile_result]. rewrite bd_neq_false. exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "Tick" *)
Lemma comp_correct_Tick ac s : comp_goal ac (wordLang.Tick, s).
Proof.
  goal_intro. wev Hev. cbn [comp] in Hcomp. injection Hcomp as <- <- <-.
  pose proof H as HS0. sr_destr HS0.
  exists 0. rewrite set_clock_add0, ev_tick, <- Hclock.
  destruct (wordSem.clock s =? 0) eqn:Ec; injection Hev as <- <-.
  - eexists; eexists; split; [reflexivity|]. cbn [option_map compile_result]. rewrite bd_neq_false.
    unfold wordSem.flush_state, empty_env. ws_fields. stk_fields. split; [symmetry; exact Hffi2|exact Hclock].
  - eexists; eexists; split; [reflexivity|]. cbn [option_map]. rewrite bd_neq_false.
    apply state_rel_dec_clock, H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "MustTerminate" *)
Lemma comp_correct_MustTerminate ac p s : comp_goal ac (wordLang.MustTerminate p, s).
Proof.
  goal_intro. wev Hev. pose proof H as HS0. sr_destr HS0. rewrite Htd in Hev. cbn in Hev.
  injection Hev as <- _. congruence.
Qed.

End SimpleCases.

Lemma ev_opcurrheap {a c ffi_t} b v src (X : stackSem.state a c ffi_t) :
  evaluate (OpCurrHeap b v src, X) =
  if negb (use_store X) then (SOME Error, X) else
  match stackSem.word_exp X (wordLang.Op b [wordLang.Var src; wordLang.Lookup CurrHeap]) with
  | SOME w => (NONE, stackSem.set_var v (Word w) X)
  | _ => (SOME Error, X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Ltac pac H :=
  unfold post_alloc_conventions in H;
  cbn [wordLang.every_var wordLang.every_stack_var call_arg_convention wordLang.every_var_exp
       wordLang.every_var_imm wordLang.every_name] in H;
  winst_prep.

Ltac mxv H := cbn [wordLang.max_var wordLang.max_var_exp] in H; winst_prep.

Section SimpleCases2.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "Inst" *)
Lemma comp_correct_Inst ac i s : comp_goal ac (wordLang.Inst i, s).
Proof.
  goal_intro. wev Hev. cbn [comp] in Hcomp. injection Hcomp as <- <- <-.
  destruct (wordSem.inst i s) as [s'|] eqn:Ei; injection Hev as <- <-; [|congruence].
  unfold post_alloc_conventions in Hpac. cbn [wordLang.every_var wordLang.every_stack_var call_arg_convention] in Hpac.
  apply andb_prop in Hpac as [Hpac Hconv]. apply andb_prop in Hpac as [Hev' _]. cbn [wordLang.max_var] in Hmax.
  destruct (evaluate_wInst ac k f f' lens i s t s') as (t' & E & H' & _); [exact (conj Ei (conj Hev' (conj Hmax (conj Hconv H))))|].
  exists 0, t', NONE. rewrite set_clock_add0. split; [exact E|]. cbn [option_map]. rewrite bd_neq_false. exact H'.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "Get" *)
Lemma comp_correct_Get ac v name s : comp_goal ac (wordLang.Get v name, s).
Proof.
  goal_intro. wev Hev. cbn [comp] in Hcomp. injection Hcomp as <- <- <-.
  unfold wordSem.get_store in Hev. destruct (FLOOKUP (wordSem.store s) name) as [x|] eqn:Ex; injection Hev as <- <-; [|congruence].
  pac Hpac. mxv Hmax. pose proof (even_div2 v ltac:(assumption)) as Ev.
  pose proof H as HS0. sr_destr HS0.
  assert (Hx : FLOOKUP (store t) name = SOME x).
  { rewrite Hstore, DOMSUB_FLOOKUP_THM in Ex. destruct (decide (Handler = name)); [discriminate|exact Ex]. }
  rewrite Ev. destruct (wRegWrite1_thm1 ac k f f' s t lens (v / 2) (fun r => Get r name) x) as (t' & E & H' & _).
  { split; [exact H|]. split; [lia|]. intros n0 _. rewrite ev_get. unfold is_true in Hust. rewrite Hust, Hx. reflexivity. }
  exists 0, t', NONE. rewrite set_clock_add0. split; [exact E|]. cbn [option_map]. rewrite bd_neq_false. exact H'.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "Set" *)
Lemma comp_correct_Set ac name exp s : comp_goal ac (wordLang.Set_ name exp, s).
Proof.
  goal_intro. wev Hev.
  destruct exp as [w|r|nm|e|bop l|sh e1 e2]; cbn [flat_exp_conventions] in Hflat; try discriminate Hflat.
  cbn [wordSem.word_exp] in Hev.
  destruct (bool_decide (name = Handler) || bool_decide (name = BitmapBase)) eqn:Eh; [injection Hev as <- _; congruence|].
  apply orb_false_iff in Eh as [Eh1 Eh2]. apply bdf in Eh1. apply bdf in Eh2.
  destruct (wordSem.get_var r s) as [w|] eqn:Eg; injection Hev as <- <-; [|congruence].
  cbn [comp] in Hcomp. rewrite decide_False in Hcomp by exact Eh2.
  destruct (wReg1 r (k, (f, f'))) as [x1 r'] eqn:Ew. injection Hcomp as <- <- <-.
  pac Hpac.
  destruct (evaluate_wStackLoad_wReg1 ac k f f' r x1 r' s t lens w) as (t1 & E1 & Hc & HT1 & _ & _ & _ & _ & _ & G1);
    [split; [exact Ew|]; split; [assumption|]; split; [exact Eg|exact H]|].
  exists 0. rewrite set_clock_add0, evaluate_wStackLoad_seq, ev_seq, E1, ev_set.
  pose proof HT1 as HS0. sr_destr HS0. unfold is_true in Hust. rewrite Hust. cbn [negb]. rewrite G1.
  eexists; eexists; split; [reflexivity|]. cbn [option_map]. rewrite bd_neq_false.
  apply state_rel_set_store. split; [exact HT1|exact Eh1].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "OpCurrHeap" *)
Lemma comp_correct_OpCurrHeap ac b dst src s : comp_goal ac (wordLang.OpCurrHeap b dst src, s).
Proof.
  goal_intro. wev Hev. cbn [wordSem.word_exp List.map wordSem.the_words] in Hev.
  destruct (wordSem.get_var src s) as [[x|]|] eqn:Eg; cbn [wordSem.the_words] in Hev; try (injection Hev as <- _; congruence).
  unfold wordSem.get_store in Hev.
  destruct (FLOOKUP (wordSem.store s) CurrHeap) as [[y|]|] eqn:Ey; cbn in Hev; try (injection Hev as <- _; congruence).
  destruct (wordLang.word_op b [x; y]) as [z|] eqn:Eop; cbn in Hev; injection Hev as <- <-; [|congruence].
  cbn [comp] in Hcomp. destruct (wReg1 src (k, (f, f'))) as [xs src_r] eqn:Ew. injection Hcomp as <- <- <-.
  pac Hpac. mxv Hmax.
  destruct (evaluate_wStackLoad_wReg1 ac k f f' src xs src_r s t lens (Word x)) as (t1 & E1 & Hc & HT1 & _ & _ & _ & _ & _ & G1);
    [split; [exact Ew|]; split; [assumption|]; split; [exact Eg|exact H]|].
  pose proof HT1 as HS0. sr_destr HS0.
  assert (Hy : FLOOKUP (store t1) CurrHeap = SOME (Word y)).
  { rewrite Hstore, DOMSUB_FLOOKUP_THM in Ey. destruct (decide (Handler = CurrHeap)); [discriminate|exact Ey]. }
  pose proof (even_div2 dst ltac:(assumption)) as Ed.
  exists 0. rewrite set_clock_add0, evaluate_wStackLoad_seq, ev_seq, E1. rewrite Ed.
  destruct (wRegWrite1_thm1 ac k f f' s t1 lens (dst / 2) (fun dst_r => OpCurrHeap b dst_r src_r) (Word z)) as (t' & E & H' & _).
  { split; [exact HT1|]. split; [lia|]. intros n0 _. rewrite ev_opcurrheap. unfold is_true in Hust. rewrite Hust. cbn [negb].
    unfold stackSem.get_var in G1. cbn [stackSem.word_exp List.map]. rewrite G1, Hy. cbn. rewrite Eop. reflexivity. }
  unfold wRegWrite1 in E. cbv beta iota zeta in E.
  rewrite E. eexists; eexists; split; [reflexivity|]. cbn [option_map]. rewrite bd_neq_false. exact H'.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "LocValue" *)
Lemma comp_correct_LocValue ac r l1 s : comp_goal ac (wordLang.LocValue r l1, s).
Proof.
  goal_intro. wev Hev. destruct (classical_dec _) as [Hl|Hl]; injection Hev as <- <-; [|congruence].
  cbn [comp] in Hcomp. injection Hcomp as <- <- <-.
  pac Hpac. mxv Hmax. pose proof (even_div2 r ltac:(assumption)) as Er.
  assert (Hlc : loc_check (code t) (l1, 0)) by (left; split; [reflexivity|]; apply (state_rel_code_domain _ _ _ _ _ _ _ _ H), Hl).
  rewrite Er. destruct (wRegWrite1_thm1 ac k f f' s t lens (r / 2) (fun r => LocValue r l1 0) (Loc l1 0)) as (t' & E & H' & _).
  { split; [exact H|]. split; [lia|]. intros n0 _. rewrite ev_locvalue. destruct (classical_dec _); [reflexivity|contradiction]. }
  exists 0, t', NONE. rewrite set_clock_add0. split; [exact E|]. cbn [option_map]. rewrite bd_neq_false. exact H'.
Qed.

End SimpleCases2.

Lemma ev_alloc {a c ffi_t} r (X : stackSem.state a c ffi_t) :
  evaluate (stackLang.Alloc r, X) =
  if negb (use_alloc X) then (SOME Error, X) else
  match stackSem.get_var r X with SOME (Word w) => stackSem.alloc w X | _ => (SOME Error, X) end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma MAX_LIST_In' (l : list N) m : In m l -> m <= MAX_LIST l.
Proof.
  induction l as [|x l IH]; intros H; [contradiction|]. cbn [MAX_LIST]. unfold MAX.
  destruct H as [->|H]; [destruct (N.ltb_spec m (MAX_LIST l)); lia|].
  specialize (IH H). destruct (N.ltb_spec x (MAX_LIST l)); lia.
Qed.

Lemma domain_toAList {A} `{EqDecision A} (t : num_map A) x : x IN domain t -> In x (MAP FST (toAList t)).
Proof.
  intros Hx. apply domain_lookup in Hx as [v Hv]. apply MEM_toAList in Hv. unfold is_true in Hv.
  rewrite MEM_In in Hv. apply (in_map FST _ _ Hv).
Qed.

Lemma every_name_dom (P : N -> bool) (names : wordLang.cutsets) x :
  is_true (wordLang.every_name P names) -> x IN domain (FST names) \/ x IN domain (SND names) -> is_true (P x).
Proof.
  unfold wordLang.every_name. intros H Hx. apply andb_prop in H as [H1 H2].
  destruct Hx as [Hx|Hx]; apply domain_toAList in Hx; [apply (EVERY_In _ _ _ H1 Hx)|apply (EVERY_In _ _ _ H2 Hx)].
Qed.

Section AllocCase.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "Alloc" *)
Lemma comp_correct_Alloc ac r names s : comp_goal ac (wordLang.Alloc r names, s).
Proof.
  goal_intro. wev Hev.
  destruct (wordSem.get_var r s) as [[w|]|] eqn:Eg; try (injection Hev as <- _; congruence).
  unfold post_alloc_conventions in Hpac.
  cbn [wordLang.every_var wordLang.every_stack_var call_arg_convention] in Hpac.
  apply andb_prop in Hpac as [Hpac Hr2]. apply andb_prop in Hpac as [Hpac Hst]. apply andb_prop in Hpac as [Hphy Hnm].
  apply N.eqb_eq in Hr2. subst r.
  assert (Hdom : forall x, x IN domain (FST names) \/ x IN domain (SND names) -> EVEN x /\ k <= x DIV 2).
  { intros x Hx. split.
    - apply is_phy_var_EVEN. exact (every_name_dom _ _ _ Hnm Hx).
    - pose proof (every_name_dom _ _ _ Hst Hx) as Hk. apply N.leb_le in Hk.
      apply N.div_le_lower_bound; lia. }
  pose proof H as HS0. sr_destr HS0.
  assert (Hg1 : FLOOKUP (regs t) 1 = SOME (Word w)) by (apply (state_rel_get_var_imp ac k f f' s t lens 0 1); split; [exact H|]; split; [exact Eg|lia]).
  cbn [comp] in Hcomp. destruct (wLive names (bs, n) (k, (f, f'))) as [q1 [bs1 n1]] eqn:Ew.
  injection Hcomp as <- <- <-.
  exists 0. rewrite set_clock_add0, ev_seq.
  destruct (wordSem.cut_envs names (wordSem.locals s)) as [envs|] eqn:Ecut.
  2:{ unfold wordSem.alloc in Hev. rewrite Ecut in Hev. injection Hev as <- _. congruence. }
  destruct (N.le_gt_cases 1 f) as [Hf|Hf].
  - destruct (evaluate_wLive ac k f f' lens names bs n q1 bs1 n1 s t envs) as (t5 & E5 & HR0 & HR & HL5 & HS5 & HG5).
    { split; [exact Ew|]. split; [intros x Hx; apply Hdom; left; exact Hx|].
      split; [intros x Hx; apply Hdom; right; exact Hx|]. split; [exact H|]. split; [exact Hf|]. split; [exact Ecut|].
      split; [exact Hbs1|]. split; [exact Hbs2|]. exact Hpre. }
    destruct (alloc_IMP_alloc ac k f f' lens w names s s1 t5 envs res) as (t1 & res1 & Ea & Hif).
    { split; [exact Hev|]. split; [intros x Hx; apply Hdom; left; exact Hx|].
      split; [intros x Hx; apply Hdom; right; exact Hx|]. split; [exact Hf|]. split; [exact HR|]. split; [exact HR0|].
      split; [exact Ecut|exact Hres]. }
    rewrite E5, ev_alloc. pose proof HR as HS1. sr_destr HS1. unfold is_true in Hua0. rewrite Hua0. cbn [negb].
    rewrite (HG5 1) by lia. unfold stackSem.get_var. rewrite Hg1, Ea.
    exists t1, res1. split; [reflexivity|].
    destruct (decide (res = NONE)) as [->|Hn].
    + destruct Hif as (-> & Hif & _). cbn [option_map]. rewrite bd_neq_false. exact Hif.
    + destruct Hif as (-> & -> & Hc & Hf2). cbn [option_map compile_result]. rewrite bd_neq_false. split; congruence.
  - assert (Hf0 : f = 0) by lia. subst f.
    assert (Hf'0 : f' = 0) by (destruct (f' =? 0) eqn:E; [apply N.eqb_eq in E; exact E|lia]). subst f'.
    unfold wLive in Ew. cbn in Ew. injection Ew as <- _ _.
    assert (Hempty : forall x, ~ (x IN domain (FST names) \/ x IN domain (SND names))).
    { intros x Hx. destruct (Hdom x Hx) as [_ Hx2]. cbn [wordLang.max_var] in Hmax.
      rewrite MAX_lt_iff in Hmax. destruct Hmax as [_ Hmax]. unfold wordLang.cutsets_max in Hmax.
      rewrite MAX_lt_iff in Hmax. destruct Hx as [Hx|Hx]; apply domain_toAList in Hx; apply MAX_LIST_In' in Hx; lia. }
    destruct (alloc_IMP_alloc2 ac k lens w names s s1 t res) as (t1 & res1 & Ea & Hif).
    { split; [exact Hev|]. split; [exact H|].
      split; [apply set_ext; intros x; split; [intros Hx; exfalso; apply (Hempty x); left; exact Hx|intros []]|].
      split; [apply set_ext; intros x; split; [intros Hx; exfalso; apply (Hempty x); right; exact Hx|intros []]|].
      exact Hres. }
    rewrite ev_skip, ev_alloc. unfold is_true in Hua. rewrite Hua. cbn [negb].
    unfold stackSem.get_var. rewrite Hg1, Ea.
    exists t1, res1. split; [reflexivity|].
    destruct (decide (res = NONE)) as [->|Hn].
    + destruct Hif as (-> & Hif & _). cbn [option_map]. rewrite bd_neq_false. exact Hif.
    + destruct Hif as (-> & -> & Hc & Hf2). cbn [option_map compile_result]. rewrite bd_neq_false. split; congruence.
Qed.

End AllocCase.

Lemma ev_storeconsts {a c ffi_t} t1 t2 stub (X : stackSem.state a c ffi_t) :
  evaluate (StoreConsts t1 t2 stub, X) =
  if negb (use_store X) then (SOME Error, X) else
  if andb (negb (use_alloc X)) (IS_SOME stub) then (SOME Error, X) else
  if negb (check_store_consts_opt t1 t2 stub (code X)) then (SOME Error, X) else
    store_const_sem t1 t2 X.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Ltac dec_lia := repeat (first [rewrite decide_True by lia | rewrite decide_False by lia]).

Section StoreConstsCase.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "StoreConsts" *)
Lemma comp_correct_StoreConsts ac r1 r2 ad off ws s : comp_goal ac (wordLang.StoreConsts r1 r2 ad off ws, s).
Proof.
  goal_intro. wev Hev.
  destruct (wordSem.get_var ad s) as [[A|]|] eqn:Ea; try (injection Hev as <- _; congruence).
  destruct (wordSem.get_var off s) as [[O|]|] eqn:Eo; try (injection Hev as <- _; congruence).
  destruct (wordSem.const_addresses A ws (wordSem.mdomain s)) eqn:Eca; cbn [negb] in Hev; [|injection Hev as <- _; congruence].
  cbv zeta in Hev. injection Hev as <- <-.
  unfold post_alloc_conventions in Hpac. cbn [wordLang.every_var wordLang.every_stack_var call_arg_convention] in Hpac.
  apply andb_prop in Hpac as [_ Hconv]. to_prop. subst r1 r2 ad off.
  cbn [comp] in Hcomp. unfold insert_bitmap in Hcomp. cbv zeta in Hcomp. injection Hcomp as <- <- <-.
  pose proof H as HS0. sr_destr HS0.
  (* the bitmap is in place *)
  assert (Hbm : exists xs ys, bitmaps t = xs ++ const_words_to_bitmap ws (LENGTH ws) ++ ys /\ LENGTH xs = n).
  { destruct (proj1 (isPREFIX_iff _ _) Hpre) as [ys Hys]. rewrite (proj1 (append_thm _ _ [])) in Hys.
    rewrite (proj1 (proj2 (append_thm bs bs (const_words_to_bitmap ws (LENGTH ws))))) in Hys.
    exists (TAKE (n - LENGTH (append bs)) (bitmaps t) ++ append bs), ys. split.
    - rewrite <- app_assoc in Hys. rewrite <- !app_assoc, <- Hys. rewrite TAKE_firstn, DROP_skipn. symmetry. apply firstn_skipn.
    - set (L := LENGTH (append bs)) in *. rewrite LENGTH_app', TAKE_firstn. rewrite (LENGTH_length (firstn _ _)), length_firstn.
      rewrite LENGTH_length in Hbs2. lia. }
  destruct Hbm as (xs & ys & Ebm & Exs).
  assert (G2 : FLOOKUP (regs t) 2 = SOME (Word A)) by (apply (state_rel_get_var_imp ac k f f' s t lens 0 2); split; [exact H|]; split; [exact Ea|lia]).
  assert (G3 : FLOOKUP (regs t) 3 = SOME (Word O)) by (apply (state_rel_get_var_imp ac k f f' s t lens 0 3); split; [exact H|]; split; [exact Eo|lia]).
  assert (Hn : n < dimword a).
  { assert (LENGTH (bitmaps t) >= n) by (rewrite Ebm, !LENGTH_app'; lia). lia. }
  exists 0. rewrite set_clock_add0, ev_seq, ev_inst, inst_const, ev_storeconsts.
  unfold stackSem.set_var. stk_fields. unfold is_true in Hust, Hua. rewrite Hust, Hua. cbn [negb andb IS_SOME].
  unfold check_store_consts_opt. rewrite bd_true' by exact Hsc. cbn [negb].
  unfold store_const_sem.
  assert (Hd : ALL_DISTINCT [0; 1; 2; 3; k; k + 1] = true).
  { apply ALL_DISTINCT_iff. repeat constructor; cbn; intuition lia. }
  rewrite Hd. cbn [negb]. unfold stackSem.get_var. stk_fields. rewrite !FLOOKUP_UPDATE. dec_lia.
  rewrite G2, G3. rewrite w2n_n2w, N.mod_small by exact Hn.
  rewrite Ebm, <- Exs, Hmd, Hmem. rewrite copy_words_correct by (split; [exact Eca|exact Hgd]).
  rewrite Hua.
  eexists; eexists; split; [reflexivity|]. cbn [option_map]. rewrite bd_neq_false.
  unfold wordSem.set_var, wordSem.unset_var, wordSem.set_memory, unset_var, stackSem.set_var, set_memory.
  sr_split; ws_fields; stk_fields; try assumption; try reflexivity.
  - apply wf_insert, wf_insert, wf_delete, wf_delete, Hwf.
  - intros m v Hm. rewrite !lookup_insert, !lookup_delete in Hm.
    rewrite DOMSUB_FLOOKUP_THM, !FLOOKUP_UPDATE.
    destruct (decide (m = 4)) as [->|H4].
    + injection Hm as <-. split; [reflexivity|].
      replace (4 DIV 2) with 2 by reflexivity. rewrite (proj2 (N.ltb_lt 2 k)) by lia. dec_lia. reflexivity.
    + destruct (decide (m = 6)) as [->|H6].
      * injection Hm as <-. split; [reflexivity|].
        replace (6 DIV 2) with 3 by reflexivity. rewrite (proj2 (N.ltb_lt 3 k)) by lia. dec_lia. exact G3.
      * destruct (decide (m = 0)) as [->|H0]; [discriminate|].
        destruct (decide (m = 2)) as [->|H2]; [discriminate|].
        destruct (Hloc m v Hm) as [He Hr]. split; [exact He|].
        pose proof (even_div2 m He) as Em.
        destruct (m / 2 <? k) eqn:Ek; [|exact Hr]. apply N.ltb_lt in Ek. dec_lia. exact Hr.
Qed.

End StoreConstsCase.

Section MoveCase.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "Move" *)
Lemma comp_correct_Move ac pri moves s : comp_goal ac (wordLang.Move pri moves, s).
Proof.
  goal_intro. wev Hev.
  destruct (ALL_DISTINCT (MAP FST moves)) eqn:Hd; [|injection Hev as <- _; congruence].
  destruct (wordSem.get_vars (MAP SND moves) s) as [vs|] eqn:Egv; injection Hev as <- <-; [|congruence].
  cbn [comp] in Hcomp. injection Hcomp as <- <- <-.
  unfold post_alloc_conventions in Hpac. cbn [wordLang.every_var wordLang.every_stack_var call_arg_convention] in Hpac.
  apply andb_prop in Hpac as [Hpac _]. apply andb_prop in Hpac as [Hpac _]. apply andb_prop in Hpac as [HF HS].
  cbn [wordLang.max_var] in Hmax.
  assert (HeF : forall x, In x (MAP FST moves) -> EVEN x) by (intros x Hx; apply is_phy_var_EVEN, (EVERY_In _ _ _ HF Hx)).
  assert (HeS : forall x, In x (MAP SND moves) -> EVEN x) by (intros x Hx; apply is_phy_var_EVEN, (EVERY_In _ _ _ HS Hx)).
  assert (HbF : forall x, In x (MAP FST moves) -> x < 2 * f' + 2 * k)
    by (intros x Hx; pose proof (MAX_LIST_In' _ x (in_or_app (MAP FST moves) (MAP SND moves) x (or_introl Hx))); lia).
  assert (HbS : forall x, In x (MAP SND moves) -> x < 2 * f' + 2 * k)
    by (intros x Hx; pose proof (MAX_LIST_In' _ x (in_or_app (MAP FST moves) (MAP SND moves) x (or_intror Hx))); lia).
  set (g := fun n : N => n DIV 2).
  set (mvs := MAP (g ## g) moves).
  assert (HevF : is_true (EVERY EVEN (MAP FST moves))) by (unfold is_true; rewrite EVERY_Forall, Forall_forall; exact HeF).
  assert (HevS : is_true (EVERY EVEN (MAP SND moves))) by (unfold is_true; rewrite EVERY_Forall, Forall_forall; exact HeS).
  assert (Hwm : windmill mvs).
  { unfold windmill, mvs. rewrite map_FST_PAIR_MAP. apply ALL_DISTINCT_iff. apply ALL_DISTINCT_iff in Hd.
    apply proofs.NoDup_map_inj_on; [exact Hd|]. intros x y Hx Hy E. apply EVEN_DIV2_INJ.
    split; [apply HeF, Hx|]. split; [apply HeF, Hy|exact E]. }
  pose proof H as HS0. sr_destr HS0.
  set (pm := parmove mvs).
  set (r := fun x : option N => match x with NONE => stackSem.get_var (k + 1) t | SOME i => wordSem.get_var (2 * i) s end).
  assert (Hsome : forall y, In y (MAP SND moves) -> exists w, wordSem.get_var y s = SOME w).
  { intros y Hy. pose proof (IS_SOME_get_vars_EVERY (MAP SND moves) s) as HE. rewrite Egv in HE.
    pose proof (EVERY_In _ _ _ (eq_sym HE) Hy) as Hi. cbv beta in Hi.
    destruct (wordSem.get_var y s) as [w|]; [exists w; reflexivity|discriminate]. }
  assert (HmS : forall y, In (SOME y) (MAP SND pm) -> exists Y, In Y (MAP SND moves) /\ y = Y / 2).
  { intros y Hy. assert (Hm : is_true (MEM (SOME y) (MAP SND pm))) by (apply MEM_iff; exact Hy).
    apply proofs.MEM_MAP_SND_parmove, MEM_iff in Hm. unfold mvs in Hm.
    rewrite map_map in Hm. apply in_map_iff in Hm as ([X Y] & Ey & HXY). cbn in Ey.
    exists Y. split; [apply (in_map SND _ _ HXY)|symmetry; exact Ey]. }
  assert (HmF : forall y, In (SOME y) (MAP FST pm) -> exists X, In X (MAP FST moves) /\ y = X / 2).
  { intros y Hy. assert (Hm : is_true (MEM (SOME y) (MAP FST pm))) by (apply MEM_iff; exact Hy).
    apply proofs.MEM_MAP_FST_parmove, MEM_iff in Hm. unfold mvs in Hm.
    rewrite map_FST_PAIR_MAP in Hm. apply in_map_iff in Hm as (X & Ey & HX).
    exists X. split; [exact HX|symmetry; exact Ey]. }
  destruct (evaluate_wMoveAux_seqsem ac k f f' lens pm s t r) as (t' & E' & H' & HL' & HS').
  { split; [exact H|]. split; [intros; reflexivity|]. split; [intros v Hv; exact Hv|].
    split.
    { rewrite IS_SOME_get_vars_EVERY. unfold is_true. rewrite EVERY_Forall, Forall_forall.
      intros x Hx. apply in_map_iff in Hx as ([y|] & <- & Hy); [|apply filter_In in Hy as [_ Hy]; discriminate].
      apply filter_In in Hy as [Hy _]. destruct (HmS y Hy) as (Y & HY & ->). cbn [THE].
      rewrite <- (even_div2 Y (HeS Y HY)). destruct (Hsome Y HY) as [w ->]. reflexivity. }
    split.
    { pose proof (proofs.parmove_not_use_temp_before_assign mvs Hwm) as Hn. fold pm in Hn.
      destruct (find_index NONE (MAP SND pm) 0) as [i|]; [|exact Logic.I].
      destruct (find_index NONE (MAP FST pm) 0) as [j|]; [|contradiction]. intros Hij. contradiction. }
    split.
    { unfold is_true. rewrite EVERY_Forall, Forall_forall. intros [x y] Hxy. apply bool_decide_spec.
      intros a0 [-> | ->].
      - destruct (HmF a0 (in_map FST _ _ Hxy)) as (X & HX & ->). pose proof (HbF X HX). apply N.Div0.div_lt_upper_bound; lia.
      - destruct (HmS a0 (in_map SND _ _ Hxy)) as (Y & HY & ->). pose proof (HbS Y HY). apply N.Div0.div_lt_upper_bound; lia. }
    apply proofs.ALL_DISTINCT_parmove, Hwm. }
  exists 0, t', NONE. rewrite set_clock_add0.
  unfold wMove. cbv beta iota.
  replace (MAP (fun '(x, y) => (x DIV 2, y DIV 2)) moves) with mvs by (unfold mvs; apply map_ext; intros [x y]; reflexivity).
  fold pm.
  replace (MAP (fun '(x, y) => (format_var k x, format_var k y)) pm) with (MAP (format_var k ## format_var k) pm)
    by (apply map_ext; intros [x y]; reflexivity).
  split; [exact E'|]. cbn [option_map]. rewrite bd_neq_false.
  replace (wordSem.set_vars (MAP FST moves) vs s) with
    (wordSem.set_vars (MAP (fun x => 2 * THE x) (FILTER IS_SOME (MAP FST (REVERSE pm))))
       (MAP THE (MAP (seqsem pm r) (FILTER IS_SOME (MAP FST (REVERSE pm))))) s); [exact H'|].
  unfold wordSem.set_vars. f_equal.
  set (F0 := FILTER IS_SOME (MAP FST pm)).
  assert (HF0 : FILTER IS_SOME (MAP FST (REVERSE pm)) = REVERSE F0) by (unfold F0; rewrite map_rev, proofs.filter_rev; reflexivity).
  rewrite HF0, !map_rev.
  assert (HdF0 : is_true (ALL_DISTINCT F0)) by (apply proofs.ALL_DISTINCT_parmove, Hwm).
  rewrite alist_insert_REVERSE.
  2:{ split; [|rewrite !LENGTH_length, !length_map; reflexivity].
      apply ALL_DISTINCT_iff. apply ALL_DISTINCT_iff in HdF0. apply proofs.NoDup_map_inj_on; [exact HdF0|].
      intros x y Hx Hy E. unfold F0 in Hx, Hy. apply filter_In in Hx as [_ Hx], Hy as [_ Hy].
      destruct x, y; try discriminate. cbn [THE] in E. f_equal. lia. }
  (* the keys *)
  assert (HK : MAP (fun x => 2 * THE x) F0 = MAP THE (FILTER IS_SOME (MAP FST (parmove moves)))).
  { unfold F0, pm, mvs, g. apply TIMES2_DIV2_lemma. split; [exact Hd|]. split; assumption. }
  rewrite HK.
  (* the values *)
  assert (HV : MAP THE (MAP (seqsem pm r) F0) =
               MAP (fun x => THE (wordSem.get_var (THE (ALOOKUP moves (THE x))) s)) (FILTER IS_SOME (MAP FST (parmove moves)))).
  { transitivity (MAP THE (MAP (parsem (MAP (SOME ## SOME) mvs) r) F0)).
    { f_equal. apply map_ext_in. intros x Hx. unfold F0 in Hx. apply filter_In in Hx as [_ Hx].
      pose proof (proofs.parmove_correct mvs Hwm r x Hx) as Hc. fold pm in Hc. rewrite Hc. f_equal.
      apply map_ext. intros [p q]. reflexivity. }
    unfold F0, pm, mvs, g. rewrite parsem_parmove_DIV2_lemma by (split; [exact Hd|]; split; assumption).
    rewrite map_map. apply map_ext_in. intros x Hx. apply filter_In in Hx as [Hx Hs].
    destruct x as [z|]; [|discriminate]. cbv beta.
    assert (Hz : is_true (MEM z (MAP FST moves))) by (apply proofs.MEM_MAP_FST_parmove, MEM_iff; exact Hx).
    apply MEM_iff, in_map_iff in Hz as ([z' y] & Ez & Hzy). cbn in Ez. subst z'.
    rewrite (proofs.parsem_in _ _ (SOME z) (SOME y)).
    - cbn [THE option_map]. rewrite (ALOOKUP_ALL_DISTINCT_MEM moves z y) by (split; [exact Hd|apply MEM_iff; exact Hzy]).
      cbn [THE]. unfold r. rewrite <- (even_div2 y (HeS y (in_map SND _ _ Hzy))). reflexivity.
    - rewrite map_map. apply ALL_DISTINCT_iff in Hd. replace (List.map (fun x0 => fst ((SOME ## SOME) x0)) moves) with (List.map SOME (List.map fst moves))
        by (rewrite map_map; reflexivity).
      apply proofs.NoDup_map_inj_on; [exact Hd|intros p q _ _ Epq; injection Epq; auto].
    - apply (in_map (SOME ## SOME) _ _ Hzy). }
  rewrite HV. apply alist_insert_get_vars.
  split; [exact Hd|]. split; [exact Egv|]. split; [apply proofs.ALL_DISTINCT_parmove, Hd|]. split; [exact Hwf|].
  split; [intros x Hx; apply proofs.MEM_MAP_FST_parmove, Hx|].
  intros x y [Hxy Hne]. apply (proofs.parmove_preserves_moves moves x y). split; [exact Hd|]. split; [exact Hxy|exact Hne].
Qed.

End MoveCase.

Lemma ev_return {a c ffi_t} r (X : stackSem.state a c ffi_t) :
  evaluate (Return r, X) =
  match stackSem.get_var r X with SOME (Loc l1 l2) => (SOME (Result (Loc l1 l2)), X) | _ => (SOME Error, X) end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma get_vars_EL' {a C F} (s : wordSem.state a C F) : forall ls ys i,
  wordSem.get_vars ls s = SOME ys -> i < LENGTH ys -> wordSem.get_var (EL i ls) s = SOME (EL i ys).
Proof.
  intros ls ys i H Hi. pose proof (dec_clock.get_vars_length_lemma _ _ _ H) as HL.
  destruct (get_vars_EL s ls ys i H) as (v & H1 & H2); [rewrite !LENGTH_length in *; lia|].
  unfold wordSem.get_var. rewrite H2. f_equal. rewrite EL_nth'. symmetry. apply nth_error_nth, H1.
Qed.

Section ReturnCase.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "Return" *)
Lemma comp_correct_Return ac r ms s : comp_goal ac (wordLang.Return r ms, s).
Proof.
  goal_intro. wev Hev.
  destruct (wordSem.get_var r s) as [[w|l1 l2]|] eqn:Eg; try (injection Hev as <- _; congruence).
  destruct (wordSem.get_vars ms s) as [ys|] eqn:Egv; [|injection Hev as <- _; congruence].
  injection Hev as <- <-.
  unfold post_alloc_conventions in Hpac. cbn [wordLang.every_var wordLang.every_stack_var call_arg_convention] in Hpac.
  apply andb_prop in Hpac as [Hpac Hconv]. apply andb_prop in Hpac as [Hpac _]. apply andb_prop in Hpac as [Hr _].
  apply bool_decide_spec in Hconv. apply is_phy_var_EVEN in Hr.
  pose proof (dec_clock.get_vars_length_lemma _ _ _ Egv) as HLys.
  cbn [wordLang.max_var MAX_LIST] in Hmax. rewrite MAX_lt_iff in Hmax. destruct Hmax as [Hmr Hmms].
  rewrite Hconv, MAX_LIST_GENLIST_evens2 in Hmms.
  cbn [comp] in Hcomp. destruct (wReg1 r (k, (f, f'))) as [xs x] eqn:Ew. injection Hcomp as <- <- <-.
  destruct (evaluate_wStackLoad_wReg1 ac k f f' r xs x s t lens (Loc l1 l2)) as (t1 & E1 & Hc1 & HT1 & HL1 & HS1 & HB1 & HR1 & _ & G1);
    [split; [exact Ew|]; split; [exact Hr|]; split; [exact Eg|exact H]|].
  pose proof HT1 as HS0. sr_destr HS0.
  assert (Hff0 : f = 0 /\ f' = 0 \/ f = f' + 1) by (destruct (f' =? 0) eqn:E; [apply N.eqb_eq in E; lia|lia]).
  set (nsr := num_stack_ret k ms).
  assert (Hnsr : nsr <= f) by (unfold nsr, num_stack_ret; lia).
  exists 0. rewrite set_clock_add0, evaluate_wStackLoad_seq, ev_seq, E1.
  rewrite evaluate_SeqStackFree by (split; [exact Hus|lia]).
  rewrite ev_seq, ev_stackfree. unfold is_true in Hus. rewrite Hus. cbn [negb].
  unfold skip_free. rewrite (proj2 (N.ltb_ge _ _)) by lia.
  rewrite ev_return. unfold stackSem.get_var in G1 |- *. stk_fields. rewrite G1.
  eexists; eexists; split; [reflexivity|]. cbn [option_map compile_result]. rewrite bd_neq_false.
  replace (LENGTH ys - (k - 1)) with nsr by (unfold nsr, num_stack_ret; lia).
  split.
  - unfold wordSem.flush_state. sr_split; ws_fields; stk_fields; try assumption; try lia; try reflexivity; try apply wf_LN.
    + unfold stack_size_rel in *. destruct Hssr as (_ & Hl & Hm). split; [intros C; lia|]. split; [exact Hl|].
      intros sm Hsm. destruct (Hm sm Hsm) as (Hm1 & Hm2 & ss & Hss & Ess). split; [lia|]. split; [reflexivity|].
      exists ss. split; [exact Hss|lia].
    + replace (stack_space t1 + (f - nsr) + nsr) with (stack_space t1 + f) by lia. rewrite DROP_0_eq, N.add_0_r in *.
      rewrite DROP_DROP_EQ in Hsr. replace (f + stack_space t1) with (stack_space t1 + f) in Hsr by lia. exact Hsr.
    + intros n0 v Hn0. rewrite lookup_LN in Hn0. discriminate.
  - intros i Hi. assert (HEi : EL i ms = 2 * (i + 1)).
    { rewrite Hconv, EL_GENLIST_N by lia. reflexivity. }
    pose proof (get_vars_EL' s ms ys i Egv Hi) as Gi. rewrite HEi in Gi. unfold wordSem.get_var in Gi.
    destruct (Hloc _ _ Gi) as [_ HRi]. rewrite mul2_div2 in HRi.
    destruct (i + 1 <? k) eqn:Eik; [exact HRi|]. apply N.ltb_ge in Eik. destruct HRi as [HRi HRi2].
    assert (Hf1 : f = f' + 1) by lia.
    rewrite N.add_0_r, oEL_TAKE_lt, oEL_DROP in HRi by lia. stk_fields. rewrite oEL_DROP. rewrite <- HRi. f_equal.
    unfold nsr, num_stack_ret. lia.
Qed.

End ReturnCase.

Lemma ev_call_none {a c ffi_t} dest (X : stackSem.state a c ffi_t) :
  evaluate (Call NONE dest NONE, X) =
  match find_code dest (regs X) (code X) with
  | NONE => (SOME Error, X)
  | SOME prog0 =>
      if (clock X =? 0)%N then (SOME TimeOut, empty_env X) else
        match fix_clock (dec_clock X) (evaluate (prog0, dec_clock X)) with
        | (res, s) => if bad_fun_return res then (SOME Error, s) else (res, s)
        end
  end.
Proof.
  rewrite evaluate_eqn. cbn [evaluate_body]. destruct (find_code dest (regs X) (code X)); [|reflexivity].
  rewrite bd_true' by reflexivity. reflexivity.
Qed.

Lemma ev_stacksetsize {a c ffi_t} r (X : stackSem.state a c ffi_t) :
  evaluate (StackSetSize r, X) =
  if negb (use_stack X) then (SOME Error, X) else
  match stackSem.get_var r X with
  | SOME (Word w) =>
      if (LENGTH (stackSem.stack X) <=? w2n w)%N then (SOME Error, empty_env X)
      else (NONE, stackSem.set_var r (Word (word_lsl w (word_shift a))) (set_stack_space (w2n w) X))
  | _ => (SOME Error, X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_raise {a c ffi_t} r (X : stackSem.state a c ffi_t) :
  evaluate (Raise r, X) =
  match stackSem.get_var r X with SOME (Loc l1 l2) => (SOME (Exception (Loc l1 l2)), X) | _ => (SOME Error, X) end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma dec_clock_set_clock1 {a c ffi_t} (t : stackSem.state a c ffi_t) : dec_clock (set_clock (clock t + 1) t) = t.
Proof. unfold dec_clock. stk_fields. replace (clock t + 1 - 1) with (clock t) by lia. destruct t; reflexivity. Qed.

Section RaiseCase.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "Raise" *)
Lemma comp_correct_Raise ac v s : comp_goal ac (wordLang.Raise v, s).
Proof.
  goal_intro. wev Hev.
  destruct (wordSem.get_var v s) as [w|] eqn:Eg; [|injection Hev as <- _; congruence].
  destruct (wordSem.jump_exc s) as [[s' [l1 l2]]|] eqn:Ej; [|injection Hev as <- _; congruence].
  injection Hev as <- <-.
  unfold post_alloc_conventions in Hpac. cbn [wordLang.every_var wordLang.every_stack_var call_arg_convention] in Hpac.
  apply andb_prop in Hpac as [_ Hv2]. apply N.eqb_eq in Hv2. subst v.
  unfold wordSem.jump_exc in Ej. destruct (wordSem.handler s <? LENGTH (wordSem.stack s)) eqn:Eh; [|discriminate].
  apply N.ltb_lt in Eh.
  destruct (LASTN (wordSem.handler s + 1) (wordSem.stack s)) as [|[m e0 e [[n0 [l1' l2']]|]] xs] eqn:EL;
    try discriminate. injection Ej as <- -> ->.
  cbn [comp] in Hcomp. injection Hcomp as <- <- <-.
  pose proof H as HS0. sr_destr HS0.
  destruct Hsr as (Hsrt & astack & Habs & Hhnd & Hrel).
  rewrite N.add_0_r, DROP_DROP_EQ in Habs.
  assert (Hh : FLOOKUP (store t) Handler = SOME (Word (n2w (LENGTH (stackSem.stack t) - handler_val (LASTN (wordSem.handler s + 1) astack))))).
  { apply Hhnd. split; [exact Eh|]. rewrite <- LASTN_HD by lia. rewrite EL. reflexivity. }
  assert (Hse : SORTED (fun x y => FST x > FST y) e).
  { pose proof (EVERY_IMP_EVERY_LASTN _ _ _ _ (conj Hsrt EL)) as HE. cbn [EVERY] in HE.
    apply andb_prop in HE as [HE _]. apply bool_decide_spec in HE. exact HE. }
  destruct (stack_rel_raise (f + stack_space t) (stackSem.stack t) (wordSem.handler s) (wordSem.stack s) e m e0 n0 l1 l2 xs
              (bitmaps t) lens astack k) as (ex & payload & HLA & H3L & H3hv & HEL1 & HEL2 & Hrel' & Habs').
  { split; [lia|]. split; [lia|]. split; [exact Hse|]. split; [exact EL|]. split; [exact Habs|exact Hrel]. }
  assert (He : FST (wordSem.env_to_list (fromAList e) (K I)) = e).
  { destruct (wordSem.env_to_list (fromAList e) (K I)) as [l' orc] eqn:Een. cbn [FST fst].
    apply env_to_list_K_I_IMP in Een as (Hs' & _ & Hperm').
    apply SORTED_FST_PERM_IMP_ALIST_EQ; auto. }
  rewrite He in Hrel', Habs'.
  set (HV := handler_val (LASTN (wordSem.handler s + 1) astack)) in *.
  assert (HVle : HV <= LENGTH (stackSem.stack t) - (f + stack_space t)).
  { pose proof (abs_stack_len _ _ _ _ _ (wordSem.handler s + 1) Habs) as Hl. rewrite LENGTH_DROP' in Hl. exact Hl. }
  set (L := LENGTH (stackSem.stack t)) in *.
  exists 1. rewrite ev_call_none. stk_fields. cbn [find_code]. rewrite Hraise.
  rewrite (proj2 (N.eqb_neq _ _)) by lia. rewrite dec_clock_set_clock1, fix_clock_evaluate, raise_stub_F.
  unfold is_true in Hus, Hust.
  rewrite ev_seq, ev_get, Hust. cbn [negb]. rewrite Hh.
  rewrite ev_seq, ev_stacksetsize. unfold stackSem.set_var, stackSem.get_var. stk_fields. rewrite Hus. cbn [negb].
  rewrite FLOOKUP_UPDATE, decide_True by reflexivity. rewrite w2n_n2w, N.mod_small by lia.
  rewrite (proj2 (N.leb_gt _ _)) by lia.
  rewrite ev_seq, ev_skip.
  rewrite ev_seq, ev_stackload. unfold stackSem.set_var. stk_fields. rewrite Hus. cbn [negb].
  rewrite (proj2 (N.ltb_lt _ _)) by lia.
  rewrite ev_seq, ev_set. unfold stackSem.set_var, stackSem.get_var. stk_fields. rewrite Hust. cbn [negb].
  rewrite FLOOKUP_UPDATE, decide_True by reflexivity.
  rewrite ev_seq, ev_stackload. unfold stackSem.set_var, stackSem.set_store. stk_fields. rewrite Hus. cbn [negb].
  rewrite (proj2 (N.ltb_lt _ _)) by lia.
  rewrite ev_seq, ev_stackfree. unfold stackSem.set_var. stk_fields. rewrite Hus. cbn [negb].
  rewrite (proj2 (N.ltb_ge _ _)) by lia.
  rewrite ev_raise. unfold stackSem.get_var. stk_fields. rewrite FLOOKUP_UPDATE, decide_True by reflexivity.
  replace (L - HV + 1) with (L - HV + 1) by reflexivity. rewrite HEL1.
  cbn [bad_fun_return].
  eexists; eexists; split; [reflexivity|]. cbn [option_map compile_result]. rewrite bd_neq_false.
  exists e0, e.
  split; [|split; [reflexivity|]].
  2:{ stk_fields. rewrite !FLOOKUP_UPDATE. dec_lia.
      apply (state_rel_get_var_imp ac k f f' s t lens 0 1). split; [exact H|]. split; [exact Eg|lia]. }
  pose proof (stack_rel_aux_LENGTH _ _ _ _ Hrel') as HLr'. rewrite !LENGTH_cons' in HLr'.
  unfold HV in *. rewrite HLA in *.
  destruct payload as [bits fr]. cbn [handler_val] in *.
  unfold push_locals. sr_split; ws_fields; stk_fields; try assumption; try reflexivity; try apply wf_LN.
  - rewrite Hstore, DOMSUB_FUPDATE. reflexivity.
  - rewrite FDOM_FUPDATE. apply IN_INSERT. left; reflexivity.
  - lia.
  - unfold stack_size_rel in *. destruct Hssr as (_ & Hl & Hm). split; [intros C; lia|]. split; [exact Hl|].
    intros sm Hsm. destruct (Hm sm Hsm) as (Hm1 & Hm2 & ss & Hss & Ess). split; [lia|]. split; [reflexivity|].
    destruct (stack_max.LASTN_stack_size_SOME (wordSem.handler s + 1) (wordSem.stack s) (StackFrame m e0 e (SOME (n0, (l1, l2))) :: xs) ss) as (y & Hy & _);
      [split; [exact EL|]; split; [exact Hss|lia]|].
    change (wordSem.stack_size (StackFrame m e0 e (SOME (n0, (l1, l2))) :: xs))
      with (OPTION_MAP2 N.add (OPTION_MAP (N.add 3) m) (wordSem.stack_size xs)) in Hy.
    change (wordSem.stack_size (StackFrame m e0 e NONE :: xs))
      with (OPTION_MAP2 N.add m (wordSem.stack_size xs)).
    pose proof (stack_rel_aux_stack_size _ _ _ _ Hrel') as Hz.
    change (wordSem.stack_size (StackFrame m e0 e NONE :: xs))
      with (OPTION_MAP2 N.add m (wordSem.stack_size xs)) in Hz.
    destruct m as [mv|]; [|discriminate]. destruct (wordSem.stack_size xs) as [z|]; [|discriminate].
    rewrite om_some, om2_some in Hy. rewrite om2_some in Hz |- *. cbn [the] in Hz. cbn [handler_val] in Hz.
    eexists; split; [reflexivity|]. lia.
  - split.
    { pose proof (EVERY_IMP_EVERY_LASTN _ _ _ _ (conj Hsrt EL)) as HE. cbn [EVERY] in HE |- *.
      apply andb_prop in HE as [HE1 HE2]. rewrite HE2, andb_true_r. apply bool_decide_spec in HE1. apply bool_decide_spec. exact HE1. }
    exists ((NONE, (bits, fr)) :: LASTN (wordSem.handler s) astack). split.
    { rewrite DROP_0_eq, N.add_0_r. exact Habs'. }
    split; [|exact Hrel'].
    intros [Hn0 Hhf]. rewrite FLOOKUP_UPDATE, decide_True by reflexivity. f_equal.
    rewrite LENGTH_cons' in Hn0, Hhf.
    destruct (N.eq_dec (n0 + 1) (LENGTH xs + 1)) as [En|En].
    + exfalso. rewrite En, N.sub_diag in Hhf. rewrite EL_0' in Hhf. discriminate.
    + replace (LENGTH xs + 1 - (n0 + 1)) with (LENGTH xs - (n0 + 1) + 1) in Hhf by lia.
      rewrite EL_nth' in Hhf. replace (N.to_nat (LENGTH xs - (n0 + 1) + 1)) with (Datatypes.S (N.to_nat (LENGTH xs - (n0 + 1)))) in Hhf by lia.
      cbn [nth] in Hhf. rewrite <- EL_nth' in Hhf.
      rewrite HEL2 by (split; [lia|exact Hhf]).
      rewrite !LASTN_cons_le by lia. reflexivity.
  - intros n1 v1 Hn1. rewrite lookup_LN in Hn1. discriminate.
Qed.

End RaiseCase.

Lemma isPREFIX_LENGTH' {A} `{EqDecision A} (l1 l2 : list A) : is_true (isPREFIX l1 l2) -> LENGTH l1 <= LENGTH l2.
Proof. intros Hp. apply isPREFIX_iff in Hp as [l ->]. rewrite LENGTH_app'. lia. Qed.

Lemma set_clock_set_clock {a c ffi_t} X Y (t : stackSem.state a c ffi_t) : set_clock Y (set_clock X t) = set_clock Y t.
Proof. destruct t; reflexivity. Qed.

Lemma wev_seq {a c ffi_t} (c1 c2 : wordLang.prog a) (s : wordSem.state a c ffi_t) :
  wordSem.evaluate (wordLang.Seq c1 c2, s) =
  let '(res, s1) := wordSem.evaluate (c1, s) in
  if bool_decide (res = NONE) then wordSem.evaluate (c2, s1) else (res, s1).
Proof. rewrite wordSem.evaluate_eqn. cbn [wordSem.evaluate_body]. rewrite wordSem.fix_clock_evaluate. reflexivity. Qed.

Lemma pac_seq {a} k (c1 c2 : wordLang.prog a) :
  is_true (post_alloc_conventions k (wordLang.Seq c1 c2)) ->
  is_true (post_alloc_conventions k c1) /\ is_true (post_alloc_conventions k c2).
Proof.
  unfold post_alloc_conventions. cbn [wordLang.every_var wordLang.every_stack_var call_arg_convention].
  intros H. to_prop. unfold is_true. rewrite !andb_true_iff. tauto.
Qed.

Section SeqCase.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "Seq" *)
Lemma comp_correct_Seq ac c1 c2 s :
  (forall y, wordSem.eval_lt y (wordLang.Seq c1 c2, s) -> comp_goal ac y) ->
  comp_goal ac (wordLang.Seq c1 c2, s).
Proof.
  intros IH. goal_intro. rewrite wev_seq in Hev.
  destruct (wordSem.evaluate (c1, s)) as [res' s1'] eqn:E1.
  pose proof (wordSem.evaluate_clock _ _ _ _ E1) as [Hc1 Ht1].
  destruct (pac_seq _ _ _ Hpac) as [Hpac1 Hpac2]. cbn [flat_exp_conventions] in Hflat. apply andb_prop in Hflat as [Hfl1 Hfl2].
  cbn [wordLang.max_var] in Hmax. rewrite MAX_lt_iff in Hmax. destruct Hmax as [Hm1 Hm2].
  cbn [comp] in Hcomp.
  destruct (comp ac false c1 (bs, n) (k, (f, f'))) as [q1 [bs1 n1]] eqn:Ec1.
  destruct (comp ac false c2 (bs1, n1) (k, (f, f'))) as [q2 [bs2 n2]] eqn:Ec2.
  injection Hcomp as <- <- <-.
  pose proof (comp_IMP_isPREFIX _ _ _ _ _ _ _ Ec1) as Hp1. pose proof (comp_IMP_isPREFIX _ _ _ _ _ _ _ Ec2) as Hp2.
  cbn [FST fst] in Hp1, Hp2.
  destruct (comp_IMP_LENGTH _ _ _ _ _ _ _ (conj Ec1 Hbs1)) as [HL1 HE1]. cbn [FST SND fst snd] in HL1, HE1.
  cbn [get_labels] in Hlab.
  assert (Hlab1 : get_labels q1 SUBSET loc_check (code t)) by (intros x Hx; apply Hlab; left; exact Hx).
  assert (Hlab2 : get_labels q2 SUBSET loc_check (code t)) by (intros x Hx; apply Hlab; right; exact Hx).
  pose proof H as HS0. sr_destr HS0.
  destruct (IH (c1, s)) with k f f' res' s1' t bs n bs1 n1 q1 lens as (ck & t1 & res1 & Eq1 & HR1).
  { right. split; [reflexivity|]. right. split; [reflexivity|]. cbn [wordSem.psize fst]. lia. }
  { split; [exact E1|]. split; [destruct (bool_decide (res' = NONE)) eqn:Eb; [apply bool_decide_spec in Eb; congruence|injection Hev as <- _; exact Hres]|].
    split; [exact H|]. split; [exact Hpac1|]. split; [exact Hfl1|]. split; [exact Ec1|].
    split; [exact Hbs1|]. split; [exact Hbs2|]. split; [eapply isPREFIX_TRANS; split; eassumption|].
    split; [exact Hlab1|exact Hm1]. }
  destruct (bool_decide (res' = NONE)) eqn:Eb.
  - apply bool_decide_spec in Eb. subst res'.
    destruct (decide (res1 = NONE)) as [->|Hr1].
    + cbn [option_map] in HR1. rewrite bd_neq_false in HR1.
      pose proof (stack_swap.evaluate_stack_swap c1 s) as Hsw. rewrite E1 in Hsw. destruct Hsw as (_ & Hhnd & _).
      pose proof (evaluate_mono _ _ _ _ Eq1) as [Hbm Hcd]. stk_fields.
      pose proof HR1 as HS1. sr_destr HS1.
      destruct (IH (c2, s1')) with k f f' res s1 t1 bs1 n1 bs2 n2 q2 lens as (ck' & t2 & res2 & Eq2 & HR2).
      { destruct (N.lt_ge_cases (wordSem.clock s1') (wordSem.clock s)) as [Hlt|Hge].
        - right. split; [exact Ht1|]. left. exact Hlt.
        - right. split; [exact Ht1|]. right. split; [cbn [snd]; lia|]. cbn [wordSem.psize fst]. lia. }
      { split; [exact Hev|]. split; [exact Hres|]. split; [exact HR1|]. split; [exact Hpac2|]. split; [exact Hfl2|].
        split; [exact Ec2|]. split; [exact HL1|].
        pose proof (isPREFIX_LENGTH' _ _ Hbm) as Hlbm.
        split; [lia|]. split.
        - rewrite <- HE1. eapply isPREFIX_TRANS; split; [exact Hpre|]. apply isPREFIX_DROP. exact Hbm.
        - split; [|exact Hm2]. intros x Hx. apply (loc_check_SUBSET _ _ Hcd), Hlab2, Hx. }
      exists (ck + ck'), t2, res2. split.
      { rewrite ev_seq. rewrite N.add_assoc.
        assert (Hnt : (NONE : option (stackSem.result a)) <> SOME TimeOut) by discriminate.
        pose proof (evaluate_add_clock ck' q1 (set_clock (clock t + ck) t) NONE t1 (conj Eq1 Hnt)) as Ea.
        stk_fields. rewrite set_clock_set_clock in Ea. rewrite Ea. exact Eq2. }
      rewrite Hhnd in HR2. exact HR2.
    + destruct (bool_decide (OPTION_MAP compile_result NONE <> res1)) eqn:Ec;
        [|apply bdf in Ec; exfalso; apply Ec; cbn [option_map]; intros E; apply Hr1; symmetry; exact E].
      destruct HR1 as (-> & Hio & Hslim).
      exists ck, t1, (SOME (Halt (Word (n2w 2)))). split; [rewrite ev_seq, Eq1; reflexivity|].
      rewrite bd_true' by (destruct res as [r|]; [cbn; intros E; injection E as E; apply (compile_result_NOT_2 r Hgd), E|discriminate]).
      split; [reflexivity|]. split.
      * eapply isPREFIX_TRANS; split; [exact Hio|]. eapply clock.evaluate_io_events_mono; exact Hev.
      * eapply stack_max.evaluate_stack_limit_stack_max; split; eassumption.
  - injection Hev as <- <-. exists ck, t1, res1. split; [|exact HR1].
    rewrite ev_seq, Eq1. destruct res1 as [r1|]; [reflexivity|].
    exfalso. apply bdf in Eb.
    destruct (bool_decide (OPTION_MAP compile_result res' <> NONE)) eqn:Ec.
    + destruct HR1 as [HH1 _]. discriminate.
    + apply bdf in Ec. apply Ec. destruct res'; [discriminate|congruence].
Qed.

End SeqCase.

Lemma ev_if {a c ffi_t} cmp r1 ri (c1 c2 : prog a) (X : stackSem.state a c ffi_t) :
  evaluate (If cmp r1 ri c1 c2, X) =
  match stackSem.get_var r1 X, get_var_imm ri X with
  | SOME x, SOME y =>
      match wordSem.word_cmp cmp x y with
      | SOME true => evaluate (c1, X)
      | SOME false => evaluate (c2, X)
      | NONE => (SOME Error, X)
      end
  | _, _ => (SOME Error, X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma pac_if {a} k cmp r1 ri (c1 c2 : wordLang.prog a) :
  is_true (post_alloc_conventions k (wordLang.If cmp r1 ri c1 c2)) ->
  EVEN r1 /\ (forall r, ri = Reg r -> EVEN r) /\
  is_true (post_alloc_conventions k c1) /\ is_true (post_alloc_conventions k c2).
Proof.
  unfold post_alloc_conventions. cbn [wordLang.every_var wordLang.every_stack_var call_arg_convention].
  intros H. unfold is_true in *. rewrite !andb_true_iff in *.
  split; [apply is_phy_var_EVEN; unfold is_true; tauto|].
  split; [intros r ->; apply is_phy_var_EVEN; cbn [wordLang.every_var_imm] in H; unfold is_true; tauto|]. tauto.
Qed.

Section IfCase.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(** Galette-only: the two branches of [If] by the induction hypothesis. *)
Lemma if_ih ac c1 c2 s k f f' lens (T : stackSem.state a c ffi_t) bs n bs1 n1 bs2 n2 q1 q2 (b : bool) res s1 :
  comp_goal ac (c1, s) -> comp_goal ac (c2, s) ->
  wordSem.evaluate (if b then c1 else c2, s) = (res, s1) -> res <> SOME wordSem.Error ->
  state_rel ac k f f' s T lens 0 ->
  is_true (post_alloc_conventions k c1) -> is_true (post_alloc_conventions k c2) ->
  is_true (flat_exp_conventions c1) -> is_true (flat_exp_conventions c2) ->
  comp ac false c1 (bs, n) (k, (f, f')) = (q1, (bs1, n1)) ->
  comp ac false c2 (bs1, n1) (k, (f, f')) = (q2, (bs2, n2)) ->
  LENGTH (append bs) <= n -> n - LENGTH (append bs) <= LENGTH (bitmaps T) ->
  is_true (isPREFIX (append bs2) (DROP (n - LENGTH (append bs)) (bitmaps T))) ->
  get_labels q1 SUBSET loc_check (code T) -> get_labels q2 SUBSET loc_check (code T) ->
  wordLang.max_var c1 < 2 * f' + 2 * k -> wordLang.max_var c2 < 2 * f' + 2 * k ->
  exists ck (t1 : stackSem.state a c ffi_t) res1,
    evaluate (if b then q1 else q2, set_clock (clock T + ck) T) = (res1, t1) /\
    comp_res ac k f f' s res s1 t1 res1 lens.
Proof.
  intros IH1 IH2 Hev Hres H Hp1 Hp2 Hf1 Hf2 Ec1 Ec2 Hb1 Hb2 Hpre Hl1 Hl2 Hm1 Hm2.
  pose proof (comp_IMP_isPREFIX _ _ _ _ _ _ _ Ec2) as Hp. cbn [FST fst] in Hp.
  destruct (comp_IMP_LENGTH _ _ _ _ _ _ _ (conj Ec1 Hb1)) as [HL1 HE1]. cbn [FST SND fst snd] in HL1, HE1.
  destruct b.
  - apply (IH1 k f f' res s1 T bs n bs1 n1 q1 lens).
    split; [exact Hev|]. split; [exact Hres|]. split; [exact H|]. split; [exact Hp1|]. split; [exact Hf1|].
    split; [exact Ec1|]. split; [exact Hb1|]. split; [exact Hb2|].
    split; [eapply isPREFIX_TRANS; split; eassumption|]. split; [exact Hl1|exact Hm1].
  - apply (IH2 k f f' res s1 T bs1 n1 bs2 n2 q2 lens).
    split; [exact Hev|]. split; [exact Hres|]. split; [exact H|]. split; [exact Hp2|]. split; [exact Hf2|].
    split; [exact Ec2|]. split; [exact HL1|]. split; [lia|].
    split; [rewrite <- HE1; exact Hpre|]. split; [exact Hl2|exact Hm2].
Qed.

End IfCase.

Section IfCase2.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "If" *)
Lemma comp_correct_If ac cmp r1 ri c1 c2 s :
  (forall y, wordSem.eval_lt y (wordLang.If cmp r1 ri c1 c2, s) -> comp_goal ac y) ->
  comp_goal ac (wordLang.If cmp r1 ri c1 c2, s).
Proof.
  intros IH. goal_intro.
  assert (IH1 : comp_goal ac (c1, s)) by (apply IH; right; split; [reflexivity|]; right; split; [reflexivity|]; cbn; lia).
  assert (IH2 : comp_goal ac (c2, s)) by (apply IH; right; split; [reflexivity|]; right; split; [reflexivity|]; cbn; lia).
  wev Hev.
  destruct (wordSem.get_var r1 s) as [x|] eqn:Ex; [|injection Hev as <- _; congruence].
  destruct (wordSem.get_var_imm ri s) as [y|] eqn:Ey; [|injection Hev as <- _; congruence].
  destruct (wordSem.word_cmp cmp x y) as [b|] eqn:Ecmp; [|injection Hev as <- _; congruence].
  assert (Hevb : wordSem.evaluate (if b then c1 else c2, s) = (res, s1)) by (destruct b; exact Hev).
  destruct (pac_if _ _ _ _ _ _ Hpac) as (He1 & Hei & Hp1 & Hp2).
  cbn [flat_exp_conventions] in Hflat. apply andb_prop in Hflat as [Hf1 Hf2].
  cbn [wordLang.max_var] in Hmax. rewrite max3_lt_iff in Hmax. destruct Hmax as (Hmr & Hm1 & Hm2).
  cbn [comp] in Hcomp.
  destruct (wReg1 r1 (k, (f, f'))) as [x1 r'] eqn:Ew1.
  destruct (comp ac false c1 (bs, n) (k, (f, f'))) as [q1 [bs1 n1]] eqn:Ec1.
  destruct (comp ac false c2 (bs1, n1) (k, (f, f'))) as [q2 [bs2 n2]] eqn:Ec2.
  assert (Hlab' : forall X : prog a, get_labels X SUBSET loc_check (code t) ->
            forall t', is_true (sptree.subspt (code t) (code t')) -> get_labels X SUBSET loc_check (code t'))
    by (intros X HX t' Hs z Hz; apply (loc_check_SUBSET _ _ Hs), HX, Hz).
  destruct ri as [r|imm].
  - destruct (wReg2 r (k, (f, f'))) as [x2 nn] eqn:Ew2. injection Hcomp as <- <- <-.
    cbn [wordSem.get_var_imm] in Ey.
    destruct (evaluate_wStackLoad_wReg1 ac k f f' r1 x1 r' s t lens x) as (T1 & E1 & Hc1 & HT1 & HL1 & HS1 & HB1 & HR1 & Hr'k & G1);
      [split; [exact Ew1|]; split; [exact He1|]; split; [exact Ex|exact H]|].
    destruct (evaluate_wStackLoad_wReg2 ac k f f' r x2 nn s T1 lens y) as (T2 & E2 & Hc2 & HB2 & HT2 & HL2 & HS2 & HR2 & _ & G2);
      [split; [exact Ew2|]; split; [apply Hei; reflexivity|]; split; [exact Ey|exact HT1]|].
    rewrite get_labels_wStackLoad in Hlab. cbn [get_labels] in Hlab.
    pose proof (evaluate_mono _ _ _ _ E1) as [_ Hcd1]. pose proof (evaluate_mono _ _ _ _ E2) as [_ Hcd2].
    edestruct (if_ih ac c1 c2 s k f f' lens T2 bs n bs1 n1 bs2 n2 q1 q2 b res s1 IH1 IH2 Hevb Hres HT2 Hp1 Hp2 Hf1 Hf2 Ec1 Ec2 Hbs1)
      as (ck & t1 & res1 & Eq & HR).
    + rewrite <- HB2, HB1. exact Hbs2.
    + rewrite <- HB2, HB1. exact Hpre.
    + apply (Hlab' _ (fun x0 Hx0 => Hlab x0 (or_introl Hx0))). apply (subspt_trans _ _ _ (conj Hcd1 Hcd2)).
    + apply (Hlab' _ (fun x0 Hx0 => Hlab x0 (or_intror Hx0))). apply (subspt_trans _ _ _ (conj Hcd1 Hcd2)).
    + exact Hm1.
    + exact Hm2.
    + exists ck, t1, res1. split; [|exact HR].
      rewrite wStackLoad_append, (load_clock _ _ _ _ _ E1), (load_clock _ _ _ _ _ E2), ev_if.
      unfold stackSem.get_var in *. stk_fields. rewrite (HR2 r' Hr'k), G1. cbn [get_var_imm]. unfold stackSem.get_var. stk_fields.
      rewrite G2, Ecmp. rewrite Hc1, Hc2 in *. destruct b; exact Eq.
  - cbn [wordSem.get_var_imm] in Ey. injection Ey as <-.
    destruct (valid_imm ac (inr cmp) imm) eqn:Ev; injection Hcomp as <- <- <-.
    + destruct (evaluate_wStackLoad_wReg1 ac k f f' r1 x1 r' s t lens x) as (T1 & E1 & Hc1 & HT1 & HL1 & HS1 & HB1 & HR1 & Hr'k & G1);
        [split; [exact Ew1|]; split; [exact He1|]; split; [exact Ex|exact H]|].
      rewrite get_labels_wStackLoad in Hlab. cbn [get_labels] in Hlab.
      pose proof (evaluate_mono _ _ _ _ E1) as [_ Hcd1].
      edestruct (if_ih ac c1 c2 s k f f' lens T1 bs n bs1 n1 bs2 n2 q1 q2 b res s1 IH1 IH2 Hevb Hres HT1 Hp1 Hp2 Hf1 Hf2 Ec1 Ec2 Hbs1)
        as (ck & t1 & res1 & Eq & HR).
      * rewrite HB1. exact Hbs2.
      * rewrite HB1. exact Hpre.
      * apply (Hlab' _ (fun x0 Hx0 => Hlab x0 (or_introl Hx0))). exact Hcd1.
      * apply (Hlab' _ (fun x0 Hx0 => Hlab x0 (or_intror Hx0))). exact Hcd1.
      * exact Hm1.
      * exact Hm2.
      * exists ck, t1, res1. split; [|exact HR].
        rewrite (load_clock _ _ _ _ _ E1), ev_if.
        unfold stackSem.get_var in *. stk_fields. rewrite G1. cbn [get_var_imm].
        rewrite Ecmp. rewrite Hc1 in *. destruct b; exact Eq.
    + cbn [fst] in *.
      destruct (evaluate_const_inst ac k f f' s t lens 0 imm H) as (T0 & E0 & Hc0 & HT0 & HL0 & HS0' & G0).
      destruct (evaluate_wStackLoad_wReg1 ac k f f' r1 x1 r' s T0 lens x) as (T1 & E1 & Hc1 & HT1 & HL1 & HS1 & HB1 & HR1 & Hr'k & G1);
        [split; [exact Ew1|]; split; [exact He1|]; split; [exact Ex|exact HT0]|].
      cbn [get_labels] in Hlab. rewrite get_labels_wStackLoad in Hlab. cbn [get_labels] in Hlab.
      pose proof (evaluate_mono _ _ _ _ E0) as [HB0 Hcd0]. pose proof (evaluate_mono _ _ _ _ E1) as [_ Hcd1].
      assert (HB0' : bitmaps T0 = bitmaps t) by (rewrite ev_inst, inst_const in E0; injection E0 as <-; reflexivity).
      edestruct (if_ih ac c1 c2 s k f f' lens T1 bs n bs1 n1 bs2 n2 q1 q2 b res s1 IH1 IH2 Hevb Hres HT1 Hp1 Hp2 Hf1 Hf2 Ec1 Ec2 Hbs1)
        as (ck & t1 & res1 & Eq & HR).
      * rewrite HB1, HB0'. exact Hbs2.
      * rewrite HB1, HB0'. exact Hpre.
      * apply (Hlab' _ (fun x0 Hx0 => Hlab x0 (or_intror (or_introl Hx0)))). apply (subspt_trans _ _ _ (conj Hcd0 Hcd1)).
      * apply (Hlab' _ (fun x0 Hx0 => Hlab x0 (or_intror (or_intror Hx0)))). apply (subspt_trans _ _ _ (conj Hcd0 Hcd1)).
      * exact Hm1.
      * exact Hm2.
      * exists ck, t1, res1. split; [|exact HR].
        rewrite ev_seq, evaluate_const_inst_clock, E0. cbn [PAIR_MAP I FST SND fst snd].
        rewrite (load_clock _ _ _ _ _ E1), ev_if.
        unfold stackSem.get_var in *. stk_fields. rewrite G1. cbn [get_var_imm]. unfold stackSem.get_var. stk_fields.
        pose proof (HR1 (k + 1) ltac:(lia)) as G0'. unfold stackSem.get_var in G0'. rewrite G0', G0.
        rewrite Ecmp. rewrite Hc0, Hc1 in *. destruct b; exact Eq.
Qed.

End IfCase2.

Lemma ev_codebufferwrite {a c ffi_t} r1 r2 (X : stackSem.state a c ffi_t) :
  evaluate (CodeBufferWrite r1 r2, X) =
  match stackSem.get_var r1 X, stackSem.get_var r2 X with
  | SOME (Word w1), SOME (Word w2) =>
      match wordSem.buffer_write (code_buffer X) w1 (w2w w2) with
      | SOME new_cb => (NONE, set_code_buffer new_cb X)
      | _ => (SOME Error, X)
      end
  | _, _ => (SOME Error, X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_databufferwrite {a c ffi_t} r1 r2 (X : stackSem.state a c ffi_t) :
  evaluate (DataBufferWrite r1 r2, X) =
  if negb (use_stack X) then (SOME Error, X) else
  match stackSem.get_var r1 X, stackSem.get_var r2 X with
  | SOME (Word w1), SOME (Word w2) =>
      match wordSem.buffer_write (data_buffer X) w1 w2 with
      | SOME new_db => (NONE, set_data_buffer new_db X)
      | _ => (SOME Error, X)
      end
  | _, _ => (SOME Error, X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Section BufferCases.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

Lemma load12_clock0 ac k f f' s t lens r2 r3 l l' n2 n3 w2 w3 (P : prog a) :
  state_rel ac k f f' s t lens 0 ->
  wReg1 r2 (k, (f, f')) = (l, n2) -> EVEN r2 -> wordSem.get_var r2 s = SOME w2 ->
  wReg2 r3 (k, (f, f')) = (l', n3) -> EVEN r3 -> wordSem.get_var r3 s = SOME w3 ->
  exists t1, evaluate (wStackLoad (l ++ l') P, t) = evaluate (P, t1) /\ state_rel ac k f f' s t1 lens 0 /\
    stackSem.get_var n2 t1 = SOME w2 /\ stackSem.get_var n3 t1 = SOME w3 /\
    LENGTH (stackSem.stack t1) = LENGTH (stackSem.stack t) /\ stack_space t1 = stack_space t.
Proof.
  intros H Hw2 He2 Hg2 Hw3 He3 Hg3.
  destruct (load12 ac k f f' s t lens r2 r3 l l' n2 n3 w2 w3 P H Hw2 He2 Hg2 Hw3 He3 Hg3) as (t1 & E & H1 & G2 & G3 & L1 & S1 & _).
  exists t1. auto 10.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "CodeBufferWrite" *)
Lemma comp_correct_CodeBufferWrite ac r1 r2 s : comp_goal ac (wordLang.CodeBufferWrite r1 r2, s).
Proof.
  goal_intro. wev Hev.
  destruct (wordSem.get_var r1 s) as [[w1|]|] eqn:E1; try (injection Hev as <- _; congruence).
  destruct (wordSem.get_var r2 s) as [[w2|]|] eqn:E2; try (injection Hev as <- _; congruence).
  destruct (wordSem.buffer_write (wordSem.code_buffer s) w1 (w2w w2)) as [cb|] eqn:Eb; injection Hev as <- <-; [|congruence].
  pac Hpac.
  cbn [comp] in Hcomp. destruct (wReg1 r1 (k, (f, f'))) as [l1 n1'] eqn:Ew1. destruct (wReg2 r2 (k, (f, f'))) as [l2 n2'] eqn:Ew2.
  injection Hcomp as <- <- <-.
  destruct (load12 ac k f f' s t lens r1 r2 l1 l2 n1' n2' _ _ (CodeBufferWrite n1' n2') H Ew1 ltac:(assumption) E1 Ew2 ltac:(assumption) E2)
    as (t1 & E & HT1 & G1 & G2 & _).
  exists 0. rewrite set_clock_add0, E, ev_codebufferwrite, G1, G2.
  pose proof HT1 as HS0. sr_destr HS0. rewrite Hcb, Eb.
  eexists; eexists; split; [reflexivity|]. cbn [option_map]. rewrite bd_neq_false.
  sr_split; ws_fields; stk_fields; try assumption; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "DataBufferWrite" *)
Lemma comp_correct_DataBufferWrite ac r1 r2 s : comp_goal ac (wordLang.DataBufferWrite r1 r2, s).
Proof.
  goal_intro. wev Hev.
  destruct (wordSem.get_var r1 s) as [[w1|]|] eqn:E1; try (injection Hev as <- _; congruence).
  destruct (wordSem.get_var r2 s) as [[w2|]|] eqn:E2; try (injection Hev as <- _; congruence).
  destruct (wordSem.buffer_write (wordSem.data_buffer s) w1 w2) as [db|] eqn:Eb; injection Hev as <- <-; [|congruence].
  pac Hpac.
  cbn [comp] in Hcomp. destruct (wReg1 r1 (k, (f, f'))) as [l1 n1'] eqn:Ew1. destruct (wReg2 r2 (k, (f, f'))) as [l2 n2'] eqn:Ew2.
  injection Hcomp as <- <- <-.
  destruct (load12 ac k f f' s t lens r1 r2 l1 l2 n1' n2' _ _ (DataBufferWrite n1' n2') H Ew1 ltac:(assumption) E1 Ew2 ltac:(assumption) E2)
    as (t1 & E & HT1 & G1 & G2 & _).
  exists 0. rewrite set_clock_add0, E, ev_databufferwrite.
  pose proof HT1 as HS0. sr_destr HS0. unfold is_true in Hus. rewrite Hus. cbn [negb]. rewrite G1, G2.
  rewrite Hdb, Eb.
  eexists; eexists; split; [reflexivity|]. cbn [option_map]. rewrite bd_neq_false.
  assert (Hbw : LENGTH (wordSem.buffer_buffer db) + wordSem.space_left db =
                LENGTH (wordSem.buffer_buffer (wordSem.data_buffer s)) + wordSem.space_left (wordSem.data_buffer s)).
  { unfold wordSem.buffer_write in Eb. destruct (_ && _) eqn:Ec; [|discriminate]. apply andb_prop in Ec as [_ Ec].
    apply N.ltb_lt in Ec. injection Eb as <-. cbn. rewrite LENGTH_app'. cbn [LENGTH]. lia. }
  sr_split; ws_fields; stk_fields; try assumption; try reflexivity. lia.
Qed.

End BufferCases.

Lemma ev_ffi {a c ffi_t} i ptr len ptr2 len2 ret (X : stackSem.state a c ffi_t) :
  evaluate (FFI i ptr len ptr2 len2 ret, X) =
  match stackSem.get_var len X, stackSem.get_var ptr X, stackSem.get_var len2 X, stackSem.get_var ptr2 X with
  | SOME (Word w), SOME (Word w2), SOME (Word w3), SOME (Word w4) =>
      match read_bytearray w2 (w2n w) (wordSem.mem_load_byte_aux (memory X) (mdomain X) (be X)),
            read_bytearray w4 (w2n w3) (wordSem.mem_load_byte_aux (memory X) (mdomain X) (be X)) with
      | SOME bytes, SOME bytes2 =>
          match call_FFI (ffi X) (ExtCall i) bytes bytes2 with
          | FFI_final outcome => (SOME (FinalFFI outcome), X)
          | FFI_return new_ffi new_bytes =>
              let new_m := wordSem.write_bytearray w4 new_bytes (memory X) (mdomain X) (be X) in
              (NONE, set_ffi new_ffi (set_fp_regs FEMPTY
                       (set_regs (DRESTRICT (regs X) (ffi_save_regs X)) (set_memory new_m X))))
          end
      | _, _ => (SOME Error, X)
      end
  | _, _, _, _ => (SOME Error, X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Section FFICase.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "FFI" *)
Lemma comp_correct_FFI ac i p1 l1 p2 l2 names s : comp_goal ac (wordLang.FFI i p1 l1 p2 l2 names, s).
Proof.
  goal_intro. wev Hev.
  unfold post_alloc_conventions in Hpac. cbn [wordLang.every_var wordLang.every_stack_var call_arg_convention] in Hpac.
  apply andb_prop in Hpac as [Hpac Hconv]. apply andb_prop in Hpac as [_ Hst]. to_prop. subst p1 l1 p2 l2.
  cbn [comp] in Hcomp. injection Hcomp as <- <- <-.
  pose proof H as HS0. sr_destr HS0.
  assert (G : forall x w, wordSem.get_var (2 * x) s = SOME w -> x < k -> FLOOKUP (regs t) x = SOME w).
  { intros x w Hg Hx. apply (state_rel_get_var_imp ac k f f' s t lens 0 x w). auto. }
  exists 0. rewrite set_clock_add0, ev_ffi. unfold stackSem.get_var.
  replace (4 DIV 2) with 2 by reflexivity. replace (2 DIV 2) with 1 by reflexivity.
  replace (8 DIV 2) with 4 by reflexivity. replace (6 DIV 2) with 3 by reflexivity.
  destruct (wordSem.get_var 4 s) as [[w|]|] eqn:E4; try (injection Hev as <- _; congruence).
  destruct (wordSem.get_var 2 s) as [[w2|]|] eqn:E2; try (injection Hev as <- _; congruence).
  destruct (wordSem.get_var 8 s) as [[w3|]|] eqn:E8; try (injection Hev as <- _; congruence).
  destruct (wordSem.get_var 6 s) as [[w4|]|] eqn:E6; try (injection Hev as <- _; congruence).
  rewrite (G 2 (Word w)) by (exact E4 || lia). rewrite (G 1 (Word w2)) by (exact E2 || lia).
  rewrite (G 4 (Word w3)) by (exact E8 || lia). rewrite (G 3 (Word w4)) by (exact E6 || lia).
  destruct (wordSem.cut_env names (wordSem.locals s)) as [env|] eqn:Ecut; [|injection Hev as <- _; congruence].
  rewrite Hmem, Hmd, Hbe, Hffi.
  destruct (read_bytearray w2 (w2n w) _) as [bytes|]; [|injection Hev as <- _; congruence].
  destruct (read_bytearray w4 (w2n w3) _) as [bytes2|]; [|injection Hev as <- _; congruence].
  destruct (call_FFI (wordSem.ffi s) (ExtCall i) bytes bytes2) as [nf nb|o] eqn:Ef; injection Hev as <- <-.
  - eexists; eexists; split; [reflexivity|]. cbn [option_map]. rewrite bd_neq_false. cbv zeta.
    sr_split; ws_fields; stk_fields; try assumption; try reflexivity.
    + unfold wordSem.cut_env, wordSem.cut_envs, wordSem.cut_names in Ecut.
      destruct (classical_dec _); [|discriminate]. destruct (classical_dec _); [|discriminate].
      injection Ecut as <-. apply wf_union. split; apply wf_inter.
    + intros n0 v Hn0. unfold wordSem.cut_env, wordSem.cut_envs, wordSem.cut_names in Ecut.
      destruct (classical_dec _); [|discriminate]. destruct (classical_dec _); [|discriminate].
      injection Ecut as <-. rewrite lookup_union, !lookup_inter in Hn0.
      assert (Hdm : exists u, lookup n0 (FST names) = SOME u \/ lookup n0 (SND names) = SOME u).
      { destruct (lookup n0 (wordSem.locals s)); [|destruct (lookup n0 (SND names)), (lookup n0 (FST names)); discriminate].
        destruct (lookup n0 (SND names)) eqn:E1; [eauto|]. destruct (lookup n0 (FST names)) eqn:E3; [eauto|discriminate]. }
      assert (Hl : lookup n0 (wordSem.locals s) = SOME v).
      { destruct (lookup n0 (wordSem.locals s)); [|destruct (lookup n0 (SND names)), (lookup n0 (FST names)); discriminate].
        destruct (lookup n0 (SND names)); [exact Hn0|]. destruct (lookup n0 (FST names)); [exact Hn0|discriminate]. }
      destruct (Hloc n0 v Hl) as [He Hr]. split; [exact He|].
      destruct Hdm as [u Hu].
      assert (Hk2 : 2 * k <= n0).
      { apply N.leb_le. apply (every_name_dom _ _ _ Hst). destruct Hu as [Hu|Hu]; [left|right]; apply domain_lookup; eauto. }
      replace (n0 DIV 2 <? k) with false in Hr |- * by (symmetry; apply N.ltb_ge; apply N.div_le_lower_bound; lia).
      exact Hr.
  - eexists; eexists; split; [reflexivity|]. cbn [option_map compile_result]. rewrite bd_neq_false.
    unfold wordSem.flush_state. ws_fields. split; [symmetry; exact Hffi|exact Hclock].
Qed.

End FFICase.

Section ShareInstCase.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "ShareInst" *)
Lemma comp_correct_ShareInst ac op v exp s : comp_goal ac (wordLang.ShareInst op v exp, s).
Proof.
  goal_intro.
  destruct (flat_exp_conventions_ShareInst_exp_simp op v exp Hflat) as [[ad ->]|(ad & off & ->)].
  - rewrite evaluate_ShareInst_Var_eq_Op_Add in Hev.
    unfold post_alloc_conventions in Hpac. cbn [wordLang.every_var wordLang.every_stack_var call_arg_convention wordLang.every_var_exp] in Hpac.
    winst_prep. cbn [wordLang.max_var wordLang.max_var_exp] in Hmax. rewrite MAX_lt_iff in Hmax. destruct Hmax as [Hm1 Hm2].
    cbn [comp wordLang.exp_to_addr] in Hcomp. injection Hcomp as <- <- <-.
    rewrite (even_div2 v ltac:(assumption)), (even_div2 ad ltac:(assumption)) in Hev |- *.
    destruct (evaluate_ShareInst_correct_lemma ac k f f' s t lens op (v / 2) (ad / 2) (n2w 0) res s1)
      as (ck & t1 & E & HR).
    { split; [exact Hev|]. split; [exact Hres|]. split; [exact H|]. split; [apply N.Div0.div_lt_upper_bound; lia|apply N.Div0.div_lt_upper_bound; lia]. }
    exists ck, t1, (OPTION_MAP compile_result res). rewrite N.add_comm. split; [exact E|]. rewrite bd_neq_false.
    destruct HR as [(-> & HR)|(fv & -> & HR1 & HR2)]; [exact HR|]. split; assumption.
  - unfold post_alloc_conventions in Hpac. cbn [wordLang.every_var wordLang.every_stack_var call_arg_convention wordLang.every_var_exp] in Hpac.
    cbn [EVERY wordLang.every_var_exp] in Hpac.
    winst_prep. cbn [wordLang.max_var wordLang.max_var_exp MAX_LIST List.map] in Hmax. rewrite !MAX_lt_iff in Hmax.
    cbn [comp wordLang.exp_to_addr] in Hcomp. injection Hcomp as <- <- <-.
    rewrite (even_div2 v ltac:(assumption)), (even_div2 ad ltac:(assumption)) in Hev |- *.
    destruct (evaluate_ShareInst_correct_lemma ac k f f' s t lens op (v / 2) (ad / 2) off res s1)
      as (ck & t1 & E & HR).
    { split; [exact Hev|]. split; [exact Hres|]. split; [exact H|]. split; apply N.Div0.div_lt_upper_bound; lia. }
    exists ck, t1, (OPTION_MAP compile_result res). rewrite N.add_comm. split; [exact E|]. rewrite bd_neq_false.
    destruct HR as [(-> & HR)|(fv & -> & HR1 & HR2)]; [exact HR|]. split; assumption.
Qed.

End ShareInstCase.

Lemma cut_env_lookup {a} (names : wordLang.cutsets) (l env : num_map (word_loc a)) n v :
  wordSem.cut_env names l = SOME env -> lookup n env = SOME v ->
  lookup n l = SOME v /\ (n IN domain (FST names) \/ n IN domain (SND names)).
Proof.
  unfold wordSem.cut_env, wordSem.cut_envs, wordSem.cut_names. intros Hc Hn.
  destruct (classical_dec _); [|discriminate]. destruct (classical_dec _); [|discriminate].
  injection Hc as <-. rewrite lookup_union, !lookup_inter in Hn.
  destruct (lookup n l) eqn:El; [|destruct (lookup n (SND names)), (lookup n (FST names)); discriminate].
  destruct (lookup n (SND names)) eqn:E1.
  - injection Hn as <-. split; [reflexivity|right; apply domain_lookup; eauto].
  - destruct (lookup n (FST names)) eqn:E2; [|discriminate]. injection Hn as <-.
    split; [reflexivity|left; apply domain_lookup; eauto].
Qed.

Lemma cut_env_wf {a} (names : wordLang.cutsets) (l env : num_map (word_loc a)) :
  wordSem.cut_env names l = SOME env -> sptree.wf env.
Proof.
  unfold wordSem.cut_env, wordSem.cut_envs, wordSem.cut_names. intros Hc.
  destruct (classical_dec _); [|discriminate]. destruct (classical_dec _); [|discriminate].
  injection Hc as <-. apply wf_union. split; apply wf_inter.
Qed.

Lemma ev_install {a c ffi_t} ptr len dptr dlen ret (X : stackSem.state a c ffi_t) :
  evaluate (Install ptr len dptr dlen ret, X) =
  match stackSem.get_var ptr X, stackSem.get_var len X, stackSem.get_var dptr X, stackSem.get_var dlen X with
  | SOME (Word w1), SOME (Word w2), SOME (Word w3), SOME (Word w4) =>
      let '(cfg, (progs, bm)) := compile_oracle X 0 in
      match wordSem.buffer_flush (code_buffer X) w1 w2,
            (if use_stack X then wordSem.buffer_flush (data_buffer X) w3 w4
             else SOME (bm, data_buffer X)) with
      | SOME (bytes, cb), SOME (data, db) =>
          let new_oracle := shift_seq 1 (compile_oracle X) in
          match compile X cfg progs, progs with
          | SOME (bytes', cfg'), (k, prog0) :: _ =>
              if andb (andb (bool_decide (bytes = bytes')) (bool_decide (data = bm)))
                      ⌜FST (new_oracle 0) = cfg'⌝ then
                (NONE, set_compile_oracle new_oracle
                    (set_fp_regs FEMPTY
                      (set_regs (DRESTRICT (regs X) (ffi_save_regs X) |+ (ptr, Loc k 0))
                        (set_code (sptree.union (code X) (sptree.fromAList progs))
                          (set_data_buffer db
                            (set_code_buffer cb
                              (set_bitmaps (bitmaps X ++ bm) X)))))))
              else (SOME Error, X)
          | _, _ => (SOME Error, X)
          end
      | _, _ => (SOME Error, X)
      end
  | _, _, _, _ => (SOME Error, X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Section InstallCase.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "Install" *)
Lemma comp_correct_Install ac p1 l1 p2 l2 names s : comp_goal ac (wordLang.Install p1 l1 p2 l2 names, s).
Proof.
  goal_intro. wev Hev.
  destruct (wordSem.cut_env names (wordSem.locals s)) as [env|] eqn:Ecut; [|injection Hev as <- _; congruence].
  destruct (wordSem.get_var p1 s) as [[w1|]|] eqn:E1; try (injection Hev as <- _; congruence).
  destruct (wordSem.get_var l1 s) as [[w2|]|] eqn:E2; try (injection Hev as <- _; congruence).
  destruct (wordSem.get_var p2 s) as [[w3|]|] eqn:E3; try (injection Hev as <- _; congruence).
  destruct (wordSem.get_var l2 s) as [[w4|]|] eqn:E4; try (injection Hev as <- _; congruence).
  destruct (wordSem.compile_oracle s 0) as [[bm0 cfg0] progs] eqn:Eo.
  destruct (wordSem.buffer_flush (wordSem.code_buffer s) w1 w2) as [[bytes cb]|] eqn:Ecb; [|injection Hev as <- _; congruence].
  destruct (wordSem.buffer_flush (wordSem.data_buffer s) w3 w4) as [[data db]|] eqn:Edb; [|injection Hev as <- _; congruence].
  cbv zeta in Hev.
  destruct (wordSem.compile s (bm0, cfg0) progs) as [[bytes' [data' cfg']]|] eqn:Ec; [|injection Hev as <- _; congruence].
  destruct progs as [|[k' prog'] progs]; [injection Hev as <- _; congruence|].
  destruct (_ && _ && _) eqn:Eb; [|injection Hev as <- _; congruence].
  injection Hev as <- <-.
  apply andb_prop in Eb as [Eb Eo1]. apply andb_prop in Eb as [Eby Eda].
  apply bool_decide_spec in Eby, Eda, Eo1. subst bytes' data'.
  unfold shift_seq in Eo1. cbn [N.add] in Eo1.
  unfold post_alloc_conventions in Hpac. cbn [wordLang.every_var wordLang.every_stack_var call_arg_convention] in Hpac.
  apply andb_prop in Hpac as [Hpac Hconv]. apply andb_prop in Hpac as [Hpac Hst].
  apply andb_prop in Hpac as [Hpac _]. apply andb_prop in Hpac as [Hpac He4]. apply andb_prop in Hpac as [Hpac He3].
  apply is_phy_var_EVEN in He3, He4. apply andb_prop in Hconv as [Hc1 Hc2]. apply N.eqb_eq in Hc1, Hc2. subst p1 l1.
  cbn [comp] in Hcomp. destruct (wReg1 p2 (k, (f, f'))) as [l3 r3] eqn:Ew3. destruct (wReg2 l2 (k, (f, f'))) as [l4 r4] eqn:Ew4.
  injection Hcomp as <- <- <-. replace (2 DIV 2) with 1 by reflexivity. replace (4 DIV 2) with 2 by reflexivity.
  destruct (load12 ac k f f' s t lens p2 l2 l3 l4 r3 r4 _ _ (Install 1 2 r3 r4 0) H Ew3 He3 E3 Ew4 He4 E4)
    as (T & ET & HT & G3 & G4 & LT & ST & _).
  pose proof HT as HS0. sr_destr HS0.
  assert (G1 : FLOOKUP (regs T) 1 = SOME (Word w1)) by (apply (state_rel_get_var_imp ac k f f' s T lens 0 1); split; [exact HT|]; split; [exact E1|lia]).
  assert (G2 : FLOOKUP (regs T) 2 = SOME (Word w2)) by (apply (state_rel_get_var_imp ac k f f' s T lens 0 2); split; [exact HT|]; split; [exact E2|lia]).
  (* the stackLang oracle and compiler *)
  destruct (compile_word_to_stack ac false k ((k', prog') :: progs) (Nil, bm0)) as [progs2 [fs [bm1 n1]]] eqn:Ecw.
  pose proof (MAP_FST_compile_word_to_stack _ _ _ _ _ _ _ Ecw) as HMF.
  destruct progs2 as [|[k2 p2'] progs2]; [discriminate|]. injection HMF as Ek2 HMF. subst k2.
  rewrite Hcomp in Ec. cbv beta iota in Ec. rewrite Ecw in Ec.
  destruct (compile T cfg0 ((k', p2') :: progs2)) as [[bytesS cfgS]|] eqn:EcS; [|discriminate].
  cbn [option_map] in Ec. injection Ec as <- <- <-.
  assert (HL0 : LENGTH (append (@Nil (word a))) <= bm0) by (change (LENGTH (append (@Nil (word a)))) with 0; lia).
  destruct (compile_word_to_stack_IMP_LENGTH _ _ _ _ _ _ _ _ _ _ (conj Ecw HL0)) as [HLn0 HLn1].
  change (LENGTH (append (@Nil (word a)))) with 0 in HLn1.
  assert (Hcon0 := Hcon 0). rewrite Eo in Hcon0. destruct Hcon0 as (Hpa0 & Hfl0 & Hrs0 & Hsc0 & Hbm0).
  specialize (Hbm0 eq_refl).
  exists 0. rewrite set_clock_add0, ET, ev_install. unfold stackSem.get_var in *. rewrite G1, G2, G3, G4.
  rewrite Hco. cbv beta. rewrite Eo. rewrite Ecw. cbv beta iota zeta.
  rewrite Hcb, Ecb. unfold is_true in Hus. rewrite Hus, Hdb, Edb. rewrite EcS.
  destruct (wordSem.compile_oracle s 1) as [[bm2 cfg2] progs3] eqn:Eo1'. cbn [FST fst] in Eo1. injection Eo1 as -> ->.
  match goal with |- exists _ _, (if ?b then _ else _) = _ /\ _ => replace b with true end.
  2:{ symmetry. apply andb_true_iff. split; [apply andb_true_iff; split|]; apply bool_decide_spec; [reflexivity|reflexivity|].
      unfold shift_seq. cbv beta. replace (0 + 1) with 1 by reflexivity. rewrite Eo1'.
      destruct (compile_word_to_stack ac false k progs3 (Nil, n1)) as [? [? ?]]. reflexivity. }
  eexists; eexists; split; [reflexivity|]. cbn [option_map]. rewrite bd_neq_false.
  sr_split; ws_fields; stk_fields; try assumption; try reflexivity.
  - intros n0. unfold shift_seq. pose proof (Hcon (n0 + 1)) as Hc.
    destruct (wordSem.compile_oracle s (n0 + 1)) as [[b0 c0'] p0] eqn:Eon. destruct Hc as (A1 & A2 & A3 & A4 & _).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. intros ->.
    replace (0 + 1) with 1 in Eon by reflexivity. rewrite Eo1' in Eon. injection Eon as <- _ _.
    rewrite LENGTH_app'. lia.
  - rewrite !domain_union, Hdom.
    change (insert k' prog' (fromAList progs)) with (fromAList ((k', prog') :: progs)).
    rewrite !domain_fromAList. cbn [List.map fst]. rewrite HMF.
    apply set_ext. intros x. unfold pred_set.INSERT, pred_set.IN. tauto.
  - change (insert k' prog' (fromAList progs)) with (fromAList ((k', prog') :: progs)).
    intros n0 wp ac' Hl. rewrite lookup_union in Hl.
    destruct (lookup n0 (wordSem.code s)) as [[ac0 wp0]|] eqn:El.
    + injection Hl as -> ->. destruct (Hcode n0 _ _ El) as (C1 & C2 & bs0 & i & bs2 & i2 & f0 & sp & Hc & Hi1 & Hi2 & Hi3 & Hi4 & Hi5).
      split; [exact C1|]. split; [exact C2|]. exists bs0, i, bs2, i2, f0, sp.
      split; [exact Hc|]. split; [exact Hi1|]. split; [rewrite LENGTH_app'; lia|].
      split; [apply isPREFIX_iff in Hi3 as [l Hl']; apply isPREFIX_iff; exists (l ++ append bm1);
              rewrite DROP_skipn, skipn_app, <- DROP_skipn, Hl', <- app_assoc; f_equal;
              pose proof (LENGTH_length (bitmaps T)) as HLb; replace (N.to_nat (i - LENGTH (append bs0)) - length (bitmaps T))%nat with 0%nat by lia; reflexivity|].
      split; [rewrite lookup_union, Hi4; reflexivity|]. reflexivity.
    + rewrite lookup_fromAList in Hl.
      assert (Hm : In (n0, (ac', wp)) ((k', prog') :: progs)) by (apply ALOOKUP_In; exact Hl).
      pose proof (EVERY_In _ _ _ Hpa0 Hm) as C1. pose proof (EVERY_In _ _ _ Hfl0 Hm) as C2.
      pose proof (EVERY_In _ _ _ Hrs0 Hm) as C3. pose proof (EVERY_In _ _ _ Hsc0 Hm) as C4. cbn in C1, C2, C3, C4.
      split; [exact C1|]. split; [exact C2|].
      destruct (compile_word_to_stack_IMP_ALOOKUP ac false ((k', prog') :: progs) k Nil bm0 ((k', p2') :: progs2) fs bm1 n1 n0 ac' wp
                  (bitmaps T ++ append bm1)) as (bs0 & i & bs2 & i2 & f0 & sp & Hc & Hi1 & Hi2 & Hi3 & Hi4).
      { split; [exact Ecw|]. split; [exact Hl|]. split; [exact HL0|].
        change (LENGTH (append (@Nil (word a)))) with 0. split; [rewrite LENGTH_app'; lia|].
        rewrite N.sub_0_r, Hbm0, DROP_skipn, skipn_app, LENGTH_length, Nat2N.id, skipn_all, Nat.sub_diag. cbn [skipn app].
        apply isPREFIX_REFL. }
      exists bs0, i, bs2, i2, f0, sp. split; [exact Hc|]. split; [exact Hi1|]. split; [exact Hi2|]. split; [exact Hi3|].
      split; [|reflexivity]. rewrite lookup_union, lookup_fromAList.
      assert (Hnt : lookup n0 (code T) = NONE).
      { destruct (lookup n0 (code T)) eqn:ET0; [|reflexivity]. exfalso.
        assert (Hd : n0 IN domain (code T)) by (apply domain_lookup; eauto). rewrite Hdom in Hd.
        unfold pred_set.INSERT, pred_set.IN in Hd. destruct Hd as [->|[->|Hd]].
        - revert C3. cbn. discriminate.
        - revert C4. cbn. discriminate.
        - apply domain_lookup in Hd as [v Hv]. congruence. }
      rewrite Hnt. exact Hi4.
  - rewrite lookup_union, Hraise. reflexivity.
  - rewrite lookup_union, Hsc. reflexivity.
  - unfold wordSem.buffer_flush in Edb. destruct (_ && _); [|discriminate]. injection Edb as Edata <-.
    cbn. rewrite LENGTH_app', <- Edata. lia.
  - rewrite LENGTH_app'. lia.
  - destruct (bitmaps T) as [|b0 bl]; [cbn in Hbm1; lia|]. exact Hhd.
  - apply wf_insert. eapply cut_env_wf, Ecut.
  - unfold stack_size_rel in *. destruct Hssr as (A & B & _). split; [exact A|]. split; [exact B|]. intros sm Hsm. discriminate.
  - destruct Hsr as (S1 & st & Ha & Hh & Hr). split; [exact S1|]. exists st.
    split; [apply abs_stack_bitmaps_prefix, Ha|]. split; [exact Hh|exact Hr].
  - intros n0 v Hn0. rewrite lookup_insert in Hn0. destruct (decide (n0 = 2)) as [->|Hn2].
    + injection Hn0 as <-. split; [reflexivity|]. replace (2 DIV 2) with 1 by reflexivity.
      rewrite (proj2 (N.ltb_lt 1 k)) by lia. rewrite FLOOKUP_UPDATE, decide_True by reflexivity. reflexivity.
    + destruct (cut_env_lookup _ _ _ _ _ Ecut Hn0) as [Hl Hd]. destruct (Hloc n0 v Hl) as [He Hr]. split; [exact He|].
      assert (Hk2 : 2 * k <= n0) by (apply N.leb_le; exact (every_name_dom _ _ _ Hst Hd)).
      replace (n0 DIV 2 <? k) with false in Hr |- * by (symmetry; apply N.ltb_ge; apply N.div_le_lower_bound; lia).
      exact Hr.
Qed.

End InstallCase.

Lemma wev_loop {a c ffi_t} names (c0 : wordLang.prog a) en (s : wordSem.state a c ffi_t) :
  wordSem.evaluate (wordLang.Loop names c0 en, s) =
  match wordSem.cut_state (names, LN) s with
  | NONE => (SOME wordSem.Error, s)
  | SOME s0 =>
      let '(res, s1) := wordSem.evaluate (c0, s0) in
      if wordSem.cont_loop res then
        (if wordSem.clock s1 =? 0 then (SOME wordSem.TimeOut, wordSem.flush_state true s1)
         else wordSem.evaluate (wordLang.Loop names c0 en, wordSem.dec_clock s1))
      else if bool_decide (res = SOME (wordSem.Break 0)) then
        match wordSem.cut_state (en, LN) s1 with
        | NONE => (SOME wordSem.Error, s1)
        | SOME s2 => (NONE, s2)
        end
      else (wordSem.exit_loop res, s1)
  end.
Proof.
  rewrite wordSem.evaluate_eqn. cbn [wordSem.evaluate_body].
  destruct (wordSem.cut_state (names, LN) s); [|reflexivity]. rewrite wordSem.fix_clock_evaluate. reflexivity.
Qed.

Lemma ev_loop {a c ffi_t} (q : prog a) (X : stackSem.state a c ffi_t) :
  evaluate (Loop q, X) =
  let '(res, s1) := evaluate (q, X) in
  if cont_loop res then
    (if (clock s1 =? 0)%N then (SOME TimeOut, empty_env s1) else evaluate (Loop q, dec_clock s1))
  else (exit_loop res, s1).
Proof. rewrite evaluate_eqn. cbn [evaluate_body]. rewrite fix_clock_evaluate. reflexivity. Qed.

Lemma pac_loop {a} k names (c0 : wordLang.prog a) en :
  is_true (post_alloc_conventions k (wordLang.Loop names c0 en)) -> is_true (post_alloc_conventions k c0).
Proof.
  unfold post_alloc_conventions. cbn [wordLang.every_var wordLang.every_stack_var call_arg_convention].
  intros H. unfold is_true in *. rewrite !andb_true_iff in *. tauto.
Qed.

Lemma dec_clock_set_clock_add {a c ffi_t} (t : stackSem.state a c ffi_t) e :
  clock t <> 0 -> dec_clock (set_clock (clock t + e) t) = set_clock (clock (dec_clock t) + e) (dec_clock t).
Proof. intros Hc. destruct t. unfold dec_clock, set_clock in *. cbn in *. f_equal. lia. Qed.

Lemma wcut_state_fields {a c ffi_t} names (s x : wordSem.state a c ffi_t) :
  wordSem.cut_state names s = SOME x ->
  wordSem.clock x = wordSem.clock s /\ wordSem.termdep x = wordSem.termdep s /\ wordSem.handler x = wordSem.handler s /\
  wordSem.ffi x = wordSem.ffi s /\ wordSem.stack_limit x = wordSem.stack_limit s /\ wordSem.stack_max x = wordSem.stack_max s.
Proof.
  unfold wordSem.cut_state. destruct (wordSem.cut_env _ _); [|discriminate]. intros E. injection E as <-.
  ws_fields. repeat split.
Qed.

Lemma cont_loop_compile_result {a} (q : option (wordSem.result a)) :
  cont_loop (OPTION_MAP compile_result q) = wordSem.cont_loop q.
Proof. destruct q as [[]|]; reflexivity. Qed.

Lemma exit_loop_compile_result {a} (q : option (wordSem.result a)) :
  q <> SOME (wordSem.Break 0) ->
  OPTION_MAP compile_result (wordSem.exit_loop q) = exit_loop (OPTION_MAP compile_result q).
Proof.
  intros Hq. destruct q as [[]|]; try reflexivity. cbn.
  destruct (n =? 0) eqn:E; [apply N.eqb_eq in E; subst; contradiction|reflexivity].
Qed.

Section LoopCase.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "Loop" *)
Lemma comp_correct_Loop ac names c0 en s :
  (forall y, wordSem.eval_lt y (wordLang.Loop names c0 en, s) -> comp_goal ac y) ->
  comp_goal ac (wordLang.Loop names c0 en, s).
Proof.
  intros IH. goal_intro. pose proof Hcomp as Hcomp0. cbn [comp] in Hcomp.
  destruct (comp ac false c0 (bs, n) (k, (f, f'))) as [q1 [bs1 n1]] eqn:Ec. injection Hcomp as <- <- <-.
  pose proof Hev as Hev0. rewrite wev_loop in Hev.
  destruct (wordSem.cut_state (names, LN) s) as [x|] eqn:Ecut; [|injection Hev as <- _; congruence].
  destruct (wcut_state_fields _ _ _ Ecut) as (Xc & Xt & Xh & Xf & Xsl & Xsm).
  destruct (wordSem.evaluate (c0, x)) as [q r] eqn:Eb.
  destruct (wordSem.evaluate_clock _ _ _ _ Eb) as [Rc Rt].
  pose proof (state_rel_cut_state _ _ _ _ _ _ _ _ _ (conj H Ecut)) as Hx.
  pose proof (pac_loop _ _ _ _ Hpac) as Hpac1. cbn [flat_exp_conventions] in Hflat.
  pose proof Hmax as Hmax0. cbn [wordLang.max_var] in Hmax. rewrite max3_lt_iff in Hmax. destruct Hmax as (_ & Hm1 & _).
  cbn [get_labels] in Hlab.
  pose proof H as HS0. sr_destr HS0.
  assert (Hq : q <> SOME wordSem.Error).
  { intros ->. cbn [wordSem.cont_loop] in Hev. rewrite bool_decide_eq_false_2 in Hev by discriminate.
    injection Hev as <- _. congruence. }
  destruct (IH (c0, x)) with k f f' q r t bs n bs1 n1 q1 lens as (ck & t1 & res1 & Eq1 & HR1).
  { right. split; [exact Xt|]. right. split; [exact Xc|]. cbn [wordSem.psize fst]. lia. }
  { split; [exact Eb|]. split; [exact Hq|]. split; [exact Hx|]. split; [exact Hpac1|]. split; [exact Hflat|].
    split; [exact Ec|]. split; [exact Hbs1|]. split; [exact Hbs2|]. split; [exact Hpre|]. split; [exact Hlab|exact Hm1]. }
  destruct (decide (OPTION_MAP compile_result q = res1)) as [<-|Hne].
  2:{
    rewrite bd_true' in HR1 by exact Hne. destruct HR1 as (-> & Hio & Hslim).
    exists ck, t1, (SOME (Halt (Word (n2w 2)))). split; [rewrite ev_loop, Eq1; reflexivity|].
    rewrite bd_true' by (destruct res as [r0|]; [cbn; intros E; injection E as E; apply (compile_result_NOT_2 r0 Hgd), E|discriminate]).
    split; [reflexivity|].
    assert (Hfin : isPREFIX (io_events (wordSem.ffi r)) (io_events (wordSem.ffi s1)) /\
                   the (wordSem.stack_limit s1 + 1) (wordSem.stack_max s1) > wordSem.stack_limit s1).
    { destruct (wordSem.cont_loop q).
      - destruct (wordSem.clock r =? 0).
        + injection Hev as <- <-. unfold wordSem.flush_state. ws_fields. split; [apply isPREFIX_REFL|exact Hslim].
        + split; [exact (clock.evaluate_io_events_mono _ _ _ _ Hev)|].
          exact (stack_max.evaluate_stack_limit_stack_max _ _ _ _ (conj Hev Hslim)).
      - destruct (bool_decide (q = SOME (wordSem.Break 0))).
        + destruct (wordSem.cut_state (en, LN) r) as [s2|] eqn:Ec2; injection Hev as <- <-.
          * destruct (wcut_state_fields _ _ _ Ec2) as (_ & _ & _ & -> & -> & ->). split; [apply isPREFIX_REFL|exact Hslim].
          * congruence.
        + injection Hev as <- <-. split; [apply isPREFIX_REFL|exact Hslim]. }
    destruct Hfin as [Hio2 Hsl2]. split; [eapply isPREFIX_TRANS; split; eassumption|exact Hsl2]. }
  rewrite bd_neq_false in HR1. rewrite Xh in HR1.
  pose proof (cont_loop_compile_result q) as Hclc.
  destruct (wordSem.cont_loop q) eqn:Ecl.
  - assert (HRr : state_rel ac k f f' r t1 lens 0 /\ OPTION_MAP compile_result q <> SOME TimeOut).
    { destruct q as [rq|]; [destruct rq|]; cbn [wordSem.cont_loop] in Ecl; try discriminate Ecl;
        (split; [exact HR1|discriminate]). }
    destruct HRr as [HRr HnT]. pose proof HRr as HS1. sr_destr HS1.
    destruct (wordSem.clock r =? 0) eqn:Erc.
    + injection Hev as <- <-. exists ck, (empty_env t1), (SOME TimeOut). split.
      { rewrite ev_loop, Eq1, Hclc, <- Hclock0, Erc. reflexivity. }
      cbn [option_map compile_result]. rewrite bd_neq_false.
      unfold wordSem.flush_state, empty_env. ws_fields. stk_fields. split; [symmetry; exact Hffi0|exact Hclock0].
    + apply N.eqb_neq in Erc.
      pose proof (evaluate_mono _ _ _ _ Eq1) as [Hbm Hcd]. stk_fields.
      pose proof (isPREFIX_LENGTH' _ _ Hbm) as Hlbm.
      destruct (IH (wordLang.Loop names c0 en, wordSem.dec_clock r)) with k f f' res s1 (dec_clock t1) bs n bs1 n1 (Loop q1) lens
        as (ck' & t2 & res2 & Eq2 & HR2).
      { right. cbn [snd]. unfold wordSem.dec_clock. ws_fields. split; [congruence|]. left. lia. }
      { split; [exact Hev|]. split; [exact Hres|]. split; [apply state_rel_dec_clock; exact HRr|].
        split; [exact Hpac|]. split; [exact Hflat|]. split; [exact Hcomp0|]. split; [exact Hbs1|].
        unfold dec_clock. stk_fields. split; [lia|].
        split; [eapply isPREFIX_TRANS; split; [exact Hpre|apply isPREFIX_DROP; exact Hbm]|].
        split; [intros z Hz; apply (loc_check_SUBSET _ _ Hcd), Hlab, Hz|exact Hmax0]. }
      exists (ck + ck'), t2, res2. split.
      { rewrite ev_loop, N.add_assoc.
        pose proof (evaluate_add_clock ck' q1 (set_clock (clock t + ck) t) _ t1 (conj Eq1 HnT)) as Ea.
        stk_fields. rewrite set_clock_set_clock in Ea. rewrite Ea, Hclc. stk_fields.
        replace (clock t1 + ck' =? 0) with false by (symmetry; apply N.eqb_neq; lia).
        rewrite dec_clock_set_clock_add by lia. exact Eq2. }
      assert (Hh2 : wordSem.handler (wordSem.dec_clock r) = wordSem.handler s).
      { unfold wordSem.dec_clock. ws_fields. rewrite (evaluate_cont_loop_handler _ _ _ _ (conj Eb Ecl)). exact Xh. }
      rewrite Hh2 in HR2. exact HR2.
  - destruct (bool_decide (q = SOME (wordSem.Break 0))) eqn:Ebk.
    + apply bool_decide_spec in Ebk. subst q.
      destruct (wordSem.cut_state (en, LN) r) as [s2|] eqn:Ec2; injection Hev as <- <-; [|congruence].
      exists ck, t1, NONE. split; [rewrite ev_loop, Eq1; reflexivity|].
      cbn [option_map]. rewrite bd_neq_false. eapply state_rel_cut_state; split; [exact HR1|exact Ec2].
    + apply bdf in Ebk. injection Hev as <- <-.
      exists ck, t1, (exit_loop (OPTION_MAP compile_result q)). split; [rewrite ev_loop, Eq1, Hclc; reflexivity|].
      rewrite <- (exit_loop_compile_result q Ebk), bd_neq_false.
      destruct q as [rq|]; [destruct rq|]; cbn [wordSem.exit_loop]; try exact HR1; discriminate Ecl.
Qed.

End LoopCase.

Section CallEnv.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(** Galette-only: [state_rel] for the callee frame of a tail call. *)
Lemma state_rel_call_env ac k f f' fs svc s t lens args1 ss sac :
  state_rel ac k f f' s t lens 0 ->
  (forall n v, lookup n (fromList2 args1) = SOME v -> lookup n (wordSem.locals s) = SOME v) ->
  LENGTH args1 - k = sac -> sac <= f -> sac <= svc ->
  fs = (if svc =? 0 then 0 else svc + 1) ->
  the fs ss = fs ->
  fs - sac <= stack_space t + (f - sac) ->
  state_rel ac k fs svc (wordSem.call_env args1 ss (wordSem.dec_clock s))
    (set_stack_space (stack_space t + (f - sac) - (fs - sac))
       (dec_clock (set_stack_space (stack_space t + (f - sac)) t))) lens 0.
Proof.
  intros H Hargs Hsac Hsf Hsv Hfs Hthe Hno.
  assert (Hfs2 : sac <= fs) by (subst fs; destruct (svc =? 0) eqn:E; [apply N.eqb_eq in E|]; lia).
  sr_destr H. unfold wordSem.call_env, wordSem.dec_clock, dec_clock.
  sr_split; ws_fields; stk_fields; try assumption.
  - rewrite Hclock. reflexivity.
  - lia.
  - destruct (svc =? 0); exact Hfs.
  - apply wf_fromList2.
  - unfold stack_size_rel in *. destruct Hssr as (A1 & A2 & A3). split; [exact (fun _ => Hthe)|]. split; [exact A2|].
    intros sm Hsm. destruct (wordSem.stack_max s) as [m|]; [|discriminate].
    destruct (A3 m eq_refl) as (B1 & B2 & z & B3 & B4).
    rewrite B3 in Hsm |- *. destruct ss as [x|]; [|discriminate]. cbn in Hsm. injection Hsm as <-.
    cbn in Hthe. subst x. split; [|split; [reflexivity|exists z; split; [reflexivity|lia]]].
    unfold MAX. destruct (m <? z + fs) eqn:E; [apply N.ltb_lt in E|apply N.ltb_ge in E]; lia.
  - rewrite !N.add_0_r in *. rewrite !DROP_DROP_EQ in *.
    replace (fs + (stack_space t + (f - sac) - (fs - sac))) with (f + stack_space t) by lia. exact Hsr.
  - intros n v Hn. pose proof (Hargs n v Hn) as Hl. destruct (Hloc n v Hl) as [He Hr]. split; [exact He|].
    rewrite lookup_fromList2' in Hn. destruct (decide _) as [(_ & Hlt)|]; [|discriminate].
    destruct (n / 2 <? k) eqn:Ek; [exact Hr|]. apply N.ltb_ge in Ek. destruct Hr as [Hr Hr2].
    assert (Hsv0 : svc <> 0) by lia.
    assert (Hfs1 : fs = svc + 1) by (rewrite Hfs; apply N.eqb_neq in Hsv0; rewrite Hsv0; reflexivity).
    assert (Hf1 : f <> 0) by lia.
    split; [|lia].
    rewrite oEL_TAKE_lt in Hr |- * by lia. rewrite oEL_DROP in Hr |- *. rewrite <- Hr. f_equal. lia.
Qed.

End CallEnv.

Lemma FRONT_LAST_eq {A} `{Inhabited A} : forall (l : list A), l <> [] -> l = FRONT l ++ [LAST l].
Proof.
  intros l; induction l as [|x l IH]; intros Hn; [congruence|]. destruct l as [|y l]; [reflexivity|].
  cbn [FRONT LAST]. cbn [app]. f_equal. apply IH. discriminate.
Qed.

Lemma wfind_code_props {a} dest (xs : list (word_loc a)) code0 sss args1 prog ss :
  wordSem.find_code dest xs code0 sss = SOME (args1, (prog, ss)) ->
  (exists p ar, lookup p code0 = SOME (ar, prog)) /\ (exists l, xs = args1 ++ l) /\
  LENGTH args1 = (match dest with SOME _ => LENGTH xs | NONE => LENGTH xs - 1 end) /\
  (dest = NONE -> xs <> []).
Proof.
  unfold wordSem.find_code. destruct dest as [p|].
  - destruct (lookup p code0) as [[ar e]|] eqn:El; [|discriminate].
    destruct (LENGTH xs =? ar); [|discriminate]. intros E. injection E as <- <- <-.
    split; [exists p, ar; exact El|]. split; [exists []; rewrite app_nil_r; reflexivity|]. split; [reflexivity|discriminate].
  - destruct (bool_decide (xs = [])) eqn:Ex; [discriminate|]. apply bdf in Ex.
    destruct (LAST xs) as [w|loc n0]; [discriminate|]. destruct (n0 =? 0); [|discriminate].
    destruct (lookup loc code0) as [[ar e]|] eqn:El; [|discriminate].
    destruct (LENGTH xs =? ar + 1); [|discriminate]. intros E. injection E as <- <- <-.
    pose proof (FRONT_LAST_eq xs Ex) as Hfl.
    split; [exists loc, ar; exact El|]. split; [exists [LAST xs]; exact Hfl|].
    split; [|intros _; exact Ex]. rewrite Hfl at 2. rewrite LENGTH_app'. cbn. lia.
Qed.

Lemma ev_call_tail {a c ffi_t} sf dest' (sp : prog a) (T : stackSem.state a c ffi_t) :
  use_stack T -> stack_space T + sf <= LENGTH (stackSem.stack T) -> find_code dest' (regs T) (code T) = SOME sp ->
  evaluate (SeqStackFree sf (Call NONE dest' NONE), T) =
  if clock T =? 0 then (SOME TimeOut, empty_env (set_stack_space (stack_space T + sf) T))
  else let '(r, T') := evaluate (sp, dec_clock (set_stack_space (stack_space T + sf) T)) in
       if bad_fun_return r then (SOME Error, T') else (r, T').
Proof.
  intros Hu Hs Hf. rewrite evaluate_SeqStackFree by (split; [exact Hu|lia]).
  rewrite ev_seq, ev_stackfree, Hu. cbn [negb].
  replace (LENGTH (stackSem.stack T) <? stack_space T + sf) with false by (symmetry; apply N.ltb_ge; lia).
  rewrite ev_call_none. stk_fields. rewrite Hf. rewrite fix_clock_evaluate. reflexivity.
Qed.

Lemma tail_state_eq {a c ffi_t} (T : stackSem.state a c ffi_t) X Y c0 ck : c0 <> 0 ->
  set_stack_space Y (dec_clock (set_stack_space X (set_clock (c0 + ck) T))) =
  set_clock (clock (set_stack_space Y (dec_clock (set_stack_space X (set_clock c0 T)))) + ck)
    (set_stack_space Y (dec_clock (set_stack_space X (set_clock c0 T)))).
Proof. intros H. destruct T. unfold dec_clock, set_clock, set_stack_space. cbn. f_equal. lia. Qed.

Lemma bad_fun_return_compile_result {a} (r : option (wordSem.result a)) :
  bad_fun_return (OPTION_MAP compile_result r) = wordSem.bad_fun_return r.
Proof. destruct r as [[]|]; reflexivity. Qed.

Section CallTailCase.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : wordSem.state a (N * c) ffi_t) (t : stackSem.state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756 case "Call_tail" *)
Lemma comp_correct_Call_tail ac dest args h s :
  (forall y, wordSem.eval_lt y (wordLang.Call NONE dest args h, s) -> comp_goal ac y) ->
  comp_goal ac (wordLang.Call NONE dest args h, s).
Proof.
  intros IH. goal_intro. cbn [comp] in Hcomp.
  destruct (call_dest dest args (k, (f, f'))) as [q0 dest'] eqn:Ecd. injection Hcomp as <- <- <-.
  wev Hev.
  destruct (wordSem.get_vars args s) as [xs|] eqn:Egv; [|injection Hev as <- _; congruence].
  destruct (wordSem.bad_dest_args dest args) eqn:Ebd; [injection Hev as <- _; congruence|].
  destruct (wordSem.find_code dest (wordSem.add_ret_loc NONE xs) (wordSem.code s) (wordSem.state_stack_size s))
    as [[args1 [prog ss]]|] eqn:Efc; [|injection Hev as <- _; congruence].
  destruct (bool_decide (h = NONE)) eqn:Eh; [apply bool_decide_spec in Eh; subst h|injection Hev as <- _; congruence].
  pose proof H as HS0. sr_destr HS0.
  destruct (call_dest_lemma ac k f f' s t lens dest args q0 dest' xs NONE) as (t4 & E4 & H4 & HL4 & HS4 & Hfc).
  { split; [rewrite Ebd; discriminate|]. split; [exact H|]. split; [exact Ecd|exact Egv]. }
  destruct (Hfc args1 prog ss Efc) as (bs0 & i0 & bs2 & i2 & fs & sp & Ecp & Hi1 & Hi2 & Hi3 & Hthe & Hfind).
  cbn [wordSem.add_ret_loc] in Efc.
  destruct (wfind_code_props _ _ _ _ _ _ _ Efc) as ((p & ar & Elk) & (lx & Hxs) & HLa1 & Hne).
  destruct (Hcode p prog ar Elk) as (Hpac1 & Hflat1 & _).
  pose proof (dec_clock.get_vars_length_lemma _ _ _ Egv) as HLxs.
  (* argument conventions *)
  unfold post_alloc_conventions in Hpac. cbn [wordLang.every_var wordLang.every_stack_var call_arg_convention] in Hpac.
  assert (Hargs : args = GENLIST (fun x => 2 * x) (LENGTH args)).
  { unfold is_true in Hpac. rewrite !andb_true_iff in Hpac. destruct Hpac as [_ Hp]. apply bool_decide_spec in Hp. exact Hp. }
  cbn [wordLang.max_var] in Hmax. rewrite Hargs, MAX_LIST_GENLIST_evens in Hmax.
  set (sac := LENGTH args1 - k).
  assert (Hsac : stack_arg_count dest' (LENGTH args) k = sac).
  { unfold sac. destruct dest as [pos|]; cbn [call_dest] in Ecd.
    - injection Ecd as <- <-. cbn in HLa1 |- *. rewrite HLa1, HLxs. reflexivity.
    - destruct (LENGTH args =? 0) eqn:E0.
      + apply N.eqb_eq in E0. exfalso. apply (Hne eq_refl). destruct xs; [reflexivity|]. cbn in HLxs. lia.
      + apply N.eqb_neq in E0. destruct (wReg2 (LAST args) (k, (f, f'))) as [x1 r]. injection Ecd as <- <-. cbn in HLa1 |- *. lia. }
  assert (HLa2 : LENGTH args1 <= LENGTH args) by (rewrite <- HLxs; destruct dest; lia).
  assert (Hsf' : sac <= f') by (unfold sac; lia).
  assert (Hsf : sac <= f) by (revert Hff; destruct (f' =? 0) eqn:E; [apply N.eqb_eq in E|apply N.eqb_neq in E]; lia).
  unfold compile_prog in Ecp. cbv zeta in Ecp.
  match type of Ecp with context [comp ?A ?B ?C ?D ?E] => destruct (comp A B C D E) as [q1 [bs3 i3]] eqn:Eq1 end.
  injection Ecp as Esp Efs Ebs2 Ei2. subst sp bs2 i2.
  set (svc := MAX (wordLang.max_var prog DIV 2 + 1 - k) (LENGTH args1 - k)) in *.
  assert (Hsv : sac <= svc) by (unfold svc, sac, MAX; destruct (_ <? _) eqn:E; [apply N.ltb_lt in E|apply N.ltb_ge in E]; lia).
  assert (Hfs2 : sac <= fs) by (rewrite <- Efs; destruct (svc =? 0) eqn:E; [apply N.eqb_eq in E|]; lia).
  rewrite Efs in Hfind, Eq1. change (LENGTH args1 - k) with sac in Hfind.
  pose proof H4 as HS4'. sr_destr HS4'.
  rewrite Hsac.
  pose proof (evaluate_mono _ _ _ _ E4) as [Hbm4 Hcd4]. pose proof (isPREFIX_LENGTH' _ _ Hbm4) as Hlbm4.
  destruct (wordSem.clock s =? 0) eqn:Ec0.
  - injection Hev as <- <-. apply N.eqb_eq in Ec0.
    exists 0, (empty_env (set_stack_space (stack_space t4 + (f - sac)) t4)), (SOME TimeOut). split.
    { rewrite set_clock_add0, (ev_seq_none _ _ _ _ E4), (ev_call_tail (f - sac) dest' _ t4 Hus0 ltac:(lia) Hfind).
      rewrite <- Hclock0, Ec0. reflexivity. }
    cbn [option_map compile_result]. rewrite bd_neq_false.
    unfold wordSem.flush_state, empty_env. ws_fields. stk_fields. split; [symmetry; exact Hffi0|congruence].
  - apply N.eqb_neq in Ec0.
    destruct (wordSem.evaluate (prog, wordSem.call_env args1 ss (wordSem.dec_clock s))) as [res' s'] eqn:Ep.
    destruct (wordSem.bad_fun_return res') eqn:Ebf; injection Hev as <- <-; [congruence|].
    assert (E4c : forall ck, evaluate (q0, set_clock (clock t + ck) t) = (NONE, set_clock (clock t + ck) t4)).
    { intros ck. rewrite (evaluate_call_dest_clock _ _ _ _ _ _ _ _ _ Ecd), E4. reflexivity. }
    assert (Ect : clock t = clock t4) by congruence.
    destruct (stack_space t4 + (f - sac) <? fs - sac) eqn:Eov.
    + apply N.ltb_lt in Eov. exists 0. eexists. eexists. split.
      { rewrite (ev_seq_none _ _ _ _ (E4c 0)).
        rewrite (ev_call_tail (f - sac) dest' _ (set_clock (clock t + 0) t4) Hus0 ltac:(stk_fields; lia) Hfind).
        stk_fields. replace (clock t + 0 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
        rewrite ev_seq, ev_stackalloc. unfold dec_clock. stk_fields. rewrite Hus0. cbn [negb].
        replace (stack_space t4 + (f - sac) <? fs - sac) with true by (symmetry; apply N.ltb_lt; lia).
        reflexivity. }
      rewrite bd_true' by (destruct res' as [r0|]; [cbn; intros E; injection E as E; apply (compile_result_NOT_2 r0 Hgd), E|discriminate]).
      split; [reflexivity|]. unfold empty_env. stk_fields. split.
      { rewrite Hffi0. exact (clock.evaluate_io_events_mono _ _ _ _ Ep). }
      pose proof (stack_max.evaluate_stack_limit _ _ _ _ Ep) as Hsl'. pose proof (stack_max.evaluate_stack_max _ _ _ _ Ep) as Hsm'.
      unfold wordSem.call_env, wordSem.dec_clock in Hsl', Hsm'. ws_fields. rewrite Hsl'.
      destruct Hssr0 as (A1 & A2 & A3). rewrite A2.
      destruct (wordSem.stack_max s) as [m|] eqn:Esm.
      * destruct (A3 m eq_refl) as (B1 & B2 & z & B3 & B4). rewrite B3 in Hsm'. destruct ss as [x|]; cbn in Hsm'.
        -- cbn in Hthe. subst x. destruct (wordSem.stack_max s') as [y|]; cbn in Hsm' |- *; [|lia].
           unfold MAX in Hsm'. destruct (m <? z + fs) eqn:E; [apply N.ltb_lt in E|apply N.ltb_ge in E]; lia.
        -- rewrite Hsm'. cbn. lia.
      * rewrite Hsm'. cbn. lia.
    + apply N.ltb_ge in Eov.
      assert (Hargsl : forall n0 v, lookup n0 (fromList2 args1) = SOME v -> lookup n0 (wordSem.locals s) = SOME v).
      { intros n0 v Hl. apply (get_vars_fromList2_eq args s xs n0 v). split; [rewrite <- Hargs; exact Egv|].
        apply (lookup_fromList2_prefix n0 args1 xs v). split; [apply isPREFIX_iff; exists lx; exact Hxs|exact Hl]. }
      pose proof (state_rel_call_env ac k f f' fs svc s t4 lens args1 ss sac H4 Hargsl eq_refl Hsf Hsv (eq_sym Efs) Hthe Eov) as H5.
      set (T5 := set_stack_space (stack_space t4 + (f - sac) - (fs - sac)) (dec_clock (set_stack_space (stack_space t4 + (f - sac)) t4))) in H5.
      destruct (IH (prog, wordSem.call_env args1 ss (wordSem.dec_clock s))) with k fs svc res' s' T5 bs0 i0 bs3 i3 q1 lens
        as (ck & t1 & res1 & Eq & HR).
      { right. unfold wordSem.call_env, wordSem.dec_clock. cbn [snd]. ws_fields. split; [reflexivity|]. left. lia. }
      { split; [exact Ep|]. split; [exact Hres|]. split; [exact H5|]. split; [exact Hpac1|]. split; [exact Hflat1|].
        split; [exact Eq1|]. split; [exact Hi1|]. split; [unfold T5, dec_clock; stk_fields; lia|].
        split; [unfold T5, dec_clock; stk_fields; eapply isPREFIX_TRANS; split; [exact Hi3|apply isPREFIX_DROP; exact Hbm4]|].
        split.
        - pose proof (find_code_IMP_get_labels _ _ _ _ Hfind) as Hgl. intros z Hz. unfold T5, dec_clock. stk_fields.
          apply Hgl. cbn [get_labels]. right. exact Hz.
        - unfold svc. pose proof (N.div_mod (wordLang.max_var prog) 2 ltac:(lia)) as D1.
          pose proof (N.mod_lt (wordLang.max_var prog) 2 ltac:(lia)) as D2.
          unfold MAX. destruct (_ <? _) eqn:E; [apply N.ltb_lt in E|apply N.ltb_ge in E]; lia. }
      exists ck, t1, res1. split.
      { rewrite (ev_seq_none _ _ _ _ (E4c ck)).
        rewrite (ev_call_tail (f - sac) dest' _ (set_clock (clock t + ck) t4) Hus0 ltac:(stk_fields; lia) Hfind).
        stk_fields. replace (clock t + ck =? 0) with false by (symmetry; apply N.eqb_neq; lia).
        rewrite ev_seq, ev_stackalloc.
        assert (ES : set_stack_space (stack_space (dec_clock (set_stack_space (stack_space t4 + (f - sac)) (set_clock (clock t + ck) t4))) - (fs - sac))
                       (dec_clock (set_stack_space (stack_space t4 + (f - sac)) (set_clock (clock t + ck) t4))) = set_clock (clock T5 + ck) T5).
        { rewrite Ect. unfold T5, dec_clock, set_clock, set_stack_space. cbn. f_equal. lia. }
        replace (use_stack (dec_clock (set_stack_space (stack_space t4 + (f - sac)) (set_clock (clock t + ck) t4)))) with true by (symmetry; exact Hus0).
        replace (stack_space (dec_clock (set_stack_space (stack_space t4 + (f - sac)) (set_clock (clock t + ck) t4))) <? fs - sac)
          with false by (symmetry; apply N.ltb_ge; unfold dec_clock; stk_fields; lia).
        cbn [negb]. rewrite ES, Eq.
        destruct (decide (OPTION_MAP compile_result res' = res1)) as [<-|Hne1].
        - rewrite bad_fun_return_compile_result, Ebf. reflexivity.
        - rewrite bd_true' in HR by exact Hne1. destruct HR as (-> & _). reflexivity. }
      destruct res' as [[]|]; cbn [wordSem.bad_fun_return] in Ebf; try discriminate Ebf; exact HR.
Qed.

End CallTailCase.
