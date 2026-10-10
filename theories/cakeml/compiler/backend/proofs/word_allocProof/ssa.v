(** * CakeML [word_allocProof]: correctness of the SSA transformation

    Part of the port of
    [cakeml/compiler/backend/proofs/word_allocProofScript.sml] (HOL lines
    7666-10377): [ssa_cc_trans_correct] and [full_ssa_cc_trans_correct].

    Notes: as in [ssa_props.v].  [ssa_cc_trans_correct] is proved by
    structural induction on the program (HOL: complete induction on
    [prog_size]), one Galette-only lemma per constructor ([ssa_X]); the
    statement is folded into the Galette-only [ssa_hyp]/[ssa_concl]
    (defined in [ssa_loop.v]) for these lemmas. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set extra.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From Galette.cakeml.compiler.backend Require Import stackLang wordLang word_alloc.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem wordConvs.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import
  consts consts_with clock dec_clock locals_rel permute_swap stack_swap code.
From Galette.cakeml.compiler.backend.proofs.word_allocProof Require Import colouring ssa_props ssa_loop.
Open Scope N_scope.

Ltac destr_lets_goal :=
  repeat match goal with
  | |- context [match ?X with (_, _) => _ end] =>
      lazymatch X with
      | (_, _) => fail
      | evaluate _ => fail
      | match _ with _ => _ end => fail
      | (if _ then _ else _) => fail
      | _ => tryif is_var X then destruct X else (let Ex := fresh "Ex" in destruct X eqn:Ex)
      end; cbn beta iota zeta
  end.

Lemma LENGTH_GENLIST' {A} (f : N -> A) n : LENGTH (GENLIST f n) = n.
Proof.
  induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (GENLIST_thm f n)), SNOC_app, !LENGTH_length, length_app.
  rewrite LENGTH_length in IH. cbn [Datatypes.length]. lia.
Qed.

Section SSA3.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).
Implicit Types (st cst : state).

Lemma ssa_by p st cst ssa na lt :
  word_state_eq_rel st cst ->
  (forall res rst, word_state_eq_rel (set_permute (permute cst) st) cst ->
     evaluate (p, set_permute (permute cst) st) = (res, rst) -> res <> SOME Error ->
     let '(p', (ssa', na')) := ssa_cc_trans p ssa na lt in
     let '(res', rcst) := evaluate (p', cst) in
     res = res' /\ word_state_eq_rel rst rcst /\ ssa_post lt na' ssa' res rst rcst) ->
  ssa_concl p st cst ssa na lt.
Proof.
  intros Heq H. exists (permute cst).
  destruct (evaluate (p, set_permute (permute cst) st)) as [res rst] eqn:E.
  destruct (decide (res = SOME Error)) as [->|Hr]; [left; reflexivity|right].
  apply H; [|reflexivity|exact Hr].
  apply word_state_eq_rel_iff in Heq. rewrite Heq at 2. apply word_state_eq_rel_iff.
  rewrite permute_set_permute, locals_set_permute, locals_set_locals. reflexivity.
Qed.

Lemma ol_props {A} na ssa (sl L : num_map A) x v :
  ssa_locals_rel na ssa sl L -> ssa_map_ok na ssa -> lookup x sl = Some v ->
  lookup (option_lookup ssa x) L = Some v /\ ~ is_phy_var (option_lookup ssa x) /\ option_lookup ssa x < na.
Proof.
  intros [_ R2] Hok Hx. destruct (R2 _ _ Hx) as (Hd & Hl & _). apply domain_lookup in Hd as [z Hz].
  unfold option_lookup. rewrite Hz in Hl |- *. cbn [THE] in Hl. destruct (Hok _ _ Hz). auto.
Qed.

(** Normal form: the target runs on [set_locals L st0]. *)
Ltac ssa_start :=
  let res := fresh "res" in let rst := fresh "rst" in let Heq0 := fresh "Heq0" in
  let Hev0 := fresh "Hev" in let Hres := fresh "Hres" in let st0 := fresh "st0" in
  intros (Heq & Hr & Ha & Hevar & Hok & Hlt); apply ssa_by; [exact Heq|];
  intros res rst Heq0 Hev0 Hres;
  lazymatch type of Heq0 with
  | word_state_eq_rel (set_permute ?p ?s) _ =>
      set (st0 := set_permute p s) in *; change (locals s) with (locals st0) in Hr
  end;
  rewrite evaluate_eqn in Hev0; cbn [evaluate_body] in Hev0;
  cbn [ssa_cc_trans next_var_rename]; destr_lets_goal;
  cbn [every_var] in Hevar;
  match goal with
  | st0 := _ |- _ =>
    match goal with
    | H0 : word_state_eq_rel st0 ?cst |- _ =>
      let Hcst := fresh "Hcst" in let L := fresh "L" in let HL := fresh "HL" in
      assert (Hcst : cst = set_locals (locals cst) st0)
        by (apply wser_set_locals_eq; [exact H0|reflexivity]);
      clearbody st0;
      remember (locals cst) as L eqn:HL; clear HL; subst cst
    end
  end;
  autorewrite with lrl in *.

Ltac ssa_err Hev Hr := injection Hev as <- _; exfalso; apply Hr; reflexivity.

Lemma ssa_Skip st cst ssa na lt :
  ssa_hyp (@Skip a) st cst ssa na lt -> ssa_concl (@Skip a) st cst ssa na lt.
Proof.
  ssa_start. injection Hev as <- <-. rewrite evaluate_eqn; cbn [evaluate_body ssa_post].
  split; [reflexivity|split; [apply wser_sl|exact Hr]].
Qed.

Lemma ssa_exp (st0 : state) L ssa na e w :
  ssa_locals_rel na ssa (locals st0) L -> word_exp st0 e = Some w ->
  word_exp (set_locals L st0) (ssa_cc_trans_exp ssa e) = Some w.
Proof.
  intros Hr He. apply (ssa_cc_trans_exp_correct st0 e _ ssa na w).
  split; [exact He|split; [apply wser_sl|rewrite locals_set_locals; exact Hr]].
Qed.

Lemma ltb_var x na : is_true (x <? na) -> x < na.
Proof. unfold is_true; apply N.ltb_lt. Qed.

Ltac bool_split :=
  repeat match goal with
  | H : is_true (_ && _) |- _ => apply andb_prop in H; destruct H
  | H : (_ && _) = true |- _ => apply andb_prop in H; destruct H
  end.

Lemma ssa_Assign v e st cst ssa na lt :
  ssa_hyp (Assign v e) st cst ssa na lt -> ssa_concl (Assign v e) st cst ssa na lt.
Proof.
  ssa_start. bool_split. destruct (word_exp st0 e) as [w|] eqn:Ee; [|ssa_err Hev Hres]. injection Hev as <- <-.
  rewrite evaluate_eqn; cbn [evaluate_body]. rewrite (ssa_exp st0 L ssa na e w Hr Ee).
  cbn [ssa_post]. unfold set_var. rewrite ?sl_sl. autorewrite with lrl. split; [reflexivity|split; [apply wser_sl'|]].
  apply ssa_locals_rel_insert. split; [exact Hr|split; [exact Hok|apply ltb_var; assumption]].
Qed.

Lemma ssa_Get v n st cst ssa na lt :
  ssa_hyp (Get v n) st cst ssa na lt -> ssa_concl (Get v n) st cst ssa na lt.
Proof.
  ssa_start. destruct (get_store n st0) as [w|] eqn:Ee; [|ssa_err Hev Hres]. injection Hev as <- <-.
  rewrite evaluate_eqn; cbn [evaluate_body]. rewrite get_store_set_locals, Ee.
  cbn [ssa_post]. unfold set_var. rewrite ?sl_sl. autorewrite with lrl. split; [reflexivity|split; [apply wser_sl'|]].
  apply ssa_locals_rel_insert. split; [exact Hr|split; [exact Hok|apply ltb_var; assumption]].
Qed.

Lemma ssa_Set v e st cst ssa na lt :
  ssa_hyp (Set_ v e) st cst ssa na lt -> ssa_concl (Set_ v e) st cst ssa na lt.
Proof.
  ssa_start. destruct (_ || _) eqn:Eb; [ssa_err Hev Hres|].
  destruct (word_exp st0 e) as [w|] eqn:Ee; [|ssa_err Hev Hres]. injection Hev as <- <-.
  rewrite evaluate_eqn; cbn [evaluate_body]. rewrite Eb, (ssa_exp st0 L ssa na e w Hr Ee).
  cbn [ssa_post]. unfold set_store. split; [reflexivity|split; [wser|cbn_ws; exact Hr]].
Qed.

Lemma ssa_Store e v st cst ssa na lt :
  ssa_hyp (Store e v) st cst ssa na lt -> ssa_concl (Store e v) st cst ssa na lt.
Proof.
  ssa_start. destruct (word_exp st0 e) as [[w|]|] eqn:Ee; try ssa_err Hev Hres.
  destruct (get_var v st0) as [x|] eqn:Ev; [|ssa_err Hev Hres].
  destruct (mem_store w x st0) as [s1|] eqn:Em; [|ssa_err Hev Hres]. injection Hev as <- <-.
  rewrite evaluate_eqn; cbn [evaluate_body]. rewrite (ssa_exp st0 L ssa na e (Word w) Hr Ee).
  destruct (ol_props na ssa _ _ v x Hr Hok Ev) as (Hv & _).
  unfold get_var at 1. rewrite locals_set_locals, Hv. rewrite mem_store_set_locals, Em.
  cbn [ssa_post]. unfold mem_store in Em. destruct (classical_dec _); [|discriminate]. injection Em as <-.
  split; [reflexivity|split; [wser|cbn_ws; exact Hr]].
Qed.

Lemma ssa_Tick st cst ssa na lt :
  ssa_hyp (@Tick a) st cst ssa na lt -> ssa_concl (@Tick a) st cst ssa na lt.
Proof.
  ssa_start. rewrite evaluate_eqn; cbn [evaluate_body]. rewrite clock_set_locals.
  destruct (clock st0 =? 0); injection Hev as <- <-; cbn [ssa_post].
  - rewrite flush_state_set_locals. split; [reflexivity|split; [apply word_state_eq_rel_refl|reflexivity]].
  - rewrite dec_clock_set_locals. split; [reflexivity|split; [apply wser_sl|]]. rewrite locals_set_locals.
    exact Hr.
Qed.

Lemma ssa_LocValue r l1 st cst ssa na lt :
  ssa_hyp (LocValue r l1) st cst ssa na lt -> ssa_concl (LocValue r l1) st cst ssa na lt.
Proof.
  ssa_start. destruct (classical_dec _) as [Hc|]; [|ssa_err Hev Hres]. injection Hev as <- <-.
  rewrite evaluate_eqn; cbn [evaluate_body]. rewrite code_set_locals. destruct (classical_dec _); [|contradiction].
  cbn [ssa_post]. unfold set_var. rewrite ?sl_sl. autorewrite with lrl. split; [reflexivity|split; [apply wser_sl'|]].
  apply ssa_locals_rel_insert. split; [exact Hr|split; [exact Hok|apply ltb_var; assumption]].
Qed.

Lemma ssa_OpCurrHeap b dst src st cst ssa na lt :
  ssa_hyp (OpCurrHeap b dst src) st cst ssa na lt -> ssa_concl (OpCurrHeap b dst src) st cst ssa na lt.
Proof.
  ssa_start. bool_split. destruct (word_exp st0 (Op b [Var src; Lookup CurrHeap])) as [w|] eqn:Ee; [|ssa_err Hev Hres].
  injection Hev as <- <-.
  rewrite evaluate_eqn; cbn [evaluate_body].
  pose proof (ssa_exp st0 L ssa na _ w Hr Ee) as He. cbn [ssa_cc_trans_exp MAP List.map] in He. rewrite He.
  cbn [ssa_post]. unfold set_var. rewrite ?sl_sl. autorewrite with lrl. split; [reflexivity|split; [apply wser_sl'|]].
  apply ssa_locals_rel_insert. split; [exact Hr|split; [exact Hok|apply ltb_var; assumption]].
Qed.

Lemma ssa_CodeBufferWrite r1 r2 st cst ssa na lt :
  ssa_hyp (CodeBufferWrite r1 r2) st cst ssa na lt -> ssa_concl (CodeBufferWrite r1 r2) st cst ssa na lt.
Proof.
  ssa_start. destruct (get_var r1 st0) as [[w1|]|] eqn:E1; try ssa_err Hev Hres.
  destruct (get_var r2 st0) as [[w2|]|] eqn:E2; try ssa_err Hev Hres.
  destruct (buffer_write _ _ _) as [cb|] eqn:Eb; [|ssa_err Hev Hres]. injection Hev as <- <-.
  rewrite evaluate_eqn; cbn [evaluate_body]. unfold get_var at 1 2. rewrite !locals_set_locals.
  rewrite (proj1 (ol_props na ssa _ _ r1 _ Hr Hok E1)), (proj1 (ol_props na ssa _ _ r2 _ Hr Hok E2)).
  rewrite code_buffer_set_locals, Eb. cbn [ssa_post]. split; [reflexivity|split; [wser|cbn_ws; exact Hr]].
Qed.

Lemma ssa_DataBufferWrite r1 r2 st cst ssa na lt :
  ssa_hyp (DataBufferWrite r1 r2) st cst ssa na lt -> ssa_concl (DataBufferWrite r1 r2) st cst ssa na lt.
Proof.
  ssa_start. destruct (get_var r1 st0) as [[w1|]|] eqn:E1; try ssa_err Hev Hres.
  destruct (get_var r2 st0) as [[w2|]|] eqn:E2; try ssa_err Hev Hres.
  destruct (buffer_write _ _ _) as [cb|] eqn:Eb; [|ssa_err Hev Hres]. injection Hev as <- <-.
  rewrite evaluate_eqn; cbn [evaluate_body]. unfold get_var at 1 2. rewrite !locals_set_locals.
  rewrite (proj1 (ol_props na ssa _ _ r1 _ Hr Hok E1)), (proj1 (ol_props na ssa _ _ r2 _ Hr Hok E2)).
  rewrite data_buffer_set_locals, Eb. cbn [ssa_post]. split; [reflexivity|split; [wser|cbn_ws; exact Hr]].
Qed.

Lemma ssa_Raise n st cst ssa na lt :
  ssa_hyp (Raise n) st cst ssa na lt -> ssa_concl (Raise n) st cst ssa na lt.
Proof.
  ssa_start. destruct (get_var n st0) as [w|] eqn:E1; [|ssa_err Hev Hres].
  destruct (jump_exc st0) as [[s1 [l1 l2]]|] eqn:Ej; [|ssa_err Hev Hres]. injection Hev as <- <-.
  destruct (ol_props na ssa _ _ n _ Hr Hok E1) as (Hn & _).
  rewrite (eval_Seq_none _ _ _ _ (eval_move1 1 2 _ (set_locals L st0) w ltac:(rewrite locals_set_locals; exact Hn))).
  rewrite evaluate_eqn; cbn [evaluate_body]. unfold get_var. rewrite !locals_set_locals, lookup_insert1.
  rewrite !jump_exc_set_locals, Ej. cbn [ssa_post]. split; [reflexivity|split; [apply word_state_eq_rel_refl|reflexivity]].
Qed.

Lemma GENLIST_rets_props n :
  NoDup (GENLIST (fun x => 2 * (x + 1)) n) /\ forall y, In y (GENLIST (fun x => 2 * (x + 1)) n) -> is_phy_var y = true.
Proof.
  split.
  - apply ALL_DISTINCT_iff', ALL_DISTINCT_GENLIST. intros; lia.
  - intros y Hy. apply In_GENLIST_iff in Hy as (i & _ & ->). unfold is_phy_var. apply N.eqb_eq.
    replace (2 * (i + 1)) with (0 + (i + 1) * 2) by lia. rewrite N.Div0.mod_add. reflexivity.
Qed.

Lemma ssa_Return n ns st cst ssa na lt :
  ssa_hyp (Return n ns) st cst ssa na lt -> ssa_concl (Return n ns) st cst ssa na lt.
Proof.
  ssa_start. destruct (get_var n st0) as [[w|l1 l2]|] eqn:E1; try ssa_err Hev Hres.
  destruct (get_vars ns st0) as [ys|] eqn:E2; [|ssa_err Hev Hres]. injection Hev as <- <-.
  set (rets := GENLIST (fun x => 2 * (x + 1)) (LENGTH (MAP (option_lookup ssa) ns))).
  destruct (GENLIST_rets_props (LENGTH (MAP (option_lookup ssa) ns))) as [Hnd Hph]. fold rets in Hnd, Hph.
  assert (Hlr : LENGTH rets = LENGTH (MAP (option_lookup ssa) ns)) by (unfold rets; apply LENGTH_GENLIST').
  assert (Hly : LENGTH ys = LENGTH rets)
    by (rewrite Hlr, LENGTH_MAP'; exact (get_vars_length_lemma _ _ _ E2)).
  assert (Hg : get_vars (MAP (option_lookup ssa) ns) (set_locals L st0) = Some ys).
  { apply (ssa_locals_rel_get_vars ns ys na ssa st0). rewrite locals_set_locals. auto. }
  rewrite evaluate_Seq_eq'. rewrite (evaluate_eqn (Move 0 _)); cbn [evaluate_body].
  rewrite MAP_FST_ZIP', MAP_SND_ZIP' by exact Hlr.
  assert (Hd : ALL_DISTINCT rets = true) by (apply ALL_DISTINCT_iff', Hnd).
  rewrite Hd, Hg. cbn beta iota. rewrite bd_true' by reflexivity.
  destruct (ol_props na ssa _ _ n _ Hr Hok E1) as (Hn & Hnp & _).
  rewrite evaluate_eqn; cbn [evaluate_body].
  rewrite get_var_set_vars_notin.
  2: { split; [|lia]. rewrite MEM_iff'. intros Hin. apply Hph in Hin. rewrite Hin in Hnp. apply Hnp; reflexivity. }
  unfold get_var at 1. rewrite locals_set_locals, Hn.
  rewrite get_vars_set_vars_eq by (split; [apply ALL_DISTINCT_iff', Hnd|exact Hly]).
  unfold set_vars. rewrite !flush_state_set_locals. cbn [ssa_post].
  split; [reflexivity|split; [apply word_state_eq_rel_refl|reflexivity]].
Qed.

Lemma ssa_Break n st cst ssa na lt :
  ssa_hyp (wordLang.Break n) st cst ssa na lt -> ssa_concl (wordLang.Break n) st cst ssa na lt.
Proof.
  ssa_start. injection Hev as <- <-.
  destruct (oEL n lt) as [[tgt [nm ex]]|] eqn:Eo.
  - destruct (lt_ok_oEL _ _ _ _ _ Hlt Eo) as [_ Hi].
    destruct (evaluate_ssa_reconcile na ssa (locals st0) (set_locals L st0) tgt ex)
      as (cst' & Ec & Hw & Hs); [rewrite locals_set_locals; auto|].
    assert (Hb : forall (s9 : state), evaluate (@wordLang.Break a n, s9) = (SOME (Break n), s9))
      by (intros s9; rewrite evaluate_eqn; reflexivity).
    destruct (is_Skip _) eqn:Es.
    + apply is_Skip_eq in Es. rewrite Es in Ec. rewrite evaluate_eqn in Ec; cbn [evaluate_body] in Ec.
      injection Ec as <-. rewrite Hb. cbn [ssa_post]. rewrite Eo.
      split; [reflexivity|split; [exact Heq0|exact Hs]].
    + rewrite (eval_Seq_none _ _ _ _ Ec), Hb. cbn [ssa_post]. rewrite Eo.
      split; [reflexivity|split; [exact (word_state_eq_rel_trans _ _ _ Heq0 Hw)|exact Hs]].
  - rewrite evaluate_eqn; cbn [evaluate_body ssa_post]. rewrite Eo.
    split; [reflexivity|split; [exact Heq0|exact Logic.I]].
Qed.

Lemma ssa_Continue n st cst ssa na lt :
  ssa_hyp (wordLang.Continue n) st cst ssa na lt -> ssa_concl (wordLang.Continue n) st cst ssa na lt.
Proof.
  ssa_start. injection Hev as <- <-.
  destruct (oEL n lt) as [[tgt [nm ex]]|] eqn:Eo.
  - destruct (lt_ok_oEL _ _ _ _ _ Hlt Eo) as [Hi _].
    destruct (evaluate_ssa_reconcile na ssa (locals st0) (set_locals L st0) tgt nm)
      as (cst' & Ec & Hw & Hs); [rewrite locals_set_locals; auto|].
    assert (Hb : forall (s9 : state), evaluate (@wordLang.Continue a n, s9) = (SOME (Continue n), s9))
      by (intros s9; rewrite evaluate_eqn; reflexivity).
    destruct (is_Skip _) eqn:Es.
    + apply is_Skip_eq in Es. rewrite Es in Ec. rewrite evaluate_eqn in Ec; cbn [evaluate_body] in Ec.
      injection Ec as <-. rewrite Hb. cbn [ssa_post]. rewrite Eo.
      split; [reflexivity|split; [exact Heq0|exact Hs]].
    + rewrite (eval_Seq_none _ _ _ _ Ec), Hb. cbn [ssa_post]. rewrite Eo.
      split; [reflexivity|split; [exact (word_state_eq_rel_trans _ _ _ Heq0 Hw)|exact Hs]].
  - rewrite evaluate_eqn; cbn [evaluate_body ssa_post]. rewrite Eo.
    split; [reflexivity|split; [exact Heq0|exact Logic.I]].
Qed.

Definition ssa_IH (p : prog a) : Prop :=
  forall st cst ssa na lt, ssa_hyp p st cst ssa na lt -> ssa_concl p st cst ssa na lt.

Lemma ssa_post_some lt n s n' s' (res : option (result a)) (rst rcst : state) :
  res <> NONE -> ssa_post lt n s res rst rcst -> ssa_post lt n' s' res rst rcst.
Proof. intros H; destruct res as [[]|]; cbn [ssa_post]; auto; congruence. Qed.

Lemma ssa_MustTerminate p st cst ssa na lt :
  ssa_IH p -> ssa_hyp (MustTerminate p) st cst ssa na lt -> ssa_concl (MustTerminate p) st cst ssa na lt.
Proof.
  intros IH (Heq & Hr & Ha & Hev & Hok & Hlt). cbn [every_var] in Hev.
  set (st' := set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) st)).
  set (cst' := set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) cst)).
  destruct (IH st' cst' ssa na lt) as [perm Hp].
  { split; [subst st' cst'; wser|]. split; [exact Hr|auto]. }
  exists perm. rewrite evaluate_eqn; cbn [evaluate_body]. rewrite termdep_set_permute.
  destruct (termdep st =? 0) eqn:Et; [left; reflexivity|].
  rewrite set_clock_set_permute, set_termdep_set_permute. fold st'.
  destruct (evaluate (p, set_permute perm st')) as [res rst] eqn:E.
  destruct Hp as [->|Hp]; [destruct (⌜_⌝); left; reflexivity|].
  destruct (⌜res = SOME TimeOut⌝) eqn:Eto; [left; reflexivity|right].
  cbn [ssa_cc_trans]. destruct (ssa_cc_trans p ssa na lt) as [p' [ssa' na']].
  rewrite evaluate_eqn; cbn [evaluate_body].
  assert (Htd : termdep cst = termdep st) by (destruct Heq; destr_conj; congruence).
  rewrite Htd, Et. fold cst'.
  destruct (evaluate (p', cst')) as [res' rcst] eqn:E'.
  destruct Hp as (<- & Hw & Hpost). rewrite Eto. split; [reflexivity|split].
  - unfold word_state_eq_rel in *; cbn_ws; destr_conj; repeat split; congruence.
  - destruct res as [[]|]; cbn [ssa_post] in *; cbn_ws; exact Hpost.
Qed.

Lemma every_var_lt_mono (p : prog a) na na' :
  is_true (every_var (fun x => x <? na) p) -> na <= na' -> is_true (every_var (fun x => x <? na') p).
Proof.
  intros H Hle. apply (every_var_mono (fun x => x <? na)). split; [|exact H].
  intros x Hx. unfold is_true in *. apply N.ltb_lt in Hx. apply N.ltb_lt. lia.
Qed.

Lemma ssa_Seq p1 p2 st cst ssa na lt :
  ssa_IH p1 -> ssa_IH p2 -> ssa_hyp (Seq p1 p2) st cst ssa na lt -> ssa_concl (Seq p1 p2) st cst ssa na lt.
Proof.
  intros IH1 IH2 (Heq & Hr & Ha & Hev & Hok & Hlt). cbn [every_var] in Hev.
  apply andb_prop in Hev as [Hev1 Hev2].
  destruct (IH1 st cst ssa na lt (conj Heq (conj Hr (conj Ha (conj Hev1 (conj Hok Hlt)))))) as [perm1 Hp1].
  unfold ssa_concl. cbn [ssa_cc_trans]. destruct (ssa_cc_trans p1 ssa na lt) as [p1' [ssa1 na1]] eqn:Et1.
  destruct (ssa_cc_trans p2 ssa1 na1 lt) as [p2' [ssa2 na2]] eqn:Et2.
  destruct (ssa_cc_trans_props _ _ _ _ _ _ _ Et1 (conj Hok Ha)) as (Hle1 & Ha1 & Hok1).
  destruct (evaluate (p1, set_permute perm1 st)) as [r1 s1] eqn:E1.
  destruct Hp1 as [->|Hp1].
  { exists perm1. rewrite evaluate_Seq_eq', E1. rewrite bd_false' by discriminate. left; reflexivity. }
  destruct (evaluate (p1', cst)) as [r1' cs1] eqn:E1'.
  destruct Hp1 as (<- & Hw1 & Hpost1).
  destruct r1 as [r1|].
  - exists perm1. rewrite evaluate_Seq_eq', E1. rewrite bd_false' by discriminate. cbn beta iota zeta. right.
    rewrite evaluate_Seq_eq', E1', bd_false' by discriminate. cbn beta iota zeta.
    split; [reflexivity|split; [exact Hw1|]]. eapply ssa_post_some; [discriminate|exact Hpost1].
  - cbn [ssa_post] in Hpost1.
    destruct (IH2 s1 cs1 ssa1 na1 lt) as [perm2 Hp2].
    { split; [exact Hw1|split; [exact Hpost1|split; [exact Ha1|split; [|split; [exact Hok1|exact Hlt]]]]].
      eapply every_var_lt_mono; eassumption. }
    rewrite Et2 in Hp2.
    pose proof (permute_swap_lemma p1 (set_permute perm1 st) perm2) as H3.
    rewrite E1 in H3. assert (Hne : (NONE : option (result a)) <> SOME Error) by discriminate.
    destruct (H3 Hne) as [perm3 E3]. rewrite set_permute_set_permute in E3.
    exists perm3. rewrite evaluate_Seq_eq'. rewrite E3. rewrite bd_true' by reflexivity.
    rewrite evaluate_Seq_eq', E1', bd_true' by reflexivity. exact Hp2.
Qed.
Lemma ssa_If cmp r ri p1 p2 st cst ssa na lt :
  ssa_IH p1 -> ssa_IH p2 -> ssa_hyp (If cmp r ri p1 p2) st cst ssa na lt ->
  ssa_concl (If cmp r ri p1 p2) st cst ssa na lt.
Proof.
  intros IH1 IH2 (Heq & Hr & Ha & Hev & Hok & Hlt). cbn [every_var] in Hev.
  apply andb_prop in Hev as [Hev Hev2]. apply andb_prop in Hev as [Hev Hev1]. apply andb_prop in Hev as [Hevr Hevi].
  unfold ssa_concl. cbn [ssa_cc_trans].
  destruct (ssa_cc_trans p1 ssa na lt) as [e2' [ssa2 na2]] eqn:Et1.
  destruct (ssa_cc_trans p2 ssa na2 lt) as [e3' [ssa3 na3]] eqn:Et2.
  destruct (ssa_cc_trans_props _ _ _ _ _ _ _ Et1 (conj Hok Ha)) as (Hle2 & Ha2 & Hok2).
  assert (Hokn2 : ssa_map_ok na2 ssa) by (apply (ssa_map_ok_more na); auto).
  destruct (ssa_cc_trans_props _ _ _ _ _ _ _ Et2 (conj Hokn2 Ha2)) as (Hle3 & Ha3 & Hok3).
  pose proof (@fix_inconsistencies_correctL a c ffi_t (mk_prio e2' e3') na3 ssa2 ssa3
                (conj Ha3 (ssa_map_ok_more na2 ssa2 na3 (conj Hok2 Hle3)))) as FL.
  pose proof (@fix_inconsistencies_correctR a c ffi_t na3 ssa2 ssa3 (mk_prio e2' e3') (conj Ha3 Hok3)) as FR.
  destruct (fix_inconsistencies (mk_prio e2' e3') ssa2 ssa3 na3) as [c2 [c3 [nf sf]]] eqn:Ef.
  destruct (IH1 st cst ssa na lt (conj Heq (conj Hr (conj Ha (conj Hev1 (conj Hok Hlt)))))) as [perm1 Hp1].
  destruct (IH2 st cst ssa na2 lt) as [perm2 Hp2].
  { split; [exact Heq|split; [apply (ssa_locals_rel_more na); auto|split; [exact Ha2|]]].
    split; [eapply every_var_lt_mono; eassumption|split; [exact Hokn2|exact Hlt]]. }
  rewrite Et1 in Hp1. rewrite Et2 in Hp2.
  destruct (get_var r st) as [x|] eqn:Ex; [|exists perm1; rewrite evaluate_eqn; cbn [evaluate_body];
    rewrite get_var_set_permute, Ex; cbn beta iota zeta; left; reflexivity].
  destruct (get_var_imm ri st) as [y|] eqn:Ey; [|exists perm1; rewrite evaluate_eqn; cbn [evaluate_body];
    rewrite get_var_set_permute, get_var_imm_set_permute, Ex, Ey; cbn beta iota zeta; left; reflexivity].
  assert (Ex' : get_var (option_lookup ssa r) cst = Some x)
    by (unfold get_var in *; exact (proj1 (ol_props na ssa _ _ r x Hr Hok Ex))).
  assert (Ey' : get_var_imm (match ri with Reg r0 => Reg (option_lookup ssa r0) | Imm v => Imm v end) cst = Some y).
  { destruct ri as [r2|w]; cbn [get_var_imm] in *; [|exact Ey].
    unfold get_var in *; exact (proj1 (ol_props na ssa _ _ r2 y Hr Hok Ey)). }
  destruct (word_cmp cmp x y) as [[]|] eqn:Ec.
  - exists perm1. rewrite evaluate_eqn; cbn [evaluate_body]. rewrite get_var_set_permute, get_var_imm_set_permute, Ex, Ey, Ec.
    destruct (evaluate (p1, set_permute perm1 st)) as [res rst]. destruct Hp1 as [Hp1|Hp1]; [left; exact Hp1|right].
    rewrite evaluate_eqn; cbn [evaluate_body]. rewrite Ex', Ey', Ec.
    destruct (evaluate (e2', cst)) as [r1' t1'] eqn:E1'. destruct Hp1 as (<- & Hw1 & Hpost1).
    rewrite evaluate_Seq_eq', E1'. destruct res as [res|].
    + rewrite bd_false' by discriminate. split; [reflexivity|split; [exact Hw1|]].
      eapply ssa_post_some; [discriminate|exact Hpost1].
    + rewrite bd_true' by reflexivity. cbn [ssa_post] in Hpost1.
      specialize (FL rst t1' (ssa_locals_rel_more na2 ssa2 _ _ na3 (conj Hpost1 Hle3))).
      destruct (evaluate (c2, t1')) as [r2 t2]. destruct FL as (-> & Hrel & Hw2).
      split; [reflexivity|split; [eapply word_state_eq_rel_trans; eassumption|exact Hrel]].
  - exists perm2. rewrite evaluate_eqn; cbn [evaluate_body]. rewrite get_var_set_permute, get_var_imm_set_permute, Ex, Ey, Ec.
    destruct (evaluate (p2, set_permute perm2 st)) as [res rst]. destruct Hp2 as [Hp2|Hp2]; [left; exact Hp2|right].
    rewrite evaluate_eqn; cbn [evaluate_body]. rewrite Ex', Ey', Ec.
    destruct (evaluate (e3', cst)) as [r1' t1'] eqn:E1'. destruct Hp2 as (<- & Hw1 & Hpost1).
    rewrite evaluate_Seq_eq', E1'. destruct res as [res|].
    + rewrite bd_false' by discriminate. split; [reflexivity|split; [exact Hw1|]].
      eapply ssa_post_some; [discriminate|exact Hpost1].
    + rewrite bd_true' by reflexivity. cbn [ssa_post] in Hpost1.
      specialize (FR rst t1' Hpost1).
      destruct (evaluate (c3, t1')) as [r2 t2]. destruct FR as (-> & Hrel & Hw2).
      split; [reflexivity|split; [eapply word_state_eq_rel_trans; eassumption|exact Hrel]].
  - exists perm1. rewrite evaluate_eqn; cbn [evaluate_body].
    rewrite get_var_set_permute, get_var_imm_set_permute, Ex, Ey, Ec. cbn beta iota zeta. left; reflexivity.
Qed.

Lemma rel_to_strong {A} n s (sl cl : num_map A) D :
  ssa_locals_rel n s sl cl -> strong_locals_rel (option_lookup s) D sl cl.
Proof.
  intros [_ R2] x v [_ Hx]. destruct (R2 _ _ Hx) as (Hd & Hl & _). apply domain_lookup in Hd as [z Hz].
  unfold option_lookup. rewrite Hz in Hl |- *. exact Hl.
Qed.

Lemma EVERY_lt_mono (l : list N) na na' :
  is_true (EVERY (fun x => x <? na) l) -> na <= na' -> is_true (EVERY (fun x => x <? na') l).
Proof.
  unfold is_true; rewrite !EVERY_Forall, !Forall_forall. intros H Hle x Hx. specialize (H x Hx).
  apply N.ltb_lt in H. apply N.ltb_lt. lia.
Qed.

Lemma ssa_Loop names body exit_names st cst ssa na lt :
  ssa_IH body -> ssa_hyp (Loop names body exit_names) st cst ssa na lt ->
  ssa_concl (Loop names body exit_names) st cst ssa na lt.
Proof.
  intros IH (Heq & Hr & Ha & Hev & Hok & Hlt). cbn [every_var] in Hev.
  apply andb_prop in Hev as [Hev Hke]. apply andb_prop in Hev as [Hkn Hevb].
  unfold ssa_concl. cbn [ssa_cc_trans].
  destruct (loop_setup names exit_names ssa na) as [sp [ssa_r na_r]] eqn:Es.
  destruct (ssa_cc_trans body (inter ssa_r names) na_r ((ssa_r, (names, exit_names)) :: lt)) as [body' [ssa' na']] eqn:Eb.
  destruct (loop_setup_correct st cst ssa na names exit_names sp ssa_r na_r (conj Heq (conj Hr (conj Hok (conj Ha Es)))))
    as (rcst & Esp & Hwr & Hrr & Hle & Har & Hokr & Hdom & Hin & Hex & _).
  assert (Hsub : forall x, domain (union names exit_names) x -> domain ssa_r x)
    by (intros x Hx; rewrite Hdom; right; exact Hx).
  destruct (ssa_Loop_gen body names exit_names lt ssa_r na_r body' ssa' na' IH Hokr Har
              (every_var_lt_mono _ _ _ Hevb Hle) Hin Hex
              ltac:(intros x Hx; apply Hsub; rewrite domain_union; left; exact Hx)
              ltac:(intros x Hx; apply Hsub; rewrite domain_union; right; exact Hx)
              (EVERY_lt_mono _ _ _ Hkn Hle) (EVERY_lt_mono _ _ _ Hke Hle) Hlt Eb st rcst Hwr
              (rel_to_strong _ _ _ _ _ Hrr)) as [perm Hp].
  exists perm. destruct (evaluate (Loop names body exit_names, set_permute perm st)) as [res rst].
  destruct Hp as [Hp|Hp]; [left; exact Hp|right]. rewrite (eval_Seq_none _ _ _ _ Esp). exact Hp.
Qed.

Lemma zip_get_alist (xs ks : list N) vs (st : state) l x y :
  NoDup ks -> In (x, y) (combine xs ks) -> get_vars xs st = Some vs ->
  lookup y (alist_insert ks vs l) = get_var x st.
Proof.
  revert ks vs; induction xs as [|x0 xs IH]; intros [|k0 ks] vs Hnd Hin Hg; [destruct Hin|destruct Hin|destruct Hin|].
  cbn [get_vars] in Hg. destruct (get_var x0 st) as [v0|] eqn:E0; [|discriminate].
  destruct (get_vars xs st) as [vs'|] eqn:Evs; [|discriminate]. injection Hg as <-.
  cbn [alist_insert]. inversion Hnd as [|? ? Hk Hnd']; subst. rewrite lookup_insert'.
  destruct Hin as [E|Hin].
  - injection E as <- <-. rewrite decide_True' by reflexivity. symmetry; exact E0.
  - rewrite decide_False'; [apply IH; auto|]. intros ->. apply Hk. apply in_combine_r in Hin. exact Hin.
Qed.

Lemma get_vars_In_some (xs : list N) vs (st : state) x :
  get_vars xs st = Some vs -> In x xs -> exists v, get_var x st = Some v.
Proof.
  revert vs; induction xs as [|x0 xs IH]; intros vs Hg Hx; [destruct Hx|].
  cbn [get_vars] in Hg. destruct (get_var x0 st) as [v0|] eqn:E0; [|discriminate].
  destruct (get_vars xs st) as [vs'|] eqn:Evs; [|discriminate].
  destruct Hx as [<-|Hx]; [eauto|eapply IH; eauto].
Qed.

Lemma ssa_Move pri ls st cst ssa na lt :
  ssa_hyp (Move pri ls) st cst ssa na lt -> ssa_concl (Move pri ls) st cst ssa na lt.
Proof.
  ssa_start. apply andb_prop in Hevar as [Hev1 Hev2].
  destruct (ALL_DISTINCT (MAP FST ls)) eqn:Ed; [|ssa_err Hev Hres].
  destruct (get_vars (MAP SND ls) st0) as [vs|] eqn:Eg; [|ssa_err Hev Hres]. injection Hev as <- <-.
  rename l into ren1, s into ssa', n into na'.
  destruct (list_next_var_rename_lemma_1 _ _ _ _ _ _ Ex) as (Hd1 & _ & _).
  destruct (list_next_var_rename_lemma_2' _ _ _ _ _ _ Ex Ed) as (Hm1 & _ & _ & _).
  assert (Hlen : LENGTH ren1 = LENGTH (MAP (option_lookup ssa) (MAP SND ls)))
    by (rewrite Hm1, !LENGTH_MAP'; reflexivity).
  assert (Hlv : LENGTH vs = LENGTH (MAP FST ls))
    by (rewrite (get_vars_length_lemma _ _ _ Eg), !LENGTH_MAP'; reflexivity).
  assert (Hlv' : LENGTH ren1 = LENGTH vs) by (rewrite Hlv, Hm1, !LENGTH_MAP'; reflexivity).
  rewrite evaluate_eqn; cbn [evaluate_body]. rewrite MAP_FST_ZIP', MAP_SND_ZIP' by exact Hlen.
  rewrite Hd1. rewrite (ssa_locals_rel_get_vars (MAP SND ls) vs na ssa st0 (set_locals L st0))
    by (rewrite locals_set_locals; auto).
  cbn [ssa_post]. unfold set_vars. rewrite sl_sl, !locals_set_locals.
  split; [reflexivity|split; [apply wser_sl'|]].
  apply ssa_locals_rel_force_rename. split; [|split].
  - apply (ssa_locals_rel_list_next_var_rename (MAP FST ls) ssa na _ _ ren1 ssa' na' vs).
    split; [exact Ex|split; [exact Hr|split; [exact Hok|split; [lia|split; [exact Hev1|split; [exact Ed|]]]]]].
    rewrite is_alloc_var_not_phy by exact Ha. discriminate.
  - unfold is_true; rewrite EVERY_Forall, Forall_forall. intros [x y] Hxy. apply bool_decide_spec.
    apply filter_In in Hxy as [Hxy Hnx]. apply Bool.negb_true_iff in Hnx. rewrite ZIP_combine' in Hxy.
    cbn [FST SND fst snd]. rewrite alist_insert_notin by (rewrite <- MEM_iff'; congruence).
    rewrite (zip_get_alist (MAP SND ls) ren1 vs st0 L x y); [reflexivity| |exact Hxy|exact Eg].
    apply ALL_DISTINCT_iff', Hd1.
  - intros y Hy. apply IN_set in Hy. apply in_map_iff in Hy as [[x y'] [Ey Hxy]]. cbn [SND snd] in Ey. subst y'.
    apply filter_In in Hxy as [Hxy _]. rewrite ZIP_combine' in Hxy.
    apply domain_lookup. pose proof Hxy as Hxy'. apply in_combine_l in Hxy'.
    rewrite (zip_get_alist (MAP SND ls) ren1 vs st0 L x y); [| |exact Hxy|exact Eg].
    + destruct (get_vars_In_some (MAP SND ls) vs st0 x Eg Hxy') as [v Hv]. eauto.
    + apply ALL_DISTINCT_iff', Hd1.
Qed.
Ltac rw_ol Hr Hok :=
  repeat match goal with
  | E : lookup ?r ?sl = Some ?v |- context [lookup (option_lookup ?ssa ?r) ?L] =>
      rewrite (proj1 (ol_props _ ssa sl L r v Hr Hok E))
  end.

Lemma rel_nonphy {A} n s (sl L1 L2 : num_map A) :
  ssa_map_ok n s -> (forall k, ~ is_phy_var k -> lookup k L1 = lookup k L2) ->
  ssa_locals_rel n s sl L1 -> ssa_locals_rel n s sl L2.
Proof.
  intros Hok He [R1 R2]. split.
  - intros x y Hx. destruct (Hok _ _ Hx) as [Hp _]. apply domain_lookup. rewrite <- (He y Hp).
    apply domain_lookup, (R1 _ _ Hx).
  - intros x y Hx. destruct (R2 _ _ Hx) as (Hd & Hl & Ha). split; [exact Hd|split; [|exact Ha]].
    apply domain_lookup in Hd as [z Hz]. rewrite Hz in Hl |- *. cbn [THE] in *.
    destruct (Hok _ _ Hz) as [Hp _]. rewrite <- (He z Hp). exact Hl.
Qed.

Lemma rel_insert_same {A} na ssa (sl L : num_map A) n v :
  ssa_locals_rel na ssa sl L -> ssa_map_ok na ssa -> n < na -> lookup n sl = Some v ->
  ssa_locals_rel (na + 4) (insert n na ssa) sl (insert na v L).
Proof.
  intros Hr Hok Hn Hv.
  assert (E : forall k, lookup k sl = lookup k (insert n v sl))
    by (intros k; rewrite lookup_insert'; destruct (decide (k = n)); subst; auto).
  assert (Hr' : ssa_locals_rel (na + 4) (insert n na ssa) (insert n v sl) (insert na v L))
    by (apply ssa_locals_rel_insert; auto).
  destruct Hr' as [R1 R2]. split; [exact R1|]. intros x y Hx. apply R2. rewrite <- E. exact Hx.
Qed.

Lemma nonphy_neq x p : ~ is_phy_var x -> is_phy_var p = true -> x <> p.
Proof. intros H Hp ->. apply H. exact Hp. Qed.

Lemma ok_ext2 na ssa n n0 :
  ssa_map_ok na ssa -> is_alloc_var na -> ssa_map_ok (na + 4 + 4) (insert n0 (na + 4) (insert n na ssa)).
Proof.
  intros Hok Ha. apply ssa_map_ok_extend. split; [apply ssa_map_ok_extend; split; [exact Hok|]|].
  - rewrite is_alloc_var_not_phy by exact Ha. discriminate.
  - rewrite is_alloc_var_not_phy by (apply is_alloc_var_add, Ha). discriminate.
Qed.

Lemma ev_inst (i : asm.inst a) (s s1 : state) : inst i s = Some s1 -> evaluate (Inst i, s) = (NONE, s1).
Proof. intros E. rewrite evaluate_eqn; cbn [evaluate_body]. rewrite E. reflexivity. Qed.

Lemma ev_move (p : N) moves vs L (s : state) :
  ALL_DISTINCT (MAP FST moves) = true -> get_vars (MAP SND moves) (set_locals L s) = Some vs ->
  evaluate (Move p moves, set_locals L s) = (NONE, set_locals (alist_insert (MAP FST moves) vs L) s).
Proof.
  intros Hd Hg. rewrite evaluate_eqn; cbn [evaluate_body]. rewrite Hd, Hg. unfold set_vars.
  rewrite sl_sl, locals_set_locals. reflexivity.
Qed.

Ltac neq := first [ discriminate | lia | (apply nonphy_neq; [assumption|reflexivity])
                  | (apply not_eq_sym; apply nonphy_neq; [assumption|reflexivity]) ].
Ltac lk := repeat first [ rewrite lookup_insert1 | (rewrite lookup_insert', decide_False' by neq) ].
Ltac nonphy_eq :=
  let k := fresh "k" in let Hk := fresh "Hk" in
  intros k Hk;
  repeat (rewrite ?lookup_insert', ?lookup_delete;
          try (destruct (decide _) as [?|?]; subst; try (exfalso; apply Hk; reflexivity); try lia));
  try reflexivity.

Ltac ol_all Hr Hok :=
  repeat match goal with
  | E : lookup ?r ?sl = Some ?v |- _ =>
      lazymatch goal with
      | _ : lookup (option_lookup _ r) _ = Some v |- _ => fail
      | _ => let H1 := fresh "Hl" in let H2 := fresh "Hp" in let H3 := fresh "Hn" in
             destruct (ol_props _ _ sl _ r v Hr Hok E) as (H1 & H2 & H3)
      end
  end.

Ltac symev Hr Hok :=
  repeat (first
    [ rewrite evaluate_Seq_eq'
    | rewrite (evaluate_eqn (Move _ _))
    | rewrite (evaluate_eqn (Inst _))
    | rewrite (evaluate_eqn (StoreConsts _ _ _ _ _))
    | progress cbn [evaluate_body MAP List.map FST SND fst snd get_vars alist_insert word_exp the_words
                    ALL_DISTINCT MEM negb andb orb]
    | progress (unfold get_var, set_vars, set_var, get_fp_var, set_fp_var, unset_var)
    | rewrite mdomain_set_locals | rewrite memory_set_locals
    | (rewrite lookup_delete, decide_False' by neq)
    | progress (cbv beta iota zeta delta [inst wordSem.assign])
    | rewrite sl_sl | rewrite locals_set_locals | rewrite fp_regs_set_locals
    | rewrite lookup_insert1
    | (rewrite lookup_insert', decide_False' by neq)
    | progress rw_ol Hr Hok
    | progress rw_eqs
    | rewrite bd_true' by reflexivity
    | rewrite bd_false' by neq ]).

Ltac ok_tac Hok Ha :=
  first [ exact Hok
        | apply ssa_map_ok_extend; split;
          [ok_tac Hok Ha|rewrite is_alloc_var_not_phy by (repeat apply is_alloc_var_add; exact Ha); discriminate] ].
Ltac lt_tac := repeat match goal with H : (_ <? _) = true |- _ => apply N.ltb_lt in H end; lia.
Ltac rel_chain Hr Hok Ha :=
  first [ exact Hr
        | apply ssa_locals_rel_delete_left; rel_chain Hr Hok Ha
        | apply ssa_locals_rel_insert; split; [rel_chain Hr Hok Ha|split; [ok_tac Hok Ha|lt_tac]] ].
Ltac ipost Hr Hok Ha :=
  unfold set_var; rewrite ?locals_set_locals, ?sl_sl;
  split; [first [apply wser_sl' | apply wser_sl]|];
  eapply rel_nonphy; cycle 2; [rel_chain Hr Hok Ha|ok_tac Hok Ha|nonphy_eq].

Lemma ssa_inst i (st0 : state) L ssa na s1 :
  ssa_locals_rel na ssa (locals st0) L -> ssa_map_ok na ssa -> is_alloc_var na ->
  is_true (every_var_inst (fun x => x <? na) i) -> inst i st0 = Some s1 ->
  let '(i', (ssa', na')) := ssa_cc_trans_inst i ssa na in
  exists cs1, evaluate (i', set_locals L st0) = (NONE, cs1) /\ word_state_eq_rel s1 cs1 /\
    ssa_locals_rel na' ssa' (locals s1) (locals cs1).
Proof.
  intros Hr Hok Ha Hev H.
  destruct_inst i; cbn [ssa_cc_trans_inst next_var_rename every_var_inst every_var_imm] in *;
    cbv beta iota zeta delta [inst wordSem.assign get_vars] in H;
    cbn [word_exp the_words MAP List.map] in H;
    unfold get_var, mem_load, get_fp_var, set_fp_var in *;
    split_in H; try discriminate H; try (injection H as <-); subst; bool_split.
  all: try (eexists; split;
    [ rewrite evaluate_eqn; cbn [evaluate_body];
      cbv beta iota zeta delta [inst wordSem.assign get_vars];
      cbn [word_exp the_words MAP List.map];
      unfold get_var, mem_load, get_fp_var, set_fp_var in *; autorewrite with lrl; rewrite ?locals_set_locals;
      rw_ol Hr Hok; rw_eqs; autorewrite with lrl; rw_eqs; cbn [OPTION_MAP]; reflexivity
    | repeat match goal with E : mem_store _ _ _ = Some _ |- _ =>
               unfold mem_store in E; destruct (classical_dec _); [injection E as <-|discriminate E] end;
      unfold set_var in *; rewrite ?sl_sl; autorewrite with lrl in *;
      try (split; [first [apply wser_sl' | apply wser_sl | wser]|]);
      first [ apply ssa_locals_rel_insert; split; [exact Hr|split; [exact Hok|apply ltb_var; assumption]]
            | cbn_ws; exact Hr ] ]).
  all: ol_all Hr Hok.
  10: (destruct (option_lookup ssa n0 =? option_lookup ssa n1) eqn:Eq01; cbn beta iota zeta).
  all: eexists; split; [symev Hr Hok; reflexivity|].
  all: try (ipost Hr Hok Ha; fail).
  - split; [wser|]. cbn_ws. apply (rel_insert_same _ _ _ _ _ (Word w2)); auto; lt_tac.
  - split; [wser|]. cbn_ws. exact Hr.
Qed.
Lemma ssa_Inst i st cst ssa na lt :
  ssa_hyp (Inst i) st cst ssa na lt -> ssa_concl (Inst i) st cst ssa na lt.
Proof.
  ssa_start. destruct (inst i st0) as [s1|] eqn:Ei; [|ssa_err Hev Hres]. injection Hev as <- <-.
  pose proof (ssa_inst i st0 L ssa na s1 Hr Hok Ha Hevar Ei) as H. rewrite Ex in H.
  destruct H as (cs1 & -> & Hw & Hrel). cbn [ssa_post]. auto.
Qed.

Lemma ssa_StoreConsts t1 t2 ad off ws st cst ssa na lt :
  ssa_hyp (StoreConsts t1 t2 ad off ws) st cst ssa na lt -> ssa_concl (StoreConsts t1 t2 ad off ws) st cst ssa na lt.
Proof.
  ssa_start. bool_split. unfold get_var in Hev.
  destruct (lookup ad (locals st0)) as [[w1|]|] eqn:E1; try ssa_err Hev Hres.
  destruct (lookup off (locals st0)) as [[w2|]|] eqn:E2; try ssa_err Hev Hres.
  destruct (negb _) eqn:Ec; [ssa_err Hev Hres|]. injection Hev as <- <-.
  ol_all Hr Hok. symev Hr Hok. cbn beta iota. cbn [ssa_post].
  split; [reflexivity|]. unfold set_var, unset_var. cbn_ws. split; [wser|].
  eapply rel_nonphy; cycle 2; [rel_chain Hr Hok Ha|ok_tac Hok Ha|nonphy_eq].
Qed.

Lemma ssa_ShareInst op v e st cst ssa na lt :
  ssa_hyp (ShareInst op v e) st cst ssa na lt -> ssa_concl (ShareInst op v e) st cst ssa na lt.
Proof.
  ssa_start. bool_split.
  destruct (word_exp st0 e) as [[ad|]|] eqn:Ee; try ssa_err Hev Hres.
  pose proof (ssa_exp st0 L ssa na e (Word ad) Hr Ee) as He.
  destruct (bool_decide _) eqn:Eb.
  - apply bool_decide_spec in Eb.
    rewrite evaluate_eqn; cbn [evaluate_body]. rewrite He.
    unfold share_inst in *.
    destruct op; try (exfalso; destruct Eb as [E|[E|[E|E]]]; discriminate E);
      unfold get_var in *; rewrite locals_set_locals;
      (destruct (lookup v (locals st0)) as [[w|]|] eqn:Ev; try ssa_err Hev Hres);
      rewrite (proj1 (ol_props _ _ _ _ v _ Hr Hok Ev));
      unfold sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32 in *;
      autorewrite with lrl;
      (destruct (classical_dec _); [|ssa_err Hev Hres]);
      (destruct (call_FFI _ _ _ _) eqn:Ef; injection Hev as <- <-; cbn [ssa_post];
       first [ (split; [reflexivity|split; [wser|cbn_ws; exact Hr]])
             | (unfold flush_state in *; cbn_ws; split; [reflexivity|split; [wser|reflexivity]]) ]).
  - destr_lets_goal.
    rewrite evaluate_eqn; cbn [evaluate_body]. rewrite He.
    unfold share_inst in *.
    destruct op; try (exfalso; apply Bool.not_true_iff_false in Eb; apply Eb, bool_decide_spec; tauto);
      unfold sh_mem_set_var in *; autorewrite with lrl;
      (lazymatch type of Hev with context [match ?X with SOME _ => _ | NONE => _ end] =>
         destruct X as [[nf nb|out]|] eqn:Es end; injection Hev as <- <-; [| |exfalso; apply Hres; reflexivity]);
      cbn [ssa_post];
      first [ (unfold flush_state in *; cbn_ws; split; [reflexivity|split; [wser|reflexivity]])
            | (unfold set_var; cbn_ws; split; [reflexivity|split; [wser|]];
               apply ssa_locals_rel_insert; split; [exact Hr|split; [exact Hok|apply ltb_var; assumption]]) ].
Qed.

Lemma alloc_rel f (n1 n2 : num_set) w (st cst : state) :
  INJ f (domain n1 UNION domain n2) UNIV ->
  word_state_eq_rel st cst ->
  strong_locals_rel f (domain n1 UNION domain n2) (locals st) (locals cst) ->
  exists perm,
    let '(res, rst) := alloc w (n1, n2) (set_permute perm st) in
    res = SOME Error \/
    let '(res', rcst) := alloc w (apply_nummaps_key f (n1, n2)) cst in
    res = res' /\ word_state_eq_rel rst rcst /\ (res = NONE \/ res = SOME NotEnoughSpace) /\
    (res = NONE -> strong_locals_rel f (domain n1 UNION domain n2) (locals rst) (locals rcst) /\
                   domain (locals rst) = domain n1 UNION domain n2) /\
    (res <> NONE -> locals rst = locals rcst).
Proof.
  intros Hi1 Heq Hs.
  destruct (cut_envs (n1, n2) (locals st)) as [[x0 x1]|] eqn:Ec;
    [|exists (permute st); unfold alloc; rewrite locals_set_permute, Ec; left; reflexivity].
  destruct (cut_envs_lemma f n1 n2 (locals st) (locals cst) x0 x1) as
    (y1 & y2 & Ecy & D1 & D2 & S1 & S2 & I1 & I2 & X1 & X2).
  { split; [inj_less Hi1|split; [inj_less Hi1|split; [exact Ec|split]]];
      eapply strong_locals_rel_subset; (split; [|exact Hs]); set_solve. }
  set (sst := set_store AllocSize (Word w) st). set (scst := set_store AllocSize (Word w) cst).
  destruct (push_env_s_val_eq sst scst x1 y2 x0 y1 f None None (permute cst)) as [perm [Hpe Hsv]].
  { unfold word_state_eq_rel in Heq; destr_conj; subst sst scst; cbn_ws.
    repeat (split; [first [congruence|rewrite X2; exact D2|rewrite X2; exact I2|rewrite X1; exact D1|rewrite X1; exact I1]|]).
    split; [rewrite X2; exact S2|reflexivity]. }
  exists perm.
  unfold alloc. rewrite locals_set_permute, Ec, set_store_set_permute. fold sst.
  set (st' := push_env (x0, x1) NONE (set_permute perm sst)) in *.
  destruct (gc st') as [x|] eqn:Egc; [|left; reflexivity].
  destruct (pop_env x) as [xx|] eqn:Epx; [|left; reflexivity].
  set (cst' := push_env (y1, y2) NONE scst) in *.
  change (permute scst) with (permute cst) in *.
  destruct (env_to_list y2 (permute cst)) as [l pc] eqn:El.
  destruct (env_to_list x1 perm) as [l' pc'] eqn:El'.
  destruct Hpe as (Hpc & Hml & Hinj).
  pose proof Heq as Heq'. unfold word_state_eq_rel in Heq'.
  assert (Hst' : st' = set_permute pc' (set_stack_max (OPTION_MAP2 MAX (stack_max st)
            (stack_size (StackFrame (locals_size st) (toAList x0) l' NONE :: stack st)))
            (set_stack (StackFrame (locals_size st) (toAList x0) l' NONE :: stack st) (set_permute perm sst)))).
  { subst st'. unfold push_env. cbn [FST SND fst snd]. rewrite permute_set_permute, El'. reflexivity. }
  assert (Hcst' : cst' = set_permute pc (set_stack_max (OPTION_MAP2 MAX (stack_max cst)
            (stack_size (StackFrame (locals_size cst) (toAList y1) l NONE :: stack cst)))
            (set_stack (StackFrame (locals_size cst) (toAList y1) l NONE :: stack cst) scst))).
  { subst cst'. unfold push_env. cbn [FST SND fst snd]. subst scst. cbn_ws. rewrite El. reflexivity. }
  assert (Hss : stack_size (StackFrame (locals_size st) (toAList x0) l' NONE :: stack st) =
                stack_size (StackFrame (locals_size cst) (toAList y1) l NONE :: stack cst)).
  { apply s_val_eq_stack_size. rewrite Hst', Hcst' in Hsv. cbn_ws. exact Hsv. }
  destruct (gc_s_val_eq_gen st' cst' x) as (y & Egy & Hv2 & Hk2 & Hm2 & Hstore2 & Hsz2 & Hsm2 & Hsl2).
  { rewrite Hst', Hcst'. subst sst scst. cbn_ws. destr_conj.
    repeat (split; [congruence|]). split; [rewrite Hst', Hcst' in Hsv; cbn_ws; exact Hsv|].
    split; [congruence|]. split; [rewrite Hss; congruence|]. split; [congruence|].
    rewrite <- Hst'. exact Egc. }
  pose proof (gc_frame _ _ Egc) as Fx. pose proof (gc_frame _ _ Egy) as Fy.
  pose proof (gc_s_key_eq _ _ Egc) as Kx.
  assert (Hyx : y = set_permute (permute y) (set_locals (locals y) (set_stack (stack y) x))).
  { rewrite Hst', Hcst' in *. subst sst scst. cbn_ws. destr_conj.
    apply state_eq_except; congruence. }
  destruct (pop_env_set_stack_some x (stack y) xx Hv2 Epx) as [yy0 Epy0].
  assert (Epy : pop_env y = SOME (set_permute (permute y) yy0)).
  { rewrite Hyx, pop_env_set_permute, pop_env_set_locals', Epy0. reflexivity. }
  rewrite Hst' in Kx. rewrite Hcst' in Hk2. cbn_ws.
  unfold pop_env in Epx, Epy0. rewrite stack_set_stack in Epy0.
  destruct (stack x) as [|[mx ex0 lx hx] rx] eqn:Esx; [discriminate|].
  destruct (stack y) as [|[my ey0 ly hy] ry] eqn:Esy; [contradiction|].
  cbn [s_key_eq s_val_eq] in Kx, Hk2, Hv2. destruct Kx as [Kx Kfx], Hk2 as [Hk2 Kfy], Hv2 as [Hv2 Vf].
  apply s_frame_key_eq_def2 in Kfx as (Kx1 & <- & <- & <-).
  apply s_frame_key_eq_def2 in Kfy as (Ky1 & <- & <- & <-).
  apply s_frame_val_eq_def2 in Vf as (Vf1 & _ & _).
  injection Epx as Exx. injection Epy0 as Eyy.
  assert (Hrr : ry = rx).
  { symmetry; apply s_val_and_key_eq; split; [exact Hv2|].
    apply (s_key_eq_trans _ (stack st)); split; [apply s_key_eq_sym; exact Kx|].
    replace (stack st) with (stack cst) by (destr_conj; congruence). exact Hk2. }
  subst ry.
  assert (Hw : word_state_eq_rel xx (set_permute (permute y) yy0)).
  { subst xx yy0. unfold word_state_eq_rel; cbn_ws. destr_conj. repeat split; congruence. }
  assert (Hl : strong_locals_rel f (domain n1 UNION domain n2) (locals xx) (locals (set_permute (permute y) yy0))).
  { subst xx yy0. cbn_ws. apply union_fromAList_rel.
    - exact Vf1.
    - rewrite <- Ky1, <- Kx1. symmetry; apply key_map_implies; exact Hml.
    - rewrite X1; exact S1.
    - pose proof (env_to_list_keys x1 perm) as Hk. rewrite El' in Hk. rewrite <- Kx1, Hk, X1, X2.
      eapply INJ_less; split; [exact Hi1|]. set_solve. }
  assert (Hd : domain (locals xx) = domain n1 UNION domain n2).
  { subst xx. cbn_ws. rewrite domain_union, !domain_fromAList. pose proof (env_to_list_keys x1 perm) as Hk.
    rewrite El' in Hk. apply set_ext; intros z. unfold pred_set.UNION, pred_set.IN.
    assert (HA : is_true (MEM z (MAP FST lx)) <-> domain n2 z).
    { rewrite <- Kx1, MEM_iff', <- X2. pose proof (f_equal (fun P => P z) Hk) as Hkz. cbv beta in Hkz.
      rewrite <- Hkz. symmetry; apply IN_set. }
    assert (HB : is_true (MEM z (MAP FST (toAList x0))) <-> domain n1 z) by (rewrite MEM_toAList_dom, X1; reflexivity).
    change (is_true (MEM z (MAP FST lx)) \/ is_true (MEM z (MAP FST (toAList x0))) <-> domain n1 z \/ domain n2 z).
    tauto. }
  pose proof Hw as Hw'. destruct Hw' as (_ & Hstore & _).
  rewrite Ecy. fold scst. fold cst'. rewrite Egy, Epy.
  unfold get_store, has_space, get_store in *. rewrite Hstore.
  destruct (FLOOKUP (store xx) AllocSize) as [ws|]; [|left; reflexivity].
  destruct ws as [ws|]; [|left; reflexivity].
  destruct (FLOOKUP (store xx) NextFree) as [[nf|]|]; try (left; reflexivity).
  destruct (FLOOKUP (store xx) TriggerGC) as [[tg|]|]; try (left; reflexivity).
  destruct (_ <=? _); right.
  - split; [reflexivity|split; [exact Hw|split; [left; reflexivity|split; [intros _; split; [exact Hl|exact Hd]|intros []; reflexivity]]]].
  - split; [reflexivity|split; [unfold flush_state; wser|split; [right; reflexivity|split; [discriminate|intros _; reflexivity]]]].
Qed.

Lemma rel_cut (ssa' : num_map N) (all : num_set) (sl cl : num_map (word_loc a)) n :
  (forall x, domain all x -> domain ssa' x) ->
  domain sl = domain all -> strong_locals_rel (option_lookup ssa') (domain all) sl cl ->
  (forall x, domain all x -> x < n) ->
  ssa_locals_rel n (inter ssa' all) sl cl.
Proof.
  intros Hsub Hd Hs Hlt. split.
  - intros x y Hxy. rewrite lookup_inter in Hxy.
    destruct (lookup x ssa') as [z|] eqn:Ez, (lookup x all) eqn:Ea; try discriminate. injection Hxy as <-.
    assert (Hx : domain all x) by (apply domain_lookup; eauto).
    rewrite <- Hd in Hx. apply domain_lookup in Hx as [v Hv].
    apply domain_lookup. exists v. assert (E : option_lookup ssa' x = z) by (unfold option_lookup; rewrite Ez; reflexivity).
    rewrite <- E. apply Hs. split; [rewrite <- Hd; apply domain_lookup; eauto|exact Hv].
  - intros x v Hxv. assert (Hx : domain all x) by (rewrite <- Hd; apply domain_lookup; eauto).
    destruct (proj1 (domain_lookup _ _) (Hsub x Hx)) as [z Hz].
    pose proof Hx as Hx'. apply domain_lookup in Hx' as [u Hu].
    rewrite domain_inter. split; [split; apply domain_lookup; eauto|split; [|intros _; apply Hlt, Hx]].
    rewrite lookup_inter, Hz, Hu. cbn [THE].
    assert (E : option_lookup ssa' x = z) by (unfold option_lookup; rewrite Hz; reflexivity).
    rewrite <- E. apply Hs. split; [exact Hx|exact Hxv].
Qed.

Lemma every_name_lt (n1 n2 : num_set) na x :
  is_true (every_name (fun x => x <? na) (n1, n2)) -> domain (union n1 n2) x -> x < na.
Proof.
  unfold every_name, is_true. cbn [FST SND fst snd]. intros H Hx. apply andb_prop in H as [H1 H2].
  rewrite EVERY_Forall, Forall_forall in H1, H2. rewrite domain_union in Hx.
  destruct Hx as [Hx|Hx]; [specialize (H1 x (proj2 (In_toAList_keys _ x) Hx))|specialize (H2 x (proj2 (In_toAList_keys _ x) Hx))];
    apply N.ltb_lt; assumption.
Qed.

Lemma lnvrm_inj ssa na ls (mov : prog a) ssa' na' :
  list_next_var_rename_move ssa na ls = (mov, (ssa', na')) -> ALL_DISTINCT ls ->
  INJ (option_lookup ssa') (fun x => In x ls) UNIV.
Proof.
  intros E Hd. split; [intros; exact Logic.I|]. intros x y [Hx Hy] Exy.
  apply (list_next_var_rename_move_distinct ssa na ls mov ssa' na' x y).
  repeat split; auto; apply MEM_iff'; assumption.
Qed.

Lemma lnvrm_dom ssa na ls (mov : prog a) ssa' na' x :
  list_next_var_rename_move ssa na ls = (mov, (ssa', na')) -> ALL_DISTINCT ls -> In x ls -> domain ssa' x.
Proof.
  intros E Hd Hx. unfold list_next_var_rename_move in E.
  destruct (list_next_var_rename ls ssa na) as [l [s n]] eqn:E1. injection E as _ <- <-.
  destruct (list_next_var_rename_lemma_2' _ _ _ _ _ _ E1 Hd) as (_ & _ & _ & Hex).
  destruct (Hex x (proj2 (MEM_iff' _ _) Hx)) as [y Hy]. apply domain_lookup; eauto.
Qed.

Lemma ssa_Alloc num names st cst ssa na lt :
  ssa_hyp (Alloc num names) st cst ssa na lt -> ssa_concl (Alloc num names) st cst ssa na lt.
Proof.
  intros (Heq & Hr & Ha & Hev & Hok & Hlt). cbn [every_var] in Hev. apply andb_prop in Hev as [Hevn Hevs].
  destruct names as [n1 n2]. unfold ssa_concl. cbn [ssa_cc_trans FST SND fst snd].
  set (all := union n1 n2). set (ls := MAP FST (toAList all)).
  assert (Hdls : ALL_DISTINCT ls) by apply ALL_DISTINCT_MAP_FST_toAList.
  assert (Hls : forall x, In x ls <-> domain all x) by (intros x; apply In_toAList_keys).
  destruct (list_next_var_rename_move ssa (na + 2) ls) as [smov [ssa' na']] eqn:E1.
  destruct (list_next_var_rename_move (inter ssa' all) (na' + 2) ls) as [rmov [ssa'' na'']] eqn:E2.
  destruct (get_var num st) as [[w|]|] eqn:Eg;
    try (exists (permute st); rewrite evaluate_eqn; cbn [evaluate_body]; rewrite get_var_set_permute, Eg;
         left; reflexivity).
  destruct (cut_envs (n1, n2) (locals st)) as [[x0 x1]|] eqn:Ec;
    [|exists (permute st); rewrite evaluate_eqn; cbn [evaluate_body]; rewrite get_var_set_permute, Eg;
      unfold alloc; rewrite locals_set_permute, Ec; left; reflexivity].
  destruct (cut_envs_domain_SUBSET _ _ _ _ Ec) as [Hs1 Hs2].
  assert (Hall_st : forall x, domain all x -> domain (locals st) x).
  { intros x Hx. unfold all in Hx. rewrite domain_union in Hx. destruct Hx; [apply Hs1|apply Hs2]; assumption. }
  assert (Hall_ssa : forall x, In x ls -> domain ssa x).
  { intros x Hx. apply Hls, Hall_st in Hx. apply domain_lookup in Hx as [v Hv]. destruct Hr as [_ R2].
    apply (R2 _ _ Hv). }
  pose proof (list_next_var_rename_move_props_2 _ _ _ _ _ _ E1 (conj (or_introl Ha) Hok)) as (Hle1 & Hst1 & _ & Hok1).
  specialize (Hst1 Ha).
  assert (Hle2 : na <= na + 2) by lia.
  pose proof (lnvrm_core st cst ssa (na + 2) ls (ssa_locals_rel_more na ssa (locals st) (locals cst) (na + 2) (conj Hr Hle2)) Hall_ssa Hdls
                (ssa_map_ok_more na ssa (na + 2) (conj Hok Hle2)) Heq) as C1.
  rewrite E1 in C1. destruct (evaluate (smov, cst)) as [r1 c1] eqn:Es1.
  destruct C1 as (-> & Hr1 & Hw1 & _ & _).
  destruct (ol_props _ _ _ _ num _ Hr1 Hok1 Eg) as (Hn1 & Hnp & _).
  set (c2 := set_locals (insert 2 (Word w) (locals c1)) c1).
  assert (Hr2 : ssa_locals_rel na' ssa' (locals st) (locals c2)).
  { unfold c2. rewrite locals_set_locals. apply ssa_locals_rel_ignore_insert. split; [exact Hok1|split; [exact Hr1|reflexivity]]. }
  assert (Hw2 : word_state_eq_rel st c2) by (unfold c2; eapply word_state_eq_rel_trans; [exact Hw1|apply wser_sl]).
  assert (Hinj : INJ (option_lookup ssa') (domain n1 UNION domain n2) UNIV).
  { eapply INJ_less; split; [exact (lnvrm_inj _ _ _ _ _ _ E1 Hdls)|]. intros x Hx. apply Hls. unfold all.
    rewrite domain_union. exact Hx. }
  destruct (alloc_rel (option_lookup ssa') n1 n2 w st c2 Hinj Hw2 (rel_to_strong _ _ _ _ _ Hr2)) as [perm Hp].
  exists perm. rewrite evaluate_eqn; cbn [evaluate_body]. rewrite get_var_set_permute, Eg.
  destruct (alloc w (n1, n2) (set_permute perm st)) as [res rst] eqn:Ea.
  destruct Hp as [Hp|Hp]; [left; exact Hp|right].
  rewrite (eval_Seq_none _ _ _ _ Es1).
  rewrite (eval_Seq_none _ _ _ _ (eval_move1 1 2 _ c1 (Word w) Hn1)). fold c2.
  rewrite evaluate_Seq_eq'. rewrite (evaluate_eqn (Alloc _ _)); cbn [evaluate_body].
  unfold get_var at 1. unfold c2 at 1. rewrite locals_set_locals, lookup_insert1.
  destruct (alloc w (apply_nummaps_key (option_lookup ssa') (n1, n2)) c2) as [res' rc] eqn:Ea'.
  destruct Hp as (<- & Hwr & Hrs & Hnone & Hsome).
  destruct Hrs as [ -> | -> ].
  - rewrite bd_true' by reflexivity. destruct (Hnone eq_refl) as [Hsr Hdr].
    assert (Hrc : ssa_locals_rel (na' + 2) (inter ssa' all) (locals rst) (locals rc)).
    { apply rel_cut.
      - intros x Hx. apply (lnvrm_dom _ _ _ _ _ _ x E1 Hdls), Hls, Hx.
      - rewrite Hdr. unfold all. rewrite domain_union. reflexivity.
      - eapply strong_locals_rel_subset; split; [|exact Hsr]. intros x Hx. unfold all in Hx. rewrite domain_union in Hx. exact Hx.
      - intros x Hx. pose proof (every_name_lt n1 n2 na x Hevs Hx). lia. }
    pose proof (lnvrm_core rst rc (inter ssa' all) (na' + 2) ls Hrc) as C2.
    rewrite E2 in C2. destruct (evaluate (rmov, rc)) as [r3 c3] eqn:Es3.
    destruct C2 as (-> & Hr3 & Hw3 & _ & _).
    + intros x Hx. rewrite domain_inter. split; [apply (lnvrm_dom _ _ _ _ _ _ x E1 Hdls), Hx|apply Hls, Hx].
    + exact Hdls.
    + apply ssa_map_ok_inter, (ssa_map_ok_more na'); split; [exact Hok1|lia].
    + exact Hwr.
    + cbn [ssa_post]. split; [reflexivity|split; [exact Hw3|exact Hr3]].
  - rewrite bd_false' by discriminate. cbn [ssa_post].
    split; [reflexivity|split; [exact Hwr|apply Hsome; discriminate]].
Qed.

Lemma eval_move_sl p ms L (s s' : state) :
  evaluate (Move p ms, set_locals L s) = (NONE, s') -> s' = set_locals (locals s') s.
Proof.
  rewrite evaluate_eqn; cbn [evaluate_body]. destruct (ALL_DISTINCT _); [|discriminate].
  destruct (get_vars _ _); [|discriminate]. intros E; injection E as <-. unfold set_vars.
  rewrite !locals_set_locals, !sl_sl. reflexivity.
Qed.

Lemma lnvrm_is_move ssa n ls (mov : prog a) x :
  list_next_var_rename_move ssa n ls = (mov, x) -> exists ms, mov = Move 0 ms.
Proof.
  unfold list_next_var_rename_move. destruct (list_next_var_rename _ _ _) as [l [s m]].
  intros E; injection E as <- _. eauto.
Qed.

(** The stack moves before a cutting instruction (Galette-only). *)
Lemma stack_moves_eval (st0 : state) L ssa na (n1 n2 : num_set) smov ssa' na' :
  ssa_locals_rel na ssa (locals st0) L -> ssa_map_ok na ssa -> is_alloc_var na ->
  (forall x, domain (union n1 n2) x -> domain (locals st0) x) ->
  list_next_var_rename_move ssa (na + 2) (MAP FST (toAList (union n1 n2))) = (smov, (ssa', na')) ->
  exists L1, evaluate (smov, set_locals L st0) = (NONE, set_locals L1 st0) /\
    ssa_locals_rel na' ssa' (locals st0) L1 /\ ssa_map_ok na' ssa' /\ na + 2 <= na' /\ is_stack_var na' /\
    INJ (option_lookup ssa') (domain n1 UNION domain n2) UNIV /\
    (forall x, domain (union n1 n2) x -> domain ssa' x).
Proof.
  intros Hr Hok Ha Hsub E1. set (ls := MAP FST (toAList (union n1 n2))) in *.
  assert (Hdls : ALL_DISTINCT ls) by apply ALL_DISTINCT_MAP_FST_toAList.
  assert (Hls : forall x, In x ls <-> domain (union n1 n2) x) by (intros x; apply In_toAList_keys).
  assert (Hall_ssa : forall x, In x ls -> domain ssa x).
  { intros x Hx. apply Hls, Hsub in Hx. apply domain_lookup in Hx as [v Hv]. destruct Hr as [_ R2].
    apply (R2 _ _ Hv). }
  pose proof (list_next_var_rename_move_props_2 _ _ _ _ _ _ E1 (conj (or_introl Ha) Hok)) as (Hle1 & Hst1 & _ & Hok1).
  assert (Hle2 : na <= na + 2) by lia.
  pose proof (lnvrm_core st0 (set_locals L st0) ssa (na + 2) ls
                (ssa_locals_rel_more na ssa (locals st0) L (na + 2) (conj Hr Hle2))
                Hall_ssa Hdls (ssa_map_ok_more na ssa (na + 2) (conj Hok Hle2)) (wser_sl st0 L)) as C1.
  rewrite E1 in C1. destruct (evaluate (smov, set_locals L st0)) as [r1 c1] eqn:Es1.
  destruct C1 as (-> & Hr1 & _ & _ & _).
  destruct (lnvrm_is_move _ _ _ _ _ E1) as [ms ->].
  pose proof (eval_move_sl _ _ _ _ _ Es1) as Hc1.
  exists (locals c1). split; [f_equal; exact Hc1|split; [exact Hr1|split; [exact Hok1|split; [lia|split; [exact (Hst1 Ha)|split]]]]].
  - eapply INJ_less; split; [exact (lnvrm_inj _ _ _ _ _ _ E1 Hdls)|]. intros x Hx. apply Hls.
    rewrite domain_union. exact Hx.
  - intros x Hx. apply (lnvrm_dom _ _ _ _ _ _ x E1 Hdls), Hls, Hx.
Qed.

Lemma sl_sm l m l' (s : state) : set_locals l (set_memory m (set_locals l' s)) = set_locals l (set_memory m s).
Proof. destruct s; reflexivity. Qed.

Lemma ssa_FFI idx p1 l1 p2 l2 names st cst ssa na lt :
  ssa_hyp (FFI idx p1 l1 p2 l2 names) st cst ssa na lt -> ssa_concl (FFI idx p1 l1 p2 l2 names) st cst ssa na lt.
Proof.
  destruct names as [n1 n2]. ssa_start. cbn [FST SND fst snd] in *. bool_split. unfold get_var in Hev.
  destruct (lookup l1 (locals st0)) as [[w1|]|] eqn:E1; try ssa_err Hev Hres.
  destruct (lookup p1 (locals st0)) as [[w2|]|] eqn:E2; try ssa_err Hev Hres.
  destruct (lookup l2 (locals st0)) as [[w3|]|] eqn:E3; try ssa_err Hev Hres.
  destruct (lookup p2 (locals st0)) as [[w4|]|] eqn:E4; try ssa_err Hev Hres.
  destruct (cut_env (n1, n2) (locals st0)) as [env|] eqn:Ec; [|ssa_err Hev Hres].
  assert (Hsub : forall x, domain (union n1 n2) x -> domain (locals st0) x).
  { unfold cut_env in Ec. destruct (cut_envs (n1, n2) (locals st0)) as [[e1 e2]|] eqn:Ecs; [|discriminate].
    destruct (cut_envs_domain_SUBSET _ _ _ _ Ecs) as [Hs1 Hs2]. intros x Hx. rewrite domain_union in Hx.
    destruct Hx; [apply Hs1|apply Hs2]; assumption. }
  destruct (stack_moves_eval st0 L ssa na n1 n2 p s n Hr Hok Ha Hsub Ex)
    as (L1 & Es1 & Hr1 & Hok1 & Hle1 & Hst1 & Hinj & Hdom1).
  rewrite (eval_Seq_none _ _ _ _ Es1).
  ol_all Hr1 Hok1.
  set (L2 := alist_insert [2; 4; 6; 8] [Word w2; Word w1; Word w4; Word w3] L1).
  assert (Em : evaluate (Move 1 [(2, option_lookup s p1); (4, option_lookup s l1); (6, option_lookup s p2); (8, option_lookup s l2)],
                         set_locals L1 st0) = (NONE, set_locals L2 st0)).
  { unfold L2. apply (ev_move 1 [(2, option_lookup s p1); (4, option_lookup s l1); (6, option_lookup s p2); (8, option_lookup s l2)] [Word w2; Word w1; Word w4; Word w3] L1 st0); [reflexivity|].
    cbn [MAP List.map SND snd get_vars]. unfold get_var. rewrite !locals_set_locals.
    rw_ol Hr1 Hok1. reflexivity. }
  rewrite (eval_Seq_none _ _ _ _ Em).
  assert (Hr2 : ssa_locals_rel n s (locals st0) L2).
  { unfold L2. apply (ssa_locals_rel_ignore_list_insert n s st0 (set_locals L1 st0)).
    rewrite locals_set_locals. split; [exact Hok1|split; [exact Hr1|split; reflexivity]]. }
  destruct (cut_env_lemma (option_lookup s) (n1, n2) (locals st0) L2 env) as (env' & Ec' & Dy & Sy & Iy & Dx).
  { cbn [FST SND fst snd]. split; [exact Hinj|split; [exact Ec|apply rel_to_strong with (n := n); exact Hr2]]. }
  rewrite evaluate_Seq_eq'. rewrite (evaluate_eqn (FFI _ _ _ _ _ _)); cbn [evaluate_body].
  unfold get_var. rewrite !locals_set_locals. unfold L2 in *. cbn [alist_insert] in *. lk.
  rewrite Ec'. autorewrite with lrl.
  destruct (misc.read_bytearray w2 _ _) as [bytes|]; [|ssa_err Hev Hres].
  destruct (misc.read_bytearray w4 _ _) as [bytes2|]; [|ssa_err Hev Hres].
  destruct (call_FFI _ _ _ _) as [nf nb|out] eqn:Ef.
  - injection Hev as <- <-. rewrite bd_true' by reflexivity. rewrite sl_sm.
    assert (Hdenv : domain env = domain (union n1 n2)) by (rewrite Dx, domain_union; reflexivity).
    assert (Hrc : ssa_locals_rel (n + 2) (inter s (union n1 n2)) env env').
    { apply rel_cut; [exact Hdom1|exact Hdenv| |].
      - eapply strong_locals_rel_subset; split; [|exact Sy]. intros x Hx. rewrite domain_union in Hx. exact Hx.
      - intros x Hx. pose proof (every_name_lt n1 n2 na x H0 Hx). lia. }
    set (sF := set_ffi nf (set_fp_regs FEMPTY (set_locals env (set_memory (write_bytearray w4 nb (memory st0) (mdomain st0) (be st0)) st0)))).
    set (cF := set_ffi nf (set_fp_regs FEMPTY (set_locals env' (set_memory (write_bytearray w4 nb (memory st0) (mdomain st0) (be st0)) st0)))).
    assert (HwF : word_state_eq_rel sF cF) by (unfold sF, cF; wser).
    pose proof (lnvrm_core sF cF (inter s (union n1 n2)) (n + 2) (MAP FST (toAList (union n1 n2)))
                  ltac:(unfold sF, cF; cbn_ws; exact Hrc)) as C2.
    rewrite Ex0 in C2. destruct (evaluate (p0, cF)) as [r3 c3] eqn:Es3.
    destruct C2 as (-> & Hr3 & Hw3 & _ & _).
    + intros x Hx. apply In_toAList_keys in Hx. rewrite domain_inter. split; [apply Hdom1, Hx|exact Hx].
    + apply ALL_DISTINCT_MAP_FST_toAList.
    + apply ssa_map_ok_inter, (ssa_map_ok_more n); split; [exact Hok1|lia].
    + exact HwF.
    + cbn [ssa_post]. split; [reflexivity|split; [exact Hw3|exact Hr3]].
  - injection Hev as <- <-. rewrite bd_false' by discriminate. cbn [ssa_post].
    unfold flush_state; cbn_ws. split; [reflexivity|split; [wser|reflexivity]].
Qed.

Lemma ssa_Install ptr len dptr dlen names st cst ssa na lt :
  ssa_hyp (Install ptr len dptr dlen names) st cst ssa na lt ->
  ssa_concl (Install ptr len dptr dlen names) st cst ssa na lt.
Proof.
  destruct names as [n1 n2]. ssa_start. cbn [FST SND fst snd] in *. bool_split.
  destruct (cut_env (n1, n2) (locals st0)) as [env|] eqn:Ec; [|ssa_err Hev Hres].
  unfold get_var in Hev.
  destruct (lookup ptr (locals st0)) as [[w1|]|] eqn:E1; try ssa_err Hev Hres.
  destruct (lookup len (locals st0)) as [[w2|]|] eqn:E2; try ssa_err Hev Hres.
  destruct (lookup dptr (locals st0)) as [[w3|]|] eqn:E3; try ssa_err Hev Hres.
  destruct (lookup dlen (locals st0)) as [[w4|]|] eqn:E4; try ssa_err Hev Hres.
  assert (Hsub : forall x, domain (union n1 n2) x -> domain (locals st0) x).
  { unfold cut_env in Ec. destruct (cut_envs (n1, n2) (locals st0)) as [[e1 e2]|] eqn:Ecs; [|discriminate].
    destruct (cut_envs_domain_SUBSET _ _ _ _ Ecs) as [Hs1 Hs2]. intros x Hx. rewrite domain_union in Hx.
    destruct Hx; [apply Hs1|apply Hs2]; assumption. }
  destruct (stack_moves_eval st0 L ssa na n1 n2 p s n Hr Hok Ha Hsub Ex)
    as (L1 & Es1 & Hr1 & Hok1 & Hle1 & Hst1 & Hinj & Hdom1).
  rewrite (eval_Seq_none _ _ _ _ Es1).
  ol_all Hr1 Hok1.
  assert (Em : evaluate (Move 1 [(2, option_lookup s ptr); (4, option_lookup s len)], set_locals L1 st0) =
               (NONE, set_locals (insert 2 (Word w1) (insert 4 (Word w2) L1)) st0)).
  { apply (ev_move 1 [(2, option_lookup s ptr); (4, option_lookup s len)] [Word w1; Word w2] L1 st0); [reflexivity|].
    cbn [MAP List.map SND snd get_vars]. unfold get_var. rewrite !locals_set_locals.
    rw_ol Hr1 Hok1. reflexivity. }
  rewrite (eval_Seq_none _ _ _ _ Em).
  set (L2 := insert 2 (Word w1) (insert 4 (Word w2) L1)).
  assert (Hr2 : ssa_locals_rel n s (locals st0) L2).
  { unfold L2. apply ssa_locals_rel_ignore_insert. split; [exact Hok1|split; [|reflexivity]].
    apply ssa_locals_rel_ignore_insert. split; [exact Hok1|split; [exact Hr1|reflexivity]]. }
  destruct (cut_env_lemma (option_lookup s) (n1, n2) (locals st0) L2 env) as (env' & Ec' & Dy & Sy & Iy & Dx).
  { cbn [FST SND fst snd]. split; [exact Hinj|split; [exact Ec|apply rel_to_strong with (n := n); exact Hr2]]. }
  rewrite evaluate_Seq_eq'. rewrite (evaluate_eqn (Install _ _ _ _ _)); cbn [evaluate_body].
  rewrite locals_set_locals, Ec'. unfold get_var. rewrite !locals_set_locals. unfold L2. lk. rw_ol Hr1 Hok1.
  autorewrite with lrl.
  destruct (compile_oracle st0 0) as [cfg progs] eqn:Eco.
  destruct (buffer_flush _ w1 w2) as [[bytes cb]|]; [|ssa_err Hev Hres].
  destruct (buffer_flush _ w3 w4) as [[data db]|]; [|ssa_err Hev Hres].
  destruct (compile st0 cfg progs) as [[bytes' [data' cfg']]|]; [|ssa_err Hev Hres].
  destruct progs as [|[k prog] progs']; [ssa_err Hev Hres|].
  destruct (_ && _ && _); [|ssa_err Hev Hres]. injection Hev as <- <-.
  rewrite bd_true' by reflexivity.
  assert (Hdenv : domain env = domain (union n1 n2)) by (rewrite Dx, domain_union; reflexivity).
  assert (Hrc : ssa_locals_rel (n + 2) (inter s (union n1 n2)) env env').
  { apply rel_cut; [exact Hdom1|exact Hdenv| |].
    - eapply strong_locals_rel_subset; split; [|exact Sy]. intros x Hx. rewrite domain_union in Hx. exact Hx.
    - intros x Hx. pose proof (every_name_lt n1 n2 na x H0 Hx). lia. }
  assert (Hokc : ssa_map_ok (n + 2) (inter s (union n1 n2)))
    by (apply ssa_map_ok_inter, (ssa_map_ok_more n); split; [exact Hok1|lia]).
  assert (Han : is_alloc_var (n + 2)) by (apply is_stack_var_flip, Hst1).
  rewrite evaluate_Seq_eq'.
  match goal with |- context [evaluate (Move 1 [(?x, 2)], ?cs)] =>
    rewrite (eval_move1 1 x 2 cs (Loc k 0)) by (cbn_ws; apply lookup_insert1) end.
  rewrite bd_true' by reflexivity.
  match goal with |- let '(_, _) := evaluate (_, ?C) in _ = _ /\ word_state_eq_rel ?S _ /\ _ =>
    set (cI := C); set (sI := S) end.
  assert (HwI : word_state_eq_rel sI cI) by (unfold sI, cI; wser).
  assert (HrI : ssa_locals_rel (n + 2 + 4) (insert ptr (n + 2) (inter s (union n1 n2))) (locals sI) (locals cI)).
  { unfold sI, cI. cbn_ws. apply ssa_locals_rel_insert. split; [|split; [exact Hokc|apply ltb_var in H; lia]].
    apply ssa_locals_rel_ignore_insert. split; [exact Hokc|split; [exact Hrc|reflexivity]]. }
  pose proof (lnvrm_core sI cI (insert ptr (n + 2) (inter s (union n1 n2))) (n + 2 + 4)
                (MAP FST (toAList (union n1 n2))) HrI) as C2.
  rewrite Ex0 in C2. destruct (evaluate (p0, cI)) as [r3 c3] eqn:Es3.
  destruct C2 as (-> & Hr3 & Hw3 & _ & _).
  - intros x Hx. apply In_toAList_keys in Hx. rewrite domain_insert, domain_inter. right. split; [apply Hdom1, Hx|exact Hx].
  - apply ALL_DISTINCT_MAP_FST_toAList.
  - apply ssa_map_ok_extend. split; [exact Hokc|]. rewrite is_alloc_var_not_phy by exact Han. discriminate.
  - exact HwI.
  - cbn [ssa_post]. split; [reflexivity|split; [exact Hw3|exact Hr3]].
Qed.

Lemma bad_dest_args_GENLIST (f : N -> N) dest (args : list N) :
  bad_dest_args dest (GENLIST f (LENGTH args)) = bad_dest_args dest args.
Proof.
  unfold bad_dest_args. destruct args as [|x args]; [reflexivity|].
  cbn [LENGTH]. rewrite GENLIST_CONS_aux. reflexivity.
Qed.

Lemma GENLIST_conv_props n :
  NoDup (GENLIST (fun x => 2 * x) n) /\ forall y, In y (GENLIST (fun x => 2 * x) n) -> is_phy_var y = true.
Proof.
  split.
  - apply ALL_DISTINCT_iff', ALL_DISTINCT_GENLIST. intros; lia.
  - intros y Hy. apply In_GENLIST_iff in Hy as (i & _ & ->). unfold is_phy_var. apply N.eqb_eq.
    replace (2 * i) with (0 + i * 2) by lia. rewrite N.Div0.mod_add. reflexivity.
Qed.

Lemma ssa_Call_None dest args h st cst ssa na lt :
  ssa_hyp (Call None dest args h) st cst ssa na lt -> ssa_concl (Call None dest args h) st cst ssa na lt.
Proof.
  ssa_start.
  destruct (get_vars args st0) as [xs|] eqn:Eg; [|ssa_err Hev Hres].
  set (conv := GENLIST (fun x => 2 * x) (LENGTH (MAP (option_lookup ssa) args))).
  destruct (GENLIST_conv_props (LENGTH (MAP (option_lookup ssa) args))) as [Hnd _]. fold conv in Hnd.
  assert (Hlc : LENGTH conv = LENGTH (MAP (option_lookup ssa) args)) by (unfold conv; apply LENGTH_GENLIST').
  assert (Hlx : LENGTH xs = LENGTH conv)
    by (rewrite Hlc, LENGTH_MAP'; exact (get_vars_length_lemma _ _ _ Eg)).
  assert (Hg : get_vars (MAP (option_lookup ssa) args) (set_locals L st0) = Some xs).
  { apply (ssa_locals_rel_get_vars args xs na ssa st0). rewrite locals_set_locals. auto. }
  assert (Hd : ALL_DISTINCT conv = true) by (apply ALL_DISTINCT_iff', Hnd).
  rewrite evaluate_Seq_eq'. rewrite (evaluate_eqn (Move 1 _)); cbn [evaluate_body].
  rewrite MAP_FST_ZIP', MAP_SND_ZIP' by exact Hlc. rewrite Hd, Hg. cbn beta iota. rewrite bd_true' by reflexivity.
  rewrite (evaluate_eqn (Call _ _ _ _)); cbn [evaluate_body].
  rewrite get_vars_set_vars_eq by (split; [exact Hd|exact Hlx]).
  unfold conv. rewrite bad_dest_args_GENLIST, bad_dest_args_MAP.
  destruct (bad_dest_args dest args); [ssa_err Hev Hres|].
  cbn [add_ret_loc] in *. unfold set_vars. autorewrite with lrl.
  destruct (find_code dest xs (code st0) (state_stack_size st0)) as [[args1 [prog ss]]|] eqn:Ef;
    [|ssa_err Hev Hres].
  destruct h as [[hv [hp [hl1 hl2]]]|].
  - rewrite bd_false' in Hev by discriminate. ssa_err Hev Hres.
  - rewrite bd_true' in Hev |- * by reflexivity.
    destruct (clock st0 =? 0).
    + injection Hev as <- <-. cbn [ssa_post]. split; [reflexivity|split; [apply word_state_eq_rel_refl|reflexivity]].
    + rewrite ?dec_clock_set_locals, ?call_env_set_locals.
      destruct (evaluate (prog, call_env args1 ss (dec_clock st0))) as [r1 s1].
      destruct (bad_fun_return r1) eqn:Eb; [ssa_err Hev Hres|]. injection Hev as <- <-.
      split; [reflexivity|split; [apply word_state_eq_rel_refl|]].
      destruct r1 as [[]|]; cbn [ssa_post bad_fun_return] in *; try reflexivity; discriminate.
Qed.

End SSA3.


